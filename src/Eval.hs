module Eval ( eval
            , apply
            , applyProc
            , valuePolicy
            ) where

import Control.Monad
import Control.Monad.Except
import Data.Maybe (isNothing)

import Types
import Env
import Parser

data EvalPolicy = EvalPolicy { setPolicy :: Env -> String -> LispVal -> IOThrowsError LispVal
                             , definePolicy :: Env -> String -> LispVal -> IOThrowsError LispVal
                             , applyPolicy :: Env -> [String] -> Maybe String -> [LispVal] -> Env -> [LispVal] -> IOThrowsError LispVal
                             }

eval :: EvalPolicy -> Env -> LispVal -> IOThrowsError LispVal
eval _ _ val@(String _) = return val
eval _ _ val@(Number _) = return val
eval _ _ val@(Bool   _) = return val
eval _ _  (Atom  "else") = return $ Bool True
eval policy env (Atom id     ) = evalVar (eval policy) env id
-- Special Forms --
eval _ _ (List [Atom "quote", val ]) = return val
eval policy env (List [Atom "if", pred, conseq, alt]) = do
     result <- eval policy env pred
     case result of
       Bool True  -> eval policy env conseq
       Bool False -> eval policy env alt
       _          -> throwError $ TypeMismatch "boolean" pred
eval policy env (List (Atom "cond" : conds)) = case conds of
     (x:xs) -> case x of
                 (List (pred:conseqs)) -> do
                    result <- eval policy env pred
                    case result of
                      Bool True ->  do
                        results <- mapM (eval policy env) conseqs
                        case results of
                          [] -> throwError $ 
                                  BadSpecialForm "Need at least one expression to evalute cond" x
                          _  -> return $ last results
                      Bool False -> eval policy env (List (Atom "cond" : xs))
                      _          -> throwError $ TypeMismatch "boolean" pred
                 _                     -> throwError $ TypeMismatch "non-empty list" x
     []     -> return $ List []
eval policy env (List [Atom "set!"   , Atom var, form]) =
        setPolicy policy env var form
eval _ env (List (Atom "define" : List       (Atom var : params)         : body)) =
  do
        v <- makeNormalFunc env params body
        defineVar env var (Evaluated v)
        return v
eval _ env (List (Atom "define" : DottedList (Atom var : params) varargs : body)) =
  do
       v <- makeVarArgs varargs env params body
       defineVar env var (Evaluated v)
       return v
eval policy env (List [Atom "define" , Atom var    , form]) =
        definePolicy policy env var form
eval _ env (List (Atom "lambda" : List params : body)) =
        makeNormalFunc env params body
eval _ env (List (Atom "lambda" : DottedList params varargs : body)) =
        makeVarArgs varargs env params body
eval _ env (List (Atom "lambda" : varargs@(Atom _) : body)) =
        makeVarArgs varargs env [] body
eval policy env (List [Atom "load", String filename]) =
        load filename >>= liftM last . mapM (eval policy env)
eval policy env (List (function : args))    = do
        func <- eval policy env function
        apply policy env func args
eval _ env badForm                     = throwError $ BadSpecialForm "Unrecognized special form" badForm

makeFunc :: Monad m => Maybe String -> Env -> [LispVal] -> [LispVal] -> m LispVal
makeFunc varargs env params body = return $ Func (map showVal params) varargs body env

makeNormalFunc :: Monad m => Env -> [LispVal] -> [LispVal] -> m LispVal
makeNormalFunc = makeFunc Nothing

makeVarArgs :: Monad m => LispVal -> Env -> [LispVal] -> [LispVal] -> m LispVal
makeVarArgs = makeFunc . Just . showVal

apply :: EvalPolicy -> Env -> LispVal -> [LispVal] -> IOThrowsError LispVal
apply policy env   (PrimitiveFunc func) args = mapM (eval policy env) args >>= (liftThrows . func)
apply policy env   (IOFunc        func) args = mapM (eval policy env) args >>= func
apply _      env   (Macro         func) args = func args
apply policy env   (EnvFunc       func) args = mapM (eval policy env) args >>= func env
apply policy env   (Func params varargs body closure) args =
  applyPolicy policy env params varargs body closure args

load :: String -> IOThrowsError [LispVal]
load filename = liftIO (readFile filename) >>= liftThrows . readExprList


valuePolicy = EvalPolicy valueSetPolicy valueDefinePolicy valueApplyPolicy

valueSetPolicy :: Env -> String -> LispVal -> IOThrowsError LispVal
valueSetPolicy env var form =
  do
    v <- eval valuePolicy env form
    setVar env var (Evaluated v)
    return v

valueDefinePolicy :: Env -> String -> LispVal -> IOThrowsError LispVal
valueDefinePolicy env var form =
  do
    v <- eval valuePolicy env form
    defineVar env var (Evaluated v)
    return v

valueApplyPolicy :: Env -> [String] -> Maybe String -> [LispVal] -> Env -> [LispVal] -> IOThrowsError LispVal
valueApplyPolicy dynamicEnv params varargs body staticEnv args =
    do valArgs <- mapM (eval valuePolicy dynamicEnv) args
       let remainingArgs = drop (length params) valArgs
       let num = toInteger . length
       let evalBody env = liftM last $ mapM (eval valuePolicy env) body
       let bindVarArgs arg env = case arg of
                                       Just argName -> liftIO $ bindVars dynamicEnv [(argName, Evaluated $ List remainingArgs)]
                                       Nothing      -> return env
       if num params /= num valArgs && isNothing varargs
           then throwError $ NumArgs (num params) valArgs
           else liftIO (bindVars staticEnv $ zip params (map Evaluated valArgs)) >>= bindVarArgs varargs >>= evalBody

applyProc :: EvalPolicy -> Env -> [LispVal] -> IOThrowsError LispVal
applyProc policy env [func, List args] = apply policy env func args
applyProc policy env (func : args    ) = apply policy env func args
