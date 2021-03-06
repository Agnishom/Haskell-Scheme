module Env where

import Types
import Control.Monad.Except
import Data.IORef
import Data.Maybe
import qualified Data.Map as M

nullEnv :: IO Env
nullEnv = newIORef M.empty

isBound :: Env -> String -> IO Bool
isBound envRef var = liftM (M.member var) (readIORef envRef)

getVar :: Env -> String -> IOThrowsError EnvVal
getVar envRef var = do env <- liftIO $ readIORef envRef
                       maybe (throwError $ UnboundVar "Getting an unbound variable" var)
                             (liftIO . readIORef)
                             (M.lookup var env)

evalVar :: Evaluator -> Env -> String -> IOThrowsError LispVal
evalVar eval envRef var =
  do env <- liftIO $ readIORef envRef
     case (M.lookup var env) of
      Nothing -> (throwError $ UnboundVar "Getting an unbound variable" var)
      Just eVIO -> do ev <- liftIO $ readIORef eVIO
                      case ev of
                       Evaluated val -> liftIO $ return val
                       Thunk closure lval -> (eval closure lval)

setEvalVar :: Evaluator -> Env -> String -> IOThrowsError LispVal
setEvalVar eval envRef var =
  do evaluated <- evalVar eval envRef var
     setVar envRef var (Evaluated evaluated)
     return evaluated

setVar :: Env -> String -> EnvVal -> IOThrowsError EnvVal
setVar envRef var value = do
                       env <- liftIO $ readIORef envRef
                       maybe (throwError $ UnboundVar "Getting an unbound variable" var)
                             (liftIO . (`writeIORef` value))
                             (M.lookup var env)
                       return value

defineVar :: Env -> String -> EnvVal -> IOThrowsError EnvVal
defineVar envRef var value = do
        alreadyDefined <- liftIO $ isBound envRef var
        if alreadyDefined
           then setVar envRef var value >> return value
           else liftIO $ do
                   valueRef <- newIORef value
                   env <- readIORef envRef
                   writeIORef envRef (M.insert var valueRef env)
                   return value

bindVars :: Env -> [(String, EnvVal)] -> IO Env
bindVars envRef bindings = readIORef envRef >>= extendEnv bindings >>= newIORef
    where extendEnv bindings env = liftM ((`M.union` env) . M.fromList) (mapM addBindings bindings)
          addBindings (var, value) = do ref <- newIORef value
                                        return (var, ref)
