{-# LANGUAGE ExistentialQuantification #-}
module Types where

import Control.Monad.Except
import Data.IORef
import System.IO
import Text.ParserCombinators.Parsec (ParseError)
import qualified Data.Map as M

data LispVal = Atom          String
             | List          [LispVal]
             | DottedList    [LispVal] LispVal
             | Number        Integer
             | Character     Char
             | String        String
             | Bool          Bool
             | Port          Handle
             | IOFunc        ([LispVal] -> IOThrowsError LispVal)
             | PrimitiveFunc ([LispVal] -> ThrowsError LispVal)
             | EnvFunc       (Env -> [LispVal] -> IOThrowsError LispVal)
             | Macro         ([LispVal] -> IOThrowsError LispVal)
             | Func { params  :: [String]
                    , varArg  :: Maybe String
                    , body    :: [LispVal]
                    , closure :: Env
                    }

data LispError = NumArgs        Integer      [LispVal]
               | TypeMismatch   String LispVal
               | BadSpecialForm String LispVal
               | NotFunction    String String
               | UnboundVar     String String
               | Default        String
               | Parser         ParseError

type ThrowsError = Either LispError

data Unpacker = forall a. Eq a => AnyUnpacker (LispVal -> ThrowsError a)

type Evaluator = Env -> LispVal -> IOThrowsError LispVal

data EnvVal = Evaluated LispVal
            | Thunk Env LispVal

type Env = IORef (M.Map String (IORef EnvVal))

type IOThrowsError = ExceptT LispError IO


instance Show LispVal where show = showVal

instance Show LispError where show = showError

isMacro :: LispVal -> Bool
isMacro (Macro _) = True
isMacro _         = False

showVal :: LispVal -> String
showVal (String     s     ) = "\"" ++ s ++ "\""
showVal (Character  ch    ) = "#\\" ++ show ch
showVal (Atom       a     ) = a
showVal (Number     n     ) = show n
showVal (Bool       True  ) = "#t"
showVal (Bool       False ) = "#f"
showVal (List       l     ) = "(" ++ unwordsList l                   ++ ")"
showVal (DottedList h t   ) = "(" ++ unwordsList h ++ " . " ++ showVal t ++ ")"
showVal (Port       _     ) = "<IO port>"
showVal (IOFunc     _     ) = "<IO primitive>"
showVal (PrimitiveFunc _  ) = "<primitive>"
showVal (EnvFunc    _     ) = "<primitive>"
showVal (Macro      _     ) = "<macro>"
showVal (Func args varargs body env) = 
        "(lambda (" ++ unwords (map show args) ++
          (case varargs of
            Nothing -> ""
            Just arg -> " . " ++ arg) ++ ") ...)"

showError :: LispError -> String
showError (UnboundVar     message  varname ) = message ++ ": " ++ varname
showError (BadSpecialForm message  form    ) = message ++ ": " ++ show form
showError (NotFunction    message  func    ) = message ++ ": " ++ show func
showError (Parser         parseErr         ) = "Parse error at " ++ show parseErr
showError (NumArgs        expected found   ) = "Expected " ++ show expected
                                             ++ " args; found values " ++ unwordsList found
showError (TypeMismatch   expected found   ) = "Invalid type: expected " ++ expected
                                             ++ ", found " ++ show found

trapError :: (MonadError e m, Show e) => m String -> m String
trapError action = catchError action (return . show)

extractValue :: ThrowsError a -> a
extractValue (Right val) = val


liftThrows :: ThrowsError a -> IOThrowsError a
liftThrows (Left  err) = throwError err
liftThrows (Right val) = return val

runIOThrows :: IOThrowsError String -> IO String
runIOThrows action = liftM extractValue $ runExceptT $ trapError action

unwordsList :: [LispVal]  -> String
unwordsList = unwords . map showVal
