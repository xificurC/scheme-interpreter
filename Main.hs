import Text.Parsec hiding (spaces)
import Text.Parsec.String (Parser)
-- import Text.Parsec.Token hiding (symbol)
-- import Text.Parsec.Language
-- import Control.Monad (liftM)
import Control.Monad.Error
-- import Text.Parsec.Char
import System.Environment
import Text.Printf
import System.IO
import Data.IORef
import Data.Maybe
    
data LispVal = Atom String
             | List [LispVal]
             | DottedList [LispVal] LispVal
             | Number Integer
             | String String
             | Bool Bool
               
unwordsList :: [LispVal] -> String
unwordsList = unwords . map show
               
instance Show LispVal where
    show (Atom s)         = s
    show (List l)         = printf "(%s)" (unwordsList l)
    show (DottedList l v) = printf "(%s . %s)" (unwordsList l) (show v)
    show (Number i)       = show i
    show (String s)       = printf "\"%s\"" s
    show (Bool True)      = show "#t"
    show (Bool False)     = show "#f"

data LispError = NumArgs Integer [LispVal]
               | TypeMismatch String LispVal
               | Parser ParseError
               | BadSpecialForm String LispVal
               | NotFunction String String
               | UnboundVar String String
               | Default String
                 
instance Show LispError where
    show (UnboundVar message varname)  = message ++ ": " ++ varname
    show (BadSpecialForm message form) = message ++ ": " ++ show form
    show (NotFunction message func)    = message ++ ": " ++ show func
    show (NumArgs expected found)
        = printf "Expected %d args, found values %s"
          expected (unwordsList found)
    show (TypeMismatch expected found)
        = printf "Invalid type: expected %s, found %s"
          expected (show found)
    show (Parser parseErr) = "Parse error at " ++ show parseErr
                             
instance Error LispError where
    noMsg  = Default "An error has occurred"
    strMsg = Default
             
type ThrowsError = Either LispError

trapError :: (MonadError e m, Show e) => m String -> m String
trapError action = catchError action (return . show)

extractValue :: ThrowsError a -> a
extractValue (Right val) = val

symbol :: Parser Char
symbol =  oneOf "!#$%&|*+-/:<=>?@^_~"
          
spaces :: Parser ()
spaces = skipMany1 space
         
parseString :: Parser LispVal
parseString = do
  char '"'
  x <- many (try parseChar)
  char '"'
  return (String x)
         
parseChar :: Parser Char
parseChar = do
  first <- anyChar
  case first of
    '\\' -> do
      second <- anyChar
      case second of
        '\\' -> return '\\'
        't'  -> return '\t'
        'n'  -> return '\n'
        'r'  -> return '\r'
        c    -> return c
    '"'  -> unexpected "unexpected \""
    c    -> return c
                                   
         
parseAtom :: Parser LispVal
parseAtom = do
  first <- letter <|> symbol
  rest <- many (letter <|> symbol <|> digit)
  case first : rest of
    "#t" -> return (Bool True)
    "#f" -> return (Bool False)
    x    -> return (Atom x)
    
parseNumber :: Parser LispVal
-- parseNumber = liftM Number (natural haskell)
parseNumber = liftM (Number . read) (many1 digit)

parseList :: Parser LispVal
parseList = liftM List (sepBy parseExpr spaces)
            
parseDottedList :: Parser LispVal
parseDottedList = do
  h <- endBy parseExpr spaces
  t <- char '.' >> spaces >> parseExpr
  return (DottedList h t)
         
parseQuoted :: Parser LispVal
parseQuoted = do
  char '\''
  x <- parseExpr
  return (List [Atom "quote", x])
              
parseExpr :: Parser LispVal
parseExpr = parseAtom
            <|> parseString
            <|> parseNumber
            <|> parseQuoted
            <|> do char '('
                   x <- try parseList <|> parseDottedList
                   char ')'
                   return x

readExpr :: String -> ThrowsError LispVal
readExpr input = case parse parseExpr "lisp" input of
                   Left err  -> throwError (Parser err)
                   Right val -> return val
                                
eval :: Env -> LispVal -> IOThrowsError LispVal
eval _ val@(String _)             = return val
eval _ val@(Number _)             = return val
eval _ val@(Bool _)               = return val
eval env (Atom idt)               = getVar env idt
eval _ (List [Atom "quote", val]) = return val
eval env (List [Atom "if", predicate, conseq, alt]) =
    do result <- eval env predicate
       case result of
         Bool False -> eval env alt
         _          -> eval env conseq
eval env (List [Atom "set!", Atom var, form]) =
    eval env form >>= setVar env var
eval env (List [Atom "define!", Atom var, form]) =
    eval env form >>= defineVar env var
eval env (List (Atom "cond" : clauses)) =
    go clauses
        where go :: [LispVal] -> IOThrowsError LispVal
              go [] = throwError (Default "no cond clauses")
              go [List [Atom "else", expr]] = eval env expr
              go (List [test, expr] : rest) =
                  do result <- eval env test
                     case result of
                       Bool True -> eval env expr
                       _         -> go rest
              go (notClause : _) = throwError (BadSpecialForm
                                               "unrecognized cond clause"
                                               notClause)
eval env (List (Atom "case" : key : clauses)) =
    do result <- eval env key
       go result clauses
           where go :: LispVal -> [LispVal] -> IOThrowsError LispVal
                 go _ [] = throwError (Default "no case clauses")
                 go _ [List [Atom "else", expr]] = eval env expr
                 go k (List [datums, expr] : rest) =
                     case datums of
                       List l -> do
                         ts <- liftThrows (mapM (\x -> eqv [k, x]) l)
                         let f (Bool True) = True
                             f _           = False
                         if any f ts
                         then eval env expr
                         else go k rest
                       notList -> throwError (BadSpecialForm "not a list"
                                                             notList)
eval env (List (Atom func : args)) =
    mapM (eval env) args >>= liftThrows . apply func
eval _ badForm = throwError (BadSpecialForm "unrecognized special form" badForm)
                                  
apply :: String -> [LispVal] -> ThrowsError LispVal
apply func args = maybe
                  (throwError (NotFunction
                               "Unrecognized primitive function args"
                               func))
                  ($ args)
                  (lookup func primitives)
                  
primitives :: [(String, [LispVal] -> ThrowsError LispVal)]
primitives = [("+", numericBinop (+)),
              ("-", numericBinop (-)),
              ("*", numericBinop (*)),
              ("/", numericBinop div),
              ("mod", numericBinop mod),
              ("quotient", numericBinop quot),
              ("remainder", numericBinop rem),
              ("=", numBoolBinop (==)),
              ("<", numBoolBinop (<)),
              (">", numBoolBinop (>)),
              ("/=", numBoolBinop (/=)),
              (">=", numBoolBinop (>=)),
              ("<=", numBoolBinop (<=)),
              ("&&", boolBoolBinop (&&)),
              ("||", boolBoolBinop (||)),
              ("string=?", strBoolBinop (==)),
              ("string<?", strBoolBinop (<)),
              ("string>?", strBoolBinop (>)),
              ("string<=?", strBoolBinop (<=)),
              ("string>=?", strBoolBinop (>=)),
              ("car", car),
              ("cdr", cdr),
              ("cons", cons),
              ("eq?", eqv),
              ("eqv?", eqv)
             ]
             
numericBinop :: (Integer -> Integer -> Integer)
             -> [LispVal]
             -> ThrowsError LispVal
numericBinop _ [] = throwError (NumArgs 2 [])
numericBinop _ singleVal@[_] = throwError (NumArgs 2 singleVal)
numericBinop op params = liftM
                         (Number . foldl1 op)
                         (mapM unpackNum params)

unpackNum :: LispVal -> ThrowsError Integer
unpackNum (Number n) = return n
unpackNum notNum     = throwError (TypeMismatch "number" notNum)
                       
boolBinop :: (LispVal -> ThrowsError a)
          -> (a -> a -> Bool)
          -> [LispVal]
          -> ThrowsError LispVal
boolBinop unpacker op args = if length args /= 2
                             then throwError (NumArgs 2 args)
                             else do left  <- unpacker (head args)
                                     right <- unpacker (args !! 1)
                                     return . Bool $ left `op` right

numBoolBinop :: (Integer -> Integer -> Bool) -> [LispVal]
             -> ThrowsError LispVal
numBoolBinop = boolBinop unpackNum
               
strBoolBinop :: (String -> String -> Bool) -> [LispVal]
             -> ThrowsError LispVal
strBoolBinop = boolBinop unpackStr
               
boolBoolBinop :: (Bool -> Bool -> Bool) -> [LispVal]
              -> ThrowsError LispVal
boolBoolBinop = boolBinop unpackBool

unpackStr :: LispVal -> ThrowsError String
unpackStr (String s) = return s
unpackStr notString  = throwError (TypeMismatch "string" notString)
                       
unpackBool :: LispVal -> ThrowsError Bool
unpackBool (Bool b) = return b
unpackBool notBool = throwError (TypeMismatch "boolean" notBool)
                     
car :: [LispVal] -> ThrowsError LispVal
car [List (x : _)]         = return x
car [DottedList (x : _) _] = return x
car [badArg]               = throwError (TypeMismatch "pair" badArg)
car badArgList             = throwError (NumArgs 1 badArgList)
                             
cdr :: [LispVal] -> ThrowsError LispVal
cdr [List (_ : xs)] = return (List xs)
cdr [DottedList [_] x] = return x
cdr [DottedList (_ : xs) x] = return (DottedList xs x)
cdr [badArg] = throwError (TypeMismatch "pair" badArg)
cdr badArgList = throwError (NumArgs 1 badArgList)

cons :: [LispVal] -> ThrowsError LispVal
cons [x1, List []] = return (List [x1])
cons [x, List xs] = return (List (x:xs))
cons [x, DottedList xs xlast] = return (DottedList (x:xs) xlast)
cons [x1, x2] = return (DottedList [x1] x2)
cons badArgList = throwError (NumArgs 2 badArgList)
                  
eqv :: [LispVal] -> ThrowsError LispVal
eqv [Bool arg1, Bool arg2] = return (Bool (arg1 == arg2))
eqv [Number arg1, Number arg2] = return (Bool (arg1 == arg2))
eqv [String arg1, String arg2] = return (Bool (arg1 == arg2))
eqv [Atom arg1, Atom arg2] = return (Bool (arg1 == arg2))
eqv [DottedList xs x, DottedList ys y] = eqv [List (xs ++ [x])
                                                 , List (ys ++ [y])
                                                 ]
eqv [List arg1, List arg2] = return $ Bool $
                                 (length arg1 == length arg2)
                                 && all eqvPair (zip arg1 arg2)
    where  eqvPair (x1, x2) = case eqv [x1, x2] of
                                Left _ -> False
                                Right (Bool val) -> val
eqv [_, _] = return (Bool False)
eqv badArgList = throwError (NumArgs 2 badArgList)
                 
                 
-- REPL stuff

flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

evalString :: Env -> String -> IO String
evalString env expr = runIOThrows . liftM show $
                      liftThrows (readExpr expr) >>= eval env
                           
evalAndPrint :: Env -> String -> IO ()
evalAndPrint env expr = evalString env expr >>= putStrLn

until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ p prompt action = do
  result <- prompt
  unless (p result) (action result >> until_ p prompt action)
         
runOne :: String -> IO ()
runOne expr = nullEnv >>= flip evalAndPrint expr
         
runRepl :: IO ()
runRepl = nullEnv >>= until_ (== "quit") (readPrompt "Lisp>>> ") . evalAndPrint

          
-- Variables and assignment

type Env = IORef [(String, IORef LispVal)]

nullEnv :: IO Env
nullEnv = newIORef []

type IOThrowsError = ErrorT LispError IO

liftThrows :: ThrowsError a -> IOThrowsError a
liftThrows (Left err) = throwError err
liftThrows (Right val) = return val

runIOThrows :: IOThrowsError String -> IO String
runIOThrows action = liftM extractValue (runErrorT (trapError action))
                     
isBound :: Env -> String -> IO Bool
isBound envRef var = liftM (isJust . lookup var) (readIORef envRef)
                     
getVar :: Env -> String -> IOThrowsError LispVal
getVar envRef var =
    do env <- liftIO (readIORef envRef)
       maybe (throwError (UnboundVar "Getting an unbound variable" var))
             (liftIO . readIORef)
             (lookup var env)
             
setVar :: Env -> String -> LispVal -> IOThrowsError LispVal
setVar envRef var value =
    do env <- liftIO (readIORef envRef)
       maybe (throwError (UnboundVar "Setting an unbound variable" var))
             (liftIO . flip writeIORef value)
             (lookup var env)
       return value
              
defineVar :: Env -> String -> LispVal -> IOThrowsError LispVal
defineVar envRef var value =
    do alreadyDefined <- liftIO (isBound envRef var)
       if alreadyDefined
       then setVar envRef var value >> return value
       else liftIO $ do
         valueRef <- newIORef value
         env <- readIORef envRef
         writeIORef envRef ((var, valueRef) : env)
         return value
                
bindVars :: Env -> [(String, LispVal)] -> IO Env
bindVars envRef bindings =
    readIORef envRef >>= extendEnv bindings >>= newIORef
        where extendEnv bs env = liftM (++env) (mapM addBinding bs)
              addBinding (var, value) = do ref <- newIORef value
                                           return (var, ref)

main :: IO ()
main = do
  args <- getArgs
  case length args of
    0 -> runRepl
    1 -> runOne (head args)
    _ -> putStrLn "Program takes only 0 or 1 argument"
