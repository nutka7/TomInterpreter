module TomInterpreter where

import qualified Data.Map as M

import Control.Monad.Identity
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State

import AbsTom

type Semantics = ReaderT Env (ErrorT String (StateT Stor IO))

type Var = String
type Loc = Int
type Env = M.Map Var Loc
data Stor = Stor { freeLoc :: Loc, memory :: M.Map Loc Val }
    deriving (Show, Eq)

data Val = VInt Integer | VBool Bool deriving (Show, Eq)

initEnv :: Env
initEnv = M.empty

initStor :: Stor
initStor = Stor 0 M.empty

runStm :: Stm -> IO (Either String (Maybe Val), Stor)
runStm stm = runStateT(runErrorT(runReaderT (exec stm) initEnv)) initStor

resolve :: Var -> Semantics Loc
resolve var = do
    mloc <- asks (M.lookup var)
    case mloc of
        Nothing -> throwError ("RuntimeError -- unbound variable: " ++ show var)
        Just loc -> return loc

fetch :: Loc -> Semantics Val
fetch loc = do
    mval <- gets (M.lookup loc . memory)
    case mval of
        Nothing -> throwError ("RuntimeError -- invalid location: " ++ show loc)
        Just val -> return val

write :: Loc -> Val -> Semantics ()
write loc val = do
    mem <- gets memory
    modify $ \s -> s { memory = M.insert loc val mem }

alloc :: Semantics Loc
alloc = do
    free <- gets freeLoc
    modify $ \s -> s { freeLoc = free + 1 }
    return free

{- Expressions -}
eval :: Exp -> Semantics Val

eval (EVar (Ident var)) = resolve var >>= fetch

eval (EInt i) = return $ VInt i

eval (EBool BTrue)  = return $ VBool True
eval (EBool BFalse) = return $ VBool False

eval (EIver e) = do
    VBool b <- eval e
    return $ VInt $ if b then 1 else 0

eval (ENot e) = do
    VBool b <- eval e
    return $ VBool $ not b

eval (ENeg e) = do
    VInt i <- eval e
    return $ VInt $ -i

eval (EEq eL eR) = do
    valL <- eval eL
    valR <- eval eR
    return $ VBool $ valL == valR

eval (ENeq eL eR) = do
    valL <- eval eL
    valR <- eval eR
    return $ VBool $ valL /= valR

{- Binary operators with boolean arguments returning boolean -}
eval (EOr eL eR)  = boolBinBoolOp (||) eL eR
eval (EAnd eL eR) = boolBinBoolOp (&&) eL eR

{- Binary operators with integer arguments returning integer -}
eval (ELt eL eR)  = boolBinIntOp (<)  eL eR
eval (EGt eL eR)  = boolBinIntOp (>)  eL eR
eval (ELte eL eR) = boolBinIntOp (<=) eL eR
eval (EGte eL eR) = boolBinIntOp (>=) eL eR

{- Binary operators with integer arguments returning boolean -}
eval (EAdd eL eR) = intBinIntOp (+) eL eR
eval (ESub eL eR) = intBinIntOp (-) eL eR
eval (EMul eL eR) = intBinIntOp (*) eL eR
eval (EDiv eL eR) = intBinIntOp div eL eR
eval (EMod eL eR) = intBinIntOp mod eL eR

boolBinBoolOp :: (Bool -> Bool -> Bool) -> Exp -> Exp -> Semantics Val
boolBinBoolOp op eL eR = do
    VBool bL <- eval eL
    VBool bR <- eval eR
    return $ VBool $ bL `op` bR

boolBinIntOp  :: (Integer -> Integer -> Bool) -> Exp -> Exp -> Semantics Val
boolBinIntOp op eL eR = do
    VInt iL <- eval eL
    VInt iR <- eval eR
    return $ VBool $ iL `op` iR

intBinIntOp :: (Integer -> Integer -> Integer) -> Exp -> Exp -> Semantics Val
intBinIntOp op eL eR = do
    VInt iL <- eval eL
    VInt iR <- eval eR
    return $ VInt $ iL `op` iR

exec :: Stm -> Semantics (Maybe Val)

exec (SExp e) = eval e >> return Nothing

exec this@(SWhile e stm) = do
    VBool b <- eval e
    if b then do
        result <- exec stm
        case result of
            Nothing -> exec this
            _ -> return result
    else return Nothing

exec (SIf e stm) = do
    VBool b <- eval e
    if b then exec stm else return Nothing

exec (SIfElse e stmT stmF) = do
    VBool b <- eval e
    if b then exec stmT else exec stmF

exec (SReturn e) = eval e >>= return . Just

exec (SAssign (LIdent (Ident var)) e) = do
    val <- eval e
    loc <- resolve var
    write loc val
    return Nothing

exec (SPrint e) = do
    val <- eval e
    case val of
        VBool b -> liftIO $ putStrLn $ show b
        VInt  i -> liftIO $ putStrLn $ show i
    return Nothing

exec (SBlock declList stmList) = do
    blockEnv <- declVars declList
    local (const blockEnv) (execStms stmList)

execStms :: [Stm] -> Semantics (Maybe Val)
execStms stmList = foldM appendStm Nothing stmList

appendStm :: Maybe Val -> Stm -> Semantics (Maybe Val)
appendStm Nothing stm = exec stm
appendStm rval _ = return rval

bind :: Var -> Loc -> Env -> Env
bind = M.insert

declVars :: [Decl] -> Semantics Env
declVars declList = do
    env <- ask
    foldM declVar env declList

declVar :: Env -> Decl -> Semantics Env
declVar env d = do
    let Decl (Ident var) varT = d
    loc <- alloc
    case varT of
        TInt  -> write loc (VInt 0)
        TBool -> write loc (VBool False)
    return $ bind var loc env
