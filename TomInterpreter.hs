module TomInterpreter where

import qualified Data.Map as M

import Control.Monad.Identity
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State

import AbsTom

type Semantics = ReaderT Env (ErrorT String (StateT Stor IO))

type Loc = Int
type Env = M.Map Ident Loc
data Stor = Stor { nextLoc :: Loc, memory :: M.Map Loc Val }
data Val = VInt Integer | VBool Bool | VFun ([(Loc, IsTmp)] -> Semantics Val)
type IsTmp = Bool

initEnv :: Env
initEnv = M.empty

initStor :: Stor
initStor = Stor 0 M.empty

runStm :: Stm -> IO (Either String (Maybe Val), Stor)
runStm stm = runStateT(runErrorT(runReaderT (exec stm) initEnv)) initStor

resolve :: Ident -> Semantics Loc
resolve name = do
    mloc <- asks (M.lookup name)
    case mloc of
        Nothing -> throwError ("RuntimeError -- unbound name: " ++ show name)
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
    loc <- gets nextLoc
    modify $ \s -> s { nextLoc = loc + 1 }
    return loc

free :: Loc -> Semantics ()
free loc = do
    mem <- gets memory
    modify $ \s -> s { memory = M.delete loc mem }

{- Expressions -}

evalToLoc :: Lvalue -> Semantics Loc
evalToLoc (LIdent ident) = resolve ident

evalArg :: Exp -> Semantics (Loc, IsTmp)

evalArg (ELvalue lval) = do
    loc <- evalToLoc lval
    return (loc, False)

evalArg e = do
    val <- eval e
    loc <- alloc
    write loc val
    return (loc, True)
    
eval :: Exp -> Semantics Val

eval (ECall name es) = do
    fLoc <- resolve name
    VFun f <- fetch fLoc
    argLocs <- mapM evalArg es
    f argLocs

eval (ELvalue lval) = evalToLoc lval >>= fetch

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

{- Binary operators with integer arguments returning boolean -}
eval (ELt eL eR)  = boolBinIntOp (<)  eL eR
eval (EGt eL eR)  = boolBinIntOp (>)  eL eR
eval (ELte eL eR) = boolBinIntOp (<=) eL eR
eval (EGte eL eR) = boolBinIntOp (>=) eL eR

{- Binary operators with integer arguments returning integer -}
eval (EAdd eL eR) = intBinIntOp (+) eL eR
eval (ESub eL eR) = intBinIntOp (-) eL eR
eval (EMul eL eR) = intBinIntOp (*) eL eR
eval (EDiv eL eR) = intBinIntOpNoRZero quot eL eR
eval (EMod eL eR) = intBinIntOpNoRZero rem  eL eR

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

intBinIntOpNoRZero op eL eR = do
    VInt iL <- eval eL
    VInt iR <- eval eR
    when (iR == 0) $ throwError "RuntimeError -- Zero on the right side of \"/\" or \"%\""
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

exec (SAssign (LIdent name) e) = do
    val <- eval e
    loc <- resolve name
    write loc val
    return Nothing

exec (SPrint e) = do
    val <- eval e
    case val of
        VBool b -> liftIO $ putStrLn $ show b
        VInt  i -> liftIO $ putStrLn $ show i
    return Nothing

exec (SBlock varList funList stmList) = do
    env <- ask
    (env',  locList1) <- defVars env  varList
    (env'', locList2) <- defFuns env' funList
    
    rval <- local (const env'') (execStms stmList)
    mapM_ free (locList1 ++ locList2)
    return rval

execStms :: [Stm] -> Semantics (Maybe Val)
execStms stmList = foldM appendStm Nothing stmList

appendStm :: Maybe Val -> Stm -> Semantics (Maybe Val)
appendStm Nothing stm = exec stm
appendStm rval _ = return rval


bind :: Ident -> Loc -> Env -> Env
bind = M.insert

bindMany :: [(Ident, Loc)] -> Env -> Env
bindMany = flip $ foldl (\env x -> (uncurry bind) x env)

defVars :: Env -> [Decl] -> Semantics (Env, [Loc])
defVars env varList = do 
    l <- mapM defVar varList
    let env' = bindMany l env
        locList = snd . unzip $ l
    return (env', locList)

defVar :: Decl -> Semantics (Ident, Loc)
defVar (Decl name varT) = do
    loc <- alloc
    case varT of
        TInt  -> write loc (VInt 0)
        TBool -> write loc (VBool False)
    return (name, loc)

defFuns :: Env -> [FunDef] -> Semantics (Env, [Loc])
defFuns env funList = do
    res@(env', locList) <- preDefFuns env funList
    let funs = map (createFun env') funList 
    mapM_ (uncurry write) (zip locList funs)
    return res

preDefFuns :: Env -> [FunDef] -> Semantics (Env, [Loc])
preDefFuns env funList = do
    l <- mapM preDefFun funList
    let env' = bindMany l env
        locList = snd . unzip $ l
    return (env', locList)

preDefFun :: FunDef -> Semantics (Ident, Loc)
preDefFun (FunDef name _ _ _) = do
    loc <- alloc
    return (name, loc)

createFun :: Env -> FunDef -> Val
createFun env (FunDef name params _ stm) = VFun $ \locList -> do
    l <- mapM (uncurry defPar) (zip locList params)
    let (idents, locs, isTmps) = unzip3 l
        env' = bindMany (zip idents locs) env
        tmpLocs = fst . unzip . filter snd $ zip locs isTmps
    rval <- local (const env') (exec stm)
    mapM_ free tmpLocs
    case rval of
        Just val -> return val
        Nothing -> let Ident f = name in
                       throwError ("RuntimeError -- nothing returned in call to: " ++ f)

defPar :: (Loc, IsTmp) -> Param -> Semantics (Ident, Loc, IsTmp)
defPar (loc, isTmp) (PRef name _) = return (name, loc, isTmp)
defPar (loc, False) (PFun name _) = return (name, loc, False)
defPar (loc, True)  (PVar name _) = return (name, loc, True)
defPar (loc, False) (PVar name _) = do
    loc' <- alloc
    val <- fetch loc
    write loc' val
    return (name, loc', True)

{- Instances -}
instance Eq Val where
    VBool bL == VBool bR = bL == bR
    VInt iL == VInt iR = iL == iR
    _ == _ = error "Compared incomparable values."
