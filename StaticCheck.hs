module StaticCheck where

import qualified Data.Map as M

import Control.Monad.Identity
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State

import AbsTom


type Env = M.Map Ident Type

type StaticDecl  = ErrorT String (StateT Env Identity)
type StaticCheck = ReaderT Env (ErrorT String Identity)

rtypeId = Ident "return"

initEnv :: Env
initEnv = M.singleton rtypeId TInt

staticCheck :: Stm -> Either String ()
staticCheck stm = runIdentity $ runErrorT $ runReaderT (checkStm stm) initEnv

extractId :: Ident -> String
extractId (Ident id) = id

resolve :: Ident -> StaticCheck Type
resolve name = do
    mtype <- asks (M.lookup name)
    case mtype of
        Nothing -> throwError ("Unbound name: " ++ extractId name)
        Just t -> return t

assertFun :: Type -> StaticCheck ()
assertFun (TFun _ _) = return ()
assertFun t = throwError $
    "Type mismatch -- expected funtion, actual: " ++ show t

assertNotFun :: Type -> StaticCheck ()
assertNotFun funT@(TFun _ _) = throwError $
    "Type mismatch -- one of "
    ++ show [TInt, TBool]
    ++ " expected, actual: "
    ++ show funT
assertNotFun _ = return ()

assertType :: Type -> Type -> StaticCheck ()
assertType expected actual = 
    when (actual /= expected) $ 
        throwError (
            "Type mismatch -- expected: "
            ++ show expected
            ++ ", actual: "
            ++ show actual)

assertExp :: Type -> Exp -> StaticCheck ()
assertExp expected e = do
    t <- checkExp e
    assertType expected t


checkExp :: Exp -> StaticCheck Type

checkExp (ECall name es) = do 
    fun <- resolve name
    assertFun fun
    let TFun params rType = fun
    when (length es /= length params) $ 
        throwError $
            "Actual argument list and formal parameter list in call to "
            ++ extractId name
            ++ " have different length"
    args <- mapM checkExp es
    mapM_ (uncurry assertType) (zip params args)
    return rType
    
checkExp (ELvalue (LIdent ident)) = resolve ident

checkExp (EInt _)  = return TInt
checkExp (EBool _) = return TBool

checkExp (EIver e) = checkUnaryOp TBool TInt e
checkExp (ENot e) = checkUnaryOp TBool TBool e
checkExp (ENeg e) = checkUnaryOp TInt TInt e

checkExp (EEq eL eR) = do
    tL <- checkExp eL
    tR <- checkExp eR
    assertNotFun tL
    assertNotFun tR
    assertType tL tR
    return TBool

checkExp (ENeq eL eR) = checkExp (EEq eL eR)

checkExp (EOr eL eR)  = checkBinOp TBool TBool eL eR
checkExp (EAnd eL eR) = checkBinOp TBool TBool eL eR

checkExp (ELt eL eR)  = checkBinOp TInt TBool eL eR
checkExp (EGt eL eR)  = checkBinOp TInt TBool eL eR
checkExp (ELte eL eR) = checkBinOp TInt TBool eL eR
checkExp (EGte eL eR) = checkBinOp TInt TBool eL eR

checkExp (EAdd eL eR) = checkBinOp TInt TInt eL eR
checkExp (ESub eL eR) = checkBinOp TInt TInt eL eR
checkExp (EMul eL eR) = checkBinOp TInt TInt eL eR
checkExp (EDiv eL eR) = checkBinOp TInt TInt eL eR
checkExp (EMod eL eR) = checkBinOp TInt TInt eL eR

checkUnaryOp :: Type -> Type -> Exp -> StaticCheck Type
checkUnaryOp argType rType e = do
    assertExp argType e
    return rType

checkBinOp :: Type -> Type -> Exp -> Exp -> StaticCheck Type
checkBinOp argsType rType eL eR = do
    assertExp argsType eL
    assertExp argsType eR
    return rType

checkStm :: Stm -> StaticCheck ()

checkStm (SExp e) = checkExp e >> return ()

checkStm (SWhile e stm) = do
    assertExp TBool e
    checkStm stm

checkStm (SIf e stm) = do
    assertExp TBool e
    checkStm stm

checkStm (SIfElse e stmT stmF) = do
    assertExp TBool e
    checkStm stmT
    checkStm stmF

checkStm (SReturn e) = do
    rtype <- resolve rtypeId
    assertExp rtype e

checkStm (SAssign (LIdent name) e) = do
    t <- resolve name
    assertExp t e

checkStm (SPrint e) = do
    t <- checkExp e
    assertNotFun t

checkStm (SBlock varList funList stmList) = do
    env <- defineNames $ buildBlockScope varList funList
    mapM_ (local (const env) . checkFun) funList
    mapM_ (local (const env) . checkStm) stmList

defineNames :: StaticDecl Env -> StaticCheck Env
defineNames m =
    ReaderT $ \env ->
        let newScopePacked = runIdentity $ evalStateT (runErrorT m) M.empty
        in ErrorT $ Identity $
            case newScopePacked of
                Right newScope -> Right $ M.union newScope env
                err -> err

buildBlockScope :: [Decl] -> [FunDef] -> StaticDecl Env
buildBlockScope varList funList = do
    mapM_ defineVar varList
    mapM_ defineFun funList
    get

assertNotDefined :: Ident -> StaticDecl ()
assertNotDefined name = do
    env <- get
    when (M.member name env) $ 
        throwError $
            "Redefinition of "
             ++ extractId name 
             ++ " within the same scope"

safeBind :: Ident -> Type -> StaticDecl ()
safeBind name t = do
    assertNotDefined name
    modify $ M.insert name t

defineVar :: Decl -> StaticDecl ()
defineVar (Decl name varT) = safeBind name varT

defineFun :: FunDef -> StaticDecl ()
defineFun (FunDef name params rType _) = do
    let funT = TFun (map paramType params) rType
    safeBind name funT
    
    where
        paramType (PVar _ t) = t
        paramType (PRef _ t) = t
        paramType (PFun _ t) = t 

checkFun :: FunDef -> StaticCheck ()
checkFun (FunDef name params rType stm) = do
    env <- defineNames $ buildParamScope params
    let env' = M.insert rtypeId rType env
    local (const env') (checkStm stm)

buildParamScope :: [Param] -> StaticDecl Env
buildParamScope params = do
    mapM_ defineParam params
    get
    
    where
        defineParam (PVar name t) = safeBind name t
        defineParam (PRef name t) = safeBind name t
        defineParam (PFun name t) = safeBind name t
