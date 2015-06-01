module TomInterpreter where

import qualified Data.Map as M

import Control.Monad.Identity
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State

import AbsTom


data Q = QInt | QBool | QFun [Q] Q deriving (Show, Eq)
type Env = M.Map Ident Q


type StaticCheck = ReaderT Env (ErrorT String Identity)

initEnv :: Env
initEnv = M.empty

resolve :: Ident -> StaticCheck Q
resolve name = do
    mtype <- asks (M.lookup name)
    case mtype of
        Nothing -> throwError ("Unbound name: " ++ show name)
        Just t -> return t

assertFun :: Q -> StaticCheck ()
assertFun (QFun _ _) = return ()
assertFun t = throwError $
    "Type mismatch -- expected funtion, actual: " ++
    show t

assertNotFun :: Q -> StaticCheck ()
assertNotFun funT@(QFun _ _) = throwError $
    "Type mismatch -- one of " ++
    show [QInt, QBool] ++
    " expected, actual: " ++
    show funT
assertNotFun _ = return ()

assertType :: Q -> Q -> StaticCheck ()
assertType expected actual = 
    when (actual /= expected) $ 
        throwError (
            "Type mismatch -- expected: " ++
            show expected ++
            ", actual: " ++
            show actual)

assertExp :: Q -> Exp -> StaticCheck ()
assertExp expected e = do
    t <- checkExp e
    assertType expected t


checkExp :: Exp -> StaticCheck Q

checkExp (ECall name es) = do 
    fun <- resolve name
    assertFun fun
    let QFun params rType = fun
    when (length es /= length params) $ 
        let Ident id = name in throwError $
            "Actual argument list in call" ++
            "and formal parameter list of " ++
            id ++
            " have different length"
    args <- mapM checkExp es
    mapM_ (uncurry assertType) (zip params args)
    return rType
    
checkExp (ELvalue (LIdent ident)) = resolve ident

checkExp (EInt _)  = return QInt
checkExp (EBool _) = return QBool

checkExp (EIver e) = checkUnaryOp QBool QInt e
checkExp (ENot e) = checkUnaryOp QBool QBool e
checkExp (ENeg e) = checkUnaryOp QInt QInt e

checkExp (EEq eL eR) = do
    tL <- checkExp eL
    tR <- checkExp eR
    assertNotFun tL
    assertNotFun tR
    assertType tL tR
    return QInt

checkExp (ENeq eL eR) = checkExp (EEq eL eR)

checkExp (EOr eL eR)  = checkBinOp QBool QBool eL eR
checkExp (EAnd eL eR) = checkBinOp QBool QBool eL eR

checkExp (ELt eL eR)  = checkBinOp QInt QBool eL eR
checkExp (EGt eL eR)  = checkBinOp QInt QBool eL eR
checkExp (ELte eL eR) = checkBinOp QInt QBool eL eR
checkExp (EGte eL eR) = checkBinOp QInt QBool eL eR

checkExp (EAdd eL eR) = checkBinOp QInt QInt eL eR
checkExp (ESub eL eR) = checkBinOp QInt QInt eL eR
checkExp (EMul eL eR) = checkBinOp QInt QInt eL eR
checkExp (EDiv eL eR) = checkBinOp QInt QInt eL eR
checkExp (EMod eL eR) = checkBinOp QInt QInt eL eR

checkUnaryOp :: Q -> Q -> Exp -> StaticCheck Q
checkUnaryOp argType rType e = do
    assertExp argType e
    return rType

checkBinOp :: Q -> Q -> Exp -> Exp -> StaticCheck Q
checkBinOp argsType rType eL eR = do
    assertExp argsType eL
    assertExp argsType eR
    return rType
