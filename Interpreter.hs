-- automatically generated by BNF Converter
module Main where

import qualified Data.Map as M

import System.IO
import System.Environment ( getArgs, getProgName )
import System.Exit ( exitFailure, exitSuccess )

import LexTom
import ParTom
import SkelTom
import PrintTom
import AbsTom
import TomInterpreter


import ErrM

type ParseFun a = [Token] -> Err a

myLLexer = myLexer

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = if v > 1 then hPutStrLn stderr s else return ()

runFile :: Verbosity -> ParseFun Stm -> FilePath -> IO ()
runFile v p f = readFile f >>= run v p

run :: Verbosity -> ParseFun Stm -> String -> IO ()
run v p s = let ts = myLLexer s in case p ts of
           Bad s    -> do hPutStrLn stderr "\nParse              Failed...\n"
                          putStrV v "Tokens:"
                          putStrV v $ show ts
                          hPutStrLn stderr s
           Ok  tree -> do runFromTree tree

runFromTree :: Stm -> IO ()
runFromTree stm = do
    (rval, stor) <- runStm stm
    case rval of
        Left s -> do hPutStrLn stderr $ "Error occured: " ++ s
                     exitFailure
        Right rval -> do putStrLn $ "Returned: " ++ case rval of
                            Just (VInt i)  -> show i
                            Just (VBool b) -> show b
                            Nothing -> "Nothing"
                         let leak = M.size (memory stor)
                         if leak > 0 then do
                            hPutStrLn stderr $
                                "Memory leak: " ++ show leak ++ " locations were not freed!"
                            exitFailure
                         else exitSuccess


showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree
 = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

main :: IO ()
main = do args <- getArgs
          case args of
            [] -> hGetContents stdin >>= run 2 pStm
            "-s":fs -> mapM_ (runFile 0 pStm) fs
            fs -> mapM_ (runFile 2 pStm) fs
