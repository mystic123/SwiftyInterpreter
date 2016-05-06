{-# LANGUAGE FlexibleContexts #-}
module Main where

import System.IO (stdin, hGetContents)
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure, exitSuccess)

import LexSwifty
import ParSwifty
import SkelSwifty
import PrintSwifty
import AbsSwifty
import EvalSwifty
import ErrM
import TypeChecker

type ParseFun a = [Token] -> Err a

myLLexer = myLexer

runFile :: (Print Program, Show Program) => ParseFun Program -> FilePath -> IO ()
runFile p f = readFile f >>= run p

run :: (Print Program, Show Program) => ParseFun Program -> String -> IO ()
run p s = let ts = myLLexer s in
               case p ts of
                  Bad s    -> do putStrLn "Parse Failed..."
                                 --putStrLn "Tokens:"
                                 --putStrLn $ show ts
                                 putStrLn s
                                 exitFailure
                  Ok tree  -> do --putStrLn "\nParse Successful!"
                                 --showTree tree
                                 checkProg tree
                                 execProg tree
                                 exitSuccess

showTree :: (Show Program, Print Program) => Program -> IO ()
showTree tree = do
                  putStrLn $ "\n[Abstract Syntax]\n\n" ++ show tree
                  putStrLn $ "\n[Linearized tree]\n\n" ++ printTree tree

main :: IO ()
main = do
      args <- getArgs
      mapM_ (runFile pProgram) args
