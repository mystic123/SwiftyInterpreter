{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module EvalSwifty where

import Data.Maybe
import AbsSwifty
import qualified Control.Monad.State as S
import Control.Monad.Reader
import qualified Data.Map as M

data ExprValue = I Integer | B Bool | None deriving (Eq, Ord, Show)

type Var = Ident
type State = M.Map Var ExprValue

instance Num ExprValue where
   (+) (I a) (I b) = I $ a + b
   (-) (I a) (I b) = I $ a - b
   (*) (I a) (I b) = I $ a * b
   abs (I a)
            | a  > 0 = I a
            | otherwise = I $ (-1) * a
   signum (I a)
               | a == 0 = I 0
               | a > 0 = I 1
               | otherwise = I $ -1
   fromInteger i = (I i)


getValue :: (S.MonadState State m) => Expr -> m ExprValue
getValue e = S.get >>= return . evalExpr e

execProg :: Program -> IO ()
execProg (Prog ([])) = return ()
execProg (Prog p) =  mapM_ (putStrLn . show) $ M.toList $ execProg' p M.empty
                        where
                           execProg' ([]) s = s
                           execProg' (f:fs) s = let s' = S.execState (execForm f) s
                                                   in execProg' fs s'

execForm :: (S.MonadState State m) => Form -> m ()
execForm (F_Stmt s) = execStmt s

execStmt :: (S.MonadState State m) => Stmt -> m ()
execStmt (S_Assign x e) = do
                           v <- getValue e
                           S.modify $ M.insert x v
                           return ()
execStmt w@(S_While e s) = do
                              B c <- getValue e
                              when c $ execStmt s >> execStmt w
execStmt (S_If e s) = do
                        B c <- getValue e
                        if c then execStmt s else return ()

execStmt (S_IfE e s1 s2) = do
                              B c <- getValue e
                              execStmt $ if c then s1 else s2
execStmt (S_Print e) = do
                        v <- getValue e
                        (putStrLn "print")

-- EXPRESSIONS
evalExpr :: (MonadReader State m) => Expr -> m ExprValue
evalExpr (E_Const c) = return $ evalConst c
evalExpr (E_Or x y)= do
                        B v1 <- evalExpr x
                        if v1 then return $ B v1 else evalExpr y
evalExpr (E_And x y) = do
                        B v1 <- evalExpr x
                        B v2 <- evalExpr y
                        return $ B $ v1 && v2
evalExpr (E_Eq x y) = do
                        v1 <- evalExpr x
                        v2 <- evalExpr y
                        return $ B $ v1 == v2
evalExpr (E_Neq x y) = do
                        v1 <- evalExpr x
                        v2 <- evalExpr y
                        return $ B $ v1 /= v2
evalExpr (E_Lt x y) = evalComp (<) x y
evalExpr (E_Gt x y) = evalComp (>) x y
evalExpr (E_Lte x y) = evalComp (<=) x y
evalExpr (E_Gte x y) = evalComp (>=) x y
evalExpr (E_Add x y) = evalArithm (+) x y
evalExpr (E_Subt x y) = evalArithm (-) x y
evalExpr (E_Mult x y) = evalArithm (*) x y
evalExpr (E_Div x y) = evalArithm (div) x y
evalExpr (E_Min x) = do
                        I v <- evalExpr x
                        return $ I $ (-1) * v
evalExpr (E_Neg x) = do
                        B v <- evalExpr x
                        return $ B $ not v
evalExpr (E_VarName x) = do
                           e <- asks $ M.lookup x
                           return $ fromMaybe (error "Undefined variable") e

evalComp :: (MonadReader State m) => (Integer -> Integer -> Bool) -> Expr -> Expr -> m ExprValue
evalComp f e1 e2 = do
                     I v1 <- evalExpr e1
                     I v2 <- evalExpr e2
                     return $ B $ f v1 v2

evalArithm :: (MonadReader State m) => (Integer -> Integer -> Integer) -> Expr -> Expr -> m ExprValue
evalArithm f e1 e2 = do
                        I v1 <- evalExpr e1
                        I v2 <- evalExpr e2
                        return $ I $ f v1 v2

evalConst :: Constant -> ExprValue
evalConst (Integer_Const n) = I n
evalConst (True_Const) = B True
evalConst (False_Const) = B False
