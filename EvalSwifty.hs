{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module EvalSwifty where

import Data.Maybe
import AbsSwifty
--import Control.Monad.Reader
--import qualified Control.Monad.State as S
--import qualified Control.Monad.Cont as C
import qualified Data.Map as M

data ExprValue = I Integer | B Bool deriving (Eq, Ord)

instance Show ExprValue where
   show (I n) = show n
   show (B b) = show b

type Loc = Integer
type Var = Ident
type FName = Ident
type Store = M.Map Loc ExprValue
type Env = M.Map Var Loc

type Cont = Store -> IO (Store)
type ContE = ExprValue -> Cont

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


newLoc :: Store -> Loc
newLoc s = if null s then 0 else (fst $ M.findMax s) + 1

getLoc :: Store -> Env -> Var -> Loc
getLoc s g x = let l = M.lookup x g
               in if isJust l
                  then fromJust l
                  else getLoc s (M.insert x (newLoc s) g) x

execProg :: Program -> IO ()
execProg (Prog p) = do
                     s <- execProg' p M.empty M.empty
                     mapM_ (putStrLn . show) $ M.toList s
                     where
                        execProg' :: [Form] -> Store -> Env -> IO Store
                        execProg' [] s g = return s
                        execProg' (f:fs) s g = do
                                                execForm f s g (\s' -> execProg' fs s' g) s

execForm :: Form -> Store -> Env -> Cont -> Cont
execForm (F_Stmt stmt) = execStmt stmt

-- STATEMENTS
execStmt :: Stmt -> Store -> Env -> Cont -> Cont
execStmt (S_Assign x e) s g k = evalExpr e s g k'
                                 where
                                    k' :: ContE
                                    k' n s' = k $ M.insert (getLoc s g x) n s'
{-
execStmt w@(S_While e s) = do
                              B c <- getValue e
                              when c $ execStmt s >> execStmt w
execStmt (S_If e s) = do
                        B c <- getValue e
                        if c then execStmt s else return ()
execStmt (S_IfE e s1 s2) = do
                              B c <- getValue e
                              execStmt $ if c then s1 else s2
-}
execStmt (S_Print e) s g k = evalExpr e s g k'
                              where
                                 k' :: ContE
                                 k' n s' = do
                                             putStrLn $ show n
                                             return s'

-- EXPRESSIONS
evalExpr :: Expr -> Store -> Env -> ContE -> Cont
evalExpr (E_Const c) s g k = k $ evalConst c
{-
evalExpr k (E_Or x y)= do
                        B v1 <- evalExpr x
                        if v1 then return $ B v1 else evalExpr y
evalExpr k (E_And x y) = do
                        B v1 <- evalExpr x
                        B v2 <- evalExpr y
                        return $ B $ v1 && v2
evalExpr k (E_Eq x y) = do
                        v1 <- evalExpr x
                        v2 <- evalExpr y
                        return $ B $ v1 == v2
evalExpr k (E_Neq x y) = do
                        v1 <- evalExpr x
                        v2 <- evalExpr y
                        return $ B $ v1 /= v2
evalExpr k (E_Lt x y) = evalComp (<) x y
evalExpr k (E_Gt x y) = evalComp (>) x y
evalExpr k (E_Lte x y) = evalComp (<=) x y
evalExpr k (E_Gte x y) = evalComp (>=) x y
evalExpr k (E_Add x y) = evalArithm (+) x y
evalExpr k (E_Subt x y) = evalArithm (-) x y
evalExpr k (E_Mult x y) = evalArithm (*) x y
evalExpr k (E_Div x y) = evalArithm (div) x y
evalExpr k (E_Min x) = do
                        I v <- evalExpr k x
                        return $ I $ (-1) * v
evalExpr k (E_Neg x) = do
                        B v <- evalExpr k x
                        return $ B $ not v
evalExpr k (E_VarName x) = do
                           e <- asks $ M.lookup x
                           return $ fromMaybe (error "Undefined variable") e
evalComp :: (Integer -> Integer -> Bool) -> Expr -> Expr -> IO ExprValue
evalComp f e1 e2 = do
                     I v1 <- evalExpr e1
                     I v2 <- evalExpr e2
                     return $ B $ f v1 v2

evalArithm :: (MonadReader State m) => (Integer -> Integer -> Integer) -> Expr -> Expr -> m ExprValue
evalArithm f e1 e2 = do
                        I v1 <- evalExpr e1
                        I v2 <- evalExpr e2
                        return $ I $ f v1 v2

-}
evalConst :: Constant -> ExprValue
evalConst (Integer_Const n) = I n
evalConst (True_Const) = B True
evalConst (False_Const) = B False
