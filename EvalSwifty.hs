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

data ExprValue = I Integer | B Bool

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
type ContD = Store -> Env -> Cont
type ContB = Store -> Cont

instance Eq ExprValue where
   I a == I b = a == b
   B a == B b = a == b

instance Ord ExprValue where
   I a <= I b = a <= b

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


exprDiv :: ExprValue -> ExprValue -> ExprValue
exprDiv (I a) (I b) = I $ div a b

newLoc :: Store -> Loc
newLoc s = if null s then 0 else (fst $ M.findMax s) + 1

getLoc :: Store -> Env -> Var -> Loc
getLoc s g x = let l = M.lookup x g
               in if isJust l
                  then fromJust l
                  else getLoc s (M.insert x (newLoc s) g) x

newVar :: Ident -> Loc -> Env -> Env
newVar = M.insert

execProg :: Program -> IO ()
execProg (Prog p) = do
                     s <- execProg' p M.empty M.empty
                     mapM_ (putStrLn . show) $ M.toList s
                     where
                        execProg' :: [Stmt] -> Store -> Env -> IO Store
                        execProg' [] s g = return s
                        execProg' (f:fs) s g = do
                                                execStmt f s g (\s' -> execProg' fs s' g) s

-- DECLARATIONS
evalDecl :: Decl -> Store -> Env -> ContD -> Cont
evalDecl (D_Var x e) s g k = evalExpr e s g k' s
                              where
                                 k' :: ContE
                                 k' n s' = let l = newLoc s
                                               g' = newVar x l g
                                               s'' = M.insert l n s'
                                                in k s' g'

-- BLOCK
execBlock :: Block -> Store -> Env -> Cont -> Cont
execBlock (B_Block b) = execBlock' b
                           where
                              execBlock' :: [Stmt] -> Store -> Env -> Cont -> Cont
                              execBlock' [] s g k = k
                              execBlock' (b:bs) s g k = execStmt b s g (\s' -> execBlock' bs s' g k s)

-- STATEMENTS
execStmt :: Stmt -> Store -> Env -> Cont -> Cont
{-execStmt (S_Assign x e) s g k = evalExpr e s g k'
                                 where
                                    k' :: ContE
                                    k' n s' = k $ M.insert (getLoc s g x) n s'
-}
--execStmt w@(S_While e s) = B c <- getValue e
--                              when c $ execStmt s >> execStmt w
execStmt (S_Decl d) s g k = evalDecl d s g (\s' g' -> k)
execStmt (S_Block b) s g k = execBlock b s g k
execStmt (S_If e s1) s g k = evalExpr e s g k'
                              where
                                 k' :: ContE
                                 k' (B b) = if b then execStmt s1 s g k
                                             else k
execStmt (S_IfE e s1 s2) s g k = evalExpr e s g k'
                                  where
                                    k' :: ContE
                                    k' (B b) = if b then execBlock s1 s g k
                                                else execStmt s2 s g k
execStmt (S_Print e) s g k = evalExpr e s g k'
                              where
                                 k' :: ContE
                                 k' n s' = do
                                             putStrLn $ show n
                                             putStrLn $ show $ null g
                                             mapM_ (putStrLn . show) $ M.toList g
                                             k s'

-- EXPRESSIONS
evalExpr :: Expr -> Store -> Env -> ContE -> Cont
evalExpr (E_Const c) s g k = k $ evalConst c
evalExpr (E_Or x y) s g k = evalExpr x s g k'
                              where
                                 k' :: ContE
                                 k' (B b) = if b then k (B b)
                                             else evalExpr y s g k
evalExpr (E_And x y) s g k = evalExpr x s g k'
                              where
                                 k' :: ContE
                                 k' (B b1) = evalExpr y s g (\(B b2) -> k $ B $ b1 && b2)
evalExpr (E_Eq x y) s g k = evalExpr x s g k'
                              where
                                 k' :: ContE
                                 k' v1 = evalExpr y s g (\v2 -> k $ B $ v1 == v2)
evalExpr (E_Neq x y) s g k = evalExpr x s g k'
                              where
                                 k' :: ContE
                                 k' v1 = evalExpr y s g (\v2 -> k $ B $ v1 /= v2)
evalExpr (E_Lt x y) s g k = evalComp (<) x y s g k
evalExpr (E_Gt x y) s g k = evalComp (>) x y s g k
evalExpr (E_Lte x y) s g k = evalComp (<=) x y s g k
evalExpr (E_Gte x y) s g k = evalComp (>=) x y s g k
evalExpr (E_Add x y) s g k = evalArithm (+) x y s g k
evalExpr (E_Subt x y) s g k = evalArithm (-) x y s g k
evalExpr (E_Mult x y) s g k= evalArithm (*) x y s g k
evalExpr (E_Div x y) s g k= evalArithm (exprDiv) x y s g k
evalExpr (E_Min x) s g k = evalExpr x s g (\(I n) -> k $ I $ (-1)*n)
evalExpr (E_Neg x) s g k = evalExpr x s g (\(B b) -> k $ B $ not b)
evalExpr (E_VarName x) s g k = let Just l = M.lookup x g
                                   n = M.lookup l s
                                 in k $ fromMaybe (error "Undefined variable") n

evalComp :: (ExprValue -> ExprValue -> Bool) -> Expr -> Expr -> Store -> Env -> ContE -> Cont
evalComp f e1 e2 s g k = evalExpr e1 s g (\v1 -> evalExpr e2 s g (\v2 -> k $ B $ f v1 v2))

evalArithm :: (ExprValue -> ExprValue -> ExprValue) -> Expr -> Expr -> Store -> Env -> ContE -> Cont
evalArithm f e1 e2 s g k = evalExpr e1 s g (\v1 -> evalExpr e2 s g (\v2 -> k $ f v1 v2))

evalConst :: Constant -> ExprValue
evalConst (Integer_Const n) = I n
evalConst (True_Const) = B True
evalConst (False_Const) = B False
