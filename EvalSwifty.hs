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
type ContS = Store -> Env -> Cont
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

getLoc :: Var -> Store -> Env -> Loc
getLoc x s g = let l = M.lookup x g
               in if isJust l
                  then fromJust l
                  else newLoc s

newVar :: Ident -> Loc -> Env -> Env
newVar = M.insert

execProg :: Program -> IO ()
execProg (Prog p) = do
                     s <- execProg' p M.empty M.empty
                     mapM_ (putStrLn . show) $ M.toList s
                     where
                        execProg' :: [Stmt] -> Store -> Env -> IO Store
                        execProg' [] s g = return s
                        execProg' x s g = let
                                                k = execStmts x g (\s' g' -> (\s -> return s))
                                          in k s

-- DECLARATIONS
evalDecl :: Decl -> Env -> ContD -> Cont
evalDecl (D_Var x e) g k = evalExpr e g k'
                              where
                                 k' :: ContE
                                 k' n s = let
                                             l = getLoc x s g
                                             g' = newVar x l g
                                             s' = M.insert l n s
                                          in k s' g' s'

-- BLOCK
execBlock :: Block -> Env -> ContB -> Cont
execBlock (B_Block b) = execBlock' b
                           where
                              execBlock' :: [Stmt] -> Env -> ContB -> Cont
                              execBlock' [] g k = (\s -> k s s)
                              execBlock' (b:bs) g k = execStmt b g (\s' g' -> execBlock' bs g' k )

-- STATEMENTS
execStmts :: [Stmt] -> Env -> ContS -> Cont
execStmts [] g k = (\s -> k s g s)
execStmts (x:xs) g k = execStmt x g (\s' g' -> execStmts xs g' k)

execStmt :: Stmt -> Env -> ContS -> Cont
execStmt w@(S_While e s) g k = evalExpr e g k'
                                 where
                                    k' :: ContE
                                    k' (B b) = if b
                                                then execStmt s g (\s' g' -> execStmt w g' k)
                                                else (\s -> k s g s)
execStmt (S_Decl d) g k = evalDecl d g (\s' g' -> k s' g')
execStmt (S_Block b) g k = execBlock b g (\s -> k s g)
execStmt (S_If e s1) g k = evalExpr e g k'
                              where
                                 k' :: ContE
                                 k' (B b) = if b then execStmt s1 g k
                                             else (\s -> return s)
execStmt (S_IfE e s1 s2) g k = evalExpr e g k'
                                  where
                                    k' :: ContE
                                    k' (B b) = if b then execBlock s1 g (\s -> k s g)
                                                else execStmt s2 g k
execStmt (S_Print e) g k = evalExpr e g k'
                              where
                                 k' :: ContE
                                 k' n s = do
                                             putStrLn $ "PRINT: " ++ show n
                                             putStrLn "ENV:"
                                             mapM_ (putStrLn . show) $ M.toList g
                                             putStrLn "----------\nSTORE:"
                                             mapM_ (putStrLn . show) $ M.toList s
                                             putStrLn "-----------"
                                             k s g s

-- EXPRESSIONS
evalExpr :: Expr -> Env -> ContE -> Cont
evalExpr (E_Const c) g k = k $ evalConst c
evalExpr (E_Or x y) g k = evalExpr x g k'
                              where
                                 k' :: ContE
                                 k' (B b) = if b then k (B b)
                                             else evalExpr y g k
evalExpr (E_And x y) g k = evalExpr x g k'
                              where
                                 k' :: ContE
                                 k' (B b1) = evalExpr y g (\(B b2) -> k $ B $ b1 && b2)
evalExpr (E_Eq x y) g k = evalExpr x g k'
                              where
                                 k' :: ContE
                                 k' v1 = evalExpr y g (\v2 -> k $ B $ v1 == v2)
evalExpr (E_Neq x y) g k = evalExpr x g k'
                              where
                                 k' :: ContE
                                 k' v1 = evalExpr y g (\v2 -> k $ B $ v1 /= v2)
evalExpr (E_Lt x y) g k = evalComp (<) x y g k
evalExpr (E_Gt x y) g k = evalComp (>) x y g k
evalExpr (E_Lte x y) g k = evalComp (<=) x y g k
evalExpr (E_Gte x y) g k = evalComp (>=) x y g k
evalExpr (E_Add x y) g k = evalArithm (+) x y g k
evalExpr (E_Subt x y) g k = evalArithm (-) x y g k
evalExpr (E_Mult x y) g k= evalArithm (*) x y g k
evalExpr (E_Div x y) g k= evalArithm (exprDiv) x y g k
evalExpr (E_Min x) g k = evalExpr x g (\(I n) -> k $ I $ (-1)*n)
evalExpr (E_Neg x) g k = evalExpr x g (\(B b) -> k $ B $ not b)
evalExpr (E_VarName x) g k = (\s -> let
                                       l = M.lookup x g
                                       n = M.lookup (fromMaybe (error "Undefined variable") l) s
                                    in k (fromMaybe (error "Undefined variable") n) s)

evalComp :: (ExprValue -> ExprValue -> Bool) -> Expr -> Expr -> Env -> ContE -> Cont
evalComp f e1 e2 g k = evalExpr e1 g (\v1 -> evalExpr e2 g (\v2 -> k $ B $ f v1 v2))

evalArithm :: (ExprValue -> ExprValue -> ExprValue) -> Expr -> Expr -> Env -> ContE -> Cont
evalArithm f e1 e2 g k = evalExpr e1 g (\v1 -> evalExpr e2 g (\v2 -> k $ f v1 v2))

evalConst :: Constant -> ExprValue
evalConst (Integer_Const n) = I n
evalConst (True_Const) = B True
evalConst (False_Const) = B False
