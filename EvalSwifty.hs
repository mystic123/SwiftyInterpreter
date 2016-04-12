{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module EvalSwifty where

import Data.Maybe
import AbsSwifty
import qualified Data.Map as M

data ExprValue = I Integer | B Bool | None

instance Show ExprValue where
   show (I n) = show n
   show (B b) = show b

type Loc = Integer
type Var = Ident
type FName = Ident
type Store = M.Map Loc ExprValue
type Env = (EnvV, EnvF)
type EnvV = M.Map Var Loc
type EnvF = M.Map FName ([PDecl], [Loc], Stmt)

type Cont = Store -> IO (Store)
type ContS = Store -> Env -> Cont
type ContE = ExprValue -> Cont
type ContD = Store -> Env -> Cont
type ContB = Store -> Cont
type ContR = ExprValue -> Cont

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
getLoc x s g = let l = M.lookup x $ fst g
               in if isJust l
                  then fromJust l
                  else newLoc s

newVar :: Ident -> Loc -> Env -> Env
newVar x l (gv, gf) = (M.insert x l gv, gf)

newFunc :: Ident -> [PDecl] -> [Loc] -> Stmt -> Env -> Env
newFunc f pd l s (gv, gf) = (gv, M.insert f (pd, l, s) gf)

emptyStore :: Store
emptyStore = M.empty

emptyEnv :: Env
emptyEnv = (M.empty, M.empty)

constM :: (Monad m) => a -> m (a)
constM = return

-- PROGRAM
execProg :: Program -> IO ()
execProg (Prog p) = do
                     s <- execProg' p emptyStore emptyEnv
                     mapM_ (putStrLn . show) $ M.toList s
                     where
                        execProg' :: [Stmt] -> Store -> Env -> IO Store
                        execProg' [] s g = return s
                        execProg' x s g = let
                                                k' = (\s' g' -> constM)
                                                kr' = (\n -> constM)
                                                k = execStmts x g k' kr'
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
evalDecl (D_Fun foo pd rtype stmt) g k = k'
                                          where
                                          k' :: Cont
                                          k' s = let
                                                    pd' = filter (not . isRef) pd
                                                    (locs, s') = getLocs pd' s
                                                    g' = newFunc foo pd locs stmt g
                                                 in k s' g' s'

isRef :: PDecl -> Bool
isRef (P_Decl _ (T_Ref _)) = True
isRef _ = False

getLocs :: [PDecl] -> Store -> ([Loc], Store)
getLocs [] s = ([], s)
getLocs (p:ps) s
               | isRef p = getLocs ps s
               | otherwise = let
                                 (locs, s') = getLocs ps s
                                 l = newLoc s'
                             in ([l] ++ locs, M.insert l 0 s')

-- BLOCK
execBlock :: Block -> Env -> ContB -> ContR -> Cont
execBlock (B_Block b) = execBlock' b
                           where
                              execBlock' :: [Stmt] -> Env -> ContB -> ContR -> Cont
                              execBlock' [] g k kr = (\s -> k s s)
                              execBlock' (b:bs) g k kr = execStmt b g (\s' g' -> execBlock' bs g' k kr) kr

-- STATEMENTS
execStmts :: [Stmt] -> Env -> ContS -> ContR -> Cont
execStmts [] g k kr = (\s -> k s g s)
execStmts (x:xs) g k kr = execStmt x g (\s' g' -> execStmts xs g' k kr) kr

execStmt :: Stmt -> Env -> ContS -> ContR -> Cont
execStmt w@(S_While e s) g k kr = evalExpr e g k'
                                 where
                                    k' :: ContE
                                    k' (B b) = if b
                                                then execStmt s g (\s' g' -> execStmt w g' k kr) kr
                                                else (\s -> k s g s)
execStmt (S_Decl d) g k kr = evalDecl d g (\s' g' -> k s' g')
execStmt (S_Block b) g k kr = execBlock b g (\s -> k s g) kr
execStmt (S_Expr e) g k kr = evalExpr (E_FuncCall e) g (\_ -> constM)
execStmt (S_If e s1) g k kr = evalExpr e g k'
                              where
                                 k' :: ContE
                                 k' (B b) = if b then execStmt s1 g k kr
                                             else (\s -> k s g s)
execStmt (S_IfE e s1 s2) g k kr = evalExpr e g k'
                                  where
                                    k' :: ContE
                                    k' (B b) = if b then execBlock s1 g (\s -> k s g) kr
                                                else execStmt s2 g k kr
execStmt (S_Return e) g k kr = evalExpr e g (\n -> kr n)
execStmt (S_Print e) g k kr = evalExpr e g k'
                              where
                                 k' :: ContE
                                 k' n s = do
                                             putStrLn $ "PRINT: " ++ show n
                                             putStrLn "ENV:"
                                             mapM_ (putStrLn . show) $ M.toList $ fst g
                                             mapM_ (putStrLn . show) $ M.toList $ snd g
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
                                       l = M.lookup x $ fst g
                                       n = M.lookup (fromMaybe (error "Undefined variable") l) s
                                    in k (fromMaybe (error "Undefined variable") n) s)
evalExpr (E_FuncCall (Fun_Call foo args)) g@(gv, gf) k = let
                                          (pd, l, stmt) = fromMaybe (error "Undefined funcion") $ M.lookup foo gf
                                          --g' = modifyEnvFunc pd l args g
                                       in callFunc args pd l stmt g k--execStmt stmt g' (\_ _ -> k None) k

callFunc :: [Expr] -> [PDecl] -> [Loc] -> Stmt -> Env -> ContE -> Cont
callFunc [] pd locs stmt g k = execStmt stmt g (\_ _ -> k None) k
callFunc (a:as) (p:ps) locs@(l:ls) stmt g@(gv,gf) k
                                                   | isRef p = let
                                                                  (P_Decl x _) = p
                                                                  (E_VarName y) = a
                                                                  l' = fromMaybe (error "Undefined variable") $ M.lookup y gv
                                                                  gv' = M.insert x l' gv
                                                               in callFunc as ps locs stmt (gv', gf) k
                                                   | otherwise = let
                                                                    (P_Decl x _) = p
                                                                    gv' = M.insert x l gv
                                                                 in evalExpr a g (\n -> \s -> callFunc as ps ls stmt (gv', gf) (\n -> k n) (M.insert l n s))
{-
modifyEnvFunc :: [PDecl] -> [Loc] -> [Expr] -> Env -> Env
modifyEnvFunc [] _ _ g = g
modifyEnvFunc (p:ps) (l:ls) args@(a:as) g@(gv, gf)
                                          | isRef p = let
                                                         (P_Decl x _) = p
                                                         (E_VarName y) = a
                                                         loc = fromMaybe (error "Undefined variable") $ M.lookup y gv
                                                         gv' = M.insert x loc gv
                                                      in modifyEnvFunc ps (l:ls) as (gv', gf)
                                          | otherwise = let
                                                            (P_Decl x _) = p
                                                            gv' = M.insert x l gv
                                                        in modifyEnvFunc ps ls args (gv', gf)
-}
evalComp :: (ExprValue -> ExprValue -> Bool) -> Expr -> Expr -> Env -> ContE -> Cont
evalComp f e1 e2 g k = evalExpr e1 g (\v1 -> evalExpr e2 g (\v2 -> k $ B $ f v1 v2))

evalArithm :: (ExprValue -> ExprValue -> ExprValue) -> Expr -> Expr -> Env -> ContE -> Cont
evalArithm f e1 e2 g k = evalExpr e1 g (\v1 -> evalExpr e2 g (\v2 -> k $ f v1 v2))

evalConst :: Constant -> ExprValue
evalConst (Integer_Const n) = I n
evalConst (True_Const) = B True
evalConst (False_Const) = B False
