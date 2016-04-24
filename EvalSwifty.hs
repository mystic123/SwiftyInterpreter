{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module EvalSwifty where

import Data.Maybe
import AbsSwifty
import ErrM
import Data.List
import qualified Data.Map as M

data ExprValue = I Integer | B Bool | A Type [Loc] | T [ExprValue] | S (M.Map Var Loc) | L [ExprValue]

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
type ContA = [ExprValue] -> Cont

instance Eq ExprValue where
   I a == I b     = a == b
   B a == B b     = a == b
   A t1 v1 == A t2 v2
                     | t1 /= t2 = False
                     | otherwise = v1 == v2
   T v1 == T v2   = v1 == v2

instance Ord ExprValue where
   I a <= I b = a <= b

instance Num ExprValue where
   (+) (I a) (I b)       = I $ a + b
   --(+) (A T_Int a) (I b) = A T_Int $ map (+ (I b)) a
   (-) (I a) (I b)       = I $ a - b
   --(-) (A T_Int a) (I b) = A T_Int $ map ((-) (I b)) a
   (*) (I a) (I b)       = I $ a * b
   --(*) (A T_Int a) (I b) = A T_Int $ map (* (I b)) a
   abs (I a)
            | a  > 0 = I a
            | otherwise  = I $ (-1) * a
   signum (I a)
               | a == 0  = I 0
               | a > 0   = I 1
               | otherwise = I $ -1
   fromInteger i = (I i)

instance Show ExprValue where
   show (I n)     = show n
   show (B b)     = show b
   show (A t l)   = "A: {" ++ (intercalate "," $ map show l) ++ "}"
   show (T l)     = "T: (" ++ (intercalate "," $ map show l) ++ ")"
   show (L l)     = "L: {" ++ (intercalate "," $ map show l) ++ "}"
   show (S str)   = show $ M.toList str

-- HELPER FUNCTIONS
exprDiv :: ExprValue -> ExprValue -> ExprValue
exprDiv (I a) (I b) = I $ div a b
--exprDiv (A T_Int a) (I b) = A T_Int $ map (exprDiv (I b)) a

newLoc :: Store -> Loc
newLoc s = if null s then 0 else (fst $ M.findMax s) + 1

getLoc :: Var -> Store -> Env -> Loc
getLoc x s g = fromMaybe (undefVar x) (M.lookup x $ fst g)

newVar :: Var -> Loc -> Env -> Env
newVar x l (gv, gf) = (M.insert x l gv, gf)

newVars :: [Var] -> [Loc] -> Env -> Env
newVars [] [] g = g
newVars (x:xs) (l:ls) (gv, gf) = newVars xs ls (M.insert x l gv, gf)

newFunc :: Var -> [PDecl] -> [Loc] -> Stmt -> Env -> Env
newFunc f pd l s (gv, gf) = (gv, M.insert f (pd, l, s) gf)

emptyStore :: Store
emptyStore = M.empty

emptyEnv :: Env
emptyEnv = (M.empty, M.empty)

constM :: (Monad m) => a -> m (a)
constM = return

undefVar (Ident x) = error $ concat ["Undefined variable: ", show x]

undefFunc (Ident f) = error $ concat ["Undefined function: ", show f]

isRef :: PDecl -> Bool
isRef (P_Decl _ (T_Ref _)) = True
isRef _ = False

getLocs :: [PDecl] -> Store -> ([Loc], Store)
getLocs [] s = ([], s)
getLocs (p:ps) s
               | isRef p = getLocs ps s
               | otherwise = ((l:locs), M.insert l 0 s')
                              where
                                 (locs, s') = getLocs ps s
                                 l = newLoc s'

getLocs2 :: [ExprValue] -> Store -> ([Loc], Store)
getLocs2 [] s = ([], s)
getLocs2 (v:vs) s = case v of
                     (L vals) -> (l:locs', M.insert l arr s''')
                                    where
                                       (locs, s') = getLocs2 vals s
                                       l = newLoc s'
                                       arr = A T_Int $ reverse locs
                                       s'' = M.insert l arr s'
                                       (locs',s''') = getLocs2 vs s''
                     _ -> (l:locs, M.insert l v s')
                           where
                              (locs, s') = getLocs2 vs s
                              l = newLoc s'

getType :: ExprValue -> Type
getType (I _) = T_Int
getType (B _) = T_Bool
getType (A t _) = T_Arr t

-- PROGRAM
execProg :: Program -> IO ()
execProg (Prog p) = do
                     execProg' p emptyStore emptyEnv
                     return ()
                     --mapM_ (putStrLn . show) $ M.toList s
                     where
                        execProg' :: [Stmt] -> Store -> Env -> IO Store
                        execProg' [] s g = return s
                        execProg' x s g = k s
                                          where
                                             k' = (\s' g' -> constM)
                                             kr' = (\n -> constM)
                                             k = execStmts x g k' kr'

-- DECLARATIONS
evalDecl :: Decl -> Env -> ContD -> Cont
evalDecl (D_Var x e) g k = evalExpr e g k'
                              where
                                 k' :: ContE
                                 k' (L vals) s = let
                                                   (locs, s') = getLocs2 vals s
                                                   l = newLoc s'
                                                   s'' = M.insert l (A T_Int $ reverse locs) s'
                                                   g' = newVar x l g
                                                 in k s'' g' s''
                                 k' n s = let
                                             l = newLoc s
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
evalDecl (D_Proc proc pd stmt) g k = k'
                                       where
                                       k' :: Cont
                                       k' s = let
                                                 pd' = filter (not . isRef) pd
                                                 (locs, s') = getLocs pd' s
                                                 g' = newFunc proc pd locs stmt g
                                              in k s' g' s'
evalDecl (D_MVar x xs (Tup e es)) g k = evalExprList (x:xs) (e:es) [] g k
                                          where
                                             evalExprList :: [Var] -> [Expr] -> [ExprValue] -> Env -> ContD -> Cont
                                             evalExprList x [] y g k = multVarDecl x (reverse y) g k
                                             evalExprList x (e:es) y g k = evalExpr e g (\n -> evalExprList x es (n:y) g k)
                                             multVarDecl :: [Var] -> [ExprValue] -> Env -> ContD -> Cont
                                             multVarDecl x y g k s = let
                                                                        (locs, s') = getLocs2 y s
                                                                        g' = newVars x locs g
                                                                     in k s' g' s'
-- BLOCK
execBlock :: Block -> Env -> ContB -> ContR -> Cont
execBlock (B_Block b) = execBlock' b
                           where
                              execBlock' :: [Stmt] -> Env -> ContB -> ContR -> Cont
                              execBlock' [] g k kr = (\s -> k s s)
                              execBlock' (b:bs) g k kr = execStmt b g (\s' g' -> execBlock' bs g' k kr) kr

assignVar :: Var -> ExprValue -> Env -> Store -> Store
assignVar x n (gv,gf) s = M.insert l n s
                     where
                        l = fromMaybe (undefVar x) $ M.lookup x gv

assignArr :: Var -> ExprValue -> ExprValue -> Env -> Store -> Store
assignArr x i n (gv,gf) s = M.insert l n s
                           where
                              al = fromMaybe (undefVar x) $ M.lookup x gv
                              (A _ arr) = fromMaybe (undefVar x) $ M.lookup al s
                              (I i') = i
                              l = (!!) arr $fromInteger i'

-- STATEMENTS
execStmts :: [Stmt] -> Env -> ContS -> ContR -> Cont
execStmts [] g k kr = (\s -> k s g s)
execStmts (x:xs) g k kr = execStmt x g (\s' g' -> execStmts xs g' k kr) kr

execStmt :: Stmt -> Env -> ContS -> ContR -> Cont
execStmt (S_Block b) g k kr = execBlock b g (\s -> k s g) kr
execStmt (S_Decl d) g k kr = evalDecl d g (\s' g' -> k s' g')
execStmt (S_Assign x e) g k kr = evalExpr e g k'
                                 where
                                    k' :: ContE
                                    k' n s = let
                                                s' = assignVar x n g s
                                             in k s' g s'
execStmt (S_ArrAss x (Arr_Sub i) e) g k kr = evalExpr i g (\n -> evalExpr e g (\m -> k' n m))
                                             where
                                                k' i n s = let
                                                            s' = assignArr x i n g s
                                                           in k s' g s'
execStmt w@(S_While e s) g k kr = evalExpr e g k'
                                 where
                                    k' :: ContE
                                    k' (B b) = if b
                                                then execStmt s g (\s' g' -> execStmt w g' k kr) kr
                                                else (\s -> k s g s)
execStmt (S_For x e stmt) g k kr = execFor x e stmt g k kr
execStmt (S_If e s1) g k kr = evalExpr e g k'
                              where
                                 k' :: ContE
                                 k' (B b) = if b
                                             then execStmt s1 g k kr
                                             else (\s -> k s g s)
execStmt (S_IfE e s1 s2) g k kr = evalExpr e g k'
                                  where
                                    k' :: ContE
                                    k' (B b) = if b
                                                then execBlock s1 g (\s -> k s g) kr
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
                                             putStrLn "-----------\n"
                                             k s g s
execStmt (S_Expr e) g k kr = evalExpr (E_FuncCall e) g (\_ -> constM)

{-
execAssign :: ExprValue -> Acc -> Env -> ContS -> ContR -> Cont
execAssign n (A_Iden x) g k kr s = k $ M.insert (getLoc x) n s
execAssign n (A_Arr a (Arr_Sub e)) = evalExpr e g (\(I n') -> 


--modifyArray :: ExprValue -> Acc -> ExprValue
modifyArray arr i val = modifyArray' [] arr i val
                        where
                           --modifyArray' :: ExprValue -> ExprValue -> Acc -> ExprValue
                           modifyArray' r (A_Iden x) i val g s = fromMaybe (undefVar x) $ M.looku
                           modifyArray' r (A _ vals) (A_Arr a (Arr_Sub e))


evalAcc acc g k = evalAcc' [] acc g k
                  where
                     evalAcc' (A_Iden x) 
                     evalAcc' es (A_Arr x e) = evalAcc' (e:es) x
-}
execFor :: Var -> Expr -> Stmt -> Env -> ContS -> ContR -> Cont
execFor x e stmt g k kr = evalExpr e g (\(A _ arr) -> execFor' x arr stmt g k kr)
                           where
                              execFor' :: Var -> [Loc] -> Stmt -> Env -> ContS -> ContR -> Cont
                              execFor' x [] stmt g k kr = (\s -> k s g s)
                              execFor' x (l:ls) stmt g@(gv,gf) k kr = let
                                                                           block = (B_Block [stmt])
                                                                           g' = (M.insert x l gv,gf)
                                                                        in execBlock block g' (\s -> execFor' x ls stmt g k kr) kr


-- EXPRESSIONS
callFunc :: [Expr] -> [PDecl] -> [Loc] -> Stmt -> Env -> ContE -> Cont
callFunc [] _ _ stmt g k = execStmt stmt g (\s _ -> constM) k
callFunc (a:as) (p:ps) locs@(l:ls) stmt g@(gv,gf) k
                                                   | isRef p = callFunc as ps locs stmt (gv', gf) k
                                                   | otherwise = evalExpr a g k'
                                                                  where
                                                                     (P_Decl x _) = p
                                                                     (E_VarName y) = a
                                                                     l' = fromMaybe (undefVar y) $ M.lookup y gv
                                                                     gv' = M.insert x l' gv
                                                                     gv'' = M.insert x l gv
                                                                     k' :: ContE
                                                                     k' n s = callFunc as ps ls stmt (gv'', gf) (\n -> k n) $ M.insert l n s

evalExprList :: [Expr] -> Env -> ContA -> Cont
evalExprList l g k = evalExprList' l [] g k
                     where
                        evalExprList' [] v g k = k $ reverse v
                        evalExprList' (e:es) v g k = evalExpr e g (\n -> evalExprList' es (n:v) g k)

evalTuple :: [Expr] -> Env -> ContE -> Cont
evalTuple l g k = evalExprList l g (\vals -> k $ L $ reverse vals)

evalArray :: [Expr] -> Env -> ContE -> Cont
evalArray l g k = evalExprList l g (\vals -> k $ L $ reverse vals)

evalExpr :: Expr -> Env -> ContE -> Cont
evalExpr (E_TupI (Tup e es)) g k = evalTuple (e:es) g k
evalExpr (E_ArrI (Arr es)) g k = evalArray es g k
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
evalExpr (E_Mult x y) g k = evalArithm (*) x y g k
evalExpr (E_Div x y) g k = evalArithm (exprDiv) x y g k
evalExpr (E_Min x) g k = evalExpr x g (\(I n) -> k $ I $ (-1)*n)
evalExpr (E_Neg x) g k = evalExpr x g (\(B b) -> k $ B $ not b)
evalExpr (E_VarName x) (gv, gf) k = (\s -> let
                                       l = fromMaybe (undefVar x) $ M.lookup x gv
                                       n = fromMaybe (undefVar x) $ M.lookup l s
                                       v = case n of
                                             A _ locs -> getArray locs s
                                             _ -> n
                                    in k v s)
evalExpr (E_FuncCall (Fun_Call foo args)) g k = callFunc args pd l stmt g k
                                                where
                                                   (pd, l, stmt) = fromMaybe (undefFunc foo) $ M.lookup foo $ snd g
--evalExpr (E_ArrS e (Arr_Sub i)) g k = evalExpr e g (\(A _ v) -> evalExpr i g (\(I i) -> k $ (!!) v $ fromInteger i))

getArray :: [Loc] -> Store -> ExprValue
getArray locs s = getArray' [] locs s
                  where
                     getArray' :: [ExprValue] -> [Loc] -> Store -> ExprValue
                     getArray' r [] _ = L $ reverse r
                     getArray' r (l:ls) s = case l' of
                                             A _ locs' -> let
                                                            arr = getArray locs' s
                                                          in getArray' (arr:r) ls s
                                             _ -> getArray' (l':r) ls s
                                             where
                                                Just l' = M.lookup l s

evalComp :: (ExprValue -> ExprValue -> Bool) -> Expr -> Expr -> Env -> ContE -> Cont
evalComp f e1 e2 g k = evalExpr e1 g (\v1 -> evalExpr e2 g (\v2 -> k $ B $ f v1 v2))

evalArithm :: (ExprValue -> ExprValue -> ExprValue) -> Expr -> Expr -> Env -> ContE -> Cont
evalArithm f e1 e2 g k = evalExpr e1 g
                           (\v1 -> evalExpr e2 g
                              (\v2 -> k $ if v2 /= 0 then f v1 v2
                                             else (error "Division by zero!")))

evalConst :: Constant -> ExprValue
evalConst (Integer_Const n) = I n
evalConst (True_Const) = B True
evalConst (False_Const) = B False
