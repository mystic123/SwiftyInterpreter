{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module EvalSwifty where

import Data.Maybe
import AbsSwifty
import Data.List --intercalate
import qualified Data.Map as M

type AArray = M.Map Int Loc
type Struct = M.Map Var Loc
type StructVal = M.Map Var ExprValue

data ExprValue = I Integer | B Bool | A AArray | T [ExprValue] | S Struct | L [ExprValue] | Str StructVal | None

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
type ContL = Loc -> Cont

instance Eq ExprValue where
   I a == I b     = a == b
   B a == B b     = a == b
   A v1 == A v2   = v1 == v2
   T v1 == T v2   = v1 == v2

instance Ord ExprValue where
   I a <= I b = a <= b

instance Num ExprValue where
   (+) (I a) (I b)       = I $ a + b
   (-) (I a) (I b)       = I $ a - b
   (*) (I a) (I b)       = I $ a * b
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
   show (A l)     = "A: {" ++ (intercalate "," $ map show $ M.elems l) ++ "}"
   show (T l)     = "T: (" ++ (intercalate "," $ map show l) ++ ")"
   show (L l)     = "{" ++ (intercalate "," $ map show l) ++ "}"
   show (S str)   = show $ M.toList str
   show (Str s)   = show $ M.toList s
   show None      = "None"

-- HELPER FUNCTIONS
exprDiv :: ExprValue -> ExprValue -> ExprValue
exprDiv (I a) (I b) = I $ div a b

newLoc :: Store -> Loc
newLoc s = if null s then 0 else (fst $ M.findMax s) + 1

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

indexOutR = error "Runtime error: Index out of range"
divByZero = error "Runtime error: Division by zero"
notReturn = error "Runtime error: Function did not return any value"

isRef :: PDecl -> Bool
isRef (P_Decl _ (T_Ref _)) = True
isRef _ = False

arrayFromList :: [Loc] -> ExprValue
arrayFromList locs = A $ M.fromList $ zip [0..] locs

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
                                       arr = arrayFromList locs
                                       s'' = M.insert l arr s'
                                       (locs',s''') = getLocs2 vs s''
                     (Str str) -> (l:locs', M.insert l str' s''')
                                 where
                                    (locs, s') = getLocs2 (M.elems str) s
                                    l = newLoc s'
                                    str' = S $ M.fromList $ zip (M.keys str) locs
                                    s'' = M.insert l str' s'
                                    (locs', s''') = getLocs2 vs s''
                     _ -> (l:locs, M.insert l v s')
                           where
                              (locs, s') = getLocs2 vs s
                              l = newLoc s'

(!!!) :: ExprValue -> ExprValue -> Loc
(!!!) (A m) (I i) = let
                        i' = fromInteger i
                    in fromMaybe indexOutR $ M.lookup i' m

-- PROGRAM
execProg :: Program -> IO ()
execProg (Prog p) = do
                     execProg' p emptyStore emptyEnv
                     return ()
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
                                                   l = newLoc s
                                                   g' = newVar x l g
                                                   s' = M.insert l None s
                                                 in allocArray l vals g' k s'
                                 k' (Str str) s = let
                                                   l = newLoc s
                                                   g' = newVar x l g
                                                   s' = M.insert l None s
                                                  in allocStruct l str g' k s'
                                 k' n s = let
                                             l = newLoc s
                                             g' = newVar x l g
                                             s' = M.insert l n s
                                          in k s' g' s'
evalDecl (D_Str x) g k = k'
                        where
                           k' :: Cont
                           k' s = let
                                    l = newLoc s
                                    s' = M.insert l (S M.empty) s
                                    g' = newVar x l g
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
evalDecl (D_MVar x xs t) g k = evalExpr (E_TupI t) g (\(T es) -> multVarDecl (x:xs) es g k)
                                          where
                                             multVarDecl :: [Var] -> [ExprValue] -> Env -> ContD -> Cont
                                             multVarDecl x y g k s = let
                                                                        (locs, s') = getLocs2 y s
                                                                        g' = newVars x locs g
                                                                     in k s' g' s'

allocArray :: Loc -> [ExprValue] -> Env -> (Store -> Env -> Cont) -> Cont
allocArray l vals g k s = let
                           (locs, s') = getLocs2 vals s
                           s'' = M.insert l (arrayFromList locs) s'
                          in k s'' g s''

allocStruct :: Loc -> (M.Map Var ExprValue) -> Env -> (Store -> Env -> Cont) -> Cont
allocStruct l str g k s = let
                           (locs, s') = getLocs2 (M.elems str) s
                           str' = M.fromList $ zip (M.keys str) locs
                           s'' = M.insert l (S str') s'
                          in k s'' g s''

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
execStmt (S_Block b) g k kr = execBlock b g (\s -> k s g) kr
execStmt (S_Decl d) g k kr = evalDecl d g (\s' g' -> k s' g')
execStmt (S_Assign x e) g k kr = evalExpr e g (\n -> assignValue x n g k)
execStmt (S_MAss x xs e) g k kr = evalExpr (E_TupI e) g (\(T vals) -> assignValues (x:xs) vals g k)
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
execStmt (S_Expr e) g k kr = evalExpr (E_FuncCall e) g (\_ -> \s -> k s g s)

execFor :: Var -> Expr -> Stmt -> Env -> ContS -> ContR -> Cont
execFor x e stmt g k kr = evalExpr e g (\(A arr) -> execFor' x (M.elems arr) stmt g k kr)
                           where
                              execFor' :: Var -> [Loc] -> Stmt -> Env -> ContS -> ContR -> Cont
                              execFor' x [] stmt g k kr = (\s -> k s g s)
                              execFor' x (l:ls) stmt g@(gv,gf) k kr = let
                                                                           block = B_Block [stmt]
                                                                           g' = (M.insert x l gv,gf)
                                                                        in execBlock block g' (\s -> execFor' x ls stmt g k kr) kr

accToLoc :: Acc -> Env -> ContL -> Cont
accToLoc (A_Iden x) (gv,gf) k = k $ fromJust $ M.lookup x gv
accToLoc (A_Arr acc (Arr_Sub i)) g@(gv,gf) k = accToLoc acc g k'
                                                where
                                                   k' :: ContL
                                                   k' l s = let
                                                               v = fromMaybe indexOutR $ M.lookup l s
                                                            in evalExpr i g (\i' -> k $ (!!!) v i') s
accToLoc (A_Str acc (Str_Sub x)) g@(gv,gf) k = accToLoc acc g k'
                                                where
                                                   k' :: ContL
                                                   k' l s = let
                                                               S str = fromJust $ M.lookup l s
                                                               l' = M.lookup x str
                                                            in case l' of
                                                                  Just l'' -> k l'' s
                                                                  Nothing -> let
                                                                              l'' = newLoc s
                                                                              s' = M.insert l'' None s
                                                                              str' = M.insert x l'' str
                                                                              s'' = M.insert l (S str') s'
                                                                             in k l'' s''

assignValue :: Acc -> ExprValue -> Env -> ContS -> Cont
assignValue acc n g k = accToLoc acc g k'
                        where
                           k' :: ContL
                           k' l s = case n of
                                       (L vals) -> allocArray l vals g k s
                                       (Str str) -> allocStruct l str g k s
                                       _ -> let
                                             s' = M.insert l n s
                                            in k s' g s'

assignValues :: [Acc] -> [ExprValue] -> Env -> ContS -> Cont
assignValues [] [] g k = (\s -> k s g s)
assignValues (a:as) (v:vs) g k = assignValue a v g (\s g' -> assignValues as vs g' k)

-- EXPRESSIONS
evalExprList :: [Expr] -> Env -> ContA -> Cont
evalExprList = evalExprList' []
                  where
                     evalExprList' v [] g k = k $ reverse v
                     evalExprList' v (e:es) g k = evalExpr e g (\n -> evalExprList' (n:v) es g k)

evalTuple :: [Expr] -> Env -> ContE -> Cont
evalTuple l g k = evalExprList l g (\vals -> k $ T vals)

evalArray :: [Expr] -> Env -> ContE -> Cont
evalArray l g k = evalExprList l g (\vals -> k $ L vals)

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
evalExpr (E_VarName x) (gv, gf) k = k'
                                    where
                                       k' :: Cont
                                       k' s = let
                                                l = fromJust $ M.lookup x gv
                                                n = fromJust $ M.lookup l s
                                                v = case n of
                                                      A m -> getArray (M.elems m) s
                                                      S str -> getStruct str s
                                                      _ -> n
                                              in k v s
evalExpr (E_FuncCall (Fun_Call foo args)) g k = callFunc args pd l stmt g k
                                                where
                                                   (pd, l, stmt) = fromJust $ M.lookup foo $ snd g
evalExpr (E_ArrS acc (Arr_Sub i)) g k = evalExpr i g k'
                                       where
                                          k' :: ContE
                                          k' n = accToLoc acc g (\l -> k'' l n)
                                          k'' l n s = let
                                                         l' = fromMaybe indexOutR $ M.lookup l s
                                                         v = fromJust $ M.lookup ((!!!) l' n) s
                                                      in k v s
evalExpr (E_StrS acc (Str_Sub y)) g k = accToLoc acc g k'
                                          where
                                             k' :: ContL
                                             k' l s = let
                                                         S str = fromJust $ M.lookup l s
                                                         l' = fromJust $ M.lookup y str
                                                         n = fromJust $ M.lookup l' s
                                                      in k n s

callFunc :: [Expr] -> [PDecl] -> [Loc] -> Stmt -> Env -> ContE -> Cont
callFunc [] _ _ stmt g k = execStmt stmt g notReturn k
callFunc (e:es) (p:ps) locs stmt g@(gv,gf) k
                                          | isRef p = callFunc es ps locs stmt (gv', gf) k
                                          | otherwise = evalExpr e g k'
                                                         where
                                                            (P_Decl x _) = p
                                                            (E_VarName y) = e
                                                            (l:ls) = locs
                                                            l' = fromJust $ M.lookup y gv
                                                            gv' = M.insert x l' gv
                                                            gv'' = M.insert x l gv
                                                            k' :: ContE
                                                            k' n s = callFunc es ps ls stmt (gv'', gf) (\n -> k n) $ M.insert l n s

locToExprVal :: Store -> Loc -> ExprValue
locToExprVal s l = case val of
                     (A arr) -> getArray (M.elems arr) s
                     (S str) -> getStruct str s
                     x -> x
                  where
                     val = fromJust $ M.lookup l s

getArray :: [Loc] -> Store -> ExprValue
getArray locs = getArray' [] $ reverse locs
            where
               getArray' :: [ExprValue] -> [Loc] -> Store -> ExprValue
               getArray' r [] _ = L r
               getArray' r (l:ls) s = case l' of
                                       A m -> let
                                                arr = getArray (M.elems m) s
                                              in getArray' (arr:r) ls s
                                       S str -> let
                                                   str' = getStruct str s
                                                in getArray' (str':r) ls s
                                       _ -> getArray' (l':r) ls s
                                       where
                                          Just l' = M.lookup l s

getStruct :: Struct -> Store -> ExprValue
getStruct = getStruct' M.empty
            where
               getStruct' :: StructVal -> Struct -> Store -> ExprValue
               getStruct' r str s = let
                                       str' = M.map (locToExprVal s) str
                                    in Str $ M.union r str'

evalComp :: (ExprValue -> ExprValue -> Bool) -> Expr -> Expr -> Env -> ContE -> Cont
evalComp f e1 e2 g k = evalExpr e1 g (\v1 -> evalExpr e2 g (\v2 -> k $ B $ f v1 v2))

evalArithm :: (ExprValue -> ExprValue -> ExprValue) -> Expr -> Expr -> Env -> ContE -> Cont
evalArithm f e1 e2 g k = evalExpr e1 g
                           (\v1 -> evalExpr e2 g
                              (\v2 -> k $ if v2 /= 0 then f v1 v2
                                             else divByZero))

evalConst :: Constant -> ExprValue
evalConst (Integer_Const n) = I n
evalConst (True_Const) = B True
evalConst (False_Const) = B False
