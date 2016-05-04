{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TypeChecker where

import Data.Maybe
import AbsSwifty
import ErrM
import qualified Data.Map as M
import qualified Data.Set as St
import Data.Maybe
import Data.List
import Control.Monad.State as S

type Var = Ident
type FName = Ident
type EnvV = M.Map Var TCType
type EnvF = M.Map FName (TCType, [(Var, TCType)], Stmt)
type CheckedFun = St.Set Var
type Env = (EnvV,EnvF,CheckedFun)

data TCType = S (M.Map Var TCType) | T Type | A TCType | Tp [TCType] | R TCType | None deriving (Eq, Ord)

instance Show TCType where
   show (T T_Int) = "Int"
   show (T T_Bool) = "Bool"
   show (T T_Void) = "Void"
   show (T _) = "kupa"
   show (R t) = "&" ++ show t
   show (S m) = concat ["Struct {", desc, "}"]
                  where
                     desc = intercalate "," (map (\(Ident k,v) -> show k ++ ": " ++ show v) $ M.assocs m)
   show (A t) = (show t) ++ "[]"
   show (Tp l) = concat ["(", intercalate "," (map show l),")"]
   show None = "None"

type TState = S.State Env

-- ERRORS
errorExpected t1 t2 f1 f2 = error $ concat ["Type error: Expected: ",show t1,",",show t2,", found: ",show f1,",",show f2]
errorExpected2 t f = error $ concat ["Type error: Expected: ",show t,", found: ",show f]
undefVar (Ident x) = error $ "Name error: Undefined variable: " ++ (show x)
undefFunc (Ident f) = error $ "Name error: Undefined function: " ++ (show f)
notArray = error $ "Type error: Not an array"
notStruct = error $ "Type error: Not a struct"
notValidArrSub x = error $ "Type error: Not valid array subscript: " ++ (show x)
argsNoMatch l1 l2 = let
                        l1' = concat $ ["[",intercalate "," (map show l1),"]"]
                        l2' = concat $ ["[",intercalate "," (map show l2),"]"]
                    in error $ concat ["Type error: Mismatched function parameters. Expected: ",l1', ", found: ", l2']
notIterable x = error $ "Type error: Not iterable: " ++ (show x)
arrayElemsError = error "Type error: Array elements must be of same type"
invRetType = error "Type error: Type of return value does not match function's return type"
refTypeError = error "Type error: Expected type, found reference"
errorMultAssign l1 l2 = error $ concat ["Error in multiple assign: ", "Expected: ", show l1 , " values, found: ", show l2]
errorProcAssign = error "Type error: Fuction does not return any value"

emptyEnv = (M.empty, M.empty, St.empty)

-- PROGRAM
checkProg :: Program -> IO ()
checkProg (Prog p) = checkProg' p emptyEnv
                        where
                           checkProg' [] env = do
                                                --mapM_ (putStrLn . show) (M.toList $ fst env)
                                                return ()
                           checkProg' (s:ss) env = do
                                                      env' <- execStateT (checkStmt s) env
                                                      checkProg' ss env'

-- DECLARATIONS
checkDecl :: MonadState Env m => Decl -> m TCType
checkDecl (D_Var x e) = do
                           t <- checkExpr e
                           if t /= T T_Void
                              then modify (\(ev,ef,f) -> (M.insert x t ev,ef,f)) >> return None
                              else errorProcAssign
checkDecl (D_Fun x pd t s) = do
                              (ev,ef,fs) <- get
                              put $ (ev, M.insert x (toTCType t, getParams pd, s) ef, St.delete x fs)
                              return None
checkDecl (D_Proc x pd s) = do
                              (ev,ef,fs) <- get
                              put $ (ev, M.insert x (T T_Void, getParams pd, s) ef, St.delete x fs)
                              return None
checkDecl (D_Str x) = do
                        modify (\(ev,ef,f) -> (M.insert x (S M.empty) ev,ef,f))
                        return None
checkDecl (D_MVar x xs (Tup e es)) = do
                                       let l1 = length (x:xs)
                                       let l2 = length (e:es)
                                       if l1 == l2
                                          then (mapM (\(x',e') -> checkDecl (D_Var x' e')) $ zip (x:xs) (e:es)) >> return None
                                          else errorMultAssign l1 l2

toTCType :: Type -> TCType
toTCType t = let
               toTCType' t = case t of
                              T_Ref t' -> refTypeError
                              _ -> toTCType t
             in case t of
                  T_Ref t' -> R $ toTCType' t'
                  T_Arr t' -> A $ toTCType' t'
                  T_Tup t' -> Tp $ map toTCType' t'
                  _ -> T t

getParams :: [PDecl] -> [(Var, TCType)]
getParams = map (\(P_Decl x t) -> (x,toTCType t))

-- BLOCKS
checkBlock :: MonadState Env m => Block -> m TCType
checkBlock (B_Block stmts) = do
                              env <- get
                              types <- mapM checkStmt stmts
                              put env
                              let types' = filter (/= None) types
                              if types' == []
                                 then return None
                                 else let
                                          t0 = head types'
                                       in if all (== t0) types'
                                             then return t0
                                             else invRetType

-- STATEMENTS
checkStmt :: MonadState Env m => Stmt -> m TCType
checkStmt (S_Decl d) = checkDecl d
checkStmt (S_Block b) = checkBlock b
checkStmt (S_Assign acc e) = do
                              t1 <- getAccType acc
                              t2 <- checkExpr e
                              if t1 == None
                                 then updateStrType acc t2
                                 else if t1 == t2
                                       then return None
                                       else errorExpected2 t1 t2
checkStmt (S_MAss a as (Tup e es)) = do
                                       let l1 = length (a:as)
                                       let l2 = length (e:es)
                                       if l1 == l2
                                          then (mapM (\(a',e') -> checkStmt (S_Assign a' e')) $ zip (a:as) (e:es)) >> return None
                                          else errorMultAssign l1 l2
checkStmt (S_While e s) = do
                           t <- checkExpr e
                           if t == T T_Bool
                              then checkStmt s
                              else errorExpected2 T_Bool t
checkStmt (S_For x e s) = do
                           t <- checkExpr e
                           env@(ev,ef,f) <- get
                           case t of
                              A t' -> do
                                       modify (\(ev',ef',f') -> (M.insert x t' ev', ef', f'))
                                       checkStmt s
                                       put env
                                       return None
                              _ -> notIterable e
checkStmt (S_If e s) = do
                        t <- checkExpr e
                        case t of
                           T T_Bool -> checkStmt s
                           _ -> errorExpected2 (T T_Bool) t
checkStmt (S_IfE e b s) = do
                              t <- checkExpr e
                              case t of
                                 T T_Bool -> checkBlock b >> checkStmt s
                                 _ -> errorExpected2 (T T_Bool) t
checkStmt (S_Return e) = checkExpr e >>= return
checkStmt (S_Print e) = checkExpr e >> return None
checkStmt (S_Expr fc) = checkFunCall fc

checkFuncParams :: MonadState Env m => [Expr] -> m [TCType]
checkFuncParams exprs = mapM checkExpr' exprs >>= return
                           where
                              checkExpr' e = case e of
                                                E_VarName _ -> do
                                                                  t <- checkExpr e
                                                                  return $ R t
                                                _ -> checkExpr e


checkFunCall :: MonadState Env m => FCall -> m TCType
checkFunCall (Fun_Call x exprs) = do
                                    args <- checkFuncParams exprs
                                    env@(ev,ef,fs) <- get
                                    let (t,parTyp,s) = fromMaybe (undefFunc x) $ M.lookup x ef
                                    let params = map snd parTyp
                                    if paramsMatch args params
                                       then if St.member x fs
                                                then return t
                                                else do
                                                   let fs' = St.insert x fs
                                                   put (ev,ef,fs')
                                                   mapM (\(x',t') -> modify (\(ev,ef,fs) -> (M.insert x' (fromRef t') ev, ef,fs))) parTyp
                                                   rt <- checkStmt s
                                                   put (ev,ef,fs')
                                                   if rt /= t
                                                      then invRetType
                                                      else return rt
                                       else argsNoMatch params args
                                          where
                                             fromRef :: TCType -> TCType
                                             fromRef t = case t of
                                                            R t -> t
                                                            x -> x
                                             paramsMatch :: [TCType] -> [TCType] -> Bool
                                             paramsMatch args params = let
                                                                        l = zip args params
                                                                        f = (\(x,y) -> (x == y) || (fromRef x == y))
                                                                       in if length args == length params
                                                                           then and $ map f l
                                                                           else argsNoMatch params args

updateStrType :: MonadState Env m => Acc -> TCType -> m TCType
updateStrType acc t = do
                        updateStrType' acc t
                        return None
                           where
                              updateStrType' (A_Iden x) _ = do
                                                               (ev,ef,_) <- get
                                                               return (fromMaybe (undefVar x) $ M.lookup x ev, x)
                              updateStrType' (A_Str acc (Str_Sub y)) t = do
                                                                           (S str',x) <- updateStrType' acc t
                                                                           let str'' = M.insert y t str'
                                                                           modify (\(ev,ef,fs) -> (M.insert x (S str'') ev, ef,fs))
                                                                           return (S str'', y)

-- EXPRESSIONS
checkExpr :: MonadState Env m => Expr -> m TCType
checkExpr (E_Or e1 e2) = checkBoolean e1 e2
checkExpr (E_And e1 e2) = checkBoolean e1 e2
checkExpr (E_Eq e1 e2) = checkEq e1 e2
checkExpr (E_Neq e1 e2) = checkEq e1 e2
checkExpr (E_Lt e1 e2) = checkComp e1 e2
checkExpr (E_Gt e1 e2) = checkComp e1 e2
checkExpr (E_Lte e1 e2) = checkComp e1 e2
checkExpr (E_Gte e1 e2) = checkComp e1 e2
checkExpr (E_Add e1 e2) = checkArithm e1 e2
checkExpr (E_Subt e1 e2) = checkArithm e1 e2
checkExpr (E_Mult e1 e2) = checkArithm e1 e2
checkExpr (E_Div e1 e2) = checkArithm e1 e2
checkExpr (E_Min e) = do
                        t <- checkExpr e
                        if t == T T_Int
                           then return $ T T_Int
                           else errorExpected2 (T T_Int) t
checkExpr (E_Neg e) = do
                        t <- checkExpr e
                        if t == T T_Bool
                           then return $ T T_Bool
                           else errorExpected2 (T T_Bool) e
checkExpr (E_ArrI arr) = checkArrayInit arr
checkExpr (E_TupI tup) = checkTupleInit tup
checkExpr (E_ArrS arr sub) = checkArraySub arr sub
checkExpr (E_StrS str sub) = checkStructSub str sub
checkExpr e@(E_FuncCall fc) = checkFunCall fc >> inferType e
checkExpr e@(E_VarName x) = inferType e
checkExpr e@(E_Const c) = inferType e

getAccType :: MonadState Env m => Acc -> m TCType
getAccType (A_Iden x) = do
                           (ev,ef,_) <- get
                           case M.lookup x ev of
                              Just t' -> return t'
                              Nothing -> undefVar x
getAccType (A_Arr acc _) = do
                              t <- getAccType acc
                              case t of
                                 (A t') -> return t'
                                 _ -> notArray
getAccType (A_Str acc (Str_Sub x)) = do
                                       t <- getAccType acc
                                       case t of
                                          S m -> return $ fromMaybe None $ M.lookup x m
                                          _ -> notStruct

checkArrayInit :: MonadState Env m => Array -> m TCType
checkArrayInit (Arr exps) = do
                              types <- mapM checkExpr exps
                              let t0 = head types
                              let allEq = all ((==) t0) types
                              if allEq
                                 then return $ A t0
                                 else arrayElemsError

checkArraySub :: MonadState Env m => Acc -> ArraySub -> m TCType
checkArraySub (A_Iden x) sub = do
                                 _ <- checkArrSub sub
                                 (ev,ef,_) <- get
                                 let t = M.lookup x ev
                                 if isNothing t
                                    then undefVar x
                                    else case fromJust t of
                                             A t -> return t
                                             _ -> notArray
checkArraySub (A_Arr acc sub) sub' = do
                                       _ <- checkArrSub sub'
                                       t <- checkArraySub acc sub
                                       return t

checkArrSub :: MonadState Env m => ArraySub -> m TCType
checkArrSub (Arr_Sub e) = do
                           t <- checkExpr e
                           if t == T T_Int
                              then return $ T T_Int
                              else notValidArrSub e

checkStructSub :: MonadState Env m => Acc -> StructSub -> m TCType
checkStructSub (A_Iden x) (Str_Sub y) = do
                                          (ev,ef,_) <- get
                                          let t = M.lookup x ev
                                          if isNothing t
                                             then undefVar x
                                             else case fromJust t of
                                                      S m -> case M.lookup y m of
                                                               Just t' -> return t'
                                                               _ -> notStruct
                                                      _ -> notStruct
checkStructSub (A_Str str sub) (Str_Sub y) = do
                                                t <- checkStructSub str sub
                                                case t of
                                                   S m -> case M.lookup y m of
                                                            Just t' -> return t'
                                                            _ -> notStruct
                                                   _ -> notStruct

checkTupleInit :: MonadState Env m => Tuple -> m TCType
checkTupleInit (Tup e exps) = do
                                 types <- mapM checkExpr (e:exps)
                                 return $ Tp types

checkBoolean :: MonadState Env m => Expr -> Expr -> m TCType
checkBoolean e1 e2 = do
                        t1 <- checkExpr e1
                        t2 <- checkExpr e2
                        if t1 == T T_Bool && t1 == t2
                           then return $ T T_Bool
                           else errorExpected (T T_Bool) (T T_Bool) t1 t2

checkEq :: MonadState Env m => Expr -> Expr -> m TCType
checkEq e1 e2 = do
                     t1 <- checkExpr e1
                     t2 <- checkExpr e2
                     if t1 == t2
                        then return $ T T_Bool
                        else errorExpected t1 t1 t1 t2

checkArithm :: MonadState Env m => Expr -> Expr -> m TCType
checkArithm e1 e2 = do
                     t1 <- checkExpr e1
                     t2 <- checkExpr e2
                     if t1 == T T_Int && t1 == t2
                        then return $ T T_Int
                        else errorExpected (T T_Int) (T T_Int) t1 t2

checkComp :: MonadState Env m => Expr -> Expr -> m TCType
checkComp e1 e2 = do
                     t1 <- checkExpr e1
                     t2 <- checkExpr e2
                     if t1 == T T_Int && t1 == t2
                        then return $ T T_Bool
                        else errorExpected (T T_Int) (T T_Int) t1 t2

inferType :: MonadState Env m => Expr -> m TCType
inferType (E_Const c) = return $ case c of
                                 False_Const -> T T_Bool
                                 True_Const -> T T_Bool
                                 Integer_Const _ -> T T_Int
inferType (E_VarName x) = do
                           (ev,ef,_) <- get
                           let t = M.lookup x ev
                           if isJust t
                              then return $ fromJust t
                              else undefVar x
inferType (E_FuncCall (Fun_Call f exprs)) = do
                                             (ev,ef,_) <- get
                                             let (t,_,_) = fromMaybe (undefFunc f) $ M.lookup f ef
                                             return t
