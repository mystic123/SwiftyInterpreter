module SkelSwifty where

-- Haskell module generated by the BNF converter

import AbsSwifty
import ErrM
type Result = Err String

failure :: Show a => a -> Result
failure x = Bad $ "Undefined case: " ++ show x

transIdent :: Ident -> Result
transIdent x = case x of
  Ident string -> failure x
transProgram :: Program -> Result
transProgram x = case x of
  Prog stmts -> failure x
transDecl :: Decl -> Result
transDecl x = case x of
  D_Fun ident pdecls type_ stmt -> failure x
  D_Proc ident pdecls stmt -> failure x
  D_Var ident expr -> failure x
  D_Str ident -> failure x
  D_MVar ident idents tuple -> failure x
transPDecl :: PDecl -> Result
transPDecl x = case x of
  P_Decl ident type_ -> failure x
transBlock :: Block -> Result
transBlock x = case x of
  B_Block stmts -> failure x
transAcc :: Acc -> Result
transAcc x = case x of
  A_Iden ident -> failure x
  A_Arr acc arraysub -> failure x
  A_Str acc structsub -> failure x
transStmt :: Stmt -> Result
transStmt x = case x of
  S_Block block -> failure x
  S_Decl decl -> failure x
  S_Assign acc expr -> failure x
  S_MAss acc accs tuple -> failure x
  S_While expr stmt -> failure x
  S_For ident expr stmt -> failure x
  S_If expr stmt -> failure x
  S_IfE expr block stmt -> failure x
  S_Return expr -> failure x
  S_Print expr -> failure x
  S_Expr fcall -> failure x
transFCall :: FCall -> Result
transFCall x = case x of
  Fun_Call ident exprs -> failure x
transArraySub :: ArraySub -> Result
transArraySub x = case x of
  Arr_Sub expr -> failure x
transArray :: Array -> Result
transArray x = case x of
  Arr exprs -> failure x
transTuple :: Tuple -> Result
transTuple x = case x of
  Tup expr exprs -> failure x
transStructSub :: StructSub -> Result
transStructSub x = case x of
  Str_Sub ident -> failure x
transExpr :: Expr -> Result
transExpr x = case x of
  E_Or expr1 expr2 -> failure x
  E_And expr1 expr2 -> failure x
  E_Eq expr1 expr2 -> failure x
  E_Neq expr1 expr2 -> failure x
  E_Lt expr1 expr2 -> failure x
  E_Gt expr1 expr2 -> failure x
  E_Lte expr1 expr2 -> failure x
  E_Gte expr1 expr2 -> failure x
  E_Add expr1 expr2 -> failure x
  E_Subt expr1 expr2 -> failure x
  E_Mult expr1 expr2 -> failure x
  E_Div expr1 expr2 -> failure x
  E_Min expr -> failure x
  E_Neg expr -> failure x
  E_ArrI array -> failure x
  E_TupI tuple -> failure x
  E_ArrS acc arraysub -> failure x
  E_StrS acc structsub -> failure x
  E_FuncCall fcall -> failure x
  E_Const constant -> failure x
  E_VarName ident -> failure x
transConstant :: Constant -> Result
transConstant x = case x of
  False_Const -> failure x
  True_Const -> failure x
  Integer_Const integer -> failure x
transType :: Type -> Result
transType x = case x of
  T_Int -> failure x
  T_Bool -> failure x
  T_Arr type_ -> failure x
  T_Tup types -> failure x
  T_Ref type_ -> failure x
  T_Void -> failure x
  T_Str -> failure x

