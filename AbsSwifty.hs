

module AbsSwifty where

-- Haskell module generated by the BNF converter




newtype Ident = Ident String deriving (Eq, Ord, Show, Read)
data Program = Prog [Stmt]
  deriving (Eq, Ord, Show, Read)

data Decl
    = D_Fun Ident [PDecl] Type Stmt
    | D_Proc Ident [PDecl] Stmt
    | D_Var Ident Expr
    | D_Str Ident
    | D_MVar Ident [Ident] Tuple
  deriving (Eq, Ord, Show, Read)

data PDecl = P_Decl Ident Type
  deriving (Eq, Ord, Show, Read)

data Block = B_Block [Stmt]
  deriving (Eq, Ord, Show, Read)

data Acc = A_Iden Ident | A_Arr Acc ArraySub | A_Str Acc StructSub
  deriving (Eq, Ord, Show, Read)

data Stmt
    = S_Block Block
    | S_Decl Decl
    | S_Assign Acc Expr
    | S_MAss Acc [Acc] Tuple
    | S_While Expr Stmt
    | S_For Ident Expr Stmt
    | S_If Expr Stmt
    | S_IfE Expr Block Stmt
    | S_Return Expr
    | S_Print Expr
    | S_Expr FCall
  deriving (Eq, Ord, Show, Read)

data FCall = Fun_Call Ident [Expr]
  deriving (Eq, Ord, Show, Read)

data Expr
    = E_TupI Tuple
    | E_Or Expr Expr
    | E_And Expr Expr
    | E_Eq Expr Expr
    | E_Neq Expr Expr
    | E_Lt Expr Expr
    | E_Gt Expr Expr
    | E_Lte Expr Expr
    | E_Gte Expr Expr
    | E_Add Expr Expr
    | E_Subt Expr Expr
    | E_Mult Expr Expr
    | E_Div Expr Expr
    | E_Min Expr
    | E_Neg Expr
    | E_ArrI Array
    | E_ArrS Acc ArraySub
    | E_StrS Acc StructSub
    | E_FuncCall FCall
    | E_Const Constant
    | E_VarName Ident
  deriving (Eq, Ord, Show, Read)

data ArraySub = Arr_Sub Expr
  deriving (Eq, Ord, Show, Read)

data Array = Arr [Expr]
  deriving (Eq, Ord, Show, Read)

data Tuple = Tup Expr [Expr]
  deriving (Eq, Ord, Show, Read)

data StructSub = Str_Sub Ident
  deriving (Eq, Ord, Show, Read)

data Constant = False_Const | True_Const | Integer_Const Integer
  deriving (Eq, Ord, Show, Read)

data Type = T_Int | T_Bool | T_Arr Type | T_Tup [Type] | T_Ref Type
  deriving (Eq, Ord, Show, Read)

