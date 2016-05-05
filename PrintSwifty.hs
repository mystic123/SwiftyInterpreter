{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module PrintSwifty where

-- pretty-printer generated by the BNF converter

import AbsSwifty
import Data.Char


-- the top-level printing method
printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 (map ($ "") $ d []) "" where
  rend i ss = case ss of
    "["      :ts -> showChar '[' . rend i ts
    "("      :ts -> showChar '(' . rend i ts
    "{"      :ts -> showChar '{' . new (i+1) . rend (i+1) ts
    "}" : ";":ts -> new (i-1) . space "}" . showChar ';' . new (i-1) . rend (i-1) ts
    "}"      :ts -> new (i-1) . showChar '}' . new (i-1) . rend (i-1) ts
    ";"      :ts -> showChar ';' . new i . rend i ts
    t  : "," :ts -> showString t . space "," . rend i ts
    t  : ")" :ts -> showString t . showChar ')' . rend i ts
    t  : "]" :ts -> showString t . showChar ']' . rend i ts
    t        :ts -> space t . rend i ts
    _            -> id
  new i   = showChar '\n' . replicateS (2*i) (showChar ' ') . dropWhile isSpace
  space t = showString t . (\s -> if null s then "" else (' ':s))

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- the printer class does the job
class Print a where
  prt :: Int -> a -> Doc
  prtList :: Int -> [a] -> Doc
  prtList i = concatD . map (prt i)

instance Print a => Print [a] where
  prt = prtList

instance Print Char where
  prt _ s = doc (showChar '\'' . mkEsc '\'' s . showChar '\'')
  prtList _ s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q s = case s of
  _ | s == q -> showChar '\\' . showChar s
  '\\'-> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  _ -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j<i then parenth else id


instance Print Integer where
  prt _ x = doc (shows x)


instance Print Double where
  prt _ x = doc (shows x)


instance Print Ident where
  prt _ (Ident i) = doc (showString ( i))
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, doc (showString ","), prt 0 xs])


instance Print Program where
  prt i e = case e of
    Prog stmts -> prPrec i 0 (concatD [prt 0 stmts])

instance Print Decl where
  prt i e = case e of
    D_Fun id pdecls type_ stmt -> prPrec i 0 (concatD [doc (showString "func"), prt 0 id, doc (showString "("), prt 0 pdecls, doc (showString ")"), doc (showString "->"), prt 0 type_, prt 0 stmt])
    D_Proc id pdecls stmt -> prPrec i 0 (concatD [doc (showString "func"), prt 0 id, doc (showString "("), prt 0 pdecls, doc (showString ")"), prt 0 stmt])
    D_Var id expr -> prPrec i 0 (concatD [doc (showString "var"), prt 0 id, doc (showString "="), prt 0 expr])
    D_Str id -> prPrec i 0 (concatD [doc (showString "struct"), prt 0 id])
    D_MVar id ids tuple -> prPrec i 0 (concatD [doc (showString "var"), prt 0 id, doc (showString ","), prt 0 ids, doc (showString "="), prt 0 tuple])

instance Print PDecl where
  prt i e = case e of
    P_Decl id type_ -> prPrec i 0 (concatD [prt 0 id, doc (showString ":"), prt 0 type_])
  prtList _ [] = (concatD [])
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, doc (showString ","), prt 0 xs])
instance Print Block where
  prt i e = case e of
    B_Block stmts -> prPrec i 0 (concatD [doc (showString "{"), prt 0 stmts, doc (showString "}")])

instance Print Acc where
  prt i e = case e of
    A_Iden id -> prPrec i 0 (concatD [prt 0 id])
    A_Arr acc arraysub -> prPrec i 0 (concatD [prt 0 acc, prt 0 arraysub])
    A_Str acc structsub -> prPrec i 0 (concatD [prt 0 acc, prt 0 structsub])
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, doc (showString ","), prt 0 xs])
instance Print Stmt where
  prt i e = case e of
    S_Block block -> prPrec i 0 (concatD [prt 0 block])
    S_Decl decl -> prPrec i 0 (concatD [prt 0 decl])
    S_Assign acc expr -> prPrec i 0 (concatD [prt 0 acc, doc (showString "="), prt 0 expr])
    S_MAss acc accs tuple -> prPrec i 0 (concatD [prt 0 acc, doc (showString ","), prt 0 accs, doc (showString "="), prt 0 tuple])
    S_While expr stmt -> prPrec i 0 (concatD [doc (showString "while"), doc (showString "("), prt 0 expr, doc (showString ")"), prt 0 stmt])
    S_For id acc stmt -> prPrec i 0 (concatD [doc (showString "for"), prt 0 id, doc (showString "in"), prt 0 acc, prt 0 stmt])
    S_If expr stmt -> prPrec i 0 (concatD [doc (showString "if"), doc (showString "("), prt 0 expr, doc (showString ")"), prt 0 stmt])
    S_IfE expr block stmt -> prPrec i 0 (concatD [doc (showString "if"), doc (showString "("), prt 0 expr, doc (showString ")"), prt 0 block, doc (showString "else"), prt 0 stmt])
    S_Return expr -> prPrec i 0 (concatD [doc (showString "return"), prt 0 expr])
    S_Print expr -> prPrec i 0 (concatD [doc (showString "print"), prt 0 expr])
    S_Expr fcall -> prPrec i 0 (concatD [prt 0 fcall])
  prtList _ [] = (concatD [])
  prtList _ (x:xs) = (concatD [prt 0 x, prt 0 xs])
instance Print FCall where
  prt i e = case e of
    Fun_Call id exprs -> prPrec i 0 (concatD [prt 0 id, doc (showString "("), prt 0 exprs, doc (showString ")")])

instance Print ArraySub where
  prt i e = case e of
    Arr_Sub expr -> prPrec i 0 (concatD [doc (showString "["), prt 0 expr, doc (showString "]")])

instance Print Array where
  prt i e = case e of
    Arr exprs -> prPrec i 0 (concatD [doc (showString "{"), prt 0 exprs, doc (showString "}")])

instance Print Tuple where
  prt i e = case e of
    Tup expr exprs -> prPrec i 0 (concatD [doc (showString "("), prt 0 expr, doc (showString ","), prt 0 exprs, doc (showString ")")])

instance Print StructSub where
  prt i e = case e of
    Str_Sub id -> prPrec i 0 (concatD [doc (showString "."), prt 0 id])

instance Print Expr where
  prt i e = case e of
    E_Or expr1 expr2 -> prPrec i 1 (concatD [prt 1 expr1, doc (showString "||"), prt 2 expr2])
    E_And expr1 expr2 -> prPrec i 2 (concatD [prt 2 expr1, doc (showString "&&"), prt 3 expr2])
    E_Eq expr1 expr2 -> prPrec i 3 (concatD [prt 3 expr1, doc (showString "=="), prt 4 expr2])
    E_Neq expr1 expr2 -> prPrec i 3 (concatD [prt 3 expr1, doc (showString "!="), prt 4 expr2])
    E_Lt expr1 expr2 -> prPrec i 4 (concatD [prt 4 expr1, doc (showString "<"), prt 5 expr2])
    E_Gt expr1 expr2 -> prPrec i 4 (concatD [prt 4 expr1, doc (showString ">"), prt 5 expr2])
    E_Lte expr1 expr2 -> prPrec i 4 (concatD [prt 4 expr1, doc (showString "<="), prt 5 expr2])
    E_Gte expr1 expr2 -> prPrec i 4 (concatD [prt 4 expr1, doc (showString ">="), prt 5 expr2])
    E_Add expr1 expr2 -> prPrec i 5 (concatD [prt 5 expr1, doc (showString "+"), prt 6 expr2])
    E_Subt expr1 expr2 -> prPrec i 5 (concatD [prt 5 expr1, doc (showString "-"), prt 6 expr2])
    E_Mult expr1 expr2 -> prPrec i 6 (concatD [prt 6 expr1, doc (showString "*"), prt 7 expr2])
    E_Div expr1 expr2 -> prPrec i 6 (concatD [prt 6 expr1, doc (showString "/"), prt 7 expr2])
    E_Min expr -> prPrec i 7 (concatD [doc (showString "-"), prt 8 expr])
    E_Neg expr -> prPrec i 7 (concatD [doc (showString "!"), prt 8 expr])
    E_ArrI array -> prPrec i 8 (concatD [prt 0 array])
    E_ArrI2 expr1 expr2 -> prPrec i 8 (concatD [doc (showString "array"), doc (showString "("), prt 0 expr1, doc (showString ","), prt 0 expr2, doc (showString ")")])
    E_TupI tuple -> prPrec i 8 (concatD [prt 0 tuple])
    E_ArrS acc arraysub -> prPrec i 8 (concatD [prt 0 acc, prt 0 arraysub])
    E_StrS acc structsub -> prPrec i 8 (concatD [prt 0 acc, prt 0 structsub])
    E_FuncCall fcall -> prPrec i 8 (concatD [prt 0 fcall])
    E_Const constant -> prPrec i 8 (concatD [prt 0 constant])
    E_VarName id -> prPrec i 8 (concatD [prt 0 id])
  prtList _ [] = (concatD [])
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, doc (showString ","), prt 0 xs])
instance Print Constant where
  prt i e = case e of
    False_Const -> prPrec i 0 (concatD [doc (showString "false")])
    True_Const -> prPrec i 0 (concatD [doc (showString "true")])
    Integer_Const n -> prPrec i 0 (concatD [prt 0 n])

instance Print Type where
  prt i e = case e of
    T_Int -> prPrec i 0 (concatD [doc (showString "int")])
    T_Bool -> prPrec i 0 (concatD [doc (showString "bool")])
    T_Arr type_ -> prPrec i 0 (concatD [doc (showString "Array"), doc (showString "of"), prt 0 type_])
    T_Tup types -> prPrec i 0 (concatD [doc (showString "("), prt 0 types, doc (showString ")")])
    T_Ref type_ -> prPrec i 0 (concatD [doc (showString "&"), prt 0 type_])
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, doc (showString ","), prt 0 xs])

