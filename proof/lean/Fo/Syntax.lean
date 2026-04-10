namespace Fo

inductive Ty where
  | unit
  | bool
  | int
  | string
  | tuple (items : List Ty)
  | struct (name : String)
  | enum (name : String)
  | fn (params : List Ty) (result : Ty)
deriving Repr

inductive Pattern where
  | wild
  | binder (name : String)
  | tuple (items : List Pattern)
  | ctor (name : String) (args : List Pattern)
  | struct (name : String) (fields : List (String × Pattern))
deriving Repr

inductive Expr where
  | var (name : String)
  | unit
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | tuple (items : List Expr)
  | ctor (name : String) (args : List Expr)
  | structLit (name : String) (fields : List (String × Expr))
  | copyUpdate (base : Expr) (path : List String) (value : Expr)
  | unary (op : String) (arg : Expr)
  | binary (op : String) (lhs rhs : Expr)
  | call (fn : String) (args : List Expr)
  | ite (cond yes no : Expr)
  | matchE (scrutinee : Expr) (cases : List (Pattern × Expr))
deriving Repr

inductive Stmt where
  | bind (name : String) (value : Expr)
  | ret (value : Expr)
  | ite (cond : Expr) (yes no : List Stmt)
  | matchS (scrutinee : Expr) (cases : List (Pattern × List Stmt))
deriving Repr

structure FnDef where
  name : String
  params : List (String × Ty)
  result : Ty
  body : List Stmt
deriving Repr

structure Program where
  fns : List FnDef
deriving Repr

end Fo
