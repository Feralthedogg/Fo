From Coq Require Import List String ZArith.
Import ListNotations.

Module FoSyntax.

Inductive ty :=
| TyUnit
| TyBool
| TyInt
| TyString
| TyTuple (items : list ty)
| TyStruct (name : string)
| TyEnum (name : string)
| TyFn (params : list ty) (result : ty).

Inductive pattern :=
| PWild
| PBinder (name : string)
| PTuple (items : list pattern)
| PCtor (name : string) (args : list pattern)
| PStruct (name : string) (fields : list (string * pattern)).

Inductive expr :=
| EVar (name : string)
| EUnit
| EBool (b : bool)
| EInt (n : Z)
| EString (s : string)
| ETuple (items : list expr)
| ECtor (name : string) (args : list expr)
| EStructLit (name : string) (fields : list (string * expr))
| ECopyUpdate (base : expr) (path : list string) (value : expr)
| EUnary (op : string) (arg : expr)
| EBinary (op : string) (lhs rhs : expr)
| ECall (fn : string) (args : list expr)
| EIf (cond yes no : expr)
| EMatch (scrutinee : expr) (cases : list (pattern * expr)).

Inductive stmt :=
| SBind (name : string) (value : expr)
| SReturn (value : expr)
| SIf (cond : expr) (yes no : list stmt)
| SMatch (scrutinee : expr) (cases : list (pattern * list stmt)).

Record fndef := {
  fn_name : string;
  fn_params : list (string * ty);
  fn_result : ty;
  fn_body : list stmt;
}.

Record program := {
  prog_fns : list fndef;
}.

End FoSyntax.
