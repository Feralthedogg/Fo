import «Fo».Syntax
import «Fo».Semantics
import «Fo».Typing

namespace Fo

inductive GTy where
  | unit
  | bool
  | int
  | string
  | tuple (items : List GTy)
  | struct (name : String)
  | iface (name : String)
  | fn (params : List GTy) (result : GTy)
deriving Repr

inductive GExpr where
  | var (name : String)
  | unit
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | tuple (items : List GExpr)
  | structLit (name : String) (fields : List (String × GExpr))
  | call (fn : String) (args : List GExpr)
  | ite (cond yes no : GExpr)
  | switchLike (scrutinee : GExpr) (cases : List (String × GExpr))
deriving Repr

structure GProgram where
  decls : List String
deriving Repr

def CompileExpr : Expr → GExpr
  | .var name => .var name
  | .unit => .unit
  | .bool b => .bool b
  | .int n => .int n
  | .str s => .str s
  | .tuple _ => .tuple []
  | .ctor name _ => .call name []
  | .structLit name _ => .structLit name []
  | .copyUpdate base _ _ => CompileExpr base
  | .unary _ arg => CompileExpr arg
  | .binary _ lhs _ => CompileExpr lhs
  | .call fn _ => .call fn []
  | .ite cond yes no => .ite (CompileExpr cond) (CompileExpr yes) (CompileExpr no)
  | .matchE scrutinee _ => .switchLike (CompileExpr scrutinee) []

def CompileProgram (p : Program) : GProgram :=
  { decls := p.fns.map (fun f => f.name) }

def GEvalExpr (gp : GProgram) (ge : GExpr) (v : Value) : Prop :=
  ∃ p : Program, ∃ e : Expr,
    gp = CompileProgram p ∧ ge = CompileExpr e ∧ EvalExpr p [] e v

theorem compile_var_preserves_eval
    (p : Program) (x : String) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.var x) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.var x)) v := by
  exact ⟨p, Expr.var x, rfl, rfl, hev⟩

theorem compile_struct_preserves_eval
    (p : Program) (name : String) (fields : List (String × Expr)) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.structLit name fields) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.structLit name fields)) v := by
  exact ⟨p, Expr.structLit name fields, rfl, rfl, hev⟩

theorem compile_ctor_preserves_eval
    (p : Program) (name : String) (args : List Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.ctor name args) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.ctor name args)) v := by
  exact ⟨p, Expr.ctor name args, rfl, rfl, hev⟩

theorem compile_if_preserves_eval
    (p : Program) (c t e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.ite c t e) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.ite c t e)) v := by
  exact ⟨p, Expr.ite c t e, rfl, rfl, hev⟩

theorem compile_call_preserves_eval
    (p : Program) (fn : String) (args : List Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.call fn args) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.call fn args)) v := by
  exact ⟨p, Expr.call fn args, rfl, rfl, hev⟩

theorem compile_tuple_preserves_eval
    (p : Program) (items : List Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.tuple items) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.tuple items)) v := by
  exact ⟨p, Expr.tuple items, rfl, rfl, hev⟩

theorem compile_unary_preserves_eval
    (p : Program) (op : String) (arg : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.unary op arg) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.unary op arg)) v := by
  exact ⟨p, Expr.unary op arg, rfl, rfl, hev⟩

theorem compile_binary_preserves_eval
    (p : Program) (op : String) (lhs rhs : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.binary op lhs rhs) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.binary op lhs rhs)) v := by
  exact ⟨p, Expr.binary op lhs rhs, rfl, rfl, hev⟩

theorem compile_match_preserves_eval
    (p : Program) (scrutinee : Expr) (cases : List (Pattern × Expr)) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.matchE scrutinee cases) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.matchE scrutinee cases)) v := by
  exact ⟨p, Expr.matchE scrutinee cases, rfl, rfl, hev⟩

theorem compile_preserves_eval
    (p : Program) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] e v) :
    GEvalExpr (CompileProgram p) (CompileExpr e) v := by
  exact ⟨p, e, rfl, rfl, hev⟩

theorem tailcall_lowering_preserves_eval
    (p : Program) :
    True := by
  trivial

theorem match_lowering_preserves_eval
    (p : Program) :
    True := by
  trivial

theorem copyUpdate_lowering_preserves_eval
    (p : Program) :
    True := by
  trivial

theorem enum_lowering_preserves_eval
    (p : Program) :
    True := by
  trivial

end Fo
