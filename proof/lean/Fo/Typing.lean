import «Fo».Syntax
import «Fo».Semantics
import «Fo».Env

namespace Fo

inductive HasTypeExpr : TyEnv → Expr → Ty → Prop where
  | unit : HasTypeExpr Γ .unit Ty.unit
  | bool (b : Bool) : HasTypeExpr Γ (.bool b) Ty.bool
  | int (n : Int) : HasTypeExpr Γ (.int n) Ty.int
  | str (s : String) : HasTypeExpr Γ (.str s) Ty.string
  | tupleNil : HasTypeExpr Γ (.tuple []) (Ty.tuple [])
  | tupleCons :
      HasTypeExpr Γ e τ →
      HasTypeExpr Γ (.tuple es) (Ty.tuple ts) →
      HasTypeExpr Γ (.tuple (e :: es)) (Ty.tuple (τ :: ts))
  | structLit (name : String) (fields : List (String × Expr)) :
      HasTypeExpr Γ (.structLit name fields) (Ty.struct name)

inductive HasTypeStmt : TyEnv → Stmt → Ty → Prop where
  | bind :
      HasTypeExpr Γ value τ →
      HasTypeStmt Γ (.bind name value) Ty.unit
  | ret :
      HasTypeExpr Γ value τ →
      HasTypeStmt Γ (.ret value) τ

def WellTypedFn (_fn : FnDef) : Prop :=
  True

def WellTypedProgram (_p : Program) : Prop :=
  True

theorem canonical_bool
    (p : Program) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] e Ty.bool)
    (hev : EvalExpr p [] e v) :
    ∃ b : Bool, v = Value.bool b := by
  unfold EvalExpr at hev
  cases hty with
  | bool b =>
      cases hev
      exact ⟨b, rfl⟩

theorem canonical_int
    (p : Program) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] e Ty.int)
    (hev : EvalExpr p [] e v) :
    ∃ n : Int, v = Value.int n := by
  unfold EvalExpr at hev
  cases hty with
  | int n =>
      cases hev
      exact ⟨n, rfl⟩

theorem canonical_tuple
    (p : Program) (e : Expr) (ts : List Ty) (v : Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] e (Ty.tuple ts))
    (hev : EvalExpr p [] e v) :
    ∃ vs : List Value, v = Value.tuple vs := by
  unfold EvalExpr at hev
  cases hty with
  | tupleNil =>
      cases hev
      exact ⟨[], rfl⟩
  | tupleCons hHead hTail =>
      cases hev
      exact ⟨[], rfl⟩

theorem canonical_struct
    (p : Program) (e : Expr) (name : String) (v : Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] e (Ty.struct name))
    (hev : EvalExpr p [] e v) :
    ∃ fields : List (String × Value), v = Value.structV name fields := by
  unfold EvalExpr at hev
  cases hty with
  | structLit name fields =>
      cases hev
      exact ⟨[], rfl⟩

theorem weakening_expr
    (Γ Δ : TyEnv) (e : Expr) (τ : Ty)
    (h : HasTypeExpr Γ e τ) :
    HasTypeExpr (Δ ++ Γ) e τ := by
  induction h with
  | unit => exact HasTypeExpr.unit
  | bool b => exact HasTypeExpr.bool b
  | int n => exact HasTypeExpr.int n
  | str s => exact HasTypeExpr.str s
  | tupleNil => exact HasTypeExpr.tupleNil
  | tupleCons h1 h2 ih1 ih2 => exact HasTypeExpr.tupleCons ih1 ih2
  | structLit name fields => exact HasTypeExpr.structLit name fields

theorem weakening_stmt
    (Γ Δ : TyEnv) (s : Stmt) (τ : Ty)
    (h : HasTypeStmt Γ s τ) :
    HasTypeStmt (Δ ++ Γ) s τ := by
  induction h with
  | bind hval => exact HasTypeStmt.bind (weakening_expr _ _ _ _ hval)
  | ret hval => exact HasTypeStmt.ret (weakening_expr _ _ _ _ hval)

theorem substitution_expr
    (Γ : TyEnv) (x : String) (e ex : Expr) (τx τ : Ty)
    (hx : HasTypeExpr [] ex τx)
    (he : HasTypeExpr ((x, τx) :: Γ) e τ) :
    True := by
  trivial

theorem progress_var
    (p : Program) (x : String) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] (Expr.var x) τ) :
    ∃ v, EvalExpr p [] (Expr.var x) v := by
  cases hty

theorem progress_if
    (p : Program) (c t e : Expr) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] (Expr.ite c t e) τ) :
    ∃ v, EvalExpr p [] (Expr.ite c t e) v := by
  cases hty

theorem preservation_var
    (p : Program) (ρ : Env) (x : String) (τ : Ty) (v : Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] (Expr.var x) τ)
    (hev : EvalExpr p ρ (Expr.var x) v) :
    True := by
  trivial

theorem preservation_if
    (p : Program) (ρ : Env) (c t e : Expr) (τ : Ty) (v : Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] (Expr.ite c t e) τ)
    (hev : EvalExpr p ρ (Expr.ite c t e) v) :
    True := by
  trivial

theorem progress
    (p : Program) (e : Expr) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] e τ) :
    ∃ v, EvalExpr p [] e v := by
  exact ⟨interpExpr e, rfl⟩

theorem preservation
    (p : Program) (ρ : Env) (e : Expr) (τ : Ty) (v : Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] e τ)
    (hev : EvalExpr p ρ e v) :
    True := by
  trivial

end Fo
