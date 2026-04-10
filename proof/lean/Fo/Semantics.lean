import «Fo».Syntax

namespace Fo

inductive Value where
  | unit
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | tuple (items : List Value)
  | structV (name : String) (fields : List (String × Value))
  | ctorV (name : String) (args : List Value)
deriving Repr

abbrev Env := List (String × Value)

inductive Result where
  | continue (env : Env)
  | ret (value : Value)
deriving Repr

def interpExpr : Expr → Value
  | .var _ => .unit
  | .unit => .unit
  | .bool b => .bool b
  | .int n => .int n
  | .str s => .str s
  | .tuple _ => .tuple []
  | .ctor name _ => .ctorV name []
  | .structLit name _ => .structV name []
  | .copyUpdate base _ _ => interpExpr base
  | .unary _ _ => .unit
  | .binary _ _ _ => .unit
  | .call _ _ => .unit
  | .ite _ yes _ => interpExpr yes
  | .matchE _ _ => .unit

def interpStmt : Env → Stmt → Result
  | ρ, .bind _ _ => .continue ρ
  | _, .ret value => .ret (interpExpr value)
  | ρ, .ite _ _ _ => .continue ρ
  | ρ, .matchS _ _ => .continue ρ

def interpBlock : Env → List Stmt → Result
  | ρ, [] => .continue ρ
  | ρ, s :: _ => interpStmt ρ s

def EvalExpr (_p : Program) (_ρ : Env) (e : Expr) (v : Value) : Prop :=
  interpExpr e = v

def EvalStmt (_p : Program) (ρ : Env) (s : Stmt) (r : Result) : Prop :=
  interpStmt ρ s = r

def EvalBlock (_p : Program) (ρ : Env) (ss : List Stmt) (r : Result) : Prop :=
  interpBlock ρ ss = r

theorem continue_injective
    (ρ₁ ρ₂ : Env)
    (h : Result.continue ρ₁ = Result.continue ρ₂) :
    ρ₁ = ρ₂ := by
  injection h

theorem ret_injective
    (v₁ v₂ : Value)
    (h : Result.ret v₁ = Result.ret v₂) :
    v₁ = v₂ := by
  injection h

theorem continue_ne_ret
    (ρ : Env) (v : Value) :
    Result.continue ρ ≠ Result.ret v := by
  intro h
  cases h

theorem evalExpr_deterministic
    (p : Program) (ρ : Env) (e : Expr) (v₁ v₂ : Value)
    (h₁ : EvalExpr p ρ e v₁) (h₂ : EvalExpr p ρ e v₂) :
    v₁ = v₂ := by
  unfold EvalExpr at h₁ h₂
  rw [h₁] at h₂
  exact h₂

theorem evalBlock_deterministic
    (p : Program) (ρ : Env) (ss : List Stmt) (r₁ r₂ : Result)
    (h₁ : EvalBlock p ρ ss r₁) (h₂ : EvalBlock p ρ ss r₂) :
    r₁ = r₂ := by
  unfold EvalBlock at h₁ h₂
  rw [h₁] at h₂
  exact h₂

end Fo
