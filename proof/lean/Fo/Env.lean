import «Fo».Syntax
import «Fo».Semantics

namespace Fo

abbrev TyEnv := List (String × Ty)

def lookupTy : TyEnv → String → Option Ty
  | [], _ => none
  | (n, τ) :: rest, x => if n = x then some τ else lookupTy rest x

def lookupVal : Env → String → Option Value
  | [], _ => none
  | (n, v) :: rest, x => if n = x then some v else lookupVal rest x

inductive HasTypeValue : Value → Ty → Prop where
  | unit : HasTypeValue Value.unit Ty.unit
  | bool (b : Bool) : HasTypeValue (Value.bool b) Ty.bool
  | int (n : Int) : HasTypeValue (Value.int n) Ty.int
  | str (s : String) : HasTypeValue (Value.str s) Ty.string
  | tuple (vs : List Value) (ts : List Ty) :
      HasTypeValue (Value.tuple vs) (Ty.tuple ts)
  | structV (name : String) (fields : List (String × Value)) :
      HasTypeValue (Value.structV name fields) (Ty.struct name)
  | ctorV (name enumName : String) (args : List Value) :
      HasTypeValue (Value.ctorV name args) (Ty.enum enumName)

def EnvWellTyped (ρ : Env) (Γ : TyEnv) : Prop :=
  ∀ x v, lookupVal ρ x = some v → ∃ τ, lookupTy Γ x = some τ ∧ HasTypeValue v τ

theorem lookupTy_nil (x : String) : lookupTy [] x = none := by
  rfl

theorem lookupVal_nil (x : String) : lookupVal [] x = none := by
  rfl

theorem lookupTy_shadow
    (x : String) (τ : Ty) (Γ : TyEnv) :
    lookupTy ((x, τ) :: Γ) x = some τ := by
  simp [lookupTy]

theorem lookupVal_shadow
    (x : String) (v : Value) (ρ : Env) :
    lookupVal ((x, v) :: ρ) x = some v := by
  simp [lookupVal]

theorem lookupTy_miss
    (x y : String) (τ : Ty) (Γ : TyEnv)
    (h : x ≠ y) :
    lookupTy ((x, τ) :: Γ) y = lookupTy Γ y := by
  simp [lookupTy, h]

theorem lookupVal_miss
    (x y : String) (v : Value) (ρ : Env)
    (h : x ≠ y) :
    lookupVal ((x, v) :: ρ) y = lookupVal ρ y := by
  simp [lookupVal, h]

theorem env_lookup_deterministic
    (Γ : TyEnv) (x : String) (τ₁ τ₂ : Ty)
    (h₁ : lookupTy Γ x = some τ₁)
    (h₂ : lookupTy Γ x = some τ₂) :
    τ₁ = τ₂ := by
  rw [h₁] at h₂
  injection h₂

theorem value_lookup_deterministic
    (ρ : Env) (x : String) (v₁ v₂ : Value)
    (h₁ : lookupVal ρ x = some v₁)
    (h₂ : lookupVal ρ x = some v₂) :
    v₁ = v₂ := by
  rw [h₁] at h₂
  injection h₂

end Fo
