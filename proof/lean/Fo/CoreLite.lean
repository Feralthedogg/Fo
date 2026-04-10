namespace Fo

inductive LiteTy where
  | unit
  | bool
  | int
  | string
  | tuple (items : List LiteTy)
deriving Repr

inductive LiteValue where
  | unit
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | tuple (items : List LiteValue)
deriving Repr

abbrev LiteEnv := List (String × LiteValue)

def lookupLite : LiteEnv → String → Option LiteValue
  | [], _ => none
  | (n, v) :: rest, x => if n = x then some v else lookupLite rest x

inductive LiteExpr where
  | var (name : String)
  | unit
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | tuple (items : List LiteExpr)
  | ite (cond yes no : LiteExpr)
deriving Repr

inductive LiteEval : LiteEnv → LiteExpr → LiteValue → Prop where
  | var :
      lookupLite ρ x = some v →
      LiteEval ρ (.var x) v
  | unit :
      LiteEval ρ .unit .unit
  | bool :
      LiteEval ρ (.bool b) (.bool b)
  | int :
      LiteEval ρ (.int n) (.int n)
  | str :
      LiteEval ρ (.str s) (.str s)
  | tupleNil :
      LiteEval ρ (.tuple []) (.tuple [])
  | tupleCons :
      LiteEval ρ e v →
      LiteEval ρ (.tuple es) (.tuple vs) →
      LiteEval ρ (.tuple (e :: es)) (.tuple (v :: vs))
  | ifTrue :
      LiteEval ρ c (.bool true) →
      LiteEval ρ t v →
      LiteEval ρ (.ite c t e) v
  | ifFalse :
      LiteEval ρ c (.bool false) →
      LiteEval ρ e v →
      LiteEval ρ (.ite c t e) v

abbrev LiteTyEnv := List (String × LiteTy)

def lookupLiteTy : LiteTyEnv → String → Option LiteTy
  | [], _ => none
  | (n, τ) :: rest, x => if n = x then some τ else lookupLiteTy rest x

inductive LiteHasType : LiteTyEnv → LiteExpr → LiteTy → Prop where
  | var :
      lookupLiteTy Γ x = some τ →
      LiteHasType Γ (.var x) τ
  | unit :
      LiteHasType Γ .unit .unit
  | bool :
      LiteHasType Γ (.bool b) .bool
  | int :
      LiteHasType Γ (.int n) .int
  | str :
      LiteHasType Γ (.str s) .string
  | tupleNil :
      LiteHasType Γ (.tuple []) (.tuple [])
  | tupleCons :
      LiteHasType Γ e τ →
      LiteHasType Γ (.tuple es) (.tuple ts) →
      LiteHasType Γ (.tuple (e :: es)) (.tuple (τ :: ts))
  | if_ :
      LiteHasType Γ c .bool →
      LiteHasType Γ t τ →
      LiteHasType Γ e τ →
      LiteHasType Γ (.ite c t e) τ

theorem lookupLite_nil (x : String) : lookupLite [] x = none := by
  rfl

theorem lookupLite_shadow (x : String) (v : LiteValue) (ρ : LiteEnv) :
    lookupLite ((x, v) :: ρ) x = some v := by
  simp [lookupLite]

theorem lookupLiteTy_nil (x : String) : lookupLiteTy [] x = none := by
  rfl

theorem lookupLiteTy_shadow (x : String) (τ : LiteTy) (Γ : LiteTyEnv) :
    lookupLiteTy ((x, τ) :: Γ) x = some τ := by
  simp [lookupLiteTy]

theorem lookupLite_deterministic
    (ρ : LiteEnv) (x : String) (v₁ v₂ : LiteValue)
    (h₁ : lookupLite ρ x = some v₁)
    (h₂ : lookupLite ρ x = some v₂) :
    v₁ = v₂ := by
  rw [h₁] at h₂
  injection h₂

theorem lookupLiteTy_deterministic
    (Γ : LiteTyEnv) (x : String) (τ₁ τ₂ : LiteTy)
    (h₁ : lookupLiteTy Γ x = some τ₁)
    (h₂ : lookupLiteTy Γ x = some τ₂) :
    τ₁ = τ₂ := by
  rw [h₁] at h₂
  injection h₂

theorem canonical_bool_lite
    (ρ : LiteEnv) (e : LiteExpr) (v : LiteValue)
    (hty : LiteHasType [] e .bool)
    (hev : LiteEval ρ e v) :
    ∃ b, v = .bool b := by
  revert hty
  induction hev with
  | var h =>
      intro hty
      cases hty with
      | var hlookup =>
          simp [lookupLiteTy] at hlookup
  | unit =>
      intro hty
      cases hty
  | bool =>
      intro hty
      cases hty with
      | bool =>
          exact ⟨_, rfl⟩
  | int =>
      intro hty
      cases hty
  | str =>
      intro hty
      cases hty
  | tupleNil =>
      intro hty
      cases hty
  | tupleCons he htail ihe iht =>
      intro hty
      cases hty
  | ifTrue hc ht ihc iht =>
      intro hty
      cases hty with
      | if_ hcond hthen helse =>
          exact iht hthen
  | ifFalse hc he ihc ihe =>
      intro hty
      cases hty with
      | if_ hcond hthen helse =>
          exact ihe helse

theorem canonical_unit_lite
    (ρ : LiteEnv) (e : LiteExpr) (v : LiteValue)
    (hty : LiteHasType [] e .unit)
    (hev : LiteEval ρ e v) :
    v = .unit := by
  revert hty
  induction hev with
  | var h =>
      intro hty
      cases hty with
      | var hlookup =>
          simp [lookupLiteTy] at hlookup
  | unit =>
      intro hty
      cases hty with
      | unit =>
          rfl
  | bool =>
      intro hty
      cases hty
  | int =>
      intro hty
      cases hty
  | str =>
      intro hty
      cases hty
  | tupleNil =>
      intro hty
      cases hty
  | tupleCons he htail ihe iht =>
      intro hty
      cases hty
  | ifTrue hc ht ihc iht =>
      intro hty
      cases hty with
      | if_ hcond hthen helse =>
          exact iht hthen
  | ifFalse hc he ihc ihe =>
      intro hty
      cases hty with
      | if_ hcond hthen helse =>
          exact ihe helse

theorem canonical_int_lite
    (ρ : LiteEnv) (e : LiteExpr) (v : LiteValue)
    (hty : LiteHasType [] e .int)
    (hev : LiteEval ρ e v) :
    ∃ n, v = .int n := by
  revert hty
  induction hev with
  | var h =>
      intro hty
      cases hty with
      | var hlookup =>
          simp [lookupLiteTy] at hlookup
  | unit =>
      intro hty
      cases hty
  | bool =>
      intro hty
      cases hty
  | int =>
      intro hty
      cases hty with
      | int =>
          exact ⟨_, rfl⟩
  | str =>
      intro hty
      cases hty
  | tupleNil =>
      intro hty
      cases hty
  | tupleCons he htail ihe iht =>
      intro hty
      cases hty
  | ifTrue hc ht ihc iht =>
      intro hty
      cases hty with
      | if_ hcond hthen helse =>
          exact iht hthen
  | ifFalse hc he ihc ihe =>
      intro hty
      cases hty with
      | if_ hcond hthen helse =>
          exact ihe helse

theorem canonical_string_lite
    (ρ : LiteEnv) (e : LiteExpr) (v : LiteValue)
    (hty : LiteHasType [] e .string)
    (hev : LiteEval ρ e v) :
    ∃ s, v = .str s := by
  revert hty
  induction hev with
  | var h =>
      intro hty
      cases hty with
      | var hlookup =>
          simp [lookupLiteTy] at hlookup
  | unit =>
      intro hty
      cases hty
  | bool =>
      intro hty
      cases hty
  | int =>
      intro hty
      cases hty
  | str =>
      intro hty
      cases hty with
      | str =>
          exact ⟨_, rfl⟩
  | tupleNil =>
      intro hty
      cases hty
  | tupleCons he htail ihe iht =>
      intro hty
      cases hty
  | ifTrue hc ht ihc iht =>
      intro hty
      cases hty with
      | if_ hcond hthen helse =>
          exact iht hthen
  | ifFalse hc he ihc ihe =>
      intro hty
      cases hty with
      | if_ hcond hthen helse =>
          exact ihe helse

theorem progress_unit_lite
    (ρ : LiteEnv) :
    ∃ v, LiteEval ρ .unit v := by
  exact ⟨.unit, LiteEval.unit⟩

theorem progress_bool_lite
    (ρ : LiteEnv) (b : Bool) :
    ∃ v, LiteEval ρ (.bool b) v := by
  exact ⟨.bool b, LiteEval.bool⟩

theorem progress_int_lite
    (ρ : LiteEnv) (n : Int) :
    ∃ v, LiteEval ρ (.int n) v := by
  exact ⟨.int n, LiteEval.int⟩

theorem progress_string_lite
    (ρ : LiteEnv) (s : String) :
    ∃ v, LiteEval ρ (.str s) v := by
  exact ⟨.str s, LiteEval.str⟩

theorem progress_tuple_nil_lite
    (ρ : LiteEnv) :
    ∃ v, LiteEval ρ (.tuple []) v := by
  exact ⟨.tuple [], LiteEval.tupleNil⟩

theorem progress_tuple_cons_lite
    (ρ : LiteEnv) (e : LiteExpr) (es : List LiteExpr)
    (v : LiteValue) (vs : List LiteValue)
    (he : LiteEval ρ e v)
    (hes : LiteEval ρ (.tuple es) (.tuple vs)) :
    ∃ out, LiteEval ρ (.tuple (e :: es)) out := by
  exact ⟨.tuple (v :: vs), LiteEval.tupleCons he hes⟩

theorem progress_if_true_lite
    (ρ : LiteEnv) (c t e : LiteExpr) (v : LiteValue)
    (hc : LiteEval ρ c (.bool true))
    (ht : LiteEval ρ t v) :
    ∃ out, LiteEval ρ (.ite c t e) out := by
  exact ⟨v, LiteEval.ifTrue hc ht⟩

theorem progress_if_false_lite
    (ρ : LiteEnv) (c t e : LiteExpr) (v : LiteValue)
    (hc : LiteEval ρ c (.bool false))
    (he : LiteEval ρ e v) :
    ∃ out, LiteEval ρ (.ite c t e) out := by
  exact ⟨v, LiteEval.ifFalse hc he⟩

end Fo
