import «Fo».Syntax
import «Fo».Semantics

namespace Fo

abbrev MatchSubst := List (String × Value)

def matchDomain (σ : MatchSubst) : List String :=
  σ.map Prod.fst

def MatchSubstUnique (σ : MatchSubst) : Prop :=
  List.Nodup (matchDomain σ)

inductive CoreMatchRel : Pattern → Value → MatchSubst → Prop where
  | wild :
      CoreMatchRel Pattern.wild v []
  | binder :
      CoreMatchRel (Pattern.binder x) v [(x, v)]
  | tupleExact :
      MatchSubstUnique σ →
      CoreMatchRel (Pattern.tuple ps) (Value.tuple vs) σ
  | ctorExact :
      MatchSubstUnique σ →
      CoreMatchRel (Pattern.ctor name ps) (Value.ctorV name vs) σ
  | structExact :
      MatchSubstUnique σ →
      CoreMatchRel (Pattern.struct name fs) (Value.structV name vs) σ

def BranchMatches (p : Pattern) (v : Value) : Prop :=
  ∃ σ, CoreMatchRel p v σ

theorem coreMatch_branch_unique
    (p : Pattern) (v : Value) (σ₁ σ₂ : MatchSubst)
    (hp : p = Pattern.wild ∨ ∃ x, p = Pattern.binder x)
    (h₁ : CoreMatchRel p v σ₁)
    (h₂ : CoreMatchRel p v σ₂) :
    σ₁ = σ₂ := by
  rcases hp with hpw | ⟨x, hpb⟩
  · subst hpw
    cases h₁ with
    | wild =>
        cases h₂ with
        | wild =>
            rfl
  · subst hpb
    cases h₁ with
    | binder =>
        cases h₂ with
        | binder =>
            rfl

theorem coreMatch_binding_sound
    (x : String) (v : Value) :
    CoreMatchRel (Pattern.binder x) v [(x, v)] := by
  exact CoreMatchRel.binder

theorem coreMatch_wild_only
    (v : Value) (σ : MatchSubst)
    (h : CoreMatchRel Pattern.wild v σ) :
    σ = [] := by
  cases h
  rfl

theorem coreMatch_binder_only
    (x : String) (v : Value) (σ : MatchSubst)
    (h : CoreMatchRel (Pattern.binder x) v σ) :
    σ = [(x, v)] := by
  cases h
  rfl

theorem coreMatch_wild_domain_empty
    (v : Value) (σ : MatchSubst)
    (h : CoreMatchRel Pattern.wild v σ) :
    matchDomain σ = [] := by
  rw [coreMatch_wild_only v σ h]
  rfl

theorem coreMatch_binder_domain_singleton
    (x : String) (v : Value) (σ : MatchSubst)
    (h : CoreMatchRel (Pattern.binder x) v σ) :
    matchDomain σ = [x] := by
  rw [coreMatch_binder_only x v σ h]
  rfl

theorem coreMatch_tuple_exact
    (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (hσ : MatchSubstUnique σ) :
    CoreMatchRel (Pattern.tuple ps) (Value.tuple vs) σ := by
  exact CoreMatchRel.tupleExact hσ

theorem coreMatch_ctor_exact
    (name : String) (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (hσ : MatchSubstUnique σ) :
    CoreMatchRel (Pattern.ctor name ps) (Value.ctorV name vs) σ := by
  exact CoreMatchRel.ctorExact hσ

theorem coreMatch_struct_exact
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : MatchSubst)
    (hσ : MatchSubstUnique σ) :
    CoreMatchRel (Pattern.struct name fs) (Value.structV name vs) σ := by
  exact CoreMatchRel.structExact hσ

theorem coreMatch_tuple_unique
    (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (h : CoreMatchRel (Pattern.tuple ps) (Value.tuple vs) σ) :
    MatchSubstUnique σ := by
  cases h with
  | tupleExact hσ =>
      exact hσ

theorem coreMatch_ctor_unique
    (name : String) (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (h : CoreMatchRel (Pattern.ctor name ps) (Value.ctorV name vs) σ) :
    MatchSubstUnique σ := by
  cases h with
  | ctorExact hσ =>
      exact hσ

theorem coreMatch_struct_unique
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : MatchSubst)
    (h : CoreMatchRel (Pattern.struct name fs) (Value.structV name vs) σ) :
    MatchSubstUnique σ := by
  cases h with
  | structExact hσ =>
      exact hσ

theorem coreMatch_progress_tuple_exact
    (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (hσ : MatchSubstUnique σ) :
    BranchMatches (Pattern.tuple ps) (Value.tuple vs) := by
  exact ⟨σ, CoreMatchRel.tupleExact hσ⟩

theorem coreMatch_progress_ctor_exact
    (name : String) (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (hσ : MatchSubstUnique σ) :
    BranchMatches (Pattern.ctor name ps) (Value.ctorV name vs) := by
  exact ⟨σ, CoreMatchRel.ctorExact hσ⟩

theorem coreMatch_progress_struct_exact
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : MatchSubst)
    (hσ : MatchSubstUnique σ) :
    BranchMatches (Pattern.struct name fs) (Value.structV name vs) := by
  exact ⟨σ, CoreMatchRel.structExact hσ⟩

theorem coreMatch_progress_wild
    (v : Value) :
    BranchMatches Pattern.wild v := by
  exact ⟨[], CoreMatchRel.wild⟩

theorem coreMatch_progress_binder
    (x : String) (v : Value) :
    BranchMatches (Pattern.binder x) v := by
  exact ⟨[(x, v)], CoreMatchRel.binder⟩

theorem coreMatch_progress
    (p : Pattern) (v : Value) :
    (p = Pattern.wild ∨ ∃ x, p = Pattern.binder x) →
    BranchMatches p v := by
  intro h
  cases h with
  | inl hw =>
      subst hw
      exact coreMatch_progress_wild v
  | inr hb =>
      rcases hb with ⟨x, hx⟩
      subst hx
      exact coreMatch_progress_binder x v

end Fo
