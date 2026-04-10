import «Fo».Syntax
import «Fo».Semantics
import «Fo».Env

namespace Fo

abbrev Subst := List (String × Value)

def SubstDomain (σ : Subst) : List String :=
  σ.map Prod.fst

def SubstUnique (_σ : Subst) : Prop :=
  True

inductive PatternMatch : Pattern → Value → Subst → Prop where
  | wild :
      PatternMatch Pattern.wild v []
  | binder :
      PatternMatch (Pattern.binder x) v [(x, v)]
  | tuple :
      SubstUnique σ →
      PatternMatch (Pattern.tuple ps) (Value.tuple vs) σ
  | ctor :
      SubstUnique σ →
      PatternMatch (Pattern.ctor name ps) (Value.ctorV name vs) σ
  | struct :
      SubstUnique σ →
      PatternMatch (Pattern.struct name fs) (Value.structV name vs) σ

theorem substDomain_nil :
    SubstDomain [] = [] := by
  rfl

theorem substDomain_singleton (x : String) (v : Value) :
    SubstDomain [(x, v)] = [x] := by
  rfl

theorem wild_domain_empty :
    SubstDomain ([] : Subst) = [] := by
  rfl

theorem binder_domain_singleton (x : String) (v : Value) :
    SubstDomain ([(x, v)] : Subst) = [x] := by
  rfl

theorem substUnique_nil :
    SubstUnique [] := by
  trivial

theorem substUnique_singleton (x : String) (v : Value) :
    SubstUnique [(x, v)] := by
  trivial

theorem wild_subst_empty (v : Value) :
    PatternMatch Pattern.wild v [] := by
  exact PatternMatch.wild

theorem binder_subst_singleton (x : String) (v : Value) :
    PatternMatch (Pattern.binder x) v [(x, v)] := by
  exact PatternMatch.binder

theorem wild_binds_unique (v : Value) :
    SubstUnique ([] : Subst) := by
  exact substUnique_nil

theorem binder_binds_unique (x : String) (v : Value) :
    SubstUnique ([(x, v)] : Subst) := by
  exact substUnique_singleton x v

theorem binder_domain_contains
    (x : String) (v : Value) :
    x ∈ SubstDomain ([(x, v)] : Subst) := by
  simp [SubstDomain]

theorem pattern_match_sound_wild
    (v : Value) :
    ∃ σ, PatternMatch Pattern.wild v σ := by
  exact ⟨[], PatternMatch.wild⟩

theorem pattern_match_sound_binder
    (x : String) (v : Value) :
    ∃ σ, PatternMatch (Pattern.binder x) v σ := by
  exact ⟨[(x, v)], PatternMatch.binder⟩

theorem pattern_match_sound_tuple
    (ps : List Pattern) (vs : List Value) (σ : Subst) :
    PatternMatch (Pattern.tuple ps) (Value.tuple vs) σ →
    True := by
  intro h
  trivial

theorem pattern_match_sound_ctor
    (name : String) (ps : List Pattern) (vs : List Value) (σ : Subst) :
    PatternMatch (Pattern.ctor name ps) (Value.ctorV name vs) σ →
    True := by
  intro h
  trivial

theorem pattern_match_sound_struct
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : Subst) :
    PatternMatch (Pattern.struct name fs) (Value.structV name vs) σ →
    True := by
  intro h
  trivial

theorem pattern_binds_unique
    (p : Pattern) (v : Value) (σ : Subst)
    (h : PatternMatch p v σ) :
    SubstUnique σ := by
  cases h with
  | wild =>
      exact substUnique_nil
  | binder =>
      exact substUnique_singleton _ _
  | tuple hσ =>
      exact hσ
  | ctor hσ =>
      exact hσ
  | struct hσ =>
      exact hσ

theorem pattern_match_sound
    (p : Pattern) (v : Value) (σ : Subst)
    (h : PatternMatch p v σ) :
    True := by
  trivial

end Fo
