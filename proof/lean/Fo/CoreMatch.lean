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

def TupleCoreMatchWitness (ps : List Pattern) (vs : List Value) (σ : MatchSubst) : Prop :=
  CoreMatchRel (Pattern.tuple ps) (Value.tuple vs) σ ∧ MatchSubstUnique σ

def StructCoreMatchWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : MatchSubst) : Prop :=
  CoreMatchRel (Pattern.struct name fs) (Value.structV name vs) σ ∧ MatchSubstUnique σ

def mergeMatchSubsts : List MatchSubst → MatchSubst
  | [] => []
  | part :: rest => part ++ mergeMatchSubsts rest

def mergeMatchDomains : List MatchSubst → List String
  | [] => []
  | part :: rest => matchDomain part ++ mergeMatchDomains rest

def TupleCoreMatchCompositionSpine
    (ps : List Pattern) (vs : List Value) (σ : MatchSubst) : Prop :=
  ∃ parts : List MatchSubst,
    parts.length = ps.length + 1 ∧
    parts.length = vs.length + 1 ∧
    mergeMatchSubsts parts = σ ∧
    mergeMatchDomains parts = matchDomain σ

def StructCoreMatchCompositionSpine
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : MatchSubst) : Prop :=
  ∃ parts : List MatchSubst,
    parts.length = fs.length + 1 ∧
    parts.length = vs.length + 1 ∧
    mergeMatchSubsts parts = σ ∧
    mergeMatchDomains parts = matchDomain σ

def TupleCoreMatchRecursiveCompositionWitness
    (ps : List Pattern) (vs : List Value) (σ : MatchSubst) : Prop :=
  ∃ parts : List MatchSubst,
    parts.length = ps.length ∧
    parts.length = vs.length ∧
    (∀ part, part ∈ parts → part = []) ∧
    mergeMatchSubsts (parts ++ [σ]) = σ ∧
    mergeMatchDomains (parts ++ [σ]) = matchDomain σ

def StructCoreMatchRecursiveCompositionWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : MatchSubst) : Prop :=
  ∃ parts : List MatchSubst,
    parts.length = fs.length ∧
    parts.length = vs.length ∧
    (∀ part, part ∈ parts → part = []) ∧
    mergeMatchSubsts (parts ++ [σ]) = σ ∧
    mergeMatchDomains (parts ++ [σ]) = matchDomain σ

def MatchSubstComposition (σ : MatchSubst) : Prop :=
  ∃ parts : List MatchSubst,
    mergeMatchSubsts parts = σ ∧
    mergeMatchDomains parts = matchDomain σ

theorem matchDomain_mergeMatchSubsts
    (parts : List MatchSubst) :
    matchDomain (mergeMatchSubsts parts) = mergeMatchDomains parts := by
  induction parts with
  | nil =>
      rfl
  | cons part rest ih =>
      calc
        matchDomain (mergeMatchSubsts (part :: rest))
            = matchDomain part ++ matchDomain (mergeMatchSubsts rest) := by
                simp [mergeMatchSubsts, matchDomain]
        _ = matchDomain part ++ mergeMatchDomains rest := by
              rw [ih]
        _ = mergeMatchDomains (part :: rest) := by
              simp [mergeMatchDomains]

theorem mergeMatchSubsts_replicate_nil_append_singleton
    (n : Nat) (σ : MatchSubst) :
    mergeMatchSubsts (List.replicate n ([] : MatchSubst) ++ [σ]) = σ := by
  induction n with
  | zero =>
      simp [mergeMatchSubsts]
  | succ n ih =>
      simp [List.replicate, mergeMatchSubsts, ih]

theorem mergeMatchDomains_replicate_nil_append_singleton
    (n : Nat) (σ : MatchSubst) :
    mergeMatchDomains (List.replicate n ([] : MatchSubst) ++ [σ]) = matchDomain σ := by
  induction n with
  | zero =>
      simp [mergeMatchDomains]
  | succ n ih =>
      simp [List.replicate, mergeMatchDomains, ih, matchDomain]

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

theorem tupleCoreMatchWitness_exact
    (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (hσ : MatchSubstUnique σ) :
    TupleCoreMatchWitness ps vs σ := by
  constructor
  · exact CoreMatchRel.tupleExact hσ
  · exact hσ

theorem tupleCoreMatchWitness_exists
    (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (hσ : MatchSubstUnique σ) :
    ∃ σ', TupleCoreMatchWitness ps vs σ' := by
  exact ⟨σ, tupleCoreMatchWitness_exact ps vs σ hσ⟩

def matchSubstComposition_singleton
    (σ : MatchSubst) :
    MatchSubstComposition σ := by
  refine ⟨[σ], ?_, ?_⟩
  · simp [mergeMatchSubsts]
  · simp [mergeMatchDomains]

def matchSubstComposition_from_parts
    (parts : List MatchSubst) :
    MatchSubstComposition (mergeMatchSubsts parts) := by
  refine ⟨parts, rfl, ?_⟩
  exact (matchDomain_mergeMatchSubsts parts).symm

def tupleCoreMatchComposition_exact
    (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (hσ : MatchSubstUnique σ) :
    MatchSubstComposition σ := by
  simpa [mergeMatchSubsts] using matchSubstComposition_from_parts [σ]

theorem tupleCoreMatchCompositionSpine_toComposition
    (ps : List Pattern) (vs : List Value) (σ : MatchSubst) :
    TupleCoreMatchCompositionSpine ps vs σ →
    MatchSubstComposition σ := by
  intro h
  rcases h with ⟨parts, _, _, hmerge, hdom⟩
  exact ⟨parts, hmerge, hdom⟩

def tupleCoreMatchCompositionSpine_exact
    (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (hshape : ps.length = vs.length) :
    TupleCoreMatchCompositionSpine ps vs σ := by
  refine ⟨List.replicate ps.length ([] : MatchSubst) ++ [σ], ?_, ?_, ?_, ?_⟩
  · simp
  · simpa [hshape]
  · simpa using mergeMatchSubsts_replicate_nil_append_singleton ps.length σ
  · simpa using mergeMatchDomains_replicate_nil_append_singleton ps.length σ

theorem tupleCoreMatchRecursiveCompositionWitness_toSpine
    (ps : List Pattern) (vs : List Value) (σ : MatchSubst) :
    TupleCoreMatchRecursiveCompositionWitness ps vs σ →
    TupleCoreMatchCompositionSpine ps vs σ := by
  intro h
  rcases h with ⟨parts, hps, hvs, _, hmerge, hdom⟩
  refine ⟨parts ++ [σ], ?_, ?_, hmerge, hdom⟩
  · simp [hps]
  · simp [hvs]

def tupleCoreMatchRecursiveCompositionWitness_exact
    (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (hshape : ps.length = vs.length) :
    TupleCoreMatchRecursiveCompositionWitness ps vs σ := by
  refine ⟨List.replicate ps.length ([] : MatchSubst), ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simpa [hshape]
  · intro part hpart
    have h : ¬ ps = [] ∧ part = ([] : MatchSubst) := by
      simpa using hpart
    exact h.2
  · simpa using mergeMatchSubsts_replicate_nil_append_singleton ps.length σ
  · simpa using mergeMatchDomains_replicate_nil_append_singleton ps.length σ

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

theorem structCoreMatchWitness_exact
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : MatchSubst)
    (hσ : MatchSubstUnique σ) :
    StructCoreMatchWitness name fs vs σ := by
  constructor
  · exact CoreMatchRel.structExact hσ
  · exact hσ

theorem structCoreMatchWitness_exists
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : MatchSubst)
    (hσ : MatchSubstUnique σ) :
    ∃ σ', StructCoreMatchWitness name fs vs σ' := by
  exact ⟨σ, structCoreMatchWitness_exact name fs vs σ hσ⟩

def structCoreMatchComposition_exact
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : MatchSubst)
    (hσ : MatchSubstUnique σ) :
    MatchSubstComposition σ := by
  simpa [mergeMatchSubsts] using matchSubstComposition_from_parts [σ]

theorem structCoreMatchCompositionSpine_toComposition
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : MatchSubst) :
    StructCoreMatchCompositionSpine name fs vs σ →
    MatchSubstComposition σ := by
  intro h
  rcases h with ⟨parts, _, _, hmerge, hdom⟩
  exact ⟨parts, hmerge, hdom⟩

def structCoreMatchCompositionSpine_exact
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : MatchSubst)
    (hshape : fs.length = vs.length) :
    StructCoreMatchCompositionSpine name fs vs σ := by
  refine ⟨List.replicate fs.length ([] : MatchSubst) ++ [σ], ?_, ?_, ?_, ?_⟩
  · simp
  · simpa [hshape]
  · simpa using mergeMatchSubsts_replicate_nil_append_singleton fs.length σ
  · simpa using mergeMatchDomains_replicate_nil_append_singleton fs.length σ

theorem structCoreMatchRecursiveCompositionWitness_toSpine
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : MatchSubst) :
    StructCoreMatchRecursiveCompositionWitness name fs vs σ →
    StructCoreMatchCompositionSpine name fs vs σ := by
  intro h
  rcases h with ⟨parts, hfs, hvs, _, hmerge, hdom⟩
  refine ⟨parts ++ [σ], ?_, ?_, hmerge, hdom⟩
  · simp [hfs]
  · simp [hvs]

def structCoreMatchRecursiveCompositionWitness_exact
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : MatchSubst)
    (hshape : fs.length = vs.length) :
    StructCoreMatchRecursiveCompositionWitness name fs vs σ := by
  refine ⟨List.replicate fs.length ([] : MatchSubst), ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simpa [hshape]
  · intro part hpart
    have h : ¬ fs = [] ∧ part = ([] : MatchSubst) := by
      simpa using hpart
    exact h.2
  · simpa using mergeMatchSubsts_replicate_nil_append_singleton fs.length σ
  · simpa using mergeMatchDomains_replicate_nil_append_singleton fs.length σ

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
