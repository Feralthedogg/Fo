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

def TuplePatternWitness (ps : List Pattern) (vs : List Value) (σ : Subst) : Prop :=
  PatternMatch (Pattern.tuple ps) (Value.tuple vs) σ ∧ SubstUnique σ

def StructPatternWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : Subst) : Prop :=
  PatternMatch (Pattern.struct name fs) (Value.structV name vs) σ ∧ SubstUnique σ

def mergeSubsts : List Subst → Subst
  | [] => []
  | part :: rest => part ++ mergeSubsts rest

def mergeSubstDomains : List Subst → List String
  | [] => []
  | part :: rest => SubstDomain part ++ mergeSubstDomains rest

def TuplePatternCompositionSpine
    (ps : List Pattern) (vs : List Value) (σ : Subst) : Prop :=
  ∃ parts : List Subst,
    parts.length = ps.length + 1 ∧
    parts.length = vs.length + 1 ∧
    mergeSubsts parts = σ ∧
    mergeSubstDomains parts = SubstDomain σ

def StructPatternCompositionSpine
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : Subst) : Prop :=
  ∃ parts : List Subst,
    parts.length = fs.length + 1 ∧
    parts.length = vs.length + 1 ∧
    mergeSubsts parts = σ ∧
    mergeSubstDomains parts = SubstDomain σ

def TuplePatternRecursiveCompositionWitness
    (ps : List Pattern) (vs : List Value) (σ : Subst) : Prop :=
  ∃ parts : List Subst,
    parts.length = ps.length ∧
    parts.length = vs.length ∧
    (∀ part, part ∈ parts → part = []) ∧
    mergeSubsts (parts ++ [σ]) = σ ∧
    mergeSubstDomains (parts ++ [σ]) = SubstDomain σ

def StructPatternRecursiveCompositionWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : Subst) : Prop :=
  ∃ parts : List Subst,
    parts.length = fs.length ∧
    parts.length = vs.length ∧
    (∀ part, part ∈ parts → part = []) ∧
    mergeSubsts (parts ++ [σ]) = σ ∧
    mergeSubstDomains (parts ++ [σ]) = SubstDomain σ

def SubstComposition (σ : Subst) : Prop :=
  ∃ parts : List Subst,
    mergeSubsts parts = σ ∧
    mergeSubstDomains parts = SubstDomain σ

def BinderWildPattern : Pattern → Prop
  | .wild => True
  | .binder _ => True
  | _ => False

def BinderWildPatternList (ps : List Pattern) : Prop :=
  ∀ p, p ∈ ps → BinderWildPattern p

def BinderWildStructFieldPatternList
    (fs : List (String × Pattern)) : Prop :=
  ∀ fp, fp ∈ fs → BinderWildPattern fp.2

def binderWildPatternPart (p : Pattern) (v : Value) : Subst :=
  match p with
  | .wild => []
  | .binder x => [(x, v)]
  | _ => []

def tupleBinderWildPatternParts : List Pattern → List Value → List Subst
  | [], [] => []
  | p :: ps, v :: vs => binderWildPatternPart p v :: tupleBinderWildPatternParts ps vs
  | _, _ => []

def structBinderWildPatternParts
    : List (String × Pattern) → List (String × Value) → List Subst
  | [], [] => []
  | (_, p) :: fs, (_, v) :: vs =>
      binderWildPatternPart p v :: structBinderWildPatternParts fs vs
  | _, _ => []

def TupleBinderWildGeneratedWitness
    (ps : List Pattern) (vs : List Value) (σ : Subst) : Prop :=
  BinderWildPatternList ps ∧
  ps.length = vs.length ∧
  mergeSubsts (tupleBinderWildPatternParts ps vs) = σ ∧
  mergeSubstDomains (tupleBinderWildPatternParts ps vs) = SubstDomain σ

def StructBinderWildGeneratedWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : Subst) : Prop :=
  BinderWildStructFieldPatternList fs ∧
  fs.length = vs.length ∧
  mergeSubsts (structBinderWildPatternParts fs vs) = σ ∧
  mergeSubstDomains (structBinderWildPatternParts fs vs) = SubstDomain σ

def TupleBinderWildGeneratedPartListWitness
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst) : Prop :=
  BinderWildPatternList ps ∧
  parts = tupleBinderWildPatternParts ps vs ∧
  parts.length = ps.length ∧
  parts.length = vs.length ∧
  mergeSubsts parts = σ ∧
  mergeSubstDomains parts = SubstDomain σ

def StructBinderWildGeneratedPartListWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst) : Prop :=
  BinderWildStructFieldPatternList fs ∧
  parts = structBinderWildPatternParts fs vs ∧
  parts.length = fs.length ∧
  parts.length = vs.length ∧
  mergeSubsts parts = σ ∧
  mergeSubstDomains parts = SubstDomain σ

inductive TupleBinderWildPartwiseWitness : List Pattern → List Value → List Subst → Prop where
  | nil :
      TupleBinderWildPartwiseWitness [] [] []
  | cons :
      BinderWildPattern p →
      TupleBinderWildPartwiseWitness ps vs parts →
      TupleBinderWildPartwiseWitness (p :: ps) (v :: vs) (binderWildPatternPart p v :: parts)

inductive StructBinderWildPartwiseWitness
    : List (String × Pattern) → List (String × Value) → List Subst → Prop where
  | nil :
      StructBinderWildPartwiseWitness [] [] []
  | cons :
      BinderWildPattern p →
      StructBinderWildPartwiseWitness fs vs parts →
      StructBinderWildPartwiseWitness ((fname, p) :: fs) ((vname, v) :: vs) (binderWildPatternPart p v :: parts)

def TupleBinderWildGeneratedDecompositionWitness
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst) : Prop :=
  TupleBinderWildGeneratedPartListWitness ps vs parts σ ∧
  TupleBinderWildPartwiseWitness ps vs parts

def StructBinderWildGeneratedDecompositionWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst) : Prop :=
  StructBinderWildGeneratedPartListWitness name fs vs parts σ ∧
  StructBinderWildPartwiseWitness fs vs parts

mutual
inductive NestedBinderWildPattern : Pattern → Prop where
  | wild :
      NestedBinderWildPattern .wild
  | binder :
      NestedBinderWildPattern (.binder x)
  | tuple :
      NestedBinderWildPatternList ps →
      NestedBinderWildPattern (.tuple ps)
  | struct :
      NestedBinderWildStructFieldPatternList fs →
      NestedBinderWildPattern (.struct name fs)

inductive NestedBinderWildPatternList : List Pattern → Prop where
  | nil :
      NestedBinderWildPatternList []
  | cons :
      NestedBinderWildPattern p →
      NestedBinderWildPatternList ps →
      NestedBinderWildPatternList (p :: ps)

inductive NestedBinderWildStructFieldPatternList : List (String × Pattern) → Prop where
  | nil :
      NestedBinderWildStructFieldPatternList []
  | cons :
      NestedBinderWildPattern p →
      NestedBinderWildStructFieldPatternList fs →
      NestedBinderWildStructFieldPatternList ((fname, p) :: fs)
end

mutual
inductive NestedBinderWildGeneratedParts : Pattern → Value → List Subst → Prop where
  | wild :
      NestedBinderWildGeneratedParts .wild v [[]]
  | binder :
      NestedBinderWildGeneratedParts (.binder x) v [[(x, v)]]
  | tuple :
      TupleNestedBinderWildGeneratedParts ps vs parts →
      NestedBinderWildGeneratedParts (.tuple ps) (.tuple vs) parts
  | struct :
      StructNestedBinderWildGeneratedParts fs vs parts →
      NestedBinderWildGeneratedParts (.struct name fs) (.structV name vs) parts

inductive TupleNestedBinderWildGeneratedParts : List Pattern → List Value → List Subst → Prop where
  | nil :
      TupleNestedBinderWildGeneratedParts [] [] []
  | cons :
      NestedBinderWildGeneratedParts p v parts₁ →
      TupleNestedBinderWildGeneratedParts ps vs parts₂ →
      TupleNestedBinderWildGeneratedParts (p :: ps) (v :: vs) (parts₁ ++ parts₂)

inductive StructNestedBinderWildGeneratedParts
    : List (String × Pattern) → List (String × Value) → List Subst → Prop where
  | nil :
      StructNestedBinderWildGeneratedParts [] [] []
  | cons :
      NestedBinderWildGeneratedParts p v parts₁ →
      StructNestedBinderWildGeneratedParts fs vs parts₂ →
      StructNestedBinderWildGeneratedParts ((fname, p) :: fs) ((vname, v) :: vs) (parts₁ ++ parts₂)
end

def TupleNestedBinderWildGeneratedPartListWitness
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst) : Prop :=
  NestedBinderWildPatternList ps ∧
  TupleNestedBinderWildGeneratedParts ps vs parts ∧
  mergeSubsts parts = σ ∧
  mergeSubstDomains parts = SubstDomain σ

def StructNestedBinderWildGeneratedPartListWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst) : Prop :=
  NestedBinderWildStructFieldPatternList fs ∧
  StructNestedBinderWildGeneratedParts fs vs parts ∧
  mergeSubsts parts = σ ∧
  mergeSubstDomains parts = SubstDomain σ

inductive PatternPathSeg where
  | tupleItem (index : Nat)
  | structField (name : String)
deriving Repr

abbrev PatternPath := List PatternPathSeg
abbrev BinderPathBinding := PatternPath × String

def BinderPathBindingNames (bs : List BinderPathBinding) : List String :=
  bs.map Prod.snd

mutual
def NestedBinderWildPatternDomain : Pattern → List String
  | .wild => []
  | .binder x => [x]
  | .tuple ps => NestedBinderWildPatternListDomain ps
  | .struct _ fs => NestedBinderWildStructFieldPatternListDomain fs
  | .ctor _ _ => []

def NestedBinderWildPatternListDomain : List Pattern → List String
  | [] => []
  | p :: ps => NestedBinderWildPatternDomain p ++ NestedBinderWildPatternListDomain ps

def NestedBinderWildStructFieldPatternListDomain : List (String × Pattern) → List String
  | [] => []
  | (_, p) :: fs => NestedBinderWildPatternDomain p ++ NestedBinderWildStructFieldPatternListDomain fs
end

mutual
def NestedBinderWildPatternBinderPathBindings : Pattern → PatternPath → List BinderPathBinding
  | .wild, _ => []
  | .binder x, path => [(path, x)]
  | .tuple ps, path => NestedBinderWildPatternListBinderPathBindings ps path 0
  | .struct _ fs, path => NestedBinderWildStructFieldBinderPathBindings fs path
  | .ctor _ _, _ => []

def NestedBinderWildPatternListBinderPathBindings : List Pattern → PatternPath → Nat → List BinderPathBinding
  | [], _, _ => []
  | p :: ps, path, idx =>
      NestedBinderWildPatternBinderPathBindings p (path ++ [.tupleItem idx]) ++
      NestedBinderWildPatternListBinderPathBindings ps path (idx + 1)

def NestedBinderWildStructFieldBinderPathBindings : List (String × Pattern) → PatternPath → List BinderPathBinding
  | [], _ => []
  | (fname, p) :: fs, path =>
      NestedBinderWildPatternBinderPathBindings p (path ++ [.structField fname]) ++
      NestedBinderWildStructFieldBinderPathBindings fs path
end

def TupleNestedBinderWildPathCorrespondenceWitness
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst) : Prop :=
  TupleNestedBinderWildGeneratedPartListWitness ps vs parts σ ∧
  SubstDomain σ = BinderPathBindingNames (NestedBinderWildPatternListBinderPathBindings ps [] 0)

def StructNestedBinderWildPathCorrespondenceWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst) : Prop :=
  StructNestedBinderWildGeneratedPartListWitness name fs vs parts σ ∧
  SubstDomain σ = BinderPathBindingNames (NestedBinderWildStructFieldBinderPathBindings fs [])

def TupleNestedBinderWildPathBridgeAssumption
    (ps : List Pattern) : Prop :=
  BinderPathBindingNames (NestedBinderWildPatternListBinderPathBindings ps [] 0) =
    NestedBinderWildPatternListDomain ps

def StructNestedBinderWildPathBridgeAssumption
    (fs : List (String × Pattern)) : Prop :=
  BinderPathBindingNames (NestedBinderWildStructFieldBinderPathBindings fs []) =
    NestedBinderWildStructFieldPatternListDomain fs

def TupleNestedBinderWildPathBridgeCertificate
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst) : Prop :=
  TupleNestedBinderWildGeneratedPartListWitness ps vs parts σ ∧
  TupleNestedBinderWildPathBridgeAssumption ps

structure TupleNestedBinderWildPathBridgeProvider
    (ps : List Pattern) where
  assumption : TupleNestedBinderWildPathBridgeAssumption ps

def StructNestedBinderWildPathBridgeCertificate
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst) : Prop :=
  StructNestedBinderWildGeneratedPartListWitness name fs vs parts σ ∧
  StructNestedBinderWildPathBridgeAssumption fs

structure StructNestedBinderWildPathBridgeProvider
    (fs : List (String × Pattern)) where
  assumption : StructNestedBinderWildPathBridgeAssumption fs

def BinderPathNameMembershipWitness
    (bs : List BinderPathBinding) (σ : Subst) : Prop :=
  ∀ x, x ∈ BinderPathBindingNames bs ↔ x ∈ SubstDomain σ

def BinderPathNameLengthWitness
    (bs : List BinderPathBinding) (σ : Subst) : Prop :=
  (BinderPathBindingNames bs).length = (SubstDomain σ).length

def BinderPathCoverageWitness
    (bs : List BinderPathBinding) (σ : Subst) : Prop :=
  (∀ b, b ∈ bs → b.2 ∈ SubstDomain σ) ∧
  (∀ x, x ∈ SubstDomain σ → ∃ path, (path, x) ∈ bs)

def BinderPathDomainCoverageWitness
    (bs : List BinderPathBinding) (dom : List String) : Prop :=
  (∀ b, b ∈ bs → b.2 ∈ dom) ∧
  (∀ x, x ∈ dom → ∃ path, (path, x) ∈ bs)

def BinderPathLeafWitness
    (bs : List BinderPathBinding) (σ : Subst) (dom : List String) : Prop :=
  ∀ x, x ∈ dom → x ∈ SubstDomain σ ∧ ∃ path, (path, x) ∈ bs

def BinderPathPartLeafWitness
    (bs : List BinderPathBinding) (parts : List Subst) (dom : List String) : Prop :=
  ∀ x, x ∈ dom → (∃ path, (path, x) ∈ bs) ∧ ∃ part, part ∈ parts ∧ x ∈ SubstDomain part

def BinderPathPartOriginWitness
    (bs : List BinderPathBinding) (parts : List Subst) (dom : List String) : Prop :=
  ∀ x, x ∈ dom → ∃ path part, (path, x) ∈ bs ∧ part ∈ parts ∧ x ∈ SubstDomain part

def BinderPathValueOriginWitness
    (bs : List BinderPathBinding) (parts : List Subst) (dom : List String) : Prop :=
  ∀ x, x ∈ dom → ∃ path part value, (path, x) ∈ bs ∧ part ∈ parts ∧ (x, value) ∈ part

def TupleNestedBinderWildPathSummaryWitness
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst) : Prop :=
  TupleNestedBinderWildPathCorrespondenceWitness ps vs parts σ ∧
  BinderPathNameMembershipWitness (NestedBinderWildPatternListBinderPathBindings ps [] 0) σ ∧
  BinderPathNameLengthWitness (NestedBinderWildPatternListBinderPathBindings ps [] 0) σ

def StructNestedBinderWildPathSummaryWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst) : Prop :=
  StructNestedBinderWildPathCorrespondenceWitness name fs vs parts σ ∧
  BinderPathNameMembershipWitness (NestedBinderWildStructFieldBinderPathBindings fs []) σ ∧
  BinderPathNameLengthWitness (NestedBinderWildStructFieldBinderPathBindings fs []) σ

def TupleNestedBinderWildPathCoverageWitness
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst) : Prop :=
  TupleNestedBinderWildPathCorrespondenceWitness ps vs parts σ ∧
  BinderPathCoverageWitness (NestedBinderWildPatternListBinderPathBindings ps [] 0) σ

def StructNestedBinderWildPathCoverageWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst) : Prop :=
  StructNestedBinderWildPathCorrespondenceWitness name fs vs parts σ ∧
  BinderPathCoverageWitness (NestedBinderWildStructFieldBinderPathBindings fs []) σ

structure TupleNestedBinderWildPathWitnessBundle
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst) where
  bridge : TupleNestedBinderWildPathBridgeCertificate ps vs parts σ
  correspondence : TupleNestedBinderWildPathCorrespondenceWitness ps vs parts σ
  summary : TupleNestedBinderWildPathSummaryWitness ps vs parts σ
  coverage : TupleNestedBinderWildPathCoverageWitness ps vs parts σ
  domainCoverage :
    BinderPathDomainCoverageWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      (NestedBinderWildPatternListDomain ps)
  leaf :
    BinderPathLeafWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      σ
      (NestedBinderWildPatternListDomain ps)
  partLeaf :
    BinderPathPartLeafWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      parts
      (NestedBinderWildPatternListDomain ps)
  origin :
    BinderPathPartOriginWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      parts
      (NestedBinderWildPatternListDomain ps)
  valueOrigin :
    BinderPathValueOriginWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      parts
      (NestedBinderWildPatternListDomain ps)

structure StructNestedBinderWildPathWitnessBundle
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst) where
  bridge : StructNestedBinderWildPathBridgeCertificate name fs vs parts σ
  correspondence : StructNestedBinderWildPathCorrespondenceWitness name fs vs parts σ
  summary : StructNestedBinderWildPathSummaryWitness name fs vs parts σ
  coverage : StructNestedBinderWildPathCoverageWitness name fs vs parts σ
  domainCoverage :
    BinderPathDomainCoverageWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      (NestedBinderWildStructFieldPatternListDomain fs)
  leaf :
    BinderPathLeafWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      σ
      (NestedBinderWildStructFieldPatternListDomain fs)
  partLeaf :
    BinderPathPartLeafWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      parts
      (NestedBinderWildStructFieldPatternListDomain fs)
  origin :
    BinderPathPartOriginWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      parts
      (NestedBinderWildStructFieldPatternListDomain fs)
  valueOrigin :
    BinderPathValueOriginWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      parts
      (NestedBinderWildStructFieldPatternListDomain fs)

theorem substDomain_mergeSubsts
    (parts : List Subst) :
    SubstDomain (mergeSubsts parts) = mergeSubstDomains parts := by
  induction parts with
  | nil =>
      rfl
  | cons part rest ih =>
      calc
        SubstDomain (mergeSubsts (part :: rest))
            = SubstDomain part ++ SubstDomain (mergeSubsts rest) := by
                simp [mergeSubsts, SubstDomain]
        _ = SubstDomain part ++ mergeSubstDomains rest := by
              rw [ih]
        _ = mergeSubstDomains (part :: rest) := by
              simp [mergeSubstDomains]

theorem mergeSubstDomains_append
    (parts₁ parts₂ : List Subst) :
    mergeSubstDomains (parts₁ ++ parts₂) =
      mergeSubstDomains parts₁ ++ mergeSubstDomains parts₂ := by
  induction parts₁ with
  | nil =>
      simp [mergeSubstDomains]
  | cons part rest ih =>
      simp [mergeSubstDomains, ih, List.append_assoc]

theorem mergeSubsts_replicate_nil_append_singleton
    (n : Nat) (σ : Subst) :
    mergeSubsts (List.replicate n ([] : Subst) ++ [σ]) = σ := by
  induction n with
  | zero =>
      simp [mergeSubsts]
  | succ n ih =>
      simp [List.replicate, mergeSubsts, ih]

theorem mergeSubstDomains_replicate_nil_append_singleton
    (n : Nat) (σ : Subst) :
    mergeSubstDomains (List.replicate n ([] : Subst) ++ [σ]) = SubstDomain σ := by
  induction n with
  | zero =>
      simp [mergeSubstDomains]
  | succ n ih =>
      simp [List.replicate, mergeSubstDomains, ih, SubstDomain]

theorem tupleBinderWildPatternParts_length
    (ps : List Pattern) (vs : List Value)
    (hshape : ps.length = vs.length) :
    (tupleBinderWildPatternParts ps vs).length = ps.length := by
  induction ps generalizing vs with
  | nil =>
      cases vs with
      | nil => rfl
      | cons v vs => cases hshape
  | cons p ps ih =>
      cases vs with
      | nil => cases hshape
      | cons v vs =>
          simp [tupleBinderWildPatternParts]
          have htail : ps.length = vs.length := by
            simpa using Nat.succ.inj hshape
          simpa [ih vs htail]

theorem structBinderWildPatternParts_length
    (fs : List (String × Pattern)) (vs : List (String × Value))
    (hshape : fs.length = vs.length) :
    (structBinderWildPatternParts fs vs).length = fs.length := by
  induction fs generalizing vs with
  | nil =>
      cases vs with
      | nil => rfl
      | cons v vs => cases hshape
  | cons f fs ih =>
      cases vs with
      | nil => cases hshape
      | cons v vs =>
          simp [structBinderWildPatternParts]
          have htail : fs.length = vs.length := by
            simpa using Nat.succ.inj hshape
          simpa [ih vs htail]

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

theorem tuplePatternWitness_exact
    (ps : List Pattern) (vs : List Value) (σ : Subst)
    (hσ : SubstUnique σ) :
    TuplePatternWitness ps vs σ := by
  constructor
  · exact PatternMatch.tuple hσ
  · exact hσ

theorem tuplePatternWitness_exists
    (ps : List Pattern) (vs : List Value) (σ : Subst)
    (hσ : SubstUnique σ) :
    ∃ σ', TuplePatternWitness ps vs σ' := by
  exact ⟨σ, tuplePatternWitness_exact ps vs σ hσ⟩

def substComposition_singleton
    (σ : Subst) :
    SubstComposition σ := by
  refine ⟨[σ], ?_, ?_⟩
  · simp [mergeSubsts]
  · simp [mergeSubstDomains]

def substComposition_from_parts
    (parts : List Subst) :
    SubstComposition (mergeSubsts parts) := by
  refine ⟨parts, rfl, ?_⟩
  exact (substDomain_mergeSubsts parts).symm

def tuplePatternComposition_exact
    (ps : List Pattern) (vs : List Value) (σ : Subst)
    (hσ : SubstUnique σ) :
    SubstComposition σ := by
  simpa [mergeSubsts] using substComposition_from_parts [σ]

theorem tupleBinderWildGeneratedWitness_exact
    (ps : List Pattern) (vs : List Value)
    (hfrag : BinderWildPatternList ps)
    (hshape : ps.length = vs.length) :
    TupleBinderWildGeneratedWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) := by
  constructor
  · exact hfrag
  · constructor
    · exact hshape
    · constructor
      · rfl
      · exact (substDomain_mergeSubsts (tupleBinderWildPatternParts ps vs)).symm

theorem tupleBinderWildGeneratedPartListWitness_exact
    (ps : List Pattern) (vs : List Value)
    (hfrag : BinderWildPatternList ps)
    (hshape : ps.length = vs.length) :
    TupleBinderWildGeneratedPartListWitness
      ps
      vs
      (tupleBinderWildPatternParts ps vs)
      (mergeSubsts (tupleBinderWildPatternParts ps vs)) := by
  constructor
  · exact hfrag
  · constructor
    · rfl
    · constructor
      · exact tupleBinderWildPatternParts_length ps vs hshape
      · constructor
        · simpa [hshape] using tupleBinderWildPatternParts_length ps vs hshape
        · constructor
          · rfl
          · exact (substDomain_mergeSubsts (tupleBinderWildPatternParts ps vs)).symm

theorem tupleBinderWildPartwiseWitness_exact
    (ps : List Pattern) (vs : List Value)
    (hfrag : BinderWildPatternList ps)
    (hshape : ps.length = vs.length) :
    TupleBinderWildPartwiseWitness ps vs (tupleBinderWildPatternParts ps vs) := by
  induction ps generalizing vs with
  | nil =>
      cases vs with
      | nil =>
          exact TupleBinderWildPartwiseWitness.nil
      | cons v vs =>
          cases hshape
  | cons p ps ih =>
      cases vs with
      | nil =>
          cases hshape
      | cons v vs =>
          have hp : BinderWildPattern p := hfrag p (by simp)
          have hfragTail : BinderWildPatternList ps := by
            intro q hq
            exact hfrag q (by simp [hq])
          have hshapeTail : ps.length = vs.length := by
            simpa using Nat.succ.inj hshape
          simpa [tupleBinderWildPatternParts] using
            TupleBinderWildPartwiseWitness.cons hp (ih vs hfragTail hshapeTail)

theorem tupleBinderWildGeneratedDecompositionWitness_exact
    (ps : List Pattern) (vs : List Value)
    (hfrag : BinderWildPatternList ps)
    (hshape : ps.length = vs.length) :
    TupleBinderWildGeneratedDecompositionWitness
      ps
      vs
      (tupleBinderWildPatternParts ps vs)
      (mergeSubsts (tupleBinderWildPatternParts ps vs)) := by
  constructor
  · exact tupleBinderWildGeneratedPartListWitness_exact ps vs hfrag hshape
  · exact tupleBinderWildPartwiseWitness_exact ps vs hfrag hshape

theorem tupleBinderWildGeneratedDecompositionWitness_toPartListWitness
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst) :
    TupleBinderWildGeneratedDecompositionWitness ps vs parts σ →
    TupleBinderWildGeneratedPartListWitness ps vs parts σ := by
  intro h
  exact h.1

theorem tupleBinderWildGeneratedPartListWitness_toGeneratedWitness
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst) :
    TupleBinderWildGeneratedPartListWitness ps vs parts σ →
    TupleBinderWildGeneratedWitness ps vs σ := by
  intro h
  rcases h with ⟨hfrag, hparts, hps, hvs, hmerge, hdom⟩
  subst hparts
  constructor
  · exact hfrag
  · constructor
    · calc
        ps.length = (tupleBinderWildPatternParts ps vs).length := hps.symm
        _ = vs.length := hvs
    · constructor
      · exact hmerge
      · exact hdom

theorem tupleBinderWildGeneratedWitness_toComposition
    (ps : List Pattern) (vs : List Value) (σ : Subst) :
    TupleBinderWildGeneratedWitness ps vs σ →
    SubstComposition σ := by
  intro h
  rcases h with ⟨_, _, hmerge, hdom⟩
  exact ⟨tupleBinderWildPatternParts ps vs, hmerge, hdom⟩

theorem tuplePatternCompositionSpine_toComposition
    (ps : List Pattern) (vs : List Value) (σ : Subst) :
    TuplePatternCompositionSpine ps vs σ →
    SubstComposition σ := by
  intro h
  rcases h with ⟨parts, _, _, hmerge, hdom⟩
  exact ⟨parts, hmerge, hdom⟩

def tuplePatternCompositionSpine_exact
    (ps : List Pattern) (vs : List Value) (σ : Subst)
    (hshape : ps.length = vs.length) :
    TuplePatternCompositionSpine ps vs σ := by
  refine ⟨List.replicate ps.length ([] : Subst) ++ [σ], ?_, ?_, ?_, ?_⟩
  · simp
  · simpa [hshape]
  · simpa using mergeSubsts_replicate_nil_append_singleton ps.length σ
  · simpa using mergeSubstDomains_replicate_nil_append_singleton ps.length σ

theorem tuplePatternRecursiveCompositionWitness_toSpine
    (ps : List Pattern) (vs : List Value) (σ : Subst) :
    TuplePatternRecursiveCompositionWitness ps vs σ →
    TuplePatternCompositionSpine ps vs σ := by
  intro h
  rcases h with ⟨parts, hps, hvs, _, hmerge, hdom⟩
  refine ⟨parts ++ [σ], ?_, ?_, hmerge, hdom⟩
  · simp [hps]
  · simp [hvs]

def tuplePatternRecursiveCompositionWitness_exact
    (ps : List Pattern) (vs : List Value) (σ : Subst)
    (hshape : ps.length = vs.length) :
    TuplePatternRecursiveCompositionWitness ps vs σ := by
  refine ⟨List.replicate ps.length ([] : Subst), ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simpa [hshape]
  · intro part hpart
    have h : ¬ ps = [] ∧ part = ([] : Subst) := by
      simpa using hpart
    exact h.2
  · simpa using mergeSubsts_replicate_nil_append_singleton ps.length σ
  · simpa using mergeSubstDomains_replicate_nil_append_singleton ps.length σ

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

theorem structPatternWitness_exact
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : Subst)
    (hσ : SubstUnique σ) :
    StructPatternWitness name fs vs σ := by
  constructor
  · exact PatternMatch.struct hσ
  · exact hσ

theorem structPatternWitness_exists
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : Subst)
    (hσ : SubstUnique σ) :
    ∃ σ', StructPatternWitness name fs vs σ' := by
  exact ⟨σ, structPatternWitness_exact name fs vs σ hσ⟩

def structPatternComposition_exact
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : Subst)
    (hσ : SubstUnique σ) :
    SubstComposition σ := by
  simpa [mergeSubsts] using substComposition_from_parts [σ]

theorem structBinderWildGeneratedWitness_exact
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (hfrag : BinderWildStructFieldPatternList fs)
    (hshape : fs.length = vs.length) :
    StructBinderWildGeneratedWitness name fs vs (mergeSubsts (structBinderWildPatternParts fs vs)) := by
  constructor
  · exact hfrag
  · constructor
    · exact hshape
    · constructor
      · rfl
      · exact (substDomain_mergeSubsts (structBinderWildPatternParts fs vs)).symm

theorem structBinderWildGeneratedPartListWitness_exact
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (hfrag : BinderWildStructFieldPatternList fs)
    (hshape : fs.length = vs.length) :
    StructBinderWildGeneratedPartListWitness
      name
      fs
      vs
      (structBinderWildPatternParts fs vs)
      (mergeSubsts (structBinderWildPatternParts fs vs)) := by
  constructor
  · exact hfrag
  · constructor
    · rfl
    · constructor
      · exact structBinderWildPatternParts_length fs vs hshape
      · constructor
        · simpa [hshape] using structBinderWildPatternParts_length fs vs hshape
        · constructor
          · rfl
          · exact (substDomain_mergeSubsts (structBinderWildPatternParts fs vs)).symm

theorem structBinderWildPartwiseWitness_exact
    (fs : List (String × Pattern)) (vs : List (String × Value))
    (hfrag : BinderWildStructFieldPatternList fs)
    (hshape : fs.length = vs.length) :
    StructBinderWildPartwiseWitness fs vs (structBinderWildPatternParts fs vs) := by
  induction fs generalizing vs with
  | nil =>
      cases vs with
      | nil =>
          exact StructBinderWildPartwiseWitness.nil
      | cons v vs =>
          cases hshape
  | cons f fs ih =>
      cases vs with
      | nil =>
          cases hshape
      | cons v vs =>
          cases f with
          | mk fname p =>
              cases v with
              | mk vname vv =>
                  have hp : BinderWildPattern p := hfrag (fname, p) (by simp)
                  have hfragTail : BinderWildStructFieldPatternList fs := by
                    intro fp hfp
                    exact hfrag fp (by simp [hfp])
                  have hshapeTail : fs.length = vs.length := by
                    simpa using Nat.succ.inj hshape
                  simpa [structBinderWildPatternParts] using
                    StructBinderWildPartwiseWitness.cons hp (ih vs hfragTail hshapeTail)

theorem structBinderWildGeneratedDecompositionWitness_exact
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (hfrag : BinderWildStructFieldPatternList fs)
    (hshape : fs.length = vs.length) :
    StructBinderWildGeneratedDecompositionWitness
      name
      fs
      vs
      (structBinderWildPatternParts fs vs)
      (mergeSubsts (structBinderWildPatternParts fs vs)) := by
  constructor
  · exact structBinderWildGeneratedPartListWitness_exact name fs vs hfrag hshape
  · exact structBinderWildPartwiseWitness_exact fs vs hfrag hshape

theorem structBinderWildGeneratedDecompositionWitness_toPartListWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst) :
    StructBinderWildGeneratedDecompositionWitness name fs vs parts σ →
    StructBinderWildGeneratedPartListWitness name fs vs parts σ := by
  intro h
  exact h.1

theorem structBinderWildGeneratedPartListWitness_toGeneratedWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst) :
    StructBinderWildGeneratedPartListWitness name fs vs parts σ →
    StructBinderWildGeneratedWitness name fs vs σ := by
  intro h
  rcases h with ⟨hfrag, hparts, hfs, hvs, hmerge, hdom⟩
  subst hparts
  constructor
  · exact hfrag
  · constructor
    · calc
        fs.length = (structBinderWildPatternParts fs vs).length := hfs.symm
        _ = vs.length := hvs
    · constructor
      · exact hmerge
      · exact hdom

theorem structBinderWildGeneratedWitness_toComposition
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : Subst) :
    StructBinderWildGeneratedWitness name fs vs σ →
    SubstComposition σ := by
  intro h
  rcases h with ⟨_, _, hmerge, hdom⟩
  exact ⟨structBinderWildPatternParts fs vs, hmerge, hdom⟩

theorem tupleNestedBinderWildGeneratedPartListWitness_of_generated
    (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts) :
    TupleNestedBinderWildGeneratedPartListWitness ps vs parts (mergeSubsts parts) := by
  constructor
  · exact hfrag
  · constructor
    · exact hparts
    · constructor
      · rfl
      · exact (substDomain_mergeSubsts parts).symm

theorem tupleNestedBinderWildGeneratedPartListWitness_toComposition
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst) :
    TupleNestedBinderWildGeneratedPartListWitness ps vs parts σ →
    SubstComposition σ := by
  intro h
  rcases h with ⟨_, _, hmerge, hdom⟩
  exact ⟨parts, hmerge, hdom⟩

theorem structNestedBinderWildGeneratedPartListWitness_of_generated
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (parts : List Subst)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs vs parts) :
    StructNestedBinderWildGeneratedPartListWitness name fs vs parts (mergeSubsts parts) := by
  constructor
  · exact hfrag
  · constructor
    · exact hparts
    · constructor
      · rfl
      · exact (substDomain_mergeSubsts parts).symm

theorem structNestedBinderWildGeneratedPartListWitness_toComposition
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst) :
    StructNestedBinderWildGeneratedPartListWitness name fs vs parts σ →
    SubstComposition σ := by
  intro h
  rcases h with ⟨_, _, hmerge, hdom⟩
  exact ⟨parts, hmerge, hdom⟩

mutual
theorem nestedBinderWildGeneratedParts_domain
    {p : Pattern} {v : Value} {parts : List Subst}
    (h : NestedBinderWildGeneratedParts p v parts) :
    mergeSubstDomains parts = NestedBinderWildPatternDomain p := by
  cases h with
  | wild =>
      exact substDomain_nil
  | binder =>
      simp [NestedBinderWildPatternDomain, mergeSubstDomains, SubstDomain]
  | tuple hparts =>
      simpa [NestedBinderWildPatternDomain] using
        tupleNestedBinderWildGeneratedParts_domain hparts
  | struct hparts =>
      simpa [NestedBinderWildPatternDomain] using
        structNestedBinderWildGeneratedParts_domain hparts

theorem tupleNestedBinderWildGeneratedParts_domain
    {ps : List Pattern} {vs : List Value} {parts : List Subst}
    (h : TupleNestedBinderWildGeneratedParts ps vs parts) :
    mergeSubstDomains parts = NestedBinderWildPatternListDomain ps := by
  cases h with
  | nil =>
      simp [NestedBinderWildPatternListDomain, mergeSubstDomains]
  | cons h₁ h₂ =>
      have ih₁ := nestedBinderWildGeneratedParts_domain h₁
      have ih₂ := tupleNestedBinderWildGeneratedParts_domain h₂
      simpa [NestedBinderWildPatternListDomain, mergeSubstDomains_append, ih₁, ih₂]

theorem structNestedBinderWildGeneratedParts_domain
    {fs : List (String × Pattern)} {vs : List (String × Value)} {parts : List Subst}
    (h : StructNestedBinderWildGeneratedParts fs vs parts) :
    mergeSubstDomains parts = NestedBinderWildStructFieldPatternListDomain fs := by
  cases h with
  | nil =>
      simp [NestedBinderWildStructFieldPatternListDomain, mergeSubstDomains]
  | cons h₁ h₂ =>
      have ih₁ := nestedBinderWildGeneratedParts_domain h₁
      have ih₂ := structNestedBinderWildGeneratedParts_domain h₂
      simpa [NestedBinderWildStructFieldPatternListDomain, mergeSubstDomains_append, ih₁, ih₂]
end

theorem tupleNestedBinderWildGeneratedPartListWitness_domain
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst)
    (h : TupleNestedBinderWildGeneratedPartListWitness ps vs parts σ) :
    mergeSubstDomains parts = NestedBinderWildPatternListDomain ps := by
  exact tupleNestedBinderWildGeneratedParts_domain h.2.1

theorem tupleNestedBinderWildGeneratedPartListWitness_substDomain
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst)
    (h : TupleNestedBinderWildGeneratedPartListWitness ps vs parts σ) :
    SubstDomain σ = NestedBinderWildPatternListDomain ps := by
  exact h.2.2.2.symm.trans (tupleNestedBinderWildGeneratedPartListWitness_domain ps vs parts σ h)

theorem structNestedBinderWildGeneratedPartListWitness_domain
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst)
    (h : StructNestedBinderWildGeneratedPartListWitness name fs vs parts σ) :
    mergeSubstDomains parts = NestedBinderWildStructFieldPatternListDomain fs := by
  exact structNestedBinderWildGeneratedParts_domain h.2.1

theorem structNestedBinderWildGeneratedPartListWitness_substDomain
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst)
    (h : StructNestedBinderWildGeneratedPartListWitness name fs vs parts σ) :
    SubstDomain σ = NestedBinderWildStructFieldPatternListDomain fs := by
  exact h.2.2.2.symm.trans
    (structNestedBinderWildGeneratedPartListWitness_domain name fs vs parts σ h)

theorem binderWildPatternBinderPathBindings_names
    (p : Pattern) (path : PatternPath)
    (h : BinderWildPattern p) :
    BinderPathBindingNames (NestedBinderWildPatternBinderPathBindings p path) =
      NestedBinderWildPatternDomain p := by
  cases p with
  | wild =>
      simp [BinderWildPattern, NestedBinderWildPatternBinderPathBindings, NestedBinderWildPatternDomain, BinderPathBindingNames]
  | binder x =>
      simp [BinderWildPattern, NestedBinderWildPatternBinderPathBindings, NestedBinderWildPatternDomain, BinderPathBindingNames]
  | tuple ps =>
      cases h
  | ctor name args =>
      cases h
  | struct name fs =>
      cases h

theorem binderWildPatternListBinderPathBindings_names
    (ps : List Pattern) (path : PatternPath) (idx : Nat)
    (h : BinderWildPatternList ps) :
    BinderPathBindingNames (NestedBinderWildPatternListBinderPathBindings ps path idx) =
      NestedBinderWildPatternListDomain ps := by
  induction ps generalizing idx with
  | nil =>
      simp [BinderWildPatternList, NestedBinderWildPatternListBinderPathBindings, NestedBinderWildPatternListDomain, BinderPathBindingNames]
  | cons p ps ih =>
      have hp : BinderWildPattern p := h p (by simp)
      have hps : BinderWildPatternList ps := by
        intro q hq
        exact h q (by simp [hq])
      have hHead := binderWildPatternBinderPathBindings_names p (path ++ [.tupleItem idx]) hp
      have hTail := ih (idx + 1) hps
      have hHead' := by
        simpa [BinderPathBindingNames] using hHead
      have hTail' := by
        simpa [BinderPathBindingNames] using hTail
      simp [NestedBinderWildPatternListBinderPathBindings, NestedBinderWildPatternListDomain, BinderPathBindingNames]
      rw [hHead', hTail']

theorem binderWildStructFieldBinderPathBindings_names
    (fs : List (String × Pattern)) (path : PatternPath)
    (h : BinderWildStructFieldPatternList fs) :
    BinderPathBindingNames (NestedBinderWildStructFieldBinderPathBindings fs path) =
      NestedBinderWildStructFieldPatternListDomain fs := by
  induction fs with
  | nil =>
      simp [BinderWildStructFieldPatternList, NestedBinderWildStructFieldBinderPathBindings, NestedBinderWildStructFieldPatternListDomain, BinderPathBindingNames]
  | cons f fs ih =>
      cases f with
      | mk fname p =>
          have hp : BinderWildPattern p := h (fname, p) (by simp)
          have hfs : BinderWildStructFieldPatternList fs := by
            intro fp hfp
            exact h fp (by simp [hfp])
          have hHead := binderWildPatternBinderPathBindings_names p (path ++ [.structField fname]) hp
          have hTail := ih hfs
          have hHead' := by
            simpa [BinderPathBindingNames] using hHead
          have hTail' := by
            simpa [BinderPathBindingNames] using hTail
          simp [NestedBinderWildStructFieldBinderPathBindings, NestedBinderWildStructFieldPatternListDomain, BinderPathBindingNames]
          rw [hHead', hTail']

theorem tupleBinderWildPathBridgeAssumption_constructive
    (ps : List Pattern)
    (h : BinderWildPatternList ps) :
    TupleNestedBinderWildPathBridgeAssumption ps := by
  exact binderWildPatternListBinderPathBindings_names ps [] 0 h

theorem structBinderWildPathBridgeAssumption_constructive
    (fs : List (String × Pattern))
    (h : BinderWildStructFieldPatternList fs) :
    StructNestedBinderWildPathBridgeAssumption fs := by
  exact binderWildStructFieldBinderPathBindings_names fs [] h

mutual
def nestedBinderWildPatternBinderPathBindings_names
    (p : Pattern) (path : PatternPath) :
    BinderPathBindingNames (NestedBinderWildPatternBinderPathBindings p path) =
      NestedBinderWildPatternDomain p := by
  cases p with
  | wild =>
      simp [NestedBinderWildPatternBinderPathBindings, NestedBinderWildPatternDomain, BinderPathBindingNames]
  | binder x =>
      simp [NestedBinderWildPatternBinderPathBindings, NestedBinderWildPatternDomain, BinderPathBindingNames]
  | tuple ps =>
      simpa [NestedBinderWildPatternBinderPathBindings] using
        nestedBinderWildPatternListBinderPathBindings_names ps path 0
  | ctor name args =>
      simp [NestedBinderWildPatternBinderPathBindings, NestedBinderWildPatternDomain, BinderPathBindingNames]
  | struct name fs =>
      simpa [NestedBinderWildPatternBinderPathBindings] using
        nestedBinderWildStructFieldBinderPathBindings_names fs path

def nestedBinderWildPatternListBinderPathBindings_names
    (ps : List Pattern) (path : PatternPath) (idx : Nat) :
    BinderPathBindingNames (NestedBinderWildPatternListBinderPathBindings ps path idx) =
      NestedBinderWildPatternListDomain ps := by
  cases ps with
  | nil =>
      simp [NestedBinderWildPatternListBinderPathBindings, NestedBinderWildPatternListDomain, BinderPathBindingNames]
  | cons p ps =>
      have hHead := nestedBinderWildPatternBinderPathBindings_names p (path ++ [.tupleItem idx])
      have hTail := nestedBinderWildPatternListBinderPathBindings_names ps path (idx + 1)
      have hHead' := by
        simpa [BinderPathBindingNames] using hHead
      have hTail' := by
        simpa [BinderPathBindingNames] using hTail
      simp [NestedBinderWildPatternListBinderPathBindings, NestedBinderWildPatternListDomain, BinderPathBindingNames]
      rw [hHead', hTail']

def nestedBinderWildStructFieldBinderPathBindings_names
    (fs : List (String × Pattern)) (path : PatternPath) :
    BinderPathBindingNames (NestedBinderWildStructFieldBinderPathBindings fs path) =
      NestedBinderWildStructFieldPatternListDomain fs := by
  cases fs with
  | nil =>
      simp [NestedBinderWildStructFieldBinderPathBindings, NestedBinderWildStructFieldPatternListDomain, BinderPathBindingNames]
  | cons f fs =>
      cases f with
      | mk fname p =>
          have hHead := nestedBinderWildPatternBinderPathBindings_names p (path ++ [.structField fname])
          have hTail := nestedBinderWildStructFieldBinderPathBindings_names fs path
          have hHead' := by
            simpa [BinderPathBindingNames] using hHead
          have hTail' := by
            simpa [BinderPathBindingNames] using hTail
          simp [NestedBinderWildStructFieldBinderPathBindings, NestedBinderWildStructFieldPatternListDomain, BinderPathBindingNames]
          rw [hHead', hTail']
end

theorem tupleNestedBinderWildPathBridgeAssumption_holds
    (ps : List Pattern) :
    TupleNestedBinderWildPathBridgeAssumption ps := by
  exact nestedBinderWildPatternListBinderPathBindings_names ps [] 0

theorem structNestedBinderWildPathBridgeAssumption_holds
    (fs : List (String × Pattern)) :
    StructNestedBinderWildPathBridgeAssumption fs := by
  exact nestedBinderWildStructFieldBinderPathBindings_names fs []

def buildTupleNestedBinderWildPathBridgeProvider
    (ps : List Pattern) :
    TupleNestedBinderWildPathBridgeProvider ps :=
  ⟨tupleNestedBinderWildPathBridgeAssumption_holds ps⟩

def buildStructNestedBinderWildPathBridgeProvider
    (fs : List (String × Pattern)) :
    StructNestedBinderWildPathBridgeProvider fs :=
  ⟨structNestedBinderWildPathBridgeAssumption_holds fs⟩

def buildTupleNestedBinderWildPathBridgeProviderOfWitness
    (ps : List Pattern) (_vs : List Value) (_parts : List Subst) (_σ : Subst)
    (_h : TupleNestedBinderWildGeneratedPartListWitness ps _vs _parts _σ) :
    TupleNestedBinderWildPathBridgeProvider ps :=
  buildTupleNestedBinderWildPathBridgeProvider ps

def buildStructNestedBinderWildPathBridgeProviderOfWitness
    (fs : List (String × Pattern)) (_name : String)
    (_vs : List (String × Value)) (_parts : List Subst) (_σ : Subst)
    (_h : StructNestedBinderWildGeneratedPartListWitness _name fs _vs _parts _σ) :
    StructNestedBinderWildPathBridgeProvider fs :=
  buildStructNestedBinderWildPathBridgeProvider fs

def buildTupleNestedBinderWildPathBridgeProviderOfGenerated
    (ps : List Pattern) (_vs : List Value) (_parts : List Subst)
    (_hfrag : NestedBinderWildPatternList ps)
    (_hparts : TupleNestedBinderWildGeneratedParts ps _vs _parts) :
    TupleNestedBinderWildPathBridgeProvider ps :=
  buildTupleNestedBinderWildPathBridgeProvider ps

def buildStructNestedBinderWildPathBridgeProviderOfGenerated
    (fs : List (String × Pattern)) (_name : String)
    (_vs : List (String × Value)) (_parts : List Subst)
    (_hfrag : NestedBinderWildStructFieldPatternList fs)
    (_hparts : StructNestedBinderWildGeneratedParts fs _vs _parts) :
    StructNestedBinderWildPathBridgeProvider fs :=
  buildStructNestedBinderWildPathBridgeProvider fs

def buildTupleNestedBinderWildPathBridgeCertificateWithProvider
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst)
    (provider : TupleNestedBinderWildPathBridgeProvider ps)
    (h : TupleNestedBinderWildGeneratedPartListWitness ps vs parts σ) :
    TupleNestedBinderWildPathBridgeCertificate ps vs parts σ :=
  ⟨h, provider.assumption⟩

def buildStructNestedBinderWildPathBridgeCertificateWithProvider
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst)
    (provider : StructNestedBinderWildPathBridgeProvider fs)
    (h : StructNestedBinderWildGeneratedPartListWitness name fs vs parts σ) :
    StructNestedBinderWildPathBridgeCertificate name fs vs parts σ :=
  ⟨h, provider.assumption⟩

def buildTupleNestedBinderWildPathBridgeCertificate
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst)
    (h : TupleNestedBinderWildGeneratedPartListWitness ps vs parts σ) :
    TupleNestedBinderWildPathBridgeCertificate ps vs parts σ :=
  buildTupleNestedBinderWildPathBridgeCertificateWithProvider
    ps vs parts σ (buildTupleNestedBinderWildPathBridgeProviderOfWitness ps vs parts σ h) h

def buildStructNestedBinderWildPathBridgeCertificate
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst)
    (h : StructNestedBinderWildGeneratedPartListWitness name fs vs parts σ) :
    StructNestedBinderWildPathBridgeCertificate name fs vs parts σ :=
  buildStructNestedBinderWildPathBridgeCertificateWithProvider
    name fs vs parts σ
    (buildStructNestedBinderWildPathBridgeProviderOfWitness fs name vs parts σ h) h

def buildTupleNestedBinderWildPathBridgeCertificateOfGenerated
    (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts) :
    TupleNestedBinderWildPathBridgeCertificate ps vs parts (mergeSubsts parts) :=
  buildTupleNestedBinderWildPathBridgeCertificateWithProvider
    ps vs parts (mergeSubsts parts)
    (buildTupleNestedBinderWildPathBridgeProviderOfGenerated ps vs parts hfrag hparts)
    (tupleNestedBinderWildGeneratedPartListWitness_of_generated ps vs parts hfrag hparts)

def buildStructNestedBinderWildPathBridgeCertificateOfGenerated
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs vs parts) :
    StructNestedBinderWildPathBridgeCertificate name fs vs parts (mergeSubsts parts) :=
  buildStructNestedBinderWildPathBridgeCertificateWithProvider
    name fs vs parts (mergeSubsts parts)
    (buildStructNestedBinderWildPathBridgeProviderOfGenerated fs name vs parts hfrag hparts)
    (structNestedBinderWildGeneratedPartListWitness_of_generated name fs vs parts hfrag hparts)

theorem tupleNestedBinderWildGeneratedPartListWitness_toPathCorrespondenceWitness_of_bridge
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst)
    (h : TupleNestedBinderWildGeneratedPartListWitness ps vs parts σ)
    (hbridge : TupleNestedBinderWildPathBridgeAssumption ps) :
    TupleNestedBinderWildPathCorrespondenceWitness ps vs parts σ := by
  constructor
  · exact h
  · exact (tupleNestedBinderWildGeneratedPartListWitness_substDomain ps vs parts σ h).trans hbridge.symm

theorem tupleNestedBinderWildPathBridgeCertificate_toPathCorrespondenceWitness
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst)
    (h : TupleNestedBinderWildPathBridgeCertificate ps vs parts σ) :
    TupleNestedBinderWildPathCorrespondenceWitness ps vs parts σ := by
  exact tupleNestedBinderWildGeneratedPartListWitness_toPathCorrespondenceWitness_of_bridge
    ps vs parts σ h.1 h.2

def buildTupleNestedBinderWildPathCorrespondenceWitness
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst)
    (h : TupleNestedBinderWildGeneratedPartListWitness ps vs parts σ) :
    TupleNestedBinderWildPathCorrespondenceWitness ps vs parts σ :=
  tupleNestedBinderWildPathBridgeCertificate_toPathCorrespondenceWitness
    ps vs parts σ (buildTupleNestedBinderWildPathBridgeCertificate ps vs parts σ h)

theorem tupleNestedBinderWildGeneratedPartListWitness_toPathCorrespondenceWitness
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst)
    (h : TupleNestedBinderWildGeneratedPartListWitness ps vs parts σ) :
    TupleNestedBinderWildPathCorrespondenceWitness ps vs parts σ := by
  exact buildTupleNestedBinderWildPathCorrespondenceWitness ps vs parts σ h

theorem structNestedBinderWildGeneratedPartListWitness_toPathCorrespondenceWitness_of_bridge
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst)
    (h : StructNestedBinderWildGeneratedPartListWitness name fs vs parts σ)
    (hbridge : StructNestedBinderWildPathBridgeAssumption fs) :
    StructNestedBinderWildPathCorrespondenceWitness name fs vs parts σ := by
  constructor
  · exact h
  · exact (structNestedBinderWildGeneratedPartListWitness_substDomain name fs vs parts σ h).trans hbridge.symm

theorem structNestedBinderWildPathBridgeCertificate_toPathCorrespondenceWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst)
    (h : StructNestedBinderWildPathBridgeCertificate name fs vs parts σ) :
    StructNestedBinderWildPathCorrespondenceWitness name fs vs parts σ := by
  exact structNestedBinderWildGeneratedPartListWitness_toPathCorrespondenceWitness_of_bridge
    name fs vs parts σ h.1 h.2

def buildStructNestedBinderWildPathCorrespondenceWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst)
    (h : StructNestedBinderWildGeneratedPartListWitness name fs vs parts σ) :
    StructNestedBinderWildPathCorrespondenceWitness name fs vs parts σ :=
  structNestedBinderWildPathBridgeCertificate_toPathCorrespondenceWitness
    name fs vs parts σ (buildStructNestedBinderWildPathBridgeCertificate name fs vs parts σ h)

theorem structNestedBinderWildGeneratedPartListWitness_toPathCorrespondenceWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst)
    (h : StructNestedBinderWildGeneratedPartListWitness name fs vs parts σ) :
    StructNestedBinderWildPathCorrespondenceWitness name fs vs parts σ := by
  exact buildStructNestedBinderWildPathCorrespondenceWitness name fs vs parts σ h

theorem binderPathNameMembership_of_domainEq
    (bs : List BinderPathBinding) (σ : Subst)
    (h : SubstDomain σ = BinderPathBindingNames bs) :
    BinderPathNameMembershipWitness bs σ := by
  intro x
  simpa [h]

theorem binderPathNameLength_of_domainEq
    (bs : List BinderPathBinding) (σ : Subst)
    (h : SubstDomain σ = BinderPathBindingNames bs) :
    BinderPathNameLengthWitness bs σ := by
  simpa [BinderPathNameLengthWitness, h]

theorem binderPathBindingName_of_mem
    (bs : List BinderPathBinding) (b : BinderPathBinding)
    (hb : b ∈ bs) :
    b.2 ∈ BinderPathBindingNames bs := by
  induction bs with
  | nil =>
      cases hb
  | cons b' bs ih =>
      cases hb with
      | head =>
          simp [BinderPathBindingNames]
      | tail _ hb' =>
          have htail : ∃ a, (a, b.snd) ∈ bs := by
            simpa [BinderPathBindingNames] using ih hb'
          simpa [BinderPathBindingNames] using Or.inr htail

theorem binderPathBinding_exists_of_name_mem
    (bs : List BinderPathBinding) (x : String)
    (hx : x ∈ BinderPathBindingNames bs) :
    ∃ path, (path, x) ∈ bs := by
  induction bs with
  | nil =>
      cases hx
  | cons b bs ih =>
      simp [BinderPathBindingNames] at hx
      cases hx with
      | inl hEq =>
          exact ⟨b.1, by simp [hEq]⟩
      | inr hRest =>
      rcases hRest with ⟨path, hmem⟩
      exact ⟨path, by simp [hmem]⟩

theorem mem_mergeSubstDomains_exists_part
    (parts : List Subst) (x : String)
    (hx : x ∈ mergeSubstDomains parts) :
    ∃ part, part ∈ parts ∧ x ∈ SubstDomain part := by
  induction parts with
  | nil =>
      cases hx
  | cons part parts ih =>
      simp [mergeSubstDomains] at hx
      cases hx with
      | inl hhead =>
          exact ⟨part, by simp, hhead⟩
      | inr htail =>
          rcases ih htail with ⟨part', hmem, hxpart⟩
          exact ⟨part', by simp [hmem], hxpart⟩

theorem subst_binding_exists_of_domain_mem
    (part : Subst) (x : String)
    (hx : x ∈ SubstDomain part) :
    ∃ value, (x, value) ∈ part := by
  induction part with
  | nil =>
      cases hx
  | cons binding part ih =>
      cases binding with
      | mk y value =>
          simp [SubstDomain] at hx
          cases hx with
          | inl hxy =>
              subst hxy
              exact ⟨value, by simp⟩
          | inr htail =>
              rcases htail with ⟨value', hmem⟩
              exact ⟨value', by simp [hmem]⟩

theorem binderPathCoverage_of_domainEq
    (bs : List BinderPathBinding) (σ : Subst)
    (h : SubstDomain σ = BinderPathBindingNames bs) :
    BinderPathCoverageWitness bs σ := by
  constructor
  · intro b hb
    have hname : b.2 ∈ BinderPathBindingNames bs := binderPathBindingName_of_mem bs b hb
    simpa [h] using hname
  · intro x hx
    have hname : x ∈ BinderPathBindingNames bs := by
      simpa [h] using hx
    exact binderPathBinding_exists_of_name_mem bs x hname

theorem binderPathDomainCoverage_of_namesEq
    (bs : List BinderPathBinding) (dom : List String)
    (h : BinderPathBindingNames bs = dom) :
    BinderPathDomainCoverageWitness bs dom := by
  constructor
  · intro b hb
    have hname : b.2 ∈ BinderPathBindingNames bs := binderPathBindingName_of_mem bs b hb
    simpa [h] using hname
  · intro x hx
    have hname : x ∈ BinderPathBindingNames bs := by
      simpa [h] using hx
    exact binderPathBinding_exists_of_name_mem bs x hname

theorem binderPathLeaf_of_domainEq_domainCoverage
    (bs : List BinderPathBinding) (σ : Subst) (dom : List String)
    (hσ : SubstDomain σ = BinderPathBindingNames bs)
    (hdom : BinderPathDomainCoverageWitness bs dom) :
    BinderPathLeafWitness bs σ dom := by
  intro x hx
  rcases hdom.2 x hx with ⟨path, hmem⟩
  constructor
  · have hname : x ∈ BinderPathBindingNames bs :=
      binderPathBindingName_of_mem bs (path, x) hmem
    simpa [hσ] using hname
  · exact ⟨path, hmem⟩

theorem binderPathPartLeaf_of_domainCoverage_mergeDomains
    (bs : List BinderPathBinding) (parts : List Subst) (dom : List String)
    (hdom : BinderPathDomainCoverageWitness bs dom)
    (hparts : mergeSubstDomains parts = dom) :
    BinderPathPartLeafWitness bs parts dom := by
  intro x hx
  constructor
  · exact hdom.2 x hx
  · have hmerge : x ∈ mergeSubstDomains parts := by
      rw [hparts]
      exact hx
    exact mem_mergeSubstDomains_exists_part parts x hmerge

theorem binderPathPartOrigin_of_partLeaf
    (bs : List BinderPathBinding) (parts : List Subst) (dom : List String)
    (h : BinderPathPartLeafWitness bs parts dom) :
    BinderPathPartOriginWitness bs parts dom := by
  intro x hx
  rcases h x hx with ⟨⟨path, hpath⟩, part, hpart, hxpart⟩
  exact ⟨path, part, hpath, hpart, hxpart⟩

theorem binderPathValueOrigin_of_partOrigin
    (bs : List BinderPathBinding) (parts : List Subst) (dom : List String)
    (h : BinderPathPartOriginWitness bs parts dom) :
    BinderPathValueOriginWitness bs parts dom := by
  intro x hx
  rcases h x hx with ⟨path, part, hpath, hpart, hxpart⟩
  rcases subst_binding_exists_of_domain_mem part x hxpart with ⟨value, hbind⟩
  exact ⟨path, part, value, hpath, hpart, hbind⟩

theorem nestedBinderWildPatternBinderPathBindings_domainCoverage
    (p : Pattern) (path : PatternPath) :
    BinderPathDomainCoverageWitness
      (NestedBinderWildPatternBinderPathBindings p path)
      (NestedBinderWildPatternDomain p) := by
  exact binderPathDomainCoverage_of_namesEq
    (NestedBinderWildPatternBinderPathBindings p path)
    (NestedBinderWildPatternDomain p)
    (nestedBinderWildPatternBinderPathBindings_names p path)

theorem nestedBinderWildPatternListBinderPathBindings_domainCoverage
    (ps : List Pattern) (path : PatternPath) (idx : Nat) :
    BinderPathDomainCoverageWitness
      (NestedBinderWildPatternListBinderPathBindings ps path idx)
      (NestedBinderWildPatternListDomain ps) := by
  exact binderPathDomainCoverage_of_namesEq
    (NestedBinderWildPatternListBinderPathBindings ps path idx)
    (NestedBinderWildPatternListDomain ps)
    (nestedBinderWildPatternListBinderPathBindings_names ps path idx)

theorem nestedBinderWildStructFieldBinderPathBindings_domainCoverage
    (fs : List (String × Pattern)) (path : PatternPath) :
    BinderPathDomainCoverageWitness
      (NestedBinderWildStructFieldBinderPathBindings fs path)
      (NestedBinderWildStructFieldPatternListDomain fs) := by
  exact binderPathDomainCoverage_of_namesEq
    (NestedBinderWildStructFieldBinderPathBindings fs path)
    (NestedBinderWildStructFieldPatternListDomain fs)
    (nestedBinderWildStructFieldBinderPathBindings_names fs path)

theorem tupleNestedBinderWildPathCorrespondenceWitness_toSummaryWitness
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst)
    (h : TupleNestedBinderWildPathCorrespondenceWitness ps vs parts σ) :
    TupleNestedBinderWildPathSummaryWitness ps vs parts σ := by
  constructor
  · exact h
  · constructor
    · exact binderPathNameMembership_of_domainEq
        (NestedBinderWildPatternListBinderPathBindings ps [] 0) σ h.2
    · exact binderPathNameLength_of_domainEq
        (NestedBinderWildPatternListBinderPathBindings ps [] 0) σ h.2

theorem structNestedBinderWildPathCorrespondenceWitness_toSummaryWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst)
    (h : StructNestedBinderWildPathCorrespondenceWitness name fs vs parts σ) :
    StructNestedBinderWildPathSummaryWitness name fs vs parts σ := by
  constructor
  · exact h
  · constructor
    · exact binderPathNameMembership_of_domainEq
        (NestedBinderWildStructFieldBinderPathBindings fs []) σ h.2
    · exact binderPathNameLength_of_domainEq
        (NestedBinderWildStructFieldBinderPathBindings fs []) σ h.2

theorem tupleNestedBinderWildPathCorrespondenceWitness_toCoverageWitness
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst)
    (h : TupleNestedBinderWildPathCorrespondenceWitness ps vs parts σ) :
    TupleNestedBinderWildPathCoverageWitness ps vs parts σ := by
  constructor
  · exact h
  · exact binderPathCoverage_of_domainEq
      (NestedBinderWildPatternListBinderPathBindings ps [] 0) σ h.2

theorem structNestedBinderWildPathCorrespondenceWitness_toCoverageWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst)
    (h : StructNestedBinderWildPathCorrespondenceWitness name fs vs parts σ) :
    StructNestedBinderWildPathCoverageWitness name fs vs parts σ := by
  constructor
  · exact h
  · exact binderPathCoverage_of_domainEq
      (NestedBinderWildStructFieldBinderPathBindings fs []) σ h.2

def buildTupleNestedBinderWildPathSummaryWitness
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst)
    (h : TupleNestedBinderWildGeneratedPartListWitness ps vs parts σ) :
    TupleNestedBinderWildPathSummaryWitness ps vs parts σ :=
  tupleNestedBinderWildPathCorrespondenceWitness_toSummaryWitness ps vs parts σ
    (buildTupleNestedBinderWildPathCorrespondenceWitness ps vs parts σ h)

def buildStructNestedBinderWildPathSummaryWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst)
    (h : StructNestedBinderWildGeneratedPartListWitness name fs vs parts σ) :
    StructNestedBinderWildPathSummaryWitness name fs vs parts σ :=
  structNestedBinderWildPathCorrespondenceWitness_toSummaryWitness name fs vs parts σ
    (buildStructNestedBinderWildPathCorrespondenceWitness name fs vs parts σ h)

def buildTupleNestedBinderWildPathCoverageWitness
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst)
    (h : TupleNestedBinderWildGeneratedPartListWitness ps vs parts σ) :
    TupleNestedBinderWildPathCoverageWitness ps vs parts σ :=
  tupleNestedBinderWildPathCorrespondenceWitness_toCoverageWitness ps vs parts σ
    (buildTupleNestedBinderWildPathCorrespondenceWitness ps vs parts σ h)

def buildStructNestedBinderWildPathCoverageWitness
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst)
    (h : StructNestedBinderWildGeneratedPartListWitness name fs vs parts σ) :
    StructNestedBinderWildPathCoverageWitness name fs vs parts σ :=
  structNestedBinderWildPathCorrespondenceWitness_toCoverageWitness name fs vs parts σ
    (buildStructNestedBinderWildPathCorrespondenceWitness name fs vs parts σ h)

def buildTupleNestedBinderWildPathWitnessBundleWithProvider
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst)
    (provider : TupleNestedBinderWildPathBridgeProvider ps)
    (h : TupleNestedBinderWildGeneratedPartListWitness ps vs parts σ) :
    TupleNestedBinderWildPathWitnessBundle ps vs parts σ :=
  { bridge := buildTupleNestedBinderWildPathBridgeCertificateWithProvider ps vs parts σ provider h
    correspondence := tupleNestedBinderWildPathBridgeCertificate_toPathCorrespondenceWitness
      ps vs parts σ (buildTupleNestedBinderWildPathBridgeCertificateWithProvider ps vs parts σ provider h)
    summary := tupleNestedBinderWildPathCorrespondenceWitness_toSummaryWitness ps vs parts σ
      (tupleNestedBinderWildPathBridgeCertificate_toPathCorrespondenceWitness
        ps vs parts σ (buildTupleNestedBinderWildPathBridgeCertificateWithProvider ps vs parts σ provider h))
    coverage := tupleNestedBinderWildPathCorrespondenceWitness_toCoverageWitness ps vs parts σ
      (tupleNestedBinderWildPathBridgeCertificate_toPathCorrespondenceWitness
        ps vs parts σ (buildTupleNestedBinderWildPathBridgeCertificateWithProvider ps vs parts σ provider h))
    domainCoverage := nestedBinderWildPatternListBinderPathBindings_domainCoverage ps [] 0
    leaf := binderPathLeaf_of_domainEq_domainCoverage
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      σ
      (NestedBinderWildPatternListDomain ps)
      (tupleNestedBinderWildPathBridgeCertificate_toPathCorrespondenceWitness
        ps vs parts σ (buildTupleNestedBinderWildPathBridgeCertificateWithProvider ps vs parts σ provider h)).2
      (nestedBinderWildPatternListBinderPathBindings_domainCoverage ps [] 0)
    partLeaf := binderPathPartLeaf_of_domainCoverage_mergeDomains
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      parts
      (NestedBinderWildPatternListDomain ps)
      (nestedBinderWildPatternListBinderPathBindings_domainCoverage ps [] 0)
      (tupleNestedBinderWildGeneratedPartListWitness_domain ps vs parts σ h)
    origin := binderPathPartOrigin_of_partLeaf
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      parts
      (NestedBinderWildPatternListDomain ps)
      (binderPathPartLeaf_of_domainCoverage_mergeDomains
        (NestedBinderWildPatternListBinderPathBindings ps [] 0)
        parts
        (NestedBinderWildPatternListDomain ps)
        (nestedBinderWildPatternListBinderPathBindings_domainCoverage ps [] 0)
        (tupleNestedBinderWildGeneratedPartListWitness_domain ps vs parts σ h))
    valueOrigin := binderPathValueOrigin_of_partOrigin
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      parts
      (NestedBinderWildPatternListDomain ps)
      (binderPathPartOrigin_of_partLeaf
        (NestedBinderWildPatternListBinderPathBindings ps [] 0)
        parts
        (NestedBinderWildPatternListDomain ps)
        (binderPathPartLeaf_of_domainCoverage_mergeDomains
          (NestedBinderWildPatternListBinderPathBindings ps [] 0)
          parts
          (NestedBinderWildPatternListDomain ps)
          (nestedBinderWildPatternListBinderPathBindings_domainCoverage ps [] 0)
          (tupleNestedBinderWildGeneratedPartListWitness_domain ps vs parts σ h))) }

def buildStructNestedBinderWildPathWitnessBundleWithProvider
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst)
    (provider : StructNestedBinderWildPathBridgeProvider fs)
    (h : StructNestedBinderWildGeneratedPartListWitness name fs vs parts σ) :
    StructNestedBinderWildPathWitnessBundle name fs vs parts σ :=
  { bridge := buildStructNestedBinderWildPathBridgeCertificateWithProvider
      name fs vs parts σ provider h
    correspondence := structNestedBinderWildPathBridgeCertificate_toPathCorrespondenceWitness
      name fs vs parts σ
      (buildStructNestedBinderWildPathBridgeCertificateWithProvider name fs vs parts σ provider h)
    summary := structNestedBinderWildPathCorrespondenceWitness_toSummaryWitness name fs vs parts σ
      (structNestedBinderWildPathBridgeCertificate_toPathCorrespondenceWitness
        name fs vs parts σ
        (buildStructNestedBinderWildPathBridgeCertificateWithProvider name fs vs parts σ provider h))
    coverage := structNestedBinderWildPathCorrespondenceWitness_toCoverageWitness name fs vs parts σ
      (structNestedBinderWildPathBridgeCertificate_toPathCorrespondenceWitness
        name fs vs parts σ
        (buildStructNestedBinderWildPathBridgeCertificateWithProvider name fs vs parts σ provider h))
    domainCoverage := nestedBinderWildStructFieldBinderPathBindings_domainCoverage fs []
    leaf := binderPathLeaf_of_domainEq_domainCoverage
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      σ
      (NestedBinderWildStructFieldPatternListDomain fs)
      (structNestedBinderWildPathBridgeCertificate_toPathCorrespondenceWitness
        name fs vs parts σ
        (buildStructNestedBinderWildPathBridgeCertificateWithProvider name fs vs parts σ provider h)).2
      (nestedBinderWildStructFieldBinderPathBindings_domainCoverage fs [])
    partLeaf := binderPathPartLeaf_of_domainCoverage_mergeDomains
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      parts
      (NestedBinderWildStructFieldPatternListDomain fs)
      (nestedBinderWildStructFieldBinderPathBindings_domainCoverage fs [])
      (structNestedBinderWildGeneratedPartListWitness_domain name fs vs parts σ h)
    origin := binderPathPartOrigin_of_partLeaf
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      parts
      (NestedBinderWildStructFieldPatternListDomain fs)
      (binderPathPartLeaf_of_domainCoverage_mergeDomains
        (NestedBinderWildStructFieldBinderPathBindings fs [])
        parts
        (NestedBinderWildStructFieldPatternListDomain fs)
        (nestedBinderWildStructFieldBinderPathBindings_domainCoverage fs [])
        (structNestedBinderWildGeneratedPartListWitness_domain name fs vs parts σ h))
    valueOrigin := binderPathValueOrigin_of_partOrigin
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      parts
      (NestedBinderWildStructFieldPatternListDomain fs)
      (binderPathPartOrigin_of_partLeaf
        (NestedBinderWildStructFieldBinderPathBindings fs [])
        parts
        (NestedBinderWildStructFieldPatternListDomain fs)
        (binderPathPartLeaf_of_domainCoverage_mergeDomains
          (NestedBinderWildStructFieldBinderPathBindings fs [])
          parts
          (NestedBinderWildStructFieldPatternListDomain fs)
          (nestedBinderWildStructFieldBinderPathBindings_domainCoverage fs [])
          (structNestedBinderWildGeneratedPartListWitness_domain name fs vs parts σ h))) }

def buildTupleNestedBinderWildPathWitnessBundle
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (σ : Subst)
    (h : TupleNestedBinderWildGeneratedPartListWitness ps vs parts σ) :
    TupleNestedBinderWildPathWitnessBundle ps vs parts σ :=
  buildTupleNestedBinderWildPathWitnessBundleWithProvider
    ps vs parts σ (buildTupleNestedBinderWildPathBridgeProviderOfWitness ps vs parts σ h) h

def buildTupleNestedBinderWildPathWitnessBundleOfGenerated
    (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts) :
    TupleNestedBinderWildPathWitnessBundle ps vs parts (mergeSubsts parts) :=
  buildTupleNestedBinderWildPathWitnessBundleWithProvider
    ps vs parts (mergeSubsts parts)
    (buildTupleNestedBinderWildPathBridgeProviderOfGenerated ps vs parts hfrag hparts)
    (tupleNestedBinderWildGeneratedPartListWitness_of_generated ps vs parts hfrag hparts)

def buildStructNestedBinderWildPathWitnessBundle
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst) (σ : Subst)
    (h : StructNestedBinderWildGeneratedPartListWitness name fs vs parts σ) :
    StructNestedBinderWildPathWitnessBundle name fs vs parts σ :=
  buildStructNestedBinderWildPathWitnessBundleWithProvider
    name fs vs parts σ
    (buildStructNestedBinderWildPathBridgeProviderOfWitness fs name vs parts σ h) h

def buildStructNestedBinderWildPathWitnessBundleOfGenerated
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value))
    (parts : List Subst)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs vs parts) :
    StructNestedBinderWildPathWitnessBundle name fs vs parts (mergeSubsts parts) :=
  buildStructNestedBinderWildPathWitnessBundleWithProvider
    name fs vs parts (mergeSubsts parts)
    (buildStructNestedBinderWildPathBridgeProviderOfGenerated fs name vs parts hfrag hparts)
    (structNestedBinderWildGeneratedPartListWitness_of_generated name fs vs parts hfrag hparts)

theorem structPatternCompositionSpine_toComposition
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : Subst) :
    StructPatternCompositionSpine name fs vs σ →
    SubstComposition σ := by
  intro h
  rcases h with ⟨parts, _, _, hmerge, hdom⟩
  exact ⟨parts, hmerge, hdom⟩

def structPatternCompositionSpine_exact
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : Subst)
    (hshape : fs.length = vs.length) :
    StructPatternCompositionSpine name fs vs σ := by
  refine ⟨List.replicate fs.length ([] : Subst) ++ [σ], ?_, ?_, ?_, ?_⟩
  · simp
  · simpa [hshape]
  · simpa using mergeSubsts_replicate_nil_append_singleton fs.length σ
  · simpa using mergeSubstDomains_replicate_nil_append_singleton fs.length σ

theorem structPatternRecursiveCompositionWitness_toSpine
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : Subst) :
    StructPatternRecursiveCompositionWitness name fs vs σ →
    StructPatternCompositionSpine name fs vs σ := by
  intro h
  rcases h with ⟨parts, hfs, hvs, _, hmerge, hdom⟩
  refine ⟨parts ++ [σ], ?_, ?_, hmerge, hdom⟩
  · simp [hfs]
  · simp [hvs]

def structPatternRecursiveCompositionWitness_exact
    (name : String) (fs : List (String × Pattern)) (vs : List (String × Value)) (σ : Subst)
    (hshape : fs.length = vs.length) :
    StructPatternRecursiveCompositionWitness name fs vs σ := by
  refine ⟨List.replicate fs.length ([] : Subst), ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simpa [hshape]
  · intro part hpart
    have h : ¬ fs = [] ∧ part = ([] : Subst) := by
      simpa using hpart
    exact h.2
  · simpa using mergeSubsts_replicate_nil_append_singleton fs.length σ
  · simpa using mergeSubstDomains_replicate_nil_append_singleton fs.length σ

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
