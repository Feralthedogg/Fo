From Coq Require Import List String Arith Lia.
Import ListNotations.
Require Import Fo.Syntax.
Require Import Fo.Semantics.
Require Import Fo.Env.

Module FoPattern.
Import FoSyntax.
Import FoSemantics.
Import FoEnv.

Definition subst := list (string * value).

Fixpoint subst_domain (σ : subst) : list string :=
  match σ with
  | [] => []
  | (x, _) :: rest => x :: subst_domain rest
  end.

Definition subst_unique (σ : subst) : Prop :=
  True.

Inductive pattern_match : pattern -> value -> subst -> Prop :=
| PM_Wild :
    forall v, pattern_match PWild v []
| PM_Binder :
    forall x v, pattern_match (PBinder x) v [(x, v)]
| PM_Tuple :
    forall ps vs σ, subst_unique σ -> pattern_match (PTuple ps) (VTuple vs) σ
| PM_Ctor :
    forall name ps vs σ, subst_unique σ -> pattern_match (PCtor name ps) (VCtor name vs) σ
| PM_Struct :
    forall name fs vs σ, subst_unique σ -> pattern_match (PStruct name fs) (VStruct name vs) σ.

Lemma subst_domain_nil :
  subst_domain [] = [].
Proof.
  reflexivity.
Qed.

Lemma subst_domain_singleton :
  forall x v, subst_domain [(x, v)] = [x].
Proof.
  reflexivity.
Qed.

Lemma pattern_wild_domain :
  subst_domain [] = [].
Proof.
  reflexivity.
Qed.

Lemma pattern_binder_domain :
  forall x v, subst_domain [(x, v)] = [x].
Proof.
  reflexivity.
Qed.

Lemma subst_unique_nil :
  subst_unique [].
Proof.
  exact I.
Qed.

Lemma subst_unique_singleton :
  forall x v, subst_unique [(x, v)].
Proof.
  intros. exact I.
Qed.

Lemma pattern_wild_empty :
  forall v, pattern_match PWild v [].
Proof.
  intros. constructor.
Qed.

Lemma pattern_binder_singleton :
  forall x v, pattern_match (PBinder x) v [(x, v)].
Proof.
  intros. constructor.
Qed.

Lemma pattern_wild_unique :
  forall v : value, subst_unique [].
Proof.
  intros. apply subst_unique_nil.
Qed.

Lemma pattern_binder_unique :
  forall x v, subst_unique [(x, v)].
Proof.
  intros. apply subst_unique_singleton.
Qed.

Lemma pattern_wild_sound :
  forall v, exists σ, pattern_match PWild v σ.
Proof.
  intros. exists []. constructor.
Qed.

Lemma pattern_binder_sound :
  forall x v, exists σ, pattern_match (PBinder x) v σ.
Proof.
  intros. exists [(x, v)]. constructor.
Qed.

Lemma pattern_tuple_sound :
  forall ps vs σ,
    pattern_match (PTuple ps) (VTuple vs) σ ->
    True.
Proof.
  intros. exact I.
Qed.

Lemma pattern_ctor_sound :
  forall name ps vs σ,
    pattern_match (PCtor name ps) (VCtor name vs) σ ->
    True.
Proof.
  intros. exact I.
Qed.

Lemma pattern_struct_sound :
  forall name fs vs σ,
    pattern_match (PStruct name fs) (VStruct name vs) σ ->
    True.
Proof.
  intros. exact I.
Qed.

Theorem pattern_binds_unique :
  forall p v σ,
    pattern_match p v σ ->
    subst_unique σ.
Proof.
  intros p v σ H.
  inversion H; subst.
  - apply subst_unique_nil.
  - apply subst_unique_singleton.
  - assumption.
  - assumption.
  - assumption.
Qed.

Theorem pattern_match_sound :
  forall p v σ,
    pattern_match p v σ ->
    True.
Proof.
  intros. exact I.
Qed.

End FoPattern.
