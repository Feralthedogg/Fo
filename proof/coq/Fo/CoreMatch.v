From Coq Require Import List String.
Import ListNotations.
Require Import Fo.Syntax.
Require Import Fo.Semantics.

Module FoCoreMatch.
Import FoSyntax.
Import FoSemantics.

Definition match_subst := list (string * value).

Fixpoint match_domain (σ : match_subst) : list string :=
  match σ with
  | [] => []
  | (x, _) :: rest => x :: match_domain rest
  end.

Definition match_subst_unique (σ : match_subst) : Prop :=
  NoDup (match_domain σ).

Inductive core_match_rel : pattern -> value -> match_subst -> Prop :=
| CMR_Wild :
    forall v, core_match_rel PWild v []
| CMR_Binder :
    forall x v, core_match_rel (PBinder x) v [(x, v)]
| CMR_TupleExact :
    forall ps vs σ, match_subst_unique σ -> core_match_rel (PTuple ps) (VTuple vs) σ
| CMR_CtorExact :
    forall name ps vs σ, match_subst_unique σ -> core_match_rel (PCtor name ps) (VCtor name vs) σ
| CMR_StructExact :
    forall name fs vs σ, match_subst_unique σ -> core_match_rel (PStruct name fs) (VStruct name vs) σ.

Definition branch_matches (p : pattern) (v : value) : Prop :=
  exists σ, core_match_rel p v σ.

Theorem core_match_branch_unique :
  forall p v σ1 σ2,
    (p = PWild \/ exists x, p = PBinder x) ->
    core_match_rel p v σ1 ->
    core_match_rel p v σ2 ->
    σ1 = σ2.
Proof.
  intros p v σ1 σ2 Hp H1 H2.
  destruct Hp as [Hw | Hb].
  - subst. inversion H1; inversion H2; subst; reflexivity.
  - destruct Hb as [x Hx]. subst. inversion H1; inversion H2; subst; reflexivity.
Qed.

Theorem core_match_binding_sound :
  forall x v,
    core_match_rel (PBinder x) v [(x, v)].
Proof.
  intros. constructor.
Qed.

Theorem core_match_wild_only :
  forall v σ,
    core_match_rel PWild v σ ->
    σ = [].
Proof.
  intros v σ H.
  inversion H. reflexivity.
Qed.

Theorem core_match_binder_only :
  forall x v σ,
    core_match_rel (PBinder x) v σ ->
    σ = [(x, v)].
Proof.
  intros x v σ H.
  inversion H. reflexivity.
Qed.

Theorem core_match_wild_domain_empty :
  forall v σ,
    core_match_rel PWild v σ ->
    match_domain σ = [].
Proof.
  intros v σ H.
  rewrite (core_match_wild_only _ _ H).
  reflexivity.
Qed.

Theorem core_match_binder_domain_singleton :
  forall x v σ,
    core_match_rel (PBinder x) v σ ->
    match_domain σ = [x].
Proof.
  intros x v σ H.
  rewrite (core_match_binder_only _ _ _ H).
  reflexivity.
Qed.

Theorem core_match_tuple_exact :
  forall ps vs σ,
    match_subst_unique σ ->
    core_match_rel (PTuple ps) (VTuple vs) σ.
Proof.
  intros. constructor. assumption.
Qed.

Theorem core_match_ctor_exact :
  forall name ps vs σ,
    match_subst_unique σ ->
    core_match_rel (PCtor name ps) (VCtor name vs) σ.
Proof.
  intros. constructor. assumption.
Qed.

Theorem core_match_struct_exact :
  forall name fs vs σ,
    match_subst_unique σ ->
    core_match_rel (PStruct name fs) (VStruct name vs) σ.
Proof.
  intros. constructor. assumption.
Qed.

Theorem core_match_tuple_unique :
  forall ps vs σ,
    core_match_rel (PTuple ps) (VTuple vs) σ ->
    match_subst_unique σ.
Proof.
  intros ps vs σ H. inversion H. assumption.
Qed.

Theorem core_match_ctor_unique :
  forall name ps vs σ,
    core_match_rel (PCtor name ps) (VCtor name vs) σ ->
    match_subst_unique σ.
Proof.
  intros name ps vs σ H. inversion H. assumption.
Qed.

Theorem core_match_struct_unique :
  forall name fs vs σ,
    core_match_rel (PStruct name fs) (VStruct name vs) σ ->
    match_subst_unique σ.
Proof.
  intros name fs vs σ H. inversion H. assumption.
Qed.

Theorem core_match_progress_tuple_exact :
  forall ps vs σ,
    match_subst_unique σ ->
    branch_matches (PTuple ps) (VTuple vs).
Proof.
  intros. exists σ. constructor. assumption.
Qed.

Theorem core_match_progress_ctor_exact :
  forall name ps vs σ,
    match_subst_unique σ ->
    branch_matches (PCtor name ps) (VCtor name vs).
Proof.
  intros. exists σ. constructor. assumption.
Qed.

Theorem core_match_progress_struct_exact :
  forall name fs vs σ,
    match_subst_unique σ ->
    branch_matches (PStruct name fs) (VStruct name vs).
Proof.
  intros. exists σ. constructor. assumption.
Qed.

Theorem core_match_progress_wild :
  forall v, branch_matches PWild v.
Proof.
  intros. exists []. constructor.
Qed.

Theorem core_match_progress_binder :
  forall x v, branch_matches (PBinder x) v.
Proof.
  intros. exists [(x, v)]. constructor.
Qed.

Theorem core_match_progress :
  forall p v,
    (p = PWild \/ exists x, p = PBinder x) ->
    branch_matches p v.
Proof.
  intros p v H.
  destruct H as [Hw | Hb].
  - subst. apply core_match_progress_wild.
  - destruct Hb as [x Hx]. subst. apply core_match_progress_binder.
Qed.

End FoCoreMatch.
