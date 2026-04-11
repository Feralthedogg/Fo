From Coq Require Import List String Arith Lia.
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

Definition tuple_core_match_witness (ps : list pattern) (vs : list value) (σ : match_subst) : Prop :=
  core_match_rel (PTuple ps) (VTuple vs) σ /\ match_subst_unique σ.

Definition struct_core_match_witness
    (name : string) (fs : list (string * pattern)) (vs : list (string * value)) (σ : match_subst) : Prop :=
  core_match_rel (PStruct name fs) (VStruct name vs) σ /\ match_subst_unique σ.

Fixpoint merge_match_substs (parts : list match_subst) : match_subst :=
  match parts with
  | [] => []
  | part :: rest => (part ++ merge_match_substs rest)%list
  end.

Fixpoint merge_match_domains (parts : list match_subst) : list string :=
  match parts with
  | [] => []
  | part :: rest => (match_domain part ++ merge_match_domains rest)%list
  end.

Definition tuple_core_match_composition_spine
    (ps : list pattern) (vs : list value) (σ : match_subst) : Prop :=
  exists parts : list match_subst,
    List.length parts = List.length ps + 1 /\
    List.length parts = List.length vs + 1 /\
    merge_match_substs parts = σ /\
    merge_match_domains parts = match_domain σ.

Definition struct_core_match_composition_spine
    (name : string) (fs : list (string * pattern)) (vs : list (string * value)) (σ : match_subst) : Prop :=
  exists parts : list match_subst,
    List.length parts = List.length fs + 1 /\
    List.length parts = List.length vs + 1 /\
    merge_match_substs parts = σ /\
    merge_match_domains parts = match_domain σ.

Definition tuple_core_match_recursive_composition_witness
    (ps : list pattern) (vs : list value) (σ : match_subst) : Prop :=
  exists parts : list match_subst,
    List.length parts = List.length ps /\
    List.length parts = List.length vs /\
    Forall (fun part => part = []) parts /\
    merge_match_substs ((parts ++ [σ])%list) = σ /\
    merge_match_domains ((parts ++ [σ])%list) = match_domain σ.

Definition struct_core_match_recursive_composition_witness
    (name : string) (fs : list (string * pattern)) (vs : list (string * value)) (σ : match_subst) : Prop :=
  exists parts : list match_subst,
    List.length parts = List.length fs /\
    List.length parts = List.length vs /\
    Forall (fun part => part = []) parts /\
    merge_match_substs ((parts ++ [σ])%list) = σ /\
    merge_match_domains ((parts ++ [σ])%list) = match_domain σ.

Definition match_subst_composition (σ : match_subst) : Prop :=
  exists parts : list match_subst,
    merge_match_substs parts = σ /\
    merge_match_domains parts = match_domain σ.

Theorem match_domain_app :
  forall σ1 σ2,
    match_domain ((σ1 ++ σ2)%list) = (match_domain σ1 ++ match_domain σ2)%list.
Proof.
  induction σ1 as [| [x v] rest IH]; intros σ2.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

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

Theorem tuple_core_match_witness_exact :
  forall ps vs σ,
    match_subst_unique σ ->
    tuple_core_match_witness ps vs σ.
Proof.
  intros. split.
  - constructor. exact H.
  - exact H.
Qed.

Theorem tuple_core_match_witness_exists :
  forall ps vs σ,
    match_subst_unique σ ->
    exists σ', tuple_core_match_witness ps vs σ'.
Proof.
  intros. exists σ. exact (tuple_core_match_witness_exact ps vs σ H).
Qed.

Theorem match_domain_merge_match_substs :
  forall parts,
    match_domain (merge_match_substs parts) = merge_match_domains parts.
Proof.
  induction parts as [| part rest IH].
  - reflexivity.
  - simpl. rewrite match_domain_app. rewrite IH. reflexivity.
Qed.

Theorem merge_match_substs_repeat_nil_singleton :
  forall n σ,
    merge_match_substs ((repeat ([] : match_subst) n ++ [σ])%list) = σ.
Proof.
  induction n as [| n IH]; intros σ.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. exact (IH σ).
Qed.

Theorem merge_match_domains_repeat_nil_singleton :
  forall n σ,
    merge_match_domains ((repeat ([] : match_subst) n ++ [σ])%list) = match_domain σ.
Proof.
  induction n as [| n IH]; intros σ.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. exact (IH σ).
Qed.

Theorem forall_repeat_nil_match_subst :
  forall n,
    Forall (fun part : match_subst => part = []) (repeat ([] : match_subst) n).
Proof.
  induction n as [| n IH].
  - constructor.
  - simpl. constructor.
    + reflexivity.
    + exact IH.
Qed.

Theorem match_subst_composition_from_parts :
  forall parts,
    match_subst_composition (merge_match_substs parts).
Proof.
  intros. exists parts. split.
  - reflexivity.
  - symmetry. apply match_domain_merge_match_substs.
Qed.

Theorem tuple_core_match_composition_exact :
  forall (ps : list pattern) (vs : list value) (σ : match_subst),
    match_subst_unique σ ->
    match_subst_composition σ.
Proof.
  intros ps vs σ Hσ.
  exists [σ]. split.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite app_nil_r. reflexivity.
Qed.

Theorem tuple_core_match_composition_spine_to_composition :
  forall ps vs σ,
    tuple_core_match_composition_spine ps vs σ ->
    match_subst_composition σ.
Proof.
  intros ps vs σ H.
  destruct H as [parts [_ [_ [Hmerge Hdom]]]].
  exists parts. split; assumption.
Qed.

Theorem tuple_core_match_composition_spine_exact :
  forall (ps : list pattern) (vs : list value) (σ : match_subst),
    List.length ps = List.length vs ->
    tuple_core_match_composition_spine ps vs σ.
Proof.
  intros ps vs σ Hshape.
  exists ((repeat ([] : match_subst) (List.length ps) ++ [σ])%list).
  repeat split.
  - rewrite app_length, repeat_length. simpl. lia.
  - rewrite app_length, repeat_length. simpl. lia.
  - apply merge_match_substs_repeat_nil_singleton.
  - apply merge_match_domains_repeat_nil_singleton.
Qed.

Theorem tuple_core_match_recursive_composition_witness_to_spine :
  forall ps vs σ,
    tuple_core_match_recursive_composition_witness ps vs σ ->
    tuple_core_match_composition_spine ps vs σ.
Proof.
  intros ps vs σ H.
  destruct H as [parts [Hps [Hvs [_ [Hmerge Hdom]]]]].
  exists ((parts ++ [σ])%list). repeat split.
  - rewrite app_length. simpl. lia.
  - rewrite app_length. simpl. lia.
  - exact Hmerge.
  - exact Hdom.
Qed.

Theorem tuple_core_match_recursive_composition_witness_exact :
  forall (ps : list pattern) (vs : list value) (σ : match_subst),
    List.length ps = List.length vs ->
    tuple_core_match_recursive_composition_witness ps vs σ.
Proof.
  intros ps vs σ Hshape.
  exists (repeat ([] : match_subst) (List.length ps)).
  repeat split.
  - rewrite repeat_length. reflexivity.
  - rewrite repeat_length. exact Hshape.
  - apply forall_repeat_nil_match_subst.
  - apply merge_match_substs_repeat_nil_singleton.
  - apply merge_match_domains_repeat_nil_singleton.
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

Theorem struct_core_match_witness_exact :
  forall name fs vs σ,
    match_subst_unique σ ->
    struct_core_match_witness name fs vs σ.
Proof.
  intros. split.
  - constructor. exact H.
  - exact H.
Qed.

Theorem struct_core_match_witness_exists :
  forall name fs vs σ,
    match_subst_unique σ ->
    exists σ', struct_core_match_witness name fs vs σ'.
Proof.
  intros. exists σ. exact (struct_core_match_witness_exact name fs vs σ H).
Qed.

Theorem struct_core_match_composition_exact :
  forall (name : string) (fs : list (string * pattern)) (vs : list (string * value)) (σ : match_subst),
    match_subst_unique σ ->
    match_subst_composition σ.
Proof.
  intros name fs vs σ Hσ.
  exists [σ]. split.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite app_nil_r. reflexivity.
Qed.

Theorem struct_core_match_composition_spine_to_composition :
  forall name fs vs σ,
    struct_core_match_composition_spine name fs vs σ ->
    match_subst_composition σ.
Proof.
  intros name fs vs σ H.
  destruct H as [parts [_ [_ [Hmerge Hdom]]]].
  exists parts. split; assumption.
Qed.

Theorem struct_core_match_composition_spine_exact :
  forall (name : string) (fs : list (string * pattern)) (vs : list (string * value)) (σ : match_subst),
    List.length fs = List.length vs ->
    struct_core_match_composition_spine name fs vs σ.
Proof.
  intros name fs vs σ Hshape.
  exists ((repeat ([] : match_subst) (List.length fs) ++ [σ])%list).
  repeat split.
  - rewrite app_length, repeat_length. simpl. lia.
  - rewrite app_length, repeat_length. simpl. lia.
  - apply merge_match_substs_repeat_nil_singleton.
  - apply merge_match_domains_repeat_nil_singleton.
Qed.

Theorem struct_core_match_recursive_composition_witness_to_spine :
  forall name fs vs σ,
    struct_core_match_recursive_composition_witness name fs vs σ ->
    struct_core_match_composition_spine name fs vs σ.
Proof.
  intros name fs vs σ H.
  destruct H as [parts [Hfs [Hvs [_ [Hmerge Hdom]]]]].
  exists ((parts ++ [σ])%list). repeat split.
  - rewrite app_length. simpl. lia.
  - rewrite app_length. simpl. lia.
  - exact Hmerge.
  - exact Hdom.
Qed.

Theorem struct_core_match_recursive_composition_witness_exact :
  forall (name : string) (fs : list (string * pattern)) (vs : list (string * value)) (σ : match_subst),
    List.length fs = List.length vs ->
    struct_core_match_recursive_composition_witness name fs vs σ.
Proof.
  intros name fs vs σ Hshape.
  exists (repeat ([] : match_subst) (List.length fs)).
  repeat split.
  - rewrite repeat_length. reflexivity.
  - rewrite repeat_length. exact Hshape.
  - apply forall_repeat_nil_match_subst.
  - apply merge_match_substs_repeat_nil_singleton.
  - apply merge_match_domains_repeat_nil_singleton.
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
