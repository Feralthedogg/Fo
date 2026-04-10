From Coq Require Import List String.
Import ListNotations.
Require Import Fo.Semantics.

Module FoCoreUpdate.
Import FoSemantics.

Definition field_store := list (string * value).

Fixpoint lookup_field (fs : field_store) (name : string) : option value :=
  match fs with
  | [] => None
  | (k, v) :: rest => if String.eqb name k then Some v else lookup_field rest name
  end.

Fixpoint update_field (fs : field_store) (name : string) (v : value) : field_store :=
  match fs with
  | [] => [(name, v)]
  | (k, old) :: rest =>
      if String.eqb name k then (k, v) :: rest else (k, old) :: update_field rest name v
  end.

Lemma lookup_field_nil :
  forall name, lookup_field [] name = None.
Proof.
  reflexivity.
Qed.

Lemma lookup_field_shadow :
  forall name v rest,
    lookup_field ((name, v) :: rest) name = Some v.
Proof.
  intros. simpl. rewrite String.eqb_refl. reflexivity.
Qed.

Theorem update_field_shadow :
  forall fs name v1 v2,
    update_field (update_field fs name v1) name v2 = update_field fs name v2.
Proof.
  induction fs as [| [k old] tail IH]; intros.
  - simpl. destruct (String.eqb name name) eqn:Heq.
    + reflexivity.
    + apply String.eqb_neq in Heq. contradiction.
  - simpl. destruct (String.eqb name k) eqn:Heq.
    + simpl. rewrite Heq. reflexivity.
    + simpl. rewrite Heq. f_equal. apply IH.
Qed.

Theorem update_field_idempotent_same_value :
  forall fs name v,
    update_field (update_field fs name v) name v = update_field fs name v.
Proof.
  intros. rewrite update_field_shadow. reflexivity.
Qed.

Theorem core_update_path_correct :
  forall fs name v,
    lookup_field (update_field fs name v) name = Some v.
Proof.
  induction fs as [| [k old] tail IH]; intros.
  - simpl. rewrite String.eqb_refl. reflexivity.
  - simpl. destruct (String.eqb name k) eqn:Heq.
    + simpl. rewrite Heq. reflexivity.
    + simpl. rewrite Heq. exact (IH name v).
Qed.

Fixpoint lookup_value_path (v : value) (path : list string) : option value :=
  match path with
  | [] => Some v
  | key :: rest =>
      match v with
      | VStruct _ fs =>
          match lookup_field fs key with
          | Some child => lookup_value_path child rest
          | None => None
          end
      | _ => None
      end
  end.

Fixpoint update_value_path (v : value) (path : list string) (newv : value) : option value :=
  match path with
  | [] => Some newv
  | key :: rest =>
      match v with
      | VStruct name fs =>
          match lookup_field fs key with
          | Some child =>
              match update_value_path child rest newv with
              | Some child' => Some (VStruct name (update_field fs key child'))
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  end.

Lemma lookup_value_path_root :
  forall v, lookup_value_path v [] = Some v.
Proof.
  reflexivity.
Qed.

Lemma update_value_path_root :
  forall v newv, update_value_path v [] newv = Some newv.
Proof.
  reflexivity.
Qed.

Theorem update_value_path_one_segment_correct :
  forall name fs key newv,
    lookup_value_path
      (match update_value_path (VStruct name fs) [key] newv with
       | Some out => out
       | None => VStruct name fs
       end)
      [key] =
      match lookup_field fs key with
      | Some _ => Some newv
      | None => None
      end.
Proof.
  intros. simpl.
  destruct (lookup_field fs key) eqn:Hlook.
  - simpl. rewrite core_update_path_correct. reflexivity.
  - rewrite Hlook. reflexivity.
Qed.

Theorem update_value_path_two_segment_correct :
  forall outer innerFs outerFs innerName key newv,
    lookup_field outerFs innerName = Some (VStruct "inner" innerFs) ->
    lookup_value_path
      (match update_value_path (VStruct outer outerFs) [innerName; key] newv with
       | Some out => out
       | None => VStruct outer outerFs
       end)
      [innerName; key] =
      match lookup_field innerFs key with
      | Some _ => Some newv
      | None => None
      end.
Proof.
  intros outer innerFs outerFs innerName key newv Houter.
  simpl. rewrite Houter. simpl.
  destruct (lookup_field innerFs key) eqn:Hinner.
  - replace
      (lookup_field
        (update_field outerFs innerName (VStruct "inner" (update_field innerFs key newv)))
        innerName)
      with (Some (VStruct "inner" (update_field innerFs key newv))).
    + simpl.
      replace
        match lookup_field (update_field innerFs key newv) key with
        | Some child => Some child
        | None => None
        end
      with (Some newv).
      * reflexivity.
      * rewrite (core_update_path_correct innerFs key newv). reflexivity.
    + symmetry. apply core_update_path_correct.
  - simpl. rewrite Houter. simpl. rewrite Hinner. reflexivity.
Qed.

Theorem core_update_preserves_untouched_fields :
  forall fs target other v kept,
    other <> target ->
    lookup_field fs other = Some kept ->
    lookup_field (update_field fs target v) other = Some kept.
Proof.
  induction fs as [| [k old] tail IH]; intros.
  - simpl in H0. discriminate.
  - simpl in H0 |- *.
    destruct (String.eqb_spec other k).
    + subst.
      destruct (String.eqb_spec target k).
      * subst. contradiction.
      * inversion H0. subst. simpl. rewrite String.eqb_refl. reflexivity.
    + destruct (String.eqb_spec target k).
      * subst. simpl. destruct (String.eqb_spec other k).
        { contradiction. }
        { assumption. }
      * simpl. destruct (String.eqb_spec other k).
        { contradiction. }
        { eapply IH; eauto. }
Qed.

Theorem core_update_preserves_missing_untouched_fields :
  forall fs target other v,
    other <> target ->
    lookup_field fs other = None ->
    lookup_field (update_field fs target v) other = None.
Proof.
  induction fs as [| [k old] tail IH]; intros.
  - simpl. destruct (String.eqb_spec other target).
    + contradiction.
    + reflexivity.
  - simpl in H0 |- *.
    destruct (String.eqb_spec other k).
    + subst.
      destruct (String.eqb_spec target k).
      * subst. contradiction.
      * discriminate.
    + destruct (String.eqb_spec target k).
      * subst. simpl. destruct (String.eqb_spec other k).
        { contradiction. }
        { assumption. }
      * simpl. destruct (String.eqb_spec other k).
        { contradiction. }
        { eapply IH; eauto. }
Qed.

Theorem core_update_deterministic :
  forall fs name v1 v2,
    update_field fs name v1 = update_field fs name v2 ->
    v1 = v2.
Proof.
  intros fs name v1 v2 H.
  pose proof (core_update_path_correct fs name v1) as H1.
  pose proof (core_update_path_correct fs name v2) as H2.
  rewrite H in H1.
  rewrite H1 in H2.
  inversion H2. reflexivity.
Qed.

End FoCoreUpdate.
