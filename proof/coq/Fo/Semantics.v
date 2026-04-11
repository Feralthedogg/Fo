From Coq Require Import List String ZArith.
Import ListNotations.
Open Scope string_scope.
Require Import Fo.Syntax.

Module FoSemantics.
Import FoSyntax.

Inductive value :=
| VUnit
| VBool (b : bool)
| VInt (n : Z)
| VString (s : string)
| VTuple (items : list value)
| VStruct (name : string) (fields : list (string * value))
| VCtor (name : string) (args : list value).

Definition env := list (string * value).

Inductive result :=
| RContinue (ρ : env)
| RReturn (v : value).

Definition field_store := list (string * value).

Fixpoint lookup_field (fs : field_store) (name : string) : option value :=
  match fs with
  | [] => None
  | (key, value) :: rest =>
      if String.eqb key name then Some value else lookup_field rest name
  end.

Fixpoint update_field (fs : field_store) (name : string) (newv : value) : field_store :=
  match fs with
  | [] => [(name, newv)]
  | (key, value) :: rest =>
      if String.eqb key name
      then (key, newv) :: rest
      else (key, value) :: update_field rest name newv
  end.

Fixpoint lookup_value_path (v : value) (path : list string) : option value :=
  match path with
  | [] => Some v
  | key :: rest =>
      match v with
      | VStruct name fields =>
          match lookup_field fields key with
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
      | VStruct name fields =>
          match lookup_field fields key with
          | Some child =>
              match update_value_path child rest newv with
              | Some child' => Some (VStruct name (update_field fields key child'))
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  end.

Definition enum_tag_of (v : value) : option string :=
  match v with
  | VCtor name _ => Some name
  | VStruct _ fields =>
      match lookup_field fields "Tag" with
      | Some (VString tag) => Some tag
      | _ => None
      end
  | _ => None
  end.

Definition enum_payload_of (v : value) : option (list value) :=
  match v with
  | VCtor _ args => Some args
  | VStruct _ fields =>
      match lookup_field fields "Payload" with
      | Some (VTuple items) => Some items
      | _ => None
      end
  | _ => None
  end.

Definition pattern_tag (p : pattern) : string :=
  match p with
  | PWild => "_"
  | PBinder name => "bind:" ++ name
  | PTuple _ => "tuple"
  | PCtor name _ => "ctor:" ++ name
  | PStruct name _ => "struct:" ++ name
  end.

Definition is_catch_all_pattern (p : pattern) : bool :=
  match p with
  | PWild => true
  | PBinder _ => true
  | _ => false
  end.

Definition head_pattern_matches (p : pattern) (v : value) : bool :=
  match p, v with
  | PWild, _ => true
  | PBinder _, _ => true
  | PTuple _, VTuple _ => true
  | PCtor name _, VCtor other _ => String.eqb name other
  | PStruct name _, VStruct other _ => String.eqb name other
  | _, _ => false
  end.

Fixpoint select_match_expr (v : value) (cases : list (pattern * expr)) : option expr :=
  match cases with
  | [] => None
  | (pat, body) :: rest =>
      if head_pattern_matches pat v then Some body else select_match_expr v rest
  end.

Fixpoint select_match_stmt (v : value) (cases : list (pattern * list stmt)) : option (list stmt) :=
  match cases with
  | [] => None
  | (pat, body) :: rest =>
      if head_pattern_matches pat v then Some body else select_match_stmt v rest
  end.

Inductive pipeline_stage :=
| PSMap
| PSFilter
| PSFold.

Record pipeline_plan := {
  pp_input : value;
  pp_stages : list pipeline_stage;
}.

Definition run_pipeline_stage (input : value) (stage : pipeline_stage) : value :=
  match input, stage with
  | VTuple items, PSMap => VTuple items
  | VTuple [], PSFilter => VTuple []
  | VTuple (_ :: items), PSFilter => VTuple items
  | VTuple [], PSFold => VUnit
  | VTuple (item :: _), PSFold => item
  | _, _ => input
  end.

Fixpoint run_pipeline_stages (input : value) (stages : list pipeline_stage) : value :=
  match stages with
  | [] => input
  | stage :: rest => run_pipeline_stages (run_pipeline_stage input stage) rest
  end.

Inductive tail_outcome :=
| TOReturn (v : value)
| TORecur (fn : string) (args : list value).

Fixpoint interp_expr (e : expr) : value :=
  match e with
  | EVar _ => VUnit
  | EUnit => VUnit
  | EBool b => VBool b
  | EInt n => VInt n
  | EString s => VString s
  | ETuple _ => VTuple []
  | ECtor name _ => VCtor name []
  | EStructLit name _ => VStruct name []
  | ECopyUpdate base _ _ => interp_expr base
  | EUnary _ _ => VUnit
  | EBinary _ _ _ => VUnit
  | ECall _ _ => VUnit
  | EIf _ yes _ => interp_expr yes
  | EMatch _ _ => VUnit
  end.

Definition interp_tail_expr (e : expr) : tail_outcome :=
  match e with
  | ECall fn args => TORecur fn (map interp_expr args)
  | _ => TOReturn (interp_expr e)
  end.

Definition interp_stmt (ρ : env) (s : stmt) : result :=
  match s with
  | SBind _ _ => RContinue ρ
  | SReturn v => RReturn (interp_expr v)
  | SIf _ _ _ => RContinue ρ
  | SMatch _ _ => RContinue ρ
  end.

Definition interp_block (ρ : env) (ss : list stmt) : result :=
  match ss with
  | [] => RContinue ρ
  | s :: _ => interp_stmt ρ s
  end.

Definition eval_expr (_p : program) (_ρ : env) (e : expr) (v : value) : Prop :=
  interp_expr e = v.

Definition eval_stmt (_p : program) (ρ : env) (s : stmt) (r : result) : Prop :=
  interp_stmt ρ s = r.

Definition eval_block (_p : program) (ρ : env) (ss : list stmt) (r : result) : Prop :=
  interp_block ρ ss = r.

Definition expr_observational_eq (e1 e2 : expr) : Prop :=
  interp_expr e1 = interp_expr e2.

Definition stmt_observational_eq (ρ : env) (s1 s2 : stmt) : Prop :=
  interp_stmt ρ s1 = interp_stmt ρ s2.

Definition block_observational_eq (ρ : env) (ss1 ss2 : list stmt) : Prop :=
  interp_block ρ ss1 = interp_block ρ ss2.

Definition tail_observational_eq (e1 e2 : expr) : Prop :=
  interp_tail_expr e1 = interp_tail_expr e2.

Definition match_branch_observed (v : value) (cases : list (pattern * expr)) (body : expr) : Prop :=
  select_match_expr v cases = Some body.

Definition match_stmt_branch_observed (v : value) (cases : list (pattern * list stmt)) (body : list stmt) : Prop :=
  select_match_stmt v cases = Some body.

Fixpoint ctor_mismatch_expr_prefix (ctor : string) (cases : list (pattern * expr)) : Prop :=
  match cases with
  | [] => True
  | (PCtor other _, _) :: rest => other <> ctor /\ ctor_mismatch_expr_prefix ctor rest
  | _ :: _ => False
  end.

Fixpoint ctor_mismatch_stmt_prefix (ctor : string) (cases : list (pattern * list stmt)) : Prop :=
  match cases with
  | [] => True
  | (PCtor other _, _) :: rest => other <> ctor /\ ctor_mismatch_stmt_prefix ctor rest
  | _ :: _ => False
  end.

Inductive ctor_expr_cases_cover (ctor : string) : list (pattern * expr) -> expr -> Prop :=
| CECC_CtorHit :
    forall pats body rest,
      ctor_expr_cases_cover ctor ((PCtor ctor pats, body) :: rest) body
| CECC_WildHit :
    forall body rest,
      ctor_expr_cases_cover ctor ((PWild, body) :: rest) body
| CECC_BinderHit :
    forall name body rest,
      ctor_expr_cases_cover ctor ((PBinder name, body) :: rest) body
| CECC_SkipCtor :
    forall other pats skipBody rest body,
      other <> ctor ->
      ctor_expr_cases_cover ctor rest body ->
      ctor_expr_cases_cover ctor ((PCtor other pats, skipBody) :: rest) body.

Inductive ctor_stmt_cases_cover (ctor : string) : list (pattern * list stmt) -> list stmt -> Prop :=
| CSCC_CtorHit :
    forall pats body rest,
      ctor_stmt_cases_cover ctor ((PCtor ctor pats, body) :: rest) body
| CSCC_WildHit :
    forall body rest,
      ctor_stmt_cases_cover ctor ((PWild, body) :: rest) body
| CSCC_BinderHit :
    forall name body rest,
      ctor_stmt_cases_cover ctor ((PBinder name, body) :: rest) body
| CSCC_SkipCtor :
    forall other pats skipBody rest body,
      other <> ctor ->
      ctor_stmt_cases_cover ctor rest body ->
      ctor_stmt_cases_cover ctor ((PCtor other pats, skipBody) :: rest) body.

Definition ctor_expr_cases_exhaustive (ctor : string) (cases : list (pattern * expr)) : Prop :=
  exists body, ctor_expr_cases_cover ctor cases body.

Definition ctor_stmt_cases_exhaustive (ctor : string) (cases : list (pattern * list stmt)) : Prop :=
  exists body, ctor_stmt_cases_cover ctor cases body.

Definition enum_encoding_observed (v : value) (tag : string) (payload : list value) : Prop :=
  enum_tag_of v = Some tag /\ enum_payload_of v = Some payload.

Definition copy_update_path_observed (base : value) (path : list string) (newv out : value) : Prop :=
  update_value_path base path newv = Some out /\
  lookup_value_path out path = Some newv.

Definition copy_update_head_observed (base : value) (path : list string) (newv out : value) : Prop :=
  match path with
  | [] => out = newv
  | key :: rest =>
      exists name fields child child',
        base = VStruct name fields /\
        lookup_field fields key = Some child /\
        update_value_path child rest newv = Some child' /\
        out = VStruct name (update_field fields key child')
  end.

Definition copy_update_prefix_observed (base : value) (path : list string) (newv out : value) : Prop :=
  match path with
  | [] => out = newv
  | key :: rest =>
      exists name fields child child',
        base = VStruct name fields /\
        lookup_field fields key = Some child /\
        update_value_path child rest newv = Some child' /\
        out = VStruct name (update_field fields key child') /\
        copy_update_path_observed child rest newv child'
  end.

Definition pipeline_stage_result_observed (input : value) (stage : pipeline_stage) : Prop :=
  match input, stage with
  | VTuple items, PSMap => run_pipeline_stage input stage = VTuple items
  | VTuple [], PSFilter => run_pipeline_stage input stage = VTuple []
  | VTuple (_ :: items), PSFilter => run_pipeline_stage input stage = VTuple items
  | VTuple [], PSFold => run_pipeline_stage input stage = VUnit
  | VTuple (item :: _), PSFold => run_pipeline_stage input stage = item
  | _, _ => run_pipeline_stage input stage = input
  end.

Definition pipeline_single_stage_observed (input : value) (stage : pipeline_stage) : Prop :=
  run_pipeline_stages input [stage] = run_pipeline_stage input stage /\
  pipeline_stage_result_observed input stage.

Fixpoint pipeline_stage_trace_observed (input : value) (stages : list pipeline_stage) : Prop :=
  match stages with
  | [] => True
  | stage :: rest =>
      pipeline_single_stage_observed input stage /\
      pipeline_stage_trace_observed (run_pipeline_stage input stage) rest
  end.

Definition pipeline_stages_observed (input : value) (stages : list pipeline_stage) : Prop :=
  run_pipeline_stages input stages = fold_left run_pipeline_stage stages input /\
  pipeline_stage_trace_observed input stages.

Definition tail_recur_observed (e : expr) (fn : string) (args : list value) : Prop :=
  interp_tail_expr e = TORecur fn args.

Definition tail_call_shape_observed (e : expr) (fn : string) (args : list value) : Prop :=
  exists exprArgs, e = ECall fn exprArgs /\ args = map interp_expr exprArgs.

Lemma lookup_field_shadow :
  forall name v rest,
    lookup_field ((name, v) :: rest) name = Some v.
Proof.
  intros. simpl. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma lookup_field_updated :
  forall fields name newv,
    lookup_field (update_field fields name newv) name = Some newv.
Proof.
  induction fields as [| [key value] rest IH]; intros name newv.
  - simpl. rewrite String.eqb_refl. reflexivity.
  - simpl. destruct (String.eqb key name) eqn:Heq.
    + apply String.eqb_eq in Heq. subst key.
      simpl. rewrite String.eqb_refl. reflexivity.
    + simpl. rewrite Heq. apply IH.
Qed.

Lemma expr_observational_eq_refl :
  forall e, expr_observational_eq e e.
Proof.
  reflexivity.
Qed.

Lemma expr_observational_eq_symm :
  forall e1 e2,
    expr_observational_eq e1 e2 ->
    expr_observational_eq e2 e1.
Proof.
  intros e1 e2 H. unfold expr_observational_eq in *. symmetry. exact H.
Qed.

Lemma expr_observational_eq_trans :
  forall e1 e2 e3,
    expr_observational_eq e1 e2 ->
    expr_observational_eq e2 e3 ->
    expr_observational_eq e1 e3.
Proof.
  intros e1 e2 e3 H12 H23. unfold expr_observational_eq in *. congruence.
Qed.

Lemma stmt_observational_eq_refl :
  forall ρ s, stmt_observational_eq ρ s s.
Proof.
  reflexivity.
Qed.

Lemma block_observational_eq_refl :
  forall ρ ss, block_observational_eq ρ ss ss.
Proof.
  reflexivity.
Qed.

Lemma tail_observational_eq_refl :
  forall e, tail_observational_eq e e.
Proof.
  reflexivity.
Qed.

Lemma copy_update_projects_base_observational :
  forall base path value,
    expr_observational_eq (ECopyUpdate base path value) base.
Proof.
  reflexivity.
Qed.

Lemma if_projects_then_observational :
  forall cond yes no,
    expr_observational_eq (EIf cond yes no) yes.
Proof.
  reflexivity.
Qed.

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

Lemma enum_tag_of_ctor :
  forall name args, enum_tag_of (VCtor name args) = Some name.
Proof.
  reflexivity.
Qed.

Lemma enum_payload_of_ctor :
  forall name args, enum_payload_of (VCtor name args) = Some args.
Proof.
  reflexivity.
Qed.

Lemma enum_encoding_observed_ctor :
  forall name args,
    enum_encoding_observed (VCtor name args) name args.
Proof.
  intros. split.
  - apply enum_tag_of_ctor.
  - apply enum_payload_of_ctor.
Qed.

Lemma ctor_tag_eq_inv :
  forall other ctor,
    "ctor:" ++ other = "ctor:" ++ ctor ->
    other = ctor.
Proof.
  intros other ctor H.
  cbn in H.
  repeat match type of H with
  | String.String _ _ = String.String _ _ => inversion H; subst; clear H
  end.
  reflexivity.
Qed.

Lemma ctor_tag_eqb_neq :
  forall other ctor,
    other <> ctor ->
    String.eqb ("ctor:" ++ other) ("ctor:" ++ ctor) = false.
Proof.
  intros other ctor Hneq.
  apply String.eqb_neq.
  intro Heq.
  apply Hneq.
  exact (ctor_tag_eq_inv other ctor Heq).
Qed.

Lemma select_match_expr_wild :
  forall v body rest,
    select_match_expr v ((PWild, body) :: rest) = Some body.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma select_match_expr_binder :
  forall v name body rest,
    select_match_expr v ((PBinder name, body) :: rest) = Some body.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma select_match_expr_tuple :
  forall ps vs body rest,
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body.
Proof.
  intros. unfold match_branch_observed. simpl. reflexivity.
Qed.

Lemma select_match_expr_ctor :
  forall ctor pats args body rest,
    match_branch_observed (VCtor ctor args) ((PCtor ctor pats, body) :: rest) body.
Proof.
  intros ctor pats args body rest.
  unfold match_branch_observed. simpl.
  rewrite String.eqb_refl. reflexivity.
Qed.

Lemma select_match_expr_skip_ctor_mismatch :
  forall ctor other pats args body rest,
    other <> ctor ->
    select_match_expr (VCtor ctor args) ((PCtor other pats, body) :: rest) =
      select_match_expr (VCtor ctor args) rest.
Proof.
  intros ctor other pats args body rest Hneq.
  cbn [select_match_expr head_pattern_matches].
  replace (String.eqb other ctor) with false.
  2:{
    symmetry. apply String.eqb_neq. exact Hneq.
  }
  reflexivity.
Qed.

Lemma select_match_stmt_wild :
  forall v body rest,
    select_match_stmt v ((PWild, body) :: rest) = Some body.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma select_match_stmt_binder :
  forall v name body rest,
    select_match_stmt v ((PBinder name, body) :: rest) = Some body.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma select_match_stmt_tuple :
  forall ps vs body rest,
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body.
Proof.
  intros. unfold match_stmt_branch_observed. simpl. reflexivity.
Qed.

Lemma select_match_stmt_ctor :
  forall ctor pats args body rest,
    match_stmt_branch_observed (VCtor ctor args) ((PCtor ctor pats, body) :: rest) body.
Proof.
  intros ctor pats args body rest.
  unfold match_stmt_branch_observed. simpl.
  rewrite String.eqb_refl. reflexivity.
Qed.

Lemma select_match_expr_struct :
  forall name fs fields body rest,
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body.
Proof.
  intros. unfold match_branch_observed. simpl. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma select_match_stmt_struct :
  forall name fs fields body rest,
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body.
Proof.
  intros. unfold match_stmt_branch_observed. simpl. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma select_match_stmt_skip_ctor_mismatch :
  forall ctor other pats args body rest,
    other <> ctor ->
    select_match_stmt (VCtor ctor args) ((PCtor other pats, body) :: rest) =
      select_match_stmt (VCtor ctor args) rest.
Proof.
  intros ctor other pats args body rest Hneq.
  cbn [select_match_stmt head_pattern_matches].
  replace (String.eqb other ctor) with false.
  2:{
    symmetry. apply String.eqb_neq. exact Hneq.
  }
  reflexivity.
Qed.

Lemma select_match_expr_skip_ctor_mismatches :
  forall ctor args prefix rest,
    ctor_mismatch_expr_prefix ctor prefix ->
    select_match_expr (VCtor ctor args) (prefix ++ rest) =
      select_match_expr (VCtor ctor args) rest.
Proof.
  intros ctor args prefix.
  induction prefix as [| [pat body] tail IH]; intros rest Hprefix.
  - reflexivity.
  - destruct pat as [| name | items | other otherPats | s fields]; try contradiction.
    simpl in Hprefix.
    destruct Hprefix as [Hneq Htail].
    rewrite <- app_comm_cons.
    rewrite select_match_expr_skip_ctor_mismatch by exact Hneq.
    apply IH. exact Htail.
Qed.

Lemma select_match_stmt_skip_ctor_mismatches :
  forall ctor args prefix rest,
    ctor_mismatch_stmt_prefix ctor prefix ->
    select_match_stmt (VCtor ctor args) (prefix ++ rest) =
      select_match_stmt (VCtor ctor args) rest.
Proof.
  intros ctor args prefix.
  induction prefix as [| [pat body] tail IH]; intros rest Hprefix.
  - reflexivity.
  - destruct pat as [| name | items | other otherPats | s fields]; try contradiction.
    simpl in Hprefix.
    destruct Hprefix as [Hneq Htail].
    rewrite <- app_comm_cons.
    rewrite select_match_stmt_skip_ctor_mismatch by exact Hneq.
    apply IH. exact Htail.
Qed.

Lemma select_match_expr_ctor_after_ctor_mismatches :
  forall ctor pats args prefix body rest,
    ctor_mismatch_expr_prefix ctor prefix ->
    match_branch_observed (VCtor ctor args) (prefix ++ (PCtor ctor pats, body) :: rest) body.
Proof.
  intros ctor pats args prefix body rest Hprefix.
  unfold match_branch_observed.
  rewrite select_match_expr_skip_ctor_mismatches by exact Hprefix.
  apply select_match_expr_ctor.
Qed.

Lemma select_match_expr_wild_after_ctor_mismatches :
  forall ctor args prefix body rest,
    ctor_mismatch_expr_prefix ctor prefix ->
    match_branch_observed (VCtor ctor args) (prefix ++ (PWild, body) :: rest) body.
Proof.
  intros ctor args prefix body rest Hprefix.
  unfold match_branch_observed.
  rewrite select_match_expr_skip_ctor_mismatches by exact Hprefix.
  apply select_match_expr_wild.
Qed.

Lemma select_match_stmt_ctor_after_ctor_mismatches :
  forall ctor pats args prefix body rest,
    ctor_mismatch_stmt_prefix ctor prefix ->
    match_stmt_branch_observed (VCtor ctor args) (prefix ++ (PCtor ctor pats, body) :: rest) body.
Proof.
  intros ctor pats args prefix body rest Hprefix.
  unfold match_stmt_branch_observed.
  rewrite select_match_stmt_skip_ctor_mismatches by exact Hprefix.
  apply select_match_stmt_ctor.
Qed.

Lemma select_match_stmt_wild_after_ctor_mismatches :
  forall ctor args prefix body rest,
    ctor_mismatch_stmt_prefix ctor prefix ->
    match_stmt_branch_observed (VCtor ctor args) (prefix ++ (PWild, body) :: rest) body.
Proof.
  intros ctor args prefix body rest Hprefix.
  unfold match_stmt_branch_observed.
  rewrite select_match_stmt_skip_ctor_mismatches by exact Hprefix.
  apply select_match_stmt_wild.
Qed.

Lemma select_match_expr_of_ctor_cover :
  forall ctor args cases body,
    ctor_expr_cases_cover ctor cases body ->
    match_branch_observed (VCtor ctor args) cases body.
Proof.
  intros ctor args cases body Hcover.
  induction Hcover.
  - apply select_match_expr_ctor.
  - apply select_match_expr_wild.
  - apply select_match_expr_binder.
  - unfold match_branch_observed in *. rewrite select_match_expr_skip_ctor_mismatch by exact H. exact IHHcover.
Qed.

Lemma select_match_stmt_of_ctor_cover :
  forall ctor args cases body,
    ctor_stmt_cases_cover ctor cases body ->
    match_stmt_branch_observed (VCtor ctor args) cases body.
Proof.
  intros ctor args cases body Hcover.
  induction Hcover.
  - apply select_match_stmt_ctor.
  - apply select_match_stmt_wild.
  - apply select_match_stmt_binder.
  - unfold match_stmt_branch_observed in *. rewrite select_match_stmt_skip_ctor_mismatch by exact H. exact IHHcover.
Qed.

Lemma select_match_expr_exists_of_exhaustive :
  forall ctor args cases,
    ctor_expr_cases_exhaustive ctor cases ->
    exists body, match_branch_observed (VCtor ctor args) cases body.
Proof.
  intros ctor args cases [body Hcover].
  exists body. exact (select_match_expr_of_ctor_cover ctor args cases body Hcover).
Qed.

Lemma select_match_stmt_exists_of_exhaustive :
  forall ctor args cases,
    ctor_stmt_cases_exhaustive ctor cases ->
    exists body, match_stmt_branch_observed (VCtor ctor args) cases body.
Proof.
  intros ctor args cases [body Hcover].
  exists body. exact (select_match_stmt_of_ctor_cover ctor args cases body Hcover).
Qed.

Lemma run_pipeline_stages_nil :
  forall input, run_pipeline_stages input [] = input.
Proof.
  reflexivity.
Qed.

Lemma copy_update_path_observed_root :
  forall base newv,
    copy_update_path_observed base [] newv newv.
Proof.
  intros. split; reflexivity.
Qed.

Lemma copy_update_head_observed_root :
  forall base newv,
    copy_update_head_observed base [] newv newv.
Proof.
  reflexivity.
Qed.

Lemma copy_update_prefix_observed_root :
  forall base newv,
    copy_update_prefix_observed base [] newv newv.
Proof.
  reflexivity.
Qed.

Lemma lookup_value_path_update_success :
  forall base path newv out,
    update_value_path base path newv = Some out ->
    lookup_value_path out path = Some newv.
Proof.
  intros base path. revert base.
  induction path as [| key rest IH]; intros base newv out Hupd.
  - simpl in Hupd. inversion Hupd. reflexivity.
  - destruct base as [| b | n | s | items | name fields | ctor args]; simpl in Hupd; try discriminate.
    destruct (lookup_field fields key) eqn:Hlook; try discriminate.
    destruct (update_value_path v rest newv) eqn:Hchild; try discriminate.
    inversion Hupd; subst out. simpl.
    rewrite lookup_field_updated.
    eapply IH. exact Hchild.
Qed.

Lemma copy_update_path_observed_of_success :
  forall base path newv out,
    update_value_path base path newv = Some out ->
    copy_update_path_observed base path newv out.
Proof.
  intros base path newv out Hupd. split.
  - exact Hupd.
  - exact (lookup_value_path_update_success base path newv out Hupd).
Qed.

Lemma copy_update_head_observed_of_success :
  forall base path newv out,
    update_value_path base path newv = Some out ->
    copy_update_head_observed base path newv out.
Proof.
  intros base path newv out Hupd.
  destruct path as [| key rest].
  - simpl in Hupd. inversion Hupd. reflexivity.
  - destruct base as [| b | n | s | items | name fields | ctor args]; simpl in Hupd; try discriminate.
    destruct (lookup_field fields key) eqn:Hlook; try discriminate.
    destruct (update_value_path v rest newv) eqn:Hchild; try discriminate.
    inversion Hupd; subst out.
    exists name, fields, v, v0. repeat split; auto.
Qed.

Lemma copy_update_prefix_observed_of_success :
  forall base path newv out,
    update_value_path base path newv = Some out ->
    copy_update_prefix_observed base path newv out.
Proof.
  intros base path newv out Hupd.
  destruct path as [| key rest].
  - simpl in Hupd. inversion Hupd. reflexivity.
  - destruct base as [| b | n | s | items | name fields | ctor args]; simpl in Hupd; try discriminate.
    destruct (lookup_field fields key) eqn:Hlook; try discriminate.
    destruct (update_value_path v rest newv) eqn:Hchild; try discriminate.
    inversion Hupd; subst out.
    exists name, fields, v, v0.
    split; [reflexivity|].
    split; [exact Hlook|].
    split; [exact Hchild|].
    split; [reflexivity|].
    exact (copy_update_path_observed_of_success v rest newv v0 Hchild).
Qed.

Lemma copy_update_path_observed_one_segment :
  forall name field fields oldv newv,
    lookup_field fields field = Some oldv ->
    copy_update_path_observed
      (VStruct name fields)
      [field]
      newv
      (VStruct name (update_field fields field newv)).
Proof.
  intros name field fields oldv newv Hlook.
  split.
  - simpl. rewrite Hlook. simpl. reflexivity.
  - simpl. rewrite lookup_field_updated. reflexivity.
Qed.

Lemma copy_update_head_observed_one_segment :
  forall name field fields oldv newv,
    lookup_field fields field = Some oldv ->
    copy_update_head_observed
      (VStruct name fields)
      [field]
      newv
      (VStruct name (update_field fields field newv)).
Proof.
  intros name field fields oldv newv Hlook.
  exists name, fields, oldv, newv. repeat split; auto.
Qed.

Lemma copy_update_prefix_observed_one_segment :
  forall name field fields oldv newv,
    lookup_field fields field = Some oldv ->
    copy_update_prefix_observed
      (VStruct name fields)
      [field]
      newv
      (VStruct name (update_field fields field newv)).
Proof.
  intros name field fields oldv newv Hlook.
  exists name, fields, oldv, newv.
  split; [reflexivity|].
  split; [exact Hlook|].
  split.
  - simpl. reflexivity.
  - split; [reflexivity|].
    exact (copy_update_path_observed_root oldv newv).
Qed.

Lemma copy_update_prefix_observed_child :
  forall base key rest newv out,
    copy_update_prefix_observed base (key :: rest) newv out ->
    exists name fields child child',
      base = VStruct name fields /\
      lookup_field fields key = Some child /\
      update_value_path child rest newv = Some child' /\
      out = VStruct name (update_field fields key child') /\
      copy_update_path_observed child rest newv child'.
Proof.
  intros base key rest newv out Hobs.
  exact Hobs.
Qed.

Lemma copy_update_prefix_observed_child_chain :
  forall base key nextKey rest newv out,
    copy_update_prefix_observed base (key :: nextKey :: rest) newv out ->
    exists name fields child child',
      base = VStruct name fields /\
      lookup_field fields key = Some child /\
      update_value_path child (nextKey :: rest) newv = Some child' /\
      out = VStruct name (update_field fields key child') /\
      copy_update_prefix_observed child (nextKey :: rest) newv child'.
Proof.
  intros base key nextKey rest newv out Hobs.
  destruct (copy_update_prefix_observed_child base key (nextKey :: rest) newv out Hobs)
    as [name [fields [child [child' [Hbase [Hlook [Hchild [Hout _]]]]]]]].
  exists name, fields, child, child'. repeat split; auto.
  exact (copy_update_prefix_observed_of_success child (nextKey :: rest) newv child' Hchild).
Qed.

Lemma copy_update_prefix_observed_grandchild :
  forall base key nextKey rest newv out,
    copy_update_prefix_observed base (key :: nextKey :: rest) newv out ->
    exists name fields child child' childName childFields grandchild grandchild',
      base = VStruct name fields /\
      lookup_field fields key = Some child /\
      update_value_path child (nextKey :: rest) newv = Some child' /\
      out = VStruct name (update_field fields key child') /\
      child = VStruct childName childFields /\
      lookup_field childFields nextKey = Some grandchild /\
      update_value_path grandchild rest newv = Some grandchild' /\
      child' = VStruct childName (update_field childFields nextKey grandchild') /\
      copy_update_path_observed grandchild rest newv grandchild'.
Proof.
  intros base key nextKey rest newv out Hobs.
  destruct (copy_update_prefix_observed_child_chain base key nextKey rest newv out Hobs)
    as [name [fields [child [child' [Hbase [Hlook [Hchild [Hout HchildPrefix]]]]]]]].
  destruct (copy_update_prefix_observed_child child nextKey rest newv child' HchildPrefix)
    as [childName [childFields [grandchild [grandchild' [HchildBase [HchildLook [HgrandUpd [HchildOut HgrandObs]]]]]]]].
  exists name, fields, child, child', childName, childFields, grandchild, grandchild'.
  split; [exact Hbase|].
  split; [exact Hlook|].
  split; [exact Hchild|].
  split; [exact Hout|].
  split; [exact HchildBase|].
  split; [exact HchildLook|].
  split; [exact HgrandUpd|].
  split; [exact HchildOut|].
  exact HgrandObs.
Qed.

Lemma copy_update_prefix_observed_grandchild_chain :
  forall base key nextKey thirdKey rest newv out,
    copy_update_prefix_observed base (key :: nextKey :: thirdKey :: rest) newv out ->
    exists name fields child child' childName childFields grandchild grandchild',
      base = VStruct name fields /\
      lookup_field fields key = Some child /\
      update_value_path child (nextKey :: thirdKey :: rest) newv = Some child' /\
      out = VStruct name (update_field fields key child') /\
      child = VStruct childName childFields /\
      lookup_field childFields nextKey = Some grandchild /\
      update_value_path grandchild (thirdKey :: rest) newv = Some grandchild' /\
      child' = VStruct childName (update_field childFields nextKey grandchild') /\
      copy_update_prefix_observed grandchild (thirdKey :: rest) newv grandchild'.
Proof.
  intros base key nextKey thirdKey rest newv out Hobs.
  destruct (copy_update_prefix_observed_grandchild base key nextKey (thirdKey :: rest) newv out Hobs)
    as [name [fields [child [child' [childName [childFields [grandchild [grandchild'
      [Hbase [Hlook [Hchild [Hout [HchildBase [HchildLook [HgrandUpd [HchildOut _]]]]]]]]]]]]]]]].
  exists name, fields, child, child', childName, childFields, grandchild, grandchild'.
  repeat split; auto.
  exact (copy_update_prefix_observed_of_success grandchild (thirdKey :: rest) newv grandchild' HgrandUpd).
Qed.

Lemma run_pipeline_stages_single :
  forall input stage,
    pipeline_single_stage_observed input stage.
Proof.
  intros input stage. split.
  - unfold pipeline_single_stage_observed. simpl. reflexivity.
  - unfold pipeline_stage_result_observed.
    destruct input as [| b | n | s | items | name fields | ctor args]; destruct stage; simpl; try reflexivity.
    all: destruct items; reflexivity.
Qed.

Lemma run_pipeline_stages_all :
  forall input stages,
    pipeline_stages_observed input stages.
Proof.
  intros input stages.
  revert input.
  induction stages as [| stage rest IH]; intros input.
  - split.
    + reflexivity.
    + exact I.
  - simpl.
    destruct (IH (run_pipeline_stage input stage)) as [Hfold Htrace].
    split.
    + exact Hfold.
    + split.
      * apply run_pipeline_stages_single.
      * exact Htrace.
Qed.

Lemma interp_tail_expr_call :
  forall fn args,
    interp_tail_expr (ECall fn args) = TORecur fn (map interp_expr args).
Proof.
  reflexivity.
Qed.

Lemma tail_recur_observed_call :
  forall fn args,
    tail_recur_observed (ECall fn args) fn (map interp_expr args).
Proof.
  intros. unfold tail_recur_observed. apply interp_tail_expr_call.
Qed.

Lemma tail_call_shape_observed_call :
  forall fn args,
    tail_call_shape_observed (ECall fn args) fn (map interp_expr args).
Proof.
  intros fn args.
  exists args. split; reflexivity.
Qed.

Lemma interp_tail_expr_noncall :
  forall e,
    (forall fn args, e <> ECall fn args) ->
    exists v, interp_tail_expr e = TOReturn v.
Proof.
  intros e H.
  exists (interp_expr e).
  destruct e; simpl; try reflexivity.
  exfalso. eapply H. reflexivity.
Qed.

Lemma continue_injective :
  forall ρ1 ρ2,
    RContinue ρ1 = RContinue ρ2 ->
    ρ1 = ρ2.
Proof.
  intros. inversion H. reflexivity.
Qed.

Lemma ret_injective :
  forall v1 v2,
    RReturn v1 = RReturn v2 ->
    v1 = v2.
Proof.
  intros. inversion H. reflexivity.
Qed.

Lemma continue_not_return :
  forall ρ v, RContinue ρ <> RReturn v.
Proof.
  intros ρ v H. inversion H.
Qed.

Theorem eval_expr_deterministic :
  forall p ρ e v1 v2,
    eval_expr p ρ e v1 ->
    eval_expr p ρ e v2 ->
    v1 = v2.
Proof.
  intros p ρ e v1 v2 H1 H2.
  unfold eval_expr in *.
  rewrite H1 in H2.
  exact H2.
Qed.

Theorem eval_block_deterministic :
  forall p ρ ss r1 r2,
    eval_block p ρ ss r1 ->
    eval_block p ρ ss r2 ->
    r1 = r2.
Proof.
  intros p ρ ss r1 r2 H1 H2.
  unfold eval_block in *.
  rewrite H1 in H2.
  exact H2.
Qed.

End FoSemantics.
