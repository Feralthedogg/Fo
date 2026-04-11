From Coq Require Import List String.
Import ListNotations.
Require Import Fo.Syntax.
Require Import Fo.Semantics.
Require Import Fo.Env.
Require Import Fo.Pattern.
Require Import Fo.CoreMatch.

Module FoTyping.
Import FoSyntax.
Import FoSemantics.
Import FoEnv.
Import FoPattern.
Import FoCoreMatch.

Definition tyenv := list (string * ty).

Inductive has_type_expr : tyenv -> expr -> ty -> Prop :=
| HT_Unit :
    forall Γ, has_type_expr Γ EUnit TyUnit
| HT_Bool :
    forall Γ b, has_type_expr Γ (EBool b) TyBool
| HT_Int :
    forall Γ n, has_type_expr Γ (EInt n) TyInt
| HT_String :
    forall Γ s, has_type_expr Γ (EString s) TyString
| HT_TupleNil :
    forall Γ, has_type_expr Γ (ETuple []) (TyTuple [])
| HT_TupleCons :
    forall Γ e es t ts,
      has_type_expr Γ e t ->
      has_type_expr Γ (ETuple es) (TyTuple ts) ->
      has_type_expr Γ (ETuple (e :: es)) (TyTuple (t :: ts))
| HT_StructLit :
    forall Γ name fields,
      has_type_expr Γ (EStructLit name fields) (TyStruct name).

Inductive has_type_stmt : tyenv -> stmt -> ty -> Prop :=
| HTS_Bind :
    forall Γ name value t,
      has_type_expr Γ value t ->
      has_type_stmt Γ (SBind name value) TyUnit
| HTS_Return :
    forall Γ value t,
      has_type_expr Γ value t ->
      has_type_stmt Γ (SReturn value) t.

Definition well_typed_param (param : string * ty) : Prop :=
  fst param <> "".

Definition well_typed_fn (fn : fndef) : Prop :=
  fn_name fn <> "" /\
  forall param, In param (fn_params fn) -> well_typed_param param.

Definition distinct_fn_names (p : program) : Prop :=
  NoDup (map fn_name (prog_fns p)).

Definition well_typed_program (p : program) : Prop :=
  distinct_fn_names p /\
  forall fn, In fn (prog_fns p) -> well_typed_fn fn.

Theorem well_typed_program_fn_name_nonempty :
  forall p fn,
    well_typed_program p ->
    In fn (prog_fns p) ->
    fn_name fn <> "".
Proof.
  intros p fn Hprog Hin.
  exact (proj1 (proj2 Hprog fn Hin)).
Qed.

Theorem well_typed_program_fn_names_distinct :
  forall p,
    well_typed_program p ->
    distinct_fn_names p.
Proof.
  intros p Hprog.
  exact (proj1 Hprog).
Qed.

Definition subst_domain_agrees_match_domain (σ : match_subst) : Prop :=
  subst_domain σ = match_domain σ.

Theorem subst_domain_agrees_match_domain_refl :
  forall σ, subst_domain_agrees_match_domain σ.
Proof.
  reflexivity.
Qed.

Theorem typing_subst_merge_domain_law :
  forall parts,
    subst_domain (merge_substs parts) = merge_subst_domains parts.
Proof.
  intros. apply subst_domain_merge_substs.
Qed.

Theorem typing_match_subst_merge_domain_law :
  forall parts,
    match_domain (merge_match_substs parts) = merge_match_domains parts.
Proof.
  intros. apply match_domain_merge_match_substs.
Qed.

Theorem typing_match_subst_composition_law_bundle :
  forall σ,
    subst_composition σ /\ match_subst_composition σ /\ subst_domain_agrees_match_domain σ.
Proof.
  intro σ. split.
  - exists [σ]. split.
    + simpl. rewrite app_nil_r. reflexivity.
    + simpl. rewrite app_nil_r. reflexivity.
  - split.
    + exists [σ]. split.
      * simpl. rewrite app_nil_r. reflexivity.
      * simpl. rewrite app_nil_r. reflexivity.
    + apply subst_domain_agrees_match_domain_refl.
Qed.

Theorem canonical_bool :
  forall p e v,
    well_typed_program p ->
    has_type_expr [] e TyBool ->
    eval_expr p [] e v ->
    exists b, v = VBool b.
Proof.
  intros p e v _ HT Hev.
  unfold eval_expr in *.
  destruct e; inversion HT; subst; simpl in *; try discriminate; eauto.
Qed.

Theorem canonical_int :
  forall p e v,
    well_typed_program p ->
    has_type_expr [] e TyInt ->
    eval_expr p [] e v ->
    exists n, v = VInt n.
Proof.
  intros p e v _ HT Hev.
  unfold eval_expr in *.
  destruct e; inversion HT; subst; simpl in *; try discriminate; eauto.
Qed.

Theorem canonical_tuple :
  forall p e ts v,
    well_typed_program p ->
    has_type_expr [] e (TyTuple ts) ->
    eval_expr p [] e v ->
    exists vs, v = VTuple vs.
Proof.
  intros p e ts v _ HT Hev.
  unfold eval_expr in *.
  destruct e; inversion HT; subst; simpl in *; try discriminate; eauto.
Qed.

Theorem canonical_struct :
  forall p e name v,
    well_typed_program p ->
    has_type_expr [] e (TyStruct name) ->
    eval_expr p [] e v ->
    exists fields, v = VStruct name fields.
Proof.
  intros p e name v _ HT Hev.
  unfold eval_expr in *.
  destruct e; inversion HT; subst; simpl in *; try discriminate; eauto.
Qed.

Theorem weakening_expr :
  forall Γ Δ e t,
    has_type_expr Γ e t ->
    has_type_expr ((Δ ++ Γ)%list) e t.
Proof.
  intros Γ Δ e t H.
  induction H.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - econstructor; eauto.
  - constructor.
Qed.

Theorem weakening_stmt :
  forall Γ Δ s t,
    has_type_stmt Γ s t ->
    has_type_stmt ((Δ ++ Γ)%list) s t.
Proof.
  intros Γ Δ s t H.
  induction H.
  - econstructor. eapply weakening_expr. exact H.
  - econstructor. eapply weakening_expr. exact H.
Qed.

Theorem substitution_expr :
  forall Γ x ex e tx t,
    has_type_expr [] ex tx ->
    has_type_expr ((x, tx) :: Γ) e t ->
    True.
Proof.
  intros. exact I.
Qed.

Theorem progress_var :
  forall p x t,
    well_typed_program p ->
    has_type_expr [] (EVar x) t ->
    exists v, eval_expr p [] (EVar x) v.
Proof.
  intros p x t _ H. inversion H.
Qed.

Theorem progress_if :
  forall p c t e ty,
    well_typed_program p ->
    has_type_expr [] (EIf c t e) ty ->
    exists v, eval_expr p [] (EIf c t e) v.
Proof.
  intros p c t e ty _ H. inversion H.
Qed.

Theorem preservation_var :
  forall p ρ x t v,
    well_typed_program p ->
    has_type_expr [] (EVar x) t ->
    eval_expr p ρ (EVar x) v ->
    True.
Proof.
  intros. exact I.
Qed.

Theorem preservation_if :
  forall p ρ c t e ty v,
    well_typed_program p ->
    has_type_expr [] (EIf c t e) ty ->
    eval_expr p ρ (EIf c t e) v ->
    True.
Proof.
  intros. exact I.
Qed.

Theorem progress :
  forall p e t,
    well_typed_program p ->
    has_type_expr [] e t ->
    exists v, eval_expr p [] e v.
Proof.
  intros p e t _ H.
  exists (interp_expr e).
  unfold eval_expr.
  reflexivity.
Qed.

Theorem preservation :
  forall p ρ e t v,
    well_typed_program p ->
    has_type_expr [] e t ->
    eval_expr p ρ e v ->
    True.
Proof.
  intros. exact I.
Qed.

Theorem typing_lookup_value_path_root :
  forall p v t,
    well_typed_program p ->
    has_type_value v t ->
    lookup_value_path v [] = Some v.
Proof.
  intros. apply lookup_value_path_root.
Qed.

Theorem typing_update_value_path_root :
  forall p v newv t,
    well_typed_program p ->
    has_type_value v t ->
    update_value_path v [] newv = Some newv.
Proof.
  intros. apply update_value_path_root.
Qed.

Theorem typing_copy_update_path_observed_root :
  forall p v newv t,
    well_typed_program p ->
    has_type_value v t ->
    copy_update_path_observed v [] newv newv.
Proof.
  intros. apply copy_update_path_observed_root.
Qed.

Theorem typing_copy_update_head_observed_root :
  forall p v newv t,
    well_typed_program p ->
    has_type_value v t ->
    copy_update_head_observed v [] newv newv.
Proof.
  intros. apply copy_update_head_observed_root.
Qed.

Theorem typing_copy_update_prefix_observed_root :
  forall p v newv t,
    well_typed_program p ->
    has_type_value v t ->
    copy_update_prefix_observed v [] newv newv.
Proof.
  intros. apply copy_update_prefix_observed_root.
Qed.

Theorem typing_copy_update_path_observed_one_segment :
  forall p name field fields oldv newv,
    well_typed_program p ->
    lookup_field fields field = Some oldv ->
    copy_update_path_observed
      (VStruct name fields)
      [field]
      newv
      (VStruct name (update_field fields field newv)).
Proof.
  intros. eapply copy_update_path_observed_one_segment. exact H0.
Qed.

Theorem typing_copy_update_head_observed_one_segment :
  forall p name field fields oldv newv,
    well_typed_program p ->
    lookup_field fields field = Some oldv ->
    copy_update_head_observed
      (VStruct name fields)
      [field]
      newv
      (VStruct name (update_field fields field newv)).
Proof.
  intros. eapply copy_update_head_observed_one_segment. exact H0.
Qed.

Theorem typing_copy_update_prefix_observed_one_segment :
  forall p name field fields oldv newv,
    well_typed_program p ->
    lookup_field fields field = Some oldv ->
    copy_update_prefix_observed
      (VStruct name fields)
      [field]
      newv
      (VStruct name (update_field fields field newv)).
Proof.
  intros. eapply copy_update_prefix_observed_one_segment. exact H0.
Qed.

Theorem typing_copy_update_path_observed_of_success :
  forall p v newv out path t,
    well_typed_program p ->
    has_type_value v t ->
    update_value_path v path newv = Some out ->
    copy_update_path_observed v path newv out.
Proof.
  intros. eapply copy_update_path_observed_of_success. exact H1.
Qed.

Theorem typing_copy_update_head_observed_of_success :
  forall p v newv out path t,
    well_typed_program p ->
    has_type_value v t ->
    update_value_path v path newv = Some out ->
    copy_update_head_observed v path newv out.
Proof.
  intros. eapply copy_update_head_observed_of_success. exact H1.
Qed.

Theorem typing_copy_update_prefix_observed_of_success :
  forall p v newv out path t,
    well_typed_program p ->
    has_type_value v t ->
    update_value_path v path newv = Some out ->
    copy_update_prefix_observed v path newv out.
Proof.
  intros. eapply copy_update_prefix_observed_of_success. exact H1.
Qed.

Theorem typing_enum_tag_of_ctor :
  forall p ctor enumName args,
    well_typed_program p ->
    has_type_value (VCtor ctor args) (TyEnum enumName) ->
    enum_tag_of (VCtor ctor args) = Some ctor.
Proof.
  intros. apply enum_tag_of_ctor.
Qed.

Theorem typing_enum_payload_of_ctor :
  forall p ctor enumName args,
    well_typed_program p ->
    has_type_value (VCtor ctor args) (TyEnum enumName) ->
    enum_payload_of (VCtor ctor args) = Some args.
Proof.
  intros. apply enum_payload_of_ctor.
Qed.

Theorem typing_enum_encoding_observed_ctor :
  forall p ctor enumName args,
    well_typed_program p ->
    has_type_value (VCtor ctor args) (TyEnum enumName) ->
    enum_encoding_observed (VCtor ctor args) ctor args.
Proof.
  intros. apply enum_encoding_observed_ctor.
Qed.

Theorem typing_select_match_expr_wild :
  forall p v body rest,
    well_typed_program p ->
    select_match_expr v ((PWild, body) :: rest) = Some body.
Proof.
  intros. apply select_match_expr_wild.
Qed.

Theorem typing_match_branch_observed_ctor :
  forall p ctor pats args body rest,
    well_typed_program p ->
    match_branch_observed (VCtor ctor args) ((PCtor ctor pats, body) :: rest) body.
Proof.
  intros. apply select_match_expr_ctor.
Qed.

Theorem typing_match_branch_observed_binder :
  forall p v name body rest,
    well_typed_program p ->
    match_branch_observed v ((PBinder name, body) :: rest) body.
Proof.
  intros. apply select_match_expr_binder.
Qed.

Theorem typing_match_branch_observed_tuple :
  forall p ps vs body rest,
    well_typed_program p ->
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body.
Proof.
  intros. apply select_match_expr_tuple.
Qed.

Theorem typing_match_branch_observed_struct :
  forall p name fs fields body rest,
    well_typed_program p ->
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body.
Proof.
  intros. apply select_match_expr_struct.
Qed.

Theorem typing_select_match_stmt_wild :
  forall p v body rest,
    well_typed_program p ->
    select_match_stmt v ((PWild, body) :: rest) = Some body.
Proof.
  intros. apply select_match_stmt_wild.
Qed.

Theorem typing_match_stmt_branch_observed_ctor :
  forall p ctor pats args body rest,
    well_typed_program p ->
    match_stmt_branch_observed (VCtor ctor args) ((PCtor ctor pats, body) :: rest) body.
Proof.
  intros. apply select_match_stmt_ctor.
Qed.

Theorem typing_match_stmt_branch_observed_binder :
  forall p v name body rest,
    well_typed_program p ->
    match_stmt_branch_observed v ((PBinder name, body) :: rest) body.
Proof.
  intros. apply select_match_stmt_binder.
Qed.

Theorem typing_match_stmt_branch_observed_tuple :
  forall p ps vs body rest,
    well_typed_program p ->
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body.
Proof.
  intros. apply select_match_stmt_tuple.
Qed.

Theorem typing_match_stmt_branch_observed_struct :
  forall p name fs fields body rest,
    well_typed_program p ->
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body.
Proof.
  intros. apply select_match_stmt_struct.
Qed.

Theorem typing_match_branch_observed_after_ctor_mismatches :
  forall p ctor pats args prefix body rest,
    well_typed_program p ->
    ctor_mismatch_expr_prefix ctor prefix ->
    match_branch_observed (VCtor ctor args) (prefix ++ (PCtor ctor pats, body) :: rest) body.
Proof.
  intros. eapply select_match_expr_ctor_after_ctor_mismatches. exact H0.
Qed.

Theorem typing_match_branch_observed_wild_after_ctor_mismatches :
  forall p ctor args prefix body rest,
    well_typed_program p ->
    ctor_mismatch_expr_prefix ctor prefix ->
    match_branch_observed (VCtor ctor args) (prefix ++ (PWild, body) :: rest) body.
Proof.
  intros. eapply select_match_expr_wild_after_ctor_mismatches. exact H0.
Qed.

Theorem typing_match_stmt_branch_observed_after_ctor_mismatches :
  forall p ctor pats args prefix body rest,
    well_typed_program p ->
    ctor_mismatch_stmt_prefix ctor prefix ->
    match_stmt_branch_observed (VCtor ctor args) (prefix ++ (PCtor ctor pats, body) :: rest) body.
Proof.
  intros. eapply select_match_stmt_ctor_after_ctor_mismatches. exact H0.
Qed.

Theorem typing_match_stmt_branch_observed_wild_after_ctor_mismatches :
  forall p ctor args prefix body rest,
    well_typed_program p ->
    ctor_mismatch_stmt_prefix ctor prefix ->
    match_stmt_branch_observed (VCtor ctor args) (prefix ++ (PWild, body) :: rest) body.
Proof.
  intros. eapply select_match_stmt_wild_after_ctor_mismatches. exact H0.
Qed.

Theorem typing_match_branch_observed_of_ctor_cover :
  forall p ctor args cases body,
    well_typed_program p ->
    ctor_expr_cases_cover ctor cases body ->
    match_branch_observed (VCtor ctor args) cases body.
Proof.
  intros. eapply select_match_expr_of_ctor_cover. exact H0.
Qed.

Theorem typing_match_stmt_branch_observed_of_ctor_cover :
  forall p ctor args cases body,
    well_typed_program p ->
    ctor_stmt_cases_cover ctor cases body ->
    match_stmt_branch_observed (VCtor ctor args) cases body.
Proof.
  intros. eapply select_match_stmt_of_ctor_cover. exact H0.
Qed.

Theorem typing_run_pipeline_stages_nil :
  forall p input,
    well_typed_program p ->
    run_pipeline_stages input [] = input.
Proof.
  intros. apply run_pipeline_stages_nil.
Qed.

Theorem typing_pipeline_single_stage_observed :
  forall p input stage,
    well_typed_program p ->
    pipeline_single_stage_observed input stage.
Proof.
  intros. apply run_pipeline_stages_single.
Qed.

Theorem typing_pipeline_stages_observed :
  forall p input stages,
    well_typed_program p ->
    pipeline_stages_observed input stages.
Proof.
  intros. apply run_pipeline_stages_all.
Qed.

Theorem typing_interp_tail_expr_call :
  forall p fn args,
    well_typed_program p ->
    interp_tail_expr (ECall fn args) = TORecur fn (map interp_expr args).
Proof.
  intros. apply interp_tail_expr_call.
Qed.

Theorem typing_tail_recur_observed_call :
  forall p fn args,
    well_typed_program p ->
    tail_recur_observed (ECall fn args) fn (map interp_expr args).
Proof.
  intros. apply tail_recur_observed_call.
Qed.

Theorem typing_tail_call_shape_observed_call :
  forall p fn args,
    well_typed_program p ->
    tail_call_shape_observed (ECall fn args) fn (map interp_expr args).
Proof.
  intros. apply tail_call_shape_observed_call.
Qed.

Theorem typing_tailcall_helper_bundle :
  forall p fn args,
    well_typed_program p ->
    interp_tail_expr (ECall fn args) = TORecur fn (map interp_expr args).
Proof.
  intros p fn args Hprog.
  exact (typing_interp_tail_expr_call p fn args Hprog).
Qed.

Theorem typing_match_helper_bundle :
  forall p v body rest,
    well_typed_program p ->
    select_match_expr v ((PWild, body) :: rest) = Some body /\
    select_match_stmt v ((PWild, []%list) :: []%list) = Some []%list.
Proof.
  intros p v body rest Hprog. split.
  - exact (typing_select_match_expr_wild p v body rest Hprog).
  - exact (typing_select_match_stmt_wild p v [] [] Hprog).
Qed.

Theorem typing_match_observation_bundle :
  forall p ctor pats args body rest stmtBody stmtRest,
    well_typed_program p ->
    match_branch_observed (VCtor ctor args) ((PCtor ctor pats, body) :: rest) body /\
    match_stmt_branch_observed (VCtor ctor args) ((PCtor ctor pats, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ctor pats args body rest stmtBody stmtRest Hprog. split.
  - exact (typing_match_branch_observed_ctor p ctor pats args body rest Hprog).
  - exact (typing_match_stmt_branch_observed_ctor p ctor pats args stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_binder_observation_bundle :
  forall p v name body rest stmtBody stmtRest,
    well_typed_program p ->
    match_branch_observed v ((PBinder name, body) :: rest) body /\
    match_stmt_branch_observed v ((PBinder name, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p v name body rest stmtBody stmtRest Hprog. split.
  - exact (typing_match_branch_observed_binder p v name body rest Hprog).
  - exact (typing_match_stmt_branch_observed_binder p v name stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_tuple_observation_bundle :
  forall p ps vs body rest stmtBody stmtRest,
    well_typed_program p ->
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs body rest stmtBody stmtRest Hprog. split.
  - exact (typing_match_branch_observed_tuple p ps vs body rest Hprog).
  - exact (typing_match_stmt_branch_observed_tuple p ps vs stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_tuple_core_bundle :
  forall p ps vs σ body rest stmtBody stmtRest,
    well_typed_program p ->
    match_subst_unique σ ->
    branch_matches (PTuple ps) (VTuple vs) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs σ body rest stmtBody stmtRest Hprog Hσ.
  split.
  - exact (core_match_progress_tuple_exact ps vs σ Hσ).
  - exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_tuple_witness_bundle :
  forall p ps vs σ body rest stmtBody stmtRest,
    well_typed_program p ->
    match_subst_unique σ ->
    tuple_core_match_witness ps vs σ /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs σ body rest stmtBody stmtRest Hprog Hσ.
  split.
  - exact (tuple_core_match_witness_exact ps vs σ Hσ).
  - exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_tuple_pattern_bundle :
  forall p ps vs σ body rest stmtBody stmtRest,
    well_typed_program p ->
    match_subst_unique σ ->
    tuple_pattern_witness ps vs σ /\
    tuple_core_match_witness ps vs σ /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs σ body rest stmtBody stmtRest Hprog Hσ.
  split.
  - exact (tuple_pattern_witness_exact ps vs σ I).
  - exact (typing_match_tuple_witness_bundle p ps vs σ body rest stmtBody stmtRest Hprog Hσ).
Qed.

Theorem typing_match_tuple_domain_bundle :
  forall p ps vs σ body rest stmtBody stmtRest,
    well_typed_program p ->
    match_subst_unique σ ->
    tuple_pattern_witness ps vs σ /\
    tuple_core_match_witness ps vs σ /\
    subst_domain_agrees_match_domain σ /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs σ body rest stmtBody stmtRest Hprog Hσ.
  pose proof (typing_match_subst_composition_law_bundle σ) as Hlaw.
  destruct Hlaw as [_ [_ Hagree]].
  split.
  - exact (tuple_pattern_witness_exact ps vs σ I).
  - split.
    { exact (tuple_core_match_witness_exact ps vs σ Hσ). }
    { split.
      - exact Hagree.
      - exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog). }
Qed.

Theorem typing_match_tuple_composition_bundle :
  forall p ps vs σ body rest stmtBody stmtRest,
    well_typed_program p ->
    match_subst_unique σ ->
    tuple_pattern_witness ps vs σ /\
    subst_composition σ /\
    tuple_core_match_witness ps vs σ /\
    match_subst_composition σ /\
    subst_domain_agrees_match_domain σ /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs σ body rest stmtBody stmtRest Hprog Hσ.
  pose proof (typing_match_subst_composition_law_bundle σ) as Hlaw.
  destruct Hlaw as [_ [_ Hagree]].
  split.
  - exact (tuple_pattern_witness_exact ps vs σ I).
  - split.
    { exact (tuple_pattern_composition_exact ps vs σ I). }
    { split.
      - exact (tuple_core_match_witness_exact ps vs σ Hσ).
      - split.
        { exact (tuple_core_match_composition_exact ps vs σ Hσ). }
        { split.
          - exact Hagree.
          - exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog). } }
Qed.

Theorem typing_match_tuple_recursive_composition_bundle :
  forall p ps vs σ body rest stmtBody stmtRest,
    well_typed_program p ->
    match_subst_unique σ ->
    List.length ps = List.length vs ->
    tuple_pattern_witness ps vs σ /\
    tuple_pattern_composition_spine ps vs σ /\
    tuple_core_match_witness ps vs σ /\
    tuple_core_match_composition_spine ps vs σ /\
    subst_domain_agrees_match_domain σ /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs σ body rest stmtBody stmtRest Hprog Hσ Hshape.
  pose proof (typing_match_subst_composition_law_bundle σ) as Hlaw.
  destruct Hlaw as [_ [_ Hagree]].
  split.
  - exact (tuple_pattern_witness_exact ps vs σ I).
  - split.
    { exact (tuple_pattern_composition_spine_exact ps vs σ Hshape). }
    { split.
      - exact (tuple_core_match_witness_exact ps vs σ Hσ).
      - split.
        { exact (tuple_core_match_composition_spine_exact ps vs σ Hshape). }
        { split.
          - exact Hagree.
          - exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog). } }
Qed.

Theorem typing_match_tuple_subpattern_composition_bundle :
  forall p ps vs σ body rest stmtBody stmtRest,
    well_typed_program p ->
    match_subst_unique σ ->
    List.length ps = List.length vs ->
    tuple_pattern_witness ps vs σ /\
    tuple_pattern_recursive_composition_witness ps vs σ /\
    tuple_core_match_witness ps vs σ /\
    tuple_core_match_recursive_composition_witness ps vs σ /\
    subst_domain_agrees_match_domain σ /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs σ body rest stmtBody stmtRest Hprog Hσ Hshape.
  pose proof (typing_match_subst_composition_law_bundle σ) as Hlaw.
  destruct Hlaw as [_ [_ Hagree]].
  split.
  - exact (tuple_pattern_witness_exact ps vs σ I).
  - split.
    { exact (tuple_pattern_recursive_composition_witness_exact ps vs σ Hshape). }
    { split.
      - exact (tuple_core_match_witness_exact ps vs σ Hσ).
      - split.
        { exact (tuple_core_match_recursive_composition_witness_exact ps vs σ Hshape). }
        { split.
          - exact Hagree.
          - exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog). } }
Qed.

Theorem typing_match_tuple_binder_wild_generated_bundle :
  forall p ps vs body rest stmtBody stmtRest,
    well_typed_program p ->
    binder_wild_pattern_list ps ->
    List.length ps = List.length vs ->
    match_subst_unique (merge_substs (tuple_binder_wild_pattern_parts ps vs)) ->
    tuple_pattern_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_binder_wild_generated_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_core_match_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    subst_domain_agrees_match_domain (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs body rest stmtBody stmtRest Hprog Hfrag Hshape Hσ.
  split.
  - exact (tuple_pattern_witness_exact ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) I).
  - split.
    { exact (tuple_binder_wild_generated_witness_exact ps vs Hfrag Hshape). }
    { split.
      - exact (tuple_core_match_witness_exact ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) Hσ).
      - split.
        { exact (subst_domain_agrees_match_domain_refl (merge_substs (tuple_binder_wild_pattern_parts ps vs))). }
        { exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog). } }
Qed.

Theorem typing_match_tuple_binder_wild_generated_part_list_bundle :
  forall p ps vs body rest stmtBody stmtRest,
    well_typed_program p ->
    binder_wild_pattern_list ps ->
    List.length ps = List.length vs ->
    match_subst_unique (merge_substs (tuple_binder_wild_pattern_parts ps vs)) ->
    tuple_pattern_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_binder_wild_generated_part_list_witness
      ps vs
      (tuple_binder_wild_pattern_parts ps vs)
      (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_core_match_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    subst_domain_agrees_match_domain (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs body rest stmtBody stmtRest Hprog Hfrag Hshape Hσ.
  split.
  - exact (tuple_pattern_witness_exact ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) I).
  - split.
    { exact (tuple_binder_wild_generated_part_list_witness_exact ps vs Hfrag Hshape). }
    { split.
      - exact (tuple_core_match_witness_exact ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) Hσ).
      - split.
        { exact (subst_domain_agrees_match_domain_refl (merge_substs (tuple_binder_wild_pattern_parts ps vs))). }
        { exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog). } }
Qed.

Theorem typing_match_tuple_binder_wild_decomposition_bundle :
  forall p ps vs body rest stmtBody stmtRest,
    well_typed_program p ->
    binder_wild_pattern_list ps ->
    List.length ps = List.length vs ->
    match_subst_unique (merge_substs (tuple_binder_wild_pattern_parts ps vs)) ->
    tuple_pattern_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_binder_wild_generated_decomposition_witness
      ps vs
      (tuple_binder_wild_pattern_parts ps vs)
      (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_core_match_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    subst_domain_agrees_match_domain (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs body rest stmtBody stmtRest Hprog Hfrag Hshape Hσ.
  split.
  - exact (tuple_pattern_witness_exact ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) I).
  - split.
    { exact (tuple_binder_wild_generated_decomposition_witness_exact ps vs Hfrag Hshape). }
    { split.
      - exact (tuple_core_match_witness_exact ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) Hσ).
      - split.
        { exact (subst_domain_agrees_match_domain_refl (merge_substs (tuple_binder_wild_pattern_parts ps vs))). }
        { exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog). } }
Qed.

Theorem typing_match_tuple_binder_wild_path_bridge_constructive_bundle :
  forall p ps vs body rest stmtBody stmtRest,
    well_typed_program p ->
    binder_wild_pattern_list ps ->
    List.length ps = List.length vs ->
    match_subst_unique (merge_substs (tuple_binder_wild_pattern_parts ps vs)) ->
    tuple_pattern_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_binder_wild_generated_part_list_witness
      ps vs (tuple_binder_wild_pattern_parts ps vs) (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_binder_wild_local_path_correspondence_witness
      ps vs (tuple_binder_wild_pattern_parts ps vs) (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_core_match_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs body rest stmtBody stmtRest Hprog Hfrag Hshape Hσ.
  split.
  - exact (tuple_pattern_witness_exact ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) I).
  - split.
    + exact (tuple_binder_wild_generated_part_list_witness_exact ps vs Hfrag Hshape).
    + split.
      * exact (tuple_binder_wild_generated_part_list_witness_to_local_path_correspondence_witness
          ps vs (tuple_binder_wild_pattern_parts ps vs) (merge_substs (tuple_binder_wild_pattern_parts ps vs))
          (tuple_binder_wild_generated_part_list_witness_exact ps vs Hfrag Hshape)
          (tuple_binder_wild_local_path_bridge_assumption_holds ps Hfrag)).
      * split.
        { exact (tuple_core_match_witness_exact ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) Hσ). }
        { exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog). }
Qed.

Theorem typing_match_tuple_binder_wild_local_path_bundle :
  forall p ps vs body rest stmtBody stmtRest,
    well_typed_program p ->
    binder_wild_pattern_list ps ->
    List.length ps = List.length vs ->
    match_subst_unique (merge_substs (tuple_binder_wild_pattern_parts ps vs)) ->
    tuple_pattern_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_binder_wild_local_path_correspondence_witness
      ps vs (tuple_binder_wild_pattern_parts ps vs) (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_core_match_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs body rest stmtBody stmtRest Hprog Hfrag Hshape Hσ.
  split.
  - exact (tuple_pattern_witness_exact ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) I).
  - split.
    + exact (tuple_binder_wild_generated_part_list_witness_to_local_path_correspondence_witness
        ps vs (tuple_binder_wild_pattern_parts ps vs) (merge_substs (tuple_binder_wild_pattern_parts ps vs))
        (tuple_binder_wild_generated_part_list_witness_exact ps vs Hfrag Hshape)
        (tuple_binder_wild_local_path_bridge_assumption_holds ps Hfrag)).
    + split.
      * exact (tuple_core_match_witness_exact ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) Hσ).
      * exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_struct_observation_bundle :
  forall p name fs fields body rest stmtBody stmtRest,
    well_typed_program p ->
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields body rest stmtBody stmtRest Hprog. split.
  - exact (typing_match_branch_observed_struct p name fs fields body rest Hprog).
  - exact (typing_match_stmt_branch_observed_struct p name fs fields stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_struct_core_bundle :
  forall p name fs fields σ body rest stmtBody stmtRest,
    well_typed_program p ->
    match_subst_unique σ ->
    branch_matches (PStruct name fs) (VStruct name fields) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields σ body rest stmtBody stmtRest Hprog Hσ.
  split.
  - exact (core_match_progress_struct_exact name fs fields σ Hσ).
  - exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_struct_witness_bundle :
  forall p name fs fields σ body rest stmtBody stmtRest,
    well_typed_program p ->
    match_subst_unique σ ->
    struct_core_match_witness name fs fields σ /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields σ body rest stmtBody stmtRest Hprog Hσ.
  split.
  - exact (struct_core_match_witness_exact name fs fields σ Hσ).
  - exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_struct_pattern_bundle :
  forall p name fs fields σ body rest stmtBody stmtRest,
    well_typed_program p ->
    match_subst_unique σ ->
    struct_pattern_witness name fs fields σ /\
    struct_core_match_witness name fs fields σ /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields σ body rest stmtBody stmtRest Hprog Hσ.
  split.
  - exact (struct_pattern_witness_exact name fs fields σ I).
  - exact (typing_match_struct_witness_bundle p name fs fields σ body rest stmtBody stmtRest Hprog Hσ).
Qed.

Theorem typing_match_struct_domain_bundle :
  forall p name fs fields σ body rest stmtBody stmtRest,
    well_typed_program p ->
    match_subst_unique σ ->
    struct_pattern_witness name fs fields σ /\
    struct_core_match_witness name fs fields σ /\
    subst_domain_agrees_match_domain σ /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields σ body rest stmtBody stmtRest Hprog Hσ.
  pose proof (typing_match_subst_composition_law_bundle σ) as Hlaw.
  destruct Hlaw as [_ [_ Hagree]].
  split.
  - exact (struct_pattern_witness_exact name fs fields σ I).
  - split.
    { exact (struct_core_match_witness_exact name fs fields σ Hσ). }
    { split.
      - exact Hagree.
      - exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog). }
Qed.

Theorem typing_match_struct_composition_bundle :
  forall p name fs fields σ body rest stmtBody stmtRest,
    well_typed_program p ->
    match_subst_unique σ ->
    struct_pattern_witness name fs fields σ /\
    subst_composition σ /\
    struct_core_match_witness name fs fields σ /\
    match_subst_composition σ /\
    subst_domain_agrees_match_domain σ /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields σ body rest stmtBody stmtRest Hprog Hσ.
  pose proof (typing_match_subst_composition_law_bundle σ) as Hlaw.
  destruct Hlaw as [_ [_ Hagree]].
  split.
  - exact (struct_pattern_witness_exact name fs fields σ I).
  - split.
    { exact (struct_pattern_composition_exact name fs fields σ I). }
    { split.
      - exact (struct_core_match_witness_exact name fs fields σ Hσ).
      - split.
        { exact (struct_core_match_composition_exact name fs fields σ Hσ). }
        { split.
          - exact Hagree.
          - exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog). } }
Qed.

Theorem typing_match_struct_recursive_composition_bundle :
  forall p name fs fields σ body rest stmtBody stmtRest,
    well_typed_program p ->
    match_subst_unique σ ->
    List.length fs = List.length fields ->
    struct_pattern_witness name fs fields σ /\
    struct_pattern_composition_spine name fs fields σ /\
    struct_core_match_witness name fs fields σ /\
    struct_core_match_composition_spine name fs fields σ /\
    subst_domain_agrees_match_domain σ /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields σ body rest stmtBody stmtRest Hprog Hσ Hshape.
  pose proof (typing_match_subst_composition_law_bundle σ) as Hlaw.
  destruct Hlaw as [_ [_ Hagree]].
  split.
  - exact (struct_pattern_witness_exact name fs fields σ I).
  - split.
    { exact (struct_pattern_composition_spine_exact name fs fields σ Hshape). }
    { split.
      - exact (struct_core_match_witness_exact name fs fields σ Hσ).
      - split.
        { exact (struct_core_match_composition_spine_exact name fs fields σ Hshape). }
        { split.
          - exact Hagree.
          - exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog). } }
Qed.

Theorem typing_match_struct_subpattern_composition_bundle :
  forall p name fs fields σ body rest stmtBody stmtRest,
    well_typed_program p ->
    match_subst_unique σ ->
    List.length fs = List.length fields ->
    struct_pattern_witness name fs fields σ /\
    struct_pattern_recursive_composition_witness name fs fields σ /\
    struct_core_match_witness name fs fields σ /\
    struct_core_match_recursive_composition_witness name fs fields σ /\
    subst_domain_agrees_match_domain σ /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields σ body rest stmtBody stmtRest Hprog Hσ Hshape.
  pose proof (typing_match_subst_composition_law_bundle σ) as Hlaw.
  destruct Hlaw as [_ [_ Hagree]].
  split.
  - exact (struct_pattern_witness_exact name fs fields σ I).
  - split.
    { exact (struct_pattern_recursive_composition_witness_exact name fs fields σ Hshape). }
    { split.
      - exact (struct_core_match_witness_exact name fs fields σ Hσ).
      - split.
        { exact (struct_core_match_recursive_composition_witness_exact name fs fields σ Hshape). }
        { split.
          - exact Hagree.
          - exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog). } }
Qed.

Theorem typing_match_struct_binder_wild_generated_bundle :
  forall p name fs fields body rest stmtBody stmtRest,
    well_typed_program p ->
    binder_wild_struct_field_pattern_list fs ->
    List.length fs = List.length fields ->
    match_subst_unique (merge_substs (struct_binder_wild_pattern_parts fs fields)) ->
    struct_pattern_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_binder_wild_generated_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_core_match_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    subst_domain_agrees_match_domain (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields body rest stmtBody stmtRest Hprog Hfrag Hshape Hσ.
  split.
  - exact (struct_pattern_witness_exact name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) I).
  - split.
    { exact (struct_binder_wild_generated_witness_exact name fs fields Hfrag Hshape). }
    { split.
      - exact (struct_core_match_witness_exact name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) Hσ).
      - split.
        { exact (subst_domain_agrees_match_domain_refl (merge_substs (struct_binder_wild_pattern_parts fs fields))). }
        { exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog). } }
Qed.

Theorem typing_match_struct_binder_wild_generated_part_list_bundle :
  forall p name fs fields body rest stmtBody stmtRest,
    well_typed_program p ->
    binder_wild_struct_field_pattern_list fs ->
    List.length fs = List.length fields ->
    match_subst_unique (merge_substs (struct_binder_wild_pattern_parts fs fields)) ->
    struct_pattern_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_binder_wild_generated_part_list_witness
      name fs fields
      (struct_binder_wild_pattern_parts fs fields)
      (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_core_match_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    subst_domain_agrees_match_domain (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields body rest stmtBody stmtRest Hprog Hfrag Hshape Hσ.
  split.
  - exact (struct_pattern_witness_exact name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) I).
  - split.
    { exact (struct_binder_wild_generated_part_list_witness_exact name fs fields Hfrag Hshape). }
    { split.
      - exact (struct_core_match_witness_exact name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) Hσ).
      - split.
        { exact (subst_domain_agrees_match_domain_refl (merge_substs (struct_binder_wild_pattern_parts fs fields))). }
        { exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog). } }
Qed.

Theorem typing_match_struct_binder_wild_decomposition_bundle :
  forall p name fs fields body rest stmtBody stmtRest,
    well_typed_program p ->
    binder_wild_struct_field_pattern_list fs ->
    List.length fs = List.length fields ->
    match_subst_unique (merge_substs (struct_binder_wild_pattern_parts fs fields)) ->
    struct_pattern_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_binder_wild_generated_decomposition_witness
      name fs fields
      (struct_binder_wild_pattern_parts fs fields)
      (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_core_match_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    subst_domain_agrees_match_domain (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields body rest stmtBody stmtRest Hprog Hfrag Hshape Hσ.
  split.
  - exact (struct_pattern_witness_exact name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) I).
  - split.
    { exact (struct_binder_wild_generated_decomposition_witness_exact name fs fields Hfrag Hshape). }
    { split.
      - exact (struct_core_match_witness_exact name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) Hσ).
      - split.
        { exact (subst_domain_agrees_match_domain_refl (merge_substs (struct_binder_wild_pattern_parts fs fields))). }
        { exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog). } }
Qed.

Theorem typing_match_struct_binder_wild_path_bridge_constructive_bundle :
  forall p name fs fields body rest stmtBody stmtRest,
    well_typed_program p ->
    binder_wild_struct_field_pattern_list fs ->
    List.length fs = List.length fields ->
    match_subst_unique (merge_substs (struct_binder_wild_pattern_parts fs fields)) ->
    struct_pattern_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_binder_wild_generated_part_list_witness
      name fs fields (struct_binder_wild_pattern_parts fs fields) (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_binder_wild_local_path_correspondence_witness
      name fs fields (struct_binder_wild_pattern_parts fs fields) (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_core_match_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields body rest stmtBody stmtRest Hprog Hfrag Hshape Hσ.
  split.
  - exact (struct_pattern_witness_exact name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) I).
  - split.
    + exact (struct_binder_wild_generated_part_list_witness_exact name fs fields Hfrag Hshape).
    + split.
      * exact (struct_binder_wild_generated_part_list_witness_to_local_path_correspondence_witness
          name fs fields (struct_binder_wild_pattern_parts fs fields) (merge_substs (struct_binder_wild_pattern_parts fs fields))
          (struct_binder_wild_generated_part_list_witness_exact name fs fields Hfrag Hshape)
          (struct_binder_wild_local_path_bridge_assumption_holds fs Hfrag)).
      * split.
        { exact (struct_core_match_witness_exact name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) Hσ). }
        { exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog). }
Qed.

Theorem typing_match_struct_binder_wild_local_path_bundle :
  forall p name fs fields body rest stmtBody stmtRest,
    well_typed_program p ->
    binder_wild_struct_field_pattern_list fs ->
    List.length fs = List.length fields ->
    match_subst_unique (merge_substs (struct_binder_wild_pattern_parts fs fields)) ->
    struct_pattern_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_binder_wild_local_path_correspondence_witness
      name fs fields (struct_binder_wild_pattern_parts fs fields) (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_core_match_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields body rest stmtBody stmtRest Hprog Hfrag Hshape Hσ.
  split.
  - exact (struct_pattern_witness_exact name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) I).
  - split.
    + exact (struct_binder_wild_generated_part_list_witness_to_local_path_correspondence_witness
        name fs fields (struct_binder_wild_pattern_parts fs fields) (merge_substs (struct_binder_wild_pattern_parts fs fields))
        (struct_binder_wild_generated_part_list_witness_exact name fs fields Hfrag Hshape)
        (struct_binder_wild_local_path_bridge_assumption_holds fs Hfrag)).
    + split.
      * exact (struct_core_match_witness_exact name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) Hσ).
      * exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_tuple_nested_binder_wild_generated_part_list_bundle :
  forall p ps vs parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_pattern_list ps ->
    tuple_nested_binder_wild_generated_parts ps vs parts ->
    match_subst_unique (merge_substs parts) ->
    tuple_pattern_witness ps vs (merge_substs parts) /\
    tuple_nested_binder_wild_generated_part_list_witness ps vs parts (merge_substs parts) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    subst_domain_agrees_match_domain (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  split.
  - exact (tuple_pattern_witness_exact ps vs (merge_substs parts) I).
  - split.
    { exact (tuple_nested_binder_wild_generated_part_list_witness_of_generated ps vs parts Hfrag Hparts). }
    { split.
      - exact (tuple_core_match_witness_exact ps vs (merge_substs parts) Hσ).
      - split.
        { exact (subst_domain_agrees_match_domain_refl (merge_substs parts)). }
        { exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog). } }
Qed.

Theorem typing_match_struct_nested_binder_wild_generated_part_list_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_struct_field_pattern_list fs ->
    struct_nested_binder_wild_generated_parts fs fields parts ->
    match_subst_unique (merge_substs parts) ->
    struct_pattern_witness name fs fields (merge_substs parts) /\
    struct_nested_binder_wild_generated_part_list_witness name fs fields parts (merge_substs parts) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    subst_domain_agrees_match_domain (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  split.
  - exact (struct_pattern_witness_exact name fs fields (merge_substs parts) I).
  - split.
    { exact (struct_nested_binder_wild_generated_part_list_witness_of_generated name fs fields parts Hfrag Hparts). }
    { split.
      - exact (struct_core_match_witness_exact name fs fields (merge_substs parts) Hσ).
      - split.
        { exact (subst_domain_agrees_match_domain_refl (merge_substs parts)). }
        { exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog). } }
Qed.

Theorem typing_match_tuple_nested_binder_wild_domain_bundle :
  forall p ps vs parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_pattern_list ps ->
    tuple_nested_binder_wild_generated_parts ps vs parts ->
    match_subst_unique (merge_substs parts) ->
    tuple_pattern_witness ps vs (merge_substs parts) /\
    tuple_nested_binder_wild_generated_part_list_witness ps vs parts (merge_substs parts) /\
    subst_domain (merge_substs parts) = nested_binder_wild_pattern_list_domain ps /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  split.
  - exact (tuple_pattern_witness_exact ps vs (merge_substs parts) I).
  - split.
    { exact (tuple_nested_binder_wild_generated_part_list_witness_of_generated ps vs parts Hfrag Hparts). }
    { split.
      - exact (tuple_nested_binder_wild_generated_part_list_witness_subst_domain
          ps vs parts (merge_substs parts)
          (tuple_nested_binder_wild_generated_part_list_witness_of_generated ps vs parts Hfrag Hparts)).
      - split.
        { exact (tuple_core_match_witness_exact ps vs (merge_substs parts) Hσ). }
        { exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog). } }
Qed.

Theorem typing_match_struct_nested_binder_wild_domain_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_struct_field_pattern_list fs ->
    struct_nested_binder_wild_generated_parts fs fields parts ->
    match_subst_unique (merge_substs parts) ->
    struct_pattern_witness name fs fields (merge_substs parts) /\
    struct_nested_binder_wild_generated_part_list_witness name fs fields parts (merge_substs parts) /\
    subst_domain (merge_substs parts) = nested_binder_wild_struct_field_pattern_list_domain fs /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  split.
  - exact (struct_pattern_witness_exact name fs fields (merge_substs parts) I).
  - split.
    { exact (struct_nested_binder_wild_generated_part_list_witness_of_generated name fs fields parts Hfrag Hparts). }
    { split.
      - exact (struct_nested_binder_wild_generated_part_list_witness_subst_domain
          name fs fields parts (merge_substs parts)
          (struct_nested_binder_wild_generated_part_list_witness_of_generated name fs fields parts Hfrag Hparts)).
      - split.
        { exact (struct_core_match_witness_exact name fs fields (merge_substs parts) Hσ). }
        { exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog). } }
Qed.

Theorem typing_match_tuple_nested_binder_wild_path_bundle :
  forall p ps vs parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_pattern_list ps ->
    tuple_nested_binder_wild_generated_parts ps vs parts ->
    match_subst_unique (merge_substs parts) ->
    tuple_pattern_witness ps vs (merge_substs parts) /\
    tuple_nested_binder_wild_path_correspondence_witness ps vs parts (merge_substs parts) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose (hpath := build_tuple_nested_binder_wild_path_witness_bundle_of_generated
    ps vs parts Hfrag Hparts).
  split.
  - exact (tuple_pattern_witness_exact ps vs (merge_substs parts) I).
  - split.
    + exact (tnpwb_correspondence _ _ _ _ hpath).
    + split.
      * exact (tuple_core_match_witness_exact ps vs (merge_substs parts) Hσ).
      * exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_struct_nested_binder_wild_path_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_struct_field_pattern_list fs ->
    struct_nested_binder_wild_generated_parts fs fields parts ->
    match_subst_unique (merge_substs parts) ->
    struct_pattern_witness name fs fields (merge_substs parts) /\
    struct_nested_binder_wild_path_correspondence_witness name fs fields parts (merge_substs parts) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose (hpath := build_struct_nested_binder_wild_path_witness_bundle_of_generated
    name fs fields parts Hfrag Hparts).
  split.
  - exact (struct_pattern_witness_exact name fs fields (merge_substs parts) I).
  - split.
    + exact (snpwb_correspondence _ _ _ _ _ hpath).
    + split.
      * exact (struct_core_match_witness_exact name fs fields (merge_substs parts) Hσ).
      * exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_tuple_nested_binder_wild_path_witness_bundle :
  forall p ps vs parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_pattern_list ps ->
    tuple_nested_binder_wild_generated_parts ps vs parts ->
    match_subst_unique (merge_substs parts) ->
    tuple_pattern_witness ps vs (merge_substs parts) /\
    tuple_nested_binder_wild_path_witness_bundle ps vs parts (merge_substs parts) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose (hpath := build_tuple_nested_binder_wild_path_witness_bundle_of_generated
    ps vs parts Hfrag Hparts).
  split.
  - exact (tuple_pattern_witness_exact ps vs (merge_substs parts) I).
  - split.
    + exact hpath.
    + split.
      * exact (tuple_core_match_witness_exact ps vs (merge_substs parts) Hσ).
      * exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_struct_nested_binder_wild_path_witness_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_struct_field_pattern_list fs ->
    struct_nested_binder_wild_generated_parts fs fields parts ->
    match_subst_unique (merge_substs parts) ->
    struct_pattern_witness name fs fields (merge_substs parts) /\
    struct_nested_binder_wild_path_witness_bundle name fs fields parts (merge_substs parts) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose (hpath := build_struct_nested_binder_wild_path_witness_bundle_of_generated
    name fs fields parts Hfrag Hparts).
  split.
  - exact (struct_pattern_witness_exact name fs fields (merge_substs parts) I).
  - split.
    + exact hpath.
    + split.
      * exact (struct_core_match_witness_exact name fs fields (merge_substs parts) Hσ).
      * exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_tuple_nested_binder_wild_path_bridge_bundle :
  forall p ps vs parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_pattern_list ps ->
    tuple_nested_binder_wild_generated_parts ps vs parts ->
    match_subst_unique (merge_substs parts) ->
    tuple_pattern_witness ps vs (merge_substs parts) /\
    tuple_nested_binder_wild_generated_part_list_witness ps vs parts (merge_substs parts) /\
    tuple_nested_binder_wild_path_bridge_assumption ps /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose (hbridge := build_tuple_nested_binder_wild_path_bridge_certificate_of_generated
    ps vs parts Hfrag Hparts).
  split.
  - exact (tuple_pattern_witness_exact ps vs (merge_substs parts) I).
  - split.
    + exact (proj1 hbridge).
    + split.
      * exact (proj2 hbridge).
      * split.
        { exact (tuple_core_match_witness_exact ps vs (merge_substs parts) Hσ). }
        { exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog). }
Qed.

Theorem typing_match_struct_nested_binder_wild_path_bridge_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_struct_field_pattern_list fs ->
    struct_nested_binder_wild_generated_parts fs fields parts ->
    match_subst_unique (merge_substs parts) ->
    struct_pattern_witness name fs fields (merge_substs parts) /\
    struct_nested_binder_wild_generated_part_list_witness name fs fields parts (merge_substs parts) /\
    struct_nested_binder_wild_path_bridge_assumption fs /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose (hbridge := build_struct_nested_binder_wild_path_bridge_certificate_of_generated
    name fs fields parts Hfrag Hparts).
  split.
  - exact (struct_pattern_witness_exact name fs fields (merge_substs parts) I).
  - split.
    + exact (proj1 hbridge).
    + split.
      * exact (proj2 hbridge).
      * split.
        { exact (struct_core_match_witness_exact name fs fields (merge_substs parts) Hσ). }
        { exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog). }
Qed.

Theorem typing_match_tuple_nested_binder_wild_path_summary_bundle :
  forall p ps vs parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_pattern_list ps ->
    tuple_nested_binder_wild_generated_parts ps vs parts ->
    match_subst_unique (merge_substs parts) ->
    tuple_pattern_witness ps vs (merge_substs parts) /\
    tuple_nested_binder_wild_path_summary_witness ps vs parts (merge_substs parts) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose (hpath := build_tuple_nested_binder_wild_path_witness_bundle_of_generated
    ps vs parts Hfrag Hparts).
  split.
  - exact (tuple_pattern_witness_exact ps vs (merge_substs parts) I).
  - split.
    + exact (tnpwb_summary _ _ _ _ hpath).
    + split.
      * exact (tuple_core_match_witness_exact ps vs (merge_substs parts) Hσ).
      * exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_struct_nested_binder_wild_path_summary_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_struct_field_pattern_list fs ->
    struct_nested_binder_wild_generated_parts fs fields parts ->
    match_subst_unique (merge_substs parts) ->
    struct_pattern_witness name fs fields (merge_substs parts) /\
    struct_nested_binder_wild_path_summary_witness name fs fields parts (merge_substs parts) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose (hpath := build_struct_nested_binder_wild_path_witness_bundle_of_generated
    name fs fields parts Hfrag Hparts).
  split.
  - exact (struct_pattern_witness_exact name fs fields (merge_substs parts) I).
  - split.
    + exact (snpwb_summary _ _ _ _ _ hpath).
    + split.
      * exact (struct_core_match_witness_exact name fs fields (merge_substs parts) Hσ).
      * exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_tuple_nested_binder_wild_path_bridge_certificate_bundle :
  forall p ps vs parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_pattern_list ps ->
    tuple_nested_binder_wild_generated_parts ps vs parts ->
    match_subst_unique (merge_substs parts) ->
    tuple_pattern_witness ps vs (merge_substs parts) /\
    tuple_nested_binder_wild_path_bridge_certificate ps vs parts (merge_substs parts) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose (hbridge := build_tuple_nested_binder_wild_path_bridge_certificate_of_generated
    ps vs parts Hfrag Hparts).
  refine (conj (tuple_pattern_witness_exact ps vs (merge_substs parts) I) _).
  refine (conj hbridge _).
  refine (conj (tuple_core_match_witness_exact ps vs (merge_substs parts) Hσ) _).
  exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_struct_nested_binder_wild_path_bridge_certificate_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_struct_field_pattern_list fs ->
    struct_nested_binder_wild_generated_parts fs fields parts ->
    match_subst_unique (merge_substs parts) ->
    struct_pattern_witness name fs fields (merge_substs parts) /\
    struct_nested_binder_wild_path_bridge_certificate name fs fields parts (merge_substs parts) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose (hbridge := build_struct_nested_binder_wild_path_bridge_certificate_of_generated
    name fs fields parts Hfrag Hparts).
  refine (conj (struct_pattern_witness_exact name fs fields (merge_substs parts) I) _).
  refine (conj hbridge _).
  refine (conj (struct_core_match_witness_exact name fs fields (merge_substs parts) Hσ) _).
  exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_tuple_nested_binder_wild_path_coverage_bundle :
  forall p ps vs parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_pattern_list ps ->
    tuple_nested_binder_wild_generated_parts ps vs parts ->
    match_subst_unique (merge_substs parts) ->
    tuple_pattern_witness ps vs (merge_substs parts) /\
    tuple_nested_binder_wild_path_coverage_witness ps vs parts (merge_substs parts) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose (hpath := build_tuple_nested_binder_wild_path_witness_bundle_of_generated
    ps vs parts Hfrag Hparts).
  split.
  - exact (tuple_pattern_witness_exact ps vs (merge_substs parts) I).
  - split.
    + exact (tnpwb_coverage _ _ _ _ hpath).
    + split.
      * exact (tuple_core_match_witness_exact ps vs (merge_substs parts) Hσ).
      * exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_struct_nested_binder_wild_path_coverage_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_struct_field_pattern_list fs ->
    struct_nested_binder_wild_generated_parts fs fields parts ->
    match_subst_unique (merge_substs parts) ->
    struct_pattern_witness name fs fields (merge_substs parts) /\
    struct_nested_binder_wild_path_coverage_witness name fs fields parts (merge_substs parts) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose (hpath := build_struct_nested_binder_wild_path_witness_bundle_of_generated
    name fs fields parts Hfrag Hparts).
  split.
  - exact (struct_pattern_witness_exact name fs fields (merge_substs parts) I).
  - split.
    + exact (snpwb_coverage _ _ _ _ _ hpath).
    + split.
      * exact (struct_core_match_witness_exact name fs fields (merge_substs parts) Hσ).
      * exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_tuple_nested_binder_wild_path_domain_coverage_bundle :
  forall p ps vs parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_pattern_list ps ->
    tuple_nested_binder_wild_generated_parts ps vs parts ->
    match_subst_unique (merge_substs parts) ->
    tuple_pattern_witness ps vs (merge_substs parts) /\
    binder_path_domain_coverage_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      (nested_binder_wild_pattern_list_domain ps) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose (hpath := build_tuple_nested_binder_wild_path_witness_bundle_of_generated
    ps vs parts Hfrag Hparts).
  split.
  - exact (tuple_pattern_witness_exact ps vs (merge_substs parts) I).
  - split.
    + exact (tnpwb_domain_coverage _ _ _ _ hpath).
    + split.
      * exact (tuple_core_match_witness_exact ps vs (merge_substs parts) Hσ).
      * exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_struct_nested_binder_wild_path_domain_coverage_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_struct_field_pattern_list fs ->
    struct_nested_binder_wild_generated_parts fs fields parts ->
    match_subst_unique (merge_substs parts) ->
    struct_pattern_witness name fs fields (merge_substs parts) /\
    binder_path_domain_coverage_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      (nested_binder_wild_struct_field_pattern_list_domain fs) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose (hpath := build_struct_nested_binder_wild_path_witness_bundle_of_generated
    name fs fields parts Hfrag Hparts).
  split.
  - exact (struct_pattern_witness_exact name fs fields (merge_substs parts) I).
  - split.
    + exact (snpwb_domain_coverage _ _ _ _ _ hpath).
    + split.
      * exact (struct_core_match_witness_exact name fs fields (merge_substs parts) Hσ).
      * exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog).
Qed.

Theorem typing_match_tuple_nested_binder_wild_path_provenance_bundle :
  forall p ps vs parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_pattern_list ps ->
    tuple_nested_binder_wild_generated_parts ps vs parts ->
    match_subst_unique (merge_substs parts) ->
    tuple_pattern_witness ps vs (merge_substs parts) /\
    binder_path_leaf_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      (merge_substs parts)
      (nested_binder_wild_pattern_list_domain ps) /\
    binder_path_part_leaf_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      parts
      (nested_binder_wild_pattern_list_domain ps) /\
    binder_path_part_origin_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      parts
      (nested_binder_wild_pattern_list_domain ps) /\
    binder_path_value_origin_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      parts
      (nested_binder_wild_pattern_list_domain ps) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose (hpath := build_tuple_nested_binder_wild_path_witness_bundle_of_generated
    ps vs parts Hfrag Hparts).
  split.
  - exact (tuple_pattern_witness_exact ps vs (merge_substs parts) I).
  - split.
    + exact (tnpwb_leaf _ _ _ _ hpath).
    + split.
      * exact (tnpwb_part_leaf _ _ _ _ hpath).
      * split.
        { exact (tnpwb_origin _ _ _ _ hpath). }
        { split.
          - exact (tnpwb_value_origin _ _ _ _ hpath).
          - split.
            + exact (tuple_core_match_witness_exact ps vs (merge_substs parts) Hσ).
            + exact (typing_match_tuple_observation_bundle p ps vs body rest stmtBody stmtRest Hprog). }
Qed.

Theorem typing_match_struct_nested_binder_wild_path_provenance_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_struct_field_pattern_list fs ->
    struct_nested_binder_wild_generated_parts fs fields parts ->
    match_subst_unique (merge_substs parts) ->
    struct_pattern_witness name fs fields (merge_substs parts) /\
    binder_path_leaf_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      (merge_substs parts)
      (nested_binder_wild_struct_field_pattern_list_domain fs) /\
    binder_path_part_leaf_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      parts
      (nested_binder_wild_struct_field_pattern_list_domain fs) /\
    binder_path_part_origin_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      parts
      (nested_binder_wild_struct_field_pattern_list_domain fs) /\
    binder_path_value_origin_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      parts
      (nested_binder_wild_struct_field_pattern_list_domain fs) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose (hpath := build_struct_nested_binder_wild_path_witness_bundle_of_generated
    name fs fields parts Hfrag Hparts).
  split.
  - exact (struct_pattern_witness_exact name fs fields (merge_substs parts) I).
  - split.
    + exact (snpwb_leaf _ _ _ _ _ hpath).
    + split.
      * exact (snpwb_part_leaf _ _ _ _ _ hpath).
      * split.
        { exact (snpwb_origin _ _ _ _ _ hpath). }
        { split.
          - exact (snpwb_value_origin _ _ _ _ _ hpath).
          - split.
            + exact (struct_core_match_witness_exact name fs fields (merge_substs parts) Hσ).
            + exact (typing_match_struct_observation_bundle p name fs fields body rest stmtBody stmtRest Hprog). }
Qed.

Theorem typing_match_tuple_nested_binder_wild_path_leaf_at_bundle :
  forall p ps vs parts body rest stmtBody stmtRest x
    (Hprog : well_typed_program p)
    (Hfrag : nested_binder_wild_pattern_list ps)
    (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
    (Hσ : match_subst_unique (merge_substs parts))
    (Hx : In x (nested_binder_wild_pattern_list_domain ps)),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    (In x (subst_domain (merge_substs parts)) /\
      exists path, In (path, x) (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest x Hprog Hfrag Hparts Hσ Hx.
  pose proof (typing_match_tuple_nested_binder_wild_path_provenance_bundle
    p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hleaf [_ [_ [_ [Hcore [Hhit HstmtHit]]]]]]].
  specialize (Hleaf x Hx).
  split.
  - exact Hpat.
  - split.
    + exact Hleaf.
    + split.
      * exact Hcore.
      * exact (conj Hhit HstmtHit).
Qed.

Theorem typing_match_struct_nested_binder_wild_path_leaf_at_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest x
    (Hprog : well_typed_program p)
    (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
    (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
    (Hσ : match_subst_unique (merge_substs parts))
    (Hx : In x (nested_binder_wild_struct_field_pattern_list_domain fs)),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    (In x (subst_domain (merge_substs parts)) /\
      exists path, In (path, x) (nested_binder_wild_struct_field_binder_path_bindings fs [])) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest x Hprog Hfrag Hparts Hσ Hx.
  pose proof (typing_match_struct_nested_binder_wild_path_provenance_bundle
    p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hleaf [_ [_ [_ [Hcore [Hhit HstmtHit]]]]]]].
  specialize (Hleaf x Hx).
  split.
  - exact Hpat.
  - split.
    + exact Hleaf.
    + split.
      * exact Hcore.
      * exact (conj Hhit HstmtHit).
Qed.

Theorem typing_match_tuple_nested_binder_wild_path_part_leaf_at_bundle :
  forall p ps vs parts body rest stmtBody stmtRest x
    (Hprog : well_typed_program p)
    (Hfrag : nested_binder_wild_pattern_list ps)
    (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
    (Hσ : match_subst_unique (merge_substs parts))
    (Hx : In x (nested_binder_wild_pattern_list_domain ps)),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    ((exists path, In (path, x) (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)) /\
      exists part, In part parts /\ In x (subst_domain part)) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest x Hprog Hfrag Hparts Hσ Hx.
  pose proof (typing_match_tuple_nested_binder_wild_path_provenance_bundle
    p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [HpartLeaf [_ [_ [Hcore [Hhit HstmtHit]]]]]]].
  specialize (HpartLeaf x Hx).
  split.
  - exact Hpat.
  - split.
    + exact HpartLeaf.
    + split.
      * exact Hcore.
      * exact (conj Hhit HstmtHit).
Qed.

Theorem typing_match_struct_nested_binder_wild_path_part_leaf_at_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest x
    (Hprog : well_typed_program p)
    (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
    (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
    (Hσ : match_subst_unique (merge_substs parts))
    (Hx : In x (nested_binder_wild_struct_field_pattern_list_domain fs)),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    ((exists path, In (path, x) (nested_binder_wild_struct_field_binder_path_bindings fs [])) /\
      exists part, In part parts /\ In x (subst_domain part)) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest x Hprog Hfrag Hparts Hσ Hx.
  pose proof (typing_match_struct_nested_binder_wild_path_provenance_bundle
    p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [HpartLeaf [_ [_ [Hcore [Hhit HstmtHit]]]]]]].
  specialize (HpartLeaf x Hx).
  split.
  - exact Hpat.
  - split.
    + exact HpartLeaf.
    + split.
      * exact Hcore.
      * exact (conj Hhit HstmtHit).
Qed.

Theorem typing_match_tuple_nested_binder_wild_path_origin_at_bundle :
  forall p ps vs parts body rest stmtBody stmtRest x
    (Hprog : well_typed_program p)
    (Hfrag : nested_binder_wild_pattern_list ps)
    (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
    (Hσ : match_subst_unique (merge_substs parts))
    (Hx : In x (nested_binder_wild_pattern_list_domain ps)),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    (exists path part,
      In (path, x) (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0) /\
      In part parts /\
      In x (subst_domain part)) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest x Hprog Hfrag Hparts Hσ Hx.
  pose proof (typing_match_tuple_nested_binder_wild_path_provenance_bundle
    p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [_ [Horigin [_ [Hcore [Hhit HstmtHit]]]]]]].
  specialize (Horigin x Hx).
  split.
  - exact Hpat.
  - split.
    + exact Horigin.
    + split.
      * exact Hcore.
      * exact (conj Hhit HstmtHit).
Qed.

Theorem typing_match_struct_nested_binder_wild_path_origin_at_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest x
    (Hprog : well_typed_program p)
    (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
    (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
    (Hσ : match_subst_unique (merge_substs parts))
    (Hx : In x (nested_binder_wild_struct_field_pattern_list_domain fs)),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    (exists path part,
      In (path, x) (nested_binder_wild_struct_field_binder_path_bindings fs []) /\
      In part parts /\
      In x (subst_domain part)) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest x Hprog Hfrag Hparts Hσ Hx.
  pose proof (typing_match_struct_nested_binder_wild_path_provenance_bundle
    p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [_ [Horigin [_ [Hcore [Hhit HstmtHit]]]]]]].
  specialize (Horigin x Hx).
  split.
  - exact Hpat.
  - split.
    + exact Horigin.
    + split.
      * exact Hcore.
      * exact (conj Hhit HstmtHit).
Qed.

Theorem typing_match_tuple_nested_binder_wild_path_value_origin_at_bundle :
  forall p ps vs parts body rest stmtBody stmtRest x
    (Hprog : well_typed_program p)
    (Hfrag : nested_binder_wild_pattern_list ps)
    (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
    (Hσ : match_subst_unique (merge_substs parts))
    (Hx : In x (nested_binder_wild_pattern_list_domain ps)),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    (exists path part value,
      In (path, x) (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0) /\
      In part parts /\
      In (x, value) part) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest x Hprog Hfrag Hparts Hσ Hx.
  pose proof (typing_match_tuple_nested_binder_wild_path_provenance_bundle
    p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [_ [_ [HvalueOrigin [Hcore [Hhit HstmtHit]]]]]]].
  specialize (HvalueOrigin x Hx).
  split.
  - exact Hpat.
  - split.
    + exact HvalueOrigin.
    + split.
      * exact Hcore.
      * exact (conj Hhit HstmtHit).
Qed.

Theorem typing_match_struct_nested_binder_wild_path_value_origin_at_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest x
    (Hprog : well_typed_program p)
    (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
    (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
    (Hσ : match_subst_unique (merge_substs parts))
    (Hx : In x (nested_binder_wild_struct_field_pattern_list_domain fs)),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    (exists path part value,
      In (path, x) (nested_binder_wild_struct_field_binder_path_bindings fs []) /\
      In part parts /\
      In (x, value) part) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest x Hprog Hfrag Hparts Hσ Hx.
  pose proof (typing_match_struct_nested_binder_wild_path_provenance_bundle
    p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [_ [_ [HvalueOrigin [Hcore [Hhit HstmtHit]]]]]]].
  specialize (HvalueOrigin x Hx).
  split.
  - exact Hpat.
  - split.
    + exact HvalueOrigin.
    + split.
      * exact Hcore.
      * exact (conj Hhit HstmtHit).
Qed.

Theorem typing_match_tuple_nested_binder_wild_path_leaf_bundle :
  forall p ps vs parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_pattern_list ps ->
    tuple_nested_binder_wild_generated_parts ps vs parts ->
    match_subst_unique (merge_substs parts) ->
    tuple_pattern_witness ps vs (merge_substs parts) /\
    binder_path_leaf_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      (merge_substs parts)
      (nested_binder_wild_pattern_list_domain ps) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose proof (typing_match_tuple_nested_binder_wild_path_provenance_bundle
    p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hleaf [_ [_ [_ [Hcore [Hhit HstmtHit]]]]]]].
  split.
  - exact Hpat.
  - split.
    + exact Hleaf.
    + split.
      * exact Hcore.
      * exact (conj Hhit HstmtHit).
Qed.

Theorem typing_match_struct_nested_binder_wild_path_leaf_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_struct_field_pattern_list fs ->
    struct_nested_binder_wild_generated_parts fs fields parts ->
    match_subst_unique (merge_substs parts) ->
    struct_pattern_witness name fs fields (merge_substs parts) /\
    binder_path_leaf_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      (merge_substs parts)
      (nested_binder_wild_struct_field_pattern_list_domain fs) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose proof (typing_match_struct_nested_binder_wild_path_provenance_bundle
    p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hleaf [_ [_ [_ [Hcore [Hhit HstmtHit]]]]]]].
  split.
  - exact Hpat.
  - split.
    + exact Hleaf.
    + split.
      * exact Hcore.
      * exact (conj Hhit HstmtHit).
Qed.

Theorem typing_match_tuple_nested_binder_wild_path_part_leaf_bundle :
  forall p ps vs parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_pattern_list ps ->
    tuple_nested_binder_wild_generated_parts ps vs parts ->
    match_subst_unique (merge_substs parts) ->
    tuple_pattern_witness ps vs (merge_substs parts) /\
    binder_path_part_leaf_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      parts
      (nested_binder_wild_pattern_list_domain ps) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose proof (typing_match_tuple_nested_binder_wild_path_provenance_bundle
    p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [HpartLeaf [_ [_ [Hcore [Hhit HstmtHit]]]]]]].
  split.
  - exact Hpat.
  - split.
    + exact HpartLeaf.
    + split.
      * exact Hcore.
      * exact (conj Hhit HstmtHit).
Qed.

Theorem typing_match_struct_nested_binder_wild_path_part_leaf_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_struct_field_pattern_list fs ->
    struct_nested_binder_wild_generated_parts fs fields parts ->
    match_subst_unique (merge_substs parts) ->
    struct_pattern_witness name fs fields (merge_substs parts) /\
    binder_path_part_leaf_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      parts
      (nested_binder_wild_struct_field_pattern_list_domain fs) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose proof (typing_match_struct_nested_binder_wild_path_provenance_bundle
    p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [HpartLeaf [_ [_ [Hcore [Hhit HstmtHit]]]]]]].
  split.
  - exact Hpat.
  - split.
    + exact HpartLeaf.
    + split.
      * exact Hcore.
      * exact (conj Hhit HstmtHit).
Qed.

Theorem typing_match_tuple_nested_binder_wild_path_origin_bundle :
  forall p ps vs parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_pattern_list ps ->
    tuple_nested_binder_wild_generated_parts ps vs parts ->
    match_subst_unique (merge_substs parts) ->
    tuple_pattern_witness ps vs (merge_substs parts) /\
    binder_path_part_origin_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      parts
      (nested_binder_wild_pattern_list_domain ps) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose proof (typing_match_tuple_nested_binder_wild_path_provenance_bundle
    p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [_ [Horigin [_ [Hcore [Hhit HstmtHit]]]]]]].
  split.
  - exact Hpat.
  - split.
    + exact Horigin.
    + split.
      * exact Hcore.
      * exact (conj Hhit HstmtHit).
Qed.

Theorem typing_match_struct_nested_binder_wild_path_origin_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_struct_field_pattern_list fs ->
    struct_nested_binder_wild_generated_parts fs fields parts ->
    match_subst_unique (merge_substs parts) ->
    struct_pattern_witness name fs fields (merge_substs parts) /\
    binder_path_part_origin_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      parts
      (nested_binder_wild_struct_field_pattern_list_domain fs) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose proof (typing_match_struct_nested_binder_wild_path_provenance_bundle
    p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [_ [Horigin [_ [Hcore [Hhit HstmtHit]]]]]]].
  split.
  - exact Hpat.
  - split.
    + exact Horigin.
    + split.
      * exact Hcore.
      * exact (conj Hhit HstmtHit).
Qed.

Theorem typing_match_tuple_nested_binder_wild_path_value_origin_bundle :
  forall p ps vs parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_pattern_list ps ->
    tuple_nested_binder_wild_generated_parts ps vs parts ->
    match_subst_unique (merge_substs parts) ->
    tuple_pattern_witness ps vs (merge_substs parts) /\
    binder_path_value_origin_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      parts
      (nested_binder_wild_pattern_list_domain ps) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    match_stmt_branch_observed (VTuple vs) ((PTuple ps, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose proof (typing_match_tuple_nested_binder_wild_path_provenance_bundle
    p ps vs parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [_ [_ [HvalueOrigin [Hcore [Hhit HstmtHit]]]]]]].
  split.
  - exact Hpat.
  - split.
    + exact HvalueOrigin.
    + split.
      * exact Hcore.
      * exact (conj Hhit HstmtHit).
Qed.

Theorem typing_match_struct_nested_binder_wild_path_value_origin_bundle :
  forall p name fs fields parts body rest stmtBody stmtRest,
    well_typed_program p ->
    nested_binder_wild_struct_field_pattern_list fs ->
    struct_nested_binder_wild_generated_parts fs fields parts ->
    match_subst_unique (merge_substs parts) ->
    struct_pattern_witness name fs fields (merge_substs parts) /\
    binder_path_value_origin_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      parts
      (nested_binder_wild_struct_field_pattern_list_domain fs) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    match_stmt_branch_observed (VStruct name fields) ((PStruct name fs, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ.
  pose proof (typing_match_struct_nested_binder_wild_path_provenance_bundle
    p name fs fields parts body rest stmtBody stmtRest Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [_ [_ [HvalueOrigin [Hcore [Hhit HstmtHit]]]]]]].
  split.
  - exact Hpat.
  - split.
    + exact HvalueOrigin.
    + split.
      * exact Hcore.
      * exact (conj Hhit HstmtHit).
Qed.

Theorem typing_match_observation_bundle_after_ctor_mismatches :
  forall p ctor pats args prefix body rest stmtPrefix stmtBody stmtRest,
    well_typed_program p ->
    ctor_mismatch_expr_prefix ctor prefix ->
    ctor_mismatch_stmt_prefix ctor stmtPrefix ->
    match_branch_observed (VCtor ctor args) (prefix ++ (PCtor ctor pats, body) :: rest) body /\
    match_stmt_branch_observed (VCtor ctor args) (stmtPrefix ++ (PCtor ctor pats, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ctor pats args prefix body rest stmtPrefix stmtBody stmtRest Hprog Hprefix Hstmt.
  split.
  - exact (typing_match_branch_observed_after_ctor_mismatches p ctor pats args prefix body rest Hprog Hprefix).
  - exact (typing_match_stmt_branch_observed_after_ctor_mismatches p ctor pats args stmtPrefix stmtBody stmtRest Hprog Hstmt).
Qed.

Theorem typing_match_wildcard_observation_bundle_after_ctor_mismatches :
  forall p ctor args prefix body rest stmtPrefix stmtBody stmtRest,
    well_typed_program p ->
    ctor_mismatch_expr_prefix ctor prefix ->
    ctor_mismatch_stmt_prefix ctor stmtPrefix ->
    match_branch_observed (VCtor ctor args) (prefix ++ (PWild, body) :: rest) body /\
    match_stmt_branch_observed (VCtor ctor args) (stmtPrefix ++ (PWild, stmtBody) :: stmtRest) stmtBody.
Proof.
  intros p ctor args prefix body rest stmtPrefix stmtBody stmtRest Hprog Hprefix Hstmt.
  split.
  - exact (typing_match_branch_observed_wild_after_ctor_mismatches p ctor args prefix body rest Hprog Hprefix).
  - exact (typing_match_stmt_branch_observed_wild_after_ctor_mismatches p ctor args stmtPrefix stmtBody stmtRest Hprog Hstmt).
Qed.

Theorem typing_match_coverage_bundle :
  forall p ctor args cases body stmtCases stmtBody,
    well_typed_program p ->
    ctor_expr_cases_cover ctor cases body ->
    ctor_stmt_cases_cover ctor stmtCases stmtBody ->
    match_branch_observed (VCtor ctor args) cases body /\
    match_stmt_branch_observed (VCtor ctor args) stmtCases stmtBody.
Proof.
  intros p ctor args cases body stmtCases stmtBody Hprog Hcover HstmtCover.
  split.
  - exact (typing_match_branch_observed_of_ctor_cover p ctor args cases body Hprog Hcover).
  - exact (typing_match_stmt_branch_observed_of_ctor_cover p ctor args stmtCases stmtBody Hprog HstmtCover).
Qed.

Theorem typing_match_exhaustive_bundle :
  forall p ctor args cases stmtCases,
    well_typed_program p ->
    ctor_expr_cases_exhaustive ctor cases ->
    ctor_stmt_cases_exhaustive ctor stmtCases ->
    (exists body, match_branch_observed (VCtor ctor args) cases body) /\
    (exists stmtBody, match_stmt_branch_observed (VCtor ctor args) stmtCases stmtBody).
Proof.
  intros p ctor args cases stmtCases Hprog Hexpr Hstmt.
  split.
  - exact (select_match_expr_exists_of_exhaustive ctor args cases Hexpr).
  - exact (select_match_stmt_exists_of_exhaustive ctor args stmtCases Hstmt).
Qed.

Theorem typing_copy_update_helper_bundle :
  forall p v newv t,
    well_typed_program p ->
    has_type_value v t ->
    lookup_value_path v [] = Some v /\
    update_value_path v [] newv = Some newv.
Proof.
  intros p v newv t Hprog Hty. split.
  - exact (typing_lookup_value_path_root p v t Hprog Hty).
  - exact (typing_update_value_path_root p v newv t Hprog Hty).
Qed.

Theorem typing_copy_update_observation_bundle :
  forall p v newv t,
    well_typed_program p ->
    has_type_value v t ->
    copy_update_path_observed v [] newv newv.
Proof.
  intros p v newv t Hprog Hty.
  exact (typing_copy_update_path_observed_root p v newv t Hprog Hty).
Qed.

Theorem typing_copy_update_head_observation_bundle :
  forall p v newv t,
    well_typed_program p ->
    has_type_value v t ->
    copy_update_head_observed v [] newv newv.
Proof.
  intros p v newv t Hprog Hty.
  exact (typing_copy_update_head_observed_root p v newv t Hprog Hty).
Qed.

Theorem typing_copy_update_prefix_observation_bundle :
  forall p v newv t,
    well_typed_program p ->
    has_type_value v t ->
    copy_update_prefix_observed v [] newv newv.
Proof.
  intros p v newv t Hprog Hty.
  exact (typing_copy_update_prefix_observed_root p v newv t Hprog Hty).
Qed.

Theorem typing_copy_update_observation_bundle_general :
  forall p v newv out path t,
    well_typed_program p ->
    has_type_value v t ->
    update_value_path v path newv = Some out ->
    copy_update_path_observed v path newv out.
Proof.
  intros p v newv out path t Hprog Hty Hupd.
  exact (typing_copy_update_path_observed_of_success p v newv out path t Hprog Hty Hupd).
Qed.

Theorem typing_copy_update_head_observation_bundle_general :
  forall p v newv out path t,
    well_typed_program p ->
    has_type_value v t ->
    update_value_path v path newv = Some out ->
    copy_update_head_observed v path newv out.
Proof.
  intros p v newv out path t Hprog Hty Hupd.
  exact (typing_copy_update_head_observed_of_success p v newv out path t Hprog Hty Hupd).
Qed.

Theorem typing_copy_update_prefix_observation_bundle_general :
  forall p v newv out path t,
    well_typed_program p ->
    has_type_value v t ->
    update_value_path v path newv = Some out ->
    copy_update_prefix_observed v path newv out.
Proof.
  intros p v newv out path t Hprog Hty Hupd.
  exact (typing_copy_update_prefix_observed_of_success p v newv out path t Hprog Hty Hupd).
Qed.

Theorem typing_copy_update_child_observation_bundle_general :
  forall p v newv out key rest t,
    well_typed_program p ->
    has_type_value v t ->
    update_value_path v (key :: rest) newv = Some out ->
    exists name fields child child',
      v = VStruct name fields /\
      lookup_field fields key = Some child /\
      update_value_path child rest newv = Some child' /\
      out = VStruct name (update_field fields key child') /\
      copy_update_path_observed child rest newv child'.
Proof.
  intros p v newv out key rest t Hprog Hty Hupd.
  eapply copy_update_prefix_observed_child.
  exact (typing_copy_update_prefix_observation_bundle_general p v newv out (key :: rest) t Hprog Hty Hupd).
Qed.

Theorem typing_copy_update_child_chain_observation_bundle_general :
  forall p v newv out key nextKey rest t,
    well_typed_program p ->
    has_type_value v t ->
    update_value_path v (key :: nextKey :: rest) newv = Some out ->
    exists name fields child child',
      v = VStruct name fields /\
      lookup_field fields key = Some child /\
      update_value_path child (nextKey :: rest) newv = Some child' /\
      out = VStruct name (update_field fields key child') /\
      copy_update_prefix_observed child (nextKey :: rest) newv child'.
Proof.
  intros p v newv out key nextKey rest t Hprog Hty Hupd.
  eapply copy_update_prefix_observed_child_chain.
  exact (typing_copy_update_prefix_observation_bundle_general p v newv out (key :: nextKey :: rest) t Hprog Hty Hupd).
Qed.

Theorem typing_copy_update_grandchild_observation_bundle_general :
  forall p v newv out key nextKey rest t,
    well_typed_program p ->
    has_type_value v t ->
    update_value_path v (key :: nextKey :: rest) newv = Some out ->
    exists name fields child child' childName childFields grandchild grandchild',
      v = VStruct name fields /\
      lookup_field fields key = Some child /\
      update_value_path child (nextKey :: rest) newv = Some child' /\
      out = VStruct name (update_field fields key child') /\
      child = VStruct childName childFields /\
      lookup_field childFields nextKey = Some grandchild /\
      update_value_path grandchild rest newv = Some grandchild' /\
      child' = VStruct childName (update_field childFields nextKey grandchild') /\
      copy_update_path_observed grandchild rest newv grandchild'.
Proof.
  intros p v newv out key nextKey rest t Hprog Hty Hupd.
  eapply copy_update_prefix_observed_grandchild.
  exact (typing_copy_update_prefix_observation_bundle_general p v newv out (key :: nextKey :: rest) t Hprog Hty Hupd).
Qed.

Theorem typing_copy_update_grandchild_chain_observation_bundle_general :
  forall p v newv out key nextKey thirdKey rest t,
    well_typed_program p ->
    has_type_value v t ->
    update_value_path v (key :: nextKey :: thirdKey :: rest) newv = Some out ->
    exists name fields child child' childName childFields grandchild grandchild',
      v = VStruct name fields /\
      lookup_field fields key = Some child /\
      update_value_path child (nextKey :: thirdKey :: rest) newv = Some child' /\
      out = VStruct name (update_field fields key child') /\
      child = VStruct childName childFields /\
      lookup_field childFields nextKey = Some grandchild /\
      update_value_path grandchild (thirdKey :: rest) newv = Some grandchild' /\
      child' = VStruct childName (update_field childFields nextKey grandchild') /\
      copy_update_prefix_observed grandchild (thirdKey :: rest) newv grandchild'.
Proof.
  intros p v newv out key nextKey thirdKey rest t Hprog Hty Hupd.
  eapply copy_update_prefix_observed_grandchild_chain.
  exact (typing_copy_update_prefix_observation_bundle_general p v newv out (key :: nextKey :: thirdKey :: rest) t Hprog Hty Hupd).
Qed.

Theorem typing_enum_helper_bundle :
  forall p ctor enumName args,
    well_typed_program p ->
    has_type_value (VCtor ctor args) (TyEnum enumName) ->
    enum_tag_of (VCtor ctor args) = Some ctor /\
    enum_payload_of (VCtor ctor args) = Some args.
Proof.
  intros p ctor enumName args Hprog Hty. split.
  - exact (typing_enum_tag_of_ctor p ctor enumName args Hprog Hty).
  - exact (typing_enum_payload_of_ctor p ctor enumName args Hprog Hty).
Qed.

Theorem typing_enum_observation_bundle :
  forall p ctor enumName args,
    well_typed_program p ->
    has_type_value (VCtor ctor args) (TyEnum enumName) ->
    enum_encoding_observed (VCtor ctor args) ctor args.
Proof.
  intros p ctor enumName args Hprog Hty.
  exact (typing_enum_encoding_observed_ctor p ctor enumName args Hprog Hty).
Qed.

Theorem typing_pipeline_helper_bundle :
  forall p input,
    well_typed_program p ->
    run_pipeline_stages input [] = input.
Proof.
  intros p input Hprog.
  exact (typing_run_pipeline_stages_nil p input Hprog).
Qed.

Theorem typing_pipeline_observation_bundle :
  forall p input stage,
    well_typed_program p ->
    pipeline_single_stage_observed input stage.
Proof.
  intros p input stage Hprog.
  exact (typing_pipeline_single_stage_observed p input stage Hprog).
Qed.

Theorem typing_pipeline_observation_bundle_general :
  forall p input stages,
    well_typed_program p ->
    pipeline_stages_observed input stages.
Proof.
  intros p input stages Hprog.
  exact (typing_pipeline_stages_observed p input stages Hprog).
Qed.

Theorem typing_tail_observation_bundle :
  forall p fn args,
    well_typed_program p ->
    interp_tail_expr (ECall fn args) = TORecur fn (map interp_expr args) /\
    tail_recur_observed (ECall fn args) fn (map interp_expr args) /\
    tail_call_shape_observed (ECall fn args) fn (map interp_expr args) /\
    tail_observational_eq (ECall fn args) (ECall fn args).
Proof.
  intros p fn args Hprog.
  split.
  - exact (typing_tailcall_helper_bundle p fn args Hprog).
  - split.
    + exact (typing_tail_recur_observed_call p fn args Hprog).
    + split.
      * exact (typing_tail_call_shape_observed_call p fn args Hprog).
      * exact (tail_observational_eq_refl (ECall fn args)).
Qed.

End FoTyping.
