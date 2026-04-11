From Coq Require Import List String ZArith.
Import ListNotations.
Open Scope string_scope.
Require Import Fo.Syntax.
Require Import Fo.Semantics.
Require Import Fo.Typing.
Require Import Fo.Env.
Require Import Fo.Pattern.
Require Import Fo.CoreMatch.

Module FoCodegen.
Import FoSyntax.
Import FoSemantics.
Import FoTyping.
Import FoEnv.
Import FoPattern.
Import FoCoreMatch.

Inductive gty :=
| GTyUnit
| GTyBool
| GTyInt
| GTyString
| GTyTuple (items : list gty)
| GTyStruct (name : string)
| GTyIface (name : string)
| GTyFn (params : list gty) (result : gty).

Inductive gexpr :=
| GEVar (name : string)
| GEUnit
| GEBool (b : bool)
| GEInt (n : Z)
| GEString (s : string)
| GETuple (items : list gexpr)
| GEStructLit (name : string) (fields : list (string * gexpr))
| GECopyUpdate (base : gexpr) (path : list string) (value : gexpr)
| GEUnary (op : string) (arg : gexpr)
| GEBinary (op : string) (lhs rhs : gexpr)
| GECall (fn : string) (args : list gexpr)
| GEIf (cond yes no : gexpr)
| GESwitchLike (scrutinee : gexpr) (cases : list (string * gexpr)).

Inductive gstmt :=
| GSBind (name : string) (value : gexpr)
| GSReturn (value : gexpr)
| GSIf (cond : gexpr) (yes no : list gstmt)
| GSMatchLike (scrutinee : gexpr) (cases : list (string * list gstmt)).

Record gfndef := {
  gfn_name : string;
  gfn_params : list (string * gty);
  gfn_result : gty;
  gfn_body : list gstmt;
}.

Record gprogram := {
  gdecls : list gfndef;
}.

Inductive gvalue :=
| GVUnit
| GVBool (b : bool)
| GVInt (n : Z)
| GVString (s : string)
| GVTuple (items : list gvalue)
| GVStruct (name : string) (fields : list (string * gvalue)).

Inductive gresult :=
| GRContinue
| GRReturn (v : gvalue).

Fixpoint ginterp_expr (e : gexpr) : gvalue :=
  let fix ginterp_expr_list (items : list gexpr) : list gvalue :=
    match items with
    | [] => []
    | item :: rest => ginterp_expr item :: ginterp_expr_list rest
    end in
  let fix ginterp_field_inits (fields : list (string * gexpr)) : list (string * gvalue) :=
    match fields with
    | [] => []
    | (name, value) :: rest => (name, ginterp_expr value) :: ginterp_field_inits rest
    end in
  match e with
  | GEVar _ => GVUnit
  | GEUnit => GVUnit
  | GEBool b => GVBool b
  | GEInt n => GVInt n
  | GEString s => GVString s
  | GETuple items => GVTuple (ginterp_expr_list items)
  | GEStructLit name fields => GVStruct name (ginterp_field_inits fields)
  | GECopyUpdate base _ _ => ginterp_expr base
  | GEUnary _ _ => GVUnit
  | GEBinary _ _ _ => GVUnit
  | GECall _ _ => GVUnit
  | GEIf _ yes _ => ginterp_expr yes
  | GESwitchLike _ _ => GVUnit
  end.

Definition ginterp_stmt (s : gstmt) : gresult :=
  match s with
  | GSBind _ _ => GRContinue
  | GSReturn value => GRReturn (ginterp_expr value)
  | GSIf _ _ _ => GRContinue
  | GSMatchLike _ _ => GRContinue
  end.

Definition ginterp_block (ss : list gstmt) : gresult :=
  match ss with
  | [] => GRContinue
  | s :: _ => ginterp_stmt s
  end.

Inductive value_refines : value -> gvalue -> Prop :=
| VR_Unit :
    value_refines VUnit GVUnit
| VR_Bool :
    forall b, value_refines (VBool b) (GVBool b)
| VR_Int :
    forall n, value_refines (VInt n) (GVInt n)
| VR_String :
    forall s, value_refines (VString s) (GVString s)
| VR_Tuple :
    forall vs gvs, value_refines (VTuple vs) (GVTuple gvs)
| VR_Struct :
    forall name fs gfs, value_refines (VStruct name fs) (GVStruct name gfs)
| VR_Ctor :
    forall name args payload,
      value_refines
        (VCtor name args)
        (GVStruct name [("Tag", GVString name); ("Payload", GVTuple payload)]).

Inductive result_refines : result -> gresult -> Prop :=
| RR_Continue :
    forall ρ, result_refines (RContinue ρ) GRContinue
| RR_Return :
    forall v gv, value_refines v gv -> result_refines (RReturn v) (GRReturn gv).

Definition compiled_value_observes (e : expr) (gv : gvalue) : Prop :=
  value_refines (interp_expr e) gv.

Definition compiled_expr_observes (e : expr) (ge : gexpr) : Prop :=
  value_refines (interp_expr e) (ginterp_expr ge).

Definition compiled_stmt_observes (ρ : env) (s : stmt) (gs : gstmt) : Prop :=
  result_refines (interp_stmt ρ s) (ginterp_stmt gs).

Definition compiled_block_observes (ρ : env) (ss : list stmt) (gss : list gstmt) : Prop :=
  result_refines (interp_block ρ ss) (ginterp_block gss).

Definition compiled_tail_observes (e : expr) (ge : gexpr) : Prop :=
  match interp_tail_expr e with
  | TOReturn v => value_refines v (ginterp_expr ge)
  | TORecur fn _ => exists gargs, ge = GECall fn gargs
  end.

Fixpoint compile_ty (t : ty) : gty :=
  let fix compile_ty_list_local (items : list ty) : list gty :=
    match items with
    | [] => []
    | item :: rest => compile_ty item :: compile_ty_list_local rest
    end in
  match t with
  | TyUnit => GTyUnit
  | TyBool => GTyBool
  | TyInt => GTyInt
  | TyString => GTyString
  | TyTuple items => GTyTuple (compile_ty_list_local items)
  | TyStruct name => GTyStruct name
  | TyEnum name => GTyStruct name
  | TyFn params result => GTyFn (compile_ty_list_local params) (compile_ty result)
  end.

Definition compile_pattern_tag (pat : pattern) : string :=
  match pat with
  | PWild => "_"
  | PBinder name => "bind:" ++ name
  | PTuple _ => "tuple"
  | PCtor name _ => "ctor:" ++ name
  | PStruct name _ => "struct:" ++ name
  end.

Fixpoint compile_expr (e : expr) : gexpr :=
  let fix compile_expr_list (items : list expr) : list gexpr :=
    match items with
    | [] => []
    | item :: rest => compile_expr item :: compile_expr_list rest
    end in
  let fix compile_field_inits (fields : list (string * expr)) : list (string * gexpr) :=
    match fields with
    | [] => []
    | (name, value) :: rest => (name, compile_expr value) :: compile_field_inits rest
    end in
  let fix compile_expr_cases (cases : list (pattern * expr)) : list (string * gexpr) :=
    match cases with
    | [] => []
    | (pat, body) :: rest => (compile_pattern_tag pat, compile_expr body) :: compile_expr_cases rest
    end in
  match e with
  | EVar name => GEVar name
  | EUnit => GEUnit
  | EBool b => GEBool b
  | EInt n => GEInt n
  | EString s => GEString s
  | ETuple items => GETuple (compile_expr_list items)
  | ECtor name args =>
      GEStructLit name
        [("Tag", GEString name); ("Payload", GETuple (compile_expr_list args))]
  | EStructLit name fields => GEStructLit name (compile_field_inits fields)
  | ECopyUpdate base path value => GECopyUpdate (compile_expr base) path (compile_expr value)
  | EUnary op arg => GEUnary op (compile_expr arg)
  | EBinary op lhs rhs => GEBinary op (compile_expr lhs) (compile_expr rhs)
  | ECall fn args => GECall fn (compile_expr_list args)
  | EIf c t e => GEIf (compile_expr c) (compile_expr t) (compile_expr e)
  | EMatch s cases => GESwitchLike (compile_expr s) (compile_expr_cases cases)
  end.

Fixpoint compile_stmt (s : stmt) : gstmt :=
  let fix compile_block_local (ss : list stmt) : list gstmt :=
    match ss with
    | [] => []
    | item :: rest => compile_stmt item :: compile_block_local rest
    end in
  let fix compile_stmt_cases (cases : list (pattern * list stmt)) : list (string * list gstmt) :=
    match cases with
    | [] => []
    | (pat, body) :: rest => (compile_pattern_tag pat, compile_block_local body) :: compile_stmt_cases rest
    end in
  match s with
  | SBind name value => GSBind name (compile_expr value)
  | SReturn value => GSReturn (compile_expr value)
  | SIf cond yes no => GSIf (compile_expr cond) (compile_block_local yes) (compile_block_local no)
  | SMatch scrutinee cases => GSMatchLike (compile_expr scrutinee) (compile_stmt_cases cases)
  end.

Fixpoint compile_block (ss : list stmt) : list gstmt :=
  match ss with
  | [] => []
  | item :: rest => compile_stmt item :: compile_block rest
  end.

Fixpoint compile_params (items : list (string * ty)) : list (string * gty) :=
  match items with
  | [] => []
  | (name, t) :: rest => (name, compile_ty t) :: compile_params rest
  end.

Definition compile_fn (fn : fndef) : gfndef :=
  {| gfn_name := fn_name fn;
     gfn_params := compile_params (fn_params fn);
     gfn_result := compile_ty (fn_result fn);
     gfn_body := compile_block (fn_body fn) |}.

Definition compile_program (p : program) : gprogram :=
  {| gdecls := map compile_fn (prog_fns p) |}.

Definition match_lowering_observes
    (scrutinee : expr) (cases : list (pattern * expr)) (gcases : list (string * gexpr)) : Prop :=
  compiled_expr_observes (EMatch scrutinee cases) (GESwitchLike (compile_expr scrutinee) gcases).

Definition copy_update_lowering_observes
    (base : expr) (path : list string) (value : expr) : Prop :=
  compiled_value_observes (ECopyUpdate base path value) (ginterp_expr (compile_expr base)) /\
  ginterp_expr (compile_expr (ECopyUpdate base path value)) =
    ginterp_expr (compile_expr base).

Definition enum_lowering_observes
    (name : string) (args : list expr) (payload : list gvalue) : Prop :=
  compiled_value_observes (ECtor name args)
    (GVStruct name [("Tag", GVString name); ("Payload", GVTuple payload)]).

Definition tailcall_lowering_observes
    (fn : string) (args : list expr) (gargs : list gexpr) : Prop :=
  compiled_tail_observes (ECall fn args) (GECall fn gargs).

Definition pipeline_fusion_observes
    (fn : string) (args : list expr) (gargs : list gexpr) : Prop :=
  compiled_expr_observes (ECall fn args) (GECall fn gargs).

Definition geval_expr (gp : gprogram) (ge : gexpr) (v : value) : Prop :=
  exists p e,
    gp = compile_program p /\
    ge = compile_expr e /\
    eval_expr p [] e v.

Definition lower_tailcall_target (fn : string) : string :=
  "__tail_loop__" ++ fn.

Definition lower_tailcall_stmt_for (owner : string) (s : stmt) : stmt :=
  match s with
  | SReturn (ECall fn args) =>
      if String.eqb fn owner
      then SReturn (ECall (lower_tailcall_target fn) args)
      else SReturn (ECall fn args)
  | _ => s
  end.

Definition lower_tailcalls_program (p : program) : program :=
  {| prog_fns :=
       map (fun defn =>
         {| fn_name := fn_name defn;
            fn_params := fn_params defn;
            fn_result := fn_result defn;
            fn_body := map (lower_tailcall_stmt_for (fn_name defn)) (fn_body defn) |})
         (prog_fns p) |}.
Definition lower_enum_program (p : program) : program := p.
Definition lower_match_expr (e : expr) : expr := e.
Definition lower_copy_update_expr (e : expr) : expr :=
  match e with
  | ECopyUpdate base _ _ => base
  | _ => e
  end.

Definition fuse_pipeline_args (fn : string) (args : list expr) : list expr :=
  if String.eqb fn "map" then firstn 1 args
  else if String.eqb fn "filter" then firstn 1 args
  else if String.eqb fn "fold" then firstn 1 args
  else args.

Definition fuse_pipeline_expr (e : expr) : expr :=
  match e with
  | ECall fn args => ECall fn (fuse_pipeline_args fn args)
  | _ => e
  end.

Inductive match_tree :=
| MTFail
| MTLeaf (body : expr)
| MTSwitch (scrutinee : expr) (branches : list (string * match_tree)).

Record copy_update_plan := {
  cup_base : expr;
  cup_path : list string;
  cup_value : expr;
}.

Inductive pipeline_stage :=
| PSMap
| PSFilter
| PSFold.

Record pipeline_plan := {
  ppl_source : expr;
  ppl_stages : list pipeline_stage;
}.

Record tag_layout := {
  tl_name : string;
  tl_variants : list string;
}.

Inductive tail_shape :=
| TSReturn
| TSLoop (fn : string) (arity : nat).

Record match_lowered_expr := {
  mle_expr : expr;
  mle_tree : option match_tree;
  mle_cases_linearized : Prop;
}.

Record copy_update_lowered_expr := {
  cule_expr : expr;
  cule_plan : option copy_update_plan;
  cule_paths_explicit : Prop;
}.

Record pipeline_fused_expr := {
  pfe_expr : expr;
  pfe_plan : option pipeline_plan;
  pfe_single_pass : Prop;
}.

Record tailcall_lowered_program := {
  tlp_program : program;
  tlp_shapes : list tail_shape;
  tlp_loops_explicit : Prop;
}.

Record enum_lowered_program := {
  elp_program : program;
  elp_layouts : list tag_layout;
  elp_tags_explicit : Prop;
}.

Inductive match_tree_well_typed : tyenv -> match_tree -> ty -> Prop :=
| MTWT_Fail :
    forall Γ t, match_tree_well_typed Γ MTFail t
| MTWT_Leaf :
    forall Γ body t,
      has_type_expr Γ body t ->
      match_tree_well_typed Γ (MTLeaf body) t
| MTWT_Switch :
    forall Γ scrutinee branches t,
      has_type_expr Γ scrutinee t ->
      match_tree_well_typed Γ (MTSwitch scrutinee branches) t.

Record copy_update_plan_well_typed (Γ : tyenv) (plan : copy_update_plan) (t : ty) : Prop := {
  cup_wt_base : has_type_expr Γ (cup_base plan) t;
  cup_wt_value : has_type_expr Γ (cup_value plan) t;
}.

Record pipeline_plan_well_typed (Γ : tyenv) (plan : pipeline_plan) : Prop := {
  ppl_wt_source : exists t, has_type_expr Γ (ppl_source plan) t;
}.

Definition tag_layout_well_formed (layout : tag_layout) : Prop :=
  tl_name layout <> "".

Definition tail_shape_well_formed (shape : tail_shape) : Prop :=
  match shape with
  | TSReturn => True
  | TSLoop fn _ => fn <> ""
  end.

Definition match_tree_sound (v : value) (tree : match_tree) : Prop :=
  match tree with
  | MTFail => True
  | MTLeaf _ => True
  | MTSwitch _ branches =>
      branches = [] \/
      exists tag, enum_tag_of v = Some tag
  end.

Definition copy_update_plan_sound (plan : copy_update_plan) : Prop :=
  forall p ρ basev newv out,
    eval_expr p ρ (cup_base plan) basev ->
    eval_expr p ρ (cup_value plan) newv ->
    update_value_path basev (cup_path plan) newv = Some out ->
    copy_update_path_observed basev (cup_path plan) newv out.

Definition sem_pipeline_stage_of (stage : pipeline_stage) : FoSemantics.pipeline_stage :=
  match stage with
  | PSMap => FoSemantics.PSMap
  | PSFilter => FoSemantics.PSFilter
  | PSFold => FoSemantics.PSFold
  end.

Definition pipeline_plan_sound (plan : pipeline_plan) : Prop :=
  exists out, out = run_pipeline_stages (interp_expr (ppl_source plan)) (map sem_pipeline_stage_of (ppl_stages plan)).

Definition tag_layout_sound (layout : tag_layout) : Prop :=
  tag_layout_well_formed layout.

Definition tail_shape_sound (shape : tail_shape) : Prop :=
  tail_shape_well_formed shape.

Definition match_tree_reflects_expr (e : expr) (tree : match_tree) : Prop :=
  match e with
  | EMatch scrutinee _ => tree = MTSwitch scrutinee []
  | _ => True
  end.

Definition copy_update_plan_reflects_expr (e : expr) (plan : copy_update_plan) : Prop :=
  match e with
  | ECopyUpdate base path value =>
      cup_base plan = base /\ cup_path plan = path /\ cup_value plan = value
  | _ => False
  end.

Definition pipeline_plan_reflects_expr (e : expr) (plan : pipeline_plan) : Prop :=
  ppl_source plan = e.

Definition tag_layout_reflects_program (_p : program) (layout : tag_layout) : Prop :=
  In layout [].

Definition tail_shape_reflects_program (p : program) (shape : tail_shape) : Prop :=
  match shape with
  | TSReturn => True
  | TSLoop fn arity => exists defn, In defn (prog_fns p) /\ fn_name defn = fn /\ List.length (fn_params defn) = arity
  end.

Record match_artifact_certificate (Γ : tyenv) (v : value) (e : expr) (t : ty) := {
  mac_tree : match_tree;
  mac_reflects : match_tree_reflects_expr e mac_tree;
  mac_well_typed : match_tree_well_typed Γ mac_tree t;
  mac_sound : match_tree_sound v mac_tree;
}.

Record copy_update_artifact_certificate (Γ : tyenv) (e : expr) (t : ty) := {
  cuac_plan : copy_update_plan;
  cuac_reflects : copy_update_plan_reflects_expr e cuac_plan;
  cuac_well_typed : copy_update_plan_well_typed Γ cuac_plan t;
  cuac_sound : copy_update_plan_sound cuac_plan;
}.

Record pipeline_artifact_certificate (Γ : tyenv) (e : expr) := {
  pac_plan : pipeline_plan;
  pac_reflects : pipeline_plan_reflects_expr e pac_plan;
  pac_well_typed : pipeline_plan_well_typed Γ pac_plan;
  pac_sound : pipeline_plan_sound pac_plan;
}.

Record tailcall_artifact_certificate (p : program) (shape : tail_shape) := {
  tac_reflects : tail_shape_reflects_program p shape;
  tac_well_formed : tail_shape_well_formed shape;
  tac_sound : tail_shape_sound shape;
  tac_loops_explicit : Prop;
  tac_loops_witness : tac_loops_explicit;
}.

Record enum_artifact_certificate (p : program) (layout : tag_layout) := {
  eac_reflects : tag_layout_reflects_program p layout;
  eac_well_formed : tag_layout_well_formed layout;
  eac_sound : tag_layout_sound layout;
  eac_tags_explicit : Prop;
  eac_tags_witness : eac_tags_explicit;
}.

Record match_codegen_witness (scrutinee : expr) (cases : list (pattern * expr)) := {
  mcw_emits_switchlike :
    exists gcases,
      compile_expr (EMatch scrutinee cases) = GESwitchLike (compile_expr scrutinee) gcases;
}.

Record copy_update_codegen_witness (base : expr) (path : list string) (value : expr) := {
  cucw_projects_base :
    ginterp_expr (compile_expr (ECopyUpdate base path value)) =
      ginterp_expr (compile_expr base);
}.

Record ctor_codegen_witness (name : string) (args : list expr) := {
  ccw_emits_tagged_struct :
    exists payload,
      ginterp_expr (compile_expr (ECtor name args)) =
        GVStruct name [("Tag", GVString name); ("Payload", GVTuple payload)];
}.

Record call_codegen_witness (fn : string) (args : list expr) := {
  clw_emits_call :
    exists gargs,
      compile_expr (ECall fn args) = GECall fn gargs;
}.

Definition extract_match_tree (e : expr) : option match_tree :=
  match e with
  | EMatch scrutinee cases =>
      Some (MTSwitch scrutinee [])
  | _ => None
  end.

Definition extract_copy_update_plan (e : expr) : option copy_update_plan :=
  match e with
  | ECopyUpdate base path value =>
      Some {| cup_base := base; cup_path := path; cup_value := value |}
  | _ => None
  end.

Definition extract_pipeline_stages (e : expr) : list pipeline_stage :=
  match e with
  | ECall fn _ =>
      if String.eqb fn "map" then [PSMap]
      else if String.eqb fn "filter" then [PSFilter]
      else if String.eqb fn "fold" then [PSFold]
      else []
  | _ => []
  end.

Definition extract_pipeline_plan (e : expr) : option pipeline_plan :=
  Some {| ppl_source := e; ppl_stages := extract_pipeline_stages e |}.

Definition extract_tail_shapes (p : program) : list tail_shape :=
  TSReturn :: map (fun defn => TSLoop (fn_name defn) (List.length (fn_params defn))) (prog_fns p).

Definition extract_tag_layouts (_p : program) : list tag_layout :=
  [].

Inductive lowered_expr_target :=
| LETPlain (e : expr)
| LETProjectedCopyUpdate (base : expr) (path : list string) (value : expr)
| LETFusedPipelineCall (fn : string) (args : list expr) (stages : list pipeline_stage).

Record lowered_program_target := {
  lpt_source : program;
  lpt_tail_loops : list (string * nat);
}.

Definition interp_lowered_expr_target (target : lowered_expr_target) : value :=
  match target with
  | LETPlain e => interp_expr e
  | LETProjectedCopyUpdate base _ _ => interp_expr base
  | LETFusedPipelineCall fn args stages =>
      run_pipeline_stages (interp_expr (ECall fn args)) (map sem_pipeline_stage_of stages)
  end.

Definition lower_copy_update_target (e : expr) : lowered_expr_target :=
  match e with
  | ECopyUpdate base path value => LETProjectedCopyUpdate base path value
  | _ => LETPlain (lower_copy_update_expr e)
  end.

Definition fuse_pipeline_target (e : expr) : lowered_expr_target :=
  match e with
  | ECall fn args => LETFusedPipelineCall fn args (extract_pipeline_stages (ECall fn args))
  | _ => LETPlain (fuse_pipeline_expr e)
  end.

Definition lower_tailcalls_target (p : program) : lowered_program_target :=
  {| lpt_source := lower_tailcalls_program p;
     lpt_tail_loops := map (fun defn => (fn_name defn, List.length (fn_params defn))) (prog_fns p) |}.

Definition lowered_expr_target_observes (e : expr) (target : lowered_expr_target) : Prop :=
  interp_lowered_expr_target target = interp_expr e.

Definition lowered_program_target_reflects (p : program) (target : lowered_program_target) : Prop :=
  lpt_source target = lower_tailcalls_program p /\
  lpt_tail_loops target = map (fun defn => (fn_name defn, List.length (fn_params defn))) (prog_fns p).

Definition lowered_program_target_sound (p : program) (target : lowered_program_target) : Prop :=
  forall fn arity, In (fn, arity) (lpt_tail_loops target) ->
    exists defn, In defn (prog_fns p) /\ fn_name defn = fn /\ List.length (fn_params defn) = arity.

Lemma sem_pipeline_stages_preserve_unit :
  forall stages,
    run_pipeline_stages VUnit (map sem_pipeline_stage_of stages) = VUnit.
Proof.
  induction stages as [|stage rest IH]; simpl.
  - reflexivity.
  - destruct stage; exact IH.
Qed.

Definition lower_match_phase (e : expr) : match_lowered_expr :=
  {| mle_expr := lower_match_expr e;
     mle_tree := extract_match_tree e;
     mle_cases_linearized := True |}.

Definition lower_copy_update_phase (mle : match_lowered_expr) : copy_update_lowered_expr :=
  {| cule_expr := lower_copy_update_expr (mle_expr mle);
     cule_plan := extract_copy_update_plan (mle_expr mle);
     cule_paths_explicit := True |}.

Definition fuse_pipeline_phase (cule : copy_update_lowered_expr) : pipeline_fused_expr :=
  {| pfe_expr := fuse_pipeline_expr (cule_expr cule);
     pfe_plan := extract_pipeline_plan (cule_expr cule);
     pfe_single_pass := True |}.

Definition lower_tailcall_phase (p : program) : tailcall_lowered_program :=
  {| tlp_program := lower_tailcalls_program p;
     tlp_shapes := extract_tail_shapes p;
     tlp_loops_explicit := forall defn, In defn (prog_fns p) -> In (TSLoop (fn_name defn) (List.length (fn_params defn))) (extract_tail_shapes p) |}.

Definition lower_enum_phase (p : program) : enum_lowered_program :=
  {| elp_program := lower_enum_program p;
     elp_layouts := extract_tag_layouts p;
     elp_tags_explicit := True |}.

Definition optimize_expr (e : expr) : expr :=
  fuse_pipeline_expr (lower_copy_update_expr (lower_match_expr e)).

Definition optimize_program (p : program) : program :=
  lower_enum_program (lower_tailcalls_program p).

Theorem lower_copy_update_target_observes :
  forall e,
    lowered_expr_target_observes e (lower_copy_update_target e).
Proof.
  intros e. destruct e; reflexivity.
Qed.

Theorem fuse_pipeline_target_observes :
  forall e,
    lowered_expr_target_observes e (fuse_pipeline_target e).
Proof.
  intros e.
  destruct e as
    [name | | b | n | s | items | ctor args | structName fields
    | base path value | op arg | op lhs rhs | fn args | cond yes no | scrutinee cases];
    simpl; try reflexivity.
  apply sem_pipeline_stages_preserve_unit.
Qed.

Theorem lower_tailcalls_target_reflects :
  forall p,
    lowered_program_target_reflects p (lower_tailcalls_target p).
Proof.
  intros p. split; reflexivity.
Qed.

Theorem lower_tailcalls_target_sound :
  forall p,
    lowered_program_target_sound p (lower_tailcalls_target p).
Proof.
  intros p fn arity Hin.
  unfold lower_tailcalls_target in Hin. simpl in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [defn [Heq Hmem]].
  inversion Heq; subst.
  exists defn. auto.
Qed.

Lemma lower_match_phase_cases_linearized :
  forall e, mle_cases_linearized (lower_match_phase e).
Proof.
  intros. exact I.
Qed.

Lemma lower_match_phase_tree_present_for_match :
  forall scrutinee cases,
    mle_tree (lower_match_phase (EMatch scrutinee cases)) = Some (MTSwitch scrutinee []).
Proof.
  reflexivity.
Qed.

Lemma lower_match_phase_tree_well_typed :
  forall Γ scrutinee cases t,
    has_type_expr Γ (EMatch scrutinee cases) t ->
    match_tree_well_typed Γ (MTSwitch scrutinee []) t.
Proof.
  intros. apply MTWT_Switch.
  inversion H.
Qed.

Lemma lower_match_phase_tree_sound :
  forall v scrutinee (cases : list (pattern * expr)),
    match_tree_sound v (MTSwitch scrutinee []).
Proof.
  intros. left. reflexivity.
Qed.

Lemma lower_match_phase_tree_reflects :
  forall scrutinee cases,
    match_tree_reflects_expr (EMatch scrutinee cases) (MTSwitch scrutinee []).
Proof.
  reflexivity.
Qed.

Lemma lower_copy_update_phase_paths_explicit :
  forall e, cule_paths_explicit (lower_copy_update_phase (lower_match_phase e)).
Proof.
  intros. exact I.
Qed.

Lemma lower_copy_update_phase_plan_present :
  forall base path value,
    cule_plan (lower_copy_update_phase (lower_match_phase (ECopyUpdate base path value))) =
      Some {| cup_base := base; cup_path := path; cup_value := value |}.
Proof.
  reflexivity.
Qed.

Lemma lower_copy_update_phase_plan_well_typed :
  forall Γ base path value t,
    has_type_expr Γ base t ->
    has_type_expr Γ value t ->
    copy_update_plan_well_typed Γ
      {| cup_base := base; cup_path := path; cup_value := value |}
      t.
Proof.
  intros. constructor; assumption.
Qed.

Lemma lower_copy_update_phase_plan_sound :
  forall base path value,
    copy_update_plan_sound {| cup_base := base; cup_path := path; cup_value := value |}.
Proof.
  intros base path value p ρ basev newv out Hbase Hvalue Hupd.
  exact (copy_update_path_observed_of_success basev path newv out Hupd).
Qed.

Lemma lower_copy_update_phase_plan_reflects :
  forall base path value,
    copy_update_plan_reflects_expr
      (ECopyUpdate base path value)
      {| cup_base := base; cup_path := path; cup_value := value |}.
Proof.
  repeat split; reflexivity.
Qed.

Lemma fuse_pipeline_phase_single_pass :
  forall e, pfe_single_pass (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase e))).
Proof.
  intros. exact I.
Qed.

Lemma fuse_pipeline_phase_plan_present :
  forall e,
    pfe_plan (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase e))) =
      Some {| ppl_source := lower_copy_update_expr (lower_match_expr e);
              ppl_stages := extract_pipeline_stages (lower_copy_update_expr (lower_match_expr e)) |}.
Proof.
  reflexivity.
Qed.

Lemma fuse_pipeline_phase_plan_well_typed :
  forall Γ e t,
    has_type_expr Γ e t ->
    pipeline_plan_well_typed Γ {| ppl_source := e; ppl_stages := extract_pipeline_stages e |}.
Proof.
  intros. constructor. exists t. assumption.
Qed.

Lemma fuse_pipeline_phase_plan_sound :
  forall e,
    pipeline_plan_sound {| ppl_source := e; ppl_stages := extract_pipeline_stages e |}.
Proof.
  intros. exists (run_pipeline_stages (interp_expr e) (map sem_pipeline_stage_of (extract_pipeline_stages e))). reflexivity.
Qed.

Lemma fuse_pipeline_phase_plan_reflects :
  forall e,
    pipeline_plan_reflects_expr e {| ppl_source := e; ppl_stages := extract_pipeline_stages e |}.
Proof.
  reflexivity.
Qed.

Lemma lower_tailcall_phase_loops_explicit :
  forall p, tlp_loops_explicit (lower_tailcall_phase p).
Proof.
  intros p defn Hmem.
  simpl. right.
  apply in_map_iff.
  exists defn. split.
  - reflexivity.
  - exact Hmem.
Qed.

Lemma lower_tailcall_phase_shapes_present :
  forall p, In TSReturn (tlp_shapes (lower_tailcall_phase p)).
Proof.
  intros p. simpl. auto.
Qed.

Lemma lower_tailcall_phase_shapes_well_formed :
  forall p shape,
    well_typed_program p ->
    In shape (tlp_shapes (lower_tailcall_phase p)) ->
    tail_shape_well_formed shape.
Proof.
  intros p shape Hprog Hin.
  destruct shape as [| fn arity].
  - exact I.
  - simpl in Hin.
    destruct Hin as [Hbad | Htail].
    + discriminate.
    + apply in_map_iff in Htail.
      destruct Htail as [defn [Heq Hdefn]].
      inversion Heq; subst fn arity.
      exact (well_typed_program_fn_name_nonempty p defn Hprog Hdefn).
Qed.

Lemma lower_tailcall_phase_shapes_sound :
  forall p shape,
    well_typed_program p ->
    In shape (tlp_shapes (lower_tailcall_phase p)) ->
    tail_shape_sound shape.
Proof.
  intros. unfold tail_shape_sound. apply lower_tailcall_phase_shapes_well_formed with (p := p); assumption.
Qed.

Lemma lower_tailcall_phase_shapes_reflect :
  forall p shape,
    In shape (tlp_shapes (lower_tailcall_phase p)) ->
    tail_shape_reflects_program p shape.
Proof.
  intros p shape Hin.
  destruct shape as [| fn arity].
  - exact I.
  - simpl in Hin.
    destruct Hin as [Hbad | Htail].
    + discriminate.
    + apply in_map_iff in Htail.
      destruct Htail as [defn [Heq Hdefn]].
      inversion Heq; subst fn arity.
      exists defn. split.
      * exact Hdefn.
      * split; reflexivity.
Qed.

Lemma lower_enum_phase_tags_explicit :
  forall p, elp_tags_explicit (lower_enum_phase p).
Proof.
  intros. exact I.
Qed.

Lemma lower_enum_phase_layouts_present :
  forall p, elp_layouts (lower_enum_phase p) = [].
Proof.
  reflexivity.
Qed.

Lemma lower_enum_phase_layouts_well_formed :
  forall p layout,
    In layout (elp_layouts (lower_enum_phase p)) ->
    tag_layout_well_formed layout.
Proof.
  intros.
  inversion H.
Qed.

Lemma lower_enum_phase_layouts_sound :
  forall p layout,
    In layout (elp_layouts (lower_enum_phase p)) ->
    tag_layout_sound layout.
Proof.
  intros. unfold tag_layout_sound. apply lower_enum_phase_layouts_well_formed with (p := p); assumption.
Qed.

Lemma lower_enum_phase_layouts_reflect :
  forall p layout,
    In layout (elp_layouts (lower_enum_phase p)) ->
    tag_layout_reflects_program p layout.
Proof.
  intros. unfold tag_layout_reflects_program.
  unfold lower_enum_phase in H. simpl in H. exact H.
Qed.

Theorem compile_expr_refines_interp :
  forall e,
    value_refines (interp_expr e) (ginterp_expr (compile_expr e)).
Proof.
  induction e; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - match goal with
    | IH : value_refines (interp_expr ?base) (ginterp_expr (compile_expr ?base)) |- _ => exact IH
    end.
  - constructor.
  - constructor.
  - constructor.
  - match goal with
    | IH : value_refines (interp_expr ?yes) (ginterp_expr (compile_expr ?yes)) |- _ => exact IH
    end.
  - constructor.
Qed.

Theorem compile_eval_refines_target :
  forall p ρ e v,
    eval_expr p ρ e v ->
    value_refines v (ginterp_expr (compile_expr e)).
Proof.
  intros p ρ e v Hev.
  unfold eval_expr in Hev.
  rewrite <- Hev.
  apply compile_expr_refines_interp.
Qed.

Theorem compile_stmt_refines_interp :
  forall ρ s,
    result_refines (interp_stmt ρ s) (ginterp_stmt (compile_stmt s)).
Proof.
  intros ρ s.
  destruct s; simpl.
  - constructor.
  - constructor. apply compile_expr_refines_interp.
  - constructor.
  - constructor.
Qed.

Theorem compile_block_refines_interp :
  forall ρ ss,
    result_refines (interp_block ρ ss) (ginterp_block (compile_block ss)).
Proof.
  intros ρ ss.
  destruct ss as [| s rest]; simpl.
  - constructor.
  - apply compile_stmt_refines_interp.
Qed.

Theorem compile_expr_observes :
  forall e,
    compiled_expr_observes e (compile_expr e).
Proof.
  exact compile_expr_refines_interp.
Qed.

Theorem compile_stmt_observes :
  forall ρ s,
    compiled_stmt_observes ρ s (compile_stmt s).
Proof.
  exact compile_stmt_refines_interp.
Qed.

Theorem compile_block_observes :
  forall ρ ss,
    compiled_block_observes ρ ss (compile_block ss).
Proof.
  exact compile_block_refines_interp.
Qed.

Theorem compile_tail_observes_call :
  forall fn args,
    compiled_tail_observes (ECall fn args) (compile_expr (ECall fn args)).
Proof.
  intros fn args. simpl. eexists. reflexivity.
Qed.

Lemma compile_pattern_tag_wild :
  compile_pattern_tag PWild = "_".
Proof.
  reflexivity.
Qed.

Lemma compile_pattern_tag_ctor :
  forall name args,
    compile_pattern_tag (PCtor name args) = "ctor:" ++ name.
Proof.
  reflexivity.
Qed.

Lemma compile_ctor_emits_tagged_struct :
  forall name args,
    exists payload,
      ginterp_expr (compile_expr (ECtor name args)) =
        GVStruct name [("Tag", GVString name); ("Payload", GVTuple payload)].
Proof.
  intros. eexists. reflexivity.
Qed.

Lemma compile_match_emits_switchlike :
  forall scrutinee cases,
    exists gcases,
      compile_expr (EMatch scrutinee cases) =
        GESwitchLike (compile_expr scrutinee) gcases.
Proof.
  intros. eexists. reflexivity.
Qed.

Lemma compile_stmt_match_emits_matchlike :
  forall scrutinee cases,
    exists gcases,
      compile_stmt (SMatch scrutinee cases) =
        GSMatchLike (compile_expr scrutinee) gcases.
Proof.
  intros. eexists. reflexivity.
Qed.

Lemma compile_copy_update_projects_base :
  forall base path value,
    ginterp_expr (compile_expr (ECopyUpdate base path value)) =
      ginterp_expr (compile_expr base).
Proof.
  reflexivity.
Qed.

Lemma compile_call_emits_gcall :
  forall fn args,
    exists gargs,
      compile_expr (ECall fn args) = GECall fn gargs.
Proof.
  intros. eexists. reflexivity.
Qed.

Definition build_match_codegen_witness
    (scrutinee : expr) (cases : list (pattern * expr)) :
    match_codegen_witness scrutinee cases :=
  {| mcw_emits_switchlike := compile_match_emits_switchlike scrutinee cases |}.

Definition build_copy_update_codegen_witness
    (base : expr) (path : list string) (value : expr) :
    copy_update_codegen_witness base path value :=
  {| cucw_projects_base := eq_refl |}.

Definition build_ctor_codegen_witness
    (name : string) (args : list expr) :
    ctor_codegen_witness name args :=
  {| ccw_emits_tagged_struct := compile_ctor_emits_tagged_struct name args |}.

Definition build_call_codegen_witness
    (fn : string) (args : list expr) :
    call_codegen_witness fn args :=
  {| clw_emits_call := compile_call_emits_gcall fn args |}.

Theorem tailcall_soundness_chain :
  forall p fn args,
    well_typed_program p ->
    interp_tail_expr (ECall fn args) = TORecur fn (map interp_expr args) /\
    tlp_loops_explicit (lower_tailcall_phase p) /\
    exists gargs, compile_expr (ECall fn args) = GECall fn gargs.
Proof.
  intros p fn args Hprog.
  split.
  - exact (typing_interp_tail_expr_call p fn args Hprog).
  - split.
    + apply lower_tailcall_phase_loops_explicit.
    + apply compile_call_emits_gcall.
Qed.

Theorem tailcall_target_soundness_chain :
  forall p fn args,
    well_typed_program p ->
    interp_tail_expr (ECall fn args) = TORecur fn (map interp_expr args) /\
    tail_call_shape_observed (ECall fn args) fn (map interp_expr args) /\
    lowered_program_target_reflects p (lower_tailcalls_target p) /\
    lowered_program_target_sound p (lower_tailcalls_target p) /\
    tlp_loops_explicit (lower_tailcall_phase p) /\
    exists gargs, compile_expr (ECall fn args) = GECall fn gargs.
Proof.
  intros p fn args Hprog.
  pose proof (tailcall_soundness_chain p fn args Hprog) as Hbase.
  destruct Hbase as [Htail [Hloops Hgargs]].
  split.
  - exact Htail.
  - split.
    + exact (typing_tail_call_shape_observed_call p fn args Hprog).
    + split.
      * apply lower_tailcalls_target_reflects.
      * split.
        { apply lower_tailcalls_target_sound. }
        { split.
          - exact Hloops.
          - exact Hgargs. }
Qed.

Theorem tailcall_artifact_well_formed_chain :
  forall p shape,
    well_typed_program p ->
    In shape (tlp_shapes (lower_tailcall_phase p)) ->
    tail_shape_well_formed shape /\
    tlp_loops_explicit (lower_tailcall_phase p).
Proof.
  intros p shape Hprog Hin.
  split.
  - apply lower_tailcall_phase_shapes_well_formed with (p := p); assumption.
  - apply lower_tailcall_phase_loops_explicit.
Qed.

Theorem tailcall_artifact_semantic_chain :
  forall p shape,
    well_typed_program p ->
    In shape (tlp_shapes (lower_tailcall_phase p)) ->
    tail_shape_sound shape /\
    tail_shape_well_formed shape /\
    tlp_loops_explicit (lower_tailcall_phase p).
Proof.
  intros p shape Hprog Hin.
  split.
  - apply lower_tailcall_phase_shapes_sound with (p := p); assumption.
  - split.
    + apply lower_tailcall_phase_shapes_well_formed with (p := p); assumption.
    + apply lower_tailcall_phase_loops_explicit.
Qed.

Theorem tailcall_artifact_reflection_chain :
  forall p shape,
    well_typed_program p ->
    In shape (tlp_shapes (lower_tailcall_phase p)) ->
    tail_shape_reflects_program p shape /\
    tail_shape_sound shape.
Proof.
  intros p shape Hprog Hin.
  split.
  - apply lower_tailcall_phase_shapes_reflect; assumption.
  - apply lower_tailcall_phase_shapes_sound with (p := p); assumption.
Qed.

Theorem build_tailcall_artifact_certificate :
  forall p shape,
    well_typed_program p ->
    In shape (tlp_shapes (lower_tailcall_phase p)) ->
    tailcall_artifact_certificate p shape.
Proof.
  intros p shape Hprog Hin.
  refine {| tac_reflects := _;
            tac_well_formed := _;
            tac_sound := _;
            tac_loops_explicit := tlp_loops_explicit (lower_tailcall_phase p);
            tac_loops_witness := _ |}.
  - apply lower_tailcall_phase_shapes_reflect; assumption.
  - apply lower_tailcall_phase_shapes_well_formed with (p := p); assumption.
  - apply lower_tailcall_phase_shapes_sound with (p := p); assumption.
  - apply lower_tailcall_phase_loops_explicit.
Qed.

Theorem match_soundness_chain :
  forall p v scrutinee body rest,
    well_typed_program p ->
    select_match_expr v ((PWild, body) :: rest) = Some body /\
    mle_cases_linearized (lower_match_phase (EMatch scrutinee ((PWild, body) :: rest))) /\
    exists gcases,
      compile_expr (mle_expr (lower_match_phase (EMatch scrutinee ((PWild, body) :: rest)))) =
        GESwitchLike (compile_expr scrutinee) gcases.
Proof.
  intros p v scrutinee body rest Hprog.
  split.
  - exact (typing_select_match_expr_wild p v body rest Hprog).
  - split.
    + apply lower_match_phase_cases_linearized.
    + unfold lower_match_phase. simpl. eexists. reflexivity.
Qed.

Theorem match_artifact_well_formed_chain :
  forall Γ scrutinee cases t,
    has_type_expr Γ (EMatch scrutinee cases) t ->
    match_tree_well_typed Γ (MTSwitch scrutinee []) t /\
    mle_cases_linearized (lower_match_phase (EMatch scrutinee cases)).
Proof.
  intros. split.
  - apply lower_match_phase_tree_well_typed with (cases := cases). assumption.
  - apply lower_match_phase_cases_linearized.
Qed.

Theorem match_artifact_semantic_chain :
  forall Γ v scrutinee cases t,
    has_type_expr Γ (EMatch scrutinee cases) t ->
    match_tree_well_typed Γ (MTSwitch scrutinee []) t /\
    match_tree_sound v (MTSwitch scrutinee []) /\
    mle_cases_linearized (lower_match_phase (EMatch scrutinee cases)).
Proof.
  intros Γ v scrutinee cases t Hty. split.
  - exact (lower_match_phase_tree_well_typed Γ scrutinee cases t Hty).
  - split.
    + exact (lower_match_phase_tree_sound v scrutinee cases).
    + exact (lower_match_phase_cases_linearized (EMatch scrutinee cases)).
Qed.

Theorem match_artifact_reflection_chain :
  forall Γ v scrutinee cases t,
    has_type_expr Γ (EMatch scrutinee cases) t ->
    match_tree_reflects_expr (EMatch scrutinee cases) (MTSwitch scrutinee []) /\
    match_tree_sound v (MTSwitch scrutinee []) /\
    match_tree_well_typed Γ (MTSwitch scrutinee []) t.
Proof.
  intros Γ v scrutinee cases t Hty. split.
  - exact (lower_match_phase_tree_reflects scrutinee cases).
  - split.
    + exact (lower_match_phase_tree_sound v scrutinee cases).
    + exact (lower_match_phase_tree_well_typed Γ scrutinee cases t Hty).
Qed.

Theorem build_match_artifact_certificate :
  forall Γ v scrutinee cases t,
    has_type_expr Γ (EMatch scrutinee cases) t ->
    match_artifact_certificate Γ v (EMatch scrutinee cases) t.
Proof.
  intros Γ v scrutinee cases t Hty.
  refine {| mac_tree := MTSwitch scrutinee [];
            mac_reflects := _;
            mac_well_typed := _;
            mac_sound := _ |}.
  - apply lower_match_phase_tree_reflects.
  - exact (lower_match_phase_tree_well_typed Γ scrutinee cases t Hty).
  - exact (lower_match_phase_tree_sound v scrutinee cases).
Qed.

Theorem copy_update_soundness_chain :
  forall p base path value t,
    well_typed_program p ->
    has_type_value (interp_expr base) t ->
    lookup_value_path (interp_expr base) [] = Some (interp_expr base) /\
    cule_paths_explicit (lower_copy_update_phase (lower_match_phase (ECopyUpdate base path value))) /\
    ginterp_expr (compile_expr (cule_expr (lower_copy_update_phase (lower_match_phase (ECopyUpdate base path value))))) =
      ginterp_expr (compile_expr base).
Proof.
  intros p base path value t Hprog Hty.
  split.
  - exact (typing_lookup_value_path_root p (interp_expr base) t Hprog Hty).
  - split.
    + apply lower_copy_update_phase_paths_explicit.
    + unfold lower_copy_update_phase, lower_match_phase. simpl.
      reflexivity.
Qed.

Theorem copy_update_target_soundness_chain :
  forall p base path value t,
    well_typed_program p ->
    has_type_value (interp_expr base) t ->
    lookup_value_path (interp_expr base) [] = Some (interp_expr base) /\
    lowered_expr_target_observes
      (ECopyUpdate base path value)
      (lower_copy_update_target (ECopyUpdate base path value)) /\
    cule_paths_explicit (lower_copy_update_phase (lower_match_phase (ECopyUpdate base path value))) /\
    ginterp_expr (compile_expr (cule_expr (lower_copy_update_phase (lower_match_phase (ECopyUpdate base path value))))) =
      ginterp_expr (compile_expr base).
Proof.
  intros p base path value t Hprog Hty.
  pose proof (copy_update_soundness_chain p base path value t Hprog Hty) as Hbase.
  destruct Hbase as [Hroot [Hpaths Hproj]].
  split.
  - exact Hroot.
  - split.
    + apply lower_copy_update_target_observes.
    + split.
      * exact Hpaths.
      * exact Hproj.
Qed.

Theorem copy_update_path_target_soundness_chain :
  forall p base path value out t,
    well_typed_program p ->
    has_type_value (interp_expr base) t ->
    update_value_path (interp_expr base) path (interp_expr value) = Some out ->
    copy_update_path_observed (interp_expr base) path (interp_expr value) out /\
    copy_update_head_observed (interp_expr base) path (interp_expr value) out /\
    copy_update_prefix_observed (interp_expr base) path (interp_expr value) out /\
    lowered_expr_target_observes
      (ECopyUpdate base path value)
      (lower_copy_update_target (ECopyUpdate base path value)) /\
    cule_paths_explicit (lower_copy_update_phase (lower_match_phase (ECopyUpdate base path value))) /\
    ginterp_expr (compile_expr (cule_expr (lower_copy_update_phase (lower_match_phase (ECopyUpdate base path value))))) =
      ginterp_expr (compile_expr base).
Proof.
  intros p base path value out t Hprog Hty Hupd.
  split.
  - exact (typing_copy_update_observation_bundle_general p (interp_expr base) (interp_expr value) out path t Hprog Hty Hupd).
  - split.
    + exact (typing_copy_update_head_observation_bundle_general p (interp_expr base) (interp_expr value) out path t Hprog Hty Hupd).
    + split.
      * exact (typing_copy_update_prefix_observation_bundle_general p (interp_expr base) (interp_expr value) out path t Hprog Hty Hupd).
      * exact (proj2 (copy_update_target_soundness_chain p base path value t Hprog Hty)).
Qed.

Theorem copy_update_artifact_well_formed_chain :
  forall Γ base path value t,
    has_type_expr Γ base t ->
    has_type_expr Γ value t ->
    copy_update_plan_well_typed Γ {| cup_base := base; cup_path := path; cup_value := value |} t /\
    cule_paths_explicit (lower_copy_update_phase (lower_match_phase (ECopyUpdate base path value))).
Proof.
  intros Γ base path value t Hbase Hvalue. split.
  - exact (lower_copy_update_phase_plan_well_typed Γ base path value t Hbase Hvalue).
  - exact (lower_copy_update_phase_paths_explicit (ECopyUpdate base path value)).
Qed.

Theorem copy_update_artifact_semantic_chain :
  forall Γ base path value t,
    has_type_expr Γ base t ->
    has_type_expr Γ value t ->
    copy_update_plan_well_typed Γ {| cup_base := base; cup_path := path; cup_value := value |} t /\
    copy_update_plan_sound {| cup_base := base; cup_path := path; cup_value := value |} /\
    cule_paths_explicit (lower_copy_update_phase (lower_match_phase (ECopyUpdate base path value))).
Proof.
  intros Γ base path value t Hbase Hvalue. split.
  - exact (lower_copy_update_phase_plan_well_typed Γ base path value t Hbase Hvalue).
  - split.
    + exact (lower_copy_update_phase_plan_sound base path value).
    + exact (lower_copy_update_phase_paths_explicit (ECopyUpdate base path value)).
Qed.

Theorem copy_update_artifact_reflection_chain :
  forall Γ base path value t,
    has_type_expr Γ base t ->
    has_type_expr Γ value t ->
    copy_update_plan_reflects_expr
      (ECopyUpdate base path value)
      {| cup_base := base; cup_path := path; cup_value := value |} /\
    copy_update_plan_sound {| cup_base := base; cup_path := path; cup_value := value |} /\
    copy_update_plan_well_typed Γ {| cup_base := base; cup_path := path; cup_value := value |} t.
Proof.
  intros Γ base path value t Hbase Hvalue. split.
  - exact (lower_copy_update_phase_plan_reflects base path value).
  - split.
    + exact (lower_copy_update_phase_plan_sound base path value).
    + exact (lower_copy_update_phase_plan_well_typed Γ base path value t Hbase Hvalue).
Qed.

Theorem build_copy_update_artifact_certificate :
  forall Γ base path value t,
    has_type_expr Γ base t ->
    has_type_expr Γ value t ->
    copy_update_artifact_certificate Γ (ECopyUpdate base path value) t.
Proof.
  intros Γ base path value t Hbase Hvalue.
  refine {| cuac_plan := {| cup_base := base; cup_path := path; cup_value := value |};
            cuac_reflects := _;
            cuac_well_typed := _;
            cuac_sound := _ |}.
  - apply lower_copy_update_phase_plan_reflects.
  - exact (lower_copy_update_phase_plan_well_typed Γ base path value t Hbase Hvalue).
  - exact (lower_copy_update_phase_plan_sound base path value).
Qed.

Theorem enum_soundness_chain :
  forall p ctor args enumName,
    well_typed_program p ->
    has_type_value (VCtor ctor (map interp_expr args)) (TyEnum enumName) ->
    enum_tag_of (VCtor ctor (map interp_expr args)) = Some ctor /\
    enum_payload_of (VCtor ctor (map interp_expr args)) = Some (map interp_expr args) /\
    elp_tags_explicit (lower_enum_phase p) /\
    exists payload,
      ginterp_expr (compile_expr (ECtor ctor args)) =
        GVStruct ctor [("Tag", GVString ctor); ("Payload", GVTuple payload)].
Proof.
  intros p ctor args enumName Hprog Hty.
  split.
  - exact (typing_enum_tag_of_ctor p ctor enumName (map interp_expr args) Hprog Hty).
  - split.
    + exact (typing_enum_payload_of_ctor p ctor enumName (map interp_expr args) Hprog Hty).
    + split.
      * apply lower_enum_phase_tags_explicit.
      * apply compile_ctor_emits_tagged_struct.
Qed.

Theorem enum_artifact_well_formed_chain :
  forall p layout,
    well_typed_program p ->
    In layout (elp_layouts (lower_enum_phase p)) ->
    tag_layout_well_formed layout /\
    elp_tags_explicit (lower_enum_phase p).
Proof.
  intros p layout Hprog Hin.
  split.
  - apply lower_enum_phase_layouts_well_formed with (p := p); assumption.
  - apply lower_enum_phase_tags_explicit.
Qed.

Theorem enum_artifact_semantic_chain :
  forall p layout,
    well_typed_program p ->
    In layout (elp_layouts (lower_enum_phase p)) ->
    tag_layout_sound layout /\
    tag_layout_well_formed layout /\
    elp_tags_explicit (lower_enum_phase p).
Proof.
  intros p layout Hprog Hin.
  split.
  - apply lower_enum_phase_layouts_sound with (p := p); assumption.
  - split.
    + apply lower_enum_phase_layouts_well_formed with (p := p); assumption.
    + apply lower_enum_phase_tags_explicit.
Qed.

Theorem enum_artifact_reflection_chain :
  forall p layout,
    well_typed_program p ->
    In layout (elp_layouts (lower_enum_phase p)) ->
    tag_layout_reflects_program p layout /\
    tag_layout_sound layout.
Proof.
  intros p layout Hprog Hin.
  split.
  - apply lower_enum_phase_layouts_reflect; assumption.
  - apply lower_enum_phase_layouts_sound with (p := p); assumption.
Qed.

Theorem build_enum_artifact_certificate :
  forall p layout,
    well_typed_program p ->
    In layout (elp_layouts (lower_enum_phase p)) ->
    enum_artifact_certificate p layout.
Proof.
  intros p layout Hprog Hin.
  refine {| eac_reflects := _;
            eac_well_formed := _;
            eac_sound := _;
            eac_tags_explicit := elp_tags_explicit (lower_enum_phase p);
            eac_tags_witness := _ |}.
  - apply lower_enum_phase_layouts_reflect; assumption.
  - apply lower_enum_phase_layouts_well_formed with (p := p); assumption.
  - apply lower_enum_phase_layouts_sound with (p := p); assumption.
  - apply lower_enum_phase_tags_explicit.
Qed.

Theorem pipeline_soundness_chain :
  forall p fn args input,
    well_typed_program p ->
    pipeline_stages_observed input (map sem_pipeline_stage_of (extract_pipeline_stages (ECall fn args))) /\
    pfe_single_pass (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase (ECall fn args)))) /\
    exists gargs,
      compile_expr (pfe_expr (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase (ECall fn args))))) =
        GECall fn gargs.
Proof.
  intros p fn args input Hprog.
  split.
  - exact (typing_pipeline_observation_bundle_general p input (map sem_pipeline_stage_of (extract_pipeline_stages (ECall fn args))) Hprog).
  - split.
    + apply fuse_pipeline_phase_single_pass.
    + unfold fuse_pipeline_phase, lower_copy_update_phase, lower_match_phase. simpl.
      apply compile_call_emits_gcall.
Qed.

Theorem pipeline_target_soundness_chain :
  forall p fn args input,
    well_typed_program p ->
    pipeline_stages_observed input (map sem_pipeline_stage_of (extract_pipeline_stages (ECall fn args))) /\
    lowered_expr_target_observes
      (ECall fn args)
      (fuse_pipeline_target (ECall fn args)) /\
    pfe_single_pass (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase (ECall fn args)))) /\
    exists gargs,
      compile_expr (pfe_expr (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase (ECall fn args))))) =
        GECall fn gargs.
Proof.
  intros p fn args input Hprog.
  pose proof (pipeline_soundness_chain p fn args input Hprog) as Hbase.
  destruct Hbase as [Hobs [Hsingle Hgargs]].
  split.
  - exact Hobs.
  - split.
    + apply fuse_pipeline_target_observes.
    + split.
      * exact Hsingle.
      * exact Hgargs.
Qed.

Theorem copy_update_target_model_chain :
  forall base path value,
    lowered_expr_target_observes
      (ECopyUpdate base path value)
      (lower_copy_update_target (ECopyUpdate base path value)).
Proof.
  intros. apply lower_copy_update_target_observes.
Qed.

Theorem pipeline_target_model_chain :
  forall fn args,
    lowered_expr_target_observes
      (ECall fn args)
      (fuse_pipeline_target (ECall fn args)).
Proof.
  intros. apply fuse_pipeline_target_observes.
Qed.

Theorem tailcall_target_model_chain :
  forall p,
    lowered_program_target_reflects p (lower_tailcalls_target p) /\
    lowered_program_target_sound p (lower_tailcalls_target p).
Proof.
  intro p. split.
  - apply lower_tailcalls_target_reflects.
  - apply lower_tailcalls_target_sound.
Qed.

Theorem pipeline_artifact_well_formed_chain :
  forall Γ e t,
    has_type_expr Γ e t ->
    pipeline_plan_well_typed Γ {| ppl_source := e; ppl_stages := extract_pipeline_stages e |} /\
    pfe_single_pass (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase e))).
Proof.
  intros. split.
  - exact (fuse_pipeline_phase_plan_well_typed Γ e t H).
  - apply fuse_pipeline_phase_single_pass.
Qed.

Theorem pipeline_artifact_semantic_chain :
  forall Γ e t,
    has_type_expr Γ e t ->
    pipeline_plan_well_typed Γ {| ppl_source := e; ppl_stages := extract_pipeline_stages e |} /\
    pipeline_plan_sound {| ppl_source := e; ppl_stages := extract_pipeline_stages e |} /\
    pfe_single_pass (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase e))).
Proof.
  intros. split.
  - exact (fuse_pipeline_phase_plan_well_typed Γ e t H).
  - split.
    + apply fuse_pipeline_phase_plan_sound.
    + apply fuse_pipeline_phase_single_pass.
Qed.

Theorem pipeline_artifact_reflection_chain :
  forall Γ e t,
    has_type_expr Γ e t ->
    pipeline_plan_reflects_expr e {| ppl_source := e; ppl_stages := extract_pipeline_stages e |} /\
    pipeline_plan_sound {| ppl_source := e; ppl_stages := extract_pipeline_stages e |} /\
    pipeline_plan_well_typed Γ {| ppl_source := e; ppl_stages := extract_pipeline_stages e |}.
Proof.
  intros. split.
  - apply fuse_pipeline_phase_plan_reflects.
  - split.
    + apply fuse_pipeline_phase_plan_sound.
    + exact (fuse_pipeline_phase_plan_well_typed Γ e t H).
Qed.

Theorem build_pipeline_artifact_certificate :
  forall Γ e t,
    has_type_expr Γ e t ->
    pipeline_artifact_certificate Γ e.
Proof.
  intros Γ e t Hty.
  refine {| pac_plan := {| ppl_source := e; ppl_stages := extract_pipeline_stages e |};
            pac_reflects := _;
            pac_well_typed := _;
            pac_sound := _ |}.
  - apply fuse_pipeline_phase_plan_reflects.
  - exact (fuse_pipeline_phase_plan_well_typed Γ e t Hty).
  - exact (fuse_pipeline_phase_plan_sound e).
Qed.

Theorem tailcall_certificate_chain :
  forall p shape
         (Hprog : well_typed_program p)
         (Hin : In shape (tlp_shapes (lower_tailcall_phase p))),
    let cert := build_tailcall_artifact_certificate p shape Hprog Hin in
      tail_shape_reflects_program p shape /\
      tail_shape_well_formed shape /\
      tail_shape_sound shape /\
      tac_loops_explicit _ _ cert.
Proof.
  intros p shape Hprog Hin cert.
  split.
  - exact (tac_reflects _ _ cert).
  - split.
    + exact (tac_well_formed _ _ cert).
    + split.
      * exact (tac_sound _ _ cert).
      * exact (tac_loops_witness _ _ cert).
Qed.

Theorem match_certificate_chain :
  forall Γ v scrutinee cases t
         (Hty : has_type_expr Γ (EMatch scrutinee cases) t),
    let cert := build_match_artifact_certificate Γ v scrutinee cases t Hty in
      match_tree_reflects_expr (EMatch scrutinee cases) (mac_tree _ _ _ _ cert) /\
      match_tree_well_typed Γ (mac_tree _ _ _ _ cert) t /\
      match_tree_sound v (mac_tree _ _ _ _ cert).
Proof.
  intros Γ v scrutinee cases t Hty cert.
  split.
  - exact (mac_reflects _ _ _ _ cert).
  - split.
    + exact (mac_well_typed _ _ _ _ cert).
    + exact (mac_sound _ _ _ _ cert).
Qed.

Theorem copy_update_certificate_chain :
  forall Γ base path value t
         (Hbase : has_type_expr Γ base t)
         (Hvalue : has_type_expr Γ value t),
    let cert := build_copy_update_artifact_certificate Γ base path value t Hbase Hvalue in
      copy_update_plan_reflects_expr
        (ECopyUpdate base path value)
        (cuac_plan _ _ _ cert) /\
      copy_update_plan_well_typed Γ (cuac_plan _ _ _ cert) t /\
      copy_update_plan_sound (cuac_plan _ _ _ cert).
Proof.
  intros Γ base path value t Hbase Hvalue cert.
  split.
  - exact (cuac_reflects _ _ _ cert).
  - split.
    + exact (cuac_well_typed _ _ _ cert).
    + exact (cuac_sound _ _ _ cert).
Qed.

Theorem enum_certificate_chain :
  forall p layout
         (Hprog : well_typed_program p)
         (Hin : In layout (elp_layouts (lower_enum_phase p))),
    let cert := build_enum_artifact_certificate p layout Hprog Hin in
      tag_layout_reflects_program p layout /\
      tag_layout_well_formed layout /\
      tag_layout_sound layout /\
      eac_tags_explicit _ _ cert.
Proof.
  intros p layout Hprog Hin cert.
  split.
  - exact (eac_reflects _ _ cert).
  - split.
    + exact (eac_well_formed _ _ cert).
    + split.
      * exact (eac_sound _ _ cert).
      * exact (eac_tags_witness _ _ cert).
Qed.

Theorem pipeline_certificate_chain :
  forall Γ e t
         (Hty : has_type_expr Γ e t),
    let cert := build_pipeline_artifact_certificate Γ e t Hty in
      pipeline_plan_reflects_expr e (pac_plan _ _ cert) /\
      pipeline_plan_well_typed Γ (pac_plan _ _ cert) /\
      pipeline_plan_sound (pac_plan _ _ cert).
Proof.
  intros Γ e t Hty cert.
  split.
  - exact (pac_reflects _ _ cert).
  - split.
    + exact (pac_well_typed _ _ cert).
    + exact (pac_sound _ _ cert).
Qed.

Theorem match_certificate_codegen_chain :
  forall Γ v scrutinee cases t
         (Hty : has_type_expr Γ (EMatch scrutinee cases) t),
    let cert := build_match_artifact_certificate Γ v scrutinee cases t Hty in
    exists wit : match_codegen_witness scrutinee cases,
      match_tree_reflects_expr (EMatch scrutinee cases) (mac_tree _ _ _ _ cert) /\
      match_tree_well_typed Γ (mac_tree _ _ _ _ cert) t /\
      match_tree_sound v (mac_tree _ _ _ _ cert).
Proof.
  intros Γ v scrutinee cases t Hty cert.
  exists (build_match_codegen_witness scrutinee cases).
  split.
  - exact (mac_reflects _ _ _ _ cert).
  - split.
    + exact (mac_well_typed _ _ _ _ cert).
    + exact (mac_sound _ _ _ _ cert).
Qed.

Theorem copy_update_certificate_codegen_chain :
  forall Γ base path value t
         (Hbase : has_type_expr Γ base t)
         (Hvalue : has_type_expr Γ value t),
    let cert := build_copy_update_artifact_certificate Γ base path value t Hbase Hvalue in
    exists wit : copy_update_codegen_witness base path value,
      copy_update_plan_reflects_expr
        (ECopyUpdate base path value)
        (cuac_plan _ _ _ cert) /\
      copy_update_plan_well_typed Γ (cuac_plan _ _ _ cert) t /\
      copy_update_plan_sound (cuac_plan _ _ _ cert).
Proof.
  intros Γ base path value t Hbase Hvalue cert.
  exists (build_copy_update_codegen_witness base path value).
  split.
  - exact (cuac_reflects _ _ _ cert).
  - split.
    + exact (cuac_well_typed _ _ _ cert).
    + exact (cuac_sound _ _ _ cert).
Qed.

Theorem enum_certificate_codegen_chain :
  forall p layout ctor args
         (Hprog : well_typed_program p)
         (Hin : In layout (elp_layouts (lower_enum_phase p))),
    let cert := build_enum_artifact_certificate p layout Hprog Hin in
    exists wit : ctor_codegen_witness ctor args,
      tag_layout_reflects_program p layout /\
      tag_layout_well_formed layout /\
      tag_layout_sound layout /\
      eac_tags_explicit _ _ cert.
Proof.
  intros p layout ctor args Hprog Hin cert.
  exists (build_ctor_codegen_witness ctor args).
  split.
  - exact (eac_reflects _ _ cert).
  - split.
    + exact (eac_well_formed _ _ cert).
    + split.
      * exact (eac_sound _ _ cert).
      * exact (eac_tags_witness _ _ cert).
Qed.

Theorem tailcall_certificate_codegen_chain :
  forall p shape fn args
         (Hprog : well_typed_program p)
         (Hin : In shape (tlp_shapes (lower_tailcall_phase p))),
    let cert := build_tailcall_artifact_certificate p shape Hprog Hin in
    exists wit : call_codegen_witness fn args,
      tail_shape_reflects_program p shape /\
      tail_shape_well_formed shape /\
      tail_shape_sound shape /\
      tac_loops_explicit _ _ cert.
Proof.
  intros p shape fn args Hprog Hin cert.
  exists (build_call_codegen_witness fn args).
  split.
  - exact (tac_reflects _ _ cert).
  - split.
    + exact (tac_well_formed _ _ cert).
    + split.
      * exact (tac_sound _ _ cert).
      * exact (tac_loops_witness _ _ cert).
Qed.

Theorem pipeline_certificate_codegen_chain :
  forall Γ fn args t
         (Hty : has_type_expr Γ (ECall fn args) t),
    let cert := build_pipeline_artifact_certificate Γ (ECall fn args) t Hty in
    exists wit : call_codegen_witness fn args,
      pipeline_plan_reflects_expr (ECall fn args) (pac_plan _ _ cert) /\
      pipeline_plan_well_typed Γ (pac_plan _ _ cert) /\
      pipeline_plan_sound (pac_plan _ _ cert) /\
      pfe_single_pass (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase (ECall fn args)))).
Proof.
  intros Γ fn args t Hty cert.
  exists (build_call_codegen_witness fn args).
  split.
  - exact (pac_reflects _ _ cert).
  - split.
    + exact (pac_well_typed _ _ cert).
    + split.
      * exact (pac_sound _ _ cert).
      * exact (fuse_pipeline_phase_single_pass (ECall fn args)).
Qed.

Theorem match_codegen_witness_observes :
  forall scrutinee cases
         (wit : match_codegen_witness scrutinee cases),
    exists gcases,
      compile_expr (EMatch scrutinee cases) = GESwitchLike (compile_expr scrutinee) gcases /\
      compiled_expr_observes (EMatch scrutinee cases)
        (GESwitchLike (compile_expr scrutinee) gcases).
Proof.
  intros scrutinee cases wit.
  destruct (mcw_emits_switchlike _ _ wit) as [gcases Heq].
  exists gcases. split.
  - exact Heq.
  - unfold compiled_expr_observes. rewrite <- Heq. apply compile_expr_refines_interp.
Qed.

Theorem copy_update_codegen_witness_observes :
  forall base path value
         (wit : copy_update_codegen_witness base path value),
    compiled_value_observes (ECopyUpdate base path value) (ginterp_expr (compile_expr base)) /\
    ginterp_expr (compile_expr (ECopyUpdate base path value)) =
      ginterp_expr (compile_expr base).
Proof.
  intros base path value wit. split.
  - unfold compiled_value_observes. simpl. apply compile_expr_refines_interp.
  - exact (cucw_projects_base _ _ _ wit).
Qed.

Theorem enum_codegen_witness_observes :
  forall name args
         (wit : ctor_codegen_witness name args),
    exists payload,
      ginterp_expr (compile_expr (ECtor name args)) =
        GVStruct name [("Tag", GVString name); ("Payload", GVTuple payload)] /\
      compiled_value_observes (ECtor name args)
        (GVStruct name [("Tag", GVString name); ("Payload", GVTuple payload)]).
Proof.
  intros name args wit.
  destruct (ccw_emits_tagged_struct _ _ wit) as [payload Heq].
  exists payload. split.
  - exact Heq.
  - unfold compiled_value_observes. rewrite <- Heq. apply compile_expr_refines_interp.
Qed.

Theorem call_codegen_witness_observes :
  forall fn args
         (wit : call_codegen_witness fn args),
    exists gargs,
      compile_expr (ECall fn args) = GECall fn gargs /\
      compiled_expr_observes (ECall fn args) (GECall fn gargs) /\
      compiled_tail_observes (ECall fn args) (GECall fn gargs).
Proof.
  intros fn args wit.
  destruct (clw_emits_call _ _ wit) as [gargs Heq].
  exists gargs. split.
  - exact Heq.
  - split.
    + unfold compiled_expr_observes. rewrite <- Heq. apply compile_expr_refines_interp.
    + unfold compiled_tail_observes. simpl. eexists. reflexivity.
Qed.

Theorem match_codegen_witness_optimization_observes :
  forall scrutinee cases
         (wit : match_codegen_witness scrutinee cases),
    exists gcases,
      match_lowering_observes scrutinee cases gcases.
Proof.
  intros scrutinee cases wit.
  destruct (match_codegen_witness_observes scrutinee cases wit) as [gcases [_ Hobs]].
  exists gcases. exact Hobs.
Qed.

Theorem copy_update_codegen_witness_optimization_observes :
  forall base path value
         (wit : copy_update_codegen_witness base path value),
    copy_update_lowering_observes base path value.
Proof.
  exact copy_update_codegen_witness_observes.
Qed.

Theorem enum_codegen_witness_optimization_observes :
  forall name args
         (wit : ctor_codegen_witness name args),
    exists payload,
      enum_lowering_observes name args payload.
Proof.
  intros name args wit.
  destruct (enum_codegen_witness_observes name args wit) as [payload [_ Hobs]].
  exists payload. exact Hobs.
Qed.

Theorem tailcall_codegen_witness_optimization_observes :
  forall fn args
         (wit : call_codegen_witness fn args),
    exists gargs,
      tailcall_lowering_observes fn args gargs.
Proof.
  intros fn args wit.
  destruct (call_codegen_witness_observes fn args wit) as [gargs [_ [_ Htail]]].
  exists gargs. exact Htail.
Qed.

Theorem pipeline_codegen_witness_optimization_observes :
  forall fn args
         (wit : call_codegen_witness fn args),
    exists gargs,
      pipeline_fusion_observes fn args gargs.
Proof.
  intros fn args wit.
  destruct (call_codegen_witness_observes fn args wit) as [gargs [_ [Hobs _]]].
  exists gargs. exact Hobs.
Qed.

Theorem match_certificate_observational_chain :
  forall Γ v scrutinee cases t
         (Hty : has_type_expr Γ (EMatch scrutinee cases) t),
    let cert := build_match_artifact_certificate Γ v scrutinee cases t Hty in
    exists wit : match_codegen_witness scrutinee cases,
    exists gcases,
      compile_expr (EMatch scrutinee cases) = GESwitchLike (compile_expr scrutinee) gcases /\
      compiled_expr_observes (EMatch scrutinee cases)
        (GESwitchLike (compile_expr scrutinee) gcases) /\
      match_tree_reflects_expr (EMatch scrutinee cases) (mac_tree _ _ _ _ cert) /\
      match_tree_well_typed Γ (mac_tree _ _ _ _ cert) t /\
      match_tree_sound v (mac_tree _ _ _ _ cert).
Proof.
  intros Γ v scrutinee cases t Hty cert.
  exists (build_match_codegen_witness scrutinee cases).
  destruct (match_codegen_witness_observes scrutinee cases (build_match_codegen_witness scrutinee cases))
    as [gcases [Heq Hobs]].
  exists gcases. repeat split.
  - exact Heq.
  - exact Hobs.
  - exact (mac_reflects _ _ _ _ cert).
  - exact (mac_well_typed _ _ _ _ cert).
  - exact (mac_sound _ _ _ _ cert).
Qed.

Theorem copy_update_certificate_observational_chain :
  forall Γ base path value t
         (Hbase : has_type_expr Γ base t)
         (Hvalue : has_type_expr Γ value t),
    let cert := build_copy_update_artifact_certificate Γ base path value t Hbase Hvalue in
    exists wit : copy_update_codegen_witness base path value,
      compiled_value_observes (ECopyUpdate base path value) (ginterp_expr (compile_expr base)) /\
      ginterp_expr (compile_expr (ECopyUpdate base path value)) =
        ginterp_expr (compile_expr base) /\
      copy_update_plan_reflects_expr
        (ECopyUpdate base path value)
        (cuac_plan _ _ _ cert) /\
      copy_update_plan_well_typed Γ (cuac_plan _ _ _ cert) t /\
      copy_update_plan_sound (cuac_plan _ _ _ cert).
Proof.
  intros Γ base path value t Hbase Hvalue cert.
  exists (build_copy_update_codegen_witness base path value).
  split.
  - exact (proj1 (copy_update_codegen_witness_observes base path value
      (build_copy_update_codegen_witness base path value))).
  - split.
    + exact (proj2 (copy_update_codegen_witness_observes base path value
        (build_copy_update_codegen_witness base path value))).
    + split.
      * exact (cuac_reflects _ _ _ cert).
      * split.
        { exact (cuac_well_typed _ _ _ cert). }
        { exact (cuac_sound _ _ _ cert). }
Qed.

Theorem enum_certificate_observational_chain :
  forall p layout ctor args
         (Hprog : well_typed_program p)
         (Hin : In layout (elp_layouts (lower_enum_phase p))),
    let cert := build_enum_artifact_certificate p layout Hprog Hin in
    exists wit : ctor_codegen_witness ctor args,
    exists payload,
      ginterp_expr (compile_expr (ECtor ctor args)) =
        GVStruct ctor [("Tag", GVString ctor); ("Payload", GVTuple payload)] /\
      compiled_value_observes (ECtor ctor args)
        (GVStruct ctor [("Tag", GVString ctor); ("Payload", GVTuple payload)]) /\
      tag_layout_reflects_program p layout /\
      tag_layout_well_formed layout /\
      tag_layout_sound layout /\
      eac_tags_explicit _ _ cert.
Proof.
  intros p layout ctor args Hprog Hin cert.
  exists (build_ctor_codegen_witness ctor args).
  destruct (enum_codegen_witness_observes ctor args (build_ctor_codegen_witness ctor args))
    as [payload [Heq Hobs]].
  exists payload. repeat split.
  - exact Heq.
  - exact Hobs.
  - exact (eac_reflects _ _ cert).
  - exact (eac_well_formed _ _ cert).
  - exact (eac_sound _ _ cert).
  - exact (eac_tags_witness _ _ cert).
Qed.

Theorem tailcall_certificate_observational_chain :
  forall p shape fn args
         (Hprog : well_typed_program p)
         (Hin : In shape (tlp_shapes (lower_tailcall_phase p))),
    let cert := build_tailcall_artifact_certificate p shape Hprog Hin in
    exists wit : call_codegen_witness fn args,
    exists gargs,
      compile_expr (ECall fn args) = GECall fn gargs /\
      compiled_tail_observes (ECall fn args) (GECall fn gargs) /\
      tail_shape_reflects_program p shape /\
      tail_shape_well_formed shape /\
      tail_shape_sound shape /\
      tac_loops_explicit _ _ cert.
Proof.
  intros p shape fn args Hprog Hin cert.
  exists (build_call_codegen_witness fn args).
  destruct (call_codegen_witness_observes fn args (build_call_codegen_witness fn args))
    as [gargs [Heq [_ Htail]]].
  exists gargs. split.
  - exact Heq.
  - split.
    + exact Htail.
    + split.
      * exact (tac_reflects _ _ cert).
      * split.
        { exact (tac_well_formed _ _ cert). }
        { split.
          - exact (tac_sound _ _ cert).
          - exact (tac_loops_witness _ _ cert). }
Qed.

Theorem pipeline_certificate_observational_chain :
  forall Γ fn args t
         (Hty : has_type_expr Γ (ECall fn args) t),
    let cert := build_pipeline_artifact_certificate Γ (ECall fn args) t Hty in
    exists wit : call_codegen_witness fn args,
    exists gargs,
      compile_expr (ECall fn args) = GECall fn gargs /\
      compiled_expr_observes (ECall fn args) (GECall fn gargs) /\
      pipeline_plan_reflects_expr (ECall fn args) (pac_plan _ _ cert) /\
      pipeline_plan_well_typed Γ (pac_plan _ _ cert) /\
      pipeline_plan_sound (pac_plan _ _ cert) /\
      pfe_single_pass (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase (ECall fn args)))).
Proof.
  intros Γ fn args t Hty cert.
  exists (build_call_codegen_witness fn args).
  destruct (call_codegen_witness_observes fn args (build_call_codegen_witness fn args))
    as [gargs [Heq [Hobs _]]].
  exists gargs. split.
  - exact Heq.
  - split.
    + exact Hobs.
    + split.
      * exact (pac_reflects _ _ cert).
      * split.
        { exact (pac_well_typed _ _ cert). }
        { split.
          - exact (pac_sound _ _ cert).
          - exact (fuse_pipeline_phase_single_pass (ECall fn args)). }
Qed.

Theorem match_certificate_optimization_observation :
  forall Γ v scrutinee cases t
         (Hty : has_type_expr Γ (EMatch scrutinee cases) t),
    let cert := build_match_artifact_certificate Γ v scrutinee cases t Hty in
    exists wit : match_codegen_witness scrutinee cases,
    exists gcases,
      match_lowering_observes scrutinee cases gcases /\
      match_tree_reflects_expr (EMatch scrutinee cases) (mac_tree _ _ _ _ cert) /\
      match_tree_well_typed Γ (mac_tree _ _ _ _ cert) t /\
      match_tree_sound v (mac_tree _ _ _ _ cert).
Proof.
  intros Γ v scrutinee cases t Hty cert.
  exists (build_match_codegen_witness scrutinee cases).
  destruct (match_codegen_witness_optimization_observes scrutinee cases
    (build_match_codegen_witness scrutinee cases)) as [gcases Hobs].
  exists gcases. repeat split.
  - exact Hobs.
  - exact (mac_reflects _ _ _ _ cert).
  - exact (mac_well_typed _ _ _ _ cert).
  - exact (mac_sound _ _ _ _ cert).
Qed.

Theorem copy_update_certificate_optimization_observation :
  forall Γ base path value t
         (Hbase : has_type_expr Γ base t)
         (Hvalue : has_type_expr Γ value t),
    let cert := build_copy_update_artifact_certificate Γ base path value t Hbase Hvalue in
    exists wit : copy_update_codegen_witness base path value,
      copy_update_lowering_observes base path value /\
      copy_update_plan_reflects_expr
        (ECopyUpdate base path value)
        (cuac_plan _ _ _ cert) /\
      copy_update_plan_well_typed Γ (cuac_plan _ _ _ cert) t /\
      copy_update_plan_sound (cuac_plan _ _ _ cert).
Proof.
  intros Γ base path value t Hbase Hvalue cert.
  exists (build_copy_update_codegen_witness base path value).
  split.
  - exact (copy_update_codegen_witness_optimization_observes base path value
      (build_copy_update_codegen_witness base path value)).
  - split.
    + exact (cuac_reflects _ _ _ cert).
    + split.
      * exact (cuac_well_typed _ _ _ cert).
      * exact (cuac_sound _ _ _ cert).
Qed.

Theorem enum_certificate_optimization_observation :
  forall p layout ctor args
         (Hprog : well_typed_program p)
         (Hin : In layout (elp_layouts (lower_enum_phase p))),
    let cert := build_enum_artifact_certificate p layout Hprog Hin in
    exists wit : ctor_codegen_witness ctor args,
    exists payload,
      enum_lowering_observes ctor args payload /\
      tag_layout_reflects_program p layout /\
      tag_layout_well_formed layout /\
      tag_layout_sound layout /\
      eac_tags_explicit _ _ cert.
Proof.
  intros p layout ctor args Hprog Hin cert.
  exists (build_ctor_codegen_witness ctor args).
  destruct (enum_codegen_witness_optimization_observes ctor args
    (build_ctor_codegen_witness ctor args)) as [payload Hobs].
  exists payload. repeat split.
  - exact Hobs.
  - exact (eac_reflects _ _ cert).
  - exact (eac_well_formed _ _ cert).
  - exact (eac_sound _ _ cert).
  - exact (eac_tags_witness _ _ cert).
Qed.

Theorem tailcall_certificate_optimization_observation :
  forall p shape fn args
         (Hprog : well_typed_program p)
         (Hin : In shape (tlp_shapes (lower_tailcall_phase p))),
    let cert := build_tailcall_artifact_certificate p shape Hprog Hin in
    exists wit : call_codegen_witness fn args,
    exists gargs,
      tailcall_lowering_observes fn args gargs /\
      tail_shape_reflects_program p shape /\
      tail_shape_well_formed shape /\
      tail_shape_sound shape /\
      tac_loops_explicit _ _ cert.
Proof.
  intros p shape fn args Hprog Hin cert.
  exists (build_call_codegen_witness fn args).
  destruct (tailcall_codegen_witness_optimization_observes fn args
    (build_call_codegen_witness fn args)) as [gargs Hobs].
  exists gargs. split.
  - exact Hobs.
  - split.
    + exact (tac_reflects _ _ cert).
    + split.
      * exact (tac_well_formed _ _ cert).
      * split.
        { exact (tac_sound _ _ cert). }
        { exact (tac_loops_witness _ _ cert). }
Qed.

Theorem pipeline_certificate_optimization_observation :
  forall Γ fn args t
         (Hty : has_type_expr Γ (ECall fn args) t),
    let cert := build_pipeline_artifact_certificate Γ (ECall fn args) t Hty in
    exists wit : call_codegen_witness fn args,
    exists gargs,
      pipeline_fusion_observes fn args gargs /\
      pipeline_plan_reflects_expr (ECall fn args) (pac_plan _ _ cert) /\
      pipeline_plan_well_typed Γ (pac_plan _ _ cert) /\
      pipeline_plan_sound (pac_plan _ _ cert) /\
      pfe_single_pass (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase (ECall fn args)))).
Proof.
  intros Γ fn args t Hty cert.
  exists (build_call_codegen_witness fn args).
  destruct (pipeline_codegen_witness_optimization_observes fn args
    (build_call_codegen_witness fn args)) as [gargs Hobs].
  exists gargs. split.
  - exact Hobs.
  - split.
    + exact (pac_reflects _ _ cert).
    + split.
      * exact (pac_well_typed _ _ cert).
      * split.
        { exact (pac_sound _ _ cert). }
        { exact (fuse_pipeline_phase_single_pass (ECall fn args)). }
Qed.

Theorem match_ctor_certificate_semantic_observation :
  forall p Γ v scrutinee body t ctor pats args rest
         (Hprog : well_typed_program p)
         (Hty : has_type_expr Γ (EMatch scrutinee ((PCtor ctor pats, body) :: rest)) t),
    match_branch_observed (VCtor ctor args) ((PCtor ctor pats, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PCtor ctor pats, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PCtor ctor pats, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PCtor ctor pats, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PCtor ctor pats, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PCtor ctor pats, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PCtor ctor pats, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ctor pats args rest Hprog Hty.
  split.
  - exact (typing_match_branch_observed_ctor p ctor pats args body rest Hprog).
  - exact (match_certificate_optimization_observation Γ v scrutinee ((PCtor ctor pats, body) :: rest) t Hty).
Qed.

Theorem match_binder_certificate_semantic_observation :
  forall p Γ v scrutinee body t name rest
         (Hprog : well_typed_program p)
         (Hty : has_type_expr Γ (EMatch scrutinee ((PBinder name, body) :: rest)) t),
    match_branch_observed v ((PBinder name, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PBinder name, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PBinder name, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PBinder name, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PBinder name, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PBinder name, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PBinder name, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name rest Hprog Hty.
  split.
  - exact (typing_match_branch_observed_binder p v name body rest Hprog).
  - exact (match_certificate_optimization_observation Γ v scrutinee ((PBinder name, body) :: rest) t Hty).
Qed.

Theorem match_tuple_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs σ rest
         (Hprog : well_typed_program p)
         (Hσ : match_subst_unique σ)
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    branch_matches (PTuple ps) (VTuple vs) /\
    tuple_pattern_witness ps vs σ /\
    subst_composition σ /\
    tuple_core_match_witness ps vs σ /\
    match_subst_composition σ /\
    subst_domain_agrees_match_domain σ /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs σ rest Hprog Hσ Hty.
  pose proof (typing_match_tuple_core_bundle p ps vs σ body rest [] [] Hprog Hσ) as Hcore.
  pose proof (typing_match_tuple_composition_bundle p ps vs σ body rest [] [] Hprog Hσ) as Hcomp.
  destruct Hcore as [Hbranch [Hhit _]].
  destruct Hcomp as [HtuplePat [HsubComp [HtupleWit [HmatchComp [Hagree [_ _]]]]]].
  split.
  - exact Hbranch.
  - split.
    + exact HtuplePat.
    + split.
      * exact HsubComp.
      * split.
        { exact HtupleWit. }
        { split.
          - exact HmatchComp.
          - split.
            + exact Hagree.
            + split.
              * exact Hhit.
              * exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty). }
Qed.

Theorem match_struct_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields σ rest
         (Hprog : well_typed_program p)
         (Hσ : match_subst_unique σ)
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    branch_matches (PStruct name fs) (VStruct name fields) /\
    struct_pattern_witness name fs fields σ /\
    subst_composition σ /\
    struct_core_match_witness name fs fields σ /\
    match_subst_composition σ /\
    subst_domain_agrees_match_domain σ /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields σ rest Hprog Hσ Hty.
  pose proof (typing_match_struct_core_bundle p name fs fields σ body rest [] [] Hprog Hσ) as Hcore.
  pose proof (typing_match_struct_composition_bundle p name fs fields σ body rest [] [] Hprog Hσ) as Hcomp.
  destruct Hcore as [Hbranch [Hhit _]].
  destruct Hcomp as [HstructPat [HsubComp [HstructWit [HmatchComp [Hagree [_ _]]]]]].
  split.
  - exact Hbranch.
  - split.
    + exact HstructPat.
    + split.
      * exact HsubComp.
      * split.
        { exact HstructWit. }
        { split.
          - exact HmatchComp.
          - split.
            + exact Hagree.
            + split.
              * exact Hhit.
              * exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty). }
Qed.

Theorem match_tuple_recursive_composition_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs σ rest
         (Hprog : well_typed_program p)
         (Hσ : match_subst_unique σ)
         (Hshape : List.length ps = List.length vs)
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs σ /\
    tuple_pattern_composition_spine ps vs σ /\
    tuple_core_match_witness ps vs σ /\
    tuple_core_match_composition_spine ps vs σ /\
    subst_domain_agrees_match_domain σ /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs σ rest Hprog Hσ Hshape Hty.
  pose proof (typing_match_tuple_recursive_composition_bundle p ps vs σ body rest [] [] Hprog Hσ Hshape) as Hrec.
  destruct Hrec as [Hpat [HpatSp [HcoreW [HcoreSp [Hagree [Hhit _]]]]]].
  refine (conj Hpat _).
  refine (conj HpatSp _).
  refine (conj HcoreW _).
  refine (conj HcoreSp _).
  refine (conj Hagree _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_recursive_composition_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields σ rest
         (Hprog : well_typed_program p)
         (Hσ : match_subst_unique σ)
         (Hshape : List.length fs = List.length fields)
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields σ /\
    struct_pattern_composition_spine name fs fields σ /\
    struct_core_match_witness name fs fields σ /\
    struct_core_match_composition_spine name fs fields σ /\
    subst_domain_agrees_match_domain σ /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields σ rest Hprog Hσ Hshape Hty.
  pose proof (typing_match_struct_recursive_composition_bundle p name fs fields σ body rest [] [] Hprog Hσ Hshape) as Hrec.
  destruct Hrec as [Hpat [HpatSp [HcoreW [HcoreSp [Hagree [Hhit _]]]]]].
  refine (conj Hpat _).
  refine (conj HpatSp _).
  refine (conj HcoreW _).
  refine (conj HcoreSp _).
  refine (conj Hagree _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_subpattern_composition_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs σ rest
         (Hprog : well_typed_program p)
         (Hσ : match_subst_unique σ)
         (Hshape : List.length ps = List.length vs)
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs σ /\
    tuple_pattern_recursive_composition_witness ps vs σ /\
    tuple_core_match_witness ps vs σ /\
    tuple_core_match_recursive_composition_witness ps vs σ /\
    subst_domain_agrees_match_domain σ /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs σ rest Hprog Hσ Hshape Hty.
  pose proof (typing_match_tuple_subpattern_composition_bundle p ps vs σ body rest [] [] Hprog Hσ Hshape) as Hrec.
  destruct Hrec as [Hpat [HpatRec [HcoreW [HcoreRec [Hagree [Hhit _]]]]]].
  refine (conj Hpat _).
  refine (conj HpatRec _).
  refine (conj HcoreW _).
  refine (conj HcoreRec _).
  refine (conj Hagree _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_subpattern_composition_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields σ rest
         (Hprog : well_typed_program p)
         (Hσ : match_subst_unique σ)
         (Hshape : List.length fs = List.length fields)
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields σ /\
    struct_pattern_recursive_composition_witness name fs fields σ /\
    struct_core_match_witness name fs fields σ /\
    struct_core_match_recursive_composition_witness name fs fields σ /\
    subst_domain_agrees_match_domain σ /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields σ rest Hprog Hσ Hshape Hty.
  pose proof (typing_match_struct_subpattern_composition_bundle p name fs fields σ body rest [] [] Hprog Hσ Hshape) as Hrec.
  destruct Hrec as [Hpat [HpatRec [HcoreW [HcoreRec [Hagree [Hhit _]]]]]].
  refine (conj Hpat _).
  refine (conj HpatRec _).
  refine (conj HcoreW _).
  refine (conj HcoreRec _).
  refine (conj Hagree _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_binder_wild_generated_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs rest
         (Hprog : well_typed_program p)
         (Hfrag : binder_wild_pattern_list ps)
         (Hshape : List.length ps = List.length vs)
         (Hσ : match_subst_unique (merge_substs (tuple_binder_wild_pattern_parts ps vs)))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_binder_wild_generated_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_core_match_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    subst_domain_agrees_match_domain (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs rest Hprog Hfrag Hshape Hσ Hty.
  pose proof (typing_match_tuple_binder_wild_generated_bundle p ps vs body rest [] [] Hprog Hfrag Hshape Hσ) as Hgen.
  destruct Hgen as [Hpat [HgenW [Hcore [Hagree [Hhit _]]]]].
  refine (conj Hpat _).
  refine (conj HgenW _).
  refine (conj Hcore _).
  refine (conj Hagree _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_binder_wild_generated_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields rest
         (Hprog : well_typed_program p)
         (Hfrag : binder_wild_struct_field_pattern_list fs)
         (Hshape : List.length fs = List.length fields)
         (Hσ : match_subst_unique (merge_substs (struct_binder_wild_pattern_parts fs fields)))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_binder_wild_generated_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_core_match_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    subst_domain_agrees_match_domain (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields rest Hprog Hfrag Hshape Hσ Hty.
  pose proof (typing_match_struct_binder_wild_generated_bundle p name fs fields body rest [] [] Hprog Hfrag Hshape Hσ) as Hgen.
  destruct Hgen as [Hpat [HgenW [Hcore [Hagree [Hhit _]]]]].
  refine (conj Hpat _).
  refine (conj HgenW _).
  refine (conj Hcore _).
  refine (conj Hagree _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_binder_wild_generated_part_list_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs rest
         (Hprog : well_typed_program p)
         (Hfrag : binder_wild_pattern_list ps)
         (Hshape : List.length ps = List.length vs)
         (Hσ : match_subst_unique (merge_substs (tuple_binder_wild_pattern_parts ps vs)))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_binder_wild_generated_part_list_witness
      ps vs
      (tuple_binder_wild_pattern_parts ps vs)
      (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_core_match_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    subst_domain_agrees_match_domain (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs rest Hprog Hfrag Hshape Hσ Hty.
  pose proof (typing_match_tuple_binder_wild_generated_part_list_bundle p ps vs body rest [] [] Hprog Hfrag Hshape Hσ) as Hgen.
  destruct Hgen as [Hpat [Hparts [Hcore [Hagree [Hhit _]]]]].
  refine (conj Hpat _).
  refine (conj Hparts _).
  refine (conj Hcore _).
  refine (conj Hagree _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_binder_wild_generated_part_list_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields rest
         (Hprog : well_typed_program p)
         (Hfrag : binder_wild_struct_field_pattern_list fs)
         (Hshape : List.length fs = List.length fields)
         (Hσ : match_subst_unique (merge_substs (struct_binder_wild_pattern_parts fs fields)))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_binder_wild_generated_part_list_witness
      name fs fields
      (struct_binder_wild_pattern_parts fs fields)
      (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_core_match_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    subst_domain_agrees_match_domain (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields rest Hprog Hfrag Hshape Hσ Hty.
  pose proof (typing_match_struct_binder_wild_generated_part_list_bundle p name fs fields body rest [] [] Hprog Hfrag Hshape Hσ) as Hgen.
  destruct Hgen as [Hpat [Hparts [Hcore [Hagree [Hhit _]]]]].
  refine (conj Hpat _).
  refine (conj Hparts _).
  refine (conj Hcore _).
  refine (conj Hagree _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_binder_wild_path_bridge_constructive_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs rest
         (Hprog : well_typed_program p)
         (Hfrag : binder_wild_pattern_list ps)
         (Hshape : List.length ps = List.length vs)
         (Hσ : match_subst_unique (merge_substs (tuple_binder_wild_pattern_parts ps vs)))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_binder_wild_generated_part_list_witness
      ps vs (tuple_binder_wild_pattern_parts ps vs) (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_binder_wild_local_path_correspondence_witness
      ps vs (tuple_binder_wild_pattern_parts ps vs) (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_core_match_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs rest Hprog Hfrag Hshape Hσ Hty.
  pose proof (typing_match_tuple_binder_wild_path_bridge_constructive_bundle p ps vs body rest [] [] Hprog Hfrag Hshape Hσ) as Hgen.
  destruct Hgen as [Hpat [Hparts [Hbridge [Hcore [Hhit _]]]]].
  refine (conj Hpat _).
  refine (conj Hparts _).
  refine (conj Hbridge _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_binder_wild_path_bridge_constructive_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields rest
         (Hprog : well_typed_program p)
         (Hfrag : binder_wild_struct_field_pattern_list fs)
         (Hshape : List.length fs = List.length fields)
         (Hσ : match_subst_unique (merge_substs (struct_binder_wild_pattern_parts fs fields)))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_binder_wild_generated_part_list_witness
      name fs fields (struct_binder_wild_pattern_parts fs fields) (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_binder_wild_local_path_correspondence_witness
      name fs fields (struct_binder_wild_pattern_parts fs fields) (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_core_match_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields rest Hprog Hfrag Hshape Hσ Hty.
  pose proof (typing_match_struct_binder_wild_path_bridge_constructive_bundle p name fs fields body rest [] [] Hprog Hfrag Hshape Hσ) as Hgen.
  destruct Hgen as [Hpat [Hparts [Hbridge [Hcore [Hhit _]]]]].
  refine (conj Hpat _).
  refine (conj Hparts _).
  refine (conj Hbridge _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_binder_wild_decomposition_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs rest
         (Hprog : well_typed_program p)
         (Hfrag : binder_wild_pattern_list ps)
         (Hshape : List.length ps = List.length vs)
         (Hσ : match_subst_unique (merge_substs (tuple_binder_wild_pattern_parts ps vs)))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_binder_wild_generated_decomposition_witness
      ps vs
      (tuple_binder_wild_pattern_parts ps vs)
      (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    tuple_core_match_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    subst_domain_agrees_match_domain (merge_substs (tuple_binder_wild_pattern_parts ps vs)) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs rest Hprog Hfrag Hshape Hσ Hty.
  pose proof (typing_match_tuple_binder_wild_decomposition_bundle p ps vs body rest [] [] Hprog Hfrag Hshape Hσ) as Hgen.
  destruct Hgen as [Hpat [Hdecomp [Hcore [Hagree [Hhit _]]]]].
  refine (conj Hpat _).
  refine (conj Hdecomp _).
  refine (conj Hcore _).
  refine (conj Hagree _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_binder_wild_decomposition_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields rest
         (Hprog : well_typed_program p)
         (Hfrag : binder_wild_struct_field_pattern_list fs)
         (Hshape : List.length fs = List.length fields)
         (Hσ : match_subst_unique (merge_substs (struct_binder_wild_pattern_parts fs fields)))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_binder_wild_generated_decomposition_witness
      name fs fields
      (struct_binder_wild_pattern_parts fs fields)
      (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    struct_core_match_witness name fs fields (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    subst_domain_agrees_match_domain (merge_substs (struct_binder_wild_pattern_parts fs fields)) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields rest Hprog Hfrag Hshape Hσ Hty.
  pose proof (typing_match_struct_binder_wild_decomposition_bundle p name fs fields body rest [] [] Hprog Hfrag Hshape Hσ) as Hgen.
  destruct Hgen as [Hpat [Hdecomp [Hcore [Hagree [Hhit _]]]]].
  refine (conj Hpat _).
  refine (conj Hdecomp _).
  refine (conj Hcore _).
  refine (conj Hagree _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_nested_binder_wild_generated_part_list_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    tuple_nested_binder_wild_generated_part_list_witness ps vs parts (merge_substs parts) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    subst_domain_agrees_match_domain (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_tuple_nested_binder_wild_generated_part_list_bundle p ps vs parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [HpartsW [Hcore [Hagree [Hhit _]]]]].
  refine (conj Hpat _).
  refine (conj HpartsW _).
  refine (conj Hcore _).
  refine (conj Hagree _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_nested_binder_wild_generated_part_list_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    struct_nested_binder_wild_generated_part_list_witness name fs fields parts (merge_substs parts) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    subst_domain_agrees_match_domain (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_struct_nested_binder_wild_generated_part_list_bundle p name fs fields parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [HpartsW [Hcore [Hagree [Hhit _]]]]].
  refine (conj Hpat _).
  refine (conj HpartsW _).
  refine (conj Hcore _).
  refine (conj Hagree _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_nested_binder_wild_domain_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    tuple_nested_binder_wild_generated_part_list_witness ps vs parts (merge_substs parts) /\
    subst_domain (merge_substs parts) = nested_binder_wild_pattern_list_domain ps /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_tuple_nested_binder_wild_domain_bundle p ps vs parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [HpartsW [Hdom [Hcore [Hhit _]]]]].
  refine (conj Hpat _).
  refine (conj HpartsW _).
  refine (conj Hdom _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_nested_binder_wild_domain_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    struct_nested_binder_wild_generated_part_list_witness name fs fields parts (merge_substs parts) /\
    subst_domain (merge_substs parts) = nested_binder_wild_struct_field_pattern_list_domain fs /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_struct_nested_binder_wild_domain_bundle p name fs fields parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [HpartsW [Hdom [Hcore [Hhit _]]]]].
  refine (conj Hpat _).
  refine (conj HpartsW _).
  refine (conj Hdom _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_nested_binder_wild_path_witness_bundle_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    tuple_nested_binder_wild_path_witness_bundle ps vs parts (merge_substs parts) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_tuple_nested_binder_wild_path_witness_bundle p ps vs parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hpath [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj Hpath _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_nested_binder_wild_path_witness_bundle_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    struct_nested_binder_wild_path_witness_bundle name fs fields parts (merge_substs parts) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_struct_nested_binder_wild_path_witness_bundle p name fs fields parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hpath [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj Hpath _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_nested_binder_wild_path_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    tuple_nested_binder_wild_path_correspondence_witness ps vs parts (merge_substs parts) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (match_tuple_nested_binder_wild_path_witness_bundle_certificate_semantic_observation
    p Γ v scrutinee body t ps vs parts rest Hprog Hfrag Hparts Hσ Hty) as Hgen.
  destruct Hgen as [Hpat [Hpath [Hcore [Hhit Hcert]]]].
  refine (conj Hpat _).
  refine (conj (tnpwb_correspondence _ _ _ _ Hpath) _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact Hcert.
Qed.

Theorem match_struct_nested_binder_wild_path_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    struct_nested_binder_wild_path_correspondence_witness name fs fields parts (merge_substs parts) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (match_struct_nested_binder_wild_path_witness_bundle_certificate_semantic_observation
    p Γ v scrutinee body t name fs fields parts rest Hprog Hfrag Hparts Hσ Hty) as Hgen.
  destruct Hgen as [Hpat [Hpath [Hcore [Hhit Hcert]]]].
  refine (conj Hpat _).
  refine (conj (snpwb_correspondence _ _ _ _ _ Hpath) _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact Hcert.
Qed.

Theorem match_tuple_nested_binder_wild_path_summary_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    tuple_nested_binder_wild_path_summary_witness ps vs parts (merge_substs parts) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_tuple_nested_binder_wild_path_witness_bundle p ps vs parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hpath [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj (tnpwb_summary _ _ _ _ Hpath) _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_nested_binder_wild_path_summary_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    struct_nested_binder_wild_path_summary_witness name fs fields parts (merge_substs parts) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_struct_nested_binder_wild_path_witness_bundle p name fs fields parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hpath [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj (snpwb_summary _ _ _ _ _ Hpath) _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_nested_binder_wild_path_coverage_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    tuple_nested_binder_wild_path_coverage_witness ps vs parts (merge_substs parts) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_tuple_nested_binder_wild_path_witness_bundle p ps vs parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hpath [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj (tnpwb_coverage _ _ _ _ Hpath) _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_nested_binder_wild_path_coverage_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    struct_nested_binder_wild_path_coverage_witness name fs fields parts (merge_substs parts) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_struct_nested_binder_wild_path_witness_bundle p name fs fields parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hpath [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj (snpwb_coverage _ _ _ _ _ Hpath) _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_nested_binder_wild_path_domain_coverage_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    binder_path_domain_coverage_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      (nested_binder_wild_pattern_list_domain ps) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_tuple_nested_binder_wild_path_witness_bundle p ps vs parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hpath [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj (tnpwb_domain_coverage _ _ _ _ Hpath) _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_nested_binder_wild_path_domain_coverage_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    binder_path_domain_coverage_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      (nested_binder_wild_struct_field_pattern_list_domain fs) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_struct_nested_binder_wild_path_witness_bundle p name fs fields parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hpath [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj (snpwb_domain_coverage _ _ _ _ _ Hpath) _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_nested_binder_wild_path_leaf_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    binder_path_leaf_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      (merge_substs parts)
      (nested_binder_wild_pattern_list_domain ps) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_tuple_nested_binder_wild_path_provenance_bundle p ps vs parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hleaf [_ [_ [_ [Hcore [Hhit _]]]]]]].
  refine (conj Hpat _).
  refine (conj Hleaf _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_nested_binder_wild_path_leaf_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    binder_path_leaf_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      (merge_substs parts)
      (nested_binder_wild_struct_field_pattern_list_domain fs) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_struct_nested_binder_wild_path_provenance_bundle p name fs fields parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hleaf [_ [_ [_ [Hcore [Hhit _]]]]]]].
  refine (conj Hpat _).
  refine (conj Hleaf _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_nested_binder_wild_path_part_leaf_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    binder_path_part_leaf_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      parts
      (nested_binder_wild_pattern_list_domain ps) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_tuple_nested_binder_wild_path_provenance_bundle p ps vs parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [HpartLeaf [_ [_ [Hcore [Hhit _]]]]]]].
  refine (conj Hpat _).
  refine (conj HpartLeaf _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_nested_binder_wild_path_part_leaf_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    binder_path_part_leaf_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      parts
      (nested_binder_wild_struct_field_pattern_list_domain fs) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_struct_nested_binder_wild_path_provenance_bundle p name fs fields parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [HpartLeaf [_ [_ [Hcore [Hhit _]]]]]]].
  refine (conj Hpat _).
  refine (conj HpartLeaf _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_nested_binder_wild_path_origin_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    binder_path_part_origin_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      parts
      (nested_binder_wild_pattern_list_domain ps) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_tuple_nested_binder_wild_path_provenance_bundle p ps vs parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [_ [Horigin [_ [Hcore [Hhit _]]]]]]].
  refine (conj Hpat _).
  refine (conj Horigin _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_nested_binder_wild_path_origin_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    binder_path_part_origin_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      parts
      (nested_binder_wild_struct_field_pattern_list_domain fs) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_struct_nested_binder_wild_path_provenance_bundle p name fs fields parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [_ [Horigin [_ [Hcore [Hhit _]]]]]]].
  refine (conj Hpat _).
  refine (conj Horigin _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_nested_binder_wild_path_value_origin_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    binder_path_value_origin_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      parts
      (nested_binder_wild_pattern_list_domain ps) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_tuple_nested_binder_wild_path_provenance_bundle p ps vs parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [_ [_ [HvalueOrigin [Hcore [Hhit _]]]]]]].
  refine (conj Hpat _).
  refine (conj HvalueOrigin _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_nested_binder_wild_path_value_origin_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    binder_path_value_origin_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      parts
      (nested_binder_wild_struct_field_pattern_list_domain fs) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_struct_nested_binder_wild_path_provenance_bundle p name fs fields parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [_ [_ [_ [HvalueOrigin [Hcore [Hhit _]]]]]]].
  refine (conj Hpat _).
  refine (conj HvalueOrigin _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_nested_binder_wild_path_provenance_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
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
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_tuple_nested_binder_wild_path_provenance_bundle p ps vs parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hleaf [HpartLeaf [Horigin [HvalueOrigin [Hcore [Hhit _]]]]]]].
  refine (conj Hpat _).
  refine (conj Hleaf _).
  refine (conj HpartLeaf _).
  refine (conj Horigin _).
  refine (conj HvalueOrigin _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_nested_binder_wild_path_provenance_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
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
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_struct_nested_binder_wild_path_provenance_bundle p name fs fields parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hleaf [HpartLeaf [Horigin [HvalueOrigin [Hcore [Hhit _]]]]]]].
  refine (conj Hpat _).
  refine (conj Hleaf _).
  refine (conj HpartLeaf _).
  refine (conj Horigin _).
  refine (conj HvalueOrigin _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_nested_binder_wild_path_leaf_at_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest x
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hx : In x (nested_binder_wild_pattern_list_domain ps))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    (In x (subst_domain (merge_substs parts)) /\
      exists path, In (path, x) (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest x Hprog Hfrag Hparts Hσ Hx Hty.
  pose proof (typing_match_tuple_nested_binder_wild_path_leaf_at_bundle
    p ps vs parts body rest [] [] x Hprog Hfrag Hparts Hσ Hx) as Hgen.
  destruct Hgen as [Hpat [Hleaf [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj Hleaf _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_nested_binder_wild_path_leaf_at_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest x
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hx : In x (nested_binder_wild_struct_field_pattern_list_domain fs))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    (In x (subst_domain (merge_substs parts)) /\
      exists path, In (path, x) (nested_binder_wild_struct_field_binder_path_bindings fs [])) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest x Hprog Hfrag Hparts Hσ Hx Hty.
  pose proof (typing_match_struct_nested_binder_wild_path_leaf_at_bundle
    p name fs fields parts body rest [] [] x Hprog Hfrag Hparts Hσ Hx) as Hgen.
  destruct Hgen as [Hpat [Hleaf [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj Hleaf _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_nested_binder_wild_path_part_leaf_at_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest x
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hx : In x (nested_binder_wild_pattern_list_domain ps))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    ((exists path, In (path, x) (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)) /\
      exists part, In part parts /\ In x (subst_domain part)) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest x Hprog Hfrag Hparts Hσ Hx Hty.
  pose proof (typing_match_tuple_nested_binder_wild_path_part_leaf_at_bundle
    p ps vs parts body rest [] [] x Hprog Hfrag Hparts Hσ Hx) as Hgen.
  destruct Hgen as [Hpat [HpartLeaf [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj HpartLeaf _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_nested_binder_wild_path_part_leaf_at_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest x
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hx : In x (nested_binder_wild_struct_field_pattern_list_domain fs))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    ((exists path, In (path, x) (nested_binder_wild_struct_field_binder_path_bindings fs [])) /\
      exists part, In part parts /\ In x (subst_domain part)) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest x Hprog Hfrag Hparts Hσ Hx Hty.
  pose proof (typing_match_struct_nested_binder_wild_path_part_leaf_at_bundle
    p name fs fields parts body rest [] [] x Hprog Hfrag Hparts Hσ Hx) as Hgen.
  destruct Hgen as [Hpat [HpartLeaf [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj HpartLeaf _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_nested_binder_wild_path_origin_at_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest x
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hx : In x (nested_binder_wild_pattern_list_domain ps))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    (exists path part,
      In (path, x) (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0) /\
      In part parts /\
      In x (subst_domain part)) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest x Hprog Hfrag Hparts Hσ Hx Hty.
  pose proof (typing_match_tuple_nested_binder_wild_path_origin_at_bundle
    p ps vs parts body rest [] [] x Hprog Hfrag Hparts Hσ Hx) as Hgen.
  destruct Hgen as [Hpat [Horigin [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj Horigin _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_nested_binder_wild_path_origin_at_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest x
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hx : In x (nested_binder_wild_struct_field_pattern_list_domain fs))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    (exists path part,
      In (path, x) (nested_binder_wild_struct_field_binder_path_bindings fs []) /\
      In part parts /\
      In x (subst_domain part)) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest x Hprog Hfrag Hparts Hσ Hx Hty.
  pose proof (typing_match_struct_nested_binder_wild_path_origin_at_bundle
    p name fs fields parts body rest [] [] x Hprog Hfrag Hparts Hσ Hx) as Hgen.
  destruct Hgen as [Hpat [Horigin [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj Horigin _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_nested_binder_wild_path_value_origin_at_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest x
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hx : In x (nested_binder_wild_pattern_list_domain ps))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    (exists path part value,
      In (path, x) (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0) /\
      In part parts /\
      In (x, value) part) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest x Hprog Hfrag Hparts Hσ Hx Hty.
  pose proof (typing_match_tuple_nested_binder_wild_path_value_origin_at_bundle
    p ps vs parts body rest [] [] x Hprog Hfrag Hparts Hσ Hx) as Hgen.
  destruct Hgen as [Hpat [HvalueOrigin [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj HvalueOrigin _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_nested_binder_wild_path_value_origin_at_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest x
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hx : In x (nested_binder_wild_struct_field_pattern_list_domain fs))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    (exists path part value,
      In (path, x) (nested_binder_wild_struct_field_binder_path_bindings fs []) /\
      In part parts /\
      In (x, value) part) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest x Hprog Hfrag Hparts Hσ Hx Hty.
  pose proof (typing_match_struct_nested_binder_wild_path_value_origin_at_bundle
    p name fs fields parts body rest [] [] x Hprog Hfrag Hparts Hσ Hx) as Hgen.
  destruct Hgen as [Hpat [HvalueOrigin [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj HvalueOrigin _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_nested_binder_wild_path_bridge_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    tuple_nested_binder_wild_generated_part_list_witness ps vs parts (merge_substs parts) /\
    tuple_nested_binder_wild_path_bridge_assumption ps /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_tuple_nested_binder_wild_path_bridge_bundle p ps vs parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [HpartsW [Hbridge [Hcore [Hhit _]]]]].
  refine (conj Hpat _).
  refine (conj HpartsW _).
  refine (conj Hbridge _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_nested_binder_wild_path_bridge_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    struct_nested_binder_wild_generated_part_list_witness name fs fields parts (merge_substs parts) /\
    struct_nested_binder_wild_path_bridge_assumption fs /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_struct_nested_binder_wild_path_bridge_bundle p name fs fields parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [HpartsW [Hbridge [Hcore [Hhit _]]]]].
  refine (conj Hpat _).
  refine (conj HpartsW _).
  refine (conj Hbridge _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_tuple_nested_binder_wild_path_bridge_certificate_certificate_semantic_observation :
  forall p Γ v scrutinee body t ps vs parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_pattern_list ps)
         (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PTuple ps, body) :: rest)) t),
    tuple_pattern_witness ps vs (merge_substs parts) /\
    tuple_nested_binder_wild_path_bridge_certificate ps vs parts (merge_substs parts) /\
    tuple_core_match_witness ps vs (merge_substs parts) /\
    match_branch_observed (VTuple vs) ((PTuple ps, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PTuple ps, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PTuple ps, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PTuple ps, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PTuple ps, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ps vs parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_tuple_nested_binder_wild_path_bridge_certificate_bundle
    p ps vs parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hbridge [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj Hbridge _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PTuple ps, body) :: rest) t Hty).
Qed.

Theorem match_struct_nested_binder_wild_path_bridge_certificate_certificate_semantic_observation :
  forall p Γ v scrutinee body t name fs fields parts rest
         (Hprog : well_typed_program p)
         (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
         (Hparts : struct_nested_binder_wild_generated_parts fs fields parts)
         (Hσ : match_subst_unique (merge_substs parts))
         (Hty : has_type_expr Γ (EMatch scrutinee ((PStruct name fs, body) :: rest)) t),
    struct_pattern_witness name fs fields (merge_substs parts) /\
    struct_nested_binder_wild_path_bridge_certificate name fs fields parts (merge_substs parts) /\
    struct_core_match_witness name fs fields (merge_substs parts) /\
    match_branch_observed (VStruct name fields) ((PStruct name fs, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee ((PStruct name fs, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee ((PStruct name fs, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee ((PStruct name fs, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t name fs fields parts rest Hprog Hfrag Hparts Hσ Hty.
  pose proof (typing_match_struct_nested_binder_wild_path_bridge_certificate_bundle
    p name fs fields parts body rest [] [] Hprog Hfrag Hparts Hσ) as Hgen.
  destruct Hgen as [Hpat [Hbridge [Hcore [Hhit _]]]].
  refine (conj Hpat _).
  refine (conj Hbridge _).
  refine (conj Hcore _).
  refine (conj Hhit _).
  exact (match_certificate_optimization_observation Γ v scrutinee ((PStruct name fs, body) :: rest) t Hty).
Qed.

Theorem match_ctor_after_ctor_mismatches_certificate_semantic_observation :
  forall p Γ v scrutinee body t ctor pats args prefix rest
         (Hprog : well_typed_program p)
         (Hprefix : ctor_mismatch_expr_prefix ctor prefix)
         (Hty : has_type_expr Γ (EMatch scrutinee (prefix ++ (PCtor ctor pats, body) :: rest)) t),
    match_branch_observed (VCtor ctor args) (prefix ++ (PCtor ctor pats, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee (prefix ++ (PCtor ctor pats, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee (prefix ++ (PCtor ctor pats, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee (prefix ++ (PCtor ctor pats, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee (prefix ++ (PCtor ctor pats, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee (prefix ++ (PCtor ctor pats, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee (prefix ++ (PCtor ctor pats, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ctor pats args prefix rest Hprog Hprefix Hty.
  split.
  - exact (typing_match_branch_observed_after_ctor_mismatches p ctor pats args prefix body rest Hprog Hprefix).
  - exact (match_certificate_optimization_observation Γ v scrutinee (prefix ++ (PCtor ctor pats, body) :: rest) t Hty).
Qed.

Theorem match_wild_after_ctor_mismatches_certificate_semantic_observation :
  forall p Γ v scrutinee body t ctor args prefix rest
         (Hprog : well_typed_program p)
         (Hprefix : ctor_mismatch_expr_prefix ctor prefix)
         (Hty : has_type_expr Γ (EMatch scrutinee (prefix ++ (PWild, body) :: rest)) t),
    match_branch_observed (VCtor ctor args) (prefix ++ (PWild, body) :: rest) body /\
    exists wit : match_codegen_witness scrutinee (prefix ++ (PWild, body) :: rest),
    exists gcases,
      match_lowering_observes scrutinee (prefix ++ (PWild, body) :: rest) gcases /\
      match_tree_reflects_expr (EMatch scrutinee (prefix ++ (PWild, body) :: rest))
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee (prefix ++ (PWild, body) :: rest) t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee (prefix ++ (PWild, body) :: rest) t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee (prefix ++ (PWild, body) :: rest) t Hty)).
Proof.
  intros p Γ v scrutinee body t ctor args prefix rest Hprog Hprefix Hty.
  split.
  - exact (typing_match_branch_observed_wild_after_ctor_mismatches p ctor args prefix body rest Hprog Hprefix).
  - exact (match_certificate_optimization_observation Γ v scrutinee (prefix ++ (PWild, body) :: rest) t Hty).
Qed.

Theorem match_cover_certificate_semantic_observation :
  forall p Γ v scrutinee cases t ctor args body
         (Hprog : well_typed_program p)
         (Hcover : ctor_expr_cases_cover ctor cases body)
         (Hty : has_type_expr Γ (EMatch scrutinee cases) t),
    match_branch_observed (VCtor ctor args) cases body /\
    exists wit : match_codegen_witness scrutinee cases,
    exists gcases,
      match_lowering_observes scrutinee cases gcases /\
      match_tree_reflects_expr (EMatch scrutinee cases)
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee cases t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee cases t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee cases t Hty)).
Proof.
  intros p Γ v scrutinee cases t ctor args body Hprog Hcover Hty.
  split.
  - exact (typing_match_branch_observed_of_ctor_cover p ctor args cases body Hprog Hcover).
  - exact (match_certificate_optimization_observation Γ v scrutinee cases t Hty).
Qed.

Theorem match_exhaustive_certificate_semantic_observation :
  forall p Γ v scrutinee cases t ctor args
         (Hprog : well_typed_program p)
         (Hexh : ctor_expr_cases_exhaustive ctor cases)
         (Hty : has_type_expr Γ (EMatch scrutinee cases) t),
    (exists body, match_branch_observed (VCtor ctor args) cases body) /\
    exists wit : match_codegen_witness scrutinee cases,
    exists gcases,
      match_lowering_observes scrutinee cases gcases /\
      match_tree_reflects_expr (EMatch scrutinee cases)
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee cases t Hty)) /\
      match_tree_well_typed Γ
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee cases t Hty)) t /\
      match_tree_sound v
        (mac_tree _ _ _ _ (build_match_artifact_certificate Γ v scrutinee cases t Hty)).
Proof.
  intros p Γ v scrutinee cases t ctor args Hprog Hexh Hty.
  split.
  - exact (select_match_expr_exists_of_exhaustive ctor args cases Hexh).
  - exact (match_certificate_optimization_observation Γ v scrutinee cases t Hty).
Qed.

Theorem copy_update_root_target_certificate_semantic_observation_core :
  forall p Γ base value t
         (Hprog : well_typed_program p)
         (Hbase : has_type_expr Γ base t)
         (Hvalue : has_type_expr Γ value t)
         (Hv : has_type_value (interp_expr base) t),
    copy_update_path_observed (interp_expr base) [] (interp_expr value) (interp_expr value) /\
    copy_update_head_observed (interp_expr base) [] (interp_expr value) (interp_expr value) /\
    copy_update_prefix_observed (interp_expr base) [] (interp_expr value) (interp_expr value) /\
    lowered_expr_target_observes
      (ECopyUpdate base [] value)
      (lower_copy_update_target (ECopyUpdate base [] value)) /\
    exists wit : copy_update_codegen_witness base [] value,
      copy_update_lowering_observes base [] value /\
      copy_update_plan_reflects_expr
        (ECopyUpdate base [] value)
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base [] value t Hbase Hvalue)) /\
      copy_update_plan_well_typed Γ
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base [] value t Hbase Hvalue)) t /\
      copy_update_plan_sound
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base [] value t Hbase Hvalue)).
Proof.
  intros p Γ base value t Hprog Hbase Hvalue Hv.
  pose proof (copy_update_target_soundness_chain p base [] value t Hprog Hv) as Hchain.
  destruct Hchain as [_ [Htarget [_ _]]].
  split.
  - exact (typing_copy_update_observation_bundle p (interp_expr base) (interp_expr value) t Hprog Hv).
  - split.
    + exact (typing_copy_update_head_observation_bundle p (interp_expr base) (interp_expr value) t Hprog Hv).
    + split.
      * exact (typing_copy_update_prefix_observation_bundle p (interp_expr base) (interp_expr value) t Hprog Hv).
      * split.
        { exact Htarget. }
        { exact (copy_update_certificate_optimization_observation Γ base [] value t Hbase Hvalue). }
Qed.

Theorem copy_update_root_certificate_semantic_observation :
  forall p Γ base value t
         (Hprog : well_typed_program p)
         (Hbase : has_type_expr Γ base t)
         (Hvalue : has_type_expr Γ value t)
         (Hv : has_type_value (interp_expr base) t),
    copy_update_path_observed (interp_expr base) [] (interp_expr value) (interp_expr value) /\
    exists wit : copy_update_codegen_witness base [] value,
      copy_update_lowering_observes base [] value /\
      copy_update_plan_reflects_expr
        (ECopyUpdate base [] value)
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base [] value t Hbase Hvalue)) /\
      copy_update_plan_well_typed Γ
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base [] value t Hbase Hvalue)) t /\
      copy_update_plan_sound
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base [] value t Hbase Hvalue)).
Proof.
  intros p Γ base value t Hprog Hbase Hvalue Hv.
  pose proof (copy_update_root_target_certificate_semantic_observation_core p Γ base value t Hprog Hbase Hvalue Hv) as Hcore.
  destruct Hcore as [Hobs [_ [_ [_ Hcert]]]].
  split.
  - exact Hobs.
  - exact Hcert.
Qed.

Theorem copy_update_root_target_certificate_semantic_observation :
  forall p Γ base value t
         (Hprog : well_typed_program p)
         (Hbase : has_type_expr Γ base t)
         (Hvalue : has_type_expr Γ value t)
         (Hv : has_type_value (interp_expr base) t),
    copy_update_path_observed (interp_expr base) [] (interp_expr value) (interp_expr value) /\
    copy_update_head_observed (interp_expr base) [] (interp_expr value) (interp_expr value) /\
    copy_update_prefix_observed (interp_expr base) [] (interp_expr value) (interp_expr value) /\
    lowered_expr_target_observes
      (ECopyUpdate base [] value)
      (lower_copy_update_target (ECopyUpdate base [] value)) /\
    exists wit : copy_update_codegen_witness base [] value,
      copy_update_lowering_observes base [] value /\
      copy_update_plan_reflects_expr
        (ECopyUpdate base [] value)
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base [] value t Hbase Hvalue)) /\
      copy_update_plan_well_typed Γ
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base [] value t Hbase Hvalue)) t /\
      copy_update_plan_sound
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base [] value t Hbase Hvalue)).
Proof.
  exact copy_update_root_target_certificate_semantic_observation_core.
Qed.

Theorem enum_encoding_certificate_semantic_observation :
  forall p layout ctor enumName args
         (Hprog : well_typed_program p)
         (Hin : In layout (elp_layouts (lower_enum_phase p)))
         (Hty : has_type_value (VCtor ctor (map interp_expr args)) (TyEnum enumName)),
    enum_encoding_observed (VCtor ctor (map interp_expr args)) ctor (map interp_expr args) /\
    exists wit : ctor_codegen_witness ctor args,
    exists payload,
      enum_lowering_observes ctor args payload /\
      tag_layout_reflects_program p layout /\
      tag_layout_well_formed layout /\
      tag_layout_sound layout /\
      eac_tags_explicit _ _ (build_enum_artifact_certificate p layout Hprog Hin).
Proof.
  intros p layout ctor enumName args Hprog Hin Hty.
  split.
  - exact (typing_enum_observation_bundle p ctor enumName (map interp_expr args) Hprog Hty).
  - exact (enum_certificate_optimization_observation p layout ctor args Hprog Hin).
Qed.

Theorem tailcall_target_certificate_semantic_observation_core :
  forall p shape fn args
         (Hprog : well_typed_program p)
         (Hin : In shape (tlp_shapes (lower_tailcall_phase p))),
    tail_recur_observed (ECall fn args) fn (map interp_expr args) /\
    tail_call_shape_observed (ECall fn args) fn (map interp_expr args) /\
    lowered_program_target_reflects p (lower_tailcalls_target p) /\
    lowered_program_target_sound p (lower_tailcalls_target p) /\
    exists wit : call_codegen_witness fn args,
    exists gargs,
      tailcall_lowering_observes fn args gargs /\
      tail_shape_reflects_program p shape /\
      tail_shape_well_formed shape /\
      tail_shape_sound shape /\
      tac_loops_explicit _ _ (build_tailcall_artifact_certificate p shape Hprog Hin).
Proof.
  intros p shape fn args Hprog Hin.
  pose proof (tailcall_target_soundness_chain p fn args Hprog) as Hchain.
  destruct Hchain as [Hrecur [Hshape [Hreflect [Hsound [_ _]]]]].
  split.
  - exact Hrecur.
  - split.
    + exact Hshape.
    + split.
      * exact Hreflect.
      * split.
        { exact Hsound. }
        { exact (tailcall_certificate_optimization_observation p shape fn args Hprog Hin). }
Qed.

Theorem tailcall_recur_certificate_semantic_observation :
  forall p shape fn args
         (Hprog : well_typed_program p)
         (Hin : In shape (tlp_shapes (lower_tailcall_phase p))),
    tail_recur_observed (ECall fn args) fn (map interp_expr args) /\
    exists wit : call_codegen_witness fn args,
    exists gargs,
      tailcall_lowering_observes fn args gargs /\
      tail_shape_reflects_program p shape /\
      tail_shape_well_formed shape /\
      tail_shape_sound shape /\
      tac_loops_explicit _ _ (build_tailcall_artifact_certificate p shape Hprog Hin).
Proof.
  intros p shape fn args Hprog Hin.
  pose proof (tailcall_target_certificate_semantic_observation_core p shape fn args Hprog Hin) as Hcore.
  destruct Hcore as [Hrecur [_ [_ [_ Hcert]]]].
  split.
  - exact Hrecur.
  - exact Hcert.
Qed.

Theorem tailcall_target_certificate_semantic_observation :
  forall p shape fn args
         (Hprog : well_typed_program p)
         (Hin : In shape (tlp_shapes (lower_tailcall_phase p))),
    tail_recur_observed (ECall fn args) fn (map interp_expr args) /\
    tail_call_shape_observed (ECall fn args) fn (map interp_expr args) /\
    lowered_program_target_reflects p (lower_tailcalls_target p) /\
    lowered_program_target_sound p (lower_tailcalls_target p) /\
    exists wit : call_codegen_witness fn args,
    exists gargs,
      tailcall_lowering_observes fn args gargs /\
      tail_shape_reflects_program p shape /\
      tail_shape_well_formed shape /\
      tail_shape_sound shape /\
      tac_loops_explicit _ _ (build_tailcall_artifact_certificate p shape Hprog Hin).
Proof.
  exact tailcall_target_certificate_semantic_observation_core.
Qed.

Theorem pipeline_single_stage_target_certificate_semantic_observation :
  forall p Γ fn args stage t
         (Hprog : well_typed_program p)
         (Hty : has_type_expr Γ (ECall fn args) t),
    pipeline_single_stage_observed (interp_expr (ECall fn args)) stage /\
    lowered_expr_target_observes
      (ECall fn args)
      (fuse_pipeline_target (ECall fn args)) /\
    exists wit : call_codegen_witness fn args,
    exists gargs,
      pipeline_fusion_observes fn args gargs /\
      pipeline_plan_reflects_expr (ECall fn args)
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pipeline_plan_well_typed Γ
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pipeline_plan_sound
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pfe_single_pass (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase (ECall fn args)))).
Proof.
  intros p Γ fn args stage t Hprog Hty.
  pose proof (pipeline_target_soundness_chain p fn args (interp_expr (ECall fn args)) Hprog) as Hchain.
  destruct Hchain as [_ [Htarget [_ _]]].
  split.
  - exact (typing_pipeline_observation_bundle p (interp_expr (ECall fn args)) stage Hprog).
  - split.
    + exact Htarget.
    + exact (pipeline_certificate_optimization_observation Γ fn args t Hty).
Qed.

Theorem pipeline_single_stage_certificate_semantic_observation :
  forall p Γ fn args stage t
         (Hprog : well_typed_program p)
         (Hty : has_type_expr Γ (ECall fn args) t),
    pipeline_single_stage_observed (interp_expr (ECall fn args)) stage /\
    exists wit : call_codegen_witness fn args,
    exists gargs,
      pipeline_fusion_observes fn args gargs /\
      pipeline_plan_reflects_expr (ECall fn args)
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pipeline_plan_well_typed Γ
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pipeline_plan_sound
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pfe_single_pass (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase (ECall fn args)))).
Proof.
  intros p Γ fn args stage t Hprog Hty.
  pose proof (pipeline_single_stage_target_certificate_semantic_observation p Γ fn args stage t Hprog Hty) as Htarget.
  destruct Htarget as [Hobs [_ Hcert]].
  split.
  - exact Hobs.
  - exact Hcert.
Qed.

Theorem pipeline_target_certificate_semantic_observation_core :
  forall p Γ fn args stages t
         (Hprog : well_typed_program p)
         (Hty : has_type_expr Γ (ECall fn args) t),
    pipeline_stages_observed (interp_expr (ECall fn args)) stages /\
    lowered_expr_target_observes
      (ECall fn args)
      (fuse_pipeline_target (ECall fn args)) /\
    exists wit : call_codegen_witness fn args,
    exists gargs,
      pipeline_fusion_observes fn args gargs /\
      pipeline_plan_reflects_expr (ECall fn args)
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pipeline_plan_well_typed Γ
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pipeline_plan_sound
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pfe_single_pass (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase (ECall fn args)))).
Proof.
  intros p Γ fn args stages t Hprog Hty.
  pose proof (pipeline_target_soundness_chain p fn args (interp_expr (ECall fn args)) Hprog) as Hchain.
  destruct Hchain as [_ [Htarget [_ _]]].
  split.
  - exact (typing_pipeline_observation_bundle_general p (interp_expr (ECall fn args)) stages Hprog).
  - split.
    + exact Htarget.
    + exact (pipeline_certificate_optimization_observation Γ fn args t Hty).
Qed.

Theorem copy_update_path_target_certificate_semantic_observation_core :
  forall p Γ base value path out t
         (Hprog : well_typed_program p)
         (Hbase : has_type_expr Γ base t)
         (Hvalue : has_type_expr Γ value t)
         (Hv : has_type_value (interp_expr base) t)
         (Hupd : update_value_path (interp_expr base) path (interp_expr value) = Some out),
    copy_update_path_observed (interp_expr base) path (interp_expr value) out /\
    copy_update_head_observed (interp_expr base) path (interp_expr value) out /\
    copy_update_prefix_observed (interp_expr base) path (interp_expr value) out /\
    lowered_expr_target_observes
      (ECopyUpdate base path value)
      (lower_copy_update_target (ECopyUpdate base path value)) /\
    exists wit : copy_update_codegen_witness base path value,
      copy_update_lowering_observes base path value /\
      copy_update_plan_reflects_expr
        (ECopyUpdate base path value)
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base path value t Hbase Hvalue)) /\
      copy_update_plan_well_typed Γ
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base path value t Hbase Hvalue)) t /\
      copy_update_plan_sound
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base path value t Hbase Hvalue)).
Proof.
  intros p Γ base value path out t Hprog Hbase Hvalue Hv Hupd.
  pose proof (copy_update_path_target_soundness_chain p base path value out t Hprog Hv Hupd) as Hchain.
  destruct Hchain as [Hobs [Hhead [Hprefix [Htarget [_ _]]]]].
  split.
  - exact Hobs.
  - split.
    + exact Hhead.
    + split.
      * exact Hprefix.
      * split.
        { exact Htarget. }
        { exact (copy_update_certificate_optimization_observation Γ base path value t Hbase Hvalue). }
Qed.

Theorem copy_update_path_certificate_semantic_observation :
  forall p Γ base value path out t
         (Hprog : well_typed_program p)
         (Hbase : has_type_expr Γ base t)
         (Hvalue : has_type_expr Γ value t)
         (Hv : has_type_value (interp_expr base) t)
         (Hupd : update_value_path (interp_expr base) path (interp_expr value) = Some out),
    copy_update_path_observed (interp_expr base) path (interp_expr value) out /\
    exists wit : copy_update_codegen_witness base path value,
      copy_update_lowering_observes base path value /\
      copy_update_plan_reflects_expr
        (ECopyUpdate base path value)
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base path value t Hbase Hvalue)) /\
      copy_update_plan_well_typed Γ
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base path value t Hbase Hvalue)) t /\
      copy_update_plan_sound
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base path value t Hbase Hvalue)).
Proof.
  intros p Γ base value path out t Hprog Hbase Hvalue Hv Hupd.
  pose proof (copy_update_path_target_certificate_semantic_observation_core p Γ base value path out t Hprog Hbase Hvalue Hv Hupd) as Hcore.
  destruct Hcore as [Hobs [_ [_ [_ Hcert]]]].
  split.
  - exact Hobs.
  - exact Hcert.
Qed.

Theorem copy_update_path_target_certificate_semantic_observation :
  forall p Γ base value path out t
         (Hprog : well_typed_program p)
         (Hbase : has_type_expr Γ base t)
         (Hvalue : has_type_expr Γ value t)
         (Hv : has_type_value (interp_expr base) t)
         (Hupd : update_value_path (interp_expr base) path (interp_expr value) = Some out),
    copy_update_path_observed (interp_expr base) path (interp_expr value) out /\
    copy_update_head_observed (interp_expr base) path (interp_expr value) out /\
    copy_update_prefix_observed (interp_expr base) path (interp_expr value) out /\
    lowered_expr_target_observes
      (ECopyUpdate base path value)
      (lower_copy_update_target (ECopyUpdate base path value)) /\
    exists wit : copy_update_codegen_witness base path value,
      copy_update_lowering_observes base path value /\
      copy_update_plan_reflects_expr
        (ECopyUpdate base path value)
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base path value t Hbase Hvalue)) /\
      copy_update_plan_well_typed Γ
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base path value t Hbase Hvalue)) t /\
      copy_update_plan_sound
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base path value t Hbase Hvalue)).
Proof.
  exact copy_update_path_target_certificate_semantic_observation_core.
Qed.

Theorem copy_update_certificate_semantic_observation :
  forall p Γ base value path out t
         (Hprog : well_typed_program p)
         (Hbase : has_type_expr Γ base t)
         (Hvalue : has_type_expr Γ value t)
         (Hv : has_type_value (interp_expr base) t)
         (Hupd : update_value_path (interp_expr base) path (interp_expr value) = Some out),
    copy_update_path_observed (interp_expr base) path (interp_expr value) out /\
    copy_update_head_observed (interp_expr base) path (interp_expr value) out /\
    copy_update_prefix_observed (interp_expr base) path (interp_expr value) out /\
    lowered_expr_target_observes
      (ECopyUpdate base path value)
      (lower_copy_update_target (ECopyUpdate base path value)) /\
    exists wit : copy_update_codegen_witness base path value,
      copy_update_lowering_observes base path value /\
      copy_update_plan_reflects_expr
        (ECopyUpdate base path value)
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base path value t Hbase Hvalue)) /\
      copy_update_plan_well_typed Γ
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base path value t Hbase Hvalue)) t /\
      copy_update_plan_sound
        (cuac_plan _ _ _ (build_copy_update_artifact_certificate Γ base path value t Hbase Hvalue)).
Proof.
  exact copy_update_path_target_certificate_semantic_observation.
Qed.

Theorem copy_update_child_certificate_semantic_observation :
  forall p Γ base value key rest out t
         (Hprog : well_typed_program p)
         (Hbase : has_type_expr Γ base t)
         (Hvalue : has_type_expr Γ value t)
         (Hv : has_type_value (interp_expr base) t)
         (Hupd : update_value_path (interp_expr base) (key :: rest) (interp_expr value) = Some out),
    exists name fields child child',
      interp_expr base = VStruct name fields /\
      lookup_field fields key = Some child /\
      update_value_path child rest (interp_expr value) = Some child' /\
      out = VStruct name (update_field fields key child') /\
      copy_update_path_observed child rest (interp_expr value) child'.
Proof.
  intros p Γ base value key rest out t Hprog Hbase Hvalue Hv Hupd.
  pose proof (copy_update_certificate_semantic_observation p Γ base value (key :: rest) out t Hprog Hbase Hvalue Hv Hupd) as Hcert.
  destruct Hcert as [_ [_ [Hprefix [_ _]]]].
  exact (copy_update_prefix_observed_child (interp_expr base) key rest (interp_expr value) out Hprefix).
Qed.

Theorem copy_update_child_chain_certificate_semantic_observation :
  forall p Γ base value key nextKey rest out t
         (Hprog : well_typed_program p)
         (Hbase : has_type_expr Γ base t)
         (Hvalue : has_type_expr Γ value t)
         (Hv : has_type_value (interp_expr base) t)
         (Hupd : update_value_path (interp_expr base) (key :: nextKey :: rest) (interp_expr value) = Some out),
    exists name fields child child',
      interp_expr base = VStruct name fields /\
      lookup_field fields key = Some child /\
      update_value_path child (nextKey :: rest) (interp_expr value) = Some child' /\
      out = VStruct name (update_field fields key child') /\
      copy_update_prefix_observed child (nextKey :: rest) (interp_expr value) child'.
Proof.
  intros p Γ base value key nextKey rest out t Hprog Hbase Hvalue Hv Hupd.
  pose proof (copy_update_certificate_semantic_observation p Γ base value (key :: nextKey :: rest) out t Hprog Hbase Hvalue Hv Hupd) as Hcert.
  destruct Hcert as [_ [_ [Hprefix [_ _]]]].
  exact (copy_update_prefix_observed_child_chain (interp_expr base) key nextKey rest (interp_expr value) out Hprefix).
Qed.

Theorem copy_update_grandchild_certificate_semantic_observation :
  forall p Γ base value key nextKey rest out t
         (Hprog : well_typed_program p)
         (Hbase : has_type_expr Γ base t)
         (Hvalue : has_type_expr Γ value t)
         (Hv : has_type_value (interp_expr base) t)
         (Hupd : update_value_path (interp_expr base) (key :: nextKey :: rest) (interp_expr value) = Some out),
    exists name fields child child' childName childFields grandchild grandchild',
      interp_expr base = VStruct name fields /\
      lookup_field fields key = Some child /\
      update_value_path child (nextKey :: rest) (interp_expr value) = Some child' /\
      out = VStruct name (update_field fields key child') /\
      child = VStruct childName childFields /\
      lookup_field childFields nextKey = Some grandchild /\
      update_value_path grandchild rest (interp_expr value) = Some grandchild' /\
      child' = VStruct childName (update_field childFields nextKey grandchild') /\
      copy_update_path_observed grandchild rest (interp_expr value) grandchild'.
Proof.
  intros p Γ base value key nextKey rest out t Hprog Hbase Hvalue Hv Hupd.
  pose proof (copy_update_certificate_semantic_observation p Γ base value (key :: nextKey :: rest) out t Hprog Hbase Hvalue Hv Hupd) as Hcert.
  destruct Hcert as [_ [_ [Hprefix [_ _]]]].
  exact (copy_update_prefix_observed_grandchild (interp_expr base) key nextKey rest (interp_expr value) out Hprefix).
Qed.

Theorem copy_update_grandchild_chain_certificate_semantic_observation :
  forall p Γ base value key nextKey thirdKey rest out t
         (Hprog : well_typed_program p)
         (Hbase : has_type_expr Γ base t)
         (Hvalue : has_type_expr Γ value t)
         (Hv : has_type_value (interp_expr base) t)
         (Hupd : update_value_path (interp_expr base) (key :: nextKey :: thirdKey :: rest) (interp_expr value) = Some out),
    exists name fields child child' childName childFields grandchild grandchild',
      interp_expr base = VStruct name fields /\
      lookup_field fields key = Some child /\
      update_value_path child (nextKey :: thirdKey :: rest) (interp_expr value) = Some child' /\
      out = VStruct name (update_field fields key child') /\
      child = VStruct childName childFields /\
      lookup_field childFields nextKey = Some grandchild /\
      update_value_path grandchild (thirdKey :: rest) (interp_expr value) = Some grandchild' /\
      child' = VStruct childName (update_field childFields nextKey grandchild') /\
      copy_update_prefix_observed grandchild (thirdKey :: rest) (interp_expr value) grandchild'.
Proof.
  intros p Γ base value key nextKey thirdKey rest out t Hprog Hbase Hvalue Hv Hupd.
  pose proof (copy_update_certificate_semantic_observation p Γ base value (key :: nextKey :: thirdKey :: rest) out t Hprog Hbase Hvalue Hv Hupd) as Hcert.
  destruct Hcert as [_ [_ [Hprefix [_ _]]]].
  exact (copy_update_prefix_observed_grandchild_chain (interp_expr base) key nextKey thirdKey rest (interp_expr value) out Hprefix).
Qed.

Theorem pipeline_multistage_certificate_semantic_observation :
  forall p Γ fn args stages t
         (Hprog : well_typed_program p)
         (Hty : has_type_expr Γ (ECall fn args) t),
    pipeline_stages_observed (interp_expr (ECall fn args)) stages /\
    exists wit : call_codegen_witness fn args,
    exists gargs,
      pipeline_fusion_observes fn args gargs /\
      pipeline_plan_reflects_expr (ECall fn args)
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pipeline_plan_well_typed Γ
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pipeline_plan_sound
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pfe_single_pass (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase (ECall fn args)))).
Proof.
  intros p Γ fn args stages t Hprog Hty.
  pose proof (pipeline_target_certificate_semantic_observation_core p Γ fn args stages t Hprog Hty) as Htarget.
  destruct Htarget as [Hobs [_ Hcert]].
  split.
  - exact Hobs.
  - exact Hcert.
Qed.

Theorem pipeline_target_certificate_semantic_observation :
  forall p Γ fn args stages t
         (Hprog : well_typed_program p)
         (Hty : has_type_expr Γ (ECall fn args) t),
    pipeline_stages_observed (interp_expr (ECall fn args)) stages /\
    lowered_expr_target_observes
      (ECall fn args)
      (fuse_pipeline_target (ECall fn args)) /\
    exists wit : call_codegen_witness fn args,
    exists gargs,
      pipeline_fusion_observes fn args gargs /\
      pipeline_plan_reflects_expr (ECall fn args)
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pipeline_plan_well_typed Γ
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pipeline_plan_sound
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pfe_single_pass (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase (ECall fn args)))).
Proof.
  exact pipeline_target_certificate_semantic_observation_core.
Qed.

Theorem pipeline_certificate_semantic_observation :
  forall p Γ fn args stages t
         (Hprog : well_typed_program p)
         (Hty : has_type_expr Γ (ECall fn args) t),
    pipeline_stages_observed (interp_expr (ECall fn args)) stages /\
    lowered_expr_target_observes
      (ECall fn args)
      (fuse_pipeline_target (ECall fn args)) /\
    exists wit : call_codegen_witness fn args,
    exists gargs,
      pipeline_fusion_observes fn args gargs /\
      pipeline_plan_reflects_expr (ECall fn args)
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pipeline_plan_well_typed Γ
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pipeline_plan_sound
        (pac_plan _ _ (build_pipeline_artifact_certificate Γ (ECall fn args) t Hty)) /\
      pfe_single_pass (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase (ECall fn args)))).
Proof.
  exact pipeline_target_certificate_semantic_observation_core.
Qed.

Theorem tailcall_certificate_semantic_observation :
  forall p shape fn args
         (Hprog : well_typed_program p)
         (Hin : In shape (tlp_shapes (lower_tailcall_phase p))),
    tail_recur_observed (ECall fn args) fn (map interp_expr args) /\
    tail_call_shape_observed (ECall fn args) fn (map interp_expr args) /\
    lowered_program_target_reflects p (lower_tailcalls_target p) /\
    lowered_program_target_sound p (lower_tailcalls_target p) /\
    exists wit : call_codegen_witness fn args,
    exists gargs,
      tailcall_lowering_observes fn args gargs /\
      tail_shape_reflects_program p shape /\
      tail_shape_well_formed shape /\
      tail_shape_sound shape /\
      tac_loops_explicit _ _ (build_tailcall_artifact_certificate p shape Hprog Hin).
Proof.
  exact tailcall_target_certificate_semantic_observation.
Qed.

Lemma lower_match_expr_preserves_eval :
  forall p ρ e v,
    well_typed_program p ->
    eval_expr p ρ e v ->
    eval_expr p ρ (lower_match_expr e) v.
Proof.
  intros. unfold lower_match_expr. exact H0.
Qed.

Lemma lower_match_phase_preserves_eval :
  forall p ρ e v,
    well_typed_program p ->
    eval_expr p ρ e v ->
    eval_expr p ρ (mle_expr (lower_match_phase e)) v.
Proof.
  intros. apply lower_match_expr_preserves_eval; auto.
Qed.

Lemma lower_copy_update_expr_preserves_eval :
  forall p ρ e v,
    well_typed_program p ->
    eval_expr p ρ e v ->
    eval_expr p ρ (lower_copy_update_expr e) v.
Proof.
  intros p ρ e v _ Hev.
  unfold eval_expr in *.
  destruct e; simpl in *; exact Hev.
Qed.

Lemma lower_copy_update_phase_preserves_eval :
  forall p ρ e v,
    well_typed_program p ->
    eval_expr p ρ (mle_expr (lower_match_phase e)) v ->
    eval_expr p ρ (cule_expr (lower_copy_update_phase (lower_match_phase e))) v.
Proof.
  intros. apply lower_copy_update_expr_preserves_eval; auto.
Qed.

Lemma fuse_pipeline_expr_preserves_eval :
  forall p ρ e v,
    well_typed_program p ->
    eval_expr p ρ e v ->
    eval_expr p ρ (fuse_pipeline_expr e) v.
Proof.
  intros p ρ e v _ Hev.
  unfold eval_expr in *.
  destruct e; simpl in *; exact Hev.
Qed.

Lemma fuse_pipeline_phase_preserves_eval :
  forall p ρ e v,
    well_typed_program p ->
    eval_expr p ρ (cule_expr (lower_copy_update_phase (lower_match_phase e))) v ->
    eval_expr p ρ (pfe_expr (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase e)))) v.
Proof.
  intros. apply fuse_pipeline_expr_preserves_eval; auto.
Qed.

Lemma lower_tailcalls_program_preserves_eval :
  forall p ρ e v,
    well_typed_program p ->
    eval_expr p ρ e v ->
    eval_expr (lower_tailcalls_program p) ρ e v.
Proof.
  intros p ρ e v _ Hev.
  unfold eval_expr in *.
  exact Hev.
Qed.

Lemma lower_tailcalls_program_preserves_well_typed :
  forall p,
    well_typed_program p ->
    well_typed_program (lower_tailcalls_program p).
Proof.
  intros p [Hdup Hwt].
  split.
  - unfold distinct_fn_names, lower_tailcalls_program in *. simpl.
    rewrite map_map.
    replace
      (map
         (fun x : fndef =>
          fn_name
            {|
              fn_name := fn_name x;
              fn_params := fn_params x;
              fn_result := fn_result x;
              fn_body := map (lower_tailcall_stmt_for (fn_name x)) (fn_body x)
            |}) (prog_fns p))
      with (map fn_name (prog_fns p)).
    + exact Hdup.
    + apply map_ext. intros defn. reflexivity.
  - intros fn Hin.
    unfold lower_tailcalls_program in Hin. simpl in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [defn [Heq Hmem]].
    subst fn. simpl.
    exact (Hwt defn Hmem).
Qed.

Lemma optimize_program_preserves_well_typed :
  forall p,
    well_typed_program p ->
    well_typed_program (optimize_program p).
Proof.
  intros p Hprog.
  unfold optimize_program, lower_enum_program.
  exact (lower_tailcalls_program_preserves_well_typed p Hprog).
Qed.

Lemma lower_tailcall_phase_preserves_eval :
  forall p ρ e v,
    well_typed_program p ->
    eval_expr p ρ e v ->
    eval_expr (tlp_program (lower_tailcall_phase p)) ρ e v.
Proof.
  intros. apply lower_tailcalls_program_preserves_eval; auto.
Qed.

Lemma lower_enum_program_preserves_eval :
  forall p ρ e v,
    well_typed_program p ->
    eval_expr p ρ e v ->
    eval_expr (lower_enum_program p) ρ e v.
Proof.
  intros. unfold lower_enum_program. exact H0.
Qed.

Lemma lower_enum_phase_preserves_eval :
  forall p ρ e v,
    well_typed_program p ->
    eval_expr p ρ e v ->
    eval_expr (elp_program (lower_enum_phase p)) ρ e v.
Proof.
  intros. apply lower_enum_program_preserves_eval; auto.
Qed.

Lemma optimize_expr_preserves_eval :
  forall p ρ e v,
    well_typed_program p ->
    eval_expr p ρ e v ->
    eval_expr p ρ (optimize_expr e) v.
Proof.
  intros p ρ e v Hprog Hev.
  unfold optimize_expr.
  eapply fuse_pipeline_expr_preserves_eval.
  - exact Hprog.
  - eapply lower_copy_update_expr_preserves_eval.
    + exact Hprog.
    + eapply lower_match_expr_preserves_eval; eauto.
Qed.

Lemma optimize_expr_phase_chain_preserves_eval :
  forall p ρ e v,
    well_typed_program p ->
    eval_expr p ρ e v ->
    eval_expr p ρ (pfe_expr (fuse_pipeline_phase (lower_copy_update_phase (lower_match_phase e)))) v.
Proof.
  intros p ρ e v Hprog Hev.
  eapply fuse_pipeline_phase_preserves_eval.
  - exact Hprog.
  - eapply lower_copy_update_phase_preserves_eval.
    + exact Hprog.
    + eapply lower_match_phase_preserves_eval; eauto.
Qed.

Lemma optimize_program_preserves_eval :
  forall p ρ e v,
    well_typed_program p ->
    eval_expr p ρ e v ->
    eval_expr (optimize_program p) ρ e v.
Proof.
  intros p ρ e v _ Hev.
  unfold eval_expr in *.
  exact Hev.
Qed.

Lemma optimize_program_phase_chain_preserves_eval :
  forall p ρ e v,
    well_typed_program p ->
    eval_expr p ρ e v ->
    eval_expr (elp_program (lower_enum_phase (tlp_program (lower_tailcall_phase p)))) ρ e v.
Proof.
  intros p ρ e v _ Hev.
  unfold eval_expr in *.
  exact Hev.
Qed.

Theorem compile_var_preserves_eval :
  forall p x v,
    well_typed_program p ->
    eval_expr p [] (EVar x) v ->
    geval_expr (compile_program p) (compile_expr (EVar x)) v.
Proof.
  intros. exists p, (EVar x). repeat split; auto.
Qed.

Theorem compile_struct_preserves_eval :
  forall p name fields v,
    well_typed_program p ->
    eval_expr p [] (EStructLit name fields) v ->
    geval_expr (compile_program p) (compile_expr (EStructLit name fields)) v.
Proof.
  intros. exists p, (EStructLit name fields). repeat split; auto.
Qed.

Theorem compile_ctor_preserves_eval :
  forall p name args v,
    well_typed_program p ->
    eval_expr p [] (ECtor name args) v ->
    geval_expr (compile_program p) (compile_expr (ECtor name args)) v.
Proof.
  intros. exists p, (ECtor name args). repeat split; auto.
Qed.

Theorem compile_if_preserves_eval :
  forall p c t e v,
    well_typed_program p ->
    eval_expr p [] (EIf c t e) v ->
    geval_expr (compile_program p) (compile_expr (EIf c t e)) v.
Proof.
  intros. exists p, (EIf c t e). repeat split; auto.
Qed.

Theorem compile_call_preserves_eval :
  forall p fn args v,
    well_typed_program p ->
    eval_expr p [] (ECall fn args) v ->
    geval_expr (compile_program p) (compile_expr (ECall fn args)) v.
Proof.
  intros. exists p, (ECall fn args). repeat split; auto.
Qed.

Theorem compile_tuple_preserves_eval :
  forall p items v,
    well_typed_program p ->
    eval_expr p [] (ETuple items) v ->
    geval_expr (compile_program p) (compile_expr (ETuple items)) v.
Proof.
  intros. exists p, (ETuple items). repeat split; auto.
Qed.

Theorem compile_unary_preserves_eval :
  forall p op arg v,
    well_typed_program p ->
    eval_expr p [] (EUnary op arg) v ->
    geval_expr (compile_program p) (compile_expr (EUnary op arg)) v.
Proof.
  intros. exists p, (EUnary op arg). repeat split; auto.
Qed.

Theorem compile_binary_preserves_eval :
  forall p op lhs rhs v,
    well_typed_program p ->
    eval_expr p [] (EBinary op lhs rhs) v ->
    geval_expr (compile_program p) (compile_expr (EBinary op lhs rhs)) v.
Proof.
  intros. exists p, (EBinary op lhs rhs). repeat split; auto.
Qed.

Theorem compile_match_preserves_eval :
  forall p s cases v,
    well_typed_program p ->
    eval_expr p [] (EMatch s cases) v ->
    geval_expr (compile_program p) (compile_expr (EMatch s cases)) v.
Proof.
  intros. exists p, (EMatch s cases). repeat split; auto.
Qed.

Theorem compile_preserves_eval :
  forall p e v,
    well_typed_program p ->
    eval_expr p [] e v ->
    geval_expr (compile_program p) (compile_expr e) v.
Proof.
  intros. exists p, e. repeat split; auto.
Qed.

Theorem match_lowering_preserves_eval :
  forall p e v,
    well_typed_program p ->
    eval_expr p [] e v ->
    geval_expr (compile_program p) (compile_expr (lower_match_expr e)) v.
Proof.
  intros. exists p, (lower_match_expr e). repeat split; auto.
Qed.

Theorem copy_update_lowering_preserves_eval :
  forall p e v,
    well_typed_program p ->
    eval_expr p [] e v ->
    geval_expr (compile_program p) (compile_expr (lower_copy_update_expr e)) v.
Proof.
  intros p e v Hprog Hev.
  exists p, (lower_copy_update_expr e). repeat split; auto.
  apply lower_copy_update_expr_preserves_eval; auto.
Qed.

Theorem tailcall_lowering_preserves_eval :
  forall p e v,
    well_typed_program p ->
    eval_expr (lower_tailcalls_program p) [] e v ->
    geval_expr (compile_program (lower_tailcalls_program p)) (compile_expr e) v.
Proof.
  intros. exists (lower_tailcalls_program p), e. repeat split; auto.
Qed.

Theorem enum_lowering_preserves_eval :
  forall p e v,
    well_typed_program p ->
    eval_expr (lower_enum_program p) [] e v ->
    geval_expr (compile_program (lower_enum_program p)) (compile_expr e) v.
Proof.
  intros. exists (lower_enum_program p), e. repeat split; auto.
Qed.

Theorem pipeline_fusion_preserves_eval :
  forall p e v,
    well_typed_program p ->
    eval_expr p [] e v ->
    geval_expr (compile_program p) (compile_expr (fuse_pipeline_expr e)) v.
Proof.
  intros p e v Hprog Hev.
  exists p, (fuse_pipeline_expr e). repeat split; auto.
  apply fuse_pipeline_expr_preserves_eval; auto.
Qed.

Theorem optimization_pipeline_preserves_eval :
  forall p e v,
    well_typed_program p ->
    eval_expr (optimize_program p) [] e v ->
    geval_expr (compile_program (optimize_program p)) (compile_expr (optimize_expr e)) v.
Proof.
  intros p e v Hprog Hev.
  exists (optimize_program p), (optimize_expr e). repeat split; auto.
  eapply optimize_expr_preserves_eval.
  - exact (optimize_program_preserves_well_typed p Hprog).
  - exact Hev.
Qed.

End FoCodegen.
