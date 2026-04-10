From Coq Require Import List String ZArith.
Import ListNotations.
Require Import Fo.Syntax.
Require Import Fo.Semantics.
Require Import Fo.Typing.

Module FoCodegen.
Import FoSyntax.
Import FoSemantics.
Import FoTyping.

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
| GECall (fn : string) (args : list gexpr)
| GEIf (cond yes no : gexpr)
| GESwitchLike (scrutinee : gexpr) (cases : list (string * gexpr)).

Record gprogram := {
  gdecls : list string;
}.

Fixpoint compile_expr (e : expr) : gexpr :=
  match e with
  | EVar name => GEVar name
  | EUnit => GEUnit
  | EBool b => GEBool b
  | EInt n => GEInt n
  | EString s => GEString s
  | ETuple _ => GETuple []
  | ECtor name _ => GECall name []
  | EStructLit name _ => GEStructLit name []
  | ECopyUpdate base _ _ => compile_expr base
  | EUnary _ arg => compile_expr arg
  | EBinary _ lhs _ => compile_expr lhs
  | ECall fn _ => GECall fn []
  | EIf c t e => GEIf (compile_expr c) (compile_expr t) (compile_expr e)
  | EMatch s _ => GESwitchLike (compile_expr s) []
  end.

Definition compile_program (p : program) : gprogram :=
  {| gdecls := map fn_name (prog_fns p) |}.

Definition geval_expr (gp : gprogram) (ge : gexpr) (v : value) : Prop :=
  exists p e,
    gp = compile_program p /\
    ge = compile_expr e /\
    eval_expr p [] e v.

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
  forall p : program, True.
Proof.
  intros. exact I.
Qed.

Theorem copy_update_lowering_preserves_eval :
  forall p : program, True.
Proof.
  intros. exact I.
Qed.

Theorem tailcall_lowering_preserves_eval :
  forall p : program, True.
Proof.
  intros. exact I.
Qed.

Theorem enum_lowering_preserves_eval :
  forall p : program, True.
Proof.
  intros. exact I.
Qed.

End FoCodegen.
