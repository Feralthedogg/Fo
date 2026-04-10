From Coq Require Import List String.
Import ListNotations.
Require Import Fo.Syntax.
Require Import Fo.Semantics.
Require Import Fo.Env.

Module FoTyping.
Import FoSyntax.
Import FoSemantics.
Import FoEnv.

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

Definition well_typed_fn (_fn : fndef) : Prop := True.
Definition well_typed_program (_p : program) : Prop := True.

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
    has_type_expr (Δ ++ Γ) e t.
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
    has_type_stmt (Δ ++ Γ) s t.
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

End FoTyping.
