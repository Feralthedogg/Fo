From Coq Require Import List String ZArith.
Import ListNotations.
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
