From Coq Require Import List String Arith Lia.
Import ListNotations.
Require Import Fo.Syntax.
Require Import Fo.Semantics.

Module FoEnv.
Import FoSyntax.
Import FoSemantics.

Definition tyenv := list (string * ty).

Fixpoint lookup_ty (Γ : tyenv) (x : string) : option ty :=
  match Γ with
  | [] => None
  | (y, t) :: rest => if String.eqb x y then Some t else lookup_ty rest x
  end.

Fixpoint lookup_val (ρ : env) (x : string) : option value :=
  match ρ with
  | [] => None
  | (y, v) :: rest => if String.eqb x y then Some v else lookup_val rest x
  end.

Inductive has_type_value : value -> ty -> Prop :=
| HTV_Unit : has_type_value VUnit TyUnit
| HTV_Bool : forall b, has_type_value (VBool b) TyBool
| HTV_Int : forall n, has_type_value (VInt n) TyInt
| HTV_String : forall s, has_type_value (VString s) TyString
| HTV_Tuple : forall vs ts, has_type_value (VTuple vs) (TyTuple ts)
| HTV_Struct : forall name fields, has_type_value (VStruct name fields) (TyStruct name)
| HTV_Ctor : forall ctor enumName args, has_type_value (VCtor ctor args) (TyEnum enumName).

Definition env_well_typed (ρ : env) (Γ : tyenv) : Prop :=
  forall x v, lookup_val ρ x = Some v -> exists t, lookup_ty Γ x = Some t /\ has_type_value v t.

Lemma lookup_ty_nil :
  forall x, lookup_ty [] x = None.
Proof.
  reflexivity.
Qed.

Lemma lookup_val_nil :
  forall x, lookup_val [] x = None.
Proof.
  reflexivity.
Qed.

Lemma lookup_ty_shadow :
  forall x t Γ, lookup_ty ((x, t) :: Γ) x = Some t.
Proof.
  intros. simpl. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma lookup_val_shadow :
  forall x v ρ, lookup_val ((x, v) :: ρ) x = Some v.
Proof.
  intros. simpl. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma lookup_ty_miss :
  forall x y t Γ,
    x <> y ->
    lookup_ty ((x, t) :: Γ) y = lookup_ty Γ y.
Proof.
  intros. simpl.
  destruct (String.eqb_spec y x).
  - exfalso. apply H. symmetry. assumption.
  - reflexivity.
Qed.

Lemma lookup_val_miss :
  forall x y v ρ,
    x <> y ->
    lookup_val ((x, v) :: ρ) y = lookup_val ρ y.
Proof.
  intros. simpl.
  destruct (String.eqb_spec y x).
  - exfalso. apply H. symmetry. assumption.
  - reflexivity.
Qed.

Lemma lookup_ty_deterministic :
  forall Γ x t1 t2,
    lookup_ty Γ x = Some t1 ->
    lookup_ty Γ x = Some t2 ->
    t1 = t2.
Proof.
  intros. rewrite H in H0. inversion H0. reflexivity.
Qed.

Lemma lookup_val_deterministic :
  forall ρ x v1 v2,
    lookup_val ρ x = Some v1 ->
    lookup_val ρ x = Some v2 ->
    v1 = v2.
Proof.
  intros. rewrite H in H0. inversion H0. reflexivity.
Qed.

End FoEnv.
