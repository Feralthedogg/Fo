From Coq Require Import List String ZArith.
Import ListNotations.

Module FoCoreLite.

Inductive lite_ty :=
| LTyUnit
| LTyBool
| LTyInt
| LTyString
| LTyTuple (items : list lite_ty).

Inductive lite_value :=
| LVUnit
| LVBool (b : bool)
| LVInt (n : Z)
| LVString (s : string)
| LVTuple (items : list lite_value).

Definition lite_env := list (string * lite_value).

Fixpoint lookup_lite (ρ : lite_env) (x : string) : option lite_value :=
  match ρ with
  | [] => None
  | (y, v) :: rest => if String.eqb x y then Some v else lookup_lite rest x
  end.

Inductive lite_expr :=
| LEVar (name : string)
| LEUnit
| LEBool (b : bool)
| LEInt (n : Z)
| LEString (s : string)
| LETuple (items : list lite_expr)
| LEIf (cond yes no : lite_expr).

Inductive lite_eval : lite_env -> lite_expr -> lite_value -> Prop :=
| LE_Var :
    forall ρ x v,
      lookup_lite ρ x = Some v ->
      lite_eval ρ (LEVar x) v
| LE_Unit :
    forall ρ, lite_eval ρ LEUnit LVUnit
| LE_Bool :
    forall ρ b, lite_eval ρ (LEBool b) (LVBool b)
| LE_Int :
    forall ρ n, lite_eval ρ (LEInt n) (LVInt n)
| LE_String :
    forall ρ s, lite_eval ρ (LEString s) (LVString s)
| LE_TupleNil :
    forall ρ, lite_eval ρ (LETuple []) (LVTuple [])
| LE_TupleCons :
    forall ρ e es v vs,
      lite_eval ρ e v ->
      lite_eval ρ (LETuple es) (LVTuple vs) ->
      lite_eval ρ (LETuple (e :: es)) (LVTuple (v :: vs))
| LE_IfTrue :
    forall ρ c t e v,
      lite_eval ρ c (LVBool true) ->
      lite_eval ρ t v ->
      lite_eval ρ (LEIf c t e) v
| LE_IfFalse :
    forall ρ c t e v,
      lite_eval ρ c (LVBool false) ->
      lite_eval ρ e v ->
      lite_eval ρ (LEIf c t e) v.

Definition lite_tyenv := list (string * lite_ty).

Fixpoint lookup_lite_ty (Γ : lite_tyenv) (x : string) : option lite_ty :=
  match Γ with
  | [] => None
  | (y, t) :: rest => if String.eqb x y then Some t else lookup_lite_ty rest x
  end.

Fixpoint lite_interp (ρ : lite_env) (e : lite_expr) : lite_value :=
  match e with
  | LEVar x =>
      match lookup_lite ρ x with
      | Some v => v
      | None => LVUnit
      end
  | LEUnit => LVUnit
  | LEBool b => LVBool b
  | LEInt n => LVInt n
  | LEString s => LVString s
  | LETuple items =>
      let fix interp_list (items : list lite_expr) : list lite_value :=
        match items with
        | [] => []
        | e :: rest => lite_interp ρ e :: interp_list rest
        end
      in LVTuple (interp_list items)
  | LEIf c yes no =>
      match lite_interp ρ c with
      | LVBool true => lite_interp ρ yes
      | LVBool false => lite_interp ρ no
      | _ => lite_interp ρ no
      end
  end.

Inductive lite_has_type : lite_tyenv -> lite_expr -> lite_ty -> Prop :=
| LT_Var :
    forall Γ x t,
      lookup_lite_ty Γ x = Some t ->
      lite_has_type Γ (LEVar x) t
| LT_Unit :
    forall Γ, lite_has_type Γ LEUnit LTyUnit
| LT_Bool :
    forall Γ b, lite_has_type Γ (LEBool b) LTyBool
| LT_Int :
    forall Γ n, lite_has_type Γ (LEInt n) LTyInt
| LT_String :
    forall Γ s, lite_has_type Γ (LEString s) LTyString
| LT_TupleNil :
    forall Γ, lite_has_type Γ (LETuple []) (LTyTuple [])
| LT_TupleCons :
    forall Γ e es t ts,
      lite_has_type Γ e t ->
      lite_has_type Γ (LETuple es) (LTyTuple ts) ->
      lite_has_type Γ (LETuple (e :: es)) (LTyTuple (t :: ts))
| LT_If :
    forall Γ c t e ty,
      lite_has_type Γ c LTyBool ->
      lite_has_type Γ t ty ->
      lite_has_type Γ e ty ->
      lite_has_type Γ (LEIf c t e) ty.

Lemma lookup_lite_nil :
  forall x, lookup_lite [] x = None.
Proof.
  reflexivity.
Qed.

Lemma lookup_lite_shadow :
  forall x v ρ, lookup_lite ((x, v) :: ρ) x = Some v.
Proof.
  intros. simpl. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma lookup_lite_ty_nil :
  forall x, lookup_lite_ty [] x = None.
Proof.
  reflexivity.
Qed.

Lemma lookup_lite_ty_shadow :
  forall x t Γ, lookup_lite_ty ((x, t) :: Γ) x = Some t.
Proof.
  intros. simpl. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma lookup_lite_deterministic :
  forall ρ x v1 v2,
    lookup_lite ρ x = Some v1 ->
    lookup_lite ρ x = Some v2 ->
    v1 = v2.
Proof.
  intros. rewrite H in H0. inversion H0. reflexivity.
Qed.

Lemma lookup_lite_ty_deterministic :
  forall Γ x t1 t2,
    lookup_lite_ty Γ x = Some t1 ->
    lookup_lite_ty Γ x = Some t2 ->
    t1 = t2.
Proof.
  intros. rewrite H in H0. inversion H0. reflexivity.
Qed.

Lemma lite_eval_interp :
  forall ρ e v,
    lite_eval ρ e v ->
    lite_interp ρ e = v.
Proof.
  intros ρ e v Hev.
  induction Hev.
  - simpl. rewrite H. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IHHev1.
    simpl in IHHev2. inversion IHHev2. reflexivity.
  - simpl. rewrite IHHev1. exact IHHev2.
  - simpl. rewrite IHHev1. exact IHHev2.
Qed.

Theorem lite_eval_deterministic :
  forall ρ e v1 v2,
    lite_eval ρ e v1 ->
    lite_eval ρ e v2 ->
    v1 = v2.
Proof.
  intros ρ e v1 v2 H1 H2.
  pose proof (lite_eval_interp _ _ _ H1) as I1.
  pose proof (lite_eval_interp _ _ _ H2) as I2.
  rewrite I1 in I2.
  exact I2.
Qed.

Lemma canonical_bool_lite :
  forall ρ e v,
    lite_has_type [] e LTyBool ->
    lite_eval ρ e v ->
    exists b, v = LVBool b.
Proof.
  intros ρ e v HT HE.
  induction HE.
  - inversion HT; subst. simpl in H. discriminate.
  - inversion HT.
  - inversion HT; subst. eauto.
  - inversion HT.
  - inversion HT.
  - inversion HT.
  - inversion HT.
  - inversion HT; subst. eapply IHHE2; eauto.
  - inversion HT; subst. eapply IHHE2; eauto.
Qed.

Lemma canonical_unit_lite :
  forall ρ e v,
    lite_has_type [] e LTyUnit ->
    lite_eval ρ e v ->
    v = LVUnit.
Proof.
  intros ρ e v HT HE.
  induction HE.
  - inversion HT; subst. simpl in H. discriminate.
  - reflexivity.
  - inversion HT.
  - inversion HT.
  - inversion HT.
  - inversion HT.
  - inversion HT.
  - inversion HT; subst. eapply IHHE2; eauto.
  - inversion HT; subst. eapply IHHE2; eauto.
Qed.

Lemma canonical_int_lite :
  forall ρ e v,
    lite_has_type [] e LTyInt ->
    lite_eval ρ e v ->
    exists n, v = LVInt n.
Proof.
  intros ρ e v HT HE.
  induction HE.
  - inversion HT; subst. simpl in H. discriminate.
  - inversion HT.
  - inversion HT.
  - inversion HT; subst. eauto.
  - inversion HT.
  - inversion HT.
  - inversion HT.
  - inversion HT; subst. eapply IHHE2; eauto.
  - inversion HT; subst. eapply IHHE2; eauto.
Qed.

Lemma canonical_string_lite :
  forall ρ e v,
    lite_has_type [] e LTyString ->
    lite_eval ρ e v ->
    exists s, v = LVString s.
Proof.
  intros ρ e v HT HE.
  induction HE.
  - inversion HT; subst. simpl in H. discriminate.
  - inversion HT.
  - inversion HT.
  - inversion HT.
  - inversion HT; subst. eauto.
  - inversion HT.
  - inversion HT.
  - inversion HT; subst. eapply IHHE2; eauto.
  - inversion HT; subst. eapply IHHE2; eauto.
Qed.

Lemma canonical_tuple_lite :
  forall ρ e ts v,
    lite_has_type [] e (LTyTuple ts) ->
    lite_eval ρ e v ->
    exists vs, v = LVTuple vs.
Proof.
  intros ρ e ts v HT HE.
  induction HE.
  - inversion HT; subst. simpl in H. discriminate.
  - inversion HT.
  - inversion HT.
  - inversion HT.
  - inversion HT.
  - inversion HT; subst. eexists. reflexivity.
  - inversion HT; subst. eexists. reflexivity.
  - inversion HT; subst. eapply IHHE2; eauto.
  - inversion HT; subst. eapply IHHE2; eauto.
Qed.

Lemma progress_unit_lite :
  forall ρ, exists v, lite_eval ρ LEUnit v.
Proof.
  intros. exists LVUnit. constructor.
Qed.

Lemma progress_bool_lite :
  forall ρ b, exists v, lite_eval ρ (LEBool b) v.
Proof.
  intros. exists (LVBool b). constructor.
Qed.

Lemma progress_int_lite :
  forall ρ n, exists v, lite_eval ρ (LEInt n) v.
Proof.
  intros. exists (LVInt n). constructor.
Qed.

Lemma progress_string_lite :
  forall ρ s, exists v, lite_eval ρ (LEString s) v.
Proof.
  intros. exists (LVString s). constructor.
Qed.

Lemma progress_tuple_nil_lite :
  forall ρ, exists v, lite_eval ρ (LETuple []) v.
Proof.
  intros. exists (LVTuple []). constructor.
Qed.

Lemma progress_tuple_cons_lite :
  forall ρ e es v vs,
    lite_eval ρ e v ->
    lite_eval ρ (LETuple es) (LVTuple vs) ->
    exists out, lite_eval ρ (LETuple (e :: es)) out.
Proof.
  intros. exists (LVTuple (v :: vs)). econstructor; eauto.
Qed.

Lemma progress_if_true_lite :
  forall ρ c t e v,
    lite_eval ρ c (LVBool true) ->
    lite_eval ρ t v ->
    exists out, lite_eval ρ (LEIf c t e) out.
Proof.
  intros. exists v. eapply LE_IfTrue; eauto.
Qed.

Lemma progress_if_false_lite :
  forall ρ c t e v,
    lite_eval ρ c (LVBool false) ->
    lite_eval ρ e v ->
    exists out, lite_eval ρ (LEIf c t e) out.
Proof.
  intros. exists v. eapply LE_IfFalse; eauto.
Qed.

Lemma progress_lite_gen :
  forall Γ e t,
    lite_has_type Γ e t ->
    Γ = [] ->
    forall ρ, exists v, lite_eval ρ e v.
Proof.
  intros Γ e t HT.
  induction HT as
      [Γ x t Hlookup
      | Γ
      | Γ b
      | Γ n
      | Γ s
      | Γ
      | Γ e es t ts HtyE IHE HtyEs IHEs
      | Γ c texp eexp ty HtyC IHC HtyT IHT HtyE IHE]; intros Hnil ρ.
  - subst. simpl in Hlookup. discriminate.
  - exists LVUnit. constructor.
  - exists (LVBool b). constructor.
  - exists (LVInt n). constructor.
  - exists (LVString s). constructor.
  - exists (LVTuple []). constructor.
  - subst.
    destruct (IHE eq_refl ρ) as [v Hv].
    destruct (IHEs eq_refl ρ) as [vt Hvt].
    destruct (canonical_tuple_lite ρ (LETuple es) ts vt HtyEs Hvt) as [vs Hvs].
    inversion Hvs. subst.
    exists (LVTuple (v :: vs)). econstructor; eauto.
  - subst.
    destruct (IHC eq_refl ρ) as [vc Hc].
    destruct (canonical_bool_lite ρ c vc HtyC Hc) as [b Hb].
    subst vc.
    destruct b.
    + destruct (IHT eq_refl ρ) as [v Hv].
      exists v. apply LE_IfTrue; assumption.
    + destruct (IHE eq_refl ρ) as [v Hv].
      exists v. apply LE_IfFalse; assumption.
Qed.

Theorem progress_lite :
  forall e t,
    lite_has_type [] e t ->
    forall ρ, exists v, lite_eval ρ e v.
Proof.
  intros e t HT ρ.
  eapply progress_lite_gen; eauto.
Qed.

End FoCoreLite.
