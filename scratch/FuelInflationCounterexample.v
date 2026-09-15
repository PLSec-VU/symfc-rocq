From SymCoreTheory Require Import SymCore ConCore Completeness Model.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.
Open Scope string_scope.

Fixpoint nest (k : nat) (t : expr) : expr :=
  match k with
  | O => t
  | S k' => EThunk · (nest k' t)
  end.

Fixpoint nots (e : expr) : nat :=
  match e with
  | EApp (EPrimOp _) a => S (nots a)
  | _ => O
  end.

Definition inflation (j : expr) : nat := 10 + 3 * nots j.

Fixpoint inflate_not (a : expr) : expr :=
  match a with
  | EThunk _ _ => a
  | EIf c t j =>
      match c, t with
      | ELit true, EThunk _ _ => nest (inflation j) t
      | _, _ => EIf c (inflate_not t) (inflate_not j)
      end
  | _ => model_reduce_prim PNot (a :: nil)
  end.

Definition fuel_reduce_prim (p : model_primop) (args : list expr) : expr :=
  match p, args with
  | PNot, a :: nil => inflate_not a
  | _, _ => model_reduce_prim p args
  end.

Definition fuel_solver : SymCoreSolver :=
  Build_SymCoreSolver
    model_sat (PCLit true) eq_refl fuel_reduce_prim
    erase_cast keep_coercion keep_type.

#[local] Existing Instance fuel_solver | 0.

Lemma inflate_not_plain : forall a,
  is_if a = false -> is_thunk a = false -> inflate_not a = model_reduce_prim PNot (a :: nil).
Proof. intros a Hi Ht. destruct a; try discriminate; reflexivity. Qed.

Lemma inflate_not_if : forall c t j,
  inflate_not (EIf c t j) = EIf c (inflate_not t) (inflate_not j)
  \/ (c = ELit true /\ is_thunk t = true /\ inflate_not (EIf c t j) = nest (inflation j) t).
Proof.
  intros c t j. destruct c; try (left; reflexivity).
  destruct l; [| left; reflexivity].
  destruct t; try (left; reflexivity).
  right. auto.
Qed.

Lemma inflate_not_shape : forall a,
  (is_if a = false /\ is_thunk a = false /\ inflate_not a = model_reduce_prim PNot (a :: nil))
  \/ is_if (inflate_not a) = true \/ is_thunk (inflate_not a) = true.
Proof.
  intros a. destruct (is_if a) eqn:Hi; [| destruct (is_thunk a) eqn:Ht].
  - destruct a; try discriminate.
    destruct (inflate_not_if a1 a2 a3) as [H | [_ [_ H]]]; rewrite H; [right; left; reflexivity |].
    right; right. reflexivity.
  - destruct a; try discriminate. right; right. reflexivity.
  - left. auto using inflate_not_plain.
Qed.

Lemma solvable_not_if_thunk : forall Γ e, Solvable Γ e -> is_if e = false /\ is_thunk e = false.
Proof. intros Γ e H. inversion H; auto. Qed.

Lemma if_thunk_not_solvable : forall Γ e,
  is_if e = true \/ is_thunk e = true -> ~ Solvable Γ e.
Proof. intros Γ e [H | H] Hs; apply solvable_not_if_thunk in Hs; destruct Hs; congruence. Qed.

Lemma if_thunk_unspool : forall e p args,
  is_if e = true \/ is_thunk e = true -> unspool_app e [] <> (EPrimOp p, args).
Proof. intros e p args [H | H]; destruct e; try discriminate; simpl; congruence. Qed.

Lemma if_thunk_not_ground : forall e,
  is_if e = true \/ is_thunk e = true -> smt_ground e = false.
Proof. intros e [H | H]; destruct e; try discriminate; reflexivity. Qed.

#[local] Instance fuel_reduce_prim_solvable : ReducePrimSolvable.
Proof.
  intros Γ p args H.
  destruct p; [exact (model_reduce_prim_solvable Γ PAnd args H) | | exact (model_reduce_prim_solvable Γ PIte args H)].
  destruct args as [| a [| b rest]]; [exact (model_reduce_prim_solvable Γ PNot _ H) | | exact (model_reduce_prim_solvable Γ PNot _ H)].
  cbn [reduce_prim fuel_solver fuel_reduce_prim].
  pose proof (Forall_inv H) as Ha.
  destruct (solvable_not_if_thunk Γ a Ha) as [Hi Ht].
  rewrite (inflate_not_plain a Hi Ht). exact (model_reduce_prim_solvable Γ PNot [a] H).
Qed.

#[local] Instance fuel_reduce_prim_saturated : ReducePrimSaturated.
Proof.
  intros p args p0 args0 H.
  destruct p; [exact (model_reduce_prim_saturated PAnd args p0 args0 H) | | exact (model_reduce_prim_saturated PIte args p0 args0 H)].
  destruct args as [| a [| b rest]]; [exact (model_reduce_prim_saturated PNot _ p0 args0 H) | | exact (model_reduce_prim_saturated PNot _ p0 args0 H)].
  cbn [reduce_prim fuel_solver fuel_reduce_prim] in H.
  destruct (inflate_not_shape a) as [[_ [_ Heq]] | Hshape].
  - rewrite Heq in H. exact (model_reduce_prim_saturated PNot [a] p0 args0 H).
  - exfalso. exact (if_thunk_unspool _ p0 args0 Hshape H).
Qed.

#[local] Instance fuel_reduce_prim_concore : ReducePrimConcore.
Proof.
  intros p args H.
  destruct p; [exact (model_reduce_prim_concore PAnd args H) | | exact (model_reduce_prim_concore PIte args H)].
  destruct args as [| a [| b rest]]; [exact (model_reduce_prim_concore PNot _ H) | | exact (model_reduce_prim_concore PNot _ H)].
  cbn [reduce_prim fuel_solver fuel_reduce_prim].
  pose proof (Forall_inv H) as Ha.
  destruct a; try (rewrite inflate_not_plain by reflexivity; exact (model_reduce_prim_concore PNot _ H)).
  - exfalso. exact (not_concore_if _ _ _ Ha).
  - exact Ha.
Qed.

Lemma denote_not_if_thunk : forall σ S e l, denote σ S e l -> is_if e = false /\ is_thunk e = false.
Proof.
  intros σ S e l [pc [Hden _]].
  specialize (Hden · (sym_free_env_empty S)).
  destruct e; try discriminate; auto.
Qed.

#[local] Instance fuel_reduce_prim_denote : ReducePrimDenote.
Proof.
  intros σ S p args ls H.
  destruct p; [exact (model_reduce_prim_denote σ S PAnd args ls H) | | exact (model_reduce_prim_denote σ S PIte args ls H)].
  destruct args as [| a [| b rest]]; [exact (model_reduce_prim_denote σ S PNot _ ls H) | | exact (model_reduce_prim_denote σ S PNot _ ls H)].
  cbn [reduce_prim fuel_solver fuel_reduce_prim].
  destruct ls as [| l ls']; [inversion H |].
  assert (Ha : denote σ S a l) by (inversion H; assumption).
  destruct (denote_not_if_thunk σ S a l Ha) as [Hi Ht].
  rewrite (inflate_not_plain a Hi Ht). exact (model_reduce_prim_denote σ S PNot _ _ H).
Qed.

#[local] Instance fuel_reduce_prim_ground_value : ReducePrimGroundValue.
Proof.
  intros p args H.
  destruct p; [exact (model_reduce_prim_ground_value PAnd args H) | | exact (model_reduce_prim_ground_value PIte args H)].
  destruct args as [| a [| b rest]]; [exact (model_reduce_prim_ground_value PNot _ H) | | exact (model_reduce_prim_ground_value PNot _ H)].
  cbn [reduce_prim fuel_solver fuel_reduce_prim] in *.
  destruct (inflate_not_shape a) as [[_ [_ Heq]] | Hshape].
  - rewrite Heq in *. exact (model_reduce_prim_ground_value PNot [a] H).
  - exfalso. rewrite (if_thunk_not_ground _ Hshape) in H. discriminate.
Qed.

#[local] Instance fuel_reduce_prim_ite_contains : ReducePrimIteContains.
Proof. exact model_reduce_prim_ite_contains. Qed.

Lemma contains_thunk_right : forall σ S Γ e X,
  contains σ S (EThunk Γ e) X -> is_thunk X = true.
Proof.
  intros σ S Γ e X H. inversion H; subst; try reflexivity; try assumption.
  match goal with [Hu : unspool_app _ _ = _ |- _] => discriminate Hu end.
Qed.

Lemma contains_plain_right : forall σ S a X,
  contains σ S a X -> is_if a = false -> is_thunk a = false ->
  is_if X = false /\ is_thunk X = false.
Proof.
  intros σ S a X H Hi Ht.
  split; [apply flat_not_if; eapply contains_flat_instance; exact H |].
  inversion H; subst; simpl in *; congruence.
Qed.

Lemma nest_contains : forall σ S k t X,
  contains σ S t X -> is_thunk X = true -> contains σ S (nest k t) X.
Proof.
  intros σ S k t X H Ht. induction k as [| k IH]; simpl; [exact H |].
  apply (Cont_Thunk_Outer σ S · ·); [apply Cont_Env_Empty | exact IH | exact Ht].
Qed.

Lemma lit_true_not_models_not : forall σ S, ~ models_not_cond σ S (ELit true).
Proof.
  intros σ S [pc [Hden Hm]].
  specialize (Hden · (sym_free_env_empty S)). simpl in Hden. injection Hden as <-.
  unfold models in Hm. cbn in Hm. discriminate.
Qed.

Lemma inflate_not_contains : forall σ S a_s a_c,
  contains σ S a_s a_c -> contains σ S (inflate_not a_s) (inflate_not a_c).
Proof.
  intros σ S a_s. induction a_s; intros a_c H;
    try (destruct (contains_plain_right _ _ _ _ H eq_refl eq_refl) as [Hi Ht];
         rewrite (inflate_not_plain a_c Hi Ht);
         rewrite inflate_not_plain by reflexivity;
         exact (model_reduce_prim_contains σ S PNot _ _ (Forall2_cons _ _ H (Forall2_nil _)))).
  - assert (Hi : is_if a_c = false)
      by (apply flat_not_if; eapply contains_flat_instance; exact H).
    destruct (inflate_not_if a_s1 a_s2 a_s3) as [Heq | [Hc [Ht Heq]]]; rewrite Heq.
    + inversion H; subst.
      * apply Cont_If_True; [assumption | apply IHa_s2; assumption].
      * apply Cont_If_False; [assumption | apply IHa_s3; assumption].
      * match goal with [Hu : unspool_app _ _ = _ |- _] => discriminate Hu end.
    + subst. inversion H; subst.
      * destruct a_s2; try discriminate.
        match goal with [Hc : instantiates _ _ (EThunk _ _) a_c |- _] =>
          pose proof (contains_thunk_right _ _ _ _ _ Hc) as Hth end.
        destruct a_c; try discriminate. cbn [inflate_not].
        apply nest_contains; assumption.
      * exfalso. eapply lit_true_not_models_not. eassumption.
      * match goal with [Hu : unspool_app _ _ = _ |- _] => discriminate Hu end.
  - pose proof (contains_thunk_right _ _ _ _ _ H) as Hth.
    destruct a_c; try discriminate. simpl. exact H.
Qed.

#[local] Instance fuel_reduce_prim_contains : ReducePrimContains.
Proof.
  intros σ S p args_s args_c H.
  destruct p; [exact (model_reduce_prim_contains σ S PAnd _ _ H) | | exact (model_reduce_prim_contains σ S PIte _ _ H)].
  destruct H as [| a_s a_c rest_s rest_c Ha Hrest];
    [exact (model_reduce_prim_contains σ S PNot _ _ (Forall2_nil _)) |].
  destruct Hrest as [| b_s b_c rs rc Hb Hr].
  - cbn [reduce_prim fuel_solver fuel_reduce_prim]. apply inflate_not_contains. exact Ha.
  - exact (model_reduce_prim_contains σ S PNot _ _ (Forall2_cons _ _ Ha (Forall2_cons _ _ Hb Hr))).
Qed.

#[local] Instance fuel_laws : ConCoreLaws.
Proof.
  exact (@concore_laws model_sorts fuel_solver
    fuel_reduce_prim_solvable fuel_reduce_prim_saturated
    fuel_reduce_prim_concore model_cast_expr_concore
    model_models_sat model_prim_value_and
    fuel_reduce_prim_contains fuel_reduce_prim_denote fuel_reduce_prim_ground_value
    fuel_reduce_prim_ite_contains model_cast_expr_contains
    model_subst_coerc_contains_env model_subst_type_contains_env).
Qed.
