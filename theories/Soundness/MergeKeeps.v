From SymCoreTheory Require Export ConCore.Determinism Soundness.Instance.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.

Section MergeKeeps.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Lemma contains_ite_prim : forall σ p a b,
  contains_prim σ (PApp op_ite (p :: a :: b :: nil))
    (PLit (if lit_eq_dec (prim_denote σ p) lit_true then prim_denote σ a else prim_denote σ b)).
Proof.
  intros σ p a b. apply Contains_PDenote.
  - simpl. rewrite op_ite_arity. reflexivity.
  - simpl. apply prim_value_ite.
Qed.

Lemma same_shape_length : forall (A : Type) (l1 l2 : list A),
  same_shape l1 l2 = true -> length l1 = length l2.
Proof.
  intros A l1 l2 H. apply Nat.eqb_eq. exact H.
Qed.

Lemma zip_tif_keeps : forall σ p ts1 ts2 tsc,
  σ ⊨ p -> Forall2 (contains_thunk σ) ts1 tsc -> length ts1 = length ts2 ->
  Forall2 (contains_thunk σ) (zip_tif p ts1 ts2) tsc.
Proof.
  intros σ p ts1 ts2 tsc Hp Hall. revert ts2.
  induction Hall as [| t1 tc ts1' tsc' Ht _ IH]; intros [| t2 ts2'] Hlen;
    simpl in *; try discriminate; constructor.
  - apply Contains_TIfT; assumption.
  - apply IH. lia.
Qed.

Lemma zip_tif_keeps_false : forall σ p ts1 ts2 tsc,
  σ ⊨ pc_not p -> Forall2 (contains_thunk σ) ts2 tsc -> length ts1 = length ts2 ->
  Forall2 (contains_thunk σ) (zip_tif p ts1 ts2) tsc.
Proof.
  intros σ p ts1 ts2 tsc Hp Hall. revert ts1.
  induction Hall as [| t2 tc ts2' tsc' Ht _ IH]; intros [| t1 ts1'] Hlen;
    simpl in *; try discriminate; constructor.
  - apply Contains_TIfF; assumption.
  - apply IH. lia.
Qed.

Ltac split_merge_test :=
  match goal with
  | |- context [if ?b then _ else _] =>
      let Hb := fresh "Hb" in
      destruct b eqn:Hb;
      [ repeat match goal with
        | H : _ && _ = true |- _ => apply andb_prop in H as [? ?]
        | H : String.eqb _ _ = true |- _ => apply String.eqb_eq in H; subst
        | H : dec_eqb _ _ _ = true |- _ => apply dec_eqb_eq in H; subst
        | H : bottom_eqb _ _ = true |- _ => apply bottom_eqb_eq in H; subst
        | H : same_shape _ _ = true |- _ => apply same_shape_length in H
        end
      | ]
  end.

Lemma ite_leaf_keeps : forall σ p vt vf vc,
  σ ⊨ p -> contains_val σ vt vc -> contains_val σ (ite_leaf p vt vf) vc.
Proof.
  intros σ p vt vf vc Hp Hvt.
  destruct vt, vf; simpl; try (apply Contains_VIfT; assumption);
    try split_merge_test; try (apply Contains_VIfT; assumption);
    try assumption; inversion Hvt; subst.
  - apply Contains_VPrim. match goal with H : contains_prim _ _ _ |- _ => apply contains_prim_target in H; subst end.
    pose proof (contains_ite_prim σ p p0 p1) as Hite.
    destruct (lit_eq_dec (prim_denote σ p) lit_true); [exact Hite | contradiction].
  - constructor. apply zip_tif_keeps; assumption.
  - constructor. apply zip_tif_keeps; assumption.
Qed.

Lemma ite_leaf_keeps_false : forall σ p vt vf vc,
  σ ⊨ pc_not p -> contains_val σ vf vc -> contains_val σ (ite_leaf p vt vf) vc.
Proof.
  intros σ p vt vf vc Hp Hvf. pose proof (proj1 (models_not σ p) Hp) as Hnot.
  destruct vt, vf; simpl; try (apply Contains_VIfF; assumption);
    try split_merge_test; try (apply Contains_VIfF; assumption);
    try assumption; inversion Hvf; subst.
  - apply Contains_VPrim. match goal with H : contains_prim _ _ _ |- _ => apply contains_prim_target in H; subst end.
    pose proof (contains_ite_prim σ p p0 p1) as Hite.
    destruct (lit_eq_dec (prim_denote σ p) lit_true); [contradiction | exact Hite].
  - constructor. apply zip_tif_keeps_false; assumption.
  - constructor. apply zip_tif_keeps_false; assumption.
Qed.

Lemma ite_keeps : forall σ p vt vf vc,
  σ ⊨ p -> contains_val σ vt vc -> contains_val σ (ite p vt vf) vc.
Proof.
  intros σ p vt. induction vt; intros vf vc Hp Hvt;
    destruct vf; try (apply ite_leaf_keeps; assumption).
  simpl. split_merge_test; [| apply Contains_VIfT; assumption].
  inversion Hvt; subst. constructor. apply IHvt; assumption.
Qed.

Lemma ite_keeps_false : forall σ p vt vf vc,
  σ ⊨ pc_not p -> contains_val σ vf vc -> contains_val σ (ite p vt vf) vc.
Proof.
  intros σ p vt. induction vt; intros vf vc Hp Hvf;
    destruct vf; try (apply ite_leaf_keeps_false; assumption).
  simpl. split_merge_test; [| apply Contains_VIfF; assumption].
  inversion Hvf; subst. constructor. apply IHvt; assumption.
Qed.

Lemma merge_keeps : forall σ v vc, contains_val σ v vc -> contains_val σ (merge v) vc.
Proof.
  intros σ v vc Hv. destruct v; try exact Hv. simpl.
  inversion Hv; subst; [apply ite_keeps | apply ite_keeps_false]; assumption.
Qed.

Lemma merge_ground_condition_keeps : forall σ a b,
  contains_val σ (ite (PLit lit_true) (VPrim a) (VPrim b)) (VPrim (PLit (prim_denote σ a))).
Proof.
  intros σ a b. simpl. apply Contains_VPrim.
  pose proof (contains_ite_prim σ (PLit lit_true) a b) as Hite. simpl in Hite.
  destruct (lit_eq_dec lit_true lit_true); [exact Hite | contradiction].
Qed.

End MergeKeeps.

Section LiftPrimKeeps.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.
Context {reduce_prim_literal_law : ReducePrimLiteral}
  {reduce_prim_contains_law : ReducePrimContains}.

Lemma lift_prim_from_keeps : forall σ op vs_s vs_c ps ls,
  length ps + length vs_s = primop_arity op ->
  Forall2 (contains_prim σ) ps (map PLit ls) ->
  Forall2 (contains_val σ) vs_s vs_c -> Forall concrete_value vs_c ->
  contains_val σ (lift_prim_from op ps vs_s) (lift_prim_from op (map PLit ls) vs_c).
Proof.
  intros σ op vs_s vs_c ps ls Hlen Hps Hall Hconc. revert ps ls Hlen Hps Hconc.
  induction Hall as [| v_s v_c rest_s rest_c Hv Hrest IH]; intros ps ls Hlen Hps Hconc.
  - simpl in *. rewrite reduce_prim_literal.
    + apply reduce_prim_contains; [lia | exact Hps].
    + apply Forall2_length in Hps. rewrite length_map in Hps. lia.
  - inversion Hconc as [| ? ? Hvc Hrestc]; subst. clear Hconc. simpl.
    revert v_c Hv Hvc.
    induction v_s; intros v_c Hv Hvc; inversion Hv; subst; simpl;
      try solve [repeat constructor | constructor; assumption].
    + match goal with H : contains_prim _ _ _ |- _ =>
        pose proof (contains_prim_target _ _ _ H) as Hq; subst end.
      change [PLit (prim_denote σ p)] with (map PLit [prim_denote σ p]). rewrite <- map_app.
      apply IH.
      * rewrite length_app. simpl in *. lia.
      * rewrite map_app. apply Forall2_app; [exact Hps | constructor; [assumption | constructor]].
      * exact Hrestc.
    + apply ite_keeps; [assumption | apply IHv_s1; assumption].
    + apply ite_keeps_false; [assumption | apply IHv_s2; assumption].
Qed.

Lemma lift_prim_keeps : forall σ op vs_s vs_c,
  length vs_s = primop_arity op ->
  Forall2 (contains_val σ) vs_s vs_c -> Forall concrete_value vs_c ->
  contains_val σ (lift_prim op vs_s) (lift_prim op vs_c).
Proof.
  intros σ op vs_s vs_c Hlen Hall Hconc.
  exact (lift_prim_from_keeps σ op vs_s vs_c [] [] Hlen (Forall2_nil _) Hall Hconc).
Qed.

End LiftPrimKeeps.
