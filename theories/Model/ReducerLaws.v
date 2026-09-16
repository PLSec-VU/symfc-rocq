From SymCoreTheory Require Export Model.Lifting.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.

(** ========================================================================= *)
(** The laws about the reducer                                                *)
(** ========================================================================= *)

Lemma denote_args : forall σ S args ls,
  Forall2 (denote σ S) args ls ->
  exists pcs, Forall2 (denotes S) args pcs /\ map (pc_value σ) pcs = ls.
Proof.
  intros σ S args ls H.
  induction H as [| a l args ls [pc [Hd Hv]] _ [pcs [Hds Hvs]]].
  - exists nil. split; [constructor | reflexivity].
  - exists (pc :: pcs). split; [constructor; assumption |].
    cbn [map]. rewrite Hv, Hvs. reflexivity.
Qed.

Lemma denotes_all_flat : forall S args pcs,
  Forall2 (denotes S) args pcs -> Forall (fun a => flat a = true) args.
Proof.
  intros S args pcs H. induction H; constructor; [eapply denotes_flat; eassumption | assumption].
Qed.

Lemma unbranched_denote : forall σ S (p : primop) args ls,
  Forall2 (denote σ S) args ls ->
  denote σ S (reduce_unbranched p args) (prim_value p ls).
Proof.
  intros σ S p args ls HF.
  unfold reduce_unbranched.
  destruct (denote_args σ S args ls HF) as [pcs [Hds Hvs]].
  destruct (Nat.eqb (length args) (model_arity p)) eqn:Hlen.
  - rewrite (lift_flat _ (op_spine_flat p args (denotes_all_flat S args pcs Hds))),
            (fold_leaves_not_if _ (op_spine_not_if p args)).
    assert (Hd : denotes S (op_spine p args) (PCPrim p pcs))
      by (apply (op_spine_denotes S args pcs Hds (EPrimOp p) p nil); intros Γ _; reflexivity).
    assert (Hv : pc_value σ (PCPrim p pcs) = prim_value p ls)
      by (change (prim_value p (map (pc_value σ) pcs) = prim_value p ls); rewrite Hvs; reflexivity).
    unfold fold_leaf. destruct (smt_ground (op_spine p args)) eqn:Hg.
    + pose proof (Hd · (sym_free_env_empty S)) as He.
      rewrite (closed_value_of _ _ He).
      destruct (ground_pc_value _ _ closed_model σ Hg He) as [Hcl _].
      rewrite Hcl, Hv. apply denote_lit.
    + exists (PCPrim p pcs). split; [exact Hd | exact Hv].
  - apply Nat.eqb_neq in Hlen.
    change (prim_value p ls) with (model_prim_value p ls).
    rewrite model_prim_value_wrong_arity; [apply denote_lit |].
    rewrite <- Hvs, length_map, <- (Forall2_length Hds). exact Hlen.
Qed.

Lemma fold_leaves_ground : forall T,
  smt_ground (fold_leaves T) = true -> exists l, fold_leaves T = ELit l.
Proof.
  intros T H. destruct (is_if T) eqn:Hif.
  - destruct T; simpl in Hif, H; discriminate.
  - rewrite (fold_leaves_not_if T Hif) in *. unfold fold_leaf in *.
    destruct (smt_ground T) eqn:Hg; [eexists; reflexivity | congruence].
Qed.

Lemma unbranched_ground_value : forall p args,
  smt_ground (reduce_unbranched p args) = true ->
  exists l, reduce_unbranched p args = ELit l.
Proof.
  intros p args H.
  unfold reduce_unbranched in *.
  destruct (Nat.eqb (length args) (model_arity p));
    [apply fold_leaves_ground; exact H | eexists; reflexivity].
Qed.

Lemma unbranched_saturated : forall p args p0 args0,
  unspool_app (reduce_unbranched p args) nil = (EPrimOp p0, args0) ->
  length args0 = model_arity p0.
Proof.
  intros p args p0 args0 H.
  unfold reduce_unbranched in H.
  destruct (Nat.eqb (length args) (model_arity p)) eqn:Hlen; [| discriminate H].
  apply Nat.eqb_eq in Hlen.
  revert H. generalize (leaves_lift_spine p args).
  generalize (lift_branches (op_spine p args)). intros T Hl.
  destruct Hl as [e Hif [L [-> HL]] | c t f _ _]; intros H.
  - rewrite (fold_leaves_not_if _ Hif) in H. unfold fold_leaf in H.
    destruct (smt_ground (op_spine p L)); [simpl in H; discriminate H |].
    rewrite op_spine_unspool in H. injection H as <- <-. rewrite HL. exact Hlen.
  - simpl in H. discriminate H.
Qed.

Lemma solvable_op_spine : forall Γ args h,
  Solvable Γ h -> is_op_app h = true -> Forall (Solvable Γ) args ->
  Solvable Γ (fold_left EApp args h).
Proof.
  intros Γ args h Hh Hop HF. revert h Hh Hop.
  induction HF as [| a args Ha Hargs IH]; intros h Hh Hop; [exact Hh |].
  simpl. apply IH; [apply Solvable_AppPrim; [exact Hop | exact Hh | exact Ha] | exact Hop].
Qed.

Lemma unbranched_solvable : forall Γ p args,
  Forall (Solvable Γ) args -> Solvable Γ (reduce_unbranched p args).
Proof.
  intros Γ p args HF. unfold reduce_unbranched.
  destruct (Nat.eqb (length args) (model_arity p)); [| apply Solvable_Lit].
  assert (Hs : Solvable Γ (op_spine p args))
    by (apply solvable_op_spine; [apply Solvable_PrimOp | reflexivity | exact HF]).
  rewrite (lift_flat _ (solvable_flat Γ _ Hs)), (fold_leaves_not_if _ (op_spine_not_if p args)).
  unfold fold_leaf. destruct (smt_ground (op_spine p args)); [apply Solvable_Lit | exact Hs].
Qed.

Lemma unbranched_concore : forall p args,
  Forall concore_expr args -> concore_expr (reduce_unbranched p args).
Proof.
  intros p args HF. unfold reduce_unbranched.
  destruct (Nat.eqb (length args) (model_arity p)); [| apply Con_Lit].
  assert (Hc : concore_expr (op_spine p args))
    by (apply concore_fold_left_app; [exact HF | apply Con_PrimOp]).
  rewrite (lift_flat _ (concore_flat _ Hc)), (fold_leaves_not_if _ (op_spine_not_if p args)).
  unfold fold_leaf. destruct (smt_ground (op_spine p args)); [apply Con_Lit | exact Hc].
Qed.

Lemma split_arg_not_if : forall k a, is_if a = false -> split_arg k a = k a.
Proof. intros k a H. destruct a; simpl in *; congruence. Qed.

Lemma split_args_not_if : forall k args,
  Forall (fun a => is_if a = false) args -> split_args k args = k args.
Proof.
  intros k args H. revert k. induction H as [| a args Ha _ IH]; intros k; [reflexivity |].
  cbn [split_args]. rewrite split_arg_not_if by exact Ha. apply IH.
Qed.

Lemma split_args_top : forall k args,
  split_args k args = k args \/ is_if (split_args k args) = true.
Proof.
  intros k args. revert k. induction args as [| a rest IH]; intros k; [left; reflexivity |].
  cbn [split_args]. destruct (is_if a) eqn:Ha.
  - destruct a; simpl in Ha; try discriminate. right. reflexivity.
  - rewrite split_arg_not_if by exact Ha. apply (IH (fun rest' => k (a :: rest'))).
Qed.

Lemma flat_all_not_if : forall args,
  Forall (fun a => flat a = true) args -> Forall (fun a => is_if a = false) args.
Proof. intros args H. eapply Forall_impl; [| exact H]. exact flat_not_if. Qed.

Lemma contains_instances_not_if : forall σ S args_s args_c,
  Forall2 (contains σ S) args_s args_c -> Forall (fun a => is_if a = false) args_c.
Proof.
  intros σ S args_s args_c H. induction H; constructor; [| assumption].
  apply flat_not_if. eapply contains_flat_instance. eassumption.
Qed.

Lemma smt_term_need : forall e, smt_term e = true -> smt_need e = Some 0.
Proof.
  intros e H. unfold smt_term in H.
  destruct (smt_need e) as [[| n] |]; [reflexivity | discriminate H | discriminate H].
Qed.

Lemma smt_terms_of_forallb : forall args,
  forallb smt_term args = true -> Forall (fun a => smt_need a = Some 0) args.
Proof.
  intros args H. apply Forall_forall. intros a Ha.
  apply smt_term_need. exact (proj1 (forallb_forall _ _) H a Ha).
Qed.

Lemma smt_need_app : forall f a n,
  smt_need (EApp f a) = Some n -> smt_need f = Some (Datatypes.S n) /\ smt_need a = Some 0.
Proof.
  intros f a n H. simpl in H.
  destruct (smt_need f) as [[| m] |]; destruct (smt_need a) as [[| k] |];
    try discriminate H.
  injection H as <-. split; reflexivity.
Qed.

Lemma smt_need_op_app : forall e n, smt_need e = Some (Datatypes.S n) -> is_op_app e = true.
Proof.
  induction e; intros n H; try (simpl in H; discriminate H); try reflexivity.
  destruct (smt_need_app _ _ _ H) as [H1 _]. exact (IHe1 _ H1).
Qed.

Lemma smt_need_unspool : forall e n acc (q : model_primop) qs,
  smt_need e = Some n -> unspool_app e acc = (EPrimOp q, qs) ->
  n + length qs = model_arity q + length acc.
Proof.
  induction e; intros n acc q qs Hn Hu; simpl in Hu; try discriminate Hu.
  - injection Hu as Hq Hqs. subst qs. simpl in Hn. injection Hn as <-.
    change (model_arity p + length acc = model_arity q + length acc). rewrite Hq. reflexivity.
  - destruct (smt_need_app _ _ _ Hn) as [H1 _].
    pose proof (IHe1 _ _ _ _ H1 Hu) as H. simpl in H. lia.
Qed.

Lemma smt_need_flat : forall e n, smt_need e = Some n -> flat e = true.
Proof.
  induction e; intros n H; try (simpl in H; discriminate H); try reflexivity.
  destruct (smt_need_app _ _ _ H) as [H1 H2]. simpl. rewrite (IHe1 _ H1), (IHe2 _ H2). reflexivity.
Qed.

Lemma smt_need_closed_ground : forall e n,
  smt_need e = Some n -> closed_term e -> smt_ground e = true.
Proof.
  induction e; intros n Hn Hc; try (simpl in Hn; discriminate Hn); try reflexivity.
  - unfold closed_term in Hc. inversion Hc; subst.
    match goal with [H : In _ nil |- _] => destruct H end.
  - destruct (smt_need_app _ _ _ Hn) as [H1 H2].
    unfold closed_term in Hc. inversion Hc; subst. simpl.
    rewrite (smt_need_op_app _ _ H1), (IHe1 _ H1 ltac:(assumption)), (IHe2 _ H2 ltac:(assumption)).
    reflexivity.
Qed.

Lemma contains_smt_need : forall σ S L X n,
  contains σ S L X -> smt_need L = Some n -> smt_need X = Some n.
Proof.
  intros σ S L X n H. revert n.
  induction H; intros n Hn; try (simpl in Hn; discriminate Hn); try exact Hn.
  - destruct (smt_need_app _ _ _ Hn) as [H1 H2].
    simpl. rewrite (IHcontains1 _ H1), (IHcontains2 _ H2). reflexivity.
  - match goal with
    | [ Hu : unspool_app es nil = (EPrimOp ?q, ?qs), Hl : length ?qs = primop_arity ?q |- _ ] =>
        pose proof (smt_need_unspool es n nil q qs Hn Hu) as E;
        change (length qs = model_arity q) in Hl
    end.
    simpl in E. assert (n = 0) by lia. subst n. reflexivity.
Qed.

Lemma ground_denote_value : forall σ S a l,
  smt_ground a = true -> denote σ S a l -> l = closed_value a.
Proof.
  intros σ S a l Hg [pc [Hd Hv]].
  pose proof (Hd · (sym_free_env_empty S)) as He.
  rewrite (closed_value_of a pc He), <- Hv.
  destruct (ground_pc_value a pc σ closed_model Hg He) as [E _]. exact E.
Qed.

Lemma fold_leaf_denote : forall σ S a l, denote σ S a l -> denote σ S (fold_leaf a) l.
Proof.
  intros σ S a l H. unfold fold_leaf. destruct (smt_ground a) eqn:Hg; [| exact H].
  rewrite <- (ground_denote_value σ S a l Hg H). apply denote_lit.
Qed.

Lemma fold_leaf_contains_k : forall σ S a l,
  smt_need a = Some 0 -> denote σ S a l ->
  exists k, k <= smt_size a /\ contains_k σ S k (fold_leaf a) (ELit l).
Proof.
  intros σ S a l Hn Hd. unfold fold_leaf. destruct (smt_ground a) eqn:Hg.
  - rewrite <- (ground_denote_value σ S a l Hg Hd). exists 0. split; [lia | apply ContK_Lit].
  - destruct a; try (simpl in Hg; discriminate Hg); try (simpl in Hn; discriminate Hn).
    + destruct (denote_var_inv σ S v l Hd) as [Hs ->].
      exists 0. split; [lia | apply ContK_Var_Sym; exact Hs].
    + destruct (smt_need_app _ _ _ Hn) as [H1 _].
      assert (Hop : is_op_app (EApp a1 a2) = true) by exact (smt_need_op_app _ _ H1).
      destruct (is_op_app_unspool _ Hop) as [q [qs Hu]].
      exists (smt_size (EApp a1 a2)). split; [lia |].
      apply (ContK_Denote σ S _ q qs l Hu); [| exact Hg | exact Hd].
      pose proof (smt_need_unspool _ 0 nil q qs Hn Hu) as E. simpl in E.
      change (length qs = model_arity q). lia.
Qed.

Lemma fold_leaf_ground : forall a, smt_ground (fold_leaf a) = true -> exists l, fold_leaf a = ELit l.
Proof.
  intros a H. unfold fold_leaf in *. destruct (smt_ground a) eqn:Hg; [eexists; reflexivity | congruence].
Qed.

Lemma lit_of_value : forall σ S a b l, lit_of a = Some b -> denote σ S a l -> l = b.
Proof.
  intros σ S a b l H Hd. unfold lit_of in H. destruct (smt_ground a) eqn:Hg; [| discriminate H].
  injection H as <-. exact (ground_denote_value σ S a l Hg Hd).
Qed.

Lemma is_false_lit_value : forall σ S a l, is_false_lit a = true -> denote σ S a l -> l = false.
Proof.
  intros σ S a l H Hd. unfold is_false_lit in H.
  destruct (lit_of a) as [[|] |] eqn:E; try discriminate H.
  exact (lit_of_value σ S a false l E Hd).
Qed.

Lemma rewrite_prim_arity : forall p args r,
  rewrite_prim p args = Some r -> length args = model_arity p.
Proof.
  intros p args r H.
  destruct p; destruct args as [| a1 [| a2 [| a3 [| a4 args]]]]; simpl in H; try discriminate H;
    reflexivity.
Qed.

Lemma rewrite_prim_shape : forall p args r,
  rewrite_prim p args = Some r -> r = ELit false \/ exists a, In a args /\ r = fold_leaf a.
Proof.
  intros p args r H.
  destruct p; destruct args as [| a1 [| a2 [| a3 [| a4 args]]]]; simpl in H; try discriminate H.
  - destruct (is_false_lit a1 || is_false_lit a2); [| discriminate H].
    injection H as <-. left. reflexivity.
  - destruct (lit_of a1) as [[|] |].
    + injection H as <-. right. exists a2. split; [simpl; auto | reflexivity].
    + injection H as <-. right. exists a3. split; [simpl; auto | reflexivity].
    + destruct (expr_eqb a2 a3); [| discriminate H].
      injection H as <-. right. exists a2. split; [simpl; auto | reflexivity].
Qed.

Lemma simplify_facts : forall p args r,
  simplify p args = Some r ->
  Forall (fun a => smt_need a = Some 0) args /\ rewrite_prim p args = Some r.
Proof.
  intros p args r H. unfold simplify in H.
  destruct (forallb smt_term args && negb (forallb smt_ground args)) eqn:E; [| discriminate H].
  apply andb_prop in E as [Ht _]. split; [exact (smt_terms_of_forallb args Ht) | exact H].
Qed.

Lemma rewrite_prim_value : forall σ S p args vs r,
  Forall (fun a => smt_need a = Some 0) args -> Forall2 (denote σ S) args vs ->
  rewrite_prim p args = Some r ->
  denote σ S r (model_prim_value p vs) /\
  exists k, k <= list_sum (map smt_size args) /\ contains_k σ S k r (ELit (model_prim_value p vs)).
Proof.
  intros σ S p args vs r Ht Hd Hr.
  destruct p; destruct args as [| a1 [| a2 [| a3 [| a4 args]]]]; simpl in Hr; try discriminate Hr.
  - inversion Hd as [| x1 v1 l1 vs1 Hd1 Hd1']; subst.
    inversion Hd1' as [| x2 v2 l2 vs2 Hd2 Hd2']; subst.
    inversion Hd2'; subst.
    assert (Hv : r = ELit false /\ v1 && v2 = false).
    { destruct (is_false_lit a1) eqn:E1; destruct (is_false_lit a2) eqn:E2; simpl in Hr;
        try discriminate Hr; injection Hr as <-; split; try reflexivity.
      - rewrite (is_false_lit_value σ S a1 v1 E1 Hd1). reflexivity.
      - rewrite (is_false_lit_value σ S a1 v1 E1 Hd1). reflexivity.
      - rewrite (is_false_lit_value σ S a2 v2 E2 Hd2). apply andb_false_r. }
    destruct Hv as [-> Hv]. simpl. rewrite Hv.
    split; [apply denote_lit | exists 0; split; [lia | apply ContK_Lit]].
  - inversion Hd as [| x1 v1 l1 vs1 Hd1 Hd1']; subst.
    inversion Hd1' as [| x2 v2 l2 vs2 Hd2 Hd2']; subst.
    inversion Hd2' as [| x3 v3 l3 vs3 Hd3 Hd3']; subst.
    inversion Hd3'; subst.
    inversion Ht as [| y1 t1 Ht1 Ht1']; subst.
    inversion Ht1' as [| y2 t2 Ht2 Ht2']; subst.
    inversion Ht2' as [| y3 t3 Ht3 _]; subst.
    destruct (lit_of a1) as [[|] |] eqn:Ec.
    + injection Hr as <-. rewrite (lit_of_value σ S a1 true v1 Ec Hd1).
      split; [exact (fold_leaf_denote σ S a2 v2 Hd2) |].
      destruct (fold_leaf_contains_k σ S a2 v2 Ht2 Hd2) as [k [Hk Hc]].
      exists k. split; [simpl; lia | exact Hc].
    + injection Hr as <-. rewrite (lit_of_value σ S a1 false v1 Ec Hd1).
      split; [exact (fold_leaf_denote σ S a3 v3 Hd3) |].
      destruct (fold_leaf_contains_k σ S a3 v3 Ht3 Hd3) as [k [Hk Hc]].
      exists k. split; [simpl; lia | exact Hc].
    + destruct (expr_eqb a2 a3) eqn:Eab; [| discriminate Hr].
      injection Hr as <-. apply expr_eqb_eq in Eab. subst a3.
      rewrite (denote_functional σ S a2 v3 v2 Hd3 Hd2).
      assert (Hvv : model_prim_value PIte (v1 :: v2 :: v2 :: nil) = v2) by (destruct v1; reflexivity).
      rewrite Hvv.
      split; [exact (fold_leaf_denote σ S a2 v2 Hd2) |].
      destruct (fold_leaf_contains_k σ S a2 v2 Ht2 Hd2) as [k [Hk Hc]].
      exists k. split; [simpl; lia | exact Hc].
Qed.

Lemma simplify_closed_none : forall p args, Forall closed_term args -> simplify p args = None.
Proof.
  intros p args H. unfold simplify.
  destruct (forallb smt_term args) eqn:Ht; [| reflexivity].
  assert (Hg : forallb smt_ground args = true).
  { apply forallb_forall. intros a Ha.
    apply (smt_need_closed_ground a 0).
    - apply smt_term_need. exact (proj1 (forallb_forall _ _) Ht a Ha).
    - exact (proj1 (Forall_forall _ _) H a Ha). }
  rewrite Hg. reflexivity.
Qed.

Lemma fold_leaf_solvable : forall Γ a, Solvable Γ a -> Solvable Γ (fold_leaf a).
Proof. intros Γ a H. unfold fold_leaf. destruct (smt_ground a); [apply Solvable_Lit | exact H]. Qed.

Lemma fold_leaf_concore : forall a, concore_expr a -> concore_expr (fold_leaf a).
Proof. intros a H. unfold fold_leaf. destruct (smt_ground a); [apply Con_Lit | exact H]. Qed.

Lemma fold_leaf_sym_scoped : forall S L a, sym_scoped S L a -> sym_scoped S L (fold_leaf a).
Proof. intros S L a H. unfold fold_leaf. destruct (smt_ground a); [apply SymScoped_Lit | exact H]. Qed.

Lemma simplify_result : forall (P : expr -> Prop) p args r,
  P (ELit false) -> Forall (fun a => P (fold_leaf a)) args ->
  simplify p args = Some r -> P r.
Proof.
  intros P p args r Hl Ha Hs.
  destruct (simplify_facts p args r Hs) as [_ Hr].
  destruct (rewrite_prim_shape p args r Hr) as [-> | [a [Hin ->]]]; [exact Hl |].
  exact (proj1 (Forall_forall _ _) Ha a Hin).
Qed.

Lemma graft_arg_sym_scoped : forall S L f a,
  sym_scoped S L f -> sym_scoped S L a -> sym_scoped S L (graft_arg f a).
Proof.
  intros S L f a Hf. induction a; intros Ha; try (apply SymScoped_App; assumption).
  inversion Ha; subst. simpl. apply SymScoped_If; auto.
Qed.

Lemma graft_sym_scoped : forall S L f a,
  sym_scoped S L f -> sym_scoped S L a -> sym_scoped S L (graft f a).
Proof.
  intros S L f a Hf Ha. induction f; try (apply graft_arg_sym_scoped; assumption).
  inversion Hf; subst. simpl. apply SymScoped_If; auto.
Qed.

Lemma lift_branches_sym_scoped : forall S L e,
  sym_scoped S L e -> sym_scoped S L (lift_branches e).
Proof.
  intros S L e. induction e; intros H; try exact H.
  - inversion H; subst. simpl. apply graft_sym_scoped; auto.
  - inversion H; subst. simpl. apply SymScoped_If; auto.
Qed.

Lemma fold_leaves_sym_scoped : forall S L e,
  sym_scoped S L e -> sym_scoped S L (fold_leaves e).
Proof.
  intros S L e. induction e; intros H; try (apply fold_leaf_sym_scoped; exact H).
  inversion H; subst. simpl. apply SymScoped_If; auto.
Qed.

Lemma unbranched_sym_scoped : forall S L p args,
  Forall (sym_scoped S L) args -> sym_scoped S L (reduce_unbranched p args).
Proof.
  intros S L p args H. unfold reduce_unbranched.
  destruct (Nat.eqb (length args) (model_arity p)); [| apply SymScoped_Lit].
  apply fold_leaves_sym_scoped. apply lift_branches_sym_scoped.
  apply sym_scoped_fold_left_app; [exact H | apply SymScoped_PrimOp].
Qed.

Lemma split_arg_sym_scoped : forall S L K a,
  sym_scoped S L a ->
  (forall a', sym_scoped S L a' -> sym_scoped S L (K a')) ->
  sym_scoped S L (split_arg K a).
Proof.
  intros S L K a. induction a; intros Ha HK; try (apply HK; exact Ha).
  inversion Ha; subst. simpl.
  apply SymScoped_If; [assumption | apply IHa2 | apply IHa3]; assumption.
Qed.

Lemma split_args_sym_scoped : forall S L args k,
  Forall (sym_scoped S L) args ->
  (forall ls, Forall (sym_scoped S L) ls -> sym_scoped S L (k ls)) ->
  sym_scoped S L (split_args k args).
Proof.
  intros S L args. induction args as [| a rest IH]; intros k Hargs Hk; [apply Hk; constructor |].
  inversion Hargs; subst. cbn [split_args].
  apply split_arg_sym_scoped; [assumption |].
  intros a' Ha'. apply IH; [assumption |].
  intros ls Hls. apply Hk. constructor; assumption.
Qed.

#[export] Instance model_reduce_prim_scoped : ReducePrimScoped.
Proof.
  intros S L p args H.
  change (sym_scoped S L (model_reduce_prim p args)). unfold model_reduce_prim.
  apply split_args_sym_scoped; [exact H |].
  intros ls Hls. unfold simplify_unbranched.
  destruct (simplify p ls) as [r |] eqn:Hs; [| exact (unbranched_sym_scoped S L p ls Hls)].
  apply (simplify_result (sym_scoped S L) p ls r ltac:(apply SymScoped_Lit)); [| exact Hs].
  eapply Forall_impl; [| exact Hls]. intros a Ha. exact (fold_leaf_sym_scoped S L a Ha).
Qed.

#[export] Instance model_cast_expr_scoped : CastExprScoped.
Proof. intros S L e γ H. exact H. Qed.

#[export] Instance model_reduce_prim_denote : ReducePrimDenote.
Proof.
  intros σ S p args ls HF.
  change (denote σ S (model_reduce_prim p args) (prim_value p ls)).
  unfold model_reduce_prim.
  destruct (denote_args σ S args ls HF) as [pcs [Hds _]].
  rewrite (split_args_not_if _ args (flat_all_not_if _ (denotes_all_flat S args pcs Hds))).
  unfold simplify_unbranched.
  destruct (simplify p args) as [r |] eqn:Hs; [| apply unbranched_denote; exact HF].
  destruct (simplify_facts p args r Hs) as [Ht Hr].
  exact (proj1 (rewrite_prim_value σ S p args ls r Ht HF Hr)).
Qed.

#[export] Instance model_reduce_prim_ground_value : ReducePrimGroundValue.
Proof.
  intros p args H.
  change (smt_ground (model_reduce_prim p args) = true) in H.
  change (exists l, model_reduce_prim p args = ELit l).
  unfold model_reduce_prim in *.
  destruct (split_args_top (simplify_unbranched p) args) as [E | E].
  - rewrite E in *. unfold simplify_unbranched in *.
    destruct (simplify p args) as [r |] eqn:Hs; [| apply unbranched_ground_value; exact H].
    destruct (simplify_facts p args r Hs) as [_ Hr].
    destruct (rewrite_prim_shape p args r Hr) as [-> | [a [_ ->]]];
      [eexists; reflexivity | exact (fold_leaf_ground a H)].
  - destruct (split_args (simplify_unbranched p) args); simpl in E, H; discriminate.
Qed.

#[export] Instance model_reduce_prim_saturated : ReducePrimSaturated.
Proof.
  intros p args p0 args0 H.
  change (unspool_app (model_reduce_prim p args) nil = (EPrimOp p0, args0)) in H.
  change (length args0 = model_arity p0).
  unfold model_reduce_prim in H.
  destruct (split_args_top (simplify_unbranched p) args) as [E | E].
  - rewrite E in H. unfold simplify_unbranched in H.
    destruct (simplify p args) as [r |] eqn:Hs; [| exact (unbranched_saturated p args p0 args0 H)].
    destruct (simplify_facts p args r Hs) as [Ht Hr].
    destruct (rewrite_prim_shape p args r Hr) as [-> | [a [Hin ->]]]; [discriminate H |].
    unfold fold_leaf in H. destruct (smt_ground a); [discriminate H |].
    pose proof (smt_need_unspool a 0 nil p0 args0 (proj1 (Forall_forall _ _) Ht a Hin) H) as E0.
    simpl in E0. lia.
  - destruct (split_args (simplify_unbranched p) args); simpl in E, H; discriminate.
Qed.

#[export] Instance model_reduce_prim_solvable : ReducePrimSolvable.
Proof.
  intros Γ p args HF.
  change (Solvable Γ (model_reduce_prim p args)). unfold model_reduce_prim.
  assert (Hflat : Forall (fun a => flat a = true) args)
    by (eapply Forall_impl; [| exact HF]; apply solvable_flat).
  rewrite (split_args_not_if _ args (flat_all_not_if _ Hflat)).
  unfold simplify_unbranched.
  destruct (simplify p args) as [r |] eqn:Hs; [| apply unbranched_solvable; exact HF].
  apply (simplify_result (Solvable Γ) p args r ltac:(apply Solvable_Lit)); [| exact Hs].
  eapply Forall_impl; [| exact HF]. apply fold_leaf_solvable.
Qed.

#[export] Instance model_reduce_prim_concore : ReducePrimConcore.
Proof.
  intros p args HF.
  change (concore_expr (model_reduce_prim p args)). unfold model_reduce_prim.
  assert (Hflat : Forall (fun a => flat a = true) args)
    by (eapply Forall_impl; [| exact HF]; apply concore_flat).
  rewrite (split_args_not_if _ args (flat_all_not_if _ Hflat)).
  unfold simplify_unbranched.
  destruct (simplify p args) as [r |] eqn:Hs; [| apply unbranched_concore; exact HF].
  apply (simplify_result concore_expr p args r ltac:(apply Con_Lit)); [| exact Hs].
  eapply Forall_impl; [| exact HF]. apply fold_leaf_concore.
Qed.

