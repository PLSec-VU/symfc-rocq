From SymCoreTheory Require Export Model.CostLaws.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.

Lemma model_ground_arm_no_var : forall S X pca,
  smt_ground X = true -> denotes S X pca -> pc_has_var pca = false.
Proof.
  intros S X pca Hg Hd.
  exact (expr_to_pc_scoped_no_var · X pca (smt_ground_scoped X (dom_env ·) Hg)
           (Hd · (sym_free_env_empty S))).
Qed.

Lemma model_ite_spine_ground_arms : forall ec et ef,
  smt_ground (op_spine PIte (ec :: et :: ef :: nil)) = true ->
  smt_ground et = true /\ smt_ground ef = true.
Proof.
  intros ec et ef H. unfold op_spine in H. simpl in H.
  rewrite !andb_true_iff in H. tauto.
Qed.

Lemma model_ite_spine_pc_inv : forall S ec et ef pc,
  denotes S (op_spine PIte (ec :: et :: ef :: nil)) pc ->
  exists q1 q2 q3,
    pc = PCPrim PIte (q1 :: q2 :: q3 :: nil) /\
    expr_to_pc · ec = Some q1 /\ expr_to_pc · et = Some q2 /\ expr_to_pc · ef = Some q3.
Proof.
  intros S ec et ef pc Hd.
  pose proof (Hd · (sym_free_env_empty S)) as H.
  unfold op_spine in H. simpl in H.
  destruct (expr_to_pc · ec) as [q1 |] eqn:E1; simpl in H; [| discriminate H].
  destruct (expr_to_pc · et) as [q2 |] eqn:E2; simpl in H; [| discriminate H].
  destruct (expr_to_pc · ef) as [q3 |] eqn:E3; simpl in H; [| discriminate H].
  injection H as <-.
  exists q1, q2, q3.
  split; [reflexivity | split; [reflexivity | split; reflexivity]].
Qed.

Lemma model_ite_wellformed_arm : forall S X pc pca,
  denotes S (fold_leaf X) pc ->
  (pc_arities_ok pc = true \/ pc_has_var pc = false) ->
  denotes S X pca ->
  (pc_arities_ok pca = true \/ pc_has_var pca = false).
Proof.
  intros S X pc pca Hd Hok Hda.
  unfold fold_leaf in Hd. destruct (smt_ground X) eqn:Hg.
  - right. exact (model_ground_arm_no_var S X pca Hg Hda).
  - rewrite (expr_to_pc_functional X · · pc pca
               (Hd · (sym_free_env_empty S)) (Hda · (sym_free_env_empty S))) in Hok.
    exact Hok.
Qed.

Lemma model_ite_wellformed_spine : forall S ec et ef pc pca,
  denotes S (fold_leaf (op_spine PIte (ec :: et :: ef :: nil))) pc ->
  (pc_arities_ok pc = true \/ pc_has_var pc = false) ->
  (denotes S et pca \/ denotes S ef pca) ->
  (pc_arities_ok pca = true \/ pc_has_var pca = false).
Proof.
  intros S ec et ef pc pca Hd Hok Hda.
  unfold fold_leaf in Hd.
  destruct (smt_ground (op_spine PIte (ec :: et :: ef :: nil))) eqn:Hg.
  - right. destruct (model_ite_spine_ground_arms ec et ef Hg) as [Het Hef].
    destruct Hda as [H | H];
      [exact (model_ground_arm_no_var S et pca Het H)
      | exact (model_ground_arm_no_var S ef pca Hef H)].
  - destruct (model_ite_spine_pc_inv S ec et ef pc Hd) as [q1 [q2 [q3 [-> [E1 [E2 E3]]]]]].
    assert (Hq : pca = q2 \/ pca = q3).
    { destruct Hda as [H | H];
        [ left; exact (expr_to_pc_functional et · · pca q2 (H · (sym_free_env_empty S)) E2)
        | right; exact (expr_to_pc_functional ef · · pca q3 (H · (sym_free_env_empty S)) E3) ]. }
    destruct Hok as [Har | Hvar].
    + left. simpl in Har. rewrite !andb_true_iff in Har. destruct Hq as [-> | ->]; tauto.
    + right. simpl in Hvar. rewrite !orb_false_iff in Hvar. destruct Hq as [-> | ->]; tauto.
Qed.

Lemma model_rewrite_prim_ite_arm : forall ec et ef r,
  rewrite_prim PIte (ec :: et :: ef :: nil) = Some r ->
  (lit_of ec = Some true /\ r = fold_leaf et)
  \/ (lit_of ec = Some false /\ r = fold_leaf ef)
  \/ (et = ef /\ r = fold_leaf et).
Proof.
  intros ec et ef r H. cbn [rewrite_prim] in H.
  destruct (lit_of ec) as [[|] |] eqn:Ec.
  - left. injection H as <-. split; reflexivity.
  - right. left. injection H as <-. split; reflexivity.
  - destruct (expr_eqb et ef) eqn:E; [| discriminate H].
    right. right. injection H as <-.
    split; [exact (expr_eqb_eq et ef E) | reflexivity].
Qed.

#[export] Instance model_reduce_prim_ite_wellformed : ReducePrimIteWellformed.
Proof.
  intros σ S ec et ef pcc pc pca Hsc Hst Hsf Hdc Hdm Hok Hda.
  assert (Hflat : Forall (fun a => flat a = true) (ec :: et :: ef :: nil))
    by (repeat constructor; eapply solvable_flat; eassumption).
  change (denotes S (model_reduce_prim PIte (ec :: et :: ef :: nil)) pc) in Hdm.
  unfold model_reduce_prim in Hdm.
  rewrite (split_args_not_if _ _ (flat_all_not_if _ Hflat)) in Hdm.
  unfold simplify_unbranched in Hdm.
  destruct (simplify PIte (ec :: et :: ef :: nil)) as [r |] eqn:Hs.
  - destruct (simplify_facts _ _ _ Hs) as [_ Hr].
    destruct (model_rewrite_prim_ite_arm ec et ef r Hr)
      as [[Ec ->] | [[Ec ->] | [Hsame ->]]].
    + assert (Hv : pc_value σ pcc = true)
        by exact (lit_of_value σ S ec true (pc_value σ pcc) Ec
                    (ex_intro _ pcc (conj Hdc eq_refl))).
      destruct (lit_eq_dec (pc_value σ pcc) lit_true) as [_ | Hne];
        [| exfalso; exact (Hne Hv)].
      exact (model_ite_wellformed_arm S et pc pca Hdm Hok Hda).
    + assert (Hv : pc_value σ pcc = false)
        by exact (lit_of_value σ S ec false (pc_value σ pcc) Ec
                    (ex_intro _ pcc (conj Hdc eq_refl))).
      destruct (lit_eq_dec (pc_value σ pcc) lit_true) as [Heq | _];
        [rewrite Hv in Heq; discriminate Heq |].
      exact (model_ite_wellformed_arm S ef pc pca Hdm Hok Hda).
    + subst ef. destruct (lit_eq_dec (pc_value σ pcc) lit_true);
        exact (model_ite_wellformed_arm S et pc pca Hdm Hok Hda).
  - unfold reduce_unbranched in Hdm. cbn [length model_arity Nat.eqb] in Hdm.
    rewrite (lift_flat _ (op_spine_flat PIte _ Hflat)) in Hdm.
    rewrite (fold_leaves_not_if _ (op_spine_not_if _ _)) in Hdm.
    apply (model_ite_wellformed_spine S ec et ef pc pca Hdm Hok).
    destruct (lit_eq_dec (pc_value σ pcc) lit_true); [left | right]; exact Hda.
Qed.

Lemma smt_ground_no_out_of_fuel : forall e,
  smt_ground e = true -> mentions_out_of_fuel e = false.
Proof.
  induction e; intros Hg; cbn [smt_ground] in Hg; try discriminate; try reflexivity.
  apply andb_prop in Hg as [Hgf Hga]. apply andb_prop in Hgf as [_ Hgf].
  cbn [mentions_out_of_fuel]. rewrite (IHe1 Hgf), (IHe2 Hga). reflexivity.
Qed.

Lemma out_of_fuel_needs_nothing : forall e,
  mentions_out_of_fuel e = true -> smt_need e = None.
Proof.
  induction e; intros Hm; cbn [mentions_out_of_fuel] in Hm;
    try discriminate; try reflexivity.
  cbn [smt_need]. apply orb_true_iff in Hm as [Hf | Ha].
  - rewrite (IHe1 Hf). reflexivity.
  - rewrite (IHe2 Ha). destruct (smt_need e1) as [[| n] |]; reflexivity.
Qed.

Lemma out_of_fuel_not_smt_term : forall e,
  mentions_out_of_fuel e = true -> smt_term e = false.
Proof.
  intros e Hm. unfold smt_term. rewrite (out_of_fuel_needs_nothing e Hm). reflexivity.
Qed.

Lemma graft_arg_keeps_out_of_fuel : forall a f,
  (mentions_out_of_fuel f || mentions_out_of_fuel a)%bool = true ->
  mentions_out_of_fuel (graft_arg f a) = true.
Proof.
  induction a; intros f H; try exact H.
  cbn [graft_arg mentions_out_of_fuel] in H |- *.
  repeat rewrite orb_true_iff in H. repeat rewrite orb_true_iff.
  destruct H as [Hf | [Hc | [Ht | He]]].
  - right. left. apply IHa2. apply orb_true_iff. left. exact Hf.
  - left. exact Hc.
  - right. left. apply IHa2. apply orb_true_iff. right. exact Ht.
  - right. right. apply IHa3. apply orb_true_iff. right. exact He.
Qed.

Lemma graft_keeps_out_of_fuel : forall f a,
  (mentions_out_of_fuel f || mentions_out_of_fuel a)%bool = true ->
  mentions_out_of_fuel (graft f a) = true.
Proof.
  induction f; intros a H; try (apply graft_arg_keeps_out_of_fuel; exact H).
  cbn [graft mentions_out_of_fuel] in H |- *.
  repeat rewrite orb_true_iff in H. repeat rewrite orb_true_iff.
  destruct H as [[Hc | [Ht | He]] | Ha].
  - left. exact Hc.
  - right. left. apply IHf2. apply orb_true_iff. left. exact Ht.
  - right. right. apply IHf3. apply orb_true_iff. left. exact He.
  - right. left. apply IHf2. apply orb_true_iff. right. exact Ha.
Qed.

Lemma lift_branches_keeps_out_of_fuel : forall e,
  mentions_out_of_fuel e = true -> mentions_out_of_fuel (lift_branches e) = true.
Proof.
  induction e; intros H; cbn [lift_branches]; try exact H.
  - apply graft_keeps_out_of_fuel.
    cbn [mentions_out_of_fuel] in H. apply orb_true_iff in H as [Hf | Ha];
      apply orb_true_iff; [left; exact (IHe1 Hf) | right; exact (IHe2 Ha)].
  - cbn [mentions_out_of_fuel] in H |- *.
    repeat rewrite orb_true_iff in H. repeat rewrite orb_true_iff.
    destruct H as [Hc | [Ht | Hf]].
    + left. exact Hc.
    + right. left. exact (IHe2 Ht).
    + right. right. exact (IHe3 Hf).
Qed.

Lemma fold_leaf_of_out_of_fuel : forall e,
  mentions_out_of_fuel e = true -> fold_leaf e = e.
Proof.
  intros e H. unfold fold_leaf. destruct (smt_ground e) eqn:Hg; [| reflexivity].
  rewrite (smt_ground_no_out_of_fuel e Hg) in H. discriminate H.
Qed.

Lemma fold_leaves_keeps_out_of_fuel : forall e,
  mentions_out_of_fuel e = true -> mentions_out_of_fuel (fold_leaves e) = true.
Proof.
  induction e; intros H; cbn [fold_leaves];
    try (rewrite (fold_leaf_of_out_of_fuel _ H); exact H).
  cbn [mentions_out_of_fuel] in H |- *.
  repeat rewrite orb_true_iff in H. repeat rewrite orb_true_iff.
  destruct H as [Hc | [Ht | Hf]].
  - left. exact Hc.
  - right. left. exact (IHe2 Ht).
  - right. right. exact (IHe3 Hf).
Qed.

Lemma fold_left_app_mentions_out_of_fuel : forall args h,
  mentions_out_of_fuel (fold_left EApp args h)
  = (mentions_out_of_fuel h || existsb mentions_out_of_fuel args)%bool.
Proof.
  induction args as [| a rest IH]; intros h; cbn [fold_left existsb].
  - rewrite orb_false_r. reflexivity.
  - rewrite (IH (EApp h a)). cbn [mentions_out_of_fuel]. symmetry. apply orb_assoc.
Qed.

Lemma op_spine_keeps_out_of_fuel : forall p args,
  existsb mentions_out_of_fuel args = true ->
  mentions_out_of_fuel (op_spine p args) = true.
Proof.
  intros p args H. unfold op_spine. rewrite fold_left_app_mentions_out_of_fuel.
  rewrite H. apply orb_true_r.
Qed.

Lemma simplify_unbranched_keeps_out_of_fuel : forall p args,
  length args = model_arity p ->
  existsb mentions_out_of_fuel args = true ->
  mentions_out_of_fuel (simplify_unbranched p args) = true.
Proof.
  intros p args Hlen H.
  assert (Hsimp : simplify p args = None).
  { unfold simplify. destruct (forallb smt_term args) eqn:Hterm; [| reflexivity].
    exfalso. apply existsb_exists in H as [a [Hin Ha]].
    rewrite forallb_forall in Hterm. specialize (Hterm a Hin).
    rewrite (out_of_fuel_not_smt_term a Ha) in Hterm. discriminate Hterm. }
  unfold simplify_unbranched. rewrite Hsimp.
  unfold reduce_unbranched. rewrite Hlen, Nat.eqb_refl.
  apply fold_leaves_keeps_out_of_fuel. apply lift_branches_keeps_out_of_fuel.
  apply op_spine_keeps_out_of_fuel. exact H.
Qed.

Lemma split_arg_keeps_a_mentioning_continuation : forall a k,
  (forall a', mentions_out_of_fuel (k a') = true) ->
  mentions_out_of_fuel (split_arg k a) = true.
Proof.
  induction a; intros k Hk; try (apply Hk).
  cbn [split_arg mentions_out_of_fuel]. rewrite (IHa2 k Hk).
  apply orb_true_r.
Qed.

Lemma split_arg_keeps_out_of_fuel : forall a k,
  (forall a', mentions_out_of_fuel a' = true -> mentions_out_of_fuel (k a') = true) ->
  mentions_out_of_fuel a = true ->
  mentions_out_of_fuel (split_arg k a) = true.
Proof.
  induction a; intros k Hk H; try (apply Hk; exact H).
  cbn [split_arg mentions_out_of_fuel] in H |- *.
  repeat rewrite orb_true_iff in H. repeat rewrite orb_true_iff.
  destruct H as [Hc | [Ht | Hf]].
  - left. exact Hc.
  - right. left. exact (IHa2 k Hk Ht).
  - right. right. exact (IHa3 k Hk Hf).
Qed.

Lemma split_args_keeps_a_mentioning_continuation : forall args k,
  (forall args', length args' = length args -> mentions_out_of_fuel (k args') = true) ->
  mentions_out_of_fuel (split_args k args) = true.
Proof.
  induction args as [| a rest IH]; intros k Hk; cbn [split_args].
  - apply Hk. reflexivity.
  - apply split_arg_keeps_a_mentioning_continuation. intros a'.
    apply IH. intros rest' Hlen. apply Hk. cbn [length]. rewrite Hlen. reflexivity.
Qed.

Lemma split_args_keeps_out_of_fuel : forall args k,
  (forall args', length args' = length args ->
     existsb mentions_out_of_fuel args' = true ->
     mentions_out_of_fuel (k args') = true) ->
  existsb mentions_out_of_fuel args = true ->
  mentions_out_of_fuel (split_args k args) = true.
Proof.
  induction args as [| a rest IH]; intros k Hk H; [discriminate H |].
  cbn [split_args]. cbn [existsb] in H. apply orb_true_iff in H as [Ha | Hrest].
  - apply (split_arg_keeps_out_of_fuel a); [| exact Ha].
    intros a' Ha'. apply split_args_keeps_a_mentioning_continuation.
    intros rest' Hlen. apply Hk.
    + cbn [length]. rewrite Hlen. reflexivity.
    + cbn [existsb]. rewrite Ha'. reflexivity.
  - apply split_arg_keeps_a_mentioning_continuation. intros a'.
    apply IH; [| exact Hrest].
    intros rest' Hlen Hex. apply Hk.
    + cbn [length]. rewrite Hlen. reflexivity.
    + cbn [existsb]. rewrite Hex. apply orb_true_r.
Qed.

#[export] Instance model_reduce_prim_keeps_out_of_fuel : ReducePrimKeepsOutOfFuel.
Proof.
  intros p args Hlen H.
  change (mentions_out_of_fuel (model_reduce_prim p args) = true).
  unfold model_reduce_prim.
  apply split_args_keeps_out_of_fuel; [| exact H].
  intros args' Hlen' Hex.
  apply simplify_unbranched_keeps_out_of_fuel; [rewrite Hlen'; exact Hlen | exact Hex].
Qed.

#[export] Instance model_laws : ConCoreLaws.
Proof. constructor; exact _. Qed.

#[export] Instance model_symfc_cost_laws : SymFCCostLaws.
Proof. constructor; exact _. Qed.

