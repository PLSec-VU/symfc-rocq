From SymCoreTheory Require Export Model.ReducerLaws.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.

Inductive picks_k (σ : valuation) (S : symvars) : nat -> expr -> expr -> Prop :=
  | picks_k_leaf : forall e, is_if e = false -> picks_k σ S 0 e e
  | picks_k_then : forall k c t f L,
      models_cond σ S c -> picks_k σ S k t L -> picks_k σ S (1 + smt_size c + k) (EIf c t f) L
  | picks_k_else : forall k c t f L,
      models_not_cond σ S c -> picks_k σ S k f L -> picks_k σ S (1 + smt_size c + k) (EIf c t f) L.

Lemma picks_of_picks_k : forall σ S k T L, picks_k σ S k T L -> picks σ S T L.
Proof.
  intros σ S k T L H. induction H;
    [apply picks_leaf | apply picks_then | apply picks_else]; assumption.
Qed.

Lemma picks_k_contains_k : forall σ S kp T L kL Y,
  picks_k σ S kp T L -> contains_k σ S kL L Y -> contains_k σ S (kp + kL) T Y.
Proof.
  intros σ S kp T L kL Y H. induction H as [e He | k c t f L Hm Hp IH | k c t f L Hm Hp IH];
    intros Hc.
  - exact Hc.
  - replace (1 + smt_size c + k + kL) with (1 + smt_size c + (k + kL)) by lia.
    apply ContK_If_True; [exact Hm | exact (IH Hc)].
  - replace (1 + smt_size c + k + kL) with (1 + smt_size c + (k + kL)) by lia.
    apply ContK_If_False; [exact Hm | exact (IH Hc)].
Qed.

Lemma picks_k_graft_arg : forall σ S L1 k T2 L2,
  is_if L1 = false -> picks_k σ S k T2 L2 -> picks_k σ S k (graft_arg L1 T2) (EApp L1 L2).
Proof.
  intros σ S L1 k T2 L2 H1 H. induction H.
  - rewrite graft_arg_not_if by assumption. apply picks_k_leaf. reflexivity.
  - simpl. apply picks_k_then; assumption.
  - simpl. apply picks_k_else; assumption.
Qed.

Lemma picks_k_graft : forall σ S k1 T1 L1 k2 T2 L2,
  picks_k σ S k1 T1 L1 -> picks_k σ S k2 T2 L2 -> picks_k σ S (k1 + k2) (graft T1 T2) (EApp L1 L2).
Proof.
  intros σ S k1 T1 L1 k2 T2 L2 H1 H2. induction H1.
  - destruct e; simpl in H; try discriminate; simpl;
      apply picks_k_graft_arg; try reflexivity; exact H2.
  - simpl. rewrite <- Nat.add_assoc. apply picks_k_then; assumption.
  - simpl. rewrite <- Nat.add_assoc. apply picks_k_else; assumption.
Qed.

Lemma lift_picks_k : forall σ S k e X,
  contains_k σ S k e X ->
  exists kp kL L, picks_k σ S kp (lift_branches e) L /\ contains_k σ S kL L X /\
    flat L = true /\ kp + kL <= k.
Proof.
  intros σ S k e X H. induction H;
    try (exists 0; eexists; eexists; split; [apply picks_k_leaf; reflexivity
                         | split; [simpl; solve [econstructor; eassumption] | split; [reflexivity | lia]]]).
  - destruct IHcontains_k1 as [kp1 [kL1 [L1 [P1 [C1 [F1 B1]]]]]].
    destruct IHcontains_k2 as [kp2 [kL2 [L2 [P2 [C2 [F2 B2]]]]]].
    exists (kp1 + kp2), (kL1 + kL2), (EApp L1 L2).
    split; [simpl; apply picks_k_graft; assumption |].
    split; [apply ContK_App; assumption |].
    split; [simpl; rewrite F1, F2; reflexivity | lia].
  - destruct IHcontains_k as [kp [kL [L [P [C [F B]]]]]].
    exists (1 + smt_size ec + kp), kL, L.
    split; [simpl; apply picks_k_then; assumption |].
    split; [exact C | split; [exact F | lia]].
  - destruct IHcontains_k as [kp [kL [L [P [C [F B]]]]]].
    exists (1 + smt_size ec + kp), kL, L.
    split; [simpl; apply picks_k_else; assumption |].
    split; [exact C | split; [exact F | lia]].
  - assert (Hflat : flat es = true)
      by (destruct H2 as [pc [Hd _]]; exact (denotes_flat S es pc Hd)).
    exists 0, (smt_size es), es. rewrite (lift_flat es Hflat).
    split; [apply picks_k_leaf; apply flat_not_if; exact Hflat |].
    split; [eapply ContK_Denote; eassumption | split; [exact Hflat | lia]].
Qed.

Lemma picks_k_fold_leaves : forall σ S k T L,
  picks_k σ S k T L -> picks_k σ S k (fold_leaves T) (fold_leaf L).
Proof.
  intros σ S k T L H. induction H.
  - rewrite fold_leaves_not_if by assumption.
    apply picks_k_leaf. apply fold_leaf_not_if. assumption.
  - simpl. apply picks_k_then; assumption.
  - simpl. apply picks_k_else; assumption.
Qed.

Lemma fold_left_app_size_ground : forall args h,
  smt_size (fold_left EApp args h) = smt_size h + length args + list_sum (map smt_size args) /\
  (smt_ground (fold_left EApp args h) = true ->
     smt_ground h = true /\ Forall (fun a => smt_ground a = true) args).
Proof.
  induction args as [| a args IH]; intros h; simpl.
  - split; [lia | intros Hg; split; [exact Hg | constructor]].
  - destruct (IH (EApp h a)) as [Hs Hg]. split.
    + rewrite Hs. simpl. lia.
    + intros H. destruct (Hg H) as [Hha Hargs]. simpl in Hha.
      apply andb_prop in Hha as [Hh12 Ha]. apply andb_prop in Hh12 as [_ Hh].
      split; [exact Hh | constructor; assumption].
Qed.

Lemma ground_size_op_spine : forall p args,
  ground_size (op_spine p args) <= prim_slack args.
Proof.
  intros p args. unfold ground_size, prim_slack, op_spine.
  destruct (fold_left_app_size_ground args (@EPrimOp model_sorts p)) as [Hs Hg].
  destruct (smt_ground (fold_left EApp args (@EPrimOp model_sorts p))) eqn:E; [| lia].
  destruct (Hg eq_refl) as [_ Hargs]. rewrite Hs. simpl.
  enough (list_sum (map smt_size args) = list_sum (map ground_size args)) by lia.
  clear Hs Hg E. induction Hargs as [| a args Ha _ IH]; [reflexivity |].
  simpl. unfold ground_size at 1. rewrite Ha, IH. reflexivity.
Qed.

Lemma leaf_contains_k : forall σ S p kL L X,
  spine_of p (model_arity p) L ->
  contains_k σ S kL L X -> flat L = true ->
  exists k', k' <= kL + ground_size X /\ contains_k σ S k' (fold_leaf L) (fold_leaf X).
Proof.
  intros σ S p kL L X [L' [-> HL']] Hc HfL.
  pose proof (contains_k_erase _ _ _ _ _ Hc) as Hc0.
  unfold fold_leaf, ground_size.
  destruct (smt_ground X) eqn:HgX; destruct (smt_ground (op_spine p L')) eqn:HgL.
  - rewrite (closed_smt_term_is_rigid σ S _ _ HgL Hc0). exists 0. split; [lia | apply ContK_Lit].
  - destruct (ground_instance_denotes σ S _ _ Hc0 HfL HgX) as [pcL [pcX [HdL [HeX [Hv _]]]]].
    exists (smt_size (op_spine p L')).
    split; [exact (smt_size_contains_k _ _ _ _ _ Hc) |].
    apply (ContK_Denote σ S (op_spine p L') p L').
    + apply op_spine_unspool.
    + exact HL'.
    + exact HgL.
    + exists pcL. split; [exact HdL |]. rewrite (closed_value_of X pcX HeX). exact Hv.
  - pose proof (closed_smt_term_is_rigid σ S _ _ HgL Hc0) as E.
    rewrite E in HgL. congruence.
  - exists kL. split; [lia | exact Hc].
Qed.

Lemma unbranched_contains_k : forall σ S p ks args_s args_c,
  Forall3 (contains_k σ S) ks args_s args_c ->
  exists k', k' <= list_sum ks + prim_slack args_c /\
    contains_k σ S k' (reduce_unbranched p args_s) (reduce_unbranched p args_c).
Proof.
  intros σ S p ks args_s args_c HF.
  unfold reduce_unbranched. rewrite <- (forall3_length_right _ _ _ _ _ _ _ HF).
  destruct (Nat.eqb (length args_s) (model_arity p)) eqn:Hlen;
    [| exists 0; split; [lia | apply ContK_Lit]].
  apply Nat.eqb_eq in Hlen.
  pose proof (contains_k_fold_left_app σ S ks args_s args_c 0 _ _ HF (ContK_PrimOp σ S p)) as Hc.
  simpl in Hc. fold (op_spine p args_s) (op_spine p args_c) in Hc.
  rewrite (lift_flat _ (contains_flat_instance σ S _ _ (contains_k_erase _ _ _ _ _ Hc))),
          (fold_leaves_not_if _ (op_spine_not_if p args_c)).
  destruct (lift_picks_k σ S _ _ _ Hc) as [kp [kL [L [Hp [HcL [HfL Hb]]]]]].
  destruct (leaf_contains_k σ S p kL L (op_spine p args_c)) as [k' [Hk' Hc']];
    [| exact HcL | exact HfL |].
  { rewrite <- Hlen. exact (picks_leaves σ S _ _ _ (picks_of_picks_k _ _ _ _ _ Hp) (leaves_lift_spine p args_s)). }
  pose proof (ground_size_op_spine p args_c) as Hg.
  exists (kp + k'). split; [lia |].
  exact (picks_k_contains_k σ S _ _ _ _ _ (picks_k_fold_leaves σ S _ _ _ Hp) Hc').
Qed.

Lemma contains_k_picks_top : forall σ S e k X,
  contains_k σ S k e X -> exists kp kL L, picks_k σ S kp e L /\ contains_k σ S kL L X /\ kp + kL = k.
Proof.
  intros σ S e. induction e; intros k X H;
    try (exists 0, k; eexists; split; [apply picks_k_leaf; reflexivity | split; [exact H | reflexivity]]).
  destruct (contains_k_if_inv σ S _ _ _ _ X H) as [k0 [-> [[Hm Hc] | [Hm Hc]]]].
  - destruct (IHe2 k0 X Hc) as [kp [kL [L [Hp [HL Hs]]]]].
    exists (1 + smt_size e1 + kp), kL, L. split; [apply picks_k_then; assumption | split; [exact HL | lia]].
  - destruct (IHe3 k0 X Hc) as [kp [kL [L [Hp [HL Hs]]]]].
    exists (1 + smt_size e1 + kp), kL, L. split; [apply picks_k_else; assumption | split; [exact HL | lia]].
Qed.

Lemma contains_k_args_picks : forall σ S ks args_s args_c,
  Forall3 (contains_k σ S) ks args_s args_c ->
  exists kps kls ls, Forall3 (picks_k σ S) kps args_s ls /\ Forall3 (contains_k σ S) kls ls args_c /\
    list_sum kps + list_sum kls = list_sum ks.
Proof.
  intros σ S ks args_s args_c H.
  induction H as [| k a c ks args_s args_c Ha _ [kps [kls [ls [Hp [Hc Hs]]]]]].
  - exists nil, nil, nil. split; [constructor | split; [constructor | reflexivity]].
  - destruct (contains_k_picks_top σ S a k c Ha) as [kp [kL [L [HpL [HcL HsL]]]]].
    exists (kp :: kps), (kL :: kls), (L :: ls).
    split; [constructor; assumption | split; [constructor; assumption | simpl; lia]].
Qed.

Lemma picks_k_split_arg : forall σ S K kp a L k Y,
  picks_k σ S kp a L -> contains_k σ S k (K L) Y -> contains_k σ S (kp + k) (split_arg K a) Y.
Proof.
  intros σ S K kp a L k Y H. induction H; intros HK.
  - rewrite split_arg_not_if by assumption. exact HK.
  - cbn [split_arg]. replace (1 + smt_size c + k0 + k) with (1 + smt_size c + (k0 + k)) by lia.
    apply ContK_If_True; auto.
  - cbn [split_arg]. replace (1 + smt_size c + k0 + k) with (1 + smt_size c + (k0 + k)) by lia.
    apply ContK_If_False; auto.
Qed.

Lemma picks_k_split_args : forall σ S kps args ls,
  Forall3 (picks_k σ S) kps args ls ->
  forall K k Y, contains_k σ S k (K ls) Y -> contains_k σ S (list_sum kps + k) (split_args K args) Y.
Proof.
  intros σ S kps args ls H.
  induction H as [| kp a L kps args ls Ha _ IH]; intros K k Y Hk; [exact Hk |].
  cbn [split_args]. replace (list_sum (kp :: kps) + k) with (kp + (list_sum kps + k)) by (simpl; lia).
  apply (picks_k_split_arg σ S _ kp a L _ Y Ha).
  apply (IH (fun rest' => K (L :: rest'))). exact Hk.
Qed.

Lemma ground_flat : forall a, smt_ground a = true -> flat a = true.
Proof. intros a H. exact (solvable_flat · a (smt_ground_solvable a · H)). Qed.

Lemma op_spine_pc : forall args pcs h (q : model_primop) acc,
  Forall2 (fun a pc => expr_to_pc · a = Some pc) args pcs ->
  expr_to_pc · h = Some (PCPrim q acc) ->
  expr_to_pc · (fold_left EApp args h) = Some (PCPrim q (acc ++ pcs)).
Proof.
  intros args pcs h q acc H. revert h acc.
  induction H as [| a pc args pcs Ha _ IH]; intros h acc Hh.
  - rewrite app_nil_r. exact Hh.
  - simpl. replace (acc ++ pc :: pcs) with ((acc ++ pc :: nil) ++ pcs)
      by (rewrite <- app_assoc; reflexivity).
    apply IH. simpl. rewrite Hh, Ha. reflexivity.
Qed.

Lemma op_spine_ground : forall args h,
  Forall (fun a => smt_ground a = true) args ->
  smt_ground h = true -> is_op_app h = true ->
  smt_ground (fold_left EApp args h) = true.
Proof.
  intros args h H. revert h. induction H as [| a args Ha _ IH]; intros h Hh Hop; [exact Hh |].
  simpl. apply IH; simpl; [rewrite Hop, Hh, Ha; reflexivity | exact Hop].
Qed.

Lemma unbranched_ground : forall p args,
  length args = model_arity p -> Forall (fun a => smt_ground a = true) args ->
  reduce_unbranched p args = ELit (model_prim_value p (map closed_value args)).
Proof.
  intros p args Hlen Hg. unfold reduce_unbranched.
  rewrite (proj2 (Nat.eqb_eq _ _) Hlen).
  assert (Hflat : Forall (fun a => flat a = true) args)
    by (eapply Forall_impl; [| exact Hg]; exact ground_flat).
  rewrite (lift_flat _ (op_spine_flat p args Hflat)), (fold_leaves_not_if _ (op_spine_not_if p args)).
  unfold fold_leaf, op_spine.
  rewrite (op_spine_ground args (@EPrimOp model_sorts p) Hg eq_refl eq_refl).
  assert (Hpcs : exists pcs, Forall2 (fun a pc => expr_to_pc · a = Some pc) args pcs
                   /\ map (pc_value closed_model) pcs = map closed_value args).
  { clear Hlen Hflat. induction Hg as [| a args Ha _ [pcs [Hp Hv]]].
    - exists nil. split; [constructor | reflexivity].
    - destruct (solvable_expr_to_pc · a (smt_ground_solvable a · Ha)) as [pc Hpc].
      exists (pc :: pcs). split; [constructor; assumption |].
      cbn [map]. rewrite Hv, (closed_value_of a pc Hpc). reflexivity. }
  destruct Hpcs as [pcs [Hp Hv]].
  pose proof (op_spine_pc args pcs (@EPrimOp model_sorts p) p nil Hp eq_refl) as He. simpl in He.
  rewrite (closed_value_of _ _ He).
  change (ELit (model_prim_value p (map (pc_value closed_model) pcs))
          = ELit (model_prim_value p (map closed_value args))).
  rewrite Hv. reflexivity.
Qed.

Lemma arg_facts_k : forall σ S ks ls args_c,
  Forall3 (contains_k σ S) ks ls args_c -> Forall closed_term args_c ->
  Forall (fun a => smt_need a = Some 0) ls ->
  Forall (fun c => smt_ground c = true) args_c /\
  Forall2 (denote σ S) ls (map closed_value args_c) /\
  list_sum (map smt_size ls) <= list_sum ks + list_sum (map ground_size args_c).
Proof.
  intros σ S ks ls args_c H. induction H as [| k L X ks ls args_c HLX _ IH]; intros Hcl Ht.
  - split; [constructor | split; [constructor | simpl; lia]].
  - inversion Hcl as [| X0 xs0 HclX Hcl']; subst. inversion Ht as [| L0 ls0 HtL Ht']; subst.
    destruct (IH Hcl' Ht') as [Hg [Hd Hs]].
    pose proof (contains_k_erase _ _ _ _ _ HLX) as HLX0.
    pose proof (smt_need_closed_ground X 0 (contains_smt_need σ S L X 0 HLX0 HtL) HclX) as HgX.
    destruct (ground_instance_denotes σ S L X HLX0 (smt_need_flat L 0 HtL) HgX)
      as [pcL [pcX [HdL [HeX [Hv _]]]]].
    split; [constructor; assumption |].
    split.
    + constructor; [| exact Hd].
      exists pcL. split; [exact HdL |]. rewrite (closed_value_of X pcX HeX). exact Hv.
    + pose proof (smt_size_contains_k _ _ _ _ _ HLX) as HsX.
      simpl. unfold ground_size at 1. rewrite HgX. lia.
Qed.

Lemma simplified_contains_k : forall σ S p ks ls args_c,
  Forall closed_term args_c -> Forall3 (contains_k σ S) ks ls args_c ->
  exists k', k' <= list_sum ks + prim_slack args_c /\
    contains_k σ S k' (simplify_unbranched p ls) (simplify_unbranched p args_c).
Proof.
  intros σ S p ks ls args_c Hcl HF.
  unfold simplify_unbranched at 2. rewrite (simplify_closed_none p args_c Hcl).
  unfold simplify_unbranched.
  destruct (simplify p ls) as [r |] eqn:Hs; [| exact (unbranched_contains_k σ S p ks ls args_c HF)].
  destruct (simplify_facts p ls r Hs) as [Ht Hr].
  destruct (arg_facts_k σ S ks ls args_c HF Hcl Ht) as [Hg [Hd Hsz]].
  destruct (rewrite_prim_value σ S p ls _ r Ht Hd Hr) as [_ [k [Hk Hck]]].
  rewrite (unbranched_ground p args_c); [| | exact Hg].
  - exists k. split; [unfold prim_slack; lia | exact Hck].
  - rewrite <- (forall3_length_right _ _ _ _ _ _ _ HF). exact (rewrite_prim_arity p ls r Hr).
Qed.

#[export] Instance model_reduce_prim_contains_k : ReducePrimContainsK.
Proof.
  intros σ S p ks args_s args_c Hcl HF.
  change (exists k', k' <= list_sum ks + prim_slack args_c /\
    contains_k σ S k' (model_reduce_prim p args_s) (model_reduce_prim p args_c)).
  unfold model_reduce_prim.
  rewrite (split_args_not_if _ args_c
             (contains_instances_not_if σ S _ _ (forall3_contains_k_erase _ _ _ _ _ HF))).
  destruct (contains_k_args_picks σ S _ _ _ HF) as [kps [kls [ls [Hp [Hc Hs]]]]].
  destruct (simplified_contains_k σ S p kls ls args_c Hcl Hc) as [k' [Hk' Hc']].
  exists (list_sum kps + k'). split; [lia |].
  exact (picks_k_split_args σ S _ _ _ Hp _ _ _ Hc').
Qed.

#[export] Instance model_cast_expr_contains_k : CastExprContainsK.
Proof. intros σ S k es ec γ H. exact H. Qed.

#[export] Instance model_reduce_prim_contains : ReducePrimContains.
Proof. exact (reduce_prim_contains_of_k model_reduce_prim_contains_k). Qed.

