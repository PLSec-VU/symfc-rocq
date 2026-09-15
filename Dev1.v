From SymCoreTheory Require Import SymCore ConCore BranchLaws CostLaws.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.

Section CostBasics.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.

Lemma contains_env_k_sym_free : forall σ S k Γs Γc,
  contains_env_k σ S k Γs Γc -> sym_free_env S Γs.
Proof.
  intros σ S k Γs Γc H.
  exact (proj1 (contains_env_sym_free σ S Γs Γc (contains_env_k_erase _ _ _ _ _ H))).
Qed.

Lemma contains_env_k_concrete : forall σ S k Γs Γc,
  contains_env_k σ S k Γs Γc -> concrete_env Γc.
Proof.
  intros σ S k Γs Γc H.
  exact (contains_env_concrete σ S Γs Γc (contains_env_k_erase _ _ _ _ _ H)).
Qed.

Lemma contains_env_k_lookup : forall σ S k Γs Γc x Γs' es,
  contains_env_k σ S k Γs Γc ->
  lookup_env Γs x = Some (Γs', es) ->
  exists Γc' ec k1 k2,
    lookup_env Γc x = Some (Γc', ec) /\ contains_env_k σ S k1 Γs' Γc' /\
    contains_k σ S k2 es ec /\ k1 <= k /\ k2 <= k.
Proof.
  intros σ S k Γs Γc x Γs' es H. revert Γs' es.
  induction H as [| kenv ke krest y Γ1 Γ2 e1 e2 r1 r2 Hy Henv _ He Hc Hrest IH];
    intros Γs' es Hl; simpl in Hl; [discriminate |].
  simpl. destruct (string_dec x y).
  - injection Hl as <- <-. exists Γ2, e2, kenv, ke. repeat split; try assumption; lia.
  - destruct (IH Γs' es Hl) as [Γc' [ec [k1 [k2 [Hlc [H1 [H2 [Hk1 Hk2]]]]]]]].
    exists Γc', ec, k1, k2. repeat split; try assumption; lia.
Qed.

Lemma delay_contains_k : forall σ S kenv k Γs Γc es ec,
  contains_env_k σ S kenv Γs Γc ->
  contains_k σ S k es ec ->
  exists k', k' <= 1 + kenv + k /\ contains_k σ S k' (delay Γs es) (delay Γc ec).
Proof.
  intros σ S kenv k Γs Γc es ec Henv Hc.
  destruct (is_thunk es) eqn:Hs; destruct (is_thunk ec) eqn:Hcc.
  - rewrite (delay_thunk Γs es Hs), (delay_thunk Γc ec Hcc). exists k. split; [lia | exact Hc].
  - exfalso. destruct es; try discriminate Hs.
    inversion Hc; subst; simpl in *; congruence.
  - rewrite (delay_not_thunk Γs es Hs), (delay_thunk Γc ec Hcc).
    exists (1 + kenv + k). split; [lia |]. exact (ContK_Thunk_Outer σ S kenv k Γs Γc es ec Henv Hc Hcc).
  - rewrite (delay_not_thunk Γs es Hs), (delay_not_thunk Γc ec Hcc).
    exists (kenv + k). split; [lia |]. apply ContK_Thunk; assumption.
Qed.

Lemma delay_map_contains_k : forall σ S kenv Γs Γc ks args_s args_c,
  contains_env_k σ S kenv Γs Γc ->
  Forall3 (contains_k σ S) ks args_s args_c ->
  exists ks', list_sum ks' <= length ks * (1 + kenv) + list_sum ks /\
    Forall3 (contains_k σ S) ks' (map (delay Γs) args_s) (map (delay Γc) args_c).
Proof.
  intros σ S kenv Γs Γc ks args_s args_c Henv HF.
  induction HF as [| k a_s a_c ks l1 l2 Ha _ IH].
  - exists nil. split; [simpl; lia | constructor].
  - destruct IH as [ks' [Hs HF']].
    destruct (delay_contains_k σ S kenv k Γs Γc a_s a_c Henv Ha) as [k' [Hk' Hd]].
    exists (k' :: ks'). split; [simpl in *; lia | constructor; assumption].
Qed.

Lemma contains_k_spine_if : forall σ S k e_sym e_con,
  contains_k σ S k e_sym e_con ->
  forall ks L_s L_c,
    Forall3 (contains_k σ S) ks L_s L_c ->
    forall ec et ef args,
      unspool_app e_sym L_s = (EIf ec et ef, args) ->
      exists kh ks' head_c args_c,
        fold_left EApp L_c e_con = fold_left EApp args_c head_c /\
        contains_k σ S kh (EIf ec et ef) head_c /\
        Forall3 (contains_k σ S) ks' args args_c /\
        kh + list_sum ks' = k + list_sum ks.
Proof.
  induction 1; intros kl L_s L_c HL ec0 et0 ef0 args0 Hunspool; simpl in Hunspool;
    try discriminate Hunspool.
  - destruct (IHcontains_k1 (ka :: kl) (a_s :: L_s) (a_c :: L_c)
                (Forall3_cons _ _ _ _ _ _ _ H0 HL) _ _ _ _ Hunspool)
      as [kh [ks' [hc [ac [Heq [Hh [HF Hs]]]]]]].
    exists kh, ks', hc, ac. split; [exact Heq | split; [exact Hh | split; [exact HF | simpl in Hs; lia]]].
  - injection Hunspool as Hc Ht Hf Hargs. subst.
    exists (1 + smt_size ec0 + k), kl, etc, L_c.
    split; [reflexivity | split; [apply ContK_If_True; assumption | split; [exact HL | lia]]].
  - injection Hunspool as Hc Ht Hf Hargs. subst.
    exists (1 + smt_size ec0 + k), kl, efc, L_c.
    split; [reflexivity | split; [apply ContK_If_False; assumption | split; [exact HL | lia]]].
  - exfalso.
    apply (unspool_app_shift es [] L_s) in H. simpl in H.
    rewrite H in Hunspool. discriminate Hunspool.
Qed.

Lemma contains_k_app_if_spine : forall σ S k e1 e2 ec et ef args e_con,
  contains_k σ S k (EApp e1 e2) e_con ->
  unspool_app (EApp e1 e2) [] = (EIf ec et ef, args) ->
  exists k0, k = 1 + smt_size ec + k0 /\
    ((models_cond σ S ec /\ contains_k σ S k0 (fold_left EApp args et) e_con) \/
     (models_not_cond σ S ec /\ contains_k σ S k0 (fold_left EApp args ef) e_con)).
Proof.
  intros σ S k e1 e2 ec et ef args e_con Hc Hu.
  destruct (contains_k_spine_if σ S k _ _ Hc nil nil nil (Forall3_nil _) ec et ef args Hu)
    as [kh [ks' [hc [ac [Heq [Hh [HF Hs]]]]]]].
  simpl in Heq, Hs. rewrite Heq.
  destruct (contains_k_if_inv σ S kh ec et ef hc Hh) as [k0 [-> [[Hm Ht] | [Hm Hf]]]].
  - exists (k0 + list_sum ks'). split; [lia |]. left. split; [exact Hm |].
    exact (contains_k_fold_left_app σ S ks' _ _ k0 _ _ HF Ht).
  - exists (k0 + list_sum ks'). split; [lia |]. right. split; [exact Hm |].
    exact (contains_k_fold_left_app σ S ks' _ _ k0 _ _ HF Hf).
Qed.

End CostBasics.
