From SymCoreTheory Require Export Completeness.Statement.
From Stdlib Require Import Bool.Bool Arith.Wf_nat Strings.String Lists.List Lia Arith.PeanoNat.
Import ListNotations.

Section CostBasics.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.

Lemma contains_env_k_sym_free : forall σ S k Γs Γc,
  contains_env_k σ S k Γs Γc -> sym_free_env S Γs.
Proof.
  intros σ S k Γs Γc H.
  exact (proj1 (contains_env_sym_free σ S Γs Γc (contains_env_k_erase _ _ _ _ _ H))).
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

Section SmtCost.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.

Lemma unspool_smt_size : forall e L h args,
  unspool_app e L = (h, args) ->
  smt_size e + list_sum (map smt_size L) + length L =
  smt_size h + list_sum (map smt_size args) + length args.
Proof.
  induction e; intros L h args Hu; simpl in Hu;
    try (injection Hu as <- <-; reflexivity).
  apply IHe1 in Hu. simpl in *. lia.
Qed.

Lemma prim_slack_literals : forall ls,
  prim_slack (map ELit ls) = 1 + length ls + length ls.
Proof.
  intros ls. unfold prim_slack. rewrite length_map.
  assert (H : list_sum (map ground_size (map ELit ls)) = length ls).
  { induction ls as [| l ls IH]; simpl; [reflexivity |]. rewrite IH. reflexivity. }
  rewrite H. reflexivity.
Qed.

Lemma reduce_prim_literals_literal : forall p ls,
  exists l0, reduce_prim p (map ELit ls) = ELit l0.
Proof.
  intros p ls.
  apply reduce_prim_ground_value.
  apply solvable_everywhere_smt_ground. intros Γ.
  set (σ0 := fun _ : var => lit_true).
  set (S0 := fun _ : var => false).
  assert (Hargs : Forall2 (denote σ0 S0) (map ELit ls) ls).
  { induction ls as [| l ls IH]; simpl; constructor; [apply denote_lit | exact IH]. }
  destruct (reduce_prim_denote σ0 S0 p (map ELit ls) ls Hargs) as [pc [Hden _]].
  apply (expr_to_pc_solvable Γ _ pc). apply Hden.
  intros x Hx. discriminate Hx.
Qed.

Lemma solvable_value_contains_k : forall σ S Γ v l p args,
  Solvable Γ v ->
  denote σ S v l ->
  (v = ELit l \/ (exists x, v = EVar x) \/ v = reduce_prim p args) ->
  exists kv, kv <= smt_size v /\ contains_k σ S kv v (ELit l).
Proof.
  intros σ S Γ v l p args Hs Hden Hshape.
  destruct (smt_ground v) eqn:Hg.
  - exists 0. split; [lia |].
    destruct Hshape as [-> | [[x ->] | Hr]]; [apply ContK_Lit | simpl in Hg; discriminate |].
    rewrite Hr in Hg. destruct (reduce_prim_ground_value p args Hg) as [l' Hl'].
    rewrite Hr, Hl' in *. rewrite (denote_lit_inv σ S l' l Hden). apply ContK_Lit.
  - inversion Hs as [l' | x Hx | p0 | f a Hop Hf Ha]; subst.
    + simpl in Hg. discriminate.
    + destruct (denote_var_inv σ S x l Hden) as [Hsx ->].
      exists 0. split; [lia |]. apply ContK_Var_Sym. exact Hsx.
    + simpl in Hg. discriminate.
    + destruct (is_op_app_unspool (EApp f a) Hop) as [p0 [args0 Hu]].
      exists (smt_size (EApp f a)). split; [lia |].
      destruct Hshape as [Heq | [[x Heq] | Hr]]; try discriminate Heq.
      apply ContK_Denote with (p := p0) (args := args0); [exact Hu | | exact Hg | exact Hden].
      rewrite Hr in Hu. exact (reduce_prim_saturated p args p0 args0 Hu).
Qed.

Lemma denote_unspool_args : forall σ S e l p args,
  denote σ S e l -> unspool_app e [] = (EPrimOp p, args) ->
  exists ls, Forall2 (denote σ S) args ls.
Proof.
  intros σ S e l p args [pc [Hden _]] Hu.
  destruct e; simpl in Hu; try discriminate Hu.
  - injection Hu as _ <-. exists nil. constructor.
  - destruct (denotes_app_inv S e1 e2 pc Hden) as [p1 [pcs1 [pa [-> _]]]].
    destruct (denotes_unspool (EApp e1 e2) S p1 (pcs1 ++ [pa]) p args Hden Hu) as [_ HF].
    exists (map (pc_value σ) (pcs1 ++ [pa])).
    clear Hu Hden. induction HF; simpl; constructor; [| exact IHHF].
    exists y. split; [exact H | reflexivity].
Qed.

Definition smt_good σ S Φ Γ (e v : expr) (l : lit) : Prop :=
  eval Inf Φ Γ e v /\ smt_size v <= 2 * smt_size e /\
  exists kv, kv <= 2 * smt_size e /\ contains_k σ S kv v (ELit l).

Lemma smt_args_eval : forall σ S Φ Γ n args args' ls,
  (forall e v l, smt_size e < n -> denote σ S e l -> eval (Fin n) Φ Γ e v -> smt_good σ S Φ Γ e v l) ->
  Forall (fun a => smt_size a < n) args ->
  Forall2 (denote σ S) args ls ->
  Forall2 (eval (Fin n) Φ Γ) args args' ->
  Forall2 (eval Inf Φ Γ) args args' /\
  exists ks, Forall3 (contains_k σ S) ks args' (map ELit ls) /\
    list_sum ks <= 2 * list_sum (map smt_size args).
Proof.
  intros σ S Φ Γ n args args' ls IH Hsz Hden Hev. revert ls Hden Hsz.
  induction Hev as [| a a' l1 l2 Ha _ IHl]; intros ls Hden Hsz.
  - inversion Hden; subst. split; [constructor | exists nil; split; [constructor | simpl; lia]].
  - inversion Hden as [| a0 l0 l1' ls' Hd Hds]; subst.
    inversion Hsz as [| a1 l1'' Hs Hss]; subst.
    destruct (IH a a' l0 Hs Hd Ha) as [Hinf [_ [kv [Hkv Hc]]]].
    destruct (IHl ls' Hds Hss) as [Hinfs [ks [HF Hks]]].
    split; [constructor; assumption |].
    exists (kv :: ks). split; [constructor; assumption | simpl; lia].
Qed.

Lemma unspool_args_smaller : forall e p args,
  unspool_app e [] = (EPrimOp p, args) ->
  smt_size e = 1 + list_sum (map smt_size args) + length args.
Proof.
  intros e p args Hu. apply unspool_smt_size in Hu. simpl in Hu. lia.
Qed.

Lemma list_sum_map_le : forall (f : expr -> nat) l a,
  In a l -> f a <= list_sum (map f l).
Proof.
  intros f l a Hin. induction l as [| b l IH]; [destruct Hin |].
  destruct Hin as [-> | Hin]; simpl; [lia | specialize (IH Hin); lia].
Qed.

Lemma smt_eval_fin : forall σ S Φ Γ n e v l,
  σ ⊨ Φ -> sym_free_env S Γ -> smt_size e < n -> denote σ S e l ->
  eval (Fin n) Φ Γ e v -> smt_good σ S Φ Γ e v l.
Proof.
  intros σ S Φ Γ n. induction n as [| n IHn]; intros e v l Hmod Hfree Hsz Hden Hev; [lia |].
  assert (Hsolv : Solvable Γ e).
  { destruct Hden as [pc [Hd _]]. exact (expr_to_pc_solvable Γ e pc (Hd Γ Hfree)). }
  inversion Hev; subst;
    try solve [exfalso; inversion Hsolv; subst; simpl in *; congruence].
  - match goal with [Hn : lookup_env _ _ = None |- _] =>
      split; [apply Eval_SymVar; exact Hn | split; [simpl; lia |]] end.
    destruct (denote_var_inv σ S x l Hden) as [Hsx ->].
    exists 0. split; [lia | apply ContK_Var_Sym; exact Hsx].
  - rewrite <- (denote_lit_inv σ S l0 l Hden).
    split; [apply Eval_Lit | split; [simpl; lia | exists 0; split; [lia | apply ContK_Lit]]].
  - exfalso.
    match goal with [Hu : unspool_app _ _ = (ECon _, _) |- _] => apply unspool_is_con_app in Hu end.
    rewrite (solvable_not_con_app Γ e Hsolv) in *. discriminate.
  - exfalso. inversion Hsolv; subst.
    match goal with [Hc : Comp _ ?f, Hs : Solvable _ ?f |- _] => exact (comp_not_solvable _ _ Hc Hs) end.
  - match goal with
    | [ Hu : unspool_app (EApp ef ea) [] = (EPrimOp p, ?a),
        Hl : length ?a = primop_arity p,
        Hargs : Forall2 _ ?a args' |- _ ] => rename a into args; rename Hu into Hun;
                                             rename Hargs into Hev_args
    end.
    destruct (denote_unspool_args σ S _ l p args Hden Hun) as [ls Hls].
    pose proof (unspool_args_smaller _ _ _ Hun) as Hse.
    assert (Hsizes : Forall (fun a => smt_size a < n) args).
    { apply Forall_forall. intros a Ha.
      pose proof (list_sum_map_le smt_size args a Ha). lia. }
    change (dec (Remaining n)) with (Fin n) in Hev_args.
    destruct (smt_args_eval σ S Φ Γ n args args' ls
                (fun e v l Hs Hd Hv => IHn e v l Hmod Hfree Hs Hd Hv) Hsizes Hls Hev_args)
      as [Hinf [ks [HF Hks]]].
    assert (Hevinf : eval Inf Φ Γ (EApp ef ea) (reduce_prim p args'))
      by (eapply Eval_AppPrim; eassumption).
    split; [exact Hevinf |].
    destruct (reduce_prim_contains_k σ S p ks args' (map ELit ls) (closed_term_lits ls) HF) as [k' [Hk' Hc']].
    destruct (reduce_prim_literals_literal p ls) as [l0 Hl0]. rewrite Hl0 in Hc'.
    pose proof (smt_size_contains_k _ _ _ _ _ Hc') as Hsv. simpl in Hsv.
    rewrite prim_slack_literals in Hk'.
    pose proof (Forall2_length Hls) as Hlen.
    assert (Hsize : smt_size (reduce_prim p args') <= 2 * smt_size (EApp ef ea)) by lia.
    split; [exact Hsize |].
    pose proof (eval_denote Φ Γ σ S _ _ l Hmod Hfree Hevinf Hden) as Hden'.
    pose proof (solvable_eval_solvable Inf Φ Γ _ _ Hevinf eq_refl (models_sat σ Φ Hmod) Hsolv) as Hsv'.
    destruct (solvable_value_contains_k σ S Γ _ l p args' Hsv' Hden'
                (or_intror (or_intror eq_refl))) as [kv [Hkv Hcv]].
    exists kv. split; [lia | exact Hcv].
  - exfalso.
    match goal with
    | [ Hu : unspool_app (EApp _ _) _ = (EIf _ _ _, _) |- _ ] =>
        exact (solvable_unspool_not_if _ _ _ _ _ _ _ Hsolv Hu)
    end.
  - exfalso. apply models_sat in Hmod. congruence.
Qed.

End SmtCost.

Ltac sym_absurd :=
  first
  [ match goal with [ Hs : sat _ = false, Hm : models _ _ |- _ ] =>
      apply models_sat in Hm; congruence end
  | match goal with [ H : unspool_app _ _ = _ |- _ ] => simpl in H; discriminate H end
  | congruence
  | match goal with [ Hc : Comp _ ?f, Hu : unspool_app (EApp ?f ?a) nil = _ |- _ ] =>
      pose proof (comp_spine_head _ _ _ _ _ Hc Hu) as Hsh; simpl in *; discriminate end
  | match goal with [ Hc : Comp _ _ |- _ ] => inversion Hc; subst; simpl in *; discriminate end ].

