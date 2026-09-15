From SymCoreTheory Require Import SymCore ConCore BranchLaws CostLaws Dev1.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.

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
    destruct (reduce_prim_contains_k σ S p ks args' (map ELit ls) HF) as [k' [Hk' Hc']].
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
