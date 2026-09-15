From SymCoreTheory Require Import SymCore ConCore BranchLaws CostLaws Model.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.
Open Scope string_scope.

Fixpoint and_tower (n : nat) (e : expr) : expr :=
  match n with
  | O => e
  | S n' => EApp (EPrimOp PAnd) (and_tower n' e)
  end.

Definition sigma_all : valuation := fun _ => true.
Definition all_symvars : symvars := fun _ => true.
Definition sym_x : expr := EVar "x".
Definition lit_true : expr := @ELit model_sorts true.

Lemma and_tower_contains_k : forall n,
  contains_k sigma_all all_symvars 0 (and_tower n sym_x) (and_tower n lit_true).
Proof.
  induction n as [| n IH]; simpl.
  - exact (ContK_Var_Sym sigma_all all_symvars "x" eq_refl).
  - exact (ContK_App sigma_all all_symvars 0 0 _ _ _ _ (ContK_PrimOp _ _ PAnd) IH).
Qed.

Lemma and_tower_facts : forall n e,
  flat e = true ->
  flat (and_tower n e) = true /\ smt_size (and_tower n e) = 2 * n + smt_size e /\
  smt_ground (and_tower n e) = smt_ground e /\ is_if (and_tower n e) = false /\
  (0 < n -> is_op_app (and_tower n e) = true) .
Proof.
  intros n e He. induction n as [| n [Hf [Hs [Hg [Hi _]]]]]; simpl.
  - split; [exact He | split; [lia | split; [reflexivity | split; [exact (flat_not_if e He) | lia]]]].
  - rewrite Hf, Hs, Hg. split; [reflexivity | split; [lia | split; [reflexivity | split; [reflexivity | reflexivity]]]].
Qed.

Lemma reduce_not_flat : forall a,
  flat a = true ->
  reduce_prim PNot (a :: nil) = fold_leaf (EApp (EPrimOp PNot) a).
Proof.
  intros a Hf.
  change (model_reduce_prim PNot (a :: nil) = fold_leaf (EApp (EPrimOp PNot) a)).
  unfold model_reduce_prim.
  rewrite split_args_not_if by (constructor; [apply flat_not_if; exact Hf | constructor]).
  unfold reduce_unbranched, op_spine. cbn [length model_arity Nat.eqb fold_left].
  rewrite lift_flat by (simpl; rewrite Hf; reflexivity).
  reflexivity.
Qed.

Lemma app_contains_k_lit : forall σ S k f a l,
  contains_k σ S k (EApp f a) (ELit l) -> k = smt_size (EApp f a).
Proof. intros σ S k f a l H. inversion H; subst. reflexivity. Qed.

Theorem model_breaks_constant_slack : forall c,
  ~ (forall σ S p ks args_s args_c,
       Forall3 (contains_k σ S) ks args_s args_c ->
       exists k', k' <= list_sum ks + c /\
         contains_k σ S k' (reduce_prim p args_s) (reduce_prim p args_c)).
Proof.
  intros c Hlaw.
  destruct (Hlaw sigma_all all_symvars PNot (0 :: nil)
              (and_tower c sym_x :: nil) (and_tower c lit_true :: nil)
              (Forall3_cons _ _ _ _ _ _ _ (and_tower_contains_k c) (Forall3_nil _)))
    as [k' [Hle Hc]].
  destruct (and_tower_facts c sym_x eq_refl) as [Hfs [Hss [Hgs _]]].
  destruct (and_tower_facts c lit_true eq_refl) as [Hfc [_ [Hgc _]]].
  rewrite (reduce_not_flat _ Hfs), (reduce_not_flat _ Hfc) in Hc.
  unfold fold_leaf in Hc. cbn [smt_ground is_op_app andb] in Hc.
  rewrite Hgs, Hgc in Hc. simpl in Hc.
  apply app_contains_k_lit in Hc. simpl in Hc. simpl in Hle.
  rewrite Hss in Hc. simpl in Hc. lia.
Qed.

Print Assumptions model_breaks_constant_slack.

Fixpoint not_tower (n : nat) : expr :=
  match n with
  | O => sym_x
  | S n' => EApp (EPrimOp PNot) (not_tower n')
  end.

Lemma not_tower_denotes : forall n, exists pc, denotes all_symvars (not_tower n) pc.
Proof.
  induction n as [| n [pc IH]].
  - exists (PCVar "x"). intros Γ Hfree. simpl. rewrite (Hfree "x" eq_refl). reflexivity.
  - exists (@PCPrim model_sorts PNot (pc :: nil)).
    exact (op_spine_denotes all_symvars (not_tower n :: nil) (pc :: nil)
             (Forall2_cons _ _ IH (Forall2_nil _)) (@EPrimOp model_sorts PNot) PNot nil (fun Γ _ => eq_refl)).
Qed.

Lemma not_tower_facts : forall n,
  flat (not_tower n) = true /\ smt_size (not_tower n) = 2 * n + 1 /\ smt_ground (not_tower n) = false.
Proof.
  induction n as [| n [Hf [Hs Hg]]]; simpl; [split; [reflexivity | split; reflexivity] |].
  rewrite Hf, Hs, Hg. split; [reflexivity | split; [lia | reflexivity]].
Qed.

Lemma lit_true_models : models_cond sigma_all all_symvars lit_true.
Proof. exists (@PCLit model_sorts true). split; [intros Γ _; reflexivity | reflexivity]. Qed.

Theorem model_ite_needs_arm_sizes : forall c,
  ~ (forall σ S k ec et ef pt pf l,
       denotes S et pt -> denotes S ef pf ->
       contains_k σ S k (EIf ec et ef) (ELit l) ->
       exists k', k' <= k + c /\
         contains_k σ S k' (reduce_prim op_ite (ec :: et :: ef :: nil)) (ELit l)).
Proof.
  intros c Hlaw.
  destruct (not_tower_denotes c) as [pf Hpf].
  destruct (not_tower_facts c) as [Hf [Hs Hg]].
  assert (Hc : contains_k sigma_all all_symvars 2 (EIf lit_true lit_true (not_tower c)) lit_true)
    by exact (ContK_If_True sigma_all all_symvars 0 lit_true lit_true (not_tower c) lit_true
                lit_true_models (ContK_Lit _ _ true)).
  destruct (Hlaw sigma_all all_symvars 2 lit_true lit_true (not_tower c) (@PCLit model_sorts true) pf true
              (fun Γ _ => eq_refl) Hpf Hc) as [k' [Hle Hk']].
  change (contains_k sigma_all all_symvars k'
            (model_reduce_prim PIte (lit_true :: lit_true :: not_tower c :: nil)) (ELit true)) in Hk'.
  unfold model_reduce_prim in Hk'.
  rewrite split_args_not_if in Hk'
    by (repeat constructor; apply flat_not_if; exact Hf).
  unfold reduce_unbranched, op_spine in Hk'. cbn [length model_arity Nat.eqb fold_left] in Hk'.
  rewrite lift_flat in Hk' by (simpl; rewrite Hf; reflexivity).
  rewrite fold_leaves_not_if in Hk' by reflexivity. unfold fold_leaf in Hk'. cbn [smt_ground is_op_app andb] in Hk'. rewrite Hg in Hk'.
  simpl in Hk'.
  apply app_contains_k_lit in Hk'. simpl in Hk'. rewrite Hs in Hk'. lia.
Qed.

Print Assumptions model_ite_needs_arm_sizes.
