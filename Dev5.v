From SymCoreTheory Require Import SymCore ConCore BranchLaws CostLaws Dev1 Dev2 Dev3.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Arith.Wf_nat Lia.
Import ListNotations.

Section FoldPeel.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Definition fgood_at (A : environment -> Prop) (esc : expr) (altsc : list alt) (v_c : expr)
  (bk be : nat) : Prop :=
  exists h K, forall Γc Φ Γs m altss k ks kenv n v_s,
    A Γc -> k <= bk -> kenv <= be -> list_sum ks <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k m esc ->
    Forall3 (contains_alt_k σ S) ks altss altsc ->
    h <= n -> fold_alts (Fin n) Φ Γs m altss v_s ->
    exists k', k' <= K /\ contains_k σ S k' v_s v_c.

Definition fcore_at (A : environment -> Prop) (esc : expr) (altsc : list alt) (v_c : expr)
  (bk be : nat) : Prop :=
  exists h K, forall Γc Φ Γs m altss k ks kenv n v_s,
    A Γc -> k <= bk -> kenv <= be -> list_sum ks <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k m esc ->
    Forall3 (contains_alt_k σ S) ks altss altsc ->
    is_if (fst (unspool_app m [])) = false ->
    h <= n -> fold_alts (Fin n) Φ Γs m altss v_s ->
    exists k', k' <= K /\ contains_k σ S k' v_s v_c.

Definition fgood (A : environment -> Prop) (esc : expr) (altsc : list alt) (v_c : expr) : Prop :=
  forall bk be, fgood_at A esc altsc v_c bk be.

Lemma models_cond_expr_to_pc : forall Γ g,
  sym_free_env S Γ -> models_cond σ S g \/ models_not_cond σ S g ->
  exists pc, expr_to_pc Γ g = Some pc.
Proof. intros Γ g Hf Hj. exact (models_cond_total σ S Γ g Hf Hj). Qed.

Lemma fgood_of_core : forall A esc altsc v_c,
  (forall bk be, (forall bk', bk' < bk -> forall be', fgood_at A esc altsc v_c bk' be') ->
     fcore_at A esc altsc v_c bk be) ->
  fgood A esc altsc v_c.
Proof.
  intros A esc altsc v_c Hcore bk. induction bk as [bk IH] using lt_wf_ind. intros be.
  destruct (Hcore bk be IH) as [hc [Kc Hc]].
  assert (Hprev : exists h1 K1, forall Γc Φ Γs m altss k ks kenv n v_s,
    A Γc -> k < bk -> kenv <= be -> list_sum ks <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k m esc ->
    Forall3 (contains_alt_k σ S) ks altss altsc ->
    h1 <= n -> fold_alts (Fin n) Φ Γs m altss v_s ->
    exists k', k' <= K1 /\ contains_k σ S k' v_s v_c).
  { destruct bk as [| bk'].
    - exists 0, 0. intros. lia.
    - destruct (IH bk' ltac:(lia) be) as [h1 [K1 H1]].
      exists h1, K1. intros Γc0 Φ0 Γs0 m0 al0 k0 ks0 ke0 n0 v0 HA0 Hk0 Hke0 Hks0 Hm0 He0 Hc0 Ha0 Hn0 Hev0.
      exact (H1 Γc0 Φ0 Γs0 m0 al0 k0 ks0 ke0 n0 v0 HA0 ltac:(lia) Hke0 Hks0 Hm0 He0 Hc0 Ha0 Hn0 Hev0). }
  destruct Hprev as [h1 [K1 H1]].
  exists (hc + h1), (1 + bk + Kc + K1).
  intros Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv Hcont Halts Hn Hev.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  destruct (is_if (fst (unspool_app m []))) eqn:Hif.
  2: { destruct (Hc Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv Hcont Halts Hif
                  ltac:(lia) Hev) as [k' [Hk' Hc']].
       exists k'. split; [lia | exact Hc']. }
  destruct m; simpl in Hif; try discriminate Hif.
  - exfalso.
    change (unspool_app m1 [m2]) with (unspool_app (EApp m1 m2) []) in Hif.
    destruct (unspool_app (EApp m1 m2) []) as [hd args] eqn:Hu.
    simpl in Hif. destruct hd; simpl in Hif; try discriminate Hif.
    inversion Hev; subst.
    + match goal with [ Hd : decompose_con_app _ = Some _ |- _ ] =>
        unfold decompose_con_app in Hd; rewrite Hu in Hd; discriminate Hd end.
    + match goal with [ Hi : is_if (fst (unspool_app _ _)) = false |- _ ] =>
        rewrite Hu in Hi; simpl in Hi; discriminate Hi end.
  - destruct (contains_k_if_inv σ S k _ _ _ esc Hcont) as [k0 [Hk0 [[Hmc Harm] | [Hmc Harm]]]].
    + inversion Hev; subst.
      * match goal with [ Hp : expr_to_pc _ m1 = Some ?pc, Ht : fold_alts _ (Φ ∧ ?pc) _ m2 _ ?t' |- _ ] =>
          assert (Hm' : σ ⊨ (Φ ∧ pc))
            by (apply models_and_iff; split; [exact Hm | exact (models_cond_pc σ S Γs m1 pc Hp Hmc)]);
          destruct (H1 Γc _ Γs m2 altss k0 ks kenv n t' HA ltac:(lia) Hkenv Hks Hm' Henv Harm Halts
                      ltac:(lia) Ht) as [k' [Hk' Hc']];
          exists (1 + smt_size m1 + k'); split; [lia | apply ContK_If_True; assumption]
        end.
      * exfalso. destruct (models_cond_expr_to_pc Γs m1 Hfree (or_introl Hmc)) as [pc Hpc]. congruence.
      * exfalso. match goal with [ Hd : decompose_con_app _ = Some _ |- _ ] => discriminate Hd end.
      * exfalso. match goal with [ Hi : is_if _ = false |- _ ] => discriminate Hi end.
    + inversion Hev; subst.
      * match goal with [ Hp : expr_to_pc _ m1 = Some ?pc, Ht : fold_alts _ (Φ ∧ ¬ ?pc) _ m3 _ ?t' |- _ ] =>
          assert (Hm' : σ ⊨ (Φ ∧ ¬ pc))
            by (apply models_and_iff; split; [exact Hm | exact (models_not_cond_pc σ S Γs m1 pc Hp Hmc)]);
          destruct (H1 Γc _ Γs m3 altss k0 ks kenv n t' HA ltac:(lia) Hkenv Hks Hm' Henv Harm Halts
                      ltac:(lia) Ht) as [k' [Hk' Hc']];
          exists (1 + smt_size m1 + k'); split; [lia | apply ContK_If_False; assumption]
        end.
      * exfalso. destruct (models_cond_expr_to_pc Γs m1 Hfree (or_intror Hmc)) as [pc Hpc]. congruence.
      * exfalso. match goal with [ Hd : decompose_con_app _ = Some _ |- _ ] => discriminate Hd end.
      * exfalso. match goal with [ Hi : is_if _ = false |- _ ] => discriminate Hi end.
Qed.

End FoldPeel.
