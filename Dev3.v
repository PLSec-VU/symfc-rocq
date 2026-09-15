From SymCoreTheory Require Import SymCore ConCore BranchLaws CostLaws Dev1 Dev2.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Arith.Wf_nat Lia.
Import ListNotations.

Ltac sym_absurd :=
  first
  [ match goal with [ Hs : sat _ = false, Hm : models _ _ |- _ ] =>
      apply models_sat in Hm; congruence end
  | match goal with [ H : unspool_app _ _ = _ |- _ ] => simpl in H; discriminate H end
  | congruence
  | match goal with [ Hc : Comp _ ?f, Hu : unspool_app (EApp ?f ?a) nil = _ |- _ ] =>
      pose proof (comp_spine_head _ _ _ _ _ Hc Hu) as Hsh; simpl in *; discriminate end
  | match goal with [ Hc : Comp _ _ |- _ ] => inversion Hc; subst; simpl in *; discriminate end ].

Section Peel.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Definition good_at (A : environment -> Prop) (e_c v_c : expr) (bk be : nat) : Prop :=
  exists h K, forall Γc Φ Γs e_s k kenv n v_s,
    A Γc -> k <= bk -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k e_s e_c ->
    h <= n -> eval (Fin n) Φ Γs e_s v_s ->
    exists k', k' <= K /\ contains_k σ S k' v_s v_c.

Definition core_at (A : environment -> Prop) (e_c v_c : expr) (bk be : nat) : Prop :=
  exists h K, forall Γc Φ Γs e_s k kenv n v_s,
    A Γc -> k <= bk -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k e_s e_c ->
    is_if (fst (unspool_app e_s [])) = false ->
    h <= n -> eval (Fin n) Φ Γs e_s v_s ->
    exists k', k' <= K /\ contains_k σ S k' v_s v_c.

Definition good (A : environment -> Prop) (e_c v_c : expr) : Prop :=
  forall bk be, good_at A e_c v_c bk be.

Lemma guard_true : forall Φ Γ g g' pc n,
  σ ⊨ Φ -> sym_free_env S Γ -> models_cond σ S g -> smt_size g < n ->
  eval (Fin n) Φ Γ g g' -> expr_to_pc Γ g' = Some pc ->
  σ ⊨ (Φ ∧ pc) /\ smt_size g' <= 2 * smt_size g /\ models_cond σ S g'.
Proof.
  intros Φ Γ g g' pc n Hm Hf Hc Hs Hev Hpc.
  destruct Hc as [pc0 [Hd Hv]].
  destruct (smt_eval_fin σ S Φ Γ n g g' (pc_value σ pc0) Hm Hf Hs
              (ex_intro _ pc0 (conj Hd eq_refl)) Hev) as [Hinf [Hsz _]].
  assert (Hc' : models_cond σ S g') by
    (eapply eval_models_cond; [exact Hm | exact Hf | exact Hinf | exists pc0; split; assumption]).
  split; [| split; assumption].
  apply models_and_iff. split; [exact Hm |]. exact (models_cond_pc σ S Γ g' pc Hpc Hc').
Qed.

Lemma guard_false : forall Φ Γ g g' pc n,
  σ ⊨ Φ -> sym_free_env S Γ -> models_not_cond σ S g -> smt_size g < n ->
  eval (Fin n) Φ Γ g g' -> expr_to_pc Γ g' = Some pc ->
  σ ⊨ (Φ ∧ ¬ pc) /\ smt_size g' <= 2 * smt_size g /\ models_not_cond σ S g'.
Proof.
  intros Φ Γ g g' pc n Hm Hf Hc Hs Hev Hpc.
  destruct Hc as [pc0 [Hd Hv]].
  destruct (smt_eval_fin σ S Φ Γ n g g' (pc_value σ pc0) Hm Hf Hs
              (ex_intro _ pc0 (conj Hd eq_refl)) Hev) as [Hinf [Hsz _]].
  assert (Hc' : models_not_cond σ S g') by
    (eapply eval_models_not_cond; [exact Hm | exact Hf | exact Hinf | exists pc0; split; assumption]).
  split; [| split; assumption].
  apply models_and_iff. split; [exact Hm |]. exact (models_not_cond_pc σ S Γ g' pc Hpc Hc').
Qed.

Lemma if_step_true : forall Φ Γ g t f v n,
  σ ⊨ Φ -> sym_free_env S Γ -> models_cond σ S g -> smt_size g < n ->
  eval (Fin (Datatypes.S n)) Φ Γ (EIf g t f) v ->
  exists g' t' f' pc, v = EIf g' t' f' /\ eval (Fin n) (Φ ∧ pc) Γ t t' /\
    σ ⊨ (Φ ∧ pc) /\ smt_size g' <= 2 * smt_size g /\ models_cond σ S g'.
Proof.
  intros Φ Γ g t f v n Hm Hf Hc Hs Hev.
  inversion Hev; subst; try sym_absurd; change (dec (Remaining n)) with (Fin n) in *.
  match goal with
  | [ Hg : eval _ _ _ g ?g0, Hpc : expr_to_pc _ ?g0 = Some ?pc0 |- _ ] =>
      destruct (guard_true Φ Γ g g0 pc0 n Hm Hf Hc Hs Hg Hpc) as [Hm' [Hsz Hc']]
  end.
  do 4 eexists. split; [reflexivity |]. split; [eassumption |].
  split; [exact Hm' | split; assumption].
Qed.

Lemma if_step_false : forall Φ Γ g t f v n,
  σ ⊨ Φ -> sym_free_env S Γ -> models_not_cond σ S g -> smt_size g < n ->
  eval (Fin (Datatypes.S n)) Φ Γ (EIf g t f) v ->
  exists g' t' f' pc, v = EIf g' t' f' /\ eval (Fin n) (Φ ∧ ¬ pc) Γ f f' /\
    σ ⊨ (Φ ∧ ¬ pc) /\ smt_size g' <= 2 * smt_size g /\ models_not_cond σ S g'.
Proof.
  intros Φ Γ g t f v n Hm Hf Hc Hs Hev.
  inversion Hev; subst; try sym_absurd; change (dec (Remaining n)) with (Fin n) in *.
  match goal with
  | [ Hg : eval _ _ _ g ?g0, Hpc : expr_to_pc _ ?g0 = Some ?pc0 |- _ ] =>
      destruct (guard_false Φ Γ g g0 pc0 n Hm Hf Hc Hs Hg Hpc) as [Hm' [Hsz Hc']]
  end.
  do 4 eexists. split; [reflexivity |]. split; [eassumption |].
  split; [exact Hm' | split; assumption].
Qed.

Lemma app_if_step : forall Φ Γ e1 e2 g t f args v n,
  σ ⊨ Φ ->
  unspool_app (EApp e1 e2) [] = (EIf g t f, args) ->
  eval (Fin (Datatypes.S n)) Φ Γ (EApp e1 e2) v ->
  eval (Fin n) Φ Γ (EIf g (fold_left EApp args t) (fold_left EApp args f)) v.
Proof.
  intros Φ Γ e1 e2 g t f args v n Hm Hu Hev.
  inversion Hev; subst; try sym_absurd; change (dec (Remaining n)) with (Fin n) in *.
  match goal with
  | [ Hu' : unspool_app (EApp e1 e2) [] = (EIf _ _ _, _), Hr : eval _ _ _ (EIf _ _ _) v |- _ ] =>
      rewrite Hu in Hu'; injection Hu' as <- <- <- <-; exact Hr
  end.
Qed.

Lemma good_at_of_core : forall A e_c v_c,
  (forall bk be, (forall bk', bk' < bk -> forall be', good_at A e_c v_c bk' be') ->
     core_at A e_c v_c bk be) ->
  good A e_c v_c.
Proof.
  intros A e_c v_c Hcore bk. induction bk as [bk IH] using lt_wf_ind. intros be.
  destruct (Hcore bk be IH) as [hc [Kc Hc]].
  assert (Hprev : exists h1 K1, forall Γc Φ Γs e_s k kenv n v_s,
    A Γc -> k < bk -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k e_s e_c ->
    h1 <= n -> eval (Fin n) Φ Γs e_s v_s ->
    exists k', k' <= K1 /\ contains_k σ S k' v_s v_c).
  { destruct bk as [| bk'].
    - exists 0, 0. intros. lia.
    - destruct (IH bk' ltac:(lia) be) as [h1 [K1 H1]].
      exists h1, K1. intros Γc0 Φ0 Γs0 e0 k0 ke0 n0 v0 HA0 Hk0 Hke0 Hm0 He0 Hc0 Hn0 Hev0.
      exact (H1 Γc0 Φ0 Γs0 e0 k0 ke0 n0 v0 HA0 ltac:(lia) Hke0 Hm0 He0 Hc0 Hn0 Hev0). }
  destruct Hprev as [h1 [K1 H1]].
  exists (2 + bk + hc + h1), (1 + 2 * bk + Kc + K1).
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hn Hev.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  destruct (is_if (fst (unspool_app e_s []))) eqn:Hif.
  2: { destruct (Hc Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif ltac:(lia) Hev)
         as [k' [Hk' Hc']].
       exists k'. split; [lia | exact Hc']. }
  destruct n as [| n]; [lia |].
  destruct e_s; simpl in Hif; try discriminate Hif.
  - change (unspool_app e_s1 [e_s2]) with (unspool_app (EApp e_s1 e_s2) []) in Hif.
    destruct (unspool_app (EApp e_s1 e_s2) []) as [hd args] eqn:Hu.
    simpl in Hif. destruct hd; simpl in Hif; try discriminate Hif.
    pose proof (app_if_step Φ Γs _ _ _ _ _ _ _ n Hm Hu Hev) as Hev1.
    destruct n as [| n]; [lia |].
    destruct (contains_k_app_if_spine σ S k _ _ _ _ _ args e_c Hcont Hu)
      as [k0 [Hk0 [[Hmc Harm] | [Hmc Harm]]]].
    + destruct (if_step_true Φ Γs _ _ _ v_s n Hm Hfree Hmc ltac:(lia) Hev1)
        as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
      destruct (H1 Γc _ Γs _ k0 kenv n t' HA ltac:(lia) Hkenv Hm' Henv Harm ltac:(lia) Ht)
        as [k' [Hk' Hc'']].
      exists (1 + smt_size g' + k'). split; [lia | apply ContK_If_True; assumption].
    + destruct (if_step_false Φ Γs _ _ _ v_s n Hm Hfree Hmc ltac:(lia) Hev1)
        as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
      destruct (H1 Γc _ Γs _ k0 kenv n f' HA ltac:(lia) Hkenv Hm' Henv Harm ltac:(lia) Ht)
        as [k' [Hk' Hc'']].
      exists (1 + smt_size g' + k'). split; [lia | apply ContK_If_False; assumption].
  - destruct (contains_k_if_inv σ S k _ _ _ e_c Hcont) as [k0 [Hk0 [[Hmc Harm] | [Hmc Harm]]]].
    + destruct (if_step_true Φ Γs _ _ _ v_s n Hm Hfree Hmc ltac:(lia) Hev)
        as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
      destruct (H1 Γc _ Γs _ k0 kenv n t' HA ltac:(lia) Hkenv Hm' Henv Harm ltac:(lia) Ht)
        as [k' [Hk' Hc'']].
      exists (1 + smt_size g' + k'). split; [lia | apply ContK_If_True; assumption].
    + destruct (if_step_false Φ Γs _ _ _ v_s n Hm Hfree Hmc ltac:(lia) Hev)
        as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
      destruct (H1 Γc _ Γs _ k0 kenv n f' HA ltac:(lia) Hkenv Hm' Henv Harm ltac:(lia) Ht)
        as [k' [Hk' Hc'']].
      exists (1 + smt_size g' + k'). split; [lia | apply ContK_If_False; assumption].
Qed.

End Peel.
