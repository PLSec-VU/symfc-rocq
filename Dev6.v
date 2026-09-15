From SymCoreTheory Require Import SymCore ConCore BranchLaws CostLaws Dev1 Dev2 Dev3.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Arith.Wf_nat Lia.
Import ListNotations.

Section Closures.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Inductive clos_tree (C : expr) : nat -> expr -> Prop :=
  | CT_Leaf : forall k Γ x e,
      contains_k σ S k (EThunk Γ (ELam x e)) C -> clos_tree C k (EThunk Γ (ELam x e))
  | CT_True : forall k g t f,
      models_cond σ S g -> clos_tree C k t -> clos_tree C (1 + smt_size g + k) (EIf g t f)
  | CT_False : forall k g t f,
      models_not_cond σ S g -> clos_tree C k f -> clos_tree C (1 + smt_size g + k) (EIf g t f).

Lemma lam_body_value : forall Γc x ec bk be, exists h K,
  forall Φ Γs es k kenv n v,
    k <= bk -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k es (ELam x ec) ->
    h <= n -> eval (Fin n) Φ Γs es v ->
    exists k', k' <= K /\ clos_tree (EThunk Γc (ELam x ec)) k' v.
Proof.
  intros Γc x ec bk. induction bk as [bk IH] using lt_wf_ind. intros be.
  assert (Hprev : exists h1 K1, forall Φ Γs es k kenv n v,
    k < bk -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k es (ELam x ec) ->
    h1 <= n -> eval (Fin n) Φ Γs es v ->
    exists k', k' <= K1 /\ clos_tree (EThunk Γc (ELam x ec)) k' v).
  { destruct bk as [| bk'].
    - exists 0, 0. intros. lia.
    - destruct (IH bk' ltac:(lia) be) as [h1 [K1 H1]].
      exists h1, K1. intros Φ0 Γs0 es0 k0 ke0 n0 v0 Hk0 Hke0 Hm0 He0 Hc0 Hn0 Hev0.
      exact (H1 Φ0 Γs0 es0 k0 ke0 n0 v0 ltac:(lia) Hke0 Hm0 He0 Hc0 Hn0 Hev0). }
  destruct Hprev as [h1 [K1 H1]].
  exists (2 + bk + h1), (1 + be + 2 * bk + K1).
  intros Φ Γs es k kenv n v Hk Hkenv Hm Henv Hcont Hn Hev.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try (match goal with [ Ht : is_thunk _ = true |- _ ] => simpl in Ht; discriminate Ht end).
  - inversion Hev; subst; try sym_absurd.
    exists (kenv + k). split; [lia |].
    apply CT_Leaf. apply ContK_Thunk; [exact Henv | apply ContK_Lam; assumption].
  - destruct (if_step_true σ S Φ Γs _ _ _ v n Hm Hfree ltac:(eassumption) ltac:(lia) Hev)
      as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
    destruct (H1 _ Γs _ k0 kenv n t' ltac:(lia) Hkenv Hm' Henv ltac:(eassumption) ltac:(lia) Ht)
      as [k' [Hk' Hct]].
    exists (1 + smt_size g' + k'). split; [lia | apply CT_True; assumption].
  - destruct (if_step_false σ S Φ Γs _ _ _ v n Hm Hfree ltac:(eassumption) ltac:(lia) Hev)
      as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
    destruct (H1 _ Γs _ k0 kenv n f' ltac:(lia) Hkenv Hm' Henv ltac:(eassumption) ltac:(lia) Ht)
      as [k' [Hk' Hct]].
    exists (1 + smt_size g' + k'). split; [lia | apply CT_False; assumption].
Qed.

Lemma clos_value : forall Γc x ec bk, exists h K,
  forall Φ Γs es k n v,
    k <= bk -> σ ⊨ Φ -> sym_free_env S Γs ->
    contains_k σ S k es (EThunk Γc (ELam x ec)) ->
    h <= n -> eval (Fin n) Φ Γs es v ->
    exists k', k' <= K /\ clos_tree (EThunk Γc (ELam x ec)) k' v.
Proof.
  intros Γc x ec bk. induction bk as [bk IH] using lt_wf_ind.
  assert (Hprev : exists h1 K1, forall Φ Γs es k n v,
    k < bk -> σ ⊨ Φ -> sym_free_env S Γs ->
    contains_k σ S k es (EThunk Γc (ELam x ec)) ->
    h1 <= n -> eval (Fin n) Φ Γs es v ->
    exists k', k' <= K1 /\ clos_tree (EThunk Γc (ELam x ec)) k' v).
  { destruct bk as [| bk'].
    - exists 0, 0. intros. lia.
    - destruct (IH bk' ltac:(lia)) as [h1 [K1 H1]].
      exists h1, K1. intros Φ0 Γs0 es0 k0 n0 v0 Hk0 Hm0 Hf0 Hc0 Hn0 Hev0.
      exact (H1 Φ0 Γs0 es0 k0 n0 v0 ltac:(lia) Hm0 Hf0 Hc0 Hn0 Hev0). }
  destruct Hprev as [h1 [K1 H1]].
  destruct (lam_body_value Γc x ec bk bk) as [hl [Kl Hl]].
  exists (2 + bk + h1 + hl), (1 + 2 * bk + K1 + Kl).
  intros Φ Γs es k n v Hk Hm Hfree Hcont Hn Hev.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst.
  - inversion Hev; subst; try sym_absurd.
    change (dec (Remaining n)) with (Fin n) in *.
    match goal with
    | [ He : contains_env_k _ _ ?ke ?G _, Hb : contains_k _ _ ?kb ?b (ELam _ _),
        Hv : eval (Fin n) _ ?G ?b v |- _ ] =>
        destruct (Hl Φ G b kb ke n v ltac:(lia) ltac:(lia) Hm He Hb ltac:(lia) Hv) as [k' [Hk' Hct]]
    end.
    exists k'. split; [lia | exact Hct].
  - inversion Hev; subst; try sym_absurd.
    change (dec (Remaining n)) with (Fin n) in *.
    match goal with
    | [ He : contains_env_k _ _ ?ke ?G _, Hb : contains_k _ _ ?kb ?b (EThunk _ _),
        Hv : eval (Fin n) _ ?G ?b v |- _ ] =>
        destruct (H1 Φ G b kb n v ltac:(lia) Hm (contains_env_k_sym_free _ _ _ _ _ He) Hb ltac:(lia) Hv)
          as [k' [Hk' Hct]]
    end.
    exists k'. split; [lia | exact Hct].
  - destruct (if_step_true σ S Φ Γs _ _ _ v n Hm Hfree ltac:(eassumption) ltac:(lia) Hev)
      as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
    destruct (H1 _ Γs _ k0 n t' ltac:(lia) Hm' Hfree ltac:(eassumption) ltac:(lia) Ht)
      as [k' [Hk' Hct]].
    exists (1 + smt_size g' + k'). split; [lia | apply CT_True; assumption].
  - destruct (if_step_false σ S Φ Γs _ _ _ v n Hm Hfree ltac:(eassumption) ltac:(lia) Hev)
      as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
    destruct (H1 _ Γs _ k0 n f' ltac:(lia) Hm' Hfree ltac:(eassumption) ltac:(lia) Ht)
      as [k' [Hk' Hct]].
    exists (1 + smt_size g' + k'). split; [lia | apply CT_False; assumption].
Qed.

Lemma clos_tree_contains : forall C k m, clos_tree C k m -> contains_k σ S k m C.
Proof.
  intros C k m H. induction H.
  - assumption.
  - apply ContK_If_True; assumption.
  - apply ContK_If_False; assumption.
Qed.

Section AppAbs.
Variables (Γc0 Γc' : environment) (x : var) (eb ea v_c : expr).
Hypothesis Hbody : good σ S (eq (extend_env Γc' x Γc0 ea)) eb v_c.
Hypothesis Hea : concore_expr ea.

Lemma app_abs_tree : forall bk be, exists h K,
  forall Φ Γs f a kf ka kenv n v_s,
    kf <= bk -> ka <= be -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc0 ->
    clos_tree (EThunk Γc' (ELam x eb)) kf f -> contains_k σ S ka a ea ->
    h <= n -> eval (Fin n) Φ Γs (EApp f a) v_s ->
    exists k', k' <= K /\ contains_k σ S k' v_s v_c.
Proof.
  intros bk. induction bk as [bk IH] using lt_wf_ind. intros be.
  assert (Hprev : exists h1 K1, forall Φ Γs f a kf ka kenv n v_s,
    kf < bk -> ka <= be -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc0 ->
    clos_tree (EThunk Γc' (ELam x eb)) kf f -> contains_k σ S ka a ea ->
    h1 <= n -> eval (Fin n) Φ Γs (EApp f a) v_s ->
    exists k', k' <= K1 /\ contains_k σ S k' v_s v_c).
  { destruct bk as [| bk'].
    - exists 0, 0. intros. lia.
    - destruct (IH bk' ltac:(lia) be) as [h1 [K1 H1]].
      exists h1, K1. intros Φ0 Γs0 f0 a0 kf0 ka0 ke0 n0 v0 Hkf0 Hka0 Hke0 Hm0 He0 Ht0 Ha0 Hn0 Hev0.
      exact (H1 Φ0 Γs0 f0 a0 kf0 ka0 ke0 n0 v0 ltac:(lia) Hka0 Hke0 Hm0 He0 Ht0 Ha0 Hn0 Hev0). }
  destruct Hprev as [h1 [K1 H1]].
  destruct (Hbody bk (be + be + bk)) as [h0 [K0 H0]].
  exists (2 + bk + h0 + h1), (1 + 2 * bk + K0 + K1).
  intros Φ Γs f a kf ka kenv n v_s Hkf Hka Hkenv Hm Henv Htree Ha Hn Hev.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  destruct n as [| n]; [lia |].
  inversion Htree; subst.
  - match goal with [ Hc : contains_k _ _ _ (EThunk _ (ELam _ _)) _ |- _ ] =>
      destruct (contains_k_clos_inv σ S _ _ _ _ _ Hc)
        as [Γc2 [bodyc [kenv1 [kb [Heq [Hsx [Henv1 [Hb Hkk]]]]]]]] end.
    injection Heq as <- <- <-.
    inversion Hev; subst; try sym_absurd.
    change (dec (Remaining n)) with (Fin n) in *.
    match goal with [ Hv : eval (Fin n) Φ (extend_env _ _ _ _) _ v_s |- _ ] => rename Hv into Hbody_ev end.
    assert (Hext : contains_env_k σ S (kenv + ka + kenv1)
                     (extend_env Γ x Γs a) (extend_env Γc' x Γc0 ea)).
    { unfold extend_env. apply ContK_Env_Extend; assumption. }
    destruct (H0 _ Φ _ _ kb (kenv + ka + kenv1) n v_s eq_refl ltac:(lia) ltac:(lia) Hm Hext Hb
                ltac:(lia) Hbody_ev) as [k' [Hk' Hc']].
    exists k'. split; [lia | exact Hc'].
  - assert (Hu : unspool_app (EApp (EIf g t f0) a) [] = (EIf g t f0, [a])) by reflexivity.
    pose proof (app_if_step σ Φ Γs _ _ _ _ _ _ _ n Hm Hu Hev) as Hev1. simpl in Hev1.
    destruct n as [| n]; [lia |].
    destruct (if_step_true σ S Φ Γs _ _ _ v_s n Hm Hfree ltac:(eassumption) ltac:(lia) Hev1)
      as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
    destruct (H1 _ Γs t a k ka kenv n t' ltac:(lia) Hka Hkenv Hm' Henv ltac:(eassumption) Ha
                ltac:(lia) Ht) as [k' [Hk' Hct]].
    exists (1 + smt_size g' + k'). split; [lia | apply ContK_If_True; assumption].
  - assert (Hu : unspool_app (EApp (EIf g t f0) a) [] = (EIf g t f0, [a])) by reflexivity.
    pose proof (app_if_step σ Φ Γs _ _ _ _ _ _ _ n Hm Hu Hev) as Hev1. simpl in Hev1.
    destruct n as [| n]; [lia |].
    destruct (if_step_false σ S Φ Γs _ _ _ v_s n Hm Hfree ltac:(eassumption) ltac:(lia) Hev1)
      as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
    destruct (H1 _ Γs f0 a k ka kenv n f' ltac:(lia) Hka Hkenv Hm' Henv ltac:(eassumption) Ha
                ltac:(lia) Ht) as [k' [Hk' Hct]].
    exists (1 + smt_size g' + k'). split; [lia | apply ContK_If_False; assumption].
Qed.

Lemma app_abs_core : forall bk be,
  core_at σ S (eq Γc0) (EApp (EThunk Γc' (ELam x eb)) ea) v_c bk be.
Proof.
  intros bk be.
  destruct (clos_value Γc' x eb bk) as [hc [Kc Hc]].
  destruct (app_abs_tree (bk + Kc) (be + bk)) as [hL [KL HL]].
  exists (1 + hc + hL), KL.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try (simpl in Hif; discriminate Hif);
    try (match goal with [ Ht : is_thunk _ = true |- _ ] => simpl in Ht; discriminate Ht end).
  match goal with [ Hf : contains_k _ _ ?kf ?f (EThunk _ _), Ha : contains_k _ _ ?ka ?a ea |- _ ] =>
    rename Hf into Hfc; rename Ha into Hac; rename f into fs; rename a into as_;
    rename kf into kfs; rename ka into kas end.
  destruct fs; try (inversion Hfc; fail); try (simpl in Hif; discriminate Hif).
  inversion Hev; subst; try sym_absurd.
  - exact (HL Φ Γs _ as_ kfs kas kenv (Datatypes.S n) v_s ltac:(lia) ltac:(lia) ltac:(lia) Hm Henv
             (CT_Leaf _ _ _ _ _ Hfc) Hac ltac:(lia) Hev).
  - change (dec (Remaining n)) with (Fin n) in *.
    match goal with
    | [ H1 : eval (Fin n) Φ Γs (EThunk _ _) ?f', H2 : eval (Fin n) Φ Γs (EApp ?f' as_) v_s |- _ ] =>
        destruct (Hc Φ Γs _ kfs n f' ltac:(lia) Hm Hfree Hfc ltac:(lia) H1) as [k' [Hk' Ht']];
        exact (HL Φ Γs f' as_ k' kas kenv n v_s ltac:(lia) ltac:(lia) ltac:(lia) Hm Henv Ht' Hac
                 ltac:(lia) H2)
    end.
Qed.

End AppAbs.

End Closures.
