From SymCoreTheory Require Import SymCore ConCore BranchLaws CostLaws Dev1 Dev2 Dev3 Dev7.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Arith.Wf_nat Lia.
Import ListNotations.

Section SpineCores.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Definition rigid_head (h : expr) : bool :=
  match h with
  | ECon _ | EPrimOp _ => true
  | _ => false
  end.

Lemma contains_k_unspool_rigid_rev : forall k e_s e_c,
  contains_k σ S k e_s e_c ->
  forall kl Ls Lc h args_c,
    Forall3 (contains_k σ S) kl Ls Lc ->
    unspool_app e_c Lc = (h, args_c) ->
    rigid_head h = true ->
    is_if (fst (unspool_app e_s Ls)) = false ->
    exists args_s ks,
      unspool_app e_s Ls = (h, args_s) /\ Forall3 (contains_k σ S) ks args_s args_c /\
      list_sum ks = k + list_sum kl.
Proof.
  induction 1; intros kl Ls Lc h args_c HL Hu Hr Hif; simpl in Hu, Hif |- *;
    try (injection Hu as <- <-; simpl in Hr; discriminate Hr).
  - injection Hu as <- <-. exists Ls, kl. split; [reflexivity | split; [exact HL | reflexivity]].
  - injection Hu as <- <-. exists Ls, kl. split; [reflexivity | split; [exact HL | reflexivity]].
  - destruct (IHcontains_k1 (ka :: kl) (a_s :: Ls) (a_c :: Lc) h args_c
                (Forall3_cons _ _ _ _ _ _ _ H0 HL) Hu Hr Hif) as [args_s [ks [Hus [HF Hs]]]].
    exists args_s, ks. split; [exact Hus | split; [exact HF | simpl in Hs; lia]].
  - destruct ec; simpl in H1; try discriminate H1.
    simpl in Hu. injection Hu as <- <-. simpl in Hr. discriminate Hr.
  - discriminate Hif.
  - discriminate Hif.
Qed.

Lemma find_alt_contains_alt_k_rev : forall ks altss altsc d xs epc,
  Forall3 (contains_alt_k σ S) ks altss altsc ->
  find_alt d altsc = Some (xs, epc) ->
  exists eps kp, find_alt d altss = Some (xs, eps) /\ Forall (fun x => S x = false) xs /\
    contains_k σ S kp eps epc /\ kp <= list_sum ks.
Proof.
  intros ks altss altsc d xs epc HF. revert xs epc.
  induction HF as [| k a_s a_c ks la lc Ha _ IH]; intros xs epc Hf; simpl in Hf; [discriminate |].
  inversion Ha as [k0 d0 xs0 eps epc0 Hxs Hb]; subst. simpl.
  destruct (string_dec d d0).
  - injection Hf as <- <-. exists eps, k. repeat split; try assumption. simpl. lia.
  - destruct (IH xs epc Hf) as [eps' [kp [H1 [H2 [H3 H4]]]]].
    exists eps', kp. repeat split; try assumption. simpl. lia.
Qed.

Lemma extend_env_multi_contains_k : forall xs kΓ ka ks Γs Γc Γas Γac args_s args_c,
  Forall (fun x => S x = false) xs ->
  contains_env_k σ S kΓ Γs Γc ->
  contains_env_k σ S ka Γas Γac ->
  Forall3 (contains_k σ S) ks args_s args_c ->
  Forall concore_expr args_c ->
  exists k', k' <= kΓ + length xs * (ka + list_sum ks) /\
    contains_env_k σ S k' (extend_env_multi Γs xs args_s Γas) (extend_env_multi Γc xs args_c Γac).
Proof.
  induction xs as [| x xs IH]; intros kΓ ka ks Γs Γc Γas Γac args_s args_c Hxs HΓ Ha HF Hcon.
  - exists kΓ. split; [lia | exact HΓ].
  - inversion Hxs as [| x0 xs0 Hx Hxs']; subst.
    destruct HF as [| k a_s a_c ks' l1 l2 Hac HF'].
    + destruct (IH kΓ ka nil Γs Γc Γas Γac nil nil Hxs' HΓ Ha (Forall3_nil _) Hcon) as [k' [Hk' Hc']].
      exists (ka + 0 + k'). split; [simpl in *; nia |].
      simpl. unfold extend_env. apply ContK_Env_Extend;
        [exact Hx | exact Ha | apply ContK_Bot | constructor | exact Hc'].
    + inversion Hcon as [| c0 cs Hc0 Hcs]; subst.
      destruct (IH kΓ ka ks' Γs Γc Γas Γac l1 l2 Hxs' HΓ Ha HF' Hcs) as [k' [Hk' Hc']].
      exists (ka + k + k'). split; [simpl in *; nia |].
      simpl. unfold extend_env. apply ContK_Env_Extend; assumption.
Qed.

Lemma spine_head_rev : forall k f c,
  contains_k σ S k f c ->
  is_if (spine_head f) = false ->
  has_whole_spine_rule (spine_head c) = false ->
  (forall l, spine_head c <> ELit l) ->
  has_whole_spine_rule (spine_head f) = false.
Proof.
  induction 1; intros Hif Hw Hl; simpl in *; try reflexivity; try discriminate.
  - exact (IHcontains_k1 Hif Hw Hl).
  - exfalso. exact (Hl l eq_refl).
Qed.

Lemma comp_k_rev : forall kenv k Γs Γc f c,
  contains_env_k σ S kenv Γs Γc ->
  contains_k σ S k f c ->
  Comp Γc c ->
  is_if (spine_head f) = false ->
  (forall l, spine_head c <> ELit l) ->
  Comp Γs f.
Proof.
  intros kenv k Γs Γc f c Henv Hc Hcomp Hif Hl.
  destruct Hcomp as [x Hbound | x body | es alts | Γ' e Hnotlam | ef ea Hhead].
  - inversion Hc; subst; simpl in Hif; try discriminate Hif;
      try (match goal with [ Ht : is_thunk _ = true |- _ ] => simpl in Ht; discriminate Ht end).
    apply Comp_Var. intros Hnone. apply Hbound.
    exact (contains_env_lookup_none σ S Γs Γc x (contains_env_k_erase _ _ _ _ _ Henv) Hnone).
  - inversion Hc; subst; simpl in Hif; try discriminate Hif;
      try (match goal with [ Ht : is_thunk _ = true |- _ ] => simpl in Ht; discriminate Ht end). apply Comp_Lam.
  - inversion Hc; subst; simpl in Hif; try discriminate Hif;
      try (match goal with [ Ht : is_thunk _ = true |- _ ] => simpl in Ht; discriminate Ht end). apply Comp_Case.
  - inversion Hc; subst; simpl in Hif; try discriminate Hif;
      try (match goal with [ Ht : is_thunk _ = true |- _ ] => simpl in Ht; discriminate Ht end).
    + apply Comp_Thunk.
      match goal with [ Hb : contains_k _ _ _ ?b e |- is_lam ?b = false ] =>
        destruct b; try reflexivity; inversion Hb; subst; simpl in Hnotlam; discriminate end.
    + apply Comp_Thunk.
      match goal with [ Hb : contains_k _ _ _ ?b (EThunk Γ' e) |- is_lam ?b = false ] =>
        destruct b; try reflexivity; inversion Hb end.
  - inversion Hc; subst; simpl in Hif; try discriminate Hif;
      try (match goal with [ Ht : is_thunk _ = true |- _ ] => simpl in Ht; discriminate Ht end).
    apply Comp_App. exact (spine_head_rev _ _ _ Hc Hif Hhead Hl).
Qed.

Lemma eval_spine_head_lit : forall f Φ Γ e v,
  eval f Φ Γ e v -> f = Inf -> Φ = pc_true ->
  forall l, spine_head e = ELit l -> e = ELit l.
Proof.
  intros f Φ Γ e v H. induction H; intros Hf HΦ l0 Hl; try discriminate Hf; subst;
    simpl in Hl; try exact Hl; try discriminate Hl;
    try (rewrite sat_pc_true in *; discriminate).
  - rewrite <- (fst_unspool_app e []) in Hl.
    match goal with [ Hu : unspool_app e [] = _ |- _ ] => rewrite Hu in Hl end.
    discriminate Hl.
  - injection Hf as Hf. subst f.
    specialize (IHeval1 eq_refl eq_refl l0 Hl). subst ef. inversion H.
  - pose proof (fst_unspool_app (EApp ef ea) []) as Hs.
    match goal with [ Hu : unspool_app (EApp ef ea) [] = _ |- _ ] => rewrite Hu in Hs end.
    simpl in Hs. rewrite Hl in Hs. discriminate Hs.
  - pose proof (fst_unspool_app (EApp e1 e2) []) as Hs.
    match goal with [ Hu : unspool_app (EApp e1 e2) [] = _ |- _ ] => rewrite Hu in Hs end.
    simpl in Hs. rewrite Hl in Hs. discriminate Hs.
Qed.

End SpineCores.
