From SymCoreTheory Require Import SymCore ConCore BranchLaws CostLaws Dev1 Dev2 Dev3 Dev7 Dev8.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Arith.Wf_nat Lia.
Import ListNotations.

Section MoreCores.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Lemma good_weaken : forall (A A' : environment -> Prop) e v,
  (forall Γ, A' Γ -> A Γ) -> good σ S A e v -> good σ S A' e v.
Proof.
  intros A A' e v Himp Hg bk be.
  destruct (Hg bk be) as [h [K H]]. exists h, K.
  intros Γc Φ Γs e_s k kenv n v_s HA. exact (H Γc Φ Γs e_s k kenv n v_s (Himp Γc HA)).
Qed.

Lemma thunk_good : forall Γ' e v,
  good σ S (eq Γ') e v -> good σ S (fun _ => True) (EThunk Γ' e) v.
Proof.
  intros Γ' e v Hbody. apply good_at_of_core. intros bk be IH.
  destruct (Hbody bk bk) as [h0 [K0 H0]].
  assert (Hprev : exists h1 K1, forall Γc Φ Γs e_s k kenv n v_s,
    k < bk -> kenv < bk -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k e_s (EThunk Γ' e) ->
    h1 <= n -> eval (Fin n) Φ Γs e_s v_s ->
    exists k', k' <= K1 /\ contains_k σ S k' v_s v).
  { destruct bk as [| bk'].
    - exists 0, 0. intros. lia.
    - destruct (IH bk' ltac:(lia) bk') as [h1 [K1 H1]].
      exists h1, K1. intros Γc0 Φ0 Γs0 e0 k0 ke0 n0 v0 Hk0 Hke0 Hm0 He0 Hc0 Hn0 Hev0.
      exact (H1 Γc0 Φ0 Γs0 e0 k0 ke0 n0 v0 I ltac:(lia) ltac:(lia) Hm0 He0 Hc0 Hn0 Hev0). }
  destruct Hprev as [h1 [K1 H1]].
  exists (1 + h0 + h1), (K0 + K1).
  intros Γc Φ Γs e_s k kenv n v_s _ Hk Hkenv Hm Henv Hcont Hif Hn Hev.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  - inversion Hev; subst; try sym_absurd.
    change (dec (Remaining n)) with (Fin n) in *.
    match goal with
    | [ He : contains_env_k _ _ ?ke ?G Γ', Hb : contains_k _ _ ?kb ?b e,
        Hv : eval (Fin n) Φ ?G ?b v_s |- _ ] =>
        destruct (H0 Γ' Φ G b kb ke n v_s eq_refl ltac:(lia) ltac:(lia) Hm He Hb ltac:(lia) Hv)
          as [k' [Hk' Hc']]
    end.
    exists k'. split; [lia | exact Hc'].
  - inversion Hev; subst; try sym_absurd.
    change (dec (Remaining n)) with (Fin n) in *.
    match goal with
    | [ He : contains_env_k _ _ ?ke ?G ?Gc, Hb : contains_k _ _ ?kb ?b (EThunk Γ' e),
        Hv : eval (Fin n) Φ ?G ?b v_s |- _ ] =>
        destruct (H1 Gc Φ G b kb ke n v_s ltac:(lia) ltac:(lia) Hm He Hb ltac:(lia) Hv)
          as [k' [Hk' Hc']]
    end.
    exists k'. split; [lia | exact Hc'].
Qed.

Lemma con_core : forall Γc0 e_c d args_c bk be,
  unspool_app e_c [] = (ECon d, args_c) ->
  core_at σ S (eq Γc0) e_c (make_con_app d (map (delay Γc0) args_c)) bk be.
Proof.
  intros Γc0 e_c d args_c bk be Hu.
  exists 1, (length args_c * (1 + be) + bk).
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  destruct (contains_k_unspool_rigid_rev σ S k e_s e_c Hcont nil nil nil (ECon d) args_c
              (Forall3_nil _) Hu eq_refl Hif) as [args_s [ks [Hus [HF Hs]]]].
  simpl in Hs.
  assert (Hv : v_s = make_con_app d (map (delay Γs) args_s)).
  { inversion Hev; subst; sym_absurd. }
  subst v_s.
  destruct (delay_map_contains_k σ S kenv Γs Γc0 ks args_s args_c Henv HF) as [ks' [Hks' HF']].
  exists (0 + list_sum ks'). split.
  - pose proof (forall3_length_left_right _ _ _ _ _ _ _ HF) as Hlen. rewrite <- Hlen. nia.
  - unfold make_con_app. exact (contains_k_fold_left_app σ S ks' _ _ 0 _ _ HF' (ContK_Con σ S d)).
Qed.

Lemma args_good : forall Γc0 args_c args_c',
  Forall2 (fun a a' => good σ S (eq Γc0) a a') args_c args_c' ->
  forall bk be, exists h K, forall Φ Γs ks args_s args_s' kenv n,
    list_sum ks <= bk -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc0 ->
    Forall3 (contains_k σ S) ks args_s args_c ->
    h <= n -> Forall2 (eval (Fin n) Φ Γs) args_s args_s' ->
    exists ks', Forall3 (contains_k σ S) ks' args_s' args_c' /\ list_sum ks' <= K.
Proof.
  intros Γc0 args_c args_c' HG bk be.
  induction HG as [| a a' l l' Ha _ IH].
  - exists 0, 0. intros Φ Γs ks args_s args_s' kenv n _ _ _ _ HF _ HE.
    inversion HF; subst. inversion HE; subst. exists nil. split; [constructor | simpl; lia].
  - destruct IH as [h1 [K1 H1]]. destruct (Ha bk be) as [h0 [K0 H0]].
    exists (h0 + h1), (K0 + K1).
    intros Φ Γs ks args_s args_s' kenv n Hks Hkenv Hm Henv HF Hn HE.
    inversion HF as [| k0 as0 ac0 ks0 las lac Hc0 HF0]; subst.
    inversion HE as [| x x' lx lx' Hx HE0]; subst.
    simpl in Hks.
    destruct (H0 Γc0 Φ Γs as0 k0 kenv n x' eq_refl ltac:(lia) Hkenv Hm Henv Hc0 ltac:(lia) Hx)
      as [k' [Hk' Hc']].
    destruct (H1 Φ Γs ks0 las lx' kenv n ltac:(lia) Hkenv Hm Henv HF0 ltac:(lia) HE0)
      as [ks' [HF' Hks']].
    exists (k' :: ks'). split; [constructor; assumption | simpl; lia].
Qed.

Lemma app_prim_core : forall Γc0 c1 c2 p args_c args_c' bk be,
  unspool_app (EApp c1 c2) [] = (EPrimOp p, args_c) ->
  Forall2 (fun a a' => good σ S (eq Γc0) a a') args_c args_c' ->
  core_at σ S (eq Γc0) (EApp c1 c2) (reduce_prim p args_c') bk be.
Proof.
  intros Γc0 c1 c2 p args_c args_c' bk be Hu HG.
  destruct (args_good Γc0 args_c args_c' HG bk be) as [h0 [K0 H0]].
  exists (1 + h0), (K0 + prim_slack args_c').
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  destruct (contains_k_unspool_rigid_rev σ S k e_s _ Hcont nil nil nil (EPrimOp p) args_c
              (Forall3_nil _) Hu eq_refl Hif) as [args_s [ks [Hus [HF Hs]]]].
  simpl in Hs.
  inversion Hev; subst; try sym_absurd.
  change (dec (Remaining n)) with (Fin n) in *.
  match goal with [ H2 : unspool_app _ [] = (EPrimOp _, _), HE : Forall2 _ _ ?a' |- _ ] =>
    rewrite Hus in H2; injection H2 as <- <-;
    destruct (H0 Φ Γs ks args_s a' kenv n ltac:(lia) Hkenv Hm Henv HF ltac:(lia) HE)
      as [ks' [HF' Hks']]
  end.
  destruct (reduce_prim_contains_k σ S p ks' _ args_c' HF') as [k' [Hk' Hc']].
  exists k'. split; [lia | exact Hc'].
Qed.

Lemma app_spine_core : forall Γc0 c1 c2 c1' v bk be,
  Comp Γc0 c1 ->
  (forall l, spine_head c1 <> ELit l) ->
  good σ S (eq Γc0) c1 c1' ->
  good σ S (eq Γc0) (EApp c1' c2) v ->
  core_at σ S (eq Γc0) (EApp c1 c2) v bk be.
Proof.
  intros Γc0 c1 c2 c1' v bk be Hcomp Hl IH1 IH2.
  destruct (IH1 bk be) as [h1 [K1 H1]].
  destruct (IH2 (K1 + bk) be) as [h2 [K2 H2]].
  exists (1 + h1 + h2), K2.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  match goal with [ Hf : contains_k _ _ ?kf ?f c1, Ha : contains_k _ _ ?ka ?a c2 |- _ ] =>
    rename Hf into Hfc; rename Ha into Hac; rename f into fs; rename a into as_;
    rename kf into kfs; rename ka into kas end.
  assert (Hif' : is_if (spine_head fs) = false).
  { rewrite (fst_unspool_app _ []) in Hif. simpl in Hif. exact Hif. }
  pose proof (comp_k_rev σ S kenv kfs Γs Γc0 fs c1 Henv Hfc Hcomp Hif' Hl) as Hcs.
  inversion Hev; subst; try sym_absurd.
  change (dec (Remaining n)) with (Fin n) in *.
  match goal with
  | [ Hv1 : eval (Fin n) Φ Γs fs ?f', Hv2 : eval (Fin n) Φ Γs (EApp ?f' as_) v_s |- _ ] =>
      destruct (H1 Γc0 Φ Γs fs kfs kenv n f' eq_refl ltac:(lia) Hkenv Hm Henv Hfc ltac:(lia) Hv1)
        as [k' [Hk' Hc']];
      exact (H2 Γc0 Φ Γs (EApp f' as_) (k' + kas) kenv n v_s eq_refl ltac:(lia) Hkenv Hm Henv
               (ContK_App _ _ _ _ _ _ _ _ Hc' Hac) ltac:(lia) Hv2)
  end.
Qed.

End MoreCores.
