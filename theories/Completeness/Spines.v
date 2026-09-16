From SymCoreTheory Require Export Completeness.Closures.
From Stdlib Require Import Bool.Bool Arith.Wf_nat Strings.String Lists.List Lia Arith.PeanoNat.
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

Section MoreCores.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Lemma good_weaken : forall (A A' : environment -> Prop) e v,
  (forall Γ, A' Γ -> A Γ) -> good σ S A e v -> good σ S A' e v.
Proof.
  intros A A' e v Himp Hg bk be bs.
  destruct (Hg bk be bs) as [h [K H]]. exists h, K.
  intros Γc Φ Γs e_s k kenv n v_s HA. exact (H Γc Φ Γs e_s k kenv n v_s (Himp Γc HA)).
Qed.

Lemma thunk_good : forall Γ' e v,
  good σ S (eq Γ') e v -> good σ S (fun _ => True) (EThunk Γ' e) v.
Proof.
  intros Γ' e v Hbody. apply good_at_of_core. intros bk be bs IH.
  destruct (Hbody bk bk bs) as [h0 [K0 H0]].
  assert (Hprev : exists h1 K1, forall Γc Φ Γs e_s k kenv n v_s,
    k < bk -> kenv < bk -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k e_s (EThunk Γ' e) ->
    sym_ok S bs Φ (SEval Γs e_s) ->
    h1 <= n -> eval (Fin n) Φ Γs e_s v_s ->
    exists k', k' <= K1 /\ contains_k σ S k' v_s v).
  { destruct bk as [| bk'].
    - exists 0, 0. intros. lia.
    - destruct (IH bk' ltac:(lia) bk' bs) as [h1 [K1 H1]].
      exists h1, K1. intros Γc0 Φ0 Γs0 e0 k0 ke0 n0 v0 Hk0 Hke0 Hm0 He0 Hc0 Hok0 Hn0 Hev0.
      exact (H1 Γc0 Φ0 Γs0 e0 k0 ke0 n0 v0 I ltac:(lia) ltac:(lia) Hm0 He0 Hc0 Hok0 Hn0 Hev0). }
  destruct Hprev as [h1 [K1 H1]].
  exists (1 + h0 + h1), (K0 + K1).
  intros Γc Φ Γs e_s k kenv n v_s _ Hk Hkenv Hm Henv Hcont Hok Hif Hn Hev.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  - inversion Hev; subst; try sym_absurd.
    change (dec (Remaining n)) with (Fin n) in *.
    match goal with
    | [ He : contains_env_k _ _ ?ke ?G Γ', Hb : contains_k _ _ ?kb ?b e,
        Hv : eval (Fin n) Φ ?G ?b v_s |- _ ] =>
        destruct (H0 Γ' Φ G b kb ke n v_s eq_refl ltac:(lia) ltac:(lia) Hm He Hb
                    (sym_ok_step S bs Φ _ _ _ Hok (SymStep_Thunk Φ Γs G b)) ltac:(lia) Hv)
          as [k' [Hk' Hc']]
    end.
    exists k'. split; [lia | exact Hc'].
  - inversion Hev; subst; try sym_absurd.
    change (dec (Remaining n)) with (Fin n) in *.
    match goal with
    | [ He : contains_env_k _ _ ?ke ?G ?Gc, Hb : contains_k _ _ ?kb ?b (EThunk Γ' e),
        Hv : eval (Fin n) Φ ?G ?b v_s |- _ ] =>
        destruct (H1 Gc Φ G b kb ke n v_s ltac:(lia) ltac:(lia) Hm He Hb
                    (sym_ok_step S bs Φ _ _ _ Hok (SymStep_Thunk Φ Γs G b)) ltac:(lia) Hv)
          as [k' [Hk' Hc']]
    end.
    exists k'. split; [lia | exact Hc'].
Qed.

Lemma con_core : forall Γc0 e_c d args_c bk be bs,
  unspool_app e_c [] = (ECon d, args_c) ->
  core_at σ S (eq Γc0) e_c (make_con_app d (map (delay Γc0) args_c)) bk be bs.
Proof.
  intros Γc0 e_c d args_c bk be bs Hu.
  exists 1, (length args_c * (1 + be) + bk).
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hok Hif Hn Hev. subst Γc.
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
  forall bk be bs, exists h K, forall Φ Γs ks args_s args_s' kenv n,
    list_sum ks <= bk -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc0 ->
    Forall3 (contains_k σ S) ks args_s args_c ->
    Forall (fun a => sym_ok S bs Φ (SEval Γs a)) args_s ->
    h <= n -> Forall2 (eval (Fin n) Φ Γs) args_s args_s' ->
    exists ks', Forall3 (contains_k σ S) ks' args_s' args_c' /\ list_sum ks' <= K.
Proof.
  intros Γc0 args_c args_c' HG bk be bs.
  induction HG as [| a a' l l' Ha _ IH].
  - exists 0, 0. intros Φ Γs ks args_s args_s' kenv n _ _ _ _ HF _ _ HE.
    inversion HF; subst. inversion HE; subst. exists nil. split; [constructor | simpl; lia].
  - destruct IH as [h1 [K1 H1]]. destruct (Ha bk be bs) as [h0 [K0 H0]].
    exists (h0 + h1), (K0 + K1).
    intros Φ Γs ks args_s args_s' kenv n Hks Hkenv Hm Henv HF Hok Hn HE.
    inversion HF as [| k0 as0 ac0 ks0 las lac Hc0 HF0]; subst.
    inversion HE as [| x x' lx lx' Hx HE0]; subst.
    inversion Hok as [| a1 l1 Hok0 Hok1]; subst.
    simpl in Hks.
    destruct (H0 Γc0 Φ Γs as0 k0 kenv n x' eq_refl ltac:(lia) Hkenv Hm Henv Hc0 Hok0 ltac:(lia) Hx)
      as [k' [Hk' Hc']].
    destruct (H1 Φ Γs ks0 las lx' kenv n ltac:(lia) Hkenv Hm Henv HF0 Hok1 ltac:(lia) HE0)
      as [ks' [HF' Hks']].
    exists (k' :: ks'). split; [constructor; assumption | simpl; lia].
Qed.

Lemma app_prim_core : forall Γc0 c1 c2 p args_c args_c' bk be bs,
  unspool_app (EApp c1 c2) [] = (EPrimOp p, args_c) ->
  Forall closed_term args_c' ->
  Forall2 (fun a a' => good σ S (eq Γc0) a a') args_c args_c' ->
  core_at σ S (eq Γc0) (EApp c1 c2) (reduce_prim p args_c') bk be bs.
Proof.
  intros Γc0 c1 c2 p args_c args_c' bk be bs Hu Hcl HG.
  destruct (args_good Γc0 args_c args_c' HG bk be bs) as [h0 [K0 H0]].
  exists (1 + h0), (K0 + prim_slack args_c').
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hok Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  destruct (contains_k_unspool_rigid_rev σ S k e_s _ Hcont nil nil nil (EPrimOp p) args_c
              (Forall3_nil _) Hu eq_refl Hif) as [args_s [ks [Hus [HF Hs]]]].
  simpl in Hs.
  assert (Hoka : Forall (fun a => sym_ok S bs Φ (SEval Γs a)) args_s).
  { apply Forall_forall. intros a Hin.
    exact (sym_ok_step S bs Φ _ _ _ Hok (SymStep_AppArg Φ Γs e_s (EPrimOp p) args_s a Hus Hin)). }
  inversion Hev; subst; try sym_absurd.
  change (dec (Remaining n)) with (Fin n) in *.
  match goal with [ H2 : unspool_app _ [] = (EPrimOp _, _), HE : Forall2 _ _ ?a' |- _ ] =>
    rewrite Hus in H2; injection H2 as <- <-;
    destruct (H0 Φ Γs ks args_s a' kenv n ltac:(lia) Hkenv Hm Henv HF Hoka ltac:(lia) HE)
      as [ks' [HF' Hks']]
  end.
  destruct (reduce_prim_contains_k σ S p ks' _ args_c' Hcl HF') as [k' [Hk' Hc']].
  exists k'. split; [lia | exact Hc'].
Qed.

Lemma app_spine_core : forall Γc0 c1 c2 c1' v bk be bs,
  Comp Γc0 c1 ->
  (forall l, spine_head c1 <> ELit l) ->
  good σ S (eq Γc0) c1 c1' ->
  good σ S (eq Γc0) (EApp c1' c2) v ->
  core_at σ S (eq Γc0) (EApp c1 c2) v bk be bs.
Proof.
  intros Γc0 c1 c2 c1' v bk be bs Hcomp Hl IH1 IH2.
  destruct (IH1 bk be bs) as [h1 [K1 H1]].
  destruct (IH2 (K1 + bk) be bs) as [h2 [K2 H2]].
  exists (1 + h1 + h2), K2.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hok Hif Hn Hev. subst Γc.
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
      destruct (H1 Γc0 Φ Γs fs kfs kenv n f' eq_refl ltac:(lia) Hkenv Hm Henv Hfc
                  (sym_ok_step S bs Φ _ _ _ Hok (SymStep_AppFun Φ Γs fs as_)) ltac:(lia) Hv1)
        as [k' [Hk' Hc']];
      exact (H2 Γc0 Φ Γs (EApp f' as_) (k' + kas) kenv n v_s eq_refl ltac:(lia) Hkenv Hm Henv
               (ContK_App _ _ _ _ _ _ _ _ Hc' Hac)
               (sym_ok_step S bs Φ _ _ _ Hok (SymStep_AppValue Φ Γs fs as_ f' n Hv1))
               ltac:(lia) Hv2)
  end.
Qed.

End MoreCores.
