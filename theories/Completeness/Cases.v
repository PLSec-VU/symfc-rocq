From SymCoreTheory Require Export Completeness.Spines.
From Stdlib Require Import Bool.Bool Arith.Wf_nat Strings.String Lists.List Lia Arith.PeanoNat.
Import ListNotations.

Section CaseCores.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Lemma denote_reads_formula : forall e l, denote σ S e l -> exists pc, expr_to_pc · e = Some pc.
Proof. intros e l [pc [Hd _]]. exists pc. exact (Hd · (sym_free_env_empty S)). Qed.

Lemma fold_alts_formula_shape : forall f Φ Γ m alts r pc,
  expr_to_pc Γ m = Some pc ->
  fold_alts f Φ Γ m alts r ->
  pc_arities_ok pc = true \/ pc_has_var pc = false.
Proof.
  intros f Φ Γ m alts r pc Hpc Hfold.
  inversion Hfold; subst; simpl in Hpc; try discriminate Hpc.
  - match goal with [ Hd : decompose_con_app m = Some (?d, ?ea) |- _ ] =>
      rewrite (con_app_expr_to_pc_none Γ m
                 (unspool_is_con_app m [] d ea (decompose_con_app_unspool m d ea Hd))) in Hpc end.
    discriminate Hpc.
  - match goal with [ Hp : expr_to_pc Γ m = Some ?pc0, Hv : pc_has_var ?pc0 = false |- _ ] =>
      rewrite Hp in Hpc; injection Hpc as <-; right; exact Hv end.
  - match goal with [ Hp : expr_to_pc Γ m = Some ?pc0, Ha : pc_arities_ok ?pc0 = true |- _ ] =>
      rewrite Hp in Hpc; injection Hpc as <-; left; exact Ha end.
  - match goal with [ Hp : expr_to_pc Γ m = None |- _ ] => rewrite Hp in Hpc; discriminate Hpc end.
Qed.

Lemma fold_alts_op_app_formula : forall f Φ Γ m alts r,
  is_op_app m = true -> fold_alts f Φ Γ m alts r -> exists pc, expr_to_pc Γ m = Some pc.
Proof.
  intros f Φ Γ m alts r Hop Hfold.
  inversion Hfold; subst; simpl in Hop; try discriminate Hop;
    try (eexists; eassumption); try congruence.
  match goal with [ Hd : decompose_con_app m = Some (?d, ?ea) |- _ ] =>
    pose proof (unspool_is_con_app m [] d ea (decompose_con_app_unspool m d ea Hd)) as Hcon end.
  rewrite (op_app_not_con_app m Hop) in Hcon. discriminate Hcon.
Qed.

Lemma merge_keeps_k_formula_denote : forall Γs k m esc pc,
  sym_scoped S nil m ->
  merge_keeps_k σ S k m esc ->
  expr_to_pc Γs m = Some pc ->
  (pc_arities_ok pc = true \/ pc_has_var pc = false) ->
  denote σ S esc (pc_value σ pc).
Proof.
  intros Γs k m esc pc Hsc Hmk Hpc Har.
  pose proof (sym_scoped_expr_to_pc_denotes S Γs m pc Hsc Hpc) as Hden.
  destruct Hmk as [[k' [_ Hc]] | [Hsmt | [Hcm Hce]]].
  - exact (solvable_term_reads_its_value σ S m esc pc (contains_k_erase _ _ _ _ _ Hc) Hden Har).
  - destruct Hsmt as [ec [et [ef [Hm [_ [_ [_ [_ [_ Hd]]]]]]]]].
    exact (Hd pc Hden Har).
  - exfalso. destruct m; simpl in Hcm; try discriminate Hcm. simpl in Hpc. discriminate Hpc.
Qed.

Lemma fold_alts_scrutinee_denote : forall Γs f Φ k m esc altss r pc,
  sym_scoped S nil m ->
  merge_keeps_k σ S k m esc ->
  expr_to_pc Γs m = Some pc ->
  fold_alts f Φ Γs m altss r ->
  denote σ S esc (pc_value σ pc).
Proof.
  intros Γs f Φ k m esc altss r pc Hsc Hmk Hpc Hfold.
  exact (merge_keeps_k_formula_denote Γs k m esc pc Hsc Hmk Hpc
           (fold_alts_formula_shape f Φ Γs m altss r pc Hpc Hfold)).
Qed.

Lemma contains_k_is_op_app_rev : forall k m esc,
  contains_k σ S k m esc -> is_op_app esc = true ->
  is_if (fst (unspool_app m [])) = false -> is_op_app m = true.
Proof.
  intros k m esc Hc. induction Hc; intros Hop Hif; simpl in Hop; try discriminate Hop.
  - reflexivity.
  - assert (Hif' : is_if (fst (unspool_app f_s [])) = false).
    { rewrite fst_unspool_app. rewrite fst_unspool_app in Hif. simpl in Hif. exact Hif. }
    simpl. exact (IHHc1 Hop Hif').
  - match goal with [ Ht : is_thunk ?x = true |- _ ] =>
      destruct x; simpl in Ht, Hop; try discriminate end.
  - simpl in Hif. discriminate Hif.
  - simpl in Hif. discriminate Hif.
Qed.

Lemma contains_k_formula_not_op : forall Γs k m esc,
  contains_k σ S k m esc ->
  sym_free_env S Γs ->
  closed_term esc -> Solvable · esc ->
  is_if (fst (unspool_app m [])) = false ->
  is_op_app m = false ->
  exists pc, expr_to_pc Γs m = Some pc.
Proof.
  intros Γs k m esc Hc Hfree Hcl Hsolv Hif Hop.
  destruct Hc as
    [ y Hy | y Hy | l | p | d | γ | τ | b
    | kf ka fs as_ fc ac Hf Ha
    | k0 y bs0 bc Hy Hb
    | ke k0 G1 G2 es0 ec0 He0 Hc0
    | ke k0 G1 G2 es0 ec0 He0 Hc0 Ht0
    | k0 es0 ec0 γ Hc0
    | k0 ks0 es0 ec0 as0 ac0 Hc0 Ha0
    | k0 ec0 et0 ef0 etc0 Hm0 Ht0
    | k0 ec0 et0 ef0 efc0 Hm0 Hf0
    | es0 p args l Hun Har Hg Hd ];
    try (exfalso; inversion Hsolv; fail).
  - exfalso. inversion Hcl as [L0 x0 Hin | | | | | | | | | | | |]; subst. exact Hin.
  - simpl. rewrite (Hfree y Hy). eexists. reflexivity.
  - simpl. eexists. reflexivity.
  - simpl in Hop. discriminate Hop.
  - exfalso. inversion Hsolv as [| | | fc0 ac0 Hopc Hsf Hsa]; subst.
    simpl in Hop, Hopc.
    assert (Hif' : is_if (fst (unspool_app fs [])) = false).
    { rewrite fst_unspool_app. rewrite fst_unspool_app in Hif. simpl in Hif. exact Hif. }
    rewrite (contains_k_is_op_app_rev kf fs fc Hf Hopc Hif') in Hop. discriminate Hop.
  - exfalso. destruct ec0; simpl in Ht0; try discriminate Ht0. inversion Hsolv.
  - exfalso. simpl in Hif. discriminate Hif.
  - exfalso. simpl in Hif. discriminate Hif.
  - exfalso. rewrite (unspool_is_op_app es0 [] p args Hun) in Hop. discriminate Hop.
Qed.

Lemma merge_keeps_k_no_formula : forall Γs k m esc,
  sym_free_env S Γs -> sym_scoped S nil m ->
  merge_keeps_k σ S k m esc ->
  expr_to_pc Γs m = None ->
  (exists k', k' <= (1 + field_count esc) * k /\ contains_k σ S k' m esc)
  \/ (is_cast m = true /\ is_cast esc = true).
Proof.
  intros Γs k m esc Hfree Hsc Hmk Hnone.
  destruct Hmk as [Hc | [Hsmt | Hcast]]; [left; exact Hc | exfalso | right; exact Hcast].
  destruct (solvable_expr_to_pc · m
              (smt_ite_kept_solvable σ S m esc (smt_ite_kept_k_erase _ _ _ _ _ Hsmt))) as [pc Hpc].
  rewrite (sym_scoped_nil_expr_to_pc S Γs m pc Hsc Hfree Hpc) in Hnone. discriminate Hnone.
Qed.

Lemma case_core : forall Γc0 esc altsc esc' v bk be bs,
  good σ S (eq Γc0) esc esc' ->
  fgood σ S (eq Γc0) esc' altsc v ->
  core_at σ S (eq Γc0) (ECase esc altsc) v bk be bs.
Proof.
  intros Γc0 esc altsc esc' v bk be bs IH1 IHF.
  destruct (IH1 bk be bs) as [h1 [K1 H1]].
  destruct (IHF K1 (be + bk) bs bs) as [hF [KF HF]].
  exists (1 + h1 + hF), KF.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hok Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst; try sym_absurd.
  change (dec (Remaining n)) with (Fin n) in *.
  match goal with
  | [ Hc : contains_k _ _ ?k1 ?ess esc, Ha : Forall3 _ ?ks ?altss altsc,
      Hv : eval (Fin n) Φ Γs ?ess ?ess', Hf : fold_alts (Fin n) Φ Γs (merge Γs ?ess') ?altss v_s |- _ ] =>
      pose proof (sym_ok_step S bs Φ _ _ _ Hok (SymStep_CaseScrut Φ Γs ess altss)) as Hoks;
      destruct (sym_ok_scoped S bs Φ (SEval Γs ess) Hoks) as [HΓs Hsces];
      destruct (H1 Γc0 Φ Γs ess k1 kenv n ess' eq_refl ltac:(lia) Hkenv Hm Henv Hc Hoks
                  ltac:(lia) Hv) as [kv [Hkv Hcv]];
      pose proof (merge_contains_k σ S Γs kv ess' esc'
                    (sym_eval_scoped_fix _ _ _ _ _ Hv S HΓs Hsces) Hcv) as Hmk;
      pose proof (sym_ok_value_bound S bs Φ Γs ess n ess' Hoks Hv) as Hsz;
      pose proof (sym_ok_step S bs Φ _ _ _ Hok (SymStep_CaseFold Φ Γs ess altss ess' n Hv))
        as Hokf;
      rename Ha into Has; rename Hf into Hfs; rename ks into ksz
  end.
  refine (HF Γc0 Φ Γs _ _ kv ksz kenv n v_s eq_refl Hkv _ _ Hm Henv Hmk Has Hsz Hokf _ Hfs);
    lia.
Qed.

Lemma fcon_core : forall Γc0 esc d ea_c xs epc altsc v bk be bs bm,
  decompose_con_app esc = Some (d, ea_c) ->
  find_alt d altsc = Some (xs, epc) ->
  Forall concore_expr ea_c ->
  good σ S (eq (extend_env_multi Γc0 xs ea_c Γc0)) epc v ->
  fcore_at σ S (eq Γc0) esc altsc v bk be bs bm.
Proof.
  intros Γc0 esc d ea_c xs epc altsc v bk be bs bm Hd Hf Hcon IH.
  destruct (IH be (be + length xs * (be + (1 + field_count esc) * bk)) bs) as [h0 [K0 H0]].
  exists h0, K0.
  intros Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv Hmk Halts Hszm Hok Hif Hn Hev.
  subst Γc.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  destruct (sym_ok_scoped S bs Φ (SFold Γs m altss) Hok) as [HΓs [Hscm Hscalts]].
  assert (Hpcn : expr_to_pc Γs m = None).
  { destruct (expr_to_pc Γs m) as [pc |] eqn:E; [exfalso | reflexivity].
    destruct (denote_reads_formula esc (pc_value σ pc)
                (fold_alts_scrutinee_denote Γs (Fin n) Φ k m esc altss v_s pc Hscm Hmk E Hev))
      as [pcc Hpcc].
    rewrite (con_app_expr_to_pc_none · esc
               (unspool_is_con_app esc [] d ea_c (decompose_con_app_unspool esc d ea_c Hd)))
      in Hpcc.
    discriminate Hpcc. }
  destruct (merge_keeps_k_no_formula Γs k m esc Hfree Hscm Hmk Hpcn)
    as [[kc [Hkc Hcont]] | [Hcm Hce]].
  2: { exfalso. destruct esc; simpl in Hce; try discriminate Hce. simpl in Hd. discriminate Hd. }
  destruct (contains_k_unspool_rigid_rev σ S kc m esc Hcont nil nil nil (ECon d) ea_c
              (Forall3_nil _) (decompose_con_app_unspool esc d ea_c Hd) eq_refl Hif)
    as [args_s [ks' [Hus [HF Hs]]]].
  simpl in Hs.
  destruct (find_alt_contains_alt_k_rev σ S ks altss altsc d xs epc Halts Hf)
    as [eps [kp [Hfs [Hxs [Hep Hkp]]]]].
  destruct (extend_env_multi_contains_k σ S xs kenv kenv ks' Γs Γc0 Γs Γc0 args_s ea_c
              Hxs Henv Henv HF Hcon) as [k' [Hk' Henv']].
  assert (Hds : decompose_con_app m = Some (d, args_s))
    by (unfold decompose_con_app; rewrite Hus; reflexivity).
  pose proof (sym_ok_step S bs Φ _ _ _ Hok
                (SymStep_FoldCon Φ Γs m altss d args_s xs eps Hds Hfs)) as Hokc.
  inversion Hev; subst.
  - simpl in Hif. discriminate Hif.
  - simpl in Hif. discriminate Hif.
  - match goal with
    | [ Hd' : decompose_con_app m = Some _, Hf' : find_alt _ altss = Some _,
        Hv : eval (Fin n) Φ _ _ v_s |- _ ] =>
        rewrite Hds in Hd'; injection Hd' as <- <-;
        rewrite Hfs in Hf'; injection Hf' as <- <-;
        rename Hv into Hvv
    end.
    assert (Hksum : list_sum ks' <= (1 + field_count esc) * bk) by nia.
    exact (H0 _ Φ _ eps kp k' n v_s eq_refl ltac:(lia) ltac:(nia) Hm Henv' Hep Hokc
             ltac:(lia) Hvv).
  - unfold decompose_con_app in Hds. simpl in Hds. discriminate Hds.
  - congruence.
  - congruence.
  - match goal with [ Hmatch : match decompose_con_app m with _ => _ end |- _ ] =>
      rewrite Hds in Hmatch; congruence end.
Qed.

Lemma fbot_core : forall Γc0 b altsc bk be bs bm,
  fcore_at σ S (eq Γc0) (EBot b) altsc (EBot b) bk be bs bm.
Proof.
  intros Γc0 b altsc bk be bs bm.
  exists 0, 0.
  intros Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv Hmk Halts Hszm Hok Hif Hn Hev.
  subst Γc.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  destruct (sym_ok_scoped S bs Φ (SFold Γs m altss) Hok) as [HΓs [Hscm Hscalts]].
  assert (Hpcn : expr_to_pc Γs m = None).
  { destruct (expr_to_pc Γs m) as [pc |] eqn:E; [exfalso | reflexivity].
    destruct (denote_reads_formula (EBot b) (pc_value σ pc)
                (fold_alts_scrutinee_denote Γs (Fin n) Φ k m (EBot b) altss v_s pc Hscm Hmk E Hev))
      as [pcc Hpcc].
    simpl in Hpcc. discriminate Hpcc. }
  destruct (merge_keeps_k_no_formula Γs k m (EBot b) Hfree Hscm Hmk Hpcn)
    as [[kc [Hkc Hcont]] | [Hcm Hce]].
  2: { simpl in Hce. discriminate Hce. }
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst.
  - match goal with [ Hd : decompose_con_app _ = Some _ |- _ ] =>
      unfold decompose_con_app in Hd; simpl in Hd; discriminate Hd end.
  - exists 0. split; [lia | apply ContK_Bot].
  - match goal with [ Hp : expr_to_pc _ _ = Some _ |- _ ] => simpl in Hp; discriminate Hp end.
  - match goal with [ Hp : expr_to_pc _ _ = Some _ |- _ ] => simpl in Hp; discriminate Hp end.
  - match goal with [ Hb : is_bot _ = false |- _ ] => simpl in Hb; discriminate Hb end.
Qed.

Lemma fotherwise_core : forall Γc0 esc altsc bk be bs bm,
  expr_to_pc Γc0 esc = None ->
  is_op_app esc = false ->
  closed_term esc ->
  (match decompose_con_app esc with
   | Some (d, _) => find_alt d altsc = None
   | None => True
   end) ->
  is_bot esc = false ->
  fcore_at σ S (eq Γc0) esc altsc (EBot BUndefined) bk be bs bm.
Proof.
  intros Γc0 esc altsc bk be bs bm Hpcc Hopc Hclc Hmatch Hbot.
  exists 0, 0.
  intros Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv Hmk Halts Hszm Hok Hif Hn Hev.
  subst Γc.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  destruct (sym_ok_scoped S bs Φ (SFold Γs m altss) Hok) as [HΓs [Hscm Hscalts]].
  assert (Hpcn : expr_to_pc Γs m = None).
  { destruct (expr_to_pc Γs m) as [pc |] eqn:E; [exfalso | reflexivity].
    destruct (denote_reads_formula esc (pc_value σ pc)
                (fold_alts_scrutinee_denote Γs (Fin n) Φ k m esc altss v_s pc Hscm Hmk E Hev))
      as [pc2 Hpc2].
    destruct esc; simpl in Hpc2; try discriminate Hpc2.
    - inversion Hclc as [L0 x0 Hin | | | | | | | | | | | |]; subst. exact Hin.
    - simpl in Hpcc. discriminate Hpcc.
    - simpl in Hopc. discriminate Hopc.
    - destruct (expr_to_pc · esc1) as [q1 |] eqn:E1; [| discriminate Hpc2].
      destruct q1 as [ | | q qs]; try (destruct (expr_to_pc · esc2); discriminate Hpc2).
      simpl in Hopc.
      rewrite (expr_to_pc_prim_is_op_app · esc1 q qs E1) in Hopc. discriminate Hopc. }
  destruct (merge_keeps_k_no_formula Γs k m esc Hfree Hscm Hmk Hpcn)
    as [[kc [Hkc Hcont]] | [Hcm Hce]].
  2: { rewrite (fold_alts_cast_undefined (Fin n) Φ Γs m altss v_s Hcm Hev).
       exists 0. split; [lia | apply ContK_Bot]. }
  inversion Hev; subst.
  - simpl in Hif. discriminate Hif.
  - simpl in Hif. discriminate Hif.
  - exfalso.
    match goal with
    | [ Hd : decompose_con_app m = Some (?dd, ?ea), Hfa : find_alt ?dd altss = Some (?xs, ?ep) |- _ ] =>
        destruct (contains_k_unspool_con σ S kc m esc Hcont nil nil nil (Forall3_nil _) dd ea
                    (decompose_con_app_unspool m dd ea Hd)) as [args_c [ks' [Huc _]]];
        assert (Hdc : decompose_con_app esc = Some (dd, args_c))
          by (unfold decompose_con_app; simpl in Huc; rewrite Huc; reflexivity);
        rewrite Hdc in Hmatch;
        destruct (find_alt_contains_alt σ S altss altsc dd xs ep
                    (contains_alts_k_erase σ S ks altss altsc Halts) Hfa) as [epc [Hfc _]];
        congruence
    end.
  - exfalso. inversion Hcont; subst; try cont_absurd Hif. simpl in Hbot. discriminate Hbot.
  - congruence.
  - congruence.
  - exists 0. split; [lia | apply ContK_Bot].
Qed.

Lemma fground_core : forall Γc0 esc pcc altsc v bk be bs bm,
  expr_to_pc Γc0 esc = Some pcc ->
  pc_has_var pcc = false ->
  closed_term esc ->
  fgood σ S (eq Γc0) (ECon (truth_constructor (pc_closed_value pcc))) altsc v ->
  fcore_at σ S (eq Γc0) esc altsc v bk be bs bm.
Proof.
  intros Γc0 esc pcc altsc v bk be bs bm Hpcc Hvarc Hclc IHF.
  destruct (IHF 0 be bs 1) as [h0 [K0 H0]].
  exists h0, (1 + bm + K0).
  intros Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv Hmk Halts Hszm Hok Hif Hn Hev.
  subst Γc.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  destruct (sym_ok_scoped S bs Φ (SFold Γs m altss) Hok) as [HΓs [Hscm Hscalts]].
  assert (Hsome : exists pc, expr_to_pc Γs m = Some pc).
  { destruct (expr_to_pc Γs m) as [pc |] eqn:E; [eexists; reflexivity | exfalso].
    destruct (is_op_app m) eqn:Hopm.
    - destruct (fold_alts_op_app_formula (Fin n) Φ Γs m altss v_s Hopm Hev) as [pc Hpc].
      congruence.
    - destruct (merge_keeps_k_no_formula Γs k m esc Hfree Hscm Hmk E)
        as [[kc [Hkc Hcont]] | [Hcm Hce]].
      + destruct (contains_k_formula_not_op Γs kc m esc Hcont Hfree Hclc
                    (solvable_in_empty_env Γc0 esc (expr_to_pc_solvable Γc0 esc pcc Hpcc))
                    Hif Hopm) as [pc Hpc].
        congruence.
      + destruct esc; simpl in Hce; try discriminate Hce. simpl in Hpcc. discriminate Hpcc. }
  destruct Hsome as [pc Hpc].
  pose proof (fold_alts_scrutinee_denote Γs (Fin n) Φ k m esc altss v_s pc Hscm Hmk Hpc Hev)
    as Hden.
  assert (Hval : pc_value σ pc = pc_closed_value pcc).
  { destruct Hden as [pc2 [Hd2 Hv2]].
    rewrite <- Hv2.
    rewrite (expr_to_pc_functional esc · Γc0 pc2 pcc (Hd2 · (sym_free_env_empty S)) Hpcc).
    exact (pc_value_closed σ pcc Hvarc). }
  pose proof (sym_scoped_expr_to_pc_denotes S Γs m pc Hscm Hpc) as Hdenm.
  destruct (pc_has_var pc) eqn:Hvar.
  - destruct (fold_alts_formula_shape (Fin n) Φ Γs m altss v_s pc Hpc Hev) as [Har | Hno];
      [| congruence].
    destruct (fold_alts_symbolic_formula_inv (Fin n) Φ Γs m pc altss v_s Hpc Hvar Har Hev)
      as [r1 [r2 [-> [Hf1 Hf2]]]].
    destruct (lit_eq_dec (pc_closed_value pcc) lit_true) as [Htrue | Hfalse].
    + assert (Htc : truth_constructor (pc_closed_value pcc) = dcon_true).
      { unfold truth_constructor. destruct (lit_eq_dec (pc_closed_value pcc) lit_true);
          [reflexivity | congruence]. }
      rewrite Htc in H0.
      assert (Hmpc : σ ⊨ pc) by (unfold models; rewrite Hval; exact Htrue).
      destruct (H0 Γc0 (Φ ∧ pc) Γs (ECon dcon_true) altss 0 ks kenv n r1 eq_refl ltac:(lia)
                  Hkenv Hks (models_and σ Φ pc Hm Hmpc) Henv
                  (merge_keeps_k_same σ S 0 _ _ (ContK_Con σ S dcon_true)) Halts ltac:(simpl; lia)
                  (sym_ok_step S bs Φ _ _ _ Hok (SymStep_FoldTrue Φ Γs m altss pc))
                  ltac:(lia) Hf1) as [k1 [Hk1 Hc1]].
      exists (1 + smt_size m + k1). split; [lia |].
      apply ContK_If_True; [exists pc; split; assumption | exact Hc1].
    + assert (Htc : truth_constructor (pc_closed_value pcc) = dcon_false).
      { unfold truth_constructor. destruct (lit_eq_dec (pc_closed_value pcc) lit_true);
          [congruence | reflexivity]. }
      rewrite Htc in H0.
      assert (Hmpc : σ ⊨ (¬ pc)).
      { unfold models, pc_not. simpl. apply prim_value_not. rewrite Hval. exact Hfalse. }
      destruct (H0 Γc0 (Φ ∧ ¬ pc) Γs (ECon dcon_false) altss 0 ks kenv n r2 eq_refl ltac:(lia)
                  Hkenv Hks (models_and σ Φ (¬ pc) Hm Hmpc) Henv
                  (merge_keeps_k_same σ S 0 _ _ (ContK_Con σ S dcon_false)) Halts ltac:(simpl; lia)
                  (sym_ok_step S bs Φ _ _ _ Hok (SymStep_FoldFalse Φ Γs m altss pc))
                  ltac:(lia) Hf2) as [k2 [Hk2 Hc2]].
      exists (1 + smt_size m + k2). split; [lia |].
      apply ContK_If_False; [exists pc; split; assumption | exact Hc2].
  - pose proof (fold_alts_ground_formula_inv (Fin n) Φ Γs m pc altss v_s Hpc Hvar Hev) as Hrec.
    rewrite (pc_value_closed σ pc Hvar) in Hval. rewrite Hval in Hrec.
    destruct (H0 Γc0 Φ Γs (ECon (truth_constructor (pc_closed_value pcc))) altss 0 ks kenv n v_s
                eq_refl ltac:(lia) Hkenv Hks Hm Henv
                (merge_keeps_k_same σ S 0 _ _ (ContK_Con σ S _)) Halts ltac:(simpl; lia)
                (sym_ok_step S bs Φ _ _ _ Hok
                   (SymStep_FoldGround Φ Γs m altss (truth_constructor (pc_closed_value pcc))))
                ltac:(lia) Hrec) as [k1 [Hk1 Hc1]].
    exists k1. split; [lia | exact Hc1].
Qed.

End CaseCores.
