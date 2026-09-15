From SymCoreTheory Require Import SymCore ConCore BranchLaws CostLaws Dev1 Dev2 Dev3 Dev5 Dev7 Dev8.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Arith.Wf_nat Lia.
Import ListNotations.

Section CaseCores.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Lemma case_core : forall Γc0 esc altsc esc' v bk be,
  good σ S (eq Γc0) esc esc' ->
  fgood σ S (eq Γc0) esc' altsc v ->
  (inert_scrutinee esc' -> v = EBot BUndefined) ->
  core_at σ S (eq Γc0) (ECase esc altsc) v bk be.
Proof.
  intros Γc0 esc altsc esc' v bk be IH1 IHF Hinert.
  destruct (IH1 bk be) as [h1 [K1 H1]].
  destruct (IHF ((1 + field_count esc') * K1) (be + bk)) as [hF [KF HF]].
  exists (1 + h1 + hF), KF.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst; try sym_absurd.
  change (dec (Remaining n)) with (Fin n) in *.
  match goal with
  | [ Hc : contains_k _ _ ?k1 ?ess esc, Ha : Forall3 _ ?ks ?altss altsc,
      Hv : eval (Fin n) Φ Γs ?ess ?ess', Hf : fold_alts (Fin n) Φ Γs (merge Γs ?ess') ?altss v_s |- _ ] =>
      destruct (H1 Γc0 Φ Γs ess k1 kenv n ess' eq_refl ltac:(lia) Hkenv Hm Henv Hc ltac:(lia) Hv)
        as [k' [Hk' Hc']];
      destruct (merge_contains_k σ S Γs k' ess' esc' Hc') as [[k'' [Hk'' Hm'']] | [Hi1 Hi2]];
      [ exact (HF Γc0 Φ Γs (merge Γs ess') altss k'' ks kenv n v_s eq_refl ltac:(nia) ltac:(lia)
                 ltac:(lia) Hm Henv Hm'' Ha ltac:(lia) Hf)
      | rewrite (Hinert Hi2), (fold_alts_inert _ _ _ _ _ _ Hi1 Hf);
        exists 0; split; [lia | apply ContK_Bot] ]
  end.
Qed.

Lemma fcon_core : forall Γc0 esc d ea_c xs epc altsc v bk be,
  decompose_con_app esc = Some (d, ea_c) ->
  find_alt d altsc = Some (xs, epc) ->
  Forall concore_expr ea_c ->
  good σ S (eq (extend_env_multi Γc0 xs ea_c Γc0)) epc v ->
  fcore_at σ S (eq Γc0) esc altsc v bk be.
Proof.
  intros Γc0 esc d ea_c xs epc altsc v bk be Hd Hf Hcon IH.
  destruct (IH be (be + length xs * (be + bk))) as [h0 [K0 H0]].
  exists h0, K0.
  intros Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv Hcont Halts Hif Hn Hev. subst Γc.
  destruct (contains_k_unspool_rigid_rev σ S k m esc Hcont nil nil nil (ECon d) ea_c
              (Forall3_nil _) (decompose_con_app_unspool esc d ea_c Hd) eq_refl Hif)
    as [args_s [ks' [Hus [HF Hs]]]].
  simpl in Hs.
  destruct (find_alt_contains_alt_k_rev σ S ks altss altsc d xs epc Halts Hf)
    as [eps [kp [Hfs [Hxs [Hep Hkp]]]]].
  destruct (extend_env_multi_contains_k σ S xs kenv kenv ks' Γs Γc0 Γs Γc0 args_s ea_c
              Hxs Henv Henv HF Hcon) as [k' [Hk' Henv']].
  assert (Hds : decompose_con_app m = Some (d, args_s)) by (unfold decompose_con_app; rewrite Hus; reflexivity).
  inversion Hev; subst.
  - simpl in Hif. discriminate Hif.
  - simpl in Hif. discriminate Hif.
  - match goal with
    | [ Hd' : decompose_con_app m = Some _, Hf' : find_alt _ altss = Some _,
        Hv : eval (Fin n) Φ _ _ v_s |- _ ] =>
        rewrite Hds in Hd'; injection Hd' as <- <-;
        rewrite Hfs in Hf'; injection Hf' as <- <-;
        exact (H0 _ Φ _ eps kp k' n v_s eq_refl ltac:(lia) ltac:(nia) Hm Henv' Hep ltac:(lia) Hv)
    end.
  - unfold decompose_con_app in Hds. simpl in Hds. discriminate Hds.
  - match goal with [ Hmatch : match decompose_con_app m with _ => _ end |- _ ] =>
      rewrite Hds in Hmatch; congruence end.
Qed.

Lemma fbot_core : forall Γc0 b altsc bk be,
  fcore_at σ S (eq Γc0) (EBot b) altsc (EBot b) bk be.
Proof.
  intros Γc0 b altsc bk be.
  exists 0, 0.
  intros Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv Hcont Halts Hif Hn Hev. subst Γc.
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst.
  - match goal with [ Hd : decompose_con_app _ = Some _ |- _ ] =>
      unfold decompose_con_app in Hd; simpl in Hd; discriminate Hd end.
  - exists 0. split; [lia | apply ContK_Bot].
  - match goal with [ Hb : is_bot _ = false |- _ ] => simpl in Hb; discriminate Hb end.
Qed.

Lemma fotherwise_core : forall Γc0 esc altsc bk be,
  (match decompose_con_app esc with
   | Some (d, _) => find_alt d altsc = None
   | None => True
   end) ->
  is_bot esc = false ->
  fcore_at σ S (eq Γc0) esc altsc (EBot BUndefined) bk be.
Proof.
  intros Γc0 esc altsc bk be Hmatch Hbot.
  exists 0, 0.
  intros Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv Hcont Halts Hif Hn Hev. subst Γc.
  inversion Hev; subst.
  - simpl in Hif. discriminate Hif.
  - simpl in Hif. discriminate Hif.
  - exfalso.
    match goal with
    | [ Hd : decompose_con_app m = Some (?d, ?ea), Hf : find_alt ?d altss = Some (?xs, ?ep) |- _ ] =>
        destruct (contains_k_unspool_con σ S k m esc Hcont nil nil nil (Forall3_nil _) d ea
                    (decompose_con_app_unspool m d ea Hd)) as [args_c [ks' [Huc _]]];
        assert (Hdc : decompose_con_app esc = Some (d, args_c))
          by (unfold decompose_con_app; simpl in Huc; rewrite Huc; reflexivity);
        rewrite Hdc in Hmatch;
        destruct (find_alt_contains_alt σ S altss altsc d xs ep
                    (contains_alts_k_erase σ S ks altss altsc Halts) Hf) as [epc [Hfc _]];
        congruence
    end.
  - exfalso. inversion Hcont; subst; try cont_absurd Hif. simpl in Hbot. discriminate Hbot.
  - exists 0. split; [lia | apply ContK_Bot].
Qed.

End CaseCores.
