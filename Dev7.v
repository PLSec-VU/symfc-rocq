From SymCoreTheory Require Import SymCore ConCore BranchLaws CostLaws Dev1 Dev2 Dev3.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Arith.Wf_nat Lia.
Import ListNotations.

Ltac cont_absurd Hif :=
  first
  [ simpl in Hif; discriminate Hif
  | match goal with [ Ht : is_thunk _ = true |- _ ] => simpl in Ht; discriminate Ht end
  | match goal with [ Hu : unspool_app _ _ = _ |- _ ] => simpl in Hu; discriminate Hu end ].

Section SimpleCores.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Ltac core_intro :=
  let Γc := fresh "Γc" in
  intros Γc ?Φ ?Γs ?e_s ?k ?kenv ?n ?v_s ?HA ?Hk ?Hkenv ?Hm ?Henv ?Hcont ?Hif ?Hn ?Hev;
  subst Γc.

Lemma var_core : forall Γc0 x Γc' e0 v bk be,
  lookup_env Γc0 x = Some (Γc', e0) ->
  good σ S (eq Γc') e0 v ->
  core_at σ S (eq Γc0) (EVar x) v bk be.
Proof.
  intros Γc0 x Γc' e0 v bk be Hl IH.
  destruct (IH be be) as [h0 [K0 H0]].
  exists (1 + h0), K0.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst; try sym_absurd.
  - change (dec (Remaining n)) with (Fin n) in *.
    match goal with [ Hls : lookup_env Γs x = Some (?G, ?b), Hb : eval (Fin n) Φ ?G ?b v_s |- _ ] =>
      destruct (contains_env_k_lookup σ S kenv Γs Γc0 x G b Henv Hls)
        as [Gc [ec [k1 [k2 [Hlc [Hce1 [Hce2 [Hk1 Hk2]]]]]]]];
      rewrite Hl in Hlc; injection Hlc as HG He; subst Gc ec;
      exact (H0 Γc' Φ G b k2 k1 n v_s eq_refl ltac:(lia) ltac:(lia) Hm Hce1 Hce2 ltac:(lia) Hb)
    end.
  - exfalso.
    match goal with [ Hls : lookup_env Γs x = None |- _ ] =>
      pose proof (contains_env_lookup_none σ S Γs Γc0 x (contains_env_k_erase _ _ _ _ _ Henv) Hls) as Hc
    end.
    congruence.
Qed.

Lemma symvar_core : forall Γc0 x bk be,
  lookup_env Γc0 x = None ->
  core_at σ S (eq Γc0) (EVar x) (EVar x) bk be.
Proof.
  intros Γc0 x bk be Hl.
  exists 1, 0.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst; try sym_absurd.
  - exfalso.
    match goal with [ Hls : lookup_env Γs x = Some (?G, ?b) |- _ ] =>
      destruct (contains_env_k_lookup σ S kenv Γs Γc0 x G b Henv Hls)
        as [Gc [ec [k1 [k2 [Hlc _]]]]]
    end.
    congruence.
  - exists 0. split; [lia | apply ContK_Var_Bound; assumption].
Qed.

Lemma lit_core : forall Γc0 l bk be,
  core_at σ S (eq Γc0) (ELit l) (ELit l) bk be.
Proof.
  intros Γc0 l bk be.
  exists (1 + bk), (2 * bk).
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  inversion Hcont; subst; try cont_absurd Hif.
  - destruct n as [| n]; [lia |].
    inversion Hev; subst; try sym_absurd.
    + exfalso.
      match goal with [ Hls : lookup_env Γs ?y = Some _, Hsy : S ?y = true |- _ ] =>
        rewrite (Hfree y Hsy) in Hls; discriminate Hls end.
    + exists 0. split; [lia | apply ContK_Var_Sym; assumption].
  - destruct n as [| n]; [lia |].
    inversion Hev; subst; try sym_absurd.
    exists 0. split; [lia | apply ContK_Lit].
  - match goal with [ Hd : denote σ S e_s l |- _ ] =>
      destruct (smt_eval_fin σ S Φ Γs n e_s v_s l Hm Hfree ltac:(lia) Hd Hev)
        as [_ [_ [kv [Hkv Hc]]]]
    end.
    exists kv. split; [lia | exact Hc].
Qed.

Lemma lam_core : forall Γc0 x e bk be,
  core_at σ S (eq Γc0) (ELam x e) (EThunk Γc0 (ELam x e)) bk be.
Proof.
  intros Γc0 x e bk be.
  exists 1, (be + bk).
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst; try sym_absurd.
  exists (kenv + k). split; [lia |].
  apply ContK_Thunk; [exact Henv | apply ContK_Lam; assumption].
Qed.

Lemma bot_core : forall Γc0 b bk be,
  core_at σ S (eq Γc0) (EBot b) (EBot b) bk be.
Proof.
  intros Γc0 b bk be.
  exists 1, 0.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst; try sym_absurd.
  exists 0. split; [lia | apply ContK_Bot].
Qed.

Lemma contains_coercion_eq : forall a b, contains σ S (ECoercion a) (ECoercion b) -> a = b.
Proof. intros a b H. inversion H; subst; try reflexivity; simpl in *; discriminate. Qed.

Lemma contains_type_eq : forall a b, contains σ S (EType a) (EType b) -> a = b.
Proof. intros a b H. inversion H; subst; try reflexivity; simpl in *; discriminate. Qed.

Lemma coercion_core : forall Γc0 γ bk be,
  core_at σ S (eq Γc0) (ECoercion γ) (ECoercion (subst_coerc Γc0 γ)) bk be.
Proof.
  intros Γc0 γ bk be.
  exists 1, 0.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst; try sym_absurd.
  rewrite (contains_coercion_eq _ _
             (subst_coerc_contains_env σ S Γs Γc0 γ (contains_env_k_erase _ _ _ _ _ Henv))).
  exists 0. split; [lia | apply ContK_Coercion].
Qed.

Lemma type_core : forall Γc0 τ bk be,
  core_at σ S (eq Γc0) (EType τ) (EType (subst_type Γc0 τ)) bk be.
Proof.
  intros Γc0 τ bk be.
  exists 1, 0.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst; try sym_absurd.
  rewrite (contains_type_eq _ _
             (subst_type_contains_env σ S Γs Γc0 τ (contains_env_k_erase _ _ _ _ _ Henv))).
  exists 0. split; [lia | apply ContK_Type].
Qed.

Lemma app_bot_core : forall Γc0 b c2 bk be,
  core_at σ S (eq Γc0) (EApp (EBot b) c2) (EBot b) bk be.
Proof.
  intros Γc0 b c2 bk be.
  exists 1, 0.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  match goal with [ Hf : contains_k _ _ _ ?f (EBot b) |- _ ] =>
    inversion Hf; subst; try cont_absurd Hif end.
  inversion Hev; subst; try sym_absurd.
  exists 0. split; [lia | apply ContK_Bot].
Qed.

Lemma cast_core : forall Γc0 c γ c' bk be,
  good σ S (eq Γc0) c c' ->
  core_at σ S (eq Γc0) (ECast c γ) (cast_expr c' γ) bk be.
Proof.
  intros Γc0 c γ c' bk be IH.
  destruct (IH bk be) as [h0 [K0 H0]].
  exists (1 + h0), K0.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst; try sym_absurd.
  change (dec (Remaining n)) with (Fin n) in *.
  match goal with [ Hc : contains_k _ _ k ?es c, Hv : eval (Fin n) Φ Γs ?es ?es' |- _ ] =>
    destruct (H0 Γc0 Φ Γs es k kenv n es' eq_refl Hk Hkenv Hm Henv Hc ltac:(lia) Hv)
      as [k' [Hk' Hc']];
    exists k'; split; [exact Hk' | apply cast_expr_contains_k; exact Hc']
  end.
Qed.

Lemma app_cast_core : forall Γc0 c γ c2 γ_a γ_r v bk be,
  decomp_coerc_arrow γ = Some (γ_a, γ_r) ->
  good σ S (eq Γc0) (ECast (EApp c (ECast c2 (sym_coerc γ_a))) γ_r) v ->
  core_at σ S (eq Γc0) (EApp (ECast c γ) c2) v bk be.
Proof.
  intros Γc0 c γ c2 γ_a γ_r v bk be Hd IH.
  destruct (IH bk be) as [h0 [K0 H0]].
  exists (1 + h0), K0.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  match goal with [ Hf : contains_k _ _ _ ?f (ECast c γ) |- _ ] =>
    inversion Hf; subst; try cont_absurd Hif end.
  inversion Hev; subst; try sym_absurd.
  change (dec (Remaining n)) with (Fin n) in *.
  match goal with
  | [ Hd' : decomp_coerc_arrow γ = Some _, Hv : eval (Fin n) Φ Γs _ v_s,
      Hfs : contains_k _ _ ?kf ?fs c, Has : contains_k _ _ ?ka ?as0 c2 |- _ ] =>
      rewrite Hd in Hd'; injection Hd' as <- <-;
      exact (H0 Γc0 Φ Γs _ (kf + ka) kenv n v_s eq_refl Hk Hkenv Hm Henv
               (ContK_Cast _ _ _ _ _ γ_r (ContK_App _ _ _ _ _ _ _ _ Hfs (ContK_Cast _ _ _ _ _ _ Has)))
               ltac:(lia) Hv)
  end.
Qed.

End SimpleCores.
