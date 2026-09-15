From SymCoreTheory Require Import SymCore ConCore BranchLaws CostLaws Dev1 Dev2 Dev3 Dev4 Dev5 Dev6 Dev7 Dev8 Dev9 Dev10.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Arith.Wf_nat Lia.
Import ListNotations.

Section Main.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Definition eval_motive (f : fuel) (Φ : path_condition) (Γ : environment) (e v : expr) : Prop :=
  f = Inf -> Φ = pc_true -> concore_expr e -> concrete_env Γ -> good σ S (eq Γ) e v.

Definition fold_motive (f : fuel) (Φ : path_condition) (Γ : environment) (e : expr)
  (alts : list alt) (v : expr) : Prop :=
  f = Inf -> Φ = pc_true -> concore_expr e -> Forall concore_alt alts -> concrete_env Γ ->
  fgood σ S (eq Γ) e alts v.

Lemma forall2_good_of_ind : forall Γ args args',
  Forall2 (fun a a' => eval Inf pc_true Γ a a' /\ eval_motive Inf pc_true Γ a a') args args' ->
  Forall concore_expr args -> concrete_env Γ ->
  Forall2 (fun a a' => good σ S (eq Γ) a a') args args'.
Proof.
  intros Γ args args' HF Hc Hg. induction HF as [| a a' l l' [_ Ha] _ IH]; constructor.
  - inversion Hc; subst. exact (Ha eq_refl eq_refl ltac:(assumption) Hg).
  - inversion Hc; subst. exact (IH ltac:(assumption)).
Qed.

Theorem concrete_good : forall Γc e_c v_c,
  eval Inf pc_true Γc e_c v_c -> concore_expr e_c -> concrete_env Γc ->
  good σ S (eq Γc) e_c v_c.
Proof.
  intros Γc e_c v_c H.
  refine (eval_nested_ind eval_motive fold_motive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ _ _ _ Inf pc_true Γc e_c v_c H eq_refl eq_refl);
    unfold eval_motive, fold_motive.
  - intros f Φ Γ x Γ' e e' Hl _ IH Hf HΦ Hc Hg. injection Hf as ->. subst Φ.
    destruct (lookup_env_concrete Γ x Γ' e Hg Hl) as [Hg' He].
    apply good_at_of_core. intros bk be _.
    exact (var_core σ S Γ x Γ' e e' bk be Hl (IH eq_refl eq_refl He Hg')).
  - intros f Φ Γ x Hl _ _ _ _. apply good_at_of_core. intros bk be _.
    exact (symvar_core σ S Γ x bk be Hl).
  - intros f Φ Γ l _ _ _ _. apply good_at_of_core. intros bk be _. apply lit_core.
  - intros f Φ Γ e d args Hu _ _ _ _. apply good_at_of_core. intros bk be _.
    exact (con_core σ S Γ e d args bk be Hu).
  - intros f Φ Γ e γ e' _ IH Hf HΦ Hc Hg. injection Hf as ->. subst Φ.
    apply good_at_of_core. intros bk be _.
    exact (cast_core σ S Γ e γ e' bk be (IH eq_refl eq_refl (concore_expr_cast e γ Hc) Hg)).
  - intros f Φ Γ Γ' x eb ea eb' _ IH Hf HΦ Hc Hg. injection Hf as ->. subst Φ.
    pose proof (concore_expr_app_l _ _ Hc) as Hcf.
    pose proof (concore_expr_app_r _ _ Hc) as Hca.
    pose proof (concore_expr_lam _ _ (concore_expr_thunk _ _ Hcf)) as Hcb.
    pose proof (concore_expr_thunk_env _ _ Hcf) as Hg'.
    apply good_at_of_core. intros bk be _.
    exact (app_abs_core σ S Γ Γ' x eb ea eb'
             (IH eq_refl eq_refl Hcb (concrete_env_extend Γ' x Γ ea Hg' Hg Hca)) Hca bk be).
  - intros f Φ Γ ef ea ef' er Hcomp Hev1 IH1 _ IH2 Hf HΦ Hc Hg. injection Hf as ->. subst Φ.
    pose proof (concore_expr_app_l _ _ Hc) as Hcf.
    pose proof (concore_expr_app_r _ _ Hc) as Hca.
    pose proof (concore_eval_closed Γ ef ef' Hg Hcf Hev1) as Hcf'.
    assert (Hl : forall l, spine_head ef <> ELit l).
    { intros l Hsh. pose proof (eval_spine_head_lit _ _ _ _ _ Hev1 eq_refl eq_refl l Hsh) as ->.
      inversion Hcomp. }
    apply good_at_of_core. intros bk be _.
    exact (app_spine_core σ S Γ ef ea ef' er bk be Hcomp Hl (IH1 eq_refl eq_refl Hcf Hg)
             (IH2 eq_refl eq_refl (Con_App _ _ Hcf' Hca) Hg)).
  - intros f Φ Γ b _ _ _ _. apply good_at_of_core. intros bk be _. apply bot_core.
  - intros f Φ Γ ef ea p args args' Hu _ HF Hf HΦ Hc Hg. injection Hf as ->. subst Φ.
    destruct (unspool_app_concore _ _ _ _ Hu Hc (Forall_nil _)) as [_ Hargs].
    apply good_at_of_core. intros bk be _.
    exact (app_prim_core σ S Γ ef ea p args args' bk be Hu (forall2_good_of_ind Γ args args' HF Hargs Hg)).
  - intros f Φ Γ x e _ _ _ _. apply good_at_of_core. intros bk be _. apply lam_core.
  - intros f Φ Γ ef γ ea γ_a γ_r er Hd _ IH Hf HΦ Hc Hg. injection Hf as ->. subst Φ.
    pose proof (concore_expr_app_l _ _ Hc) as Hcf.
    pose proof (concore_expr_app_r _ _ Hc) as Hca.
    pose proof (concore_expr_cast _ _ Hcf) as Hcf0.
    apply good_at_of_core. intros bk be _.
    exact (app_cast_core σ S Γ ef γ ea γ_a γ_r er bk be Hd
             (IH eq_refl eq_refl (Con_Cast _ _ (Con_App _ _ Hcf0 (Con_Cast _ _ Hca))) Hg)).
  - intros f Φ Γ e1 e2 ec et ef args er Hu _ _ _ _ Hc _. exfalso.
    destruct (unspool_app_concore _ _ _ _ Hu Hc (Forall_nil _)) as [Hh _].
    exact (not_concore_if _ _ _ Hh).
  - intros f Φ Γ b ea _ _ _ _. apply good_at_of_core. intros bk be _. apply app_bot_core.
  - intros f Φ Γ es alts es' er Hev1 IH1 Hfold IHF Hf HΦ Hc Hg. injection Hf as ->. subst Φ.
    inversion Hc as [| | | | | | es0 alts0 Hces Halts | | | | | | |]; subst.
    pose proof (concore_eval_closed Γ es es' Hg Hces Hev1) as Hces'.
    change (dec Unlimited) with Inf in *.
    rewrite (merge_concore_id Γ es' Hces') in Hfold, IHF.
    apply good_at_of_core. intros bk be _.
    exact (case_core σ S Γ es alts es' er bk be (IH1 eq_refl eq_refl Hces Hg)
             (IHF eq_refl eq_refl Hces' Halts Hg) (fun Hi => fold_alts_inert _ _ _ _ _ _ Hi Hfold)).
  - intros. exfalso. match goal with [ Hc : concore_expr (EIf _ _ _) |- _ ] =>
      exact (not_concore_if _ _ _ Hc) end.
  - intros f Φ Γ γ _ _ _ _. apply good_at_of_core. intros bk be _. apply coercion_core.
  - intros f Φ Γ e Hs _ HΦ _ _. subst Φ. rewrite sat_pc_true in Hs. discriminate Hs.
  - intros f Φ Γ τ _ _ _ _. apply good_at_of_core. intros bk be _. apply type_core.
  - intros f Φ Γ Γ' e e' _ IH Hf HΦ Hc Hg. injection Hf as ->. subst Φ.
    apply (good_weaken σ S (fun _ => True)); [intros; exact I |].
    apply thunk_good.
    exact (IH eq_refl eq_refl (concore_expr_thunk _ _ Hc) (concore_expr_thunk_env _ _ Hc)).
  - intros Φ Γ e Hf. discriminate Hf.
  - intros. exfalso. match goal with [ Hc : concore_expr (EIf _ _ _) |- _ ] =>
      exact (not_concore_if _ _ _ Hc) end.
  - intros. exfalso. match goal with [ Hc : concore_expr (EIf _ _ _) |- _ ] =>
      exact (not_concore_if _ _ _ Hc) end.
  - intros f Φ Γ e d ea xs ep alts er Hd Hfa _ IH Hf HΦ Hc Halts Hg. subst f Φ.
    pose proof (decompose_con_app_concore e d ea Hd Hc) as Hea.
    pose proof (find_alt_concore d alts xs ep Hfa Halts) as Hep.
    apply fgood_of_core. intros bk be _.
    exact (fcon_core σ S Γ e d ea xs ep alts er bk be Hd Hfa Hea
             (IH eq_refl eq_refl Hep (concrete_env_extend_multi xs ea Γ Γ Hg Hg Hea))).
  - intros f Φ Γ b alts _ _ _ _ _. apply fgood_of_core. intros bk be _. apply fbot_core.
  - intros f Φ Γ e alts _ Hmatch Hbot _ _ _ _ _. apply fgood_of_core. intros bk be _.
    exact (fotherwise_core σ S Γ e alts bk be Hmatch Hbot).
Qed.

Theorem forall_form : forall Γc e_con v_con,
  Γc ⊢ᶜ e_con ⇓ᶜ v_con ->
  forall Φ Γs e_sym,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    concore_expr e_con ->
    exists h, forall n, (h <= n)%nat ->
      forall v_sym, eval (Fin n) Φ Γs e_sym v_sym -> contains σ S v_sym v_con.
Proof.
  intros Γc e_con v_con Hevc Φ Γs e_sym Hm Henv Hcont Hcon.
  destruct (contains_k_of_contains _ _ _ _ Hcont) as [k Hk].
  destruct (contains_env_k_of_contains_env _ _ _ _ Henv) as [kenv Hkenv].
  destruct (concrete_good Γc e_con v_con Hevc Hcon (contains_env_concrete σ S Γs Γc Henv)
              (k + kenv) (k + kenv)) as [h [K H]].
  exists h. intros n Hn v_sym Hv.
  destruct (H Γc Φ Γs e_sym k kenv n v_sym eq_refl ltac:(lia) ltac:(lia) Hm Hkenv Hk Hn Hv)
    as [k' [_ Hc']].
  exact (contains_k_erase _ _ _ _ _ Hc').
Qed.

End Main.

Print Assumptions forall_form.
