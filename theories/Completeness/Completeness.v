From SymCoreTheory Require Export Completeness.Cases.
From Stdlib Require Import Bool.Bool Arith.Wf_nat Strings.String Lists.List Lia Arith.PeanoNat.
Import ListNotations.

Section Main.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Definition eval_motive (f : fuel) (Φ : path_condition) (Γ : environment) (e v : expr) : Prop :=
  f = Inf -> Φ = pc_true -> concore_expr e -> concrete_env Γ -> closed_program Γ e ->
  good σ S (eq Γ) e v.

Definition fold_motive (f : fuel) (Φ : path_condition) (Γ : environment) (e : expr)
  (alts : list alt) (v : expr) : Prop :=
  f = Inf -> Φ = pc_true -> concore_expr e -> Forall concore_alt alts -> concrete_env Γ ->
  scoped_env Γ -> closed_term e -> Forall (scoped_alt (dom_env Γ)) alts ->
  fgood σ S (eq Γ) e alts v.

Lemma forall2_good_of_ind : forall Γ args args',
  Forall2 (fun a a' => eval Inf pc_true Γ a a' /\ eval_motive Inf pc_true Γ a a') args args' ->
  Forall concore_expr args -> concrete_env Γ -> scoped_env Γ -> Forall (scoped (dom_env Γ)) args ->
  Forall2 (fun a a' => good σ S (eq Γ) a a') args args'.
Proof.
  intros Γ args args' HF Hc Hg HΓ Hs. induction HF as [| a a' l l' [_ Ha] _ IH]; constructor.
  - inversion Hc; subst. inversion Hs; subst.
    match goal with [Hca : concore_expr a, Hsa : scoped _ a |- _] =>
      exact (Ha eq_refl eq_refl Hca Hg (conj HΓ Hsa)) end.
  - inversion Hc; subst. inversion Hs; subst.
    match goal with [Hcl : Forall concore_expr l, Hsl : Forall (scoped _) l |- _] =>
      exact (IH Hcl Hsl) end.
Qed.

Lemma forall2_closed_of_ind : forall Γ args args',
  Forall2 (fun a a' => eval Inf pc_true Γ a a' /\ eval_motive Inf pc_true Γ a a') args args' ->
  Forall concore_expr args -> concrete_env Γ -> scoped_env Γ -> Forall (scoped (dom_env Γ)) args ->
  Forall closed_term args'.
Proof.
  intros Γ args args' HF Hc Hg HΓ Hs. induction HF as [| a a' l l' [Hev _] _ IH]; constructor.
  - inversion Hc; subst. inversion Hs; subst.
    match goal with [Hca : concore_expr a, Hsa : scoped _ a |- _] =>
      exact (closed_eval Γ a a' Hg Hca (conj HΓ Hsa) Hev) end.
  - inversion Hc; subst. inversion Hs; subst.
    match goal with [Hcl : Forall concore_expr l, Hsl : Forall (scoped _) l |- _] =>
      exact (IH Hcl Hsl) end.
Qed.

Theorem concrete_good : forall Γc e_c v_c,
  eval Inf pc_true Γc e_c v_c -> concore_expr e_c -> concrete_env Γc -> closed_program Γc e_c ->
  good σ S (eq Γc) e_c v_c.
Proof.
  intros Γc e_c v_c H.
  refine (eval_nested_ind eval_motive fold_motive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ _ _ _ _ _ Inf pc_true Γc e_c v_c H eq_refl eq_refl);
    unfold eval_motive, fold_motive.
  - intros f Φ Γ x Γ' e e' Hl _ IH Hf HΦ Hc Hg Hcl. injection Hf as ->. subst Φ.
    destruct (lookup_env_concrete Γ x Γ' e Hg Hl) as [Hg' He].
    destruct (lookup_env_scoped Γ x Γ' e (proj1 Hcl) Hl) as [HΓ' Hse].
    apply good_at_of_core. intros bk be bs _.
    exact (var_core σ S Γ x Γ' e e' bk be bs Hl (IH eq_refl eq_refl He Hg' (conj HΓ' Hse))).
  - intros f Φ Γ x Hl _ _ _ _ _. apply good_at_of_core. intros bk be bs _.
    exact (symvar_core σ S Γ x bk be bs Hl).
  - intros f Φ Γ l _ _ _ _ _. apply good_at_of_core. intros bk be bs _. apply lit_core.
  - intros f Φ Γ e d args Hu _ _ _ _ _. apply good_at_of_core. intros bk be bs _.
    exact (con_core σ S Γ e d args bk be bs Hu).
  - intros f Φ Γ e γ e' _ IH Hf HΦ Hc Hg Hcl. injection Hf as ->. subst Φ.
    apply good_at_of_core. intros bk be bs _.
    exact (cast_core σ S Γ e γ e' bk be bs
             (IH eq_refl eq_refl (concore_expr_cast e γ Hc) Hg (closed_program_cast _ _ _ Hcl))).
  - intros f Φ Γ Γ' x eb ea eb' _ IH Hf HΦ Hc Hg Hcl. injection Hf as ->. subst Φ.
    pose proof (concore_expr_app_l _ _ Hc) as Hcf.
    pose proof (concore_expr_app_r _ _ Hc) as Hca.
    pose proof (concore_expr_lam _ _ (concore_expr_thunk _ _ Hcf)) as Hcb.
    pose proof (concore_expr_thunk_env _ _ Hcf) as Hg'.
    apply good_at_of_core. intros bk be bs _.
    exact (app_abs_core σ S Γ Γ' x eb ea eb'
             (IH eq_refl eq_refl Hcb (concrete_env_extend Γ' x Γ ea Hg' Hg Hca)
                (closed_program_abs _ _ _ _ _ Hcl)) Hca bk be bs).
  - intros f Φ Γ ef ea ef' er Hcomp Hev1 IH1 _ IH2 Hf HΦ Hc Hg Hcl. injection Hf as ->. subst Φ.
    pose proof (concore_expr_app_l _ _ Hc) as Hcf.
    pose proof (concore_expr_app_r _ _ Hc) as Hca.
    pose proof (closed_program_app_l _ _ _ Hcl) as Hclf.
    pose proof (concore_eval_closed Γ ef ef' Hg Hcf Hclf Hev1) as Hcf'.
    pose proof (closed_eval Γ ef ef' Hg Hcf Hclf Hev1) as Hclf'.
    assert (Hcl2 : closed_program Γ (EApp ef' ea)).
    { split; [exact (proj1 Hcl) |].
      apply Scoped_App; [exact (closed_term_scoped _ _ Hclf') | exact (proj2 (closed_program_app_r _ _ _ Hcl))]. }
    assert (Hl : forall l, spine_head ef <> ELit l).
    { intros l Hsh. pose proof (eval_spine_head_lit _ _ _ _ _ Hev1 eq_refl eq_refl l Hsh) as ->.
      inversion Hcomp. }
    apply good_at_of_core. intros bk be bs _.
    exact (app_spine_core σ S Γ ef ea ef' er bk be bs Hcomp Hl (IH1 eq_refl eq_refl Hcf Hg Hclf)
             (IH2 eq_refl eq_refl (Con_App _ _ Hcf' Hca) Hg Hcl2)).
  - intros f Φ Γ b _ _ _ _ _. apply good_at_of_core. intros bk be bs _. apply bot_core.
  - intros f Φ Γ ef ea p args args' Hu _ HF Hf HΦ Hc Hg Hcl. injection Hf as ->. subst Φ.
    destruct (unspool_app_concore _ _ _ _ Hu Hc (Forall_nil _)) as [_ Hargs].
    destruct (unspool_app_scoped _ _ [] _ args Hu (proj2 Hcl) (Forall_nil _)) as [_ Hsargs].
    apply good_at_of_core. intros bk be bs _.
    exact (app_prim_core σ S Γ ef ea p args args' bk be bs Hu
             (forall2_closed_of_ind Γ args args' HF Hargs Hg (proj1 Hcl) Hsargs)
             (forall2_good_of_ind Γ args args' HF Hargs Hg (proj1 Hcl) Hsargs)).
  - intros f Φ Γ x e _ _ _ _ _. apply good_at_of_core. intros bk be bs _. apply lam_core.
  - intros f Φ Γ ef γ ea γ_a γ_r er Hd _ IH Hf HΦ Hc Hg Hcl. injection Hf as ->. subst Φ.
    pose proof (concore_expr_app_l _ _ Hc) as Hcf.
    pose proof (concore_expr_app_r _ _ Hc) as Hca.
    pose proof (concore_expr_cast _ _ Hcf) as Hcf0.
    apply good_at_of_core. intros bk be bs _.
    exact (app_cast_core σ S Γ ef γ ea γ_a γ_r er bk be bs Hd
             (IH eq_refl eq_refl (Con_Cast _ _ (Con_App _ _ Hcf0 (Con_Cast _ _ Hca))) Hg
                (closed_program_push _ _ _ _ _ _ Hcl))).
  - intros f Φ Γ e1 e2 ec et ef args er Hu _ _ _ _ Hc _ _. exfalso.
    destruct (unspool_app_concore _ _ _ _ Hu Hc (Forall_nil _)) as [Hh _].
    exact (not_concore_if _ _ _ Hh).
  - intros f Φ Γ b ea _ _ _ _ _. apply good_at_of_core. intros bk be bs _. apply app_bot_core.
  - intros f Φ Γ es alts es' er Hev1 IH1 Hfold IHF Hf HΦ Hc Hg Hcl. injection Hf as ->. subst Φ.
    inversion Hc as [| | | | | | es0 alts0 Hces Halts | | | | | | |]; subst.
    pose proof (closed_program_case_es _ _ _ Hcl) as Hcles.
    pose proof (concore_eval_closed Γ es es' Hg Hces Hcles Hev1) as Hces'.
    pose proof (closed_eval Γ es es' Hg Hces Hcles Hev1) as Hcles'.
    change (dec Unlimited) with Inf in *.
    rewrite (merge_concore_id Γ es' Hces') in Hfold, IHF.
    apply good_at_of_core. intros bk be bs _.
    exact (case_core σ S Γ es alts es' er bk be bs (IH1 eq_refl eq_refl Hces Hg Hcles)
             (IHF eq_refl eq_refl Hces' Halts Hg (proj1 Hcl) Hcles'
                (closed_program_case_alts _ _ _ Hcl))).
  - intros. exfalso. match goal with [ Hc : concore_expr (EIf _ _ _) |- _ ] =>
      exact (not_concore_if _ _ _ Hc) end.
  - intros f Φ Γ γ _ _ _ _ _. apply good_at_of_core. intros bk be bs _. apply coercion_core.
  - intros f Φ Γ e Hs _ HΦ _ _ _. subst Φ. rewrite sat_pc_true in Hs. discriminate Hs.
  - intros f Φ Γ τ _ _ _ _ _. apply good_at_of_core. intros bk be bs _. apply type_core.
  - intros f Φ Γ Γ' e e' _ IH Hf HΦ Hc Hg Hcl. injection Hf as ->. subst Φ.
    apply (good_weaken σ S (fun _ => True)); [intros; exact I |].
    apply thunk_good.
    exact (IH eq_refl eq_refl (concore_expr_thunk _ _ Hc) (concore_expr_thunk_env _ _ Hc)
             (closed_program_thunk _ _ _ Hcl)).
  - intros Φ Γ e Hf. discriminate Hf.
  - intros. exfalso. match goal with [ Hc : concore_expr (EIf _ _ _) |- _ ] =>
      exact (not_concore_if _ _ _ Hc) end.
  - intros. exfalso. match goal with [ Hc : concore_expr (EIf _ _ _) |- _ ] =>
      exact (not_concore_if _ _ _ Hc) end.
  - intros f Φ Γ e d ea xs ep alts er Hd Hfa _ IH Hf HΦ Hc Halts Hg HΓ Hcle Hsalts. subst f Φ.
    pose proof (decompose_con_app_concore e d ea Hd Hc) as Hea.
    pose proof (find_alt_concore d alts xs ep Hfa Halts) as Hep.
    apply fgood_of_core. intros bk be bs bm.
    exact (fcon_core σ S Γ e d ea xs ep alts er bk be bs bm Hd Hfa Hea
             (IH eq_refl eq_refl Hep (concrete_env_extend_multi xs ea Γ Γ Hg Hg Hea)
                (closed_program_fold_con Γ e d ea alts xs ep HΓ Hcle Hsalts Hd Hfa))).
  - intros f Φ Γ b alts _ _ _ _ _ _ _ _. apply fgood_of_core. intros bk be bs bm. apply fbot_core.
  - intros f Φ Γ e pc alts r Hpc Hvar _ IH Hf HΦ Hc Halts Hg HΓ Hcle Hsalts. subst f Φ.
    apply fgood_of_core. intros bk be bs bm.
    exact (fground_core σ S Γ e pc alts r bk be bs bm Hpc Hvar Hcle
             (IH eq_refl eq_refl (Con_Con _) Halts Hg HΓ (Scoped_Con nil _) Hsalts)).
  - intros f Φ Γ e pc alts r1 r2 Hpc Hvar Har _ _ _ _ Hf HΦ Hc Halts Hg HΓ Hcle Hsalts.
    subst f Φ. exfalso.
    rewrite (expr_to_pc_scoped_no_var Γ e pc (closed_term_scoped (dom_env Γ) e Hcle) Hpc) in Hvar.
    discriminate Hvar.
  - intros f Φ Γ e alts Hpcn Hopn Hhead Hmatch Hbot _ _ _ _ _ _ Hcle _.
    apply fgood_of_core. intros bk be bs bm.
    exact (fotherwise_core σ S Γ e alts bk be bs bm Hpcn Hopn Hcle Hmatch Hbot).
Qed.

Theorem forall_form : forall Γc e_con v_con,
  Γc ⊢ᶜ e_con ⇓ᶜ v_con ->
  forall Φ Γs e_sym,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    concore_expr e_con ->
    closed_program Γc e_con ->
    symbolic_program S Γs e_sym ->
    smt_bounded_run Φ Γs e_sym ->
    exists h, forall n, (h <= n)%nat ->
      forall v_sym, eval (Fin n) Φ Γs e_sym v_sym -> contains σ S v_sym v_con.
Proof.
  intros Γc e_con v_con Hevc Φ Γs e_sym Hm Henv Hcont Hcon Hcl Hsym [bs Hbnd].
  destruct (contains_k_of_contains _ _ _ _ Hcont) as [k Hk].
  destruct (contains_env_k_of_contains_env _ _ _ _ Henv) as [kenv Hkenv].
  destruct (concrete_good Γc e_con v_con Hevc Hcon (contains_env_concrete σ S Γs Γc Henv) Hcl
              (k + kenv) (k + kenv) bs) as [h [K H]].
  exists h. intros n Hn v_sym Hv.
  destruct (H Γc Φ Γs e_sym k kenv n v_sym eq_refl ltac:(lia) ltac:(lia) Hm Hkenv Hk
              (sym_ok_intro S bs Φ Γs e_sym Hsym Hbnd) Hn Hv) as [k' [_ Hc']].
  exact (contains_k_erase _ _ _ _ _ Hc').
Qed.

End Main.

Section CompletenessUnderCostLaws.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.

Theorem concore_completeness_forall : forall_form_lemma.
Proof.
  intros Γc e_con v_con Hevc Φ Γs σ S e_sym Hm Henv Hcont Hcon Hcl Hsym Hbnd.
  exact (forall_form σ S Γc e_con v_con Hevc Φ Γs e_sym Hm Henv Hcont Hcon Hcl Hsym Hbnd).
Qed.

Theorem concore_completeness_budget : target_completeness.
Proof.
  intros Φ Γs Γc σ S e_sym e_con v_con Hm Henv Hcont Hcon Hcl Hsym Hbnd [hb Hb] Hevc.
  destruct (forall_form σ S Γc e_con v_con Hevc Φ Γs e_sym Hm Henv Hcont Hcon Hcl Hsym Hbnd)
    as [h Hh].
  exists (h + hb). intros n Hn.
  destruct (Hb n ltac:(lia)) as [v Hv].
  exists v. split; [exact Hv | exact (Hh n ltac:(lia) v Hv)].
Qed.

Corollary concore_completeness_exists : existential_corollary.
Proof. exact (existential_corollary_of_target concore_completeness_budget). Qed.

End CompletenessUnderCostLaws.
