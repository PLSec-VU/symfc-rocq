From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.PeanoNat.
Import ListNotations.

Section Completeness.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

Definition target_completeness : Prop :=
  forall Φ Γs Γc σ S e_sym e_con v_con,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    concore_expr e_con ->
    budget_total Φ Γs e_sym ->
    Γc ⊢ᶜ e_con ⇓ᶜ v_con ->
    exists h, forall n, (h <= n)%nat ->
      exists v_sym, eval (Fin n) Φ Γs e_sym v_sym /\ contains σ S v_sym v_con.

Definition forall_form_lemma : Prop :=
  forall Γc e_con v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con ->
    forall Φ Γs σ S e_sym,
      σ ⊨ Φ ->
      contains_env σ S Γs Γc ->
      contains σ S e_sym e_con ->
      concore_expr e_con ->
      exists h, forall n, (h <= n)%nat ->
        forall v_sym, eval (Fin n) Φ Γs e_sym v_sym -> contains σ S v_sym v_con.

(**
  The existential corollary follows from the upward-closed target: fix a large
  enough budget and read off one symbolic value that contains the concrete one.
  Because EBot BOutOfFuel contains no ConCore term, the value delivered here is
  never that bottom, so the corollary is not vacuous.
*)
Definition existential_corollary : Prop :=
  forall Φ Γs Γc σ S e_sym e_con v_con,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    concore_expr e_con ->
    budget_total Φ Γs e_sym ->
    Γc ⊢ᶜ e_con ⇓ᶜ v_con ->
    exists k v_sym, eval (Fin k) Φ Γs e_sym v_sym /\ contains σ S v_sym v_con.

Lemma existential_corollary_of_target :
  target_completeness -> existential_corollary.
Proof.
  intros Htarget Φ Γs Γc σ S e_sym e_con v_con Hmod Henv Hcont Hcon Hbud Hevalc.
  destruct (Htarget Φ Γs Γc σ S e_sym e_con v_con Hmod Henv Hcont Hcon Hbud Hevalc)
    as [h Hh].
  destruct (Hh h ltac:(lia)) as [v_sym [Heval Hcv]].
  exists h, v_sym. split; assumption.
Qed.

Section BudgetTotalIsNecessary.
  Variables (Φ : path_condition) (σ : valuation) (S : symvars).
  Variables (x : var) (l l' : lit).

  Hypothesis Hsat  : sat Φ = true.
  Hypothesis Hfeas : sat (Φ ∧ ¬ PCVar x) = true.
  Hypothesis Hsx   : S x = true.
  Hypothesis Hmodx : σ ⊨ PCVar x.

  Definition necessity_stuck_arm : expr := EApp (ELit l) (ELit l).
  Definition necessity_program : expr := EIf (EVar x) (ELit l') necessity_stuck_arm.

  Lemma necessity_no_value_at_large_budget : forall k v,
    ~ eval (Fin (Datatypes.S (Datatypes.S k))) Φ · necessity_program v.
  Proof.
    intros k v Hv. unfold necessity_program in Hv.
    inversion Hv as [| | | | | | | | | | | | | | kf Φ0 Γ0 ec0 et0 ef0 ec' et' ef' pc_c
                       Hc Hpc Ht Hf | | kf Φ0 Γ0 e0 Hunsat | | |]; subst.
    - no_con_head.
    - assert (Hec : ec' = EVar x)
        by (eapply eval_symvar_fin_same with (k := k) (Γ := ·);
            [reflexivity | exact Hsat | exact Hc]).
      subst ec'. simpl in Hpc. injection Hpc as Hpc. subst pc_c.
      unfold necessity_stuck_arm in Hf.
      eapply app_lit_no_value_fin; [exact Hfeas | exact Hf].
    - rewrite Hsat in Hunsat. discriminate.
  Qed.

  Theorem budget_total_fails_on_stuck_arm : ~ budget_total Φ · necessity_program.
  Proof.
    intros [h Hh].
    destruct (Hh (Datatypes.S (Datatypes.S h)) ltac:(lia)) as [v Hv].
    exact (necessity_no_value_at_large_budget h v Hv).
  Qed.

  Theorem stuck_arm_concrete_instance_terminates :
    · ⊢ᶜ ELit l' ⇓ᶜ ELit l' /\ contains σ S necessity_program (ELit l').
  Proof.
    split.
    - apply Eval_Lit.
    - apply Cont_If_True; [| apply Cont_Lit].
      exists (PCVar x). split; [| exact Hmodx].
      intros Γ Hfree. simpl. rewrite (Hfree x Hsx). reflexivity.
  Qed.

End BudgetTotalIsNecessary.

Section LoopingArmUnderCase.
  Variables (Φ : path_condition) (σ : valuation) (S : symvars).
  Variables (x : var) (l' : lit).

  Hypothesis HmodPhi : σ ⊨ Φ.
  Hypothesis Hsx     : S x = true.
  Hypothesis Hmodx   : σ ⊨ PCVar x.
  Hypothesis Hsf     : S self_app_var = false.

  Definition case_alts : list alt :=
    Alt "T" [] (ELit l') :: Alt "F" [] self_app :: nil.
  Definition case_sym : expr := ECase (EIf (EVar x) (ECon "T") (ECon "F")) case_alts.
  Definition case_con : expr := ECase (ECon "T") case_alts.

  Lemma case_guard_cond : models_cond σ S (EVar x).
  Proof.
    exists (PCVar x). split; [| exact Hmodx].
    intros Γ Hfree. simpl. rewrite (Hfree x Hsx). reflexivity.
  Qed.

  Lemma case_alts_contains : Forall2 (contains_alt σ S) case_alts case_alts.
  Proof.
    apply Forall2_cons; [| apply Forall2_cons; [| apply Forall2_nil]].
    - apply Cont_Alt; [apply Forall_nil | apply Cont_Lit].
    - apply Cont_Alt; [apply Forall_nil |].
      unfold self_app, self_app_fun, self_app_body.
      apply Cont_App; (apply Cont_Lam; [exact Hsf |]);
        (apply Cont_App; apply Cont_Var_Bound; exact Hsf).
  Qed.

  Lemma case_contains : contains σ S case_sym case_con.
  Proof.
    apply Cont_Case; [| exact case_alts_contains].
    apply Cont_If_True; [exact case_guard_cond | apply Cont_Con].
  Qed.

  Lemma case_con_concore : concore_expr case_con.
  Proof.
    apply Con_Case; [apply Con_Con |].
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
    - apply Con_Alt. apply Con_Lit.
    - apply Con_Alt. unfold self_app, self_app_fun, self_app_body.
      apply Con_App; apply Con_Lam; apply Con_App; apply Con_Var.
  Qed.

  Lemma case_con_converges : Φ ; · ⊢ case_con ⇓ (ELit l').
  Proof.
    unfold case_con.
    eapply Eval_Case.
    - eapply Eval_Con. reflexivity.
    - simpl. eapply FoldAlts_Con.
      + reflexivity.
      + simpl. destruct (string_dec "T" "T"); [reflexivity | congruence].
      + simpl. apply Eval_Lit.
  Qed.

  Lemma case_budget_total : budget_total Φ · case_sym.
  Proof.
    exists 3%nat. intros n Hn. destruct n as [| [| [| m]]]; [lia | lia | lia |].
    destruct (self_app_has_value_at_every_budget (Datatypes.S (Datatypes.S m))
                (Φ ∧ ¬ PCVar x) ·) as [vf Hvf].
    exists (EIf (EVar x) (ELit l') vf).
    unfold case_sym.
    eapply Eval_Case.
    - eapply Eval_If with (pc_c := PCVar x).
      + apply Eval_SymVar. reflexivity.
      + reflexivity.
      + eapply Eval_Con. reflexivity.
      + eapply Eval_Con. reflexivity.
    - simpl. eapply FoldAlts_If.
      + reflexivity.
      + simpl. eapply FoldAlts_Con.
        * reflexivity.
        * simpl. destruct (string_dec "T" "T"); [reflexivity | congruence].
        * simpl. apply Eval_Lit.
      + simpl. eapply FoldAlts_Con.
        * reflexivity.
        * simpl. destruct (string_dec "F" "T"); [congruence |].
          simpl. destruct (string_dec "F" "F"); [reflexivity | congruence].
        * simpl. exact Hvf.
  Qed.

  Theorem case_target_conclusion :
    exists h, forall n, (h <= n)%nat ->
      exists v_sym, eval (Fin n) Φ · case_sym v_sym /\ contains σ S v_sym (ELit l').
  Proof.
    exists 3%nat. intros n Hn. destruct n as [| [| [| m]]]; [lia | lia | lia |].
    destruct (self_app_has_value_at_every_budget (Datatypes.S (Datatypes.S m))
                (Φ ∧ ¬ PCVar x) ·) as [vf Hvf].
    exists (EIf (EVar x) (ELit l') vf). split.
    - unfold case_sym.
      eapply Eval_Case.
      + eapply Eval_If with (pc_c := PCVar x).
        * apply Eval_SymVar. reflexivity.
        * reflexivity.
        * eapply Eval_Con. reflexivity.
        * eapply Eval_Con. reflexivity.
      + simpl. eapply FoldAlts_If.
        * reflexivity.
        * simpl. eapply FoldAlts_Con.
          -- reflexivity.
          -- simpl. destruct (string_dec "T" "T"); [reflexivity | congruence].
          -- simpl. apply Eval_Lit.
        * simpl. eapply FoldAlts_Con.
          -- reflexivity.
          -- simpl. destruct (string_dec "F" "T"); [congruence |].
             simpl. destruct (string_dec "F" "F"); [reflexivity | congruence].
          -- simpl. exact Hvf.
    - apply Cont_If_True; [exact case_guard_cond | apply Cont_Lit].
  Qed.

End LoopingArmUnderCase.

Section AppliedCaseWithBranchScrutinee.
  Variables (Φ : path_condition) (σ : valuation) (S : symvars).
  Variables (x : var) (la : lit).

  Hypothesis HmodPhi : σ ⊨ Φ.
  Hypothesis Hsx     : S x = true.
  Hypothesis Hmodx   : σ ⊨ PCVar x.
  Hypothesis Hsy     : S "y" = false.
  Hypothesis Hsz     : S "z" = false.

  Definition app_alts : list alt :=
    Alt "T" [] (ELam "y" (EVar "y")) :: Alt "F" [] (ELam "z" (EVar "z")) :: nil.
  Definition app_case : expr := ECase (EIf (EVar x) (ECon "T") (ECon "F")) app_alts.
  Definition app_sym : expr := EApp app_case (ELit la).
  Definition app_case_con : expr := ECase (ECon "T") app_alts.
  Definition app_con : expr := EApp app_case_con (ELit la).

  Lemma app_guard_cond : models_cond σ S (EVar x).
  Proof.
    exists (PCVar x). split; [| exact Hmodx].
    intros Γ Hfree. simpl. rewrite (Hfree x Hsx). reflexivity.
  Qed.

  Lemma app_alts_contains : Forall2 (contains_alt σ S) app_alts app_alts.
  Proof.
    apply Forall2_cons; [| apply Forall2_cons; [| apply Forall2_nil]].
    - apply Cont_Alt; [apply Forall_nil |].
      apply Cont_Lam; [exact Hsy | apply Cont_Var_Bound; exact Hsy].
    - apply Cont_Alt; [apply Forall_nil |].
      apply Cont_Lam; [exact Hsz | apply Cont_Var_Bound; exact Hsz].
  Qed.

  Lemma app_contains : contains σ S app_sym app_con.
  Proof.
    apply Cont_App; [| apply Cont_Lit].
    apply Cont_Case; [| exact app_alts_contains].
    apply Cont_If_True; [exact app_guard_cond | apply Cont_Con].
  Qed.

  Lemma app_con_concore : concore_expr app_con.
  Proof.
    apply Con_App; [| apply Con_Lit].
    apply Con_Case; [apply Con_Con |].
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]];
      apply Con_Alt; apply Con_Lam; apply Con_Var.
  Qed.

  Lemma app_con_converges : Φ ; · ⊢ app_con ⇓ (ELit la).
  Proof.
    unfold app_con, app_case_con.
    eapply Eval_AppSpine.
    - apply Comp_Case.
    - eapply Eval_Case.
      + eapply Eval_Con. reflexivity.
      + simpl. eapply FoldAlts_Con.
        * reflexivity.
        * simpl. destruct (string_dec "T" "T"); [reflexivity | congruence].
        * simpl. apply Eval_Lam.
    - eapply Eval_AppAbs. simpl.
      eapply Eval_Var.
      + simpl. destruct (string_dec "y" "y"); [reflexivity | congruence].
      + apply Eval_Lit.
  Qed.

  Lemma app_sym_converges : Φ ; · ⊢ app_sym ⇓ (EIf (EVar x) (ELit la) (ELit la)).
  Proof.
    unfold app_sym, app_case.
    eapply Eval_AppSpine.
    - apply Comp_Case.
    - eapply Eval_Case.
      + eapply Eval_If with (pc_c := PCVar x).
        * apply Eval_SymVar. reflexivity.
        * reflexivity.
        * eapply Eval_Con. reflexivity.
        * eapply Eval_Con. reflexivity.
      + simpl. eapply FoldAlts_If.
        * reflexivity.
        * simpl. eapply FoldAlts_Con.
          -- reflexivity.
          -- simpl. destruct (string_dec "T" "T"); [reflexivity | congruence].
          -- simpl. apply Eval_Lam.
        * simpl. eapply FoldAlts_Con.
          -- reflexivity.
          -- simpl. destruct (string_dec "F" "T"); [congruence |].
             simpl. destruct (string_dec "F" "F"); [reflexivity | congruence].
          -- simpl. apply Eval_Lam.
    - eapply Eval_AppIf.
      + reflexivity.
      + simpl. eapply Eval_If with (pc_c := PCVar x).
        * apply Eval_SymVar. reflexivity.
        * reflexivity.
        * eapply Eval_AppAbs. simpl. eapply Eval_Var.
          -- simpl. destruct (string_dec "y" "y"); [reflexivity | congruence].
          -- apply Eval_Lit.
        * eapply Eval_AppAbs. simpl. eapply Eval_Var.
          -- simpl. destruct (string_dec "z" "z"); [reflexivity | congruence].
          -- apply Eval_Lit.
  Qed.

  Lemma app_budget_total : budget_total Φ · app_sym.
  Proof.
    apply budget_total_of_terminating. exists (EIf (EVar x) (ELit la) (ELit la)).
    exact app_sym_converges.
  Qed.

  Theorem app_target_conclusion :
    exists h, forall n, (h <= n)%nat ->
      exists v_sym, eval (Fin n) Φ · app_sym v_sym /\ contains σ S v_sym (ELit la).
  Proof.
    destruct (eval_inf_has_budget Φ · app_sym (EIf (EVar x) (ELit la) (ELit la))
                app_sym_converges) as [h Hh].
    exists h. intros n Hn. exists (EIf (EVar x) (ELit la) (ELit la)). split.
    - apply Hh. exact Hn.
    - apply Cont_If_True; [exact app_guard_cond | apply Cont_Lit].
  Qed.

End AppliedCaseWithBranchScrutinee.

End Completeness.
