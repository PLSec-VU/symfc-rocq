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

End Completeness.
