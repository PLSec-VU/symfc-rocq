From SymCoreTheory Require Import SymCore ConCore CostLaws Completeness Model.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.
Open Scope string_scope.

Section ElseBranchLoopingThenArm.

Definition nv_x : var := "x".
Definition nv_S : symvars := only nv_x.
Definition nv_sigma : valuation := fun _ => false.
Definition nv_phi : path_condition := PCLit true.
Definition nv_true : expr := @ELit model_sorts true.

Definition nv_alts : list alt :=
  Alt "T" [] self_app :: Alt "F" [] nv_true :: nil.
Definition nv_sym : expr := ECase (EIf (EVar nv_x) (ECon "T") (ECon "F")) nv_alts.
Definition nv_con : expr := ECase (ECon "F") nv_alts.

Lemma nv_sat : forall Φ, @sat model_sorts model_solver Φ = true.
Proof. reflexivity. Qed.

Lemma nv_sigma_models_phi : nv_sigma ⊨ nv_phi.
Proof. reflexivity. Qed.

Lemma nv_guard_false : models_not_cond nv_sigma nv_S (EVar nv_x).
Proof.
  exists (PCVar nv_x). split; [| reflexivity].
  intros Γ Hfree. simpl. rewrite (Hfree nv_x (only_self nv_x)). reflexivity.
Qed.

Lemma nv_contains : contains nv_sigma nv_S nv_sym nv_con.
Proof.
  apply Cont_Case.
  - apply Cont_If_False; [exact nv_guard_false | apply Cont_Con].
  - apply Forall2_cons; [| apply Forall2_cons; [| apply Forall2_nil]].
    + apply Cont_Alt; [apply Forall_nil |].
      unfold self_app, self_app_fun, self_app_body.
      apply Cont_App; (apply Cont_Lam; [reflexivity |]);
        (apply Cont_App; apply Cont_Var_Bound; reflexivity).
    + apply Cont_Alt; [apply Forall_nil | apply Cont_Lit].
Qed.

Lemma nv_con_concore : concore_expr nv_con.
Proof.
  apply Con_Case; [apply Con_Con |].
  apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
  - apply Con_Alt. unfold self_app, self_app_fun, self_app_body.
    apply Con_App; apply Con_Lam; apply Con_App; apply Con_Var.
  - apply Con_Alt. apply Con_Lit.
Qed.

Lemma nv_con_closed : closed_program · nv_con.
Proof.
  split; [apply Scoped_Env_Empty |].
  unfold nv_con, nv_alts, self_app, self_app_fun, self_app_body.
  apply Scoped_Case; [apply Scoped_Con |].
  repeat constructor.
Qed.

Lemma nv_con_evaluates : · ⊢ᶜ nv_con ⇓ᶜ ELit true.
Proof.
  unfold eval_con, nv_con.
  eapply Eval_Case; [eapply Eval_Con; reflexivity |].
  simpl. eapply FoldAlts_Con; [reflexivity | reflexivity | apply Eval_Lit].
Qed.

Lemma nv_budget_total : budget_total nv_phi · nv_sym.
Proof.
  exists 3%nat. intros n Hn. destruct n as [| [| [| m]]]; [lia | lia | lia |].
  destruct (self_app_has_value_at_every_budget (Datatypes.S (Datatypes.S m))
              (nv_phi ∧ PCVar nv_x) ·) as [vt Hvt].
  exists (EIf (EVar nv_x) vt nv_true).
  unfold nv_sym. eapply Eval_Case.
  - eapply Eval_If with (pc_c := PCVar nv_x);
      [apply Eval_SymVar; reflexivity | reflexivity
      | eapply Eval_Con; reflexivity | eapply Eval_Con; reflexivity].
  - simpl. eapply FoldAlts_If; [reflexivity | |].
    + eapply FoldAlts_Con; [reflexivity | reflexivity | exact Hvt].
    + eapply FoldAlts_Con; [reflexivity | reflexivity | apply Eval_Lit].
Qed.

Theorem nv_completeness_instance :
  exists h, forall n, (h <= n)%nat ->
    exists v_sym, eval (Fin n) nv_phi · nv_sym v_sym /\ contains nv_sigma nv_S v_sym nv_true.
Proof.
  exact (concore_completeness_budget nv_phi · · nv_sigma nv_S nv_sym nv_con nv_true
           nv_sigma_models_phi (Cont_Env_Empty _ _) nv_contains nv_con_concore nv_con_closed
           nv_budget_total nv_con_evaluates).
Qed.

Theorem nv_completeness_forall_instance :
  exists h, forall n, (h <= n)%nat ->
    forall v_sym, eval (Fin n) nv_phi · nv_sym v_sym -> contains nv_sigma nv_S v_sym nv_true.
Proof.
  exact (concore_completeness_forall · nv_con nv_true nv_con_evaluates nv_phi · nv_sigma nv_S nv_sym
           nv_sigma_models_phi (Cont_Env_Empty _ _) nv_contains nv_con_concore nv_con_closed).
Qed.

Theorem nv_completeness_exists_instance :
  exists k v_sym, eval (Fin k) nv_phi · nv_sym v_sym /\ contains nv_sigma nv_S v_sym nv_true.
Proof.
  exact (concore_completeness_exists nv_phi · · nv_sigma nv_S nv_sym nv_con nv_true
           nv_sigma_models_phi (Cont_Env_Empty _ _) nv_contains nv_con_concore nv_con_closed
           nv_budget_total nv_con_evaluates).
Qed.

Theorem nv_symbolic_run_diverges : forall v, ~ nv_phi ; · ⊢ nv_sym ⇓ v.
Proof.
  intros v Hv.
  pose proof (eq_refl : @sat model_sorts model_solver nv_phi = true) as Hsat.
  destruct (SymCore.eval_case_inv nv_phi · _ _ v Hsat Hv) as [es' [Hes Hfold]].
  destruct (SymCore.eval_if_inv nv_phi · _ _ _ es' Hsat Hes)
    as [ec' [et' [ef' [pc [Hc [Hpc [Ht [Hf ->]]]]]]]].
  apply (eval_var_free_inv nv_phi · nv_x ec' Hsat eq_refl) in Hc. subst ec'.
  simpl in Hpc. injection Hpc as <-.
  apply (SymCore.eval_con_same (nv_phi ∧ PCVar nv_x) · "T" et' (nv_sat _)) in Ht.
  apply (SymCore.eval_con_same (nv_phi ∧ ¬ PCVar nv_x) · "F" ef' (nv_sat _)) in Hf.
  subst et' ef'.
  destruct (fold_alts_if_some_inv Inf nv_phi · (EVar nv_x) (ECon "T") (ECon "F") nv_alts v
              (PCVar nv_x) eq_refl Hfold) as [et' [ef' [_ [Hft _]]]].
  pose proof (SymCore.fold_alts_con_inv Inf (nv_phi ∧ PCVar nv_x) · (ECon "T") nv_alts et' "T" [] [] self_app
                eq_refl eq_refl eq_refl eq_refl Hft) as Hloop.
  exact (self_app_diverges (nv_phi ∧ PCVar nv_x) _ et' (nv_sat _) Hloop).
Qed.

Theorem nv_concrete_value_unique : forall v, · ⊢ᶜ nv_con ⇓ᶜ v -> v = nv_true.
Proof.
  intros v Hv.
  exact (concore_eval_deterministic · nv_con v nv_true CEnv_Empty nv_con_concore Hv nv_con_evaluates).
Qed.

End ElseBranchLoopingThenArm.

Section PruningModel.

Fixpoint conjuncts (Φ : @path_condition model_sorts) : list path_condition :=
  match Φ with
  | PCPrim PAnd (a :: b :: nil) => conjuncts a ++ conjuncts b
  | _ => Φ :: nil
  end.

Definition refutes (cs : list (@path_condition model_sorts)) (c : path_condition) : bool :=
  match c with
  | PCVar x =>
      existsb (fun d => match d with
                        | PCPrim PNot (PCVar y :: nil) => String.eqb x y
                        | _ => false
                        end) cs
  | _ => false
  end.

Definition pruning_sat (Φ : @path_condition model_sorts) : bool :=
  negb (existsb (refutes (conjuncts Φ)) (conjuncts Φ)).

#[local] Instance pruning_solver : @SymCoreSolver model_sorts :=
  Build_SymCoreSolver
    pruning_sat (PCLit true) eq_refl model_reduce_prim
    erase_cast keep_coercion keep_type.

Fixpoint conjuncts_hold (σ : valuation) (Φ : path_condition) {struct Φ} :
  σ ⊨ Φ -> Forall (fun c => σ ⊨ c) (conjuncts Φ).
Proof.
  intros H. destruct Φ as [x | l | p args].
  - repeat constructor. exact H.
  - repeat constructor. exact H.
  - destruct p; [| repeat constructor; exact H | repeat constructor; exact H].
    destruct args as [| a [| b [| c rest]]];
      try (repeat constructor; exact H).
    unfold models in H. simpl in H. apply andb_true_iff in H as [Ha Hb].
    simpl. apply Forall_app. split; apply conjuncts_hold; assumption.
Qed.

#[local] Instance pruning_models_sat : @ModelsSat model_sorts pruning_solver.
Proof.
  intros σ Φ H.
  pose proof (conjuncts_hold σ Φ H) as Hall.
  change (negb (existsb (refutes (conjuncts Φ)) (conjuncts Φ)) = true).
  apply negb_true_iff. apply not_true_iff_false. intros Hex.
  apply existsb_exists in Hex as [c [Hc Hr]].
  destruct c as [x | l | p args]; try discriminate Hr.
  apply existsb_exists in Hr as [d [Hd Hxd]].
  destruct d as [| | q dargs]; try discriminate Hxd.
  destruct q; try discriminate Hxd.
  destruct dargs as [| [y | | ] [| ]]; try discriminate Hxd.
  apply String.eqb_eq in Hxd. subst y.
  rewrite Forall_forall in Hall.
  pose proof (Hall _ Hc) as Hx. pose proof (Hall _ Hd) as Hnx.
  unfold models in Hx, Hnx. simpl in Hx, Hnx. rewrite Hx in Hnx. discriminate Hnx.
Qed.

#[local] Instance pruning_cost_laws : @SymFCCostLaws model_sorts pruning_solver.
Proof.
  constructor.
  - constructor.
    + exact model_reduce_prim_solvable.
    + exact model_reduce_prim_saturated.
    + exact model_reduce_prim_concore.
    + exact model_cast_expr_concore.
    + exact model_reduce_prim_scoped.
    + exact model_cast_expr_scoped.
    + exact pruning_models_sat.
    + exact model_prim_value_and.
    + exact model_reduce_prim_contains.
    + exact model_reduce_prim_denote.
    + exact model_reduce_prim_ground_value.
    + exact model_cast_expr_contains.
    + exact model_subst_coerc_contains_env.
    + exact model_subst_type_contains_env.
  - exact model_cast_expr_contains_k.
  - exact model_reduce_prim_contains_k.
Qed.

Definition pm_x : var := "x".
Definition pm_S : symvars := only pm_x.
Definition pm_sigma : valuation := fun _ => true.
Definition pm_phi : path_condition := PCVar pm_x.
Definition pm_true : expr := @ELit model_sorts true.
Definition pm_sym : expr := necessity_program pm_x true true.

Lemma pm_sigma_models_phi : pm_sigma ⊨ pm_phi.
Proof. reflexivity. Qed.

Lemma pm_else_path_pruned : @sat model_sorts pruning_solver (pm_phi ∧ ¬ PCVar pm_x) = false.
Proof. reflexivity. Qed.

Lemma pm_sym_evaluates :
  @eval model_sorts pruning_solver Inf pm_phi · pm_sym (EIf (EVar pm_x) pm_true (EBot BUnreachable)).
Proof.
  unfold pm_sym, necessity_program.
  eapply Eval_If with (pc_c := PCVar pm_x).
  - apply Eval_SymVar. reflexivity.
  - reflexivity.
  - apply Eval_Lit.
  - apply Eval_Prune. exact pm_else_path_pruned.
Qed.

Lemma pm_contains : contains pm_sigma pm_S pm_sym pm_true.
Proof.
  apply Cont_If_True; [| apply Cont_Lit].
  exists (PCVar pm_x). split; [| reflexivity].
  intros Γ Hfree. simpl. rewrite (Hfree pm_x (only_self pm_x)). reflexivity.
Qed.

Lemma pm_true_closed : closed_program · pm_true.
Proof. split; [apply Scoped_Env_Empty | apply Scoped_Lit]. Qed.

Lemma pm_con_evaluates : @eval_con model_sorts pruning_solver · pm_true pm_true.
Proof. apply Eval_Lit. Qed.

Theorem pm_soundness_instance :
  exists v_con, @eval_con model_sorts pruning_solver · pm_true v_con /\
    contains pm_sigma pm_S (EIf (EVar pm_x) pm_true (EBot BUnreachable)) v_con.
Proof.
  exact (concore_soundness pm_phi · · pm_sigma pm_S pm_sym pm_true _
           pm_sigma_models_phi (Cont_Env_Empty _ _) pm_contains (Con_Lit _) pm_true_closed
           pm_sym_evaluates).
Qed.

Theorem pm_completeness_instance :
  exists h, forall n, (h <= n)%nat ->
    exists v_sym, @eval model_sorts pruning_solver (Fin n) pm_phi · pm_sym v_sym
      /\ contains pm_sigma pm_S v_sym pm_true.
Proof.
  exact (concore_completeness_budget pm_phi · · pm_sigma pm_S pm_sym pm_true pm_true
           pm_sigma_models_phi (Cont_Env_Empty _ _) pm_contains (Con_Lit _) pm_true_closed
           (budget_total_of_terminating _ _ _ (ex_intro _ _ pm_sym_evaluates))
           pm_con_evaluates).
Qed.

Theorem pm_plain_model_not_budget_total :
  ~ @budget_total model_sorts model_solver pm_phi · pm_sym.
Proof.
  exact (@budget_total_fails_on_stuck_arm model_sorts model_solver pm_phi pm_x true true
           eq_refl eq_refl).
Qed.

Theorem pm_symbolic_evaluation_not_deterministic :
  @eval model_sorts pruning_solver Inf pm_phi · (EIf (EVar pm_x) pm_true pm_true)
    (EIf (EVar pm_x) pm_true pm_true)
  /\ @eval model_sorts pruning_solver Inf pm_phi · (EIf (EVar pm_x) pm_true pm_true)
    (EIf (EVar pm_x) pm_true (EBot BUnreachable)).
Proof.
  split; eapply Eval_If with (pc_c := PCVar pm_x);
    try (apply Eval_SymVar; reflexivity); try reflexivity; try apply Eval_Lit.
  apply Eval_Prune. exact pm_else_path_pruned.
Qed.

End PruningModel.
