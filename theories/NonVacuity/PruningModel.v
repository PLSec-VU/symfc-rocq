From SymCoreTheory Require Export NonVacuity.LoopingArm.
From Stdlib Require Import Strings.String Lists.List Lia Arith.PeanoNat Bool.Bool Arith.Wf_nat.
Import ListNotations.

Section ConCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}
  {reduce_prim_solvable_law : ReducePrimSolvable}
  {reduce_prim_saturated_law : ReducePrimSaturated}
  {reduce_prim_concore_law : ReducePrimConcore} {cast_expr_concore_law : CastExprConcore}
  {reduce_prim_scoped_law : ReducePrimScoped} {cast_expr_scoped_law : CastExprScoped}
  {models_sat_law : ModelsSat} {prim_value_and_law : PrimValueAnd}.
Context {reduce_prim_contains_law : ReducePrimContains}
  {reduce_prim_denote_law : ReducePrimDenote}
  {reduce_prim_ground_value_law : ReducePrimGroundValue}.
Context {cast_expr_contains_law : CastExprContains}.
Context {reduce_prim_ite_wellformed_law : ReducePrimIteWellformed}.
Context {subst_coerc_contains_env_law : SubstCoercContainsEnv}
  {subst_type_contains_env_law : SubstTypeContainsEnv}.
(** The same at a positive budget. Rule Out-Of-Fuel fires at Fin 0 only, so
    it cannot rescue the stuck application here. *)
Lemma app_lit_no_value_fin : forall k Ψ Γ l a v,
  sat Ψ = true -> eval (Fin (Datatypes.S k)) Ψ Γ (EApp (ELit l) a) v -> False.
Proof.
  intros k Ψ Γ l a v Hsat Heval.
  inversion Heval; subst; app_rule_absurd.
Qed.

Lemma eval_symvar_fin_same : forall k Ψ Γ x v,
  lookup_env Γ x = None -> sat Ψ = true ->
  eval (Fin (Datatypes.S k)) Ψ Γ (EVar x) v -> v = EVar x.
Proof.
  intros k Ψ Γ x v Hnone Hsat Heval.
  inversion Heval; subst; [congruence | reflexivity | no_con_head | congruence].
Qed.
End ConCore.

Section Completeness.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.
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

End BudgetTotalIsNecessary.
End Completeness.
Open Scope string_scope.

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
    + exact model_reduce_prim_keeps_out_of_fuel.
    + exact model_cast_expr_keeps_out_of_fuel.
    + exact pruning_models_sat.
    + exact model_prim_value_and.
    + exact model_reduce_prim_contains.
    + exact model_reduce_prim_denote.
    + exact model_reduce_prim_ground_value.
    + exact model_cast_expr_contains.
    + exact model_reduce_prim_ite_wellformed.
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

Definition pm_bot : expr := @EBot model_sorts BOutOfFuel.
Definition pm_unreach : expr := @EBot model_sorts BUnreachable.
Definition pm_stuck : expr := EApp pm_true pm_true.

Definition pm_stop (v : expr) : Prop := v = pm_bot \/ v = pm_unreach.

Definition pm_terms (e : expr) : Prop :=
  e = pm_sym \/ e = @EVar model_sorts pm_x \/ e = pm_true \/ e = pm_stuck \/
  e = EApp pm_bot pm_true \/ e = EApp pm_unreach pm_true \/
  e = pm_bot \/ e = pm_unreach.

Ltac pm_pick :=
  unfold pm_stop, pm_bot, pm_unreach, pm_true, pm_stuck, pm_terms, pm_sym,
    necessity_program, necessity_stuck_arm;
  repeat (first [ left; reflexivity | right ]); reflexivity.

Ltac pm_live_fuel n :=
  match goal with [ Hf : Live ?f = Fin n |- _ ] =>
    destruct f as [| m]; [destruct n; discriminate Hf |] end.

Lemma pm_symbolic_program : symbolic_program pm_S · pm_sym.
Proof.
  split; [apply SymScoped_Env_Empty |].
  unfold pm_sym, necessity_program, necessity_stuck_arm.
  apply SymScoped_If;
    [apply SymScoped_Var; right; apply only_self | apply SymScoped_Lit |].
  apply SymScoped_App; apply SymScoped_Lit.
Qed.

Lemma pm_lit_values : forall Φ n Γ (b : bool) v,
  @eval model_sorts pruning_solver (Fin n) Φ Γ (ELit b) v ->
  v = @ELit model_sorts b \/ pm_stop v.
Proof.
  intros Φ n Γ b v H. inversion H; subst; try (simpl in *; discriminate); pm_pick.
Qed.

Lemma pm_var_values : forall Φ n Γ z v,
  @eval model_sorts pruning_solver (Fin n) Φ Γ (EVar z) v -> lookup_env Γ z = None ->
  v = @EVar model_sorts z \/ pm_stop v.
Proof.
  intros Φ n Γ z v H Hl. inversion H; subst; try (simpl in *; discriminate);
    try congruence; pm_pick.
Qed.

Lemma pm_bot_values : forall Φ n Γ b v,
  @eval model_sorts pruning_solver (Fin n) Φ Γ (@EBot model_sorts b) v ->
  v = @EBot model_sorts b \/ pm_stop v.
Proof.
  intros Φ n Γ b v H. inversion H; subst; try (simpl in *; discriminate); pm_pick.
Qed.

Lemma pm_appbot_values : forall Φ n Γ b u v,
  @eval model_sorts pruning_solver (Fin n) Φ Γ (EApp (@EBot model_sorts b) u) v ->
  v = @EBot model_sorts b \/ pm_stop v.
Proof.
  intros Φ n Γ b u v H. inversion H; subst; try sym_absurd;
    try (simpl in *; discriminate); pm_pick.
Qed.

Lemma pm_stuck_values : forall Φ n Γ v,
  @eval model_sorts pruning_solver (Fin n) Φ Γ pm_stuck v -> pm_stop v.
Proof.
  intros Φ n Γ v H. unfold pm_stuck, pm_true in H.
  inversion H; subst; try sym_absurd; try (simpl in *; discriminate); pm_pick.
Qed.

Lemma pm_sym_values : forall Φ n v,
  @eval model_sorts pruning_solver (Fin n) Φ · pm_sym v ->
  (exists t f, v = EIf (@EVar model_sorts pm_x) t f
     /\ (t = pm_true \/ pm_stop t) /\ pm_stop f) \/ pm_stop v.
Proof.
  intros Φ n v H. unfold pm_sym, necessity_program in H.
  inversion H; subst; try (simpl in *; discriminate); try (right; pm_pick).
  pm_live_fuel n.
  match goal with [ Hc : eval _ _ · (EVar pm_x) ?w |- _ ] =>
    destruct (pm_var_values Φ m · pm_x w Hc eq_refl) as [-> | Hst] end.
  - match goal with [ Hf : eval _ _ · (necessity_stuck_arm true) ?w |- _ ] =>
      pose proof (pm_stuck_values _ m · w Hf) as Hstf end.
    match goal with [ Ht : eval _ _ · (ELit true) ?t |- _ ] =>
      destruct (pm_lit_values _ m · true t Ht) as [-> | Hstt] end.
    + left. eexists; eexists.
      split; [reflexivity | split; [left; reflexivity | exact Hstf]].
    + left. eexists; eexists.
      split; [reflexivity | split; [right; exact Hstt | exact Hstf]].
  - exfalso. destruct Hst as [-> | ->];
      match goal with [ Hpc : expr_to_pc · _ = Some _ |- _ ] =>
        unfold pm_bot, pm_unreach in Hpc; simpl in Hpc; discriminate Hpc end.
Qed.

Lemma pm_merge_bound : forall t f,
  (t = pm_true \/ pm_stop t) -> pm_stop f ->
  smt_size (@merge model_sorts pruning_solver · (EIf (@EVar model_sorts pm_x) t f)) <= 8.
Proof.
  intros t f [-> | [-> | ->]] [-> | ->]; vm_compute; lia.
Qed.

Definition pm_reach (st : sym_state) : Prop :=
  match st with
  | SEval Γ e => Γ = · /\ pm_terms e
  | SFold _ _ _ => False
  end.

Ltac pm_cases H :=
  destruct H as [-> He];
  cbv beta delta [pm_terms] in He;
  repeat match goal with [ Hx : _ \/ _ |- _ ] => destruct Hx end;
  subst;
  unfold pm_sym, necessity_program, necessity_stuck_arm, pm_stuck, pm_true,
    pm_bot, pm_unreach in *.

Ltac pm_split := split; [reflexivity | pm_pick].

Lemma pm_reach_step : forall Φ st Φ' st',
  pm_reach st -> @sym_step model_sorts pruning_solver Φ st Φ' st' -> pm_reach st'.
Proof.
  intros Φ st Φ' st' Hr Hstep.
  destruct Hstep; simpl in Hr |- *; try contradiction.
  - pm_cases Hr; discriminate.
  - pm_cases Hr; discriminate.
  - pm_cases Hr; discriminate.
  - pm_cases Hr; try discriminate;
      match goal with [ Hd : EApp _ _ = EApp _ _ |- _ ] => injection Hd as -> -> end;
      pm_split.
  - pm_cases Hr; try discriminate;
      match goal with [ Hd : EApp _ _ = EApp _ _ |- _ ] => injection Hd as -> -> end;
      [ destruct (pm_lit_values Φ n · true _ H) as [-> | [-> | ->]]
      | destruct (pm_bot_values Φ n · BOutOfFuel _ H) as [-> | [-> | ->]]
      | destruct (pm_bot_values Φ n · BUnreachable _ H) as [-> | [-> | ->]] ];
      pm_split.
  - pm_cases Hr; simpl in H; injection H as <- <-; simpl in H0;
      repeat (destruct H0 as [<- | H0]); try contradiction; pm_split.
  - pm_cases Hr; discriminate.
  - pm_cases Hr; try discriminate;
      match goal with [ Hd : EApp _ _ = EApp _ _ |- _ ] => injection Hd as -> -> end;
      simpl in H; discriminate H.
  - pm_cases Hr; discriminate.
  - pm_cases Hr; try discriminate;
      match goal with [ Hd : EIf _ _ _ = EIf _ _ _ |- _ ] =>
        injection Hd as -> -> -> end; pm_split.
  - pm_cases Hr; try discriminate;
      match goal with [ Hd : EIf _ _ _ = EIf _ _ _ |- _ ] =>
        injection Hd as -> -> -> end; pm_split.
  - pm_cases Hr; try discriminate;
      match goal with [ Hd : EIf _ _ _ = EIf _ _ _ |- _ ] =>
        injection Hd as -> -> -> end; pm_split.
  - pm_cases Hr; discriminate.
  - pm_cases Hr; discriminate.
Qed.

Lemma pm_reach_closed : forall Φ st Φ' st',
  pm_reach st -> @sym_reach model_sorts pruning_solver Φ st Φ' st' -> pm_reach st'.
Proof.
  intros Φ st Φ' st' Hr Hre. induction Hre; [exact Hr |].
  exact (IHHre (pm_reach_step Φ st Φ1 st1 Hr H)).
Qed.

Theorem pm_smt_bounded : @smt_bounded_run model_sorts pruning_solver pm_phi · pm_sym.
Proof.
  exists 8. intros Φ' Γ' e' n v Hre Hev.
  assert (Hr0 : pm_reach (SEval · pm_sym))
    by (simpl; split; [reflexivity | unfold pm_terms; tauto]).
  pose proof (pm_reach_closed pm_phi _ Φ' _ Hr0 Hre) as Hr.
  simpl in Hr. destruct Hr as [-> He]. unfold pm_terms in He.
  destruct He as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
  - destruct (pm_sym_values Φ' n v Hev) as [[t [f [-> [Ht Hf]]]] | [-> | ->]];
      [exact (pm_merge_bound t f Ht Hf) | vm_compute; lia | vm_compute; lia].
  - destruct (pm_var_values Φ' n · pm_x v Hev eq_refl) as [-> | [-> | ->]];
      vm_compute; lia.
  - destruct (pm_lit_values Φ' n · true v Hev) as [-> | [-> | ->]]; vm_compute; lia.
  - destruct (pm_stuck_values Φ' n · v Hev) as [-> | ->]; vm_compute; lia.
  - destruct (pm_appbot_values Φ' n · BOutOfFuel _ v Hev) as [-> | [-> | ->]];
      vm_compute; lia.
  - destruct (pm_appbot_values Φ' n · BUnreachable _ v Hev) as [-> | [-> | ->]];
      vm_compute; lia.
  - destruct (pm_bot_values Φ' n · BOutOfFuel v Hev) as [-> | [-> | ->]]; vm_compute; lia.
  - destruct (pm_bot_values Φ' n · BUnreachable v Hev) as [-> | [-> | ->]]; vm_compute; lia.
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
           pm_symbolic_program pm_sym_evaluates).
Qed.

Theorem pm_completeness_instance :
  exists h, forall n, (h <= n)%nat ->
    exists v_sym, @eval model_sorts pruning_solver (Fin n) pm_phi · pm_sym v_sym
      /\ contains pm_sigma pm_S v_sym pm_true.
Proof.
  exact (concore_completeness_budget pm_phi · · pm_sigma pm_S pm_sym pm_true pm_true
           pm_sigma_models_phi (Cont_Env_Empty _ _) pm_contains (Con_Lit _) pm_true_closed
           pm_symbolic_program pm_smt_bounded
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
