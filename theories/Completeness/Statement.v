From SymCoreTheory Require Export Completeness.Reach.
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

(** ========================================================================= *)
(** Budget-Total Terms                                                    *)
(** ========================================================================= *)

(**
  A term is budget-total when every budget from some point on gives it a
  value. The value may change with the budget.

  A term that terminates is budget-total: budget_total_of_terminating below
  proves it. A term that loops can be budget-total:
  self_app_has_value_at_every_budget in NonVacuity/SelfApplication.v proves
  it for the self-application loop. A stuck term is not budget-total: it has
  no value at a positive budget. app_lit_no_value_fin in
  NonVacuity/PruningModel.v proves this for an application of a literal.

  Completeness is proved in Completeness/Completeness.v. It takes
  budget_total as a hypothesis and assumes the cost laws of
  Completeness/Cost.v.
*)
Definition budget_total (Φ : path_condition) (Γ : environment) (e : expr) : Prop :=
  exists h, forall n, (h <= n)%nat -> exists v, eval (Fin n) Φ Γ e v.

Lemma budget_total_of_terminating : forall Φ Γ e,
  (exists v, Φ ; Γ ⊢ e ⇓ v) -> budget_total Φ Γ e.
Proof.
  intros Φ Γ e [v Hv].
  destruct (eval_inf_has_budget Φ Γ e v Hv) as [h Hh].
  exists h. intros n Hn. exists v. apply Hh. exact Hn.
Qed.

End ConCore.

Section Completeness.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

Definition target_completeness : Prop :=
  forall Φ Γs Γc σ S e_sym e_con v_con,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    concore_expr e_con ->
    closed_program Γc e_con ->
    symbolic_program S Γs e_sym ->
    smt_bounded_run Φ Γs e_sym ->
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
      closed_program Γc e_con ->
      symbolic_program S Γs e_sym ->
      smt_bounded_run Φ Γs e_sym ->
      exists h, forall n, (h <= n)%nat ->
        forall v_sym, eval (Fin n) Φ Γs e_sym v_sym -> contains σ S v_sym v_con.

Definition existential_corollary : Prop :=
  forall Φ Γs Γc σ S e_sym e_con v_con,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    concore_expr e_con ->
    closed_program Γc e_con ->
    symbolic_program S Γs e_sym ->
    smt_bounded_run Φ Γs e_sym ->
    budget_total Φ Γs e_sym ->
    Γc ⊢ᶜ e_con ⇓ᶜ v_con ->
    exists k v_sym, eval (Fin k) Φ Γs e_sym v_sym /\ contains σ S v_sym v_con.

Lemma existential_corollary_of_target :
  target_completeness -> existential_corollary.
Proof.
  intros Htarget Φ Γs Γc σ S e_sym e_con v_con Hmod Henv Hcont Hcon Hcl Hsym Hbnd Hbud Hevalc.
  destruct (Htarget Φ Γs Γc σ S e_sym e_con v_con Hmod Henv Hcont Hcon Hcl Hsym Hbnd Hbud Hevalc)
    as [h Hh].
  destruct (Hh h ltac:(lia)) as [v_sym [Heval Hcv]].
  exists h, v_sym. split; assumption.
Qed.

End Completeness.
