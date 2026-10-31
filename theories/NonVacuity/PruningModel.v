From SymCoreTheory Require Import Model.Reducer Soundness.Laws NonVacuity.SelfApplication.
From SymCoreTheory Require Model.Model.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition pruning_sat (p : prim) : bool :=
  match p with
  | PLit l => l
  | _ => true
  end.

#[local] Instance pruning_solver : SymCoreSolver :=
  @Build_SymCoreSolver model_sorts pruning_sat (PLit true) eq_refl model_reduce_prim
    VCast (fun _ γ => γ) (fun _ τ => τ).

Lemma pruning_sat_refutes_false : sat (PLit false) = false.
Proof. reflexivity. Qed.

#[local] Instance pruning_models_sat : ModelsSat.
Proof.
  intros σ Φ H. destruct Φ as [l | x | op ps]; try reflexivity. exact H.
Qed.

#[local] Instance pruning_subst_contains : SubstContains.
Proof. split; intros σ Γs Γc x _; reflexivity. Qed.

#[local] Instance pruning_model_laws : @ConCoreLaws model_sorts pruning_solver :=
  @concore_laws model_sorts pruning_solver Model.Model.model_reduce_prim_literal Model.Model.model_cast_concore
    pruning_models_sat Model.Model.model_reduce_prim_contains
    Model.Model.model_cast_contains pruning_subst_contains.

Theorem pruning_prunes_refuted_path : eval (Fin 1) (PLit false) EmptyEnv ω (VBot BUnreachable).
Proof. apply Eval_Prune. reflexivity. Qed.

Theorem app_lit_stuck :
  ~ exists v, eval (Fin 2) pc_true EmptyEnv (EApp (ELit true) (ELit true)) v.
Proof.
  intros [v H].
  inversion H as [| | | | | f Φ Γ ef ea vf w Hfun Happ | | | | | | | f Φ Γ e Hpruned |];
    subst; [| discriminate Hpruned].
  inversion Hfun as [| f Φ Γ l | | | | | | | | | | | f Φ Γ e Hpruned |]; subst;
    [| discriminate Hpruned].
  inversion Happ.
Qed.
