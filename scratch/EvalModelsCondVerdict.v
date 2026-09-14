From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

(**
  Why models_cond is defined the way it is in ConCore.v §9, and why
  eval_models_cond carries a sym_free_env hypothesis.

  The obvious definition of models_cond reads the condition in the empty
  environment and asks the model to satisfy the formula:

      exists pc, expr_to_pc · e = Some pc /\ σ ⊨ pc

  It is wrong, and this file shows exactly how. Rule Var lets a condition
  that IS a formula evaluate to something that is NOT one, as soon as the
  ambient environment binds the variable the condition tests. Then
  eval_models_cond, which was harmless while models_cond was abstract,
  proves that no model satisfies any variable atom at all.

  Both theorems below are stated as implications from the axiom shape, so
  nothing here is assumed: each says "if you adopt that shape, here is what
  it costs".
*)

(* ==================================================================== *)
(* 1. The environment-free definition empties out models.               *)
(* ==================================================================== *)

Definition naive_models_cond (σ : valuation) (S : symvars) (e : expr) : Prop :=
  exists pc, expr_to_pc · e = Some pc /\ σ ⊨ pc.

(** eval_models_cond, verbatim, read at the naive definition. *)
Definition NaiveEvalModelsCond : Prop := forall Φ Γ S ec ec' σ,
  σ ⊨ Φ -> Φ ; Γ ⊢ ec ⇓ ec' ->
  naive_models_cond σ S ec -> naive_models_cond σ S ec'.

(** The witness: an environment that binds the tested variable to a bottom. *)
Definition binds_to_bottom (x : var) : environment :=
  ExtendEnv x (MkClosure · (EBot BUndefined)) ·.

Lemma condition_evaluates_out_of_the_formulas : forall x,
  (PCVar x) ; (binds_to_bottom x) ⊢ EVar x ⇓ EBot BUndefined.
Proof.
  intros x. eapply Eval_Var with (Γ' := ·) (e := EBot BUndefined).
  - unfold binds_to_bottom. simpl. destruct (string_dec x x); congruence.
  - apply Eval_Bot.
Qed.

Theorem naive_definition_collapses_models :
  NaiveEvalModelsCond -> forall σ x, ~ (σ ⊨ PCVar x).
Proof.
  intros HE σ x Hmod.
  assert (Hin : naive_models_cond σ (fun _ => true) (EVar x))
    by (exists (PCVar x); split; [reflexivity | exact Hmod]).
  destruct (HE (PCVar x) (binds_to_bottom x) (fun _ => true)
               (EVar x) (EBot BUndefined) σ Hmod
               (condition_evaluates_out_of_the_formulas x) Hin) as [pc [Hpc _]].
  simpl in Hpc. discriminate.
Qed.

(** So §11(a) would die outright: no model satisfies any variable atom. *)
Corollary naive_definition_kills_symvar_atom :
  NaiveEvalModelsCond -> ~ (exists σ x, σ ⊨ PCVar x).
Proof.
  intros HE [σ [x H]]. exact (naive_definition_collapses_models HE σ x H).
Qed.

(* ==================================================================== *)
(* 2. With the real definition, the scope hypothesis is what saves it.  *)
(* ==================================================================== *)

(** ConCore's models_cond, but with eval_models_cond's sym_free_env
    hypothesis dropped. The same collapse returns. *)
Definition EvalModelsCondWithoutScope : Prop := forall Φ Γ S ec ec' σ,
  σ ⊨ Φ -> Φ ; Γ ⊢ ec ⇓ ec' -> models_cond σ S ec -> models_cond σ S ec'.

Theorem scope_hypothesis_is_necessary :
  EvalModelsCondWithoutScope -> forall σ x, ~ (σ ⊨ PCVar x).
Proof.
  intros HE σ x Hmod.
  assert (Hin : models_cond σ (only x) (EVar x)).
  { exists (PCVar x). split; [| exact Hmod].
    intros Γ Hfree. simpl. rewrite (Hfree x (only_self x)). reflexivity. }
  destruct (HE (PCVar x) (binds_to_bottom x) (only x)
               (EVar x) (EBot BUndefined) σ Hmod
               (condition_evaluates_out_of_the_formulas x) Hin) as [pc [Hden _]].
  specialize (Hden · (sym_free_env_empty _)). simpl in Hden. discriminate.
Qed.

(** With the hypothesis present, ConCore.eval_models_cond_residue shows the
    only evaluation rule left to assume anything about is App-Prim. *)
