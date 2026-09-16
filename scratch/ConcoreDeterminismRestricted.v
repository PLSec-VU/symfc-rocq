From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

Section Scratch.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

(* Determinism restricted to actual ConCore programs -- the only thing the
   soundness theorem ever evaluates concretely. *)
Definition ConcoreEvalDeterministic : Prop :=
  forall Γ e v1 v2, concore_expr e ->
    Γ ⊢ᶜ e ⇓ᶜ v1 -> Γ ⊢ᶜ e ⇓ᶜ v2 -> v1 = v2.

(* Counterexample 1 does NOT survive the restriction: its term is an EIf,
   which ConCore excludes by construction. *)
Lemma ce1_term_is_not_concore : forall ec,
  ~ concore_expr (EIf ec (EBot BUndefined) (EBot BUndefined)).
Proof. intros ec H. inversion H. Qed.

(* Counterexample 2 DOES survive: every constructor it uses is ConCore. *)
Lemma ce2_term_is_concore : forall x z d γ,
  concore_expr (EApp (ECast (ELam x (ELam z (EVar x))) γ) (ECon d)).
Proof.
  intros. apply Con_App; [| apply Con_Con].
  apply Con_Cast. apply Con_Lam. apply Con_Lam. apply Con_Var.
Qed.

(* ------------------------------------------------------------------- *)
(* What the repair did to all of this.                                  *)
(* ------------------------------------------------------------------- *)

(* Counterexample 2 is no longer a counterexample. Rule App-Spine refuses
   every cast operator, because a cast is not a computation, so the term
   keeps only the value Rule App-Cast gives it. *)
Lemma ce2_term_has_one_value :
  (forall Γ0 x body γ, cast_expr (EThunk Γ0 (ELam x body)) γ = EThunk Γ0 (ELam x body)) ->
  forall v, · ⊢ᶜ EApp coerced_operator plain_operand ⇓ᶜ v ->
  v = EThunk (extend_env · "x" · coerced_operand) (ELam "z" (EVar "x")).
Proof. exact casted_application_value_unique. Qed.

(* But restricting only the EXPRESSION is still not enough. A ConCore
   expression can be a variable, and the environment is unrestricted, so it
   can bind that variable to the dead branch of counterexample 1. *)
Lemma restriction_must_reach_the_environment : forall (x y : var),
  sat (pc_true ∧ PCVar y) = false ->
  ~ ConcoreEvalDeterministic.
Proof. exact unsatisfiable_guard_in_environment_breaks_concore_determinism. Qed.

(* Restrict the environment the same way and it holds. This is the
   statement ConCore.v proves. The statement also asks the program to be closed: a free variable would
   let Rule Sym-Var and Rule Var both fire. *)
Lemma concore_determinism_in_a_concore_environment : forall Γ e v1 v2,
  concrete_env Γ -> concore_expr e -> closed_program Γ e ->
  Γ ⊢ᶜ e ⇓ᶜ v1 -> Γ ⊢ᶜ e ⇓ᶜ v2 -> v1 = v2.
Proof. exact concore_eval_deterministic. Qed.

(* A whole program starts in the empty environment, so for closed programs
   the restriction on the expression alone is enough after all. *)
Lemma concore_program_determinism : forall e v1 v2,
  concore_expr e -> closed_term e -> ⊢ᶜ e ⇓ᶜ v1 -> ⊢ᶜ e ⇓ᶜ v2 -> v1 = v2.
Proof. exact concore_eval_deterministic_top. Qed.

End Scratch.
