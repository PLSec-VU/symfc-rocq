From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

Section Scratch.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

(* The determinism that fold_alts_deterministic_given_eval ASSUMES. *)
Definition EvalDeterministic : Prop :=
  forall Φ Γ e v1 v2, Φ ; Γ ⊢ e ⇓ v1 -> Φ ; Γ ⊢ e ⇓ v2 -> v1 = v2.

(* It is not merely unproven: it is FALSE as soon as any path condition is
   unsatisfiable, which is the entire point of Rule Prune. *)
Theorem eval_not_deterministic :
  (exists Φ, sat Φ = false) -> ~ EvalDeterministic.
Proof.
  intros [Φ Hunsat] Hdet.
  assert (H1 : Φ ; · ⊢ EBot BUndefined ⇓ EBot BUndefined) by apply Eval_Bot.
  assert (H2 : Φ ; · ⊢ EBot BUndefined ⇓ EBot BUnreachable)
    by (apply Eval_Prune; exact Hunsat).
  specialize (Hdet _ _ _ _ _ H1 H2). discriminate.
Qed.

(* Concrete evaluation is a different question: pc_true is satisfiable, so
   Prune cannot fire and this argument says nothing about it. *)
Definition ConEvalDeterministic : Prop :=
  forall Γ e v1 v2, Γ ⊢ᶜ e ⇓ᶜ v1 -> Γ ⊢ᶜ e ⇓ᶜ v2 -> v1 = v2.

Corollary prune_cannot_refute_concrete_determinism :
  forall Γ e v, Γ ⊢ᶜ e ⇓ᶜ v -> sat pc_true = true.
Proof. intros. apply sat_pc_true. Qed.

End Scratch.
