From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

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
