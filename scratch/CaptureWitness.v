From SymCoreTheory Require Import SymCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

(* The Eval_Var transport obstacle, stated on SymCore alone.

   Rule Var evaluates the closure body in the STORED environment Γ', but the
   soundness conclusion must be read in the AMBIENT environment Γ. A variable
   can be unbound (hence symbolic) in Γ' and bound in Γ, so "symbolic
   variable" is not stable between the two. Witness: *)
Definition Gp : environment := EmptyEnv.                        (* stores nothing *)
Definition G  : environment :=
  ExtendEnv "y" (MkClosure EmptyEnv (EBot BUndefined))
    (ExtendEnv "x" (MkClosure Gp (EVar "y")) EmptyEnv).

Lemma capture_witness :
  lookup_env G "x" = Some (Gp, EVar "y")
  /\ lookup_env Gp "y" = None            (* "y" is SYMBOLIC in the stored env *)
  /\ lookup_env G  "y" <> None.          (* but BOUND in the ambient env *)
Proof.
  split; [reflexivity | split; [reflexivity |]].
  simpl. discriminate.
Qed.

(* And the stored body really does evaluate to the symbolic variable, so the
   value that must be re-read in G is exactly the captured one. *)
Lemma capture_value : forall Phi, Phi ; Gp ⊢ EVar "y" ⇓ EVar "y".
Proof. intros. apply Eval_SymVar. reflexivity. Qed.
