From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

(* A malformed application is stuck: no rule applies, and Rule Prune cannot
   rescue it while the path condition is satisfiable. *)
Lemma app_lit_stuck : forall Φ Γ l a v,
  sat Φ = true -> Φ ; Γ ⊢ EApp (ELit l) a ⇓ v -> False.
Proof.
  intros Φ Γ l a v Hsat Heval.
  inversion Heval; subst; try discriminate.
  - apply H1. apply Whnf_Solvable. apply Solvable_Lit.
  - congruence.
Qed.

(* The counterexample.

   e_sym = if x then ? else ((l) l)      -- else branch is malformed
   e_con = ?                             -- sigma picks the then branch

   The concrete run terminates.  The symbolic one cannot even start:
   Eval_If insists on a derivation for the else branch, which is stuck,
   and Prune cannot fire because that branch is feasible. *)
Section CompletenessFailsOnPlainEval.
  Variables (Φ : path_condition) (σ : valuation) (S : symvars).
  Variables (x : var) (l : lit).

  Hypothesis Hsat    : sat Φ = true.
  Hypothesis Hfeas   : forall pc, sat (Φ ∧ ¬ pc) = true.
  Hypothesis Hchoose : models_cond σ S (EVar x).

  Definition stuck_else : expr := EApp (ELit l) (ELit l).
  Definition e_sym     : expr := EIf (EVar x) (EBot BUndefined) stuck_else.

  (* The hypotheses of concore_completeness are all met. *)
  Lemma premises_hold :
    contains σ S e_sym (EBot BUndefined)
    /\ · ⊢ᶜ EBot BUndefined ⇓ᶜ EBot BUndefined.
  Proof.
    split.
    - apply Cont_If_True; [exact Hchoose | apply Cont_Bot].
    - apply Eval_Bot.
  Qed.

  (* But no symbolic value exists at all, so the conclusion is unreachable. *)
  Theorem no_symbolic_derivation : ~ (exists v, Φ ; · ⊢ e_sym ⇓ v).
  Proof.
    intros [v Heval]. unfold e_sym in Heval.
    inversion Heval; subst.
    - (* Eval_If: the else branch must evaluate, but it is stuck *)
      eapply app_lit_stuck; [apply Hfeas | exact H8].
    - (* Eval_Prune *)
      congruence.
  Qed.
End CompletenessFailsOnPlainEval.
