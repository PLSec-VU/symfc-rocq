From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

Section Scratch.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

(* Every statement here is about the unlimited budget, eval Inf, which the
   notation "Phi ; Gamma |- e ==> v" now means. The finite budgets are
   covered in scratch/DivergenceNeedsFuel.v, Section 5: at Fin 0 the program
   answers only the out-of-fuel bottom, and at every greater budget it has no
   value that contains the concrete one. *)

(* A malformed application is stuck: no rule applies, and Rule Prune cannot
   rescue it while the path condition is satisfiable. *)
Lemma app_lit_stuck : forall Φ Γ l a v,
  sat Φ = true -> Φ ; Γ ⊢ EApp (ELit l) a ⇓ v -> False.
Proof.
  exact app_lit_no_value_inf.
Qed.

(* The counterexample.

   e_sym = if x then l' else ((l) l)     -- else branch is malformed
   e_con = l'                            -- sigma picks the then branch

   The concrete run terminates.  The symbolic one cannot even start:
   Eval_If insists on a derivation for the else branch, which is stuck,
   and Prune cannot fire because that branch is feasible.

   The then branch is a LITERAL on purpose.  A uniform depth bound does
   not rescue this: at depth 0 the whole program is EBot BOutOfFuel, and
   contains (EBot BOutOfFuel) (ELit l') is false; at depth 1 the guard is
   read at depth 0, no formula reads off it, and Rule If does not fire;
   at any greater depth the stuck else arm has no derivation at all and
   out-of-fuel cannot fire.  Fuel decrements uniformly, so no single k
   gives the taken path enough depth AND the untaken arm little enough.
   Stuckness needs the EBot BUndefined fallback that fold_alts already
   has, not a bound. *)
Section CompletenessFailsOnPlainEval.
  Variables (Φ : path_condition) (σ : valuation) (S : symvars).
  Variables (x : var) (l l' : lit).

  Hypothesis Hsat    : sat Φ = true.
  Hypothesis Hfeas   : forall pc, sat (Φ ∧ ¬ pc) = true.
  Hypothesis Hchoose : models_cond σ S (EVar x).

  Definition stuck_else : expr := EApp (ELit l) (ELit l).
  Definition e_sym     : expr := EIf (EVar x) (ELit l') stuck_else.

  (* The concretion and the concrete run that completeness asks for both hold. *)
  Lemma premises_hold :
    contains σ S e_sym (ELit l')
    /\ · ⊢ᶜ ELit l' ⇓ᶜ ELit l'.
  Proof.
    split.
    - apply Cont_If_True; [exact Hchoose | apply Cont_Lit].
    - apply Eval_Lit.
  Qed.

  (* But no symbolic value exists at all, so the conclusion is unreachable. *)
  Theorem no_symbolic_derivation : ~ (exists v, Φ ; · ⊢ e_sym ⇓ v).
  Proof.
    intros [v Heval]. unfold e_sym in Heval.
    inversion Heval; subst.
    - (* Eval_Con: a branch has no constructor at the head of its spine *)
      no_con_head.
    - (* Eval_If: the else branch must evaluate, but it is stuck *)
      match goal with
      | [ H : eval _ _ _ stuck_else _ |- _ ] =>
          unfold stuck_else in H;
          eapply app_lit_stuck; [apply Hfeas | exact H]
      end.
    - (* Eval_Prune *)
      congruence.
  Qed.
End CompletenessFailsOnPlainEval.

(* Why "just don't pick the false branch" is not available.

   The symbolic evaluator never consults a model: Eval_If mentions no
   sigma at all, and its conclusion is EIf ec' et' ef', a tree carrying
   BOTH arms.  sigma enters only afterwards, in contains, to say which
   arm the concrete run corresponds to.  So the malformed arm blocks the
   symbolic derivation whatever sigma would have chosen -- there is no
   sigma in the statement below. *)
Theorem stuck_regardless_of_any_model : forall Φ x l l',
  sat Φ = true ->
  (forall pc, sat (Φ ∧ ¬ pc) = true) ->
  ~ (exists v, Φ ; · ⊢ EIf (EVar x) (ELit l') (EApp (ELit l) (ELit l)) ⇓ v).
Proof.
  intros Φ x l l' Hsat Hfeas [v Heval].
  inversion Heval; subst.
  - no_con_head.
  - match goal with
    | [ H : eval _ _ _ (EApp (ELit _) _) _ |- _ ] =>
        eapply app_lit_stuck; [apply Hfeas | exact H]
    end.
  - congruence.
Qed.

End Scratch.
