From SymCoreTheory Require Import SymCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

(* THIS FILE MUST FAIL TO COMPILE. Its failure is the regression check that
   the fold_alts rules still reject a scrutinee that hides a branch under an
   application.

   fold_alts_no_nested_if says that whenever fold_alts accepts a scrutinee
   whose spine head is a branch, that head IS the whole scrutinee. Rule
   FoldAlts_Otherwise once contradicted this: it accepted every scrutinee that
   is not itself a branch, not a bottom, and has no matching alternative -
   including an application whose operator is a branch. The rule now reads the
   head of the scrutinee's application spine instead of the scrutinee itself,
   so it rejects that shape, and fold_alts_no_nested_if is a lemma proved from
   the five rules rather than an assumption. *)

Definition nested_if : expr := EIf (EVar "x") (EBot BUndefined) (EBot BUndefined).
Definition applied_if : expr := EApp nested_if (EBot BUndefined).

Lemma applied_if_head : unspool_app applied_if [] = (nested_if, [EBot BUndefined]).
Proof. reflexivity. Qed.

(* What is true now: no rule folds over this scrutinee at all. *)
Lemma applied_if_does_not_fold :
  forall Φ Γ alts er, ~ fold_alts Inf Φ Γ applied_if alts er.
Proof.
  intros Φ Γ alts er H. inversion H; subst; discriminate.
Qed.

(* And the statement that was an axiom now rests on nothing but the base
   signature - no propositional assumption, so no way to reach False. *)
Print Assumptions fold_alts_no_nested_if.

(* ------------------------------------------------------------------------ *)
(* The two lemmas below flipped from provable to unprovable. Everything from
   here on is expected to be rejected; that rejection is the point of the
   file. *)

Lemma applied_if_folds :
  fold_alts Inf (PCVar "p") EmptyEnv applied_if [] (EBot BUndefined).
Proof.
  apply FoldAlts_Otherwise.
  - reflexivity.
  - unfold decompose_con_app. simpl. exact I.
  - reflexivity.
Qed.

Lemma fold_alts_no_nested_if_gives_false : False.
Proof.
  pose proof (fold_alts_no_nested_if (PCVar "p") EmptyEnv applied_if []
                (EBot BUndefined) applied_if_folds
                nested_if [EBot BUndefined] applied_if_head eq_refl) as H.
  unfold applied_if, nested_if in H. discriminate H.
Qed.
