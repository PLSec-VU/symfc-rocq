From SymCoreTheory Require Import SymCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

(* The axiom fold_alts_no_nested_if says that whenever fold_alts accepts a
   scrutinee whose spine head is a branch, that head IS the whole scrutinee.
   Rule FoldAlts_Otherwise contradicts this: it accepts every scrutinee that
   is not itself a branch, not a bottom, and has no matching alternative -
   including an application whose operator is a branch. *)

Definition nested_if : expr := EIf (EVar "x") (EBot BUndefined) (EBot BUndefined).
Definition applied_if : expr := EApp nested_if (EBot BUndefined).

Lemma applied_if_folds :
  fold_alts Inf (PCVar "p") EmptyEnv applied_if [] (EBot BUndefined).
Proof.
  apply FoldAlts_Otherwise.
  - reflexivity.
  - unfold decompose_con_app. simpl. exact I.
  - reflexivity.
Qed.

Lemma applied_if_head : unspool_app applied_if [] = (nested_if, [EBot BUndefined]).
Proof. reflexivity. Qed.

(* The axiom is therefore inconsistent: the development proves False. *)
Lemma fold_alts_no_nested_if_gives_false : False.
Proof.
  pose proof (fold_alts_no_nested_if (PCVar "p") EmptyEnv applied_if []
                (EBot BUndefined) applied_if_folds
                nested_if [EBot BUndefined] applied_if_head eq_refl) as H.
  unfold applied_if, nested_if in H. discriminate H.
Qed.

(* Nothing but that one axiom is used. *)
Print Assumptions fold_alts_no_nested_if_gives_false.
