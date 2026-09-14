From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

(* Nullary constructor: does a case on it work? *)
Lemma nullary_case_works : forall Γ l,
  pc_true ; Γ ⊢ ECase (ECon "D") [Alt "D" [] (ELit l)] ⇓ ELit l.
Proof.
  intros. eapply Eval_Case; [apply Eval_Con |].
  apply merge_fold_alts_equiv.
  eapply FoldAlts_Con with (d := "D") (ea := []) (xs := []) (ep := ELit l).
  - reflexivity.
  - simpl. destruct (string_dec "D" "D"); [reflexivity | congruence].
  - simpl. apply Eval_Lit.
Qed.

(* Applied constructor: can it be built at all? *)
Lemma applied_constructor_is_stuck : forall Γ a v,
  pc_true ; Γ ⊢ EApp (ECon "D") a ⇓ v -> False.
Proof. intros. eapply eval_app_con_false; eassumption. Qed.

(* So a case on an APPLIED constructor cannot evaluate its scrutinee. *)
Lemma case_on_applied_constructor_stuck : forall Γ a alts v,
  pc_true ; Γ ⊢ ECase (EApp (ECon "D") a) alts ⇓ v -> False.
Proof.
  intros Γ a alts v H. inversion H; subst.
  - eapply eval_app_con_false; eassumption.
  - rewrite sat_pc_true in *; discriminate.
Qed.
