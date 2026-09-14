From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

(* Nullary constructor: a case on it works. *)
Lemma nullary_case_works : forall Γ l,
  pc_true ; Γ ⊢ ECase (ECon "D") [Alt "D" [] (ELit l)] ⇓ ELit l.
Proof.
  intros. eapply Eval_Case; [eapply Eval_Con; reflexivity |].
  rewrite (merge_not_if Γ (ECon "D") eq_refl).
  eapply FoldAlts_Con with (d := "D") (ea := []) (xs := []) (ep := ELit l).
  - reflexivity.
  - simpl. destruct (string_dec "D" "D"); [reflexivity | congruence].
  - simpl. apply Eval_Lit.
Qed.

(* Applied constructor: it is a value, and it is its own value. *)
Lemma applied_constructor_evaluates : forall Γ a,
  pc_true ; Γ ⊢ EApp (ECon "D") a ⇓ EApp (ECon "D") a.
Proof. intros. eapply Eval_Con. reflexivity. Qed.

Lemma applied_constructor_value_is_unique : forall Γ a v,
  pc_true ; Γ ⊢ EApp (ECon "D") a ⇓ v -> v = EApp (ECon "D") a.
Proof.
  intros Γ a v H.
  eapply eval_con_spine_same; [apply sat_pc_true | reflexivity | exact H].
Qed.

(* So a case on an APPLIED constructor evaluates its scrutinee and binds the
   constructor's argument to the pattern variable. *)
Lemma case_on_applied_constructor_binds_the_field : forall Γ l,
  pc_true ; Γ ⊢ ECase (EApp (ECon "D") (ELit l)) [Alt "D" ["y"] (EVar "y")] ⇓ ELit l.
Proof.
  intros Γ l.
  eapply Eval_Case; [apply applied_constructor_evaluates |].
  rewrite (merge_not_if Γ (EApp (ECon "D") (ELit l)) eq_refl).
  eapply FoldAlts_Con with (d := "D") (ea := [ELit l]) (xs := ["y"]) (ep := EVar "y").
  - reflexivity.
  - simpl. destruct (string_dec "D" "D"); [reflexivity | congruence].
  - simpl. eapply Eval_Var.
    + unfold extend_env. simpl.
      destruct (string_dec "y" "y"); [reflexivity | congruence].
    + simpl. apply Eval_Lit.
Qed.
