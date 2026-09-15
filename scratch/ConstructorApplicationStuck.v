From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

Section Scratch.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

(* Nullary constructor: a case on it works. *)
Lemma nullary_case_works : forall Γ l,
  pc_true ; Γ ⊢ ECase (ECon "D") [Alt "D" [] (ELit l)] ⇓ ELit l.
Proof.
  intros. eapply Eval_Case; [apply eval_nullary_con |].
  rewrite (merge_not_if Γ (ECon "D") eq_refl).
  eapply FoldAlts_Con with (d := "D") (ea := []) (xs := []) (ep := ELit l).
  - reflexivity.
  - simpl. destruct (string_dec "D" "D"); [reflexivity | congruence].
  - simpl. apply Eval_Lit.
Qed.

(* Applied constructor: it is a value, and its field is paired with the
   environment it was written in, unless the field is a thunk already. *)
Lemma applied_constructor_evaluates : forall Γ a,
  pc_true ; Γ ⊢ EApp (ECon "D") a ⇓ EApp (ECon "D") (delay Γ a).
Proof. intros. exact (Eval_Con _ _ Γ (EApp (ECon "D") a) "D" [a] eq_refl). Qed.

Lemma applied_constructor_value_is_unique : forall Γ a v,
  pc_true ; Γ ⊢ EApp (ECon "D") a ⇓ v -> v = EApp (ECon "D") (delay Γ a).
Proof.
  intros Γ a v H.
  exact (eval_con_spine_same pc_true Γ (EApp (ECon "D") a) "D" [a] v sat_pc_true eq_refl H).
Qed.

(* So a case on an APPLIED constructor evaluates its scrutinee and binds the
   constructor's field, as a thunk, to the pattern variable. *)
Lemma case_on_applied_constructor_binds_the_field : forall Γ l,
  pc_true ; Γ ⊢ ECase (EApp (ECon "D") (ELit l)) [Alt "D" ["y"] (EVar "y")] ⇓ ELit l.
Proof.
  intros Γ l.
  eapply Eval_Case; [apply applied_constructor_evaluates |].
  rewrite (merge_not_if Γ (EApp (ECon "D") (EThunk Γ (ELit l))) eq_refl).
  eapply FoldAlts_Con with (d := "D") (ea := [EThunk Γ (ELit l)]) (xs := ["y"]) (ep := EVar "y").
  - reflexivity.
  - simpl. destruct (string_dec "D" "D"); [reflexivity | congruence].
  - simpl. eapply Eval_Var.
    + unfold extend_env. simpl.
      destruct (string_dec "y" "y"); [reflexivity | congruence].
    + simpl. apply Eval_Thunk. apply Eval_Lit.
Qed.

End Scratch.
