From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

(* γ_ok  : (Int -> String) ~ (Word -> Text)   -- both sides are arrows *)
Definition g_ok : coercion :=
  MkCoercion (TyArrow (TyVar "Int")  (TyVar "String"))
             (TyArrow (TyVar "Word") (TyVar "Text"))
             RoleRepresentational.

(* γ_bad : Int ~ Word                          -- neither side is an arrow *)
Definition g_bad : coercion :=
  MkCoercion (TyVar "Int") (TyVar "Word") RoleRepresentational.

Definition g_dom : coercion := MkCoercion (TyVar "Int") (TyVar "Word") RoleRepresentational.
Definition g_cod : coercion := MkCoercion (TyVar "String") (TyVar "Text") RoleRepresentational.

Lemma ok_splits  : decomp_coerc_arrow g_ok  = Some (g_dom, g_cod).
Proof. reflexivity. Qed.

Lemma bad_splits : decomp_coerc_arrow g_bad = None.
Proof. reflexivity. Qed.

Definition fn : expr := ELam "y" (EVar "y").

(* Both operators are casts, so Rule App-Spine refuses both. *)
Lemma both_refused_by_app_spine : is_cast (ECast fn g_ok) = true /\ is_cast (ECast fn g_bad) = true.
Proof. split; reflexivity. Qed.

(* The good one: Rule App-Cast applies, and its premise is the pushed term. *)
Lemma good_reduces_by_app_cast : forall Φ Γ x er,
  Φ ; Γ ⊢ ECast (EApp fn (ECast x (sym_coerc g_dom))) g_cod ⇓ er ->
  Φ ; Γ ⊢ EApp (ECast fn g_ok) x ⇓ er.
Proof. intros. eapply Eval_AppCast; [apply ok_splits | assumption]. Qed.

(* The bad one: no rule at all, at any satisfiable path condition. *)
(* The bad one: no rule at all, at any satisfiable path condition.
   App-Spine is refused because the operator is a cast; App-Cast is
   refused because g_bad does not split; every other rule wants a
   different operator; Prune wants an unsatisfiable path condition. *)
Lemma bad_is_stuck : forall Φ Γ x v,
  sat Φ = true -> ~ (Φ ; Γ ⊢ EApp (ECast fn g_bad) x ⇓ v).
Proof.
  intros Φ Γ x v Hsat H.
  inversion H; subst; try discriminate.
  congruence.
Qed.
