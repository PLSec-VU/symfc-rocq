From SymCoreTheory Require Import SymCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

Lemma eval_preserves_if : forall Φ Γ e v,
  Φ ; Γ ⊢ e ⇓ v ->
  sat Φ = true ->
  is_if e = true ->
  is_if v = true.
Proof.
  intros Φ Γ e v Heval Hsat Hif.
  destruct e; try discriminate.
  inversion Heval; subst; [reflexivity | rewrite Hsat in *; discriminate].
Qed.

Lemma eval_app_if_false : forall Φ Γ e v,
  Φ ; Γ ⊢ e ⇓ v ->
  sat Φ = true ->
  forall ef ea, e = EApp ef ea -> is_if ef = true -> False.
Proof.
  induction 1; intros Hsat f0 a0 Heq Hif; try discriminate.
  Show.
  Show 2.
  Show 3.
  Show 4.
Abort.
