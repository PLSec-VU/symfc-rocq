From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

Lemma fold_alts_con_inv : forall Φ Γ e d ea xs ep alts r,
  decompose_con_app e = Some (d, ea) ->
  find_alt d alts = Some (xs, ep) ->
  fold_alts Φ Γ e alts r ->
  Φ ; extend_env_multi Γ xs ea Γ ⊢ ep ⇓ r.
Proof.
  intros Φ Γ e d ea xs ep alts r Hdec Hfind Hfold.
  inversion Hfold; subst; unfold decompose_con_app in Hdec; simpl in Hdec;
    try discriminate.
  Show.
  Show 2.
Abort.
