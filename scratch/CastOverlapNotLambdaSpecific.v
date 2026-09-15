From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

Section Scratch.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

(* Whnf of a cast is exactly Whnf of what is under it. *)
Lemma whnf_cast_inv : forall Γ e γ, Whnf Γ (ECast e γ) -> Whnf Γ e.
Proof. intros Γ e γ H. inversion H; subst; [inversion H0 | no_con_head | assumption]. Qed.

Lemma not_whnf_cast : forall Γ e γ, ~ Whnf Γ e -> ~ Whnf Γ (ECast e γ).
Proof. intros Γ e γ Hn H. apply Hn. eapply whnf_cast_inv; eauto. Qed.

(* So Eval_AppSpine's WHNF premise is satisfied for a cast over ANY non-WHNF
   operator -- no lambda need appear under the cast.  An application in
   the operator position does just as well.

   This is why the repair guards Eval_AppSpine on the COERCION instead: what
   sits under the cast is beside the point, and only the coercion says
   whether Rule App-Cast owns the application. *)
Lemma application_under_cast_is_not_whnf : forall Γ f a γ,
  is_op_app (EApp f a) = false ->
  is_con_app (EApp f a) = false ->
  ~ Whnf Γ (ECast (EApp f a) γ).
Proof.
  intros Γ f a γ Hop Hcon. apply not_whnf_cast.
  exact (not_op_app_not_whnf Γ f a Hop Hcon).
Qed.

End Scratch.
