From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

Section Scratch.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

(* The overlap between Rule App-Spine and Rule App-Cast never depended on a
   lambda under the cast. While Rule App-Spine asked for an operator that is
   not a value, a cast over ANY operator that is not a value passed, an
   application just as well as a lambda.

   Rule App-Spine now asks for a computation, and no cast is one, whatever
   sits under it. *)
Lemma cast_is_not_comp : forall Γ e γ, ~ Comp Γ (ECast e γ).
Proof. intros Γ e γ H. inversion H. Qed.

Lemma application_under_cast_is_not_comp : forall Γ f a γ,
  ~ Comp Γ (ECast (EApp f a) γ).
Proof. intros Γ f a γ. apply cast_is_not_comp. Qed.

End Scratch.
