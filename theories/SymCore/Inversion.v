From SymCoreTheory Require Export SymCore.Eval.
From Stdlib Require Import Lists.List.
Import ListNotations.

Section SymCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Lemma non_arrow_cast_app_stuck : forall g Φ Γ v γ e v',
  decomp_coerc_arrow γ = None -> ~ apply g Φ Γ (VCast v γ) e v'.
Proof.
  intros g Φ Γ v γ e v' Hnone Happ. inversion Happ. congruence.
Qed.

Lemma eval_spent : forall Φ Γ e v, eval Spent Φ Γ e v -> v = VBot BOutOfFuel.
Proof.
  intros Φ Γ e v Heval. inversion Heval. reflexivity.
Qed.

End SymCore.
