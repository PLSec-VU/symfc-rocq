From SymCoreTheory Require Export Model.Model NonVacuity.SelfApplication.
From Stdlib Require Import Strings.String Lists.List Lia.
Import ListNotations.

Definition literal_applied_to_literal : expr := EApp (ELit true) (ELit true).

Lemma app_lit_stuck_above_one : forall n,
  ~ exists v, eval (Fin (S (S n))) pc_true EmptyEnv literal_applied_to_literal v.
Proof.
  intros n [v H].
  inversion H as [| | | | | f Φ Γ ef ea vf w Hfun Happ | | | | | | | f Φ Γ e Hpruned |];
    subst; [| discriminate Hpruned].
  inversion Hfun as [| f Φ Γ l | | | | | | | | | | | f Φ Γ e Hpruned |]; subst;
    [| discriminate Hpruned].
  inversion Happ.
Qed.

Theorem app_lit_stuck :
  ~ exists v, eval (Fin 2) pc_true EmptyEnv (EApp (ELit true) (ELit true)) v.
Proof. exact (app_lit_stuck_above_one 0). Qed.

Theorem app_lit_not_budget_total :
  ~ budget_total pc_true EmptyEnv (EApp (ELit true) (ELit true)).
Proof.
  intros [h Hh]. apply (app_lit_stuck_above_one h). apply Hh. lia.
Qed.
