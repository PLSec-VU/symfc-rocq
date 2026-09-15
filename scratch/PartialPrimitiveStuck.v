From SymCoreTheory Require Import SymCore ConCore Model.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition tt : @expr model_sorts := ELit true.
Definition partial_and : @expr model_sorts := EApp (EPrimOp PAnd) tt.
Definition apply_to_true : @expr model_sorts := ELam "f" (EApp (EVar "f") tt).
Definition partial_program : @expr model_sorts := EApp apply_to_true partial_and.
Definition eta_and : @expr model_sorts := ELam "y" (EApp (EApp (EPrimOp PAnd) tt) (EVar "y")).
Definition eta_program : @expr model_sorts := EApp apply_to_true eta_and.

Lemma partial_program_concore : concore_expr partial_program.
Proof. repeat constructor. Qed.

Lemma partial_and_stuck : forall Γ v, ~ Γ ⊢ᶜ partial_and ⇓ᶜ v.
Proof.
  intros Γ v H. unfold eval_con, partial_and in H.
  inversion H; subst.
  - match goal with [ Hu : unspool_app _ _ = (ECon _, _) |- _ ] => discriminate Hu end.
  - match goal with [ Hc : Comp _ (EPrimOp _) |- _ ] => inversion Hc end.
  - match goal with
    | [ Hu : unspool_app _ _ = (EPrimOp _, _), Hl : length _ = primop_arity _ |- _ ] =>
        simpl in Hu; injection Hu as <- <-; discriminate Hl
    end.
  - match goal with [ Hu : unspool_app _ _ = (EIf _ _ _, _) |- _ ] => discriminate Hu end.
  - match goal with [ Hs : sat _ = false |- _ ] => discriminate Hs end.
Qed.

Theorem partial_program_stuck : forall v, ~ ⊢ᶜ partial_program ⇓ᶜ v.
Proof.
  intros v H. unfold eval_con, partial_program in H.
  destruct (eval_app_spine_inv _ _ _ _ v sat_pc_true (Comp_Lam _ _ _) H) as [f1 [Hf1 Happ]].
  apply (eval_lam_inv _ _ _ _ _ sat_pc_true) in Hf1. subst f1.
  apply (eval_app_clos_inv _ _ _ _ _ _ _ sat_pc_true) in Happ.
  assert (Hcomp : Comp (extend_env · "f" · partial_and) (EVar "f"))
    by (apply Comp_Var; discriminate).
  destruct (eval_app_spine_inv _ _ _ _ v sat_pc_true Hcomp Happ) as [f2 [Hf2 _]].
  apply (eval_var_bound_inv pc_true (extend_env · "f" · partial_and) "f" · partial_and f2 sat_pc_true eq_refl) in Hf2.
  exact (partial_and_stuck · f2 Hf2).
Qed.

Theorem eta_program_evaluates : ⊢ᶜ eta_program ⇓ᶜ tt.
Proof.
  unfold eval_con, eta_program, apply_to_true, eta_and.
  eapply Eval_AppSpine; [apply Comp_Lam | apply Eval_Lam |].
  apply Eval_AppAbs.
  eapply Eval_AppSpine; [apply Comp_Var; discriminate | eapply Eval_Var; [reflexivity | apply Eval_Lam] |].
  apply Eval_AppAbs.
  change (dec Unlimited) with (@Live Unlimited).
  rewrite <- (eq_refl : @reduce_prim model_sorts model_solver PAnd (tt :: tt :: nil) = tt).
  eapply Eval_AppPrim; [reflexivity | reflexivity |].
  constructor; [apply Eval_Lit |].
  constructor; [eapply Eval_Var; [reflexivity | apply Eval_Lit] | constructor].
Qed.
