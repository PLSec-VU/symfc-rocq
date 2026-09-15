From SymCoreTheory Require Import SymCore ConCore Model.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition tt : @expr model_sorts := ELit true.
Definition ff : @expr model_sorts := ELit false.
Definition guard_fun : @expr model_sorts := ELam "g" (EIf (EVar "g") tt ff).
Definition guard_program : @expr model_sorts := EApp guard_fun (EVar "x").

Definition binds_g : @environment model_sorts := ExtendEnv "g" (MkClosure · ff) ·.

Theorem guard_fun_has_no_instance : forall σ S e, ~ contains σ S guard_fun e.
Proof.
  intros σ S e H. inversion H; subst.
  - match goal with
    | [ Hg : S "g" = false, Hb : contains _ _ (EIf _ _ _) _ |- _ ] =>
        assert (Hfree : sym_free_env S binds_g)
          by (intros y Hy; simpl; destruct (string_dec y "g");
              [subst; rewrite Hg in Hy; discriminate Hy | reflexivity]);
        destruct (contains_if_inv σ S _ _ _ _ Hb) as [[[pc [Hd _]] _] | [[pc [Hd _]] _]];
        specialize (Hd binds_g Hfree); discriminate Hd
    end.
  - match goal with [ Hu : unspool_app _ _ = (EPrimOp _, _) |- _ ] => discriminate Hu end.
Qed.

Theorem guard_program_has_no_instance : forall σ S e, ~ contains σ S guard_program e.
Proof.
  intros σ S e H. inversion H; subst.
  - match goal with
    | [ Hf : contains _ _ guard_fun _ |- _ ] => exact (guard_fun_has_no_instance σ S _ Hf)
    end.
  - match goal with [ Hu : unspool_app _ _ = (EPrimOp _, _) |- _ ] => discriminate Hu end.
Qed.

Theorem guard_program_evaluates :
  @eval model_sorts model_solver Inf pc_true · guard_program (EIf (EVar "x") tt ff).
Proof.
  unfold guard_program, guard_fun.
  eapply Eval_AppSpine; [apply Comp_Lam | apply Eval_Lam |].
  apply Eval_AppAbs.
  eapply Eval_If with (pc_c := PCVar "x").
  - eapply Eval_Var; [reflexivity | apply Eval_SymVar; reflexivity].
  - reflexivity.
  - apply Eval_Lit.
  - apply Eval_Lit.
Qed.
