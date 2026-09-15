From SymCoreTheory Require Import SymCore ConCore CostLaws Model.
From Stdlib Require Import Strings.String Lists.List Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Section LeakyCast.

Fixpoint leak (e : @expr model_sorts) : expr :=
  match e with
  | ELam z _ => EVar z
  | EThunk _ e0 => leak e0
  | EIf c t f => EIf c (leak t) (leak f)
  | _ => e
  end.

Definition leaky_cast (e : expr) (γ : coercion) : expr := leak e.

Definition leaky_solver : @SymCoreSolver model_sorts :=
  Build_SymCoreSolver
    model_sat (PCLit true) eq_refl model_reduce_prim
    leaky_cast keep_coercion keep_type.

#[local] Existing Instance leaky_solver | 0.

#[local] Instance leaky_reduce_prim_solvable : ReducePrimSolvable.
Proof. exact model_reduce_prim_solvable. Qed.
#[local] Instance leaky_reduce_prim_saturated : ReducePrimSaturated.
Proof. exact model_reduce_prim_saturated. Qed.
#[local] Instance leaky_reduce_prim_concore : ReducePrimConcore.
Proof. exact model_reduce_prim_concore. Qed.
#[local] Instance leaky_reduce_prim_scoped : ReducePrimScoped.
Proof. exact model_reduce_prim_scoped. Qed.
#[local] Instance leaky_models_sat : ModelsSat.
Proof. exact model_models_sat. Qed.
#[local] Instance leaky_prim_value_and : PrimValueAnd.
Proof. exact model_prim_value_and. Qed.
#[local] Instance leaky_reduce_prim_contains : ReducePrimContains.
Proof. exact model_reduce_prim_contains. Qed.
#[local] Instance leaky_reduce_prim_denote : ReducePrimDenote.
Proof. exact model_reduce_prim_denote. Qed.
#[local] Instance leaky_reduce_prim_ground_value : ReducePrimGroundValue.
Proof. exact model_reduce_prim_ground_value. Qed.
#[local] Instance leaky_subst_coerc_contains_env : SubstCoercContainsEnv.
Proof. exact model_subst_coerc_contains_env. Qed.
#[local] Instance leaky_subst_type_contains_env : SubstTypeContainsEnv.
Proof. exact model_subst_type_contains_env. Qed.

#[local] Instance leaky_cast_expr_concore : CastExprConcore.
Proof.
  intros e γ H. change (concore_expr (leak e)).
  induction e; try exact H.
  - apply Con_Var.
  - exfalso. exact (not_concore_if _ _ _ H).
  - simpl. apply IHe. exact (concore_expr_thunk _ _ H).
Qed.

#[local] Instance leaky_cast_expr_contains : CastExprContains.
Proof.
  intros σ S es ec γ H. change (contains σ S (leak es) (leak ec)).
  induction H; try (simpl; solve [constructor; assumption]); try assumption.
  match goal with
    | [ Hu : unspool_app es nil = _, Hg : smt_ground es = false |- _ ] =>
        destruct (cont_denote_is_app es _ _ Hu Hg) as [f [a ->]]
  end.
  simpl. eapply Cont_Denote; eassumption.
Qed.

Theorem leaky_cast_not_scoped : ~ CastExprScoped.
Proof.
  intros Hlaw.
  pose proof (Hlaw (ELam "z" (EVar "z")) (MkCoercion (TyCon tt) (TyCon tt) RoleNominal)
                (Scoped_Lam nil "z" (EVar "z") (Scoped_Var ("z" :: nil) "z" (or_introl eq_refl)))) as H.
  change (scoped nil (EVar "z")) in H.
  inversion H as [L x Hin | | | | | | | | | | | |]; subst. destruct Hin.
Qed.

Definition leak_coercion : coercion := MkCoercion (TyCon tt) (TyCon tt) RoleNominal.
Definition leak_arg : expr := ECast (ELam "z" (EVar "z")) leak_coercion.
Definition ite3 (c a b : expr) : expr := EApp (EApp (EApp (EPrimOp PIte) c) a) b.

Definition leak_sym : expr := ite3 leak_arg (EVar "y") (ELit true).
Definition leak_con : expr := ite3 leak_arg (ELit true) (ELit true).
Definition leak_sigma : valuation := fun _ => true.
Definition leak_S : symvars := only "y".
Definition leak_residual : expr := ite3 (EVar "z") (EVar "y") (ELit true).

Lemma leak_contains : contains leak_sigma leak_S leak_sym leak_con.
Proof.
  unfold leak_sym, leak_con, ite3, leak_arg.
  repeat apply Cont_App; try apply Cont_PrimOp; try apply Cont_Lit.
  - apply Cont_Cast. apply Cont_Lam; [reflexivity |]. apply Cont_Var_Bound. reflexivity.
  - apply Cont_Var_Sym. reflexivity.
Qed.

Lemma leak_con_concore : concore_expr leak_con.
Proof.
  unfold leak_con, ite3, leak_arg.
  repeat apply Con_App; try apply Con_PrimOp; try apply Con_Lit.
  apply Con_Cast. apply Con_Lam. apply Con_Var.
Qed.

Lemma leak_con_closed : closed_program · leak_con.
Proof.
  split; [apply Scoped_Env_Empty |].
  unfold leak_con, ite3, leak_arg.
  repeat apply Scoped_App; try apply Scoped_PrimOp; try apply Scoped_Lit.
  apply Scoped_Cast. apply Scoped_Lam. apply Scoped_Var. left. reflexivity.
Qed.

Lemma leak_arg_evaluates : forall Φ Γ,
  eval Inf Φ Γ leak_arg (EVar "z").
Proof.
  intros Φ Γ. unfold leak_arg.
  change (EVar "z") with (cast_expr (EThunk Γ (ELam "z" (EVar "z"))) leak_coercion).
  apply Eval_Cast. apply Eval_Lam.
Qed.

Lemma leak_sym_evaluates : PCLit true ; · ⊢ leak_sym ⇓ leak_residual.
Proof.
  unfold leak_sym.
  change leak_residual
    with (reduce_prim PIte (EVar "z" :: EVar "y" :: ELit true :: nil)).
  eapply Eval_AppPrim; [reflexivity | reflexivity |].
  constructor; [apply leak_arg_evaluates |].
  constructor; [apply Eval_SymVar; reflexivity |].
  constructor; [apply Eval_Lit | constructor].
Qed.

Lemma leak_con_evaluates : · ⊢ᶜ leak_con ⇓ᶜ ELit true.
Proof.
  unfold eval_con, leak_con.
  change (@ELit model_sorts true)
    with (reduce_prim PIte (EVar "z" :: ELit true :: ELit true :: nil)).
  eapply Eval_AppPrim; [reflexivity | reflexivity |].
  constructor; [apply leak_arg_evaluates |].
  constructor; [apply Eval_Lit |].
  constructor; [apply Eval_Lit | constructor].
Qed.

Lemma leak_residual_not_instance : ~ contains leak_sigma leak_S leak_residual (ELit true).
Proof.
  intros H. inversion H; subst.
  match goal with
  | [ Hd : denote _ _ _ _ |- _ ] =>
      destruct Hd as [pc [Hden _]];
      specialize (Hden (ExtendEnv "z" (MkClosure · (ELit true)) ·));
      assert (Hfree : sym_free_env leak_S (ExtendEnv "z" (MkClosure · (ELit true)) ·))
        by (intros w Hw; unfold leak_S, only in Hw; destruct (string_dec w "y");
            [subst; reflexivity | discriminate Hw]);
      specialize (Hden Hfree); vm_compute in Hden; discriminate Hden
  end.
Qed.

Theorem leak_argument_reaches_reduce_prim_open :
  eval Inf pc_true · leak_arg (EVar "z") /\ ~ closed_term (@EVar model_sorts "z").
Proof.
  split; [apply leak_arg_evaluates |].
  intros H. inversion H as [L x Hin | | | | | | | | | | | |]; subst. destruct Hin.
Qed.

Theorem soundness_fails_without_cast_scoped :
  leak_sigma ⊨ PCLit true /\
  contains_env leak_sigma leak_S · · /\
  contains leak_sigma leak_S leak_sym leak_con /\
  concore_expr leak_con /\
  closed_program · leak_con /\
  PCLit true ; · ⊢ leak_sym ⇓ leak_residual /\
  ~ exists v_con, · ⊢ᶜ leak_con ⇓ᶜ v_con /\ contains leak_sigma leak_S leak_residual v_con.
Proof.
  split; [reflexivity |].
  split; [apply Cont_Env_Empty |].
  split; [exact leak_contains |].
  split; [exact leak_con_concore |].
  split; [exact leak_con_closed |].
  split; [exact leak_sym_evaluates |].
  intros [v_con [Hev Hc]].
  rewrite (concore_eval_deterministic_top leak_con v_con (@ELit model_sorts true) leak_con_concore Hev
             leak_con_evaluates) in Hc.
  exact (leak_residual_not_instance Hc).
Qed.

End LeakyCast.
