From SymCoreTheory Require Import SymCore ConCore Model.
From Stdlib Require Import Strings.String Lists.List Bool.Bool.
Import ListNotations.

Section ConThunkField.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Definition field_binder : var := "y"%string.
Definition field_env : environment := ExtendEnv field_binder (MkClosure · (ECon "E"%string)) ·.
Definition field_thunk : expr := EThunk field_env (ECon "E"%string).
Definition branch_field_program (c : expr) : expr :=
  EApp (ECon "D"%string) (EIf c field_thunk field_thunk).
Definition thunk_field_program : expr := EApp (ECon "D"%string) field_thunk.

Definition SoundnessStatement : Prop :=
  forall Φ Γs Γc σ S e_sym e_con v_sym,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    concore_expr e_con ->
    Φ ; Γs ⊢ e_sym ⇓ v_sym ->
    exists v_con, Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S v_sym v_con.

Lemma branch_field_contains_thunk_field : forall σ S c,
  S field_binder = false -> models_cond σ S c ->
  contains σ S (branch_field_program c) thunk_field_program.
Proof.
  intros σ S c Hy Hc.
  apply Cont_App; [apply Cont_Con |].
  apply Cont_If_True; [exact Hc |].
  apply Cont_Thunk; [| apply Cont_Con].
  apply Cont_Env_Extend;
    [exact Hy | apply Cont_Env_Empty | apply Cont_Con | apply Con_Con | apply Cont_Env_Empty].
Qed.

Lemma thunk_field_program_concore : concore_expr thunk_field_program.
Proof. repeat constructor. Qed.

Lemma branch_field_symbolic_value : forall Φ c,
  Φ ; · ⊢ branch_field_program c
    ⇓ EApp (ECon "D"%string) (EThunk · (EIf c field_thunk field_thunk)).
Proof.
  intros Φ c.
  exact (Eval_Con Unlimited Φ · (branch_field_program c) "D"%string
           (EIf c field_thunk field_thunk :: nil) eq_refl).
Qed.

Lemma thunk_field_concrete_value : forall v,
  · ⊢ᶜ thunk_field_program ⇓ᶜ v -> v = thunk_field_program.
Proof.
  intros v Hv. unfold eval_con in Hv.
  exact (eval_con_spine_same pc_true · thunk_field_program "D"%string
           (field_thunk :: nil) v sat_pc_true eq_refl Hv).
Qed.

Lemma symbolic_value_misses_concrete_value : forall σ S c,
  ~ contains σ S (EApp (ECon "D"%string) (EThunk · (EIf c field_thunk field_thunk)))
                 thunk_field_program.
Proof.
  intros σ S c Hcv.
  inversion Hcv as [| | | | | | | | f_s a_s f_c a_c Hf Ha | | | | | | | ]; subst.
  unfold field_thunk in Ha.
  inversion Ha as [| | | | | | | | | | Γs0 Γc0 es0 ec0 Henv Hes | | | | |]; subst.
  inversion Henv.
Qed.

Theorem con_thunk_field_breaks_soundness : forall σ S c,
  S field_binder = false -> models_cond σ S c -> ~ SoundnessStatement.
Proof.
  intros σ S c Hy Hc Hsound.
  pose proof (branch_field_contains_thunk_field σ S c Hy Hc) as Hcont.
  destruct Hc as [pc [_ Hm]].
  destruct (Hsound pc · · σ S _ thunk_field_program _ Hm (Cont_Env_Empty _ _) Hcont
              thunk_field_program_concore (branch_field_symbolic_value pc c))
    as [v [Hv Hcv]].
  rewrite (thunk_field_concrete_value v Hv) in Hcv.
  exact (symbolic_value_misses_concrete_value σ S c Hcv).
Qed.

End ConThunkField.

Definition guard_var : var := "x"%string.
Definition guard_symvars : symvars := fun y => String.eqb y guard_var.
Definition guard_model : @valuation model_sorts := fun _ => true.

Lemma guard_is_modelled : @models_cond model_sorts guard_model guard_symvars (EVar guard_var).
Proof.
  exists (PCVar guard_var). split; [| reflexivity].
  intros Γ Hfree. simpl. rewrite (Hfree guard_var eq_refl). reflexivity.
Qed.

Theorem model_con_thunk_field_breaks_soundness :
  ~ @SoundnessStatement model_sorts model_solver.
Proof.
  exact (con_thunk_field_breaks_soundness guard_model guard_symvars (EVar guard_var)
           eq_refl guard_is_modelled).
Qed.

Print Assumptions con_thunk_field_breaks_soundness.
Print Assumptions model_con_thunk_field_breaks_soundness.
