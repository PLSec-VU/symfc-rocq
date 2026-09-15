From SymCoreTheory Require Import SymCore ConCore Model.
From Stdlib Require Import Strings.String Lists.List Bool.Bool.
Import ListNotations.

(* Rule Con wraps a field with delay. A field that is a branch between two
   thunks is not a thunk, so the symbolic value wraps it again in the empty
   environment. The concrete field is one of those thunks, and it keeps its
   own environment. Before Cont_Thunk_Outer, a thunk was related only to a
   thunk whose environment was related to its own, and the empty environment
   is related to nothing but itself. OldThunkInversion states that old
   reading as a hypothesis, and con_thunk_field_breaks_soundness shows that
   it refutes soundness. The rest of the file shows the current relation. *)

Section ConThunkField.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Definition field_binder : var := "y"%string.
Definition field_env : environment := ExtendEnv field_binder (MkClosure · (ECon "E"%string)) ·.
Definition field_thunk : expr := EThunk field_env (ECon "E"%string).
Definition branch_field_program (c : expr) : expr :=
  EApp (ECon "D"%string) (EIf c field_thunk field_thunk).
Definition thunk_field_program : expr := EApp (ECon "D"%string) field_thunk.
Definition branch_field_value (c : expr) : expr :=
  EApp (ECon "D"%string) (EThunk · (EIf c field_thunk field_thunk)).

Definition SoundnessStatement : Prop :=
  forall Φ Γs Γc σ S e_sym e_con v_sym,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    concore_expr e_con ->
    closed_program Γc e_con ->
    Φ ; Γs ⊢ e_sym ⇓ v_sym ->
    exists v_con, Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S v_sym v_con.

Definition OldThunkInversion (σ : valuation) (S : symvars) : Prop :=
  forall Γs es ec,
    contains σ S (EThunk Γs es) ec ->
    exists Γc ec', ec = EThunk Γc ec' /\ contains_env σ S Γs Γc /\ contains σ S es ec'.

Lemma field_thunk_contains_itself : forall σ S,
  S field_binder = false -> contains σ S field_thunk field_thunk.
Proof.
  intros σ S Hy.
  apply Cont_Thunk; [| apply Cont_Con].
  apply Cont_Env_Extend;
    [exact Hy | apply Cont_Env_Empty | apply Cont_Con | apply Con_Con | apply Cont_Env_Empty].
Qed.

Lemma branch_field_contains_thunk_field : forall σ S c,
  S field_binder = false -> models_cond σ S c ->
  contains σ S (branch_field_program c) thunk_field_program.
Proof.
  intros σ S c Hy Hc.
  apply Cont_App; [apply Cont_Con |].
  apply Cont_If_True; [exact Hc | exact (field_thunk_contains_itself σ S Hy)].
Qed.

Lemma thunk_field_program_concore : concore_expr thunk_field_program.
Proof. repeat constructor. Qed.

Lemma thunk_field_program_closed : closed_program · thunk_field_program.
Proof. split; [constructor | repeat constructor]. Qed.

Lemma branch_field_symbolic_value : forall Φ c,
  Φ ; · ⊢ branch_field_program c ⇓ branch_field_value c.
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

Lemma old_symbolic_value_misses_concrete_value : forall σ S c,
  OldThunkInversion σ S ->
  ~ contains σ S (branch_field_value c) thunk_field_program.
Proof.
  intros σ S c Hold Hcv.
  inversion Hcv as [| | | | | | | | f_s a_s f_c a_c Hf Ha | | | | | | | | ]; subst.
  destruct (Hold · _ _ Ha) as [Γc [ec' [Heq [Henv _]]]].
  unfold field_thunk in Heq. injection Heq as <- <-.
  inversion Henv.
Qed.

Theorem con_thunk_field_breaks_soundness : forall σ S c,
  OldThunkInversion σ S ->
  S field_binder = false -> models_cond σ S c -> ~ SoundnessStatement.
Proof.
  intros σ S c Hold Hy Hc Hsound.
  pose proof (branch_field_contains_thunk_field σ S c Hy Hc) as Hcont.
  destruct Hc as [pc [_ Hm]].
  destruct (Hsound pc · · σ S _ thunk_field_program _ Hm (Cont_Env_Empty _ _) Hcont
              thunk_field_program_concore thunk_field_program_closed (branch_field_symbolic_value pc c))
    as [v [Hv Hcv]].
  rewrite (thunk_field_concrete_value v Hv) in Hcv.
  exact (old_symbolic_value_misses_concrete_value σ S c Hold Hcv).
Qed.

Lemma branch_field_value_contains_thunk_field : forall σ S c,
  S field_binder = false -> models_cond σ S c ->
  contains σ S (branch_field_value c) thunk_field_program.
Proof.
  intros σ S c Hy Hc.
  apply Cont_App; [apply Cont_Con |].
  apply (Cont_Thunk_Outer σ S · ·); [apply Cont_Env_Empty | | reflexivity].
  apply Cont_If_True; [exact Hc | exact (field_thunk_contains_itself σ S Hy)].
Qed.

Lemma current_contains_refutes_old_inversion : forall σ S c,
  S field_binder = false -> models_cond σ S c -> ~ OldThunkInversion σ S.
Proof.
  intros σ S c Hy Hc Hold.
  exact (old_symbolic_value_misses_concrete_value σ S c Hold
           (branch_field_value_contains_thunk_field σ S c Hy Hc)).
Qed.

Theorem thunk_field_regression : forall σ S c,
  S field_binder = false -> models_cond σ S c ->
  exists v, · ⊢ᶜ thunk_field_program ⇓ᶜ v /\ contains σ S (branch_field_value c) v.
Proof.
  intros σ S c Hy Hc.
  exists thunk_field_program. split.
  - exact (Eval_Con Unlimited pc_true · thunk_field_program "D"%string
             (field_thunk :: nil) eq_refl).
  - exact (branch_field_value_contains_thunk_field σ S c Hy Hc).
Qed.

End ConThunkField.

Section CurrentSoundness.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

Theorem thunk_field_soundness_holds : SoundnessStatement.
Proof. exact concore_soundness. Qed.

End CurrentSoundness.

Definition guard_var : var := "x"%string.
Definition guard_symvars : symvars := fun y => String.eqb y guard_var.
Definition guard_model : @valuation model_sorts := fun _ => true.

Lemma guard_is_modelled : @models_cond model_sorts guard_model guard_symvars (EVar guard_var).
Proof.
  exists (PCVar guard_var). split; [| reflexivity].
  intros Γ Hfree. simpl. rewrite (Hfree guard_var eq_refl). reflexivity.
Qed.

Theorem model_con_thunk_field_breaks_soundness :
  @OldThunkInversion model_sorts guard_model guard_symvars ->
  ~ @SoundnessStatement model_sorts model_solver.
Proof.
  intros Hold.
  exact (con_thunk_field_breaks_soundness guard_model guard_symvars (EVar guard_var)
           Hold eq_refl guard_is_modelled).
Qed.

Theorem model_current_contains_refutes_old_inversion :
  ~ @OldThunkInversion model_sorts guard_model guard_symvars.
Proof.
  exact (current_contains_refutes_old_inversion guard_model guard_symvars (EVar guard_var)
           eq_refl guard_is_modelled).
Qed.

Theorem model_thunk_field_soundness_holds : @SoundnessStatement model_sorts model_solver.
Proof. exact thunk_field_soundness_holds. Qed.

Print Assumptions con_thunk_field_breaks_soundness.
Print Assumptions thunk_field_regression.
Print Assumptions model_thunk_field_soundness_holds.
