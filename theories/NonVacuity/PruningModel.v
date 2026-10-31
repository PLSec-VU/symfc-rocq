From SymCoreTheory Require Import Model.Reducer Soundness.Laws NonVacuity.SelfApplication.
From SymCoreTheory Require Import ConCore.Determinism.
From SymCoreTheory Require Model.Model.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Lia.
Import ListNotations.
Open Scope string_scope.

Fixpoint conjuncts (Φ : prim) : list prim :=
  match Φ with
  | PApp PAnd (a :: b :: nil) => conjuncts a ++ conjuncts b
  | _ => Φ :: nil
  end.

Definition negation_of (q r : prim) : bool := prim_eqb r (PApp PNot (q :: nil)).

Definition contradicts_itself (cs : list prim) : bool :=
  existsb (fun q => existsb (negation_of q) cs) cs.

Definition pruning_sat (Φ : prim) : bool := negb (contradicts_itself (conjuncts Φ)).

#[local] Instance pruning_solver : SymCoreSolver :=
  @Build_SymCoreSolver model_sorts pruning_sat (PLit true) eq_refl model_reduce_prim
    VCast (fun _ γ => γ) (fun _ τ => τ).

Fixpoint conjuncts_hold (σ : valuation) (Φ : prim) {struct Φ} :
  σ ⊨ Φ -> Forall (models σ) (conjuncts Φ).
Proof.
  intros H. destruct Φ as [l | x | op args]; [repeat constructor; exact H | repeat constructor; exact H |].
  destruct op; [| repeat constructor; exact H | repeat constructor; exact H].
  destruct args as [| a [| b [| c rest]]]; try (repeat constructor; exact H).
  unfold models in H. simpl in H. apply andb_true_iff in H as [Ha Hb].
  simpl. apply Forall_app. split; apply conjuncts_hold; assumption.
Qed.

#[local] Instance pruning_models_sat : ModelsSat.
Proof.
  intros σ Φ H. pose proof (conjuncts_hold σ Φ H) as Hall.
  change (negb (contradicts_itself (conjuncts Φ)) = true).
  apply negb_true_iff. apply not_true_iff_false. intros Hcontra.
  apply existsb_exists in Hcontra as [q [Hq Hneg]].
  apply existsb_exists in Hneg as [r [Hr Hqr]].
  apply prim_eqb_eq in Hqr. subst r.
  rewrite Forall_forall in Hall.
  pose proof (Hall _ Hq) as Hmq. pose proof (Hall _ Hr) as Hmr.
  unfold models in Hmq, Hmr. simpl in Hmr. rewrite Hmq in Hmr. discriminate Hmr.
Qed.

#[local] Instance pruning_subst_contains : SubstContains :=
  @Build_SubstContains model_sorts pruning_solver
    (@subst_type_contains _ _ Model.Model.model_subst_contains)
    (@subst_coerc_contains _ _ Model.Model.model_subst_contains).

#[local] Instance pruning_model_laws : @ConCoreLaws model_sorts pruning_solver :=
  @concore_laws model_sorts pruning_solver Model.Model.model_reduce_prim_literal
    Model.Model.model_cast_concore pruning_models_sat Model.Model.model_reduce_prim_contains
    Model.Model.model_cast_contains pruning_subst_contains.

Definition repeat_var : var := "s".
Definition repeat_guard : prim := PSym repeat_var.

Lemma pruning_refutes_repeated_branch :
  sat (pc_and (pc_and pc_true repeat_guard) (pc_not repeat_guard)) = false /\
  sat (pc_and (pc_and pc_true (pc_not repeat_guard)) repeat_guard) = false.
Proof. split; reflexivity. Qed.

Lemma pruning_keeps_single_branch :
  sat (pc_and pc_true repeat_guard) = true /\ sat (pc_and pc_true (pc_not repeat_guard)) = true.
Proof. split; reflexivity. Qed.

Definition inner_branch (c : expr) : expr := ite_expr c (ECon "C") (ECon "D").
Definition repeat_alts (c : expr) : list alt :=
  Alt "A" [] (inner_branch c) :: Alt "B" [] (inner_branch c) :: nil.
Definition repeat_branch (c : expr) : expr := ECase (ite_expr c (ECon "A") (ECon "B")) (repeat_alts c).

Definition repeat_sym : expr := repeat_branch (ESym repeat_var).
Definition repeat_con (σ : valuation) : expr := repeat_branch (ELit (σ repeat_var)).

Definition repeat_sym_value : value :=
  VIf repeat_guard
    (VIf repeat_guard (VCon "C" []) (VBot BUnreachable))
    (VIf repeat_guard (VBot BUnreachable) (VCon "D" [])).

Theorem repeat_sym_run_prunes : eval Inf pc_true EmptyEnv repeat_sym repeat_sym_value.
Proof.
  eapply eval_equal_value; [eapply Eval_Case |].
  - unfold ite_expr. run_ite_spine.
    + constructor. constructor.
    + eapply Select_Sym; [reflexivity | constructor; constructor | constructor; constructor].
  - cbn. eapply Fold_If.
    + eapply Fold_Con; [reflexivity |]. unfold inner_branch, ite_expr. run_ite_spine.
      * constructor. constructor.
      * eapply Select_Sym;
          [reflexivity | constructor; constructor | constructor; apply Eval_Prune; reflexivity].
    + eapply Fold_Con; [reflexivity |]. unfold inner_branch, ite_expr. run_ite_spine.
      * constructor. constructor.
      * eapply Select_Sym;
          [reflexivity | constructor; apply Eval_Prune; reflexivity | constructor; constructor].
  - reflexivity.
Qed.

Lemma repeat_con_run : forall σ, σ repeat_var = true ->
  EmptyEnv ⊢ᶜ repeat_con σ ⇓ᶜ VCon "C" [].
Proof.
  intros σ Hs. unfold repeat_con. rewrite Hs. eapply Eval_Case.
  - unfold repeat_branch, ite_expr. run_ite_spine.
    + constructor. constructor.
    + refine (Select_True _ _ _ _ _ _). constructor. constructor.
  - cbn. eapply Fold_Con; [reflexivity |]. unfold inner_branch, ite_expr. run_ite_spine.
    + constructor. constructor.
    + refine (Select_True _ _ _ _ _ _). constructor. constructor.
Qed.

Lemma repeat_contains : forall σ : valuation, contains_expr σ repeat_sym (repeat_con σ).
Proof. intros σ. repeat constructor. Qed.

Lemma repeat_concore : forall σ : valuation, concore_expr (repeat_con σ).
Proof. intros σ. repeat constructor. Qed.

Theorem pruning_soundness : forall σ : valuation, σ repeat_var = true ->
  exists v_c, EmptyEnv ⊢ᶜ repeat_con σ ⇓ᶜ v_c /\
    contains_val σ repeat_sym_value v_c /\ v_c = VCon "C" [].
Proof.
  intros σ Hs.
  destruct (concore_soundness pc_true EmptyEnv EmptyEnv σ repeat_sym (repeat_con σ)
    repeat_sym_value (Model.Model.models_pc_true σ) (Contains_Empty σ) (repeat_contains σ)
    (repeat_concore σ) Concrete_Empty repeat_sym_run_prunes) as [v_c [Hrun Hrel]].
  exists v_c. split; [exact Hrun | split; [exact Hrel |]].
  exact (concore_eval_deterministic EmptyEnv (repeat_con σ) v_c (VCon "C" []) Concrete_Empty
    (repeat_concore σ) Hrun (repeat_con_run σ Hs)).
Qed.
