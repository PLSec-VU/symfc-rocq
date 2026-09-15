From SymCoreTheory Require Import SymCore ConCore Completeness Model.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.
Open Scope string_scope.

Definition guard_var : var := "y".
Definition guard : expr := EVar guard_var.

Fixpoint loop_bound (L : nat) (w : expr) : nat :=
  match w with
  | EIf _ a _ => S (Nat.max (L + 2) (loop_bound (S L) a + 2))
  | _ => 0
  end.

Definition stack_height (w : expr) : nat := loop_bound 0 w + 3.

Fixpoint stack (c : expr) (k : nat) (t : expr) : expr :=
  match k with
  | O => t
  | S k' => EIf c (stack c k' t) t
  end.

Fixpoint stacking_cast (e : expr) (γ : coercion) : expr :=
  match e with
  | EIf c a b => EIf c (stack c (stack_height b) (stacking_cast a γ)) (stacking_cast b γ)
  | _ => e
  end.

Definition stacking_solver : SymCoreSolver :=
  Build_SymCoreSolver
    model_sat (PCLit true) eq_refl model_reduce_prim
    stacking_cast keep_coercion keep_type.

#[local] Existing Instance stacking_solver | 0.

Lemma stack_contains : forall σ S c t x k,
  models_cond σ S c -> contains σ S t x -> contains σ S (stack c k t) x.
Proof.
  intros σ S c t x k Hc Ht. induction k as [| k IH]; simpl; [exact Ht |].
  apply Cont_If_True; assumption.
Qed.

#[local] Instance stacking_cast_concore : CastExprConcore.
Proof.
  intros e γ H. destruct e; simpl; try exact H.
  exfalso. eapply not_concore_if. exact H.
Qed.

#[local] Instance stacking_cast_contains : CastExprContains.
Proof.
  intros σ S es ec γ H.
  induction H; simpl; try (constructor; assumption).
  - destruct ec; try discriminate. eapply Cont_Thunk_Outer; eassumption.
  - apply Cont_If_True; [assumption |]. apply stack_contains; assumption.
  - destruct (cont_denote_is_app es p args H H1) as [f [a Hfa]]. subst es.
    eapply Cont_Denote; eassumption.
Qed.

#[local] Instance stacking_laws : ConCoreLaws.
Proof.
  exact (@concore_laws model_sorts stacking_solver
    model_reduce_prim_solvable model_reduce_prim_saturated
    model_reduce_prim_concore stacking_cast_concore
    model_models_sat model_prim_value_and
    model_reduce_prim_contains model_reduce_prim_denote model_reduce_prim_ground_value
    model_reduce_prim_ite_contains stacking_cast_contains
    model_subst_coerc_contains_env model_subst_type_contains_env).
Qed.

Print Assumptions stacking_laws.
