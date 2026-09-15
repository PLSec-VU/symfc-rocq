From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

Section Scratch.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

(**
  Why models_cond is defined the way it is in ConCore.v §9, and why
  eval_models_cond carries a sym_free_env hypothesis.

  The obvious definition of models_cond reads the condition in the empty
  environment and asks the model to satisfy the formula:

      exists pc, expr_to_pc · e = Some pc /\ σ ⊨ pc

  It is wrong, and this file shows exactly how. Rule Var lets a condition
  that IS a formula evaluate to something that is NOT one, as soon as the
  ambient environment binds the variable the condition tests. Then
  eval_models_cond, which was harmless while models_cond was abstract,
  proves that no model satisfies any variable atom at all.

  Both theorems below are stated as implications from the axiom shape, so
  nothing here is assumed: each says "if you adopt that shape, here is what
  it costs".
*)

(* ==================================================================== *)
(* 1. The environment-free definition empties out models.               *)
(* ==================================================================== *)

Definition naive_models_cond (σ : valuation) (S : symvars) (e : expr) : Prop :=
  exists pc, expr_to_pc · e = Some pc /\ σ ⊨ pc.

(** eval_models_cond, verbatim, read at the naive definition. *)
Definition NaiveEvalModelsCond : Prop := forall Φ Γ S ec ec' σ,
  σ ⊨ Φ -> Φ ; Γ ⊢ ec ⇓ ec' ->
  naive_models_cond σ S ec -> naive_models_cond σ S ec'.

(** The witness: an environment that binds the tested variable to a bottom. *)
Definition binds_to_bottom (x : var) : environment :=
  ExtendEnv x (MkClosure · (EBot BUndefined)) ·.

Lemma condition_evaluates_out_of_the_formulas : forall x,
  (PCVar x) ; (binds_to_bottom x) ⊢ EVar x ⇓ EBot BUndefined.
Proof.
  intros x. eapply Eval_Var with (Γ' := ·) (e := EBot BUndefined).
  - unfold binds_to_bottom. simpl. destruct (string_dec x x); congruence.
  - apply Eval_Bot.
Qed.

Theorem naive_definition_collapses_models :
  NaiveEvalModelsCond -> forall σ x, ~ (σ ⊨ PCVar x).
Proof.
  intros HE σ x Hmod.
  assert (Hin : naive_models_cond σ (fun _ => true) (EVar x))
    by (exists (PCVar x); split; [reflexivity | exact Hmod]).
  destruct (HE (PCVar x) (binds_to_bottom x) (fun _ => true)
               (EVar x) (EBot BUndefined) σ Hmod
               (condition_evaluates_out_of_the_formulas x) Hin) as [pc [Hpc _]].
  simpl in Hpc. discriminate.
Qed.

(** So §11(a) would die outright: no model satisfies any variable atom. *)
Corollary naive_definition_kills_symvar_atom :
  NaiveEvalModelsCond -> ~ (exists σ x, σ ⊨ PCVar x).
Proof.
  intros HE [σ [x H]]. exact (naive_definition_collapses_models HE σ x H).
Qed.

(* ==================================================================== *)
(* 2. With the real definition, the scope hypothesis is what saves it.  *)
(* ==================================================================== *)

(** ConCore's models_cond, but with eval_models_cond's sym_free_env
    hypothesis dropped. The same collapse returns. *)
Definition EvalModelsCondWithoutScope : Prop := forall Φ Γ S ec ec' σ,
  σ ⊨ Φ -> Φ ; Γ ⊢ ec ⇓ ec' -> models_cond σ S ec -> models_cond σ S ec'.

Theorem scope_hypothesis_is_necessary :
  EvalModelsCondWithoutScope -> forall σ x, ~ (σ ⊨ PCVar x).
Proof.
  intros HE σ x Hmod.
  assert (Hin : models_cond σ (only x) (EVar x)).
  { exists (PCVar x). split; [| exact Hmod].
    intros Γ Hfree. simpl. rewrite (Hfree x (only_self x)). reflexivity. }
  destruct (HE (PCVar x) (binds_to_bottom x) (only x)
               (EVar x) (EBot BUndefined) σ Hmod
               (condition_evaluates_out_of_the_formulas x) Hin) as [pc [Hden _]].
  specialize (Hden · (sym_free_env_empty _)). simpl in Hden. discriminate.
Qed.

(** With the hypothesis present, ConCore.eval_models_cond_residue shows the
    only evaluation rule left to assume anything about is App-Prim. *)

(* ==================================================================== *)
(* 3. What is left to assume, once both hypotheses are present.         *)
(* ==================================================================== *)

(**
  The two axioms are not derivable. This section says exactly what is
  missing, and it assumes nothing: every result below is an implication
  from a named shape.

  A path condition has two independent readings in this development.

  - `models` (written ⊨) is a Parameter. The only facts about it are
    models_sat and models_and_iff.
  - `pc_value` is a function into lit, built from the Parameter
    prim_value.

  Nothing ties the two together. A model can therefore judge one formula
  true and judge a second formula false, even when the two formulas have
  the same SMT value under that same model.

  That is the whole gap. ConCore.eval_denote already proves that
  evaluation preserves the SMT value: from a condition that denotes the
  formula pc, the step reaches a condition that denotes some formula pc'
  with pc_value σ pc' = pc_value σ pc. The existence half of models_cond
  is thus free. The remaining goal is

      σ ⊨ pc,  pc_value σ pc' = pc_value σ pc  ⊢  σ ⊨ pc'

  and no fact in the development reaches it. The step is real: Rule
  App-Prim replaces the condition by reduce_prim's answer, and
  reduce_prim is free to return a term that reads off a different
  formula.

  Note which ingredient is missing. reduce_prim_denote, the bridge from
  Solvable to expr_to_pc, and eval_models_cond_residue are all present
  and all used. The missing one is a fourth: an SMT contract saying the
  model's verdict depends only on the SMT value.
*)

(** The missing contract, named. *)
Definition PcValueSound : Prop := forall σ pc1 pc2,
  pc_value σ pc1 = pc_value σ pc2 -> σ ⊨ pc1 -> σ ⊨ pc2.

(** It is sufficient: it turns both axioms into one-line consequences of
    the proved eval_denote. *)
Theorem value_soundness_gives_eval_models_cond :
  PcValueSound -> forall Φ Γ S ec ec' σ,
  σ ⊨ Φ -> sym_free_env S Γ ->
  Φ ; Γ ⊢ ec ⇓ ec' -> models_cond σ S ec -> models_cond σ S ec'.
Proof.
  intros HB Φ Γ S ec ec' σ Hmod Hfree Heval [pc [Hden Hsat]].
  destruct (eval_denote Φ Γ σ S ec ec' (pc_value σ pc) Hmod Hfree Heval
              (ex_intro _ pc (conj Hden eq_refl))) as [pc' [Hden' Hval']].
  exists pc'. split; [exact Hden' | exact (HB σ pc pc' (eq_sym Hval') Hsat)].
Qed.

(** The negated form needs no extra assumption: ¬ is the primitive
    application op_not, so equal values give equal values under it. *)
Theorem value_soundness_gives_eval_models_not_cond :
  PcValueSound -> forall Φ Γ S ec ec' σ,
  σ ⊨ Φ -> sym_free_env S Γ ->
  Φ ; Γ ⊢ ec ⇓ ec' -> models_not_cond σ S ec -> models_not_cond σ S ec'.
Proof.
  intros HB Φ Γ S ec ec' σ Hmod Hfree Heval [pc [Hden Hsat]].
  destruct (eval_denote Φ Γ σ S ec ec' (pc_value σ pc) Hmod Hfree Heval
              (ex_intro _ pc (conj Hden eq_refl))) as [pc' [Hden' Hval']].
  exists pc'. split; [exact Hden' |].
  apply (HB σ (¬ pc) (¬ pc')); [| exact Hsat].
  unfold pc_not. simpl. rewrite Hval'. reflexivity.
Qed.

(* ==================================================================== *)
(* 4. The assumption is about the solver, not about evaluation.         *)
(* ==================================================================== *)

(**
  Read the axiom at one primitive operation of arity one, applied to a
  symbolic variable, in the empty environment. What comes out is a joint
  constraint on reduce_prim and models: whatever term the reducer hands
  back, the model must still judge it true. reduce_prim and models are
  separate Parameters, so nothing in the development supplies that.
*)

Definition EvalModelsCondShape : Prop := forall Φ Γ S ec ec' σ,
  σ ⊨ Φ -> sym_free_env S Γ ->
  Φ ; Γ ⊢ ec ⇓ ec' -> models_cond σ S ec -> models_cond σ S ec'.

Lemma unary_app_evaluates : forall p x Φ,
  primop_arity p = 1 ->
  Φ ; · ⊢ EApp (EPrimOp p) (EVar x) ⇓ reduce_prim p [EVar x].
Proof.
  intros p x Φ Harity.
  apply Eval_AppPrim with (args := [EVar x]).
  - reflexivity.
  - simpl. rewrite Harity. reflexivity.
  - constructor; [| constructor]. apply Eval_SymVar. reflexivity.
Qed.

Lemma unary_app_denotes : forall S p x,
  S x = true -> denotes S (EApp (EPrimOp p) (EVar x)) (PCPrim p [PCVar x]).
Proof.
  intros S p x Hsx Γ Hfree. simpl. rewrite (Hfree x Hsx). reflexivity.
Qed.

Theorem axiom_constrains_reduce_prim_and_models_jointly :
  EvalModelsCondShape ->
  forall σ S p x,
    S x = true -> primop_arity p = 1 ->
    σ ⊨ (PCPrim p [PCVar x]) ->
    models_cond σ S (reduce_prim p [EVar x]).
Proof.
  intros HE σ S p x Hsx Harity Hsat.
  apply (HE (PCPrim p [PCVar x]) · S (EApp (EPrimOp p) (EVar x))
            (reduce_prim p [EVar x]) σ Hsat (sym_free_env_empty S)
            (unary_app_evaluates p x _ Harity)).
  exists (PCPrim p [PCVar x]). split; [apply unary_app_denotes; exact Hsx | exact Hsat].
Qed.

End Scratch.
