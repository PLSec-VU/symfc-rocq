From SymCoreTheory Require Import SymCore ConCore Model.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition tt : @expr model_sorts := ELit true.
Definition branch_of_tt : @expr model_sorts := EIf (EVar "x") tt tt.

Lemma concrete_depth_one : @eval model_sorts model_solver (Fin 1) pc_true · tt tt.
Proof. apply Eval_Lit. Qed.

Lemma branch_contains_tt : contains (fun _ => true) (only "x") branch_of_tt tt.
Proof.
  apply Cont_If_True; [| apply Cont_Lit].
  exists (PCVar "x"). split; [| reflexivity].
  intros Γ Hfree. simpl. rewrite (Hfree "x" (only_self "x")). reflexivity.
Qed.

Theorem symbolic_depth_one_has_no_value :
  forall v, ~ @eval model_sorts model_solver (Fin 1) pc_true · branch_of_tt v.
Proof.
  intros v H. inversion H; subst.
  - match goal with [ Hu : unspool_app _ _ = (ECon _, _) |- _ ] => discriminate Hu end.
  - match goal with
    | [ Hg : eval (dec (Remaining 0)) _ _ (EVar "x") ?g, Hp : expr_to_pc _ ?g = Some _ |- _ ] =>
        simpl in Hg; inversion Hg; subst; discriminate Hp
    end.
  - match goal with [ Hs : sat _ = false |- _ ] => discriminate Hs end.
Qed.

Theorem same_depth_completeness_fails :
  @eval model_sorts model_solver (Fin 1) pc_true · tt tt
  /\ contains (fun _ => true) (only "x") branch_of_tt tt
  /\ ~ exists v, @eval model_sorts model_solver (Fin 1) pc_true · branch_of_tt v.
Proof.
  split; [exact concrete_depth_one |].
  split; [exact branch_contains_tt |].
  intros [v Hv]. exact (symbolic_depth_one_has_no_value v Hv).
Qed.
