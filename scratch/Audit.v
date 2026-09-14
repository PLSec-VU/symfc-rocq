From SymCoreTheory Require Import ConCore SymCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

Definition bindx (x:var) : environment :=
  ExtendEnv x (MkClosure EmptyEnv (EBot BUndefined)) EmptyEnv.

Ltac kill_total sigma G e H :=
  destruct (models_cond_total sigma G e) as [pc Hpc]; [auto | simpl in Hpc].

(* --- Finding 1: sigma never instantiates a symbolic variable. ------------ *)
Lemma contains_var_inv : forall sigma x ec,
  contains sigma (EVar x) ec -> ec = EVar x.
Proof. intros sigma x ec H. inversion H; subst; reflexivity. Qed.

(* --- Finding 2: no condition mentioning a variable is ever judgeable. ---- *)
Lemma symvar_undecidable : forall sigma x,
  ~ models_cond sigma (EVar x) /\ ~ models_not_cond sigma (EVar x).
Proof.
  intros sigma x; split; intro H.
  - kill_total sigma (bindx x) (EVar x) H;
    unfold bindx in Hpc; simpl in Hpc;
    destruct (string_dec x x); [discriminate | congruence].
  - kill_total sigma (bindx x) (EVar x) H;
    unfold bindx in Hpc; simpl in Hpc;
    destruct (string_dec x x); [discriminate | congruence].
Qed.

Lemma prim_cond_on_symvar_undecidable : forall sigma p x l,
  ~ models_cond sigma (EApp (EApp (EPrimOp p) (EVar x)) (ELit l))
  /\ ~ models_not_cond sigma (EApp (EApp (EPrimOp p) (EVar x)) (ELit l)).
Proof.
  intros sigma p x l; split; intro H.
  - kill_total sigma (bindx x) (EApp (EApp (EPrimOp p) (EVar x)) (ELit l)) H;
    unfold bindx in Hpc; simpl in Hpc;
    destruct (string_dec x x); [discriminate | congruence].
  - kill_total sigma (bindx x) (EApp (EApp (EPrimOp p) (EVar x)) (ELit l)) H;
    unfold bindx in Hpc; simpl in Hpc;
    destruct (string_dec x x); [discriminate | congruence].
Qed.

(* A branch on "x == l" has no concretion, so soundness says nothing here. *)
Theorem soundness_vacuous_on_symbolic_branch :
  forall sigma p x l et ef ec,
    ~ contains sigma (EIf (EApp (EApp (EPrimOp p) (EVar x)) (ELit l)) et ef) ec.
Proof.
  intros sigma p x l et ef ec H.
  destruct (prim_cond_on_symvar_undecidable sigma p x l) as [H1 H2].
  inversion H; subst; eauto.
Qed.

(* --- Finding 3: Rule Prune makes EVERY branch unconcretisable. ----------- *)
Theorem prune_kills_every_branch :
  (exists Phi, sat Phi = false) ->
  forall sigma ec et ef e, ~ contains sigma (EIf ec et ef) e.
Proof.
  intros [Phi Hunsat] sigma ec et ef e H.
  assert (Hev : eval Phi EmptyEnv ec (EBot BUnreachable)) by (apply Eval_Prune; assumption).
  inversion H; subst.
  - apply (eval_models_cond Phi EmptyEnv ec (EBot BUnreachable) sigma Hev) in H4.
    kill_total sigma EmptyEnv (EBot BUnreachable) H4. discriminate.
  - apply (eval_models_not_cond Phi EmptyEnv ec (EBot BUnreachable) sigma Hev) in H4.
    kill_total sigma EmptyEnv (EBot BUnreachable) H4. discriminate.
Qed.
