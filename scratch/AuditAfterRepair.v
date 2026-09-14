From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

(* Which audit results survive the repair, once mechanically adapted to the
   new signatures? *)

Definition bindx (x:var) : environment :=
  ExtendEnv x (MkClosure EmptyEnv (EBot BUndefined)) EmptyEnv.

(* ---- Audit.v Finding 1: contains_var_inv.  REFUTED. ---- *)
Theorem audit1_refuted : forall sigma : valuation,
  ~ (forall S x ec, contains sigma S (EVar x) ec -> ec = EVar x).
Proof.
  intros sigma H.
  specialize (H (only "x") "x" (ELit (sigma "x"))
                (Cont_Var_Sym sigma (only "x") "x" (only_self "x"))).
  discriminate.
Qed.

(* ---- Audit.v Finding 2: symvar_undecidable.  BLOCKED for symbolic x. ---- *)
(* The old proof fed models_cond_total an environment that BINDS x. That is
   now rejected: models_cond_total demands the environment bind no symbolic
   variable, and bindx x binds x. *)
Theorem audit2_attack_environment_rejected : forall S x,
  S x = true -> ~ sym_free_env S (bindx x).
Proof.
  intros S x Hx Hfree. specialize (Hfree x Hx).
  unfold bindx in Hfree. simpl in Hfree.
  destruct (string_dec x x); [discriminate | congruence].
Qed.

(* ...and judging a SYMBOLIC variable is now exactly modelling its atom.
   S x = true is new: it is what "symbolic" means, and since models_cond is a
   definition rather than a parameter the backward direction now has to say
   which variables are symbolic.  The forward direction is unchanged and
   needs no such hypothesis (see audit2_judgeable_is_atom below). *)
Theorem audit2_symvar_is_judgeable : forall sigma S x,
  S x = true ->
  (models_cond sigma S (EVar x) <-> models sigma (PCVar x)).
Proof.
  intros sigma S x Hx. apply models_cond_denotes.
  intros G Hfree. simpl. rewrite (Hfree x Hx). reflexivity.
Qed.

Theorem audit2_judgeable_is_atom : forall sigma S x,
  models_cond sigma S (EVar x) -> models sigma (PCVar x).
Proof. intros. apply (models_cond_pc sigma S EmptyEnv (EVar x)); [reflexivity | assumption]. Qed.

(* ---- Audit.v Finding 3: prune_kills_every_branch.  BLOCKED. ---- *)
(* eval_models_cond now needs models sigma Phi, which contradicts sat Phi = false. *)
Theorem audit3_blocked : forall Phi sigma,
  sat Phi = false -> ~ models sigma Phi.
Proof. intros Phi sigma Hun Hmod. apply models_sat in Hmod. congruence. Qed.

(* ---- prim.v item 1: still TRUE. ---- *)
Lemma solvable_concore : forall G e, Solvable G e -> concore_expr e.
Proof.
  intros G e H. induction H.
  - apply Con_Lit.
  - apply Con_Var.
  - apply Con_PrimOp.
  - apply Con_App; assumption.
Qed.

(* ---- prim.v items 3: still TRUE (Solvable is unchanged). ---- *)
Lemma solvable_not_bot : forall G b, ~ Solvable G (EBot b).
Proof. intros G b H; inversion H. Qed.
Lemma solvable_not_lam : forall G x e, ~ Solvable G (ELam x e).
Proof. intros G x e H; inversion H. Qed.

(* ---- prim.v item 2: reduce_prim_concore_derivable.  Now CONDITIONAL. ---- *)
Lemma prim2_conditional : forall p args,
  Forall (Solvable EmptyEnv) args -> concore_expr (reduce_prim p args).
Proof.
  intros p args H. eapply solvable_concore.
  apply (reduce_prim_solvable EmptyEnv). exact H.
Qed.

(* ---- prim.v item 5: reduce_prim_erases_branches.  BLOCKED. ---- *)
(* The hypothesis reduce_prim_solvable now needs is exactly what a branching
   argument fails to satisfy. *)
Theorem prim5_blocked : forall G c t f,
  ~ Forall (Solvable G) [EIf c t f].
Proof.
  intros G c t f H. inversion H as [| a l Ha Hl]; subst. inversion Ha.
Qed.

(* ---- prim2.v item 1: solvable_contains_eq.  REFUTED. ---- *)
Theorem prim2_1_refuted : forall sigma : valuation,
  ~ (forall G es S ec, Solvable G es -> contains sigma S es ec -> es = ec).
Proof.
  intros sigma H.
  specialize (H EmptyEnv (EVar "x") (only "x") (ELit (sigma "x"))
                (Solvable_Var EmptyEnv "x" eq_refl)
                (Cont_Var_Sym sigma (only "x") "x" (only_self "x"))).
  discriminate.
Qed.
