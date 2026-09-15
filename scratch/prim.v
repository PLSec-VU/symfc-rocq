From SymCoreTheory Require Import ConCore SymCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

Section Scratch.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

(* 1. Every Solvable term is already a ConCore term. *)
Lemma solvable_concore : forall G e, Solvable G e -> concore_expr e.
Proof.
  intros G e H. induction H.
  - apply Con_Lit.
  - apply Con_Var.
  - apply Con_PrimOp.
  - apply Con_App; assumption.
Qed.

(* 2. So reduce_prim_concore is REDUNDANT: it follows from reduce_prim_solvable. *)
Lemma reduce_prim_concore_derivable : forall p args,
  concore_expr (reduce_prim p args).
Proof.
  intros p args. eapply solvable_concore. apply (reduce_prim_solvable EmptyEnv).
Qed.

(* 3. Solvable admits only literals, free vars, primops and primop spines. *)
Lemma solvable_not_bot : forall G b, ~ Solvable G (EBot b).
Proof. intros G b H; inversion H. Qed.
Lemma solvable_not_lam : forall G x e, ~ Solvable G (ELam x e).
Proof. intros G x e H; inversion H. Qed.
Lemma solvable_not_case : forall G e alts, ~ Solvable G (ECase e alts).
Proof. intros G e alts H; inversion H. Qed.
Lemma solvable_not_con : forall G d, ~ Solvable G (ECon d).
Proof. intros G d H; inversion H. Qed.

(* 4. reduce_prim can never return a bare variable either: Solvable_Var needs
      the variable unbound, but reduce_prim_solvable is stated for EVERY G. *)
Lemma reduce_prim_not_var : forall p args x,
  reduce_prim p args <> EVar x.
Proof.
  intros p args x Heq.
  pose proof (reduce_prim_solvable
    (ExtendEnv x (MkClosure EmptyEnv (EBot BUndefined)) EmptyEnv) p args) as HS.
  rewrite Heq in HS. inversion HS; subst.
  simpl in H0. destruct (string_dec x x); [discriminate | congruence].
Qed.

(* 5. The bite: primitive reduction must ERASE a symbolic branch in its
      arguments.  reduce_prim of a branching argument is EIf-free. *)
Theorem reduce_prim_erases_branches : forall p c t f,
  concore_expr (reduce_prim p [EIf c t f])
  /\ forall ec et ef, reduce_prim p [EIf c t f] <> EIf ec et ef.
Proof.
  intros p c t f. split.
  - apply reduce_prim_concore_derivable.
  - intros ec et ef Heq.
    pose proof (reduce_prim_solvable EmptyEnv p [EIf c t f]) as HS.
    rewrite Heq in HS. inversion HS.
Qed.

End Scratch.
