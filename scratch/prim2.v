From SymCoreTheory Require Import ConCore SymCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

(* On a Solvable term, `contains` is plain syntactic equality. *)
Lemma solvable_contains_eq : forall G es,
  Solvable G es -> forall sigma ec, contains sigma es ec -> es = ec.
Proof.
  intros G es HS. induction HS; intros sigma ec Hc.
  - inversion Hc; subst; reflexivity.
  - inversion Hc; subst; reflexivity.
  - inversion Hc; subst; reflexivity.
  - inversion Hc; subst. f_equal; eauto.
Qed.

(* reduce_prim is always Solvable, so reduce_prim_contains degenerates to an
   EQUATION between the symbolic and the concrete reduction. *)
Lemma reduce_prim_contains_eq : forall sigma p args_s args_c,
  Forall2 (contains sigma) args_s args_c ->
  reduce_prim p args_s = reduce_prim p args_c.
Proof.
  intros sigma p args_s args_c Hf.
  eapply (solvable_contains_eq EmptyEnv _ (reduce_prim_solvable EmptyEnv p args_s) sigma).
  apply reduce_prim_contains. exact Hf.
Qed.

(* THE BITE.  If some condition is resolvable true under one valuation and
   false under another -- i.e. as soon as branches can be resolved at all --
   then primitive reduction is a CONSTANT function on literals: 1+1 = 1+2. *)
Theorem reduce_prim_is_constant : forall sigma sigma' p c l1 l2,
  models_cond sigma c ->
  models_not_cond sigma' c ->
  reduce_prim p [ELit l1] = reduce_prim p [ELit l2].
Proof.
  intros sigma sigma' p c l1 l2 Htrue Hfalse.
  assert (Hs1 : reduce_prim p [EIf c (ELit l1) (ELit l2)] = reduce_prim p [ELit l1]).
  { eapply (reduce_prim_contains_eq sigma). constructor; [| constructor].
    apply Cont_If_True; [exact Htrue | apply Cont_Lit]. }
  assert (Hs2 : reduce_prim p [EIf c (ELit l1) (ELit l2)] = reduce_prim p [ELit l2]).
  { eapply (reduce_prim_contains_eq sigma'). constructor; [| constructor].
    apply Cont_If_False; [exact Hfalse | apply Cont_Lit]. }
  rewrite <- Hs1, Hs2. reflexivity.
Qed.
