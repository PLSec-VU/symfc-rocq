From SymCoreTheory Require Export SymCore.SideConditions.
From Stdlib Require Import Strings.String Lists.List ZArith.ZArith Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Section SymCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

(** A spine rebuilt from its head and arguments is the spine it came from *)
Lemma unspool_fold_left : forall e acc h args,
  unspool_app e acc = (h, args) -> fold_left EApp args h = fold_left EApp acc e.
Proof.
  induction e; intros acc h args H; simpl in H;
    try (injection H as ? ?; subst; reflexivity).
  apply IHe1 in H. simpl in H. exact H.
Qed.

Lemma unspool_make_con_app : forall e d args,
  unspool_app e [] = (ECon d, args) -> make_con_app d args = e.
Proof.
  intros e d args H. unfold make_con_app.
  apply (unspool_fold_left e [] (ECon d) args H).
Qed.

Lemma decompose_con_app_unspool : forall e d args,
  decompose_con_app e = Some (d, args) -> unspool_app e [] = (ECon d, args).
Proof.
  intros e d args H. unfold decompose_con_app in H.
  destruct (unspool_app e []) as [h aa]; destruct h; try discriminate.
  injection H as ? ?; subst; reflexivity.
Qed.

(** ------------------------------------------------------------------------- *)
(** Merging Common Prefixes of a Branch (§3.3)                                *)
(** ------------------------------------------------------------------------- *)

(**
  Pair the arguments of two constructor spines under one condition:
  D e⃗1 and D e⃗2 become D (if ec then e1i else e2i)⃗.
*)
Fixpoint zip_if (ec : expr) (l1 l2 : list expr) : list expr :=
  match l1, l2 with
  | a1 :: t1, a2 :: t2 => EIf ec a1 a2 :: zip_if ec t1 t2
  | _, _ => []
  end.

(**
  Section 3.3's ite(Γ, ec, et, ef), every clause but the cast.

  Clause 1: a shared constructor head stays put and the branch moves into the
  arguments, one branch per argument. This is what makes a case expression
  reduce each alternative once instead of once per path.

  Clause 2: two arms the solver can read become one SMT if-then-else term.
  op_ite is the solver's own three-place operation; reduce_prim is the
  solver's reducer. This is the clause that hands a branch to the SMT solver
  and stops the evaluator from walking it. The guard needs Γ, because whether
  a variable is solvable depends on whether Γ binds it - which is why merge
  takes an environment.

  Clauses 3, 5, 6 and 7: two lambda closures merge when their environments
  and their binders agree; a bottom, a type and a coercion merge only when the
  two arms are the same term.

  Clause 8: anything else stays a branch.

  The clauses cannot overlap. A constructor spine is not solvable
  (solvable_not_con_app), and no lambda, bottom, type or coercion is solvable
  either, so testing the constructor clause first and the solvable clause
  second changes nothing.
*)
Definition ite_leaf (Γ : environment) (ec et ef : expr) : expr :=
  match decompose_con_app et, decompose_con_app ef with
  | Some (d1, a1), Some (d2, a2) =>
      if andb (String.eqb d1 d2) (Nat.eqb (length a1) (length a2))
      then make_con_app d1 (zip_if ec a1 a2)
      else EIf ec et ef
  | _, _ =>
      if solvable_dec Γ et then
        if solvable_dec Γ ef then reduce_prim op_ite (ec :: et :: ef :: nil)
        else EIf ec et ef
      else
        match et, ef with
        | EThunk Γ1 (ELam x1 b1), EThunk Γ2 (ELam x2 b2) =>
            if andb (env_eqb Γ1 Γ2) (String.eqb x1 x2)
            then EThunk Γ1 (ELam x1 (EIf ec b1 b2))
            else EIf ec et ef
        | EBot b1, EBot b2 =>
            if bottom_eqb b1 b2 then EBot b1 else EIf ec et ef
        | EType τ1, EType τ2 =>
            if dec_eqb type_fc_eq_dec τ1 τ2 then EType τ1 else EIf ec et ef
        | ECoercion γ1, ECoercion γ2 =>
            if dec_eqb coercion_eq_dec γ1 γ2 then ECoercion γ1 else EIf ec et ef
        | _, _ => EIf ec et ef
        end
  end.

(**
  Clause 4, the cast, is the one clause that recurses: two arms under the
  same coercion keep the coercion outside and merge their bodies.

  The recursive argument if ec then e1 else e2 is built here, not taken apart
  from the input, so the recursion is not on the branch. It is on the true
  arm et, which loses its cast at each step. Writing the cast clause at the
  top of the definition, and everything else in ite_leaf, is what makes that
  visible to the termination check. No clause is lost by the split: a cast is
  neither a constructor spine nor solvable nor any of the other merged
  shapes, so ite_leaf would have left it a branch anyway.
*)
Fixpoint ite (Γ : environment) (ec et ef : expr) {struct et} : expr :=
  match et, ef with
  | ECast e1 γ1, ECast e2 γ2 =>
      if dec_eqb coercion_eq_dec γ1 γ2 then ECast (ite Γ ec e1 e2) γ1
      else EIf ec et ef
  | _, _ => ite_leaf Γ ec et ef
  end.

(**
  Leaf expression merging (Fig. 3, Rule Case & §3.3).

  Merging is about branches, so merge reads a branch at the head and hands it
  to ite; on any other expression there is nothing to merge and merge returns
  its argument.
*)
Definition merge (Γ : environment) (e : expr) : expr :=
  match e with
  | EIf ec et ef => ite Γ ec et ef
  | _ => e
  end.

(** An expression that is not a branch survives merging unchanged *)
Lemma merge_not_if : forall Γ e, is_if e = false -> merge Γ e = e.
Proof. intros Γ e H. destruct e; simpl in *; try reflexivity. discriminate. Qed.

(** Every shape but two casts under one coercion reaches ite_leaf *)
Lemma ite_leaf_of : forall Γ ec et ef,
  is_cast et = false \/ is_cast ef = false -> ite Γ ec et ef = ite_leaf Γ ec et ef.
Proof.
  intros Γ ec et ef H. destruct et; destruct ef; simpl; try reflexivity;
    destruct H as [H|H]; discriminate.
Qed.

Lemma ite_cast : forall Γ ec e1 γ1 e2 γ2,
  ite Γ ec (ECast e1 γ1) (ECast e2 γ2) =
  (if dec_eqb coercion_eq_dec γ1 γ2 then ECast (ite Γ ec e1 e2) γ1
   else EIf ec (ECast e1 γ1) (ECast e2 γ2)).
Proof. reflexivity. Qed.

End SymCore.
