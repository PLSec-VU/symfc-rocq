From SymCoreTheory Require Export Completeness.Completeness.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.

(** ========================================================================= *)
(** Sorts                                                                     *)
(** ========================================================================= *)

Inductive model_primop : Set := PAnd | PNot | PIte.

Definition model_primop_eq_dec : forall p q : model_primop, {p = q} + {p <> q}.
Proof. decide equality. Defined.

Definition model_tycon_eq_dec : forall t1 t2 : unit, {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

Definition model_arity (p : model_primop) : nat :=
  match p with PAnd => 2 | PNot => 1 | PIte => 3 end.

Definition model_prim_value (p : model_primop) (ls : list bool) : bool :=
  match p, ls with
  | PAnd, a :: b :: nil => a && b
  | PNot, a :: nil => negb a
  | PIte, c :: a :: b :: nil => if c then a else b
  | _, _ => false
  end.

Lemma model_prim_value_not_spec : forall l : bool,
  model_prim_value PNot (l :: nil) = true <-> l <> true.
Proof. intros l. destruct l; simpl; split; congruence. Qed.

Lemma model_prim_value_ite_spec : forall c t f : bool,
  model_prim_value PIte (c :: t :: f :: nil) = (if bool_dec c true then t else f).
Proof. intros c t f. destruct c; reflexivity. Qed.

#[export] Instance model_sorts : SymCoreSorts :=
  Build_SymCoreSorts
    bool model_primop PAnd PNot PIte model_arity eq_refl
    bool_dec model_primop_eq_dec unit model_tycon_eq_dec
    model_prim_value true "True"%string "False"%string
    model_prim_value_not_spec model_prim_value_ite_spec.

Lemma model_prim_value_wrong_arity : forall p ls,
  length ls <> model_arity p -> model_prim_value p ls = false.
Proof.
  intros p ls H.
  destruct p; destruct ls as [| a [| b [| c [| d ls]]]]; simpl in *; congruence.
Qed.

(** ========================================================================= *)
(** The reducer                                                               *)
(** ========================================================================= *)

Definition closed_model : valuation := fun _ => false.

Definition closed_value (e : expr) : bool :=
  match expr_to_pc · e with
  | Some pc => pc_value closed_model pc
  | None => false
  end.

Fixpoint graft_arg (f a : expr) : expr :=
  match a with
  | EIf c t e => EIf c (graft_arg f t) (graft_arg f e)
  | _ => EApp f a
  end.

Fixpoint graft (f a : expr) : expr :=
  match f with
  | EIf c t e => EIf c (graft t a) (graft e a)
  | _ => graft_arg f a
  end.

Fixpoint lift_branches (e : expr) : expr :=
  match e with
  | EIf c t f => EIf c (lift_branches t) (lift_branches f)
  | EApp f a => graft (lift_branches f) (lift_branches a)
  | _ => e
  end.

Definition fold_leaf (e : expr) : expr :=
  if smt_ground e then ELit (closed_value e) else e.

Fixpoint fold_leaves (e : expr) : expr :=
  match e with
  | EIf c t f => EIf c (fold_leaves t) (fold_leaves f)
  | _ => fold_leaf e
  end.

Fixpoint smt_need (e : expr) : option nat :=
  match e with
  | EVar _ => Some 0
  | ELit _ => Some 0
  | EPrimOp p => Some (model_arity p)
  | EApp f a =>
      match smt_need f, smt_need a with
      | Some (Datatypes.S n), Some 0 => Some n
      | _, _ => None
      end
  | _ => None
  end.

Definition smt_term (e : expr) : bool :=
  match smt_need e with
  | Some 0 => true
  | _ => false
  end.

Definition lit_of (e : expr) : option bool :=
  if smt_ground e then Some (closed_value e) else None.

Definition is_false_lit (e : expr) : bool :=
  match lit_of e with
  | Some false => true
  | _ => false
  end.

Definition rewrite_prim (p : model_primop) (args : list expr) : option expr :=
  match p, args with
  | PAnd, a :: b :: nil =>
      if is_false_lit a || is_false_lit b then Some (ELit false) else None
  | PIte, c :: a :: b :: nil =>
      match lit_of c with
      | Some true => Some (fold_leaf a)
      | Some false => Some (fold_leaf b)
      | None => if expr_eqb a b then Some (fold_leaf a) else None
      end
  | _, _ => None
  end.

Definition simplify (p : model_primop) (args : list expr) : option expr :=
  if forallb smt_term args && negb (forallb smt_ground args)
  then rewrite_prim p args
  else None.

Definition op_spine (p : model_primop) (args : list expr) : expr :=
  fold_left EApp args (EPrimOp p).

Definition reduce_unbranched (p : model_primop) (args : list expr) : expr :=
  if Nat.eqb (length args) (model_arity p)
  then fold_leaves (lift_branches (op_spine p args))
  else ELit false.

Fixpoint split_arg (k : expr -> expr) (a : expr) : expr :=
  match a with
  | EIf c t f => EIf c (split_arg k t) (split_arg k f)
  | _ => k a
  end.

Fixpoint split_args (k : list expr -> expr) (args : list expr) : expr :=
  match args with
  | nil => k nil
  | a :: rest => split_arg (fun a' => split_args (fun rest' => k (a' :: rest')) rest) a
  end.

Definition simplify_unbranched (p : model_primop) (args : list expr) : expr :=
  match simplify p args with
  | Some r => r
  | None => reduce_unbranched p args
  end.

Definition model_reduce_prim (p : model_primop) (args : list expr) : expr :=
  split_args (simplify_unbranched p) args.

Definition model_sat (Φ : path_condition) : bool := true.
Definition erase_cast (e : expr) (γ : coercion) : expr := e.
Definition keep_coercion (Γ : environment) (γ : coercion) : coercion := γ.
Definition keep_type (Γ : environment) (τ : type_fc) : type_fc := τ.

#[export] Instance model_solver : SymCoreSolver :=
  Build_SymCoreSolver
    model_sat (PCLit true) eq_refl model_reduce_prim
    erase_cast keep_coercion keep_type.

(** ========================================================================= *)
(** The laws that need no reasoning about the reducer                         *)
(** ========================================================================= *)

#[export] Instance model_cast_expr_concore : CastExprConcore.
Proof. intros e γ H. exact H. Qed.

#[export] Instance model_cast_expr_contains : CastExprContains.
Proof. intros σ S es ec γ H. exact H. Qed.

#[export] Instance model_subst_coerc_contains_env : SubstCoercContainsEnv.
Proof. intros σ S Γs Γc γ _. apply Cont_Coercion. Qed.

#[export] Instance model_subst_type_contains_env : SubstTypeContainsEnv.
Proof. intros σ S Γs Γc τ _. apply Cont_Type. Qed.

#[export] Instance model_models_sat : ModelsSat.
Proof. intros σ Φ _. reflexivity. Qed.

#[export] Instance model_prim_value_and : PrimValueAnd.
Proof. intros l1 l2. apply andb_true_iff. Qed.

#[export] Instance model_cast_expr_keeps_out_of_fuel : CastExprKeepsOutOfFuel.
Proof. intros e γ H. exact H. Qed.

