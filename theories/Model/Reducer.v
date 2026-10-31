From SymCoreTheory Require Export SymCore.Syntax.
From Stdlib Require Import Lists.List Bool.Bool.
Import ListNotations.

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

Lemma model_prim_value_and_spec : forall a b : bool,
  model_prim_value PAnd [a; b] = true <-> a = true /\ b = true.
Proof. intros a b. apply andb_true_iff. Qed.

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
    model_prim_value true model_prim_value_and_spec
    model_prim_value_not_spec model_prim_value_ite_spec.

Fixpoint all_literals (ps : list prim) : option (list lit) :=
  match ps with
  | [] => Some []
  | PLit l :: rest => option_map (cons l) (all_literals rest)
  | _ => None
  end.

Lemma all_literals_map_plit : forall ls, all_literals (map PLit ls) = Some ls.
Proof.
  induction ls as [| l rest IH]; [reflexivity |].
  cbn [map all_literals]. rewrite IH. reflexivity.
Qed.

Lemma all_literals_sound : forall ps ls, all_literals ps = Some ls -> ps = map PLit ls.
Proof.
  induction ps as [| p rest IH]; intros ls H; simpl in H.
  - injection H as <-. reflexivity.
  - destruct p; try discriminate.
    destruct (all_literals rest) as [ls'|] eqn:E; simpl in H; [| discriminate].
    injection H as <-. simpl. f_equal. apply IH. reflexivity.
Qed.

Definition model_reduce_prim (op : primop) (ps : list prim) : value :=
  match all_literals ps with
  | Some ls =>
      if Nat.eqb (length ls) (primop_arity op)
      then VPrim (PLit (prim_value op ls))
      else VPrim (PApp op ps)
  | None => VPrim (PApp op ps)
  end.
