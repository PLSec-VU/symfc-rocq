(**
  Model.v - One intended model of every parameter and law of SymCore.v and
  ConCore.v.

  Literals are the Booleans. The primitive operations are conjunction,
  negation and if-then-else, read the way the Booleans read them. A branch
  inside an argument is lifted out of the application first, so the reducer
  answers a branch of reduced terms. The reducer folds an application whose
  arguments are closed. When every argument is an SMT term and some argument
  is not closed, it also simplifies as an SMT solver does: and false z and
  and z false become false, ite true a b becomes a, ite false a b becomes b,
  and ite c a a becomes a. It leaves any other application as a residual term.
*)

From SymCoreTheory Require Import SymCore ConCore CostLaws.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.

(** ========================================================================= *)
(** 1. Sorts                                                                   *)
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

#[export] Instance model_sorts : SymCoreSorts :=
  Build_SymCoreSorts
    bool model_primop PAnd PNot PIte model_arity eq_refl
    bool_dec model_primop_eq_dec unit model_tycon_eq_dec
    model_prim_value true.

Lemma model_prim_value_wrong_arity : forall p ls,
  length ls <> model_arity p -> model_prim_value p ls = false.
Proof.
  intros p ls H.
  destruct p; destruct ls as [| a [| b [| c [| d ls]]]]; simpl in *; congruence.
Qed.

(** ========================================================================= *)
(** 2. The reducer                                                             *)
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

Lemma model_reduce_prim_folds :
  reduce_prim op_and (ELit true :: ELit false :: nil) = ELit false.
Proof. reflexivity. Qed.

Lemma model_reduce_prim_leaves_residual :
  reduce_prim op_and (EVar "x"%string :: ELit true :: nil)
  = EApp (EApp (EPrimOp PAnd) (EVar "x"%string)) (ELit true).
Proof. reflexivity. Qed.

Lemma model_and_false_left :
  reduce_prim op_and (ELit false :: EVar "z"%string :: nil) = ELit false.
Proof. reflexivity. Qed.

Lemma model_and_false_right :
  reduce_prim op_and (EVar "z"%string :: ELit false :: nil) = ELit false.
Proof. reflexivity. Qed.

Lemma model_ite_true :
  reduce_prim op_ite (ELit true :: EVar "z"%string :: EVar "w"%string :: nil) = EVar "z"%string.
Proof. reflexivity. Qed.

Lemma model_ite_false :
  reduce_prim op_ite (ELit false :: EVar "z"%string :: EVar "w"%string :: nil) = EVar "w"%string.
Proof. reflexivity. Qed.

Lemma model_ite_same_arms :
  reduce_prim op_ite (EVar "z"%string :: ELit true :: ELit true :: nil) = ELit true.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** 3. The laws that need no reasoning about the reducer                       *)
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

(** ========================================================================= *)
(** 4. Lifting branches out of an application                                  *)
(** ========================================================================= *)

Fixpoint flat (e : expr) : bool :=
  match e with
  | EIf _ _ _ => false
  | EApp f a => flat f && flat a
  | _ => true
  end.

Lemma flat_not_if : forall e, flat e = true -> is_if e = false.
Proof. intros e H. destruct e; simpl in *; congruence. Qed.

Lemma graft_arg_not_if : forall f a, is_if a = false -> graft_arg f a = EApp f a.
Proof. intros f a H. destruct a; simpl in *; congruence. Qed.

Lemma graft_not_if : forall f a,
  is_if f = false -> is_if a = false -> graft f a = EApp f a.
Proof.
  intros f a Hf Ha. destruct f; simpl in Hf; try discriminate; simpl;
    apply graft_arg_not_if; exact Ha.
Qed.

Lemma lift_flat : forall e, flat e = true -> lift_branches e = e.
Proof.
  induction e; intros H; simpl in *; try reflexivity; try discriminate.
  apply andb_prop in H as [H1 H2].
  rewrite (IHe1 H1), (IHe2 H2). apply graft_not_if; apply flat_not_if; assumption.
Qed.

Lemma solvable_flat : forall Γ e, Solvable Γ e -> flat e = true.
Proof.
  intros Γ e H. induction H; simpl; try reflexivity.
  rewrite IHSolvable1, IHSolvable2. reflexivity.
Qed.

Lemma concore_flat : forall e, concore_expr e -> flat e = true.
Proof.
  induction e; intros H; simpl; try reflexivity.
  - inversion H; subst. rewrite IHe1, IHe2 by assumption. reflexivity.
  - exfalso. exact (not_concore_if _ _ _ H).
Qed.

Lemma denotes_flat : forall S e pc, denotes S e pc -> flat e = true.
Proof. intros S e pc H. exact (solvable_flat · e (denotes_solvable S e pc H)). Qed.

Lemma contains_flat_instance : forall σ S e X, contains σ S e X -> flat X = true.
Proof.
  intros σ S e X H. induction H; simpl; try reflexivity; try assumption.
  rewrite IHcontains1, IHcontains2. reflexivity.
Qed.

Inductive picks (σ : valuation) (S : symvars) : expr -> expr -> Prop :=
  | picks_leaf : forall e, is_if e = false -> picks σ S e e
  | picks_then : forall c t f L,
      models_cond σ S c -> picks σ S t L -> picks σ S (EIf c t f) L
  | picks_else : forall c t f L,
      models_not_cond σ S c -> picks σ S f L -> picks σ S (EIf c t f) L.

Lemma picks_contains : forall σ S T L Y,
  picks σ S T L -> contains σ S L Y -> contains σ S T Y.
Proof.
  intros σ S T L Y H. induction H; intros Hc;
    [exact Hc | apply Cont_If_True | apply Cont_If_False]; auto.
Qed.

Lemma picks_graft_arg : forall σ S L1 T2 L2,
  is_if L1 = false -> picks σ S T2 L2 -> picks σ S (graft_arg L1 T2) (EApp L1 L2).
Proof.
  intros σ S L1 T2 L2 H1 H. induction H.
  - rewrite graft_arg_not_if by assumption. apply picks_leaf. reflexivity.
  - simpl. apply picks_then; assumption.
  - simpl. apply picks_else; assumption.
Qed.

Lemma picks_graft : forall σ S T1 L1 T2 L2,
  picks σ S T1 L1 -> picks σ S T2 L2 -> picks σ S (graft T1 T2) (EApp L1 L2).
Proof.
  intros σ S T1 L1 T2 L2 H1 H2. induction H1.
  - destruct e; simpl in H; try discriminate; simpl;
      apply picks_graft_arg; try reflexivity; exact H2.
  - simpl. apply picks_then; assumption.
  - simpl. apply picks_else; assumption.
Qed.

Lemma lift_picks : forall σ S e X,
  contains σ S e X ->
  exists L, picks σ S (lift_branches e) L /\ contains σ S L X /\ flat L = true.
Proof.
  intros σ S e X H. induction H;
    try (eexists; split; [apply picks_leaf; reflexivity
                         | split; [simpl; solve [econstructor; eassumption] | reflexivity]]).
  - destruct IHcontains1 as [L1 [P1 [C1 F1]]].
    destruct IHcontains2 as [L2 [P2 [C2 F2]]].
    exists (EApp L1 L2). split; [simpl; apply picks_graft; assumption |].
    split; [apply Cont_App; assumption | simpl; rewrite F1, F2; reflexivity].
  - destruct IHcontains as [L [P [C F]]].
    exists L. split; [simpl; apply picks_then; assumption | split; assumption].
  - destruct IHcontains as [L [P [C F]]].
    exists L. split; [simpl; apply picks_else; assumption | split; assumption].
  - assert (Hflat : flat es = true)
      by (destruct H2 as [pc [Hd _]]; exact (denotes_flat S es pc Hd)).
    exists es. rewrite (lift_flat es Hflat).
    split; [apply picks_leaf; apply flat_not_if; exact Hflat |].
    split; [eapply Cont_Denote; eassumption | exact Hflat].
Qed.

Inductive leaves (P : expr -> Prop) : expr -> Prop :=
  | leaves_leaf : forall e, is_if e = false -> P e -> leaves P e
  | leaves_if : forall c t f, leaves P t -> leaves P f -> leaves P (EIf c t f).

Lemma picks_leaves : forall σ S (P : expr -> Prop) T L,
  picks σ S T L -> leaves P T -> P L.
Proof.
  intros σ S P T L H. induction H; intros HT; inversion HT; subst; simpl in *;
    try discriminate; auto.
Qed.

Lemma leaves_mono : forall (P Q : expr -> Prop) T,
  (forall e, P e -> Q e) -> leaves P T -> leaves Q T.
Proof.
  intros P Q T HPQ H. induction H; [apply leaves_leaf; auto | apply leaves_if; auto].
Qed.

Definition app_of (P Q : expr -> Prop) (e : expr) : Prop :=
  exists f a, e = EApp f a /\ P f /\ Q a.

Lemma leaves_graft_arg : forall (P Q : expr -> Prop) f A,
  is_if f = false -> P f -> leaves Q A -> leaves (app_of P Q) (graft_arg f A).
Proof.
  intros P Q f A Hf Pf H. induction H.
  - rewrite graft_arg_not_if by assumption.
    apply leaves_leaf; [reflexivity | exists f, e; auto].
  - simpl. apply leaves_if; assumption.
Qed.

Lemma leaves_graft : forall (P Q : expr -> Prop) F A,
  leaves P F -> leaves Q A -> leaves (app_of P Q) (graft F A).
Proof.
  intros P Q F A HF HA. induction HF.
  - destruct e; simpl in H; try discriminate; simpl;
      apply leaves_graft_arg; try reflexivity; assumption.
  - simpl. apply leaves_if; assumption.
Qed.

Lemma leaves_lift_any : forall e, leaves (fun _ => True) (lift_branches e).
Proof.
  induction e; simpl; try (apply leaves_leaf; [reflexivity | exact I]).
  - apply (leaves_mono (app_of (fun _ => True) (fun _ => True))); [intros; exact I |].
    apply leaves_graft; assumption.
  - apply leaves_if; assumption.
Qed.

Definition spine_of (p : model_primop) (n : nat) (e : expr) : Prop :=
  exists L, e = op_spine p L /\ length L = n.

Lemma op_spine_snoc : forall p args a,
  op_spine p (args ++ a :: nil) = EApp (op_spine p args) a.
Proof. intros p args a. unfold op_spine. rewrite fold_left_app. reflexivity. Qed.

Lemma op_spine_unspool : forall p L, unspool_app (op_spine p L) nil = (EPrimOp p, L).
Proof. intros p L. unfold op_spine. rewrite unspool_fold_left_app, app_nil_r. reflexivity. Qed.

Lemma op_spine_not_if : forall p L, is_if (op_spine p L) = false.
Proof.
  intros p L. induction L as [| a L IH] using rev_ind; [reflexivity |].
  rewrite op_spine_snoc. reflexivity.
Qed.

Lemma leaves_lift_spine : forall p args,
  leaves (spine_of p (length args)) (lift_branches (op_spine p args)).
Proof.
  intros p args. induction args as [| a args IH] using rev_ind.
  - apply leaves_leaf; [reflexivity | exists nil; split; reflexivity].
  - rewrite op_spine_snoc. cbn [lift_branches].
    apply (leaves_mono (app_of (spine_of p (length args)) (fun _ => True))).
    + intros e [f [b [He [[L [Hf HL]] _]]]]. exists (L ++ b :: nil)%list.
      subst. rewrite op_spine_snoc, !length_app, HL. split; reflexivity.
    + apply leaves_graft; [exact IH | apply leaves_lift_any].
Qed.

Lemma fold_leaves_not_if : forall e, is_if e = false -> fold_leaves e = fold_leaf e.
Proof. intros e H. destruct e; simpl in *; congruence. Qed.

Lemma fold_leaf_not_if : forall e, is_if e = false -> is_if (fold_leaf e) = false.
Proof. intros e H. unfold fold_leaf. destruct (smt_ground e); [reflexivity | exact H]. Qed.

Lemma picks_fold_leaves : forall σ S T L,
  picks σ S T L -> picks σ S (fold_leaves T) (fold_leaf L).
Proof.
  intros σ S T L H. induction H.
  - rewrite fold_leaves_not_if by assumption.
    apply picks_leaf. apply fold_leaf_not_if. assumption.
  - simpl. apply picks_then; assumption.
  - simpl. apply picks_else; assumption.
Qed.

Lemma op_spine_flat : forall p args,
  Forall (fun a => flat a = true) args -> flat (op_spine p args) = true.
Proof.
  intros p args H. unfold op_spine.
  assert (Hh : flat (EPrimOp p) = true) by reflexivity.
  revert Hh. generalize (EPrimOp p). induction H as [| a args Ha Hargs IH]; intros h Hh.
  - exact Hh.
  - simpl. apply IH. simpl. rewrite Hh, Ha. reflexivity.
Qed.

(** ========================================================================= *)
(** 5. The value of a closed term does not depend on the model                *)
(** ========================================================================= *)

Lemma ground_pc_value : forall e pc σ1 σ2,
  smt_ground e = true -> expr_to_pc · e = Some pc ->
  pc_value σ1 pc = pc_value σ2 pc
  /\ (forall q qs, pc = PCPrim q qs -> map (pc_value σ1) qs = map (pc_value σ2) qs).
Proof.
  induction e; intros pc σ1 σ2 Hg Hpc; simpl in Hg; try discriminate.
  - simpl in Hpc. injection Hpc as <-.
    split; [reflexivity | intros q qs Heq; discriminate Heq].
  - simpl in Hpc. injection Hpc as <-.
    split; [reflexivity | intros q qs Heq; injection Heq as <- <-; reflexivity].
  - apply andb_prop in Hg as [Hg12 Hga]. apply andb_prop in Hg12 as [Hop Hgf].
    simpl in Hpc. destruct (expr_to_pc · e1) as [pf |] eqn:E1; [| discriminate].
    destruct pf as [v | l | q qs];
      try (destruct (expr_to_pc · e2); simpl in Hpc; discriminate).
    destruct (expr_to_pc · e2) as [pa |] eqn:E2; [| discriminate].
    injection Hpc as <-.
    destruct (IHe1 _ σ1 σ2 Hgf eq_refl) as [_ Hmap].
    destruct (IHe2 _ σ1 σ2 Hga eq_refl) as [Hva _].
    specialize (Hmap q qs eq_refl).
    assert (Hl : map (pc_value σ1) (qs ++ pa :: nil) = map (pc_value σ2) (qs ++ pa :: nil)).
    { rewrite !map_app, Hmap. cbn [map]. rewrite Hva. reflexivity. }
    split.
    + change (prim_value q (map (pc_value σ1) (qs ++ pa :: nil))
              = prim_value q (map (pc_value σ2) (qs ++ pa :: nil))).
      rewrite Hl. reflexivity.
    + intros q' qs' Heq. injection Heq as <- <-. exact Hl.
Qed.

Lemma closed_value_of : forall e pc,
  expr_to_pc · e = Some pc -> closed_value e = pc_value closed_model pc.
Proof. intros e pc H. unfold closed_value. rewrite H. reflexivity. Qed.

Lemma ground_instance_denotes : forall σ S L X,
  contains σ S L X -> flat L = true -> smt_ground X = true ->
  exists pcL pcX,
    denotes S L pcL /\ expr_to_pc · X = Some pcX /\
    pc_value σ pcL = pc_value closed_model pcX /\
    (is_op_app X = true ->
       exists q qsL qsX, pcL = PCPrim q qsL /\ pcX = PCPrim q qsX /\
         map (pc_value σ) qsL = map (pc_value closed_model) qsX).
Proof.
  intros σ S L X H. induction H; intros HfL HgX; simpl in HfL, HgX; try discriminate.
  - exists (PCVar x), (PCLit (σ x)).
    split; [intros Γ Hfree; simpl; rewrite (Hfree x H); reflexivity |].
    split; [reflexivity | split; [reflexivity | intros Hop; discriminate Hop]].
  - exists (PCLit l), (PCLit l).
    split; [intros Γ _; reflexivity |].
    split; [reflexivity | split; [reflexivity | intros Hop; discriminate Hop]].
  - exists (PCPrim p nil), (PCPrim p nil).
    split; [intros Γ _; reflexivity |].
    split; [reflexivity | split; [reflexivity |]].
    intros _. exists p, nil, nil. repeat split.
  - apply andb_prop in HgX as [HgX12 HgXa]. apply andb_prop in HgX12 as [HopX HgXf].
    apply andb_prop in HfL as [HfLf HfLa].
    destruct (IHcontains1 HfLf HgXf) as [pf [pfX [Hdf [Hef [_ Hopf]]]]].
    destruct (IHcontains2 HfLa HgXa) as [pa [paX [Hda [Hea [Hva _]]]]].
    destruct (Hopf HopX) as [q [qs [qsX [-> [-> Hmap]]]]].
    assert (Hl : map (pc_value σ) (qs ++ pa :: nil)
                 = map (pc_value closed_model) (qsX ++ paX :: nil)).
    { rewrite !map_app, Hmap. cbn [map]. rewrite Hva. reflexivity. }
    exists (PCPrim q (qs ++ pa :: nil)), (PCPrim q (qsX ++ paX :: nil)).
    split; [| split; [| split]].
    + intros Γ Hfree. simpl. rewrite (Hdf Γ Hfree), (Hda Γ Hfree). reflexivity.
    + simpl. rewrite Hef, Hea. reflexivity.
    + change (prim_value q (map (pc_value σ) (qs ++ pa :: nil))
              = prim_value q (map (pc_value closed_model) (qsX ++ paX :: nil))).
      rewrite Hl. reflexivity.
    + intros _. exists q, (qs ++ pa :: nil), (qsX ++ paX :: nil).
      split; [reflexivity | split; [reflexivity | exact Hl]].
  - exfalso. destruct ec; discriminate.
  - destruct H2 as [pc [Hd Hv]].
    exists pc, (PCLit l).
    split; [exact Hd | split; [reflexivity | split; [exact Hv | intros Hop; discriminate Hop]]].
Qed.

Lemma op_spine_denotes : forall S args pcs,
  Forall2 (denotes S) args pcs ->
  forall h q acc, denotes S h (PCPrim q acc) ->
  denotes S (fold_left EApp args h) (PCPrim q (acc ++ pcs)).
Proof.
  intros S args pcs H. induction H as [| a pa args pcs Ha Hargs IH]; intros h q acc Hh.
  - rewrite app_nil_r. exact Hh.
  - simpl. replace (acc ++ pa :: pcs) with ((acc ++ pa :: nil) ++ pcs)
      by (rewrite <- app_assoc; reflexivity).
    apply IH. intros Γ Hfree. simpl. rewrite (Hh Γ Hfree), (Ha Γ Hfree). reflexivity.
Qed.

(** ========================================================================= *)
(** 6. The laws about the reducer                                              *)
(** ========================================================================= *)

Lemma leaf_contains : forall σ S p L X,
  spine_of p (model_arity p) L ->
  contains σ S L X -> flat L = true ->
  contains σ S (fold_leaf L) (fold_leaf X).
Proof.
  intros σ S p L X [L' [-> HL']] Hc HfL.
  unfold fold_leaf.
  destruct (smt_ground X) eqn:HgX; destruct (smt_ground (op_spine p L')) eqn:HgL.
  - rewrite (closed_smt_term_is_rigid σ S _ _ HgL Hc). apply Cont_Lit.
  - destruct (ground_instance_denotes σ S _ _ Hc HfL HgX) as [pcL [pcX [HdL [HeX [Hv _]]]]].
    apply (Cont_Denote σ S (op_spine p L') p L').
    + apply op_spine_unspool.
    + exact HL'.
    + exact HgL.
    + exists pcL. split; [exact HdL |]. rewrite (closed_value_of X pcX HeX). exact Hv.
  - pose proof (closed_smt_term_is_rigid σ S _ _ HgL Hc) as E.
    rewrite E in HgL. congruence.
  - exact Hc.
Qed.

Lemma unbranched_contains : forall σ S p args_s args_c,
  Forall2 (contains σ S) args_s args_c ->
  contains σ S (reduce_unbranched p args_s) (reduce_unbranched p args_c).
Proof.
  intros σ S p args_s args_c HF.
  unfold reduce_unbranched. rewrite <- (Forall2_length HF).
  destruct (Nat.eqb (length args_s) (model_arity p)) eqn:Hlen; [| apply Cont_Lit].
  apply Nat.eqb_eq in Hlen.
  assert (Hc : contains σ S (op_spine p args_s) (op_spine p args_c))
    by (apply contains_fold_left_app; [exact HF | apply Cont_PrimOp]).
  rewrite (lift_flat _ (contains_flat_instance σ S _ _ Hc)),
          (fold_leaves_not_if _ (op_spine_not_if p args_c)).
  destruct (lift_picks σ S _ _ Hc) as [L [Hp [HcL HfL]]].
  apply (picks_contains σ S _ (fold_leaf L)); [apply picks_fold_leaves; exact Hp |].
  apply (leaf_contains σ S p L); [| exact HcL | exact HfL].
  rewrite <- Hlen. exact (picks_leaves σ S _ _ _ Hp (leaves_lift_spine p args_s)).
Qed.

Lemma denote_args : forall σ S args ls,
  Forall2 (denote σ S) args ls ->
  exists pcs, Forall2 (denotes S) args pcs /\ map (pc_value σ) pcs = ls.
Proof.
  intros σ S args ls H.
  induction H as [| a l args ls [pc [Hd Hv]] _ [pcs [Hds Hvs]]].
  - exists nil. split; [constructor | reflexivity].
  - exists (pc :: pcs). split; [constructor; assumption |].
    cbn [map]. rewrite Hv, Hvs. reflexivity.
Qed.

Lemma denotes_all_flat : forall S args pcs,
  Forall2 (denotes S) args pcs -> Forall (fun a => flat a = true) args.
Proof.
  intros S args pcs H. induction H; constructor; [eapply denotes_flat; eassumption | assumption].
Qed.

Lemma unbranched_denote : forall σ S (p : primop) args ls,
  Forall2 (denote σ S) args ls ->
  denote σ S (reduce_unbranched p args) (prim_value p ls).
Proof.
  intros σ S p args ls HF.
  unfold reduce_unbranched.
  destruct (denote_args σ S args ls HF) as [pcs [Hds Hvs]].
  destruct (Nat.eqb (length args) (model_arity p)) eqn:Hlen.
  - rewrite (lift_flat _ (op_spine_flat p args (denotes_all_flat S args pcs Hds))),
            (fold_leaves_not_if _ (op_spine_not_if p args)).
    assert (Hd : denotes S (op_spine p args) (PCPrim p pcs))
      by (apply (op_spine_denotes S args pcs Hds (EPrimOp p) p nil); intros Γ _; reflexivity).
    assert (Hv : pc_value σ (PCPrim p pcs) = prim_value p ls)
      by (change (prim_value p (map (pc_value σ) pcs) = prim_value p ls); rewrite Hvs; reflexivity).
    unfold fold_leaf. destruct (smt_ground (op_spine p args)) eqn:Hg.
    + pose proof (Hd · (sym_free_env_empty S)) as He.
      rewrite (closed_value_of _ _ He).
      destruct (ground_pc_value _ _ closed_model σ Hg He) as [Hcl _].
      rewrite Hcl, Hv. apply denote_lit.
    + exists (PCPrim p pcs). split; [exact Hd | exact Hv].
  - apply Nat.eqb_neq in Hlen.
    change (prim_value p ls) with (model_prim_value p ls).
    rewrite model_prim_value_wrong_arity; [apply denote_lit |].
    rewrite <- Hvs, length_map, <- (Forall2_length Hds). exact Hlen.
Qed.

Lemma fold_leaves_ground : forall T,
  smt_ground (fold_leaves T) = true -> exists l, fold_leaves T = ELit l.
Proof.
  intros T H. destruct (is_if T) eqn:Hif.
  - destruct T; simpl in Hif, H; discriminate.
  - rewrite (fold_leaves_not_if T Hif) in *. unfold fold_leaf in *.
    destruct (smt_ground T) eqn:Hg; [eexists; reflexivity | congruence].
Qed.

Lemma unbranched_ground_value : forall p args,
  smt_ground (reduce_unbranched p args) = true ->
  exists l, reduce_unbranched p args = ELit l.
Proof.
  intros p args H.
  unfold reduce_unbranched in *.
  destruct (Nat.eqb (length args) (model_arity p));
    [apply fold_leaves_ground; exact H | eexists; reflexivity].
Qed.

Lemma unbranched_saturated : forall p args p0 args0,
  unspool_app (reduce_unbranched p args) nil = (EPrimOp p0, args0) ->
  length args0 = model_arity p0.
Proof.
  intros p args p0 args0 H.
  unfold reduce_unbranched in H.
  destruct (Nat.eqb (length args) (model_arity p)) eqn:Hlen; [| discriminate H].
  apply Nat.eqb_eq in Hlen.
  revert H. generalize (leaves_lift_spine p args).
  generalize (lift_branches (op_spine p args)). intros T Hl.
  destruct Hl as [e Hif [L [-> HL]] | c t f _ _]; intros H.
  - rewrite (fold_leaves_not_if _ Hif) in H. unfold fold_leaf in H.
    destruct (smt_ground (op_spine p L)); [simpl in H; discriminate H |].
    rewrite op_spine_unspool in H. injection H as <- <-. rewrite HL. exact Hlen.
  - simpl in H. discriminate H.
Qed.

Lemma solvable_op_spine : forall Γ args h,
  Solvable Γ h -> is_op_app h = true -> Forall (Solvable Γ) args ->
  Solvable Γ (fold_left EApp args h).
Proof.
  intros Γ args h Hh Hop HF. revert h Hh Hop.
  induction HF as [| a args Ha Hargs IH]; intros h Hh Hop; [exact Hh |].
  simpl. apply IH; [apply Solvable_AppPrim; [exact Hop | exact Hh | exact Ha] | exact Hop].
Qed.

Lemma unbranched_solvable : forall Γ p args,
  Forall (Solvable Γ) args -> Solvable Γ (reduce_unbranched p args).
Proof.
  intros Γ p args HF. unfold reduce_unbranched.
  destruct (Nat.eqb (length args) (model_arity p)); [| apply Solvable_Lit].
  assert (Hs : Solvable Γ (op_spine p args))
    by (apply solvable_op_spine; [apply Solvable_PrimOp | reflexivity | exact HF]).
  rewrite (lift_flat _ (solvable_flat Γ _ Hs)), (fold_leaves_not_if _ (op_spine_not_if p args)).
  unfold fold_leaf. destruct (smt_ground (op_spine p args)); [apply Solvable_Lit | exact Hs].
Qed.

Lemma unbranched_concore : forall p args,
  Forall concore_expr args -> concore_expr (reduce_unbranched p args).
Proof.
  intros p args HF. unfold reduce_unbranched.
  destruct (Nat.eqb (length args) (model_arity p)); [| apply Con_Lit].
  assert (Hc : concore_expr (op_spine p args))
    by (apply concore_fold_left_app; [exact HF | apply Con_PrimOp]).
  rewrite (lift_flat _ (concore_flat _ Hc)), (fold_leaves_not_if _ (op_spine_not_if p args)).
  unfold fold_leaf. destruct (smt_ground (op_spine p args)); [apply Con_Lit | exact Hc].
Qed.

Lemma ite_selects_arm : forall σ S ec et ef pt pf l,
  denotes S et pt -> denotes S ef pf ->
  contains σ S (EIf ec et ef) (ELit l) ->
  exists pc, denotes S ec pc /\ pc_value σ (PCPrim PIte (pc :: pt :: pf :: nil)) = l.
Proof.
  intros σ S ec et ef pt pf l Ht Hf Hc.
  destruct (contains_if_inv σ S ec et ef (ELit l) Hc)
    as [[[pc [Hd Hm]] Hct] | [[pc [Hd Hm]] Hcf]]; exists pc; split; try exact Hd.
  - pose proof (smt_concretion_determined σ S et _ l (ex_intro _ pt (conj Ht eq_refl)) Hct) as Hl.
    change ((if pc_value σ pc then pc_value σ pt else pc_value σ pf) = l).
    change (pc_value σ pc = true) in Hm. rewrite Hm. exact Hl.
  - pose proof (smt_concretion_determined σ S ef _ l (ex_intro _ pf (conj Hf eq_refl)) Hcf) as Hl.
    change ((if pc_value σ pc then pc_value σ pt else pc_value σ pf) = l).
    change (negb (pc_value σ pc) = true) in Hm. apply negb_true_iff in Hm. rewrite Hm. exact Hl.
Qed.

Lemma unbranched_ite_contains : forall σ S ec et ef pt pf l,
  denotes S et pt -> denotes S ef pf ->
  contains σ S (EIf ec et ef) (ELit l) ->
  contains σ S (reduce_unbranched PIte (ec :: et :: ef :: nil)) (ELit l).
Proof.
  intros σ S ec et ef pt pf l Ht Hf Hc.
  destruct (ite_selects_arm σ S ec et ef pt pf l Ht Hf Hc) as [pc [Hdc Hv]].
  unfold reduce_unbranched.
  replace (Nat.eqb (length (ec :: et :: ef :: nil)) (model_arity PIte)) with true by reflexivity.
  assert (Hflat : flat (op_spine PIte (ec :: et :: ef :: nil)) = true).
  { apply op_spine_flat.
    repeat constructor; eapply denotes_flat; eassumption. }
  rewrite (lift_flat _ Hflat), (fold_leaves_not_if _ (op_spine_not_if _ _)).
  assert (Hd : denotes S (op_spine PIte (ec :: et :: ef :: nil)) (PCPrim PIte (pc :: pt :: pf :: nil))).
  { apply (op_spine_denotes S (ec :: et :: ef :: nil) (pc :: pt :: pf :: nil) ltac:(repeat constructor; assumption) (EPrimOp op_ite) op_ite nil).
    intros Γ _. reflexivity. }
  unfold fold_leaf. destruct (smt_ground (op_spine PIte (ec :: et :: ef :: nil))) eqn:Hg.
  - pose proof (Hd · (sym_free_env_empty S)) as He.
    rewrite (closed_value_of _ _ He).
    destruct (ground_pc_value _ _ closed_model σ Hg He) as [Hcl _].
    rewrite Hcl, Hv. apply Cont_Lit.
  - apply (Cont_Denote σ S _ op_ite (ec :: et :: ef :: nil) l).
    + apply op_spine_unspool.
    + reflexivity.
    + exact Hg.
    + exists (PCPrim op_ite (pc :: pt :: pf :: nil)). split; [exact Hd | exact Hv].
Qed.

Lemma split_arg_not_if : forall k a, is_if a = false -> split_arg k a = k a.
Proof. intros k a H. destruct a; simpl in *; congruence. Qed.

Lemma split_args_not_if : forall k args,
  Forall (fun a => is_if a = false) args -> split_args k args = k args.
Proof.
  intros k args H. revert k. induction H as [| a args Ha _ IH]; intros k; [reflexivity |].
  cbn [split_args]. rewrite split_arg_not_if by exact Ha. apply IH.
Qed.

Lemma split_args_top : forall k args,
  split_args k args = k args \/ is_if (split_args k args) = true.
Proof.
  intros k args. revert k. induction args as [| a rest IH]; intros k; [left; reflexivity |].
  cbn [split_args]. destruct (is_if a) eqn:Ha.
  - destruct a; simpl in Ha; try discriminate. right. reflexivity.
  - rewrite split_arg_not_if by exact Ha. apply (IH (fun rest' => k (a :: rest'))).
Qed.

Lemma split_args_branch : forall k pre ec et ef post,
  Forall (fun e => is_if e = false) pre ->
  split_args k (pre ++ EIf ec et ef :: post) =
  EIf ec (split_args k (pre ++ et :: post)) (split_args k (pre ++ ef :: post)).
Proof.
  intros k pre ec et ef post H. revert k.
  induction H as [| a pre Ha _ IH]; intros k; [reflexivity |].
  cbn [app split_args]. rewrite !split_arg_not_if by exact Ha. apply IH.
Qed.

Lemma flat_all_not_if : forall args,
  Forall (fun a => flat a = true) args -> Forall (fun a => is_if a = false) args.
Proof. intros args H. eapply Forall_impl; [| exact H]. exact flat_not_if. Qed.

Lemma contains_picks_top : forall σ S e X,
  contains σ S e X -> exists L, picks σ S e L /\ contains σ S L X.
Proof.
  intros σ S e. induction e; intros X H;
    try (eexists; split; [apply picks_leaf; reflexivity | exact H]).
  destruct (contains_if_inv σ S _ _ _ X H) as [[Hm Hc] | [Hm Hc]].
  - destruct (IHe2 X Hc) as [L [Hp HL]]. exists L. split; [apply picks_then |]; assumption.
  - destruct (IHe3 X Hc) as [L [Hp HL]]. exists L. split; [apply picks_else |]; assumption.
Qed.

Lemma contains_args_picks : forall σ S args_s args_c,
  Forall2 (contains σ S) args_s args_c ->
  exists ls, Forall2 (picks σ S) args_s ls /\ Forall2 (contains σ S) ls args_c.
Proof.
  intros σ S args_s args_c H.
  induction H as [| a c args_s args_c Ha _ [ls [Hp Hc]]]; [exists nil; split; constructor |].
  destruct (contains_picks_top σ S a c Ha) as [L [HpL HcL]].
  exists (L :: ls). split; constructor; assumption.
Qed.

Lemma picks_split_arg : forall σ S K a L Y,
  picks σ S a L -> contains σ S (K L) Y -> contains σ S (split_arg K a) Y.
Proof.
  intros σ S K a L Y H. induction H; intros HK;
    [rewrite split_arg_not_if by assumption; exact HK
    | apply Cont_If_True; auto
    | apply Cont_If_False; auto].
Qed.

Lemma picks_split_args : forall σ S args ls,
  Forall2 (picks σ S) args ls ->
  forall k Y, contains σ S (k ls) Y -> contains σ S (split_args k args) Y.
Proof.
  intros σ S args ls H.
  induction H as [| a L args ls Ha _ IH]; intros k Y Hk; [exact Hk |].
  cbn [split_args]. apply (picks_split_arg σ S _ a L Y Ha).
  apply (IH (fun rest' => k (L :: rest'))). exact Hk.
Qed.

Lemma contains_instances_not_if : forall σ S args_s args_c,
  Forall2 (contains σ S) args_s args_c -> Forall (fun a => is_if a = false) args_c.
Proof.
  intros σ S args_s args_c H. induction H; constructor; [| assumption].
  apply flat_not_if. eapply contains_flat_instance. eassumption.
Qed.

Lemma smt_term_need : forall e, smt_term e = true -> smt_need e = Some 0.
Proof.
  intros e H. unfold smt_term in H.
  destruct (smt_need e) as [[| n] |]; [reflexivity | discriminate H | discriminate H].
Qed.

Lemma smt_terms_of_forallb : forall args,
  forallb smt_term args = true -> Forall (fun a => smt_need a = Some 0) args.
Proof.
  intros args H. apply Forall_forall. intros a Ha.
  apply smt_term_need. exact (proj1 (forallb_forall _ _) H a Ha).
Qed.

Lemma smt_need_app : forall f a n,
  smt_need (EApp f a) = Some n -> smt_need f = Some (Datatypes.S n) /\ smt_need a = Some 0.
Proof.
  intros f a n H. simpl in H.
  destruct (smt_need f) as [[| m] |]; destruct (smt_need a) as [[| k] |];
    try discriminate H.
  injection H as <-. split; reflexivity.
Qed.

Lemma smt_need_op_app : forall e n, smt_need e = Some (Datatypes.S n) -> is_op_app e = true.
Proof.
  induction e; intros n H; try (simpl in H; discriminate H); try reflexivity.
  destruct (smt_need_app _ _ _ H) as [H1 _]. exact (IHe1 _ H1).
Qed.

Lemma smt_need_unspool : forall e n acc (q : model_primop) qs,
  smt_need e = Some n -> unspool_app e acc = (EPrimOp q, qs) ->
  n + length qs = model_arity q + length acc.
Proof.
  induction e; intros n acc q qs Hn Hu; simpl in Hu; try discriminate Hu.
  - injection Hu as Hq Hqs. subst qs. simpl in Hn. injection Hn as <-.
    change (model_arity p + length acc = model_arity q + length acc). rewrite Hq. reflexivity.
  - destruct (smt_need_app _ _ _ Hn) as [H1 _].
    pose proof (IHe1 _ _ _ _ H1 Hu) as H. simpl in H. lia.
Qed.

Lemma smt_need_flat : forall e n, smt_need e = Some n -> flat e = true.
Proof.
  induction e; intros n H; try (simpl in H; discriminate H); try reflexivity.
  destruct (smt_need_app _ _ _ H) as [H1 H2]. simpl. rewrite (IHe1 _ H1), (IHe2 _ H2). reflexivity.
Qed.

Lemma smt_need_closed_ground : forall e n,
  smt_need e = Some n -> closed_term e -> smt_ground e = true.
Proof.
  induction e; intros n Hn Hc; try (simpl in Hn; discriminate Hn); try reflexivity.
  - unfold closed_term in Hc. inversion Hc; subst.
    match goal with [H : In _ nil |- _] => destruct H end.
  - destruct (smt_need_app _ _ _ Hn) as [H1 H2].
    unfold closed_term in Hc. inversion Hc; subst. simpl.
    rewrite (smt_need_op_app _ _ H1), (IHe1 _ H1 ltac:(assumption)), (IHe2 _ H2 ltac:(assumption)).
    reflexivity.
Qed.

Lemma contains_smt_need : forall σ S L X n,
  contains σ S L X -> smt_need L = Some n -> smt_need X = Some n.
Proof.
  intros σ S L X n H. revert n.
  induction H; intros n Hn; try (simpl in Hn; discriminate Hn); try exact Hn.
  - destruct (smt_need_app _ _ _ Hn) as [H1 H2].
    simpl. rewrite (IHcontains1 _ H1), (IHcontains2 _ H2). reflexivity.
  - match goal with
    | [ Hu : unspool_app es nil = (EPrimOp ?q, ?qs), Hl : length ?qs = primop_arity ?q |- _ ] =>
        pose proof (smt_need_unspool es n nil q qs Hn Hu) as E;
        change (length qs = model_arity q) in Hl
    end.
    simpl in E. assert (n = 0) by lia. subst n. reflexivity.
Qed.

Lemma ground_denote_value : forall σ S a l,
  smt_ground a = true -> denote σ S a l -> l = closed_value a.
Proof.
  intros σ S a l Hg [pc [Hd Hv]].
  pose proof (Hd · (sym_free_env_empty S)) as He.
  rewrite (closed_value_of a pc He), <- Hv.
  destruct (ground_pc_value a pc σ closed_model Hg He) as [E _]. exact E.
Qed.

Lemma fold_leaf_denote : forall σ S a l, denote σ S a l -> denote σ S (fold_leaf a) l.
Proof.
  intros σ S a l H. unfold fold_leaf. destruct (smt_ground a) eqn:Hg; [| exact H].
  rewrite <- (ground_denote_value σ S a l Hg H). apply denote_lit.
Qed.

Lemma fold_leaf_contains_k : forall σ S a l,
  smt_need a = Some 0 -> denote σ S a l ->
  exists k, k <= smt_size a /\ contains_k σ S k (fold_leaf a) (ELit l).
Proof.
  intros σ S a l Hn Hd. unfold fold_leaf. destruct (smt_ground a) eqn:Hg.
  - rewrite <- (ground_denote_value σ S a l Hg Hd). exists 0. split; [lia | apply ContK_Lit].
  - destruct a; try (simpl in Hg; discriminate Hg); try (simpl in Hn; discriminate Hn).
    + destruct (denote_var_inv σ S v l Hd) as [Hs ->].
      exists 0. split; [lia | apply ContK_Var_Sym; exact Hs].
    + destruct (smt_need_app _ _ _ Hn) as [H1 _].
      assert (Hop : is_op_app (EApp a1 a2) = true) by exact (smt_need_op_app _ _ H1).
      destruct (is_op_app_unspool _ Hop) as [q [qs Hu]].
      exists (smt_size (EApp a1 a2)). split; [lia |].
      apply (ContK_Denote σ S _ q qs l Hu); [| exact Hg | exact Hd].
      pose proof (smt_need_unspool _ 0 nil q qs Hn Hu) as E. simpl in E.
      change (length qs = model_arity q). lia.
Qed.

Lemma fold_leaf_ground : forall a, smt_ground (fold_leaf a) = true -> exists l, fold_leaf a = ELit l.
Proof.
  intros a H. unfold fold_leaf in *. destruct (smt_ground a) eqn:Hg; [eexists; reflexivity | congruence].
Qed.

Lemma lit_of_value : forall σ S a b l, lit_of a = Some b -> denote σ S a l -> l = b.
Proof.
  intros σ S a b l H Hd. unfold lit_of in H. destruct (smt_ground a) eqn:Hg; [| discriminate H].
  injection H as <-. exact (ground_denote_value σ S a l Hg Hd).
Qed.

Lemma is_false_lit_value : forall σ S a l, is_false_lit a = true -> denote σ S a l -> l = false.
Proof.
  intros σ S a l H Hd. unfold is_false_lit in H.
  destruct (lit_of a) as [[|] |] eqn:E; try discriminate H.
  exact (lit_of_value σ S a false l E Hd).
Qed.

Lemma rewrite_prim_arity : forall p args r,
  rewrite_prim p args = Some r -> length args = model_arity p.
Proof.
  intros p args r H.
  destruct p; destruct args as [| a1 [| a2 [| a3 [| a4 args]]]]; simpl in H; try discriminate H;
    reflexivity.
Qed.

Lemma rewrite_prim_shape : forall p args r,
  rewrite_prim p args = Some r -> r = ELit false \/ exists a, In a args /\ r = fold_leaf a.
Proof.
  intros p args r H.
  destruct p; destruct args as [| a1 [| a2 [| a3 [| a4 args]]]]; simpl in H; try discriminate H.
  - destruct (is_false_lit a1 || is_false_lit a2); [| discriminate H].
    injection H as <-. left. reflexivity.
  - destruct (lit_of a1) as [[|] |].
    + injection H as <-. right. exists a2. split; [simpl; auto | reflexivity].
    + injection H as <-. right. exists a3. split; [simpl; auto | reflexivity].
    + destruct (expr_eqb a2 a3); [| discriminate H].
      injection H as <-. right. exists a2. split; [simpl; auto | reflexivity].
Qed.

Lemma simplify_facts : forall p args r,
  simplify p args = Some r ->
  Forall (fun a => smt_need a = Some 0) args /\ rewrite_prim p args = Some r.
Proof.
  intros p args r H. unfold simplify in H.
  destruct (forallb smt_term args && negb (forallb smt_ground args)) eqn:E; [| discriminate H].
  apply andb_prop in E as [Ht _]. split; [exact (smt_terms_of_forallb args Ht) | exact H].
Qed.

Lemma rewrite_prim_value : forall σ S p args vs r,
  Forall (fun a => smt_need a = Some 0) args -> Forall2 (denote σ S) args vs ->
  rewrite_prim p args = Some r ->
  denote σ S r (model_prim_value p vs) /\
  exists k, k <= list_sum (map smt_size args) /\ contains_k σ S k r (ELit (model_prim_value p vs)).
Proof.
  intros σ S p args vs r Ht Hd Hr.
  destruct p; destruct args as [| a1 [| a2 [| a3 [| a4 args]]]]; simpl in Hr; try discriminate Hr.
  - inversion Hd as [| x1 v1 l1 vs1 Hd1 Hd1']; subst.
    inversion Hd1' as [| x2 v2 l2 vs2 Hd2 Hd2']; subst.
    inversion Hd2'; subst.
    assert (Hv : r = ELit false /\ v1 && v2 = false).
    { destruct (is_false_lit a1) eqn:E1; destruct (is_false_lit a2) eqn:E2; simpl in Hr;
        try discriminate Hr; injection Hr as <-; split; try reflexivity.
      - rewrite (is_false_lit_value σ S a1 v1 E1 Hd1). reflexivity.
      - rewrite (is_false_lit_value σ S a1 v1 E1 Hd1). reflexivity.
      - rewrite (is_false_lit_value σ S a2 v2 E2 Hd2). apply andb_false_r. }
    destruct Hv as [-> Hv]. simpl. rewrite Hv.
    split; [apply denote_lit | exists 0; split; [lia | apply ContK_Lit]].
  - inversion Hd as [| x1 v1 l1 vs1 Hd1 Hd1']; subst.
    inversion Hd1' as [| x2 v2 l2 vs2 Hd2 Hd2']; subst.
    inversion Hd2' as [| x3 v3 l3 vs3 Hd3 Hd3']; subst.
    inversion Hd3'; subst.
    inversion Ht as [| y1 t1 Ht1 Ht1']; subst.
    inversion Ht1' as [| y2 t2 Ht2 Ht2']; subst.
    inversion Ht2' as [| y3 t3 Ht3 _]; subst.
    destruct (lit_of a1) as [[|] |] eqn:Ec.
    + injection Hr as <-. rewrite (lit_of_value σ S a1 true v1 Ec Hd1).
      split; [exact (fold_leaf_denote σ S a2 v2 Hd2) |].
      destruct (fold_leaf_contains_k σ S a2 v2 Ht2 Hd2) as [k [Hk Hc]].
      exists k. split; [simpl; lia | exact Hc].
    + injection Hr as <-. rewrite (lit_of_value σ S a1 false v1 Ec Hd1).
      split; [exact (fold_leaf_denote σ S a3 v3 Hd3) |].
      destruct (fold_leaf_contains_k σ S a3 v3 Ht3 Hd3) as [k [Hk Hc]].
      exists k. split; [simpl; lia | exact Hc].
    + destruct (expr_eqb a2 a3) eqn:Eab; [| discriminate Hr].
      injection Hr as <-. apply expr_eqb_eq in Eab. subst a3.
      rewrite (denote_functional σ S a2 v3 v2 Hd3 Hd2).
      assert (Hvv : model_prim_value PIte (v1 :: v2 :: v2 :: nil) = v2) by (destruct v1; reflexivity).
      rewrite Hvv.
      split; [exact (fold_leaf_denote σ S a2 v2 Hd2) |].
      destruct (fold_leaf_contains_k σ S a2 v2 Ht2 Hd2) as [k [Hk Hc]].
      exists k. split; [simpl; lia | exact Hc].
Qed.

Lemma simplify_closed_none : forall p args, Forall closed_term args -> simplify p args = None.
Proof.
  intros p args H. unfold simplify.
  destruct (forallb smt_term args) eqn:Ht; [| reflexivity].
  assert (Hg : forallb smt_ground args = true).
  { apply forallb_forall. intros a Ha.
    apply (smt_need_closed_ground a 0).
    - apply smt_term_need. exact (proj1 (forallb_forall _ _) Ht a Ha).
    - exact (proj1 (Forall_forall _ _) H a Ha). }
  rewrite Hg. reflexivity.
Qed.

Lemma fold_leaf_solvable : forall Γ a, Solvable Γ a -> Solvable Γ (fold_leaf a).
Proof. intros Γ a H. unfold fold_leaf. destruct (smt_ground a); [apply Solvable_Lit | exact H]. Qed.

Lemma fold_leaf_concore : forall a, concore_expr a -> concore_expr (fold_leaf a).
Proof. intros a H. unfold fold_leaf. destruct (smt_ground a); [apply Con_Lit | exact H]. Qed.

Lemma fold_leaf_scoped : forall L a, scoped L a -> scoped L (fold_leaf a).
Proof. intros L a H. unfold fold_leaf. destruct (smt_ground a); [apply Scoped_Lit | exact H]. Qed.

Lemma simplify_result : forall (P : expr -> Prop) p args r,
  P (ELit false) -> Forall (fun a => P (fold_leaf a)) args ->
  simplify p args = Some r -> P r.
Proof.
  intros P p args r Hl Ha Hs.
  destruct (simplify_facts p args r Hs) as [_ Hr].
  destruct (rewrite_prim_shape p args r Hr) as [-> | [a [Hin ->]]]; [exact Hl |].
  exact (proj1 (Forall_forall _ _) Ha a Hin).
Qed.

Lemma graft_arg_scoped : forall L f a, scoped L f -> scoped L a -> scoped L (graft_arg f a).
Proof.
  intros L f a Hf. induction a; intros Ha; try (apply Scoped_App; assumption).
  inversion Ha; subst. simpl. apply Scoped_If; auto.
Qed.

Lemma graft_scoped : forall L f a, scoped L f -> scoped L a -> scoped L (graft f a).
Proof.
  intros L f a Hf Ha. induction f; try (apply graft_arg_scoped; assumption).
  inversion Hf; subst. simpl. apply Scoped_If; auto.
Qed.

Lemma lift_branches_scoped : forall L e, scoped L e -> scoped L (lift_branches e).
Proof.
  intros L e. induction e; intros H; try exact H.
  - inversion H; subst. simpl. apply graft_scoped; auto.
  - inversion H; subst. simpl. apply Scoped_If; auto.
Qed.

Lemma fold_leaves_scoped : forall L e, scoped L e -> scoped L (fold_leaves e).
Proof.
  intros L e. induction e; intros H; try (apply fold_leaf_scoped; exact H).
  inversion H; subst. simpl. apply Scoped_If; auto.
Qed.

Lemma unbranched_scoped : forall p args,
  Forall closed_term args -> closed_term (reduce_unbranched p args).
Proof.
  intros p args H. unfold reduce_unbranched.
  destruct (Nat.eqb (length args) (model_arity p)); [| apply Scoped_Lit].
  apply fold_leaves_scoped. apply lift_branches_scoped.
  apply scoped_fold_left_app; [exact H | apply Scoped_PrimOp].
Qed.

Lemma split_arg_scoped : forall K a,
  closed_term a -> (forall a', closed_term a' -> closed_term (K a')) -> closed_term (split_arg K a).
Proof.
  intros K a. induction a; intros Ha HK; try (apply HK; exact Ha).
  unfold closed_term in Ha. inversion Ha; subst. simpl.
  apply Scoped_If; [assumption | apply IHa2 | apply IHa3]; assumption.
Qed.

Lemma split_args_scoped : forall args k,
  Forall closed_term args ->
  (forall ls, Forall closed_term ls -> closed_term (k ls)) ->
  closed_term (split_args k args).
Proof.
  induction args as [| a rest IH]; intros k Hargs Hk; [apply Hk; constructor |].
  inversion Hargs; subst. cbn [split_args].
  apply split_arg_scoped; [assumption |].
  intros a' Ha'. apply IH; [assumption |].
  intros ls Hls. apply Hk. constructor; assumption.
Qed.

#[export] Instance model_reduce_prim_scoped : ReducePrimScoped.
Proof.
  intros p args H.
  change (closed_term (model_reduce_prim p args)). unfold model_reduce_prim.
  apply split_args_scoped; [exact H |].
  intros ls Hls. unfold simplify_unbranched.
  destruct (simplify p ls) as [r |] eqn:Hs; [| exact (unbranched_scoped p ls Hls)].
  apply (simplify_result closed_term p ls r ltac:(apply Scoped_Lit)); [| exact Hs].
  eapply Forall_impl; [| exact Hls]. intros a Ha. exact (fold_leaf_scoped nil a Ha).
Qed.

#[export] Instance model_cast_expr_scoped : CastExprScoped.
Proof. intros e γ H. exact H. Qed.

#[export] Instance model_reduce_prim_denote : ReducePrimDenote.
Proof.
  intros σ S p args ls HF.
  change (denote σ S (model_reduce_prim p args) (prim_value p ls)).
  unfold model_reduce_prim.
  destruct (denote_args σ S args ls HF) as [pcs [Hds _]].
  rewrite (split_args_not_if _ args (flat_all_not_if _ (denotes_all_flat S args pcs Hds))).
  unfold simplify_unbranched.
  destruct (simplify p args) as [r |] eqn:Hs; [| apply unbranched_denote; exact HF].
  destruct (simplify_facts p args r Hs) as [Ht Hr].
  exact (proj1 (rewrite_prim_value σ S p args ls r Ht HF Hr)).
Qed.

#[export] Instance model_reduce_prim_ground_value : ReducePrimGroundValue.
Proof.
  intros p args H.
  change (smt_ground (model_reduce_prim p args) = true) in H.
  change (exists l, model_reduce_prim p args = ELit l).
  unfold model_reduce_prim in *.
  destruct (split_args_top (simplify_unbranched p) args) as [E | E].
  - rewrite E in *. unfold simplify_unbranched in *.
    destruct (simplify p args) as [r |] eqn:Hs; [| apply unbranched_ground_value; exact H].
    destruct (simplify_facts p args r Hs) as [_ Hr].
    destruct (rewrite_prim_shape p args r Hr) as [-> | [a [_ ->]]];
      [eexists; reflexivity | exact (fold_leaf_ground a H)].
  - destruct (split_args (simplify_unbranched p) args); simpl in E, H; discriminate.
Qed.

#[export] Instance model_reduce_prim_saturated : ReducePrimSaturated.
Proof.
  intros p args p0 args0 H.
  change (unspool_app (model_reduce_prim p args) nil = (EPrimOp p0, args0)) in H.
  change (length args0 = model_arity p0).
  unfold model_reduce_prim in H.
  destruct (split_args_top (simplify_unbranched p) args) as [E | E].
  - rewrite E in H. unfold simplify_unbranched in H.
    destruct (simplify p args) as [r |] eqn:Hs; [| exact (unbranched_saturated p args p0 args0 H)].
    destruct (simplify_facts p args r Hs) as [Ht Hr].
    destruct (rewrite_prim_shape p args r Hr) as [-> | [a [Hin ->]]]; [discriminate H |].
    unfold fold_leaf in H. destruct (smt_ground a); [discriminate H |].
    pose proof (smt_need_unspool a 0 nil p0 args0 (proj1 (Forall_forall _ _) Ht a Hin) H) as E0.
    simpl in E0. lia.
  - destruct (split_args (simplify_unbranched p) args); simpl in E, H; discriminate.
Qed.

#[export] Instance model_reduce_prim_solvable : ReducePrimSolvable.
Proof.
  intros Γ p args HF.
  change (Solvable Γ (model_reduce_prim p args)). unfold model_reduce_prim.
  assert (Hflat : Forall (fun a => flat a = true) args)
    by (eapply Forall_impl; [| exact HF]; apply solvable_flat).
  rewrite (split_args_not_if _ args (flat_all_not_if _ Hflat)).
  unfold simplify_unbranched.
  destruct (simplify p args) as [r |] eqn:Hs; [| apply unbranched_solvable; exact HF].
  apply (simplify_result (Solvable Γ) p args r ltac:(apply Solvable_Lit)); [| exact Hs].
  eapply Forall_impl; [| exact HF]. apply fold_leaf_solvable.
Qed.

#[export] Instance model_reduce_prim_concore : ReducePrimConcore.
Proof.
  intros p args HF.
  change (concore_expr (model_reduce_prim p args)). unfold model_reduce_prim.
  assert (Hflat : Forall (fun a => flat a = true) args)
    by (eapply Forall_impl; [| exact HF]; apply concore_flat).
  rewrite (split_args_not_if _ args (flat_all_not_if _ Hflat)).
  unfold simplify_unbranched.
  destruct (simplify p args) as [r |] eqn:Hs; [| apply unbranched_concore; exact HF].
  apply (simplify_result concore_expr p args r ltac:(apply Con_Lit)); [| exact Hs].
  eapply Forall_impl; [| exact HF]. apply fold_leaf_concore.
Qed.

Inductive picks_k (σ : valuation) (S : symvars) : nat -> expr -> expr -> Prop :=
  | picks_k_leaf : forall e, is_if e = false -> picks_k σ S 0 e e
  | picks_k_then : forall k c t f L,
      models_cond σ S c -> picks_k σ S k t L -> picks_k σ S (1 + smt_size c + k) (EIf c t f) L
  | picks_k_else : forall k c t f L,
      models_not_cond σ S c -> picks_k σ S k f L -> picks_k σ S (1 + smt_size c + k) (EIf c t f) L.

Lemma picks_of_picks_k : forall σ S k T L, picks_k σ S k T L -> picks σ S T L.
Proof.
  intros σ S k T L H. induction H;
    [apply picks_leaf | apply picks_then | apply picks_else]; assumption.
Qed.

Lemma picks_k_contains_k : forall σ S kp T L kL Y,
  picks_k σ S kp T L -> contains_k σ S kL L Y -> contains_k σ S (kp + kL) T Y.
Proof.
  intros σ S kp T L kL Y H. induction H as [e He | k c t f L Hm Hp IH | k c t f L Hm Hp IH];
    intros Hc.
  - exact Hc.
  - replace (1 + smt_size c + k + kL) with (1 + smt_size c + (k + kL)) by lia.
    apply ContK_If_True; [exact Hm | exact (IH Hc)].
  - replace (1 + smt_size c + k + kL) with (1 + smt_size c + (k + kL)) by lia.
    apply ContK_If_False; [exact Hm | exact (IH Hc)].
Qed.

Lemma picks_k_graft_arg : forall σ S L1 k T2 L2,
  is_if L1 = false -> picks_k σ S k T2 L2 -> picks_k σ S k (graft_arg L1 T2) (EApp L1 L2).
Proof.
  intros σ S L1 k T2 L2 H1 H. induction H.
  - rewrite graft_arg_not_if by assumption. apply picks_k_leaf. reflexivity.
  - simpl. apply picks_k_then; assumption.
  - simpl. apply picks_k_else; assumption.
Qed.

Lemma picks_k_graft : forall σ S k1 T1 L1 k2 T2 L2,
  picks_k σ S k1 T1 L1 -> picks_k σ S k2 T2 L2 -> picks_k σ S (k1 + k2) (graft T1 T2) (EApp L1 L2).
Proof.
  intros σ S k1 T1 L1 k2 T2 L2 H1 H2. induction H1.
  - destruct e; simpl in H; try discriminate; simpl;
      apply picks_k_graft_arg; try reflexivity; exact H2.
  - simpl. rewrite <- Nat.add_assoc. apply picks_k_then; assumption.
  - simpl. rewrite <- Nat.add_assoc. apply picks_k_else; assumption.
Qed.

Lemma lift_picks_k : forall σ S k e X,
  contains_k σ S k e X ->
  exists kp kL L, picks_k σ S kp (lift_branches e) L /\ contains_k σ S kL L X /\
    flat L = true /\ kp + kL <= k.
Proof.
  intros σ S k e X H. induction H;
    try (exists 0; eexists; eexists; split; [apply picks_k_leaf; reflexivity
                         | split; [simpl; solve [econstructor; eassumption] | split; [reflexivity | lia]]]).
  - destruct IHcontains_k1 as [kp1 [kL1 [L1 [P1 [C1 [F1 B1]]]]]].
    destruct IHcontains_k2 as [kp2 [kL2 [L2 [P2 [C2 [F2 B2]]]]]].
    exists (kp1 + kp2), (kL1 + kL2), (EApp L1 L2).
    split; [simpl; apply picks_k_graft; assumption |].
    split; [apply ContK_App; assumption |].
    split; [simpl; rewrite F1, F2; reflexivity | lia].
  - destruct IHcontains_k as [kp [kL [L [P [C [F B]]]]]].
    exists (1 + smt_size ec + kp), kL, L.
    split; [simpl; apply picks_k_then; assumption |].
    split; [exact C | split; [exact F | lia]].
  - destruct IHcontains_k as [kp [kL [L [P [C [F B]]]]]].
    exists (1 + smt_size ec + kp), kL, L.
    split; [simpl; apply picks_k_else; assumption |].
    split; [exact C | split; [exact F | lia]].
  - assert (Hflat : flat es = true)
      by (destruct H2 as [pc [Hd _]]; exact (denotes_flat S es pc Hd)).
    exists 0, (smt_size es), es. rewrite (lift_flat es Hflat).
    split; [apply picks_k_leaf; apply flat_not_if; exact Hflat |].
    split; [eapply ContK_Denote; eassumption | split; [exact Hflat | lia]].
Qed.

Lemma picks_k_fold_leaves : forall σ S k T L,
  picks_k σ S k T L -> picks_k σ S k (fold_leaves T) (fold_leaf L).
Proof.
  intros σ S k T L H. induction H.
  - rewrite fold_leaves_not_if by assumption.
    apply picks_k_leaf. apply fold_leaf_not_if. assumption.
  - simpl. apply picks_k_then; assumption.
  - simpl. apply picks_k_else; assumption.
Qed.

Lemma fold_left_app_size_ground : forall args h,
  smt_size (fold_left EApp args h) = smt_size h + length args + list_sum (map smt_size args) /\
  (smt_ground (fold_left EApp args h) = true ->
     smt_ground h = true /\ Forall (fun a => smt_ground a = true) args).
Proof.
  induction args as [| a args IH]; intros h; simpl.
  - split; [lia | intros Hg; split; [exact Hg | constructor]].
  - destruct (IH (EApp h a)) as [Hs Hg]. split.
    + rewrite Hs. simpl. lia.
    + intros H. destruct (Hg H) as [Hha Hargs]. simpl in Hha.
      apply andb_prop in Hha as [Hh12 Ha]. apply andb_prop in Hh12 as [_ Hh].
      split; [exact Hh | constructor; assumption].
Qed.

Lemma ground_size_op_spine : forall p args,
  ground_size (op_spine p args) <= prim_slack args.
Proof.
  intros p args. unfold ground_size, prim_slack, op_spine.
  destruct (fold_left_app_size_ground args (@EPrimOp model_sorts p)) as [Hs Hg].
  destruct (smt_ground (fold_left EApp args (@EPrimOp model_sorts p))) eqn:E; [| lia].
  destruct (Hg eq_refl) as [_ Hargs]. rewrite Hs. simpl.
  enough (list_sum (map smt_size args) = list_sum (map ground_size args)) by lia.
  clear Hs Hg E. induction Hargs as [| a args Ha _ IH]; [reflexivity |].
  simpl. unfold ground_size at 1. rewrite Ha, IH. reflexivity.
Qed.

Lemma leaf_contains_k : forall σ S p kL L X,
  spine_of p (model_arity p) L ->
  contains_k σ S kL L X -> flat L = true ->
  exists k', k' <= kL + ground_size X /\ contains_k σ S k' (fold_leaf L) (fold_leaf X).
Proof.
  intros σ S p kL L X [L' [-> HL']] Hc HfL.
  pose proof (contains_k_erase _ _ _ _ _ Hc) as Hc0.
  unfold fold_leaf, ground_size.
  destruct (smt_ground X) eqn:HgX; destruct (smt_ground (op_spine p L')) eqn:HgL.
  - rewrite (closed_smt_term_is_rigid σ S _ _ HgL Hc0). exists 0. split; [lia | apply ContK_Lit].
  - destruct (ground_instance_denotes σ S _ _ Hc0 HfL HgX) as [pcL [pcX [HdL [HeX [Hv _]]]]].
    exists (smt_size (op_spine p L')).
    split; [exact (smt_size_contains_k _ _ _ _ _ Hc) |].
    apply (ContK_Denote σ S (op_spine p L') p L').
    + apply op_spine_unspool.
    + exact HL'.
    + exact HgL.
    + exists pcL. split; [exact HdL |]. rewrite (closed_value_of X pcX HeX). exact Hv.
  - pose proof (closed_smt_term_is_rigid σ S _ _ HgL Hc0) as E.
    rewrite E in HgL. congruence.
  - exists kL. split; [lia | exact Hc].
Qed.

Lemma unbranched_contains_k : forall σ S p ks args_s args_c,
  Forall3 (contains_k σ S) ks args_s args_c ->
  exists k', k' <= list_sum ks + prim_slack args_c /\
    contains_k σ S k' (reduce_unbranched p args_s) (reduce_unbranched p args_c).
Proof.
  intros σ S p ks args_s args_c HF.
  unfold reduce_unbranched. rewrite <- (forall3_length_right _ _ _ _ _ _ _ HF).
  destruct (Nat.eqb (length args_s) (model_arity p)) eqn:Hlen;
    [| exists 0; split; [lia | apply ContK_Lit]].
  apply Nat.eqb_eq in Hlen.
  pose proof (contains_k_fold_left_app σ S ks args_s args_c 0 _ _ HF (ContK_PrimOp σ S p)) as Hc.
  simpl in Hc. fold (op_spine p args_s) (op_spine p args_c) in Hc.
  rewrite (lift_flat _ (contains_flat_instance σ S _ _ (contains_k_erase _ _ _ _ _ Hc))),
          (fold_leaves_not_if _ (op_spine_not_if p args_c)).
  destruct (lift_picks_k σ S _ _ _ Hc) as [kp [kL [L [Hp [HcL [HfL Hb]]]]]].
  destruct (leaf_contains_k σ S p kL L (op_spine p args_c)) as [k' [Hk' Hc']];
    [| exact HcL | exact HfL |].
  { rewrite <- Hlen. exact (picks_leaves σ S _ _ _ (picks_of_picks_k _ _ _ _ _ Hp) (leaves_lift_spine p args_s)). }
  pose proof (ground_size_op_spine p args_c) as Hg.
  exists (kp + k'). split; [lia |].
  exact (picks_k_contains_k σ S _ _ _ _ _ (picks_k_fold_leaves σ S _ _ _ Hp) Hc').
Qed.

Lemma contains_k_picks_top : forall σ S e k X,
  contains_k σ S k e X -> exists kp kL L, picks_k σ S kp e L /\ contains_k σ S kL L X /\ kp + kL = k.
Proof.
  intros σ S e. induction e; intros k X H;
    try (exists 0, k; eexists; split; [apply picks_k_leaf; reflexivity | split; [exact H | reflexivity]]).
  destruct (contains_k_if_inv σ S _ _ _ _ X H) as [k0 [-> [[Hm Hc] | [Hm Hc]]]].
  - destruct (IHe2 k0 X Hc) as [kp [kL [L [Hp [HL Hs]]]]].
    exists (1 + smt_size e1 + kp), kL, L. split; [apply picks_k_then; assumption | split; [exact HL | lia]].
  - destruct (IHe3 k0 X Hc) as [kp [kL [L [Hp [HL Hs]]]]].
    exists (1 + smt_size e1 + kp), kL, L. split; [apply picks_k_else; assumption | split; [exact HL | lia]].
Qed.

Lemma contains_k_args_picks : forall σ S ks args_s args_c,
  Forall3 (contains_k σ S) ks args_s args_c ->
  exists kps kls ls, Forall3 (picks_k σ S) kps args_s ls /\ Forall3 (contains_k σ S) kls ls args_c /\
    list_sum kps + list_sum kls = list_sum ks.
Proof.
  intros σ S ks args_s args_c H.
  induction H as [| k a c ks args_s args_c Ha _ [kps [kls [ls [Hp [Hc Hs]]]]]].
  - exists nil, nil, nil. split; [constructor | split; [constructor | reflexivity]].
  - destruct (contains_k_picks_top σ S a k c Ha) as [kp [kL [L [HpL [HcL HsL]]]]].
    exists (kp :: kps), (kL :: kls), (L :: ls).
    split; [constructor; assumption | split; [constructor; assumption | simpl; lia]].
Qed.

Lemma picks_k_split_arg : forall σ S K kp a L k Y,
  picks_k σ S kp a L -> contains_k σ S k (K L) Y -> contains_k σ S (kp + k) (split_arg K a) Y.
Proof.
  intros σ S K kp a L k Y H. induction H; intros HK.
  - rewrite split_arg_not_if by assumption. exact HK.
  - cbn [split_arg]. replace (1 + smt_size c + k0 + k) with (1 + smt_size c + (k0 + k)) by lia.
    apply ContK_If_True; auto.
  - cbn [split_arg]. replace (1 + smt_size c + k0 + k) with (1 + smt_size c + (k0 + k)) by lia.
    apply ContK_If_False; auto.
Qed.

Lemma picks_k_split_args : forall σ S kps args ls,
  Forall3 (picks_k σ S) kps args ls ->
  forall K k Y, contains_k σ S k (K ls) Y -> contains_k σ S (list_sum kps + k) (split_args K args) Y.
Proof.
  intros σ S kps args ls H.
  induction H as [| kp a L kps args ls Ha _ IH]; intros K k Y Hk; [exact Hk |].
  cbn [split_args]. replace (list_sum (kp :: kps) + k) with (kp + (list_sum kps + k)) by (simpl; lia).
  apply (picks_k_split_arg σ S _ kp a L _ Y Ha).
  apply (IH (fun rest' => K (L :: rest'))). exact Hk.
Qed.


Lemma ground_flat : forall a, smt_ground a = true -> flat a = true.
Proof. intros a H. exact (solvable_flat · a (smt_ground_solvable a · H)). Qed.

Lemma op_spine_pc : forall args pcs h (q : model_primop) acc,
  Forall2 (fun a pc => expr_to_pc · a = Some pc) args pcs ->
  expr_to_pc · h = Some (PCPrim q acc) ->
  expr_to_pc · (fold_left EApp args h) = Some (PCPrim q (acc ++ pcs)).
Proof.
  intros args pcs h q acc H. revert h acc.
  induction H as [| a pc args pcs Ha _ IH]; intros h acc Hh.
  - rewrite app_nil_r. exact Hh.
  - simpl. replace (acc ++ pc :: pcs) with ((acc ++ pc :: nil) ++ pcs)
      by (rewrite <- app_assoc; reflexivity).
    apply IH. simpl. rewrite Hh, Ha. reflexivity.
Qed.

Lemma op_spine_ground : forall args h,
  Forall (fun a => smt_ground a = true) args ->
  smt_ground h = true -> is_op_app h = true ->
  smt_ground (fold_left EApp args h) = true.
Proof.
  intros args h H. revert h. induction H as [| a args Ha _ IH]; intros h Hh Hop; [exact Hh |].
  simpl. apply IH; simpl; [rewrite Hop, Hh, Ha; reflexivity | exact Hop].
Qed.

Lemma unbranched_ground : forall p args,
  length args = model_arity p -> Forall (fun a => smt_ground a = true) args ->
  reduce_unbranched p args = ELit (model_prim_value p (map closed_value args)).
Proof.
  intros p args Hlen Hg. unfold reduce_unbranched.
  rewrite (proj2 (Nat.eqb_eq _ _) Hlen).
  assert (Hflat : Forall (fun a => flat a = true) args)
    by (eapply Forall_impl; [| exact Hg]; exact ground_flat).
  rewrite (lift_flat _ (op_spine_flat p args Hflat)), (fold_leaves_not_if _ (op_spine_not_if p args)).
  unfold fold_leaf, op_spine.
  rewrite (op_spine_ground args (@EPrimOp model_sorts p) Hg eq_refl eq_refl).
  assert (Hpcs : exists pcs, Forall2 (fun a pc => expr_to_pc · a = Some pc) args pcs
                   /\ map (pc_value closed_model) pcs = map closed_value args).
  { clear Hlen Hflat. induction Hg as [| a args Ha _ [pcs [Hp Hv]]].
    - exists nil. split; [constructor | reflexivity].
    - destruct (solvable_expr_to_pc · a (smt_ground_solvable a · Ha)) as [pc Hpc].
      exists (pc :: pcs). split; [constructor; assumption |].
      cbn [map]. rewrite Hv, (closed_value_of a pc Hpc). reflexivity. }
  destruct Hpcs as [pcs [Hp Hv]].
  pose proof (op_spine_pc args pcs (@EPrimOp model_sorts p) p nil Hp eq_refl) as He. simpl in He.
  rewrite (closed_value_of _ _ He).
  change (ELit (model_prim_value p (map (pc_value closed_model) pcs))
          = ELit (model_prim_value p (map closed_value args))).
  rewrite Hv. reflexivity.
Qed.

Lemma arg_facts_k : forall σ S ks ls args_c,
  Forall3 (contains_k σ S) ks ls args_c -> Forall closed_term args_c ->
  Forall (fun a => smt_need a = Some 0) ls ->
  Forall (fun c => smt_ground c = true) args_c /\
  Forall2 (denote σ S) ls (map closed_value args_c) /\
  list_sum (map smt_size ls) <= list_sum ks + list_sum (map ground_size args_c).
Proof.
  intros σ S ks ls args_c H. induction H as [| k L X ks ls args_c HLX _ IH]; intros Hcl Ht.
  - split; [constructor | split; [constructor | simpl; lia]].
  - inversion Hcl as [| X0 xs0 HclX Hcl']; subst. inversion Ht as [| L0 ls0 HtL Ht']; subst.
    destruct (IH Hcl' Ht') as [Hg [Hd Hs]].
    pose proof (contains_k_erase _ _ _ _ _ HLX) as HLX0.
    pose proof (smt_need_closed_ground X 0 (contains_smt_need σ S L X 0 HLX0 HtL) HclX) as HgX.
    destruct (ground_instance_denotes σ S L X HLX0 (smt_need_flat L 0 HtL) HgX)
      as [pcL [pcX [HdL [HeX [Hv _]]]]].
    split; [constructor; assumption |].
    split.
    + constructor; [| exact Hd].
      exists pcL. split; [exact HdL |]. rewrite (closed_value_of X pcX HeX). exact Hv.
    + pose proof (smt_size_contains_k _ _ _ _ _ HLX) as HsX.
      simpl. unfold ground_size at 1. rewrite HgX. lia.
Qed.

Lemma simplified_contains_k : forall σ S p ks ls args_c,
  Forall closed_term args_c -> Forall3 (contains_k σ S) ks ls args_c ->
  exists k', k' <= list_sum ks + prim_slack args_c /\
    contains_k σ S k' (simplify_unbranched p ls) (simplify_unbranched p args_c).
Proof.
  intros σ S p ks ls args_c Hcl HF.
  unfold simplify_unbranched at 2. rewrite (simplify_closed_none p args_c Hcl).
  unfold simplify_unbranched.
  destruct (simplify p ls) as [r |] eqn:Hs; [| exact (unbranched_contains_k σ S p ks ls args_c HF)].
  destruct (simplify_facts p ls r Hs) as [Ht Hr].
  destruct (arg_facts_k σ S ks ls args_c HF Hcl Ht) as [Hg [Hd Hsz]].
  destruct (rewrite_prim_value σ S p ls _ r Ht Hd Hr) as [_ [k [Hk Hck]]].
  rewrite (unbranched_ground p args_c); [| | exact Hg].
  - exists k. split; [unfold prim_slack; lia | exact Hck].
  - rewrite <- (forall3_length_right _ _ _ _ _ _ _ HF). exact (rewrite_prim_arity p ls r Hr).
Qed.

#[export] Instance model_reduce_prim_contains_k : ReducePrimContainsK.
Proof.
  intros σ S p ks args_s args_c Hcl HF.
  change (exists k', k' <= list_sum ks + prim_slack args_c /\
    contains_k σ S k' (model_reduce_prim p args_s) (model_reduce_prim p args_c)).
  unfold model_reduce_prim.
  rewrite (split_args_not_if _ args_c
             (contains_instances_not_if σ S _ _ (forall3_contains_k_erase _ _ _ _ _ HF))).
  destruct (contains_k_args_picks σ S _ _ _ HF) as [kps [kls [ls [Hp [Hc Hs]]]]].
  destruct (simplified_contains_k σ S p kls ls args_c Hcl Hc) as [k' [Hk' Hc']].
  exists (list_sum kps + k'). split; [lia |].
  exact (picks_k_split_args σ S _ _ _ Hp _ _ _ Hc').
Qed.

#[export] Instance model_cast_expr_contains_k : CastExprContainsK.
Proof. intros σ S k es ec γ H. exact H. Qed.

#[export] Instance model_reduce_prim_contains : ReducePrimContains.
Proof. exact (reduce_prim_contains_of_k model_reduce_prim_contains_k). Qed.

#[export] Instance model_laws : ConCoreLaws.
Proof. constructor; exact _. Qed.

#[export] Instance model_symfc_cost_laws : SymFCCostLaws.
Proof. constructor; exact _. Qed.

(** ========================================================================= *)
(** 7. What the model shows                                                    *)
(** ========================================================================= *)

Theorem model_negation_is_satisfiable : prim_value op_not (false :: nil) = lit_true.
Proof. reflexivity. Qed.

Corollary some_literal_satisfies_negation :
  ~ (forall l : lit, prim_value op_not (l :: nil) <> lit_true).
Proof. intros H. exact (H false model_negation_is_satisfiable). Qed.

Theorem model_soundness_takes_else_branch :
  exists v_con,
    ⊢ᶜ else_match true false ⇓ᶜ v_con /\
    contains (else_model false) (only branch_var) (branch_on_x (ELit true) (ELit false)) v_con.
Proof. exact (soundness_takes_else_branch false model_negation_is_satisfiable true false). Qed.

Corollary model_else_branch_value : forall v,
  ⊢ᶜ else_match true false ⇓ᶜ v -> v = ELit false.
Proof.
  intros v Hv.
  exact (concore_eval_deterministic_top _ _ _ (else_match_concore true false) Hv
           (else_match_reads_else_arm true false)).
Qed.

Theorem model_soundness_on_negation : forall σ x,
  σ ⊨ pc_true ->
  exists v_con,
    ⊢ᶜ EApp (EPrimOp PNot) (ELit (σ x)) ⇓ᶜ v_con /\
    contains σ (only x) (reduce_prim PNot (EVar x :: nil)) v_con.
Proof.
  exact (soundness_on_computing_primitive PNot eq_refl (fun x => eq_refl)).
Qed.

