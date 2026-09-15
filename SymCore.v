(**
  SymCore.v - Formalization of the Syntax and Foundations of SymCore
  from the paper "SymFC: Configurable Semantics for All Paths
  Symbolic Execution in Haskell via Embeddings".

  Covers:
  - Terminal sorts: var, dcon, lit, primop, type_fc, role, coercion.
  - Figure 1: Expressions, Alternatives, and Bottom values.
  - Figure 2: Environment (Γ) and Path Condition (Φ).
  - Reduction helpers: unspooling spines, coercion operations, environment lookups.
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(**
  The parameters of this development are the fields of classes: three here
  and four in ConCore.v. Every section takes the classes as context, so each
  definition and theorem holds for every instance. Model.v gives one.
*)
Section SymCore.

(** ========================================================================= *)
(** 1. Variables and Data Constructors (§3.1)                                  *)
(** ========================================================================= *)

Definition var : Set := string.
Definition dcon : Set := string.

(** ========================================================================= *)
(** 2. Literals and Primitive Operations (§3.1)                                *)
(** ========================================================================= *)

Class SymCoreSorts : Type := {

(** Literals mirror those found in SMT solvers; a parameter from external SMT (§3.1) *)
lit : Set;

(** Primitive operations mirror SMT solver primitives; a parameter from external SMT (§3.1) *)
primop : Set;

(** SMT boolean primitives for path condition connectives *)
op_and : primop;
op_not : primop;

(**
  SMT if-then-else. This is the solver's own three-place term, not the
  evaluator's branch EIf. Section 3.3's merge turns a branch between two
  solvable arms into this term, which is the point at which a branch stops
  being a tree the evaluator walks and becomes a formula the solver reads.
*)
op_ite : primop;

(** Arity of a primitive operation: the number of arguments it is applied to (§3.1) *)
primop_arity : primop -> nat;

(** if-then-else takes a condition and two arms *)
op_ite_arity : primop_arity op_ite = 3%nat;

(**
  Literals and primitive operations have decidable equality.

  Merge needs it: Section 3.3 merges two arms only when they are the same
  shape carrying the same payload, and "the same payload" has to be a test
  the definition can run. Equality of expressions is built from these two
  and from tycon_eq_dec below.
*)
lit_eq_dec : forall (l1 l2 : lit), {l1 = l2} + {l1 <> l2};
primop_eq_dec : forall (p1 p2 : primop), {p1 = p2} + {p1 <> p2};

(** Type Constructors (e.g. Int, Bool, SMT.BitVec), used by Section 3; left abstract *)
tycon : Set;

(** Type constructors have decidable equality; merge compares whole types *)
tycon_eq_dec : forall (t1 t2 : tycon), {t1 = t2} + {t1 <> t2};

(**
  The SMT theory's own reading of a primitive operation: the literal the
  solver gives to that operation applied to literal arguments. It is external
  to this development in exactly the way lit and primop already are.
*)
prim_value : primop -> list lit -> lit;

(** The literal the SMT theory reads as truth. External in the same way. *)
lit_true : lit
}.

Context {sorts : SymCoreSorts}.

(** ========================================================================= *)
(** 3. Types and Coercions in System FC / SymCore (§3.1)                      *)
(** ========================================================================= *)

(** System FC Types with arrow types for higher-order coercions *)
Inductive type_fc : Set :=
  | TyVar   : var -> type_fc
  | TyCon   : tycon -> type_fc
  | TyArrow : type_fc -> type_fc -> type_fc
  | TyApp   : type_fc -> type_fc -> type_fc.

(** Roles in System FC / SymCore (§3.1, [Breitner et al. 2016]) *)
Inductive role : Set :=
  | RoleNominal             (** N: exact type equality *)
  | RoleRepresentational    (** R: same runtime representation *)
  | RolePhantom.            (** P: phantom types *)

Definition role_eq_dec : forall (r1 r2 : role), {r1 = r2} + {r1 <> r2}.
Proof.
  decide equality.
Defined.

Definition type_fc_eq_dec : forall (τ1 τ2 : type_fc), {τ1 = τ2} + {τ1 <> τ2}.
Proof.
  decide equality; [apply string_dec | apply tycon_eq_dec].
Defined.

(** A test that runs a decision procedure and reports the verdict as a Boolean *)
Definition dec_eqb {A : Type} (d : forall x y : A, {x = y} + {x <> y}) (x y : A) : bool :=
  if d x y then true else false.

Lemma dec_eqb_eq : forall (A : Type) (d : forall x y : A, {x = y} + {x <> y}) x y,
  dec_eqb d x y = true -> x = y.
Proof.
  intros A d x y H. unfold dec_eqb in H. destruct (d x y); [assumption | discriminate].
Qed.

(** Coercions witnessing type equality with endpoints (Section 3.1: γ : τ1 ~ρ τ2) *)
Record coercion : Set := MkCoercion {
  coerc_src  : type_fc;     (** τ1 *)
  coerc_dst  : type_fc;     (** τ2 *)
  coerc_role : role         (** ρ *)
}.

(** Symmetry of a coercion: sym γ witnesses τ2 ~ρ τ1 (Fig. 3, Rule App-Cast) *)
Definition sym_coerc (γ : coercion) : coercion :=
  MkCoercion (coerc_dst γ) (coerc_src γ) (coerc_role γ).

Definition coercion_eq_dec : forall (γ1 γ2 : coercion), {γ1 = γ2} + {γ1 <> γ2}.
Proof.
  decide equality; [apply role_eq_dec | apply type_fc_eq_dec | apply type_fc_eq_dec].
Defined.

(** Decomposition of arrow coercion: (γa -> γr) = γ (Fig. 3, Rule App-Cast) *)
Definition decomp_coerc_arrow (γ : coercion) : option (coercion * coercion) :=
  match coerc_src γ, coerc_dst γ with
  | TyArrow s1 s2, TyArrow d1 d2 =>
      Some (MkCoercion s1 d1 (coerc_role γ),
            MkCoercion s2 d2 (coerc_role γ))
  | _, _ => None
  end.

(** ========================================================================= *)
(** 4. Expressions, Bottom, Closures, and Environment (Figures 1 & 2)          *)
(** ========================================================================= *)

(**
  Expressions (Fig. 1) and Environment Γ ::= {x ↦ (Γ, e)} (Fig. 2).
  Extended with runtime closures (Γ, λx. e) produced by Rule Lam and applied
  in Rule App-Abs, and with thunks (Γ, e) produced by Rule Con for the fields
  of a constructor value and forced by Rule Thunk.
*)

Inductive bottom : Type :=
  | BRaise : expr -> bottom      (** raise e: error throw *)
  | BUnreachable : bottom        (** ∅: unreachable *)
  | BUndefined : bottom          (** ?: undefined behavior *)
  | BOutOfFuel : bottom          (** ⊥ₖ: the evaluation budget ran out *)

with expr : Type :=
  | EVar : var -> expr                            (** x: variable *)
  | ELit : lit -> expr                            (** l: literal *)
  | EPrimOp : primop -> expr                      (** ⊗: primitive operation *)
  | ECon : dcon -> expr                           (** D: data constructor *)
  | EApp : expr -> expr -> expr                   (** ef ea: application *)
  | ELam : var -> expr -> expr                    (** λx. e: abstraction *)
  | EClos : environment -> var -> expr -> expr    (** (Γ, λx. e): runtime closure (Fig. 3 Lam/App-Abs) *)
  | ECase : expr -> list alt -> expr              (** case e of a⃗: case split *)
  | ECast : expr -> coercion -> expr              (** e ⊲ γ: cast *)
  | ECoercion : coercion -> expr                  (** γ: coercion *)
  | EType : type_fc -> expr                       (** τ: type *)
  | EIf : expr -> expr -> expr -> expr            (** if ec then et else ef: symbolic branch *)
  | EBot : bottom -> expr                         (** b: bottom *)
  | EThunk : environment -> expr -> expr          (** (Γ, e): runtime thunk (Rules Con and Thunk) *)

with alt : Type :=
  | Alt : dcon -> list var -> expr -> alt         (** D x⃗ → e: pattern *)

with closure : Type :=
  | MkClosure : environment -> expr -> closure    (** (Γ, e) from Fig. 2 *)

with environment : Type :=
  | EmptyEnv : environment                        (** empty substitution map *)
  | ExtendEnv : var -> closure -> environment -> environment.
                                                  (** Γ{x ↦ (Γ', e)}: substitution map *)

End SymCore.

Notation "'·'" := EmptyEnv.

Section SymCore.
Context {sorts : SymCoreSorts}.

(**
  Syntactic equality of expressions, as a test the merge definition can run.

  Section 3.3 merges two bottoms only when they are the same bottom, and a
  bottom may carry a whole expression (raise e), so the test has to descend
  into expressions, alternatives and environments at once. Only the direction
  "the test says yes, so the two really are equal" is proved below, and only
  that direction is used: a false answer just leaves the branch unmerged.
*)
Fixpoint expr_eqb (e1 e2 : expr) {struct e1} : bool :=
  match e1, e2 with
  | EVar x1, EVar x2 => String.eqb x1 x2
  | ELit l1, ELit l2 => dec_eqb lit_eq_dec l1 l2
  | EPrimOp p1, EPrimOp p2 => dec_eqb primop_eq_dec p1 p2
  | ECon d1, ECon d2 => String.eqb d1 d2
  | EApp f1 a1, EApp f2 a2 => andb (expr_eqb f1 f2) (expr_eqb a1 a2)
  | ELam x1 b1, ELam x2 b2 => andb (String.eqb x1 x2) (expr_eqb b1 b2)
  | EClos Γ1 x1 b1, EClos Γ2 x2 b2 =>
      andb (andb (env_eqb Γ1 Γ2) (String.eqb x1 x2)) (expr_eqb b1 b2)
  | ECase s1 alts1, ECase s2 alts2 =>
      andb (expr_eqb s1 s2)
        ((fix alts_eqb (l1 l2 : list alt) {struct l1} : bool :=
            match l1, l2 with
            | nil, nil => true
            | Alt d1 xs1 p1 :: t1, Alt d2 xs2 p2 :: t2 =>
                andb (andb (andb (andb
                  (String.eqb d1 d2)
                  (forallb (fun p => String.eqb (fst p) (snd p)) (combine xs1 xs2)))
                  (Nat.eqb (length xs1) (length xs2)))
                  (expr_eqb p1 p2)) (alts_eqb t1 t2)
            | _, _ => false
            end) alts1 alts2)
  | ECast b1 γ1, ECast b2 γ2 => andb (expr_eqb b1 b2) (dec_eqb coercion_eq_dec γ1 γ2)
  | ECoercion γ1, ECoercion γ2 => dec_eqb coercion_eq_dec γ1 γ2
  | EType τ1, EType τ2 => dec_eqb type_fc_eq_dec τ1 τ2
  | EIf c1 t1 f1, EIf c2 t2 f2 =>
      andb (andb (expr_eqb c1 c2) (expr_eqb t1 t2)) (expr_eqb f1 f2)
  | EBot b1, EBot b2 => bottom_eqb b1 b2
  | EThunk Γ1 b1, EThunk Γ2 b2 => andb (env_eqb Γ1 Γ2) (expr_eqb b1 b2)
  | _, _ => false
  end
with bottom_eqb (b1 b2 : bottom) {struct b1} : bool :=
  match b1, b2 with
  | BRaise e1, BRaise e2 => expr_eqb e1 e2
  | BUnreachable, BUnreachable => true
  | BUndefined, BUndefined => true
  | BOutOfFuel, BOutOfFuel => true
  | _, _ => false
  end
with env_eqb (Γ1 Γ2 : environment) {struct Γ1} : bool :=
  match Γ1, Γ2 with
  | EmptyEnv, EmptyEnv => true
  | ExtendEnv x1 (MkClosure Γ1' e1) r1, ExtendEnv x2 (MkClosure Γ2' e2) r2 =>
      andb (andb (andb (String.eqb x1 x2) (env_eqb Γ1' Γ2')) (expr_eqb e1 e2))
           (env_eqb r1 r2)
  | _, _ => false
  end.

(** Two binder lists that agree pairwise and in length are the same list *)
Lemma vars_eqb_eq : forall xs1 xs2,
  forallb (fun p => String.eqb (fst p) (snd p)) (combine xs1 xs2) = true ->
  Nat.eqb (length xs1) (length xs2) = true ->
  xs1 = xs2.
Proof.
  induction xs1 as [| x xs IH]; intros xs2 Hall Hlen.
  - destruct xs2; [reflexivity | discriminate].
  - destruct xs2 as [| y ys]; [discriminate |].
    simpl in Hall, Hlen. apply andb_prop in Hall as [Hxy Hrest].
    apply String.eqb_eq in Hxy. subst y. f_equal. apply IH; assumption.
Qed.

(** The test only says yes to equal terms *)
Fixpoint expr_eqb_eq (e1 : expr) {struct e1} :
  forall e2, expr_eqb e1 e2 = true -> e1 = e2
with bottom_eqb_eq (b1 : bottom) {struct b1} :
  forall b2, bottom_eqb b1 b2 = true -> b1 = b2
with env_eqb_eq (Γ1 : environment) {struct Γ1} :
  forall Γ2, env_eqb Γ1 Γ2 = true -> Γ1 = Γ2.
Proof.
  - destruct e1; intros e2 H; destruct e2; simpl in H; try discriminate.
    + apply String.eqb_eq in H. subst. reflexivity.
    + apply dec_eqb_eq in H. subst. reflexivity.
    + apply dec_eqb_eq in H. subst. reflexivity.
    + apply String.eqb_eq in H. subst. reflexivity.
    + apply andb_prop in H as [H1 H2].
      rewrite (expr_eqb_eq _ _ H1), (expr_eqb_eq _ _ H2). reflexivity.
    + apply andb_prop in H as [H1 H2]. apply String.eqb_eq in H1. subst.
      rewrite (expr_eqb_eq _ _ H2). reflexivity.
    + apply andb_prop in H as [H12 H3]. apply andb_prop in H12 as [H1 H2].
      apply String.eqb_eq in H2. subst.
      rewrite (env_eqb_eq _ _ H1), (expr_eqb_eq _ _ H3). reflexivity.
    + apply andb_prop in H as [H1 H2].
      rewrite (expr_eqb_eq _ _ H1). f_equal.
      revert l0 H2. induction l as [| [d1 xs1 p1] t1 IH]; intros l0 H2.
      * destruct l0; [reflexivity | discriminate].
      * destruct l0 as [| [d2 xs2 p2] t2]; [discriminate |].
        apply andb_prop in H2 as [H1234 H5]. apply andb_prop in H1234 as [H123 H4].
        apply andb_prop in H123 as [H12 H3]. apply andb_prop in H12 as [Hd Hxs].
        apply String.eqb_eq in Hd. subst d2.
        rewrite (vars_eqb_eq xs1 xs2 Hxs H3).
        rewrite (expr_eqb_eq _ _ H4). f_equal. apply IH. exact H5.
    + apply andb_prop in H as [H1 H2]. apply dec_eqb_eq in H2. subst.
      rewrite (expr_eqb_eq _ _ H1). reflexivity.
    + apply dec_eqb_eq in H. subst. reflexivity.
    + apply dec_eqb_eq in H. subst. reflexivity.
    + apply andb_prop in H as [H12 H3]. apply andb_prop in H12 as [H1 H2].
      rewrite (expr_eqb_eq _ _ H1), (expr_eqb_eq _ _ H2), (expr_eqb_eq _ _ H3).
      reflexivity.
    + rewrite (bottom_eqb_eq _ _ H). reflexivity.
    + apply andb_prop in H as [H1 H2].
      rewrite (env_eqb_eq _ _ H1), (expr_eqb_eq _ _ H2). reflexivity.
  - destruct b1; intros b2 H; destruct b2; simpl in H;
      try discriminate; try reflexivity.
    rewrite (expr_eqb_eq _ _ H). reflexivity.
  - destruct Γ1 as [| x1 [Γ1' e1] r1]; intros Γ2 H;
      destruct Γ2 as [| x2 [Γ2' e2] r2]; simpl in H;
      try discriminate; try reflexivity.
    apply andb_prop in H as [H123 H4]. apply andb_prop in H123 as [H12 H3].
    apply andb_prop in H12 as [H1 H2].
    apply String.eqb_eq in H1. subst x2.
    rewrite (env_eqb_eq _ _ H2), (expr_eqb_eq _ _ H3), (env_eqb_eq _ _ H4).
    reflexivity.
Qed.

(** Environment lookup: (Γ', e) = Γ(x) (Fig. 3, Rule Var) *)
Fixpoint lookup_env (Γ : environment) (x : var) : option (environment * expr) :=
  match Γ with
  | · => None
  | ExtendEnv y (MkClosure Γ' e) rest =>
      if string_dec x y then Some (Γ', e) else lookup_env rest x
  end.

(** Predicate checking whether a variable is in the environment Γ *)
Definition in_env (Γ : environment) (x : var) : bool :=
  match lookup_env Γ x with
  | Some _ => true
  | None => false
  end.

(** Single-variable environment extension: Γ{x ↦ (Γ', e)} (Fig. 3, Rule App-Abs) *)
Definition extend_env (Γ : environment) (x : var) (Γ' : environment) (e : expr) : environment :=
  ExtendEnv x (MkClosure Γ' e) Γ.

(** Multi-variable environment extension for pattern matching: Γ{x⃗ ↦ (Γ', e⃗)} (Fig. 3, fold-alts) *)
Definition missing_field : expr := EBot BUndefined.

Fixpoint extend_env_multi (Γ : environment) (xs : list var) (args : list expr) (Γ_arg : environment) : environment :=
  match xs, args with
  | x :: xs', a :: args' =>
      extend_env (extend_env_multi Γ xs' args' Γ_arg) x Γ_arg a
  | x :: xs', [] =>
      extend_env (extend_env_multi Γ xs' [] Γ_arg) x Γ_arg missing_field
  | [], _ => Γ
  end.


(** ========================================================================= *)
(** 5. Path Condition Φ (Figure 2)                                            *)
(** ========================================================================= *)

(**
  Path Condition (Fig. 2):
    Φ ::= x | l | ⊗ Φ⃗
*)
Inductive path_condition : Set :=
  | PCVar  : var -> path_condition
  | PCLit  : lit -> path_condition
  | PCPrim : primop -> list path_condition -> path_condition.

(** Conjunction of path conditions: Φ1 ∧ Φ2 *)
Definition pc_and (Φ1 Φ2 : path_condition) : path_condition :=
  PCPrim op_and [Φ1; Φ2].

(** Negation of a path condition: ¬Φ *)
Definition pc_not (Φ : path_condition) : path_condition :=
  PCPrim op_not [Φ].

End SymCore.

Notation "Φ1 '∧' Φ2" := (pc_and Φ1 Φ2) (at level 40, left associativity).
Notation "'¬' Φ" := (pc_not Φ) (at level 35, right associativity).

Section SymCore.
Context {sorts : SymCoreSorts}.

(** Convert a solvable expression into a path condition formula *)
Fixpoint expr_to_pc (Γ : environment) (e : expr) : option path_condition :=
  match e with
  | EVar x =>
      match lookup_env Γ x with
      | None => Some (PCVar x)
      | Some _ => None
      end
  | ELit l => Some (PCLit l)
  | EPrimOp p => Some (PCPrim p [])
  | EApp f a =>
      match expr_to_pc Γ f, expr_to_pc Γ a with
      | Some (PCPrim p args), Some pca => Some (PCPrim p (args ++ [pca]))
      | _, _ => None
      end
  | _ => None
  end.

(** ========================================================================= *)
(** 6. Application Spine & Primitive / Cast Helpers (§3.2)                     *)
(** ========================================================================= *)

(** Unspool application spine into head expression and arguments: e.g. D e1 ... en *)
Fixpoint unspool_app (e : expr) (args : list expr) : (expr * list expr) :=
  match e with
  | EApp f a => unspool_app f (a :: args)
  | _ => (e, args)
  end.

Class SymCoreSolver : Type := {

(** SMT satisfiability oracle SAT(Φ) (Fig. 3, Rule Prune); a parameter from the SMT solver *)
sat : path_condition -> bool;

(** Canonical trivially satisfiable path condition (Top / True) *)
pc_true : path_condition;
sat_pc_true : sat pc_true = true;

(** Theory-specific primitive reduction: reduce-prim(⊗ e⃗) (Fig. 3, Rule App-Prim); a parameter from the SMT solver *)
reduce_prim : primop -> list expr -> expr;

(** Cast simplification: cast(e, γ) (Fig. 3, Rule Cast) *)
cast_expr : expr -> coercion -> expr;

(** Type and Coercion substitution under environment Γ (Fig. 3, Rules Type and Coercion) *)
subst_coerc : environment -> coercion -> coercion;
subst_type : environment -> type_fc -> type_fc
}.

Context {solver : SymCoreSolver}.

(** Leaf expression merging is Section 8.1 below, a definition rather than an
    assumption. It needs Solvable and the spine helpers, which come first. *)

(** ========================================================================= *)
(** 7. Solvable and Computation Definitions in Prop (§3.2)                     *)
(** ========================================================================= *)

(** Helper: checks if the head of an expression is a primitive operation *)
Fixpoint is_op_app (e : expr) : bool :=
  match e with
  | EPrimOp _ => true
  | EApp f _ => is_op_app f
  | _ => false
  end.

(** Helper: checks if the head of an application spine is a data constructor *)
Fixpoint is_con_app (e : expr) : bool :=
  match e with
  | ECon _ => true
  | EApp f _ => is_con_app f
  | _ => false
  end.

(** A constructor-headed spine unspools to that constructor *)
Lemma is_con_app_unspool_gen : forall e args,
  is_con_app e = true ->
  exists d args0, unspool_app e args = (ECon d, args0).
Proof.
  induction e; intros args H; simpl in H; try discriminate.
  - exists d, args. reflexivity.
  - simpl. apply IHe1. exact H.
Qed.

Lemma is_con_app_unspool : forall e,
  is_con_app e = true ->
  exists d args, unspool_app e [] = (ECon d, args).
Proof. intros e H. apply is_con_app_unspool_gen. exact H. Qed.

(** A spine has one head, so it cannot be headed by both a primitive
    operation and a data constructor *)
Lemma op_app_not_con_app : forall e,
  is_op_app e = true -> is_con_app e = false.
Proof.
  induction e; intros H; simpl in H; simpl; try discriminate; try reflexivity.
  apply IHe1. exact H.
Qed.

(** Unspooling to a constructor head is exactly is_con_app *)
Lemma unspool_is_con_app : forall e args d args0,
  unspool_app e args = (ECon d, args0) ->
  is_con_app e = true.
Proof.
  induction e; intros args d0 args0 H; simpl in H; try discriminate.
  - reflexivity.
  - simpl. eapply IHe1. exact H.
Qed.

Inductive Solvable (Γ : environment) : expr -> Prop :=
  | Solvable_Lit : forall l,
      Solvable Γ (ELit l)
  | Solvable_Var : forall x,
      lookup_env Γ x = None ->
      Solvable Γ (EVar x)
  | Solvable_PrimOp : forall p,
      Solvable Γ (EPrimOp p)
  | Solvable_AppPrim : forall f a,
      is_op_app (EApp f a) = true ->
      Solvable Γ f ->
      Solvable Γ a ->
      Solvable Γ (EApp f a).

Fixpoint spine_head (e : expr) : expr :=
  match e with
  | EApp f _ => spine_head f
  | _ => e
  end.

Definition is_con_or_prim (e : expr) : bool :=
  match e with
  | ECon _ | EPrimOp _ => true
  | _ => false
  end.

Inductive Comp (Γ : environment) : expr -> Prop :=
  | Comp_Var : forall x,
      lookup_env Γ x <> None ->
      Comp Γ (EVar x)
  | Comp_Lam : forall x body,
      Comp Γ (ELam x body)
  | Comp_Case : forall es alts,
      Comp Γ (ECase es alts)
  | Comp_Thunk : forall Γ' e,
      Comp Γ (EThunk Γ' e)
  | Comp_App : forall ef ea,
      is_con_or_prim (spine_head (EApp ef ea)) = false ->
      Comp Γ (EApp ef ea).

End SymCore.

(** Closes the Eval_Con case of an inversion on an expression
    whose spine head is visibly not a data constructor. *)
Ltac no_con_head :=
  match goal with
  | [ H : unspool_app _ _ = (ECon _, _) |- _ ] => simpl in H; discriminate H
  end.

Section SymCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

(** ------------------------------------------------------------------------- *)
(** 7.1 expr_to_pc Reads a Formula Off the Syntax Alone                       *)
(** ------------------------------------------------------------------------- *)

(**
  An environment can only make expr_to_pc FAIL, by capturing a variable that
  would otherwise be symbolic. It can never change which formula comes out.
  So a Some-result is a property of the expression alone, and the empty
  environment is the most permissive environment.
*)
Lemma expr_to_pc_functional : forall e Γ1 Γ2 pc1 pc2,
  expr_to_pc Γ1 e = Some pc1 -> expr_to_pc Γ2 e = Some pc2 -> pc1 = pc2.
Proof.
  induction e; intros Γ1 Γ2 pc1 pc2 H1 H2; simpl in *;
    try discriminate; try (injection H1 as ?; injection H2 as ?; congruence).
  - destruct (lookup_env Γ1 v); [discriminate|].
    destruct (lookup_env Γ2 v); [discriminate|].
    injection H1 as ?; injection H2 as ?; congruence.
  - destruct (expr_to_pc Γ1 e1) as [q1|] eqn:E1; [|discriminate].
    destruct (expr_to_pc Γ2 e1) as [q1'|] eqn:E1'; [|discriminate].
    destruct (expr_to_pc Γ1 e2) as [q2|] eqn:E2; [|destruct q1; discriminate].
    destruct (expr_to_pc Γ2 e2) as [q2'|] eqn:E2'; [|destruct q1'; discriminate].
    assert (q1 = q1') by eauto. assert (q2 = q2') by eauto. subst.
    destruct q1'; try discriminate.
    injection H1 as ?; injection H2 as ?; congruence.
Qed.

Lemma expr_to_pc_empty : forall e Γ pc,
  expr_to_pc Γ e = Some pc -> expr_to_pc · e = Some pc.
Proof.
  induction e; intros Γ pc H; simpl in *; try discriminate; try assumption.
  - destruct (lookup_env Γ v); [discriminate | assumption].
  - destruct (expr_to_pc Γ e1) as [q1|] eqn:E1; [|discriminate].
    destruct (expr_to_pc Γ e2) as [q2|] eqn:E2; [|destruct q1; discriminate].
    rewrite (IHe1 Γ q1 E1). rewrite (IHe2 Γ q2 E2). exact H.
Qed.

Lemma expr_to_pc_op_app : forall e Γ pc,
  is_op_app e = true -> expr_to_pc Γ e = Some pc ->
  exists p args, pc = PCPrim p args.
Proof.
  induction e; intros Γ pc Hop Hpc; simpl in *; try discriminate.
  - injection Hpc as ?; subst. eauto.
  - destruct (expr_to_pc Γ e1) as [q1|] eqn:E1; [|discriminate].
    destruct (expr_to_pc Γ e2) as [q2|] eqn:E2; [|destruct q1; discriminate].
    destruct q1; try discriminate. injection Hpc as ?; subst. eauto.
Qed.

(** ========================================================================= *)
(** 8. Decision Functions (Fixpoints) for Solvable and Computations            *)
(** ========================================================================= *)

(** Solvable is decidable *)
Fixpoint solvable_dec (Γ : environment) (e : expr) : {Solvable Γ e} + {~ Solvable Γ e}.
Proof.
  destruct e.
  - destruct (lookup_env Γ v) eqn:Heq.
    + right. intros H. inversion H. rewrite Heq in H1. discriminate.
    + left. apply Solvable_Var. assumption.
  - left. apply Solvable_Lit.
  - left. apply Solvable_PrimOp.
  - right. intros H. inversion H.
  - destruct (is_op_app (EApp e1 e2)) eqn:Hop.
    + destruct (solvable_dec Γ e1) as [S1 | N1].
      * destruct (solvable_dec Γ e2) as [S2 | N2].
        -- left. apply Solvable_AppPrim; auto.
        -- right. intros H. inversion H; subst. apply N2; auto.
      * right. intros H. inversion H; subst. apply N1; auto.
    + right. intros H. inversion H; subst. congruence.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
Defined.

(** Helper inversion lemmas on Solvable *)
Lemma solvable_not_cast : forall Γ e γ, ~ Solvable Γ (ECast e γ).
Proof. intros Γ e γ H. inversion H. Qed.

Lemma solvable_not_if : forall Γ c t f, ~ Solvable Γ (EIf c t f).
Proof. intros Γ c t f H. inversion H. Qed.

(** A solvable term is an SMT term, so the head of its spine is never a data
    constructor *)
Lemma solvable_not_con_app : forall Γ e,
  Solvable Γ e -> is_con_app e = false.
Proof.
  intros Γ e H. induction H as [l | x Hx | p | f a Hop Hf IHf Ha IHa]; simpl;
    try reflexivity.
  exact IHf.
Qed.

Lemma spine_head_con_or_prim : forall e,
  is_con_or_prim (spine_head e) = (is_con_app e || is_op_app e)%bool.
Proof. induction e; simpl; try reflexivity. exact IHe1. Qed.

Lemma fst_unspool_app : forall e args, fst (unspool_app e args) = spine_head e.
Proof. induction e; intros args; simpl; try reflexivity. apply IHe1. Qed.

Lemma comp_app_iff : forall Γ ef ea,
  Comp Γ (EApp ef ea) <-> is_con_app ef = false /\ is_op_app ef = false.
Proof.
  intros Γ ef ea. split.
  - intros H. inversion H as [| | | | ef0 ea0 Hhead]; subst.
    simpl in Hhead. rewrite spine_head_con_or_prim in Hhead.
    apply Bool.orb_false_iff in Hhead. exact Hhead.
  - intros [Hc Ho]. apply Comp_App. simpl.
    rewrite spine_head_con_or_prim, Hc, Ho. reflexivity.
Qed.

Definition comp_dec (Γ : environment) (e : expr) : {Comp Γ e} + {~ Comp Γ e}.
Proof.
  destruct e;
    try (right; intros H; inversion H; fail);
    try (left; constructor; fail).
  - destruct (lookup_env Γ v) eqn:Heq.
    + left. apply Comp_Var. rewrite Heq. discriminate.
    + right. intros H. inversion H; subst. contradiction.
  - destruct (is_con_or_prim (spine_head (EApp e1 e2))) eqn:Hhead.
    + right. intros H. inversion H; subst. congruence.
    + left. apply Comp_App. exact Hhead.
Defined.

Lemma comp_not_con_app : forall Γ e, Comp Γ e -> is_con_app e = false.
Proof.
  intros Γ e Hc. destruct Hc as [| | | | ef ea Hhead]; try reflexivity.
  simpl in Hhead |- *. rewrite spine_head_con_or_prim in Hhead.
  apply Bool.orb_false_iff in Hhead. exact (proj1 Hhead).
Qed.

Lemma comp_not_op_app : forall Γ e, Comp Γ e -> is_op_app e = false.
Proof.
  intros Γ e Hc. destruct Hc as [| | | | ef ea Hhead]; try reflexivity.
  simpl in Hhead |- *. rewrite spine_head_con_or_prim in Hhead.
  apply Bool.orb_false_iff in Hhead. exact (proj2 Hhead).
Qed.

Lemma comp_not_solvable : forall Γ e, Comp Γ e -> ~ Solvable Γ e.
Proof.
  intros Γ e Hc Hs.
  pose proof (comp_not_op_app Γ e Hc) as Hop.
  destruct Hc; inversion Hs; subst; congruence.
Qed.

(** Helper: path-condition convertible primitive application is an operator application *)
Lemma expr_to_pc_prim_is_op_app : forall Γ e p args,
  expr_to_pc Γ e = Some (PCPrim p args) ->
  is_op_app e = true.
Proof.
  intros Γ e.
  induction e; intros p' args' H; simpl in *; try discriminate.
  - destruct (lookup_env Γ v); discriminate.
  - reflexivity.
  - destruct (expr_to_pc Γ e1) eqn:He1; try discriminate.
    destruct p; try discriminate.
    destruct (expr_to_pc Γ e2) eqn:He2; try discriminate.
    inversion H; subst.
    eapply (IHe1 p' l). reflexivity.
Qed.

(** Any expression that successfully converts to a path condition is Solvable *)
Lemma expr_to_pc_solvable : forall Γ e pc,
  expr_to_pc Γ e = Some pc -> Solvable Γ e.
Proof.
  intros Γ e.
  induction e; intros pc Hpc; simpl in Hpc; try discriminate.
  - (* EVar *)
    destruct (lookup_env Γ v) eqn:Heq; [discriminate |].
    inversion Hpc; subst.
    apply Solvable_Var. assumption.
  - (* ELit *)
    inversion Hpc; subst.
    apply Solvable_Lit.
  - (* EPrimOp *)
    inversion Hpc; subst.
    apply Solvable_PrimOp.
  - (* EApp *)
    destruct (expr_to_pc Γ e1) eqn:He1; try discriminate.
    destruct p as [vx | vl | op args]; try discriminate.
    destruct (expr_to_pc Γ e2) eqn:He2; try discriminate.
    inversion Hpc; subst.
    apply Solvable_AppPrim.
    + simpl. eapply (expr_to_pc_prim_is_op_app Γ e1 op args He1).
    + apply (IHe1 (PCPrim op args) eq_refl).
    + apply (IHe2 p eq_refl).
Qed.

(** Solvable is exactly expr_to_pc's domain: expr_to_pc_solvable above is one
    direction, and since only capture can make expr_to_pc fail, anything
    solvable in any environment has a formula in the empty environment. *)
Lemma solvable_expr_to_pc : forall Γ e,
  Solvable Γ e -> exists pc, expr_to_pc · e = Some pc.
Proof.
  intros Γ e H. induction H as [l | x Hx | p | f a Hop Hf IHf Ha IHa]; simpl.
  - eauto.
  - eauto.
  - eauto.
  - destruct IHf as [pcf Ef]. destruct IHa as [pca Ea]. simpl in Hop.
    destruct (expr_to_pc_op_app f · pcf Hop Ef) as [p [args Hpcf]]. subst.
    rewrite Ef, Ea. eauto.
Qed.


(** ========================================================================= *)
(** 8. Pattern Matching and Branch Folding: fold-alts (§3.2, lines 570-590)   *)
(** ========================================================================= *)

(** Helper predicate identifying if-then-else expressions *)
Definition is_if (e : expr) : bool :=
  match e with
  | EIf _ _ _ => true
  | _ => false
  end.

(** Helper predicate identifying bottom values *)
Definition is_bot (e : expr) : bool :=
  match e with
  | EBot _ => true
  | _ => false
  end.

(** Helper predicate identifying casts *)
Definition is_cast (e : expr) : bool :=
  match e with
  | ECast _ _ => true
  | _ => false
  end.

(** Lookup a matching constructor alternative in a branch list: find(D, a⃗) *)
Fixpoint find_alt (d : dcon) (alts : list alt) : option (list var * expr) :=
  match alts with
  | [] => None
  | Alt d' xs ep :: rest =>
      if string_dec d d' then Some (xs, ep) else find_alt d rest
  end.

(** Decompose constructor application into constructor name and argument list: D e⃗a *)
Definition decompose_con_app (e : expr) : option (dcon * list expr) :=
  match unspool_app e [] with
  | (ECon d, args) => Some (d, args)
  | _ => None
  end.

(** The head of a spine is the expression itself when the expression is not an
    application, so a spine whose head is not a branch is not a branch. *)
Lemma is_if_false_of_spine_head : forall e,
  is_if (fst (unspool_app e [])) = false -> is_if e = false.
Proof.
  intros e H. destruct e; simpl in H |- *; try reflexivity. discriminate H.
Qed.

(** Construct curried constructor application from constructor name and argument list *)
Definition make_con_app (d : dcon) (args : list expr) : expr :=
  fold_left EApp args (ECon d).

Definition delay (Γ : environment) (e : expr) : expr :=
  match e with
  | EThunk _ _ => e
  | _ => EThunk Γ e
  end.

Lemma delay_delay : forall Γ Γ' e, delay Γ (delay Γ' e) = delay Γ' e.
Proof. intros Γ Γ' e. destruct e; reflexivity. Qed.

Lemma map_delay_delay : forall Γ Γ' args,
  map (delay Γ) (map (delay Γ') args) = map (delay Γ') args.
Proof.
  intros Γ Γ' args. rewrite map_map.
  apply map_ext. apply delay_delay.
Qed.

Lemma unspool_fold_left_app : forall args h acc,
  unspool_app (fold_left EApp args h) acc = unspool_app h (args ++ acc).
Proof.
  induction args as [| a tl IH]; intros h acc; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Lemma make_con_app_unspool : forall d args,
  unspool_app (make_con_app d args) [] = (ECon d, args).
Proof.
  intros d args. unfold make_con_app. rewrite unspool_fold_left_app.
  rewrite app_nil_r. reflexivity.
Qed.

Lemma make_con_app_is_con_app : forall d args,
  is_con_app (make_con_app d args) = true.
Proof. intros d args. exact (unspool_is_con_app _ _ _ _ (make_con_app_unspool d args)). Qed.

End SymCore.

Ltac no_con_value :=
  match goal with
  | [ H : make_con_app ?d ?args = _ |- _ ] =>
      let Hc := fresh "Hc" in
      pose proof (make_con_app_is_con_app d args) as Hc;
      rewrite H in Hc; simpl in Hc; discriminate Hc
  end.

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
(** 8.1 Merging Common Prefixes of a Branch (§3.3)                            *)
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

  Clauses 3, 5, 6 and 7: a lambda merges when the binders agree; a bottom, a
  type and a coercion merge only when the two arms are the same term.

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
        | ELam x1 b1, ELam x2 b2 =>
            if String.eqb x1 x2 then ELam x1 (EIf ec b1 b2) else EIf ec et ef
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

(** ------------------------------------------------------------------------- *)
(** Fuel: a depth bound carried by the reduction judgement                     *)
(** ------------------------------------------------------------------------- *)

(**
  A fuel value bounds how deep a derivation may nest. Inf is no bound. Fin n
  is a bound of n rules.

  A fuel is Spent or Live. Every rule below except Rule Out-Of-Fuel concludes
  at a Live fuel f and passes dec f to each of its recursive premises. So a
  rule at Fin (S n) has its premises at Fin n, and at Fin 0, which is Spent,
  Rule Out-Of-Fuel is the only rule. A derivation at Fin n therefore nests at
  most n ordinary rules, and any part of it that needs more ends in Rule
  Out-Of-Fuel.

  dec Unlimited is Inf, so a derivation at Inf never runs down, and the rule
  set at Inf is exactly the rule set this judgement had before fuel existed.
  The notation Φ; Γ ⊢ e ⇓ e' below therefore still means what it always meant.

  fold_alts is the fold-alts function of Rule Case, not a rule of the
  reduction. It spends nothing: it runs at the fuel Rule Case hands it and
  passes that fuel on unchanged.
*)
Inductive live_fuel := Unlimited | Remaining (n : nat).

Inductive fuel := Spent | Live (f : live_fuel).

End SymCore.

Notation Inf := (Live Unlimited).

Section SymCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Definition Fin (n : nat) : fuel :=
  match n with O => Spent | S m => Live (Remaining m) end.

(** Spend one level of the bound. *)
Definition dec (f : live_fuel) : fuel :=
  match f with Unlimited => Inf | Remaining n => Fin n end.

(** The unlimited budget is a fixed point of dec. This is the equation that
    makes eval Inf the old, unindexed relation. *)
Lemma dec_Inf : dec Unlimited = Inf. Proof. reflexivity. Qed.

(**
  Mutual inductive definitions of:
  - Big-Step Reduction Judgement: Φ; Γ ⊢ e ⇓ e' (Figure 3)
  - Pattern Matching and Branch Folding: fold-alts(Φ, Γ, e, a⃗) (§3.2, lines 570-590)
*)
Inductive eval : fuel -> path_condition -> environment -> expr -> expr -> Prop :=
  (** Rule Var: Variable lookup in Γ and recursive evaluation *)
  | Eval_Var : forall f Φ Γ x Γ' e e',
      lookup_env Γ x = Some (Γ', e) ->
      eval (dec f) Φ Γ' e e' ->
      eval (Live f) Φ Γ (EVar x) e'

  (** Rule Sym-Var: a variable that Γ does not bind is a symbolic value.
      Solvable_Var already classifies it as a value, and every other value
      form (literal, constructor, bottom, coercion, type, closure) has a
      reflexivity rule; without this one no expression that mentions a
      symbolic variable can reduce at all. *)
  | Eval_SymVar : forall f Φ Γ x,
      lookup_env Γ x = None ->
      eval (Live f) Φ Γ (EVar x) (EVar x)

  (** Rule Lit: Literal reflexivity *)
  | Eval_Lit : forall f Φ Γ l,
      eval (Live f) Φ Γ (ELit l) (ELit l)

  (** Rule Con: a constructor spine is a value once each field is paired with
      the environment it was written in. A field that is already a thunk
      keeps the environment it carries. The fields stay unevaluated:
      fold-alts binds them into the environment, and Rule Thunk forces one
      only when a variable reads it. *)
  | Eval_Con : forall f Φ Γ e d args,
      unspool_app e [] = (ECon d, args) ->
      eval (Live f) Φ Γ e (make_con_app d (map (delay Γ) args))

  (** Rule Cast: Evaluate expression and simplify cast *)
  | Eval_Cast : forall f Φ Γ e γ e',
      eval (dec f) Φ Γ e e' ->
      eval (Live f) Φ Γ (ECast e γ) (cast_expr e' γ)

  (** Rule App-Abs: Beta-reduction with closure environment extension *)
  | Eval_AppAbs : forall f Φ Γ Γ' x eb ea eb',
      eval (dec f) Φ (extend_env Γ' x Γ ea) eb eb' ->
      eval (Live f) Φ Γ (EApp (EClos Γ' x eb) ea) eb'

  (** Rule App-Spine: Reduce a function head that is a computation. A cast,
      a branch, a closure, a bottom and a constructor or primitive spine are
      not computations; each of them has its own application rule. *)
  | Eval_AppSpine : forall f Φ Γ ef ea ef' er,
      Comp Γ ef ->
      eval (dec f) Φ Γ ef ef' ->
      eval (dec f) Φ Γ (EApp ef' ea) er ->
      eval (Live f) Φ Γ (EApp ef ea) er

  (** Rule Bot: Bottom value reflexivity *)
  | Eval_Bot : forall f Φ Γ b,
      eval (Live f) Φ Γ (EBot b) (EBot b)

  (** Rule App-Prim: Evaluate primitive operation arguments and reduce *)
  | Eval_AppPrim : forall f Φ Γ ef ea p args args',
      unspool_app (EApp ef ea) [] = (EPrimOp p, args) ->
      length args = primop_arity p ->
      Forall2 (eval (dec f) Φ Γ) args args' ->
      eval (Live f) Φ Γ (EApp ef ea) (reduce_prim p args')

  (** Rule Lam: Function abstraction evaluates to runtime closure *)
  | Eval_Lam : forall f Φ Γ x e,
      eval (Live f) Φ Γ (ELam x e) (EClos Γ x e)

  (** Rule App-Cast: Higher-order coercion pushing *)
  | Eval_AppCast : forall f Φ Γ ef γ ea γ_a γ_r er,
      decomp_coerc_arrow γ = Some (γ_a, γ_r) ->
      eval (dec f) Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er ->
      eval (Live f) Φ Γ (EApp (ECast ef γ) ea) er

  (** Rule App-If: an application of a branch applies each arm *)
  | Eval_AppIf : forall f Φ Γ ec et ef ea er,
      eval (dec f) Φ Γ (EIf ec (EApp et ea) (EApp ef ea)) er ->
      eval (Live f) Φ Γ (EApp (EIf ec et ef) ea) er

  (**
    No rule for: applying a VALUE that carries a coercion which is not an
    arrow.

    Figure 3 has no rule for this shape and neither does this judgement.
    Rule App-Cast wants a coercion that splits into an argument coercion and
    a result coercion, and this one does not split. Rule App-Spine reads only
    computations, and a cast is not one. So the term is stuck, deliberately:
    applying something whose coercion is not an arrow is applying a
    non-function, which System FC rejects at type-check time. A judgement with
    no typing rules gets stuck there instead of inventing an answer.

    ConCore.v, Section 12.5 records the history: this shape once had a rule,
    Rule App-Cast-Opaque, because Rule App-Spine then accepted a non-arrow
    cast operator and the concrete side could reach the shape while the
    symbolic side walked on. Comp excludes every cast, which closes that gap
    on both sides at once.
  *)

  (** Rule App-Bot: Propagation of bottom in function position *)
  | Eval_AppBot : forall f Φ Γ b ea,
      eval (Live f) Φ Γ (EApp (EBot b) ea) (EBot b)

  (** Rule Case: Evaluate scrutinee, merge common prefixes, and fold alternatives *)
  | Eval_Case : forall f Φ Γ es alts es' er,
      eval (dec f) Φ Γ es es' ->
      fold_alts (dec f) Φ Γ (merge Γ es') alts er ->
      eval (Live f) Φ Γ (ECase es alts) er

  (** Rule If: Evaluate condition, convert to path condition, and branch *)
  | Eval_If : forall f Φ Γ ec et ef ec' et' ef' pc_c,
      eval (dec f) Φ Γ ec ec' ->
      expr_to_pc Γ ec' = Some pc_c ->
      eval (dec f) (Φ ∧ pc_c) Γ et et' ->
      eval (dec f) (Φ ∧ ¬ pc_c) Γ ef ef' ->
      eval (Live f) Φ Γ (EIf ec et ef) (EIf ec' et' ef')

  (** Rule Coercion: Evaluate coercion under substitution *)
  | Eval_Coercion : forall f Φ Γ γ,
      eval (Live f) Φ Γ (ECoercion γ) (ECoercion (subst_coerc Γ γ))

  (** Rule Prune: Infeasible path conditions reduce to unreachable *)
  | Eval_Prune : forall f Φ Γ e,
      sat Φ = false ->
      eval (Live f) Φ Γ e (EBot BUnreachable)

  (** Rule Type: Evaluate type under substitution *)
  | Eval_Type : forall f Φ Γ τ,
      eval (Live f) Φ Γ (EType τ) (EType (subst_type Γ τ))

  (** Rule Thunk: a thunk evaluates its expression in its own environment *)
  | Eval_Thunk : forall f Φ Γ Γ' e e',
      eval (dec f) Φ Γ' e e' ->
      eval (Live f) Φ Γ (EThunk Γ' e) e'

  (**
    Rule Out-Of-Fuel: a spent budget gives up and reports the out-of-fuel
    bottom. No concrete term is that bottom.
    It is the only rule at Spent, and no other rule concludes there, so an
    expression at Fin 0 has exactly one value.

    The rule writes Spent directly in its CONCLUSION index, and every other
    rule writes Live f. Two different constructors never unify, so inversion
    of a derivation at Inf drops this case outright, and inversion of a
    derivation at Spent drops every other case. That keeps eval Inf a drop-in
    replacement for the unindexed judgement, which is what lets every existing
    statement stand unchanged.

    This is a rule of eval only. fold_alts has no out-of-fuel rule: it spends
    no fuel, and every expression it evaluates goes through eval.
  *)
  | Eval_OutOfFuel : forall Φ Γ e,
      eval Spent Φ Γ e (EBot BOutOfFuel)

with fold_alts : fuel -> path_condition -> environment -> expr -> list alt -> expr -> Prop :=
  (** Branch traversal: condition is converted to path condition *)
  | FoldAlts_If : forall f Φ Γ ec et ef alts et' ef' pc_c,
      expr_to_pc Γ ec = Some pc_c ->
      fold_alts f (Φ ∧ pc_c) Γ et alts et' ->
      fold_alts f (Φ ∧ ¬ pc_c) Γ ef alts ef' ->
      fold_alts f Φ Γ (EIf ec et ef) alts (EIf ec et' ef')

  (** Fallback for ill-formed condition in branching *)
  | FoldAlts_IfFail : forall f Φ Γ ec et ef alts,
      expr_to_pc Γ ec = None ->
      fold_alts f Φ Γ (EIf ec et ef) alts (EBot BUndefined)

  (** Constructor match: find alternative and reduce body *)
  | FoldAlts_Con : forall f Φ Γ e d ea xs ep alts er,
      decompose_con_app e = Some (d, ea) ->
      find_alt d alts = Some (xs, ep) ->
      eval f Φ (extend_env_multi Γ xs ea Γ) ep er ->
      fold_alts f Φ Γ e alts er

  (** Bottom propagation *)
  | FoldAlts_Bot : forall f Φ Γ b alts,
      fold_alts f Φ Γ (EBot b) alts (EBot b)

  (**
    Otherwise: undefined behaviour.

    The first premise reads the head of the scrutinee's application spine and
    demands that it is not a branch. Demanding only that the scrutinee itself
    is not a branch would be too weak: it would let this rule answer
    EApp (EIf ec et ef) a, a scrutinee that still has a branch to resolve, with
    a bottom. Rule FoldAlts_If resolves branches, and it only sees a branch
    that sits at the top. The premise as written implies is_if e = false
    (is_if_false_of_spine_head), so nothing this rule used to reject is
    accepted now.
  *)
  | FoldAlts_Otherwise : forall f Φ Γ e alts,
      is_if (fst (unspool_app e [])) = false ->
      (match decompose_con_app e with
       | Some (d, _) => find_alt d alts = None
       | None => True
       end) ->
      is_bot e = false ->
      fold_alts f Φ Γ e alts (EBot BUndefined).

End SymCore.

(** Notation for big-step reduction: Φ; Γ ⊢ e ⇓ e' *)
Notation "Φ ';' Γ '⊢' e '⇓' e'" := (eval Inf Φ Γ e e') (at level 70, no associativity).

Section SymCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

(** ========================================================================= *)
(** 10. Metatheory of SymCore (§3.2, §3.3)                                     *)
(** ========================================================================= *)

(** ------------------------------------------------------------------------- *)
(** 10.0 Source Expressions (System FC Translated AST, Fig. 1)                *)
(** ------------------------------------------------------------------------- *)

(**
  Source expressions represent pure System FC ASTs translated from Haskell
  prior to evaluation. They contain no runtime environment closures (EClos)
  and no runtime symbolic execution branch trees (EIf).
*)



(** ------------------------------------------------------------------------- *)
(** Free Variables and Well-Formed Environments                               *)
(** ------------------------------------------------------------------------- *)

(** Free variables of an expression *)
Fixpoint fv (e : expr) : list var :=
  match e with
  | EVar x => [x]
  | EApp f a => fv f ++ fv a
  | ELam x body => remove string_dec x (fv body)
  | EClos _ x body => remove string_dec x (fv body)
  | ECase es alts => fv es ++ flat_map fv_alt alts
  | ECast e _ => fv e
  | EIf ec et ef => fv ec ++ fv et ++ fv ef
  | EBot (BRaise e) => fv e
  | EThunk _ e => fv e
  | _ => []
  end
with fv_alt (a : alt) : list var :=
  match a with
  | Alt _ xs ep => fold_right (remove string_dec) (fv ep) xs
  end.

(** Domain (bound variables) of an environment *)
Fixpoint dom_env (Γ : environment) : list var :=
  match Γ with
  | · => []
  | ExtendEnv x _ rest => x :: dom_env rest
  end.

(**
  An environment Γ is well-formed with respect to expression e if
  no free variable of e occurs in Γ (i.e. all free variables of e
  are fresh / unbound / symbolic).
*)
Definition wf_env (e : expr) (Γ : environment) : Prop :=
  forall x, In x (fv e) -> lookup_env Γ x = None.

(** The empty environment is universally well-formed for any expression *)
Lemma wf_empty_env : forall e,
  wf_env e ·.
Proof.
  intros e x Hin.
  reflexivity.
Qed.

(** In a well-formed environment, every free variable is Solvable *)
Lemma wf_env_var_solvable : forall x Γ,
  wf_env (EVar x) Γ ->
  Solvable Γ (EVar x).
Proof.
  intros x Γ Hwf.
  apply Solvable_Var.
  apply Hwf.
  simpl. left. reflexivity.
Qed.

(** Well-formedness distributes over sub-expressions *)
Lemma wf_env_app_l : forall f a Γ,
  wf_env (EApp f a) Γ ->
  wf_env f Γ.
Proof.
  intros f a Γ Hwf x Hin.
  apply Hwf.
  simpl. apply in_or_app. left. assumption.
Qed.

Lemma wf_env_app_r : forall f a Γ,
  wf_env (EApp f a) Γ ->
  wf_env a Γ.
Proof.
  intros f a Γ Hwf x Hin.
  apply Hwf.
  simpl. apply in_or_app. right. assumption.
Qed.

Lemma wf_env_if_c : forall ec et ef Γ,
  wf_env (EIf ec et ef) Γ ->
  wf_env ec Γ.
Proof.
  intros ec et ef Γ Hwf x Hin.
  apply Hwf.
  simpl. apply in_or_app. left. assumption.
Qed.

(** ------------------------------------------------------------------------- *)
(** 10.1 Infeasible Path Invariance & Pruning Soundness (§3.3)                 *)
(** ------------------------------------------------------------------------- *)

(** Under an unsatisfiable path condition, evaluation always prunes to unreachable *)
Lemma eval_prune_sound : forall Φ Γ e,
  sat Φ = false ->
  Φ ; Γ ⊢ e ⇓ (EBot BUnreachable).
Proof.
  intros Φ Γ e Hsat.
  apply Eval_Prune.
  assumption.
Qed.

(** ------------------------------------------------------------------------- *)
(** 10.2 Merge and Alternative Folding (§3.3)                                  *)
(** ------------------------------------------------------------------------- *)

(**
  There is no contract here any more, because merge is now a definition.

  What used to sit here was an assumption saying that folding a merged
  scrutinee and folding the raw one reach the same result. That assumption is
  false of the definition in Section 8.1, and so is the one-sided repair that
  asks only for the merged fold to answer SOMETHING:

    fold_alts f Φ Γ e alts r ->
    exists r', fold_alts f Φ Γ (merge Γ e) alts r' and r' covers r.

  scratch/MergeIsNotThePapersIte.v proves both false and shows why. Rule
  FoldAlts_If reads its guard with expr_to_pc BEFORE the guard is evaluated,
  while Rule If reads the guard's VALUE. Merging a constructor spine moves
  the guard from the first position to the second, so a guard fold-alts
  accepts can be a guard evaluation is stuck on, and the merged fold then has
  no derivation at all.

  What IS true of merge, and what the development uses, is merge_not_if
  above - merge leaves a non-branch alone, so it is the identity on every
  ConCore term - and merge_contains in ConCore.v: merging keeps an instance,
  or turns the branch into a scrutinee that no alternative matches, as the
  instance is too.
*)

(**
  No branch is ever buried below a resolved head: a scrutinee fold_alts can
  fold over either IS the branch (§3.3 - the case a match still needs to
  choose between alternatives) or its application spine has no branch at its
  head at all. The ill-formed shape "EApp (EIf ..) a" therefore never appears
  as a scrutinee.

  This was an axiom about Grisette state merging until the rules were fixed.
  As an axiom it was false, because Rule FoldAlts_Otherwise then accepted
  exactly the shape the axiom denied; scratch/FoldAltsNoNestedIfIsFalse.v
  derived False from it. Rule FoldAlts_Otherwise now reads the spine head
  itself, so the statement is a consequence of the five rules and needs no
  assumption about merge.
*)
Lemma fold_alts_no_nested_if : forall Φ Γ e alts er,
  fold_alts Inf Φ Γ e alts er ->
  forall head args, unspool_app e [] = (head, args) -> is_if head = true -> head = e.
Proof.
  intros Φ Γ e alts er Hfold head args Hunspool Hhead_if.
  inversion Hfold as
    [ f0 Φ0 Γ0 ec et ef alts0 et' ef' pc_c Hpc Hfold_t Hfold_f
    | f0 Φ0 Γ0 ec et ef alts0 Hpc_none
    | f0 Φ0 Γ0 e0 d ea xs ep alts0 er0 Hdec Halt Heval_ep
    | f0 Φ0 Γ0 b alts0
    | f0 Φ0 Γ0 e0 alts0 Hspine Hnoalt Hnotbot ]; subst.
  - simpl in Hunspool; injection Hunspool as Hh Ha; subst; reflexivity.
  - simpl in Hunspool; injection Hunspool as Hh Ha; subst; reflexivity.
  - exfalso. unfold decompose_con_app in Hdec. rewrite Hunspool in Hdec.
    destruct head; try discriminate Hdec; discriminate Hhead_if.
  - simpl in Hunspool; injection Hunspool as Hh Ha; subst; discriminate Hhead_if.
  - exfalso. rewrite Hunspool in Hspine. simpl in Hspine.
    rewrite Hspine in Hhead_if. discriminate Hhead_if.
Qed.

(** ------------------------------------------------------------------------- *)
(** 10.3 Solvable Results of Primitives (§3.2)                                *)
(** ------------------------------------------------------------------------- *)

(**
  Primitive reduction produces a solvable expression WHEN ITS ARGUMENTS ARE
  THEMSELVES SOLVABLE (§3.2, SMT contract - Axiom 2).

  The hypothesis is essential and was missing. Solvable admits no EIf, so an
  unconditional version would say that reduce-prim of a *branching* argument
  is still a plain SMT term - i.e. that the theory solver silently erases the
  branch. Worse, it is stated for EVERY Γ, and Solvable_Var demands the
  variable be unbound in Γ, so an unconditional version would force the result
  to mention no variable at all: reduce-prim's range would be ground terms.
  ConCore.v's unconditional_solvable_forces_constancy turns that into the
  collapse it is: with reduce_prim_contains, an unconditional version forces
  reduce_prim to be a CONSTANT function on literals as soon as any condition
  is resolvable (1+1 = 1+2).

  With the hypothesis, a primitive applied to plain SMT arguments still yields
  a plain SMT term, while a primitive applied to an argument that still
  branches is left free to distribute over that branch and return an EIf.
*)
Class ReducePrimSolvable : Prop :=
reduce_prim_solvable : forall Γ p args,
  Forall (Solvable Γ) args ->
  Solvable Γ (reduce_prim p args).

Context {reduce_prim_solvable_law : ReducePrimSolvable}.

(**
  SMT terms are always fully-formed application trees: an SMT solver has no
  notion of a "partially applied" or "over-applied" operator, so whenever
  reduce_prim's result unspools to an operator head, that operator is
  applied to exactly as many arguments as its arity demands (§3.1, SMT
  contract - Axiom 3). This is what makes over-application of an
  already-saturated primitive (Rule App-Prim never fires on it) get stuck
  rather than silently re-reducing with the wrong number of arguments.
*)
Class ReducePrimSaturated : Prop :=
reduce_prim_saturated : forall p args p0 args0,
  unspool_app (reduce_prim p args) [] = (EPrimOp p0, args0) ->
  length args0 = primop_arity p0.

Context {reduce_prim_saturated_law : ReducePrimSaturated}.

(** Unspooling an application spine preserves the operator head property *)
Lemma unspool_is_op_app : forall e args p args0,
  unspool_app e args = (EPrimOp p, args0) ->
  is_op_app e = true.
Proof.
  induction e; intros args op args0 H; simpl in *; try discriminate.
  - injection H as ? ?; subst. reflexivity.
  - apply IHe1 in H. exact H.
Qed.

(** Unspooling with an extra accumulator only ever appends to the argument
    list already found for the empty accumulator; the head is unchanged *)
Lemma unspool_app_shift : forall (e : expr) (L acc : list expr) (head : expr) (args : list expr),
  unspool_app e L = (head, args) ->
  unspool_app e (L ++ acc)%list = (head, (args ++ acc)%list).
Proof.
  induction e; intros L acc head args H; simpl in *;
  try (injection H as ? ?; subst; reflexivity).
  apply IHe1 with (L := e2 :: L). exact H.
Qed.

(** An operator-headed application spine always unspools to a primitive head *)
Lemma is_op_app_unspool : forall e,
  is_op_app e = true ->
  exists p args, unspool_app e [] = (EPrimOp p, args).
Proof.
  induction e; intros H; simpl in H; try discriminate.
  - exists p, []. reflexivity.
  - destruct (IHe1 H) as [p [args Heq]].
    apply (unspool_app_shift e1 [] [e2] (EPrimOp p) args) in Heq.
    simpl in Heq. exists p, (args ++ [e2])%list. exact Heq.
Qed.

(** Solvable expressions that are not operators cannot be applied as functions *)
Lemma solvable_app_eval_false : forall Φ Γ e a v,
  sat Φ = true ->
  Solvable Γ e ->
  is_op_app e = false ->
  eval Inf Φ Γ (EApp e a) v ->
  False.
Proof.
  intros Φ Γ e a v Hsat Hsolv Hnotop Heval.
  inversion Heval; subst.
  - (* Eval_Con: a solvable head is never a constructor *)
    match goal with
    | [ Hu : unspool_app _ _ = (ECon _, _) |- _ ] =>
        apply unspool_is_con_app in Hu; simpl in Hu;
        rewrite (solvable_not_con_app Γ e Hsolv) in Hu; discriminate
    end.
  - (* Eval_AppAbs *)
    inversion Hsolv; subst; try discriminate.
  - (* Eval_AppSpine *)
    match goal with [ Hc : Comp _ _ |- _ ] => exact (comp_not_solvable _ _ Hc Hsolv) end.
  - (* Eval_AppPrim *)
    match goal with
    | [ H : unspool_app (EApp _ _) [] = _ |- _ ] =>
        simpl in H; apply unspool_is_op_app in H; rewrite H in Hnotop; discriminate
    end.
  - (* Eval_AppCast *)
    inversion Hsolv; subst; try discriminate.
  - (* Eval_AppIf *)
    inversion Hsolv.
  - (* Eval_AppBot *)
    inversion Hsolv; subst; try discriminate.
  - (* Eval_Prune *)
    match goal with
    | [ H : sat Φ = false |- _ ] =>
        rewrite Hsat in H; discriminate
    end.
Qed.

(**
  A saturated (arity-matching) primitive-operator result can never itself be
  applied to a further argument: Rule App-Prim demands the combined spine's
  argument count match the operator's arity exactly (§3.1, arity), so one
  argument too many gets stuck, and no other rule can fire on a solvable
  operator application.
*)
(** Every argument of a solvable operator spine is itself solvable *)
Lemma solvable_spine_args : forall Γ e,
  Solvable Γ e ->
  forall L p args,
    Forall (Solvable Γ) L ->
    unspool_app e L = (EPrimOp p, args) ->
    Forall (Solvable Γ) args.
Proof.
  induction 1; intros L p0 args0 HL Hunspool; simpl in Hunspool;
    try (injection Hunspool as ? ?; subst; assumption);
    try discriminate.
  eapply IHSolvable1; [| exact Hunspool].
  constructor; assumption.
Qed.

(**
  Solvable terms reduce to solvable terms: a literal and a symbolic variable
  are already values, a bare operator is stuck, and an operator spine reduces
  by Rule App-Prim, whose arguments are solvable by solvable_spine_args and
  so reduce to solvable results - which is exactly the hypothesis the
  repaired reduce_prim_solvable needs.

  Written as a Fixpoint on the derivation rather than by `induction` because
  Rule App-Prim needs the statement for every argument of its
  Forall2 (eval (dec f) Φ Γ) args args', which Coq's auto-derived induction
  principle does not supply.

  Unlimited budget only, which is why the fuel comes in as k0 with a k0 = Inf
  premise instead of being left free. At Fin 0 Rule Out-Of-Fuel takes the
  solvable literal ELit l to EBot BOutOfFuel, and no rule of Solvable accepts
  a bottom. The premise is what lets the out-of-fuel case close by
  discriminate.
*)
Fixpoint solvable_eval_solvable (k0 : fuel) (Φ : path_condition) (Γ : environment) (e v : expr)
  (Heval : eval k0 Φ Γ e v) {struct Heval} :
  k0 = Inf -> sat Φ = true -> Solvable Γ e -> Solvable Γ v.
Proof.
  destruct Heval as
    [ k Φ Γ x Γ' e e' Hlookup Heval_x
    | k Φ Γ x Hnone
    | k Φ Γ l
    | k Φ Γ e d args Hunspool
    | k Φ Γ e γ e' Heval_e
    | k Φ Γ Γ' x eb ea eb' Heval_b
    | k Φ Γ ef ea ef' er Hcomp Heval_f Heval_app2
    | k Φ Γ b
    | k Φ Γ ef ea p args args' Hunspool Harity Hargs
    | k Φ Γ x e
    | k Φ Γ ef γ ea γ_a γ_r er Hdecomp Heval_pushed
    | k Φ Γ ec et ef ea er Heval_arms
    | k Φ Γ b ea
    | k Φ Γ es alts es' er Heval_es Hfold
    | k Φ Γ ec et ef ec' et' ef' pc_c Heval_c Hpc Heval_t Heval_f
    | k Φ Γ γ
    | k Φ Γ e Hunsat
    | k Φ Γ τ
    | k Φ Γ Γ' e e' Heval_t
    | Φ Γ e
    ]; intros Hk0 Hsat Hsolv; try (injection Hk0 as Hk0; subst k).
  - (* Eval_Var: a bound variable is not solvable *)
    inversion Hsolv; subst. rewrite Hlookup in H0. discriminate.
  - (* Eval_SymVar *) exact Hsolv.
  - (* Eval_Lit *) exact Hsolv.
  - (* Eval_Con: a solvable head is never a constructor *)
    exfalso. apply unspool_is_con_app in Hunspool.
    rewrite (solvable_not_con_app Γ e Hsolv) in Hunspool. discriminate.
  - (* Eval_Cast *) inversion Hsolv.
  - (* Eval_AppAbs: a closure is not solvable *)
    inversion Hsolv as [| | | f a Hop Hsf Hsa]; subst. inversion Hsf.
  - (* Eval_AppSpine: a solvable head is not a computation *)
    exfalso. apply (comp_not_solvable _ _ Hcomp).
    inversion Hsolv as [| | | f a Hop Hsf Hsa]; subst. exact Hsf.
  - (* Eval_Bot *) inversion Hsolv.
  - (* Eval_AppPrim *)
    assert (Hsargs : Forall (Solvable Γ) args)
      by (eapply solvable_spine_args; [exact Hsolv | constructor | exact Hunspool]).
    apply reduce_prim_solvable.
    clear Hunspool Harity Hsolv.
    induction Hargs as [| a a' args_tl args'_tl Ha Hargs_tl IH].
    + constructor.
    + inversion Hsargs as [| a0 tl0 Hsa Hstl]; subst.
      constructor.
      * exact (solvable_eval_solvable Inf Φ Γ a a' Ha eq_refl Hsat Hsa).
      * exact (IH Hstl).
  - (* Eval_Lam *) inversion Hsolv.
  - (* Eval_AppCast: a cast is not solvable *)
    inversion Hsolv as [| | | f a Hop Hsf Hsa]; subst. inversion Hsf.
  - (* Eval_AppIf: a branch is not solvable *)
    inversion Hsolv as [| | | f a Hop Hsf Hsa]; subst. inversion Hsf.
  - (* Eval_AppBot: a bottom is not solvable *)
    inversion Hsolv as [| | | f a Hop Hsf Hsa]; subst. inversion Hsf.
  - (* Eval_Case *) inversion Hsolv.
  - (* Eval_If *) inversion Hsolv.
  - (* Eval_Coercion *) inversion Hsolv.
  - (* Eval_Prune *) rewrite Hsat in Hunsat. discriminate.
  - (* Eval_Type *) inversion Hsolv.
  - (* Eval_Thunk *) inversion Hsolv.
  - (* Eval_OutOfFuel *) discriminate Hk0.
Qed.

Lemma reduce_prim_app_false : forall Γ p args ac v,
  Forall (Solvable Γ) args ->
  eval Inf pc_true Γ (EApp (reduce_prim p args) ac) v -> False.
Proof.
  intros Γ p args ac v Hsargs Heval.
  remember (reduce_prim p args) as v_f eqn:Heqvf.
  assert (Hsolv : Solvable Γ v_f) by (subst v_f; apply reduce_prim_solvable; assumption).
  destruct (is_op_app v_f) eqn:Hop.
  - destruct (is_op_app_unspool v_f Hop) as [p0 [args0 Hunspool]].
    assert (Hsat : length args0 = primop_arity p0)
      by (subst v_f; eapply reduce_prim_saturated; exact Hunspool).
    inversion Heval; subst.
    + (* Eval_Con: a solvable head is never a constructor *)
      match goal with
      | [ Hu : unspool_app _ _ = (ECon _, _) |- _ ] =>
          apply unspool_is_con_app in Hu; simpl in Hu;
          rewrite (solvable_not_con_app _ _ Hsolv) in Hu; discriminate
      end.
    + (* Eval_AppAbs: v_f cannot be a closure *)
      rewrite <- H0 in Hsolv. inversion Hsolv.
    + (* Eval_AppSpine: a solvable v_f is not a computation *)
      match goal with [ Hc : Comp _ _ |- _ ] => exact (comp_not_solvable _ _ Hc Hsolv) end.
    + (* Eval_AppPrim: the combined spine's arity no longer matches *)
      simpl in H2.
      apply (unspool_app_shift (reduce_prim p args) [] [ac] (EPrimOp p0) args0) in Hunspool.
      simpl in Hunspool.
      rewrite Hunspool in H2.
      inversion H2; subst.
      rewrite length_app in H5.
      simpl in H5.
      lia.
    + (* Eval_AppCast: v_f cannot be a cast *)
      rewrite <- H0 in Hsolv. inversion Hsolv.
    + (* Eval_AppIf: v_f cannot be a branch *)
      match goal with [ Heq : EIf _ _ _ = _ |- _ ] => rewrite <- Heq in Hsolv end.
      inversion Hsolv.
    + (* Eval_AppBot: v_f cannot be a bottom *)
      rewrite <- H in Hsolv. inversion Hsolv.
    + (* Eval_Prune: pc_true is always satisfiable *)
      rewrite sat_pc_true in H0. discriminate.
  - eapply solvable_app_eval_false;
      [apply sat_pc_true | exact Hsolv | exact Hop | exact Heval].
Qed.

(** ------------------------------------------------------------------------- *)
(** 10.4 Determinism of Evaluation (§3.2)                                      *)
(** ------------------------------------------------------------------------- *)

(** Branch folding on bottom always preserves the bottom value *)
Lemma fold_alts_bot_same : forall f Φ Γ b alts r,
  fold_alts f Φ Γ (EBot b) alts r ->
  r = EBot b.
Proof.
  intros f Φ Γ b alts r Hfold.
  inversion Hfold; subst.
  - simpl in H. discriminate.
  - reflexivity.
  - simpl in H1. discriminate.
Qed.

(** Branch folding on bottom is deterministic *)
Lemma fold_alts_bot_deterministic : forall f Φ Γ b alts r1 r2,
  fold_alts f Φ Γ (EBot b) alts r1 ->
  fold_alts f Φ Γ (EBot b) alts r2 ->
  r1 = r2.
Proof.
  intros f Φ Γ b alts r1 r2 H1 H2.
  apply fold_alts_bot_same in H1.
  apply fold_alts_bot_same in H2.
  subst. reflexivity.
Qed.

(** Evaluation of bottom values under a satisfiable path condition *)
Lemma eval_bot_same : forall Φ Γ b v,
  sat Φ = true ->
  Φ ; Γ ⊢ EBot b ⇓ v ->
  v = EBot b.
Proof.
  intros Φ Γ b v Hsat Heval.
  inversion Heval; subst.
  - no_con_head.
  - reflexivity.
  - rewrite Hsat in H0. discriminate.
Qed.

(** Evaluation of literals under a satisfiable path condition *)
Lemma eval_lit_same : forall Φ Γ l v,
  sat Φ = true ->
  Φ ; Γ ⊢ ELit l ⇓ v ->
  v = ELit l.
Proof.
  intros Φ Γ l v Hsat Heval.
  inversion Heval; subst.
  - reflexivity.
  - no_con_head.
  - rewrite Hsat in H0. discriminate.
Qed.

Lemma eval_nullary_con : forall f Φ Γ d, eval (Live f) Φ Γ (ECon d) (ECon d).
Proof. intros f Φ Γ d. exact (Eval_Con f Φ Γ (ECon d) d [] eq_refl). Qed.

(** Evaluation of constructors under a satisfiable path condition *)
Lemma eval_con_same : forall Φ Γ d v,
  sat Φ = true ->
  Φ ; Γ ⊢ ECon d ⇓ v ->
  v = ECon d.
Proof.
  intros Φ Γ d v Hsat Heval.
  inversion Heval; subst.
  - match goal with
    | [ Hu : unspool_app (ECon d) [] = (ECon _, _) |- _ ] =>
        simpl in Hu; injection Hu as <- <-; reflexivity
    end.
  - rewrite Hsat in H0; discriminate.
Qed.

(** A constructor spine has one value, the one Rule Con builds: every other
    application rule wants a different head. *)
Lemma eval_con_spine_same : forall Φ Γ e d args v,
  sat Φ = true ->
  unspool_app e [] = (ECon d, args) ->
  Φ ; Γ ⊢ e ⇓ v ->
  v = make_con_app d (map (delay Γ) args).
Proof.
  intros Φ Γ e d args v Hsat Hu Heval.
  destruct e; simpl in Hu; try discriminate.
  - (* ECon *)
    injection Hu as ? ?; subst.
    exact (eval_con_same Φ Γ d v Hsat Heval).
  - (* EApp *)
    inversion Heval; subst.
    + match goal with
      | [ Hu2 : unspool_app (EApp _ _) [] = (ECon _, _) |- _ ] =>
          simpl in Hu2; rewrite Hu in Hu2; injection Hu2 as <- <-; reflexivity
      end.
    + simpl in Hu; discriminate.
    + match goal with
      | [ Hc : Comp _ e1 |- _ ] =>
          pose proof (unspool_is_con_app e1 [e2] d args Hu) as Hcon;
          rewrite (comp_not_con_app _ _ Hc) in Hcon; discriminate Hcon
      end.
    + match goal with
      | [ Hp : unspool_app (EApp _ _) [] = (EPrimOp _, _) |- _ ] =>
          simpl in Hp; rewrite Hu in Hp; discriminate
      end.
    + simpl in Hu; discriminate.
    + simpl in Hu; discriminate.
    + simpl in Hu; discriminate.
    + rewrite Hsat in *; discriminate.
Qed.

Lemma eval_con_value_itself : forall f Φ Γ Γ' d args,
  eval (Live f) Φ Γ (make_con_app d (map (delay Γ') args))
                    (make_con_app d (map (delay Γ') args)).
Proof.
  intros f Φ Γ Γ' d args.
  rewrite <- (map_delay_delay Γ Γ' args) at 2.
  apply Eval_Con. apply make_con_app_unspool.
Qed.

Lemma eval_con_value_same : forall Φ Γ Γ' d args v,
  sat Φ = true ->
  Φ ; Γ ⊢ make_con_app d (map (delay Γ') args) ⇓ v ->
  v = make_con_app d (map (delay Γ') args).
Proof.
  intros Φ Γ Γ' d args v Hsat Hv.
  rewrite (eval_con_spine_same Φ Γ _ d _ v Hsat (make_con_app_unspool _ _) Hv).
  rewrite map_delay_delay. reflexivity.
Qed.

(** Evaluation of lambdas under a satisfiable path condition *)
Lemma eval_lam_same : forall Φ Γ x body v,
  sat Φ = true ->
  Φ ; Γ ⊢ ELam x body ⇓ v ->
  v = EClos Γ x body.
Proof.
  intros Φ Γ x body v Hsat Heval.
  inversion Heval; subst.
  - no_con_head.
  - reflexivity.
  - rewrite Hsat in H0; discriminate.
Qed.

(** Evaluation of coercions under a satisfiable path condition *)
Lemma eval_coercion_same : forall Φ Γ γ v,
  sat Φ = true ->
  Φ ; Γ ⊢ ECoercion γ ⇓ v ->
  v = ECoercion (subst_coerc Γ γ).
Proof.
  intros Φ Γ γ v Hsat Heval.
  inversion Heval; subst.
  - no_con_head.
  - reflexivity.
  - rewrite Hsat in H0; discriminate.
Qed.

(** Evaluation of types under a satisfiable path condition *)
Lemma eval_type_same : forall Φ Γ τ v,
  sat Φ = true ->
  Φ ; Γ ⊢ EType τ ⇓ v ->
  v = EType (subst_type Γ τ).
Proof.
  intros Φ Γ τ v Hsat Heval.
  inversion Heval; subst.
  - no_con_head.
  - rewrite Hsat in H0; discriminate.
  - reflexivity.
Qed.

(** Inversion of variable evaluation under a satisfiable path condition:
    a bound variable reduces to the reduct of its closure, an unbound
    (symbolic) one reduces to itself. *)
Lemma eval_var_inv : forall Φ Γ x v,
  sat Φ = true ->
  Φ ; Γ ⊢ EVar x ⇓ v ->
  (exists Γ' e, lookup_env Γ x = Some (Γ', e) /\ Φ ; Γ' ⊢ e ⇓ v)
  \/ (lookup_env Γ x = None /\ v = EVar x).
Proof.
  intros Φ Γ x v Hsat Heval.
  inversion Heval; subst.
  - left. exists Γ', e. split; [assumption | assumption].
  - right. split; [assumption | reflexivity].
  - no_con_head.
  - rewrite Hsat in H0; discriminate.
Qed.

(** A bound variable's evaluation still inverts to its closure alone *)
Lemma eval_var_bound_inv : forall Φ Γ x v Γ' e,
  sat Φ = true ->
  lookup_env Γ x = Some (Γ', e) ->
  Φ ; Γ ⊢ EVar x ⇓ v ->
  Φ ; Γ' ⊢ e ⇓ v.
Proof.
  intros Φ Γ x v Γ' e Hsat Hlook Heval.
  destruct (eval_var_inv Φ Γ x v Hsat Heval) as [[Γ'' [e'' [Hlook'' Hev'']]] | [Hnone Heq]].
  - rewrite Hlook in Hlook''. injection Hlook'' as ? ?; subst. assumption.
  - rewrite Hlook in Hnone. discriminate.
Qed.

(** Inversion of cast evaluation under a satisfiable path condition *)
Lemma eval_cast_inv : forall Φ Γ e γ v,
  sat Φ = true ->
  Φ ; Γ ⊢ ECast e γ ⇓ v ->
  exists e',
    Φ ; Γ ⊢ e ⇓ e' /\
    v = cast_expr e' γ.
Proof.
  intros Φ Γ e γ v Hsat Heval.
  inversion Heval; subst.
  - no_con_head.
  - exists e'. split; [assumption | reflexivity].
  - rewrite Hsat in H0; discriminate.
Qed.

(** Inversion of case evaluation under a satisfiable path condition *)
Lemma eval_case_inv : forall Φ Γ es alts v,
  sat Φ = true ->
  Φ ; Γ ⊢ ECase es alts ⇓ v ->
  exists es',
    Φ ; Γ ⊢ es ⇓ es' /\
    fold_alts Inf Φ Γ (merge Γ es') alts v.
Proof.
  intros Φ Γ es alts v Hsat Heval.
  inversion Heval; subst.
  - no_con_head.
  - exists es'. split; [assumption | assumption].
  - rewrite Hsat in H0; discriminate.
Qed.

(** Inversion of if-then-else evaluation under a satisfiable path condition *)
Lemma eval_if_inv : forall Φ Γ ec et ef v,
  sat Φ = true ->
  Φ ; Γ ⊢ EIf ec et ef ⇓ v ->
  exists ec' et' ef' pc_c,
    Φ ; Γ ⊢ ec ⇓ ec' /\
    expr_to_pc Γ ec' = Some pc_c /\
    (Φ ∧ pc_c) ; Γ ⊢ et ⇓ et' /\
    (Φ ∧ ¬ pc_c) ; Γ ⊢ ef ⇓ ef' /\
    v = EIf ec' et' ef'.
Proof.
  intros Φ Γ ec et ef v Hsat Heval.
  inversion Heval; subst.
  - no_con_head.
  - exists ec', et', ef', pc_c. split; [assumption|].
    split; [assumption|]. split; [assumption|].
    split; [assumption|reflexivity].
  - rewrite Hsat in H0; discriminate.
Qed.

(** Inversion for fold_alts on if-expressions with valid path condition *)
Lemma fold_alts_if_some_inv : forall f Φ Γ ec et ef alts r pc_c,
  expr_to_pc Γ ec = Some pc_c ->
  fold_alts f Φ Γ (EIf ec et ef) alts r ->
  exists et' ef',
    r = EIf ec et' ef' /\
    fold_alts f (Φ ∧ pc_c) Γ et alts et' /\
    fold_alts f (Φ ∧ ¬ pc_c) Γ ef alts ef'.
Proof.
  intros f Φ Γ ec et ef alts r pc_c Hpc Hfold.
  remember (EIf ec et ef) as e eqn:Heq.
  revert ec et ef Heq Hpc.
  induction Hfold; intros ec0 et0 ef0 Heq Hpc; inversion Heq; subst.
  - rewrite H in Hpc. inversion Hpc; subst.
    exists et', ef'. auto.
  - rewrite H in Hpc; discriminate.
  - discriminate.
  - simpl in H; discriminate.
Qed.

(** Inversion for fold_alts on if-expressions with invalid path condition *)
Lemma fold_alts_if_none_inv : forall f Φ Γ ec et ef alts r,
  expr_to_pc Γ ec = None ->
  fold_alts f Φ Γ (EIf ec et ef) alts r ->
  r = EBot BUndefined.
Proof.
  intros f Φ Γ ec et ef alts r Hpc Hfold.
  remember (EIf ec et ef) as e eqn:Heq.
  revert ec et ef Heq Hpc.
  induction Hfold; intros ec0 et0 ef0 Heq Hpc; inversion Heq; subst.
  - rewrite H in Hpc; discriminate.
  - reflexivity.
  - discriminate.
  - simpl in H; discriminate.
Qed.

(** Inversion for fold_alts on matching constructor patterns *)
Lemma fold_alts_con_inv : forall f Φ Γ e alts r d ea xs ep,
  decompose_con_app e = Some (d, ea) ->
  find_alt d alts = Some (xs, ep) ->
  is_if e = false ->
  is_bot e = false ->
  fold_alts f Φ Γ e alts r ->
  eval f Φ (extend_env_multi Γ xs ea Γ) ep r.
Proof.
  intros f Φ Γ e alts r d ea xs ep Hdec Halt Hnot_if Hnot_bot Hfold.
  inversion Hfold; subst.
  - simpl in Hnot_if; discriminate.
  - simpl in Hnot_if; discriminate.
  - rewrite H in Hdec. inversion Hdec; subst.
    rewrite H0 in Halt. inversion Halt; subst.
    assumption.
  - simpl in Hnot_bot; discriminate.
  - rewrite Hdec in H0. rewrite Halt in H0. discriminate.
Qed.

(** Inversion for fold_alts on non-matching fallback expressions *)
Lemma fold_alts_otherwise_same : forall f Φ Γ e alts r,
  is_if e = false ->
  (match decompose_con_app e with
   | Some (d, _) => find_alt d alts = None
   | None => True
   end) ->
  is_bot e = false ->
  fold_alts f Φ Γ e alts r ->
  r = EBot BUndefined.
Proof.
  intros f Φ Γ e alts r Hnot_if Hno_alt Hnot_bot Hfold.
  inversion Hfold; subst.
  - simpl in Hnot_if; discriminate.
  - simpl in Hnot_if; discriminate.
  - rewrite H in Hno_alt. rewrite H0 in Hno_alt. discriminate.
  - simpl in Hnot_bot; discriminate.
  - reflexivity.
Qed.

(** Alternative folding is completely deterministic given determinism of evaluation *)
Lemma fold_alts_deterministic_given_eval :
  (forall f Φ Γ e v1 v2, eval f Φ Γ e v1 -> eval f Φ Γ e v2 -> v1 = v2) ->
  forall f Φ Γ e alts r1 r2,
    fold_alts f Φ Γ e alts r1 ->
    fold_alts f Φ Γ e alts r2 ->
    r1 = r2.
Proof.
  intros Heval_det f Φ Γ e alts r1 r2 H1.
  revert r2.
  induction H1; intros r2 H2.
  - (* FoldAlts_If *)
    apply (fold_alts_if_some_inv f Φ Γ ec et ef alts r2 pc_c) in H2; [| assumption].
    destruct H2 as [et'2 [ef'2 [Heq2 [Hfold_t2 Hfold_f2]]]].
    subst.
    f_equal.
    + apply IHfold_alts1. assumption.
    + apply IHfold_alts2. assumption.
  - (* FoldAlts_IfFail *)
    apply (fold_alts_if_none_inv f Φ Γ ec et ef alts r2) in H2; [| assumption].
    subst. reflexivity.
  - (* FoldAlts_Con *)
    assert (Hnot_if : is_if e = false).
    { destruct e; simpl in H; try discriminate; reflexivity. }
    assert (Hnot_bot : is_bot e = false).
    { destruct e; simpl in H; try discriminate; reflexivity. }
    apply (fold_alts_con_inv f Φ Γ e alts r2 d ea xs ep H H0 Hnot_if Hnot_bot) in H2.
    eapply Heval_det; eassumption.
  - (* FoldAlts_Bot *)
    apply fold_alts_bot_same in H2. subst. reflexivity.
  - (* FoldAlts_Otherwise *)
    apply (fold_alts_otherwise_same f Φ Γ e alts r2
             (is_if_false_of_spine_head e H) H0 H1) in H2.
    subst. reflexivity.
Qed.

(** ------------------------------------------------------------------------- *)
(** 10.5 The Unlimited Budget against a Finite Budget (§3.2)                   *)
(** ------------------------------------------------------------------------- *)

(**
  This file carries two judgements: eval Inf, the unlimited budget, and
  eval (Fin n), a bound of n levels of rules. This section says how the two
  relate, and closes with what the bound rules out.

  The bridge, first. Every derivation at the unlimited budget is reproduced
  at some finite budget. The budget that works is the height of the
  derivation: every rule of eval needs a live fuel for itself, its premises
  run one level lower, and fold_alts spends nothing.

  The proof below carries more than the bridge asks for. It produces a
  threshold h and shows that EVERY budget at or above h reproduces the
  derivation. The weaker form, "some budget works", does not survive the
  induction. Rule App-Spine has two recursive premises, and the budgets they
  report back need not be equal. Only an upward-closed statement lets the
  rule keep the larger of the two. Rule App-Prim asks for the same thing over
  a whole list: its Forall2 must run all its arguments at one budget. The
  inner induction on the Forall2 folds the argument thresholds together with
  max as it walks the list, so no separate list-maximum lemma is needed.

  The proof is a pair of mutually recursive fixpoints on the derivation, for
  the same reason as concore_eval_closed_fix in ConCore.v: the derived mutual
  induction scheme supplies no hypothesis under the Forall2 of Rule App-Prim.

  The fuel comes in as f0 with an f0 = Inf premise instead of being left
  free, because destruct on the index brings Rule Out-Of-Fuel back as a case.
  The premise is what discharges it.
*)
Fixpoint eval_fin_of_inf_fix (f0 : fuel) (Φ : path_condition) (Γ : environment) (e v : expr)
  (Heval : eval f0 Φ Γ e v) {struct Heval} :
  f0 = Inf -> exists h, forall n, (h <= n)%nat -> eval (Fin n) Φ Γ e v
with fold_alts_fin_of_inf_fix (f0 : fuel) (Φ : path_condition) (Γ : environment) (e : expr)
  (alts : list alt) (er : expr)
  (Hfold : fold_alts f0 Φ Γ e alts er) {struct Hfold} :
  f0 = Inf -> exists h, forall n, (h <= n)%nat -> fold_alts (Fin n) Φ Γ e alts er.
Proof.
{
  destruct Heval as
    [ k Φ Γ x Γ' e e' Hlook Heval_x
    | k Φ Γ x Hnone
    | k Φ Γ l
    | k Φ Γ e d args Hunspool
    | k Φ Γ e γ e' Heval_e
    | k Φ Γ Γ' x eb ea eb' Heval_b
    | k Φ Γ ef ea ef' er Hcomp Heval_f Heval_app2
    | k Φ Γ b
    | k Φ Γ ef ea p args args' Hunspool Harity Hargs
    | k Φ Γ x e
    | k Φ Γ ef γ ea γ_a γ_r er Hdecomp Heval_pushed
    | k Φ Γ ec et ef ea er Heval_arms
    | k Φ Γ b ea
    | k Φ Γ es alts es' er Heval_es Hfold
    | k Φ Γ ec et ef ec' et' ef' pc_c Heval_c Hpc Heval_t Heval_f
    | k Φ Γ γ
    | k Φ Γ e Hunsat
    | k Φ Γ τ
    | k Φ Γ Γ' e e' Heval_t
    | Φ Γ e
    ]; intros Hk0; try (injection Hk0 as Hk0; subst k).
  - (* Eval_Var *)
    destruct (eval_fin_of_inf_fix Inf Φ Γ' e e' Heval_x eq_refl) as [h Hh].
    exists (S h). intros n Hn. destruct n as [| m]; [lia |].
    eapply Eval_Var; [exact Hlook |]. simpl. apply Hh. lia.
  - (* Eval_SymVar *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_SymVar. exact Hnone.
  - (* Eval_Lit *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_Lit.
  - (* Eval_Con *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. eapply Eval_Con. exact Hunspool.
  - (* Eval_Cast *)
    destruct (eval_fin_of_inf_fix Inf Φ Γ e e' Heval_e eq_refl) as [h Hh].
    exists (S h). intros n Hn. destruct n as [| m]; [lia |].
    apply Eval_Cast. simpl. apply Hh. lia.
  - (* Eval_AppAbs *)
    destruct (eval_fin_of_inf_fix Inf Φ (extend_env Γ' x Γ ea) eb eb' Heval_b eq_refl)
      as [h Hh].
    exists (S h). intros n Hn. destruct n as [| m]; [lia |].
    apply Eval_AppAbs. simpl. apply Hh. lia.
  - (* Eval_AppSpine *)
    destruct (eval_fin_of_inf_fix Inf Φ Γ ef ef' Heval_f eq_refl) as [h1 Hh1].
    destruct (eval_fin_of_inf_fix Inf Φ Γ (EApp ef' ea) er Heval_app2 eq_refl) as [h2 Hh2].
    exists (S (Nat.max h1 h2)). intros n Hn. destruct n as [| m]; [lia |].
    eapply Eval_AppSpine.
    + exact Hcomp.
    + simpl. apply Hh1. lia.
    + simpl. apply Hh2. lia.
  - (* Eval_Bot *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_Bot.
  - (* Eval_AppPrim *)
    assert (Hbound : exists h, forall n, (h <= n)%nat -> Forall2 (eval (Fin n) Φ Γ) args args').
    { clear Hunspool Harity.
      induction Hargs as [| a a' tl tl' Ha Htl IH].
      - exists 0%nat. intros n _. constructor.
      - destruct IH as [h2 Hh2].
        destruct (eval_fin_of_inf_fix Inf Φ Γ a a' Ha eq_refl) as [h1 Hh1].
        exists (Nat.max h1 h2). intros n Hn. constructor.
        + apply Hh1. lia.
        + apply Hh2. lia. }
    destruct Hbound as [h Hh].
    exists (S h). intros n Hn. destruct n as [| m]; [lia |].
    eapply Eval_AppPrim; [exact Hunspool | exact Harity |]. simpl. apply Hh. lia.
  - (* Eval_Lam *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_Lam.
  - (* Eval_AppCast *)
    destruct (eval_fin_of_inf_fix Inf Φ Γ
                (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er Heval_pushed eq_refl)
      as [h Hh].
    exists (S h). intros n Hn. destruct n as [| m]; [lia |].
    eapply Eval_AppCast; [exact Hdecomp |]. simpl. apply Hh. lia.
  - (* Eval_AppIf *)
    destruct (eval_fin_of_inf_fix Inf Φ Γ
                (EIf ec (EApp et ea) (EApp ef ea)) er Heval_arms eq_refl)
      as [h Hh].
    exists (S h). intros n Hn. destruct n as [| m]; [lia |].
    apply Eval_AppIf. simpl. apply Hh. lia.
  - (* Eval_AppBot *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_AppBot.
  - (* Eval_Case *)
    destruct (eval_fin_of_inf_fix Inf Φ Γ es es' Heval_es eq_refl) as [h1 Hh1].
    destruct (fold_alts_fin_of_inf_fix Inf Φ Γ (merge Γ es') alts er Hfold eq_refl) as [h2 Hh2].
    exists (S (Nat.max h1 h2)). intros n Hn. destruct n as [| m]; [lia |].
    eapply Eval_Case.
    + simpl. apply Hh1. lia.
    + simpl. apply Hh2. lia.
  - (* Eval_If *)
    destruct (eval_fin_of_inf_fix Inf Φ Γ ec ec' Heval_c eq_refl) as [h1 Hh1].
    destruct (eval_fin_of_inf_fix Inf (Φ ∧ pc_c) Γ et et' Heval_t eq_refl) as [h2 Hh2].
    destruct (eval_fin_of_inf_fix Inf (Φ ∧ ¬ pc_c) Γ ef ef' Heval_f eq_refl) as [h3 Hh3].
    exists (S (Nat.max h1 (Nat.max h2 h3))). intros n Hn. destruct n as [| m]; [lia |].
    eapply Eval_If.
    + simpl. apply Hh1. lia.
    + exact Hpc.
    + simpl. apply Hh2. lia.
    + simpl. apply Hh3. lia.
  - (* Eval_Coercion *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_Coercion.
  - (* Eval_Prune *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_Prune. exact Hunsat.
  - (* Eval_Type *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_Type.
  - (* Eval_Thunk *)
    destruct (eval_fin_of_inf_fix Inf Φ Γ' e e' Heval_t eq_refl) as [h Hh].
    exists (S h). intros n Hn. destruct n as [| m]; [lia |].
    apply Eval_Thunk. simpl. apply Hh. lia.
  - (* Eval_OutOfFuel *)
    discriminate Hk0.
}
{
  destruct Hfold as
    [ k Φ Γ ec et ef alts et' ef' pc_c Hpc Hfold_t Hfold_f
    | k Φ Γ ec et ef alts Hpc_none
    | k Φ Γ e d ea xs ep alts er Hdec Halt Heval_ep
    | k Φ Γ b alts
    | k Φ Γ e alts Hnotif Hnoalt Hnotbot
    ]; intros Hk0; subst k.
  - (* FoldAlts_If *)
    destruct (fold_alts_fin_of_inf_fix Inf (Φ ∧ pc_c) Γ et alts et' Hfold_t eq_refl)
      as [h1 Hh1].
    destruct (fold_alts_fin_of_inf_fix Inf (Φ ∧ ¬ pc_c) Γ ef alts ef' Hfold_f eq_refl)
      as [h2 Hh2].
    exists (Nat.max h1 h2). intros n Hn.
    eapply FoldAlts_If.
    + exact Hpc.
    + simpl. apply Hh1. lia.
    + simpl. apply Hh2. lia.
  - (* FoldAlts_IfFail *)
    exists 0%nat. intros n _. apply FoldAlts_IfFail. exact Hpc_none.
  - (* FoldAlts_Con *)
    destruct (eval_fin_of_inf_fix Inf Φ (extend_env_multi Γ xs ea Γ) ep er Heval_ep eq_refl)
      as [h Hh].
    exists h. intros n Hn.
    eapply FoldAlts_Con; [exact Hdec | exact Halt |]. simpl. apply Hh. lia.
  - (* FoldAlts_Bot *)
    exists 0%nat. intros n _. apply FoldAlts_Bot.
  - (* FoldAlts_Otherwise *)
    exists 0%nat. intros n _. apply FoldAlts_Otherwise; assumption.
}
Qed.

(** An unbounded derivation has a budget from which on every budget works. *)
Lemma eval_inf_has_budget : forall Φ Γ e v,
  Φ ; Γ ⊢ e ⇓ v ->
  exists h, forall n, (h <= n)%nat -> eval (Fin n) Φ Γ e v.
Proof.
  intros Φ Γ e v Heval. exact (eval_fin_of_inf_fix Inf Φ Γ e v Heval eq_refl).
Qed.

(** The same for branch folding. *)
Lemma fold_alts_inf_has_budget : forall Φ Γ e alts er,
  fold_alts Inf Φ Γ e alts er ->
  exists h, forall n, (h <= n)%nat -> fold_alts (Fin n) Φ Γ e alts er.
Proof.
  intros Φ Γ e alts er Hfold.
  exact (fold_alts_fin_of_inf_fix Inf Φ Γ e alts er Hfold eq_refl).
Qed.

(** The bridge: every unbounded derivation runs at some finite budget. *)
Corollary eval_inf_to_fin : forall Φ Γ e v,
  Φ ; Γ ⊢ e ⇓ v ->
  exists n, eval (Fin n) Φ Γ e v.
Proof.
  intros Φ Γ e v Heval.
  destruct (eval_inf_has_budget Φ Γ e v Heval) as [h Hh].
  exists h. apply Hh. lia.
Qed.

(**
  Monotonicity in the budget. The plain claim, "if a budget of n gives the
  value v then every larger budget gives v as well", is false, and the two
  lemmas below say so with witnesses.

  The reason is Rule Out-Of-Fuel. It is the only rule whose answer ignores
  the expression, and it is available at Fin 0 only. So an answer that Rule
  Out-Of-Fuel produced is usually gone one unit higher up, where the ordinary
  rules take over and give the real value instead. A larger budget gives a
  better answer, not the same answer.

  Worse: a larger budget can leave a term with NO value. A stuck term at
  Fin 0 still has the out-of-fuel answer of Rule Out-Of-Fuel; at Fin 1 it has
  nothing.

  What is true is eval_inf_has_budget above. Once a budget is large enough to
  carry a derivation that the unlimited budget also has, every larger budget
  carries the same derivation to the same value. So growing the budget is
  safe exactly for a value that the unlimited judgement gives too, and unsafe
  for a value that only Rule Out-Of-Fuel gave.
*)
Lemma bigger_budget_changes_the_value : forall Φ Γ d,
  eval (Fin 0) Φ Γ (ECon d) (EBot BOutOfFuel)
  /\ ~ eval (Fin 1) Φ Γ (ECon d) (EBot BOutOfFuel).
Proof.
  intros Φ Γ d. split.
  - apply Eval_OutOfFuel.
  - intro H. inversion H; subst. no_con_value.
Qed.

Lemma eval_fuel_not_monotone :
  ~ (forall n m Φ Γ e v,
       (n <= m)%nat -> eval (Fin n) Φ Γ e v -> eval (Fin m) Φ Γ e v).
Proof.
  intros Hmono.
  destruct (bigger_budget_changes_the_value pc_true · "C") as [H0 H1].
  apply H1. apply (Hmono 0%nat 1%nat); [lia | exact H0].
Qed.

Lemma bigger_budget_loses_the_value : forall Φ Γ x ea,
  sat Φ = true ->
  lookup_env Γ x = None ->
  eval (Fin 0) Φ Γ (EApp (EVar x) ea) (EBot BOutOfFuel)
  /\ (forall v, ~ eval (Fin 1) Φ Γ (EApp (EVar x) ea) v).
Proof.
  intros Φ Γ x ea Hsat Hnone. split.
  - apply Eval_OutOfFuel.
  - intros v H. inversion H; subst.
    + no_con_head.
    + match goal with [ Hc : Comp _ _ |- _ ] => inversion Hc; subst; congruence end.
    + match goal with [ Hu : unspool_app _ _ = _ |- _ ] => simpl in Hu; discriminate Hu end.
    + congruence.
Qed.

(**
  The bridge does not run backwards. A finite budget answers terms that the
  unlimited budget never answers, so the two judgements are not the same
  relation and no later proof may treat them as one.

  The witness is the self-application below, the same term as in
  scratch/DivergenceNeedsFuel.v. It is not stuck: the rules do apply to it,
  and each turn of the loop lands in the same shape one environment deeper.
  The unlimited budget therefore runs forever and delivers nothing, while
  every finite budget stops the loop and delivers a value.

  The environment is what makes the argument work. Each turn binds f again,
  and the new binding is not the lambda but the name f read back in the
  previous environment. So after n turns the name resolves through a chain of
  n indirections. ResolvesToSelfApp is that chain, and SelfAppState lists the
  four shapes the loop passes through.
*)
Definition self_app_var : var := "f".
Definition self_app_body : expr := EApp (EVar self_app_var) (EVar self_app_var).
Definition self_app_fun : expr := ELam self_app_var self_app_body.
Definition self_app : expr := EApp self_app_fun self_app_fun.

Lemma self_app_fun_comp : forall Γ, Comp Γ self_app_fun.
Proof. intros Γ. apply Comp_Lam. Qed.

Lemma eval_self_app_fun : forall Φ Γ v,
  sat Φ = true -> Φ ; Γ ⊢ self_app_fun ⇓ v -> v = EClos Γ self_app_var self_app_body.
Proof.
  intros Φ Γ v Hsat H. inversion H; subst; [no_con_head | reflexivity | congruence].
Qed.

(** The chain of indirections that still ends at the loop lambda. *)
Inductive ResolvesToSelfApp : environment -> Prop :=
  | RSA_Lam : forall Γ Γ0,
      lookup_env Γ self_app_var = Some (Γ0, self_app_fun) ->
      ResolvesToSelfApp Γ
  | RSA_Indirect : forall Γ Γ0,
      lookup_env Γ self_app_var = Some (Γ0, EVar self_app_var) ->
      ResolvesToSelfApp Γ0 ->
      ResolvesToSelfApp Γ.

Lemma self_app_extend_fun : forall Γ0 Γ,
  ResolvesToSelfApp (extend_env Γ0 self_app_var Γ self_app_fun).
Proof.
  intros Γ0 Γ. eapply RSA_Lam. unfold extend_env. simpl.
  destruct (string_dec self_app_var self_app_var); [reflexivity | contradiction].
Qed.

Lemma self_app_extend_var : forall Γ0 Γ,
  ResolvesToSelfApp Γ ->
  ResolvesToSelfApp (extend_env Γ0 self_app_var Γ (EVar self_app_var)).
Proof.
  intros Γ0 Γ H. eapply RSA_Indirect; [| exact H]. unfold extend_env. simpl.
  destruct (string_dec self_app_var self_app_var); [reflexivity | contradiction].
Qed.

Lemma self_app_var_comp : forall Γ,
  ResolvesToSelfApp Γ -> Comp Γ (EVar self_app_var).
Proof.
  intros Γ HR. apply Comp_Var. destruct HR; congruence.
Qed.

Lemma eval_self_app_var : forall Φ Γ,
  ResolvesToSelfApp Γ ->
  sat Φ = true ->
  forall v, Φ ; Γ ⊢ EVar self_app_var ⇓ v ->
  exists Γ0, v = EClos Γ0 self_app_var self_app_body.
Proof.
  intros Φ Γ HR Hsat. induction HR.
  - intros v Hev. inversion Hev; subst.
    + rewrite H in H2. injection H2 as ? ?; subst.
      eexists. eapply eval_self_app_fun; [exact Hsat | eassumption].
    + congruence.
    + no_con_head.
    + congruence.
  - intros v Hev. inversion Hev; subst.
    + rewrite H in H2. injection H2 as ? ?; subst. apply IHHR. eassumption.
    + congruence.
    + no_con_head.
    + congruence.
Qed.

(** The four shapes the loop passes through. *)
Inductive SelfAppState : environment -> expr -> Prop :=
  | SA_Self : forall Γ,
      SelfAppState Γ self_app
  | SA_ClosFun : forall Γ Γ0,
      SelfAppState Γ (EApp (EClos Γ0 self_app_var self_app_body) self_app_fun)
  | SA_Var : forall Γ,
      ResolvesToSelfApp Γ ->
      SelfAppState Γ self_app_body
  | SA_ClosVar : forall Γ Γ0,
      ResolvesToSelfApp Γ ->
      SelfAppState Γ (EApp (EClos Γ0 self_app_var self_app_body) (EVar self_app_var)).

(** Every step out of a loop shape lands in a loop shape, so an unbounded
    derivation can never bottom out. The induction is on the derivation, not
    on the term. It keeps the index, so that Rule Out-Of-Fuel stays out. *)
Lemma self_app_has_no_value : forall Φ Γ e v,
  Φ ; Γ ⊢ e ⇓ v -> sat Φ = true -> SelfAppState Γ e -> False.
Proof.
  intros Φ Γ e v H.
  remember Inf as kf eqn:Hkf in H.
  induction H; try discriminate Hkf; try (injection Hkf as Hkf); subst;
    intros Hsat HL;
    try (inversion HL; unfold self_app, self_app_body, self_app_fun in *; discriminate).
  - (* Rule Con: no loop shape has a constructor at the head of its spine *)
    inversion HL; subst;
      match goal with
      | [ Hu : unspool_app _ _ = (ECon _, _) |- _ ] => discriminate Hu
      end.
  - (* Rule App-Abs *)
    inversion HL; subst.
    + apply IHeval; [reflexivity | exact Hsat | apply SA_Var; apply self_app_extend_fun].
    + apply IHeval; [reflexivity | exact Hsat |].
      apply SA_Var. apply self_app_extend_var. assumption.
  - (* Rule App-Spine *)
    inversion HL; subst.
    + assert (Hef : ef' = EClos Γ self_app_var self_app_body)
        by (apply (eval_self_app_fun Φ Γ ef' Hsat); assumption).
      subst ef'. apply IHeval2; [reflexivity | exact Hsat | apply SA_ClosFun].
    + match goal with [ Hc : Comp _ (EClos _ _ _) |- _ ] => inversion Hc end.
    + match goal with
      | [ HR : ResolvesToSelfApp Γ, He : eval _ Φ Γ (EVar self_app_var) ef' |- _ ] =>
          destruct (eval_self_app_var Φ Γ HR Hsat ef' He) as [Γ0 Hef]; subst ef';
          apply IHeval2; [reflexivity | exact Hsat | apply SA_ClosVar; exact HR]
      end.
    + match goal with [ Hc : Comp _ (EClos _ _ _) |- _ ] => inversion Hc end.
  - (* Rule App-Prim *)
    inversion HL; subst; unfold self_app, self_app_body, self_app_fun in H; simpl in H;
      injection H as ? ?; discriminate.
  - (* Rule Prune *)
    congruence.
Qed.

Lemma self_app_diverges : forall Φ Γ v,
  sat Φ = true -> ~ (Φ ; Γ ⊢ self_app ⇓ v).
Proof.
  intros Φ Γ v Hsat H.
  eapply self_app_has_no_value; [exact H | exact Hsat | apply SA_Self].
Qed.

(** Reading f at a finite budget either runs out of budget or delivers the
    loop closure, whatever the length of the chain. *)
Lemma self_app_var_value_bounded : forall Γ,
  ResolvesToSelfApp Γ ->
  forall k Ψ, exists v,
    eval (Fin k) Ψ Γ (EVar self_app_var) v
    /\ (v = EBot BOutOfFuel \/ exists Γ0, v = EClos Γ0 self_app_var self_app_body).
Proof.
  intros Γ HR. induction HR as [Γa Γb Hl | Γa Γb Hl HR IH];
    intros k Ψ; destruct k as [| k].
  - exists (EBot BOutOfFuel). split; [apply Eval_OutOfFuel | left; reflexivity].
  - destruct k as [| k].
    + exists (EBot BOutOfFuel).
      split; [eapply Eval_Var; [exact Hl | apply Eval_OutOfFuel] | left; reflexivity].
    + exists (EClos Γb self_app_var self_app_body). split.
      * eapply Eval_Var; [exact Hl |]. simpl. unfold self_app_fun. apply Eval_Lam.
      * right. exists Γb. reflexivity.
  - exists (EBot BOutOfFuel). split; [apply Eval_OutOfFuel | left; reflexivity].
  - destruct (IH k Ψ) as [v [Hv Hshape]].
    exists v. split; [eapply Eval_Var; [exact Hl | exact Hv] | exact Hshape].
Qed.

(** Every loop shape has a value at every finite budget. The loop never
    blocks, it only stops, so a budget always delivers a derivation where the
    unlimited judgement delivers none. *)
Lemma self_app_state_has_value_at_every_budget : forall k Ψ Γ e,
  SelfAppState Γ e -> exists v, eval (Fin k) Ψ Γ e v.
Proof.
  induction k as [| k IH]; intros Ψ Γ e HL.
  - exists (EBot BOutOfFuel). apply Eval_OutOfFuel.
  - inversion HL; subst.
    + destruct k as [| k].
      * exists (EBot BOutOfFuel). unfold self_app.
        eapply Eval_AppSpine with (ef' := EBot BOutOfFuel);
          [apply self_app_fun_comp | apply Eval_OutOfFuel
          | apply Eval_OutOfFuel].
      * destruct (IH Ψ Γ (EApp (EClos Γ self_app_var self_app_body) self_app_fun)
                   (SA_ClosFun Γ Γ)) as [v Hv].
        exists v. unfold self_app.
        eapply Eval_AppSpine with (ef' := EClos Γ self_app_var self_app_body).
        -- apply self_app_fun_comp.
        -- simpl. unfold self_app_fun. apply Eval_Lam.
        -- simpl. exact Hv.
    + destruct (IH Ψ (extend_env Γ1 self_app_var Γ self_app_fun) self_app_body
                 (SA_Var _ (self_app_extend_fun Γ1 Γ))) as [v Hv].
      exists v. apply Eval_AppAbs. simpl. exact Hv.
    + destruct (self_app_var_value_bounded Γ H k Ψ) as [vf [Hvf [Hbot | [Γ0 Hclos]]]].
      * subst vf. exists (EBot BOutOfFuel). unfold self_app_body.
        eapply Eval_AppSpine with (ef' := EBot BOutOfFuel).
        -- apply self_app_var_comp. exact H.
        -- simpl. exact Hvf.
        -- destruct k as [| k]; [apply Eval_OutOfFuel | apply Eval_AppBot].
      * subst vf.
        destruct (IH Ψ Γ (EApp (EClos Γ0 self_app_var self_app_body) (EVar self_app_var))
                   (SA_ClosVar Γ Γ0 H)) as [v Hv].
        exists v. unfold self_app_body.
        eapply Eval_AppSpine with (ef' := EClos Γ0 self_app_var self_app_body).
        -- apply self_app_var_comp. exact H.
        -- simpl. exact Hvf.
        -- simpl. exact Hv.
    + destruct (IH Ψ (extend_env Γ1 self_app_var Γ (EVar self_app_var)) self_app_body
                 (SA_Var _ (self_app_extend_var Γ1 Γ H))) as [v Hv].
      exists v. apply Eval_AppAbs. simpl. exact Hv.
Qed.

Corollary self_app_has_value_at_every_budget : forall k Ψ Γ,
  exists v, eval (Fin k) Ψ Γ self_app v.
Proof.
  intros k Ψ Γ.
  apply (self_app_state_has_value_at_every_budget k Ψ Γ self_app (SA_Self Γ)).
Qed.

(** The converse of the bridge is false: the loop has a value at every finite
    budget and no value at all at the unlimited budget. *)
Lemma bounded_evaluation_is_not_unbounded : forall Φ Γ,
  sat Φ = true ->
  eval (Fin 0) Φ Γ self_app (EBot BOutOfFuel)
  /\ (forall n, exists v, eval (Fin n) Φ Γ self_app v)
  /\ (forall v, ~ (Φ ; Γ ⊢ self_app ⇓ v)).
Proof.
  intros Φ Γ Hsat. split; [| split].
  - apply Eval_OutOfFuel.
  - intros n. apply self_app_has_value_at_every_budget.
  - intros v. apply self_app_diverges. exact Hsat.
Qed.

(** So the two judgements are different relations. Nobody may assume they
    coincide. *)
Lemma eval_fin_does_not_imply_eval_inf :
  ~ (forall n Φ Γ e v, eval (Fin n) Φ Γ e v -> eval Inf Φ Γ e v).
Proof.
  intros Hconv.
  destruct (bounded_evaluation_is_not_unbounded pc_true · sat_pc_true) as [Hfin [_ Hinf]].
  apply (Hinf (EBot BOutOfFuel)). apply (Hconv 0%nat). exact Hfin.
Qed.

(**
  What the bound rules out. Fin 0 is Spent, where only Rule Out-Of-Fuel
  fires, and a rule at Fin (S n) has its premises at Fin n. So a derivation
  at Fin n nests at most n rules of eval. The chain of variables below makes
  that visible: reading the chain costs one level per link, and a bound one
  level short of the chain has no derivation of its end at all.
*)
Lemma fin_succ_is_live : forall n, Fin (S n) = Live (Remaining n).
Proof. reflexivity. Qed.

Lemma dec_remaining : forall n, dec (Remaining n) = Fin n.
Proof. reflexivity. Qed.

Lemma eval_fin_zero_inv : forall Φ Γ e v,
  eval (Fin 0) Φ Γ e v -> v = EBot BOutOfFuel.
Proof. intros Φ Γ e v H. inversion H. reflexivity. Qed.

Lemma eval_fin_zero_iff : forall Φ Γ e v,
  eval (Fin 0) Φ Γ e v <-> v = EBot BOutOfFuel.
Proof.
  intros Φ Γ e v. split; [apply eval_fin_zero_inv |].
  intros Hv. subst v. apply Eval_OutOfFuel.
Qed.

Definition chain_var : var := "x".
Definition chain_end : expr := ELam chain_var (EVar chain_var).
Definition chain_value : expr := EClos EmptyEnv chain_var (EVar chain_var).

Fixpoint var_chain (k : nat) : environment :=
  match k with
  | O => extend_env EmptyEnv chain_var EmptyEnv chain_end
  | S k => extend_env EmptyEnv chain_var (var_chain k) (EVar chain_var)
  end.

Lemma var_chain_lookup_end :
  lookup_env (var_chain 0) chain_var = Some (EmptyEnv, chain_end).
Proof. reflexivity. Qed.

Lemma var_chain_lookup_link : forall k,
  lookup_env (var_chain (S k)) chain_var = Some (var_chain k, EVar chain_var).
Proof. reflexivity. Qed.

Lemma var_chain_unbounded : forall k Φ,
  Φ ; var_chain k ⊢ EVar chain_var ⇓ chain_value.
Proof.
  induction k as [| k IH]; intros Φ.
  - eapply Eval_Var; [exact var_chain_lookup_end | apply Eval_Lam].
  - eapply Eval_Var; [exact (var_chain_lookup_link k) | apply IH].
Qed.

Lemma var_chain_within_bound : forall k n Φ,
  (k + 2 <= n)%nat -> eval (Fin n) Φ (var_chain k) (EVar chain_var) chain_value.
Proof.
  induction k as [| k IH]; intros n Φ Hn; destruct n as [| m]; try lia.
  - destruct m as [| m]; [lia |].
    eapply Eval_Var; [exact var_chain_lookup_end | apply Eval_Lam].
  - eapply Eval_Var; [exact (var_chain_lookup_link k) |].
    rewrite dec_remaining. apply IH. lia.
Qed.

Lemma var_chain_needs_bound : forall k n Φ,
  eval (Fin n) Φ (var_chain k) (EVar chain_var) chain_value -> (k + 2 <= n)%nat.
Proof.
  induction k as [| k IH]; intros n Φ H; destruct n as [| m];
    try (apply eval_fin_zero_inv in H; discriminate H).
  - inversion H; subst; [| no_con_head].
    match goal with
    | [ Hl : lookup_env _ _ = Some _, Hv : eval _ _ _ _ _ |- _ ] =>
        rewrite var_chain_lookup_end in Hl; injection Hl as <- <-;
        rewrite dec_remaining in Hv
    end.
    destruct m as [| m]; [| lia].
    match goal with
    | [ Hv : eval (Fin 0) _ _ _ _ |- _ ] => apply eval_fin_zero_inv in Hv; discriminate Hv
    end.
  - inversion H; subst; [| no_con_head].
    match goal with
    | [ Hl : lookup_env _ _ = Some _, Hv : eval _ _ _ _ _ |- _ ] =>
        rewrite var_chain_lookup_link in Hl; injection Hl as <- <-;
        rewrite dec_remaining in Hv; apply IH in Hv
    end.
    lia.
Qed.

(** Lowering the bound loses derivations: the index is not antitone. *)
Corollary lowering_the_bound_loses_derivations :
  ~ (forall n Φ Γ e v, eval (Fin (S n)) Φ Γ e v -> eval (Fin n) Φ Γ e v).
Proof.
  intros Hanti.
  pose proof (var_chain_within_bound 0 2 pc_true ltac:(lia)) as H2.
  apply Hanti in H2. apply var_chain_needs_bound in H2. lia.
Qed.

(** No finite bound carries every unbounded derivation. *)
Corollary eval_inf_is_not_within_any_bound : forall n,
  ~ (forall Φ Γ e v, Φ ; Γ ⊢ e ⇓ v -> eval (Fin n) Φ Γ e v).
Proof.
  intros n Hwithin.
  pose proof (Hwithin pc_true (var_chain n) (EVar chain_var) chain_value
                (var_chain_unbounded n pc_true)) as Hn.
  apply var_chain_needs_bound in Hn. lia.
Qed.



End SymCore.
