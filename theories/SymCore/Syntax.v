From Stdlib Require Import Strings.String Lists.List ZArith.ZArith Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Section SymCore.

(** ========================================================================= *)
(** Variables and Data Constructors (§3.1)                                    *)
(** ========================================================================= *)

Definition var : Set := string.
Definition dcon : Set := string.

(** ========================================================================= *)
(** Literals and Primitive Operations (§3.1)                                  *)
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
lit_true : lit;

(**
  The data constructors that Boolean control flow scrutinises. Rule Case turns
  a scrutinee that is an SMT boolean formula into a match on these two, so a
  program that compares symbolic values (for example inside Map.insert) reaches
  a real branch. A concrete formula picks the True or False constructor; a
  symbolic one folds both alternatives under the formula and its negation.
*)
dcon_true : dcon;
dcon_false : dcon;

(**
  The SMT theory's reading of negation and if-then-else. These describe the
  theory, not the solver, so they live here beside prim_value rather than in a
  law class. They are what lets Rule Case read the truth value of a merged
  boolean and select the arm the model takes.
*)
prim_value_not : forall l, prim_value op_not (l :: nil) = lit_true <-> l <> lit_true;
prim_value_ite : forall c t f,
  prim_value op_ite (c :: t :: f :: nil) = if lit_eq_dec c lit_true then t else f
}.

Context {sorts : SymCoreSorts}.

(** ========================================================================= *)
(** Types and Coercions in System FC / SymCore (§3.1)                         *)
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
(** Expressions, Bottom, Closures, and Environment (Figures 1 & 2)            *)
(** ========================================================================= *)

(**
  Expressions (Fig. 1) and Environment Γ ::= {x ↦ (Γ, e)} (Fig. 2).
  Extended with runtime thunks (Γ, e). Rule Con produces them for the fields
  of a constructor value and Rule Thunk forces them. Rule Lam produces the
  thunk (Γ, λx. e), which is the closure of a lambda, and Rule App-Abs
  applies it.
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

Fixpoint mentions_out_of_fuel (e : expr) {struct e} : bool :=
  match e with
  | EApp f a => orb (mentions_out_of_fuel f) (mentions_out_of_fuel a)
  | ELam _ body => mentions_out_of_fuel body
  | ECase es alts =>
      orb (mentions_out_of_fuel es)
        ((fix alts_mention (l : list alt) {struct l} : bool :=
            match l with
            | nil => false
            | Alt _ _ ep :: rest => orb (mentions_out_of_fuel ep) (alts_mention rest)
            end) alts)
  | ECast body _ => mentions_out_of_fuel body
  | EIf ec et ef =>
      orb (mentions_out_of_fuel ec)
        (orb (mentions_out_of_fuel et) (mentions_out_of_fuel ef))
  | EBot b => bottom_mentions_out_of_fuel b
  | EThunk Γ body => orb (env_mentions_out_of_fuel Γ) (mentions_out_of_fuel body)
  | _ => false
  end
with bottom_mentions_out_of_fuel (b : bottom) {struct b} : bool :=
  match b with
  | BRaise e => mentions_out_of_fuel e
  | BOutOfFuel => true
  | _ => false
  end
with env_mentions_out_of_fuel (Γ : environment) {struct Γ} : bool :=
  match Γ with
  | EmptyEnv => false
  | ExtendEnv _ (MkClosure Γ' e) rest =>
      orb (orb (env_mentions_out_of_fuel Γ') (mentions_out_of_fuel e))
        (env_mentions_out_of_fuel rest)
  end.

(** Environment lookup: (Γ', e) = Γ(x) (Fig. 3, Rule Var) *)
Fixpoint lookup_env (Γ : environment) (x : var) : option (environment * expr) :=
  match Γ with
  | · => None
  | ExtendEnv y (MkClosure Γ' e) rest =>
      if string_dec x y then Some (Γ', e) else lookup_env rest x
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
(** Path Condition Φ (Figure 2)                                               *)
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

(** A model assigns every symbolic variable a literal value. *)
Definition valuation : Type := var -> lit.

(** The fixed set of symbolic variables of a run. *)
Definition symvars : Type := var -> bool.

(** The SMT value of a formula under a model. Rule Case reads the truth value
    of a boolean scrutinee with it. *)
Fixpoint pc_value (σ : valuation) (pc : path_condition) : lit :=
  match pc with
  | PCVar x => σ x
  | PCLit l => l
  | PCPrim p args => prim_value p (map (pc_value σ) args)
  end.

(** A formula mentions a variable. *)
Fixpoint pc_has_var (pc : path_condition) : bool :=
  match pc with
  | PCVar _ => true
  | PCLit _ => false
  | PCPrim _ args => existsb pc_has_var args
  end.

(** Every primitive application in a formula has exactly its arity. *)
Fixpoint pc_arities_ok (pc : path_condition) : bool :=
  match pc with
  | PCVar _ | PCLit _ => true
  | PCPrim p args => andb (Nat.eqb (length args) (primop_arity p)) (forallb pc_arities_ok args)
  end.

(** The value of a formula with no variable, read against any model at all. *)
Definition pc_closed_value (pc : path_condition) : lit := pc_value (fun _ => lit_true) pc.

(** The constructor a literal boolean scrutinises to. *)
Definition truth_constructor (l : lit) : dcon :=
  if lit_eq_dec l lit_true then dcon_true else dcon_false.

(** A formula with no variable has the same value under every model. *)
Fixpoint pc_value_no_var (σ1 σ2 : valuation) (pc : path_condition) {struct pc} :
  pc_has_var pc = false -> pc_value σ1 pc = pc_value σ2 pc.
Proof.
  destruct pc as [x | l | p args]; intros H; simpl in *.
  - discriminate.
  - reflexivity.
  - f_equal. induction args as [| a args IH]; simpl in *; [reflexivity |].
    apply orb_false_elim in H as [Ha Hargs].
    rewrite (pc_value_no_var σ1 σ2 a Ha), (IH Hargs). reflexivity.
Qed.

(** So the value of a variable-free formula is its closed value. *)
Lemma pc_value_closed : forall σ pc,
  pc_has_var pc = false -> pc_value σ pc = pc_closed_value pc.
Proof. intros σ pc H. exact (pc_value_no_var σ (fun _ => lit_true) pc H). Qed.

End SymCore.

Notation "Φ1 '∧' Φ2" := (pc_and Φ1 Φ2) (at level 40, left associativity).
Notation "'¬' Φ" := (pc_not Φ) (at level 35, right associativity).
