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
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** ========================================================================= *)
(** 1. Variables and Data Constructors (§3.1)                                  *)
(** ========================================================================= *)

Definition var : Set := string.
Definition dcon : Set := string.

(** ========================================================================= *)
(** 2. Literals and Primitive Operations (§3.1)                                *)
(** ========================================================================= *)

(** Literals mirror those found in SMT solvers; left abstract in §3.1 *)
Parameter lit : Set.
Parameter lit_eq_dec : forall (l1 l2 : lit), {l1 = l2} + {l1 <> l2}.

(** Primitive operations mirror SMT solver primitives; left abstract in §3.1 *)
Parameter primop : Set.
Parameter primop_eq_dec : forall (p1 p2 : primop), {p1 = p2} + {p1 <> p2}.

(** ========================================================================= *)
(** 3. Types and Coercions in System FC / SymCore (§3.1)                      *)
(** ========================================================================= *)

(** Type Constructors (e.g. Int, Bool, SMT.BitVec); left abstract *)
Parameter tycon : Set.
Parameter tycon_eq_dec : forall (tc1 tc2 : tycon), {tc1 = tc2} + {tc1 <> tc2}.

(** System FC Types with arrow types for higher-order coercions *)
Inductive type_fc : Set :=
  | TyVar   : var -> type_fc
  | TyCon   : tycon -> type_fc
  | TyArrow : type_fc -> type_fc -> type_fc
  | TyApp   : type_fc -> type_fc -> type_fc.

Fixpoint type_fc_eq_dec (t1 t2 : type_fc) : {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
  - apply string_dec.
  - apply tycon_eq_dec.
Defined.

(** Roles in System FC / SymCore (§3.1, [Breitner et al. 2016]) *)
Inductive role : Set :=
  | RoleNominal             (** N: exact type equality *)
  | RoleRepresentational    (** R: same runtime representation *)
  | RolePhantom.            (** P: phantom types *)

Definition role_eq_dec : forall (r1 r2 : role), {r1 = r2} + {r1 <> r2}.
Proof.
  decide equality.
Defined.

(** Coercions witnessing type equality with endpoints (Section 3.1: γ : τ1 ~ρ τ2) *)
Record coercion : Set := MkCoercion {
  coerc_src  : type_fc;     (** τ1 *)
  coerc_dst  : type_fc;     (** τ2 *)
  coerc_role : role         (** ρ *)
}.

Definition coercion_eq_dec : forall (c1 c2 : coercion), {c1 = c2} + {c1 <> c2}.
Proof.
  intros [s1 d1 r1] [s2 d2 r2].
  destruct (type_fc_eq_dec s1 s2); [subst | right; intros H; inversion H; contradiction].
  destruct (type_fc_eq_dec d1 d2); [subst | right; intros H; inversion H; contradiction].
  destruct (role_eq_dec r1 r2); [subst | right; intros H; inversion H; contradiction].
  left; reflexivity.
Defined.

(** Symmetry of a coercion: sym γ witnesses τ2 ~ρ τ1 (Fig. 3, Rule App-Cast) *)
Definition sym_coerc (c : coercion) : coercion :=
  MkCoercion (coerc_dst c) (coerc_src c) (coerc_role c).

(** Decomposition of arrow coercion: (γa -> γr) = γ (Fig. 3, Rule App-Cast) *)
Definition decomp_coerc_arrow (c : coercion) : option (coercion * coercion) :=
  match coerc_src c, coerc_dst c with
  | TyArrow s1 s2, TyArrow d1 d2 =>
      Some (MkCoercion s1 d1 (coerc_role c),
            MkCoercion s2 d2 (coerc_role c))
  | _, _ => None
  end.

(** ========================================================================= *)
(** 4. Path Condition Φ (Figure 2)                                            *)
(** ========================================================================= *)

(**
  Path Condition (Fig. 2):
    Φ ::= x | l | ⊗ Φ⃗
  with boolean constants and connectives for branching (Φ ∧ ec, Φ ∧ ¬ec).
*)
Inductive path_condition : Set :=
  | PCTrue  : path_condition
  | PCFalse : path_condition
  | PCVar   : var -> path_condition
  | PCLit   : lit -> path_condition
  | PCPrim  : primop -> list path_condition -> path_condition
  | PCAnd   : path_condition -> path_condition -> path_condition
  | PCNot   : path_condition -> path_condition.

(** SMT satisfiability oracle SAT(Φ) (Fig. 3, Rule Prune) *)
Parameter sat : path_condition -> bool.

(** ========================================================================= *)
(** 5. Expressions, Bottom, Closures, and Environment (Figures 1 & 2)          *)
(** ========================================================================= *)

(**
  Expressions (Fig. 1) and Environment Γ ::= {x ↦ (Γ, e)} (Fig. 2).
  Extended with runtime closures (Γ, λx. e) produced by Rule Lam and applied
  in Rule App-Abs.
*)

Inductive bottom : Type :=
  | BRaise : expr -> bottom      (** raise e: error throw *)
  | BUnreachable : bottom        (** ∅: unreachable *)
  | BUndefined : bottom          (** ?: undefined behavior *)

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

with alt : Type :=
  | Alt : dcon -> list var -> expr -> alt         (** D x⃗ → e: pattern *)

with closure : Type :=
  | MkClosure : environment -> expr -> closure    (** (Γ, e) from Fig. 2 *)

with environment : Type :=
  | EmptyEnv : environment                        (** ∅: empty substitution map *)
  | ExtendEnv : var -> closure -> environment -> environment.
                                                  (** Γ{x ↦ (Γ', e)}: substitution map *)

(** Environment lookup: (Γ', e) = Γ(x) (Fig. 3, Rule Var) *)
Fixpoint lookup_env (g : environment) (x : var) : option (environment * expr) :=
  match g with
  | EmptyEnv => None
  | ExtendEnv y (MkClosure g' e) rest =>
      if string_dec x y then Some (g', e) else lookup_env rest x
  end.

(** Predicate checking whether a variable is in the environment Γ *)
Definition in_env (g : environment) (x : var) : bool :=
  match lookup_env g x with
  | Some _ => true
  | None => false
  end.

(** Single-variable environment extension: Γ{x ↦ (Γ', e)} (Fig. 3, Rule App-Abs) *)
Definition extend_env (g : environment) (x : var) (g' : environment) (e : expr) : environment :=
  ExtendEnv x (MkClosure g' e) g.

(** Multi-variable environment extension for pattern matching: Γ{x⃗ ↦ (Γ', e⃗)} (Fig. 3, fold-alts) *)
Fixpoint extend_env_multi (g : environment) (xs : list var) (args : list expr) (g_arg : environment) : environment :=
  match xs, args with
  | x :: xs', a :: args' =>
      extend_env (extend_env_multi g xs' args' g_arg) x g_arg a
  | _, _ => g
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

(** Theory-specific primitive reduction: reduce-prim(⊗ e⃗) (Fig. 3, Rule App-Prim) *)
Parameter reduce_prim : primop -> list expr -> expr.

(** Cast simplification: cast(e, γ) (Fig. 3, Rule Cast) *)
Parameter cast_expr : expr -> coercion -> expr.

(** ========================================================================= *)
(** 7. Solvable and WHNF Definitions in Prop (§3.2)                            *)
(** ========================================================================= *)

(** Helper: checks if the head of an expression is a primitive operation *)
Fixpoint is_op_app (e : expr) : bool :=
  match e with
  | EPrimOp _ => true
  | EApp f _ => is_op_app f
  | _ => false
  end.

(**
  Solvable g e in Prop (§3.2):
    - Literals: e ≡ l
    - Symbolic variables: e ≡ x ∧ x ∉ Γ
    - Primitive operations: e ≡ ⊗ e⃗ where all arguments are solvable
*)
Inductive Solvable (g : environment) : expr -> Prop :=
  | Solvable_Lit : forall l,
      Solvable g (ELit l)
  | Solvable_Var : forall x,
      lookup_env g x = None ->
      Solvable g (EVar x)
  | Solvable_PrimOp : forall p,
      Solvable g (EPrimOp p)
  | Solvable_AppPrim : forall f a,
      is_op_app (EApp f a) = true ->
      Solvable g f ->
      Solvable g a ->
      Solvable g (EApp f a).

(**
  Whnf g e in Prop (§3.2):
    - Solvable(Γ, e)
    - e ≡ D
    - e ≡ b
    - e ≡ λx. e (or closure (Γ', λx. e))
    - e ≡ eb ⊲ γ ∧ Whnf(Γ, eb)
    - e ≡ if ec then et else ef ∧ Solvable(Γ, ec) ∧ Whnf(Γ, et) ∧ Whnf(Γ, ef)
*)
Inductive Whnf (g : environment) : expr -> Prop :=
  | Whnf_Solvable : forall e,
      Solvable g e ->
      Whnf g e
  | Whnf_Con : forall d,
      Whnf g (ECon d)
  | Whnf_Bot : forall b,
      Whnf g (EBot b)
  | Whnf_Lam : forall x body,
      Whnf g (ELam x body)
  | Whnf_Clos : forall g_def x body,
      Whnf g (EClos g_def x body)
  | Whnf_Coercion : forall gamma,
      Whnf g (ECoercion gamma)
  | Whnf_Type : forall tau,
      Whnf g (EType tau)
  | Whnf_Cast : forall eb gamma,
      Whnf g eb ->
      Whnf g (ECast eb gamma)
  | Whnf_If : forall ec et ef,
      Solvable g ec ->
      Whnf g et ->
      Whnf g ef ->
      Whnf g (EIf ec et ef).

(** ========================================================================= *)
(** 8. Decision Functions (Fixpoints) for Solvable and WHNF                    *)
(** ========================================================================= *)

(** Solvable is decidable *)
Fixpoint solvable_dec (g : environment) (e : expr) : {Solvable g e} + {~ Solvable g e}.
Proof.
  destruct e.
  - destruct (lookup_env g v) eqn:Heq.
    + right. intros H. inversion H. rewrite Heq in H1. discriminate.
    + left. apply Solvable_Var. assumption.
  - left. apply Solvable_Lit.
  - left. apply Solvable_PrimOp.
  - right. intros H. inversion H.
  - destruct (is_op_app (EApp e1 e2)) eqn:Hop.
    + destruct (solvable_dec g e1) as [S1 | N1].
      * destruct (solvable_dec g e2) as [S2 | N2].
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
Defined.

(** Helper inversion lemmas on Solvable *)
Lemma solvable_not_cast : forall g e c, ~ Solvable g (ECast e c).
Proof. intros g e c H. inversion H. Qed.

Lemma solvable_not_if : forall g c t f, ~ Solvable g (EIf c t f).
Proof. intros g c t f H. inversion H. Qed.

(** WHNF is decidable *)
Fixpoint whnf_dec (g : environment) (e : expr) : {Whnf g e} + {~ Whnf g e}.
Proof.
  destruct (solvable_dec g e) as [S | NS].
  - left. apply Whnf_Solvable. assumption.
  - destruct e.
    + right. intros H. inversion H; subst; [contradiction | inversion H0..].
    + (* ELit *) exfalso. apply NS. apply Solvable_Lit.
    + (* EPrimOp *) exfalso. apply NS. apply Solvable_PrimOp.
    + left. apply Whnf_Con.
    + right. intros H. inversion H; subst; [contradiction | inversion H0..].
    + left. apply Whnf_Lam.
    + left. apply Whnf_Clos.
    + right. intros H. inversion H; subst; [contradiction | inversion H0..].
    + destruct (whnf_dec g e) as [W | NW].
      * left. apply Whnf_Cast. assumption.
      * right. intros H. inversion H; subst.
        -- apply (solvable_not_cast g e c); auto.
        -- apply NW; auto.
    + left. apply Whnf_Coercion.
    + left. apply Whnf_Type.
    + destruct (solvable_dec g e1) as [S1 | NS1].
      * destruct (whnf_dec g e2) as [W2 | NW2].
        -- destruct (whnf_dec g e3) as [W3 | NW3].
           ++ left. apply Whnf_If; auto.
           ++ right. intros H. inversion H; subst.
              ** apply (solvable_not_if g e1 e2 e3); auto.
              ** apply NW3; auto.
        -- right. intros H. inversion H; subst.
           ++ apply (solvable_not_if g e1 e2 e3); auto.
           ++ apply NW2; auto.
      * right. intros H. inversion H; subst.
        -- apply (solvable_not_if g e1 e2 e3); auto.
        -- apply NS1; auto.
    + left. apply Whnf_Bot.
Defined.
