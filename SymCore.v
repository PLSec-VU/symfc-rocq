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
(** 7. Solvable and WHNF Predicates (§3.2)                                    *)
(** ========================================================================= *)

(** Helper: checks if the head of an expression is a primitive operation *)
Fixpoint is_op_app (e : expr) : bool :=
  match e with
  | EPrimOp _ => true
  | EApp f _ => is_op_app f
  | _ => false
  end.

(**
  solvable(Γ, e) predicate (§3.2):
    solvable(Γ, e) =
      True   if e ≡ l
      True   if e ≡ x ∧ x ∉ Γ
      True   if e ≡ ⊗ e⃗ ∧ ∀ ea ∈ e⃗, solvable(Γ, ea)
      False  otherwise
*)
Fixpoint solvable (g : environment) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar x => negb (in_env g x)
  | EPrimOp _ => true
  | EApp f a =>
      if is_op_app e then
        solvable g f && solvable g a
      else
        false
  | _ => false
  end.

(**
  WHNF(Γ, e) predicate (§3.2):
    WHNF(Γ, e) =
      True   if solvable(Γ, e)
      True   if e ≡ D
      True   if e ≡ b
      True   if e ≡ λx. e (or closure (Γ', λx. e))
      True   if e ≡ eb ⊲ γ ∧ WHNF(Γ, eb)
      True   if e ≡ if ec then et else ef ∧ solvable(Γ, ec) ∧ WHNF(Γ, et) ∧ WHNF(Γ, ef)
      False  otherwise
*)
Fixpoint whnf (g : environment) (e : expr) : bool :=
  if solvable g e then
    true
  else
    match e with
    | ECon d => true
    | EBot b => true
    | ELam x body => true
    | EClos env_def x body => true
    | ECoercion gamma => true
    | EType tau => true
    | ECast eb gamma => whnf g eb
    | EIf ec et ef =>
        solvable g ec && whnf g et && whnf g ef
    | _ => false
    end.
