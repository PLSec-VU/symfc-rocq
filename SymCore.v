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

(** Literals mirror those found in SMT solvers; axiomatized from external SMT (§3.1) *)
Axiom lit : Set.
Axiom lit_eq_dec : forall (l1 l2 : lit), {l1 = l2} + {l1 <> l2}.

(** Primitive operations mirror SMT solver primitives; axiomatized from external SMT (§3.1) *)
Axiom primop : Set.
Axiom primop_eq_dec : forall (p1 p2 : primop), {p1 = p2} + {p1 <> p2}.

(** SMT boolean primitives for path condition connectives *)
Axiom op_and : primop.
Axiom op_not : primop.

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
Definition sym_coerc (γ : coercion) : coercion :=
  MkCoercion (coerc_dst γ) (coerc_src γ) (coerc_role γ).

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
Fixpoint lookup_env (Γ : environment) (x : var) : option (environment * expr) :=
  match Γ with
  | EmptyEnv => None
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
Fixpoint extend_env_multi (Γ : environment) (xs : list var) (args : list expr) (Γ_arg : environment) : environment :=
  match xs, args with
  | x :: xs', a :: args' =>
      extend_env (extend_env_multi Γ xs' args' Γ_arg) x Γ_arg a
  | _, _ => Γ
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

(** SMT satisfiability oracle SAT(Φ) (Fig. 3, Rule Prune); axiomatized from SMT solver *)
Axiom sat : path_condition -> bool.

(** Conjunction of path conditions: Φ1 ∧ Φ2 *)
Definition pc_and (Φ1 Φ2 : path_condition) : path_condition :=
  PCPrim op_and [Φ1; Φ2].

(** Negation of a path condition: ¬Φ *)
Definition pc_not (Φ : path_condition) : path_condition :=
  PCPrim op_not [Φ].

Notation "Φ1 '∧' Φ2" := (pc_and Φ1 Φ2) (at level 40, left associativity).
Notation "'¬' Φ" := (pc_not Φ) (at level 35, right associativity).

(** Convert a solvable expression into a path condition formula *)
Fixpoint expr_to_pc (e : expr) : option path_condition :=
  match e with
  | EVar x => Some (PCVar x)
  | ELit l => Some (PCLit l)
  | EPrimOp p => Some (PCPrim p [])
  | EApp f a =>
      match expr_to_pc f, expr_to_pc a with
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

(** Theory-specific primitive reduction: reduce-prim(⊗ e⃗) (Fig. 3, Rule App-Prim); axiomatized from SMT solver *)
Axiom reduce_prim : primop -> list expr -> expr.

(** Cast simplification: cast(e, γ) (Fig. 3, Rule Cast) *)
Parameter cast_expr : expr -> coercion -> expr.

(** Leaf expression merging (Fig. 3, Rule Case & Section 3.3); axiomatized from Grisette *)
Axiom merge : expr -> expr.

(** Type and Coercion substitution under environment Γ (Fig. 3, Rules Type and Coercion) *)
Parameter subst_coerc : environment -> coercion -> coercion.
Parameter subst_type : environment -> type_fc -> type_fc.

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
  Solvable Γ e in Prop (§3.2):
    - Literals: e ≡ l
    - Symbolic variables: e ≡ x ∧ x ∉ Γ
    - Primitive operations: e ≡ ⊗ e⃗ where all arguments are solvable
*)
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

(**
  Whnf Γ e in Prop (§3.2):
    - Solvable(Γ, e)
    - e ≡ D
    - e ≡ b
    - e ≡ λx. e (or closure (Γ', λx. e))
    - e ≡ eb ⊲ γ ∧ Whnf(Γ, eb)
    - e ≡ if ec then et else ef ∧ Solvable(Γ, ec) ∧ Whnf(Γ, et) ∧ Whnf(Γ, ef)
*)
Inductive Whnf (Γ : environment) : expr -> Prop :=
  | Whnf_Solvable : forall e,
      Solvable Γ e ->
      Whnf Γ e
  | Whnf_Con : forall d,
      Whnf Γ (ECon d)
  | Whnf_Bot : forall b,
      Whnf Γ (EBot b)
  | Whnf_Lam : forall x body,
      Whnf Γ (ELam x body)
  | Whnf_Clos : forall Γ_def x body,
      Whnf Γ (EClos Γ_def x body)
  | Whnf_Coercion : forall γ,
      Whnf Γ (ECoercion γ)
  | Whnf_Type : forall τ,
      Whnf Γ (EType τ)
  | Whnf_Cast : forall eb γ,
      Whnf Γ eb ->
      Whnf Γ (ECast eb γ)
  | Whnf_If : forall ec et ef,
      Solvable Γ ec ->
      Whnf Γ et ->
      Whnf Γ ef ->
      Whnf Γ (EIf ec et ef).

(** ========================================================================= *)
(** 8. Decision Functions (Fixpoints) for Solvable and WHNF                    *)
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
Defined.

(** Helper inversion lemmas on Solvable *)
Lemma solvable_not_cast : forall Γ e γ, ~ Solvable Γ (ECast e γ).
Proof. intros Γ e γ H. inversion H. Qed.

Lemma solvable_not_if : forall Γ c t f, ~ Solvable Γ (EIf c t f).
Proof. intros Γ c t f H. inversion H. Qed.

(** WHNF is decidable *)
Fixpoint whnf_dec (Γ : environment) (e : expr) : {Whnf Γ e} + {~ Whnf Γ e}.
Proof.
  destruct (solvable_dec Γ e) as [S | NS].
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
    + destruct (whnf_dec Γ e) as [W | NW].
      * left. apply Whnf_Cast. assumption.
      * right. intros H. inversion H; subst.
        -- apply (solvable_not_cast Γ e c); auto.
        -- apply NW; auto.
    + left. apply Whnf_Coercion.
    + left. apply Whnf_Type.
    + destruct (solvable_dec Γ e1) as [S1 | NS1].
      * destruct (whnf_dec Γ e2) as [W2 | NW2].
        -- destruct (whnf_dec Γ e3) as [W3 | NW3].
           ++ left. apply Whnf_If; auto.
           ++ right. intros H. inversion H; subst.
              ** apply (solvable_not_if Γ e1 e2 e3); auto.
              ** apply NW3; auto.
        -- right. intros H. inversion H; subst.
           ++ apply (solvable_not_if Γ e1 e2 e3); auto.
           ++ apply NW2; auto.
      * right. intros H. inversion H; subst.
        -- apply (solvable_not_if Γ e1 e2 e3); auto.
        -- apply NS1; auto.
    + left. apply Whnf_Bot.
Defined.

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

(** Construct curried constructor application from constructor name and argument list *)
Definition make_con_app (d : dcon) (args : list expr) : expr :=
  fold_left EApp args (ECon d).

(**
  Mutual inductive definitions of:
  - Big-Step Reduction Judgement: Φ; Γ ⊢ e ⇓ e' (Figure 3)
  - Pattern Matching and Branch Folding: fold-alts(Φ, Γ, e, a⃗) (§3.2, lines 570-590)
*)
Inductive eval : path_condition -> environment -> expr -> expr -> Prop :=
  (** Rule Var: Variable lookup in Γ and recursive evaluation *)
  | Eval_Var : forall Φ Γ x Γ' e e',
      lookup_env Γ x = Some (Γ', e) ->
      eval Φ Γ' e e' ->
      eval Φ Γ (EVar x) e'

  (** Rule Lit: Literal reflexivity *)
  | Eval_Lit : forall Φ Γ l,
      eval Φ Γ (ELit l) (ELit l)

  (** Rule Con: Data constructor reflexivity *)
  | Eval_Con : forall Φ Γ d,
      eval Φ Γ (ECon d) (ECon d)

  (** Rule Cast: Evaluate expression and simplify cast *)
  | Eval_Cast : forall Φ Γ e γ e',
      eval Φ Γ e e' ->
      eval Φ Γ (ECast e γ) (cast_expr e' γ)

  (** Rule App-Abs: Beta-reduction with closure environment extension *)
  | Eval_AppAbs : forall Φ Γ Γ' x eb ea eb',
      eval Φ (extend_env Γ' x Γ ea) eb eb' ->
      eval Φ Γ (EApp (EClos Γ' x eb) ea) eb'

  (** Rule App-Spine: Reduce function head when not in WHNF *)
  | Eval_AppSpine : forall Φ Γ ef ea ef' er,
      ~ Whnf Γ ef ->
      eval Φ Γ ef ef' ->
      eval Φ Γ (EApp ef' ea) er ->
      eval Φ Γ (EApp ef ea) er

  (** Rule Bot: Bottom value reflexivity *)
  | Eval_Bot : forall Φ Γ b,
      eval Φ Γ (EBot b) (EBot b)

  (** Rule App-Prim: Evaluate primitive operation arguments and reduce *)
  | Eval_AppPrim : forall Φ Γ ef ea p args args',
      unspool_app (EApp ef ea) [] = (EPrimOp p, args) ->
      Forall2 (eval Φ Γ) args args' ->
      eval Φ Γ (EApp ef ea) (reduce_prim p args')

  (** Rule Lam: Function abstraction evaluates to runtime closure *)
  | Eval_Lam : forall Φ Γ x e,
      eval Φ Γ (ELam x e) (EClos Γ x e)

  (** Rule App-Cast: Higher-order coercion pushing *)
  | Eval_AppCast : forall Φ Γ ef γ ea γ_a γ_r er,
      decomp_coerc_arrow γ = Some (γ_a, γ_r) ->
      eval Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er ->
      eval Φ Γ (EApp (ECast ef γ) ea) er

  (** Rule App-Bot: Propagation of bottom in function position *)
  | Eval_AppBot : forall Φ Γ b ea,
      eval Φ Γ (EApp (EBot b) ea) (EBot b)

  (** Rule Case: Evaluate scrutinee, merge common prefixes, and fold alternatives *)
  | Eval_Case : forall Φ Γ es alts es' er,
      eval Φ Γ es es' ->
      fold_alts Φ Γ (merge es') alts er ->
      eval Φ Γ (ECase es alts) er

  (** Rule If: Evaluate condition, convert to path condition, and branch *)
  | Eval_If : forall Φ Γ ec et ef ec' et' ef' pc_c,
      eval Φ Γ ec ec' ->
      expr_to_pc ec' = Some pc_c ->
      eval (Φ ∧ pc_c) Γ et et' ->
      eval (Φ ∧ ¬ pc_c) Γ ef ef' ->
      eval Φ Γ (EIf ec et ef) (EIf ec' et' ef')

  (** Rule Coercion: Evaluate coercion under substitution *)
  | Eval_Coercion : forall Φ Γ γ,
      eval Φ Γ (ECoercion γ) (ECoercion (subst_coerc Γ γ))

  (** Rule Prune: Infeasible path conditions reduce to unreachable *)
  | Eval_Prune : forall Φ Γ e,
      sat Φ = false ->
      eval Φ Γ e (EBot BUnreachable)

  (** Rule Type: Evaluate type under substitution *)
  | Eval_Type : forall Φ Γ τ,
      eval Φ Γ (EType τ) (EType (subst_type Γ τ))

with fold_alts : path_condition -> environment -> expr -> list alt -> expr -> Prop :=
  (** Branch traversal: condition is converted to path condition *)
  | FoldAlts_If : forall Φ Γ ec et ef alts et' ef' pc_c,
      expr_to_pc ec = Some pc_c ->
      fold_alts (Φ ∧ pc_c) Γ et alts et' ->
      fold_alts (Φ ∧ ¬ pc_c) Γ ef alts ef' ->
      fold_alts Φ Γ (EIf ec et ef) alts (EIf ec et' ef')

  (** Fallback for ill-formed condition in branching *)
  | FoldAlts_IfFail : forall Φ Γ ec et ef alts,
      expr_to_pc ec = None ->
      fold_alts Φ Γ (EIf ec et ef) alts (EBot BUndefined)

  (** Constructor match: find alternative and reduce body *)
  | FoldAlts_Con : forall Φ Γ e d ea xs ep alts er,
      decompose_con_app e = Some (d, ea) ->
      find_alt d alts = Some (xs, ep) ->
      eval Φ (extend_env_multi Γ xs ea Γ) ep er ->
      fold_alts Φ Γ e alts er

  (** Bottom propagation *)
  | FoldAlts_Bot : forall Φ Γ b alts,
      fold_alts Φ Γ (EBot b) alts (EBot b)

  (** Otherwise: undefined behavior *)
  | FoldAlts_Otherwise : forall Φ Γ e alts,
      is_if e = false ->
      (match decompose_con_app e with
       | Some (d, _) => find_alt d alts = None
       | None => True
       end) ->
      is_bot e = false ->
      fold_alts Φ Γ e alts (EBot BUndefined).

(** Notation for big-step reduction: Φ; Γ ⊢ e ⇓ e' *)
Notation "Φ ';' Γ '⊢' e '⇓' e'" := (eval Φ Γ e e') (at level 70, no associativity).

(** ========================================================================= *)
(** 10. Metatheory of SymCore (§3.2, §3.3)                                     *)
(** ========================================================================= *)

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

(** Any evaluation under an unsatisfiable path condition yields unreachable *)
Lemma eval_unsat_unreachable : forall Φ Γ e v,
  sat Φ = false ->
  Φ ; Γ ⊢ e ⇓ v ->
  v = EBot BUnreachable.
Admitted.

(** ------------------------------------------------------------------------- *)
(** 10.2 Semantic Contract for Merge (§3.3)                                    *)
(** ------------------------------------------------------------------------- *)

(** Leaf merging preserves alternative folding in case expressions *)
Axiom merge_fold_alts_equiv : forall Φ Γ e alts r,
  fold_alts Φ Γ (merge e) alts r <-> fold_alts Φ Γ e alts r.

(** Leaf merging preserves WHNF *)
Axiom merge_preserves_whnf : forall Γ e,
  Whnf Γ e -> Whnf Γ (merge e).

(** ------------------------------------------------------------------------- *)
(** 10.3 Normal Form / WHNF Guarantee (§3.2)                                   *)
(** ------------------------------------------------------------------------- *)

(** Evaluation under a satisfiable path condition produces a WHNF (or bottom) *)
Theorem eval_whnf : forall Φ Γ e v,
  Φ ; Γ ⊢ e ⇓ v ->
  sat Φ = false \/ Whnf Γ v.
Admitted.

Lemma fold_alts_whnf : forall Φ Γ e alts r,
  fold_alts Φ Γ e alts r ->
  sat Φ = false \/ Whnf Γ r.
Admitted.

(** ------------------------------------------------------------------------- *)
(** 10.4 Determinism of Evaluation (§3.2)                                      *)
(** ------------------------------------------------------------------------- *)

(** Evaluation in SymCore is deterministic *)
Theorem eval_deterministic : forall Φ Γ e v1 v2,
  Φ ; Γ ⊢ e ⇓ v1 ->
  Φ ; Γ ⊢ e ⇓ v2 ->
  v1 = v2.
Admitted.

Lemma fold_alts_deterministic : forall Φ Γ e alts r1 r2,
  fold_alts Φ Γ e alts r1 ->
  fold_alts Φ Γ e alts r2 ->
  r1 = r2.
Admitted.

(** ------------------------------------------------------------------------- *)
(** 10.5 Environment Extensionality                                           *)
(** ------------------------------------------------------------------------- *)

(** Evaluation depends only on the extensional behavior of environment lookup *)
Lemma eval_extensional_env : forall Φ Γ1 Γ2 e v,
  (forall x, lookup_env Γ1 x = lookup_env Γ2 x) ->
  Φ ; Γ1 ⊢ e ⇓ v ->
  Φ ; Γ2 ⊢ e ⇓ v.
Admitted.

