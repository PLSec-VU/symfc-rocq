From SymCoreTheory Require Export SymCore.Merge.
From Stdlib Require Import Strings.String Lists.List ZArith.ZArith Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Section SymCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.
(** ------------------------------------------------------------------------- *)
(** Fuel: a depth bound carried by the reduction judgement                    *)
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
      eval (Live f) Φ Γ (EApp (EThunk Γ' (ELam x eb)) ea) eb'

  (** Rule App-Spine: Reduce a function head that is a computation. A cast,
      a closure, a bottom and a constructor, primitive or branch spine are
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

  (** Rule Lam: a lambda evaluates to its closure, the thunk (Γ, λx. e) *)
  | Eval_Lam : forall f Φ Γ x e,
      eval (Live f) Φ Γ (ELam x e) (EThunk Γ (ELam x e))

  (** Rule App-Cast: Higher-order coercion pushing *)
  | Eval_AppCast : forall f Φ Γ ef γ ea γ_a γ_r er,
      decomp_coerc_arrow γ = Some (γ_a, γ_r) ->
      eval (dec f) Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er ->
      eval (Live f) Φ Γ (EApp (ECast ef γ) ea) er

  (** Rule App-If: a spine headed by a branch applies each arm to the whole
      argument spine *)
  | Eval_AppIf : forall f Φ Γ e1 e2 ec et ef args er,
      unspool_app (EApp e1 e2) [] = (EIf ec et ef, args) ->
      eval (dec f) Φ Γ (EIf ec (fold_left EApp args et) (fold_left EApp args ef)) er ->
      eval (Live f) Φ Γ (EApp e1 e2) er

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
    Kind 1: the scrutinee is a boolean formula with no variable, for example
    true or not true. Its truth value is fixed, so the match picks the True or
    the False alternative just as a constructor match would.
  *)
  | FoldAlts_GroundFormula : forall f Φ Γ e pc alts r,
      expr_to_pc Γ e = Some pc ->
      pc_has_var pc = false ->
      fold_alts f Φ Γ (ECon (truth_constructor (pc_closed_value pc))) alts r ->
      fold_alts f Φ Γ e alts r

  (**
    Kind 2: the scrutinee is a boolean formula that mentions a variable and
    whose primitives all have their exact arity, for example and x y. The match
    becomes a runtime branch: the True alternative folds under the path
    condition strengthened by the formula, the False alternative under the
    negation.
  *)
  | FoldAlts_SymbolicFormula : forall f Φ Γ e pc alts r1 r2,
      expr_to_pc Γ e = Some pc ->
      pc_has_var pc = true ->
      pc_arities_ok pc = true ->
      fold_alts f (Φ ∧ pc) Γ (ECon dcon_true) alts r1 ->
      fold_alts f (Φ ∧ ¬ pc) Γ (ECon dcon_false) alts r2 ->
      fold_alts f Φ Γ e alts (EIf e r1 r2)

  (**
    Otherwise: undefined behaviour.

    The scrutinee is not a branch at its spine head, matches no alternative,
    is not a bottom, and is neither a boolean formula nor a primitive
    application. The last two extra premises are what keep this rule off the
    boolean formulas that the two clauses above resolve, and off a primitive
    application that does not convert to a formula (a solver that leaves a
    branch inside a primitive), which is stuck rather than undefined.

    Demanding only that the scrutinee itself is not a branch would be too weak:
    it would let this rule answer EApp (EIf ec et ef) a, a scrutinee that still
    has a branch to resolve, with a bottom. Rule FoldAlts_If resolves branches,
    and it only sees a branch that sits at the top. The spine-head premise
    implies is_if e = false (is_if_false_of_spine_head), so nothing this rule
    used to reject is accepted now.
  *)
  | FoldAlts_Otherwise : forall f Φ Γ e alts,
      expr_to_pc Γ e = None ->
      is_op_app e = false ->
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
