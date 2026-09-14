# Handoff: writing the SymFC revision

The paper will carry **pen-and-paper proofs**. It will not claim a mechanisation.
The Rocq development in this repository exists to check that those proofs are not
wrong. Treat it as a bullshit detector, not as an artefact to cite.

This document carries what a paper-writing session needs: the definitions in a
form you can transcribe, the two theorems and how they are proved, every
assumption that survives, the places where the **paper itself is wrong**, and the
counterexamples that force each design choice. The counterexamples matter most.
A pen-and-paper proof that ignores them will be wrong in exactly that spot,
because each one is a place where the obvious thing to write down is false.

Build: `coqc -Q . SymCoreTheory SymCore.v && coqc -Q . SymCoreTheory ConCore.v`.

---

## 1. Corrections the paper needs

These are defects in `../pantomime-symbex-paper/src/theory.tex`, not in the
mechanisation. Fix them before writing proofs, because each changes a case
analysis.

**1.1 Rule App-Spine is non-deterministic as printed.** Its premise is a bare
`¬WHNF(Γ, e_f)`. A cast is in WHNF exactly when its operand is, and a lambda
never is, so `((λx. λz. x) ⊲ γ) D` satisfies it while Rule App-Cast also
applies — and the two disagree. App-Spine strips the cast and passes the plain
argument; App-Cast pushes `sym γ_dom` into the argument first. The resulting
closures bind `x` to `D` and to `D ⊲ sym γ_dom` respectively. The fix is one
extra premise: App-Spine refuses **every** cast operator. See §4.3.

**1.2 WHNF lists a bare `λx. e` as a value, but App-Abs takes a closure.** Both
cannot be right. If `λx. e` is a value then `(λx. e) e_a` has no applicable rule
at all. The mechanisation resolves it by making only the closure form a value,
which is the reading that keeps the calculus running. Say which you mean.

**1.3 A constructor application has no value.** WHNF lists only `e ≡ D`, and no
rule builds `D e⃗`. So `Just 5` cannot be constructed or matched, and the
`fold-alts` clause for `e ≡ D e⃗` is unreachable for any arity above zero. Both
theorems go vacuous on any program using data with fields. The fix is to
generalise both constructor rules from a bare `D` to a spine headed by one; the
arguments must stay unevaluated, which is what `fold-alts` already assumes when
it binds them into the environment as thunks. See §4.4.

**1.4 There is no rule for applying a cast whose coercion does not split.**
`Case-Scrut` also sits commented out in `theory.tex`, which suggests this area
was mid-revision. The mechanisation now makes that shape deliberately stuck; say
so explicitly rather than leaving it as an omission. See §4.3.

---

## 2. The two theorems

Notation used below: `σ ⊨ Φ` for a model satisfying a path condition,
`e ⊒σ,S e′` for "e′ is the σ-instance of e" (the `contains` relation),
`Φ ; Γ ⊢ e ⇓ v` for unbounded symbolic evaluation, `Φ ; Γ ⊢ e ⇓ᵏ v` for
evaluation under a budget of `k`, and `Γ ⊢ᶜ e ⇓ᶜ v` for concrete evaluation.

### Soundness

> Let σ ⊨ Φ. If Γₛ ⊒σ,S Γ𝚌 and eₛ ⊒σ,S e𝚌 with e𝚌 ∈ ConCore, and
> Φ ; Γₛ ⊢ eₛ ⇓ vₛ, then there is a v𝚌 with Γ𝚌 ⊢ᶜ e𝚌 ⇓ᶜ v𝚌 and vₛ ⊒σ,S v𝚌.

Plain English: whatever symbolic execution reports, every concrete instance
really does compute, and the symbolic result stands for the concrete one.
No budget, no side condition.

### Completeness

> Let σ ⊨ Φ. If Γₛ ⊒σ,S Γ𝚌, eₛ ⊒σ,S e𝚌 with e𝚌 ∈ ConCore, **eₛ is progressive**,
> and Γ𝚌 ⊢ᶜ e𝚌 ⇓ᶜ v𝚌, then there are k ∈ ℕ and vₛ with
> Φ ; Γₛ ⊢ eₛ ⇓ᵏ vₛ and vₛ ⊒σ,S v𝚌.

Plain English: if the symbolic evaluator progresses on the path the model takes,
then any value the concrete run produces is also produced by symbolic execution
at some finite unrolling depth.

**Quantifier warning.** `eₛ` is universally quantified. The theorem does *not*
say a progressive symbolic expression exists that matches `e𝚌`. It says the
program you actually wrote covers its own concrete instances. `progressive` sits
in the same position as "well-typed" in a preservation theorem. The only
existentials are `k` and `vₛ`.

---

## 3. Definitions to transcribe

### 3.1 `contains` — the instance relation

`e ⊒σ,S e′` where σ maps symbolic variables to literals and `S` is the set of
symbolic variables. Nineteen rules; the ones that are not plain congruence:

- **Cont_Var_Sym** — a symbolic variable goes to its value: `S x = true` gives
  `EVar x ⊒ ELit (σ x)`. This is what makes the concrete side free of symbolic
  variables, which is what the rebuttal promised.
- **Cont_Var_Bound** — a non-symbolic variable stands for itself.
- **Cont_If_True / Cont_If_False** — a branch resolves to the arm σ selects.
  Note neither rule inspects the arm it does *not* take. This is load-bearing:
  it is why truncating an untaken arm costs nothing.
- **Cont_Denote** — a saturated primitive application that mentions a symbolic
  variable is related to the literal it denotes. Guarded by `smt_ground e = false`,
  so a closed SMT term stays rigid.
- **Cont_Env_Extend** — every binder must satisfy `S x = false`. That is the
  freshness discipline that makes "symbolic variable" well defined.

The relation is **semantic on the SMT fragment and syntactic everywhere else.**
That split is forced; see §5.1.

### 3.2 `progressive` — the completeness side condition

Walks down the branch spine, following the arm σ selects. Three clauses:

- **Prog_Then / Prog_Else** — at a branch: the guard evaluates to some `ec′` at
  every budget; σ reads the guard one way; `ec′` is expressible as a path
  condition; the **untaken** arm is `budget_total`; and the taken arm is
  recursively progressive.
- **Prog_Leaf** — when the branches run out:
  `leaf_progressive Φ Γ e := (solver_free e ∧ solver_free_env Γ) ∨ (∃v, Φ ; Γ ⊢ e ⇓ v)`

where `budget_total Φ Γ e := ∃h, ∀n ≥ h, ∃v, Φ ; Γ ⊢ e ⇓ⁿ v` — "for a big enough
budget it answers *something*". A looping arm satisfies it. A stuck arm does not.
That is exactly the line the predicate must draw.

`solver_free` excludes `EIf`, `ECase`, `ECast` and `EPrimOp` — the four shapes
whose value comes from an axiomatised function (`merge`, `cast_expr`,
`reduce_prim`) or from branch resolution.

**Do not call this a stand-in for a type system.** It bundles three different
things, and only the first is typing:
1. well-typedness of the applicative core (rules out applying a literal, or a
   cast whose coercion does not split);
2. opacity of the solver primitives — `case`, `cast` and primops are perfectly
   well-typed and are excluded because no syntactic invariant survives an
   axiomatised function;
3. convergence, for leaves that touch those primitives — and no type system
   gives you termination.

A reviewer who knows FC will ask why `case` is barred from a leaf. "Typing" is
not the answer. Say what would remove each part: a type system for SymCore
discharges (1); modelling the solver concretely instead of axiomatising it
discharges (2).

### 3.3 The budget

`fuel ::= Inf | Fin n`, with `dec Inf = Inf` and `dec (Fin (S n)) = Fin n`.
Every rule threads `dec f` through its recursive premises. One added rule:

> **Out-Of-Fuel.** `Φ ; Γ ⊢ e ⇓^(Fin 0) ⊥?` for any `e`.

`eval Inf` is exactly the unbounded relation, so the two judgements are one
inductive definition rather than two. On paper this is just "evaluation indexed
by a budget, with ∞ allowed".

---

## 4. Proof structure

### 4.1 Soundness

Induction on the **symbolic** derivation, as a pair of mutually recursive
functions over `eval` and `fold_alts`. The plain induction principle does not
work, for a reason worth stating in the paper: Rule App-Prim carries a
`Forall2 (eval Φ Γ) args args'`, and the derived scheme does not strengthen
through it, nor through the sibling `fold_alts` relation. On paper this is the
difference between "induction on the derivation" and "induction on the height of
the derivation, with a simultaneous statement for `fold-alts`". Write the latter.

### 4.2 Completeness

Induction on the `progressive` derivation — **not** on the concrete derivation.
Three cases.

At a leaf, soundness carries the concrete run back and determinism pins the
value. At a branch, the guard costs nothing (it answers at every budget), the
taken arm's threshold comes from the induction hypothesis, the untaken arm's from
`budget_total`, and Rule If spends one more.

**The statement must be upward closed in the budget**, i.e. prove
`∃h, ∀n ≥ h, …` and not `∃n, …`. The "some budget works" form does not survive
the induction, because a branch has several premises whose budgets differ and
taking the maximum is only legal if the statement is upward closed. This is the
single most likely thing for a paper proof to get wrong.

### 4.3 Determinism

Concrete evaluation is deterministic on ConCore programs, given a concrete
environment. This needs both fixes from §1.1 and §1.4: App-Spine refusing every
cast operator, and no rule for applying a non-splitting cast. Without them the
counterexample in §5.3 stands.

Symbolic evaluation is **not** deterministic, and this is not fixable: Rule
Prune reduces anything to unreachable whenever the path condition is
unsatisfiable, which is the entire point of the rule. Do not claim symbolic
determinism.

### 4.4 The constructor rules

> WHNF: a spine whose head is a constructor is a value.
> Rule Con: such a spine evaluates to itself, arguments untouched.

Laziness is forced, not chosen: `fold-alts` binds the raw argument expressions
into the environment, so they must arrive unevaluated.

---

## 5. The counterexamples

Each is a place where the natural thing to write is false. They are the reason to
trust the rest.

### 5.1 `reduce_prim` cannot compute, if `contains` is syntactic

If `contains` is a syntactic congruence, then `reduce_prim_contains` forces:
if `⊗ l` returns a literal for every literal — that is, if the reducer computes
at all — then `⊗` is either a constant function or the identity. Negation and
increment are neither. *This is why `contains` must be semantic on the SMT
fragment.* Without `Cont_Denote` the axiom set is consistent only because the
reducer never evaluates anything.

### 5.2 Completeness is false without the side condition

`if x then l′ else ((l) l)`. The concrete run terminates at `l′`. Symbolic
execution has **no** value at any budget: at depth zero the taken arm truncates
to the wrong value, and at any greater depth the malformed else-branch has no
derivation at all. Introduce this **before** the `progressive` predicate, never
after. A reviewer shown that completeness is false will accept a hypothesis; one
shown a hypothesis first will wonder what you are hiding.

### 5.3 The determinism counterexample

`((λx. λz. x) ⊲ γ) D` with `γ : (a → b) ~ (c → d)`. Two rules apply and disagree;
the resulting closures bind `x` to `D` and `D ⊲ sym γ_dom`. Note the inner `λz`
is essential — it makes evaluation stop at a closure with the binding still
visible. Without it the disagreement hides inside a `cast` call.

### 5.4 A budget rescues divergence, never stuckness

`if x then l′ else Ω` with `Ω = (λf. f f)(λf. f f)`: the whole program has **no**
unbounded value, yet completeness delivers one at `k = 2`, and every larger `k`
works too. Contrast §5.2, where no `k` works. Divergence truncates gracefully at
any depth; stuckness has no derivation at any positive depth and Out-Of-Fuel
lives only at zero. Use both examples together — the first alone does not show
the budget earning its keep.

### 5.5 A bigger budget can lose the value

Monotonicity is false. Worse: a bigger budget can leave a stuck term with **no**
value at all, not merely a different one. What is true is that above the
threshold from the unbounded derivation, every larger budget gives the *same*
value. Say the true statement; the naive one is refuted.

### 5.6 A branch at the top is not enough

`is_if e = false` constrains only the top node. `(if x then λy. y else (l l)) l`
passes it, concretises to an ordinary converging redex, and has no symbolic value
at any budget. Any lemma phrased "branch-free at the root" is false.

---

## 6. Assumptions

Thirty-four. Group them this way in the paper; the grouping is the justification.

**Abstract sorts and signatures (14)** — `lit`, `primop`, `tycon`, `op_and`,
`op_not`, `primop_arity`, `sat`, `pc_true`, `models`, `reduce_prim`, `merge`,
`cast_expr`, `subst_coerc`, `subst_type`. These assert nothing; they say the
things exist.

**Solver facts (3)** — `sat_pc_true`, `models_sat`, `models_and_iff`. True of any
solver and any Boolean semantics.

**Syntactic preservation (5)** — `reduce_prim_solvable`, `reduce_prim_saturated`,
`reduce_prim_concore`, `merge_concore`, `cast_expr_concore`. The first and third
are **conditional on their arguments being well-formed**; unconditional versions
caused the collapse in §5.1.

**Grisette and coercion behaviour (4)** — `merge_fold_alts_equiv`,
`fold_alts_no_nested_if`, `eval_models_cond`, `eval_models_not_cond`. The last two
assume precisely that `reduce_prim` preserves a condition's denotation and its
truth; everything else about them is proved.

**Simulation (8)** — `merge_contains`, `cast_expr_contains`,
`subst_coerc_contains_env`, `subst_type_contains_env`, `reduce_prim_contains`,
`prim_value`, `reduce_prim_denote`, `reduce_prim_ground_value`.

`models_cond` and `models_not_cond` are **definitions**, not assumptions —
`models_cond σ S e := ∃pc, denotes S e pc ∧ σ ⊨ pc`. Deriving them rather than
assuming them removed five assumptions and is worth a sentence.

---

## 7. Honest limits

**No model of the axiom set has been exhibited.** `lit` and `models` are abstract,
so no model can be built inside the development. Every non-vacuity result about
branches is therefore conditional on a model existing. What *is* unconditional:
σ genuinely instantiates symbolic variables, `contains` is not syntactic identity,
and the `reduce_prim` collapse is gone. Closing this means instantiating the
theory concretely (say `lit := bool`) and checking all 34 assumptions hold.

**`reduce_prim` is still a term-builder, not a computing reducer**, outside the
`Cont_Denote` fragment. This is the largest remaining semantic gap.

**Completeness covers the branch spine, not arbitrary nesting.** A divergent
untaken arm is tolerated on the spine the model resolves. A branch buried under
an application needs arms that terminate, because the leaf clause requires the
solver-free disjunct or convergence.

**The leaf clause cannot currently be weakened further.** Rule Case is the
blocker: the concrete fold runs on `merge e𝚌′` while concretion relates
`merge eₛ′` to `e𝚌′`. Closing it needs a fact saying concretion survives `merge`
on the concrete side — a new assumption, deliberately not added. Well-founded
recursion on derivation height does not help, because the converted derivation
carries no height.

**Symbolic evaluation is not deterministic** (Rule Prune). Only concrete
evaluation is, and only on ConCore programs in a concrete environment.

---

## 8. Checking a claim against the development

While writing prose you will keep asking "is this actually true?". Answer it in
Rocq rather than by reading the file. The workflow below is the one that made
this development's defects findable; the discipline is not optional, because the
naive approach is slow enough to make you stop checking.

### 8.1 Never recompile to test an idea

`ConCore.v` is ~4800 lines. Recompiling it to find out whether one tactic worked
will burn an hour and your patience. Instead write a scratch file that imports the
already-compiled development, and compile only that:

```bash
coqc -Q . SymCoreTheory SymCore.v     # once
coqc -Q . SymCoreTheory ConCore.v     # once
```

```coq
(* probe.v *)
From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.
```

```bash
coqtop -q -Q . SymCoreTheory -batch -l probe.v
```

Silence means everything in the file was accepted. Any output is a failure with
its line number.

### 8.2 Look at the goal before writing a tactic

Guessing a tactic and recompiling is the slow path. Put `Show.` where you are
stuck and end the proof with `Abort.` so the file still runs:

```coq
Lemma whatever : forall Φ Γ e, ...
Proof.
  intros. inversion H; subst. Show 1. Show 2.
Abort.
```

`Show N.` prints the Nth remaining goal with its full context. Read it, then write
the tactic that closes it. `Check foo.` prints a statement, `Print foo.` prints a
definition, `Print Assumptions foo.` lists exactly which axioms a result rests on.

### 8.3 Three questions worth asking constantly

**"Is this statement true?"** Write it as a `Lemma` and try to prove it. If it
compiles, it is true.

**"Is this statement false?"** Prove its negation. Several results in `scratch/`
are negations — that is how the counterexamples in §5 are recorded, and a proved
negation is much stronger evidence than a failed proof attempt.

**"What does this result depend on?"** `Print Assumptions foo.` If it lists
something you did not expect, the proof is leaning on an assumption you have not
justified in the paper.

### 8.4 Two gotchas specific to this development

**The fuel index breaks `destruct` and `induction`.** `inversion H` on a
derivation at `Inf` correctly drops the Out-Of-Fuel case, because `Fin 0` cannot
unify with `Inf`. But `destruct` and `induction` *generalise* the index, so the
case returns and sub-derivations arrive at `dec f` rather than `Inf`. Use the
`inf_destruct` / `inf_induction` tactics in `ConCore.v`, or add an explicit
`k0 = Inf ->` premise and discharge the bad case with `discriminate`.

**`match goal` patterns written with notation can stop matching.** `Φ ; Γ ⊢ e ⇓ v`
means `eval Inf Φ Γ e v`, so a pattern written that way will not match a premise
sitting at `eval (dec Inf) ...`. Write `eval _ Φ Γ e v` in tactic patterns.

### 8.5 The regression suite

`scratch/` holds twenty-three files. Nineteen must compile; four
(`Audit.v`, `prim.v`, `prim2.v`, `ReducePrimCannotCompute.v`) must **fail** —
they are pre-repair results that must stay unprovable. If one of those four starts
compiling, a defect has come back. Check all of them after any change:

```bash
for f in scratch/*.v; do coqtop -q -Q . SymCoreTheory -batch -l "$f" >/dev/null 2>&1 \
  && echo "PASS $f" || echo "FAIL $f"; done
```

The files most worth reading before writing proofs: `CompletenessNeedsFuel.v`
(§5.2), `DivergenceNeedsFuel.v` (§5.4), `ReducePrimCannotCompute.v` (§5.1, must
fail), `CastSplitWorkedExample.v` (§5.3), `ConstructorApplicationStuck.v` (§1.3).

If you add a counterexample while writing, put it in `scratch/` so the next person
inherits it. That directory is the reason the five defects fixed this session
cannot come back silently.
