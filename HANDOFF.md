# Handoff: rewriting the SymFC theory section

This document is for a new session that rewrites the theory section of the SymFC paper. That session adds determinism, soundness and completeness theorems, with pen-and-paper proofs. The paper source is `../pantomime-symbex-paper/src/theory.tex`. The reviews and the rebuttal are `../pantomime-symbex-paper/reviews.md` and `rebuttal.md`.

The Rocq development in this repository is the ground truth. It checks every definition and theorem below. Use it to check that the paper's statements are true. The paper does not claim a mechanisation.

Terms used in this document:

- **Symbolic run.** Evaluation of a SymCore program that contains symbolic variables and symbolic branches.
- **Concrete run.** Evaluation of a ConCore program. A ConCore program is a SymCore program with no symbolic branch and no free variable.
- **Model.** A map `σ` from symbolic variables to literals. The SMT solver returns it.
- **Instance.** The concrete term `e_c` is an instance of the symbolic term `e_s` under `σ` when `contains σ S e_s e_c` holds. `S` is the set of symbolic variables.
- **Formula.** A path condition, the solver's own term language. `expr_to_pc` reads a formula off an expression.
- **Fuel.** A bound on the depth of a derivation. `Fin n` allows depth `n`. `Inf` has no bound.
- **Law.** An assumption about an opaque solver function (`reduce-prim` or `cast`). Each law is a Rocq class, not an `Axiom`. `Model.v` proves every law.

When this document is not enough, section 11 tells you how to ask Rocq directly. Do that before you write a claim you are unsure of.

---

## 1. Status

- **The files in `_CoqProject` were last changed in commit `1267e5f`.** The `scratch/` suite was repaired for the new design in `8727495` and `cf4b7f6`, and this document was rewritten after that. All files build. No file in `_CoqProject` contains `Admitted`, `admit`, `Axiom` or `Parameter`.
- **`case` can now branch on an SMT boolean.** This is the large change since the last handoff. Section 3, item 11 describes it. It is what a compiled comparison needs, so the theorems now cover a branch whose guard is computed while the program runs.
- **The main theorems are closed.** `Print Assumptions` says "Closed under the global context" for each. The laws enter only as section arguments.
- **The laws have a model.** `Model.v` builds a concrete solver with `lit := bool`, real `and`, `not` and `ite`, and a reducer that simplifies. It proves every law.
- **Every theorem is non-vacuous.** `NonVacuity.v` checks, inside the model, that each theorem has an instance where all hypotheses hold and the conclusion says something. Its `RuntimeBranch` section holds a program whose guard is computed at run time; soundness and both completeness forms have instances there.
- **Two audits.** The first found four defects. The second, `REVIEW2`, found that the laws forbade realistic simplifiers, and that fix is done. Both defect lists are resolved except the open items in section 10.

Build:

```bash
for f in $(grep '\.v$' _CoqProject); do coqc -Q . SymCoreTheory "$f" || break; done
```

The file order is `SymCore.v`, `ConCore.v`, `CostLaws.v`, `Completeness.v`, `Model.v`, `Saturation.v`, `ApplicationRules.v`, `NonVacuity.v`. Each file builds in seconds.

---

## 2. File map

| File | Contents |
| --- | --- |
| `SymCore.v` | Syntax, the solver parameters (`SymCoreSorts`, `SymCoreSolver`), `Solvable`, `Comp`, `delay`, merge (`ite_leaf`, `ite`, `merge`), fuel, the judgements `eval` and `fold_alts`, the formula reader `expr_to_pc`, the formula helpers `pc_value`, `pc_has_var`, `pc_arities_ok`, `pc_closed_value`, `truth_constructor`, the bottom detector `mentions_out_of_fuel`, the model types `valuation` and `symvars`, fuel lemmas (`eval_inf_has_budget`, `eval_fin_zero_inv`) |
| `ConCore.v` | `concore_expr`, `concrete_env`, `scoped`/`closed_term`/`closed_program`, `sym_scoped`/`symbolic_program`, valuations and `models`, `denotes`/`denote`, the instance relation `contains`, most laws, alignment lemmas, `merge_keeps`, **soundness**, **concrete determinism**, **symbolic results agree** (`symbolic_results_share_the_instance`), the scope limit `branch_on_bound_variable_has_no_instance`, `budget_total`, the bundle `ConCoreLaws` |
| `CostLaws.v` | `contains_k` (instances indexed by symbolic overhead), `smt_size`, erasure lemmas, the cost laws, `merge_contains_k`, the bundle `SymFCCostLaws`, the scope limits `cast_of_symvar_is_not_branch` and `cast_of_smt_term_is_not_its_own_branch`, and the two bottom results `merge_folds_no_branch_that_ran_out_of_fuel` and `a_clean_value_can_come_from_a_derivation_that_ran_out_of_fuel` |
| `Completeness.v` | The completeness statements, the reachability relation `sym_step`/`sym_reach`, the SMT size bound `smt_terms_bounded`/`smt_bounded_run`, worked examples, and the proof: `eval_nested_ind`, `smt_eval_fin`, `good_at`, `forall_form`, and the three **completeness theorems** |
| `Model.v` | The concrete solver and proofs of every law (`model_laws`, `model_symfc_cost_laws`), and the obstruction `merged_branch_size_is_not_bounded_by_the_instance_index` |
| `Saturation.v` | The well-formedness condition "primitives are fully applied", its two laws, and preservation by evaluation |
| `ApplicationRules.v` | Regression lemmas for the application rules, and the obstruction to determinism at finite fuel |
| `NonVacuity.v` | Model instances of every theorem, the pruning solver, and the `RuntimeBranch` section |
| `scratch/*.v` | Counterexamples and worked examples. Section 9 lists them. |

---

## 3. What the paper's theory section must change

Each item is a defect in `theory.tex` that the formalization fixes. The file in brackets proves the defect or its fix. The paper must adopt each change, or it states something false.

1. **Drop WHNF.** WHNF in `theory.tex` is used only as App-Spine's premise `¬WHNF(Γ, e_f)`. That premise overlaps App-Cast, and it never fires on an applied branch. Replace it with the predicate `comp(Γ, e)` in section 4.2. The claim "evaluation reduces to WHNF" was never provable, because `reduce-prim` and `cast` are opaque. Drop that claim too. [`scratch/CastSplitWorkedExample.v`, `scratch/CastOverlapNotLambdaSpecific.v`]
2. **Add Rule App-If.** An application whose head is a branch has no rule in the paper. All-paths evaluation creates such terms. For example, `(case (if x then T else F) of T → λy.y; F → λz.z) l` gets stuck in the paper's rules. App-If pushes the **whole** argument spine into both arms. Pushing one argument at a time breaks soundness. [`ApplicationRules.v`: `branch_application_regression`; `scratch/AppIfPrimSpineUnsound.v`: `app_if_breaks_soundness`]
3. **Closures and constructor fields become thunks `(Γ, e)`.** The paper's Rule Con returns `D e⃗` without an environment, and `fold-alts` binds the fields in the `case`'s environment. That is dynamic scope: `(λy. case (λy. D y) A of D z → z) B` returns `B`. The fixes:
   - Rule Con wraps each field as a thunk.
   - A new Rule Thunk evaluates a thunk in its own environment.
   - Rule Lam returns `(Γ, λx.e)`, which is the same thunk form.
   - Field wrapping uses `delay`, which does not re-wrap a field that is already a thunk. Double wrapping breaks soundness.

   [`ConCore.v`: section `FieldsAreLexical`, `field_reader_reads_lexically`; `scratch/ConThunkFieldUnsound.v`; `scratch/AppIfPrimSpineUnsound.v`: `double_thunk_regression`]
4. **Constructor spines are values.** Only a bare `D` was a value in the paper, so `Just 5` could not be built or matched. [`scratch/ConstructorApplicationStuck.v`]
5. **Add Rule Sym-Var.** A variable that the environment does not bind is a symbolic value. Without this rule, no term that mentions a symbolic variable evaluates.
6. **Fuel is a real depth bound.** The judgement carries a bound. At bound 0 only Rule Out-Of-Fuel fires, and it returns a new bottom `⊥ₖ`, "bound exceeded". `⊥ₖ` is not a ConCore term, so no concrete value is an instance of it. If Out-Of-Fuel returned the paper's undefined value `?` instead, "complete at some bound" would hold trivially whenever the concrete value is `?`. [`scratch/FuelIndexFeasibility.v`, `scratch/DivergenceNeedsFuel.v`, `ApplicationRules.v`: `out_of_fuel_contains_nothing_concrete`]
7. **`fold-alts` details.**
   - A branch whose guard does not convert to a formula gives `?` (`FoldAlts_IfFail`).
   - The "otherwise" clause must also demand that the head of the scrutinee's spine is not a branch, that the scrutinee reads as no formula, and that it is not a primitive application. [`scratch/FoldAltsNoNestedIfIsFalse.v`, which must fail]
   - A pattern variable with no matching field is bound to `?`. [`ConCore.v`: `fieldless_reader_is_undefined`]
   - `fold-alts` spends no fuel.
8. **Merge's lambda clause.** The paper merges `λx.e₁` with `λx.e₂`. Evaluation never produces a bare lambda, only closures. The clause now merges two closures with the same environment and the same binder: `(Γ, λx.e₁)` and `(Γ, λx.e₂)` become `(Γ, λx. if c then e₁ else e₂)`.
9. **Applying a cast whose coercion does not split is stuck, on purpose.** No rule applies, on either side. [`scratch/OpaqueCastOperatorStuck.v`]
10. **Merging and folding.** Do not claim that `fold-alts` on a merged scrutinee equals `fold-alts` on the raw one. That claim is false. [`scratch/MergeIsNotThePapersIte.v`]
11. **`case` can branch on an SMT boolean.** This is new, and the paper has nothing like it. SymFC compiles a comparison into a `case` on a solver term: `(<) = convert .: ilt`, `convert v = ite v True False`, and `ite` is itself `case scrut of True → tr; False → fl`. So the scrutinee of a `case` can be a formula rather than a constructor. Rule Case now reads the scrutinee as a formula and answers by its shape.

   The table is what `case` does for each scrutinee, after merge has run on it:

   | Scrutinee, after merge | What `case` does | Rule |
   | --- | --- | --- |
   | a constructor spine `D e⃗` | takes the alternative for `D`, binding the fields | `FoldAlts_Con` |
   | a branch `if c then t else f`, where `c` reads as a formula | folds both arms, under `Φ ∧ c` and `Φ ∧ ¬c` | `FoldAlts_If` |
   | a branch whose guard reads as no formula | `?` | `FoldAlts_IfFail` |
   | a formula with no variable, such as `true` or `not true` | takes the `True` or the `False` alternative, by the formula's value | `FoldAlts_GroundFormula` |
   | a formula with a variable and the right arity everywhere, such as `and x y` | builds `if e then r₁ else r₂`, where `r₁` folds the `True` alternative under `Φ ∧ e` and `r₂` folds the `False` alternative under `Φ ∧ ¬e` | `FoldAlts_SymbolicFormula` |
   | a formula with a variable and a wrong arity, such as `and x y true` | stuck: no rule applies | — |
   | a primitive application that reads as no formula, such as `not (if x then true else false)` | stuck: no rule applies | — |
   | a bottom | the same bottom | `FoldAlts_Bot` |
   | anything else | `?` | `FoldAlts_Otherwise` |

   The two stuck rows are deliberate. They are the shapes for which no answer is sound, and getting stuck is the safe answer. The model's reducer never produces either shape. [`scratch/RuntimeBranchWitnessesClosed.v`; `NonVacuity.v` section `RuntimeBranch`]

---

## 4. Definitions to transcribe

### 4.1 Syntax additions

- A thunk `(Γ, e)` is an expression form (`EThunk Γ e`). A lambda closure is the thunk `(Γ, λx.e)`. There is no separate closure form.
- Bottoms are `raise e`, `∅` (unreachable, produced by Rule Prune), `?` (undefined behaviour) and `⊥ₖ` (bound exceeded, produced only by Rule Out-Of-Fuel).
- A program is ConCore when it has no symbolic branch (`concore_expr`) and every environment it carries is ConCore (`concrete_env`).

### 4.2 Solvable, spine head, computation, delay

- `solvable(Γ, e)` is unchanged from the paper: a literal, an unbound variable, or a primitive applied to solvable arguments.
- `head(e)` is the head of the application spine: `head(e_f e_a) = head(e_f)`, and `head(e) = e` otherwise.
- `comp(Γ, e)` holds exactly for:
  - a bound variable `x ∈ Γ`;
  - a lambda `λx.e`;
  - a `case`;
  - a thunk `(Γ', e)` whose body is not a lambda;
  - an application whose head is not a constructor `D`, a primitive `⊗`, or a branch `if`.
- `delay(Γ, e) = e` if `e` is a thunk, and `(Γ, e)` otherwise.

`comp` excludes every operator shape that has its own application rule. So no two application rules fire on the same term. [`ApplicationRules.v`: `comp_excludes_closure`, `comp_excludes_cast`, `comp_excludes_branch`, `comp_excludes_bottom`, `comp_excludes_whole_spine_head`]

### 4.3 The judgement `Φ; Γ ⊢ e ⇓ⁿ e'`

`n` is `Inf` or a natural number. Every rule except Out-Of-Fuel needs a live bound, and it passes the bound minus one to its premises. Rocq writes this `eval (Live f) … ` with premises at `dec f`. The judgement `⇓` without an index means `⇓^Inf`.

| Rule | Premises and conclusion |
| --- | --- |
| Var | `Γ(x) = (Γ', e)`, `Γ' ⊢ e ⇓ e'` gives `x ⇓ e'` |
| Sym-Var | `x ∉ Γ` gives `x ⇓ x` |
| Lit | `l ⇓ l` |
| Con | `e ≡ D e₁ … eₙ` gives `e ⇓ D delay(Γ,e₁) … delay(Γ,eₙ)` |
| Cast | `e ⇓ e'` gives `e ▷ γ ⇓ cast(e', γ)` |
| App-Abs | `Γ'{x ↦ (Γ, e_a)} ⊢ e_b ⇓ e_b'` gives `(Γ', λx.e_b) e_a ⇓ e_b'` |
| App-Spine | `comp(Γ, e_f)`, `e_f ⇓ e_f'`, `e_f' e_a ⇓ e_r` gives `e_f e_a ⇓ e_r` |
| App-Prim | `e_f e_a ≡ ⊗ e⃗` with `|e⃗| = arity(⊗)`, each `eᵢ ⇓ eᵢ'`, gives `e_f e_a ⇓ reduce-prim(⊗, e⃗')` |
| Lam | `λx.e ⇓ (Γ, λx.e)` |
| App-Cast | `γ = γ_a → γ_r`, `(e_f (e_a ▷ sym γ_a)) ▷ γ_r ⇓ e_r` gives `(e_f ▷ γ) e_a ⇓ e_r` |
| App-If | `e ≡ (if e_c then e_t else e_f) e₁ … eₙ` with `n ≥ 1`, `if e_c then (e_t e⃗) else (e_f e⃗) ⇓ e_r` gives `e ⇓ e_r` |
| App-Bot | `b e_a ⇓ b` |
| Bot | `b ⇓ b` |
| Case | `e_s ⇓ e_s'`, `fold-alts(Φ, Γ, merge(Γ, e_s'), a⃗) = e_r` gives `case e_s of a⃗ ⇓ e_r` |
| If | `e_c ⇓ e_c'`, `e_c'` converts to formula `pc`, `Φ∧pc ⊢ e_t ⇓ e_t'`, `Φ∧¬pc ⊢ e_f ⇓ e_f'` gives `if e_c then e_t else e_f ⇓ if e_c' then e_t' else e_f'` |
| Coercion, Type | substitution, as in the paper |
| Prune | `¬SAT(Φ)` gives `e ⇓ ∅` |
| Thunk | `Γ' ⊢ e ⇓ e'` gives `(Γ', e) ⇓ e'` |
| Out-Of-Fuel | `e ⇓⁰ ⊥ₖ`. It is the only rule at bound 0. |

**`fold-alts`.** It spends no fuel, and it has seven clauses. Section 3, item 11 gives the table; this is the same list written as rules.

| Clause | Premises and conclusion |
| --- | --- |
| `FoldAlts_Con` | `e ≡ D e⃗`, the alternative for `D` is `D x⃗ → e_p`, and `Γ{x⃗ ↦ e⃗} ⊢ e_p ⇓ e_r`, gives `e_r` |
| `FoldAlts_If` | `e_c` reads as formula `pc`; fold `e_t` under `Φ ∧ pc` and `e_f` under `Φ ∧ ¬pc`; gives `if e_c then e_t' else e_f'` |
| `FoldAlts_IfFail` | `e_c` reads as no formula, gives `?` |
| `FoldAlts_Bot` | a bottom gives the same bottom |
| `FoldAlts_GroundFormula` | `e` reads as formula `pc`, `pc` has no variable; fold `True` or `False` in place of `e`, chosen by the value of `pc`; gives that result |
| `FoldAlts_SymbolicFormula` | `e` reads as formula `pc`, `pc` has a variable, every primitive in `pc` has exactly its arity; `r₁` folds `True` under `Φ ∧ pc`, `r₂` folds `False` under `Φ ∧ ¬pc`; gives `if e then r₁ else r₂` |
| `FoldAlts_Otherwise` | `e` reads as no formula, `e` is no primitive application, the head of `e`'s spine is no branch, no alternative matches `e`, and `e` is no bottom; gives `?` |

The last two premises of `FoldAlts_Otherwise` are new and they matter. Without "reads as no formula" the rule would answer `?` for a boolean formula that the two new clauses resolve. Without "is no primitive application" it would answer `?` for a primitive application that reads as no formula, and that answer is unsound: the concrete instance of such a term can read as a formula and take an alternative. Getting stuck is the right answer there. [`scratch/NestedBranchScrutineeWitness.v`]

`True` and `False` above are the two data constructors `dcon_true` and `dcon_false` of `SymCoreSorts`. A formula's value picks between them through `truth_constructor`.

Merge is `merge(Γ, if c then e_t else e_f) = ite(Γ, c, e_t, e_f)`, and merge is the identity on any other term. `ite` follows the paper, with these clauses:

- constructors with the same name and arity: zip the fields under the branch;
- two solvable arms: `reduce-prim(ite, [c, e_t, e_f])`;
- two closures with the same environment and binder;
- equal bottoms, types or coercions;
- two casts with the same coercion: recurse into their bodies;
- otherwise: keep the branch.

The second clause is what turns a branch into a formula, so merge is the step that hands a runtime branch to Rule Case.

### 4.4 ConCore evaluation

`Γ ⊢ᶜ e ⇓ᶜ v` is the same judgement at `Inf` under the path condition `true` (`eval_con`). No separate concrete calculus exists.

### 4.5 The instance relation `contains σ S e_s e_c`

Most rules are structural congruence. The rules that are not:

- **`Cont_Var_Sym`.** A symbolic variable `x ∈ S` has the instance `σ(x)`.
- **`Cont_Var_Bound`.** A variable not in `S` stands for itself.
- **`Cont_If_True` / `Cont_If_False`.** A branch has the instance of the arm the model selects. The guard must denote a formula that the model satisfies (`models_cond`) or falsifies (`models_not_cond`). The other arm is never inspected.
- **`Cont_Denote`.** A saturated primitive term that mentions a variable has the instance of its literal value under `σ`. The relation is semantic on the SMT fragment and syntactic everywhere else. A purely syntactic relation forces `reduce-prim` never to compute. [`scratch/ReducePrimCannotComputeRepaired.v`]
- **`Cont_Thunk_Outer`.** If `e_s` contains a concrete thunk, then `(Γ, e_s)` contains that same thunk. This holds whenever `Γ` is related to some concrete environment. It makes an outer environment irrelevant around a term that already carries its own environment.
- **Binders.** Every binder in a related term must be outside `S`.

`contains_k σ S k e_s e_c` (in `CostLaws.v`) is the same relation, indexed by symbolic overhead `k`:

- Structural rules add the indices of their parts.
- A branch costs `1 + size(guard)`.
- An outer thunk costs `1`.
- `Cont_Denote` costs the size of the SMT term.

`contains_k_erase` and `contains_k_of_contains` show the two relations agree up to the index.

### 4.6 Other definitions

- **`budget_total Φ Γ e`.** There is an `h` such that for every `n ≥ h`, `e` has some value at `Fin n`. A looping term satisfies it, because it runs out of fuel. A stuck term does not.
- **`closed_program Γ e`.** Every environment is scoped, and every free variable of `e` is bound by `Γ`.
- **`symbolic_program S Γ e`.** The same condition for the symbolic side, with the symbolic variables allowed free. In plain words: every free variable of the program is either bound by the environment or is a symbolic variable of the run. It is written with `sym_scoped`, which is `scoped` plus the rule "a variable in `S` is in scope anywhere". With no symbolic variable the two agree (`sym_scoped_no_symvars`).

  Soundness and completeness need it because a program may not read a variable that is neither bound nor symbolic. Such a variable makes Rule Sym-Var fire, the value is that variable, and no concrete value is an instance of it. It is also what keeps a concrete run out of `FoldAlts_SymbolicFormula`: a closed scrutinee's formula mentions no variable (`expr_to_pc_scoped_no_var`), so a concrete run never builds a runtime branch.
- **`smt_bounded_run Φ Γ e`.** There is one number `bs` that bounds the size of every SMT term the run can build, from every state it can reach, at every bound. In Rocq: `sym_reach` is the reflexive transitive closure of `sym_step`, a step relation that covers every way evaluation moves from one `(Φ, Γ, e)` state to another; `smt_terms_bounded bs Φ Γ e` says that for every reachable state and every value that state has at any fuel, `smt_size (merge Γ' v) ≤ bs`; and `smt_bounded_run` says some such `bs` exists.

  In plain words: the program's SMT terms do not grow without limit as the bound grows. A program that builds a longer and longer formula on some path fails it. Completeness needs it, and section 10, item 4 says what it rules out.
- **`saturated e`.** Every primitive occurrence is fully applied. Section 8 explains it.

---

## 5. Solver parameters and laws

### 5.1 Parameters

The parameters are abstract. The SMT theory stays configurable through them.

- **`SymCoreSorts`:** literals, primitives, `and`/`not`/`ite`, `arity`, `prim_value` (the SMT meaning of a primitive on literals), `lit_true`, the two boolean data constructors `dcon_true` and `dcon_false`, type constructors, decidable equalities, and two equations that fix the meaning of `not` and `ite`:
  - `prim_value(not, [l]) = lit_true` exactly when `l ≠ lit_true`;
  - `prim_value(ite, [c, t, f]) = t` when `c = lit_true`, and `f` otherwise.

  These two equations describe the SMT theory, not the solver, which is why they sit beside `prim_value` rather than in a law class. Rule Case needs them: it reads the truth value of a merged boolean and must pick the arm the model takes.
- **`SymCoreSolver`:** `sat`, `pc_true`, `reduce_prim`, `cast_expr`, and the two substitutions.
- **`σ ⊨ Φ`:** defined as `pc_value σ Φ = lit_true`. It is a definition, not a law.

### 5.2 Laws in `ConCoreLaws`

| Law | Plain meaning | Why it exists |
| --- | --- | --- |
| `ReducePrimSolvable` | Solvable arguments give a solvable result | Guard evaluation stays in the SMT fragment |
| `ReducePrimSaturated` | A primitive-headed result is fully applied | Over-application stays stuck |
| `ReducePrimConcore`, `CastExprConcore` | ConCore inputs give ConCore outputs | Concrete runs stay concrete |
| `ReducePrimScoped`, `CastExprScoped` | Inputs in scope give a result in scope | Without them a lawful cast can invent a free variable and break soundness [`scratch/SoundnessNeedsScopeLaws.v`: `soundness_fails_without_cast_scoped`] |
| `ReducePrimKeepsOutOfFuel`, `CastExprKeepsOutOfFuel` | A result keeps `⊥ₖ` visible when an argument shows it | So that a spent budget cannot be laundered into a clean value. See section 10, item 10 |
| `ModelsSat` | A formula with a model is satisfiable | Rule Prune cannot fire on the model's path |
| `PrimValueAnd` | `and` means conjunction | Path conditions compose |
| `ReducePrimContains` | Related arguments give related results, **when the concrete arguments are closed** | The restriction lets a real simplifier satisfy the law [`scratch/ReducerLawsForbidSimplification.v`] |
| `ReducePrimDenote` | Reduction keeps the SMT value | `reduce-prim` may compute |
| `ReducePrimGroundValue` | A result with no variable is a literal | A ground result cannot stop half-reduced |
| `CastExprContains` | A cast keeps instances | Soundness of Rule Cast |
| `ReducePrimIteWellformed` | If the reduced `ite` reads as a well-formed formula, so does the arm the model takes | Rule Case reads the merged branch as a formula, and the arm it selects must be one too |
| `SubstCoercContainsEnv`, `SubstTypeContainsEnv` | Substitution keeps instances | Rules Coercion and Type |

**The scope laws are now stated for open terms.** They used to say "closed input gives closed output". They now say: if every free variable of the input is bound in a list `L` or is symbolic, the same holds of the output. The closed forms follow at once (`reduce_prim_scoped_closed`, `cast_expr_scoped_closed`), so the concrete side is unchanged. The open form is what the symbolic side needs, because a symbolic value is open by design: it mentions symbolic variables.

The open form is strictly stronger. A cast that wraps its argument in a thunk with an empty environment satisfies the closed form and breaks the open one, because the wrap hides the argument's bound variables. `scratch/ZipLeakCounterexample.v` used to do exactly that and had to be changed.

**The two `⊥ₖ` laws are in the bundle but no theorem uses them yet.** They were added for bounded soundness, which is still unproved. Section 10, item 10 says where that stands. Do not write in the paper that they buy anything today.

### 5.3 Cost laws in `SymFCCostLaws`

This bundle is `ConCoreLaws` plus two laws. Completeness needs them.

| Law | Plain meaning |
| --- | --- |
| `CastExprContainsK` | A cast keeps the overhead index exactly |
| `ReducePrimContainsK` | The result's overhead is at most the sum of the arguments' overheads, plus `prim_slack` of the concrete arguments |

In the paper, write these as: "`reduce-prim` and `cast` preserve instances without adding branching or indirection that the concrete run lacks."

**Why the cost laws exist.** Without them completeness is false. A lawful solver can read junk in an arm the model does not take and inflate the fuel cost of the value on the model's path. Two proofs of this are in scratch:

- `scratch/FuelInflationCounterexample.v`: `lawful_instance_refutes_target`.
- `scratch/ZipLeakCounterexample.v`: `branch_lawful_instance_refutes_target`. This one leaks the junk through merge's constructor zip.

**Read those two with care.** Both refute the completeness statements **without** the `smt_bounded_run` premise, and both fail that premise: their junk arm builds a tower of negations whose size grows with the bound. Each file states the premise-free form itself, as `target_completeness_unbounded` and friends. `FuelInflationCounterexample.v` also breaks `ReducePrimKeepsOutOfFuel`, and the file proves that (`fuel_reduce_prim_hides_the_spent_budget`), so its solver satisfies the rest of the bundle and not the whole of it. So the mechanized case for the cost laws is this: they are needed for completeness **without** a bound on SMT term size. Whether they are still needed once `smt_bounded_run` is assumed is open, and nobody has checked it.

**Why the slack depends on the arguments.** A constant slack is too strict. The model folds a concrete argument to a literal while the symbolic side keeps an SMT term. [`scratch/ReducePrimOverheadNeedsSlack.v`: `model_breaks_constant_slack`]

### 5.4 Saturation laws

These are in `Saturation.v`, not in any bundle.

- `ReducePrimKeepsSaturation` and `CastExprKeepsSaturation`.
- Only the saturation-preservation result uses them. No main theorem uses them.

### 5.5 Laws that were tried and removed

- **The ite axiom.** The old axiom `reduce_prim_ite_contains` made negation unsatisfiable, so no model could take an else-branch. [`scratch/NegationWasUnsatisfiable.v`]
- **The branch laws** (`ReducePrimBranch`, `CastExprBranch`) and **the ite-contains laws.** No theorem needed them. Some scratch files keep local copies of these classes.

### 5.6 The model

`Model.v` uses:

- `lit := bool`, with `dcon_true := "True"` and `dcon_false := "False"`;
- `sat := true`;
- casts erased and identity substitutions;
- a reducer that splits branches in its arguments, then simplifies:
  - `and false z → false`, `and z false → false`;
  - `ite true a b → a`, `ite false a b → b`;
  - `ite c a a → a`;
  - ground terms fold to literals;
  - otherwise a residual term.

`reflexivity` checks the rewrites (`model_and_false_left`, `model_ite_same_arms`). `model_symfc_cost_laws` proves every law, including the three new ones.

---

## 6. The theorems

Each statement below is exact, apart from notation. Check it with `Check` (section 11) before you transcribe it.

### 6.1 Concrete determinism: `concore_eval_deterministic` (`ConCore.v`)

> If `Γ` is a ConCore environment, `e` is a ConCore program, and `closed_program Γ e` holds, then `Γ ⊢ᶜ e ⇓ᶜ v₁` and `Γ ⊢ᶜ e ⇓ᶜ v₂` imply `v₁ = v₂`.

This is the determinism theorem of the paper.

It rests on four laws only: `ReducePrimConcore`, `CastExprConcore`, `ReducePrimScoped` and `CastExprScoped`. Soundness needs every law in `ConCoreLaws` except the two `⊥ₖ` laws, and completeness needs all of `SymFCCostLaws`.

The closedness premise is new. It is needed twice: a free variable would let Rule Var and Rule Sym-Var both fire, and a closed scrutinee's formula mentions no variable, so `FoldAlts_SymbolicFormula` cannot fire on a concrete run. `concore_eval_deterministic_top` is the whole-program corollary: it asks for `concore_expr e` and `closed_term e` in the empty environment.

Limits:

- **Unlimited bound only.** At a finite bound it does not follow from the laws. A run that exceeds the bound can pass `⊥ₖ` into `cast`, and the laws say nothing about non-ConCore input. [`ApplicationRules.v`: `bounded_concrete_determinism_fails`. Its assumptions are two `cast` equations and one unsatisfiable guard.]
- **Symbolic evaluation is not deterministic.** Rule Prune may give `∅` or the ordinary value on an infeasible path, and it does so by design. [`NonVacuity.v`: `pm_symbolic_evaluation_not_deterministic`, `scratch/EvalNotDeterministic.v`] Do not claim symbolic determinism. It is not expected: SymCore exists to find ConCore values.

**Proof structure.** Induction on the first derivation (`eval_det_fix`) with inversion on the second.

- The rules do not overlap: `comp` excludes every other operator shape.
- Prune cannot fire, because the path condition is `true` and ConCore has no branch.
- App-If cannot fire, because a ConCore spine has no branch head.
- The environment must be ConCore too. Otherwise Rule Var reaches a branch. [`scratch/ConcoreDeterminismRestricted.v`]

### 6.2 Soundness: `concore_soundness` (`ConCore.v`)

> Let `σ ⊨ Φ`. Assume:
> - `contains_env σ S Γs Γc`;
> - `contains σ S e_s e_c`;
> - `e_c` is ConCore;
> - `closed_program Γc e_c`;
> - `symbolic_program S Γs e_s`;
> - `Φ; Γs ⊢ e_s ⇓ v_s`.
>
> Then there is a `v_c` with `Γc ⊢ᶜ e_c ⇓ᶜ v_c` and `contains σ S v_s v_c`.

In plain words: whatever the symbolic run produces, every concrete instance also runs, and the symbolic result covers the concrete result. The laws needed are those in `ConCoreLaws` except the two `⊥ₖ` laws.

`symbolic_program` is the new hypothesis. Section 4.6 says what it means and why it is needed.

**Proof structure.** Induction on the **symbolic** derivation at `Inf`, as mutually recursive fixpoints over `eval` and `fold_alts` (`concore_soundness_fix`). The plain induction principle is too weak, because App-Prim has a `Forall2` premise and Case nests `fold_alts`. On paper, write "induction on derivation height, stated simultaneously for `fold-alts`". Key lemmas:

- **Alignment:** the concrete term takes the matching rule (`comp_contains`, `contains_spine_if`, `contains_app_if_spine`, `contains_unspool_primop`, `contains_unspool_con`, `contains_delay`).
- **Merge:** merge keeps the instance, or both sides are scrutinees that no alternative matches (`merge_keeps`).
- **Closedness:** evaluation of a closed program stays closed (`closed_eval`); evaluation of a symbolic program stays symbolic (`sym_eval_scoped_fix`).
- **Guards:** a guard's truth value survives evaluation (`eval_models_cond`, `eval_denote`).
- **Formula scrutinees:** the new fold clauses need the model's reading of the merged formula to line up with the concrete side, which is what `ReducePrimIteWellformed` and the two `prim_value` equations give.

### 6.3 Completeness (`Completeness.v`, section `CompletenessUnderCostLaws`, laws `SymFCCostLaws`)

`concore_completeness_budget : target_completeness`:

> Let `σ ⊨ Φ`. Assume:
> - `contains_env σ S Γs Γc`;
> - `contains σ S e_s e_c`;
> - `e_c` is ConCore;
> - `closed_program Γc e_c`;
> - `symbolic_program S Γs e_s`;
> - `smt_bounded_run Φ Γs e_s`;
> - `budget_total Φ Γs e_s`;
> - `Γc ⊢ᶜ e_c ⇓ᶜ v_c`.
>
> Then there is an `h` such that for every `n ≥ h` there is a `v_s` with `Φ; Γs ⊢ e_s ⇓ⁿ v_s` and `contains σ S v_s v_c`.

`concore_completeness_forall : forall_form_lemma` is the stronger form, and it needs no `budget_total`:

> Under the same hypotheses, except `budget_total`: there is an `h` such that for every `n ≥ h`, **every** `v_s` with `Φ; Γs ⊢ e_s ⇓ⁿ v_s` satisfies `contains σ S v_s v_c`.

`concore_completeness_exists : existential_corollary`:

> Under the hypotheses of `concore_completeness_budget`: there are `k` and `v_s` with `Φ; Γs ⊢ e_s ⇓ᵏ v_s` and `contains σ S v_s v_c`.

In plain words: if the concrete run ends, then every large enough bound gives a symbolic result that covers it. There are now three extra hypotheses beside the instance ones: `symbolic_program`, `smt_bounded_run` and `budget_total`. Divergence is allowed, including in arms the model does not take and in branches created while the program runs.

**About the bound.** `h` is not the concrete run's depth. It grows with the concrete derivation and with the symbolic overhead:

- `true` has a value at depth 1;
- `if x then true else true` has none at depth 1.

[`scratch/SameDepthCompletenessIsFalse.v`] The user accepted this. The rebuttal's "complete up to a recursion bound" is still true, but the paper must not say "the same bound".

**Why the upward-closed form, and why `⊥ₖ`.** With "some `k`" only and Out-Of-Fuel returning `?`, the theorem would hold trivially at `k = 0` whenever `v_c = ?`. The separate `⊥ₖ` removes that. The upward-closed form also matches iterative deepening.

**Proof structure.**

- **Induction.** Induction on the **concrete** derivation, using the principle `eval_nested_ind`, which has an IH for each App-Prim argument.
- **Invariant.** The invariant `good_at` holds for index bounds `bk` and `be`. It says: there are `h` and `K` such that every symbolic derivation at `n ≥ h`, from a term related with overhead at most `bk` in an environment with overhead at most `be`, gives a value related with overhead at most `K`.
- **Bounds.** `h` and `K` depend only on the concrete derivation and on `bk` and `be`. They never depend on a symbolic intermediate value, because that value changes with `n`.
- **Symbolic-only steps.** Branch and outer-thunk layers are peeled by strong induction on `bk`.
- **Guards.** A denoting guard evaluated at `n > size` gives its unbounded value (`smt_eval_fin`).
- **Opaque functions.** `merge_contains_k` bounds merge, and the cost laws bound `reduce-prim` and `cast`.
- **Runtime branches.** When a `case` builds `if e then r₁ else r₂`, the overhead of that value grows with the size of `e`, and nothing in the instance index bounds it. `smt_bounded_run` is what supplies the missing bound. `sym_ok` carries it through the induction, alongside `sym_state_scoped`.
- **Combining.** The ∀-form gives the budget form: `budget_total` supplies a derivation, and the ∀-form says it is good.

**What `budget_total` excludes.** It excludes only programs that get stuck somewhere evaluation goes. After App-If, a stuck term is ill-typed or a primitive applied to the wrong number of arguments. [`Completeness.v`: `budget_total_fails_on_stuck_arm`; `scratch/CompletenessNeedsFuel.v`] Rule Prune can rescue a stuck arm on an infeasible path. [`NonVacuity.v`: `pm_completeness_instance`, `pm_plain_model_not_budget_total`]

### 6.4 Symbolic results agree: `symbolic_results_share_the_instance` (`ConCore.v`)

This is an optional corollary, not a main theorem. Concrete determinism (section 6.1) is the determinism theorem of the paper. Use this corollary only if the text needs to say that pruning never changes an answer.

> Let `σ ⊨ Φ`. Assume:
> - `contains_env σ S Γs Γc`;
> - `contains σ S e_s e_c`;
> - `e_c` is ConCore;
> - `closed_program Γc e_c`;
> - `symbolic_program S Γs e_s`;
> - `Φ; Γs ⊢ e_s ⇓ v₁` and `Φ; Γs ⊢ e_s ⇓ v₂`.
>
> Then there is a `v_c` with `Γc ⊢ᶜ e_c ⇓ᶜ v_c`, `contains σ S v₁ v_c` and `contains σ S v₂ v_c`.

In plain words: two symbolic results of the same term can differ only on paths that no model takes. Under every model that satisfies the path condition, both give the same concrete answer.

Limits:

- **Unlimited bound only**, like soundness.
- **It does not make concrete determinism trivial.** Its proof applies soundness twice, and then concrete determinism makes the two concrete values equal.

**Proof.** Soundness gives `v_c₁` for `v₁` and `v_c₂` for `v₂`. The environment `Γc` is ConCore (`contains_env_concrete`) and closed. Concrete determinism gives `v_c₁ = v_c₂`.

---

## 7. How the design was forced

Read these before writing prose. Each one is a place where the obvious statement is false.

| Tempting statement | Why it is false | File |
| --- | --- | --- |
| Completeness needs no hypothesis | A stuck untaken arm blocks Rule If | `scratch/CompletenessNeedsFuel.v` |
| A bound is not needed | A looping untaken arm blocks Rule If at `Inf` | `scratch/DivergenceNeedsFuel.v` |
| `Fin 0` means "no fuel" | In the old encoding `Fin 0` contained every level | `scratch/FuelIndexFeasibility.v`: `old_fin_zero_is_not_a_bound` |
| A bigger bound keeps the value | Lowering the bound loses derivations, and raising it can too | `SymCore.v`: `lowering_the_bound_loses_derivations` |
| Rule Con can return its spine | Fields are then read in the wrong scope | `ConCore.v` section `FieldsAreLexical` |
| App-If can push one argument | It splits a primitive spine | `scratch/AppIfPrimSpineUnsound.v` |
| `delay` needs no outer-thunk rule in `contains` | A branch of thunks is wrapped differently on each side | `scratch/ConThunkFieldUnsound.v` |
| The solver laws allow any SMT simplifier | Only once `ReducePrimContains` is restricted to closed concrete arguments | `scratch/ReducerLawsForbidSimplification.v` |
| Opaque functions only need to keep instances | They can inflate fuel cost | `scratch/FuelInflationCounterexample.v`, `scratch/ZipLeakCounterexample.v` |
| Casts keep closedness automatically | A lawful cast can invent a free variable | `scratch/SoundnessNeedsScopeLaws.v` |
| Merge then fold equals fold | The guard is read before or after evaluation | `scratch/MergeIsNotThePapersIte.v` |
| A `case` may treat a cast of a boolean as a branch | A lawful cast can turn a literal into a formula, and can turn a formula into one whose instance is not a formula | `scratch/FormulaScrutineeCastWitness.v` |
| A `case` may read any primitive application as a formula | A lawful cast can leave a branch inside a primitive; the symbolic side then reads no formula while its instance does | `scratch/NestedBranchScrutineeWitness.v` |
| A merged branch may be scrutinised with no scope condition | The untaken arm can be a variable that is neither bound nor symbolic, and then the merged formula denotes nothing | `scratch/MergedBranchUntakenArmWitness.v` |
| A runtime branch's size is bounded by the instance index | Merge makes a formula as large as you like from an instance of index 2 | `Model.v`: `merged_branch_size_is_not_bounded_by_the_instance_index` |
| A clean value means the derivation had budget left | A lawful cast can drop a field that held `⊥ₖ` | `CostLaws.v`: `a_clean_value_can_come_from_a_derivation_that_ran_out_of_fuel` |
| The theorems cover no code that branches on a computed SMT value | They do now; see section 10, item 4 for what is still open | `NonVacuity.v` section `RuntimeBranch` |
| A counterexample from a bounded run is guaranteed | A cast that hides `⊥ₖ` can turn it into `true` | `scratch/BoundedSoundnessFailsUnderLaws.v` |

### 7.1 The four attempts at `case` on an SMT boolean

Four designs were tried. Three were refuted by a Rocq witness, and each witness copies the judgement it refutes into its own file, so the witnesses still stand. Do not repeat these.

1. **Attempt 1: a cast of a boolean is a branch.** The idea was that `case (e ▷ γ) of True → …; False → …` could treat the cast as making a branch on `e`. Two lawful casts break it. One turns the literal `true` into `not true`, a closed formula that is not a literal, so the "branch" is on something the design did not expect. The other turns the formula `and x y` into `and x y true`, a formula with the wrong arity, while the concrete instance `and true false true` reads as no formula at all. So the symbolic and the concrete side disagree. [`scratch/FormulaScrutineeCastWitness.v`: `negating_cast_gives_closed_formula_scrutinee`, `applying_cast_splits_formula_from_its_instance`]
2. **Attempt 2: read every primitive application as a formula, and answer `?` when it reads as none.** A lawful cast can leave a branch inside a primitive: `not (if x then true else false)`. That term reads as no formula, so the design answered `?`. Its concrete instance is `not true`, which reads as the ground formula `not true` and takes the `False` alternative. `?` does not cover a constructor, so soundness fails. The fix is the "is no primitive application" premise on `FoldAlts_Otherwise`: such a scrutinee is now stuck, not undefined. [`scratch/NestedBranchScrutineeWitness.v`: `proposed_design_breaks_soundness`]
3. **Attempt 3: fold a merged branch with no scope condition.** The program `case (if x then true else y) of …`, with `y` free and not symbolic, merges to the formula `ite x true y`. Under a model that takes the `true` arm, the concrete side is `case true of …` and answers the `True` alternative. The symbolic side builds a runtime branch whose guard mentions `y`, and that guard denotes no formula in an environment that binds `y`, so the branch has no instance. Soundness fails. The fix is `symbolic_program`, which rejects the program outright. [`scratch/MergedBranchUntakenArmWitness.v`: `approved_design_breaks_soundness_in_the_model`]
4. **Attempt 4, the one that is implemented.** Two clauses, split by whether the formula mentions a variable, and with the arity condition on the symbolic one; everything else stuck. `scratch/RuntimeBranchWitnessesClosed.v` runs the three refuting programs against it: the first agrees with its instance, the second and third are stuck, and the fourth is excluded by `symbolic_program` and agrees once its free variable is symbolic.

---

## 8. Well-formedness: saturated primitives

**Decision.** The user chose not to add a rule for partially applied primitives. The paper instead states that SymCore programs write every primitive with all its arguments. For example, `and true` is written `λy. and true y`.

**What `Saturation.v` proves:**

- `eval_preserves_saturation` and `fold_alts_preserves_saturation`: evaluation at any bound keeps a saturated program saturated. This uses the two saturation laws.
- `saturated_prim_app_meets_arity`: a saturated primitive application has exactly the arity.
- `evaluated_prim_app_stuck_only_if_over_applied`: a stuck primitive application reached from a saturated program is over-applied.

**Examples** (`scratch/SaturationExamples.v`):

- `(λf. f true) (and true)` is not saturated (`partial_program_not_saturated`).
- Its eta-expansion is saturated and satisfies `budget_total` (`eta_program_budget_total`, `eta_branch_budget_total`).

**Limit.** Saturation does not exclude over-application such as `(λf. f true) (and x x)`. That program is ill-typed and fails `budget_total` (`over_applied_program_not_budget_total`). So the paper may say: for saturated, well-typed programs, `budget_total` excludes nothing that terminates on every path. Say it in prose. No theorem states it, because the development has no type system.

**Branch arms.** A branch passes its argument count to its arms: `(if c then and x else not) y` counts as saturated. The model's branch lifting needs this.

**A saturated program can still be stuck at a `case`.** The two stuck rows of the table in section 3, item 11 are about the scrutinee's shape, not about arity in the program text. A cast can produce them. The model's reducer does not.

---

## 9. Scratch files

The suite command:

```bash
for f in scratch/*.v; do coqtop -q -Q . SymCoreTheory -batch -l "$f" >/dev/null 2>&1 && echo "PASS $f" || echo "FAIL $f"; done
```

Exactly five files fail today:

- **`FoldAltsNoNestedIfIsFalse.v` fails on purpose.** Its last proof tries to apply `FoldAlts_Otherwise` to a scrutinee whose spine head is a branch. The spine-head premise rejects it, and that rejection is the regression check.
- **`Audit.v`, `ReducePrimCannotCompute.v`, `prim.v`, `prim2.v`** used to fail on purpose, as results before the repairs. They now also fail because signatures changed. None of them carries a "must fail" marker, so treat them as historical.

Every other file must pass. If one of the five starts to pass, look at why.

The files about `case` on an SMT boolean:

- `FormulaScrutineeCastWitness.v`, `NestedBranchScrutineeWitness.v`, `MergedBranchUntakenArmWitness.v` refute attempts 1, 2 and 3. Section 7.1 says how.
- `RuntimeBranchWitnessesClosed.v` is new. It runs those three programs against the `fold_alts` the development has, and shows none of them breaks anything. Its five theorems are `a_ground_formula_scrutinee_agrees_with_its_instance`, `a_branch_inside_a_primitive_is_stuck`, `a_wrong_arity_formula_is_stuck`, `a_free_untaken_arm_is_not_a_symbolic_program` and `a_symbolic_untaken_arm_agrees_with_its_instance`. Both of its witness solvers satisfy the whole of `SymFCCostLaws`.

`BoundedSoundnessFailsUnderLaws.v` is the witness for section 10, item 10. It no longer builds a full `SymFCCostLaws` instance: its cast is what `CastExprKeepsOutOfFuel` forbids, and the file proves that (`bot_cast_hides_the_spent_budget`) alongside every other cast law it still satisfies.

Older files whose names describe their result:

- `CaptureWitness`, `ConatIsWorse`, `EvalModelsCondVerdict`, `FuelGuardControls`;
- `OperatorRestrictionPreservation`, `OpaqueCastOperatorReachable`, `OpaqueCastOperatorStuck`;
- `ConcoreDeterminismRestricted`, `ReducePrimCannotComputeRepaired`;
- `RepairAudit`, `AuditAfterRepair`, `assum`.

Read a file's theorem names with `grep -n '^Theorem\|^Lemma' scratch/<file>.v`.

---

## 10. Open items and honest limits

1. **The scope laws are settled.** `ReducePrimScoped` and `CastExprScoped` say that `reduce-prim` and `cast` do not create free variables, and they now say it for open terms. The user accepted them as common sense for any real solver. `CastExprScoped` is proved necessary (`scratch/SoundnessNeedsScopeLaws.v`). `ReducePrimScoped` is kept by analogy.
2. **Determinism holds only at `Inf`**, and only for closed concrete runs. Section 6.1 explains why.
3. **`merge_keeps` is weaker than "merge never loses an instance".** Merging can lose the instance of a variable outside `S`. No theorem needs the strong form, and the paper must not claim it.
4. **Runtime branches are covered, with three narrow limits and one semantic hypothesis.** A runtime branch is a symbolic branch whose guard is computed while the program runs, for example the comparison of a symbolic key inside `Map.insert`. The paper's first example, `mapLookupInsert`, needs one.

   **What is covered.** `NonVacuity.v` section `RuntimeBranch` holds the program `(λa. case (and a y) of True → true; False → false) x`, with `x` and `y` symbolic. Its guard `and a y` is built while the program runs, out of a variable the lambda binds. `rb_runtime_branch_fires` shows `FoldAlts_SymbolicFormula` firing on it. `rb_every_bounded_value_branches` shows that at every bound the value is either `⊥ₖ` or a branch, so the branch is not an accident of one bound. Soundness has an instance (`rb_soundness_instance`), and so do both completeness forms (`rb_completeness_budget_instance`, `rb_completeness_forall_instance`). The hypotheses hold: `rb_contains`, `rb_symbolic_program`, `rb_smt_bounded`.

   So the paper may now say that the theorems cover code that branches on a value computed at run time. The residual limits are these, and they must be stated:

   - **A branch written as `if` in the source, with a guard bound by a lambda, still has no instance.** `λx. if x then e_t else e_f` has no instance under any model (`ConCore.v`: `branch_on_bound_variable_has_no_instance`; `scratch/BoundGuardHasNoInstance.v` shows that the model evaluates it). So a source program must reach a runtime branch through `case` on a solver term, which is what SymFC's compilation of a comparison does, and not through a bare `if` on a bound variable.
   - **A branch created by a cast is still ruled out.** `CastExprContainsK` makes a cast keep the overhead index exactly, and a branch adds overhead. So a cast of a symbolic variable is never a branch (`CostLaws.v`: `cast_of_symvar_is_not_branch`), and a cast of an SMT term `t` is never `if t then D₁ else D₂` (`cast_of_smt_term_is_not_its_own_branch`).
   - **A solver that leaves a branch inside a primitive application makes such a `case` stuck.** That is the second stuck row of the table in section 3, item 11. Getting stuck is the sound answer, and `scratch/NestedBranchScrutineeWitness.v` shows that any other answer is not. The model's reducer never produces this shape, because it splits branches out of its arguments first.
   - **Completeness needs `smt_bounded_run`, a second semantic hypothesis beside `budget_total`.** In plain words it rules out a program whose SMT terms grow without limit as the bound grows: a loop that keeps conjoining one more comparison onto a guard, so that at bound `n` the formula has about `n` operators. It does not rule out ordinary divergence, and it does not rule out a program that builds a large but fixed formula.

     The unconditional version — completeness with no bound on SMT term size — is open. Two mechanized obstructions say why it is hard. `Model.v`: `merged_branch_size_is_not_bounded_by_the_instance_index` builds, for any `B`, a branch whose instance has index 2 and whose merged formula has size at least `B`, so that every instance of the resulting runtime branch has index at least `B`. The completeness proof carries exactly such an index bound, and this says no function of the instance index can supply it. `CostLaws.v`: `a_clean_value_can_come_from_a_derivation_that_ran_out_of_fuel` builds a lawful cast that drops a constructor field, so a run that spent its budget still answers a clean literal while the unbounded run has no value at all. Together they say that neither the index nor the value tells you the run was well behaved, so the bound has to come from somewhere else. `smt_bounded_run` is where it comes from now.
5. **Several laws only make sense relative to ConCore or closed input.** `bounded_concrete_determinism_fails` shows the laws leave `cast` free on input that contains `⊥ₖ`.
6. **`sat` is constantly true in the main model.** `NonVacuity.v` adds `pruning_solver` so that Rule Prune is exercised.
7. **Stale comments may remain** in `SymCore.v` and `ConCore.v`. Before quoting a comment, check it against the code. Search with `grep -n 'WHNF\|EClos\|progressive\|solver_free\|Section 12.5'`.
8. **The paper describes `contains` as a Boolean relation.** In the development it is a `Prop` relation with a semantic rule for SMT terms. Describe it as a relation.
9. **The worked examples at the top of `Completeness.v`** sit in a section with only `ConCoreLaws`, and they predate the cost laws. The model instances in `NonVacuity.v` are the ones to cite.
10. **No soundness theorem covers a bounded run.** Soundness needs a run at `Inf`, and such a run exists only when every path ends, including paths no model takes (`NonVacuity.v`: `nv_symbolic_run_diverges`). The tool reports counterexamples from bounded runs. The laws do not make those counterexamples real.

    The last handoff suggested a fix: add a law that `cast` and `reduce-prim` keep `⊥ₖ` visible. **That fix is now in place.** `ReducePrimKeepsOutOfFuel` and `CastExprKeepsOutOfFuel` are fields of `ConCoreLaws`, the model proves both, and `scratch/BoundedSoundnessFailsUnderLaws.v` shows that they are exactly what its `⊥ₖ`-hiding cast breaks.

    **Bounded soundness itself is still unproved.** No theorem uses the two laws yet. `CostLaws.v` has two partial results towards it: `merge_folds_no_branch_that_ran_out_of_fuel` says merge never folds away a term that shows `⊥ₖ`, and `a_clean_value_can_come_from_a_derivation_that_ran_out_of_fuel` says the laws still allow a clean value from a spent budget, because a cast may drop a whole field. So the paper must not say "guaranteed counterexample" of a bounded run unless the tool re-runs the counterexample concretely.

---

## 11. How to get more context from Rocq

Do not recompile a whole file to test an idea. Compile the development once, then write a small probe file that imports it.

```bash
for f in $(grep '\.v$' _CoqProject); do coqc -Q . SymCoreTheory "$f" || break; done
mkdir -p probe
```

`probe/P.v`:

```coq
From SymCoreTheory Require Import SymCore ConCore CostLaws Completeness Model Saturation ApplicationRules NonVacuity.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

Check @concore_soundness.
Print Assumptions concore_completeness_budget.
Print eval.
Print contains.
Search contains_k merge.
```

```bash
coqtop -q -Q . SymCoreTheory -batch -l probe/P.v
```

If the command prints nothing for a proof you wrote, Rocq accepted it. Any error names a line. `probe/` is in `.gitignore`.

### Useful commands

- `Check name.` prints the statement of `name`. Use `@name` to see the implicit arguments, including the law classes.
- `Print name.` prints a definition or inductive, for example `Print Comp.`, `Print ite_leaf.` or `Print ConCoreLaws.`
- `Print Assumptions name.` lists what a result rests on. "Closed under the global context" means no axiom.
- `Search pattern.` finds lemmas, for example `Search budget_total.` or `Search (contains _ _ (EIf _ _ _) _).`
- `Locate "⇓".` shows what a notation means.

### Checking a claim you are about to write

- **"Is this true?"** State it as a `Lemma` in a probe inside a section with `Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.` Try to prove it.
- **"Is this false?"** Prove its negation. For a claim about all solvers, prove the negation inside a concrete instance, the way the scratch counterexamples do. Copy the model from `Model.v`, and see `scratch/RuntimeBranchWitnessesClosed.v` for a short local `SymFCCostLaws` instance.
- **Look at a goal before writing a tactic.** Put `Show.` at the point where you are stuck and end the proof with `Abort.` Run coqtop and read the goal and hypothesis names. Never guess tactics and recompile repeatedly; that burns time and tokens.

### Traps

- The notation `Φ ; Γ ⊢ e ⇓ v` means `eval Inf Φ Γ e v`. It clashes with `;` inside `pose proof (...)` and inside list literals `[a; b]`. Write `pose proof (...) as H` and `a :: b :: nil`.
- In `match goal` patterns, write `eval _ Φ Γ e v` and `EmptyEnv`, not the notation and not `·`.
- `destruct` or `induction` on an `eval Inf` hypothesis generalises the bound, and Out-Of-Fuel returns as a case. Use `remember`, or the tactics `inf_destruct` and `inf_induction` in `ConCore.v`. `inversion` keeps the term's shape and is usually what you want instead.
- You cannot predict hypothesis names after `inversion`. Read them from `Show`.
- Inverting a `fold_alts` now gives seven cases, not five. Two of them, `FoldAlts_GroundFormula` and `FoldAlts_SymbolicFormula`, apply to a scrutinee of any shape, so they are not dropped by unification. Kill them with the `expr_to_pc … = Some …` premise.
- In a model instance, literals may need their sort written out, as in `@ELit model_sorts true`.
- The laws are section arguments. A lemma stated outside a section that provides them will not find them.

---

## 12. Suggested order for the paper rewrite

1. Fix the calculus figures using sections 3 and 4:
   - syntax with thunks and `⊥ₖ`;
   - `comp` in place of WHNF;
   - the rule table;
   - `fold-alts`, including the two boolean-formula clauses, and merge.
2. Add a short "solver assumptions" paragraph listing the laws of section 5 in plain words, with the model as evidence that they are consistent.
3. Define ConCore, instances (`contains`), `symbolic_program`, `smt_bounded_run`, `budget_total` and saturation.
4. State determinism, soundness and completeness as in section 6.
5. Before the completeness statement, present the stuck-arm counterexample. Then present the looping-arm example, which shows why the bound is needed.
6. Present the runtime-branch example from `NonVacuity.v` after the theorems, and state the residual limits of section 10, item 4 honestly.
7. Write the proofs by following the proof structures in section 6. Check every lemma you rely on with `Check`.
