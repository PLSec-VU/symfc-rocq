# Rocq Tracks the WHNF Paper: Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Rewrite the Rocq development so that its syntax, evaluation and three theorems
match the theory section of the paper. In that section, expressions and values in weak
head normal form are separate grammars.

**Architecture:** Expressions lose `EIf` and `EThunk` and gain a symbolic variable
`ESym`. Values, primitives and thunks become their own mutual types. Evaluation is one
mutual inductive family: `eval`, `apply`, `prim`, `force`, `select` and `fold_alts`.
Branch lifting in that family spends no fuel. So the leaf that the model selects runs in
lock step with the concrete run at the same fuel, and soundness and completeness are both
proved by a lock-step induction. The cost-index machinery of the old completeness proof is
deleted.

**Tech Stack:** Rocq 9.0.1, Stdlib. The toolchain is in the opam switch `default`, so
run `eval $(opam env --switch=default)` first. Build with
`rocq makefile -f _CoqProject -o Makefile && make -j8`.

**Spec:** `/Users/octeep/workspace/pantostuff/pantomime-symbex-paper/src/theory.tex`.
Its changes are uncommitted. The spec is §3.1–3.4, Figs. 2–6. Ignore `appendix.tex`.

## Global Constraints

- Every proof ends in `Qed` or `Defined`. Run `grep -rnE "Admitted|admit|Axiom|Parameter" theories`: the output must be empty.
- Before writing a tactic, inspect the goal. Compile once. Then write a probe file that
  imports the module, put `Show.` at the failing point, end it with `Abort.`, and run
  `coqtop -q -Q theories SymCoreTheory -batch -l probe.v`. Never guess a tactic and
  recompile.
- Notation traps:
  - The `;` in the eval notation `Φ ; Γ ⊢ e ⇓ v` clashes with the `;` of `pose proof`
    and of list literals. Write `eval Inf Φ Γ e v` in those places.
  - Never write `eval _` inside `match goal` patterns.
- Comments are defects (the user's global CLAUDE.md). Name things so that they need no
  comment. The prose proof sketches go in `docs/proof-sketches.md` (Task 9), not in `.v`
  files.
- Keep these public names: `concore_eval_deterministic`, `concore_soundness`,
  `concore_completeness_budget`, `concore_completeness_forall`,
  `concore_completeness_exists` and `model_laws`.
- The theorem statements below are fixed. If a proof needs a stronger hypothesis, stop
  and report to the user. Do not add the hypothesis quietly.
- After each task, `make -j8` must finish with no error on the files that `_CoqProject`
  lists at that point.
- Commit after each task on branch `claude/pantomime-symbex-formalization-ac1cbf`. End
  each message with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.

## Decisions Taken from the Spec

| Spec | Rocq |
| --- | --- |
| `s` (symbolic variable) | `ESym : var -> expr` and `PSym : var -> prim` |
| Value `p`, closure, `D t⃗`, `⊗ t⃗`, `τ`, `γ`, `v ⊲ γ`, `b`, `if p then v else v` | `VPrim`, `VClos`, `VCon`, `VPartial`, `VType`, `VCoercion`, `VCast`, `VBot`, `VIf` |
| Thunk `(Γ, e)`, `if p then t else t` | `TSusp`, `TIf` |
| Path condition `Φ ::= p` | `path_condition := prim` |
| `prim` saturated case for any `⊗` other than `ite` | forces every argument, then calls the pure function `lift_prim`, which calls the opaque `reduce_prim` on each leaf. See Task 0. |
| `ite(p, v_t, v_f)` (Fig. 6) | `ite : prim -> value -> value -> value` in `Merge.v` |
| ConCore | no `ESym`, no `⊥ₖ`, no `∅`, no `VIf`/`TIf`, no `PSym` |

Two choices that the spec leaves open:

1. **Instance relation `I-Denote`.** Rocq drops the paper's side condition that the term
   "has symbolic variables". `ite` can merge two primitives under a condition that
   contains no variable. The merged term must then still relate to its literal value. See
   Review Focus item 1.
2. **Completeness drops "bounded SMT terms".** That hypothesis existed because the old
   rules spent fuel on SMT terms. The new rules do not, so the theorem is stated without
   it. If the proof fails without it, stop and report.

Report both choices to the user after Task 6, so that the paper can follow.

## Review Focus

1. **Merging under a condition with no variable.** `ite (PLit true) (VPrim a) (VPrim b)`
   must relate to the concrete value of `a`. Test: `merge_ground_condition_keeps` in
   Task 5.
2. **A partial primitive application that never gets all its arguments.** `(⊗ loop)`
   must not evaluate `loop`. Test: `partial_prim_is_lazy` in Task 8.
3. **A constructor with fewer fields than the pattern has binders.** The extra binders
   are bound to `?`, and extra fields are dropped. Test: `missing_field_is_undefined` in
   Task 8.
4. **Applying a cast whose coercion is not an arrow.** No rule applies, so evaluation is
   stuck and does not return a bottom. Test: `non_arrow_cast_app_stuck` in Task 3.
5. **A solver that prunes leaves the model does not take.** Soundness and completeness
   must still hold. Test: `pruning_model_laws : ConCoreLaws` in Task 8. The theorems then
   apply to this solver.

---

### Task 0: Make the paper's `prim` force every argument of a primitive other than `ite`

**Files:**
- Modify: `/Users/octeep/workspace/pantostuff/pantomime-symbex-paper/src/theory.tex`.
  Change the third case of `prim` in Fig. 3 and the Rules paragraph.

symfc forces every argument of every primitive except `ite` (in `WHNF.hs`, only
`IteOp` uses `PThunk`). So `reduce-prim` can stay a pure function on values.

- [ ] **Step 1:** Replace the case `reduce-prim^n(Φ, ⊗ t⃗)` with
  `reduce-prim(⊗ v⃗)` under `where v_i := force^n(Φ, t_i)`. Keep its condition
  `|t⃗| = arity(⊗) otherwise`.
- [ ] **Step 2:** In the Rules paragraph, replace "which forces the arguments the
  primitive needs; the primitive ite is the one exception, which prim handles itself" with
  "after forcing every argument; the primitive ite is the one exception, which forces only
  what it selects".
- [ ] **Step 3:** Run `make` in the paper repo. Expect exit code 0, no `^!` line in
  `target/main.log`, and no undefined reference. Do not commit, because the paper repo is
  the user's to commit.

### Task 1: Syntax and solver interface

**Files:**
- Rewrite: `theories/SymCore/Syntax.v`
- Create: `theories/SymCore/Solver.v`
- Delete: `theories/SymCore/SideConditions.v` and `theories/SymCore/SolvableFacts.v`
- Modify: `_CoqProject`. It lists only `Syntax.v` and `Solver.v` for now. Later tasks
  append their files.
- Delete every other `.v` file under `theories/`, because each later task writes its file
  again. Git history keeps the old versions.

**Interfaces (Produces):**

```coq
Class SymCoreSorts : Type := {
  lit : Set; primop : Set; op_and : primop; op_not : primop; op_ite : primop;
  primop_arity : primop -> nat; op_ite_arity : primop_arity op_ite = 3%nat;
  lit_eq_dec; primop_eq_dec; tycon : Set; tycon_eq_dec;
  prim_value : primop -> list lit -> lit; lit_true : lit;
  prim_value_and : forall a b, prim_value op_and [a; b] = lit_true <-> a = lit_true /\ b = lit_true;
  prim_value_not : forall l, prim_value op_not [l] = lit_true <-> l <> lit_true;
  prim_value_ite : forall c t f, prim_value op_ite [c; t; f] = if lit_eq_dec c lit_true then t else f }.

Inductive expr := EVar (x : var) | ESym (s : var) | ELit (l : lit) | EPrimOp (op : primop)
  | ECon (d : dcon) | EApp (f a : expr) | ELam (x : var) (b : expr) | ECase (e : expr) (alts : list alt)
  | ECast (e : expr) (γ : coercion) | ECoercion (γ : coercion) | EType (τ : type_fc) | EBot (b : bottom)
with bottom := BRaise (e : expr) | BUnreachable | BUndefined | BOutOfFuel
with alt := Alt (d : dcon) (xs : list var) (e : expr).

Inductive prim := PLit (l : lit) | PSym (s : var) | PApp (op : primop) (args : list prim).

Inductive value := VPrim (p : prim) | VClos (Γ : env) (x : var) (b : expr)
  | VCon (d : dcon) (ts : list thunk) | VPartial (op : primop) (ts : list thunk)
  | VType (τ : type_fc) | VCoercion (γ : coercion) | VCast (v : value) (γ : coercion)
  | VBot (b : bottom) | VIf (p : prim) (vt vf : value)
with thunk := TSusp (Γ : env) (e : expr) | TIf (p : prim) (tt tf : thunk)
with env := EmptyEnv | ExtendEnv (x : var) (t : thunk) (rest : env).

Definition path_condition := prim.
Definition pc_and (a b : prim) := PApp op_and [a; b].
Definition pc_not (a : prim) := PApp op_not [a].
lookup_env : env -> var -> option thunk
extend_env : env -> var -> thunk -> env
bind_fields : env -> list var -> list thunk -> env
  (* x_i ↦ t_i; a binder with no field ↦ TSusp EmptyEnv (EBot BUndefined); extra fields dropped *)
find_alt : dcon -> list alt -> option (list var * expr)
is_plit : prim -> bool
type_fc, role, coercion, sym_coerc, decomp_coerc_arrow   (* unchanged from the old Syntax.v *)
```

Also define the Boolean equality tests `prim_eqb`, `value_eqb`, `thunk_eqb`, `env_eqb`
and `bottom_eqb`, with their `*_eqb_eq` soundness lemmas, in the style of the old
`expr_eqb`. `ite` needs them.

`Solver.v`:

```coq
Class SymCoreSolver := {
  sat : path_condition -> bool;
  pc_true : path_condition;  sat_pc_true : sat pc_true = true;
  reduce_prim : primop -> list prim -> value;
  cast_value : value -> coercion -> value;
  subst_coerc : env -> coercion -> coercion;
  subst_type : env -> type_fc -> type_fc }.
```

- [ ] **Step 1:** Write `Example lookup_shadow : lookup_env (ExtendEnv "x" t1 (ExtendEnv "x" t2 EmptyEnv)) "x" = Some t1 := eq_refl.` Write it for arbitrary sorts, using `Section` variables `t1 t2 : thunk`.
- [ ] **Step 2:** Write `Example bind_fields_missing : lookup_env (bind_fields EmptyEnv ["a"; "b"] [t1]) "b" = Some (TSusp EmptyEnv (EBot BUndefined)).`
- [ ] **Step 3:** Implement the definitions above. Run `make -j8`. Expect success.
- [ ] **Step 4:** Commit with message `rewrite syntax around WHNF values`.

### Task 2: Merge and primitive lifting

**Files:**
- Rewrite: `theories/SymCore/Merge.v`

**Interfaces:**
- Consumes: Task 1.
- Produces:
  - `ite : prim -> value -> value -> value`
  - `merge : value -> value`
  - `lift_prim : primop -> list value -> value`
  - `zip_tif : prim -> list thunk -> list thunk -> list thunk`

`ite p vt vf` follows Fig. 6. Test the clauses in this order:

1. `VCon` with the same `d` and the same length gives `VCon d (zip_tif p ts1 ts2)`.
2. `VPartial` with the same `op` and the same length gives `VPartial op (zip_tif …)`.
3. `VPrim a`, `VPrim b` gives `VPrim (PApp op_ite [p; a; b])`.
4. `VCast v1 γ1`, `VCast v2 γ2` with the same `coerc_src` and `coerc_dst` gives
   `VCast (ite p v1 v2) γ1`. Recurse on `vt` as the old `ite` did.
5. Two equal bottoms, two equal types or two equal coercions give that one item.
6. Anything else gives `VIf p vt vf`.

`merge (VIf p vt vf) = ite p vt vf`, and `merge v = v` otherwise.

`lift_prim op vs` scans `vs` from left to right:

- A `VBot b` gives `VBot b`.
- A `VIf p a b` gives `ite p (lift_prim op (… a …)) (lift_prim op (… b …))`, with the
  same position replaced.
- A `VPrim` is collected.
- Any other value gives `VBot BUndefined`. This is symfc's `unwrap` mismatch.
- When every value is a `VPrim`, the result is `reduce_prim op ps`.

Write it as an outer `Fixpoint` on the remaining list with an inner `fix` on the head
value, so that Rocq accepts the termination.

- [ ] **Step 1:** Write these tests, with sorts and solver as section variables:
  - `Lemma ite_con_merges : ite p (VCon d [t1]) (VCon d [t2]) = VCon d [TIf p t1 t2].`
  - `Lemma ite_clos_stays : ite p (VClos Γ x b) (VClos Γ x b) = VIf p (VClos Γ x b) (VClos Γ x b).`
  - `Lemma lift_prim_bottom_leaf : lift_prim op [VIf s (VBot BUndefined) (VPrim y)] = ite s (VBot BUndefined) (reduce_prim op [y]).`
- [ ] **Step 2:** Implement. Run `make -j8`. Expect success.
- [ ] **Step 3:** Commit with message `merge and primitive lifting on values`.

### Task 3: Evaluation

**Files:**
- Rewrite: `theories/SymCore/Eval.v`, `theories/SymCore/Inversion.v` and `theories/SymCore/Budget.v`

**Interfaces:**
- Consumes: Tasks 1 and 2.
- Produces: `fuel`, `Inf`, `Fin`, `dec` (unchanged from the old `Eval.v`), and this mutual
  `Inductive`:
  - `eval : fuel -> path_condition -> env -> expr -> value -> Prop`
  - `apply : fuel -> path_condition -> env -> value -> expr -> value -> Prop`
  - `prim_app : fuel -> path_condition -> primop -> list thunk -> value -> Prop`
  - `force : fuel -> path_condition -> thunk -> value -> Prop`
  - `select : fuel -> path_condition -> value -> thunk -> thunk -> value -> Prop`
  - `fold_alts : fuel -> path_condition -> env -> value -> list alt -> value -> Prop`
- Notations: `Φ ; Γ ⊢ e ⇓ v := eval Inf Φ Γ e v` and
  `Γ ⊢ᶜ e ⇓ᶜ v := eval Inf pc_true Γ e v`.

Constructors. `f` is a `live_fuel` in each `eval` conclusion `Live f`. Every
non-`eval` relation runs at the fuel `g` that it receives.

| Name | Premises | Conclusion |
| --- | --- | --- |
| `Eval_Var` | `lookup_env Γ x = Some t`, `force (dec f) Φ t v` | `eval (Live f) Φ Γ (EVar x) v` |
| `Eval_Lit` | – | `… (ELit l) (VPrim (PLit l))` |
| `Eval_Sym` | – | `… (ESym s) (VPrim (PSym s))` |
| `Eval_Con` | – | `… (ECon d) (VCon d [])` |
| `Eval_Prim` | `prim_app (dec f) Φ op [] v` | `… (EPrimOp op) v` |
| `Eval_App` | `eval (dec f) Φ Γ ef vf`, `apply (dec f) Φ Γ vf ea v` | `… (EApp ef ea) v` |
| `Eval_Lam` | – | `… (ELam x b) (VClos Γ x b)` |
| `Eval_Cast` | `eval (dec f) Φ Γ e v` | `… (ECast e γ) (cast_value v γ)` |
| `Eval_Bot` | – | `… (EBot b) (VBot b)` |
| `Eval_Case` | `eval (dec f) Φ Γ es vs`, `fold_alts (dec f) Φ Γ (merge vs) alts v` | `… (ECase es alts) v` |
| `Eval_Coercion` / `Eval_Type` | – | `… (VCoercion (subst_coerc Γ γ))` / `… (VType (subst_type Γ τ))` |
| `Eval_Prune` | `sat Φ = false` | `… e (VBot BUnreachable)` |
| `Eval_OutOfFuel` | – | `eval Spent Φ Γ e (VBot BOutOfFuel)` |
| `Apply_Con` | – | `apply g Φ Γ (VCon d ts) e (VCon d (ts ++ [TSusp Γ e]))` |
| `Apply_Clos` | `eval g Φ (extend_env Γ' x (TSusp Γ e)) b v` | `apply g Φ Γ (VClos Γ' x b) e v` |
| `Apply_Prim` | `prim_app g Φ op (ts ++ [TSusp Γ e]) v` | `apply g Φ Γ (VPartial op ts) e v` |
| `Apply_Cast` | `decomp_coerc_arrow γ = Some (γa, γr)`, `apply g Φ Γ v' (ECast e (sym_coerc γa)) v` | `apply g Φ Γ (VCast v' γ) e (VCast v γr)` |
| `Apply_Bot` | – | `apply g Φ Γ (VBot b) e (VBot b)` |
| `Apply_If` | `apply g Φ Γ vt e vt'`, `apply g Φ Γ vf e vf'` | `apply g Φ Γ (VIf p vt vf) e (ite p vt' vf')` |
| `Prim_Partial` | `length ts < primop_arity op` | `prim_app g Φ op ts (VPartial op ts)` |
| `Prim_Ite` | `force g Φ tc c`, `select g Φ c tt tf v` | `prim_app g Φ op_ite [tc; tt; tf] v` |
| `Prim_Reduce` | `op <> op_ite`, `length ts = primop_arity op`, `Forall2 (force g Φ) ts vs` | `prim_app g Φ op ts (lift_prim op vs)` |
| `Force_Susp` | `eval g Φ Γ e v` | `force g Φ (TSusp Γ e) v` |
| `Force_If` | `force g Φ tt vt`, `force g Φ tf vf` | `force g Φ (TIf p tt tf) (ite p vt vf)` |
| `Select_True` | `force g Φ tt v` | `select g Φ (VPrim (PLit lit_true)) tt tf v` |
| `Select_False` | `l <> lit_true`, `force g Φ tf v` | `select g Φ (VPrim (PLit l)) tt tf v` |
| `Select_Sym` | `is_plit p = false`, `force g (pc_and Φ p) tt vt`, `force g (pc_and Φ (pc_not p)) tf vf` | `select g Φ (VPrim p) tt tf (ite p vt vf)` |
| `Select_Bot` | – | `select g Φ (VBot b) tt tf (VBot b)` |
| `Select_If` | `select g Φ ct tt tf vt`, `select g Φ cf tt tf vf` | `select g Φ (VIf p ct cf) tt tf (ite p vt vf)` |
| `Fold_Con` | `find_alt d alts = Some (xs, ep)`, `eval g Φ (bind_fields Γ xs ts) ep v` | `fold_alts g Φ Γ (VCon d ts) alts v` |
| `Fold_Bot` | – | `fold_alts g Φ Γ (VBot b) alts (VBot b)` |
| `Fold_If` | `fold_alts g (pc_and Φ p) Γ vt alts vt'`, `fold_alts g (pc_and Φ (pc_not p)) Γ vf alts vf'` | `fold_alts g Φ Γ (VIf p vt vf) alts (ite p vt' vf')` |
| `Fold_Otherwise` | `no_alt_matches v alts` | `fold_alts g Φ Γ v alts (VBot BUndefined)` |

`no_alt_matches v alts` is `find_alt d alts = None` when `v` is `VCon d _`. It is
`False` when `v` is a `VBot` or a `VIf`, and `True` otherwise.

`Inversion.v` holds one inversion lemma per expression form, for `eval (Live f)`. Write
each lemma when a later task first needs it. `Budget.v` proves
`eval_inf_has_budget : Φ ; Γ ⊢ e ⇓ v -> exists h, forall n, h <= n -> eval (Fin n) Φ Γ e v`,
with mutual versions for the five other relations.

- [ ] **Step 1:** Write `Lemma non_arrow_cast_app_stuck : decomp_coerc_arrow γ = None -> ~ apply g Φ Γ (VCast v γ) e v'.`
- [ ] **Step 2:** Write `Lemma eval_spent : eval Spent Φ Γ e v -> v = VBot BOutOfFuel.`
- [ ] **Step 3:** Implement `Eval.v`, `Inversion.v` and `Budget.v`. Run `make -j8`. Expect success.
- [ ] **Step 4:** Commit with message `evaluation as eval/apply/prim/force/select/fold_alts`.

### Task 4: ConCore and determinism

**Files:**
- Rewrite: `theories/ConCore/Programs.v`, `theories/ConCore/Preservation.v` and `theories/ConCore/Determinism.v`

**Interfaces:**
- Produces:
  - `concore_expr : expr -> Prop` (no `ESym`, no `BOutOfFuel`, no `BUnreachable`)
  - `concrete_value`, `concrete_thunk`, `concrete_env` (no `VIf`, no `TIf`, no `PSym`,
    no `BOutOfFuel`, no `BUnreachable`, and every `VPrim` is a `PLit`)
  - The laws `ReducePrimLiteral` and `CastConcore` (below)
  - `concore_eval_deterministic`

```coq
Class ReducePrimLiteral : Prop := reduce_prim_literal : forall op ls,
  length ls = primop_arity op -> reduce_prim op (map PLit ls) = VPrim (PLit (prim_value op ls)).
Class CastConcore : Prop := cast_concore : forall v γ, concrete_value v -> concrete_value (cast_value v γ).

Theorem concore_eval_deterministic : forall Γ e v1 v2,
  concrete_env Γ -> concore_expr e -> Γ ⊢ᶜ e ⇓ᶜ v1 -> Γ ⊢ᶜ e ⇓ᶜ v2 -> v1 = v2.
```

- [ ] **Step 1:** State `eval_preserves_concrete`, a mutual lemma over the six relations at
  any fuel and with `Φ = pc_true`. Concrete input gives a concrete output.
- [ ] **Step 2:** State `concore_eval_deterministic`.
- [ ] **Step 3:** Prove both. `Eval_Prune` cannot fire, by `sat_pc_true`. `Select_Sym`
  cannot fire, because every concrete `VPrim` is a literal.
- [ ] **Step 4:** Run `make -j8`. Expect success.
- [ ] **Step 5:** Commit with message `ConCore preservation and determinism`.

### Task 5: Instance relation and soundness

**Files:**
- Rewrite: `theories/Soundness/Instance.v`, `theories/Soundness/MergeKeeps.v`, `theories/Soundness/Soundness.v` and `theories/Soundness/Laws.v`
- Delete: `theories/Soundness/Alignment.v`

**Interfaces:**
- Produces:
  - `valuation := var -> lit`
  - `prim_denote σ : prim -> lit`
  - `models σ p := prim_denote σ p = lit_true`, with notation `σ ⊨ p`
  - Mutual relations `contains_prim σ`, `contains_expr σ`, `contains_alt σ`,
    `contains_bottom σ`, `contains_val σ`, `contains_thunk σ` and `contains_env σ`. Each
    is symbolic first, concrete second. There is no `symvars` argument.
  - The laws below, `ConCoreLaws` (a bundle in the style of the old `Laws.v`) and
    `concore_soundness`.

Rules:

- `contains_prim`:
  - `PLit l ⊒ PLit l`
  - `PSym s ⊒ PLit (σ s)`
  - Denote: `length ps = primop_arity op` and `prim_denote σ (PApp op ps) = l` give
    `PApp op ps ⊒ PLit l`.
- `contains_expr`: congruence on every form, plus `ESym s ⊒ ELit (σ s)`.
- `contains_val`, `contains_thunk` and `contains_env`:
  - Congruence: the same constructor with related fields, and the same keys in
    environments.
  - `VIf p vt vf ⊒ v` when `σ ⊨ p` and `vt ⊒ v` (IfT), and when `σ ⊨ pc_not p` and
    `vf ⊒ v` (IfF). `TIf` has the same two rules.

Laws:

```coq
Class ModelsSat : Prop := models_sat : forall σ Φ, σ ⊨ Φ -> sat Φ = true.
Class ReducePrimContains : Prop := reduce_prim_contains : forall σ op ps ls,
  length ps = primop_arity op -> Forall2 (contains_prim σ) ps (map PLit ls) ->
  contains_val σ (reduce_prim op ps) (VPrim (PLit (prim_value op ls))).
Class CastContains : Prop := cast_contains : forall σ vs vc γ,
  contains_val σ vs vc -> contains_val σ (cast_value vs γ) (cast_value vc γ).
Class SubstContains : Prop := {
  subst_type_contains : forall σ Γs Γc τ, contains_env σ Γs Γc -> subst_type Γs τ = subst_type Γc τ;
  subst_coerc_contains : forall σ Γs Γc γ, contains_env σ Γs Γc -> subst_coerc Γs γ = subst_coerc Γc γ }.
(* ConCoreLaws bundles ReducePrimLiteral, CastConcore, ModelsSat, ReducePrimContains, CastContains, SubstContains *)

Theorem concore_soundness : forall Φ Γs Γc σ e_s e_c v_s,
  σ ⊨ Φ -> contains_env σ Γs Γc -> contains_expr σ e_s e_c ->
  concore_expr e_c -> concrete_env Γc ->
  Φ ; Γs ⊢ e_s ⇓ v_s ->
  exists v_c, Γc ⊢ᶜ e_c ⇓ᶜ v_c /\ contains_val σ v_s v_c.
```

- [ ] **Step 1:** In `MergeKeeps.v`, state these lemmas:
  - `ite_keeps : σ ⊨ p -> contains_val σ vt vc -> contains_val σ (ite p vt vf) vc`
  - `ite_keeps_false`, the same with `σ ⊨ pc_not p` and `vf`
  - `merge_keeps`
  - `lift_prim_keeps`: if `Forall2 (contains_val σ) vs_s vs_c` and every `vs_c` is
    concrete, then `contains_val σ (lift_prim op vs_s) (lift_prim op vs_c)`
  - `merge_ground_condition_keeps : contains_val σ (ite (PLit lit_true) (VPrim a) (VPrim b)) (VPrim (PLit (prim_denote σ a)))`
- [ ] **Step 2:** Prove them. The primitive clause of `ite` uses `prim_value_ite` and the
  Denote rule.
- [ ] **Step 3:** In `Soundness.v`, state `lockstep_sound`. It is a mutual lemma over the
  six symbolic relations at fuel `Inf`. Each symbolic derivation from related inputs
  gives a concrete derivation from the related concrete inputs, with `pc_true`, and the
  two results are related. When the input is a `VIf` or a `TIf`, follow only the leaf
  that `σ` selects. Then derive `concore_soundness`.
- [ ] **Step 4:** Prove it. Rule out `Eval_Prune` with `models_sat`. `Select_Sym` and
  `Fold_If` keep `σ ⊨ pc_and Φ p` through `prim_value_and`.
- [ ] **Step 5:** Run `make -j8`. Expect success. Commit with message `instance relation and soundness`.

### Task 6: Completeness

**Files:**
- Rewrite: `theories/Completeness/Statement.v` and `theories/Completeness/Completeness.v`
- Delete: `Cost.v`, `Reach.v`, `SmtCost.v`, `Induction.v`, `Closures.v`, `Spines.v` and `Cases.v` under `theories/Completeness/`

**Interfaces:**
- Produces:

```coq
Definition budget_total Φ Γ e := exists h, forall n, h <= n -> exists v, eval (Fin n) Φ Γ e v.

Theorem concore_completeness_forall : forall Φ Γs Γc σ e_s e_c v_c,
  σ ⊨ Φ -> contains_env σ Γs Γc -> contains_expr σ e_s e_c ->
  concore_expr e_c -> concrete_env Γc -> Γc ⊢ᶜ e_c ⇓ᶜ v_c ->
  exists h, forall n, h <= n -> forall v_s, eval (Fin n) Φ Γs e_s v_s -> contains_val σ v_s v_c.

Theorem concore_completeness_budget : forall Φ Γs Γc σ e_s e_c v_c,
  σ ⊨ Φ -> contains_env σ Γs Γc -> contains_expr σ e_s e_c ->
  concore_expr e_c -> concrete_env Γc -> budget_total Φ Γs e_s -> Γc ⊢ᶜ e_c ⇓ᶜ v_c ->
  exists h, forall n, h <= n -> exists v_s, eval (Fin n) Φ Γs e_s v_s /\ contains_val σ v_s v_c.

Corollary concore_completeness_exists : (* same hypotheses *) …
  exists k v_s, eval (Fin k) Φ Γs e_s v_s /\ contains_val σ v_s v_c.
```

- [ ] **Step 1:** State `lockstep_complete`. It is a mutual lemma over the six concrete
  relations at any fuel `g` and with `pc_true`. Each concrete derivation, together with
  any symbolic derivation at the same `g` from related inputs, gives related results.
  Induct on the concrete derivation. For a `VIf` or `TIf` symbolic input, induct on its
  structure and follow the leaf that `σ` selects.
- [ ] **Step 2:** Prove it. At `Spent`, both sides are `VBot BOutOfFuel`.
- [ ] **Step 3:** Derive `concore_completeness_forall` from `eval_inf_has_budget` (which
  gives the concrete run at every `Fin n`, `n ≥ h`) and `lockstep_complete`. Then derive
  `concore_completeness_budget` by taking the maximum of the two thresholds, and the
  corollary from it.
- [ ] **Step 4:** Run `make -j8`. Expect success. Commit with message `completeness by lock step`.

### Task 7: Model

**Files:**
- Rewrite: `theories/Model/Reducer.v` and `theories/Model/Model.v`
- Delete: `theories/Model/Lifting.v`, `theories/Model/ReducerLaws.v` and `theories/Model/CostLaws.v`

**Interfaces:**
- Produces: `model_sorts` and `model_solver`, plus `model_laws : ConCoreLaws`.
- Sorts: Boolean literals, and the primitives `PAnd`, `PNot` and `PIte`, as in the old
  `Reducer.v`.
- `reduce_prim op ps` is `VPrim (PLit (prim_value op ls))` when `ps = map PLit ls` and
  the length is the arity. It is `VPrim (PApp op ps)` otherwise.
- `sat _ = true`
- `cast_value v γ = VCast v γ`
- `subst_* _ x = x`

- [ ] **Step 1:** State `#[export] Instance model_laws : ConCoreLaws.`
- [ ] **Step 2:** Prove each law. `ReducePrimContains` uses the Denote rule when some
  argument is not a literal.
- [ ] **Step 3:** Run `make -j8`. Expect success. Commit with message `model satisfies the laws`.

### Task 8: Non-vacuity

**Files:**
- Rewrite: `SelfApplication.v`, `SoundnessInstances.v`, `LoopingArm.v`, `PruningModel.v` and `RuntimeBranch.v` under `theories/NonVacuity/`
- Create: `theories/NonVacuity/FromJust.v`

Each file builds a closed program in the model. It discharges every hypothesis of the
theorem it targets, and it shows a conclusion that is a literal or a constructor.

- `SelfApplication.v`: `ω := (λx. x x)(λx. x x)`. Prove
  `self_app_no_value : ~ exists v, EmptyEnv ⊢ᶜ ω ⇓ᶜ v` and `self_app_budget_total`.
- `SoundnessInstances.v`: soundness applied to `ESym`, to a `TIf` binding and to a
  primitive that computes. Include `instances_distinguish : ~ contains_val σ (VPrim (PLit true)) (VPrim (PLit false))`.
- `LoopingArm.v`: `case (ite s True ω)` where `σ s = true`. Completeness gives `True`.
- `RuntimeBranch.v`: `ite (and s₁ s₂) e₁ e₂`, with `Select_Sym` used, through both theorems.
- `PruningModel.v`: a solver whose `sat` returns `false` on `PLit false`. Prove
  `pruning_model_laws : ConCoreLaws`, and prove that `app_lit_stuck : ~ exists v, eval (Fin 2) pc_true EmptyEnv (EApp (ELit true) (ELit true)) v`.
- `FromJust.v`: `m` is bound to `TIf s (TSusp · (ECon Nothing)) (TSusp · (EApp (ECon Just) (ESym y)))`,
  `x := case m of {Nothing → raise; Just z → z}`, and `r := not x`. Prove
  `from_just_budget_total`. Prove `from_just_complete`, where completeness gives
  `VPrim (PLit (negb (σ y)))` under `σ s = false`. Also prove
  `partial_prim_is_lazy : eval (Fin 3) pc_true EmptyEnv (EApp (EPrimOp PAnd) ω) (VPartial PAnd [TSusp EmptyEnv ω])`
  and `missing_field_is_undefined : eval (Fin 3) pc_true EmptyEnv (ECase (ECon "Just") [Alt "Just" ["z"] (EVar "z")]) (VBot BUndefined)`.
  Build `r` without `let`, as `EApp (EPrimOp PNot) (ECase (EVar "m") alts)`.

- [ ] **Step 1:** Write all the statements above.
- [ ] **Step 2:** Prove them.
- [ ] **Step 3:** Run `make -j8`. Expect success. Commit with message `non-vacuity witnesses`.

### Task 9: Entry points and documentation

**Files:**
- Rewrite: `theories/Theorems.v` (the `Check` and `Print Assumptions` lines for the five
  theorems and for `model_laws`), `README.md` (the theorem table and the file tables) and
  `_CoqProject` (final list)
- Create: `docs/proof-sketches.md`. It has one section per theorem, in the README's prose
  style, and it replaces the appendix proofs.
- Delete: `paper-drift.md`

- [ ] **Step 1:** Run `make -j8`. Expect success. Expect each `Print Assumptions` to list
  only the section context (sorts, solver and laws), or `Closed under the global context`.
- [ ] **Step 2:** Run `grep -rnE "Admitted|admit|Axiom|Parameter" theories`. Expect no output.
- [ ] **Step 3:** Commit with message `entry points, README and proof sketches`.
