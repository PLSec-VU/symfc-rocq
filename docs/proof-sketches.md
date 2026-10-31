# Proof sketches

This file explains the main proofs in plain words. Each section names the Rocq theorem and the file that holds it.

## Terms used here

- An expression is a program text. A value is the result of a run, in weak head normal form (WHNF). WHNF means that the outermost shape is known. A value has one of these shapes: a primitive value (a literal or a formula), a closure, a constructor with its fields, a partial application of a primitive, a type, a coercion, a cast, a bottom or a symbolic branch.
- A symbolic branch is a value of the form "if p then a else b". The formula `p` may depend on symbolic variables.
- A model `σ` gives a literal to each symbolic variable. The notation `σ ⊨ Φ` means that `σ` makes the path condition `Φ` true. A path condition is a formula that records the branches taken so far.
- A derivation is the proof tree of a run. Fuel bounds the depth of nested `eval` derivations. Each `eval` rule gives its premises one unit of fuel less. The other five relations pass the fuel on unchanged. A run at fuel `Fin n` has at most `n` nested `eval` derivations. When the fuel is spent, the run gives the out-of-fuel bottom `VBot BOutOfFuel`, which is a value. A run at fuel `Inf` has no bound.
- The relation `contains_val σ v_s v_c` means that the symbolic value `v_s`, read under `σ`, stands for the concrete value `v_c`. This is the instance relation. The relations `contains_expr`, `contains_thunk` and `contains_env` are its versions for expressions, thunks and environments.
- A concrete run is a run with path condition `pc_true` on a concrete program (`concore_expr`) and a concrete environment (`concrete_env`).
- Evaluation is defined by six mutually dependent relations: `eval`, `apply`, `prim_app`, `force`, `select` and `fold_alts`. They cover expressions, function application, primitive operations, thunk forcing, symbolic branch selection and case alternatives.

## Concrete determinism

Theorem: `concore_eval_deterministic`, in `theories/ConCore/Determinism.v`.

Let `Γ` be a concrete environment (hypothesis `concrete_env Γ`). Let `e` be a concrete program (hypothesis `concore_expr e`). If `e` has two concrete runs in `Γ`, the two runs give the same value.

The proof is one mutual induction over the six relations. The tool is `eval_mut_ind`. The induction runs at any fuel, with path condition `pc_true`. The proof shows that each relation is a function of its inputs. This is the lemma `eval_functional`.

Concrete values never contain a symbolic branch. So the rules that need a symbolic branch cannot fire. Of the rules that remain, any two that can apply to the same input are disjoint. Their premises contradict each other. So, for each input, at most one rule fires, and the induction hypotheses show that its outputs are equal.

## Soundness

Theorem: `concore_soundness`, in `theories/Soundness/Soundness.v`.

Assume a symbolic run of `e_s` gives `v_s`. Assume `σ ⊨ Φ` and that `e_s` contains `e_c`. Assume also that `contains_env σ Γs Γc` holds (the symbolic environment contains the concrete one), that `e_c` is a concrete program (`concore_expr e_c`) and that `Γc` is a concrete environment (`concrete_env Γc`). The symbolic run is at fuel `Inf`. Then `e_c` has a concrete run, and its value `v_c` is contained in `v_s`.

The proof is the lemma `lockstep_sound`. It is an induction on the symbolic run, over the same six relations. It holds at every fuel, and both runs use the same fuel. The theorem uses it at fuel `Inf`.

The symbolic run may lift a computation over a symbolic branch. Lifting spends no fuel. At each such branch, the model `σ` selects one leaf. That leaf runs step by step with the concrete run, so both runs have the same fuel. The induction hypothesis for the selected leaf gives a concrete run.

Two facts finish the proof. First, `ite_keeps`: if `σ` makes `p` true or false, then the merged value `ite p vt vf` still contains the concrete value that the selected arm contains. Second, `merge_keeps`: merging the leaves of a value keeps the instance relation. Both are in `theories/Soundness/MergeKeeps.v`.

## Bounded completeness

Theorems: `concore_completeness_forall`, `concore_completeness_budget` and `concore_completeness_exists`, in `theories/Completeness/Completeness.v`. The hypothesis `budget_total` is defined in `theories/Completeness/Statement.v`.

Start from a concrete run of `e_c` that gives `v_c`. Let `e_s` contain `e_c`. Assume `σ ⊨ Φ`, `contains_env σ Γs Γc`, `concore_expr e_c` and `concrete_env Γc`, as in soundness. There are three conclusions.

- Forall form. There is a fuel `h` such that, at every fuel `n >= h`, every symbolic run of `e_s` gives a value that contains `v_c`.
- Budget form. Assume `budget_total Φ Γs e_s`. This means that a symbolic run exists at every large enough finite fuel. Then there is a fuel `h` such that, at every `n >= h`, a symbolic run exists and its value contains `v_c`.
- Exists form. Under the same assumption, some finite fuel `k` gives a symbolic run whose value contains `v_c`.

The forall form is the base. A concrete run at fuel `Inf` is also a run at every large finite fuel. This is `eval_inf_has_budget` in `theories/SymCore/Budget.v`. It gives the fuel `h`. Then `lockstep_complete` proves the claim for any symbolic run at fuel `n`.

The lemma `lockstep_complete` is an induction on the concrete run, at equal fuel. As in soundness, lifting over a symbolic branch spends no fuel. The leaf that `σ` selects runs in step with the concrete run. The proof again uses `ite_keeps` and `merge_keeps`. Soundness inducts on the symbolic run and builds the concrete run. Completeness inducts on the concrete run and takes any symbolic run at the same fuel.

The budget form needs `budget_total` because a symbolic run may fail to exist. Running out of fuel does not cause this. A run that runs out of fuel still exists, because it gives the value `VBot BOutOfFuel`. But a symbolic run can get stuck. A run is stuck when no rule applies, for example when the program applies a literal to an argument. A symbolic run explores every path that the solver cannot rule out. So it can get stuck on a path that `σ` does not take. The concrete run never sees that path. The assumption `budget_total` rules out a stuck run. The file `theories/NonVacuity/StuckApplication.v` shows a program that is stuck at every fuel of 2 or more (`app_lit_not_budget_total`). The proof takes the larger of the fuel from `budget_total` and the fuel `h` from the forall form. At that fuel, a symbolic run exists, and the forall form shows that it contains `v_c`. The exists form takes `n = h` in the budget form.

## The model

Theorem: `model_laws`, in `theories/Model/Model.v`.

The soundness and completeness theorems are about any solver that obeys a set of laws. The class `ConCoreLaws` bundles the laws (`theories/Soundness/Laws.v`). A theorem about all solvers is empty if no solver exists. The model removes this doubt.

The model is a concrete solver, `model_solver`. Its primitive reducer computes a primitive on literals when every argument is a literal. Otherwise it builds a symbolic primitive application. The file `theories/Model/Model.v` proves each law for this solver and packs the proofs into `model_laws`. The proofs use only simple facts: the reducer computes on literals, and `prim_denote` is a function of the model.

The files in `theories/NonVacuity` then apply the theorems inside the model to real programs. They show that every hypothesis holds and that the conclusions are real values.

## Differences from the paper

1. The instance rule I-Denote has no "has symbolic variables" side condition.
2. Completeness needs no "bounded SMT terms" assumption.
3. The function `ite` merges two casts only when their coercions are equal. A coercion in Rocq carries a role. Two casts that differ only in role would otherwise break soundness. Example: a branch has a then-arm cast with coercion `γ1` and an else-arm cast with coercion `γ2`, and the two differ only in role. If `ite` kept the coercion of the then-arm for both leaves, a model that takes the else-arm would get the wrong coercion.
4. Concrete values may contain the out-of-fuel bottom. A run at finite fuel produces it.
5. The paper's rule `reduce-prim` applies the operation in each leaf of the forced arguments. In Rocq, this lifting is the fixed function `lift_prim` in `theories/SymCore/Merge.v`. Only the reducer `reduce_prim`, which computes the operation on one leaf, is a parameter of the solver. The function `lift_prim` maps a leaf that is not a primitive value, a bottom or a branch to the undefined bottom `VBot BUndefined`.
6. The paper states the instance rule I-Denote on expressions (`e ≡ ⊗ e_a`). In Rocq, the Denote rule exists only for primitive values (`Contains_PDenote` in `contains_prim`). The relation `contains_expr` has no Denote rule. In `contains_expr`, the only rule that relates a symbolic part to a literal is `Contains_ESymLit`: the symbolic variable `s` contains the literal `σ s`.
