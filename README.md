# SymCore in Rocq

This repository is a Rocq proof of the theory section of the SymFC paper. Rocq is a proof assistant: it checks every definition and proof by machine. The proofs use no axioms. Each assumption about the SMT solver is a *law*, which is a Rocq class that a proof takes as a parameter. The folder `theories/Model` gives one solver that satisfies every law, so the laws do not contradict each other.

## Build

You need Rocq 9.0. Run these commands in the repository root:

```bash
rocq makefile -f _CoqProject -o Makefile
```

```bash
make
```

A full build takes about 20 seconds. `theories/Theorems.v` prints the main theorems and their assumptions. Each theorem must print "Closed under the global context", which means it uses no axiom.

## Main results

| Paper | Rocq name | File |
| --- | --- | --- |
| Theorem "Concrete determinism" | `concore_eval_deterministic` | `theories/ConCore/Determinism.v` |
| Theorem "Soundness" | `concore_soundness` | `theories/Soundness/Soundness.v` |
| Theorem "Bounded completeness" | `concore_completeness_budget` | `theories/Completeness/Completeness.v` |

The completeness file also has two related forms. `concore_completeness_forall` needs no budget-total hypothesis and says that every result at a large enough bound covers the concrete value. `concore_completeness_exists` says that some bound gives such a result.

## Files

The files build in the order that `_CoqProject` lists. Each proof file exports the proof file before it, so a file can use everything listed above it.

### `theories/SymCore`: the language and its evaluation

| File | Contents |
| --- | --- |
| `Syntax.v` | Variables, literals, types, coercions, expressions, bottoms, environments and path conditions. The class `SymCoreSorts` holds the abstract sorts. |
| `SideConditions.v` | The solver class `SymCoreSolver`, the application spine, `Solvable`, `Comp`, the formula reader `expr_to_pc`, `find_alt` and `delay`. |
| `Merge.v` | Merging two leaves of a branch: `ite_leaf`, `ite` and `merge`. |
| `Eval.v` | Fuel, and the evaluation rules `eval` and `fold_alts`. |
| `SolvableFacts.v` | The laws `ReducePrimSolvable` and `ReducePrimSaturated`, and facts about solvable terms. |
| `Inversion.v` | Inversion lemmas for `eval` and `fold_alts`. |
| `Budget.v` | A run with no bound is also a run at some finite bound (`eval_inf_has_budget`). |

### `theories/ConCore`: concrete programs

| File | Contents |
| --- | --- |
| `Programs.v` | ConCore expressions (`concore_expr`), scoping, closed programs and symbolic programs. |
| `Preservation.v` | The laws that keep evaluation inside ConCore, and the proof that it stays there. |
| `Determinism.v` | Concrete determinism. |

### `theories/Soundness`

| File | Contents |
| --- | --- |
| `Instance.v` | Models, the value of a formula, and the instance relation `contains`. |
| `Alignment.v` | The instance laws, and lemmas that line up a symbolic rule with the matching concrete rule. |
| `MergeKeeps.v` | Merging keeps an instance (`merge_keeps`). |
| `Soundness.v` | Soundness. |
| `Laws.v` | `ConCoreLaws`, one class that bundles every law above. |

### `theories/Completeness`

| File | Contents |
| --- | --- |
| `Cost.v` | Instances counted by their symbolic overhead (`contains_k`), and the cost laws `SymFCCostLaws`. |
| `Reach.v` | The states a run reaches, and the hypothesis `smt_bounded_run` ("bounded SMT terms" in the paper). |
| `Statement.v` | The hypothesis `budget_total` and the three completeness statements. |
| `SmtCost.v` | Bounds on the size of SMT terms. |
| `Induction.v` | The induction principle `eval_nested_ind` and the lemmas that remove branch and thunk layers. |
| `Closures.v`, `Spines.v`, `Cases.v` | The proof cases, grouped by rule. |
| `Completeness.v` | Completeness in its three forms. |

### `theories/Model`: one solver that satisfies every law

| File | Contents |
| --- | --- |
| `Reducer.v` | Boolean literals, the primitives and the reducer, and the laws that need no reasoning about the reducer. |
| `Lifting.v` | Lifting branches out of an application, and a proof that the value of a closed term does not depend on the model. |
| `ReducerLaws.v` | The laws about the reducer. |
| `CostLaws.v` | The cost laws. |
| `Model.v` | The remaining laws, and the bundles `model_laws` and `model_symfc_cost_laws`. |

### `theories/NonVacuity`: the theorems are not empty

A theorem is *vacuous* when its hypotheses can never hold together, so it says nothing. These files build programs inside the model where every hypothesis holds and the conclusion is a real literal or constructor.

| File | Contents |
| --- | --- |
| `SelfApplication.v` | A loop that has no value with no bound but has a value at every finite bound. |
| `SoundnessInstances.v` | Soundness applied to symbolic variables, branches and a primitive that computes, and proof that the instance relation still tells different values apart. |
| `LoopingArm.v` | Completeness on a `case` whose other alternative, which the model does not take, loops. |
| `PruningModel.v` | A solver that prunes, and a program that is not budget-total. |
| `RuntimeBranch.v` | Soundness and completeness on a `case` whose scrutinee is a formula computed at run time. |
