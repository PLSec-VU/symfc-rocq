# SymCore in Rocq

This repository is a Rocq proof of the theory section of the SymFC paper.

## Build

You need Rocq 9.0. Run these commands in the repository root:

```bash
rocq makefile -f _CoqProject -o Makefile
```

```bash
make
```

## Main results

The file `theories/Theorems.v` prints the statement of each theorem and the axioms it uses. Every theorem is closed under the global context. The file `docs/proof-sketches.md` explains the proofs.

| Paper | Rocq name | File |
| --- | --- | --- |
| Theorem "Concrete determinism" | `concore_eval_deterministic` | `theories/ConCore/Determinism.v` |
| Theorem "Soundness" | `concore_soundness` | `theories/Soundness/Soundness.v` |
| Theorem "Bounded completeness", forall form | `concore_completeness_forall` | `theories/Completeness/Completeness.v` |
| Theorem "Bounded completeness", budget form | `concore_completeness_budget` | `theories/Completeness/Completeness.v` |
| Theorem "Bounded completeness", exists form | `concore_completeness_exists` | `theories/Completeness/Completeness.v` |
| A solver that satisfies every law | `model_laws` | `theories/Model/Model.v` |

## Files

The files build in the order that `_CoqProject` lists. A file can use the files listed above it.

### `theories/SymCore`: the language and its evaluation

| File | Contents |
| --- | --- |
| `Syntax.v` | Variables, literals, types, coercions, expressions, values, thunks, bottoms, environments and path conditions. The class `SymCoreSorts` holds the abstract sorts. |
| `Solver.v` | The solver class `SymCoreSolver`. |
| `Merge.v` | Merging two leaves of a branch: `ite_leaf`, `ite` and `merge`. |
| `Eval.v` | Fuel, the six evaluation relations and the induction principle `eval_mut_ind`. |
| `Inversion.v` | Inversion lemmas for the evaluation relations. |
| `Budget.v` | A run with no bound is also a run at every large finite bound (`eval_inf_has_budget`). |

### `theories/ConCore`: concrete programs

| File | Contents |
| --- | --- |
| `Programs.v` | ConCore expressions (`concore_expr`), concrete values and environments, and the concrete evaluation notation. |
| `Preservation.v` | The proof that evaluation stays inside ConCore. |
| `Determinism.v` | Concrete determinism. |

### `theories/Soundness`

| File | Contents |
| --- | --- |
| `Instance.v` | Models, the value of a formula, and the instance relation `contains_val` with its relatives. |
| `MergeKeeps.v` | Merging keeps an instance (`ite_keeps`, `merge_keeps`). |
| `Soundness.v` | Soundness and its lock-step induction `lockstep_sound`. |
| `Laws.v` | `ConCoreLaws`, one class that bundles every law about the solver. |

### `theories/Completeness`

| File | Contents |
| --- | --- |
| `Statement.v` | The hypothesis `budget_total` and the statements that the induction proves. |
| `Completeness.v` | The lock-step induction `lockstep_complete` and the three completeness theorems. |

### `theories/Model`: one solver that satisfies every law

| File | Contents |
| --- | --- |
| `Reducer.v` | Boolean literals, the primitives and the reducer. |
| `Model.v` | The solver `model_solver`, proofs of its laws, and the bundle `model_laws`. |

### `theories/NonVacuity`: the theorems are not empty

A theorem is *vacuous* when its hypotheses can never hold together, so it says nothing. These files build programs inside the model where every hypothesis holds and the conclusion is a real literal or constructor.

| File | Contents |
| --- | --- |
| `SelfApplication.v` | A loop that has no value with no bound but has a value at every finite bound. |
| `SoundnessInstances.v` | Soundness applied to symbolic variables, branches and a primitive that computes, and proof that the instance relation still tells different values apart. |
| `LoopingArm.v` | Completeness on a `case` whose other alternative, which the model does not take, loops. |
| `RuntimeBranch.v` | Soundness and completeness on a `case` whose scrutinee is a formula computed at run time. |
| `PruningModel.v` | A solver that prunes, and a program that is not budget-total. |
| `FromJust.v` | Soundness and completeness on a `case` that extracts the field of a symbolic `Just`. |

### `theories/Theorems.v`

The entry point. It prints the five main theorems and `model_laws`, with the axioms of each.

## Differences from the paper

The file `docs/proof-sketches.md` lists five places where the Rocq development differs from the paper.
