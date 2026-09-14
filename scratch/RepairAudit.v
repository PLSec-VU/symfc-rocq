From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

(* Every result Section 11 is required to keep, named so that a broken one
   fails here rather than silently disappearing. *)
Check symvar_instantiated.
Check symvar_instantiated_uniquely.
Check soundness_applies_to_symvar.
Check soundness_on_symbolic_primop.
Check symbolic_branch_has_concretion.
Check soundness_not_vacuous_on_symbolic_branch.
Check symbolic_branch_condition_is_judgeable.
Check prune_attack_blocked.
Check prune_does_not_kill_branches.
Check contains_not_rigid_on_solvable.
Check ground_solvable_contains_eq.
Check unconditional_solvable_forces_constancy.
Check distinct_images_survive_resolvable_conditions.
Check distinct_images_survive_symbolic_conditions.
Check old_axiom_refutes_distinct_images.

(* Anti-triviality. *)
Check distinct_literals_not_contained.
Check distinct_constructors_not_contained.
Check lambda_not_contained_by_literal.
Check constructor_not_contained_by_literal.
Check bottom_not_contained_by_literal.
Check literal_not_contained_by_lambda.
Check smt_concretion_determined.
Check wrong_value_not_contained.
Check closed_smt_term_is_rigid.

(* The computing primitive. *)
Check computing_primitive_concretion.
Check soundness_on_computing_primitive.
Check computing_primitive_value.
Check computing_primitive_refutes_old_verdict.

(* Assumption budget. *)
Print Assumptions concore_soundness.
Print Assumptions eval_denote.
Print Assumptions closed_smt_term_is_rigid.
Print Assumptions smt_concretion_determined.
Print Assumptions computing_primitive_concretion.
Print Assumptions soundness_on_computing_primitive.
