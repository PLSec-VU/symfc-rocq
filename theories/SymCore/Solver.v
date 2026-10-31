From SymCoreTheory Require Import SymCore.Syntax.

Class SymCoreSolver {sorts : SymCoreSorts} : Type := {
  sat : path_condition -> bool;
  pc_true : path_condition;
  sat_pc_true : sat pc_true = true;
  reduce_prim : primop -> list prim -> value;
  cast_value : value -> coercion -> value;
  subst_coerc : env -> coercion -> coercion;
  subst_type : env -> type_fc -> type_fc
}.
