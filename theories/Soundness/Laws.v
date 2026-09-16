From SymCoreTheory Require Export Soundness.Soundness.
From Stdlib Require Import Strings.String Lists.List Lia Arith.PeanoNat.
Import ListNotations.

(** All laws at once, for developments that take every law as context. *)
Inductive ConCoreLaws {sorts : SymCoreSorts} {solver : SymCoreSolver} : Prop :=
  concore_laws :
    ReducePrimSolvable -> ReducePrimSaturated ->
    ReducePrimConcore -> CastExprConcore ->
    ReducePrimScoped -> CastExprScoped ->
    ReducePrimKeepsOutOfFuel -> CastExprKeepsOutOfFuel ->
    ModelsSat -> PrimValueAnd ->
    ReducePrimContains -> ReducePrimDenote -> ReducePrimGroundValue ->
    CastExprContains -> ReducePrimIteWellformed ->
    SubstCoercContainsEnv -> SubstTypeContainsEnv ->
    ConCoreLaws.

Existing Class ConCoreLaws.

#[export] Instance reduce_prim_solvable_of_laws `{laws : ConCoreLaws} : ReducePrimSolvable.
Proof. destruct laws; assumption. Qed.
#[export] Instance reduce_prim_saturated_of_laws `{laws : ConCoreLaws} : ReducePrimSaturated.
Proof. destruct laws; assumption. Qed.
#[export] Instance reduce_prim_concore_of_laws `{laws : ConCoreLaws} : ReducePrimConcore.
Proof. destruct laws; assumption. Qed.
#[export] Instance cast_expr_concore_of_laws `{laws : ConCoreLaws} : CastExprConcore.
Proof. destruct laws; assumption. Qed.
#[export] Instance reduce_prim_scoped_of_laws `{laws : ConCoreLaws} : ReducePrimScoped.
Proof. destruct laws; assumption. Qed.
#[export] Instance cast_expr_scoped_of_laws `{laws : ConCoreLaws} : CastExprScoped.
Proof. destruct laws; assumption. Qed.
#[export] Instance reduce_prim_keeps_out_of_fuel_of_laws `{laws : ConCoreLaws}
  : ReducePrimKeepsOutOfFuel.
Proof. destruct laws; assumption. Qed.
#[export] Instance cast_expr_keeps_out_of_fuel_of_laws `{laws : ConCoreLaws}
  : CastExprKeepsOutOfFuel.
Proof. destruct laws; assumption. Qed.
#[export] Instance models_sat_of_laws `{laws : ConCoreLaws} : ModelsSat.
Proof. destruct laws; assumption. Qed.
#[export] Instance prim_value_and_of_laws `{laws : ConCoreLaws} : PrimValueAnd.
Proof. destruct laws; assumption. Qed.
#[export] Instance reduce_prim_contains_of_laws `{laws : ConCoreLaws} : ReducePrimContains.
Proof. destruct laws; assumption. Qed.
#[export] Instance reduce_prim_denote_of_laws `{laws : ConCoreLaws} : ReducePrimDenote.
Proof. destruct laws; assumption. Qed.
#[export] Instance reduce_prim_ground_value_of_laws `{laws : ConCoreLaws} : ReducePrimGroundValue.
Proof. destruct laws; assumption. Qed.
#[export] Instance cast_expr_contains_of_laws `{laws : ConCoreLaws} : CastExprContains.
Proof. destruct laws; assumption. Qed.
#[export] Instance reduce_prim_ite_wellformed_of_laws `{laws : ConCoreLaws} : ReducePrimIteWellformed.
Proof. destruct laws; assumption. Qed.
#[export] Instance subst_coerc_contains_env_of_laws `{laws : ConCoreLaws} : SubstCoercContainsEnv.
Proof. destruct laws; assumption. Qed.
#[export] Instance subst_type_contains_env_of_laws `{laws : ConCoreLaws} : SubstTypeContainsEnv.
Proof. destruct laws; assumption. Qed.
