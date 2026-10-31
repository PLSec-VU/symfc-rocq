From SymCoreTheory Require Export Soundness.Soundness.

Inductive ConCoreLaws {sorts : SymCoreSorts} {solver : SymCoreSolver} : Prop :=
  concore_laws :
    ReducePrimLiteral -> CastConcore ->
    ModelsSat -> ReducePrimContains -> CastContains -> SubstContains ->
    ConCoreLaws.

Existing Class ConCoreLaws.

#[export] Instance reduce_prim_literal_of_laws `{laws : ConCoreLaws} : ReducePrimLiteral.
Proof. destruct laws; assumption. Qed.
#[export] Instance cast_concore_of_laws `{laws : ConCoreLaws} : CastConcore.
Proof. destruct laws; assumption. Qed.
#[export] Instance models_sat_of_laws `{laws : ConCoreLaws} : ModelsSat.
Proof. destruct laws; assumption. Qed.
#[export] Instance reduce_prim_contains_of_laws `{laws : ConCoreLaws} : ReducePrimContains.
Proof. destruct laws; assumption. Qed.
#[export] Instance cast_contains_of_laws `{laws : ConCoreLaws} : CastContains.
Proof. destruct laws; assumption. Qed.
#[export] Instance subst_contains_of_laws `{laws : ConCoreLaws} : SubstContains.
Proof. destruct laws; assumption. Qed.
