From SymCoreTheory Require Export Soundness.Laws.
From Stdlib Require Import Lists.List.
Import ListNotations.

Section Statement.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Definition budget_total Φ Γ e := exists h, forall n, h <= n -> exists v, eval (Fin n) Φ Γ e v.

Definition complete_eval σ (g : fuel) Φc Γc e_c v_c : Prop :=
  Φc = pc_true -> concrete_env Γc -> concore_expr e_c ->
  forall Φ Γs e_s v_s, eval g Φ Γs e_s v_s -> σ ⊨ Φ ->
  contains_env σ Γs Γc -> contains_expr σ e_s e_c -> contains_val σ v_s v_c.
Definition complete_apply σ (g : fuel) Φc Γc vf_c e_c v_c : Prop :=
  Φc = pc_true -> concrete_env Γc -> concrete_value vf_c -> concore_expr e_c ->
  forall Φ Γs vf_s e_s v_s, apply g Φ Γs vf_s e_s v_s -> σ ⊨ Φ ->
  contains_env σ Γs Γc -> contains_val σ vf_s vf_c -> contains_expr σ e_s e_c ->
  contains_val σ v_s v_c.
Definition complete_prim σ (g : fuel) Φc op ts_c v_c : Prop :=
  Φc = pc_true -> Forall concrete_thunk ts_c ->
  forall Φ ts_s v_s, prim_app g Φ op ts_s v_s -> σ ⊨ Φ ->
  Forall2 (contains_thunk σ) ts_s ts_c -> contains_val σ v_s v_c.
Definition complete_force σ (g : fuel) Φc t_c v_c : Prop :=
  Φc = pc_true -> concrete_thunk t_c ->
  forall Φ t_s v_s, force g Φ t_s v_s -> σ ⊨ Φ ->
  contains_thunk σ t_s t_c -> contains_val σ v_s v_c.
Definition complete_select σ (g : fuel) Φc c_c tthen_c telse_c v_c : Prop :=
  Φc = pc_true -> concrete_value c_c -> concrete_thunk tthen_c -> concrete_thunk telse_c ->
  forall Φ c_s tthen_s telse_s v_s, select g Φ c_s tthen_s telse_s v_s -> σ ⊨ Φ ->
  contains_val σ c_s c_c -> contains_thunk σ tthen_s tthen_c ->
  contains_thunk σ telse_s telse_c -> contains_val σ v_s v_c.
Definition complete_fold σ (g : fuel) Φc Γc vs_c alts_c v_c : Prop :=
  Φc = pc_true -> concrete_env Γc -> concrete_value vs_c -> Forall concore_alt alts_c ->
  forall Φ Γs vs_s alts_s v_s, fold_alts g Φ Γs vs_s alts_s v_s -> σ ⊨ Φ ->
  contains_env σ Γs Γc -> contains_val σ vs_s vs_c -> Forall2 (contains_alt σ) alts_s alts_c ->
  contains_val σ v_s v_c.

End Statement.
