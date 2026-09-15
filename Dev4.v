From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Lists.List.
Import ListNotations.

Section NestedInduction.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Variables (P : fuel -> path_condition -> environment -> expr -> expr -> Prop)
          (Q : fuel -> path_condition -> environment -> expr -> list alt -> expr -> Prop).

Hypothesis HVar : forall f Φ Γ x Γ' e e',
  lookup_env Γ x = Some (Γ', e) -> eval (dec f) Φ Γ' e e' -> P (dec f) Φ Γ' e e' ->
  P (Live f) Φ Γ (EVar x) e'.
Hypothesis HSymVar : forall f Φ Γ x,
  lookup_env Γ x = None -> P (Live f) Φ Γ (EVar x) (EVar x).
Hypothesis HLit : forall f Φ Γ l, P (Live f) Φ Γ (ELit l) (ELit l).
Hypothesis HCon : forall f Φ Γ e d args,
  unspool_app e [] = (ECon d, args) ->
  P (Live f) Φ Γ e (make_con_app d (map (delay Γ) args)).
Hypothesis HCast : forall f Φ Γ e γ e',
  eval (dec f) Φ Γ e e' -> P (dec f) Φ Γ e e' ->
  P (Live f) Φ Γ (ECast e γ) (cast_expr e' γ).
Hypothesis HAppAbs : forall f Φ Γ Γ' x eb ea eb',
  eval (dec f) Φ (extend_env Γ' x Γ ea) eb eb' -> P (dec f) Φ (extend_env Γ' x Γ ea) eb eb' ->
  P (Live f) Φ Γ (EApp (EThunk Γ' (ELam x eb)) ea) eb'.
Hypothesis HAppSpine : forall f Φ Γ ef ea ef' er,
  Comp Γ ef ->
  eval (dec f) Φ Γ ef ef' -> P (dec f) Φ Γ ef ef' ->
  eval (dec f) Φ Γ (EApp ef' ea) er -> P (dec f) Φ Γ (EApp ef' ea) er ->
  P (Live f) Φ Γ (EApp ef ea) er.
Hypothesis HBot : forall f Φ Γ b, P (Live f) Φ Γ (EBot b) (EBot b).
Hypothesis HAppPrim : forall f Φ Γ ef ea p args args',
  unspool_app (EApp ef ea) [] = (EPrimOp p, args) ->
  length args = primop_arity p ->
  Forall2 (fun a a' => eval (dec f) Φ Γ a a' /\ P (dec f) Φ Γ a a') args args' ->
  P (Live f) Φ Γ (EApp ef ea) (reduce_prim p args').
Hypothesis HLam : forall f Φ Γ x e, P (Live f) Φ Γ (ELam x e) (EThunk Γ (ELam x e)).
Hypothesis HAppCast : forall f Φ Γ ef γ ea γ_a γ_r er,
  decomp_coerc_arrow γ = Some (γ_a, γ_r) ->
  eval (dec f) Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er ->
  P (dec f) Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er ->
  P (Live f) Φ Γ (EApp (ECast ef γ) ea) er.
Hypothesis HAppIf : forall f Φ Γ e1 e2 ec et ef args er,
  unspool_app (EApp e1 e2) [] = (EIf ec et ef, args) ->
  eval (dec f) Φ Γ (EIf ec (fold_left EApp args et) (fold_left EApp args ef)) er ->
  P (dec f) Φ Γ (EIf ec (fold_left EApp args et) (fold_left EApp args ef)) er ->
  P (Live f) Φ Γ (EApp e1 e2) er.
Hypothesis HAppBot : forall f Φ Γ b ea, P (Live f) Φ Γ (EApp (EBot b) ea) (EBot b).
Hypothesis HCase : forall f Φ Γ es alts es' er,
  eval (dec f) Φ Γ es es' -> P (dec f) Φ Γ es es' ->
  fold_alts (dec f) Φ Γ (merge Γ es') alts er -> Q (dec f) Φ Γ (merge Γ es') alts er ->
  P (Live f) Φ Γ (ECase es alts) er.
Hypothesis HIf : forall f Φ Γ ec et ef ec' et' ef' pc_c,
  eval (dec f) Φ Γ ec ec' -> P (dec f) Φ Γ ec ec' ->
  expr_to_pc Γ ec' = Some pc_c ->
  eval (dec f) (Φ ∧ pc_c) Γ et et' -> P (dec f) (Φ ∧ pc_c) Γ et et' ->
  eval (dec f) (Φ ∧ ¬ pc_c) Γ ef ef' -> P (dec f) (Φ ∧ ¬ pc_c) Γ ef ef' ->
  P (Live f) Φ Γ (EIf ec et ef) (EIf ec' et' ef').
Hypothesis HCoercion : forall f Φ Γ γ, P (Live f) Φ Γ (ECoercion γ) (ECoercion (subst_coerc Γ γ)).
Hypothesis HPrune : forall f Φ Γ e, sat Φ = false -> P (Live f) Φ Γ e (EBot BUnreachable).
Hypothesis HType : forall f Φ Γ τ, P (Live f) Φ Γ (EType τ) (EType (subst_type Γ τ)).
Hypothesis HThunk : forall f Φ Γ Γ' e e',
  eval (dec f) Φ Γ' e e' -> P (dec f) Φ Γ' e e' -> P (Live f) Φ Γ (EThunk Γ' e) e'.
Hypothesis HOutOfFuel : forall Φ Γ e, P Spent Φ Γ e (EBot BOutOfFuel).

Hypothesis HFIf : forall f Φ Γ ec et ef alts et' ef' pc_c,
  expr_to_pc Γ ec = Some pc_c ->
  fold_alts f (Φ ∧ pc_c) Γ et alts et' -> Q f (Φ ∧ pc_c) Γ et alts et' ->
  fold_alts f (Φ ∧ ¬ pc_c) Γ ef alts ef' -> Q f (Φ ∧ ¬ pc_c) Γ ef alts ef' ->
  Q f Φ Γ (EIf ec et ef) alts (EIf ec et' ef').
Hypothesis HFIfFail : forall f Φ Γ ec et ef alts,
  expr_to_pc Γ ec = None -> Q f Φ Γ (EIf ec et ef) alts (EBot BUndefined).
Hypothesis HFCon : forall f Φ Γ e d ea xs ep alts er,
  decompose_con_app e = Some (d, ea) ->
  find_alt d alts = Some (xs, ep) ->
  eval f Φ (extend_env_multi Γ xs ea Γ) ep er -> P f Φ (extend_env_multi Γ xs ea Γ) ep er ->
  Q f Φ Γ e alts er.
Hypothesis HFBot : forall f Φ Γ b alts, Q f Φ Γ (EBot b) alts (EBot b).
Hypothesis HFOtherwise : forall f Φ Γ e alts,
  is_if (fst (unspool_app e [])) = false ->
  (match decompose_con_app e with
   | Some (d, _) => find_alt d alts = None
   | None => True
   end) ->
  is_bot e = false ->
  Q f Φ Γ e alts (EBot BUndefined).

Fixpoint eval_nested_ind f Φ Γ e v (H : eval f Φ Γ e v) {struct H} : P f Φ Γ e v :=
  match H in eval f Φ Γ e v return P f Φ Γ e v with
  | Eval_Var f Φ Γ x Γ' e e' Hl He => HVar f Φ Γ x Γ' e e' Hl He (eval_nested_ind _ _ _ _ _ He)
  | Eval_SymVar f Φ Γ x Hl => HSymVar f Φ Γ x Hl
  | Eval_Lit f Φ Γ l => HLit f Φ Γ l
  | Eval_Con f Φ Γ e d args Hu => HCon f Φ Γ e d args Hu
  | Eval_Cast f Φ Γ e γ e' He => HCast f Φ Γ e γ e' He (eval_nested_ind _ _ _ _ _ He)
  | Eval_AppAbs f Φ Γ Γ' x eb ea eb' He =>
      HAppAbs f Φ Γ Γ' x eb ea eb' He (eval_nested_ind _ _ _ _ _ He)
  | Eval_AppSpine f Φ Γ ef ea ef' er Hc H1 H2 =>
      HAppSpine f Φ Γ ef ea ef' er Hc H1 (eval_nested_ind _ _ _ _ _ H1)
        H2 (eval_nested_ind _ _ _ _ _ H2)
  | Eval_Bot f Φ Γ b => HBot f Φ Γ b
  | Eval_AppPrim f Φ Γ ef ea p args args' Hu Hl HF =>
      HAppPrim f Φ Γ ef ea p args args' Hu Hl
        ((fix go l l' (HF0 : Forall2 (eval (dec f) Φ Γ) l l') {struct HF0} :
            Forall2 (fun a a' => eval (dec f) Φ Γ a a' /\ P (dec f) Φ Γ a a') l l' :=
            match HF0 in Forall2 _ l l'
              return Forall2 (fun a a' => eval (dec f) Φ Γ a a' /\ P (dec f) Φ Γ a a') l l' with
            | @Forall2_nil _ _ _ => Forall2_nil _
            | @Forall2_cons _ _ _ a a' l0 l0' Ha HF1 =>
                Forall2_cons a a' (conj Ha (eval_nested_ind _ _ _ _ _ Ha)) (go l0 l0' HF1)
            end) args args' HF)
  | Eval_Lam f Φ Γ x e => HLam f Φ Γ x e
  | Eval_AppCast f Φ Γ ef γ ea γ_a γ_r er Hd He =>
      HAppCast f Φ Γ ef γ ea γ_a γ_r er Hd He (eval_nested_ind _ _ _ _ _ He)
  | Eval_AppIf f Φ Γ e1 e2 ec et ef args er Hu He =>
      HAppIf f Φ Γ e1 e2 ec et ef args er Hu He (eval_nested_ind _ _ _ _ _ He)
  | Eval_AppBot f Φ Γ b ea => HAppBot f Φ Γ b ea
  | Eval_Case f Φ Γ es alts es' er He Hf =>
      HCase f Φ Γ es alts es' er He (eval_nested_ind _ _ _ _ _ He) Hf (fold_nested_ind _ _ _ _ _ _ Hf)
  | Eval_If f Φ Γ ec et ef ec' et' ef' pc_c Hc Hp Ht Hf =>
      HIf f Φ Γ ec et ef ec' et' ef' pc_c Hc (eval_nested_ind _ _ _ _ _ Hc) Hp
        Ht (eval_nested_ind _ _ _ _ _ Ht) Hf (eval_nested_ind _ _ _ _ _ Hf)
  | Eval_Coercion f Φ Γ γ => HCoercion f Φ Γ γ
  | Eval_Prune f Φ Γ e Hs => HPrune f Φ Γ e Hs
  | Eval_Type f Φ Γ τ => HType f Φ Γ τ
  | Eval_Thunk f Φ Γ Γ' e e' He => HThunk f Φ Γ Γ' e e' He (eval_nested_ind _ _ _ _ _ He)
  | Eval_OutOfFuel Φ Γ e => HOutOfFuel Φ Γ e
  end
with fold_nested_ind f Φ Γ e alts v (H : fold_alts f Φ Γ e alts v) {struct H} : Q f Φ Γ e alts v :=
  match H in fold_alts f Φ Γ e alts v return Q f Φ Γ e alts v with
  | FoldAlts_If f Φ Γ ec et ef alts et' ef' pc_c Hp Ht Hf =>
      HFIf f Φ Γ ec et ef alts et' ef' pc_c Hp Ht (fold_nested_ind _ _ _ _ _ _ Ht)
        Hf (fold_nested_ind _ _ _ _ _ _ Hf)
  | FoldAlts_IfFail f Φ Γ ec et ef alts Hp => HFIfFail f Φ Γ ec et ef alts Hp
  | FoldAlts_Con f Φ Γ e d ea xs ep alts er Hd Hf He =>
      HFCon f Φ Γ e d ea xs ep alts er Hd Hf He (eval_nested_ind _ _ _ _ _ He)
  | FoldAlts_Bot f Φ Γ b alts => HFBot f Φ Γ b alts
  | FoldAlts_Otherwise f Φ Γ e alts H1 H2 H3 => HFOtherwise f Φ Γ e alts H1 H2 H3
  end.

End NestedInduction.
