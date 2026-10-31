From SymCoreTheory Require Export SymCore.Syntax SymCore.Solver SymCore.Merge.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

Inductive live_fuel := Unlimited | Remaining (n : nat).

Inductive fuel := Spent | Live (f : live_fuel).

Notation Inf := (Live Unlimited).

Definition Fin (n : nat) : fuel :=
  match n with O => Spent | S m => Live (Remaining m) end.

Definition dec (f : live_fuel) : fuel :=
  match f with Unlimited => Inf | Remaining n => Fin n end.

Section SymCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Definition no_alt_matches (v : value) (alts : list alt) : Prop :=
  match v with
  | VCon d _ => find_alt d alts = None
  | VBot _ | VIf _ _ _ => False
  | _ => True
  end.

Inductive eval : fuel -> path_condition -> env -> expr -> value -> Prop :=
  | Eval_Var : forall f Φ Γ x t v,
      lookup_env Γ x = Some t ->
      force (dec f) Φ t v ->
      eval (Live f) Φ Γ (EVar x) v
  | Eval_Lit : forall f Φ Γ l,
      eval (Live f) Φ Γ (ELit l) (VPrim (PLit l))
  | Eval_Sym : forall f Φ Γ s,
      eval (Live f) Φ Γ (ESym s) (VPrim (PSym s))
  | Eval_Con : forall f Φ Γ d,
      eval (Live f) Φ Γ (ECon d) (VCon d [])
  | Eval_Prim : forall f Φ Γ op v,
      prim_app (dec f) Φ op [] v ->
      eval (Live f) Φ Γ (EPrimOp op) v
  | Eval_App : forall f Φ Γ ef ea vf v,
      eval (dec f) Φ Γ ef vf ->
      apply (dec f) Φ Γ vf ea v ->
      eval (Live f) Φ Γ (EApp ef ea) v
  | Eval_Lam : forall f Φ Γ x b,
      eval (Live f) Φ Γ (ELam x b) (VClos Γ x b)
  | Eval_Cast : forall f Φ Γ e γ v,
      eval (dec f) Φ Γ e v ->
      eval (Live f) Φ Γ (ECast e γ) (cast_value v γ)
  | Eval_Bot : forall f Φ Γ b,
      eval (Live f) Φ Γ (EBot b) (VBot b)
  | Eval_Case : forall f Φ Γ es alts vs v,
      eval (dec f) Φ Γ es vs ->
      fold_alts (dec f) Φ Γ (merge vs) alts v ->
      eval (Live f) Φ Γ (ECase es alts) v
  | Eval_Coercion : forall f Φ Γ γ,
      eval (Live f) Φ Γ (ECoercion γ) (VCoercion (subst_coerc Γ γ))
  | Eval_Type : forall f Φ Γ τ,
      eval (Live f) Φ Γ (EType τ) (VType (subst_type Γ τ))
  | Eval_Prune : forall f Φ Γ e,
      sat Φ = false ->
      eval (Live f) Φ Γ e (VBot BUnreachable)
  | Eval_OutOfFuel : forall Φ Γ e,
      eval Spent Φ Γ e (VBot BOutOfFuel)

with apply : fuel -> path_condition -> env -> value -> expr -> value -> Prop :=
  | Apply_Con : forall g Φ Γ d ts e,
      apply g Φ Γ (VCon d ts) e (VCon d (ts ++ [TSusp Γ e]))
  | Apply_Clos : forall g Φ Γ Γ' x b e v,
      eval g Φ (extend_env Γ' x (TSusp Γ e)) b v ->
      apply g Φ Γ (VClos Γ' x b) e v
  | Apply_Prim : forall g Φ Γ op ts e v,
      prim_app g Φ op (ts ++ [TSusp Γ e]) v ->
      apply g Φ Γ (VPartial op ts) e v
  | Apply_Cast : forall g Φ Γ v' γ γa γr e v,
      decomp_coerc_arrow γ = Some (γa, γr) ->
      apply g Φ Γ v' (ECast e (sym_coerc γa)) v ->
      apply g Φ Γ (VCast v' γ) e (VCast v γr)
  | Apply_Bot : forall g Φ Γ b e,
      apply g Φ Γ (VBot b) e (VBot b)
  | Apply_If : forall g Φ Γ p vt vf e vt' vf',
      apply g Φ Γ vt e vt' ->
      apply g Φ Γ vf e vf' ->
      apply g Φ Γ (VIf p vt vf) e (ite p vt' vf')

with prim_app : fuel -> path_condition -> primop -> list thunk -> value -> Prop :=
  | Prim_Partial : forall g Φ op ts,
      length ts < primop_arity op ->
      prim_app g Φ op ts (VPartial op ts)
  | Prim_Ite : forall g Φ tc tthen telse c v,
      force g Φ tc c ->
      select g Φ c tthen telse v ->
      prim_app g Φ op_ite [tc; tthen; telse] v
  | Prim_Reduce : forall g Φ op ts vs,
      op <> op_ite ->
      length ts = primop_arity op ->
      Forall2 (force g Φ) ts vs ->
      prim_app g Φ op ts (lift_prim op vs)

with force : fuel -> path_condition -> thunk -> value -> Prop :=
  | Force_Susp : forall g Φ Γ e v,
      eval g Φ Γ e v ->
      force g Φ (TSusp Γ e) v
  | Force_If : forall g Φ p tthen telse vt vf,
      force g Φ tthen vt ->
      force g Φ telse vf ->
      force g Φ (TIf p tthen telse) (ite p vt vf)

with select : fuel -> path_condition -> value -> thunk -> thunk -> value -> Prop :=
  | Select_True : forall g Φ tthen telse v,
      force g Φ tthen v ->
      select g Φ (VPrim (PLit lit_true)) tthen telse v
  | Select_False : forall g Φ l tthen telse v,
      l <> lit_true ->
      force g Φ telse v ->
      select g Φ (VPrim (PLit l)) tthen telse v
  | Select_Sym : forall g Φ p tthen telse vt vf,
      is_plit p = false ->
      force g (pc_and Φ p) tthen vt ->
      force g (pc_and Φ (pc_not p)) telse vf ->
      select g Φ (VPrim p) tthen telse (ite p vt vf)
  | Select_Bot : forall g Φ b tthen telse,
      select g Φ (VBot b) tthen telse (VBot b)
  | Select_If : forall g Φ p ct cf tthen telse vt vf,
      select g Φ ct tthen telse vt ->
      select g Φ cf tthen telse vf ->
      select g Φ (VIf p ct cf) tthen telse (ite p vt vf)

with fold_alts : fuel -> path_condition -> env -> value -> list alt -> value -> Prop :=
  | Fold_Con : forall g Φ Γ d ts alts xs ep v,
      find_alt d alts = Some (xs, ep) ->
      eval g Φ (bind_fields Γ xs ts) ep v ->
      fold_alts g Φ Γ (VCon d ts) alts v
  | Fold_Bot : forall g Φ Γ b alts,
      fold_alts g Φ Γ (VBot b) alts (VBot b)
  | Fold_If : forall g Φ Γ p vt vf alts vt' vf',
      fold_alts g (pc_and Φ p) Γ vt alts vt' ->
      fold_alts g (pc_and Φ (pc_not p)) Γ vf alts vf' ->
      fold_alts g Φ Γ (VIf p vt vf) alts (ite p vt' vf')
  | Fold_Otherwise : forall g Φ Γ v alts,
      no_alt_matches v alts ->
      fold_alts g Φ Γ v alts (VBot BUndefined).

Section MutualInduction.
Variable Peval : fuel -> path_condition -> env -> expr -> value -> Prop.
Variable Papply : fuel -> path_condition -> env -> value -> expr -> value -> Prop.
Variable Pprim : fuel -> path_condition -> primop -> list thunk -> value -> Prop.
Variable Pforce : fuel -> path_condition -> thunk -> value -> Prop.
Variable Pselect : fuel -> path_condition -> value -> thunk -> thunk -> value -> Prop.
Variable Pfold : fuel -> path_condition -> env -> value -> list alt -> value -> Prop.

Hypothesis case_Eval_Var : forall f Φ Γ x t v,
  lookup_env Γ x = Some t ->
  force (dec f) Φ t v -> Pforce (dec f) Φ t v ->
  Peval (Live f) Φ Γ (EVar x) v.
Hypothesis case_Eval_Lit : forall f Φ Γ l,
  Peval (Live f) Φ Γ (ELit l) (VPrim (PLit l)).
Hypothesis case_Eval_Sym : forall f Φ Γ s,
  Peval (Live f) Φ Γ (ESym s) (VPrim (PSym s)).
Hypothesis case_Eval_Con : forall f Φ Γ d,
  Peval (Live f) Φ Γ (ECon d) (VCon d []).
Hypothesis case_Eval_Prim : forall f Φ Γ op v,
  prim_app (dec f) Φ op [] v -> Pprim (dec f) Φ op [] v ->
  Peval (Live f) Φ Γ (EPrimOp op) v.
Hypothesis case_Eval_App : forall f Φ Γ ef ea vf v,
  eval (dec f) Φ Γ ef vf -> Peval (dec f) Φ Γ ef vf ->
  apply (dec f) Φ Γ vf ea v -> Papply (dec f) Φ Γ vf ea v ->
  Peval (Live f) Φ Γ (EApp ef ea) v.
Hypothesis case_Eval_Lam : forall f Φ Γ x b,
  Peval (Live f) Φ Γ (ELam x b) (VClos Γ x b).
Hypothesis case_Eval_Cast : forall f Φ Γ e γ v,
  eval (dec f) Φ Γ e v -> Peval (dec f) Φ Γ e v ->
  Peval (Live f) Φ Γ (ECast e γ) (cast_value v γ).
Hypothesis case_Eval_Bot : forall f Φ Γ b,
  Peval (Live f) Φ Γ (EBot b) (VBot b).
Hypothesis case_Eval_Case : forall f Φ Γ es alts vs v,
  eval (dec f) Φ Γ es vs -> Peval (dec f) Φ Γ es vs ->
  fold_alts (dec f) Φ Γ (merge vs) alts v -> Pfold (dec f) Φ Γ (merge vs) alts v ->
  Peval (Live f) Φ Γ (ECase es alts) v.
Hypothesis case_Eval_Coercion : forall f Φ Γ γ,
  Peval (Live f) Φ Γ (ECoercion γ) (VCoercion (subst_coerc Γ γ)).
Hypothesis case_Eval_Type : forall f Φ Γ τ,
  Peval (Live f) Φ Γ (EType τ) (VType (subst_type Γ τ)).
Hypothesis case_Eval_Prune : forall f Φ Γ e,
  sat Φ = false ->
  Peval (Live f) Φ Γ e (VBot BUnreachable).
Hypothesis case_Eval_OutOfFuel : forall Φ Γ e,
  Peval Spent Φ Γ e (VBot BOutOfFuel).

Hypothesis case_Apply_Con : forall g Φ Γ d ts e,
  Papply g Φ Γ (VCon d ts) e (VCon d (ts ++ [TSusp Γ e])).
Hypothesis case_Apply_Clos : forall g Φ Γ Γ' x b e v,
  eval g Φ (extend_env Γ' x (TSusp Γ e)) b v ->
  Peval g Φ (extend_env Γ' x (TSusp Γ e)) b v ->
  Papply g Φ Γ (VClos Γ' x b) e v.
Hypothesis case_Apply_Prim : forall g Φ Γ op ts e v,
  prim_app g Φ op (ts ++ [TSusp Γ e]) v ->
  Pprim g Φ op (ts ++ [TSusp Γ e]) v ->
  Papply g Φ Γ (VPartial op ts) e v.
Hypothesis case_Apply_Cast : forall g Φ Γ v' γ γa γr e v,
  decomp_coerc_arrow γ = Some (γa, γr) ->
  apply g Φ Γ v' (ECast e (sym_coerc γa)) v ->
  Papply g Φ Γ v' (ECast e (sym_coerc γa)) v ->
  Papply g Φ Γ (VCast v' γ) e (VCast v γr).
Hypothesis case_Apply_Bot : forall g Φ Γ b e,
  Papply g Φ Γ (VBot b) e (VBot b).
Hypothesis case_Apply_If : forall g Φ Γ p vt vf e vt' vf',
  apply g Φ Γ vt e vt' -> Papply g Φ Γ vt e vt' ->
  apply g Φ Γ vf e vf' -> Papply g Φ Γ vf e vf' ->
  Papply g Φ Γ (VIf p vt vf) e (ite p vt' vf').

Hypothesis case_Prim_Partial : forall g Φ op ts,
  length ts < primop_arity op ->
  Pprim g Φ op ts (VPartial op ts).
Hypothesis case_Prim_Ite : forall g Φ tc tthen telse c v,
  force g Φ tc c -> Pforce g Φ tc c ->
  select g Φ c tthen telse v -> Pselect g Φ c tthen telse v ->
  Pprim g Φ op_ite [tc; tthen; telse] v.
Hypothesis case_Prim_Reduce : forall g Φ op ts vs,
  op <> op_ite ->
  length ts = primop_arity op ->
  Forall2 (force g Φ) ts vs -> Forall2 (Pforce g Φ) ts vs ->
  Pprim g Φ op ts (lift_prim op vs).

Hypothesis case_Force_Susp : forall g Φ Γ e v,
  eval g Φ Γ e v -> Peval g Φ Γ e v ->
  Pforce g Φ (TSusp Γ e) v.
Hypothesis case_Force_If : forall g Φ p tthen telse vt vf,
  force g Φ tthen vt -> Pforce g Φ tthen vt ->
  force g Φ telse vf -> Pforce g Φ telse vf ->
  Pforce g Φ (TIf p tthen telse) (ite p vt vf).

Hypothesis case_Select_True : forall g Φ tthen telse v,
  force g Φ tthen v -> Pforce g Φ tthen v ->
  Pselect g Φ (VPrim (PLit lit_true)) tthen telse v.
Hypothesis case_Select_False : forall g Φ l tthen telse v,
  l <> lit_true ->
  force g Φ telse v -> Pforce g Φ telse v ->
  Pselect g Φ (VPrim (PLit l)) tthen telse v.
Hypothesis case_Select_Sym : forall g Φ p tthen telse vt vf,
  is_plit p = false ->
  force g (pc_and Φ p) tthen vt -> Pforce g (pc_and Φ p) tthen vt ->
  force g (pc_and Φ (pc_not p)) telse vf -> Pforce g (pc_and Φ (pc_not p)) telse vf ->
  Pselect g Φ (VPrim p) tthen telse (ite p vt vf).
Hypothesis case_Select_Bot : forall g Φ b tthen telse,
  Pselect g Φ (VBot b) tthen telse (VBot b).
Hypothesis case_Select_If : forall g Φ p ct cf tthen telse vt vf,
  select g Φ ct tthen telse vt -> Pselect g Φ ct tthen telse vt ->
  select g Φ cf tthen telse vf -> Pselect g Φ cf tthen telse vf ->
  Pselect g Φ (VIf p ct cf) tthen telse (ite p vt vf).

Hypothesis case_Fold_Con : forall g Φ Γ d ts alts xs ep v,
  find_alt d alts = Some (xs, ep) ->
  eval g Φ (bind_fields Γ xs ts) ep v -> Peval g Φ (bind_fields Γ xs ts) ep v ->
  Pfold g Φ Γ (VCon d ts) alts v.
Hypothesis case_Fold_Bot : forall g Φ Γ b alts,
  Pfold g Φ Γ (VBot b) alts (VBot b).
Hypothesis case_Fold_If : forall g Φ Γ p vt vf alts vt' vf',
  fold_alts g (pc_and Φ p) Γ vt alts vt' -> Pfold g (pc_and Φ p) Γ vt alts vt' ->
  fold_alts g (pc_and Φ (pc_not p)) Γ vf alts vf' ->
  Pfold g (pc_and Φ (pc_not p)) Γ vf alts vf' ->
  Pfold g Φ Γ (VIf p vt vf) alts (ite p vt' vf').
Hypothesis case_Fold_Otherwise : forall g Φ Γ v alts,
  no_alt_matches v alts ->
  Pfold g Φ Γ v alts (VBot BUndefined).

Fixpoint eval_mut (f : fuel) (Φ : path_condition) (Γ : env) (e : expr) (v : value)
  (H : eval f Φ Γ e v) {struct H} : Peval f Φ Γ e v :=
  match H in eval f Φ Γ e v return Peval f Φ Γ e v with
  | Eval_Var f Φ Γ x t v Hl Hf => case_Eval_Var f Φ Γ x t v Hl Hf (force_mut _ _ _ _ Hf)
  | Eval_Lit f Φ Γ l => case_Eval_Lit f Φ Γ l
  | Eval_Sym f Φ Γ s => case_Eval_Sym f Φ Γ s
  | Eval_Con f Φ Γ d => case_Eval_Con f Φ Γ d
  | Eval_Prim f Φ Γ op v Hp => case_Eval_Prim f Φ Γ op v Hp (prim_mut _ _ _ _ _ Hp)
  | Eval_App f Φ Γ ef ea vf v Hf Ha =>
      case_Eval_App f Φ Γ ef ea vf v Hf (eval_mut _ _ _ _ _ Hf) Ha (apply_mut _ _ _ _ _ _ Ha)
  | Eval_Lam f Φ Γ x b => case_Eval_Lam f Φ Γ x b
  | Eval_Cast f Φ Γ e γ v He => case_Eval_Cast f Φ Γ e γ v He (eval_mut _ _ _ _ _ He)
  | Eval_Bot f Φ Γ b => case_Eval_Bot f Φ Γ b
  | Eval_Case f Φ Γ es alts vs v Hs Hfa =>
      case_Eval_Case f Φ Γ es alts vs v Hs (eval_mut _ _ _ _ _ Hs)
        Hfa (fold_mut _ _ _ _ _ _ Hfa)
  | Eval_Coercion f Φ Γ γ => case_Eval_Coercion f Φ Γ γ
  | Eval_Type f Φ Γ τ => case_Eval_Type f Φ Γ τ
  | Eval_Prune f Φ Γ e Hs => case_Eval_Prune f Φ Γ e Hs
  | Eval_OutOfFuel Φ Γ e => case_Eval_OutOfFuel Φ Γ e
  end

with apply_mut (g : fuel) (Φ : path_condition) (Γ : env) (vf : value) (e : expr) (v : value)
  (H : apply g Φ Γ vf e v) {struct H} : Papply g Φ Γ vf e v :=
  match H in apply g Φ Γ vf e v return Papply g Φ Γ vf e v with
  | Apply_Con g Φ Γ d ts e => case_Apply_Con g Φ Γ d ts e
  | Apply_Clos g Φ Γ Γ' x b e v Hb =>
      case_Apply_Clos g Φ Γ Γ' x b e v Hb (eval_mut _ _ _ _ _ Hb)
  | Apply_Prim g Φ Γ op ts e v Hp =>
      case_Apply_Prim g Φ Γ op ts e v Hp (prim_mut _ _ _ _ _ Hp)
  | Apply_Cast g Φ Γ v' γ γa γr e v Hd Ha =>
      case_Apply_Cast g Φ Γ v' γ γa γr e v Hd Ha (apply_mut _ _ _ _ _ _ Ha)
  | Apply_Bot g Φ Γ b e => case_Apply_Bot g Φ Γ b e
  | Apply_If g Φ Γ p vt vf e vt' vf' Ht Hf =>
      case_Apply_If g Φ Γ p vt vf e vt' vf'
        Ht (apply_mut _ _ _ _ _ _ Ht) Hf (apply_mut _ _ _ _ _ _ Hf)
  end

with prim_mut (g : fuel) (Φ : path_condition) (op : primop) (ts : list thunk) (v : value)
  (H : prim_app g Φ op ts v) {struct H} : Pprim g Φ op ts v :=
  match H in prim_app g Φ op ts v return Pprim g Φ op ts v with
  | Prim_Partial g Φ op ts Hl => case_Prim_Partial g Φ op ts Hl
  | Prim_Ite g Φ tc tthen telse c v Hc Hs =>
      case_Prim_Ite g Φ tc tthen telse c v Hc (force_mut _ _ _ _ Hc) Hs (select_mut _ _ _ _ _ _ Hs)
  | Prim_Reduce g Φ op ts vs Hne Hl Hall =>
      case_Prim_Reduce g Φ op ts vs Hne Hl Hall
        ((fix forces_mut (ts : list thunk) (vs : list value)
            (Hall : Forall2 (force g Φ) ts vs) {struct Hall} : Forall2 (Pforce g Φ) ts vs :=
            match Hall in Forall2 _ ts vs return Forall2 (Pforce g Φ) ts vs with
            | @Forall2_nil _ _ _ => Forall2_nil _
            | @Forall2_cons _ _ _ t v ts' vs' Ht Hrest =>
                Forall2_cons t v (force_mut _ _ _ _ Ht) (forces_mut ts' vs' Hrest)
            end) ts vs Hall)
  end

with force_mut (g : fuel) (Φ : path_condition) (t : thunk) (v : value)
  (H : force g Φ t v) {struct H} : Pforce g Φ t v :=
  match H in force g Φ t v return Pforce g Φ t v with
  | Force_Susp g Φ Γ e v He => case_Force_Susp g Φ Γ e v He (eval_mut _ _ _ _ _ He)
  | Force_If g Φ p tthen telse vt vf Ht Hf =>
      case_Force_If g Φ p tthen telse vt vf Ht (force_mut _ _ _ _ Ht) Hf (force_mut _ _ _ _ Hf)
  end

with select_mut (g : fuel) (Φ : path_condition) (c : value) (tthen telse : thunk) (v : value)
  (H : select g Φ c tthen telse v) {struct H} : Pselect g Φ c tthen telse v :=
  match H in select g Φ c tthen telse v return Pselect g Φ c tthen telse v with
  | Select_True g Φ tthen telse v Ht => case_Select_True g Φ tthen telse v Ht (force_mut _ _ _ _ Ht)
  | Select_False g Φ l tthen telse v Hl Hf =>
      case_Select_False g Φ l tthen telse v Hl Hf (force_mut _ _ _ _ Hf)
  | Select_Sym g Φ p tthen telse vt vf Hp Ht Hf =>
      case_Select_Sym g Φ p tthen telse vt vf Hp Ht (force_mut _ _ _ _ Ht) Hf (force_mut _ _ _ _ Hf)
  | Select_Bot g Φ b tthen telse => case_Select_Bot g Φ b tthen telse
  | Select_If g Φ p ct cf tthen telse vt vf Ht Hf =>
      case_Select_If g Φ p ct cf tthen telse vt vf
        Ht (select_mut _ _ _ _ _ _ Ht) Hf (select_mut _ _ _ _ _ _ Hf)
  end

with fold_mut (g : fuel) (Φ : path_condition) (Γ : env) (vs : value) (alts : list alt)
  (v : value) (H : fold_alts g Φ Γ vs alts v) {struct H} : Pfold g Φ Γ vs alts v :=
  match H in fold_alts g Φ Γ vs alts v return Pfold g Φ Γ vs alts v with
  | Fold_Con g Φ Γ d ts alts xs ep v Hf He =>
      case_Fold_Con g Φ Γ d ts alts xs ep v Hf He (eval_mut _ _ _ _ _ He)
  | Fold_Bot g Φ Γ b alts => case_Fold_Bot g Φ Γ b alts
  | Fold_If g Φ Γ p vt vf alts vt' vf' Ht Hf =>
      case_Fold_If g Φ Γ p vt vf alts vt' vf'
        Ht (fold_mut _ _ _ _ _ _ Ht) Hf (fold_mut _ _ _ _ _ _ Hf)
  | Fold_Otherwise g Φ Γ v alts Hn => case_Fold_Otherwise g Φ Γ v alts Hn
  end.

Lemma eval_mut_ind :
  (forall f Φ Γ e v, eval f Φ Γ e v -> Peval f Φ Γ e v) /\
  (forall g Φ Γ vf e v, apply g Φ Γ vf e v -> Papply g Φ Γ vf e v) /\
  (forall g Φ op ts v, prim_app g Φ op ts v -> Pprim g Φ op ts v) /\
  (forall g Φ t v, force g Φ t v -> Pforce g Φ t v) /\
  (forall g Φ c tthen telse v, select g Φ c tthen telse v -> Pselect g Φ c tthen telse v) /\
  (forall g Φ Γ vs alts v, fold_alts g Φ Γ vs alts v -> Pfold g Φ Γ vs alts v).
Proof.
  exact (conj eval_mut (conj apply_mut (conj prim_mut (conj force_mut
    (conj select_mut fold_mut))))).
Qed.

End MutualInduction.

End SymCore.

Notation "Φ ';' Γ '⊢' e '⇓' v" := (eval Inf Φ Γ e v) (at level 70, no associativity).
Notation "Γ '⊢ᶜ' e '⇓ᶜ' v" := (eval Inf pc_true Γ e v) (at level 70, no associativity).
