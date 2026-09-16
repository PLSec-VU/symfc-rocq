From SymCoreTheory Require Export Soundness.Instance.
From Stdlib Require Import Strings.String Lists.List Lia Arith.PeanoNat.
Import ListNotations.

Section ConCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}
  {reduce_prim_solvable_law : ReducePrimSolvable}
  {reduce_prim_saturated_law : ReducePrimSaturated}
  {reduce_prim_concore_law : ReducePrimConcore} {cast_expr_concore_law : CastExprConcore}
  {reduce_prim_scoped_law : ReducePrimScoped} {cast_expr_scoped_law : CastExprScoped}
  {models_sat_law : ModelsSat} {prim_value_and_law : PrimValueAnd}.

(** An environment matched by concretion binds no symbolic variable. This is
    the scoping fact that makes models_cond_total applicable; it is PROVED
    from contains_env, not assumed. *)
Lemma contains_env_sym_free : forall σ S Γs Γc,
  contains_env σ S Γs Γc -> sym_free_env S Γs /\ sym_free_env S Γc.
Proof.
  intros σ S Γs Γc H.
  induction H as [| x Γs Γc es ec rest_s rest_c Hx Henv IHenv Hcont Hcon Hrest IHrest].
  - split; intros y Hy; reflexivity.
  - destruct IHrest as [IHs IHc]. split; intros y Hy; simpl;
      destruct (string_dec y x) as [Heq | Hneq];
      [ subst; rewrite Hx in Hy; discriminate | apply IHs; exact Hy
      | subst; rewrite Hx in Hy; discriminate | apply IHc; exact Hy ].
Qed.

Lemma contains_env_lookup_none : forall σ S Γs Γc x,
  contains_env σ S Γs Γc ->
  lookup_env Γs x = None ->
  lookup_env Γc x = None.
Proof.
  intros σ S Γs Γc x H.
  induction H as [| y Γs' Γc' es ec rest_s rest_c Hy Henv IHenv Hcont Hcon Hrest IHrest];
    intros Hnone.
  - reflexivity.
  - simpl in *. destruct (string_dec x y); [discriminate | apply IHrest; exact Hnone].
Qed.

(** ------------------------------------------------------------------------- *)
(** SMT and Coercion Solver Behaviors on Concretion                           *)
(** ------------------------------------------------------------------------- *)

(** SMT solver behavior: primitive operations preserve concretion of closed
    concrete arguments *)
Class ReducePrimContains : Prop :=
reduce_prim_contains : forall σ S p args_s args_c,
  Forall closed_term args_c ->
  Forall2 (contains σ S) args_s args_c ->
  contains σ S (reduce_prim p args_s) (reduce_prim p args_c).

(**
  SMT solver behavior: reducing a primitive application preserves its SMT
  value. This is the correctness statement for the external reducer, and it is
  what lets the reducer COMPUTE. Without it, a reduced term could stay related
  to its concrete counterpart only by being syntactically the same term, so
  reduce_prim would be forced never to compute.
*)
Class ReducePrimDenote : Prop :=
reduce_prim_denote : forall σ S p args ls,
  Forall2 (denote σ S) args ls ->
  denote σ S (reduce_prim p args) (prim_value p ls).

(**
  SMT solver behavior: when the reducer's answer mentions no variable, it is
  a value. A closed SMT term is a number the solver already knows, and a
  reducer that returned an unevaluated closed application would simply have
  stopped early.
*)
Class ReducePrimGroundValue : Prop :=
reduce_prim_ground_value : forall p args,
  smt_ground (reduce_prim p args) = true ->
  exists l, reduce_prim p args = ELit l.

Context {reduce_prim_contains_law : ReducePrimContains}
  {reduce_prim_denote_law : ReducePrimDenote}
  {reduce_prim_ground_value_law : ReducePrimGroundValue}.

(** Coercion cast simplification preserves concretion (Lemma A.5 in the paper) *)
Class CastExprContains : Prop :=
cast_expr_contains : forall σ S es ec γ,
  contains σ S es ec ->
  contains σ S (cast_expr es γ) (cast_expr ec γ).

Context {cast_expr_contains_law : CastExprContains}.

(**
  SMT solver behavior: merging two solvable arms does not invent
  well-formedness. Merge turns a branch with two solvable arms into the SMT
  if-then-else, and Rule Case then folds that term by its value. It may only
  do so when every primitive in the merged formula has its exact arity, or the
  formula mentions no variable. This law says that whenever the merged formula
  passes that test, so does the formula of the arm the model selects.

  It is the one fact the instance relation does not give. A related pair can
  disagree on the SMT value when the symbolic arm applies a primitive to more
  arguments than its arity: the instance relation may then read an inner
  saturated part as a literal, and a literal in operator position is not a
  formula at all. A reducer whose answer is well formed while such an arm is
  not is what this law rules out. A reducer that leaves the branch as a
  residual if-then-else, or that answers one arm, or that folds a
  variable-free term to a literal, satisfies it.
*)
Class ReducePrimIteWellformed : Prop :=
reduce_prim_ite_wellformed : forall σ S ec et ef pcc pc pca,
  Solvable · ec -> Solvable · et -> Solvable · ef ->
  denotes S ec pcc ->
  denotes S (reduce_prim op_ite (ec :: et :: ef :: nil)) pc ->
  (pc_arities_ok pc = true \/ pc_has_var pc = false) ->
  denotes S (if lit_eq_dec (pc_value σ pcc) lit_true then et else ef) pca ->
  (pc_arities_ok pca = true \/ pc_has_var pca = false).

Context {reduce_prim_ite_wellformed_law : ReducePrimIteWellformed}.

(** Substitution on coercions and types preserves concretion under matched environments *)
Class SubstCoercContainsEnv : Prop :=
subst_coerc_contains_env : forall σ S Γs Γc γ,
  contains_env σ S Γs Γc ->
  contains σ S (ECoercion (subst_coerc Γs γ)) (ECoercion (subst_coerc Γc γ)).

Class SubstTypeContainsEnv : Prop :=
subst_type_contains_env : forall σ S Γs Γc τ,
  contains_env σ S Γs Γc ->
  contains σ S (EType (subst_type Γs τ)) (EType (subst_type Γc τ)).

Context {subst_coerc_contains_env_law : SubstCoercContainsEnv}
  {subst_type_contains_env_law : SubstTypeContainsEnv}.

(** ------------------------------------------------------------------------- *)
(** Proven Lemmas on SMT Models, Inversion, and Contexts                      *)
(** ------------------------------------------------------------------------- *)

(** Logical Properties of SMT Models *)

Lemma models_and : forall σ Φ1 Φ2,
  σ ⊨ Φ1 -> σ ⊨ Φ2 -> σ ⊨ (Φ1 ∧ Φ2).
Proof.
  intros σ Φ1 Φ2 H1 H2. apply models_and_iff. split; assumption.
Qed.

(** Environment and Closure Context Lemmas *)

Lemma contains_env_concrete : forall σ S Γs Γc,
  contains_env σ S Γs Γc -> concrete_env Γc.
Proof.
  intros σ S Γs Γc H.
  induction H; [constructor | constructor; assumption].
Qed.

Lemma contains_var_bound : forall σ S Γs x Γ's es ec,
  sym_free_env S Γs ->
  lookup_env Γs x = Some (Γ's, es) ->
  contains σ S (EVar x) ec ->
  ec = EVar x.
Proof.
  intros σ S Γs x Γ's es ec Hfree Hlook Hcont.
  inversion Hcont; subst; [reflexivity | | kill_denote].
  match goal with
  | [ HS : S x = true |- _ ] =>
      specialize (Hfree x HS); rewrite Hlook in Hfree; discriminate
  end.
Qed.

(** This is what makes the theorem say something about genuinely symbolic
    programs. *)
Lemma contains_var_sym : forall σ S x ec,
  S x = true ->
  contains σ S (EVar x) ec ->
  ec = ELit (σ x).
Proof.
  intros σ S x ec Hsym Hcont.
  inversion Hcont; subst; [congruence | congruence | kill_denote].
Qed.

Lemma lookup_env_concore : forall σ S Γs Γc x Γ's es Γ'c ec,
  contains_env σ S Γs Γc ->
  lookup_env Γs x = Some (Γ's, es) ->
  lookup_env Γc x = Some (Γ'c, ec) ->
  concore_expr ec.
Proof.
  intros σ S Γs Γc x Γ's es Γ'c ec Henv.
  revert Γ's es Γ'c ec.
  induction Henv; intros Γ's es' Γ'c ec' Hlooks Hlookc.
  - simpl in Hlooks. discriminate.
  - simpl in Hlooks, Hlookc.
    destruct (String.string_dec x x0).
    + inversion Hlooks; inversion Hlookc; subst.
      assumption.
    + apply IHHenv2 with (Γ's := Γ's) (es := es') (Γ'c := Γ'c) (ec := ec'); assumption.
Qed.

(** Concretion Inversion and Lookup Properties *)

Lemma contains_lookup_env : forall σ S Γs Γc x Γ's es,
  contains_env σ S Γs Γc ->
  lookup_env Γs x = Some (Γ's, es) ->
  exists Γ'c ec,
    lookup_env Γc x = Some (Γ'c, ec) /\
    contains_env σ S Γ's Γ'c /\
    contains σ S es ec.
Proof.
  intros σ S Γs Γc x Γ's es Henv.
  revert Γ's es.
  induction Henv; intros Γ's es' Hlook.
  - simpl in Hlook. discriminate.
  - simpl in Hlook. simpl.
    destruct (String.string_dec x x0).
    + inversion Hlook; subst.
      exists Γc, ec. split; [reflexivity |].
      split; assumption.
    + apply IHHenv2. assumption.
Qed.

Lemma contains_lit_inv : forall σ S l ec,
  contains σ S (ELit l) ec -> ec = ELit l.
Proof.
  intros σ S l ec H. inversion H; subst; [reflexivity | kill_denote].
Qed.

Lemma contains_con_inv : forall σ S d ec,
  contains σ S (ECon d) ec -> ec = ECon d.
Proof.
  intros σ S d ec H. inversion H; subst; [reflexivity | kill_denote].
Qed.

Lemma contains_primop_inv : forall σ S p ec,
  contains σ S (EPrimOp p) ec -> ec = EPrimOp p.
Proof.
  intros σ S p ec H. inversion H; subst; [reflexivity | kill_denote].
Qed.

Lemma contains_lam_inv : forall σ S x body ec,
  contains σ S (ELam x body) ec ->
  exists bodyc, ec = ELam x bodyc /\ S x = false /\ contains σ S body bodyc.
Proof.
  intros σ S x body ec H. inversion H; subst; [| kill_denote].
  exists bodyc. split; [reflexivity | split; assumption].
Qed.

Lemma contains_thunk_inv : forall σ S Γs es ec,
  contains σ S (EThunk Γs es) ec ->
  (exists Γc ec', ec = EThunk Γc ec' /\ contains_env σ S Γs Γc /\ contains σ S es ec')
  \/ (exists Γc, contains_env σ S Γs Γc /\ contains σ S es ec /\ is_thunk ec = true).
Proof.
  intros σ S Γs es ec H. inversion H; subst; [left | right | kill_denote].
  - exists Γc, ec0. split; [reflexivity | auto].
  - exists Γc. auto.
Qed.

Lemma contains_clos_inv : forall σ S Γs x body ec,
  contains σ S (EThunk Γs (ELam x body)) ec ->
  exists Γc bodyc, ec = EThunk Γc (ELam x bodyc) /\ S x = false /\
    contains_env σ S Γs Γc /\
    contains σ S body bodyc.
Proof.
  intros σ S Γs x body ec H.
  destruct (contains_thunk_inv σ S Γs (ELam x body) ec H)
    as [[Γc [ec' [Heq [Henv Hlam]]]] | [Γc [Henv [Hlam Hthunk]]]].
  - destruct (contains_lam_inv σ S x body ec' Hlam) as [bodyc [Heq' [Hx Hbody]]].
    subst. exists Γc, bodyc. auto.
  - destruct (contains_lam_inv σ S x body ec Hlam) as [bodyc [Heq' _]].
    subst. discriminate Hthunk.
Qed.

(**
  An application is the one shape Cont_Denote can also produce, so the
  inversion is a disjunction. The second alternative carries Solvable Γ fs,
  which is what every caller uses to rule it out: a cast, a closure or a
  bottom in function position is not solvable, and neither is a function that
  Rule App-Spine has just declared a computation.

*)
Lemma contains_app_inv : forall σ S Γ fs as_ ec,
  sym_free_env S Γ ->
  contains σ S (EApp fs as_) ec ->
  (exists fc ac, ec = EApp fc ac /\ contains σ S fs fc /\ contains σ S as_ ac)
  \/ (Solvable Γ fs /\ exists p args l,
        unspool_app (EApp fs as_) [] = (EPrimOp p, args) /\
        length args = primop_arity p /\
        smt_ground (EApp fs as_) = false /\
        denote σ S (EApp fs as_) l /\
        ec = ELit l).
Proof.
  intros σ S Γ fs as_ ec Hfree H. inversion H; subst.
  - left. exists f_c, a_c. split; [reflexivity | auto].
  - right.
    match goal with
    | [ Hden : denote σ S (EApp fs as_) ?l |- _ ] =>
        assert (Hsolv : Solvable Γ (EApp fs as_));
          [ destruct Hden as [pc [Hd _]];
            exact (expr_to_pc_solvable Γ (EApp fs as_) pc (Hd Γ Hfree))
          | ]
    end.
    inversion Hsolv as [| | | f a Hop Hf Ha]; subst.
    split; [exact Hf |].
    eexists; eexists; eexists.
    split; [eassumption |]. split; [eassumption |]. split; [eassumption |].
    split; [eassumption | reflexivity].
Qed.

Lemma contains_cast_inv : forall σ S es γ ec,
  contains σ S (ECast es γ) ec ->
  exists ec', ec = ECast ec' γ /\ contains σ S es ec'.
Proof.
  intros σ S es γ ec H. inversion H; subst; [| kill_denote].
  exists ec0. split; [reflexivity | assumption].
Qed.

Lemma contains_case_inv : forall σ S ess altss ec,
  contains σ S (ECase ess altss) ec ->
  exists esc altsc, ec = ECase esc altsc /\ contains σ S ess esc
    /\ Forall2 (contains_alt σ S) altss altsc.
Proof.
  intros σ S ess altss ec H. inversion H; subst; [| kill_denote].
  exists esc, altsc. split; [reflexivity | auto].
Qed.

(** Proven Semantic Simulation Lemmas *)

Lemma eval_app_cast_sound : forall Φ Γs Γc σ S ef γ ea γ_a γ_r er e_con,
  σ ⊨ Φ ->
  contains_env σ S Γs Γc ->
  contains σ S (EApp (ECast ef γ) ea) e_con ->
  concore_expr e_con ->
  closed_instance Γc e_con ->
  decomp_coerc_arrow γ = Some (γ_a, γ_r) ->
  Φ ; Γs ⊢ ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r ⇓ er ->
  (forall (Γc : environment) (σ : valuation) (e_con : expr),
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) e_con ->
    concore_expr e_con ->
    closed_instance Γc e_con ->
    exists v_con : expr,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S er v_con) ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S er v_con.
Proof.
  intros Φ Γs Γc σ S ef γ ea γ_a γ_r er e_con Hmod Henv Hcont Hcon Hcl Hdecomp Heval_pushed_s IH.
  assert (Hfree : sym_free_env S Γs)
    by (destruct (contains_env_sym_free σ S Γs Γc Henv) as [Hf _]; exact Hf).
  destruct (contains_app_inv σ S Γs (ECast ef γ) ea e_con Hfree Hcont) as
    [[fc [ac [Heq [Hcont_f Hcont_a]]]] | [Hsolv _]];
    [subst e_con | exfalso; exact (solvable_not_cast Γs ef γ Hsolv)].
  apply contains_cast_inv in Hcont_f as [efc [Heq_fc Hcont_ef]]; subst fc.
  inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
  inversion Hf as [| | | | | | | efc0 γ0 Hcon_ef | | | | | | ]; subst.
  assert (Hcont_pushed : contains σ S (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r)
                                   (ECast (EApp efc (ECast ac (sym_coerc γ_a))) γ_r)).
  { constructor. constructor; [assumption | constructor; assumption]. }
  assert (Hcon_pushed : concore_expr (ECast (EApp efc (ECast ac (sym_coerc γ_a))) γ_r)).
  { constructor. constructor; [assumption | constructor; assumption]. }
  destruct (closed_instance_program Γc _ Hcl eq_refl) as [HΓc Hsc].
  inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
  inversion Hscf as [| | | | | | | L1 e1 γ1 Hsce | | | | |]; subst.
  assert (Hcl_pushed : closed_instance Γc (ECast (EApp efc (ECast ac (sym_coerc γ_a))) γ_r)).
  { left. split; [exact HΓc |].
    apply Scoped_Cast. apply Scoped_App; [assumption | apply Scoped_Cast; assumption]. }
  destruct (IH Γc σ (ECast (EApp efc (ECast ac (sym_coerc γ_a))) γ_r) Hmod Henv Hcont_pushed Hcon_pushed Hcl_pushed) as [v_con [Heval_pushed Hcont_v]].
  exists v_con.
  split; [| exact Hcont_v].
  unfold eval_con in *.
  eapply Eval_AppCast; eassumption.
Qed.

Lemma spine_head_contains : forall σ S es ec,
  contains σ S es ec ->
  has_whole_spine_rule (spine_head es) = false ->
  has_whole_spine_rule (spine_head ec) = false.
Proof.
  intros σ S es ec H. induction H; intros Hh; simpl in *; try reflexivity; try discriminate Hh.
  - exact (IHcontains1 Hh).
  - destruct ec; try discriminate; reflexivity.
Qed.

Lemma comp_contains : forall σ S Γs Γc ef efc,
  contains_env σ S Γs Γc ->
  contains σ S ef efc ->
  Comp Γs ef ->
  Comp Γc efc \/ exists Γ' x body, efc = EThunk Γ' (ELam x body).
Proof.
  intros σ S Γs Γc ef efc Henv Hcont Hcomp.
  destruct Hcomp as [x Hbound | x body | es alts | Γ' e Hnotlam | f a Hhead].
  - left.
    destruct (lookup_env Γs x) as [[Γ's es] |] eqn:Hlook; [| congruence].
    destruct (contains_env_sym_free σ S Γs Γc Henv) as [Hfree _].
    rewrite (contains_var_bound σ S Γs x Γ's es efc Hfree Hlook Hcont).
    destruct (contains_lookup_env σ S Γs Γc x Γ's es Henv Hlook) as [Γ'c [ec [Hlookc _]]].
    apply Comp_Var. rewrite Hlookc. discriminate.
  - left. apply contains_lam_inv in Hcont as [bodyc [-> _]]. apply Comp_Lam.
  - left. apply contains_case_inv in Hcont as [esc [altsc [-> _]]]. apply Comp_Case.
  - destruct (contains_thunk_inv σ S Γ' e efc Hcont)
      as [[Γc' [ec' [-> _]]] | [_ [_ [_ Hthunk]]]].
    + destruct (is_lam ec') eqn:Hlam.
      * right. destruct ec'; try discriminate Hlam. eexists; eexists; eexists; reflexivity.
      * left. apply Comp_Thunk. exact Hlam.
    + destruct efc; try discriminate Hthunk.
      destruct (is_lam efc) eqn:Hlam.
      * right. destruct efc; try discriminate Hlam. eexists; eexists; eexists; reflexivity.
      * left. apply Comp_Thunk. exact Hlam.
  - left. inversion Hcont; subst.
    + apply Comp_App. exact (spine_head_contains σ S _ _ Hcont Hhead).
    + exfalso.
      match goal with
      | [ Hu : unspool_app (EApp f a) [] = (EPrimOp _, _) |- _ ] =>
          rewrite <- (fst_unspool_app (EApp f a) []), Hu in Hhead; discriminate Hhead
      end.
Qed.

Lemma eval_app_spine_sound : forall Φ Γs Γc σ S ef ea ef' er e_con,
  σ ⊨ Φ ->
  contains_env σ S Γs Γc ->
  contains σ S (EApp ef ea) e_con ->
  concore_expr e_con ->
  closed_instance Γc e_con ->
  Comp Γs ef ->
  (forall (Γc : environment) (e_con : expr),
    contains_env σ S Γs Γc ->
    contains σ S ef e_con ->
    concore_expr e_con ->
    closed_instance Γc e_con ->
    exists v_con : expr,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S ef' v_con) ->
  (forall (Γc : environment) (e_con : expr),
    contains_env σ S Γs Γc ->
    contains σ S (EApp ef' ea) e_con ->
    concore_expr e_con ->
    closed_instance Γc e_con ->
    exists v_con : expr,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S er v_con) ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S er v_con.
Proof.
  intros Φ Γs Γc σ S ef ea ef' er e_con Hmod Henv Hcont Hcon Hcl Hcomp IH1 IH2.
  assert (Hfree : sym_free_env S Γs)
    by (destruct (contains_env_sym_free σ S Γs Γc Henv) as [Hf _]; exact Hf).
  destruct (contains_app_inv σ S Γs ef ea e_con Hfree Hcont) as
    [[fc [ac [Heq [Hcont_f Hcont_a]]]] | [Hsolv _]];
    [subst e_con | exfalso; exact (comp_not_solvable Γs ef Hcomp Hsolv)].
  inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
  destruct (closed_instance_program Γc _ Hcl eq_refl) as [HΓc Hsc].
  inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
  destruct (IH1 Γc fc Henv Hcont_f Hf (or_introl (conj HΓc Hscf))) as [v_f [Heval_f Hcont_vf]].
  destruct (comp_contains σ S Γs Γc ef fc Henv Hcont_f Hcomp)
    as [Hcomp_c | [Γ' [x [body ->]]]].
  - assert (Henv_c : concrete_env Γc) by (eapply contains_env_concrete; eassumption).
    assert (Hcon_vf : concore_expr v_f)
      by (eapply concore_eval_closed; [exact Henv_c | exact Hf | exact (conj HΓc Hscf) | exact Heval_f]).
    assert (Hsc_vf : closed_term v_f)
      by (eapply closed_eval; [exact Henv_c | exact Hf | exact (conj HΓc Hscf) | exact Heval_f]).
    destruct (IH2 Γc (EApp v_f ac) Henv (Cont_App σ S ef' ea v_f ac Hcont_vf Hcont_a)
                (Con_App v_f ac Hcon_vf Ha)
                (or_introl (conj HΓc (Scoped_App _ _ _ (closed_term_scoped _ _ Hsc_vf) Hsca))))
      as [v_con [Heval_app2 Hcont_er]].
    exists v_con. split; [| exact Hcont_er].
    exact (Eval_AppSpine Unlimited pc_true Γc fc ac v_f v_con Hcomp_c Heval_f Heval_app2).
  - unfold eval_con in Heval_f.
    apply (eval_closure_same pc_true Γc Γ' x body v_f sat_pc_true) in Heval_f. subst v_f.
    exact (IH2 Γc _ Henv (Cont_App σ S ef' ea _ ac Hcont_vf Hcont_a) Hcon Hcl).
Qed.

Lemma contains_delay : forall σ S Γs Γc e_s e_c,
  contains_env σ S Γs Γc ->
  contains σ S e_s e_c ->
  contains σ S (delay Γs e_s) (delay Γc e_c).
Proof.
  intros σ S Γs Γc e_s e_c Henv Hcont.
  destruct (is_thunk e_s) eqn:Hs; destruct (is_thunk e_c) eqn:Hc.
  - rewrite (delay_thunk Γs e_s Hs), (delay_thunk Γc e_c Hc). exact Hcont.
  - exfalso. destruct e_s; try discriminate Hs.
    destruct (contains_thunk_inv σ S _ _ e_c Hcont)
      as [[Γ1 [e1 [Heq _]]] | [_ [_ [_ Ht]]]]; [subst e_c; discriminate Hc | congruence].
  - rewrite (delay_not_thunk Γs e_s Hs), (delay_thunk Γc e_c Hc).
    exact (Cont_Thunk_Outer σ S Γs Γc e_s e_c Henv Hcont Hc).
  - rewrite (delay_not_thunk Γs e_s Hs), (delay_not_thunk Γc e_c Hc).
    exact (Cont_Thunk σ S Γs Γc e_s e_c Henv Hcont).
Qed.

(** ------------------------------------------------------------------------- *)
(** Symbolic Evaluation Preserves the SMT Value                               *)
(** ------------------------------------------------------------------------- *)

(** The formula of an application splits into the formula of the operator
    spine and the formula of the last argument, in every scope at once. *)
Lemma denotes_app_inv : forall S e1 e2 pc,
  denotes S (EApp e1 e2) pc ->
  exists p pcs pa,
    pc = PCPrim p (pcs ++ [pa]) /\ denotes S e1 (PCPrim p pcs) /\ denotes S e2 pa.
Proof.
  intros S e1 e2 pc Hden.
  pose proof (Hden · (sym_free_env_empty S)) as H0. simpl in H0.
  destruct (expr_to_pc · e1) as [pc1 |] eqn:E1; [| discriminate].
  destruct pc1 as [x | l | p q1];
    try (destruct (expr_to_pc · e2); discriminate).
  destruct (expr_to_pc · e2) as [pa |] eqn:E2; [| discriminate].
  injection H0 as H0. subst pc.
  exists p, q1, pa. split; [reflexivity | split];
    intros Γ Hfree; specialize (Hden Γ Hfree); simpl in Hden;
    destruct (expr_to_pc Γ e1) as [pc1' |] eqn:E1'; try discriminate;
    destruct pc1' as [x' | l' | p' q'];
      try (destruct (expr_to_pc Γ e2); discriminate);
    destruct (expr_to_pc Γ e2) as [pa' |] eqn:E2'; try discriminate.
  - rewrite (expr_to_pc_functional e1 Γ · (PCPrim p' q') (PCPrim p q1) E1' E1).
    reflexivity.
  - rewrite (expr_to_pc_functional e2 Γ · pa' pa E2' E2). reflexivity.
Qed.

(** A term whose formula is a primitive application is an operator spine, and
    its arguments carry the formula's arguments pointwise. *)
Lemma denotes_unspool : forall e S pop pcs qop eargs,
  denotes S e (PCPrim pop pcs) ->
  unspool_app e [] = (EPrimOp qop, eargs) ->
  pop = qop /\ Forall2 (denotes S) eargs pcs.
Proof.
  induction e; intros S pop pcs qop eargs Hden Hun;
    try (pose proof (Hden · (sym_free_env_empty S)) as H0; simpl in H0;
         discriminate H0).
  - pose proof (Hden · (sym_free_env_empty S)) as H0. simpl in H0.
    injection H0 as H0. subst pcs. simpl in Hun. injection Hun as Hq Hargs.
    subst. split; [reflexivity | constructor].
  - destruct (denotes_app_inv S e1 e2 (PCPrim pop pcs) Hden)
      as [p1 [pcs1 [pa [Heq [Hden1 Hden2]]]]].
    injection Heq as Hp Hpcs. subst p1 pcs.
    assert (Hop : is_op_app e1 = true).
    { pose proof (Hden1 · (sym_free_env_empty S)) as H1.
      exact (expr_to_pc_prim_is_op_app · e1 pop pcs1 H1). }
    destruct (is_op_app_unspool e1 Hop) as [p2 [args2 Hun2]].
    pose proof (unspool_app_shift e1 [] [e2] (EPrimOp p2) args2 Hun2) as Hun2'.
    simpl in Hun2'. simpl in Hun. rewrite Hun2' in Hun.
    injection Hun as Hq Hargs. subst qop eargs.
    destruct (IHe1 S pop pcs1 p2 args2 Hden1 Hun2) as [Hpp Hall].
    split; [exact Hpp |].
    apply Forall2_app; [exact Hall | constructor; [exact Hden2 | constructor]].
Qed.

Ltac denote_absurd :=
  exfalso;
  match goal with
  | [ H : denote _ ?S _ _ |- _ ] =>
      let pc := fresh "pc" in let Hd := fresh "Hd" in
      destruct H as [pc [Hd _]];
      specialize (Hd · (sym_free_env_empty S)); simpl in Hd; discriminate Hd
  end.

(**
  Symbolic evaluation of an SMT term preserves its SMT value. Every rule
  except App-Prim is excluded by the shape of a denoting term, or, for Rule
  Prune, by the model of the path condition. App-Prim is reduce_prim_denote
  applied to arguments the recursion has already handled.

  It is a Fixpoint rather than an induction because App-Prim needs the result
  for every argument in its Forall2, which Coq's derived induction principle
  does not strengthen.

  Unlimited budget only, hence the k0 = Inf premise. At Fin 0 Rule Out-Of-Fuel
  answers EBot BOutOfFuel, and expr_to_pc reads no formula off a bottom, so
  the answer denotes nothing.
*)
Fixpoint eval_denote_fix (k0 : fuel) (Φ : path_condition) (Γ : environment) (e e' : expr)
  (Heval : eval k0 Φ Γ e e') {struct Heval} :
  k0 = Inf ->
  forall σ S l,
    σ ⊨ Φ ->
    sym_free_env S Γ ->
    denote σ S e l ->
    denote σ S e' l.
Proof.
  destruct Heval as
    [ kv Φ Γ x Γ' eb eb' Hlookup Heval_x
    | kv Φ Γ x Hnone
    | kv Φ Γ l0
    | kv Φ Γ econ d args Hunspool_con
    | kv Φ Γ eb γ eb' Heval_e
    | kv Φ Γ Γ' x eb ea eb' Heval_b
    | kv Φ Γ ef ea ef' er Hcomp Heval_f Heval_app2
    | kv Φ Γ b
    | kv Φ Γ ef ea p eargs eargs' Hunspool Harity Hargs
    | kv Φ Γ x eb
    | kv Φ Γ ef γ ea γ_a γ_r er Hdecomp Heval_pushed
    | kv Φ Γ e1 e2 ec et ef args er Hunspool_if Heval_arms
    | kv Φ Γ b ea
    | kv Φ Γ es alts es' er Heval_es Hfold
    | kv Φ Γ ec et ef ec' et' ef' pc_c Heval_c Hpc Heval_t Heval_f
    | kv Φ Γ γ
    | kv Φ Γ eb Hunsat
    | kv Φ Γ τ
    | kv Φ Γ Γ' eb eb' Heval_t
    | Φ Γ eb
    ]; intros Hk0; try discriminate Hk0; injection Hk0 as Hk0; subst kv; intros σ S l Hmod Hfree Hden;
    try denote_absurd.
  - (* Eval_Var: a denoting variable is symbolic, so Γ cannot bind it *)
    exfalso. destruct (denote_var_inv σ S x l Hden) as [Hsx _].
    specialize (Hfree x Hsx). rewrite Hlookup in Hfree. discriminate.
  - (* Eval_SymVar *) exact Hden.
  - (* Eval_Lit *) exact Hden.
  - (* Eval_Con: a denoting term is solvable, so its head is not a constructor *)
    exfalso. destruct Hden as [pc [Hd _]].
    pose proof (expr_to_pc_solvable Γ econ pc (Hd Γ Hfree)) as Hsolv.
    apply unspool_is_con_app in Hunspool_con.
    rewrite (solvable_not_con_app Γ econ Hsolv) in Hunspool_con. discriminate.
  - (* Eval_AppSpine: a denoting spine has a solvable operator, which is not a computation *)
    exfalso. apply (comp_not_solvable _ _ Hcomp).
    destruct Hden as [pc [Hd _]].
    pose proof (expr_to_pc_solvable Γ (EApp ef ea) pc (Hd Γ Hfree)) as Hsolv.
    inversion Hsolv as [| | | f a Hop Hf Ha]; subst. exact Hf.
  - (* Eval_AppPrim *)
    destruct Hden as [pc [Hdenotes Hval]].
    assert (Hop : is_op_app (EApp ef ea) = true)
      by (eapply unspool_is_op_app; exact Hunspool).
    destruct (expr_to_pc_op_app (EApp ef ea) · pc Hop
                (Hdenotes · (sym_free_env_empty S))) as [p1 [pcs Hpc]].
    subst pc.
    destruct (denotes_unspool (EApp ef ea) S p1 pcs p eargs Hdenotes Hunspool)
      as [Hp1 Hpcs]. subst p1.
    assert (Hres : Forall2 (denote σ S) eargs' (map (pc_value σ) pcs)).
    { clear Hunspool Harity Hval Hop Hdenotes.
      revert pcs Hpcs.
      induction Hargs as [| a a' atl atl' Ha Htl IHtl]; intros pcs Hpcs.
      - inversion Hpcs; subst. constructor.
      - inversion Hpcs as [| a0 pc0 atl0 pctl Hden_a Hden_tl]; subst.
        simpl. constructor.
        + exact (eval_denote_fix Inf Φ Γ a a' Ha eq_refl σ S (pc_value σ pc0) Hmod Hfree
                   (ex_intro _ pc0 (conj Hden_a eq_refl))).
        + exact (IHtl pctl Hden_tl). }
    rewrite <- Hval. simpl.
    exact (reduce_prim_denote σ S p eargs' (map (pc_value σ) pcs) Hres).
  - exfalso. destruct Hden as [pc [Hd _]].
    exact (solvable_unspool_not_if _ _ _ _ _ _ _
             (expr_to_pc_solvable Γ (EApp e1 e2) pc (Hd Γ Hfree)) Hunspool_if).
  - (* Eval_Prune: unreachable under a model of the path condition *)
    exfalso. apply models_sat in Hmod. rewrite Hunsat in Hmod. discriminate.
Qed.

Lemma eval_denote : forall Φ Γ σ S e e' l,
  σ ⊨ Φ ->
  sym_free_env S Γ ->
  Φ ; Γ ⊢ e ⇓ e' ->
  denote σ S e l ->
  denote σ S e' l.
Proof.
  intros Φ Γ σ S e e' l Hmod Hfree Heval Hden.
  exact (eval_denote_fix Inf Φ Γ e e' Heval eq_refl σ S l Hmod Hfree Hden).
Qed.

(**
  SMT condition truth preservation across evaluation, FOR MODELS OF THE PATH
  CONDITION THE EVALUATION RAN UNDER.

  Both hypotheses are needed, and each one blocks a rule that would otherwise
  make the statement false.

  σ ⊨ Φ: Rule Prune lets any expression reduce to EBot BUnreachable whenever
  sat Φ = false, and EBot denotes no path-condition formula. Untied from Φ,
  the statement would say that every condition becomes unjudgeable as soon as
  ONE unsatisfiable path condition exists, and no symbolic branch could then
  be concretised. Under σ ⊨ Φ, models_sat gives sat Φ = true and Rule Prune
  cannot fire.

  sym_free_env S Γ: without it, take Γ binding x and evaluate the condition x
  by Rule Var to EBot BUndefined, which denotes no formula. The statement
  would then prove that no model satisfies the atom x, emptying out models on
  variables and making the non-vacuity checks in NonVacuity/SoundnessInstances.v
  hollow.

  Both were assumed until the verdict was defined from the value. Now the
  existence half is eval_denote above, and the verdict half is pc_value_sound
  in Soundness/Instance.v, which holds because ⊨ is read off pc_value.
*)
Lemma eval_models_cond : forall Φ Γ S ec ec' σ,
  σ ⊨ Φ -> sym_free_env S Γ ->
  Φ ; Γ ⊢ ec ⇓ ec' -> models_cond σ S ec -> models_cond σ S ec'.
Proof.
  intros Φ Γ S ec ec' σ Hmod Hfree Heval [pc [Hden Hsat]].
  destruct (eval_denote Φ Γ σ S ec ec' (pc_value σ pc) Hmod Hfree Heval
              (ex_intro _ pc (conj Hden eq_refl))) as [pc' [Hden' Hval']].
  exists pc'. split; [exact Hden' | exact (pc_value_sound σ pc pc' (eq_sym Hval') Hsat)].
Qed.

(** The negated form needs nothing about op_not: ¬ is the primitive
    application op_not, so equal values give equal values under it. *)
Lemma eval_models_not_cond : forall Φ Γ S ec ec' σ,
  σ ⊨ Φ -> sym_free_env S Γ ->
  Φ ; Γ ⊢ ec ⇓ ec' -> models_not_cond σ S ec -> models_not_cond σ S ec'.
Proof.
  intros Φ Γ S ec ec' σ Hmod Hfree Heval [pc [Hden Hsat]].
  destruct (eval_denote Φ Γ σ S ec ec' (pc_value σ pc) Hmod Hfree Heval
              (ex_intro _ pc (conj Hden eq_refl))) as [pc' [Hden' Hval']].
  exists pc'. split; [exact Hden' |].
  apply (pc_value_sound σ (¬ pc) (¬ pc')); [| exact Hsat].
  unfold pc_not. simpl. rewrite Hval'. reflexivity.
Qed.

End ConCore.
