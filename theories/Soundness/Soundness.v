From SymCoreTheory Require Export Soundness.MergeKeeps.
From Stdlib Require Import Strings.String Lists.List Lia Arith.PeanoNat.
Import ListNotations.

Section ConCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}
  {reduce_prim_solvable_law : ReducePrimSolvable}
  {reduce_prim_saturated_law : ReducePrimSaturated}
  {reduce_prim_concore_law : ReducePrimConcore} {cast_expr_concore_law : CastExprConcore}
  {reduce_prim_scoped_law : ReducePrimScoped} {cast_expr_scoped_law : CastExprScoped}
  {models_sat_law : ModelsSat} {prim_value_and_law : PrimValueAnd}.
Context {reduce_prim_contains_law : ReducePrimContains}
  {reduce_prim_denote_law : ReducePrimDenote}
  {reduce_prim_ground_value_law : ReducePrimGroundValue}.
Context {cast_expr_contains_law : CastExprContains}.
Context {reduce_prim_ite_wellformed_law : ReducePrimIteWellformed}.
Context {subst_coerc_contains_env_law : SubstCoercContainsEnv}
  {subst_type_contains_env_law : SubstTypeContainsEnv}.

(** ========================================================================= *)
(** Soundness of Symbolic Execution                                           *)
(** ========================================================================= *)

(**
  Proved as a pair of mutually recursive fixpoints rather than by plain
  induction on the `eval`/`fold_alts` derivation. The Eval_AppPrim case needs
  soundness for every argument in its Forall2 (eval Inf Φ Γ) args args', and
  Eval_Case/FoldAlts_Con need it for the nested eval buried inside fold_alts.
  Coq's auto-derived induction principle for a mutually-recursive family
  covers neither: it strengthens only direct recursive occurrences, not ones
  nested inside a Forall2 or the sibling relation. The fixpoints recurse
  through those by hand, by induction on the embedded Forall2 or fold_alts
  proof, calling back into the fixpoint being defined.

  Unlimited budget only, hence the k0 = Inf premise on both fixpoints. The
  conclusion asks for a CONCRETE value that the symbolic value contains, and
  concrete evaluation has no budget of its own: it is fixed at Inf by
  eval_con. At Fin 0 the symbolic side answers EBot BOutOfFuel, which
  contains only a concrete EBot BOutOfFuel, and no concrete expression
  reduces to that.
*)

Fixpoint concore_soundness_fix (k0 : fuel) (Φ : path_condition) (Γs : environment) (e_sym v_sym : expr)
  (Heval : eval k0 Φ Γs e_sym v_sym) {struct Heval} :
  k0 = Inf ->
  forall Γc σ S e_con,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    concore_expr e_con ->
    closed_instance Γc e_con ->
    sym_scoped_env S Γs ->
    sym_scoped S (dom_env Γs) e_sym ->
    exists v_con,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\
      contains σ S v_sym v_con
with concore_soundness_fold_fix (k0 : fuel) (Φ : path_condition) (Γs : environment) (escrut : expr) (alts : list alt) (er : expr)
  (Hfold : fold_alts k0 Φ Γs escrut alts er) {struct Hfold} :
  k0 = Inf ->
  forall Γc σ S vsc altsc,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    concore_expr vsc ->
    Forall concore_alt altsc ->
    scoped_env Γc ->
    closed_term vsc ->
    Forall (scoped_alt (dom_env Γc)) altsc ->
    merge_keeps σ S escrut vsc ->
    Forall2 (contains_alt σ S) alts altsc ->
    sym_scoped_env S Γs ->
    sym_scoped S nil escrut ->
    Forall (sym_scoped_alt S (dom_env Γs)) alts ->
    exists v_con,
      fold_alts Inf pc_true Γc vsc altsc v_con /\ contains σ S er v_con.
Proof.
{
  destruct Heval as
    [ kv Φ Γ x Γ' e e' Hlookup Heval_x
    | kv Φ Γ x Hnone
    | kv Φ Γ l
    | kv Φ Γ esp d args Hunspool_con
    | kv Φ Γ e γ e' Heval_e
    | kv Φ Γ Γ' x eb ea eb' Heval_b
    | kv Φ Γ ef ea ef' er Hcomp Heval_f Heval_app2
    | kv Φ Γ b
    | kv Φ Γ ef ea p args args' Hunspool Harity Hargs
    | kv Φ Γ x e
    | kv Φ Γ ef γ ea γ_a γ_r er Hdecomp Heval_pushed
    | kv Φ Γ e1 e2 ec et ef args er Hunspool_if Heval_arms
    | kv Φ Γ b ea
    | kv Φ Γ es alts es' er Heval_es Hfold
    | kv Φ Γ ec et ef ec' et' ef' pc_c Heval_c Hpc Heval_t Heval_f
    | kv Φ Γ γ
    | kv Φ Γ e Hunsat
    | kv Φ Γ τ
    | kv Φ Γ Γ' e e' Heval_t
    | Φ Γ e
    ]; intros Hk0; try discriminate Hk0; injection Hk0 as Hk0; subst kv;
      intros Γc σ S e_con Hmod Henv Hcont Hcon Hcl HsymE Hsym.
  - (* Eval_Var *)
    assert (Hfree : sym_free_env S Γ)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
    assert (Heq : e_con = EVar x) by (eapply contains_var_bound; eassumption).
    subst e_con.
    destruct (contains_lookup_env σ S Γ Γc x Γ' e Henv Hlookup) as [Γ'c [ec [Hlookc [Henv' Hcont']]]].
    assert (Hcon' : concore_expr ec) by (apply (lookup_env_concore σ S Γ Γc x Γ' e Γ'c ec Henv Hlookup Hlookc)).
    destruct (closed_instance_program Γc (EVar x) Hcl eq_refl) as [HΓc _].
    destruct (lookup_env_scoped Γc x Γ'c ec HΓc Hlookc) as [HΓ'c Hsc'].
    destruct (sym_lookup_env_scoped S Γ x Γ' e HsymE Hlookup) as [HsymE' Hsym'].
    destruct (concore_soundness_fix Inf Φ Γ' e e' Heval_x eq_refl Γ'c σ S ec Hmod Henv' Hcont' Hcon'
                (or_introl (conj HΓ'c Hsc')) HsymE' Hsym') as [v_con [Hevalc Hcont_v]].
    exists v_con. split; [| exact Hcont_v].
    unfold eval_con. eapply Eval_Var; eassumption.
  - (* Eval_SymVar: an unbound variable is its own value. Either it is one of
       the symbolic variables, and σ sends it to a literal, which is its own
       value concretely; or it is not, and it stands for itself on both
       sides - the concrete environment leaves it unbound too. *)
    destruct (S x) eqn:Hsx.
    + assert (Heq : e_con = ELit (σ x)) by (eapply contains_var_sym; eassumption).
      subst e_con.
      exists (ELit (σ x)). split.
      * unfold eval_con. apply Eval_Lit.
      * apply Cont_Var_Sym. exact Hsx.
    + assert (Heq : e_con = EVar x).
      { inversion Hcont; subst; [congruence | congruence | kill_denote]. }
      subst e_con.
      exists (EVar x). split.
      * unfold eval_con. apply Eval_SymVar.
        eapply contains_env_lookup_none; eassumption.
      * apply Cont_Var_Bound. exact Hsx.
  - (* Eval_Lit *)
    apply contains_lit_inv in Hcont; subst.
    exists (ELit l). split; [apply Eval_Lit | apply Cont_Lit].
  - (* Eval_Con *)
    destruct (contains_unspool_con σ S esp e_con Hcont [] [] (Forall2_nil _) d args Hunspool_con)
      as [args_c [Hunspool_c Hargs_c]].
    exists (make_con_app d (map (delay Γc) args_c)). split.
    + unfold eval_con. exact (Eval_Con Unlimited pc_true Γc e_con d args_c Hunspool_c).
    + exact (contains_con_value σ S Γ Γc d args args_c Henv Hargs_c).
  - (* Eval_Cast *)
    apply contains_cast_inv in Hcont as [ec [Heq Hcont_e]]; subst.
    inversion Hcon as [| | | | | | | ec0 γ0 Hcon_e | | | | | | ]; subst.
    destruct (closed_instance_program Γc _ Hcl eq_refl) as [HΓc Hsc].
    inversion Hsc as [| | | | | | | L1 e1 γ1 Hsce | | | | |]; subst.
    inversion Hsym as [| | | | | | | L2 e2 γ2 Hsym_e | | | | |]; subst.
    destruct (concore_soundness_fix Inf Φ Γ e e' Heval_e eq_refl Γc σ S ec Hmod Henv Hcont_e Hcon_e
                (or_introl (conj HΓc Hsce)) HsymE Hsym_e) as [vc [Hevalc Hcont_v]].
    exists (cast_expr vc γ). split; [unfold eval_con; apply Eval_Cast; exact Hevalc | apply cast_expr_contains; exact Hcont_v].
  - (* Eval_AppAbs *)
    assert (Hfree : sym_free_env S Γ)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
    destruct (contains_app_inv σ S Γ (EThunk Γ' (ELam x eb)) ea e_con Hfree Hcont) as
      [[fc [ac [Heq [Hcont_f Hcont_a]]]] | [Hsolv _]];
      [subst e_con | exfalso; inversion Hsolv].
    apply contains_clos_inv in Hcont_f as [Γ'c [ebc [Heq_f [Hsx [Henv_clos Hcont_b]]]]]; subst.
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | | | | | | | | Γ0 e0 Henv_clos_c Hcon_lam]; subst.
    inversion Hcon_lam as [| | | | | x0 body Hcon_b | | | | | | | | ]; subst.
    destruct (closed_instance_program Γc _ Hcl eq_refl) as [HΓc Hsc].
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    inversion Hscf as [| | | | | | | | | | | | L1 Γ1 e1 HΓ'c Hsclam]; subst.
    inversion Hsclam as [| | | | | L2 x2 b2 Hscb | | | | | | |]; subst.
    assert (Henv_ext : contains_env σ S (ExtendEnv x (MkClosure Γ ea) Γ') (ExtendEnv x (MkClosure Γc ac) Γ'c)).
    { apply Cont_Env_Extend; assumption. }
    inversion Hsym as [| | | | L3 f3 a3 Hsymf Hsyma | | | | | | | |]; subst.
    inversion Hsymf as [| | | | | | | | | | | | L4 Γ4 e4 HsymΓ' Hsymlam]; subst.
    inversion Hsymlam as [| | | | | L5 x5 b5 Hsymb | | | | | | |]; subst.
    assert (HsymE_ext : sym_scoped_env S (ExtendEnv x (MkClosure Γ ea) Γ'))
      by (apply SymScoped_Env_Extend; assumption).
    destruct (concore_soundness_fix Inf Φ (extend_env Γ' x Γ ea) eb eb' Heval_b eq_refl
                (ExtendEnv x (MkClosure Γc ac) Γ'c) σ S ebc Hmod Henv_ext Hcont_b Hcon_b
                (or_introl (conj (Scoped_Env_Extend x Γc ac Γ'c HΓc Hsca HΓ'c) Hscb))
                HsymE_ext Hsymb)
      as [v_con [Heval_b' Hcont_v]].
    exists v_con. split; [| exact Hcont_v].
    unfold eval_con. apply Eval_AppAbs. exact Heval_b'.
  - (* Eval_AppSpine *)
    inversion Hsym as [| | | | L0 f0 a0 Hsym_f Hsym_a | | | | | | | |]; subst.
    assert (Hsym_f' : sym_scoped S (dom_env Γ) ef')
      by (apply sym_scoped_nil_any;
          exact (sym_eval_scoped_fix Inf Φ Γ ef ef' Heval_f S HsymE Hsym_f)).
    apply (eval_app_spine_sound Φ Γ Γc σ S ef ea ef' er e_con Hmod Henv Hcont Hcon Hcl Hcomp).
    + intros Γc0 e_con0 Henv0 Hcont0 Hcon0 Hcl0.
      exact (concore_soundness_fix Inf Φ Γ ef ef' Heval_f eq_refl Γc0 σ S e_con0 Hmod Henv0 Hcont0 Hcon0 Hcl0
               HsymE Hsym_f).
    + intros Γc0 e_con0 Henv0 Hcont0 Hcon0 Hcl0.
      exact (concore_soundness_fix Inf Φ Γ (EApp ef' ea) er Heval_app2 eq_refl Γc0 σ S e_con0 Hmod Henv0 Hcont0 Hcon0 Hcl0
               HsymE (SymScoped_App S (dom_env Γ) ef' ea Hsym_f' Hsym_a)).
  - (* Eval_Bot *)
    inversion Hcont; subst; [| kill_denote].
    exists (EBot b). split; [apply Eval_Bot | apply Cont_Bot].
  - (* Eval_AppPrim *)
    assert (Hfree : sym_free_env S Γ)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
    assert (Hfree_c : sym_free_env S Γc)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [_ Hf]; exact Hf).
    destruct (contains_app_inv σ S Γ ef ea e_con Hfree Hcont) as
      [[fc [ac [Heq [Hcont_f Hcont_a]]]] |
       [Hsolv_f [p0 [args0 [lv [Hun0 [Har0 [Hg0 [Hden0 Heq]]]]]]]]];
      subst e_con;
      [| rewrite Hunspool in Hun0; injection Hun0 as Hp0 Hargs0; subst p0 args0;
         exists (ELit lv); split; [unfold eval_con; apply Eval_Lit |];
         assert (Hden' : denote σ S (reduce_prim p args') lv)
           by (eapply eval_denote;
               [ exact Hmod | exact Hfree
               | eapply Eval_AppPrim; [exact Hunspool | exact Harity | exact Hargs]
               | exact Hden0 ]);
         assert (Hsolv_r : Solvable Γc (reduce_prim p args'))
           by (destruct Hden' as [pcr [Hdr _]];
               exact (expr_to_pc_solvable Γc _ pcr (Hdr Γc Hfree_c)));
         remember (reduce_prim p args') as rt eqn:Hrt;
         destruct Hsolv_r as [l0 | y Hy | q | f a Hop Hf Ha];
         [ rewrite <- (denote_lit_inv σ S l0 lv Hden'); apply Cont_Lit
         | destruct (denote_var_inv σ S y lv Hden') as [Hsy Hlv];
           rewrite Hlv; apply Cont_Var_Sym; exact Hsy
         | exfalso;
           destruct (reduce_prim_ground_value p args'
                       (ltac:(rewrite <- Hrt; reflexivity))) as [l1 Hl1];
           rewrite <- Hrt in Hl1; discriminate Hl1
         | destruct (smt_ground (EApp f a)) eqn:Hg;
           [ exfalso;
             destruct (reduce_prim_ground_value p args'
                         (ltac:(rewrite <- Hrt; exact Hg))) as [l1 Hl1];
             rewrite <- Hrt in Hl1; discriminate Hl1
           | destruct (is_op_app_unspool (EApp f a) Hop) as [q [qargs Hunq]];
             apply (Cont_Denote σ S (EApp f a) q qargs lv Hunq);
             [ eapply reduce_prim_saturated; rewrite Hrt in Hunq; exact Hunq
             | exact Hg | exact Hden' ] ] ] ].
    inversion Hcon as [| | | | fc0 ac0 Hcon_f Hcon_a | | | | | | | | | ]; subst.
    destruct (closed_instance_program Γc _ Hcl eq_refl) as [HΓc Hsc].
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    assert (Henv_c : concrete_env Γc) by (eapply contains_env_concrete; exact Henv).
    assert (HL : Forall2 (contains σ S) [ea] [ac])
      by (constructor; [exact Hcont_a | constructor]).
    assert (Hne : [ea] <> (@nil expr)) by discriminate.
    destruct (contains_unspool_primop σ S ef fc Hcont_f [ea] [ac] HL Hne p args
               Hunspool Harity) as [args_c [Hunspool_c Hcont_args]].
    assert (Hconcore_args_c : Forall concore_expr args_c).
    { eapply unspool_app_concore; [exact Hunspool_c | exact Hcon_f | constructor; [exact Hcon_a | constructor]]. }
    assert (Hsc_args_c : Forall (scoped (dom_env Γc)) args_c).
    { eapply unspool_app_scoped; [exact Hunspool_c | exact Hscf | constructor; [exact Hsca | constructor]]. }
    assert (Hsym_args : Forall (sym_scoped S (dom_env Γ)) args).
    { exact (proj2 (sym_unspool_app_scoped S (dom_env Γ) (EApp ef ea) [] (EPrimOp p) args
                      Hunspool Hsym (Forall_nil _))). }
    assert (Hstep : exists args_c', Forall2 (eval Inf pc_true Γc) args_c args_c'
                    /\ Forall2 (contains σ S) args' args_c' /\ Forall closed_term args_c').
    { clear Hunspool Harity Hunspool_c.
      revert args_c Hcont_args Hconcore_args_c Hsc_args_c Hsym_args.
      induction Hargs as [| a a' args_tl args'_tl Ha Hargs_tl IHargs];
        intros args_c Hcont_args Hconcore_args_c Hsc_args_c Hsym_args.
      - inversion Hcont_args; subst.
        exists []. split; [constructor | split; constructor].
      - inversion Hcont_args as [| a0 ac1 args_tl0 args_c_tl Hcont_a1 Hcont_tl Heqa Heqargs]; subst.
        inversion Hconcore_args_c as [| ac2 args_c_tl2 Hcon_a1 Hcon_tl]; subst.
        inversion Hsc_args_c as [| ac3 args_c_tl3 Hsc_a1 Hsc_tl]; subst.
        inversion Hsym_args as [| a4 args_tl4 Hsym_a1 Hsym_tl]; subst.
        destruct (concore_soundness_fix Inf Φ Γ a a' Ha eq_refl Γc σ S ac1 Hmod Henv Hcont_a1 Hcon_a1
                    (or_introl (conj HΓc Hsc_a1)) HsymE Hsym_a1)
          as [v_a [Heval_a Hcont_va]].
        destruct (IHargs args_c_tl Hcont_tl Hcon_tl Hsc_tl Hsym_tl)
          as [args_c'_tl [Heval_tl [Hcont_tl' Hcl_tl]]].
        exists (v_a :: args_c'_tl).
        split; [constructor; assumption | split; [constructor; assumption | constructor; [| exact Hcl_tl]]].
        exact (closed_eval Γc ac1 v_a Henv_c Hcon_a1 (conj HΓc Hsc_a1) Heval_a).
    }
    destruct Hstep as [args_c' [Heval_args_c [Hcont_args' Hcl_args']]].
    exists (reduce_prim p args_c').
    split.
    + unfold eval_con. eapply Eval_AppPrim.
      * exact Hunspool_c.
      * assert (Hlen : length args_c = length args) by (symmetry; eapply Forall2_length; exact Hcont_args).
        rewrite Hlen. exact Harity.
      * exact Heval_args_c.
    + apply reduce_prim_contains; [exact Hcl_args' | exact Hcont_args'].
  - (* Eval_Lam *)
    apply contains_lam_inv in Hcont as [bodyc [Heq [Hsx Hcont_body]]]; subst.
    exists (EThunk Γc (ELam x bodyc)).
    split; [apply Eval_Lam | apply Cont_Thunk; [exact Henv | apply Cont_Lam; assumption]].
  - (* Eval_AppCast *)
    inversion Hsym as [| | | | L0 f0 a0 Hsym_f Hsym_a | | | | | | | |]; subst.
    inversion Hsym_f as [| | | | | | | L1 e1 γ1 Hsym_ef | | | | |]; subst.
    assert (Hsym_pushed : sym_scoped S (dom_env Γ) (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r))
      by (apply SymScoped_Cast; apply SymScoped_App;
          [exact Hsym_ef | apply SymScoped_Cast; exact Hsym_a]).
    eapply eval_app_cast_sound; try eassumption.
    intros Γc0 σ0 e_con0 Hmod0 Henv0 Hcont0 Hcon0 Hcl0.
    exact (concore_soundness_fix Inf Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er Heval_pushed eq_refl Γc0 σ0 S e_con0 Hmod0 Henv0 Hcont0 Hcon0 Hcl0
             HsymE Hsym_pushed).
  - (* Eval_AppIf *)
    destruct (sym_unspool_app_scoped S (dom_env Γ) (EApp e1 e2) [] (EIf ec et ef) args
                Hunspool_if Hsym (Forall_nil _)) as [Hsym_if Hsym_args].
    inversion Hsym_if as [| | | | | | | | | | L1 ec1 et1 ef1 Hsym_c Hsym_t Hsym_f | |]; subst.
    exact (concore_soundness_fix Inf Φ Γ _ er Heval_arms eq_refl Γc σ S e_con Hmod Henv
             (contains_app_if_spine σ S e1 e2 ec et ef args e_con Hcont Hunspool_if) Hcon Hcl
             HsymE (SymScoped_If S (dom_env Γ) ec _ _ Hsym_c
                     (sym_scoped_fold_left_app S (dom_env Γ) args et Hsym_args Hsym_t)
                     (sym_scoped_fold_left_app S (dom_env Γ) args ef Hsym_args Hsym_f))).
  - (* Eval_AppBot *)
    assert (Hfree : sym_free_env S Γ)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
    destruct (contains_app_inv σ S Γ (EBot b) ea e_con Hfree Hcont) as
      [[fc [ac [Heq [Hcont_f Hcont_a]]]] | [Hsolv _]];
      [subst e_con | exfalso; inversion Hsolv].
    inversion Hcont_f; subst; [| kill_denote].
    exists (EBot b). split; [apply Eval_AppBot | constructor].
  - (* Eval_Case *)
    apply contains_case_inv in Hcont as [esc [altsc [Heq [Hcont_es Hcont_alts]]]]; subst.
    inversion Hcon as [| | | | | | es0 alts0 Hcon_es Hcon_alts | | | | | | | ]; subst.
    destruct (closed_instance_program Γc _ Hcl eq_refl) as [HΓc Hsc].
    inversion Hsc as [| | | | | | L0 es1 alts1 Hsc_es Hsc_alts | | | | | |]; subst.
    inversion Hsym as [| | | | | | L1 es2 alts2 Hsym_es Hsym_alts | | | | | |]; subst.
    destruct (concore_soundness_fix Inf Φ Γ es es' Heval_es eq_refl Γc σ S esc Hmod Henv Hcont_es Hcon_es
                (or_introl (conj HΓc Hsc_es)) HsymE Hsym_es) as [vc_s [Heval_esc Hcont_vs]].
    assert (Hsym_es' : sym_scoped S nil es')
      by exact (sym_eval_scoped_fix Inf Φ Γ es es' Heval_es S HsymE Hsym_es).
    assert (Henv_c : concrete_env Γc) by (eapply contains_env_concrete; exact Henv).
    assert (Hcon_vcs : concore_expr vc_s)
      by exact (concore_eval_closed Γc esc vc_s Henv_c Hcon_es (conj HΓc Hsc_es) Heval_esc).
    assert (Hcl_vcs : closed_term vc_s)
      by exact (closed_eval Γc esc vc_s Henv_c Hcon_es (conj HΓc Hsc_es) Heval_esc).
    assert (Hsym_merge : sym_scoped S nil (merge Γ es')).
    { destruct es' as [ | | | | | | | | | | vc vt vf | | ]; simpl; try exact Hsym_es'.
      inversion Hsym_es' as [| | | | | | | | | | L2 vc2 vt2 vf2 Hvc Hvt Hvf | |]; subst.
      apply ite_sym_scoped; assumption. }
    destruct (concore_soundness_fold_fix Inf Φ Γ (merge Γ es') alts er Hfold eq_refl Γc σ S vc_s altsc
                Hmod Henv Hcon_vcs Hcon_alts HΓc Hcl_vcs Hsc_alts
                (merge_contains σ S Γ es' vc_s Hsym_es' Hcont_vs) Hcont_alts
                HsymE Hsym_merge Hsym_alts) as [v_con [Hfold_c Hcont_er]].
    exists v_con. split; [| exact Hcont_er].
    unfold eval_con. eapply Eval_Case; [exact Heval_esc |].
    rewrite (merge_concore_id Γc vc_s Hcon_vcs). exact Hfold_c.
  - (* Eval_If *)
    assert (Hfree : sym_free_env S Γ)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
    inversion Hsym as [| | | | | | | | | | L0 ec0 et0 ef0 Hsym_c Hsym_t Hsym_f | |]; subst.
    inversion Hcont; subst.
    + assert (Hcond' : models_cond σ S ec')
        by (apply eval_models_cond with (Φ:=Φ)(Γ:=Γ)(ec:=ec); assumption).
      assert (Hpc_mod : σ ⊨ pc_c) by (apply (models_cond_pc σ S Γ ec' pc_c Hpc); exact Hcond').
      assert (Hmod_and : σ ⊨ (Φ ∧ pc_c)) by (apply models_and; assumption).
      destruct (concore_soundness_fix Inf (Φ ∧ pc_c) Γ et et' Heval_t eq_refl Γc σ S e_con Hmod_and Henv H4 Hcon Hcl
                  HsymE Hsym_t) as [v_con [Hevalc' Hcont_v]].
      exists v_con. split; [exact Hevalc' |]. apply Cont_If_True; [exact Hcond' | exact Hcont_v].
    + assert (Hncond' : models_not_cond σ S ec')
        by (apply eval_models_not_cond with (Φ:=Φ)(Γ:=Γ)(ec:=ec); assumption).
      assert (Hpc_mod : σ ⊨ (¬ pc_c)) by (apply (models_not_cond_pc σ S Γ ec' pc_c Hpc); exact Hncond').
      assert (Hmod_and : σ ⊨ (Φ ∧ ¬ pc_c)) by (apply models_and; assumption).
      destruct (concore_soundness_fix Inf (Φ ∧ ¬ pc_c) Γ ef ef' Heval_f eq_refl Γc σ S e_con Hmod_and Henv H4 Hcon Hcl
                  HsymE Hsym_f) as [v_con [Hevalc' Hcont_v]].
      exists v_con. split; [exact Hevalc' |]. apply Cont_If_False; [exact Hncond' | exact Hcont_v].
    + kill_denote.
  - (* Eval_Coercion *)
    inversion Hcont; subst; [| kill_denote].
    exists (ECoercion (subst_coerc Γc γ)).
    split; [apply Eval_Coercion | apply subst_coerc_contains_env; assumption].
  - (* Eval_Prune *)
    apply models_sat in Hmod. rewrite Hunsat in Hmod. discriminate.
  - (* Eval_Type *)
    inversion Hcont; subst; [| kill_denote].
    exists (EType (subst_type Γc τ)).
    split; [apply Eval_Type | apply subst_type_contains_env; assumption].
  - (* Eval_Thunk *)
    inversion Hsym as [| | | | | | | | | | | | L0 Γ0 e0 HsymE' Hsym_e]; subst.
    destruct (contains_thunk_inv σ S Γ' e e_con Hcont)
      as [[Γ'c [ec [Heq [Henv' Hcont_e]]]] | [Γ'c [Henv' [Hcont_e Hthunk]]]].
    + subst e_con.
      inversion Hcon as [| | | | | | | | | | | | | Γ0 e0 Henv_c He_c]; subst.
      assert (Hcl' : closed_instance Γ'c ec).
      { left. destruct Hcl as [[_ Hs] | [_ Hs]]; inversion Hs; subst; split; assumption. }
      destruct (concore_soundness_fix Inf Φ Γ' e e' Heval_t eq_refl Γ'c σ S ec
                  Hmod Henv' Hcont_e He_c Hcl' HsymE' Hsym_e) as [v_con [Hevalc Hcont_v]].
      exists v_con. split; [| exact Hcont_v].
      unfold eval_con. apply Eval_Thunk. exact Hevalc.
    + assert (Hcl' : closed_instance Γ'c e_con).
      { right. split; [exact Hthunk |].
        destruct Hcl as [[_ Hs] | [_ Hs]]; [| exact Hs].
        destruct e_con; try discriminate Hthunk. exact (scoped_thunk_any _ _ _ _ Hs). }
      destruct (concore_soundness_fix Inf Φ Γ' e e' Heval_t eq_refl Γ'c σ S e_con
                  Hmod Henv' Hcont_e Hcon Hcl' HsymE' Hsym_e) as [v_con [Hevalc Hcont_v]].
      exists v_con. split; [| exact Hcont_v].
      destruct e_con; try discriminate Hthunk.
      unfold eval_con in *. exact (eval_thunk_ambient_env Inf pc_true Γ'c Γc _ _ _ Hevalc).
}
{
  destruct Hfold as
    [ kv Φ Γ ec et ef alts et' ef' pc_c Hpc Hfold_t Hfold_f
    | kv Φ Γ ec et ef alts Hpc_none
    | kv Φ Γ e d ea xs ep alts er Hdec Halt Heval_ep
    | kv Φ Γ b alts
    | kv Φ Γ e pc alts r Hpcg Hvarg Hrec
    | kv Φ Γ e pc alts r1 r2 Hpcs Hvars Hars Hf1 Hf2
    | kv Φ Γ e alts Hpcnone Hopnone Hnothead Hnoalt Hnotbot
    ]; intros Hk0; subst kv;
      intros Γc σ S vsc altsc Hmod Henv Hcon_vsc Hcon_altsc HΓc Hcl_vsc Hsc_altsc Hkeeps Halts
             HsymE Hsym_scrut Hsym_alts.
  - (* FoldAlts_If *)
    apply (merge_keeps_of_branch σ S ec et ef vsc) in Hkeeps.
    inversion Hsym_scrut as [| | | | | | | | | | L0 ec0 et0 ef0 Hsym_c Hsym_t Hsym_f | |]; subst.
    inversion Hkeeps; subst.
    + assert (Hpc_mod : σ ⊨ pc_c) by (apply (models_cond_pc σ S Γ ec pc_c Hpc); assumption).
      assert (Hmod_and : σ ⊨ (Φ ∧ pc_c)) by (apply models_and; assumption).
      destruct (concore_soundness_fold_fix Inf (Φ ∧ pc_c) Γ et alts et' Hfold_t eq_refl Γc σ S vsc altsc
                  Hmod_and Henv Hcon_vsc Hcon_altsc HΓc Hcl_vsc Hsc_altsc
                  (or_introl H4) Halts HsymE Hsym_t Hsym_alts) as [v_con [Hfold_c Hcont_er]].
      exists v_con. split; [exact Hfold_c | apply Cont_If_True; assumption].
    + assert (Hpc_mod : σ ⊨ (¬ pc_c)) by (apply (models_not_cond_pc σ S Γ ec pc_c Hpc); assumption).
      assert (Hmod_and : σ ⊨ (Φ ∧ ¬ pc_c)) by (apply models_and; assumption).
      destruct (concore_soundness_fold_fix Inf (Φ ∧ ¬ pc_c) Γ ef alts ef' Hfold_f eq_refl Γc σ S vsc altsc
                  Hmod_and Henv Hcon_vsc Hcon_altsc HΓc Hcl_vsc Hsc_altsc
                  (or_introl H4) Halts HsymE Hsym_f Hsym_alts) as [v_con [Hfold_c Hcont_er]].
      exists v_con. split; [exact Hfold_c | apply Cont_If_False; assumption].
    + kill_denote.
  - (* FoldAlts_IfFail *)
    exfalso.
    apply (merge_keeps_of_branch σ S ec et ef vsc) in Hkeeps.
    assert (Hfree : sym_free_env S Γ)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
    inversion Hkeeps; subst.
    + destruct (models_cond_total σ S Γ ec Hfree (or_introl H3)) as [pc Hpc_some].
      rewrite Hpc_none in Hpc_some. discriminate.
    + destruct (models_cond_total σ S Γ ec Hfree (or_intror H3)) as [pc Hpc_some].
      rewrite Hpc_none in Hpc_some. discriminate.
    + kill_denote.
  - (* FoldAlts_Con *)
    assert (Hunspool_e : unspool_app e [] = (ECon d, ea)).
    { unfold decompose_con_app in Hdec.
      destruct (unspool_app e []) as [h a0] eqn:Hu.
      destruct h; try discriminate.
      inversion Hdec; subst; reflexivity. }
    assert (Hcont_vs : contains σ S e vsc).
    { destruct Hkeeps as [Hc | [Hsmt | [Hcast _]]]; [exact Hc | | ].
      - exfalso. pose proof (smt_ite_kept_solvable σ S e vsc Hsmt) as Hsolv.
        rewrite (decompose_con_app_none e (solvable_not_con_app · e Hsolv)) in Hdec.
        discriminate Hdec.
      - exfalso. destruct e; simpl in Hcast; discriminate. }
    assert (Hunspool_vcs : exists ea_c, unspool_app vsc [] = (ECon d, ea_c) /\ Forall2 (contains σ S) ea ea_c).
    { apply (contains_unspool_con σ S e vsc Hcont_vs [] [] (Forall2_nil _) d ea Hunspool_e). }
    destruct Hunspool_vcs as [ea_c [Hunspool_vcs Hcont_ea]].
    assert (Hdec_vcs : decompose_con_app vsc = Some (d, ea_c)).
    { unfold decompose_con_app. rewrite Hunspool_vcs. reflexivity. }
    destruct (find_alt_contains_alt σ S alts altsc d xs ep Halts Halt) as [ep_c [Halt_c [Hxs Hcont_ep]]].
    assert (Hconcore_ea_c : Forall concore_expr ea_c).
    { eapply unspool_app_concore; [exact Hunspool_vcs | exact Hcon_vsc | constructor]. }
    assert (Hcon_ep_c : concore_expr ep_c) by (eapply find_alt_concore; [exact Halt_c | exact Hcon_altsc]).
    assert (Hsc_ea_c : Forall closed_term ea_c)
      by exact (proj2 (unspool_app_scoped nil vsc [] (ECon d) ea_c Hunspool_vcs Hcl_vsc (Forall_nil _))).
    assert (Hcl_ext : closed_instance (extend_env_multi Γc xs ea_c Γc) ep_c).
    { left. split.
      - apply scoped_env_extend_multi; [exact HΓc | exact HΓc |].
        eapply Forall_impl; [| exact Hsc_ea_c]. intros a Ha. exact (closed_term_scoped _ a Ha).
      - rewrite dom_env_extend_multi. exact (find_alt_scoped _ d altsc xs ep_c Hsc_altsc Halt_c). }
    assert (Henv_ext : contains_env σ S (extend_env_multi Γ xs ea Γ) (extend_env_multi Γc xs ea_c Γc)).
    { apply contains_env_extend_multi; assumption. }
    assert (Hsym_ea : Forall (sym_scoped S (dom_env Γ)) ea).
    { pose proof (proj2 (sym_unspool_app_scoped S nil e [] (ECon d) ea
                    Hunspool_e Hsym_scrut (Forall_nil _))) as H0.
      eapply Forall_impl; [| exact H0]. intros a Ha. apply sym_scoped_nil_any. exact Ha. }
    assert (HsymE_ext : sym_scoped_env S (extend_env_multi Γ xs ea Γ))
      by (apply sym_scoped_env_extend_multi; [exact HsymE | exact HsymE | exact Hsym_ea]).
    assert (Hsym_ep : sym_scoped S (dom_env (extend_env_multi Γ xs ea Γ)) ep).
    { rewrite dom_env_extend_multi.
      exact (sym_find_alt_scoped S (dom_env Γ) d alts xs ep Hsym_alts Halt). }
    destruct (concore_soundness_fix Inf Φ (extend_env_multi Γ xs ea Γ) ep er Heval_ep eq_refl
                (extend_env_multi Γc xs ea_c Γc) σ S ep_c Hmod Henv_ext Hcont_ep Hcon_ep_c Hcl_ext
                HsymE_ext Hsym_ep)
      as [v_con [Heval_ep_c Hcont_er]].
    exists v_con. split; [| exact Hcont_er].
    eapply FoldAlts_Con; [exact Hdec_vcs | exact Halt_c | exact Heval_ep_c].
  - (* FoldAlts_Bot *)
    assert (Hcont_vs : contains σ S (EBot b) vsc).
    { destruct Hkeeps as [Hc | [Hsmt | [Hcast _]]]; [exact Hc | | discriminate Hcast].
      exfalso. pose proof (smt_ite_kept_solvable σ S (EBot b) vsc Hsmt) as Hsolv.
      inversion Hsolv. }
    inversion Hcont_vs; subst; [| kill_denote].
    exists (EBot b). split; [apply FoldAlts_Bot | apply Cont_Bot].
  - (* FoldAlts_GroundFormula: a formula with no variable has a fixed truth
       value, and the concrete scrutinee reads the same one. *)
    destruct (scrutinee_reads_the_same_value σ S Γ Γc e vsc pc Henv Hkeeps Hsym_scrut Hcl_vsc
                Hpcg (or_intror Hvarg)) as [pcc [Hpcc [Hvarc Hvalc]]].
    rewrite (pc_value_closed σ pc Hvarg) in Hvalc.
    destruct (concore_soundness_fold_fix Inf Φ Γ (ECon (truth_constructor (pc_closed_value pc))) alts r
                Hrec eq_refl Γc σ S (ECon (truth_constructor (pc_closed_value pc))) altsc
                Hmod Henv (Con_Con _) Hcon_altsc HΓc (Scoped_Con nil _) Hsc_altsc
                (or_introl (Cont_Con σ S _)) Halts HsymE (SymScoped_Con S nil _) Hsym_alts)
      as [v_con [Hfold_c Hcont_er]].
    exists v_con. split; [| exact Hcont_er].
    apply (FoldAlts_GroundFormula Inf pc_true Γc vsc pcc altsc v_con Hpcc Hvarc).
    rewrite Hvalc. exact Hfold_c.
  - (* FoldAlts_SymbolicFormula: the formula mentions a variable, so the match
       becomes a runtime branch. The model picks the side whose constructor the
       concrete scrutinee reads. *)
    destruct (scrutinee_reads_the_same_value σ S Γ Γc e vsc pc Henv Hkeeps Hsym_scrut Hcl_vsc
                Hpcs (or_introl Hars)) as [pcc [Hpcc [Hvarc Hvalc]]].
    assert (Hden_e : denotes S e pc)
      by exact (sym_scoped_expr_to_pc_denotes S Γ e pc Hsym_scrut Hpcs).
    destruct (lit_eq_dec (pc_value σ pc) lit_true) as [Htrue | Hfalse].
    + assert (Hmod_pc : σ ⊨ pc) by exact Htrue.
      assert (Hmod_and : σ ⊨ (Φ ∧ pc)) by (apply models_and; assumption).
      destruct (concore_soundness_fold_fix Inf (Φ ∧ pc) Γ (ECon dcon_true) alts r1
                  Hf1 eq_refl Γc σ S (ECon dcon_true) altsc
                  Hmod_and Henv (Con_Con _) Hcon_altsc HΓc (Scoped_Con nil _) Hsc_altsc
                  (or_introl (Cont_Con σ S _)) Halts HsymE (SymScoped_Con S nil _) Hsym_alts)
        as [v_con [Hfold_c Hcont_er]].
      exists v_con. split.
      * apply (FoldAlts_GroundFormula Inf pc_true Γc vsc pcc altsc v_con Hpcc Hvarc).
        rewrite Hvalc. unfold truth_constructor.
        destruct (lit_eq_dec (pc_value σ pc) lit_true) as [_ | Hne]; [exact Hfold_c | congruence].
      * apply Cont_If_True; [exists pc; split; assumption | exact Hcont_er].
    + assert (Hmod_not : σ ⊨ (¬ pc)).
      { unfold models, pc_not. simpl. apply prim_value_not. exact Hfalse. }
      assert (Hmod_and : σ ⊨ (Φ ∧ ¬ pc)) by (apply models_and; assumption).
      destruct (concore_soundness_fold_fix Inf (Φ ∧ ¬ pc) Γ (ECon dcon_false) alts r2
                  Hf2 eq_refl Γc σ S (ECon dcon_false) altsc
                  Hmod_and Henv (Con_Con _) Hcon_altsc HΓc (Scoped_Con nil _) Hsc_altsc
                  (or_introl (Cont_Con σ S _)) Halts HsymE (SymScoped_Con S nil _) Hsym_alts)
        as [v_con [Hfold_c Hcont_er]].
      exists v_con. split.
      * apply (FoldAlts_GroundFormula Inf pc_true Γc vsc pcc altsc v_con Hpcc Hvarc).
        rewrite Hvalc. unfold truth_constructor.
        destruct (lit_eq_dec (pc_value σ pc) lit_true) as [Heq | _]; [congruence | exact Hfold_c].
      * apply Cont_If_False; [exists pc; split; assumption | exact Hcont_er].
  - (* FoldAlts_Otherwise *)
    destruct Hkeeps as [Hcont_vs | [Hsmt | [Hcast_s Hcast_c]]].
    2: { exfalso. pose proof (smt_ite_kept_solvable σ S e vsc Hsmt) as Hsolv.
         destruct (sym_solvable_denotes S e Hsym_scrut Hsolv) as [pc0 [Hden0 _]].
         assert (Hfree : sym_free_env S Γ)
           by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
         rewrite (Hden0 Γ Hfree) in Hpcnone. discriminate Hpcnone. }
    2: { exists (EBot BUndefined). split; [| apply Cont_Bot].
         exact (fold_alts_cast_undefined_intro Inf pc_true Γc vsc altsc Hcast_c). }
    destruct (contains_otherwise_shape σ S Γ Γc e vsc Henv Hcont_vs Hsym_scrut Hcl_vsc
                Hpcnone Hopnone Hnothead) as [Hpc_c Hop_c].
    destruct (unspool_app e []) as [head args] eqn:Hunspool_e.
    assert (Hif_head : is_if head = false).
    { simpl in Hnothead. exact Hnothead. }
    assert (Hfacts :
      (match decompose_con_app vsc with
       | Some (d, _) => find_alt d altsc = None
       | None => True
       end)
      /\ is_bot vsc = false /\ is_if (fst (unspool_app vsc [])) = false).
    { destruct (contains_unspool_general σ S e vsc Hcont_vs [] [] (Forall2_nil _) head args Hunspool_e Hif_head)
        as [[head_c [args_c [Hunspool_vcs [Hcont_head Hcont_args]]]]
           | [lv [args_c Hunspool_vcs]]].
      - split; [| split].
        + unfold decompose_con_app. rewrite Hunspool_vcs.
          destruct head_c eqn:Hheadc; try exact I.
          inversion Hcont_head; subst; try (simpl in Hif_head; discriminate).
          assert (Hdeco_e : decompose_con_app e = Some (d, args)) by (unfold decompose_con_app; rewrite Hunspool_e; reflexivity).
          rewrite Hdeco_e in Hnoalt.
          exact (find_alt_none_contains_alt σ S alts altsc d Halts Hnoalt).
        + destruct (is_bot vsc) eqn:Hbc; [| reflexivity].
          exfalso. destruct vsc; simpl in Hbc; try discriminate.
          inversion Hcont_vs; subst; try discriminate;
            simpl in Hunspool_e; injection Hunspool_e as Hh Ha; subst; discriminate.
        + assert (Hif_head_c : is_if head_c = false).
          { inversion Hcont_head; subst; try reflexivity; try (simpl in Hif_head; discriminate).
            match goal with
            | [ Ht : is_thunk ?e = true |- _ ] => destruct e; try discriminate Ht; reflexivity
            end. }
          rewrite Hunspool_vcs. simpl. exact Hif_head_c.
      - (* the scrutinee concretised to an SMT value, which matches no
           constructor alternative, exactly as the symbolic side did *)
        split; [| split].
        + unfold decompose_con_app. rewrite Hunspool_vcs. exact I.
        + destruct (is_bot vsc) eqn:Hbc; [| reflexivity].
          exfalso. destruct vsc; simpl in Hbc; discriminate.
        + rewrite Hunspool_vcs. reflexivity.
    }
    destruct Hfacts as [Hnoalt_c [Hnotbot_c Hnothead_c]].
    exists (EBot BUndefined). split; [| apply Cont_Bot].
    apply FoldAlts_Otherwise; assumption.
}
Qed.

(**
  The conclusion is existential: SOME concrete value matches the symbolic one.

  The stronger reading,
    forall v_con, Γc ⊢ᶜ e_con ⇓ᶜ v_con -> contains σ S v_sym v_con,
  follows for the terms the theorem is about, because ConCore/Determinism.v proves
  concrete evaluation deterministic on them: e_con is a ConCore expression by
  hypothesis, and Γc is a ConCore environment by contains_env_concrete, so
  e_con has at most one value and the existential one is it.
*)
Theorem concore_soundness : forall Φ Γs Γc σ S e_sym e_con v_sym,
  σ ⊨ Φ ->
  contains_env σ S Γs Γc ->
  contains σ S e_sym e_con ->
  concore_expr e_con ->
  closed_program Γc e_con ->
  symbolic_program S Γs e_sym ->
  Φ ; Γs ⊢ e_sym ⇓ v_sym ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\
    contains σ S v_sym v_con.
Proof.
  intros Φ Γs Γc σ S e_sym e_con v_sym Hmod Henv Hcont Hcon Hcl [HsymE Hsym] Heval.
  exact (concore_soundness_fix Inf Φ Γs e_sym v_sym Heval eq_refl Γc σ S e_con Hmod Henv Hcont Hcon
           (or_introl Hcl) HsymE Hsym).
Qed.

(** On CLOSED SMT terms the relation is plain syntactic equality: Cont_Denote
    never fires where there is no symbolic variable to instantiate. *)
Corollary closed_smt_term_is_rigid : forall σ S es ec,
  smt_ground es = true -> contains σ S es ec -> es = ec.
Proof.
  intros σ S es ec Hg Hcont.
  exact (ground_solvable_contains_eq σ S es ec Hcont
           (fun Γ => smt_ground_solvable es Γ Hg)).
Qed.

End ConCore.
