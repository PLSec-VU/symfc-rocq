From SymCoreTheory Require Export Soundness.Alignment.
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

(** `contains` commutes with `unspool_app`, threading an existing pointwise
    correspondence on the accumulator through the same accumulator on both
    sides. This is the structural core of the App-Prim case of soundness. *)
(**
  The accumulator must be non-empty and the spine saturated. Both premises
  say the same thing: the term being unspooled is a PROPER SUB-SPINE of a
  saturated application, hence under-applied, hence not itself a value of
  SMT sort, hence not something Cont_Denote could have collapsed to a
  literal. Rule App-Prim, the only caller, supplies both.
*)
Lemma contains_unspool_primop : forall σ S e_sym e_con,
  contains σ S e_sym e_con ->
  forall L_s L_c,
    Forall2 (contains σ S) L_s L_c ->
    L_s <> [] ->
    forall p args,
      unspool_app e_sym L_s = (EPrimOp p, args) ->
      length args = primop_arity p ->
      exists args_c,
        unspool_app e_con L_c = (EPrimOp p, args_c) /\
        Forall2 (contains σ S) args args_c.
Proof.
  induction 1; intros L_s L_c HL Hne p0 args0 Hunspool Harity; simpl in Hunspool;
    try discriminate.
  - injection Hunspool as ? ?; subst.
    exists L_c. split; [reflexivity | exact HL].
  - apply IHcontains1 with (L_s := a_s :: L_s) (L_c := a_c :: L_c);
      [constructor; assumption | discriminate | exact Hunspool | exact Harity].
  - exfalso.
    match goal with
    | [ Hun0 : unspool_app ?e (@nil expr) = (EPrimOp ?q, ?qargs),
        Har0 : length ?qargs = primop_arity ?q |- _ ] =>
        apply (unspool_app_shift e [] L_s) in Hun0; simpl in Hun0;
        rewrite Hun0 in Hunspool; inversion Hunspool; subst;
        rewrite length_app, Har0 in Harity;
        destruct L_s as [| z zs]; [apply Hne; reflexivity | simpl in Harity; lia]
    end.
Qed.

(** Same fact, specialized to a data-constructor head instead of a primitive
    operator - needed for FoldAlts_Con's "the pattern matched" case. *)
Lemma contains_unspool_con : forall σ S e_sym e_con,
  contains σ S e_sym e_con ->
  forall L_s L_c,
    Forall2 (contains σ S) L_s L_c ->
    forall d args,
      unspool_app e_sym L_s = (ECon d, args) ->
      exists args_c,
        unspool_app e_con L_c = (ECon d, args_c) /\
        Forall2 (contains σ S) args args_c.
Proof.
  induction 1; intros L_s L_c HL d0 args0 Hunspool; simpl in Hunspool;
    try discriminate.
  - injection Hunspool as ? ?; subst.
    exists L_c. split; [reflexivity | exact HL].
  - apply IHcontains1 with (L_s := a_s :: L_s) (L_c := a_c :: L_c).
    + constructor; assumption.
    + exact Hunspool.
  - exfalso.
    match goal with
    | [ Hun0 : unspool_app ?e (@nil expr) = (EPrimOp ?q, ?qargs) |- _ ] =>
        apply (unspool_app_shift e [] L_s) in Hun0; simpl in Hun0;
        rewrite Hun0 in Hunspool; discriminate Hunspool
    end.
Qed.

(** ------------------------------------------------------------------------- *)
(** What Merging Keeps of an Instance (§3.3)                                  *)
(** ------------------------------------------------------------------------- *)

(**
  Every concrete term the unmerged branch stands for, the merged term stands
  for too, with one exception: the SMT clause. Of its term and the instance
  only this is known: both are scrutinees that no alternative matches. That is the paper's Lemma A.4 in the form that has a model, proved
  from the definition of merge in SymCore/Merge.v.

  The proof is one case per clause of the merge table. The shape is always
  the same: the model picks an arm, the clause's result agrees with that arm
  on the head, and the branch that is left inside the result is resolved by
  the same model the same way.
*)

Lemma spine_head_app : forall f a,
  fst (unspool_app (EApp f a) []) = fst (unspool_app f []).
Proof.
  intros f a. simpl. destruct (unspool_app f []) as [h args] eqn:Hu.
  pose proof (unspool_app_shift f [] [a] h args Hu) as Hshift. simpl in Hshift.
  rewrite Hshift. reflexivity.
Qed.

(** A cast scrutinee is not a formula and not a primitive application, so both
    Rule Case sides fold it to undefined. *)
Lemma is_cast_facts : forall e, is_cast e = true ->
  expr_to_pc · e = None /\ is_op_app e = false /\
  is_if (fst (unspool_app e [])) = false /\ decompose_con_app e = None /\ is_bot e = false.
Proof.
  intros e H. destruct e; simpl in H; try discriminate.
  repeat split; reflexivity.
Qed.

Lemma fold_alts_cast_undefined : forall f Φ Γ e alts r,
  is_cast e = true -> fold_alts f Φ Γ e alts r -> r = EBot BUndefined.
Proof.
  intros f Φ Γ e alts r Hc Hfold.
  destruct (is_cast_facts e Hc) as [_ [Hop [Hh [Hd Hb]]]].
  assert (Hpc : expr_to_pc Γ e = None) by (destruct e; simpl in Hc; try discriminate; reflexivity).
  apply (fold_alts_otherwise_same f Φ Γ e alts r Hpc Hop
           (is_if_false_of_spine_head e Hh)); [rewrite Hd; exact I | exact Hb | exact Hfold].
Qed.

Lemma fold_alts_cast_undefined_intro : forall f Φ Γ e alts,
  is_cast e = true -> fold_alts f Φ Γ e alts (EBot BUndefined).
Proof.
  intros f Φ Γ e alts Hc.
  assert (Hpc : expr_to_pc Γ e = None) by (destruct e; simpl in Hc; try discriminate; reflexivity).
  destruct (is_cast_facts e Hc) as [_ [Hop [Hh [Hd Hb]]]].
  apply FoldAlts_Otherwise; [exact Hpc | exact Hop | exact Hh | rewrite Hd; exact I | exact Hb].
Qed.

Lemma solvable_in_empty_env : forall Γ e, Solvable Γ e -> Solvable · e.
Proof.
  intros Γ e H. destruct (solvable_expr_to_pc Γ e H) as [pc Hpc].
  exact (expr_to_pc_solvable · e pc Hpc).
Qed.

Lemma denotes_solvable : forall S e pc, denotes S e pc -> Solvable · e.
Proof.
  intros S e pc H. exact (expr_to_pc_solvable · e pc (H · (sym_free_env_empty S))).
Qed.

(** A branch is related to a concrete term by resolving it, never by
    denotation: a branch is not a primitive application. *)
Lemma contains_if_inv : forall σ S ec et ef e_c,
  contains σ S (EIf ec et ef) e_c ->
  (models_cond σ S ec /\ contains σ S et e_c) \/
  (models_not_cond σ S ec /\ contains σ S ef e_c).
Proof.
  intros σ S ec et ef e_c H. inversion H; subst.
  - left; split; assumption.
  - right; split; assumption.
  - simpl in *. discriminate.
Qed.

(** Concretion is a congruence for application spines *)
Lemma contains_fold_left_app : forall σ S l1 l2 h1 h2,
  Forall2 (contains σ S) l1 l2 ->
  contains σ S h1 h2 ->
  contains σ S (fold_left EApp l1 h1) (fold_left EApp l2 h2).
Proof.
  intros σ S l1 l2 h1 h2 HF. revert h1 h2.
  induction HF as [| x y l l' Hxy HF IH]; intros h1 h2 Hh; simpl.
  - exact Hh.
  - apply IH. apply Cont_App; assumption.
Qed.

Lemma contains_spine_if : forall σ S e_sym e_con,
  contains σ S e_sym e_con ->
  forall L_s L_c,
    Forall2 (contains σ S) L_s L_c ->
    forall ec et ef args,
      unspool_app e_sym L_s = (EIf ec et ef, args) ->
      exists head_c args_c,
        fold_left EApp L_c e_con = fold_left EApp args_c head_c /\
        contains σ S (EIf ec et ef) head_c /\
        Forall2 (contains σ S) args args_c.
Proof.
  induction 1; intros L_s L_c HL ec0 et0 ef0 args0 Hunspool; simpl in Hunspool;
    try discriminate Hunspool.
  - exact (IHcontains1 (a_s :: L_s) (a_c :: L_c) (Forall2_cons _ _ H0 HL) _ _ _ _ Hunspool).
  - injection Hunspool as Hc Ht Hf Hargs. subst.
    exists etc, L_c. split; [reflexivity | split; [apply Cont_If_True; assumption | exact HL]].
  - injection Hunspool as Hc Ht Hf Hargs. subst.
    exists efc, L_c. split; [reflexivity | split; [apply Cont_If_False; assumption | exact HL]].
  - exfalso.
    match goal with
    | [ Hun0 : unspool_app ?e (@nil expr) = (EPrimOp ?q, ?qargs) |- _ ] =>
        apply (unspool_app_shift e [] L_s) in Hun0; simpl in Hun0;
        rewrite Hun0 in Hunspool; discriminate Hunspool
    end.
Qed.

Lemma contains_app_if_spine : forall σ S e1 e2 ec et ef args e_con,
  contains σ S (EApp e1 e2) e_con ->
  unspool_app (EApp e1 e2) [] = (EIf ec et ef, args) ->
  contains σ S (EIf ec (fold_left EApp args et) (fold_left EApp args ef)) e_con.
Proof.
  intros σ S e1 e2 ec et ef args e_con Hcont Hunspool.
  destruct (contains_spine_if σ S _ _ Hcont [] [] (Forall2_nil _) ec et ef args Hunspool)
    as [head_c [args_c [Heq [Hhead Hargs]]]].
  simpl in Heq. rewrite Heq.
  destruct (contains_if_inv σ S ec et ef head_c Hhead) as [[Hc Ht] | [Hc Hf]].
  - apply Cont_If_True; [exact Hc | apply contains_fold_left_app; assumption].
  - apply Cont_If_False; [exact Hc | apply contains_fold_left_app; assumption].
Qed.

(** Pushing one condition into matching argument lists keeps every argument
    related to the concrete argument the model chose *)
Lemma zip_if_contains_true : forall σ S ec a1 a2 args_c,
  models_cond σ S ec ->
  length a1 = length a2 ->
  Forall2 (contains σ S) a1 args_c ->
  Forall2 (contains σ S) (zip_if ec a1 a2) args_c.
Proof.
  intros σ S ec a1 a2 args_c Hmc Hlen HF. revert a2 Hlen.
  induction HF as [| x y l l' Hxy HF IH]; intros a2 Hlen.
  - destruct a2; simpl; constructor.
  - destruct a2 as [| z zs]; [discriminate |]. simpl.
    constructor; [apply Cont_If_True; assumption | apply IH; simpl in Hlen; auto].
Qed.

Lemma zip_if_contains_false : forall σ S ec a1 a2 args_c,
  models_not_cond σ S ec ->
  length a1 = length a2 ->
  Forall2 (contains σ S) a2 args_c ->
  Forall2 (contains σ S) (zip_if ec a1 a2) args_c.
Proof.
  intros σ S ec a1 a2 args_c Hmc Hlen HF. revert a1 Hlen.
  induction HF as [| x y l l' Hxy HF IH]; intros a1 Hlen.
  - destruct a1; simpl; constructor.
  - destruct a1 as [| z zs]; [discriminate |]. simpl.
    constructor; [apply Cont_If_False; assumption | apply IH; simpl in Hlen; auto].
Qed.

(** Closes the Cont_Denote case of an inversion on a term whose spine head is
    visibly not a primitive operation *)
Ltac kill_den :=
  match goal with
  | [ H : unspool_app _ _ = (EPrimOp _, _) |- _ ] => simpl in H; discriminate H
  end.

Lemma ite_leaf_clos_contains : forall σ S Γ ec Γ1 e1 Γ2 e2 e_c,
  contains σ S (EIf ec (EThunk Γ1 e1) (EThunk Γ2 e2)) e_c ->
  contains σ S (ite_leaf Γ ec (EThunk Γ1 e1) (EThunk Γ2 e2)) e_c.
Proof.
  intros σ S Γ ec Γ1 e1 Γ2 e2 e_c Hc.
  unfold ite_leaf. simpl.
  destruct e1 as [| | | | | x1 b1 | | | | | | | ]; try exact Hc.
  destruct e2 as [| | | | | x2 b2 | | | | | | | ]; try exact Hc.
  destruct (env_eqb Γ1 Γ2 && String.eqb x1 x2)%bool eqn:Hx; [| exact Hc].
  apply andb_prop in Hx as [Hxe Hxx].
  apply env_eqb_eq in Hxe. apply String.eqb_eq in Hxx. subst Γ2 x2.
  destruct (contains_if_inv σ S ec _ _ e_c Hc) as [[Hmc Hct] | [Hmc Hcf]].
  - destruct (contains_clos_inv σ S Γ1 x1 b1 e_c Hct) as [Γc [bc [Heq [Hsx [Henv Hb]]]]].
    subst e_c. apply Cont_Thunk; [exact Henv |].
    apply Cont_Lam; [exact Hsx | apply Cont_If_True; assumption].
  - destruct (contains_clos_inv σ S Γ1 x1 b2 e_c Hcf) as [Γc [bc [Heq [Hsx [Henv Hb]]]]].
    subst e_c. apply Cont_Thunk; [exact Henv |].
    apply Cont_Lam; [exact Hsx | apply Cont_If_False; assumption].
Qed.

(** The four clauses that merge two identical or matching value forms, the
    lambda closures last *)

Ltac merge_leaf_rest et ef Hc Hcases :=
  destruct et; destruct ef; simpl; try exact Hc;
  try exact (ite_leaf_clos_contains _ _ · _ _ _ _ _ _ Hc);
  try (match goal with |- contains _ _ (match ?b with _ => _ end) _ => destruct b; exact Hc end);
  [ destruct (dec_eqb coercion_eq_dec _ _) eqn:Hx; [| exact Hc];
    apply dec_eqb_eq in Hx; subst;
    destruct Hcases as [[Hmc Hct]|[Hmc Hcf]];
    [ inversion Hct; subst; [| kill_den] | inversion Hcf; subst; [| kill_den] ];
    apply Cont_Coercion
  | destruct (dec_eqb type_fc_eq_dec _ _) eqn:Hx; [| exact Hc];
    apply dec_eqb_eq in Hx; subst;
    destruct Hcases as [[Hmc Hct]|[Hmc Hcf]];
    [ inversion Hct; subst; [| kill_den] | inversion Hcf; subst; [| kill_den] ];
    apply Cont_Type
  | destruct (bottom_eqb _ _) eqn:Hx; [| exact Hc];
    apply bottom_eqb_eq in Hx; subst;
    destruct Hcases as [[Hmc Hct]|[Hmc Hcf]];
    [ inversion Hct; subst; [| kill_den] | inversion Hcf; subst; [| kill_den] ];
    apply Cont_Bot ].

Fixpoint esize (e : expr) : nat :=
  match e with
  | EApp f a => 1 + esize f + esize a
  | _ => 1
  end.

(** A symbolic term with only symbolic variables reads the same formula in
    every environment that binds no symbolic variable. *)
Lemma sym_scoped_nil_expr_to_pc : forall S Γ e pc,
  sym_scoped S nil e -> sym_free_env S Γ ->
  expr_to_pc · e = Some pc -> expr_to_pc Γ e = Some pc.
Proof.
  intros S Γ e. induction e; intros pc Hsc Hfree Hpc; simpl in Hpc; try discriminate.
  - inversion Hsc as [L0 x0 Hx | | | | | | | | | | | |]; subst.
    destruct Hx as [[] | Hx]. simpl. rewrite (Hfree v Hx). exact Hpc.
  - exact Hpc.
  - exact Hpc.
  - inversion Hsc as [| | | | L0 f a Hscf Hsca | | | | | | | |]; subst.
    simpl in Hpc |- *.
    destruct (expr_to_pc · e1) as [pc1|] eqn:E1; [| discriminate].
    destruct pc1 as [x|l|q qs]; try (destruct (expr_to_pc · e2); discriminate).
    destruct (expr_to_pc · e2) as [pc2|] eqn:E2; [| discriminate].
    rewrite (IHe1 (PCPrim q qs) Hscf Hfree eq_refl), (IHe2 pc2 Hsca Hfree eq_refl). exact Hpc.
Qed.

Lemma sym_solvable_denotes : forall S e,
  sym_scoped S nil e -> Solvable · e -> exists pc, denotes S e pc /\ expr_to_pc · e = Some pc.
Proof.
  intros S e Hsc Hsolv.
  destruct (solvable_expr_to_pc · e Hsolv) as [pc Hpc].
  exists pc. split; [| exact Hpc].
  intros Γ Hfree. exact (sym_scoped_nil_expr_to_pc S Γ e pc Hsc Hfree Hpc).
Qed.

Lemma denotes_op_fold : forall S args pcs h qhead qacc,
  Forall2 (denotes S) args pcs ->
  denotes S h (PCPrim qhead qacc) ->
  denotes S (fold_left EApp args h) (PCPrim qhead (qacc ++ pcs)).
Proof.
  intros S args pcs h qhead qacc H. revert h qacc.
  induction H as [| a pa args pcs Ha Hargs IH]; intros h qacc Hh.
  - rewrite app_nil_r. exact Hh.
  - simpl. replace (qacc ++ pa :: pcs) with ((qacc ++ pa :: nil) ++ pcs)
      by (rewrite <- app_assoc; reflexivity).
    apply IH. intros Γ Hfree. simpl. rewrite (Hh Γ Hfree), (Ha Γ Hfree). reflexivity.
Qed.

Lemma unspool_esize : forall e acc head args arg,
  unspool_app e acc = (head, args) -> In arg args ->
  In arg acc \/ esize arg < esize e.
Proof.
  induction e; intros acc head args arg Hu Hin; simpl in Hu;
    try (injection Hu as <- <-; left; exact Hin).
  destruct (IHe1 (e2 :: acc) head args arg Hu Hin) as [Hin2 | Hlt].
  - destruct Hin2 as [-> | Hin2]; [right; simpl; lia | left; exact Hin2].
  - right; simpl; lia.
Qed.

(**
  The key lemma. A well-formed boolean formula (correct arities) and its
  concrete instance read the same SMT value under the model. This is what
  lines up Rule Case's two sides: the symbolic scrutinee folds by its value,
  and the concrete scrutinee, a variable-free formula, folds by the same value.
*)
Lemma wellformed_contains_denote : forall n σ S es ec pc,
  esize es <= n ->
  contains σ S es ec -> denotes S es pc -> pc_arities_ok pc = true ->
  denote σ S ec (pc_value σ pc).
Proof.
  induction n as [| n IH]; intros σ S es ec pc Hn Hc Hden Har.
  - destruct es; simpl in Hn; lia.
  - pose proof (Hden · (sym_free_env_empty S)) as Hpc0.
    destruct es as [ x | l | p | d | f a | | | | | | | | ];
      simpl in Hpc0; try discriminate Hpc0.
    + (* EVar x *)
      injection Hpc0 as <-.
      inversion Hc; subst.
      * (* Cont_Var_Bound: S x = false contradicts denotes *)
        exfalso.
        match goal with [ Hxf : S x = false |- _ ] =>
          assert (Hfree : sym_free_env S (ExtendEnv x (MkClosure · (EBot BUndefined)) ·))
            by (intros y Hy; simpl; destruct (string_dec y x) as [->|];
                [rewrite Hxf in Hy; discriminate | reflexivity]);
          pose proof (Hden _ Hfree) as Hcap; simpl in Hcap;
          destruct (string_dec x x); [discriminate Hcap | congruence] end.
      * (* Cont_Var_Sym: ec = ELit (σ x) *)
        simpl. apply denote_lit.
      * (* Cont_Denote: impossible for a variable *) kill_denote.
    + (* ELit l *)
      injection Hpc0 as <-. apply contains_lit_inv in Hc. subst ec. apply denote_lit.
    + (* EPrimOp p *)
      injection Hpc0 as <-. apply contains_primop_inv in Hc. subst ec.
      simpl. exists (PCPrim p nil). split; [intros Γ _; reflexivity | reflexivity].
    + (* EApp f a *)
      assert (Hsolv : Solvable · (EApp f a)) by (eapply denotes_solvable; exact Hden).
      assert (Hop : is_op_app (EApp f a) = true)
        by (inversion Hsolv as [ | | | f0 a0 Hop Hf Ha]; exact Hop).
      destruct (is_op_app_unspool (EApp f a) Hop) as [q [args Hunspool_es]].
      destruct (expr_to_pc_op_app (EApp f a) · pc Hop Hpc0) as [q0 [pcs Hpceq]]. subst pc.
      destruct (denotes_unspool (EApp f a) S q0 pcs q args Hden Hunspool_es) as [Hq Hargs_den].
      subst q0.
      simpl in Har. apply andb_prop in Har as [Hlen_ar Har_args].
      apply Nat.eqb_eq in Hlen_ar.
      assert (Hlen : length args = primop_arity q)
        by (rewrite (Forall2_length Hargs_den); exact Hlen_ar).
      inversion Hc as [ | | | | | | | | fs as_ f_c a_c Hcf Hca | | | | | | | | es0 p0 args0 lv0 Hun0 Har0 Hg0 Hd0 ];
        subst.
      * (* Cont_App: read the whole saturated spine of ec *)
        destruct (contains_unspool_primop σ S f f_c Hcf (a :: nil) (a_c :: nil)
                    (Forall2_cons a a_c Hca (Forall2_nil _)) ltac:(discriminate) q args
                    Hunspool_es Hlen) as [args_c [Hunspool_ec Hargs_c]].
        assert (Hsizes : Forall (fun arg => esize arg < esize (EApp f a)) args).
        { apply Forall_forall. intros arg Hin.
          destruct (unspool_esize (EApp f a) [] (EPrimOp q) args arg Hunspool_es Hin)
            as [[] | Hlt]. exact Hlt. }
        assert (Hpairs : Forall2 (fun ac pcarg => denote σ S ac (pc_value σ pcarg)) args_c pcs).
        { clear Hunspool_ec Hc Hcf Hca Hunspool_es Hlen_ar Hlen Hden Hpc0.
          revert pcs Hargs_den Har_args Hsizes.
          induction Hargs_c as [| arg ac0 args1 argsc1 Hca0 Hcrest IHc];
            intros pcs Hargs_den Har_args Hsizes.
          - inversion Hargs_den; subst. constructor.
          - inversion Hargs_den as [| a1 pc1 args2 pcs1 Hda Hdrest]; subst.
            inversion Hsizes as [| a2 tl2 Hsz Hsztl]; subst.
            simpl in Har_args. apply andb_prop in Har_args as [Har1 Harrest].
            constructor.
            + apply (IH σ S arg ac0 pc1); [lia | exact Hca0 | exact Hda | exact Har1].
            + apply IHc; assumption. }
        assert (Hec_eq : EApp f_c a_c = fold_left EApp args_c (EPrimOp q))
          by (symmetry; apply (unspool_fold_left (EApp f_c a_c) [] (EPrimOp q) args_c Hunspool_ec)).
        assert (Hexpcs : exists pcs', Forall2 (denotes S) args_c pcs'
                         /\ map (pc_value σ) pcs' = map (pc_value σ) pcs).
        { clear -Hpairs. induction Hpairs as [| ac pcarg args_c0 pcs0 [pc' [Hd' Hv']] _ [pcs'' [Hds Hvs]]].
          - exists nil. split; [constructor | reflexivity].
          - exists (pc' :: pcs''). split; [constructor; assumption |].
            simpl. rewrite Hv', Hvs. reflexivity. }
        destruct Hexpcs as [pcs' [Hds Hvs]].
        exists (PCPrim q pcs'). split.
        -- rewrite Hec_eq.
           apply (denotes_op_fold S args_c pcs' (EPrimOp q) q nil Hds).
           intros Γ _; reflexivity.
        -- simpl. change (prim_value q (map (pc_value σ) pcs') = prim_value q (map (pc_value σ) pcs)).
           rewrite Hvs. reflexivity.
      * (* Cont_Denote: ec = ELit lv0 *)
        assert (Hden_es : denote σ S (EApp f a) (pc_value σ (PCPrim q pcs)))
          by (exists (PCPrim q pcs); split; [exact Hden | reflexivity]).
        pose proof (denote_functional σ S (EApp f a) lv0 (pc_value σ (PCPrim q pcs)) Hd0 Hden_es) as He.
        rewrite He. apply denote_lit.
Qed.

Lemma ground_solvable_contains_eq : forall σ S es ec,
  contains σ S es ec ->
  (forall Γ, Solvable Γ es) ->
  es = ec.
Proof.
  induction 1; intros Hall;
    try reflexivity;
    try (exfalso;
         specialize (Hall ·); inversion Hall; fail).
  - (* Cont_Var_Sym *)
    exfalso.
    specialize (Hall (ExtendEnv x (MkClosure · (EBot BUndefined)) ·)).
    inversion Hall as [| x0 Hnone | |]; subst.
    simpl in Hnone. destruct (string_dec x x); [discriminate | congruence].
  - (* Cont_App *)
    assert (Hf : forall Γ, Solvable Γ f_s)
      by (intros Γ; specialize (Hall Γ); inversion Hall; assumption).
    assert (Ha : forall Γ, Solvable Γ a_s)
      by (intros Γ; specialize (Hall Γ); inversion Hall; assumption).
    rewrite (IHcontains1 Hf), (IHcontains2 Ha). reflexivity.
  - (* Cont_Denote: excluded, the semantic rule never fires on a closed term *)
    exfalso.
    match goal with
    | [ Hg : smt_ground ?t = false |- _ ] =>
        rewrite (solvable_everywhere_smt_ground t Hall) in Hg; discriminate Hg
    end.
Qed.

(** A term whose spine head is not a primitive keeps that shape in every
    instance: the semantic rule only fires on a saturated primitive spine. *)
Lemma contains_is_op_app_false : forall σ S es ec,
  contains σ S es ec ->
  is_op_app es = false ->
  is_if (fst (unspool_app es [])) = false ->
  is_op_app ec = false.
Proof.
  induction 1; intros Hop Hhead; simpl in *; try reflexivity; try discriminate.
  - apply IHcontains1; [exact Hop |]. rewrite <- (spine_head_app f_s a_s). exact Hhead.
  - match goal with
    | [ Ht : is_thunk ?t = true |- _ ] => destruct t; try discriminate Ht; reflexivity
    end.
Qed.

(** A formula with no variable comes from a term with no variable. *)
Lemma no_var_formula_smt_ground : forall Γ e pc,
  expr_to_pc Γ e = Some pc -> pc_has_var pc = false -> smt_ground e = true.
Proof.
  intros Γ e. induction e; intros pc Hpc Hvar; simpl in Hpc; try discriminate.
  - destruct (lookup_env Γ v); [discriminate |].
    injection Hpc as <-. discriminate Hvar.
  - reflexivity.
  - reflexivity.
  - destruct (expr_to_pc Γ e1) as [pc1 |] eqn:E1; [| discriminate].
    destruct pc1 as [x | l | q qs]; try (destruct (expr_to_pc Γ e2); discriminate).
    destruct (expr_to_pc Γ e2) as [pc2 |] eqn:E2; [| discriminate].
    injection Hpc as <-. simpl in Hvar. rewrite existsb_app in Hvar. simpl in Hvar.
    apply Bool.orb_false_elim in Hvar as [Hqs Hrest].
    apply Bool.orb_false_elim in Hrest as [Hpc2 _].
    simpl. rewrite (expr_to_pc_prim_is_op_app Γ e1 q qs E1).
    rewrite (IHe1 (PCPrim q qs) eq_refl Hqs), (IHe2 pc2 eq_refl Hpc2). reflexivity.
Qed.

(**
  What Rule Case reads off the concrete scrutinee. When the symbolic scrutinee
  is a formula that one of the two boolean clauses of fold-alts acts on, the
  concrete scrutinee is a formula with no variable, and both read the same
  value under the model. This is what makes the two sides pick the same
  alternative.
*)
(** A term Rule Case may fold by its value, and its instance, read the same
    value. Either the formula is well formed and the key lemma applies, or it
    mentions no variable and the instance is the term itself. *)
Lemma solvable_term_reads_its_value : forall σ S e ec pc,
  contains σ S e ec ->
  denotes S e pc ->
  (pc_arities_ok pc = true \/ pc_has_var pc = false) ->
  denote σ S ec (pc_value σ pc).
Proof.
  intros σ S e ec pc Hcont Hden [Har | Hvar].
  - exact (wellformed_contains_denote (esize e) σ S e ec pc (Nat.le_refl _) Hcont Hden Har).
  - assert (Hground : smt_ground e = true)
      by exact (no_var_formula_smt_ground · e pc (Hden · (sym_free_env_empty S)) Hvar).
    rewrite <- (ground_solvable_contains_eq σ S e ec Hcont
                  (fun Γ => smt_ground_solvable e Γ Hground)).
    exists pc. split; [exact Hden | reflexivity].
Qed.

(**
  What merge keeps of an instance. Merging a branch either keeps the concrete
  instance directly (contains), or turns two solvable arms into an SMT
  if-then-else formula that reads the same value as the concrete instance
  (smt_ite_kept), or wraps the merged branch in a cast, which both sides fold
  to undefined (merge_ite_cast).
*)
Definition smt_ite_kept (σ : valuation) (S : symvars) (m e_c : expr) : Prop :=
  exists ec et ef,
    m = reduce_prim op_ite (ec :: et :: ef :: nil) /\
    Solvable · ec /\ Solvable · et /\ Solvable · ef /\
    (forall pc, denotes S m pc ->
       (pc_arities_ok pc = true \/ pc_has_var pc = false) ->
       denote σ S e_c (pc_value σ pc)).

Definition merge_keeps (σ : valuation) (S : symvars) (m e_c : expr) : Prop :=
  contains σ S m e_c \/ smt_ite_kept σ S m e_c \/ (is_cast m = true /\ is_cast e_c = true).

Lemma smt_ite_prove : forall σ S Γ ec et ef e_c,
  sym_scoped S nil ec -> sym_scoped S nil et -> sym_scoped S nil ef ->
  Solvable Γ et -> Solvable Γ ef ->
  contains σ S (EIf ec et ef) e_c ->
  smt_ite_kept σ S (reduce_prim op_ite (ec :: et :: ef :: nil)) e_c.
Proof.
  intros σ S Γ ec et ef e_c Hscc Hsct Hscf Ht Hf Hc.
  assert (Hec : Solvable · ec).
  { destruct (contains_if_inv σ S ec et ef e_c Hc) as [[[pc [Hd _]] _] | [[pc [Hd _]] _]];
      exact (denotes_solvable S ec pc Hd). }
  exists ec, et, ef.
  split; [reflexivity |].
  split; [exact Hec |].
  split; [exact (solvable_in_empty_env Γ et Ht) |].
  split; [exact (solvable_in_empty_env Γ ef Hf) |].
  intros pc Hden Hok.
  pose proof (solvable_in_empty_env Γ et Ht) as Het.
  pose proof (solvable_in_empty_env Γ ef Hf) as Hef.
  destruct (sym_solvable_denotes S ec Hscc Hec) as [pcc [Hdenc _]].
  destruct (sym_solvable_denotes S et Hsct Het) as [pct [Hdent _]].
  destruct (sym_solvable_denotes S ef Hscf Hef) as [pcf [Hdenf _]].
  assert (Hmerged : denote σ S (reduce_prim op_ite (ec :: et :: ef :: nil))
                      (prim_value op_ite
                         (pc_value σ pcc :: pc_value σ pct :: pc_value σ pcf :: nil))).
  { apply reduce_prim_denote.
    constructor; [exists pcc; split; [exact Hdenc | reflexivity] |].
    constructor; [exists pct; split; [exact Hdent | reflexivity] |].
    constructor; [exists pcf; split; [exact Hdenf | reflexivity] | constructor]. }
  assert (Hval : pc_value σ pc
                 = prim_value op_ite
                     (pc_value σ pcc :: pc_value σ pct :: pc_value σ pcf :: nil)).
  { apply (denote_functional σ S (reduce_prim op_ite (ec :: et :: ef :: nil)));
      [exists pc; split; [exact Hden | reflexivity] | exact Hmerged]. }
  rewrite Hval, prim_value_ite.
  destruct (contains_if_inv σ S ec et ef e_c Hc) as [[Hcond Hct] | [Hncond Hcf]].
  - assert (Hcv : pc_value σ pcc = lit_true)
      by exact (proj1 (models_cond_denotes σ S ec pcc Hdenc) Hcond).
    destruct (lit_eq_dec (pc_value σ pcc) lit_true) as [_ | Hne]; [| congruence].
    apply (solvable_term_reads_its_value σ S et e_c pct Hct Hdent).
    apply (reduce_prim_ite_wellformed σ S ec et ef pcc pc pct Hec Het Hef Hdenc Hden Hok).
    destruct (lit_eq_dec (pc_value σ pcc) lit_true) as [_ | Hne]; [exact Hdent | congruence].
  - assert (Hcv : pc_value σ pcc <> lit_true).
    { apply prim_value_not.
      exact (proj1 (models_not_cond_denotes σ S ec pcc Hdenc) Hncond). }
    destruct (lit_eq_dec (pc_value σ pcc) lit_true) as [Heq | _]; [congruence |].
    apply (solvable_term_reads_its_value σ S ef e_c pcf Hcf Hdenf).
    apply (reduce_prim_ite_wellformed σ S ec et ef pcc pc pcf Hec Het Hef Hdenc Hden Hok).
    destruct (lit_eq_dec (pc_value σ pcc) lit_true) as [Heq | _]; [congruence | exact Hdenf].
Qed.

Lemma ite_leaf_contains : forall σ S Γ ec et ef e_c,
  sym_scoped S nil ec -> sym_scoped S nil et -> sym_scoped S nil ef ->
  contains σ S (EIf ec et ef) e_c -> merge_keeps σ S (ite_leaf Γ ec et ef) e_c.
Proof.
  intros σ S Γ ec et ef e_c Hscc Hsct Hscf Hc.
  assert (Hcases := contains_if_inv σ S ec et ef e_c Hc).
  unfold merge_keeps, ite_leaf.
  destruct (decompose_con_app et) as [[d1 a1]|] eqn:E1;
  destruct (decompose_con_app ef) as [[d2 a2]|] eqn:E2.
  - left.
    destruct (andb (String.eqb d1 d2) (Nat.eqb (length a1) (length a2))) eqn:Hg;
      [| exact Hc].
    apply andb_prop in Hg as [Hd Hl].
    apply String.eqb_eq in Hd. apply Nat.eqb_eq in Hl. subst d2.
    assert (Hu1 := decompose_con_app_unspool et d1 a1 E1).
    assert (Hu2 := decompose_con_app_unspool ef d1 a2 E2).
    destruct Hcases as [[Hmc Hct] | [Hmc Hcf]].
    + destruct (contains_unspool_con σ S et e_c Hct [] [] (Forall2_nil _) d1 a1 Hu1)
        as [args_c [Huc HFa]].
      rewrite <- (unspool_make_con_app e_c d1 args_c Huc).
      unfold make_con_app. apply contains_fold_left_app; [| apply Cont_Con].
      apply zip_if_contains_true; assumption.
    + destruct (contains_unspool_con σ S ef e_c Hcf [] [] (Forall2_nil _) d1 a2 Hu2)
        as [args_c [Huc HFa]].
      rewrite <- (unspool_make_con_app e_c d1 args_c Huc).
      unfold make_con_app. apply contains_fold_left_app; [| apply Cont_Con].
      apply zip_if_contains_false; assumption.
  - destruct (solvable_dec Γ et) as [Ht |]; [destruct (solvable_dec Γ ef) as [Hf |] |].
    + right. left. exact (smt_ite_prove σ S Γ ec et ef e_c Hscc Hsct Hscf Ht Hf Hc).
    + left. exact Hc.
    + left. merge_leaf_rest et ef Hc Hcases.
  - destruct (solvable_dec Γ et) as [Ht |]; [destruct (solvable_dec Γ ef) as [Hf |] |].
    + right. left. exact (smt_ite_prove σ S Γ ec et ef e_c Hscc Hsct Hscf Ht Hf Hc).
    + left. exact Hc.
    + left. merge_leaf_rest et ef Hc Hcases.
  - destruct (solvable_dec Γ et) as [Ht |]; [destruct (solvable_dec Γ ef) as [Hf |] |].
    + right. left. exact (smt_ite_prove σ S Γ ec et ef e_c Hscc Hsct Hscf Ht Hf Hc).
    + left. exact Hc.
    + left. merge_leaf_rest et ef Hc Hcases.
Qed.

Lemma ite_contains : forall σ S Γ et ec ef e_c,
  sym_scoped S nil ec -> sym_scoped S nil et -> sym_scoped S nil ef ->
  contains σ S (EIf ec et ef) e_c -> merge_keeps σ S (ite Γ ec et ef) e_c.
Proof.
  intros σ S Γ et. induction et; intros ec ef e_c Hscc Hsct Hscf Hc;
    try (rewrite ite_leaf_of by (left; reflexivity);
         apply ite_leaf_contains; assumption).
  destruct ef; try (rewrite ite_leaf_of by (right; reflexivity);
                    apply ite_leaf_contains; assumption).
  rewrite ite_cast. unfold merge_keeps.
  destruct (dec_eqb coercion_eq_dec c c0) eqn:Hx; [| left; exact Hc].
  apply dec_eqb_eq in Hx. subst c0.
  right. right. split; [reflexivity |].
  destruct (contains_if_inv σ S ec (ECast et c) (ECast ef c) e_c Hc) as [[_ Hcast]|[_ Hcast]];
    destruct (contains_cast_inv σ S _ c e_c Hcast) as [ec' [-> _]]; reflexivity.
Qed.

Lemma merge_contains : forall σ S Γ es ec,
  sym_scoped S nil es ->
  contains σ S es ec ->
  merge_keeps σ S (merge Γ es) ec.
Proof.
  intros σ S Γ es ec Hsc H. destruct es; simpl; try (left; exact H).
  inversion Hsc as [| | | | | | | | | | L1 ec1 et1 ef1 Hscc Hsct Hscf | |]; subst.
  apply ite_contains; assumption.
Qed.

(** A symbolic term whose free variables are all symbolic reads the same
    formula in the evaluation environment as in the empty one. *)
Lemma sym_scoped_expr_to_pc_denotes : forall S Γ e pc,
  sym_scoped S nil e -> expr_to_pc Γ e = Some pc -> denotes S e pc.
Proof.
  intros S Γ e pc Hsc Hpc.
  destruct (sym_solvable_denotes S e Hsc
              (solvable_in_empty_env Γ e (expr_to_pc_solvable Γ e pc Hpc)))
    as [pc0 [Hden0 Hpc0]].
  rewrite (expr_to_pc_functional e · Γ pc0 pc Hpc0 Hpc) in Hden0. exact Hden0.
Qed.

(** The merged SMT if-then-else is a solvable term, so no other clause of
    fold-alts can act on it. *)
Lemma smt_ite_kept_solvable : forall σ S m e_c,
  smt_ite_kept σ S m e_c -> Solvable · m.
Proof.
  intros σ S m e_c [ec [et [ef [-> [Hec [Het [Hef _]]]]]]].
  apply reduce_prim_solvable.
  constructor; [exact Hec | constructor; [exact Het | constructor; [exact Hef | constructor]]].
Qed.

(** Merging leaves a branch alone only in the instance sense. *)
Lemma merge_keeps_of_branch : forall σ S ec et ef e_c,
  merge_keeps σ S (EIf ec et ef) e_c -> contains σ S (EIf ec et ef) e_c.
Proof.
  intros σ S ec et ef e_c [Hc | [Hsmt | [Hcast _]]]; [exact Hc | | discriminate Hcast].
  exfalso. pose proof (smt_ite_kept_solvable σ S _ e_c Hsmt) as Hsolv. inversion Hsolv.
Qed.

Ltac kill_otherwise_case Hpc Hop Hhead Hfree :=
  first
    [ simpl in Hpc; discriminate Hpc
    | match goal with
      | [ Hy : _ ?y = true |- _ ] =>
          simpl in Hpc; rewrite (Hfree y Hy) in Hpc; discriminate Hpc
      end
    | match goal with
      | [ Hun : unspool_app ?t (@nil expr) = (EPrimOp ?q, _) |- _ ] =>
          rewrite (unspool_is_op_app t [] q _ Hun) in Hop; discriminate Hop
      end
    | simpl in Hhead; discriminate Hhead
    | match goal with [ Ht : is_thunk _ = true |- _ ] => discriminate Ht end ].

(** A scrutinee that Rule FoldAlts_Otherwise answers stays outside every other
    clause's domain on the concrete side too. *)
Lemma contains_otherwise_shape : forall σ S Γs Γc es ec,
  contains_env σ S Γs Γc ->
  contains σ S es ec ->
  sym_scoped S nil es ->
  closed_term ec ->
  expr_to_pc Γs es = None ->
  is_op_app es = false ->
  is_if (fst (unspool_app es [])) = false ->
  expr_to_pc Γc ec = None /\ is_op_app ec = false.
Proof.
  intros σ S Γs Γc es ec Henv Hcont Hsc Hcl Hpc Hop Hhead.
  assert (Hop_c : is_op_app ec = false)
    by exact (contains_is_op_app_false σ S es ec Hcont Hop Hhead).
  assert (Hfree_s : sym_free_env S Γs)
    by (destruct (contains_env_sym_free σ S Γs Γc Henv) as [Hf _]; exact Hf).
  split; [| exact Hop_c].
  destruct ec as [ x | l | p | d | f a | | | | | | | | ]; try reflexivity.
  - exfalso. inversion Hcl; subst.
    match goal with [ Hin : In _ (@nil var) |- _ ] => exact Hin end.
  - exfalso; inversion Hcont; subst; kill_otherwise_case Hpc Hop Hhead Hfree_s.
  - exfalso; inversion Hcont; subst; kill_otherwise_case Hpc Hop Hhead Hfree_s.
  - simpl. destruct (expr_to_pc Γc f) as [pcf |] eqn:Ef; [| reflexivity].
    destruct pcf as [ y | l | q qs ]; try (destruct (expr_to_pc Γc a); reflexivity).
    exfalso. simpl in Hop_c.
    rewrite (expr_to_pc_prim_is_op_app Γc f q qs Ef) in Hop_c. discriminate Hop_c.
Qed.

Lemma scrutinee_reads_the_same_value : forall σ S Γs Γc escrut vsc pc,
  contains_env σ S Γs Γc ->
  merge_keeps σ S escrut vsc ->
  sym_scoped S nil escrut ->
  closed_term vsc ->
  expr_to_pc Γs escrut = Some pc ->
  (pc_arities_ok pc = true \/ pc_has_var pc = false) ->
  exists pcc,
    expr_to_pc Γc vsc = Some pcc /\ pc_has_var pcc = false /\
    pc_closed_value pcc = pc_value σ pc.
Proof.
  intros σ S Γs Γc escrut vsc pc Henv Hkeeps Hsc Hcl Hpc Hok.
  assert (Hfree_c : sym_free_env S Γc)
    by (destruct (contains_env_sym_free σ S Γs Γc Henv) as [_ Hf]; exact Hf).
  assert (Hden_s : denotes S escrut pc).
  { destruct (sym_solvable_denotes S escrut Hsc
                (solvable_in_empty_env Γs escrut (expr_to_pc_solvable Γs escrut pc Hpc)))
      as [pc0 [Hden0 Hpc0]].
    rewrite (expr_to_pc_functional escrut · Γs pc0 pc Hpc0 Hpc) in Hden0. exact Hden0. }
  assert (Hden_c : denote σ S vsc (pc_value σ pc)).
  { destruct Hkeeps as [Hcont | [Hsmt | [Hcast _]]].
    - exact (solvable_term_reads_its_value σ S escrut vsc pc Hcont Hden_s Hok).
    - destruct Hsmt as [ec [et [ef [Hm [_ [_ [_ Hden]]]]]]].
      subst escrut. exact (Hden pc Hden_s Hok).
    - exfalso. destruct escrut; simpl in Hcast; discriminate. }
  destruct Hden_c as [pcc [Hden_pcc Hval]].
  exists pcc. split; [| split].
  - exact (Hden_pcc Γc Hfree_c).
  - exact (expr_to_pc_scoped_no_var Γc vsc pcc
             (closed_term_scoped (dom_env Γc) vsc Hcl) (Hden_pcc Γc Hfree_c)).
  - rewrite <- (pc_value_closed σ pcc
      (expr_to_pc_scoped_no_var Γc vsc pcc
         (closed_term_scoped (dom_env Γc) vsc Hcl) (Hden_pcc Γc Hfree_c))).
    exact Hval.
Qed.

(** Fully general version: whatever head the spine settles on (as long as
    it is not itself an unresolved branch), `contains` relates it to the
    matching head on the concrete side. Needed for FoldAlts_Otherwise's
    "the scrutinee is not this constructor" (negative) case, where the
    target head isn't known in advance.

    The Cont_Var_Sym case is exactly why σ must send a variable to a LITERAL:
    a literal does not unspool further, so the concrete head is the literal
    itself and `contains` still relates the two heads. If σ x could be an
    application or a constructor, the concrete spine would have a different
    head from the symbolic one, and this lemma - with it soundness of Rule
    Case - would fail. *)
Lemma contains_unspool_general : forall σ S e_sym e_con,
  contains σ S e_sym e_con ->
  forall L_s L_c,
    Forall2 (contains σ S) L_s L_c ->
    forall hd hargs,
      unspool_app e_sym L_s = (hd, hargs) ->
      is_if hd = false ->
      (exists head_c args_c,
         unspool_app e_con L_c = (head_c, args_c) /\
         contains σ S hd head_c /\
         Forall2 (contains σ S) hargs args_c)
      \/ (exists l args_c, unspool_app e_con L_c = (ELit l, args_c)).
Proof.
  induction 1; intros L_s L_c HL hd hargs Hunspool Hif; simpl in Hunspool;
    try (left; injection Hunspool as ? ?; subst;
         eexists; exists L_c;
         split; [reflexivity | split; [solve [constructor; assumption] | exact HL]]).
  - (* Cont_App *)
    apply IHcontains1 with (L_s := a_s :: L_s) (L_c := a_c :: L_c).
    + constructor; assumption.
    + exact Hunspool.
    + exact Hif.
  - left. injection Hunspool as <- <-. exists ec, L_c.
    split; [destruct ec; try discriminate; reflexivity |].
    split; [eapply Cont_Thunk_Outer; eassumption | exact HL].
  - (* Cont_If_True *) injection Hunspool as ? ?; subst. simpl in Hif. discriminate.
  - (* Cont_If_False *) injection Hunspool as ? ?; subst. simpl in Hif. discriminate.
  - (* Cont_Denote *) right. exists l, L_c. reflexivity.
Qed.

(** `find_alt` looks up alternatives by tag only, and `contains_alt`
    preserves tags exactly, so a symbolic match hit corresponds to a
    concrete match hit on the same tag. *)
Lemma find_alt_contains_alt : forall σ S alts altsc d xs ep,
  Forall2 (contains_alt σ S) alts altsc ->
  find_alt d alts = Some (xs, ep) ->
  exists epc, find_alt d altsc = Some (xs, epc)
    /\ Forall (fun x => S x = false) xs
    /\ contains σ S ep epc.
Proof.
  intros σ S alts altsc d xs ep H.
  induction H as [| a ac alts' altsc' Ha Hrest IH]; intros Hfind.
  - simpl in Hfind; discriminate.
  - simpl in Hfind. destruct a as [d' xs' ep'].
    inversion Ha as [d'' xs'' eps epc Hxs Hcont_ep]; subst.
    simpl. destruct (string_dec d d').
    + inversion Hfind; subst. exists epc. split; [reflexivity | split; assumption].
    + apply IH; assumption.
Qed.

Lemma find_alt_none_contains_alt : forall σ S alts altsc d,
  Forall2 (contains_alt σ S) alts altsc ->
  find_alt d alts = None ->
  find_alt d altsc = None.
Proof.
  intros σ S alts altsc d H.
  induction H as [| a ac alts' altsc' Ha Hrest IH]; intros Hfind.
  - reflexivity.
  - simpl in Hfind. destruct a as [d' xs' ep'].
    inversion Ha as [d'' xs'' eps epc Hxs Hcont_ep]; subst.
    simpl. destruct (string_dec d d'); [discriminate | apply IH; assumption].
Qed.

(** extend_env_multi extended pointwise by contains, argument list by
    argument list, preserves contains_env - needed for FoldAlts_Con's
    pattern body evaluation under the bound constructor arguments. *)
Lemma contains_env_extend_multi : forall σ S xs args_s args_c Γs Γc Γarg_s Γarg_c,
  Forall (fun x => S x = false) xs ->
  contains_env σ S Γs Γc ->
  contains_env σ S Γarg_s Γarg_c ->
  Forall2 (contains σ S) args_s args_c ->
  Forall concore_expr args_c ->
  contains_env σ S (extend_env_multi Γs xs args_s Γarg_s) (extend_env_multi Γc xs args_c Γarg_c).
Proof.
  induction xs as [| x xs' IH];
    intros args_s args_c Γs Γc Γarg_s Γarg_c Hxs Henv Hargenv Hargs Hconcore.
  - simpl. exact Henv.
  - inversion Hxs as [| x0 xs0 Hx Hxs' ]; subst.
    destruct args_s as [| a args_s']; destruct args_c as [| ac args_c'];
      try (inversion Hargs; fail).
    + simpl. apply Cont_Env_Extend;
        [exact Hx | exact Hargenv | apply Cont_Bot | constructor | apply IH; auto].
    + simpl. inversion Hargs as [| a0 ac0 args_s'0 args_c'0 Hcont_a Hargs' Heq1 Heq2]; subst.
      inversion Hconcore as [| ac1 args_c'1 Hcon_a Hconcore' ]; subst.
      apply Cont_Env_Extend.
      * exact Hx.
      * exact Hargenv.
      * exact Hcont_a.
      * exact Hcon_a.
      * apply IH; assumption.
Qed.

Lemma contains_con_value : forall σ S Γs Γc d args_s args_c,
  contains_env σ S Γs Γc ->
  Forall2 (contains σ S) args_s args_c ->
  contains σ S (make_con_app d (map (delay Γs) args_s))
               (make_con_app d (map (delay Γc) args_c)).
Proof.
  intros σ S Γs Γc d args_s args_c Henv Hargs.
  unfold make_con_app. apply contains_fold_left_app; [| apply Cont_Con].
  induction Hargs; simpl; constructor; [apply contains_delay |]; assumption.
Qed.
End ConCore.
