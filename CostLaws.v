From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.

Inductive Forall3 {A B C : Type} (R : A -> B -> C -> Prop) : list A -> list B -> list C -> Prop :=
  | Forall3_nil : Forall3 R nil nil nil
  | Forall3_cons : forall a b c la lb lc,
      R a b c -> Forall3 R la lb lc -> Forall3 R (a :: la) (b :: lb) (c :: lc).

Section CostRelation.
Context {sorts : SymCoreSorts}.

Fixpoint smt_size (e : expr) : nat :=
  match e with
  | EApp f a => 1 + smt_size f + smt_size a
  | _ => 1
  end.

Inductive contains_k (σ : valuation) (S : symvars) : nat -> expr -> expr -> Prop :=
  | ContK_Var_Bound : forall x,
      S x = false ->
      contains_k σ S 0 (EVar x) (EVar x)
  | ContK_Var_Sym : forall x,
      S x = true ->
      contains_k σ S 0 (EVar x) (ELit (σ x))
  | ContK_Lit : forall l,
      contains_k σ S 0 (ELit l) (ELit l)
  | ContK_PrimOp : forall p,
      contains_k σ S 0 (EPrimOp p) (EPrimOp p)
  | ContK_Con : forall d,
      contains_k σ S 0 (ECon d) (ECon d)
  | ContK_Coercion : forall γ,
      contains_k σ S 0 (ECoercion γ) (ECoercion γ)
  | ContK_Type : forall τ,
      contains_k σ S 0 (EType τ) (EType τ)
  | ContK_Bot : forall b,
      contains_k σ S 0 (EBot b) (EBot b)
  | ContK_App : forall kf ka f_s a_s f_c a_c,
      contains_k σ S kf f_s f_c ->
      contains_k σ S ka a_s a_c ->
      contains_k σ S (kf + ka) (EApp f_s a_s) (EApp f_c a_c)
  | ContK_Lam : forall k x bodys bodyc,
      S x = false ->
      contains_k σ S k bodys bodyc ->
      contains_k σ S k (ELam x bodys) (ELam x bodyc)
  | ContK_Thunk : forall kenv k Γs Γc es ec,
      contains_env_k σ S kenv Γs Γc ->
      contains_k σ S k es ec ->
      contains_k σ S (kenv + k) (EThunk Γs es) (EThunk Γc ec)
  | ContK_Thunk_Outer : forall kenv k Γs Γc es ec,
      contains_env_k σ S kenv Γs Γc ->
      contains_k σ S k es ec ->
      is_thunk ec = true ->
      contains_k σ S (1 + kenv + k) (EThunk Γs es) ec
  | ContK_Cast : forall k es ec γ,
      contains_k σ S k es ec ->
      contains_k σ S k (ECast es γ) (ECast ec γ)
  | ContK_Case : forall k ks ess esc altss altsc,
      contains_k σ S k ess esc ->
      Forall3 (contains_alt_k σ S) ks altss altsc ->
      contains_k σ S (k + list_sum ks) (ECase ess altss) (ECase esc altsc)
  | ContK_If_True : forall k ec et ef etc,
      models_cond σ S ec ->
      contains_k σ S k et etc ->
      contains_k σ S (1 + smt_size ec + k) (EIf ec et ef) etc
  | ContK_If_False : forall k ec et ef efc,
      models_not_cond σ S ec ->
      contains_k σ S k ef efc ->
      contains_k σ S (1 + smt_size ec + k) (EIf ec et ef) efc
  | ContK_Denote : forall es p args l,
      unspool_app es [] = (EPrimOp p, args) ->
      length args = primop_arity p ->
      smt_ground es = false ->
      denote σ S es l ->
      contains_k σ S (smt_size es) es (ELit l)

with contains_alt_k (σ : valuation) (S : symvars) : nat -> alt -> alt -> Prop :=
  | ContK_Alt : forall k d xs eps epc,
      Forall (fun x => S x = false) xs ->
      contains_k σ S k eps epc ->
      contains_alt_k σ S k (Alt d xs eps) (Alt d xs epc)

with contains_env_k (σ : valuation) (S : symvars) : nat -> environment -> environment -> Prop :=
  | ContK_Env_Empty :
      contains_env_k σ S 0 · ·
  | ContK_Env_Extend : forall kenv ke krest x Γs Γc es ec rest_s rest_c,
      S x = false ->
      contains_env_k σ S kenv Γs Γc ->
      contains_k σ S ke es ec ->
      concore_expr ec ->
      contains_env_k σ S krest rest_s rest_c ->
      contains_env_k σ S (kenv + ke + krest)
        (ExtendEnv x (MkClosure Γs es) rest_s)
        (ExtendEnv x (MkClosure Γc ec) rest_c).

Fixpoint contains_k_erase σ S k es ec (H : contains_k σ S k es ec) {struct H} :
  contains σ S es ec
with contains_alt_k_erase σ S k a_s a_c (H : contains_alt_k σ S k a_s a_c) {struct H} :
  contains_alt σ S a_s a_c
with contains_env_k_erase σ S k Γs Γc (H : contains_env_k σ S k Γs Γc) {struct H} :
  contains_env σ S Γs Γc.
Proof.
  - destruct H as
      [ x Hx | x Hx | l | p | d | γ | τ | b
      | kf ka f_s a_s f_c a_c Hf Ha
      | k x bodys bodyc Hx Hb
      | kenv k Γs Γc es ec Henv He
      | kenv k Γs Γc es ec Henv He Ht
      | k es ec γ He
      | k ks ess esc altss altsc He Halts
      | k ec et ef etc Hm Ht
      | k ec et ef efc Hm Hf
      | es p args l Hun Har Hg Hd ].
    + apply Cont_Var_Bound; exact Hx.
    + apply Cont_Var_Sym; exact Hx.
    + apply Cont_Lit.
    + apply Cont_PrimOp.
    + apply Cont_Con.
    + apply Cont_Coercion.
    + apply Cont_Type.
    + apply Cont_Bot.
    + apply Cont_App; [exact (contains_k_erase _ _ _ _ _ Hf) | exact (contains_k_erase _ _ _ _ _ Ha)].
    + apply Cont_Lam; [exact Hx | exact (contains_k_erase _ _ _ _ _ Hb)].
    + apply Cont_Thunk; [exact (contains_env_k_erase _ _ _ _ _ Henv) | exact (contains_k_erase _ _ _ _ _ He)].
    + apply (Cont_Thunk_Outer σ S Γs Γc es ec);
        [exact (contains_env_k_erase _ _ _ _ _ Henv) | exact (contains_k_erase _ _ _ _ _ He) | exact Ht].
    + apply Cont_Cast. exact (contains_k_erase _ _ _ _ _ He).
    + apply Cont_Case; [exact (contains_k_erase _ _ _ _ _ He) |].
      clear He.
      induction Halts as [| ka a_s a_c ks' la lc Ha Hrest IH]; constructor.
      * exact (contains_alt_k_erase _ _ _ _ _ Ha).
      * exact IH.
    + apply Cont_If_True; [exact Hm | exact (contains_k_erase _ _ _ _ _ Ht)].
    + apply Cont_If_False; [exact Hm | exact (contains_k_erase _ _ _ _ _ Hf)].
    + eapply Cont_Denote; eassumption.
  - destruct H as [k d xs eps epc Hxs He].
    apply Cont_Alt; [exact Hxs | exact (contains_k_erase _ _ _ _ _ He)].
  - destruct H as [| kenv ke krest x Γs Γc es ec rest_s rest_c Hx Henv He Hcon Hrest].
    + apply Cont_Env_Empty.
    + apply Cont_Env_Extend;
        [exact Hx | exact (contains_env_k_erase _ _ _ _ _ Henv) | exact (contains_k_erase _ _ _ _ _ He)
        | exact Hcon | exact (contains_env_k_erase _ _ _ _ _ Hrest)].
Qed.

Fixpoint contains_k_of_contains σ S es ec (H : contains σ S es ec) {struct H} :
  exists k, contains_k σ S k es ec
with contains_alt_k_of_contains_alt σ S a_s a_c (H : contains_alt σ S a_s a_c) {struct H} :
  exists k, contains_alt_k σ S k a_s a_c
with contains_env_k_of_contains_env σ S Γs Γc (H : contains_env σ S Γs Γc) {struct H} :
  exists k, contains_env_k σ S k Γs Γc.
Proof.
  - destruct H as
      [ x Hx | x Hx | l | p | d | γ | τ | b
      | f_s a_s f_c a_c Hf Ha
      | x bodys bodyc Hx Hb
      | Γs Γc es ec Henv He
      | Γs Γc es ec Henv He Ht
      | es ec γ He
      | ess esc altss altsc He Halts
      | ec et ef etc Hm Ht
      | ec et ef efc Hm Hf
      | es p args l Hun Har Hg Hd ].
    + eexists. apply ContK_Var_Bound; exact Hx.
    + eexists. apply ContK_Var_Sym; exact Hx.
    + eexists. apply ContK_Lit.
    + eexists. apply ContK_PrimOp.
    + eexists. apply ContK_Con.
    + eexists. apply ContK_Coercion.
    + eexists. apply ContK_Type.
    + eexists. apply ContK_Bot.
    + destruct (contains_k_of_contains _ _ _ _ Hf) as [kf Hkf].
      destruct (contains_k_of_contains _ _ _ _ Ha) as [ka Hka].
      eexists. exact (ContK_App σ S _ _ _ _ _ _ Hkf Hka).
    + destruct (contains_k_of_contains _ _ _ _ Hb) as [kb Hkb].
      eexists. exact (ContK_Lam σ S _ _ _ _ Hx Hkb).
    + destruct (contains_env_k_of_contains_env _ _ _ _ Henv) as [kenv Hkenv].
      destruct (contains_k_of_contains _ _ _ _ He) as [ke Hke].
      eexists. exact (ContK_Thunk σ S _ _ _ _ _ _ Hkenv Hke).
    + destruct (contains_env_k_of_contains_env _ _ _ _ Henv) as [kenv Hkenv].
      destruct (contains_k_of_contains _ _ _ _ He) as [ke Hke].
      eexists. exact (ContK_Thunk_Outer σ S _ _ _ _ _ _ Hkenv Hke Ht).
    + destruct (contains_k_of_contains _ _ _ _ He) as [ke Hke].
      eexists. exact (ContK_Cast σ S _ _ _ _ Hke).
    + destruct (contains_k_of_contains _ _ _ _ He) as [ke Hke].
      assert (Hks : exists ks, Forall3 (contains_alt_k σ S) ks altss altsc).
      { clear He Hke.
        induction Halts as [| a_s a_c la lc Ha Hrest IH].
        - exists nil. apply Forall3_nil.
        - destruct (contains_alt_k_of_contains_alt _ _ _ _ Ha) as [ka Hka].
          destruct IH as [ks Hks].
          exists (ka :: ks). apply Forall3_cons; [exact Hka | exact Hks]. }
      destruct Hks as [ks Hks].
      eexists. exact (ContK_Case σ S _ _ _ _ _ _ Hke Hks).
    + destruct (contains_k_of_contains _ _ _ _ Ht) as [kt Hkt].
      eexists. exact (ContK_If_True σ S _ _ _ _ _ Hm Hkt).
    + destruct (contains_k_of_contains _ _ _ _ Hf) as [kf Hkf].
      eexists. exact (ContK_If_False σ S _ _ _ _ _ Hm Hkf).
    + eexists. exact (ContK_Denote σ S _ _ _ _ Hun Har Hg Hd).
  - destruct H as [d xs eps epc Hxs He].
    destruct (contains_k_of_contains _ _ _ _ He) as [ke Hke].
    eexists. exact (ContK_Alt σ S _ _ _ _ _ Hxs Hke).
  - destruct H as [| x Γs Γc es ec rest_s rest_c Hx Henv He Hcon Hrest].
    + eexists. apply ContK_Env_Empty.
    + destruct (contains_env_k_of_contains_env _ _ _ _ Henv) as [kenv Hkenv].
      destruct (contains_k_of_contains _ _ _ _ He) as [ke Hke].
      destruct (contains_env_k_of_contains_env _ _ _ _ Hrest) as [kr Hkr].
      eexists. exact (ContK_Env_Extend σ S _ _ _ _ _ _ _ _ _ _ Hx Hkenv Hke Hcon Hkr).
Qed.

Lemma contains_alts_k_erase : forall σ S ks altss altsc,
  Forall3 (contains_alt_k σ S) ks altss altsc -> Forall2 (contains_alt σ S) altss altsc.
Proof.
  intros σ S ks altss altsc H.
  induction H as [| k a_s a_c ks la lc Ha _ IH]; constructor; [| exact IH].
  exact (contains_alt_k_erase _ _ _ _ _ Ha).
Qed.

Lemma contains_alts_k_of_contains_alts : forall σ S altss altsc,
  Forall2 (contains_alt σ S) altss altsc -> exists ks, Forall3 (contains_alt_k σ S) ks altss altsc.
Proof.
  intros σ S altss altsc H.
  induction H as [| a_s a_c la lc Ha _ [ks IH]]; [exists nil; constructor |].
  destruct (contains_alt_k_of_contains_alt _ _ _ _ Ha) as [k Hk].
  exists (k :: ks). constructor; assumption.
Qed.

Scheme contains_k_mut := Induction for contains_k Sort Prop
with contains_alt_k_mut := Induction for contains_alt_k Sort Prop
with contains_env_k_mut := Induction for contains_env_k Sort Prop.

End CostRelation.

Section CostFacts.
Context {sorts : SymCoreSorts}.

Fixpoint thunk_depth (e : expr) : nat :=
  match e with
  | EThunk _ e0 => 1 + thunk_depth e0
  | _ => 0
  end.

Lemma thunk_depth_contains_k : forall σ S k es ec,
  contains_k σ S k es ec -> thunk_depth es <= thunk_depth ec + k.
Proof.
  intros σ S k es ec H.
  induction H; simpl in *; try lia.
  destruct es; simpl in *; try lia. discriminate.
Qed.

Lemma smt_size_contains_k : forall σ S k es ec,
  contains_k σ S k es ec -> smt_size es <= k + smt_size ec.
Proof.
  intros σ S k es ec H.
  induction H; simpl in *; lia.
Qed.

Lemma contains_k_fold_left_app : forall σ S ks l1 l2 k h1 h2,
  Forall3 (contains_k σ S) ks l1 l2 ->
  contains_k σ S k h1 h2 ->
  contains_k σ S (k + list_sum ks) (fold_left EApp l1 h1) (fold_left EApp l2 h2).
Proof.
  intros σ S ks l1 l2 k h1 h2 HF. revert k h1 h2.
  induction HF as [| ka a_s a_c ks l1 l2 Ha _ IH]; intros k h1 h2 Hh; simpl.
  - rewrite Nat.add_0_r. exact Hh.
  - rewrite Nat.add_assoc. apply IH. apply ContK_App; assumption.
Qed.

Lemma forall3_length_right : forall (A B C : Type) (R : A -> B -> C -> Prop) la lb lc,
  Forall3 R la lb lc -> length lb = length lc.
Proof.
  intros A B C R la lb lc H. induction H; simpl; [reflexivity | f_equal; assumption].
Qed.

Lemma forall3_contains_k_erase : forall σ S ks l1 l2,
  Forall3 (contains_k σ S) ks l1 l2 -> Forall2 (contains σ S) l1 l2.
Proof.
  intros σ S ks l1 l2 H.
  induction H as [| k a_s a_c ks l1 l2 Ha _ IH]; constructor; [| exact IH].
  exact (contains_k_erase _ _ _ _ _ Ha).
Qed.

Lemma contains_k_if_inv : forall σ S k ec et ef e_c,
  contains_k σ S k (EIf ec et ef) e_c ->
  exists k0, k = 1 + smt_size ec + k0 /\
    ((models_cond σ S ec /\ contains_k σ S k0 et e_c) \/
     (models_not_cond σ S ec /\ contains_k σ S k0 ef e_c)).
Proof.
  intros σ S k ec et ef e_c H. inversion H; subst.
  - eexists. split; [reflexivity | left; split; assumption].
  - eexists. split; [reflexivity | right; split; assumption].
  - match goal with [Hu : unspool_app _ _ = _ |- _] => discriminate Hu end.
Qed.

End CostFacts.

Section CostLaws.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Definition ground_size (e : expr) : nat := if smt_ground e then smt_size e else 0.

Definition prim_slack (args_c : list expr) : nat :=
  1 + length args_c + list_sum (map ground_size args_c).

Class CastExprContainsK : Prop :=
cast_expr_contains_k : forall σ S k es ec γ,
  contains_k σ S k es ec ->
  contains_k σ S k (cast_expr es γ) (cast_expr ec γ).

Class ReducePrimContainsK : Prop :=
reduce_prim_contains_k : forall σ S p ks args_s args_c,
  Forall closed_term args_c ->
  Forall3 (contains_k σ S) ks args_s args_c ->
  exists k', k' <= list_sum ks + prim_slack args_c /\
    contains_k σ S k' (reduce_prim p args_s) (reduce_prim p args_c).


Lemma forall3_of_forall2_contains : forall σ S args_s args_c,
  Forall2 (contains σ S) args_s args_c ->
  exists ks, Forall3 (contains_k σ S) ks args_s args_c.
Proof.
  intros σ S args_s args_c H.
  induction H as [| a_s a_c la lc Ha _ [ks IH]]; [exists nil; constructor |].
  destruct (contains_k_of_contains _ _ _ _ Ha) as [k Hk].
  exists (k :: ks). constructor; assumption.
Qed.

Lemma cast_expr_contains_of_k : CastExprContainsK -> CastExprContains.
Proof.
  intros Hlaw σ S es ec γ H.
  destruct (contains_k_of_contains _ _ _ _ H) as [k Hk].
  exact (contains_k_erase _ _ _ _ _ (Hlaw σ S k es ec γ Hk)).
Qed.

Lemma reduce_prim_contains_of_k : ReducePrimContainsK -> ReducePrimContains.
Proof.
  intros Hlaw σ S p args_s args_c Hcl H.
  destruct (forall3_of_forall2_contains _ _ _ _ H) as [ks Hks].
  destruct (Hlaw σ S p ks args_s args_c Hcl Hks) as [k' [_ Hk']].
  exact (contains_k_erase _ _ _ _ _ Hk').
Qed.

End CostLaws.

Inductive SymFCCostLaws {sorts : SymCoreSorts} {solver : SymCoreSolver} : Prop :=
  symfc_cost_laws :
    ConCoreLaws -> CastExprContainsK -> ReducePrimContainsK ->
    SymFCCostLaws.

Existing Class SymFCCostLaws.

#[export] Instance concore_laws_of_cost_laws `{laws : SymFCCostLaws} : ConCoreLaws.
Proof. destruct laws; assumption. Qed.
#[export] Instance cast_expr_contains_k_of_laws `{laws : SymFCCostLaws} : CastExprContainsK.
Proof. destruct laws; assumption. Qed.
#[export] Instance reduce_prim_contains_k_of_laws `{laws : SymFCCostLaws} : ReducePrimContainsK.
Proof. destruct laws; assumption. Qed.


Section MergeCost.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}
  {reduce_prim_solvable_law : ReducePrimSolvable}.

Fixpoint field_count (e : expr) : nat :=
  match e with
  | EApp f _ => 1 + field_count f
  | ECast e0 _ => field_count e0
  | _ => 0
  end.

Lemma field_count_unspool : forall e L d args,
  unspool_app e L = (ECon d, args) -> field_count e + length L = length args.
Proof.
  induction e; intros L d0 args0 H; simpl in H; try discriminate H.
  - injection H as _ <-. reflexivity.
  - simpl. rewrite <- (IHe1 _ _ _ H). simpl. lia.
Qed.

Lemma forall3_length_left_right : forall (A B C : Type) (R : A -> B -> C -> Prop) la lb lc,
  Forall3 R la lb lc -> length la = length lc.
Proof.
  intros A B C R la lb lc H. induction H; simpl; [reflexivity | f_equal; assumption].
Qed.

Lemma list_sum_map_offset : forall c ks,
  list_sum (map (fun k => c + k) ks) = length ks * c + list_sum ks.
Proof. intros c ks. induction ks as [| k ks IH]; simpl; [reflexivity | rewrite IH; lia]. Qed.

Lemma contains_k_unspool_con : forall σ S k e_sym e_con,
  contains_k σ S k e_sym e_con ->
  forall ks L_s L_c,
    Forall3 (contains_k σ S) ks L_s L_c ->
    forall d args,
      unspool_app e_sym L_s = (ECon d, args) ->
      exists args_c ks',
        unspool_app e_con L_c = (ECon d, args_c) /\
        Forall3 (contains_k σ S) ks' args args_c /\
        list_sum ks' = k + list_sum ks.
Proof.
  induction 1; intros kl Ls Lc HL d0 args0 Hunspool; simpl in Hunspool;
    try discriminate Hunspool.
  - injection Hunspool as <- <-.
    exists Lc, kl. split; [reflexivity | split; [exact HL | reflexivity]].
  - destruct (IHcontains_k1 (ka :: kl) (a_s :: Ls) (a_c :: Lc)
                (Forall3_cons _ _ _ _ _ _ _ H0 HL) d0 args0 Hunspool)
      as [args_c [ks' [Hu [HF Hs]]]].
    exists args_c, ks'. split; [exact Hu | split; [exact HF | simpl in Hs; lia]].
  - exfalso.
    apply (unspool_app_shift es [] Ls) in H. simpl in H.
    rewrite H in Hunspool. discriminate Hunspool.
Qed.

Lemma zip_if_contains_k_true : forall σ S ec a1 a2 ks args_c,
  models_cond σ S ec ->
  length a1 = length a2 ->
  Forall3 (contains_k σ S) ks a1 args_c ->
  Forall3 (contains_k σ S) (map (fun k => 1 + smt_size ec + k) ks) (zip_if ec a1 a2) args_c.
Proof.
  intros σ S ec a1 a2 ks args_c Hmc Hlen HF. revert a2 Hlen.
  induction HF as [| k x y ks l l' Hxy HF IH]; intros a2 Hlen.
  - destruct a2; simpl; constructor.
  - destruct a2 as [| z zs]; [discriminate |]. simpl.
    constructor; [apply ContK_If_True; assumption | apply IH; simpl in Hlen; auto].
Qed.

Lemma zip_if_contains_k_false : forall σ S ec a1 a2 ks args_c,
  models_not_cond σ S ec ->
  length a1 = length a2 ->
  Forall3 (contains_k σ S) ks a2 args_c ->
  Forall3 (contains_k σ S) (map (fun k => 1 + smt_size ec + k) ks) (zip_if ec a1 a2) args_c.
Proof.
  intros σ S ec a1 a2 ks args_c Hmc Hlen HF. revert a1 Hlen.
  induction HF as [| k x y ks l l' Hxy HF IH]; intros a1 Hlen.
  - destruct a1; simpl; constructor.
  - destruct a1 as [| z zs]; [discriminate |]. simpl.
    constructor; [apply ContK_If_False; assumption | apply IH; simpl in Hlen; auto].
Qed.

Lemma contains_k_clos_inv : forall σ S k Γs x body ec,
  contains_k σ S k (EThunk Γs (ELam x body)) ec ->
  exists Γc bodyc kenv kb, ec = EThunk Γc (ELam x bodyc) /\ S x = false /\
    contains_env_k σ S kenv Γs Γc /\ contains_k σ S kb body bodyc /\ k = kenv + kb.
Proof.
  intros σ S k Γs x body ec H.
  inversion H; subst.
  - match goal with
    | [ Hl : contains_k _ _ _ (ELam _ _) _, He : contains_env_k _ _ _ _ _ |- _ ] =>
        inversion Hl; subst;
        [ eexists; eexists; eexists; eexists;
          split; [reflexivity | split; [assumption | split; [exact He | split; [eassumption | reflexivity]]]]
        | match goal with [Hu : unspool_app _ _ = _ |- _] => discriminate Hu end ]
    end.
  - exfalso.
    match goal with
    | [ Hl : contains_k _ _ _ (ELam _ _) _, Ht : is_thunk _ = true |- _ ] =>
        inversion Hl; subst;
        [ discriminate Ht
        | match goal with [Hu : unspool_app _ _ = _ |- _] => discriminate Hu end ]
    end.
  - match goal with [Hu : unspool_app _ _ = _ |- _] => discriminate Hu end.
Qed.

Definition merge_keeps_k (σ : valuation) (S : symvars) (k : nat) (m e_c : expr) : Prop :=
  (exists k', k' <= (1 + field_count e_c) * k /\ contains_k σ S k' m e_c)
  \/ (inert_scrutinee m /\ inert_scrutinee e_c).

Lemma merge_keeps_k_same : forall σ S k m e_c,
  contains_k σ S k m e_c -> merge_keeps_k σ S k m e_c.
Proof. intros σ S k m e_c H. left. exists k. split; [nia | exact H]. Qed.

Lemma merge_keeps_k_zero : forall σ S k m e_c,
  contains_k σ S 0 m e_c -> merge_keeps_k σ S k m e_c.
Proof. intros σ S k m e_c H. left. exists 0. split; [lia | exact H]. Qed.

Lemma ite_leaf_clos_contains_k : forall σ S Γ k ec Γ1 e1 Γ2 e2 e_c,
  contains_k σ S k (EIf ec (EThunk Γ1 e1) (EThunk Γ2 e2)) e_c ->
  merge_keeps_k σ S k (ite_leaf Γ ec (EThunk Γ1 e1) (EThunk Γ2 e2)) e_c.
Proof.
  intros σ S Γ k ec Γ1 e1 Γ2 e2 e_c Hc.
  unfold ite_leaf. simpl.
  destruct e1 as [| | | | | x1 b1 | | | | | | | ]; try (apply merge_keeps_k_same; exact Hc).
  destruct e2 as [| | | | | x2 b2 | | | | | | | ]; try (apply merge_keeps_k_same; exact Hc).
  destruct (env_eqb Γ1 Γ2 && String.eqb x1 x2)%bool eqn:Hx; [| apply merge_keeps_k_same; exact Hc].
  apply andb_prop in Hx as [Hxe Hxx].
  apply env_eqb_eq in Hxe. apply String.eqb_eq in Hxx. subst Γ2 x2.
  destruct (contains_k_if_inv σ S _ ec _ _ e_c Hc) as [k0 [-> [[Hmc Hct] | [Hmc Hcf]]]].
  - destruct (contains_k_clos_inv σ S _ Γ1 x1 b1 e_c Hct)
      as [Γc [bc [kenv [kb [Heq [Hsx [Henv [Hb Hk]]]]]]]].
    subst e_c k0. apply merge_keeps_k_same.
    replace (1 + smt_size ec + (kenv + kb)) with (kenv + (1 + smt_size ec + kb)) by lia.
    apply ContK_Thunk; [exact Henv |].
    apply ContK_Lam; [exact Hsx | apply ContK_If_True; assumption].
  - destruct (contains_k_clos_inv σ S _ Γ1 x1 b2 e_c Hcf)
      as [Γc [bc [kenv [kb [Heq [Hsx [Henv [Hb Hk]]]]]]]].
    subst e_c k0. apply merge_keeps_k_same.
    replace (1 + smt_size ec + (kenv + kb)) with (kenv + (1 + smt_size ec + kb)) by lia.
    apply ContK_Thunk; [exact Henv |].
    apply ContK_Lam; [exact Hsx | apply ContK_If_False; assumption].
Qed.

Ltac merge_leaf_rest_k et ef Hc Hcases :=
  destruct et; destruct ef; simpl; try (apply merge_keeps_k_same; exact Hc);
  try exact (ite_leaf_clos_contains_k _ _ · _ _ _ _ _ _ _ Hc);
  try (match goal with
       | |- merge_keeps_k _ _ _ (match ?b with _ => _ end) _ =>
           destruct b; apply merge_keeps_k_same; exact Hc
       end);
  match goal with
  | |- merge_keeps_k _ _ _ (if ?b then _ else _) _ =>
      let Hx := fresh "Hx" in
      destruct b eqn:Hx; [| apply merge_keeps_k_same; exact Hc];
      first [apply dec_eqb_eq in Hx | apply bottom_eqb_eq in Hx]; subst;
      let k0 := fresh "k0" in
      let Hk := fresh "Hk" in
      let Hm := fresh "Hm" in
      let Ha := fresh "Ha" in
      destruct Hcases as [k0 [Hk [[Hm Ha] | [Hm Ha]]]];
      inversion Ha; subst;
      try (match goal with [Hu : unspool_app _ _ = _ |- _] => discriminate Hu end);
      apply merge_keeps_k_zero; constructor
  end.

Lemma ite_leaf_contains_k : forall σ S Γ k ec et ef e_c,
  contains_k σ S k (EIf ec et ef) e_c -> merge_keeps_k σ S k (ite_leaf Γ ec et ef) e_c.
Proof.
  intros σ S Γ k ec et ef e_c Hc.
  assert (Hcases := contains_k_if_inv σ S k ec et ef e_c Hc).
  unfold ite_leaf.
  destruct (decompose_con_app et) as [[d1 a1]|] eqn:E1;
  destruct (decompose_con_app ef) as [[d2 a2]|] eqn:E2.
  - destruct (andb (String.eqb d1 d2) (Nat.eqb (length a1) (length a2))) eqn:Hg;
      [| apply merge_keeps_k_same; exact Hc].
    apply andb_prop in Hg as [Hd Hl].
    apply String.eqb_eq in Hd. apply Nat.eqb_eq in Hl. subst d2.
    assert (Hu1 := decompose_con_app_unspool et d1 a1 E1).
    assert (Hu2 := decompose_con_app_unspool ef d1 a2 E2).
    left.
    destruct Hcases as [k0 [-> [[Hmc Hct] | [Hmc Hcf]]]].
    + destruct (contains_k_unspool_con σ S _ et e_c Hct nil nil nil (Forall3_nil _) d1 a1 Hu1)
        as [args_c [ks [Huc [HFa Hs]]]].
      pose proof (field_count_unspool e_c nil d1 args_c Huc) as Hn.
      pose proof (forall3_length_left_right _ _ _ _ _ _ _ HFa) as Hlen.
      exists (list_sum (map (fun k => 1 + smt_size ec + k) ks)).
      split.
      * rewrite list_sum_map_offset. simpl in Hs, Hn. nia.
      * rewrite <- (unspool_make_con_app e_c d1 args_c Huc).
        unfold make_con_app.
        exact (contains_k_fold_left_app σ S _ _ _ 0 _ _
                 (zip_if_contains_k_true σ S ec a1 a2 ks args_c Hmc Hl HFa) (ContK_Con σ S d1)).
    + destruct (contains_k_unspool_con σ S _ ef e_c Hcf nil nil nil (Forall3_nil _) d1 a2 Hu2)
        as [args_c [ks [Huc [HFa Hs]]]].
      pose proof (field_count_unspool e_c nil d1 args_c Huc) as Hn.
      pose proof (forall3_length_left_right _ _ _ _ _ _ _ HFa) as Hlen.
      exists (list_sum (map (fun k => 1 + smt_size ec + k) ks)).
      split.
      * rewrite list_sum_map_offset. simpl in Hs, Hn. nia.
      * rewrite <- (unspool_make_con_app e_c d1 args_c Huc).
        unfold make_con_app.
        exact (contains_k_fold_left_app σ S _ _ _ 0 _ _
                 (zip_if_contains_k_false σ S ec a1 a2 ks args_c Hmc Hl HFa) (ContK_Con σ S d1)).
  - destruct (solvable_dec Γ et) as [Ht |]; [destruct (solvable_dec Γ ef) as [Hf |] |].
    + right. exact (smt_ite_inert σ S Γ ec et ef e_c Ht Hf (contains_k_erase _ _ _ _ _ Hc)).
    + apply merge_keeps_k_same. exact Hc.
    + merge_leaf_rest_k et ef Hc Hcases.
  - destruct (solvable_dec Γ et) as [Ht |]; [destruct (solvable_dec Γ ef) as [Hf |] |].
    + right. exact (smt_ite_inert σ S Γ ec et ef e_c Ht Hf (contains_k_erase _ _ _ _ _ Hc)).
    + apply merge_keeps_k_same. exact Hc.
    + merge_leaf_rest_k et ef Hc Hcases.
  - destruct (solvable_dec Γ et) as [Ht |]; [destruct (solvable_dec Γ ef) as [Hf |] |].
    + right. exact (smt_ite_inert σ S Γ ec et ef e_c Ht Hf (contains_k_erase _ _ _ _ _ Hc)).
    + apply merge_keeps_k_same. exact Hc.
    + merge_leaf_rest_k et ef Hc Hcases.
Qed.

Lemma ite_contains_k : forall σ S Γ et ec ef k e_c,
  contains_k σ S k (EIf ec et ef) e_c -> merge_keeps_k σ S k (ite Γ ec et ef) e_c.
Proof.
  intros σ S Γ et. induction et; intros ec ef k e_c Hc;
    try (rewrite ite_leaf_of by (left; reflexivity);
         apply ite_leaf_contains_k; exact Hc).
  destruct ef; try (rewrite ite_leaf_of by (right; reflexivity);
                    apply ite_leaf_contains_k; exact Hc).
  rewrite ite_cast.
  destruct (dec_eqb coercion_eq_dec c c0) eqn:Hx; [| apply merge_keeps_k_same; exact Hc].
  apply dec_eqb_eq in Hx. subst c0.
  destruct (contains_k_if_inv σ S _ ec (ECast et c) (ECast ef c) e_c Hc)
    as [k0 [-> [[Hmc Hct] | [Hmc Hcf]]]].
  - inversion Hct; subst;
      [| match goal with [Hu : unspool_app _ _ = _ |- _] => discriminate Hu end].
    match goal with
    | [ Hi : contains_k _ _ k0 et ?ec0 |- _ ] =>
        destruct (IHet ec ef _ _ (ContK_If_True σ S k0 ec et ef _ Hmc Hi))
          as [[k' [Hk' Hc']] | _];
        [ left; exists k'; split; [simpl; exact Hk' | apply ContK_Cast; exact Hc']
        | right; split; apply inert_cast ]
    end.
  - inversion Hcf; subst;
      [| match goal with [Hu : unspool_app _ _ = _ |- _] => discriminate Hu end].
    match goal with
    | [ Hi : contains_k _ _ k0 ef ?ec0 |- _ ] =>
        destruct (IHet ec ef _ _ (ContK_If_False σ S k0 ec et ef _ Hmc Hi))
          as [[k' [Hk' Hc']] | _];
        [ left; exists k'; split; [simpl; exact Hk' | apply ContK_Cast; exact Hc']
        | right; split; apply inert_cast ]
    end.
Qed.

Lemma merge_contains_k : forall σ S Γ k es ec,
  contains_k σ S k es ec ->
  merge_keeps_k σ S k (merge Γ es) ec.
Proof.
  intros σ S Γ k es ec H. destruct es; simpl; try (apply merge_keeps_k_same; exact H).
  apply ite_contains_k. exact H.
Qed.


End MergeCost.
