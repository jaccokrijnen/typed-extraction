From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import ExTyping.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import WcbvEvalAux.
From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Psatz.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import ECSubst.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Template Require Import utils.

Import ListNotations.

Import EAstUtils.
Import Erasure.
Import ExAst.

(* We have our own environment which is different from MetaCoq's erased environment
   (it includes more information and a different treatment of types).
   To reconcile this, we map our environments to theirs, but the treatment of types
   remains different. However, MetaCoq does not actually use information about types
   for anything during evaluation, so we just filter them out. This is justified
   by the following lemmas. *)
Definition is_constant (decl : EAst.global_decl) : bool :=
  match decl with
  | EAst.ConstantDecl _ => true
  | _ => false
  end.

Definition only_constants (Σ : EAst.global_context) : EAst.global_context :=
  filter (is_constant ∘ snd) Σ.

Lemma declared_constant_only_constants Σ kn decl :
  ETyping.declared_constant Σ kn decl ->
  ETyping.declared_constant (only_constants Σ) kn decl.
Proof.
  unfold ETyping.declared_constant.
  intros lookup_decl.
  induction Σ; [easy|].
  destruct a as (kn' & decl').
  cbn in *.
  destruct (is_constant decl') eqn:isconst.
  - cbn in *.
    destruct (kername_eq_dec _ _) as [<-|?]; easy.
  - apply IHΣ.
    destruct (kername_eq_dec _ _).
    + inversion lookup_decl; subst; easy.
    + auto.
Qed.

Lemma eval_only_constants Σ s t :
  Σ ⊢ s ▷ t ->
  only_constants Σ ⊢ s ▷ t.
Proof.
  induction 1 using eval_evals_ind;
    eauto using eval, declared_constant_only_constants.
Qed.

Definition trans_cst (cst : constant_body) : EAst.constant_body :=
  {| EAst.cst_body := cst_body cst |}.

Definition trans (Σ : global_env) : EAst.global_context :=
  let map_decl kn (decl : global_decl) : list (kername * EAst.global_decl) :=
      match decl with
      | ConstantDecl cst => [(kn, EAst.ConstantDecl (trans_cst cst))]
      | InductiveDecl _ => []
      end in
  flat_map (fun '(kn, decl) => map_decl kn decl) Σ.

Lemma declared_constant_trans Σ kn cst :
  declared_constant Σ kn cst ->
  ETyping.declared_constant (trans Σ) kn (trans_cst cst).
Proof.
  unfold ETyping.declared_constant, declared_constant in *.
  induction Σ; [easy|]; intros lookup.
  cbn in *.
  destruct a as (kn' & []).
  - cbn in *.
    unfold eq_kername in *.
    destruct (kername_eq_dec kn kn') as [<-|].
    + now inversion lookup; subst; clear lookup.
    + now apply IHΣ.
  - apply IHΣ.
    unfold eq_kername in lookup.
    now destruct (kername_eq_dec _ _).
Qed.

Section dearg_correctness.
Context (ind_masks : list (kername * mib_masks)).
Context (const_masks : list (kername * bitmask)).

Fixpoint has_use (rel : nat) (t : term) : bool :=
  match t with
  | tRel i => i =? rel
  | tEvar _ ts => fold_right orb false (map (has_use rel) ts)
  | tLambda _ body => has_use (S rel) body
  | tLetIn _ val body => has_use rel val || has_use (S rel) body
  | tApp hd arg => has_use rel hd || has_use rel arg
  | tCase _ discr brs => has_use rel discr || fold_right orb false (map (has_use rel ∘ snd) brs)
  | tProj _ t => has_use rel t
  | tFix defs _
  | tCoFix defs _ => fold_right orb false (map (has_use (rel + #|defs|) ∘ dbody) defs)
  | _ => false
  end.

Fixpoint valid_dearg_mask (mask : bitmask) (body : term) : Prop :=
  match body, mask with
  | tLetIn na val body, _ => valid_dearg_mask mask body
  | tLambda _ body, b :: mask =>
    (if b then has_use 0 body = false else True) /\ valid_dearg_mask mask body
  | _, [] => True
  | _, _ => False
  end.

Lemma dearg_cst_body_top_nil t :
  dearg_cst_body_top [] t = t.
Proof.
  induction t; auto.
  cbn.
  now rewrite IHt2.
Qed.

Lemma dearg_single_0_mask mask args t :
  Forall (eq false) mask ->
  #|args| = #|mask| ->
  dearg_single mask t args = mkApps t args.
Proof.
  intros mask_zero.
  revert args t.
  induction mask_zero.
  - destruct args; easy.
  - intros [|a args] t len_eq; [easy|].
    subst.
    cbn in *.
    now apply IHmask_zero.
Qed.

Lemma dearg_single_snoc mask b t args a :
  #|mask| = #|args| ->
  dearg_single (mask ++ [b]) t (args ++ [a]) =
  if b then
    dearg_single mask t args
  else
    tApp (dearg_single mask t args) a.
Proof.
  revert t args b a.
  induction mask as [|b mask IH]; intros t args bend aend len_eq.
  - now destruct args as [|a args]; [|easy].
  - destruct args as [|a args]; [easy|].
    cbn in *.
    destruct b.
    + now apply IH.
    + now apply IH.
Qed.

(* We use our own "properly ordered" contexts to represent the lambdas/lets
   that we debox away. Unlike the rest of MetaCoq, these contexts actually
   have the first declaration at the beginning. *)
Fixpoint subst_context (t : term) (k : nat) (Γ : context) : context :=
  match Γ with
  | [] => []
  | cd :: Γ => map_decl (csubst t k) cd :: subst_context t (S k) Γ
  end.

Definition mkLambda_or_LetIn (cd : context_decl) (t : term) : term :=
  match decl_body cd with
  | None => tLambda (decl_name cd) t
  | Some body => tLetIn (decl_name cd) body t
  end.

Definition it_mkLambda_or_LetIn (Γ : context) (u : term) : term :=
  fold_right mkLambda_or_LetIn u Γ.

Lemma subst_context_app t k Γ Γ' :
  subst_context t k (Γ ++ Γ') =
  subst_context t k Γ ++ subst_context t (length Γ + k) Γ'.
Proof.
  revert t k Γ'.
  induction Γ as [|cd Γ IH]; intros t k Γ'; [easy|].
  cbn.
  f_equal.
  now rewrite IH.
Qed.

Fixpoint decompose_body_masked (mask : bitmask) (t : term) : context * term :=
  match mask, t with
  | _, tLetIn na val body =>
    let (Γ, t) := decompose_body_masked mask body in
    (vdef na val :: Γ, t)
  | b :: mask, tLambda na body =>
    let (Γ, t) := decompose_body_masked mask body in
    (vass na :: Γ, t)
  | _, _ => ([], t)
  end.

Definition vasses (Γ : context) : context :=
  filter (fun cd => match decl_body cd with
                    | Some _ => false
                    | None => true
                    end) Γ.

Lemma vasses_app Γ Γ' :
  vasses (Γ ++ Γ') = vasses Γ ++ vasses Γ'.
Proof.
  unfold vasses.
  now rewrite filter_app.
Qed.

Ltac refold :=
  repeat
    match goal with
    | [H: context[fold_right _ ?t ?Γ] |- _] => progress (fold (it_mkLambda_or_LetIn Γ t) in * )
    | [|- context[fold_right _ ?t ?Γ]] => progress (fold (it_mkLambda_or_LetIn Γ t) in * )
    | [H: context[filter _ ?Γ] |- _] => progress (fold (vasses Γ) in * )
    | [|- context[filter _ ?Γ]] => progress (fold (vasses Γ) in * )
    end.

Lemma decompose_body_masked_spec mask Γ t t' :
  valid_dearg_mask mask t ->
  (Γ, t') = decompose_body_masked mask t ->
  #|vasses Γ| = #|mask| /\
  it_mkLambda_or_LetIn Γ t' = t.
Proof.
  revert Γ t' mask.
  induction t using term_forall_list_ind; intros Γ t' mask valid_mask eq.
  all: cbn in *.
  all: try solve [destruct mask; [|easy]; inversion eq; easy].
  - destruct mask as [|b mask]; inversion eq; subst; clear eq; [easy|].
    cbn in *.
    destruct (decompose_body_masked mask t) as (Γ' & t'') eqn:decomp_eq.
    inversion H0; subst; clear H0.
    symmetry in decomp_eq.
    cbn.
    refold.
    now destruct (IHt _ _ _ (proj2 valid_mask) decomp_eq) as (-> & ->).
  - destruct (decompose_body_masked mask t2) eqn:decomp_eq.
    symmetry in decomp_eq.
    destruct (IHt2 _ _ _ valid_mask decomp_eq).
    now destruct mask; inversion eq; subst.
Qed.

Lemma valid_dearg_mask_spec mask t :
  valid_dearg_mask mask t ->
  exists Γ inner,
    #|vasses Γ| = #|mask| /\ it_mkLambda_or_LetIn Γ inner = t.
Proof.
  intros is_valid.
  destruct (decompose_body_masked mask t) as (Γ & inner) eqn:decomp.
  exists Γ, inner.
  now apply decompose_body_masked_spec.
Qed.

Lemma subst_it_mkLambda_or_LetIn t k Γ u :
  csubst t k (it_mkLambda_or_LetIn Γ u) =
  it_mkLambda_or_LetIn (subst_context t k Γ) (csubst t (k + length Γ) u).
Proof.
  revert t k u.
  induction Γ as [|cd Γ IH]; intros t k u.
  - cbn.
    f_equal; lia.
  - cbn in *; refold.
    destruct cd as [na [val|]];
      cbn in *; refold;
      repeat (f_equal; rewrite ?IH; try lia).
Qed.

Lemma length_subst_context t k Γ :
  #|subst_context t k Γ| = #|Γ|.
Proof.
  revert t k.
  induction Γ; [easy|]; intros t k.
  cbn.
  now rewrite IHΓ.
Qed.

(* Represents normalized values to fill in for assumptions/definitions
   in a context *)
Inductive context_substitution Σ : context -> list term -> Type :=
| ctx_subst_nil : context_substitution Σ [] []
| ctx_subst_ass a av Γ args na :
    Σ ⊢ a ▷ av ->
    context_substitution Σ (subst_context av 0 Γ) args ->
    context_substitution Σ (vass na :: Γ) (a :: args)
| ctx_subst_def body v Γ args na :
    Σ ⊢ body ▷ v ->
    context_substitution Σ (subst_context v 0 Γ) args ->
    context_substitution Σ (vdef na body :: Γ) args.

(* Given [Γ ⊢ t] and normalized args/values for assumptions/definitions in [Γ],
   return ⊢ t' by substituting into t. *)
Equations close_term
         {Σ : global_declarations}
         (inner : term)
         {Γ : context}
         {args : list term}
         (sub : context_substitution Σ Γ args) : term :=
close_term inner ctx_subst_nil := inner;
close_term inner (ctx_subst_ass _ v Γ _ _ _ sub) := close_term (csubst v #|Γ| inner) sub;
close_term inner (ctx_subst_def _ v Γ _ _ _ sub) := close_term (csubst v #|Γ| inner) sub.

Lemma has_use_closed k t n :
  closedn k t ->
  k <= n ->
  has_use n t = false.
Proof.
  revert k n.
  induction t using term_forall_list_ind; intros k n' clos klen;
    cbn in *; auto.
  - propify.
    destruct (Nat.eqb_spec n n'); lia.
  - induction H; [easy|].
    cbn in *.
    propify.
    easy.
  - easy.
  - propify.
    easy.
  - propify.
    easy.
  - propify.
    induction X; [easy|].
    destruct x.
    cbn in *.
    propify.
    easy.
  - easy.
  - revert k n' clos klen.
    induction H; [easy|]; intros k n' clos klen.
    destruct x.
    cbn in *.
    propify.
    split; [easy|].
    replace (n' + S #|l|) with (S n' + #|l|) by abstract lia.
    apply (IHForall (S k)); [|easy].
    now rewrite Nat.add_succ_r.
  - revert k n' clos klen.
    induction H; [easy|]; intros k n' clos klen.
    destruct x.
    cbn in *.
    propify.
    split; [easy|].
    replace (n' + S #|l|) with (S n' + #|l|) by abstract lia.
    apply (IHForall (S k)); [|easy].
    now rewrite Nat.add_succ_r.
Qed.

Lemma has_use_csubst k t u k' :
  has_use k t = false ->
  closedn k u ->
  k < k' ->
  has_use k (csubst u k' t) = false.
Proof.
  revert k u k'.
  induction t using term_forall_list_ind; intros k u k' use_eq clos kltn;
    cbn in *; propify; auto.
  - destruct (Nat.compare_spec k' n) as [->| |].
    + now apply has_use_closed with k.
    + cbn.
      propify.
      lia.
    + cbn.
      propify.
      lia.
  - induction H; [easy|].
    cbn in *.
    propify.
    easy.
  - apply IHt; [easy| |easy].
    now eapply closed_upwards.
  - split; [easy|].
    apply IHt2; [easy| |easy].
    now eapply closed_upwards.
  - split; [easy|].
    apply IHt2; [easy| |easy].
    now eapply closed_upwards.
  - induction X; [easy|].
    destruct x.
    cbn in *.
    propify.
    easy.
  - revert k k' kltn use_eq clos.
    induction H; [easy|]; intros k k' kltn use_eq clos.
    destruct x.
    cbn in *.
    propify.
    rewrite map_length in *.
    split.
    + apply H; [easy| |easy].
      now eapply closed_upwards.
    + setoid_rewrite map_length in IHForall.
      replace (k + S #|l|) with (S k + #|l|) in * by abstract lia.
      rewrite <- Nat.add_succ_r.
      apply IHForall; [easy|easy|].
      now eapply closed_upwards.
  - revert k k' kltn use_eq clos.
    induction H; [easy|]; intros k k' kltn use_eq clos.
    destruct x.
    cbn in *.
    propify.
    rewrite map_length in *.
    split.
    + apply H; [easy| |easy].
      now eapply closed_upwards.
    + setoid_rewrite map_length in IHForall.
      replace (k + S #|l|) with (S k + #|l|) in * by abstract lia.
      rewrite <- Nat.add_succ_r.
      apply IHForall; [easy|easy|].
      now eapply closed_upwards.
Qed.

Lemma valid_dearg_mask_nil t : valid_dearg_mask [] t.
Proof. induction t; easy. Qed.

Lemma valid_dearg_mask_csubst mask t u k :
  valid_dearg_mask mask t ->
  closed u ->
  valid_dearg_mask mask (csubst u k t).
Proof.
  revert mask u k.
  induction t using term_forall_list_ind; intros mask u k valid_mask clos;
    cbn in *;
    try solve [now destruct mask].
  - destruct mask; [|easy].
    apply valid_dearg_mask_nil.
  - destruct mask; [easy|].
    split.
    + destruct b; [|easy].
      now apply (has_use_csubst 0).
    + now apply IHt.
Qed.

Lemma valid_dearg_mask_app mask mask' Γ inner :
  valid_dearg_mask (mask ++ mask') (it_mkLambda_or_LetIn Γ inner) ->
  #|vasses Γ| = #|mask| ->
  valid_dearg_mask mask' inner.
Proof.
  revert mask mask' inner.
  induction Γ as [|cd Γ IH]; intros mask mask' inner len_eq valid_mask.
  - destruct mask; [|easy].
    easy.
  - cbn in *; refold.
    unfold mkLambda_or_LetIn in *.
    destruct (decl_body cd) eqn:decl_eq.
    + cbn in *.
      easy.
    + cbn in *.
      destruct mask; [now cbn in *|].
      cbn in *.
      destruct b.
      * now eapply IH.
      * easy.
Qed.

(*
Section foo.
From Coq Require Import String.
From MetaCoq.Erasure Require Import EPretty.
Open Scope string.

Definition Γ := [vass (nNamed "a")].
Definition Γ' := [vass (nNamed "d"); vass (nNamed "c")].
Definition args := [tVar "a"].
Definition args' := [tVar "c"; tVar "d"].
Definition inner := tRel 0.
Open Scope list.
Compute print_term [] [] false false
        (mkApps (it_mkLambda_or_LetIn (Γ' ++ Γ) inner) (args ++ args')).
Compute print_term [] [] false false
        (mkApps (it_mkLambda_or_LetIn Γ (close_term Γ' inner args')) args).
Compute print_term [] [] false false
        (close_term (Γ' ++ Γ) inner (args ++ args')).
End foo.
*)

Lemma vasses_subst_context t k Γ :
  vasses (subst_context t k Γ) = vasses Γ.
Proof.
  revert t k.
  induction Γ as [|cd Γ IH]; [easy|]; intros t k.
  cbn in *.
  unfold map_decl.
  destruct cd.
  cbn in *.
  destruct decl_body; cbn.
  - easy.
  - f_equal.
    easy.
Qed.

Lemma eval_mkApps_it_mkLambda_or_LetIn Σ Γ inner args v :
  #|args| = #|vasses Γ| ->
  Σ ⊢ mkApps (it_mkLambda_or_LetIn Γ inner) args ▷ v ->
  exists sub : context_substitution Σ Γ args,
    Σ ⊢ close_term inner sub ▷ v.
Proof.
  intros len_eq ev.
  induction #|Γ| as [|Γlen IH] eqn:eq in Γ, len_eq, ev, inner, args |- *.
  - destruct Γ, args; try easy.
    exists (ctx_subst_nil _).
    easy.
  - destruct Γ as [|[na [body|]] Γ];
      cbn in *; refold.
    + easy.
    + apply eval_mkApps_head in ev as ev_hd.
      destruct ev_hd as (hdv & ev_hd).
      apply eval_tLetIn_inv in ev_hd as ev_let.
      destruct ev_let as (bodyv & ev_body & ev_let).
      unshelve epose proof
               (IH (subst_context bodyv 0 Γ)
                   (csubst bodyv #|Γ| inner)
                   args _ _ _) as IH.
      * now rewrite vasses_subst_context.
      * rewrite <- subst_it_mkLambda_or_LetIn.
        eapply eval_mkApps_heads; [exact ev_hd| |]; easy.
      * now rewrite length_subst_context.
      * destruct IH as (sub & ev_close_sub).
        exists (ctx_subst_def _ _ _ _ _ na ev_body sub).
        easy.
    + destruct args as [|a args]; [easy|].
      cbn in *.
      apply eval_mkApps_head in ev as ev_hd.
      destruct ev_hd as (hdv & ev_hd).
      apply eval_tApp_tLambda_inv in ev_hd as ev_app.
      destruct ev_app as (av & ev_a & ev_app).
      unshelve epose proof
               (IH (subst_context av 0 Γ)
                   (csubst av #|Γ| inner)
                   args _ _ _) as IH.
      * now rewrite vasses_subst_context.
      * rewrite <- subst_it_mkLambda_or_LetIn.
        eapply eval_mkApps_heads; [exact ev_hd| |]; easy.
      * now rewrite length_subst_context.
      * destruct IH as (sub & ev_close_sub).
        exists (ctx_subst_ass _ _ _ _ _ na ev_a sub).
        easy.
Qed.

Lemma no_use_subst_eq k t s s' :
  has_use k t = false ->
  csubst s k t = csubst s' k t.
Proof.
  Admitted.

(*
Lemma dearg_subst Σ mask na body bodyv args t tv :
  #|args| = #|mask| ->
  valid_dearg_mask mask t ->
  Σ ⊢ body ▷ bodyv ->
  Σ ⊢ dearg_single mask (dearg_cst_body_top mask (csubst bodyv 0 t)) args ▷ tv ->
  Σ ⊢ dearg_single mask (tLetIn na body (dearg_cst_body_top mask t)) args ▷ tv.
Proof.
  revert mask na body bodyv args tv.
  induction t using term_forall_list_ind;
    intros mask na body bodyv args tv len_eq valid_mask ev_body ev;
    try solve [destruct mask, args; cbn in *; try easy; try now econstructor].
  - cbn -[Nat.compare] in *.
    destruct mask, args; try easy.
    rewrite dearg_cst_body_top_nil in *.
    cbn -[Nat.compare] in *.
    econstructor; [|easy].
    easy.
  - cbn in *.
    destruct args, mask; try easy.
    + cbn in *.
      econstructor.
      * exact ev_body.
      * easy.
    + cbn in *.
      destruct b.
      *
    eapply IHt.
    destruct
  - destruct mask, args; cbn in *; try now econstructor.
    cbn in *.
    now econstructor.
    try ec
    easy.
    destruct ag
    tr
  induction mask as [|[] mask IH]; intros na body bodyv args t tv len_eq valid_mask ev_body ev.
  - cbn in *.
    destruct args; [|easy].
    cbn in *.
    rewrite !dearg_cst_body_top_nil in *.
    now econstructor.
  - destruct args; [easy|].
    cbn in *.
    destruct t; [|easy].
*)

(*
Lemma csubst_subst0 s k t s' :
  (csubst s (S k) t){0 := s'} =
  csubst s k (t{0 := s'}).
Proof.
  revert s k s'.
  induction t using term_forall_list_ind;
    intros s' k s''; cbn -[Nat.compare] in *; try easy.
  - destruct (Nat.compare_spec (S k) n).
    +
*)

Set Keyed Unification.
Declare Equivalent Keys subst1 subst.

Lemma dearg_cst_body_top_subst mask s k Γ inner :
  #|vasses Γ| = #|mask| ->
  dearg_cst_body_top mask (subst [s] k (it_mkLambda_or_LetIn Γ inner)) =
  subst [s] k (dearg_cst_body_top mask (it_mkLambda_or_LetIn Γ inner)).
Proof.
  revert mask s k inner.
  induction Γ as [|cd Γ IH]; intros mask s k inner len_eq.
  - destruct mask; [|easy].
    cbn in *.
    rewrite !dearg_cst_body_top_nil.
    now f_equal.
  - destruct cd as [na [body|]];
      cbn in *; refold.
    + now rewrite IH by easy.
    + destruct mask as [|[] mask].
      * easy.
      * rewrite IH by easy.
        cbn in *.
        now rewrite !distr_subst.
      * now rewrite IH.
Qed.

Lemma eval_dearg_single_head Σ mask head args v :
  #|args| = #|mask| ->
  Σ ⊢ dearg_single mask head args ▷ v ->
  exists hdv, Σ ⊢ head ▷ hdv.
Proof.
  revert head args v.
  induction mask as [|[] mask IH]; intros head args v len_eq ev.
  - cbn in *.
    now apply eval_mkApps_head in ev.
  - destruct args as [|a args]; [easy|].
    cbn in *.
    easy.
  - destruct args as [|a args]; [easy|].
    cbn in *.
    specialize (IH _ _ _ ltac:(easy) ev).
    destruct IH as (appv & ev_app).
    now apply eval_tApp_head in ev_app.
Qed.

Lemma eval_dearg_cst_body_top_inv Σ mask t v :
  env_closed Σ ->
  closed t ->
  Σ ⊢ dearg_cst_body_top mask t ▷ v ->
  exists tv, Σ ⊢ t ▷ tv.
Proof.
  intros env_clos.
  revert mask v.
  induction t using term_forall_list_ind; intros mask v clos ev; try easy.
  - exists (tLambda n t).
    now apply eval_atom.
  - cbn in *.
    propify.
    apply eval_tLetIn_inv in ev.
    destruct ev as (t1v & ev_t1 & ev_sub).
    exists v.
    rewrite closed_subst in ev_sub by (now eapply eval_closed).
    rewrite <- dearg_cst_body_top_subst.

Lemma eval_dearg_single_heads Σ hd hd' hdv mask args v :
  Σ ⊢ hd ▷ hdv ->
  Σ ⊢ hd' ▷ hdv ->
  Σ ⊢ dearg_single mask hd args ▷ v ->
  Σ ⊢ dearg_single mask hd' args ▷ v.
Proof.
  Admitted.

Lemma no_use_subst k t s s' :
  has_use k t = false ->
  subst [s] k t = subst [s'] k t.
Proof.
  revert k.
  induction t using term_forall_list_ind; cbn in *; intros k no_use; propify.
  - easy.
  - destruct (Nat.leb_spec k n).
    + now rewrite !(proj2 (nth_error_None _ _)) by (cbn; lia).
    + easy.
  - easy.
  - f_equal.
    induction H; [easy|].
    cbn in *.
    propify.
    now f_equal.
  - now f_equal.
  - now f_equal.
  - now f_equal.
  - easy.
  - easy.
  - f_equal; [easy|].
    destruct no_use as (_ & no_use).
    induction X; [easy|].
    cbn in *.
    propify.
    f_equal; [|easy].
    now f_equal.
  - now f_equal.
  - f_equal.
    revert k no_use.
    induction H; [easy|]; intros k no_use.
    unfold map_def in *.
    destruct x; cbn in *; propify.
    f_equal.
    + f_equal.
      apply H.
      rewrite <- (proj1 no_use).
      now f_equal.
    + rewrite <- Nat.add_succ_r in *.
      apply IHForall.
      now rewrite Nat.add_succ_comm.
  - f_equal.
    revert k no_use.
    induction H; [easy|]; intros k no_use.
    unfold map_def in *.
    destruct x; cbn in *; propify.
    f_equal.
    + f_equal.
      apply H.
      rewrite <- (proj1 no_use).
      now f_equal.
    + rewrite <- Nat.add_succ_r in *.
      apply IHForall.
      now rewrite Nat.add_succ_comm.
Qed.

Lemma dearg_single_correct mask body args Σ t :
  env_closed Σ ->
  closed body ->
  Forall (closedn 0) args ->
  valid_dearg_mask mask body ->
  #|args| = #|mask| ->
  Σ ⊢ mkApps body args ▷ t ->
  Σ ⊢ dearg_single mask (dearg_cst_body_top mask body) args ▷ t.
Proof.
  intros env_clos body_clos args_clos valid_mask len_eq ev.
  destruct (valid_dearg_mask_spec _ _ valid_mask) as (Γ & inner & vasses_len & <-).
  induction #|Γ| as [|Γlen IH] eqn:eq
    in Γ, mask, valid_mask, args, body_clos, args_clos, inner, ev, len_eq, vasses_len |- *.
  1: { destruct Γ, mask, args; try easy.
       cbn in *.
       now rewrite dearg_cst_body_top_nil. }
  destruct Γ as [|[na [body|]] Γ];
    cbn in *; refold.
  - easy.
  - apply eval_mkApps_head in ev as ev_let.
    destruct ev_let as (letv & ev_let).
    apply eval_tLetIn_inv in ev_let as ev_subst.
    destruct ev_subst as (bodyv & ev_body & ev_subst).
    propify.
    assert (closed bodyv) by (now eapply eval_closed).
    unshelve epose proof
             (IH mask args
                 (subst_context bodyv 0 Γ)
                 (csubst bodyv #|Γ| inner)
                 _ _ _ _ _ _ _) as IH.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      now apply closed_csubst.
    + easy.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      now apply valid_dearg_mask_csubst.
    + easy.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      eapply (eval_mkApps_heads _ _ _ letv); [easy|easy|].
      now eapply eval_mkApps_heads; [exact ev_let| |]; easy.
    + now rewrite vasses_subst_context.
    + now rewrite length_subst_context.
    + rewrite <- subst_it_mkLambda_or_LetIn in IH.
      apply eval_dearg_single_head in IH as ev_top; [|easy].
      destruct ev_top as (topv & ev_top).
      apply eval_dearg_cst_body_top_inv in ev_top as ev_sub_top.
      2: easy.
      2: now apply closed_csubst.
      destruct ev_sub_top as (sub_top & ev_sub_top).
      eapply eval_dearg_single_heads; [exact ev_top| |easy].
      econstructor; [easy|].
      rewrite !closed_subst in * by easy.
      now rewrite <- dearg_cst_body_top_subst.
  - destruct mask as [|[] mask];
      cbn in *; refold.
    + easy.
    + destruct args as [|a args]; [easy|].
      cbn in *.
      apply eval_mkApps_head in ev as ev_app.
      destruct ev_app as (appv & ev_app).
      apply eval_tApp_tLambda_inv in ev_app as ev_subst.
      destruct ev_subst as (av & ev_a & ev_subst).
      assert (closed av).
      { apply Forall_inv in args_clos.
        now eapply eval_closed. }
      unshelve epose proof
      (IH mask args
          (subst_context av 0 Γ)
          (csubst av #|Γ| inner)
          _ _ _ _ _ _ _) as IH.
      * rewrite <- subst_it_mkLambda_or_LetIn.
        now apply closed_csubst.
      * now apply Forall_inv_tail in args_clos.
      * rewrite <- subst_it_mkLambda_or_LetIn.
        now apply valid_dearg_mask_csubst.
      * easy.
      * rewrite <- subst_it_mkLambda_or_LetIn.
        now eapply eval_mkApps_heads; [exact ev_app| |]; easy.
      * now rewrite vasses_subst_context.
      * now rewrite length_subst_context.
      * rewrite <- subst_it_mkLambda_or_LetIn in IH.
        apply eval_dearg_single_head in IH as ev_top; [|easy].
        destruct ev_top as (topv & ev_top).
        apply eval_dearg_cst_body_top_inv in ev_top as ev_sub_top.
        2: easy.
        2: now apply closed_csubst.
        destruct ev_sub_top as (sub_top & ev_sub_top).
        eapply eval_dearg_single_heads; [exact ev_top| |easy].
        unfold subst1.
        rewrite !closed_subst in * by easy.
        rewrite <- dearg_cst_body_top_subst by easy.
        erewrite no_use_subst by easy.
        easy.
    + destruct args as [|a args]; [easy|].
      cbn in *.
      apply eval_mkApps_head in ev as ev_app.
      destruct ev_app as (appv & ev_app).
      apply eval_tApp_tLambda_inv in ev_app as ev_subst.
      destruct ev_subst as (av & ev_a & ev_subst).
      assert (closed av).
      { apply Forall_inv in args_clos.
        now eapply eval_closed. }
      unshelve epose proof
      (IH mask args
          (subst_context av 0 Γ)
          (csubst av #|Γ| inner)
          _ _ _ _ _ _ _) as IH.
      * rewrite <- subst_it_mkLambda_or_LetIn.
        now apply closed_csubst.
      * now apply Forall_inv_tail in args_clos.
      * rewrite <- subst_it_mkLambda_or_LetIn.
        now apply valid_dearg_mask_csubst.
      * easy.
      * rewrite <- subst_it_mkLambda_or_LetIn.
        now eapply eval_mkApps_heads; [exact ev_app| |]; easy.
      * now rewrite vasses_subst_context.
      * now rewrite length_subst_context.
      * rewrite <- subst_it_mkLambda_or_LetIn in IH.
        apply eval_dearg_single_head in IH as ev_top; [|easy].
        destruct ev_top as (topv & ev_top).
        apply eval_dearg_cst_body_top_inv in ev_top as ev_sub_top.
        2: easy.
        2: now apply closed_csubst.
        destruct ev_sub_top as (sub_top & ev_sub_top).
        eapply eval_dearg_single_heads; [exact ev_top| |easy].
        unfold subst1.
        rewrite !closed_subst in * by easy.
        rewrite dearg_cst_body_top_subst in ev_top by easy.
        rewrite <- closed_subst in ev_top by easy.
        eapply eval_beta; [|easy|easy].
        now eapply eval_atom.
Qed.

Print Assumptions dearg_single_correct.

Lemma foo :
  #|mask| = #|args| ->
  Σ ⊢ dearg_single mask  args ▷ res

Inductive eval_apps Σ res : term -> list term -> Prop :=
| eval_apps_nil t : Σ ⊢ t ▷ res -> eval_apps_nil Σ res t []
| eval_apps_cons t args :
    eval_apps Σ res t args ->
    Σ ⊢ tApp t

Fixpoint mkApps_eval_spine :
  -> mkApps t


      Σ ⊢ mkApps hd args ▷ res
  apply eval_mkApps_subst_context in eval; [|congruence].

  induction Γ.
  - cbn in *.
    destruct mask; [|easy].
    destruct args; [|easy].
    now rewrite dearg_cst_body_top_nil.
  - cbn in *; refold.


    rewrite <- it_mkLambda_or_LetIn_unfold in *.
  revert mask body t.
  induction args as [|a args IH] using List.rev_ind; intros mask body t eval valid_mask len_eq.
  - destruct mask as [|b mask]; [|easy].
    now rewrite dearg_cst_body_top_nil.
  - rewrite mkApps_app.
    rewrite app_length in len_eq.
    destruct mask as [|b mask] using List.rev_ind.
    + rewrite dearg_cst_body_top_nil.
      cbn.
      now rewrite Prelim.emkApps_snoc.
    + clear IHmask.
      rewrite app_length in len_eq.
      rewrite dearg_single_snoc by (cbn in *; abstract lia).
      destruct b.
      * destruct (dearg_cst_body_top_snoc_true mask body valid_mask)
          as (na & Γ & inner & -> & ->).

        destruct (valid_dearg_mask_snoc_true mask body valid_mask)
          as (na & inner_body & -> & no_use & valid_inner & ->).
        apply IH; [|easy|cbn in *; abstract lia].
      admit.
      unfold dearg_single.
      intros
    inversion eval; subst; clear eval.
    +
      destruct b.
      *
  intros eval valid_mask.
  revert args t eval mask valid_mask.
  induction body using term_forall_list_ind; intros args t eval mask valid_mask len_eq;
    try solve [
          cbn in *;
          destruct mask as [|[] ?];
          now rewrite ?dearg_single_0_mask].
  - cbn in *.
    clear IHbody.
    revert mask valid_mask len_eq.
    induction args as [|a args IH]; cbn in *; intros mask valid_mask len_eq.
    + destruct mask; easy.
    + destruct mask as [|b mask]; [easy|].
      destruct b; cbn in *.
      *
    admit.
  - cbn in *.
    induction mask as [|b mask]; [easy|].
    destruct args as [|a args]; [easy|].
    destruct b; cbn in *.
    + (* Arg was removed, use the fact that there is no use to show that unlift
         commutes with beta application in this case. *)

    destruct mask as [|[] ?].
    + cbn in *.

  - cbn in *.
    destruct mask as [|[] ?].
    + easy.
    + now rewrite dearg_single_0_mask by easy.
    + now rewrite dearg_single_0_mask by easy.
  - cbn in *.
    assert (Forall (eq false) mask).
    { destruct mask as [|[] ?]; auto. }
    rewrite dearg_single_0_mask by easy.

  - cbn in *.
    destruct mask; [|easy].
    cbn.
    now rewrite dearg_cst_body_top_nil.
  - destruct mask as [|b mask]; [easy|].
    cbn in *.
    destruct b.
    + induction body using term_forall_list_ind;
        try solve [cbn in *; inversion_clear valid_mask; congruence].
      * cbn in *.
        inversion_clear valid_mask; try congruence.
      * cbn in *.
        inversion_clear valid_mask.

Definition const_mask_wf_top Σ (p : kername * bitmask) : Prop :=
  exists cst,
    declared_constant Σ p.1 cst /\
    match cst_body cst with
    | Some body => valid_dearg_mask p.2 body
    | None => False
    end.

Definition const_masks_wf_top Σ : Prop :=
  Forall (const_mask_wf_top Σ) const_masks.

Fixpoint enough_lambdas (mask : bitmask) (body : term) : Prop :=
  match mask, body with
  | _ :: mask, tLambda _ body => enough_lambdas mask body
  | mask, _ => Forall (eq false) mask
  end.

Definition case_shape
           (ind : inductive) (npars : nat)
           (brs : list (nat * term)) : Prop :=
  match get_mib_masks ind_masks (inductive_mind ind) with
  | Some mib_masks =>
    npars = length (param_mask mib_masks) /\
    ∥ Alli (fun c '(_, br) =>
            match find (fun '(ind', c', _) => (ind' =? inductive_ind ind) && (c' =? c))
                       (ctor_masks mib_masks) with
            | Some (_, _, mask) => enough_lambdas mask br
            | None => True
            end)
         0 brs ∥
  | None => True
  end.

(* Proposition representing that all case branches have the correct shapes
   (iterated lambdas) to be dearged. *)
Fixpoint case_shapes (t : term) : Prop :=
  match t with
  | tBox => True
  | tRel _ => True
  | tVar _ => True
  | tEvar _ ts => fold_right and True (map case_shapes ts)
  | tLambda _ body => case_shapes body
  | tLetIn _ val body => case_shapes val /\ case_shapes body
  | tApp hd arg => case_shapes arg /\ case_shapes hd
  | tConst kn => True
  | tConstruct ind c => True
  | tCase (ind, npars) discr brs => case_shape ind npars brs /\
                                    fold_right and True (map (case_shapes ∘ snd) brs)
  | tProj p t => case_shapes t
  | tFix defs _
  | tCoFix defs _ => fold_right and True (map (case_shapes ∘ dbody) defs)
  end.

Notation dearg_ctor := (dearg_ctor ind_masks).
Notation dearg_consts := (dearg_const const_masks).
Notation dearg_case := (dearg_case ind_masks).
Notation dearg_aux := (dearg_aux ind_masks const_masks).
Notation dearg := (dearg ind_masks const_masks).
Notation dearg_cst := (dearg_cst ind_masks const_masks).
Notation dearg_mib := (dearg_mib ind_masks).
Notation dearg_decl := (dearg_decl ind_masks const_masks).
Notation dearg_env := (dearg_env ind_masks const_masks).

Theorem dearg_env_eval Σ s t :
  trans Σ ⊢ s ▷ t ->
  const_masks_wf_top Σ ->
  trans (dearg_env Σ) ⊢ dearg s ▷ dearg t.
Proof.
