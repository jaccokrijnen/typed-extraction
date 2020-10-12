From ConCert.Extraction Require Import Annotations.
From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import ResultMonad.
From Coq Require Import List.
From Coq Require Import VectorDef.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EArities.
From MetaCoq.Erasure Require Import Extract.
From MetaCoq.Erasure Require SafeErasureFunction.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICInversion.
From MetaCoq.PCUIC Require Import PCUICLiftSubst.
From MetaCoq.PCUIC Require Import PCUICGeneration.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.PCUIC Require Import PCUICValidity.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
From MetaCoq.SafeChecker Require Import PCUICSafeRetyping.
From MetaCoq.Template Require Import Kernames.

Import VectorNotations.
Import ListNotations.

Open Scope list.

Section fix_env.
Opaque flag_of_type erase_type.

Context (Σ : global_env_ext).
Context (wfextΣ : ∥wf_ext Σ∥).
Lemma wfΣ : ∥wf Σ∥.
Proof. now sq. Qed.

Section annotate.
  Context {A : Type}.
  Context (annotate_types :
             forall Γ t (Ht : welltyped Σ Γ t) et (er : erases Σ Γ t et), annots A et).

  Equations? (noeqns) annotate_branches
           Γ
           (brs : list (nat × term))
           (ebrs : list (nat × E.term))
           (wf : Forall2 (fun '(_, t) '(_, et) => welltyped Σ Γ t /\ erases Σ Γ t et) brs ebrs)
    : bigprod (annots A ∘ snd) ebrs by struct ebrs :=
    annotate_branches Γ _ [] _ := tt;
    annotate_branches Γ ((_, t) :: brs) ((_, et) :: ebrs) wf :=
      (annotate_types Γ t _ et _, annotate_branches Γ brs ebrs _);
    annotate_branches _ _ _ _ := !.
  Proof. all: now depelim wf. Qed.

  Equations? (noeqns) annotate_defs
           Γ
           (defs : list (def term))
           (edefs : list (E.def E.term))
           (wf : Forall2 (fun d ed => welltyped Σ Γ (dbody d) /\ erases Σ Γ (dbody d) (E.dbody ed))
                         defs edefs)
    : bigprod (annots A ∘ E.dbody) edefs by struct edefs :=
    annotate_defs Γ _ [] _ := tt;
    annotate_defs Γ (d :: defs) (ed :: edefs) wf :=
      (annotate_types Γ (dbody d) _ (E.dbody ed) _, annotate_defs Γ defs edefs _);
    annotate_defs _ _ _ _ := !.
  Proof. all: now depelim wf. Qed.
End annotate.

Fixpoint vec_repeat {A} (a : A) (n : nat) : Vector.t A n :=
  match n with
  | 0 => []%vector
  | S n => (a :: vec_repeat a n)%vector
  end.

Program Definition erase_type_of Γ t (wt : welltyped Σ Γ t) : box_type :=
  let ty := type_of Σ wfΣ _ Γ t wt in
  let flag := flag_of_type Σ wfextΣ Γ ty _ in
  if is_arity flag then
    TBox
  else
    (erase_type_aux Σ wfextΣ Γ (vec_repeat RelOther #|Γ|) ty _ None).2.
Next Obligation.
  destruct wfextΣ as [[]].
  now constructor.
Qed.
Next Obligation.
  unfold type_of.
  destruct infer as (ty & [(typ & ?)]).
  cbn.
  destruct wfΣ.
  constructor.
  eapply validity_term; eauto.
Qed.
Next Obligation.
  unfold type_of in *.
  destruct infer as (ty & [(typ & ?)]).
  cbn in *.
  destruct wfΣ.
  eapply validity_term in typ; eauto.
  destruct typ.
  - now apply nIs_conv_to_Arity_isWfArity_elim in H.
  - now constructor.
Qed.

Equations? (noeqns) annotate_types
         (Γ : context)
         (t : term) (wt : welltyped Σ Γ t)
         (et : E.term)
         (er : erases Σ Γ t et) : annots box_type et by struct et :=
(* For some reason 'with' hangs forever so we need 'where' here *)
annotate_types Γ t wt et er := annot (erase_type_of Γ t wt) et t wt er
where annot
        (bt : box_type)
        (et : E.term)
        (t : term) (wt : welltyped Σ Γ t)
        (er : erases Σ Γ t et) : annots box_type et := {
annot bt E.tBox _ _ _ => bt;
annot bt (E.tRel _) _ _ _ => bt;
annot bt (E.tVar _) _ _ _ => bt;
annot bt (E.tEvar _ ets) t wt er => !;
annot bt (E.tLambda na eB) (tLambda na' A B) wt er => (bt, annotate_types (Γ,, vass na' A) B _ eB _);
annot bt (E.tLetIn na eb eb') (tLetIn na' b ty b') wt er =>
  (bt, (annotate_types Γ b _ eb _, annotate_types (Γ,, vdef na' b ty) b' _ eb' _));
annot bt (E.tApp ehd earg) (tApp hd arg) wt er =>
  (bt, (annotate_types Γ hd _ ehd _, annotate_types Γ arg _ earg _));
annot bt (E.tConst _) _ wt er => bt;
annot bt (E.tConstruct _ _) _ wt er => bt;
annot bt (E.tCase _ ediscr ebrs) (tCase _ _ discr brs) wt er =>
  (bt, (annotate_types Γ discr _ ediscr _, annotate_branches annotate_types Γ brs ebrs _));
annot bt (E.tProj _ et) (tProj _ t) wt er => (bt, annotate_types Γ t _ et _);
annot bt (E.tFix edefs _) (tFix defs _) wt er =>
  (bt, annotate_defs annotate_types (Γ,,, fix_context defs) defs edefs _);
annot bt (E.tCoFix edefs _) (tCoFix defs _) wt er =>
  (bt, annotate_defs annotate_types (Γ,,, fix_context defs) defs edefs _);
annot bt _ _ wt er => !
}.
Proof.
  all: try solve [inversion er; auto].
  all: destruct wt.
  all: destruct wfextΣ as [[]].
  - depelim er.
    now apply inversion_Evar in X.
  - apply inversion_Lambda in X as (? & ? & ? & ? & ?); auto.
    econstructor; eauto.
  - apply inversion_LetIn in X as (?&?&?&?&?&?); auto.
    econstructor; eauto.
  - apply inversion_LetIn in X as (?&?&?&?&?&?); auto.
    econstructor; eauto.
  - apply inversion_App in X as (?&?&?&?&?&?); auto.
    econstructor; eauto.
  - apply inversion_App in X as (?&?&?&?&?&?); auto.
    econstructor; eauto.
  - apply inversion_Case in X as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?); auto.
    econstructor; eauto.
  - apply inversion_Case in X as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?); auto.
    depelim er.
    clear -a X.
    induction X in x5, a, X |- *; [constructor|].
    depelim a.
    constructor; eauto.
    destruct x, y0.
    destruct r.
    destruct p as ((?&?)&?).
    cbn in *.
    split; [|now auto].
    econstructor; eauto.
  - apply inversion_Proj in X as (?&?&?&?&?&?&?&?&?); auto.
    econstructor; eauto.
  - apply inversion_Fix in X as (?&?&?&?&?&?&?); auto.
    depelim er.
    clear -a0 X.
    eapply All2_All_mix_left in X; eauto.
    clear -X.
    revert X.
    generalize (Γ,,, fix_context defs).
    clear Γ.
    intros Γ a.
    induction a; [now constructor|].
    constructor; [|now eauto].
    destruct r as ((? & ?) & ? & ? & ?).
    split; [|now auto].
    econstructor; eauto.
  - apply inversion_CoFix in X as (?&?&?&?&?&?&?); auto.
    depelim er.
    clear -a0 X.
    eapply All2_All_mix_left in X; eauto.
    clear -X.
    revert X.
    generalize (Γ,,, fix_context defs).
    clear Γ.
    intros Γ a.
    induction a; [now constructor|].
    constructor; [|now eauto].
    destruct r as (? & ? & ? & ?).
    split; [|now auto].
    econstructor; eauto.
Qed.

Definition annotate_types_erase_constant_decl cst wt :
  match erase_constant_decl Σ wfextΣ cst wt with
  | Ok (inl cst) => constant_body_annots box_type cst
  | _ => unit
  end.
Proof.
  unfold erase_constant_decl.
  destruct flag_of_type.
  cbn in *.
  destruct is_arity.
  - destruct is_sort; [|exact tt].
    destruct cst; cbn.
    destruct cst_body; exact tt.
  - destruct cst; cbn.
    destruct cst_body; [|exact tt].
    cbn.
    apply (annotate_types [] t); [|apply SafeErasureFunction.erases_erase].
    cbn in *.
    destruct wt.
    econstructor; eauto.
Defined.

Definition annotate_types_erase_global_decl kn decl wt :
  match erase_global_decl Σ wfextΣ kn decl wt with
  | Ok decl => global_decl_annots box_type decl
  | _ => unit
  end.
Proof.
  unfold erase_global_decl.
  destruct decl; [|exact tt].
  cbn.
  pose proof (annotate_types_erase_constant_decl c wt).
  destruct erase_constant_decl; [|exact tt].
  cbn.
  destruct t; [|exact tt].
  exact X.
Defined.

End fix_env.

Definition annotate_types_erase_global_decls_deps_recursive Σ wfΣ include ignore_deps :
  match erase_global_decls_deps_recursive Σ wfΣ include ignore_deps with
  | Ok Σ => env_annots box_type Σ
  | _ => unit
  end.
Proof.
  revert include.
  induction Σ; intros include; [exact tt|].
  cbn in *.
  destruct a.
  destruct KernameSet.mem.
  - cbn.
    match goal with
    | |- context[erase_global_decl ?a ?b ?c ?d ?e] =>
      pose proof (annotate_types_erase_global_decl a b c d e);
        destruct erase_global_decl
    end; [|exact tt].
    match goal with
    | |- context[erase_global_decls_deps_recursive _ ?prf ?incl _] =>
      specialize (IHΣ prf incl);
        destruct erase_global_decls_deps_recursive
    end; [|exact tt].
    cbn.
    exact (X, IHΣ).
  - match goal with
    | |- context[erase_global_decls_deps_recursive _ ?prf ?incl _] =>
      specialize (IHΣ prf incl);
        destruct erase_global_decls_deps_recursive
    end; [|exact tt].
    exact IHΣ.
Defined.

Import EAst.
Definition annot_dearg_lambdas {A} mask {t} (ta : annots A t)
  : annots A (dearg_lambdas mask t).
Proof.
  revert t ta mask.
  fix f 1.
  intros [] ta mask; cbn in *; try exact ta.
  - destruct mask; [exact ta|].
    destruct b.
    + apply annot_subst1; [exact ta.1|].
      apply (f _ ta.2).
    + exact (ta.1, f _ ta.2 _).
  - exact (ta.1, (ta.2.1, f _ ta.2.2 _)).
Defined.

Definition annot_dearg_single
           mask
           {hd}
           (hda : annots box_type hd)
           {args}
           (argsa : All (fun t => box_type * annots box_type t) args)
  : annots box_type (dearg_single mask hd args).
Proof.
  revert hd hda args argsa.
  induction mask; intros hd hda args argsa; cbn.
  - apply annot_mkApps; assumption.
  - destruct a.
    + (* arg is being removed but overall type does not change. *)
      destruct argsa.
      * (* there is no arg. Lambda has original type so body has type of codomain *)
        refine (annot hda, _).
        apply IHmask; [|exact All_nil].
        apply annot_lift.
        (* type of body is now the codomain *)
        exact (map_annot
                 (fun bt =>
                    match bt with
                    | TArr _ cod => cod
                    | _ => bt
                    end) hda).
      * (* arg was removed. We take the new type to be the old type of the application
         instead of the codomain as the old type of the application is more specialized. *)
        apply IHmask; [|exact argsa].
        exact (map_annot (fun _ => p.1) hda).
    + destruct argsa.
      * refine (annot hda, _).
        apply IHmask; [|exact All_nil].
        cbn.
        exact (match annot hda with
                | TArr dom cod => (cod, (annot_lift _ _ hda, dom))
                | t => (t, (annot_lift _ _ hda, t))
                end).
      * apply IHmask; [|exact argsa].
        exact (p.1, (hda, p.2)).
Defined.

Definition annot_dearg_case_branches
           {A}
           mm i
           {brs} (brsa : bigprod (annots A ∘ snd) brs)
  : bigprod (annots A ∘ snd) (dearg_case_branches mm i brs).
Proof.
  destruct mm; [|exact brsa].
  cbn.
  apply bigprod_mapi_rec; [|exact brsa].
  intros.
  apply annot_dearg_lambdas.
  exact X.
Defined.

Definition annot_dearg_aux
           im cm
           {args : list term}
           (argsa : All (fun t => box_type * annots box_type t) args)
           {t : term}
           (ta : annots box_type t) : annots box_type (dearg_aux im cm args t).
Proof.
  revert args argsa t ta.
  fix f 3.
  intros args argsa [] ta; cbn.
  - exact (annot_mkApps ta argsa).
  - exact (annot_mkApps ta argsa).
  - exact (annot_mkApps ta argsa).
  - apply annot_mkApps; [|exact argsa].
    cbn in *.
    refine (ta.1, bigprod_map _ ta.2).
    apply f.
    exact All_nil.
  - apply annot_mkApps; [|exact argsa].
    exact (ta.1, f _ All_nil _ ta.2).
  - apply annot_mkApps; [|exact argsa].
    exact (ta.1, (f _ All_nil _ ta.2.1, f _ All_nil _ ta.2.2)).
  - apply f; [|exact ta.2.1].
    apply All_cons; [|exact argsa].
    exact (ta.1, f _ All_nil _ ta.2.2).
  - exact (annot_dearg_single _ ta argsa).
  - exact (annot_dearg_single _ ta argsa).
  - destruct p.
    refine (annot_mkApps _ argsa).
    cbn in *.
    refine (ta.1, _).
    refine (f _ All_nil _ ta.2.1, _).
    apply annot_dearg_case_branches.
    apply bigprod_map; [|exact ta.2.2].
    intros.
    exact (f _ All_nil _ X).
  - destruct p as ((? & ?) & ?).
    refine (annot_mkApps _ argsa).
    refine (ta.1, _).
    exact (f _ All_nil _ ta.2).
  - refine (annot_mkApps _ argsa).
    refine (ta.1, _).
    fold (annots box_type).
    apply bigprod_map; [|exact ta.2].
    intros.
    exact (f _ All_nil _ X).
  - refine (annot_mkApps _ argsa).
    refine (ta.1, _).
    fold (annots box_type).
    apply bigprod_map; [|exact ta.2].
    intros.
    exact (f _ All_nil _ X).
Defined.

Definition annot_dearg im cm {t : term} (ta : annots box_type t) : annots box_type (dearg im cm t) :=
  annot_dearg_aux im cm All_nil ta.

Definition annot_debox_type_decl Σ {decl} (a : global_decl_annots box_type decl)
  : global_decl_annots box_type (debox_type_decl Σ decl).
Proof.
  unfold debox_type_decl.
  destruct decl; [|exact a|exact a].
  cbn in *.
  (* we have removed type variables from inductives, so adjust type annotations similarly *)
  unfold constant_body_annots in *.
  cbn.
  destruct Ex.cst_body; [|exact tt].
  exact (map_annots (debox_box_type Σ) a).
Defined.

Definition annot_debox_env_types {Σ} (a : env_annots box_type Σ)
  : env_annots box_type (debox_env_types Σ).
Proof.
  unfold debox_env_types.
  apply bigprod_map; [|exact a].
  intros.
  apply annot_debox_type_decl.
  exact X.
Defined.

Definition annot_dearg_cst im cm kn {cst} (a : constant_body_annots box_type cst)
  : constant_body_annots box_type (dearg_cst im cm kn cst).
Proof.
  red in a |- *.
  unfold dearg_cst.
  cbn in *.
  destruct Annotations.Ex.cst_body; [|exact tt].
  cbn.
  apply annot_dearg.
  apply annot_dearg_lambdas.
  exact a.
Defined.

Definition annot_dearg_decl im cm kn {decl} (a : global_decl_annots box_type decl) :
  global_decl_annots box_type (dearg_decl im cm kn decl).
Proof.
  unfold dearg_decl.
  destruct decl; try exact a.
  cbn.
  apply annot_dearg_cst.
  exact a.
Defined.

Definition annot_dearg_env im cm {Σ} (a : env_annots box_type Σ)
  : env_annots box_type (dearg_env im cm Σ).
Proof.
  apply bigprod_map; [|exact a].
  intros ((? & ?) & ?) ?.
  cbn in *.
  apply annot_dearg_decl.
  exact X.
Defined.

Definition annot_extract_pcuic_env params Σ wfΣ include ignore :
  match extract_pcuic_env params Σ wfΣ include ignore with
  | Ok Σ => env_annots box_type Σ
  | _ => unit
  end.
Proof.
  unfold extract_pcuic_env.
  pose proof (annotate_types_erase_global_decls_deps_recursive Σ wfΣ include ignore).
  destruct erase_global_decls_deps_recursive; cbn; [|exact tt].
  destruct dearg_args; [|exact X].
  destruct (_ && _); [exact tt|].
  destruct analyze_env.
  destruct (_ && _); [exact tt|].
  destruct (_ && _); [exact tt|].
  apply annot_debox_env_types.
  apply annot_dearg_env.
  exact X.
Defined.

Definition annot_extract_pcuic_env_sig
           (params : extract_pcuic_params)
           (Σ : P.global_env) (wfΣ : ∥wf Σ∥)
           (include : KernameSet.t)
           (ignore : kername -> bool) : option (∑ Σ, env_annots box_type Σ).
Proof.
  pose proof (annot_extract_pcuic_env params Σ wfΣ include ignore).
  destruct extract_pcuic_env; [|exact None].
  exact (Some (t; X)).
Defined.

Definition annot_extract_template_env params Σ include ignore :
  match extract_template_env params Σ include ignore with
  | Ok Σ => env_annots box_type Σ
  | _ => unit
  end.
Proof.
  unfold extract_template_env.
  destruct check_wf_env_func; [|exact tt].
  apply annot_extract_pcuic_env.
Defined.

Definition annot_extract_template_env_sig
           (params : extract_template_env_params)
           (Σ : Ast.global_env)
           (include : KernameSet.t)
           (ignore : kername -> bool) : option (∑ Σ, env_annots box_type Σ).
Proof.
  pose proof (annot_extract_template_env params Σ include ignore).
  destruct extract_template_env; [|exact None].
  exact (Some (t; X)).
Defined.
