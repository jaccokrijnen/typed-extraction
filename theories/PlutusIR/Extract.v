From MetaCoq.Template Require Import BasicAst utils.
From MetaCoq.TypedExtraction Require Import ExAst.
From MetaCoq.TypedExtraction Require Import PlutusIR.
(* PlutusIR Erasure TypeAnnotations.*)
From Coq Require Import Datatypes.
From Coq Require Import Lists.List.

Definition lift_a2 {A B C} : (A -> B -> C) -> option A -> option B -> option C :=
  fun f x y => match x, y with
  | Some v, Some w => Some (f v w)
  | _, _ => None
  end.

Definition zip_with {A B C} (f : A -> B -> C) := 
fix zip_with (l : list A) (l' : list B) {struct l} : list C :=
  match l with
  | [] => []
  | x :: tl =>
      match l' with
      | [] => []
      | y :: tl' => f x y :: zip_with tl tl'
      end
  end.

(* TODO: generate actual fresh identifiers *)
Definition print_name (n : name) : string :=
  match n with
  | nNamed s => s
  | nAnon    => "_"
  end.

Module Types.

  (* type variables *)
  Definition trans (Δ : list tvdecl) : ExAst.box_type -> option PlutusIR.ty :=
    fix trans bt :=
      match bt with
      | TArr τ τ' => lift_a2 ty_Fun (trans τ) (trans τ')
      | TApp τ τ' => lift_a2 ty_App (trans τ) (trans τ')
      | TVar i    => option_map (ty_Var ∘ tvd_name) (nth_error Δ i)
      | TConst s  => Some (ty_Var (string_of_kername s))
      | TInd ind  => Some (ty_Var (string_of_kername (inductive_mind ind)))
      | TBox => Some (ty_Builtin (@PlutusIR.Some typeIn DefaultUniUnit (TypeIn DefaultUniUnit)))
      | TAny => None
      end.

  (* Infer kinds of all free type variables, de Bruijn indexed *)
  Axiom infer_kinds : box_type -> list kind.

  Definition trans_ty_scheme (tyvars : list name) (τ : box_type) : option ty :=
    let Δ : list tvdecl := zip_with tyVarDecl (map print_name tyvars) (infer_kinds τ) in
    let add_foralls := fun τ_pir =>
      fold_right (fun tvd σ => ty_Forall (tvd_name tvd) (tvd_kind tvd) σ) τ_pir Δ
    in
    option_map add_foralls (trans Δ τ)
    .
End Types.



(* Some tests *)

From MetaCoq.Template Require Import config Ast.
From MetaCoq.TypedExtraction Require Import TypeAnnotations Erasure.
From MetaCoq.PCUIC Require Import PCUICAst TemplateToPCUIC PCUICTyping.
From MetaCoq.SafeChecker Require Import PCUICWfEnvImpl.

Local Existing Instance fake_guard_impl_instance.
Local Existing Instance extraction_checker_flags.
Definition erase_type_impl (Σ : global_env_ext) (wfextΣ : ∥ wf_ext Σ∥) :=
  @erase_type canonical_abstract_env_impl (ltac:(now unshelve econstructor;eauto)).

Program Definition erase_type_program (p : Ast.Env.program) : global_env_ext * (list name * box_type) :=
  let Σ := trans_global_env p.1 in
  let Σext := empty_ext (PCUICProgram.trans_env_env Σ) in
  (Σext, erase_type_impl Σext _ Σext eq_refl (trans Σ p.2) _).
Next Obligation. Admitted.
Next Obligation. Admitted.

MetaCoq Quote Recursively Definition ex1 := (forall A, A -> A).
Eval cbv in snd (erase_type_program ex1).
Eval cbv in Types.trans
  [tyVarDecl "A" kind_Base]
  (TArr TBox (TArr (TVar 0) (TVar 0))).

MetaCoq Quote Recursively Definition ex2:= (bool * bool -> bool).
Definition ex2_erased_ty := snd (snd (erase_type_program ex2)).
Eval cbv in Types.trans [] ex2_erased_ty.


From MetaCoq.Erasure Require Import EAst.
From MetaCoq.TypedExtraction Require Import Annotations.

Module Terms.

  Context (Δ : list tvdecl).
  Fixpoint trans_mono
    (Γ : list name) (* term vars *)
    (t : term) : annots box_type t -> option PlutusIR.term :=
    match t with

    | tRel i => fun bt =>
        Some (Var (print_name (nth i Γ nAnon)))

    | tLambda na body => fun '(bt, a) =>
        lift_a2 (LamAbs (print_name na)) (Types.trans Δ bt) (trans_mono (na :: Γ) body a)

    | tApp hd arg => fun '(bt, (hda, arga)) =>
        lift_a2 Apply (trans_mono Γ hd hda) (trans_mono Γ arg arga)

    | _ => fun _ => None

    end.

  Definition trans
    (t : EAst.term) (ann : annots box_type t) : option PlutusIR.term :=
    let add_ty_abs := fun '(tyVarDecl v k) τ => TyAbs v k τ in
    match trans_mono [] t ann with
      | Some τ => Some (fold_right add_ty_abs τ Δ)
      | None => None
    end
  .

End Terms.

Module Inductives.

End Inductives.

From MetaCoq.TypedExtraction Require Import Optimize.
From MetaCoq.TypedExtraction Require Import Extraction.
From MetaCoq.TypedExtraction Require Import ExAst.
From MetaCoq.Template Require Import Ast.

From MetaCoq.TypedExtraction Require Import ResultMonad.
Import MCMonadNotation.


(*
   Needed for appropriate type inference of Monad below
*)
Definition result_bytestring_err A := result A bytestring.String.t.

Definition to_lam_box (p : program) : result_bytestring_err _ :=
  kn <- match p.2 with
           | tConst kn _ => Ok kn
           | tInd ind _ => Ok (inductive_mind ind)
           | _ => Err ("Expected program to be a tConst or tInd")
           end;;

  Σ <- extract_template_env_within_coq
         p.1
         (KernameSet.singleton kn)
         (fun k => false) ;;

  ret Σ.

From MetaCoq Require utils.

Definition id (A : Set) (x : A) : A := x.

MetaCoq Quote Recursively Definition t_id := id.
Eval cbv in to_lam_box t_id.

Definition to_lam_box_T (p : program) : result_bytestring_err (∑ Σ : ExAst.global_env, env_annots box_type Σ) :=
  kn <- match p.2 with
           | tConst kn _ => Ok kn
           | tInd ind _ => Ok (inductive_mind ind)
           | _ => Err ("Expected program to be a tConst or tInd")
           end;;

  match annot_extract_template_env_within_coq_sig
         p.1
         (KernameSet.singleton kn)
         (fun k => false)
  with
  | None => Err "annot_extract_template_env_within_coq failed"
  | Some (Σ ; env_anns) => Ok (Σ; env_anns)
  end.

Eval cbv in to_lam_box_T t_id.
