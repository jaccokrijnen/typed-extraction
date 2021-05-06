(** * Inlining pass on the Template Coq representation  *)

(** Essentially, just an adaptaion of the inlining pass on the erased representation.
 After the pass is applied we generate proofs that the original and the transformed terms are equal in the theory of Coq. The proofs are just by [eq_refl], since the terms are convertible *)

From Coq Require Import List String Bool Basics.

From ConCert.Extraction Require Import Transform.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import Utils.
From ConCert.Extraction Require Import Certifying.

From MetaCoq.Template Require Import All Kernames.

Import ListNotations.
Import MonadNotation.

Section inlining.
  Context (should_inline : kername -> bool).
  Context (Σ : global_env).

  Fixpoint beta_body (body : term) (args : list term) {struct args} : term :=
    match args with
    | [] => body
    | a :: args =>
      match body with
      | tLambda na _ body => beta_body (body{0 := a}) args
      | _ => mkApps body (a :: args)
      end
    end.

  Definition iota_body (body : term) : term :=
    match body with
    | tCase (ind, pars, _) _ discr brs =>
      let (hd, args) := decompose_app discr in
      match hd with
      | tConstruct _ c _ =>
        match nth_error brs c with
        | Some (_, br) => beta_body br (skipn pars args)
        | None => body
        end
      | _ => body
      end
    | t => t
    end.

  Definition inline_const (kn : kername) (u : Instance.t) (args : list term) : term :=
    let const := tConst kn u in
    match lookup_env Σ kn with
    | Some (ConstantDecl cst) =>
      match cst_body cst with
      | Some body (* once told me *) =>
        (* Often the first beta will expose an iota (record projection),
               and the projected field is often a function, so we do another beta *)
              let (hd, args) := decompose_app (beta_body body args) in
              beta_body (iota_body hd) args
      | None => tApp const args
      end
    | _ => tApp const args
    end.

  Definition map_subterms (f : term -> term) (t : term) : term :=
  match t with
  | tEvar n ts => tEvar n (map f ts)
  | tCast t kind ty => tCast (f t) kind (f ty)
  | tProd na ty body => tProd na (f ty) (f body)
  | tLambda na ty body => tLambda na (f ty) (f body)
  | tLetIn na val ty body => tLetIn na (f val) (f ty) (f body)
  | tApp hd arg => tApp (f hd) (map f arg)
  | tCase p ty disc brs =>
    tCase p (f ty) (f disc) (map (on_snd f) brs)
  | tProj p t => tProj p (f t)
  | tFix def i => tFix (map (map_def f f) def) i
  | tCoFix def i => tCoFix (map (map_def f f) def) i
  | t => t
  end.

  Fixpoint inline_aux (args : list term) (t : term) : term :=
    match t with
    | tApp hd args0 => inline_aux (map (inline_aux []) args0 ++ args) hd
    | tCast t0 _ _ => inline_aux args t0
    | tConst kn u =>
      if should_inline kn then
        match lookup_env Σ kn with
        | Some (ConstantDecl cst) =>
          match cst_body cst with
          | Some body (* once told me *) =>
            (* Often the first beta will expose an iota (record projection),
               and the projected field is often a function, so we do another beta *)
            let (hd, args) := decompose_app (beta_body body args) in
            beta_body (iota_body hd) args
          | None => mkApps (tConst kn u) args
          end
        | _ => mkApps (tConst kn u) args
        end
      else
        mkApps (tConst kn u) args
    | t => mkApps (map_subterms (inline_aux []) t) args
    end.

  Definition inline : term -> term := inline_aux [].

  (* Fixpoint inline (t : term) : term := *)
  (*   match t with *)
  (*   | tRel n => t *)
  (*   | tVar id => t *)
  (*   | tEvar ev args => *)
  (*     tEvar ev (map inline args) *)
  (*   | tSort s => t *)
  (*   | tCast t kind ty => tCast (inline t) kind (inline v) *)
  (*   | tProd na ty body => tProd na (inline ty) (inline body) *)
  (*   | tLambda na ty body => tLambda na ty (inline body) *)
  (*   | tLetIn na def def_ty body => tLetIn na (inline def) (inline def_ty) (inline body) *)

  (*   | tApp hd args => *)
  (*     let args := map inline args in *)
  (*     match hd with *)
  (*     | tConst kn u => *)
  (*       if should_inline kn then *)
  (*          inline_const kn u args *)
  (*       else tApp (inline hd) args *)
  (*     | _ => tApp (inline hd) args *)
  (*     end *)
  (*   | tConst kn u => *)
  (*     if should_inline kn then *)
  (*       inline_const kn u [] *)
  (*     else t *)
  (*   | tInd _ _ => t *)
  (*   | tConstruct ind idx u => t *)
  (*   | tCase ind_info type_info discr branches => *)
  (*     tCase ind_info (inline type_info) (inline discr) *)
  (*           (map (on_snd inline) branches) *)
  (*   | tProj prj t0 => tProj prj (inline t0) *)
  (*   | tFix mfix idx => *)
  (*     let mfix' := map (map_def inline inline) mfix in *)
  (*     tFix mfix' idx *)
  (*   | tCoFix mfix idx => *)
  (*     let mfix' := map (map_def inline inline) mfix in *)
  (*     tCoFix mfix' idx *)
  (*   | tInt _ => t *)
  (*   | tFloat _ => t *)
  (*   end. *)

  Definition inline_in_constant_body cst :=
    {| cst_type := cst_type cst;
       cst_universes := cst_universes cst;
       cst_body := option_map inline (cst_body cst) |}.

  Definition inline_in_decl d :=
    match d with
    | ConstantDecl cst => ConstantDecl (inline_in_constant_body cst)
    | _ => d
    end.

End inlining.


Definition inline_in_env (should_inline : kername -> bool) (Σ : global_env) : global_env:=
  let newΣ :=
      fold_right (fun '(kn, decl) Σ => (kn, inline_in_decl should_inline Σ decl) :: Σ) [] Σ in
  filter (fun '(kn, _) => negb (should_inline kn)) newΣ.


Definition inline_global_env_template
           (mpath : modpath)
           (Σ : global_env)
           (should_inline : kername -> bool)
           (seeds : KernameSet.t)
  : TemplateMonad global_env :=
  let suffix := "_after_inlining" in
  Σinlined <- tmEval lazy (inline_in_env should_inline Σ);;
  gen_defs_and_proofs Σ Σinlined mpath suffix seeds;;
  ret Σinlined.

(* Mainly for testing purposes *)
Definition inline_def {A}
           (should_inline : kername -> bool)
           (def : A) : TemplateMonad _ :=
  mpath <- tmCurrentModPath tt;;
  p <- tmQuoteRecTransp def false ;;
  kn <- Common.extract_def_name def ;;
  inline_global_env_template mpath p.1 should_inline (KernameSet.singleton kn).


Definition template_inline (should_inline : kername -> bool): TemplateTransform :=
  fun Σ => Ok (timed "Inlining" (fun _ => inline_in_env should_inline Σ)).

Module Tests.

  (* Inlining into the local *)
  Module Ex1.
    Definition foo : nat -> nat := fun x => x + 1.
    Definition bar : nat -> nat := fun x => foo (x * 2).

    Definition baz : nat -> nat := fun x => foo x + bar x.

    MetaCoq Run (env <- inline_def (fun kn => eq_kername <%% foo %%> kn
                                          ||  eq_kername <%% bar %%> kn)
                                  baz ;;
                 t <- tmEval lazy (map (Basics.compose snd fst) env);;
                 tmPrint t).
  End Ex1.

  (* Inlining into the definition from the standard library *)
  Module Ex2.
    MetaCoq Run (inline_def (fun kn => eq_kername <%% Nat.add %%> kn ) mult).
  End Ex2.

  (* Inlining a function of several arguments  *)
  Module Ex3.

    Definition foo : nat -> nat -> nat -> nat := fun x y z => x + y * z.
    Definition bar : nat -> nat := fun n => foo (n + 1) 1 n.

    Definition baz : nat -> nat := fun z => bar z.
    MetaCoq Run (inline_def (fun kn => eq_kername <%% foo %%> kn ||
                eq_kername <%% bar %%> kn) baz).
  End Ex3.

  (* Records *)
  Module Ex4.

    Set Primitive Projections.
    Record blah :=
      { field1 : nat;
        field2 : nat }.

    Definition set_field1 (b : blah) (n : nat) :=
      {| field1 := n; field2 := b.(field2) |}.

    Definition bar (b : blah ):= set_field1 b 0.

    MetaCoq Run (inline_def (fun kn => eq_kername <%% set_field1 %%> kn) bar).
  End Ex4.

  (* Casts *)
  Module Ex5.
    Definition foo : nat -> nat -> nat := fun x y => x + y.
    Definition bar : nat -> nat := fun x => ((foo (x * 2)) : nat -> nat) x.
    MetaCoq Run (inline_def (fun kn => eq_kername <%% foo %%> kn) bar).
  End Ex5.
End Tests.
