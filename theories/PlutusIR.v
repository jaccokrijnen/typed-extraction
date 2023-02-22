Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Bool.BoolEq.
Require Import Ascii.
Require Import Eqdep.

From MetaCoq.TypedExtraction Require Import Util.
From MetaCoq.TypedExtraction Require Import Utils.
(* To use bytestring.string *)
From MetaCoq.Template Require Import MCUtils.

Require Import Coq.Program.Basics.

Import ListNotations.



(*
  Simplification of the names in the AST

  In the AST that we dump in the plutus compiler, variables are represented with the Name type, which is
  a pair of String and Int, where the Int (newtyped as Unique) is used as a compiler detail for cheap name
  comparisons (see Language.PlutusCore.Name.

  We ignore these details and treat names (both terms and types) as strings. The definitions
  below have the same types as the original AST constructors, but forget the structure and
  map to a string.

  This simplifies the representation and especially recognizing equal subterms (since
  compiler passes may reassign unique numbers).

  Possible future approach: it is preferable to have to complete AST including e.g.
  Uniques, but prove that they do not matter for evaluation and then remove them from
  AST

*)

(** Recursivity and strictness *)
Inductive Recursivity := NonRec | Rec.

Inductive Strictness := NonStrict | Strict.

(** Universes *)
Inductive DefaultUni : Type :=
    | DefaultUniInteger    (* : DefaultUni Z (* Integer *) *)
    | DefaultUniByteString (* : DefaultUni string (* BS.ByteString *)*)
    | DefaultUniString     (* : DefaultUni string (* String *)*)
    | DefaultUniChar       (* : DefaultUni ascii (* Char *)*)
    | DefaultUniUnit       (* : DefaultUni unit (* () *)*)
    | DefaultUniBool       (* : DefaultUni bool (* Bool *)*)
    .

(** Existentials as a datype *)
Inductive some {f : DefaultUni -> Type} :=
  Some : forall {u : DefaultUni}, f u -> some.
Arguments some _ : clear implicits.

(** Builtin types *)
Inductive typeIn (u : DefaultUni) :=
  TypeIn : typeIn u.
Arguments typeIn _ : clear implicits.

(** Constants *)
Definition unitype (x : DefaultUni) : Type :=
  match x with
    | DefaultUniInteger    => Z
    | DefaultUniByteString => string
    | DefaultUniString     => string
    | DefaultUniChar       => ascii
    | DefaultUniUnit       => unit
    | DefaultUniBool       => bool
  end.

Inductive valueOf (u : DefaultUni) :=
  ValueOf : unitype u -> valueOf u.
Arguments ValueOf _ _ : clear implicits.

(** Built-in functions*)
Inductive DefaultFun :=
    | AddInteger
    | SubtractInteger
    | MultiplyInteger
    | DivideInteger
    | QuotientInteger
    | RemainderInteger
    | ModInteger
    | LessThanInteger
    | LessThanEqInteger
    | GreaterThanInteger
    | GreaterThanEqInteger
    | EqInteger
    | Concatenate
    | TakeByteString
    | DropByteString
    | SHA2
    | SHA3
    | VerifySignature
    | EqByteString
    | LtByteString
    | GtByteString
    | IfThenElse
    | CharToString
    | Append
    | Trace.



Section AST_term.

  (** kinds *)
  Inductive kind :=
    | kind_Base : kind
    | kind_Arrow : kind -> kind -> kind.

  (** types *)
  Inductive ty :=
    | ty_Var : string -> ty
    | ty_Fun : ty -> ty -> ty
    | ty_IFix : ty -> ty -> ty
    | ty_Forall : string -> kind -> ty -> ty
    | ty_Builtin : @some typeIn -> ty
    | ty_Lam : string -> kind -> ty -> ty
    | ty_App : ty -> ty -> ty.

  (*
    Simplification of attached values in the AST

    In the Haskell AST, term is a functor and each constructor may have a field of the type parameter
    `a`. Since this seems to be used only for storing intermediate compiler data, it is ignored here.
    (this works because the dumping code is ignoring it)
  *)

  (** Declarations *)
  Inductive vdecl := VarDecl : string -> ty -> vdecl.
  Record tvdecl := tyVarDecl
    { tvd_name : string
    ; tvd_kind : kind
    }.

  (* Constructor string and arity, needed for Scott encoding *)
  Inductive constr := Constructor : vdecl -> nat -> constr.
  Inductive dtdecl := Datatype : tvdecl -> list tvdecl -> string -> list constr -> dtdecl.

  (** terms and bindings *)
  Inductive term :=
    | Let      : Recursivity -> list binding -> term -> term
    | Var      : string -> term
    | TyAbs    : string -> kind -> term -> term
    | LamAbs   : string -> ty -> term -> term
    | Apply    : term -> term -> term
    | Constant : @some valueOf -> term
    | Builtin  : DefaultFun -> term
    | TyInst   : term -> ty -> term
    | Error    : ty -> term
    | IWrap    : ty -> ty -> term -> term
    | Unwrap   : term -> term

  with binding :=
    | TermBind : Strictness -> vdecl -> term -> binding
    | typeBind : tvdecl -> ty -> binding
    | DatatypeBind : dtdecl -> binding
  .

  (* Similar to mkLet in Plutus: for an empty list of bindings it is the identity, otherwise
     it constructs a let with a non-empty list of bindings *)
  Definition mk_let (r : Recursivity) (bs : list binding) (t : term) : term :=
    match bs with
      | [] => t
      | _  => Let r bs t
    end
.

  (** ** Trace of compilation *)
  Inductive pass :=
    | PassRestring
    | PasstypeCheck
    | PassInline : list string -> pass
    | PassDeadCode
    | PassThunkRec
    | PassFloatterm
    | PassLetNonStrict
    | PassLettypes
    | PassLetRec
    | PassLetNonRec.

  Inductive compilation_trace :=
    | CompilationTrace : term -> list (pass * term) -> compilation_trace.

  Definition constructorstring :=
    fun c => match c with
    | Constructor (VarDecl n _) _ => n
    end
    .

End AST_term.


Section term_rect.

  Unset Implicit Arguments.

  Variable (P : term -> Type).
  Variable (Q : binding -> Type).

  Context
    (H_Let      : forall rec bs t, ForallT Q bs -> P t -> P (Let rec bs t))
    (H_Var      : forall s : string, P (Var s))
    (H_TyAbs    : forall (s : string) (k : kind) (t : term), P t -> P (TyAbs s k t))
    (H_LamAbs   : forall (s : string) (t : ty) (t0 : term), P t0 -> P (LamAbs s t t0))
    (H_Apply    : forall t : term, P t -> forall t0 : term, P t0 -> P (Apply t t0))
    (H_Constant : forall s : some valueOf, P (Constant s))
    (H_Builtin  : forall d : DefaultFun, P (Builtin d))
    (H_TyInst   : forall t : term, P t -> forall t0 : ty, P (TyInst t t0))
    (H_Error    : forall t : ty, P (Error t))
    (H_IWrap    : forall (t t0 : ty) (t1 : term), P t1 -> P (IWrap t t0 t1))
    (H_Unwrap   : forall t : term, P t -> P (Unwrap t)).

  Context
    (H_TermBind : forall s v t, P t -> Q (TermBind s v t))
    (H_typeBind : forall v ty, Q (typeBind v ty))
    (H_DatatypeBind : forall dtd, Q (DatatypeBind dtd)).

  Definition bindings_rect' (binding_rect' : forall (b : binding), Q b) :=
    fix bindings_rect' bs :=
    match bs as p return ForallT Q p with
      | nil       => ForallT_nil
      | cons b bs => ForallT_cons (binding_rect' b) (bindings_rect' bs)
    end.

  Fixpoint term_rect' (t : term) : P t :=
    match t with
      | Let rec bs t    => H_Let rec bs t (bindings_rect' binding_rect' bs) (term_rect' t)
      | Var n           => H_Var n
      | TyAbs n k t     => H_TyAbs n k t (term_rect' t)
      | LamAbs n ty t   => H_LamAbs n ty t (term_rect' t)
      | Apply s t       => H_Apply s (term_rect' s) t (term_rect' t)
      | TyInst t ty     => H_TyInst t (term_rect' t) ty
      | IWrap ty1 ty2 t => H_IWrap ty1 ty2 t (term_rect' t)
      | Unwrap t        => H_Unwrap t (term_rect' t)
      | Error ty        => H_Error ty
      | Constant v      => H_Constant v
      | Builtin f       => H_Builtin f
    end
  with binding_rect' (b : binding) : Q b :=
    match b with
      | TermBind s v t  => H_TermBind s v t (term_rect' t)
      | typeBind v ty   => H_typeBind v ty
      | DatatypeBind dtd => H_DatatypeBind dtd
    end.
End term_rect.

Section term__ind.

  Unset Implicit Arguments.

  Variable (P : term -> Prop).
  Variable (Q : binding -> Prop).

  Context
    (H_Let      : forall rec bs t, ForallP Q bs -> P t -> P (Let rec bs t))
    (H_Var      : forall s : string, P (Var s))
    (H_TyAbs    : forall (s : string) (k : kind) (t : term), P t -> P (TyAbs s k t))
    (H_LamAbs   : forall (s : string) (t : ty) (t0 : term), P t0 -> P (LamAbs s t t0))
    (H_Apply    : forall t : term, P t -> forall t0 : term, P t0 -> P (Apply t t0))
    (H_Constant : forall s : some valueOf, P (Constant s))
    (H_Builtin  : forall d : DefaultFun, P (Builtin d))
    (H_TyInst   : forall t : term, P t -> forall t0 : ty, P (TyInst t t0))
    (H_Error    : forall t : ty, P (Error t))
    (H_IWrap    : forall (t t0 : ty) (t1 : term), P t1 -> P (IWrap t t0 t1))
    (H_Unwrap   : forall t : term, P t -> P (Unwrap t)).

  Context
    (H_TermBind : forall s v t, P t -> Q (TermBind s v t))
    (H_typeBind : forall v ty, Q (typeBind v ty))
    (H_DatatypeBind : forall dtd, Q (DatatypeBind dtd)).

  Definition bindings__ind (binding__ind : forall (b : binding), Q b) :=
    fix bindings__ind bs :=
    match bs as p return ForallP Q p with
      | nil       => ForallP_nil
      | cons b bs => ForallP_cons (binding__ind b) (bindings__ind bs)
    end.

  Fixpoint term__ind (t : term) : P t :=
    match t with
      | Let rec bs t    => H_Let rec bs t (bindings__ind binding__ind bs) (term__ind t)
      | Var n           => H_Var n
      | TyAbs n k t     => H_TyAbs n k t (term__ind t)
      | LamAbs n ty t   => H_LamAbs n ty t (term__ind t)
      | Apply s t       => H_Apply s (term__ind s) t (term__ind t)
      | TyInst t ty     => H_TyInst t (term__ind t) ty
      | IWrap ty1 ty2 t => H_IWrap ty1 ty2 t (term__ind t)
      | Unwrap t        => H_Unwrap t (term__ind t)
      | Error ty        => H_Error ty
      | Constant v      => H_Constant v
      | Builtin f       => H_Builtin f
    end
  with binding__ind (b : binding) : Q b :=
    match b with
      | TermBind s v t  => H_TermBind s v t (term__ind t)
      | typeBind v ty   => H_typeBind v ty
      | DatatypeBind dtd => H_DatatypeBind dtd
    end.

  Combined Scheme term__multind from term__ind, binding__ind.

End term__ind.
