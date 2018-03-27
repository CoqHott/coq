(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file defines the most important datatype of Coq, namely kernel terms,
    as well as a handful of generic manipulation functions. *)

open Names

(** {6 Value under universe substitution } *)
type 'a puniverses = 'a Univ.puniverses
[@@ocaml.deprecated "use Univ.puniverses"]

(** {6 Simply type aliases } *)
type pconstant = Constant.t Univ.puniverses
type pinductive = inductive Univ.puniverses
type pconstructor = constructor Univ.puniverses

(** {6 Existential variables } *)
type existential_key = Evar.t
[@@ocaml.deprecated "use Evar.t"]

(** {6 Existential variables } *)
type metavariable = int

(** {6 Case annotation } *)
type case_style = LetStyle | IfStyle | LetPatternStyle | MatchStyle
  | RegularStyle (** infer printing form from number of constructor *)
type case_printing =
  { ind_tags : bool list; (** tell whether letin or lambda in the arity of the inductive type *)
    cstr_tags : bool list array; (** tell whether letin or lambda in the signature of each constructor *)
    style     : case_style }

(* INVARIANT:
 * - Array.length ci_cstr_ndecls = Array.length ci_cstr_nargs
 * - forall (i : 0 .. pred (Array.length ci_cstr_ndecls)),
 *          ci_cstr_ndecls.(i) >= ci_cstr_nargs.(i)
 *)
type case_info =
  { ci_ind        : inductive;      (* inductive type to which belongs the value that is being matched *)
    ci_npar       : int;            (* number of parameters of the above inductive type *)
    ci_cstr_ndecls : int array;     (* For each constructor, the corresponding integer determines
                                       the number of values that can be bound in a match-construct.
                                       NOTE: parameters of the inductive type are therefore excluded from the count *)
    ci_cstr_nargs : int array;      (* for each constructor, the corresponding integers determines
                                       the number of values that can be applied to the constructor,
                                       in addition to the parameters of the related inductive type
                                       NOTE: "lets" are therefore excluded from the count
                                       NOTE: parameters of the inductive type are also excluded from the count *)
    ci_pp_info    : case_printing   (* not interpreted by the kernel *)
  }

type ground = [ `NO of Util.Empty.t ]
type evars = [ ground | `Evar of Evar.t ]

module Evkey : sig
  type 'e t = [< evars > `NO ] as 'e

  val evar : 'e t -> Evar.t
  val equal : 'e t -> 'e t -> bool
  val compare : 'e t -> 'e t -> int
  val hash : 'e t -> int
  val make : Evar.t -> evars
end

(** {6 The type of constructions } *)

type +'e constr_g
type +'e types_g = 'e constr_g

type t = ground constr_g
type constr = t
(** [types] is the same as [constr] but is intended to be used for
   documentation to indicate that such or such function specifically works
   with {e types} (i.e. terms of type a sort).
   (Rem:plurial form since [type] is a reserved ML keyword) *)

type types = constr

(** {5 Functions for dealing with constr terms. }
  The following functions are intended to simplify and to uniform the
  manipulation of terms. Some of these functions may be overlapped with
  previous ones. *)

(** {6 Term constructors. } *)

(** Constructs a de Bruijn index (DB indices begin at 1) *)
val mkRel : int -> 'e constr_g

(** Constructs a Variable *)
val mkVar : Id.t -> 'e constr_g

(** Constructs an patvar named "?n" *)
val mkMeta : metavariable -> 'e constr_g (* TODO restrict type? *)

(** Constructs an existential variable *)
type ('e,'constr) pexistential = 'e * 'constr array
type 'e existential_g = ('e, 'e constr_g) pexistential
val mkEvar : 'e existential_g -> 'e constr_g

(** Construct a sort *)
val mkSort : Sorts.t -> 'e types_g
val mkProp : 'e types_g
val mkSet  : 'e types_g
val mkType : Univ.Universe.t -> 'e types_g


(** This defines the strategy to use for verifiying a Cast *)
type cast_kind = VMcast | NATIVEcast | DEFAULTcast | REVERTcast

(** Constructs the term [t1::t2], i.e. the term t{_ 1} casted with the
   type t{_ 2} (that means t2 is declared as the type of t1). *)
val mkCast : 'e constr_g * cast_kind * 'e constr_g -> 'e constr_g

(** Constructs the product [(x:t1)t2] *)
val mkProd : Name.t * 'e types_g * 'e types_g -> 'e types_g

(** Constructs the abstraction \[x:t{_ 1}\]t{_ 2} *)
val mkLambda : Name.t * 'e types_g * 'e constr_g -> 'e constr_g

(** Constructs the product [let x = t1 : t2 in t3] *)
val mkLetIn : Name.t * 'e constr_g * 'e types_g * 'e constr_g -> 'e constr_g

(** [mkApp (f, [|t1; ...; tN|]] constructs the application
    {%html:(f t<sub>1</sub> ... t<sub>n</sub>)%}
    {%latex:$(f~t_1\dots f_n)$%}. *)
val mkApp : 'e constr_g * 'e constr_g array -> 'e constr_g

val map_puniverses : ('a -> 'b) -> 'a Univ.puniverses -> 'b Univ.puniverses

(** Constructs a Constant.t *)
val mkConst : Constant.t -> 'e constr_g
val mkConstU : pconstant -> 'e constr_g

(** Constructs a projection application *)
val mkProj : (Projection.t * 'e constr_g) -> 'e constr_g

(** Inductive types *)

(** Constructs the ith (co)inductive type of the block named kn *)
val mkInd : inductive -> 'e constr_g
val mkIndU : pinductive -> 'e constr_g

(** Constructs the jth constructor of the ith (co)inductive type of the
   block named kn. *)
val mkConstruct : constructor -> 'e constr_g
val mkConstructU : pconstructor -> 'e constr_g
val mkConstructUi : pinductive * int -> 'e constr_g

(** Constructs a destructor of inductive type.
    
    [mkCase ci p c ac] stand for match [c] as [x] in [I args] return [p] with [ac] 
    presented as describe in [ci].

    [p] stucture is [fun args x -> "return clause"]

    [ac]{^ ith} element is ith constructor case presented as 
    {e lambda construct_args (without params). case_term } *)
val mkCase : case_info * 'e constr_g * 'e constr_g * 'e constr_g array -> 'e constr_g

(** If [recindxs = [|i1,...in|]]
      [funnames = [|f1,.....fn|]]
      [typarray = [|t1,...tn|]]
      [bodies   = [|b1,.....bn|]]
   then [mkFix ((recindxs,i), funnames, typarray, bodies) ]
   constructs the {% $ %}i{% $ %}th function of the block (counting from 0)

    [Fixpoint f1 [ctx1] = b1
     with     f2 [ctx2] = b2
     ...
     with     fn [ctxn] = bn.]

   where the length of the {% $ %}j{% $ %}th context is {% $ %}ij{% $ %}.
*)
type 'e rec_declaration_g = Name.t array * 'e types_g array * 'e constr_g array
type 'e fixpoint_g = (int array * int) * 'e rec_declaration_g
type rec_declaration = ground rec_declaration_g
type fixpoint = ground fixpoint_g
val mkFix : 'e fixpoint_g -> 'e constr_g

(** If [funnames = [|f1,.....fn|]]
      [typarray = [|t1,...tn|]]
      [bodies   = [b1,.....bn]] 
   then [mkCoFix (i, (funnames, typarray, bodies))]
   constructs the ith function of the block
   
    [CoFixpoint f1 = b1
     with       f2 = b2
     ...
     with       fn = bn.]
 *)
type 'e cofixpoint_g = int * 'e rec_declaration_g
type cofixpoint = ground cofixpoint_g
val mkCoFix : 'e cofixpoint_g -> 'e constr_g


(** {6 Concrete type for making pattern-matching. } *)

(** [constr array] is an instance matching definitional [named_context] in
   the same order (i.e. last argument first) *)
type ('constr, 'types) prec_declaration =
    Name.t array * 'types array * 'constr array
type ('constr, 'types) pfixpoint =
    (int array * int) * ('constr, 'types) prec_declaration
type ('constr, 'types) pcofixpoint =
    int * ('constr, 'types) prec_declaration

type ('e,'constr, 'types, 'sort, 'univs) kind_of_term =
  | Rel       of int                                  (** Gallina-variable introduced by [forall], [fun], [let-in], [fix], or [cofix]. *)

  | Var       of Id.t                                 (** Gallina-variable that was introduced by Vernacular-command that extends
                                                          the local context of the currently open section
                                                          (i.e. [Variable] or [Let]). *)

  | Meta      of metavariable
  | Evar      of ('e,'constr) pexistential
  | Sort      of 'sort
  | Cast      of 'constr * cast_kind * 'types
  | Prod      of Name.t * 'types * 'types             (** Concrete syntax ["forall A:B,C"] is represented as [Prod (A,B,C)]. *)
  | Lambda    of Name.t * 'types * 'constr            (** Concrete syntax ["fun A:B => C"] is represented as [Lambda (A,B,C)].  *)
  | LetIn     of Name.t * 'constr * 'types * 'constr  (** Concrete syntax ["let A:C := B in D"] is represented as [LetIn (A,B,C,D)]. *)
  | App       of 'constr * 'constr array              (** Concrete syntax ["(F P1 P2 ...  Pn)"] is represented as [App (F, [|P1; P2; ...; Pn|])].

                                                          The {!mkApp} constructor also enforces the following invariant:
                                                          - [F] itself is not {!App}
                                                          - and [[|P1;..;Pn|]] is not empty. *)

  | Const     of (Constant.t * 'univs)                  (** Gallina-variable that was introduced by Vernacular-command that extends the global environment
                                                          (i.e. [Parameter], or [Axiom], or [Definition], or [Theorem] etc.) *)

  | Ind       of (inductive * 'univs)                 (** A name of an inductive type defined by [Variant], [Inductive] or [Record] Vernacular-commands. *)
  | Construct of (constructor * 'univs)              (** A constructor of an inductive type defined by [Variant], [Inductive] or [Record] Vernacular-commands. *)
  | Case      of case_info * 'constr * 'constr * 'constr array
  | Fix       of ('constr, 'types) pfixpoint
  | CoFix     of ('constr, 'types) pcofixpoint
  | Proj      of Projection.t * 'constr

(** User view of [constr]. For [App], it is ensured there is at
   least one argument and the function is not itself an applicative
   term *)

type 'e kind_g = ('e, 'e constr_g, 'e types_g, Sorts.t, Univ.Instance.t) kind_of_term

(** Sensitive to instantiated evars! *)
val kind_g : 'e Evkey.t constr_g -> 'e kind_g

val kind : constr -> ground kind_g
val of_kind : 'e kind_g -> 'e constr_g

(** {6 Simple case analysis} *)
val isRel  : constr -> bool
val isRelN : int -> constr -> bool
val isVar  : constr -> bool
val isVarId : Id.t -> constr -> bool
val isVarId_g : Id.t -> 'e Evkey.t constr_g -> bool
val isInd  : constr -> bool
val isEvar : 'e Evkey.t constr_g -> bool (* _g?? *)
val isMeta : constr -> bool
val isEvar_or_Meta : 'e Evkey.t constr_g -> bool
val isSort : constr -> bool
val isCast : constr -> bool
val isApp : constr -> bool
val isLambda : constr -> bool
val isLetIn : constr -> bool
val isProd : constr -> bool
val isConst : constr -> bool
val isConstruct : constr -> bool
val isFix : constr -> bool
val isCoFix : constr -> bool
val isCase : constr -> bool
val isProj : constr -> bool

val is_Prop : constr -> bool
val is_Set  : constr -> bool
val isprop : constr -> bool
val is_Type : constr -> bool
val iskind : constr -> bool
val is_small : Sorts.t -> bool

(** {6 Term destructors } *)
(** Destructor operations are partial functions and
    @raise DestKO if the term has not the expected form. *)

exception DestKO

(** Destructs a de Bruijn index *)
val destRel : constr -> int

(** Destructs an existential variable *)
val destMeta : constr -> metavariable

(** Destructs a variable *)
val destVar : constr -> Id.t

(** Destructs a sort. [is_Prop] recognizes the sort {% \textsf{%}Prop{% }%}, whether
   [isprop] recognizes both {% \textsf{%}Prop{% }%} and {% \textsf{%}Set{% }%}. *)
val destSort : constr -> Sorts.t

(** Destructs a casted term *)
val destCast : constr -> constr * cast_kind * constr

(** Destructs the product {% $ %}(x:t_1)t_2{% $ %} *)
val destProd : types -> Name.t * types * types

(** Destructs the abstraction {% $ %}[x:t_1]t_2{% $ %} *)
val destLambda : constr -> Name.t * types * constr

(** Destructs the let {% $ %}[x:=b:t_1]t_2{% $ %} *)
val destLetIn : constr -> Name.t * constr * types * constr

(** Destructs an application *)
val destApp : constr -> constr * constr array

(** Decompose any term as an applicative term; the list of args can be empty *)
val decompose_app : constr -> constr * constr list
val decompose_app_g : 'e Evkey.t constr_g -> 'e constr_g * 'e constr_g list

(** Same as [decompose_app], but returns an array. *)
val decompose_appvect : constr -> constr * constr array

(** Destructs a constant *)
val destConst : constr -> Constant.t Univ.puniverses

(** Destructs a (co)inductive type *)
val destInd : constr -> inductive Univ.puniverses

(** Destructs a constructor *)
val destConstruct : constr -> constructor Univ.puniverses

(** Destructs a [match c as x in I args return P with ... |
Ci(...yij...) => ti | ... end] (or [let (..y1i..) := c as x in I args
return P in t1], or [if c then t1 else t2])
@return [(info,c,fun args x => P,[|...|fun yij => ti| ...|])]
where [info] is pretty-printing information *)
val destCase : constr -> case_info * constr * constr * constr array

(** Destructs a projection *)
val destProj : constr -> Projection.t * constr

val destEvar : 'e Evkey.t constr_g -> ('e, 'e constr_g) pexistential

(** Destructs the {% $ %}i{% $ %}th function of the block
   [Fixpoint f{_ 1} ctx{_ 1} = b{_ 1}
    with    f{_ 2} ctx{_ 2} = b{_ 2}
    ...
    with    f{_ n} ctx{_ n} = b{_ n}],
   where the length of the {% $ %}j{% $ %}th context is {% $ %}ij{% $ %}.
*)
val destFix : constr -> fixpoint

val destCoFix : constr -> cofixpoint

(** {6 Equality} *)

(** [equal a b] is true if [a] equals [b] modulo alpha, casts,
   and application grouping *)
val equal : constr -> constr -> bool

(** [eq_constr_univs u a b] is [true] if [a] equals [b] modulo alpha, casts,
   application grouping and the universe equalities in [u]. *)
val eq_constr_univs : constr UGraph.check_function
val eq_constr_univs_g : 'e Evkey.t constr_g UGraph.check_function

(** [leq_constr_univs u a b] is [true] if [a] is convertible to [b] modulo 
    alpha, casts, application grouping and the universe inequalities in [u]. *)
val leq_constr_univs : constr UGraph.check_function
val leq_constr_univs_g : 'e Evkey.t constr_g UGraph.check_function

(** [eq_constr_univs u a b] is [true] if [a] equals [b] modulo alpha, casts,
   application grouping and the universe equalities in [u]. *)
val eq_constr_univs_infer : UGraph.t -> constr -> constr -> bool Univ.constrained
val eq_constr_univs_infer_g : UGraph.t -> ('e Evkey.t as 'e) constr_g -> 'e constr_g -> bool Univ.constrained

(** [leq_constr_univs u a b] is [true] if [a] is convertible to [b] modulo 
    alpha, casts, application grouping and the universe inequalities in [u]. *)
val leq_constr_univs_infer : UGraph.t -> constr -> constr -> bool Univ.constrained
val leq_constr_univs_infer_g : UGraph.t -> ('e Evkey.t as 'e) constr_g -> 'e constr_g -> bool Univ.constrained

(** [eq_constr_univs a b] [true, c] if [a] equals [b] modulo alpha, casts,
   application grouping and ignoring universe instances. *)
val eq_constr_nounivs : constr -> constr -> bool

(** Total ordering compatible with [equal] *)
val compare : constr -> constr -> int

(** {6 Functionals working on the immediate subterm of a construction } *)

(** [fold f acc c] folds [f] on the immediate subterms of [c]
   starting from [acc] and proceeding from left to right according to
   the usual representation of the constructions; it is not recursive *)

val fold : ('a -> constr -> 'a) -> 'a -> constr -> 'a

(* Evar sensitive! *)
val fold_g : ('a -> 'e constr_g -> 'a) -> 'a -> 'e constr_g -> 'a

(** [map f c] maps [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

val map : (constr -> constr) -> constr -> constr
val map_g : ('e constr_g -> 'e constr_g) -> 'e constr_g -> 'e constr_g

(** Like {!map}, but also has an additional accumulator. *)

val fold_map : ('a -> constr -> 'a * constr) -> 'a -> constr -> 'a * constr

(** [map_with_binders g f n c] maps [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

val map_with_binders :
  ('a -> 'a) -> ('a -> constr -> constr) -> 'a -> constr -> constr

val map_with_binders_g :
  ('a -> 'a) -> ('a -> 'e constr_g -> 'e constr_g) -> 'a -> 'e constr_g -> 'e constr_g

(** [iter f c] iters [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

val iter : (constr -> unit) -> constr -> unit

(** [iter_with_binders g f n c] iters [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

val iter_with_binders :
  ('a -> 'a) -> ('a -> constr -> unit) -> 'a -> constr -> unit
val iter_with_binders_g :
  ('a -> 'a) -> ('a -> 'e Evkey.t constr_g -> unit) -> 'a -> 'e constr_g -> unit

type 'e constr_compare_fn = int -> 'e constr_g -> 'e constr_g -> bool

(** [compare_head f c1 c2] compare [c1] and [c2] using [f] to compare
   the immediate subterms of [c1] of [c2] if needed; Cast's, binders
   name and Cases annotations are not taken into account *)

val compare_head : ground constr_compare_fn -> ground constr_compare_fn

(** Convert a global reference applied to 2 instances. The int says
   how many arguments are given (as we can only use cumulativity for
   fully applied inductives/constructors) .*)
type instance_compare_fn = global_reference -> int ->
  Univ.Instance.t -> Univ.Instance.t -> bool

(** [compare_head_gen u s f c1 c2] compare [c1] and [c2] using [f] to
   compare the immediate subterms of [c1] of [c2] if needed, [u] to
   compare universe instances, [s] to compare sorts; Cast's, binders
   name and Cases annotations are not taken into account *)

val compare_head_gen : instance_compare_fn ->
  (Sorts.t -> Sorts.t -> bool) ->
  ground constr_compare_fn ->
  ground constr_compare_fn

val compare_head_gen_leq_with :
  (('e Evkey.t as 'e) constr_g -> ('e, 'e constr_g, 'e types_g, Sorts.t, Univ.Instance.t) kind_of_term) ->
  ('e constr_g -> ('e, 'e constr_g, 'e types_g, Sorts.t, Univ.Instance.t) kind_of_term) ->
  instance_compare_fn ->
  (Sorts.t -> Sorts.t -> bool) ->
  'e constr_compare_fn ->
  'e constr_compare_fn ->
  'e constr_compare_fn

(** [compare_head_gen_with k1 k2 u s f c1 c2] compares [c1] and [c2]
    like [compare_head_gen u s f c1 c2], except that [k1] (resp. [k2])
    is used,rather than {!kind}, to expose the immediate subterms of
    [c1] (resp. [c2]). *)
val compare_head_gen_with :
  (('e Evkey.t as 'e) constr_g -> ('e, 'e constr_g, 'e types_g, Sorts.t, Univ.Instance.t) kind_of_term) ->
  ('e constr_g -> ('e, 'e constr_g, 'e types_g, Sorts.t, Univ.Instance.t) kind_of_term) ->
  instance_compare_fn ->
  (Sorts.t -> Sorts.t -> bool) ->
  'e constr_compare_fn ->
  'e constr_compare_fn

(** [compare_head_gen_leq u s f fle c1 c2] compare [c1] and [c2] using
    [f] to compare the immediate subterms of [c1] of [c2] for
    conversion, [fle] for cumulativity, [u] to compare universe
    instances (the first boolean tells if they belong to a Constant.t),
    [s] to compare sorts for for subtyping; Cast's, binders name and
    Cases annotations are not taken into account *)

val compare_head_gen_leq : instance_compare_fn ->
  (Sorts.t -> Sorts.t -> bool) ->
  ground constr_compare_fn ->
  ground constr_compare_fn ->
  ground constr_compare_fn

exception NotGround
val force_ground : ?unsafe:bool -> 'e constr_g -> constr

val to_econstr : constr -> 'e constr_g

(** {6 Hashconsing} *)

val hash : constr -> int
val case_info_hash : case_info -> int

(*********************************************************************)

val hcons : constr -> constr
