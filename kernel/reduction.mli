(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Environ

(***********************************************************************
  s Reduction functions *)

(* None of these functions do eta reduction *)

val whd_betaiotazeta        : ground env -> constr -> constr
val whd_all                 : ground env -> constr -> constr
val whd_allnolet : ground env -> constr -> constr

val whd_betaiota     : ground env -> constr -> constr
val nf_betaiota      : ground env -> constr -> constr

(***********************************************************************
  s conversion functions *)

exception NotConvertible
exception NotConvertibleVect of int

type ('e,'a) kernel_conversion_function = 'e env -> 'a -> 'a -> unit
type ('e,'a) extended_conversion_function =
  ?l2r:bool -> ?reds:Names.transparent_state -> 'e env ->
  ?evars:(('e existential_g -> 'e constr_g option) * UGraph.t) ->
  'a -> 'a -> unit

type conv_pb = CONV | CUMUL

type ('e,'a) universe_compare =
  { (* Might raise NotConvertible *)
    compare_sorts : 'e env -> conv_pb -> Sorts.t -> Sorts.t -> 'a -> 'a;
    compare_instances: flex:bool -> Univ.Instance.t -> Univ.Instance.t -> 'a -> 'a;
    compare_cumul_instances : conv_pb -> Univ.Variance.t array ->
      Univ.Instance.t -> Univ.Instance.t -> 'a -> 'a }

type ('e,'a) universe_state = 'a * ('e,'a) universe_compare

type ('e,'a,'b) generic_conversion_function = 'e env -> ('e,'b) universe_state -> 'a -> 'a -> 'b

type ('e,'a) infer_conversion_function = 'e env -> UGraph.t -> 'a -> 'a -> Univ.Constraint.t

val get_cumulativity_constraints : conv_pb -> Univ.Variance.t array ->
  Univ.Instance.t -> Univ.Instance.t -> Univ.Constraint.t

val inductive_cumulativity_arguments : (Declarations.mutual_inductive_body * int) -> int
val constructor_cumulativity_arguments : (Declarations.mutual_inductive_body * int * int) -> int

val sort_cmp_universes : 'e env -> conv_pb -> Sorts.t -> Sorts.t ->
  'a * ('e,'a) universe_compare -> 'a * ('e,'a) universe_compare

(* [flex] should be true for constants, false for inductive types and
constructors. *)
val convert_instances : flex:bool -> Univ.Instance.t -> Univ.Instance.t ->
  'a * ('e,'a) universe_compare -> 'a * ('e,'a) universe_compare

(** These two never raise UnivInconsistency, inferred_universes
    just gathers the constraints. *)
val checked_universes : ('e,UGraph.t) universe_compare
val inferred_universes : ('e,UGraph.t * Univ.Constraint.t) universe_compare

(** These two functions can only raise NotConvertible *)
val conv : ('e Evkey.t as 'e,'e constr_g) extended_conversion_function

val conv_leq : ('e Evkey.t as 'e,'e types_g) extended_conversion_function

(** These conversion functions are used by module subtyping, which needs to infer
    universe constraints inside the kernel *)
val infer_conv : ?l2r:bool -> ?evars:('e existential_g->'e constr_g option) ->
  ?ts:Names.transparent_state -> ('e Evkey.t as 'e,'e constr_g) infer_conversion_function
val infer_conv_leq : ?l2r:bool -> ?evars:('e existential_g->'e constr_g option) ->
  ?ts:Names.transparent_state -> ('e Evkey.t as 'e,'e types_g) infer_conversion_function

(** Depending on the universe state functions, this might raise
  [UniverseInconsistency] in addition to [NotConvertible] (for better error
  messages). *)
val generic_conv : conv_pb -> l2r:bool -> ('e existential_g->'e constr_g option) ->
  Names.transparent_state -> ('e Evkey.t as 'e,'e constr_g,'a) generic_conversion_function

(** option for conversion *)
type vm_conv_type = { vm_conv : 'e. conv_pb -> ('e Evkey.t as 'e,'e types_g) kernel_conversion_function }
val set_vm_conv : vm_conv_type -> unit
val vm_conv : conv_pb -> ('e Evkey.t as 'e,'e types_g) kernel_conversion_function

val default_conv     : conv_pb -> ?l2r:bool -> ('e Evkey.t as 'e,'e types_g) kernel_conversion_function
val default_conv_leq : ?l2r:bool -> ('e Evkey.t as 'e,'e types_g) kernel_conversion_function

(************************************************************************)

(** Builds an application node, reducing beta redexes it may produce. *)
val beta_applist : constr -> constr list -> constr

(** Builds an application node, reducing beta redexes it may produce. *)
val beta_appvect : constr -> constr array -> constr

(** Builds an application node, reducing beta redexe it may produce. *)
val beta_app : constr -> constr -> constr

(** Pseudo-reduction rule  Prod(x,A,B) a --> B[x\a] *)
val hnf_prod_applist : ground env -> types -> constr list -> types

(** In [hnf_prod_applist_assum n c args], [c] is supposed to (whd-)reduce to
    the form [∀Γ.t] with [Γ] of length [n] and possibly with let-ins; it
    returns [t] with the assumptions of [Γ] instantiated by [args] and
    the local definitions of [Γ] expanded. *)
val hnf_prod_applist_assum : ground env -> int -> types -> constr list -> types

(** Compatibility alias for Term.lambda_appvect_assum *)
val betazeta_appvect : int -> constr -> constr array -> constr

(***********************************************************************
  s Recognizing products and arities modulo reduction *)

val dest_prod       : ground env -> types -> Context.Rel.t * types
val dest_prod_assum : ground env -> types -> Context.Rel.t * types
val dest_lam_assum  : ground env -> types -> Context.Rel.t * types

exception NotArity

val dest_arity : ground env -> types -> Term.arity (* raises NotArity if not an arity *)
val is_arity   : ground env -> types -> bool

val warn_bytecode_compiler_failed : ?loc:Loc.t -> unit -> unit
