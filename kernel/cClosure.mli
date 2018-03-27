(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Environ
open Esubst

(** Flags for profiling reductions. *)
val stats : bool ref
val share : bool ref

val with_stats: 'a Lazy.t -> 'a

(** {6 ... } *)
(** Delta implies all consts (both global (= by
  [kernel_name]) and local (= by [Rel] or [Var])), all evars, and letin's.
  Rem: reduction of a Rel/Var bound to a term is Delta, but reduction of
  a LetIn expression is Letin reduction *)



val all_opaque      : transparent_state
val all_transparent : transparent_state

val is_transparent_variable : transparent_state -> variable -> bool
val is_transparent_constant : transparent_state -> Constant.t -> bool

(** Sets of reduction kinds. *)
module type RedFlagsSig = sig
  type reds
  type red_kind

  (** {7 The different kinds of reduction } *)

  val fBETA : red_kind
  val fDELTA : red_kind
  val fETA : red_kind
  (** The fETA flag is never used by the kernel reduction but pretyping does *)
  val fMATCH : red_kind
  val fFIX : red_kind
  val fCOFIX : red_kind
  val fZETA : red_kind
  val fCONST : Constant.t -> red_kind
  val fVAR : Id.t -> red_kind

  (** No reduction at all *)
  val no_red : reds

  (** Adds a reduction kind to a set *)
  val red_add : reds -> red_kind -> reds

  (** Removes a reduction kind to a set *)
  val red_sub : reds -> red_kind -> reds

  (** Adds a reduction kind to a set *)
  val red_add_transparent : reds -> transparent_state -> reds

  (** Retrieve the transparent state of the reduction flags *)
  val red_transparent : reds -> transparent_state

  (** Build a reduction set from scratch = iter [red_add] on [no_red] *)
  val mkflags : red_kind list -> reds

  (** Tests if a reduction kind is set *)
  val red_set : reds -> red_kind -> bool

  (** This tests if the projection is in unfolded state already or
      is unfodable due to delta. *)
  val red_projection : reds -> Projection.t -> bool
end

module RedFlags : RedFlagsSig
open RedFlags

(* These flags do not contain eta *)
val all               : reds
val allnolet          : reds
val beta              : reds
val betadeltazeta     : reds
val betaiota          : reds
val betaiotazeta      : reds
val betazeta          : reds
val delta             : reds
val zeta              : reds
val nored             : reds


val unfold_side_red : reds
val unfold_red : evaluable_global_reference -> reds

(***********************************************************************)
type table_key = Constant.t Univ.puniverses tableKey

type ('e,'a) infos_cache
type 'a infos_tab
type ('e,'a) infos = {
  i_flags : reds;
  i_cache : ('e,'a) infos_cache }

val ref_value_cache: ('e Evkey.t,'a) infos -> 'a infos_tab -> table_key -> 'a option
val create: (('e,'a) infos -> 'a infos_tab -> 'e constr_g -> 'a) -> reds -> 'e env ->
  ('e existential_g -> 'e constr_g option) -> ('e,'a) infos
val create_tab : unit -> 'a infos_tab
val evar_value : ('e,'a) infos_cache -> 'e existential_g -> 'e constr_g option

val info_env : ('e,'a) infos -> 'e env
val info_flags: ('e,'a) infos -> reds

(***********************************************************************
  s Lazy reduction. *)

(** [fconstr] is the type of frozen constr *)

type 'e fconstr

(** [fconstr] can be accessed by using the function [fterm_of] and by
   matching on type [fterm] *)
type 'e fterm =
  | FRel of int
  | FAtom of 'e constr_g (* Metas and Sorts *)
  | FCast of 'e fconstr * cast_kind * 'e fconstr
  | FFlex of table_key
  | FInd of pinductive
  | FConstruct of pconstructor
  | FApp of 'e fconstr * 'e fconstr array
  | FProj of Projection.t * 'e fconstr
  | FFix of 'e fixpoint_g * 'e fconstr subs
  | FCoFix of 'e cofixpoint_g * 'e fconstr subs
  | FCaseT of case_info * 'e constr_g * 'e fconstr * 'e constr_g array * 'e fconstr subs (* predicate and branches are closures *)
  | FLambda of int * (Name.t * 'e constr_g) list * 'e constr_g * 'e fconstr subs
  | FProd of Name.t * 'e fconstr * 'e fconstr
  | FLetIn of Name.t * 'e fconstr * 'e fconstr * 'e constr_g * 'e fconstr subs
  | FEvar of 'e existential_g * 'e fconstr subs
  | FLIFT of int * 'e fconstr
  | FCLOS of 'e constr_g * 'e fconstr subs
  | FLOCKED

(***********************************************************************
  s A [stack] is a context of arguments, arguments are pushed by
   [append_stack] one array at a time but popped with [decomp_stack]
   one by one *)

type 'e stack_member =
  | Zapp of 'e fconstr array
  | ZcaseT of case_info * 'e constr_g * 'e constr_g array * 'e fconstr subs
  | Zproj of int * int * Constant.t
  | Zfix of 'e fconstr * 'e stack
  | Zshift of int
  | Zupdate of 'e fconstr

and 'e stack = 'e stack_member list

val empty_stack : 'e stack
val append_stack : 'e fconstr array -> 'e stack -> 'e stack

val decomp_stack : 'e stack -> ('e fconstr * 'e stack) option
val array_of_stack : 'e stack -> 'e fconstr array
val stack_assign : 'e stack -> int -> 'e fconstr -> 'e stack
val stack_args_size : 'e stack -> int
val stack_tail : int -> 'e stack -> 'e stack
val stack_nth : 'e stack -> int -> 'e fconstr
val zip_term : ('e Evkey.t fconstr -> 'e constr_g) -> 'e constr_g -> 'e stack -> 'e constr_g
val eta_expand_stack : 'e stack -> 'e stack
val unfold_projection : ('e,'a) infos -> Projection.t -> 'e stack_member option

(** To lazy reduce a constr, create a [clos_infos] with
   [create_clos_infos], inject the term to reduce with [inject]; then use
   a reduction function *)

val inject : 'e Evkey.t constr_g -> 'e fconstr

(** mk_atom: prevents a term from being evaluated *)
val mk_atom : 'e constr_g -> 'e fconstr

(** mk_red: makes a reducible term (used in newring) *)
val mk_red : 'e fterm -> 'e fconstr

val fterm_of : 'e fconstr -> 'e fterm
val term_of_fconstr : 'e Evkey.t fconstr -> 'e constr_g
val destFLambda :
  ('e fconstr subs -> 'e constr_g -> 'e fconstr) -> 'e fconstr -> Name.t * 'e fconstr * 'e fconstr

(** Global and local constant cache *)
type 'e clos_infos = ('e,'e fconstr) infos
val create_clos_infos :
  ?evars:('e Evkey.t existential_g -> 'e constr_g option) -> reds -> 'e env -> 'e clos_infos
val oracle_of_infos : 'e clos_infos -> Conv_oracle.oracle

val env_of_infos : ('e,'a) infos -> 'e env

val infos_with_reds : 'e clos_infos -> reds -> 'e clos_infos

(** Reduction function *)

(** [norm_val] is for strong normalization *)
val norm_val : 'e Evkey.t clos_infos -> 'e fconstr infos_tab -> 'e fconstr -> 'e constr_g

(** [whd_val] is for weak head normalization *)
val whd_val : 'e Evkey.t clos_infos -> 'e fconstr infos_tab ->  'e fconstr -> 'e constr_g

(** [whd_stack] performs weak head normalization in a given stack. It
   stops whenever a reduction is blocked. *)
val whd_stack :
  'e Evkey.t clos_infos -> 'e fconstr infos_tab -> 'e fconstr -> 'e stack -> 'e fconstr * 'e stack

(** [eta_expand_ind_stack env ind c s t] computes stacks correspoding
    to the conversion of the eta expansion of t, considered as an inhabitant
    of ind, and the Constructor c of this inductive type applied to arguments
    s.
    @assumes [t] is a rigid term, and not a constructor. [ind] is the inductive
    of the constructor term [c]
    @raise Not_found if the inductive is not a primitive record, or if the
    constructor is partially applied.
 *)
val eta_expand_ind_stack : 'e env -> inductive -> 'e fconstr -> 'e stack ->
   ('e fconstr * 'e stack) -> 'e stack * 'e stack

(** Conversion auxiliary functions to do step by step normalisation *)

(** [unfold_reference] unfolds references in a [fconstr] *)
val unfold_reference : 'e Evkey.t clos_infos -> 'e fconstr infos_tab -> table_key -> 'e fconstr option

val eq_table_key : table_key -> table_key -> bool

(***********************************************************************
  i This is for lazy debug *)

val lift_fconstr      : int -> 'e fconstr -> 'e fconstr
val lift_fconstr_vect : int -> 'e fconstr array -> 'e fconstr array

val mk_clos      : 'e Evkey.t fconstr subs -> 'e constr_g -> 'e fconstr
val mk_clos_vect : 'e Evkey.t fconstr subs -> 'e constr_g array -> 'e fconstr array
val mk_clos_deep :
  ('e Evkey.t fconstr subs -> 'e constr_g -> 'e fconstr) ->
   'e fconstr subs -> 'e constr_g -> 'e fconstr

val kni: 'e Evkey.t clos_infos -> 'e fconstr infos_tab -> 'e fconstr -> 'e stack -> 'e fconstr * 'e stack
val knr: 'e Evkey.t clos_infos -> 'e fconstr infos_tab -> 'e fconstr -> 'e stack -> 'e fconstr * 'e stack
val kl : 'e Evkey.t clos_infos -> 'e fconstr infos_tab -> 'e fconstr -> 'e constr_g

val to_constr : (lift -> 'e Evkey.t fconstr -> 'e constr_g) -> lift -> 'e fconstr -> 'e constr_g

(** End of cbn debug section i*)
