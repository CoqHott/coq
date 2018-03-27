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
open Pre_env
open Nativeinstr

(** This file defines the lambda code generation phase of the native compiler *)
type 'e evars =
    { evars_val : 'e existential_g -> 'e constr_g option;
      evars_typ : 'e existential_g -> 'e types_g;
      evars_metas : metavariable -> 'e types_g }

val empty_evars : 'e evars

val decompose_Llam : lambda -> Name.t array * lambda
val decompose_Llam_Llet : lambda -> (Name.t * lambda option) array * lambda

val is_lazy : prefix -> constr -> bool
val mk_lazy : lambda -> lambda

val get_mind_prefix : 'e env -> MutInd.t -> string

val get_alias : 'e env -> pconstant -> pconstant

val lambda_of_constr : ('e Evkey.t as 'e) env -> 'e evars -> 'e Constr.constr_g -> lambda

val compile_static_int31 : bool -> Constr.constr array -> lambda

val compile_dynamic_int31 : bool -> prefix -> constructor -> lambda array ->
			    lambda

val before_match_int31 : inductive -> bool -> prefix -> constructor -> lambda ->
			 lambda

val compile_prim : CPrimitives.t -> Constant.t -> bool -> prefix -> lambda array ->
		   lambda
