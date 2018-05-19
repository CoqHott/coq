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
open Declarations
open Environ
open Evd

(** The following three functions are similar to the ones defined in
   Inductive, but they expect an env *)

val type_of_inductive    : ground env -> pinductive -> types

(** Return type as quoted by the user *)
val type_of_constructor  : ground env -> pconstructor -> types
val type_of_constructors : 'e env -> pinductive -> types array

(** Return constructor types in normal form *)
val arities_of_constructors : ground env -> pinductive -> types array

(** An inductive type with its parameters (transparently supports
    reasoning either with only recursively uniform parameters or with all
    parameters including the recursively non-uniform ones *)
type inductive_family
val make_ind_family : inductive Univ.puniverses * evars constr_g list -> inductive_family
val dest_ind_family : inductive_family -> inductive Univ.puniverses * evars constr_g list
val map_ind_family : (evars constr_g -> evars constr_g) -> inductive_family -> inductive_family
val liftn_inductive_family : int -> int -> inductive_family -> inductive_family
val lift_inductive_family  : int -> inductive_family -> inductive_family
val substnl_ind_family :
  evars constr_g list -> int -> inductive_family -> inductive_family

(** An inductive type with its parameters and real arguments *)
type inductive_type = IndType of inductive_family * EConstr.constr list
val make_ind_type : inductive_family * EConstr.constr list -> inductive_type
val dest_ind_type : inductive_type -> inductive_family * EConstr.constr list
val map_inductive_type : (EConstr.constr -> EConstr.constr) -> inductive_type -> inductive_type
val liftn_inductive_type : int -> int -> inductive_type -> inductive_type
val lift_inductive_type  : int -> inductive_type -> inductive_type
val substnl_ind_type : EConstr.constr list -> int -> inductive_type -> inductive_type

val mkAppliedInd : inductive_type -> EConstr.constr
val mis_is_recursive_subset : int list -> wf_paths -> bool
val mis_is_recursive :
  inductive * mutual_inductive_body * one_inductive_body -> bool
val mis_nf_constructor_type :
  pinductive * mutual_inductive_body * one_inductive_body -> int -> constr

(** {6 Extract information from an inductive name} *)

(** @return number of constructors *)
val nconstructors : inductive -> int
val nconstructors_env : 'e env -> inductive -> int

(** @return arity of constructors excluding parameters, excluding local defs *)
val constructors_nrealargs : inductive -> int array
val constructors_nrealargs_env : 'e env -> inductive -> int array

(** @return arity of constructors excluding parameters, including local defs *)
val constructors_nrealdecls : inductive -> int array
val constructors_nrealdecls_env : 'e env -> inductive -> int array

(** @return the arity, excluding params, excluding local defs *)
val inductive_nrealargs : inductive -> int
val inductive_nrealargs_env : 'e env -> inductive -> int

(** @return the arity, excluding params, including local defs *)
val inductive_nrealdecls : inductive -> int
val inductive_nrealdecls_env : 'e env -> inductive -> int

(** @return the arity, including params, excluding local defs *)
val inductive_nallargs : inductive -> int
val inductive_nallargs_env : 'e env -> inductive -> int

(** @return the arity, including params, including local defs *)
val inductive_nalldecls : inductive -> int
val inductive_nalldecls_env : 'e env -> inductive -> int

(** @return nb of params without local defs *)
val inductive_nparams : inductive -> int
val inductive_nparams_env : 'e env -> inductive -> int

(** @return nb of params with local defs *)
val inductive_nparamdecls : inductive -> int
val inductive_nparamdecls_env : 'e env -> inductive -> int

(** @return params context *)
val inductive_paramdecls : pinductive -> Context.Rel.t
val inductive_paramdecls_env : 'e env -> pinductive -> Context.Rel.t

(** @return full arity context, hence with letin *)
val inductive_alldecls : pinductive -> Context.Rel.t
val inductive_alldecls_env : 'e env -> pinductive -> Context.Rel.t

(** {7 Extract information from a constructor name} *)

(** @return param + args without letin *)
val constructor_nallargs : constructor -> int
val constructor_nallargs_env : 'e env -> constructor -> int

(** @return param + args with letin *)
val constructor_nalldecls : constructor -> int
val constructor_nalldecls_env : 'e env -> constructor -> int

(** @return args without letin *)
val constructor_nrealargs : constructor -> int
val constructor_nrealargs_env : 'e env -> constructor -> int

(** @return args with letin *)
val constructor_nrealdecls : constructor -> int
val constructor_nrealdecls_env : 'e env -> constructor -> int

(** Is there local defs in params or args ? *)
val constructor_has_local_defs : constructor -> bool
val inductive_has_local_defs : inductive -> bool

val allowed_sorts : 'e env -> inductive -> Sorts.family list

(** (Co)Inductive records with primitive projections do not have eta-conversion,
    hence no dependent elimination. *)
val has_dependent_elim : mutual_inductive_body -> bool

(** Primitive projections *)
val projection_nparams : Projection.t -> int
val projection_nparams_env : 'e env -> Projection.t -> int
val type_of_projection_knowing_arg : EConstr.env -> evar_map -> Projection.t ->
  EConstr.t -> EConstr.types -> evars types_g


(** Extract information from an inductive family *)

type 'e constructor_summary = {
  cs_cstr : pconstructor;    (* internal name of the constructor plus universes *)
  cs_params : 'e constr_g list;   (* parameters of the constructor in current ctx *)
  cs_nargs : int;            (* length of arguments signature (letin included) *)
  cs_args : 'e Context.Rel.gen;   (* signature of the arguments (letin included) *)
  cs_concl_realargs : 'e constr_g array; (* actual realargs in the concl of cstr *)
}
val lift_constructor : int -> evars constructor_summary -> evars constructor_summary
val get_constructor :
  pinductive * mutual_inductive_body * one_inductive_body * evars constr_g list ->
  int -> evars constructor_summary
val get_constructors : 'e env -> inductive_family -> evars constructor_summary array
val get_projections  : 'e env -> inductive_family -> Constant.t array option

(** [get_arity] returns the arity of the inductive family instantiated
    with the parameters; if recursively non-uniform parameters are not
    part of the inductive family, they appears in the arity *)
val get_arity        : evars env -> inductive_family -> evars Context.Rel.gen * Sorts.family

val build_dependent_constructor : evars constructor_summary -> evars constr_g
val build_dependent_inductive   : evars env -> inductive_family -> evars constr_g
val make_arity_signature : EConstr.env -> evar_map -> bool -> inductive_family -> EConstr.rel_context
val make_arity : EConstr.env -> evar_map -> bool -> inductive_family -> Sorts.t -> EConstr.types
val build_branch_type : EConstr.env -> evar_map -> bool -> evars constr_g -> evars constructor_summary -> evars types_g

(** Raise [Not_found] if not given a valid inductive type *)
val extract_mrectype : evar_map -> EConstr.t -> (inductive * EConstr.EInstance.t) * EConstr.constr list
val find_mrectype    : EConstr.env -> evar_map -> EConstr.types -> (inductive * EConstr.EInstance.t) * EConstr.constr list
val find_mrectype_vect : EConstr.env -> evar_map -> EConstr.types -> (inductive * EConstr.EInstance.t) * EConstr.constr array
val find_rectype     : EConstr.env -> evar_map -> EConstr.types -> inductive_type
val find_inductive   : EConstr.env -> evar_map -> EConstr.types -> (inductive * EConstr.EInstance.t) * evars constr_g list
val find_coinductive : EConstr.env -> evar_map -> EConstr.types -> (inductive * EConstr.EInstance.t) * evars constr_g list

(********************)

(** Builds the case predicate arity (dependent or not) *)
val arity_of_case_predicate :
  'e env -> inductive_family -> bool -> Sorts.t -> evars types_g

val type_case_branches_with_names :
  EConstr.env -> evar_map -> pinductive * EConstr.constr list -> evars constr_g -> evars constr_g -> evars types_g array * evars types_g

(** Annotation for cases *)
val make_case_info : 'e env -> inductive -> case_style -> case_info

(** Make a case or substitute projections if the inductive type is a record
    with primitive projections.
    Fail with an error if the elimination is dependent while the
    inductive type does not allow dependent elimination. *)
val make_case_or_project :
  'e env -> evar_map -> inductive_family -> case_info ->
  (* pred *) EConstr.constr -> (* term *) EConstr.constr -> (* branches *) EConstr.constr array -> EConstr.constr

(*i Compatibility
val make_default_case_info : env -> case_style -> inductive -> case_info
i*)

(********************)

val type_of_inductive_knowing_conclusion :
  EConstr.env -> evar_map -> Inductive.mind_specif Univ.puniverses -> EConstr.types -> evar_map * EConstr.types

(********************)
(* val control_only_guard : 'e env -> Evd.evar_map -> EConstr.types -> unit *)
