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
open Univ
open Environ
open Entries

(** {6 Typing functions (not yet tagged as safe) }

    They return unsafe judgments that are "in context" of a set of
    (local) universe variables (the ones that appear in the term)
    and associated constraints. In case of polymorphic definitions,
    these variables and constraints will be generalized.
 *)


val infer      : ground env -> constr       -> unsafe_judgment
val infer_v    : ground env -> constr array -> unsafe_judgment array
val infer_type : ground env -> types        -> unsafe_type_judgment

val infer_local_decls :
  ground env -> (Id.t * local_entry) list -> (ground env * Context.Rel.t)

(** {6 Basic operations of the typing machine. } *)

(** If [j] is the judgement {% $ %}c:t{% $ %}, then [assumption_of_judgement env j]
   returns the type {% $ %}c{% $ %}, checking that {% $ %}t{% $ %} is a sort. *)

val assumption_of_judgment :  ground env -> unsafe_judgment -> types
val type_judgment          :  ground env -> unsafe_judgment -> unsafe_type_judgment

(** {6 Type of sorts. } *)
val type1 : types
val type_of_sort : Sorts.t -> types
val judge_of_prop : unsafe_judgment
val judge_of_set  : unsafe_judgment
val judge_of_prop_contents  : Sorts.contents -> unsafe_judgment
val judge_of_type           : Universe.t -> unsafe_judgment

(** {6 Type of a bound variable. } *)
val type_of_relative : ground env -> int -> types
val judge_of_relative : ground env -> int -> unsafe_judgment

(** {6 Type of variables } *)
val type_of_variable : ground env -> variable -> types
val judge_of_variable : ground env -> variable -> unsafe_judgment

(** {6 type of a constant } *)

val judge_of_constant : ground env -> pconstant -> unsafe_judgment

(** {6 type of an applied projection } *)

val judge_of_projection : ground env -> Projection.t -> unsafe_judgment -> unsafe_judgment

(** {6 Type of application. } *)
val judge_of_apply :
  ground env -> unsafe_judgment -> unsafe_judgment array
    -> unsafe_judgment

(** {6 Type of an abstraction. } *)
val judge_of_abstraction :
  ground env -> Name.t -> unsafe_type_judgment -> unsafe_judgment
    -> unsafe_judgment

(** {6 Type of a product. } *)
val sort_of_product : ground env -> Sorts.t -> Sorts.t -> Sorts.t
val type_of_product : ground env -> Name.t -> Sorts.t -> Sorts.t -> types
val judge_of_product :
  ground env -> Name.t -> unsafe_type_judgment -> unsafe_type_judgment
    -> unsafe_judgment

(** s Type of a let in. *)
val judge_of_letin :
  ground env -> Name.t -> unsafe_judgment -> unsafe_type_judgment -> unsafe_judgment
    -> unsafe_judgment

(** {6 Type of a cast. } *)
val judge_of_cast :
  ground env -> unsafe_judgment -> cast_kind -> unsafe_type_judgment ->
  unsafe_judgment

(** {6 Inductive types. } *)

val judge_of_inductive : ground env -> inductive puniverses -> unsafe_judgment

val judge_of_constructor : ground env -> constructor puniverses -> unsafe_judgment

(** {6 Type of Cases. } *)
val judge_of_case : ground env -> case_info
  -> unsafe_judgment -> unsafe_judgment -> unsafe_judgment array
    -> unsafe_judgment

val type_of_projection_constant : ground env -> Projection.t puniverses -> types

val type_of_constant_in : ground env -> pconstant -> types

(** Check that hyps are included in env and fails with error otherwise *)
val check_hyps_inclusion : ground env -> ('a -> constr) -> 'a -> Context.Named.t -> unit
