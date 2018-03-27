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

(** The type of environments. *)

type link_info =
  | Linked of string
  | LinkedInteractive of string
  | NotLinked

type key = int CEphemeron.key option ref 

type constant_key = constant_body * (link_info ref * key)

type mind_key = mutual_inductive_body * link_info ref

type globals = {
  env_constants : constant_key Cmap_env.t;
  env_inductives : mind_key Mindmap_env.t;
  env_modules : module_body MPmap.t;
  env_modtypes : module_type_body MPmap.t}

type stratification = {
  env_universes : UGraph.t;
  env_engagement : engagement
}

type lazy_val

val force_lazy_val : lazy_val -> (Vmvalues.values * Id.Set.t) option
val dummy_lazy_val : unit -> lazy_val
val build_lazy_val : lazy_val -> (Vmvalues.values * Id.Set.t) -> unit

type +'e named_context_val = private {
  env_named_ctx : 'e Context.Named.gen;
  env_named_map : ('e Context.Named.Declaration.gen * lazy_val) Id.Map.t;
}

type +'e rel_context_val = private {
  env_rel_ctx : 'e Context.Rel.gen;
  env_rel_map : ('e Context.Rel.Declaration.gen * lazy_val) Range.t;
}

type +'e env = {
    env_globals       : globals;
    env_named_context : 'e named_context_val;
    env_rel_context   : 'e rel_context_val;
    env_nb_rel        : int;
    env_stratification : stratification;
    env_typing_flags  : typing_flags;
    retroknowledge : Retroknowledge.retroknowledge;
    indirect_pterms : Opaqueproof.opaquetab;
}

val empty_named_context_val : 'e named_context_val

val empty_env : 'e env

(** Rel context *)

val empty_rel_context_val : 'e rel_context_val
val push_rel_context_val :
  'e Context.Rel.Declaration.gen -> 'e rel_context_val -> 'e rel_context_val
val match_rel_context_val  :
  'e rel_context_val -> ('e Context.Rel.Declaration.gen * lazy_val * 'e rel_context_val) option

val nb_rel         : 'e env -> int
val push_rel       : 'e Context.Rel.Declaration.gen -> 'e env -> 'e env
val lookup_rel     : int -> 'e env -> 'e Context.Rel.Declaration.gen
val lookup_rel_val : int -> 'e env -> lazy_val
val env_of_rel     : int -> 'e env -> 'e env

(** Named context *)

val push_named_context_val  :
    'e Context.Named.Declaration.gen -> 'e named_context_val -> 'e named_context_val
val push_named_context_val_val  :
    'e Context.Named.Declaration.gen -> lazy_val -> 'e named_context_val -> 'e named_context_val
val match_named_context_val  :
  'e named_context_val -> ('e Context.Named.Declaration.gen * lazy_val * 'e named_context_val) option
val map_named_val :
   ('e constr_g -> 'e constr_g) -> 'e named_context_val -> 'e named_context_val

val push_named       : 'e Context.Named.Declaration.gen -> 'e env -> 'e env
val lookup_named     : Id.t -> 'e env -> 'e Context.Named.Declaration.gen
val lookup_named_val : Id.t -> 'e env -> lazy_val
val env_of_named     : Id.t -> 'e env -> 'e env

(** Global constants *)


val lookup_constant_key : Constant.t -> 'e env -> constant_key
val lookup_constant : Constant.t -> 'e env -> constant_body

(** Mutual Inductives *)
val lookup_mind_key : MutInd.t -> 'e env -> mind_key
val lookup_mind : MutInd.t -> 'e env -> mutual_inductive_body
