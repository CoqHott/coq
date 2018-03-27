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
open Declarations

(** Unsafe environments. We define here a datatype for environments.
   Since typing is not yet defined, it is not possible to check the
   informations added in environments, and that is why we speak here
   of ``unsafe'' environments. *)

(** Environments have the following components:
   - a context for de Bruijn variables
   - a context for de Bruijn variables vm values
   - a context for section variables and goal assumptions
   - a context for section variables and goal assumptions vm values
   - a context for global constants and axioms
   - a context for inductive definitions
   - a set of universe constraints
   - a flag telling if Set is, can be, or cannot be set impredicative *)




type +'e env
val pre_env : 'e env -> 'e Pre_env.env
val env_of_pre_env : 'e Pre_env.env -> 'e env
val oracle : 'e env -> Conv_oracle.oracle
val set_oracle : 'e env -> Conv_oracle.oracle -> 'e env

type +'e named_context_val
val eq_named_context_val : ground named_context_val -> ground named_context_val -> bool

val empty_env : 'e env

val universes     : 'e env -> UGraph.t
val rel_context   : 'e env -> 'e Context.Rel.gen
val named_context : 'e env -> 'e Context.Named.gen
val named_context_val : 'e env -> 'e named_context_val

val opaque_tables : 'e env -> Opaqueproof.opaquetab
val set_opaque_tables : 'e env -> Opaqueproof.opaquetab -> 'e env


val engagement    : 'e env -> engagement
val typing_flags    : 'e env -> typing_flags
val is_impredicative_set : 'e env -> bool
val type_in_type : 'e env -> bool
val deactivated_guard : 'e env -> bool

(** is the local context empty *)
val empty_context : 'e env -> bool

(** {5 Context of de Bruijn variables ([rel_context]) } *)

val nb_rel           : 'e env -> int
val push_rel         : 'e Context.Rel.Declaration.gen -> 'e env -> 'e env
val push_rel_context : 'e Context.Rel.gen -> 'e env -> 'e env
val push_rec_types   : 'e Evkey.t rec_declaration_g -> 'e env -> 'e env

(** Looks up in the context of local vars referred by indice ([rel_context]) 
   raises [Not_found] if the index points out of the context *)
val lookup_rel    : int -> 'e env -> 'e Context.Rel.Declaration.gen
val evaluable_rel : int -> 'e env -> bool

(** {6 Recurrence on [rel_context] } *)

val fold_rel_context :
  ('e env -> 'e Context.Rel.Declaration.gen -> 'a -> 'a) -> 'e env -> init:'a -> 'a

(** {5 Context of variables (section variables and goal assumptions) } *)

val named_context_of_val : 'e named_context_val -> 'e Context.Named.gen
val val_of_named_context : 'e Context.Named.gen -> 'e named_context_val
val empty_named_context_val : 'e named_context_val
val ids_of_named_context_val : 'e named_context_val -> Id.Set.t


(** [map_named_val f ctxt] apply [f] to the body and the type of
   each declarations.
   *** /!\ ***   [f t] should be convertible with t *)
val map_named_val :
   ('e constr_g -> 'e constr_g) -> 'e named_context_val -> 'e named_context_val

val push_named : 'e Context.Named.Declaration.gen -> 'e env -> 'e env
val push_named_context : 'e Context.Named.gen -> 'e env -> 'e env
val push_named_context_val  :
    'e Context.Named.Declaration.gen -> 'e named_context_val -> 'e named_context_val



(** Looks up in the context of local vars referred by names ([named_context]) 
   raises [Not_found] if the Id.t is not found *)

val lookup_named     : variable -> 'e env -> 'e Context.Named.Declaration.gen
val lookup_named_val : variable -> 'e named_context_val -> 'e Context.Named.Declaration.gen
val evaluable_named  : variable -> 'e env -> bool
val named_type : variable -> 'e env -> 'e types_g
val named_body : variable -> 'e env -> 'e constr_g option

(** {6 Recurrence on [named_context]: older declarations processed first } *)

val fold_named_context :
  ('e env -> 'e Context.Named.Declaration.gen -> 'a -> 'a) -> 'e env -> init:'a -> 'a

(** Recurrence on [named_context] starting from younger decl *)
val fold_named_context_reverse :
  ('a -> 'e Context.Named.Declaration.gen -> 'a) -> init:'a -> 'e env -> 'a

(** This forgets named and rel contexts *)
val reset_context : 'e env -> 'f env

(** This forgets rel context and sets a new named context *)
val reset_with_named_context : 'e named_context_val -> 'f env -> 'e env

(** This removes the [n] last declarations from the rel context *)
val pop_rel_context : int -> 'e env -> 'e env

(** {5 Global constants }
  {6 Add entries to global environment } *)

val add_constant : Constant.t -> constant_body -> 'e env -> 'e env
val add_constant_key : Constant.t -> constant_body -> Pre_env.link_info ->
  'e env -> 'e env

(** Looks up in the context of global constant names 
   raises [Not_found] if the required path is not found *)
val lookup_constant    : Constant.t -> 'e env -> constant_body
val evaluable_constant : Constant.t -> 'e env -> bool

(** New-style polymorphism *)
val polymorphic_constant  : Constant.t -> 'e env -> bool
val polymorphic_pconstant : pconstant -> 'e env -> bool
val type_in_type_constant : Constant.t -> 'e env -> bool

(** {6 ... } *)
(** [constant_value env c] raises [NotEvaluableConst Opaque] if
   [c] is opaque and [NotEvaluableConst NoBody] if it has no
   body and [NotEvaluableConst IsProj] if [c] is a projection 
   and [Not_found] if it does not exist in [env] *)

type const_evaluation_result = NoBody | Opaque
exception NotEvaluableConst of const_evaluation_result

val constant_type : 'e env -> Constant.t puniverses -> types constrained

val constant_value_and_type : 'e env -> Constant.t puniverses ->
  constr option * types * Univ.Constraint.t
(** The universe context associated to the constant, empty if not 
    polymorphic *)
val constant_context : 'e env -> Constant.t -> Univ.AUContext.t

(* These functions should be called under the invariant that [env] 
   already contains the constraints corresponding to the constant 
   application. *)
val constant_value_in : 'e env -> Constant.t puniverses -> constr
val constant_type_in : 'e env -> Constant.t puniverses -> types
val constant_opt_value_in : 'e env -> Constant.t puniverses -> constr option

(** {6 Primitive projections} *)

val lookup_projection : Projection.t -> 'e env -> projection_body
val is_projection : Constant.t -> 'e env -> bool

(** {5 Inductive types } *)
val add_mind_key : MutInd.t -> Pre_env.mind_key -> 'e env -> 'e env
val add_mind : MutInd.t -> mutual_inductive_body -> 'e env -> 'e env

(** Looks up in the context of global inductive names 
   raises [Not_found] if the required path is not found *)
val lookup_mind : MutInd.t -> 'e env -> mutual_inductive_body

(** New-style polymorphism *)
val polymorphic_ind  : inductive -> 'e env -> bool
val polymorphic_pind : pinductive -> 'e env -> bool
val type_in_type_ind : inductive -> 'e env -> bool

(** Old-style polymorphism *)
val template_polymorphic_ind : inductive -> 'e env -> bool
val template_polymorphic_pind : pinductive -> 'e env -> bool

(** {5 Modules } *)

val add_modtype : module_type_body -> 'e env -> 'e env

(** [shallow_add_module] does not add module components *)
val shallow_add_module : module_body -> 'e env -> 'e env

val lookup_module : ModPath.t -> 'e env -> module_body
val lookup_modtype : ModPath.t -> 'e env -> module_type_body

(** {5 Universe constraints } *)

(** Add universe constraints to the environment.
    @raise UniverseInconsistency .
*)
val add_constraints : Univ.Constraint.t -> 'e env -> 'e env

(** Check constraints are satifiable in the environment. *)
val check_constraints : Univ.Constraint.t -> 'e env -> bool
val push_context : ?strict:bool -> Univ.UContext.t -> 'e env -> 'e env
val push_context_set : ?strict:bool -> Univ.ContextSet.t -> 'e env -> 'e env
val push_constraints_to_env : 'a Univ.constrained -> 'e env -> 'e env

val set_engagement : engagement -> 'e env -> 'e env
val set_typing_flags : typing_flags -> 'e env -> 'e env

(** {6 Sets of referred section variables }
   [global_vars_set env c] returns the list of [id]'s occurring either
   directly as [Var id] in [c] or indirectly as a section variable
   dependent in a global reference occurring in [c] *)

val global_vars_set : 'e Evkey.t env -> 'e constr_g -> Id.Set.t

(** the constr must be a global reference *)
val vars_of_global : 'e Evkey.t env -> 'e constr_g -> Id.Set.t

(** closure of the input id set w.r.t. dependency *)
val really_needed : ground env -> Id.Set.t -> Id.Set.t

(** like [really_needed] but computes a well ordered named context *)
val keep_hyps : ground env -> Id.Set.t -> Context.Named.t

(** {5 Unsafe judgments. }
    We introduce here the pre-type of judgments, which is
  actually only a datatype to store a term with its type and the type of its
  type. *)

type ('constr, 'types) punsafe_judgment = {
  uj_val : 'constr;
  uj_type : 'types }

type unsafe_judgment = (constr, types) punsafe_judgment

val make_judge : 'constr -> 'types -> ('constr, 'types) punsafe_judgment
val j_val  : ('constr, 'types) punsafe_judgment -> 'constr
val j_type : ('constr, 'types) punsafe_judgment -> 'types

type 'types punsafe_type_judgment = {
  utj_val : 'types;
  utj_type : Sorts.t }

type unsafe_type_judgment = types punsafe_type_judgment

(** {6 Compilation of global declaration } *)

val compile_constant_body : ground env -> constant_universes ->
  constant_def -> Cemitcodes.body_code option

exception Hyp_not_found

(** [apply_to_hyp sign id f] split [sign] into [tail::(id,_,_)::head] and
   return [tail::(f head (id,_,_) (rev tail))::head].
   the value associated to id should not change *)
val apply_to_hyp : 'e named_context_val -> variable ->
  ('e Context.Named.gen -> 'e Context.Named.Declaration.gen ->
   'e Context.Named.gen -> 'e Context.Named.Declaration.gen) ->
    'e named_context_val

val remove_hyps : Id.Set.t ->
  ('e Context.Named.Declaration.gen -> 'e Context.Named.Declaration.gen) ->
  (Pre_env.lazy_val -> Pre_env.lazy_val) ->
  'e named_context_val -> 'e named_context_val



open Retroknowledge
(** functions manipulating the retroknowledge 
    @author spiwack *)
val retroknowledge : (retroknowledge->'a) -> 'e env -> 'a

val registered : 'e env -> field -> bool

val register : 'e env -> field -> Retroknowledge.entry -> 'e env

(** Native compiler *)
val no_link_info : Pre_env.link_info
