(*************************************************************
*                                                           *
* XOR EXTENSION                                             *
*                                                           *
* Vincent Cheval and Stéphanie Delaune                      *
*                                                           *
* Copyright (C) INRIA, CNRS 2000-2026                       *
* Copytight (C) University of Oxford, 2026                  *
*                                                           *
*************************************************************)


(*

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details (in file LICENSE).

    You should have received a copy of the GNU General Public License along
    with this program; if not, write to the Free Software Foundation, Inc.,
    51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.

*)

open Types

(** Matching functions *)

(** [match_terms f_next [(u1,v1);...;(un,vn)]] applies [f_next] on each most general substitution 
    [\sigma] such that [ui\sigma = vi] for all i=1...n. *)
val match_terms : (unit -> 'a) -> (term * term) list -> 'a

(** [match_facts f_next fact1 fact2] applies [f_next] on each most general substitution 
    [\sigma] such that [fact1\sigma = fact2]. *)
val match_facts : (unit -> 'a) -> fact -> fact -> 'a

(** Same as match_facts except that f1 of phase n can be matched with f2 of phase m with n >= m 
    when they are attacker facts. Used to apply Lemmas. *)
val match_facts_phase_geq : (unit -> 'a) -> fact -> fact -> 'a

(** Same as match_facts except that f1 of phase n can be matched with f2 of phase m with n <= m 
    when they are attacker facts. Used to apply Lemmas. *)
val match_facts_phase_leq : (unit -> 'a) -> fact -> fact -> 'a

(** Same as match_facts except that the predicates of [f1] and [f2] are unblocked. *)
val match_facts_unblock : (unit -> 'a) -> fact -> fact -> 'a

(** Same as match_facts except that the predicates of [f1] and [f2] are unblocked and f1 of phase n 
    can be matched with f2 of phase m with n >= m when they are attacker facts. *)
val match_facts_unblock_phase_geq : (unit -> 'a) -> fact -> fact -> 'a

(** [are_terms_matched_non_strict t1 t2] returns [true] if there exists [\sigma] such that [t1\sigma = t2] 
    or [f(t1,x)\sigma = t2] when [t1] is rooted by [f] and [x] is fresh. *)
val are_terms_matched_non_strict : term -> term -> bool

(** [are_terms_matched t1 t2] returns [true] if there exists [\sigma] such that [t1\sigma = t2] *)
val are_terms_matched : term -> term -> bool

(** [are_facts_matched fact1 fact2] returns [true] if there exists [\sigma] such that [fact1\sigma = fact2] *)
val are_facts_matched : fact -> fact -> bool

(** Matching functions for redundanty hyp *)

val mark_redundant_hyp_variables : term -> unit 
val mark_redundant_hyp_variables_fact : fact -> unit
val match_redundant_hyp_terms : (unit -> 'a) -> bool -> (term * term) list -> 'a
val match_redundant_hyp_facts : (unit -> 'a) -> bool -> fact -> fact -> 'a

(** Unify functions *)

(** [unify_terms f_next [(u1,v1);...;(un,vn)]] applies [f_next] on each most general substitution 
    [\sigma] such that [ui\sigma = vi\sigma] for all i=1...n. *)
val unify_terms : (unit -> 'a) -> (term * term) list -> 'a

(** [unify_facts f_next fact1 fact2] applies [f_next] on each most general substitution 
    [\sigma] such that [fact1\sigma = fact2\sigma]. *)
val unify_facts : (unit -> 'a) -> fact -> fact -> 'a

(** Same as [unify_facts] except that f1 of phase n can be matched with f2 of phase m with n <= m 
    when they are attacker facts. *)
val unify_facts_phase_leq : (unit -> 'a) -> fact -> fact -> 'a

(** [are_facts_unifiable fact1 fact2] returns [true] if there exists [\sigma] such that [fact1\sigma = fact2\sigma]. *)
val are_facts_unifiable : fact -> fact -> bool

(** [unify_terms f_next [(u1,v1);...;(un,vn)]] applies [f_next] on each most general substitution 
    [\sigma] such that [ui\sigma = vi\sigma] for all i=1...n. *)
val unify_for_lemma_terms : (unit -> 'a) -> binder list -> (term * term) list -> 'a

(** [unify_terms f_next [(u1,v1);...;(un,vn)]] applies [f_next vars] on each most general substitution
    [\sigma] such that [ui\sigma = vi\sigma] for all i=1...n and [vars] is the list of variabble in 
    [img(\sigma) \setminus vars(u1,v1,...,un,vn)] *)
val unify_terms_record_fresh_variables : (binder list -> 'a) -> (term * term) list -> 'a