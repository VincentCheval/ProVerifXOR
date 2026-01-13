(*************************************************************
 *                                                           *
 *  Cryptographic protocol verifier                          *
 *                                                           *
 *  Bruno Blanchet, Vincent Cheval, and Marc Sylvestre       *
 *                                                           *
 *  Copyright (C) INRIA, CNRS 2000-2026                      *
 *                                                           *
 *************************************************************)

(*************************************************************

XOR EXTENSION

Anonymously submitted for CCS 2026
Anonymous authors

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

(** [is_ac_constructor_clause cl] returns [Some f] when [cl] is the AC constructor clause of [f], 
    that is att_k(x) && att_k(y) -> att(f(x,y)) where [f] is an AC function symbol. *)
val is_ac_constructor_clause : marked_reduction -> funsymb option

(** General marking *)

val match_marking : marking -> marking -> bool

(** Static marking *)


(** Dynamic marking *)

(** [find_external_factor solved_cl t] returns [Some u_i] when [t = f(u_1,u_2,...,u_n)] and [u_i] is
  not a variable and [solved_cl] is the AC constructor clause of [f]. *)
val find_external_factor : marked_reduction -> fact -> (funsymb * term) option

(** [apply_dynamic_marking t f hypl] returns the hypotheses [hypl] of the AC constructor clause of [f] 
  with one of its hypothesis containing [t] marked dynamically. *)
val apply_dynamic_marking : term -> funsymb -> (fact * marking) list -> (fact * marking) list