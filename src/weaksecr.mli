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

val initialize : t_solver_kind -> unit

(* [is_standard_clause r] returns true when the clause [r] 
   must be preserved from transformations *)
val is_standard_clause : marked_reduction -> bool
val simplify : (marked_reduction -> unit) -> (marked_reduction -> unit) -> marked_reduction -> unit
val selfun : marked_reduction -> int
val remove_equiv_events : (marked_reduction -> unit) -> marked_reduction -> unit
