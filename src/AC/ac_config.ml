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


(** Debugging functions *)

(** By setting [activate_debug_mode] as constant and not a reference, it allows an optimisation
    in the native compiler to completely remove the debugging functions instead of always testing
    whether the variable is true, should we have put it as a reference. *)
let activate_debug_mode = false

let count_unification = ref 0
let count_matching = ref 0
let target_unification = ref 782
let target_matching = ref 0

let debug_incr_unification =
  if activate_debug_mode 
  then (fun () -> incr count_unification)
  else (fun () -> ())
  
let debug_incr_matching =
  if activate_debug_mode 
  then (fun () -> incr count_matching)
  else (fun () -> ())
      
let debug_unification f =
  if activate_debug_mode
  then 
    if !count_unification = !target_unification
    then f ()
    else ()
  else ()
  [@@inline]

let debug_matching f =
  if activate_debug_mode
  then 
    if !count_matching = !target_matching
    then f ()
    else ()
  else ()
  [@@inline]