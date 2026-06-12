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

let is_ac_constructor_clause ((hyp,concl,_,cons,variant):marked_reduction) = 
  if variant <> Protocol && Terms.is_true_constraints cons
  then 
    match hyp,concl with
    | [(Pred({p_info = Attacker _; _} as p1,[Var x]),NoMarking);(Pred(p2,[Var y]),NoMarking)], 
      Pred(p3,[FAC(f,[(Var x',1);(Var y',1)])])
      when 
        p1 == p2 && p1 == p3 &&
        ((x == x' && y == y') || (x == y' && y == x')) -> Some f
    | _ -> None
  else None

(** General marking *)

let match_marking mk1 mk2 = match mk1, mk2 with
  | NoMarking, _ -> true
  | Static f1, Static f2 when f1 == f2 -> true
  | Dynamic f1, Dynamic f2 when f1 == f2 -> true
  | _ -> false

(** Static marking *)





(** Dynamic marking *)

(** [find_external_factor_symbol f t] returns [Some u_i] when [t = f(u_1,u_2,...,u_n)] and [u_i] is
  not a variable. *)
let find_external_factor_symbol f = function
  | Pred(_,[FAC(f',margs)]) when f == f' ->
      begin match List.find_opt (fun (t,_) -> match t with 
        | Var _ -> false
        | _ -> true     
      ) margs with
      | Some (t,_) -> Some t
      | None -> None
      end
  | _ -> None

let find_external_factor ((hyp,concl,_,_,_) as cl:marked_reduction) selected_hyp = 
  match is_ac_constructor_clause cl with
  | None -> None
  | Some f -> 
      match find_external_factor_symbol f selected_hyp with
      | Some t -> Some (f,t)
      | None -> None

let potential_apply_dynamic_marking_fact factor f fact = match fact with 
    | Pred(_,[t]) ->
        let t' = Terms.copy_term4 t in
        begin match t' with
          | FunApp _ -> Terms.equal_terms t' factor
          | FAC(f',_) when f != f' -> Terms.equal_terms t' factor
          | FAC(f',margs) -> List.exists (fun (t,m) -> Terms.equal_terms t factor) margs
          | _ -> false
        end
    | _ -> false

let is_dynamic_fact_applicable f = function
  | Pred(_,[FAC(f',_)]) when f == f' -> true
  | _ -> false

let apply_dynamic_marking factor f = function
  | [fact1,NoMarking; fact2,NoMarking] as hypl ->
      (* print_string "\n\n apply_dynamic_marking: Factor = ";
      Display.Text.display_term factor;
      print_string " - Fact 1 = ";
      Display.Text.display_fact fact1;
      print_string " - Fact 2 = ";
      Display.Text.display_fact fact2;
      print_string "\n";
      let r =  *)
        if potential_apply_dynamic_marking_fact factor f fact1 
        then 
          (* [fact1,Dynamic f; fact2,NoMarking] *)
          if is_dynamic_fact_applicable f fact1 
          then [fact1,Dynamic f; fact2,NoMarking]
          else hypl
        else 
          (* [fact1,NoMarking; fact2,Dynamic f] *)
          if is_dynamic_fact_applicable f fact2 
          then [fact1,NoMarking; fact2,Dynamic f]
          else hypl
      (* in
      print_string "Result = ";
      Display.Text.display_list Display.Text.display_marked_fact " - " r;
      print_string "\n\n";
      r *)
  | hypl -> hypl