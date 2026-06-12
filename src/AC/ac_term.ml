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
open Ac_utils

let ( let* ) o f = match o with
  | None -> None
  | Some x -> f x

let get_id_display id =
  match id.display with
  | None ->
     id.orig_name
  | Some name -> name

let string_of_fsymb f =
  match f.f_name with
    Renamable id -> get_id_display id
  | Fixed s -> s

(* exception Terms.Unify *)
let dummy_var = Terms.new_var_def Param.bitstring_type
let dummy = Var dummy_var

(** String_of functions *)

let display_with_unfold = ref false

let string_of_variable v = "#"^(string_of_int v.v_id)
let string_of_symbol f = (string_of_fsymb f)

let rec string_of_term under_AC = function 
  | Var v -> string_of_variable v
  | FunApp(f,[]) -> string_of_fsymb f;
  | FunApp(f,args) -> (string_of_fsymb f) ^ List.string_of (string_of_term false) "(" ")" "," args
  | FAC(f,margs) -> string_of_term_AC under_AC f margs

and string_of_term_AC under_AC f margs = match margs with 
  | [] | [_,1] -> internal_error __POS__ "[string_of_term_AC] The AC function should contain at least two arguments."
  | [mt] -> (string_of_fsymb f) ^ "(" ^ string_of_mterm mt ^ ")"
  | margs ->
    let b,e = if under_AC then "(",")" else "","" in
    List.string_of string_of_mterm b e (" "^(string_of_fsymb f)^" ") margs

and string_of_mterm (t,k) = 
  if k = 1
  then string_of_term true t
  else string_of_term true t ^ "^{" ^ string_of_int k ^ "}"

let string_of_term t = string_of_term false t

let rec string_of_term_unfold = function 
  | Var v -> string_of_variable v
  | FunApp(f,[]) -> string_of_symbol f;
  | FunApp(f,args) -> string_of_symbol f ^ List.string_of string_of_term_unfold "(" ")" ", " args
  | FAC(f,margs) -> string_of_symbol f ^ "(" ^ string_of_mterm_unfold margs ^ ")"

and string_of_mterm_unfold = function
  | [] -> ""
  | [t,1] -> string_of_term_unfold t
  | (t,1)::q -> 
      let str_t = string_of_term_unfold t in 
      let str_q = string_of_mterm_unfold q in
      str_t ^ ", " ^ str_q
  | (t,k)::q -> 
      let str_t = string_of_term_unfold t in
      let str_q = string_of_mterm_unfold ((t,k-1)::q) in
      str_t ^ ", " ^ str_q

let string_of_term t = 
  if !display_with_unfold 
  then string_of_term_unfold t
  else string_of_term t

(** Display functions *)

let display_variable v = print_string (string_of_variable v)

let display_symbol f = print_string (string_of_fsymb f)

let rec display_term under_AC = function 
  | Var v -> display_variable v
  | FunApp(f,[]) -> display_symbol f;
  | FunApp(f,args) -> display_symbol f; List.display (display_term false) "(" ")" ", " args
  | FAC(f,margs) -> display_term_AC under_AC f margs

and display_mterm (t,k) = 
  if k = 1
  then display_term true t
  else (display_term true t; print_string "^{"; print_int k; print_string "}")

and display_mterm_list = function 
  | [] -> ()
  | [mt] -> display_mterm mt
  | mt::q ->
      display_mterm mt;
      print_string ", ";
      display_mterm_list q

and display_term_AC under_AC f margs = match margs with 
  | [] | [_,1] -> internal_error __POS__ "[display_term_AC] The AC function should contain at least two arguments."
  | [mt] -> display_symbol f; print_string "("; display_mterm mt; print_string ")"
  | margs ->
      let b,e = if under_AC then "(",")" else "","" in
      List.display display_mterm b e (" "^(string_of_fsymb f)^" ") margs

let rec display_term_unfold = function 
  | Var v -> display_variable v; print_string ":T"
  | FunApp(f,[]) -> display_symbol f;
  | FunApp(f,args) -> display_symbol f; List.display display_term_unfold "(" ")" ", " args
  | FAC(f,margs) -> display_symbol f; print_string "("; display_mterm_unfold margs; print_string ")"

and display_mterm_unfold = function
  | [] -> ()
  | [t,1] -> display_term_unfold t
  | (t,1)::q -> display_term_unfold t; print_string ", "; display_mterm_unfold q
  | (t,k)::q -> display_term_unfold t; print_string ", "; display_mterm_unfold ((t,k-1)::q)

let display_term t = 
  if !display_with_unfold 
  then display_term_unfold t
  else display_term false t
      
(** Comparaison *)

let compare_variable v1 v2 = compare v1.v_id v2.v_id

let less_symbol f1 f2 = f1.f_record < f2.f_record

let compare_symbol f1 f2 = compare f1.f_record f2.f_record

let rec compare_term t1 t2 = match t1, t2 with
  | (FunApp(f1,_) | FAC(f1,_)), (FunApp(f2,_) | FAC(f2,_)) ->
      begin match compare_symbol f1 f2 with
      | 0 -> 
          begin match t1,t2 with
          | FunApp(_,args1), FunApp(_,args2) -> lexicographic_compare compare_term args1 args2
          | FAC(_,margs1), FAC(_,margs2) -> lexicographic_compare compare_mterm margs1 margs2
          | _ -> internal_error __POS__ (Printf.sprintf "[compare_term] The symbols (%s and %s) being equal, the term should have the same type." (Terms.string_of_funsymb f1) (Terms.string_of_funsymb f2))
          end
      | c -> c
      end
  | (FunApp _ | FAC _) , _ -> -1
  | _, (FunApp _ | FAC _) -> 1
  | Var v1, Var v2 -> compare_variable v1 v2
  
and compare_mterm (t1,k1) (t2,k2) = match compare_term t1 t2 with
  | 0 -> if k1 < k2 then -1 else if k1 = k2 then 0 else 1
  | c -> c

(** [equal t1 t2] returns [true] iff they are syntactically equals. Note that it
    is compatible with [compare_term], i.e. [equal t1 t2 = true] iff [compare_term t1 t2 = 0]. *)
let rec equal t1 t2 = match t1, t2 with
  | Var v1, Var v2 -> v1 == v2
  | FunApp(f1,args1), FunApp(f2,args2) ->
      f1 == f2 && List.for_all2 equal args1 args2
  | FAC(f1,args1), FAC(f2,args2) ->
      f1 == f2 && 
      List.length args1 = List.length args2 && 
      List.for_all2 (fun (u1,k1) (u2,k2) -> k1 = k2 && equal u1 u2) args1 args2
  | _ -> false

(** Creation of terms 

    To simplify equality terms, terms are kept in a specific shape with respect
    to AC symbols. In particular, we will preserve the invariant that two terms
    equal modulo AC if and only if they are equal by [equal].
*)

(** [merge tlist1 tlist2] merges two ordered (by [compare_mterm] list of multiplicity terms. *)
let rec merge (tlist1:mterm list) (tlist2:mterm list) = match tlist1, tlist2 with
  | [], _ -> tlist2
  | _, [] -> tlist1
  | (t1,k1)::q1, (t2,k2)::q2 -> 
      match compare_term t1 t2 with
      | 0 -> (t1,k1+k2) :: merge q1 q2
      | -1 -> (t1,k1) :: merge q1 tlist2
      | _ -> (t2,k2) :: merge tlist1 q2

(** [merge tlist1 k tlist2] is equivalent (and faster) to applying  [merge tlist1] 
    sucessively [k] times on [tlist2]. *)
let rec merge_multiplicity tlist1 k1 tlist2 = match tlist1, tlist2 with
  | [], _ -> tlist2
  | _, [] -> List.map (fun (t1,k1') -> (t1,k1'*k1)) tlist1
  | (t1,k1')::q1, (t2,k2')::q2 -> 
      match compare_term t1 t2 with
      | 0 -> (t1,(k1*k1')+k2') :: merge_multiplicity q1 k1 q2
      | -1 -> (t1,(k1*k1')) :: merge_multiplicity q1 k1 tlist2
      | _ -> (t2,k2') :: merge_multiplicity tlist1 k1 q2

let rec add_aux u k tlist = match tlist with
  | [] -> [(u,k)]
  | (t,k') :: q ->
      match compare_term u t with
      | 0 -> (t,k+k') :: q
      | -1 -> (u,k) :: tlist
      | _ -> (t,k') :: (add_aux u k q) 

(** [add f u [mt1;...;mtk]] creates the list of mterms corresponding to [u f mt1 f ... f mtk].
    The function assumes that [mt1 f mt2 f ... f mtk] is correctly ordered. *)
let add f u mtlist = match u with 
  | FAC(g,args) when f == g -> merge args mtlist 
  | _ -> add_aux u 1 mtlist
  [@@inline]

(** Equivalent to [u f ... f u f mt1 f .. f mtk] where occurs [k] times. *)
let add_multiplicity f u k tlist = match u with 
  | FAC(g,args) when f == g -> merge_multiplicity args k tlist 
  | _ -> add_aux u k tlist
  [@@inline]

let apply_symbol f args = 
  if f.f_AC
  then
    let margs = 
      List.fold_left (fun acc t ->
        add_multiplicity f t 1 acc
      ) [] args
    in
    FAC(f,margs)
  else FunApp(f,args)

let apply_symbol_margs f margs = 
  if f.f_AC
  then
    let margs = 
      List.fold_left (fun acc (t,n) ->
        add_multiplicity f t n acc
      ) [] margs
    in
    FAC(f,margs)
  else failwith "Expected AC Function symbol [apply_symbol_margs]"

(*********************
   Unfolding        
**********************)

(** [unfold_links_non_rec t] unfolds the links only once. Traveres all function symbols. *)
let rec unfold_links_non_rec = function
  | Var { link = TLink t; _ } -> t
  | Var _ as t -> t
  | FunApp(f,args) -> FunApp(f,List.map unfold_links_non_rec args)
  | FAC(f,args) ->
      let copied_args = List.map (fun (x,k) -> unfold_links_non_rec x, k) args in
      let new_args = List.fold_left (fun acc (u,k) -> add_multiplicity f u k acc) []  copied_args in
      FAC(f,new_args)

(** [unfold_links_rec t] unfolds the links recursively. Traveres all function symbols. *)
let rec unfold_links_rec = function
  | Var { link = TLink t; _ } -> unfold_links_rec t
  | Var _ as t -> t
  | FunApp(f,args) -> FunApp(f,List.map unfold_links_rec args)
  | FAC(f,args) ->
      let copied_args = List.map (fun (x,k) -> unfold_links_rec x, k) args in
      let new_args = List.fold_left (fun acc (u,k) -> add_multiplicity f u k acc) [] copied_args in
      FAC(f,new_args)

(** [unfold_links_rec_only_AC f_AC acc_mt mt] unfolds the links in [mt] but only go through
    variables and terms rooted by [f_AC]. When it reaches terms rooted by a different symbol,
    the term is stored in the list [acc_mterm]. *)
let rec unfold_links_rec_only_AC f_AC acc_mterm (t,k) = match t with
  | Var { link = TLink t; _ } -> unfold_links_rec_only_AC f_AC acc_mterm (t,k)
  | FAC(f,margs) when f == f_AC ->
      List.iter (fun (t',k') ->
        unfold_links_rec_only_AC f_AC acc_mterm (t',k*k')
      ) margs
  | t -> acc_mterm := (t,k) :: !acc_mterm

(** [unfold_links_non_rec_only_AC f_AC acc_mt mt] unfolds terms rooted by [f_AC]. When it 
    reaches terms rooted by a different symbol, the term is stored in the list [acc_mterm]. *)
let rec unfold_only_AC f_AC f_next (t,k) = match t with
  | Var _ -> f_next (t,k)
  | FAC(f,margs) when f == f_AC ->
      List.iter (fun (t',k') ->
        unfold_only_AC f_AC f_next (t',k*k')
      ) margs
  | t -> f_next (t,k)

let rec unfold_no_rec_only_AC f_AC f_next_before_link f_next_after_link (t,k) = match t with
  | Var { link = TLink t'; _ } -> unfold_only_AC f_AC f_next_after_link (t',k)
  | Var v -> f_next_before_link (t,k)
  | FAC(f,margs) when f == f_AC ->
    List.iter (fun (t',k') ->
      unfold_no_rec_only_AC f_AC f_next_before_link f_next_after_link (t',k*k')
    ) margs
  | t -> f_next_before_link (t,k)
  
(** [unfold_links_rec_and_mark_variables t] unfolds the links in [t] recursively. When
    a variable not linked is found, it is marked by linking it with [Marked]. *)
let rec unfold_links_rec_and_mark_variables t = match t with
  | Var v -> 
      begin match v.link with
        | NoLink -> Terms.link v Marked; t
        | Marked -> t
        | TLink t' -> unfold_links_rec_and_mark_variables t'
        | _ -> internal_error __POS__ "[unfold_links_rec_and_mark_variables] Unexpected link." 
      end
  | FunApp(f,args) ->
      let args' = List.mapq unfold_links_rec_and_mark_variables args in
      if args == args'
      then t
      else FunApp(f,args')
  | FAC(f,margs) ->
      let margs' = unfold_links_rec_and_mark_variables_mterms f margs in
      if margs' == margs
      then t
      else FAC(f,margs')

(** Similar to [unfold_links_rec_and_mark_variables] but for [mtl] list of [mterm] under the symbol [f] *)
and unfold_links_rec_and_mark_variables_mterms f mtl =
  let unordered = ref [] in
  let rec retrieve_ordered mtl = match mtl with
  | [] -> []
  | (t,k) as mt :: q ->
      let t' = unfold_links_rec_and_mark_variables t in
      let q' = retrieve_ordered q in
      if t == t'
      then if q == q' then mtl else mt :: q'
      else (unordered := (t',k) :: !unordered; q')
  in
  let ordered = retrieve_ordered mtl in
  List.fold_left (fun acc (t,k) -> add_multiplicity f t k acc) ordered !unordered

(** [unfold_links_rec_and_get_variables_term t] unfolds the links in [t] and returns as well the list 
    of variables contained in the unfolded term [t]. *)
let unfold_links_rec_and_get_variables_term t = 
  Terms.auto_cleanup_nocatch (fun () ->
    let t' = unfold_links_rec_and_mark_variables t in
    let vars = !Terms.current_bound_vars in
    (vars,t')
  )
  [@@inline]

(** Similar to [unfold_links_rec_and_mark_variables] but for [mtl] list of [mterm] under the symbol [f] *)
let unfold_links_rec_and_get_variables_mterms f mt_l = 
  Terms.auto_cleanup_nocatch (fun () ->
    let mt_l' = unfold_links_rec_and_mark_variables_mterms f mt_l in
    let vars = !Terms.current_bound_vars in
    (vars,mt_l')
  ) 

(** [unfold_links_rec_and_mark_variables v_target t] unfolds the links in [t] recursively. When
    a variable not linked is found, it is marked by linking it with [Marked]. 
    @raise Terms.Unify when the variable [v_target] is found. *)
let rec unfold_links_rec_and_mark_variables_and_occur_checks v_target t = match t with
  | Var v -> 
      if v_target == v then raise Terms.Unify;
      begin match v.link with
        | NoLink -> Terms.link v Marked; t
        | Marked -> t
        | TLink t' -> unfold_links_rec_and_mark_variables_and_occur_checks v_target t'
        | _ -> internal_error __POS__ "[unfold_links_rec_and_mark_variables_and_occur_checks] Unexpected link." 
      end
  | FunApp(f,args) ->
      let args' = List.mapq (unfold_links_rec_and_mark_variables_and_occur_checks v_target) args in
      if args == args'
      then t
      else FunApp(f,args')
  | FAC(f,margs) ->
      let margs' = unfold_links_rec_and_mark_variables_and_occur_checks_mterms v_target f margs in
      if margs' == margs
      then t
      else FAC(f,margs')

(** Similar to [unfold_links_rec_and_mark_variables_and_occur_checks_mterms] but for [mtl] list of [mterm] under the symbol [f] *)
and unfold_links_rec_and_mark_variables_and_occur_checks_mterms v_target f mtl =
  let unordered = ref [] in
  let rec retrieve_ordered mtl = match mtl with
  | [] -> []
  | (t,k) as mt :: q ->
      let t' = unfold_links_rec_and_mark_variables_and_occur_checks v_target t in
      let q' = retrieve_ordered q in
      if t == t'
      then if q == q' then mtl else mt :: q'
      else (unordered := (t',k) :: !unordered; q')
  in
  let ordered = retrieve_ordered mtl in
  List.fold_left (fun acc (t,k) -> add_multiplicity f t k acc) ordered !unordered
  
(** [unfold_links_rec_and_get_variables_term v t] unfolds the links in [t] and returns as well the list 
    of variables contained in the unfolded term [t]. 
    @raise Terms.Unify when [v] occurs in [t]. *)
let unfold_links_rec_and_get_variables_term_and_occur_checks v t = 
  Terms.auto_cleanup (fun () ->
    let t' = unfold_links_rec_and_mark_variables_and_occur_checks v t in
    let vars = !Terms.current_bound_vars in
    (vars,t')
  )
    
let unfold_term_only_if_ground t =
  try 
    let rec loop t = match t with
      | Var { link = TLink t; _ } -> lazy t
      | Var _ -> raise Not_found
      | FunApp(f,args) -> 
          let largs = loop_term_list args in
          lazy (FunApp(f,Lazy.force largs))
      | FAC(f,margs) -> 
          let lmargs = loop_mterm_list f margs in
          lazy (FAC(f,Lazy.force lmargs))
    
    and loop_term_list = function
      | [] -> lazy []
      | (t::q) as l ->
          let lt = loop t in
          let lq = loop_term_list q in
          lazy(
            let t' = Lazy.force lt in
            let q' = Lazy.force lq in
            if t' == t && q = q' then l else t'::q'
          )

    and loop_mterm_list f = function 
      | [] -> lazy [] 
      | ((t,k) :: q) as l -> 
          let lt = loop t in
          let lq = loop_mterm_list f q in
          lazy (
            let t' = Lazy.force lt in
            let q' = Lazy.force lq in
            if q == q' && t == t' then l else add_multiplicity f t' k q'
          )
    in
    Some (Lazy.force (loop t))
  with Not_found -> None

type result_unfold = 
  | Ground of term
  | NotGround of binder list

let unfold_term_only_if_ground_and_get_variables t =
  Terms.auto_cleanup (fun () ->
    let rec loop t = match t with
      | Var { link = TLink t; _ } -> Some (lazy t)
      | Var { link = Marked } -> None
      | Var v -> Terms.link v Marked; None
      | FunApp(f,args) -> 
          let* largs = loop_term_list args in
          Some (lazy (FunApp(f,Lazy.force largs)))
      | FAC(f,margs) -> 
          let* lmargs = loop_mterm_list f margs in
          Some (lazy (FAC(f,Lazy.force lmargs)))
    
    and loop_term_list = function
      | [] -> Some (lazy [])
      | (t::q) as l ->
          let* lt = loop t in
          let* lq = loop_term_list q in
          Some (lazy(
            let t' = Lazy.force lt in
            let q' = Lazy.force lq in
            if t' == t && q = q' then l else t'::q'
          ))

    and loop_mterm_list f = function 
      | [] -> Some (lazy []) 
      | ((t,k) :: q) as l -> 
          let* lt = loop t in
          let* lq = loop_mterm_list f q in
          Some (lazy (
            let t' = Lazy.force lt in
            let q' = Lazy.force lq in
            if q == q' && t == t' then l else add_multiplicity f t' k q'
          ))
    in

    match loop t with
    | None -> NotGround !Terms.current_bound_vars
    | Some lt -> Ground (Lazy.force lt)
  )
  

(***************************
   Operations on variables         
****************************)
  
(** [occurs x t] returns [true] iff [x] is in [t]. *)
let rec occurs x = function
  | Var y -> x == y
  | FunApp(_,args) -> List.exists (occurs x) args
  | FAC(_,margs) -> List.exists (fun (t,_) -> occurs x t) margs 

let rec occurs_check x = function
  | Var { link = TLink t; _} -> occurs_check x t
  | Var y -> if x == y then raise Terms.Unify
  | FunApp(_,args) -> List.iter (occurs_check x) args
  | FAC(_,margs) -> List.iter (fun (t,_) -> occurs_check x t) margs 

(** [get_diff_variables t1 t2] returns the set vars([t1]) \ vars([t2]). *)
let get_diff_variables t1 t2 = 

  let rec go_through_t2 = function
    | Var v when v.link = NoLink -> Terms.link v Marked
    | Var _ -> ()
    | FunApp(_,args) -> List.iter go_through_t2 args
    | FAC(_,args) -> List.iter (fun (t,_) -> go_through_t2 t) args
  in

  let rec go_through_t1 vars = function
    | Var v when v.link = NoLink -> vars := v :: !vars
    | Var _ -> () 
    | FunApp(_,args) -> List.iter (go_through_t1 vars) args
    | FAC(_,args) -> List.iter (fun (t,_) -> go_through_t1 vars t) args
  in

  Terms.auto_cleanup_nocatch (fun () ->
    (** We mark the variables in [t2] *)
    go_through_t2 t2;
    (** Only the unmarked variables appear in [vars] *)
    let vars = ref [] in
    go_through_t1 vars t1;
    !vars
  )

let rec get_variables_aux = function 
  | Var v -> 
      begin match v.link with 
      | NoLink -> Terms.link v Marked
      | Marked -> ()
      | _ -> failwith "[get_variables] Unexpected link"
      end
  | FunApp(_,args) -> List.iter get_variables_aux args
  | FAC(_,margs) -> List.iter (fun (t,_) -> get_variables_aux t) margs

let get_variables t = 
  Terms.auto_cleanup_nocatch (fun () ->
    get_variables_aux t;
    !Terms.current_bound_vars
  )

let get_variables_in_term_list tl = 
  Terms.auto_cleanup_nocatch (fun () ->
    List.iter get_variables_aux tl;
    !Terms.current_bound_vars
  )

let get_variables_in_mterms (mterml:mterm list) = 
  Terms.auto_cleanup_nocatch (fun () ->
    List.iter (fun (t,k) -> get_variables_aux t) mterml;
    !Terms.current_bound_vars
  )

let rec get_variables_and_occur_check_aux v_target = function 
  | Var v -> 
      if v == v_target then raise Terms.Unify;
      begin match v.link with 
      | NoLink -> Terms.link v Marked
      | Marked -> ()
      | _ -> failwith "[get_variables] Unexpected link"
      end
  | FunApp(_,args) -> List.iter (get_variables_and_occur_check_aux v_target) args
  | FAC(_,margs) -> List.iter (fun (t,_) -> get_variables_and_occur_check_aux v_target t) margs

let get_variables_and_occur_check v_target t = 
  Terms.auto_cleanup (fun () ->
    get_variables_and_occur_check_aux v_target t;
    !Terms.current_bound_vars
  )

(** [get_variables_top_variable_and_length mterms] returns a tuple [(vars,b,n)] where 
    [vars] is the list of variables occuring in [mterms], [b] is true iff there is no 
    variable at top level in [mterms] and [n] is the number of terms (counting the
    multiplicity) in [mterms]. *)
let get_variables_top_variable_and_length mterms =
  let no_top_variable = ref true in
  let length = ref 0 in
  Terms.auto_cleanup_nocatch (fun () ->
    List.iter (fun (t,k) ->
     get_variables_aux t;
     length := k + !length;
     no_top_variable := match t with Var _ -> false | _ -> !no_top_variable 
    ) mterms;
    (!Terms.current_bound_vars,!no_top_variable,!length)
  )