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
open Ac_term
open Ac_utils

let time_recorded = ref 0.

(** Unification and matching modulo AC *)

(** Operation on bits *)

(** [int2bin size k] returns a string with the first [size] bits of the binary representation of [k] *)
let int2bin size =
  let buf = Bytes.create size in
  fun n ->
    for i = 0 to size - 1 do
      let pos = size - 1 - i in
      Bytes.set buf pos (if n land (1 lsl i) != 0 then '1' else '0')
    done;
    Bytes.to_string buf

(* Transforms an integer bn ... b1 into bn ... bi+1 bi-1 .. b1 *)
let remove_bit_i bitrep i = 
  let only_one_after_i = (-1 lsl i) in
  let only_one_before_i = -1 lsr (Sys.int_size - i + 1) in
  ((only_one_after_i land bitrep) lsr 1) lor (only_one_before_i land bitrep)

(** Some display functions *)

let display_matrix f_print m = 
  for i = 0 to Array.length m - 1 do 
    for j = 0 to Array.length m.(0) - 1 do
      Printf.printf "%s  " (f_print m.(i).(j))
    done;
    print_string "\n";
  done

let display_vector f_print m = 
  for i = 0 to Array.length m - 1 do 
    Printf.printf "%s  " (f_print m.(i))
  done;
  print_string "\n"

let display_vector_nonewline f_print m = 
  for i = 0 to Array.length m - 1 do 
    Printf.printf "%s  " (f_print m.(i))
  done
  
(* let string_of_subst () =
  List.string_of (fun v -> match v.link with 
    | TLink t -> Printf.sprintf "%s -> %s" (string_of_variable v) (string_of_term (unfold_links_rec t))
    | _ -> internal_error __POS__ "[string_of_subst] Unexpected link."
  ) "{" "}" "; " !current_bound_vars

let rec display_term = function 
  |  Var ({v_link = TLink t ;_} as v) -> print_string "["; display_variable v; print_string "]"; flush_all (); display_term t
  | Var v -> display_variable v
  | FunApp(f,args) -> display_symbol f; List.display display_term "(" ")" "," args
  | FAC(f,margs) -> display_symbol f; List.display (fun (t,k) -> print_string "("; display_term t; Printf.printf ",%d)" k) "(" ")" "," margs

let display_of_subst () =
  List.display (fun v -> match v.v_link with 
    | TLink t -> (display_variable v); print_string " -> "; flush_all (); display_term t
    | _ -> internal_error __POS__ "[string_of_subst] Unexpected link."
  ) "{" "}" "; " !current_bound_vars *)

(* Inequality constraint used to ensure minimality *)

module ConstraintsEquality =
struct

  (** The atomic constraint corresponds to a disjunction of inequalities. [term] are a list of 
      elements [(x,(vars,t))], representing the inequality [x] <> [t]. The term [t] is unfolded (no variable
      are linked) and [vars] is the list of variables in [t]. It is used to optimise checking satisfiability
      of constraints. The elements [(f,margs1,margs2)] in [termAC] is similar and represent the inequality 
      [f(margs1)] <> [f(margs2)] where [f] is an AC symbol. *)
  type disjunction = 
    {
      term : (binder * (binder list * term)) list;
      termAC : (funsymb * (binder list * (term * int) list) * (binder list * (term * int) list)) list
    }

  (** Represents an conjunction of inequality disjunctions. *)
  type t = disjunction list

  (** Display functions *)

  let display_ineq (v,(vars,t)) = 
    display_variable v;
    print_string " <> ";
    List.display display_variable "[" "]" "," vars;
    display_term t

  let display_ineq_AC (f,(vars1,margs1),(vars2,margs2)) =
    List.display display_variable "[" "]" "," vars1;
    display_term_AC false f margs1;
    print_string " <> ";
    List.display display_variable "[" "]" "," vars2;
    display_term_AC false f margs2

  let display_disjunction disj = 
    List.display display_ineq "" "" " || " disj.term;
    if disj.termAC <> [] && disj.term <> [] then print_string " || ";
    List.display display_ineq_AC "" "" " || " disj.termAC

  let display = function 
    | [] -> print_string "true" 
    | [x] -> display_disjunction x
    | cons -> 
        List.display (fun disj ->
          print_string "(";
          display_disjunction disj;
          print_string ")"
        ) "" "" " && " cons

  (** Transformation to string *)

  let string_of_ineq (v,(vars,t)) = 
    Printf.sprintf "%s <> %s%s" 
      (string_of_variable v)
      (List.string_of string_of_variable "[" "]" "," vars)
      (string_of_term t)

  let string_of_ineq_AC (f,(vars1,margs1),(vars2,margs2)) =
    (List.string_of string_of_variable "[" "]" "," vars1) ^
    (string_of_term_AC false f margs1) ^ " <> " ^
    (List.string_of string_of_variable "[" "]" "," vars2) ^
    (string_of_term_AC false f margs2)

  let string_of_disjunction disj = 
    (List.string_of string_of_ineq "" "" " || " disj.term) ^
    (if disj.termAC <> [] && disj.term <> [] then " || " else "") ^
    (List.string_of string_of_ineq_AC "" "" " || " disj.termAC)

  let string_of = function 
    | [] -> "true" 
    | [x] -> string_of_disjunction x
    | cons -> List.string_of (fun disj -> "(" ^ string_of_disjunction disj ^ ")") "" "" " && " cons

  (** Testing function *)

  (** [is_disjunction_false disj] returns true when the disjunction is false. *)
  let is_disjunction_false disj = disj.term = [] && disj.termAC = [] [@@inline]

  (** Creation *)

  (** [weak_unify_on_unfolded_terms term termAC t1 t2] tries to unify the term [t1] [t2] but
    in a very light manner: it only check the syntactic symbols. When reaching AC symbols or
    variables, the equation is stored in [termAC] and [term] respectively. *)
  let rec weak_unify_on_unfolded_terms term termAC t1 t2 = match t1, t2 with
    | Var v1, Var v2 when v1 == v2 -> ()
    | Var v, t 
    | t, Var v -> 
        let vars = get_variables_and_occur_check v t in
        term := (v,(vars,t)) :: !term
    | FunApp(f1,args1), FunApp(f2,args2) ->
        if f1 != f2 then raise Terms.Unify;
        List.iter2 (weak_unify_on_unfolded_terms term termAC) args1 args2
    | FAC(f1,margs1), FAC(f2,margs2) ->
        if f1 != f2 then raise Terms.Unify;
        let (vars1,no_top_variable1,length1) = get_variables_top_variable_and_length margs1 in
        let (vars2,no_top_variable2,length2) = get_variables_top_variable_and_length margs2 in

        (** When the two side do not have top variables, they must have the same multiplicity of
            terms other the two terms cannot be unifiable. *)
        if no_top_variable1 && no_top_variable2 && length1 <> length2 then raise Terms.Unify;

        if not (
            List.for_all2_loose (fun v1 v2 -> v1 == v2) vars1 vars2 &&
            length1 = length2 &&
            List.for_all2_loose (fun (u1,k1) (u2,k2) -> k1 = k2 && equal u1 u2) margs1 margs2
          )
        then 
          (** The terms are differents. When there is no variables, it means that they are not unifiable *)
          if vars1 = [] && vars2 = [] 
          then raise Terms.Unify
          else termAC := (f1,(vars1,margs1),(vars2,margs2)) :: !termAC
    | _ -> raise Terms.Unify 

  (** [create t1 t2] creates the inequality [t1] <> [t2]. It assumes that [t1] and [t2]
      are unfolded, that is no variable in [t1] and [t2] should be linked. 
      When the inequality is always true then it returns [None]. *)
  let create t1 t2 = 
    let term = ref [] in
    let termAC = ref [] in

    try 
      weak_unify_on_unfolded_terms term termAC t1 t2;
      Some { term = !term; termAC = !termAC }
    with Terms.Unify -> None

  (** Simplification *)

  (** Similar to [weak_unify_on_unfolded_terms] but unfold the terms. *)
  let rec weak_unify term termAC t1 t2 = match t1, t2 with
    | Var v1, Var v2 when v1 == v2 -> ()
    | Var { link = TLink t }, t'
    | t', Var { link = TLink t } -> weak_unify term termAC t t'
    | Var v, t 
    | t, Var v -> 
        let vars_term = unfold_links_rec_and_get_variables_term_and_occur_checks v t in
        term := (v,vars_term) :: !term
    | FunApp(f1,args1), FunApp(f2,args2) ->
        if f1 != f2 then raise Terms.Unify;
        List.iter2 (weak_unify term termAC) args1 args2
    | FAC(f1,margs1), FAC(f2,margs2) ->
        if f1 != f2 then raise Terms.Unify;
        let vars1,margs1' = unfold_links_rec_and_get_variables_mterms f1 margs1 in
        let vars2,margs2' = unfold_links_rec_and_get_variables_mterms f1 margs2 in

        if
          (** When implementing with DAG, this condition should be changed into:
            not (List.for_all2_loose (fun (u1,k1) (u2,k2) -> k1 = k2 && u1 == u2) margs1 margs2)
            No need to check the length of [vars1], [vars2] and [margs1'],[margs2']
          *)
          not (
            List.length vars1 = List.length vars2 &&
            List.length margs1' = List.length margs2' &&
            List.for_all2_loose (fun (u1,k1) (u2,k2) -> k1 = k2 && equal u1 u2) margs1' margs2'
          ) 
        then 
          if vars1 = [] && vars2 = [] 
          then raise Terms.Unify
          else termAC := (f1,(vars1,margs1'),(vars2,margs2')) :: !termAC
    | _ -> raise Terms.Unify

  let simplify_mterm f ((vars,margs) as vars_mterm) = 
    if List.exists (fun v -> v.link <> NoLink) vars
    then unfold_links_rec_and_get_variables_mterms f margs
    else 
      (** If no variable have been linked then [mterm] has been modified. *)
      vars_mterm

  let rec simplify_term ineq_to_evaluate disj = match disj with
    | [] -> []
    | ({link = NoLink; _},(vars,_)) as ineq :: q when List.for_all (fun v -> v.link = NoLink) vars ->
        (* The inequality was not changed *)
        let q' = simplify_term ineq_to_evaluate q in
        if q == q'
        then disj
        else (ineq_to_evaluate := ineq :: !ineq_to_evaluate; simplify_term ineq_to_evaluate q)
    | ineq :: q -> 
        ineq_to_evaluate := ineq :: !ineq_to_evaluate;
        simplify_term ineq_to_evaluate q

  let rec simplify_termAC disj = match disj with
    | [] -> []
    | (f,vars_mt1,vars_mt2) as ineq :: q ->
        let (vars1,margs1) as vars_mt1' = simplify_mterm f vars_mt1 in
        let (vars2,margs2) as vars_mt2' = simplify_mterm f vars_mt2 in
        if vars_mt1' == vars_mt1 && vars_mt2' == vars_mt2
        then 
          let q' = simplify_termAC  q in
          if q == q' then disj else ineq :: q'
        else 
          if 
            (** When implementing with DAG, this condition should be changed into:
              not (List.for_all2_loose (fun (u1,k1) (u2,k2) -> k1 = k2 && u1 == u2) margs1 margs2)
              No need to check the length of [vars1], [vars2] and [margs1],[margs2]
            *)
            not (
              List.length vars1 = List.length vars2 &&
              List.length margs1 = List.length margs2 &&
              List.for_all2_loose (fun (u1,k1) (u2,k2) -> k1 = k2 && equal u1 u2) margs1 margs2
            ) 
          then 
            if vars1 = [] && vars2 = []
            then raise Terms.Unify
            else (f,vars_mt1',vars_mt2') :: simplify_termAC q
          else simplify_termAC q
  
  (** [simplify_disjunction disj] returns [None] when the disjunction is true else [Some disj'] where [disj']
      is equivalent to [disj]. *)
  let simplify_disjunction disj = 
    let ineq_to_evaluate = ref [] in

    let term = simplify_term ineq_to_evaluate disj.term in
    let termAC = simplify_termAC disj.termAC in

    if term == disj.term
    then 
      if termAC == disj.termAC 
      then Some disj
      else Some { disj with termAC = termAC }
    else
      (* Need to evaluate some terms *)
      let term_ref = ref term in
      let termAC_ref = ref termAC in
      try 
        List.iter (fun (v,(_,t)) -> 
          weak_unify term_ref termAC_ref (Var v) t
        ) !ineq_to_evaluate; 
        Some { term = !term_ref; termAC = !termAC_ref }
      with Terms.Unify -> None

  let rec simplify consl = match consl with 
    | [] -> []
    | disj :: q ->
        match simplify_disjunction disj with 
        | Some disj' -> 
            if disj == disj'
            then 
              let q' = simplify q in
              if q == q' then consl else disj :: q'
            else 
              if is_disjunction_false disj'
              then raise Terms.Unify
              else disj' :: simplify q
        | None -> simplify q

end

module ConstraintsMatching =
struct
  
  (** The atomic constraint corresponds to a disjunction of distmatch. [term] are a list of 
    elements [(x,t)], representing the dismatchquality [x] !<= [t]. The term [t] may contain variables but they 
    are never linked (as they are considered constant). In the elements [(f,varsmargs1,margs2)] in [termAC] 
    each elements of [varsmargs1] is a tuple [(vars,t,k)] where [vars] are the variables of [t]. If 
    [varsmargs1] is the list [(vars1,t1,k1);...;(varsn,tn,kn)] then [(f,varsmargs1,margs2)] represents the 
    dismatch [f(margs1) !<= f(margs2)]. *)
  type disjunction = 
    {
      term : (binder * term) list;
      termAC : (funsymb * (binder list * term * int) list * (term * int) list) list
    }

  type t = disjunction list

  (** Display functions *)

  let display_dismatch (v,t) = 
    display_variable v;
    print_string " !<= ";
    display_term t

  let display_dismatch_AC (f,varsmargs1,margs2) =
    let vars_list,margs1 = List.fold_right (fun (vars,t,k) (acc_v,acc_a) -> (vars::acc_v,(t,k)::acc_a)) varsmargs1 ([],[]) in
    List.display (List.display display_variable "[" "]" ",") "[" "]" "," vars_list;
    display_term_AC false f margs1;
    print_string " !<= ";
    display_term_AC false f margs2

  let display_disjunction disj = 
    List.display display_dismatch "" "" " || " disj.term;
    if disj.termAC <> [] && disj.term <> [] then print_string " || ";
    List.display display_dismatch_AC "" "" " || " disj.termAC

  let display = function 
    | [] -> print_string "true" 
    | [x] -> display_disjunction x
    | cons -> 
        List.display (fun disj ->
          print_string "(";
          display_disjunction disj;
          print_string ")"
        ) "" "" " && " cons

  (** Transformation to string *)

  let string_of_dismatch (v,t) = 
    string_of_variable v ^ " !<= " ^ string_of_term t

  let string_of_dismatch_AC (f,varsmargs1,margs2) =
    let vars_list,margs1 = List.fold_right (fun (vars,t,k) (acc_v,acc_a) -> (vars::acc_v,(t,k)::acc_a)) varsmargs1 ([],[]) in
    List.string_of (List.string_of string_of_variable "[" "]" ",") "[" "]" "," vars_list ^
    string_of_term_AC false f margs1 ^ " !<= " ^ string_of_term_AC false f margs2

  let string_of_disjunction disj = 
    (List.string_of string_of_dismatch "" "" " || " disj.term) ^
    (if disj.termAC <> [] && disj.term <> [] then " || " else "") ^
    (List.string_of string_of_dismatch_AC "" "" " || " disj.termAC)

  let string_of = function 
    | [] -> "true" 
    | [x] -> string_of_disjunction x
    | cons -> List.string_of (fun disj -> "(" ^ string_of_disjunction disj ^ ")") "" "" " && " cons
  
  (** Creation of constraint *)

  (** [filter_mterm_list t k mtl] removes from [mtl] [k] occurences of [t]. 
      @raise Terms.Unify when [t] does not occur [k] times in [mtl]. *)
  let rec filter_mterm_list t k mterm_list = match mterm_list with
    | [] -> raise Terms.Unify
    | (t',k') :: q ->
        match compare_term t t' with
        | 0 -> 
            if k > k' then raise Terms.Unify
            else if k = k' then q
            else (t',k'-k) :: q
        | -1 -> raise Terms.Unify
        | _ -> (t',k') :: filter_mterm_list t k q

  (** [filter_mterm_lists f mtl1 mtl2] returns [(mtl1',mtl2')] where [mtl2'] is obtained from 
    [mtl2] by removing from it all constant terms of [mtl1] (considering their multiplicity).
    [mtl1'] is obtained from [mlt1'] by removing all its constants.
    @raise Terms.Unify when some constants of [mtl1] does not occur the same number of times in [mtl2]. *)
  let rec filter_mterm_lists f mterm_list1 mterm_list2 = match mterm_list1 with
    | [] -> [], mterm_list2
    | (t,k) :: q ->
        match unfold_term_only_if_ground_and_get_variables t with
        | Ground (FAC(g,margs)) when f == g -> 
            let mterm_list2' = 
              List.fold_left (fun acc (t',k') ->
                filter_mterm_list t' k' acc
              ) mterm_list2 margs
            in
            filter_mterm_lists f q mterm_list2'
        | Ground t' -> filter_mterm_lists f q (filter_mterm_list t' k mterm_list2)
        | NotGround vars -> 
            let (varsmterm_list1' , q') = filter_mterm_lists f q mterm_list2 in
            (vars,t,k) :: varsmterm_list1', q'

  (** [weak_match] tries to match the term [t1] [t2] but in a very light manner: it mostly only check the 
      syntactic symbols. When reaching an AC it remove terms that are constant (in the sense of matching)
      on the left if they appear on the right side (taking into account multiplicity). *)
  let rec weak_match term termAC t1 t2 = match t1, t2 with
    | Var { link = TLink t1' }, _ -> if not (equal t1' t2) then raise Terms.Unify
    | Var v, _ -> term := (v,t2) :: !term
    | FunApp(f1,args1), FunApp(f2,args2) -> 
        if f1 != f2 then raise Terms.Unify;
        List.iter2 (weak_match term termAC) args1 args2
    | FAC(f1,margs1), FAC(f2,margs2) ->
        if f1 != f2 then raise Terms.Unify;
        let varsmargs1',margs2' = filter_mterm_lists f1 margs1 margs2 in
        if (varsmargs1' = [] && margs2' <> []) || (varsmargs1' <> [] && margs2' = [])
        then raise Terms.Unify
        else termAC := (f1,varsmargs1',margs2') :: !termAC
    | _ -> raise Terms.Unify

  let create t1 t2 =
    let term = ref [] in
    let termAC = ref [] in
    try
      weak_match term termAC t1 t2;
      Some { term = !term; termAC = !termAC }
    with Terms.Unify -> None

  (** Simplification *)

  let rec filter_mterm_lists_only_bounded_variable varsmterm_list1 mterm_list2 = match varsmterm_list1 with
    | [] -> [], mterm_list2
    | (vars,t,k) :: q ->
        (** We only try to filter when all the variable are linked. Otherwise, we leave it as it is.. *)
        if List.for_all (fun v -> v.link <> NoLink) vars
        then filter_mterm_lists_only_bounded_variable q (filter_mterm_list (unfold_links_non_rec t) k mterm_list2)
        else 
          let (q',mterm_list2') = filter_mterm_lists_only_bounded_variable q mterm_list2 in
          if q == q'
          then varsmterm_list1, mterm_list2
          else (vars,t,k) :: q', mterm_list2'

  let simplify_disjunction disj = 
    try 
      let term = 
        List.filterq (fun (v,t) -> match v.link with
          | NoLink -> true
          | TLink t' -> 
              if not (equal t' t) then raise Terms.Unify;
              false
          | _ -> internal_error __POS__ "Unexpected link"
        ) disj.term
      in

      let termAC = 
        List.filterq (fun (f,varsterms1,mterms2) ->
            let varsterms1', mterms2' = filter_mterm_lists_only_bounded_variable varsterms1 mterms2 in
            match varsterms1' = [], mterms2' = [] with
            | true, true -> false
            | true, false | false, true -> raise Terms.Unify
            | _ -> true
        ) disj.termAC
      in

      if term == disj.term && termAC == disj.termAC
      then Some disj
      else Some { term = term; termAC = termAC }
    with Terms.Unify -> None 

  let rec simplify consl = match consl with 
    | [] -> []
    | disj :: q ->
        match simplify_disjunction disj with 
        | Some disj' -> 
            if disj == disj'
            then 
              let q' = simplify q in
              if q == q' then consl else disj :: q'
            else 
              if disj'.termAC = [] &&  disj'.term = []
              then raise Terms.Unify
              else disj' :: simplify q
        | None -> simplify q

end

module HullotTree =
struct

  (* The algorithm for detecting cycles (occurrence checks)*)

  type status =
    | NotVisited
    | Visited
    | Finished

  type vertex = 
  {
    mutable status : status;
    successors : (int (* Index *) * int (** Bit representation *)) list
  }

  type occurence_data = 
  {
    vertex_tbl: vertex Array.t;
    roots: int (** Index *) list
  }

  let display_occurrence_data nb_solutions occur_data = 
    Printf.printf "*** Occurrrence data:\n";
    Printf.printf "Roots: %s\n" (List.string_of string_of_int "" "" "; " occur_data.roots);
    Printf.printf "Vertex_tbl:\n";
    Array.iteri (fun i vertex ->
      Printf.printf "  %d -> %s\n" i (List.string_of (fun (j,bit_trans) -> Printf.sprintf "(%d,%s)" j (int2bin nb_solutions bit_trans)) "[" "]" " -- " vertex.successors) 
    ) occur_data.vertex_tbl

  (** [check_no_cycle occur_data subset_bits] verifies that there is no cycle
      in the  subset represented by [subset_bits]. The actual transitions in 
      the graph corresponding to [subset_bits] are all the successors [(i,repr_bits)]
      in [occur_data] such that [subset_bits land repr_bits <> 0]. *)
  let check_no_cycle occur_data subset_bits =

    let rec dfs idx = 
      let vertex = occur_data.vertex_tbl.(idx) in
      match vertex.status with 
      | Finished -> ()
      | Visited -> raise Terms.Unify
      | NotVisited ->
          vertex.status <- Visited;
          List.iter (fun (idx,repr_bits) ->
            if subset_bits land repr_bits <> 0
            then dfs idx
          ) vertex.successors;
          vertex.status <- Finished
    in

    try 
      List.iter dfs occur_data.roots;
      List.iter (fun idx -> occur_data.vertex_tbl.(idx).status <- NotVisited) occur_data.roots;
      true
    with Terms.Unify -> 
      List.iter (fun idx -> occur_data.vertex_tbl.(idx).status <- NotVisited) occur_data.roots;
      false

  (** Depth first search of Hullot trees *)
  
  (** [dfs f n all_bits constrants_bits occur_data_opt] explores the Hullot tree in a depth-first manner.
    When [occur_data_opt=None], it do occurrence checks. *)
  let dfs f_next n all_bits constants_bits occur_data_opt =
    let init_full_one = -1 lsr (Sys.int_size - n) in

    let check_occur = match occur_data_opt with 
      | None -> (fun _ -> true)
      | Some occur_data -> (fun subset_bits -> check_no_cycle occur_data subset_bits)
    in
    
    let big_enough subset_bits = 
      List.for_all (fun vi -> subset_bits land vi <> 0) all_bits
    in
    let small_enough subset_bits = 
      List.for_all (fun vi -> (subset_bits land vi) land ((subset_bits land vi) -1) = 0) constants_bits &&
      check_occur subset_bits
    in

    (* When [sign_greater = true], it corresponds to >. *)
    let rec dfs next_dfs pre a k sign_greater = 
      let subset_bits, test = 
        if sign_greater 
        then pre lor a, big_enough (pre lor a)
        else pre, small_enough pre 
      in
      if test
      then 
        if k = 0
        then f_next next_dfs subset_bits
        else 
          let a' = a lsr 1 in
          dfs (fun () -> 
            dfs next_dfs (pre lor (a lxor a')) a' (k-1) false
          ) pre a' (k-1) true
      else next_dfs () 
    in

    dfs (fun () -> raise Terms.Unify) 0 init_full_one n true 

  (** DFS with constraint manipulation *)

  let rec putting_constraints subset_bits current_constraint_ref constraints_to_add = match constraints_to_add with
    | [] -> constraints_to_add
    | (cons,bitrepr) as consbit ::q -> 
        let constraints_to_add' = putting_constraints subset_bits current_constraint_ref q in
        if subset_bits land bitrepr = 0
        then 
          begin
            current_constraint_ref := cons :: !current_constraint_ref;
            constraints_to_add'
          end
        else
          if constraints_to_add' == q
          then constraints_to_add
          else consbit :: constraints_to_add'

  let rec filter_constraints subset_bits constraints_to_add = match constraints_to_add with
    | [] -> constraints_to_add
    | (_,bitrepr) as consbit ::q -> 
        let constraints_to_add' = filter_constraints subset_bits q in
        if subset_bits land bitrepr <> 0
        then constraints_to_add'
        else 
          if constraints_to_add' == q
          then constraints_to_add
          else consbit :: constraints_to_add'
    
  let dfs_with_constraint_check f_next current_constraints n all_bits constants_bits occur_data_opt constraints_to_add =
    let init_full_one = -1 lsr (Sys.int_size - n) in

    let check_occur = match occur_data_opt with 
      | None -> (fun _ -> true)
      | Some occur_data -> (fun subset_bits -> check_no_cycle occur_data subset_bits)
    in
    
    let big_enough subset_bits = 
      List.for_all (fun vi -> subset_bits land vi <> 0) all_bits
    in
    let small_enough subset_bits = 
      List.for_all (fun vi -> (subset_bits land vi) land ((subset_bits land vi) -1) = 0) constants_bits &&
      check_occur subset_bits
    in

    (* When [sign_greater = true], it corresponds to >. *)
    let rec dfs next_dfs current_constraint constraints_to_add pre a k sign_greater = 
      (* Printf.printf "Dfs pre = %s, a = %s, k = %d, sign_greater = %b\n" (int2bin n pre) (int2bin n a) k sign_greater; *)
      let subset_bits, test = 
        if sign_greater 
        then pre lor a, big_enough (pre lor a)
        else pre, small_enough pre 
      in
      if test
      then 
        if k = 0
        then f_next next_dfs current_constraint subset_bits
        else 
          let a' = a lsr 1 in
          if sign_greater
          then 
            let current_constraint_ref = ref current_constraint in
            let constraints_to_add' = putting_constraints subset_bits current_constraint_ref constraints_to_add in
            let current_constraint' = !current_constraint_ref in
            dfs (fun () -> 
              dfs next_dfs current_constraint' constraints_to_add' (pre lor (a lxor a')) a' (k-1) false
            ) current_constraint' constraints_to_add' pre a' (k-1) true
          else
            let constraints_to_add' = filter_constraints subset_bits constraints_to_add in
            dfs (fun () -> 
              dfs next_dfs current_constraint constraints_to_add' (pre lor (a lxor a')) a' (k-1) false
            ) current_constraint constraints_to_add' pre a' (k-1) true
      else next_dfs () 
    in
  
    dfs (fun () -> raise Terms.Unify) current_constraints constraints_to_add 0 init_full_one n true
  
end

module MatrixGeneration = struct
    
  (* Should be improved when the terms will be DAG *)
  type t = 
    {
      mutable vars: (binder * int Array.t (* Coeffs *)) list;
      mutable nb_vars: int;
      mutable constants: (term * bool (* Is ground when true *) * (int list * int) (* Occur variables *) * int Array.t (* Coeffs *)) list;
      mutable nb_constants: int;
      nb_equations: int
    }

  type t_match = 
    {
      mutable vars_m: (binder * int Array.t (* Coeffs *)) list;
      mutable nb_vars_m: int;
      mutable term_with_vars_m : (term * int Array.t (* Coeffs *)) list;
      mutable term_constants_m : (term * int Array.t (* Coeffs *)) list;
      mutable nb_non_vars_terms_m: int;
      nb_equations_m: int
    }

  let display storage = 
    Printf.printf "Storage:\n";
    Printf.printf "  Vars = \n";
    List.iter (fun (v,coeffs) -> Printf.printf "    %s with coeff = " (string_of_variable v); display_vector string_of_int coeffs) storage.vars;
    Printf.printf "  Nb_vars = %d\n" storage.nb_vars;
    Printf.printf "  Constants = \n";
    List.iter (fun (t,ground,occur,coeffs) -> 
      Printf.printf "    %s with ground=%b, occur = (%s,%s) and coeff = " 
        (string_of_term t)
        ground
        (List.string_of string_of_int "[" "]" "," (fst occur))
        (int2bin storage.nb_vars (snd occur))
      ; 
      display_vector string_of_int coeffs
    ) storage.constants;
    Printf.printf "  Nb_constants = %d\n" storage.nb_constants;
    Printf.printf "  Nb_equations = %d\n" storage.nb_equations;
    flush_all ()

  let display_match storage = 
    Printf.printf "Storage:\n";
    Printf.printf "  Vars = \n";
    List.iter (fun (v,coeffs) -> Printf.printf "    %s with coeff = " (string_of_variable v); display_vector string_of_int coeffs) storage.vars_m;
    Printf.printf "  Nb_vars = %d\n" storage.nb_vars_m;
    Printf.printf "  Term_constants_m = \n";
    List.iter (fun (t,coeffs) -> 
      Printf.printf "    %s with coeff = " 
        (string_of_term t)
      ; 
      display_vector string_of_int coeffs
    ) storage.term_constants_m;
      Printf.printf "  term_with_vars_m = \n";
      List.iter (fun (t,coeffs) -> 
        Printf.printf "    %s with coeff = " 
          (string_of_term t)
        ; 
        display_vector string_of_int coeffs
      ) storage.term_with_vars_m;
    Printf.printf "  nb_non_vars_terms_m = %d\n" storage.nb_non_vars_terms_m;
    Printf.printf "  Nb_equations = %d\n" storage.nb_equations_m;
    flush_all ()

  let create nb_equations = 
    {
      vars = [];
      nb_vars = 0;
      constants = [];
      nb_constants = 0;
      nb_equations = nb_equations
    }

  let create_match nb_equations = 
    {
      vars_m = [];
      nb_vars_m = 0;
      term_with_vars_m = [];
      term_constants_m = [];
      nb_non_vars_terms_m = 0;
      nb_equations_m = nb_equations
    }

  let add_variable store ith_eq v k = 
    let rec loop list_variables = match list_variables with
      | [] -> 
          (* The variable is greater than all *)
          let coeffs = Array.make store.nb_equations 0 in
          coeffs.(ith_eq) <- k;
          store.nb_vars <- store.nb_vars + 1;
          [v,coeffs]
      | ((v',coeffs') as v_coeff)::q_vars ->
          match compare_variable v v' with
          | 0 -> 
              coeffs'.(ith_eq) <- coeffs'.(ith_eq) + k;
              list_variables
          | -1 -> 
              (* The variable was not recorded *)
              let coeffs = Array.make store.nb_equations 0 in
              coeffs.(ith_eq) <- k;
              store.nb_vars <- store.nb_vars + 1;
              (v,coeffs) :: list_variables
          | _ -> v_coeff :: loop q_vars
    in
    store.vars <- loop store.vars

  let add_variable_match store ith_eq v k = 
    let rec loop list_variables = match list_variables with
      | [] -> 
          (* The variable is greater than all *)
          let coeffs = Array.make store.nb_equations_m 0 in
          coeffs.(ith_eq) <- k;
          store.nb_vars_m <- store.nb_vars_m + 1;
          [v,coeffs]
      | ((v',coeffs') as v_coeff)::q_vars ->
          match compare_variable v v' with
          | 0 -> 
              coeffs'.(ith_eq) <- coeffs'.(ith_eq) + k;
              list_variables
          | -1 -> 
              (* The variable was not recorded *)
              let coeffs = Array.make store.nb_equations_m 0 in
              coeffs.(ith_eq) <- k;
              store.nb_vars_m <- store.nb_vars_m + 1;
              (v,coeffs) :: list_variables
          | _ -> v_coeff :: loop q_vars
    in
    store.vars_m <- loop store.vars_m  

  let add_constant store t is_ground occur_vars ith_eq k = 
    let rec loop list_constants = match list_constants with
      | [] -> 
          (* The constant is greater than all *)
          let coeffs = Array.make store.nb_equations 0 in
          coeffs.(ith_eq) <- k;
          store.nb_constants <- store.nb_constants + 1;
          [t,is_ground,occur_vars,coeffs]
      | ((t',_,_,coeffs') as t_coeff)::q_const ->
          match compare_term t t' with
          | 0 -> 
              coeffs'.(ith_eq) <- coeffs'.(ith_eq) + k;
              list_constants
          | -1 -> 
              (* The variable was not recorded *)
              let coeffs = Array.make store.nb_equations 0 in
              coeffs.(ith_eq) <- k;
              store.nb_constants <- store.nb_constants + 1;
              (t,is_ground,occur_vars,coeffs) :: list_constants
          | _ -> t_coeff :: loop q_const
    in
    store.constants <- loop store.constants

  let rec add_term store ith_eq t k list_term = match list_term with
    | [] -> 
        (* The constant is greater than all *)
        let coeffs = Array.make store.nb_equations_m 0 in
        coeffs.(ith_eq) <- k;
        store.nb_non_vars_terms_m <- store.nb_non_vars_terms_m + 1;
        [t,coeffs]
    | ((t',coeffs') as t_coeff)::q_const ->
        match compare_term t t' with
        | 0 -> 
            coeffs'.(ith_eq) <- coeffs'.(ith_eq) + k;
            list_term
        | -1 -> 
            (* The variable was not recorded *)
            let coeffs = Array.make store.nb_equations_m 0 in
            coeffs.(ith_eq) <- k;
            store.nb_non_vars_terms_m <- store.nb_non_vars_terms_m + 1;
            (t,coeffs) :: list_term
        | _ -> t_coeff :: add_term store ith_eq t k q_const

  let add_constant_match store ith_eq t k = 
    store.term_constants_m <- add_term store ith_eq t k store.term_constants_m

  let add_term_with_variables_match store ith_eq t k = 
    store.term_with_vars_m <- add_term store ith_eq t k store.term_with_vars_m

  (* type link+= ILink of int *)

  let filter_index_bool bool_ar = 
    let p = ref 0 in
    let rec loop acc i_repr = function
      | -1 -> acc, !p
      | i -> 
          if bool_ar.(i)
          then 
            begin 
              p := !p lor i_repr; 
              loop (i::acc) (i_repr lsl 1) (i-1)
            end
          else loop acc (i_repr lsl 1) (i-1)
    in
    loop [] 1 (Array.length bool_ar - 1)

  let unfold_term_with_occur_vars nb_variables t =
    let ground = ref true in
    let occur_variables = Array.make nb_variables false in

    let rec loop t = match t with
      | Var { link = TLink t; _ } -> loop t
      | Var { link = ILink j; _ } ->
          occur_variables.(j) <- true;
          ground := false;
          t
      | Var _ -> ground := false; t
      | FunApp(f,args) -> 
          let args' = List.mapq loop args in
          if args == args' then t else FunApp(f,args')
      | FAC(f,margs) -> 
          let margs' = 
            List.mapq (fun ((t,k) as pair)-> 
              let t' = loop t in
              if t == t' then pair else (t',k)
            ) margs
          in
          if margs' == margs then t else FAC(f,margs') 
    in

    let t_unfolded = loop t in
    !ground, filter_index_bool occur_variables, t_unfolded

  let cleanup_variables store = 
    let rec loop = function 
      | [] -> []
      | (_,coeffs) as v_data ::q ->
          if Array.for_all (fun i -> i = 0) coeffs
          then 
            begin 
              store.nb_vars <- store.nb_vars - 1;
              loop q
            end
          else v_data :: loop q
    in
    store.vars <- loop store.vars

  let cleanup_constants store = 
    let rec loop = function 
      | [] -> []
      | ((_,_,_,coeffs) as t_data) ::q ->
          if Array.for_all (fun i -> i = 0) coeffs
          then 
            begin 
              store.nb_constants <- store.nb_constants - 1;
              loop q
            end
          else t_data :: loop q
    in
    store.constants <- loop store.constants

  let cleanup_constants_match store = 
    let rec loop = function 
      | [] -> []
      | ((_,coeffs) as t_data) ::q ->
          if Array.for_all (fun i -> i = 0) coeffs
          then 
            begin 
              store.nb_non_vars_terms_m <- store.nb_non_vars_terms_m - 1;
              loop q
            end
          else t_data :: loop q
    in
    store.term_constants_m <- loop store.term_constants_m

  let cleanup_equations matrix = 
    let empty_equations = ref [] in
    let count_empty_eq = ref 0 in

    for i = 0 to Array.length matrix - 1 do

      if Array.for_all (fun k -> k = 0) matrix.(i)
      then (empty_equations := i :: !empty_equations; incr count_empty_eq)
      else
        let opposite_sign = ref None in
        if not (Array.exists (fun k -> match !opposite_sign with 
          | None when k = 0 -> false
          | None -> if k <> 0 then opposite_sign := Some (k>0); false
          | Some prev -> (prev && k < 0) || (not prev && k > 0)
          ) matrix.(i))
        then raise Terms.Unify
    done;

    if !empty_equations <> []
    then 
      let new_matrix = Array.make (Array.length matrix - !count_empty_eq) matrix.(0) in
      let rec loop i new_i = function 
        | [] -> for j = 0 to Array.length matrix - 1 - i do new_matrix.(new_i+j) <- matrix.(i+j) done
        | j::q when i = j -> loop (i+1) new_i q
        | l -> 
            new_matrix.(new_i) <- matrix.(i); 
            loop (i+1) (new_i+1) l
      in
      loop 0 0 (List.rev !empty_equations);
      new_matrix
    else matrix

  let from_unification_equations f_AC system_equations = 
    if system_equations = []
    then internal_error __POS__ "[MatrixGeneration.from_unification_equations] The system of equations should not be empty";

    let store = create (List.length system_equations) in

    (* Unfold variables and F_AC *)
    let system_equations = 
      List.map (fun (left_l,right_l) ->
        let new_left_l = ref [] in
        let new_right_l = ref [] in 
        List.iter (unfold_links_rec_only_AC f_AC new_left_l) left_l;
        List.iter (unfold_links_rec_only_AC f_AC new_right_l) right_l;
        !new_left_l,!new_right_l
      ) system_equations
    in

    let non_variable_terms = ref [] in

    (* Add only variables *)
    List.iteri (fun i (left_eq,right_eq) ->
      List.iter (function (t,k) -> match t with
        | Var v -> add_variable store i v k
        | t -> non_variable_terms := (i,t,k) :: !non_variable_terms
      ) left_eq;
      List.iter (function (t,k) -> match t with
        | Var v -> add_variable store i v (-k)
        | t -> non_variable_terms := (i,t,-k) :: !non_variable_terms
      ) right_eq;
    ) system_equations;

    cleanup_variables store;

    Terms.auto_cleanup_nocatch (fun () ->
      (* Link the variables *)
      List.iteri (fun i (v,_) -> Terms.link v (ILink i)) store.vars;

      let nb_variables = store.nb_vars in
        
      (* Add terms *)
      List.iter (fun (ith_eq,t,k) ->
        let (is_ground,occur_vars,t_unfolded) = unfold_term_with_occur_vars nb_variables t in
        add_constant store t_unfolded is_ground occur_vars ith_eq k
      ) !non_variable_terms;

      cleanup_constants store
    );

    let matrix = Array.make_matrix store.nb_equations (store.nb_constants + store.nb_vars) 0 in
    let variables = Array.make store.nb_vars dummy_var in
    let constants = Array.make store.nb_constants dummy in
    let occur_variables = Array.make store.nb_constants ([],0) in
    let ground_constants_status = Array.make store.nb_constants None in

    (* Register the variables *)
    List.iteri (fun j (v,coeffs) ->
      variables.(j) <- v;
      Array.iteri (fun i k ->
        matrix.(i).(store.nb_constants+j) <- k
      ) coeffs  
    ) store.vars;

    (* Register the constants *)
    List.iteri (fun j (t,is_ground,occur_vars,coeffs) ->
      constants.(j) <- t;
      occur_variables.(j) <- occur_vars;
      if not is_ground then ground_constants_status.(j) <- Some (ref dummy);
      Array.iteri (fun i k ->
        matrix.(i).(j) <- k
      ) coeffs  
    ) store.constants;

    (cleanup_equations matrix,variables,constants,occur_variables,ground_constants_status)

  let from_matching_equations f_AC system_equations =
    if system_equations = []
    then internal_error __POS__ "[MatrixGeneration.from_matching_equations] The system of equations should not be empty";

    let store = create_match (List.length system_equations) in

    (* As we have matching equations, the right hand side is considered as ground term. *)

    (* Add only variables on the left and the terms (as constant) on the right*)
    List.iteri (fun i (left_eq,right_eq) ->
      List.iter (fun (t,k) -> 
        unfold_no_rec_only_AC f_AC (fun (t',k') -> (* The term may contain variable *)
          match unfold_term_only_if_ground t' with
          | Some t'' -> (* The term is ground in a the matching sense *)
              add_constant_match store i t'' k
          | None -> (* The term is not ground in the matching sense *)
              match t' with 
              | Var v -> add_variable_match store i v k
              | _ -> add_term_with_variables_match store i t' k
        ) (fun (t',k') -> (* The term is a constant *)
          add_constant_match store i t' k'
        ) (t,k);
      ) left_eq;
      List.iter (fun (t,k) -> add_constant_match store i t (-k)) right_eq
    ) system_equations;

    cleanup_constants_match store;

    let matrix = Array.make_matrix store.nb_equations_m (store.nb_non_vars_terms_m + store.nb_vars_m) 0 in
    let variables = Array.make store.nb_vars_m dummy_var in
    let constants = Array.make store.nb_non_vars_terms_m dummy in
    let ground_constants_status = Array.make store.nb_non_vars_terms_m None in

    (* Register the variables *)
    List.iteri (fun j (v,coeffs) ->
      variables.(j) <- v;
      Array.iteri (fun i k ->
        matrix.(i).(store.nb_non_vars_terms_m+j) <- k
      ) coeffs  
    ) store.vars_m;

    let idx_constant = ref 0 in
  
    (* Register the constants in the match sense *)
    List.iter (fun (t,coeffs) ->
      constants.(!idx_constant) <- t;
      Array.iteri (fun i k ->
        matrix.(i).(!idx_constant) <- k
      ) coeffs;
      incr idx_constant
    ) store.term_constants_m;

    let first_idx_non_ground_term = !idx_constant in

    (* Register the term with variables in the match sense *)
    List.iter (fun (t,coeffs) ->
      constants.(!idx_constant) <- t;
      ground_constants_status.(!idx_constant) <- Some (ref dummy);
      Array.iteri (fun i k ->
        matrix.(i).(!idx_constant) <- k
      ) coeffs;
      incr idx_constant
    ) store.term_with_vars_m;

    (cleanup_equations matrix,variables,first_idx_non_ground_term,constants,ground_constants_status)

end 

let rec mark_redundant_hyp_variables = function
  | Var v ->
      begin match v.link with
        | TLink _ -> raise Terms.Unify
        | VLink _ -> ()
        | NoLink -> Terms.link v (VLink v)
        | _ -> Parsing_helper.internal_error "[AC_unify.ml >> mark_variables] Unexpected links"
      end
  | FunApp(_,args) -> List.iter mark_redundant_hyp_variables args
  | FAC(_,margs) -> List.iter (fun (t,_) -> mark_redundant_hyp_variables t) margs


module DiophantineSolutions = struct
  type t_unfrozen = 
    {
      elts: (int Array.t list) Array.t;
      mutable nb_elts: int;
    }

  type t_frozen =
    {
      elts_f: (((int * bool) Array.t * int Array.t) list) Array.t;
      mutable nb_elts_f: int
    }

  type t = 
    {
      elts_t: (int Array.t Array.t) Array.t;
      associated_variables: term Array.t;   (** The fresh variables associated to the solutions that do not contain constants.
        We should have [Array.length associated_variables = Array.length elts.(nb_constants)]. They should also be all
        greater than the constant term in term of [Flattened.compare]. *)
      nb_elts_t: int;     (** Total number of solutions *)
      nb_constants: int;  (** Number of constants in the initial problem *)
      nb_variables: int;  (** Number of variables in the initial problem *)
    }

  let display_unfrozen store =
    let count = ref 0 in
    Array.iteri (fun i elt ->
      if i = Array.length store.elts - 1
      then 
        begin 
          Printf.printf "- Variables :\n";
          List.iteri (fun j sol ->
            Printf.printf "  Solution %d (local = %d): " !count j;
            display_vector string_of_int sol;
            incr count
          ) elt
        end
      else
        begin 
          Printf.printf "- Constant %d:\n" i;
          List.iteri (fun j sol ->
            Printf.printf "  Solution %d (local = %d): " !count j;
            display_vector string_of_int sol;
            incr count
          ) elt
        end
    ) store.elts 

  let display_t_frozen store = 
    Array.iteri (fun i elt ->
      if i = Array.length store.elts_f - 1
      then 
        begin 
          Printf.printf "- Variables :\n";
          List.iter (fun (sol,defect) ->
            print_string "Sol ";
            display_vector_nonewline (fun (k,b) -> Printf.sprintf "(%d,%b)" k b) sol;
            print_string " with defect ";
            display_vector string_of_int defect;
          ) elt
        end
      else
        begin 
          Printf.printf "- Constant %d:\n" i;
          List.iter (fun (sol,defect) ->
            print_string "Sol ";
            display_vector_nonewline (fun (k,b) -> Printf.sprintf "(%d,%b)" k b) sol;
            print_string " with defect ";
            display_vector string_of_int defect;
          ) elt
        end
    ) store.elts_f

  let display store =
    let count = ref 0 in
    Array.iteri (fun i elt ->
      if i = store.nb_constants
      then 
        begin 
          Printf.printf "- Variables :\n";
          Array.iteri (fun j sol ->
            Printf.printf "  Solution %d (local = %d) with associated vars = %s: " !count j (string_of_term store.associated_variables.(j));
            display_vector string_of_int sol;
            incr count
          ) elt
        end
      else
        begin 
          Printf.printf "- Constant %d:\n" i;
          Array.iteri (fun j sol ->
            Printf.printf "  Solution %d (local = %d): " !count j;
            display_vector string_of_int sol;
            incr count
          ) elt
        end
    ) store.elts_t

  let create nb_constant = { elts = Array.make (nb_constant+1) []; nb_elts = 0 } 
  let create_frozen nb_constant = { elts_f = Array.make (nb_constant+1) []; nb_elts_f = 0 } 

  let add storage idx sol = 
    storage.elts.(idx) <- sol::storage.elts.(idx);
    storage.nb_elts <- succ storage.nb_elts

  let add_frozen storage idx sol = 
    storage.elts_f.(idx) <- sol::storage.elts_f.(idx);
    storage.nb_elts_f <- succ storage.nb_elts_f

  let iter_frozen f storage_frozen = 
    Array.iteri (fun idx sol_list ->
      List.iter (f idx) sol_list
    ) storage_frozen.elts_f
  
  let for_all f storage = 
    Array.for_all (fun sols ->
      List.for_all f sols
    ) storage.elts

  (* Add the content of store2 in store1 *)
  let merge store1 store2 = 
    store1.nb_elts <- store1.nb_elts + store2.nb_elts;
    Array.iteri (fun i sols2 ->
      store1.elts.(i) <- List.rev_append sols2 store1.elts.(i)
    ) store2.elts

  (** Convert the unfrozen solutions into solutions *)
  let finalize nb_constants nb_variables storage = 
    let elts = Array.map (fun l -> Array.of_list l) storage.elts in
    let nb_assoc_variables = Array.length elts.(nb_constants) in
    let associated_variables = Array.make nb_assoc_variables dummy in
    for i = 0 to nb_assoc_variables - 1 do 
      associated_variables.(i) <- Var (Terms.new_var_def Param.bitstring_type)
    done;
    {
      elts_t = elts;
      associated_variables = associated_variables;
      nb_elts_t = storage.nb_elts;
      nb_constants = nb_constants;
      nb_variables = nb_variables
    }

  (** Generation of bitvectors of a variables/constants.
    When Solultions = { s_1, ..., s_p }, the bitvector of x of index i in solutions
    are b_1...b_p where b_j = 1 iff s_j(i) <> 0.
  *)
  let generate_bitvectors_of_variable storage idx = 
    let p = ref 0 in
    for i = 0 to Array.length storage.elts_t - 1 do
      for j = 0 to Array.length storage.elts_t.(i) - 1 do 
        let p' = !p lsl 1 in
        p := if storage.elts_t.(i).(j).(idx) <> 0 then succ p' else p'
      done
    done;
    !p

  let generate_bitvector_of_all_constants ground_constants_status storage =
    let rec loop nb_remaing_solutions idx =
      if idx = storage.nb_constants
      then []
      else
        if ground_constants_status.(idx) = None
        then
          let nb_solution_of_constant_idx = Array.length storage.elts_t.(idx) in
          let nb_remaing_solutions = nb_remaing_solutions - nb_solution_of_constant_idx in
          ((-1 lsr (Sys.int_size - nb_solution_of_constant_idx)) lsl nb_remaing_solutions) :: loop nb_remaing_solutions (idx+1)
        else 
          begin
            let p = ref 0 in
            for i = 0 to storage.nb_constants - 1 do
              for j = 0 to Array.length storage.elts_t.(i) - 1 do 
                let p' = !p lsl 1 in
                p := if storage.elts_t.(i).(j).(idx) <> 0 then succ p' else p'
              done
            done;
            let full_p = !p lsl Array.length storage.elts_t.(storage.nb_constants) in
            
            let nb_solution_of_constant_idx = Array.length storage.elts_t.(idx) in
            let nb_remaing_solutions = nb_remaing_solutions - nb_solution_of_constant_idx in

            full_p :: loop nb_remaing_solutions (idx+1)
          end
    in
    loop storage.nb_elts_t 0

  (** Generate the bitvectors used in the greater/smaller test in DFS of Hullot tree. 
      Used for unification and exact matching *)
  let generate_bitvectors ground_constants_status storage = 
    let constant_bitvectors = generate_bitvector_of_all_constants ground_constants_status storage in
    let all_bitvectors = ref constant_bitvectors in
    for idx = storage.nb_constants to storage.nb_constants + storage.nb_variables - 1 do
      all_bitvectors := generate_bitvectors_of_variable storage idx :: !all_bitvectors
    done;
    constant_bitvectors, !all_bitvectors

  (** Similar to [generate_bitvectors] but avoid generating the bitvector of the variable
      given as argument.
      Used for unification and exact matching*)
  let generate_bitvectors_with_optional_variable variables op_var ground_constants_status storage =
    let constant_bitvectors = generate_bitvector_of_all_constants ground_constants_status storage in
    let all_bitvectors = ref constant_bitvectors in
    for idx = storage.nb_constants to storage.nb_constants + storage.nb_variables - 1 do
      if variables.(idx) != op_var 
      then all_bitvectors := generate_bitvectors_of_variable storage idx :: !all_bitvectors
    done;
    constant_bitvectors, !all_bitvectors

  (** Generation of the occurrence data used for occurrence check duing DFS of Hullot Tree *)
  let generate_occurrence_data (occur_variables:(int list *int) Array.t) solutions =
    
    let vertex_tbl = Array.make solutions.nb_variables { HullotTree.status = NotVisited; HullotTree.successors = [] } in

    let build_transition_bit idx_xi bit_xj =
      let p = ref 0 in
      for i = 0 to solutions.nb_constants - 1 do
        for j = 0 to Array.length solutions.elts_t.(i) - 1 do 
          let p' = !p lsl 1 in
          if solutions.elts_t.(i).(j).(idx_xi+solutions.nb_constants) <> 0 && bit_xj land (snd occur_variables.(i)) <> 0
          then p := succ p'
          else p := p'
        done
      done;
      !p lsl (Array.length solutions.elts_t.(solutions.nb_constants))
    in

    let roots = ref [] in

    for i = 0 to solutions.nb_variables - 1 do
      let bit_xj = ref (1 lsl (solutions.nb_variables - 1)) in
      let succ = ref [] in
      for j = 0 to solutions.nb_variables - 1 do
        let transition_bit = build_transition_bit i !bit_xj in
        if transition_bit <> 0
        then succ := (j,transition_bit) :: !succ;
        bit_xj := !bit_xj lsr 1
      done;
      vertex_tbl.(i) <- { status = NotVisited; successors = !succ };
      if !succ <> [] then roots := i :: !roots
    done;

    { HullotTree.vertex_tbl = vertex_tbl; HullotTree.roots = !roots }

  (** Creates the constraints that will need to be add during the DFS of Hullot tree. *)
  let create_constraints_from_solutions constants ground_status solutions =

    let last_idx_constant = Array.length constants - 1 in

    (* search_in_constraint_space *) 
    
    let bit_repr_fst_sol_idx_constant1 = ref (1 lsl (solutions.nb_elts - 1)) in
    let idx_fst_sol_idx_constant1 = ref 0 in
    let accumulator_constraints = ref [] in

    let exploration_idx1_solutions idx_constant1 idx_constant2 sols = 
      let bit_repr_col = ref !bit_repr_fst_sol_idx_constant1 in
      let bit_repr_eq = ref 0 in
      let idx_eq = ref [] in 
      
      (* Explore the solution s *)
      List.iteri (fun i sol ->
        if sol.(idx_constant2) = 1
        then 
          begin 
            bit_repr_eq := !bit_repr_col lor !bit_repr_eq;
            idx_eq := (solutions.nb_elts - i - !idx_fst_sol_idx_constant1) :: !idx_eq
          end;
        bit_repr_col := !bit_repr_col lsr 1
      ) sols;

      if !bit_repr_eq <> 0
      then 
        (* We build the inequality disjunction. Note that the disjunct created cannot be false as it would mean the two 
           term are equal which should have been prevented by the fact that our term are unfolded. *)
        match ConstraintsEquality.create constants.(idx_constant1) constants.(idx_constant2) with
        | None ->
            (** The disjunct is always true, thus [constants.(idx_constant1)]  and [constants.(idx_constant2)]
                cannot be unifiable. We discard the solutions satisfying *)
            let new_sols = 
              List.filter (fun sol -> 
                if sol.(idx_constant2) = 1 
                then (solutions.nb_elts <- solutions.nb_elts - 1; false)
                else true
              ) sols 
            in
            (* Update the solutions *)
            solutions.elts.(idx_constant1) <- new_sols;

            (** We update the bit representations of constraint we already generated *)
            let new_constraints = 
              List.filter_map (fun (disj,bitrep) ->
                let bitrep' = List.fold_left remove_bit_i bitrep !idx_eq in
                if bitrep' = 0
                then None (* The constraint is not used anymore, we discar it *)
                else Some (disj,bitrep')
              ) !accumulator_constraints
            in

            (** We update the bit representation of the first solution in idx_constant1 since 
                one solution was removed. *)
            bit_repr_fst_sol_idx_constant1 := !bit_repr_fst_sol_idx_constant1 lsr 1;

            accumulator_constraints := new_constraints
        | Some disj -> accumulator_constraints := (disj,!bit_repr_eq) :: !accumulator_constraints
    in

    for idx_constant1 = 0 to last_idx_constant do 
      if ground_status.(idx_constant1) = None
      then
        (* The constrant is ground thus we only need to look at the column of non-ground constant *)
        for idx_constant2 = 0 to last_idx_constant do 
          if ground_status.(idx_constant2) <> None
          then exploration_idx1_solutions idx_constant1 idx_constant2 solutions.elts.(idx_constant1)
        done
      else
        (* The constrant is not ground thus we need to look at all column after idx_constant1  *)
        for idx_constant2 = idx_constant1 + 1 to last_idx_constant do 
          exploration_idx1_solutions idx_constant1 idx_constant2 solutions.elts.(idx_constant1)
        done;
      
      (* Needs to be recalculated since the number of solutions might have changed. *)
      let nb_solutions_in_idx1 = List.length solutions.elts.(idx_constant1) in
      bit_repr_fst_sol_idx_constant1 := !bit_repr_fst_sol_idx_constant1 lsr nb_solutions_in_idx1;
      idx_fst_sol_idx_constant1 := nb_solutions_in_idx1 + !idx_fst_sol_idx_constant1
    done;

    !accumulator_constraints

  (** Creates the constraints that will need to be add during the DFS of Hullot tree. *)
  let create_constraints_from_solutions_matching idx_first_non_ground constants ground_status solutions =
    let nb_constants = Array.length constants in
    if idx_first_non_ground = nb_constants
    then 
      (* There is only ground terms and variables so no constraints need to be generated *)
      []
    else 
      begin
        let last_idx_constant = Array.length constants - 1 in

        (* search_in_constraint_space *) 
        
        let bit_repr_fst_sol_idx_constant1 = ref (1 lsl (solutions.nb_elts - 1)) in
        let idx_fst_sol_idx_constant1 = ref 0 in
        let accumulator_constraints = ref [] in

        let exploration_idx1_solutions idx_constant1 idx_constant2 sols = 
          let bit_repr_col = ref !bit_repr_fst_sol_idx_constant1 in
          let bit_repr_eq = ref 0 in
          let idx_eq = ref [] in 
          
          (* Explore the solution s *)
          List.iteri (fun i sol ->
            if sol.(idx_constant2) = 1
            then 
              begin 
                bit_repr_eq := !bit_repr_col lor !bit_repr_eq;
                idx_eq := (solutions.nb_elts - i - !idx_fst_sol_idx_constant1) :: !idx_eq
              end;
            bit_repr_col := !bit_repr_col lsr 1
          ) sols;

          if !bit_repr_eq <> 0
          then 
            (* We build the inequality disjunction. Note that the disjunct created cannot be false as it would mean the two 
              term are equal which should have been prevented by the fact that our term are unfolded. 
              Warning, it is important to match idx_constant2 (the non ground) with idx_constant1 (the ground) *)
            match ConstraintsMatching.create constants.(idx_constant2) constants.(idx_constant1) with
            | None ->
                (** The disjunct is always true, thus [constants.(idx_constant1)]  and [constants.(idx_constant2)]
                    cannot be unifiable. We discard the solutions satisfying *)
                let new_sols = 
                  List.filter (fun sol -> 
                    if sol.(idx_constant2) = 1 
                    then (solutions.nb_elts <- solutions.nb_elts - 1; false)
                    else true
                  ) sols 
                in
                (* Update the solutions *)
                solutions.elts.(idx_constant1) <- new_sols;

                (** We update the bit representations of constraint we already generated *)
                let new_constraints = 
                  List.filter_map (fun (disj,bitrep) ->
                    let bitrep' = List.fold_left remove_bit_i bitrep !idx_eq in
                    if bitrep' = 0
                    then None (* The constraint is not used anymore, we discar it *)
                    else Some (disj,bitrep')
                  ) !accumulator_constraints
                in

                (** We update the bit representation of the first solution in idx_constant1 since 
                    one solution was removed. *)
                bit_repr_fst_sol_idx_constant1 := !bit_repr_fst_sol_idx_constant1 lsr 1;

                accumulator_constraints := new_constraints
            | Some disj -> accumulator_constraints := (disj,!bit_repr_eq) :: !accumulator_constraints
        in

        for idx_constant1 = 0 to idx_first_non_ground - 1 do 
          (* The constrant is ground thus we only need to look at the column of non-ground constant *)
          for idx_constant2 = idx_first_non_ground to last_idx_constant do 
            if ground_status.(idx_constant2) <> None
            then exploration_idx1_solutions idx_constant1 idx_constant2 solutions.elts.(idx_constant1)
          done;

          (* Needs to be recalculated since the number of solutions might have changed. *)
          let nb_solutions_in_idx1 = List.length solutions.elts.(idx_constant1) in
          bit_repr_fst_sol_idx_constant1 := !bit_repr_fst_sol_idx_constant1 lsr nb_solutions_in_idx1;
          idx_fst_sol_idx_constant1 := nb_solutions_in_idx1 + !idx_fst_sol_idx_constant1
        done;

        !accumulator_constraints
      end
 
  (** Suitable_bitsubset_to_substitutions *)
  let suitable_bitsubset_to_substitution ?(apply_mark=false) ?(exists_vars=None) solutions f_AC constants variables ground_constant_status p = 
    
    (* Ac_config.debug_unification (fun () ->
      Printf.printf "** suitable_bitsubset_to_substitution:\n";
      Printf.printf "Solutions:\n";
      display solutions;
      
      Array.iteri (fun i v -> match v.v_link with 
        TLink t' -> Printf.printf "Should not be linked %s and %s\n" (string_of_variable v) (string_of_term t')
        | _ -> ()
      ) variables;
      Printf.printf "Variables = ";
      display_vector string_of_variable variables;
      Printf.printf "Constants = ";
      display_vector string_of_term constants;
      Printf.printf "Ground constants = ";
      display_vector (function None -> "true" | _ -> "false") ground_constant_status;
      Printf.printf "Subset bit: %s\n" (int2bin solutions.nb_elts_t p);
      flush_all ()
    ); *)

    (* Reset the recorded term in ground_constants *)
    Array.iter (function None -> () | Some ref_t -> ref_t := dummy) ground_constant_status;

    let term_links = Array.make (Array.length variables) ([],true) in

    let rec loop_vars i bit_i =
      Ac_config.debug_unification (fun () ->
        Printf.printf "loop_vars(%d,%s)\n" i (int2bin solutions.nb_elts_t bit_i);
        flush_all ()
      );
      if i = -1
      then bit_i
      else
        if bit_i land p = 0 (* The subset do not contain the solution *)
        then loop_vars (i - 1) (bit_i lsl 1)
        else 
          begin 
            let sol = solutions.elts_t.(solutions.nb_constants).(i) in
            for j = 0 to Array.length term_links -1 do
              let k = sol.(j+solutions.nb_constants) in
              if k <> 0
              then term_links.(j) <- (solutions.associated_variables.(i),k) :: (fst term_links.(j)), true
            done;
            Array.iteri (fun j ground -> match ground with
              | None -> ()
              | Some ref_t ->
                  let k = sol.(j) in
                  if k <> 0
                    then 
                      begin
                        if k <> 1 || !ref_t != dummy then failwith "[Elementary.Storage_solutions] The 'smaller than' test should have discarded this case"; 
                        ref_t := solutions.associated_variables.(i)
                      end
            ) ground_constant_status;
            loop_vars (i - 1) (bit_i lsl 1)
          end
    in

    let rec loop_constants i ith_constant constant sols_constant bit_i =
      if i = -1
      then bit_i
      else
        if bit_i land p = 0 (* The subset do not contain the solution *)
        then loop_constants (i - 1) ith_constant constant sols_constant (bit_i lsl 1)
        else 
          begin 
            let sol = sols_constant.(i) in

            for j = 0 to Array.length term_links -1 do
              let k = sol.(j+solutions.nb_constants) in
              if k <> 0
              then term_links.(j) <- (constant,k) :: fst term_links.(j), false
            done;
            Array.iteri (fun j ground -> match ground with
              | None -> ()
              | Some ref_t ->
                  if j != ith_constant
                  then 
                    let k = sol.(j) in
                    if k <> 0
                    then 
                      begin
                        if k <> 1 || !ref_t != dummy then internal_error __POS__ "[DiophantineSolutions.suitable_bitsubset_to_substitution] The 'smaller than' test should have discarded this case"; 
                        ref_t := constant
                      end
            ) ground_constant_status;
            (bit_i lsl (i + 1))
          end
    in

    let rec loop_all_constants ith_constant bit_i = 
      if ith_constant = - 1
      then ()
      else
        let sols_constant = solutions.elts_t.(ith_constant) in
        let bit_i' = loop_constants (Array.length sols_constant - 1) ith_constant constants.(ith_constant) sols_constant bit_i in
        loop_all_constants (ith_constant-1) bit_i'
    in

    let bit_i = loop_vars (Array.length solutions.associated_variables - 1) 1 in
    Ac_config.debug_unification (fun () ->
      Printf.printf "Before loop_all_constants\n";
      flush_all ();
    );
    loop_all_constants (solutions.nb_constants - 1) bit_i;
    Ac_config.debug_unification (fun () ->
      Printf.printf "After loop_all_constants\n";
      flush_all ();
    );
    for i = 0 to Array.length variables - 1 do
      match term_links.(i) with
        | [], _ -> () (* This case can only happen in the non-strict maching *)
        | [Var ({link = NoLink; } as v),1], true -> 
            (* Ac_config.debug_unification (fun () -> 
              Printf.printf "Linking %s with %s\n" (string_of_variable v) (string_of_variable variables.(i));
              match variables.(i).v_link with 
              | TLink t' -> Printf.printf "Weird link %s with %s\n" (string_of_variable variables.(i)) (string_of_term t')
              |_ -> ()
            );  *)
            
            begin match exists_vars with
            | Some l when List.memq variables.(i) l -> 
                Terms.link variables.(i) (TLink (Var v));
            | _ -> 
                Terms.link v (TLink (Var variables.(i)));
                if apply_mark then mark_redundant_hyp_variables (Var variables.(i))
            end
        | [t,1],_ -> 
          (* Ac_config.debug_unification (fun () -> Printf.printf "Linking %s with %s\n" (string_of_variable variables.(i)) (string_of_term t) ); *)
            begin match t with 
            | FunApp(f,_) when variables.(i).unfailing = false &&f.f_cat = Failure -> raise Terms.Unify
            | _ -> ()
            end;
            Terms.link variables.(i) (TLink t);
            if apply_mark then mark_redundant_hyp_variables t
        | mt,_ -> 
          (* Ac_config.debug_unification (fun () -> Printf.printf "Linking %s with %s\n" (string_of_variable variables.(i)) (string_of_term (FAC(f_AC,mt))) ); *)
            Terms.link variables.(i) (TLink (FAC(f_AC,mt)));
            if apply_mark then mark_redundant_hyp_variables (FAC(f_AC,mt))
    done
end

let solve_system_diophantine_equations nb_constants (occur_variables_opt:(int list * int) Array.t option) ground_constants matrix_system =
  let nb_equations = Array.length matrix_system in
  let nb_variables = Array.length matrix_system.(0) in

  let freezing_for_occur_check = match occur_variables_opt with 
    | None -> (fun _ _ -> ())
    | Some occur_variables -> 
        (fun v j -> List.iter (fun k -> v.(k+nb_constants) <- (0,true)) (fst occur_variables.(j)))
  in

  let sum_defect (v:int Array.t) (v_init:int Array.t) = 
    let res = Array.copy v in
    for i = 0 to nb_equations - 1 do 
      res.(i) <- res.(i) + v_init.(i)
    done;
    res
  in

  let scalar_product v1 v2 = 
    let res = ref 0 in
    for i = 0 to nb_equations - 1 do
      res := !res + (v1.(i) * v2.(i))
    done;
    !res
  in

  let is_null v = Array.for_all (fun i -> i = 0) v in

  (* not (v + e_j >_m u) *)
  let order_vector j (v:(int * bool) Array.t) (u:int Array.t) =

    let rec loop all_geq i =
      if i = nb_variables 
      then all_geq
      else 
        let vi = if i = j then (fst v.(i)) + 1 else (fst v.(i)) in
        if vi < u.(i)
        then true
        else loop (all_geq && vi = u.(i)) (succ i)
    in
    loop true 0
  in

  (* v + e_j *)
  let add_ej (v:(int * bool) Array.t) j = 
    let v' = Array.copy v in
    let (vj,frozen) = v.(j) in
    v'.(j) <- (succ vj,frozen);
    v'
  in

  (* Generate the initial defects *)
  let initial_defects = Array.make nb_variables (Array.make 0 0) in
  
  for j = 0 to nb_variables - 1 do 
    let res = Array.make nb_equations 0 in
    for i = 0 to nb_equations - 1 do 
      res.(i) <- matrix_system.(i).(j)
    done;
    initial_defects.(j) <- res
  done;

  let set_rest_Mk = DiophantineSolutions.create nb_constants in

  (** The sets [set_Vk_not_in_Mk], [set_Vk_in_Mk] and [set_rest_Mk] are in fact arrays of size
      [nb_constants+1] that stores the solution depending on wether the solution corresponds to 
      a constant or not. *)
  let rec build_M (set_Vk_not_in_Mk:DiophantineSolutions.t_frozen) (set_Vk_in_Mk:DiophantineSolutions.t_unfrozen) =   
    if set_Vk_not_in_Mk.nb_elts_f = 0 && set_Vk_in_Mk.nb_elts = 0
    then ()
    else
      begin 
        let next_Vk_not_in_Mk = DiophantineSolutions.create_frozen nb_constants in
        let next_Vk_in_Mk = DiophantineSolutions.create nb_constants in

        DiophantineSolutions.iter_frozen (fun idx (v,defect_v) ->
          let success_j = ref [] in
          for j = 0 to nb_variables - 1 do
            if snd v.(j) || scalar_product defect_v initial_defects.(j) >= 0
            then ()
            else
              if 
                DiophantineSolutions.for_all (order_vector j v) set_Vk_in_Mk &&
                DiophantineSolutions.for_all (order_vector j v) set_rest_Mk
              then 
                begin 
                  let new_v = add_ej v j in
                  let defect_new_v = sum_defect defect_v initial_defects.(j) in
                  if is_null defect_new_v
                  then 
                    let new_v' = Array.map (fun (k,_) -> k) new_v in
                    DiophantineSolutions.add next_Vk_in_Mk idx new_v'
                  else 
                    begin 
                      (* Froze the previous successful index. *)
                      List.iter (fun l ->
                        new_v.(l) <- (fst new_v.(l), true);
                      ) !success_j;

                      (* If j was a non-ground constant, froze the variables that occur in the constant *)
                      if j < nb_constants && ground_constants.(j) <> None
                      then 
                        begin 
                          new_v.(j) <- (1, true);
                          freezing_for_occur_check new_v j
                        end;

                      success_j := j :: !success_j;
                      DiophantineSolutions.add_frozen next_Vk_not_in_Mk idx (new_v,defect_new_v)
                    end
                end
          done
        ) set_Vk_not_in_Mk;

        DiophantineSolutions.merge set_rest_Mk set_Vk_in_Mk;

        build_M next_Vk_not_in_Mk next_Vk_in_Mk
      end
  in

  let init_set_Vk_not_in_Mk = DiophantineSolutions.create_frozen nb_constants in
  let init_set_Vk_in_Mk = DiophantineSolutions.create nb_constants in
  
  (* Initialise the sets *)
  let e_frozen_template = Array.make nb_variables (0,false) in

  (* Froze all the ground ground constants *)
  for j = 0 to nb_constants - 1 do
    if ground_constants.(j) = None
    then e_frozen_template.(j) <- (0,true)
  done;

  let e_frozen_template_ground = Array.copy e_frozen_template in

  for j = 0 to nb_constants - 1 do 
    if is_null initial_defects.(j)
    then 
      let ej = Array.make nb_variables 0 in
      ej.(j) <- 1;
      DiophantineSolutions.add init_set_Vk_in_Mk j ej;
      if ground_constants.(j) = None
      then
        begin
          e_frozen_template.(j) <- (0,true);
          e_frozen_template_ground.(j) <- (0,true)
        end
      else e_frozen_template.(j) <- (0,true)
    else
      begin
        let ej = 
          if ground_constants.(j) = None
          then 
            begin 
              let ej' = Array.copy e_frozen_template_ground in
              e_frozen_template.(j) <- (0,true);
              e_frozen_template_ground.(j) <- (0,true);
              ej'
            end
          else
            begin 
              let ej' = Array.copy e_frozen_template in
              e_frozen_template.(j) <- (0,true);
              ej'
            end
        in
        ej.(j) <- (1,true);
        (* Froze the variables that occur in the constant *)
        freezing_for_occur_check ej j;

        DiophantineSolutions.add_frozen init_set_Vk_not_in_Mk j (ej,initial_defects.(j));
      end
  done;
  
  for j = nb_constants to nb_variables - 1 do 
    if is_null initial_defects.(j)
    then 
      let ej = Array.make nb_variables 0 in
      ej.(j) <- 1;
      DiophantineSolutions.add init_set_Vk_in_Mk nb_constants ej
    else
      begin
        let ej = Array.copy e_frozen_template in
        ej.(j) <- (1,false);

        DiophantineSolutions.add_frozen init_set_Vk_not_in_Mk nb_constants (ej,initial_defects.(j));
      end;
    e_frozen_template.(j) <- (0,true);
  done;

  build_M init_set_Vk_not_in_Mk init_set_Vk_in_Mk;

  set_rest_Mk

(** Partition of the system of equation depending on a target AC symbol *)
let rec partition_system_equations (f_target:funsymb) = function
  | [] -> ([]:(mterm list * mterm list) list), ([]:(funsymb * mterm list * mterm list) list)
  | (f,mlist1,mlist2) :: q when f == f_target ->
      let same_f_equations, other_equations = partition_system_equations f_target q in
      (mlist1,mlist2)::same_f_equations, other_equations
  | pbl::q -> 
      let same_f_equations, other_equations = partition_system_equations f_target q in
      same_f_equations, pbl::other_equations

(*********************
   Matching          
**********************) 

let check_total_and_max_multiplicity margs1 margs2= 
  let (tot1,max1) = 
    List.fold_left (fun (tot_acc,max_acc) (t,k) ->
      (k+tot_acc,max max_acc k)  
    ) (0,0) margs1
  in
  let (tot2,max2) = 
    List.fold_left (fun (tot_acc,max_acc) (t,k) ->
      (k+tot_acc,max max_acc k)  
    ) (0,0) margs2
  in
  if tot1 > tot2 || max1 > max2 then raise Terms.Unify

(** [match_term_and_gather remaining_equations_ref t1 t2] matching the terms [t1] and [t2] unless
    they corresponds to an AC equation. In this case, it stores the equations in [remaining_equations_ref].*)
let rec match_term_and_gather remaining_equations_ref t1 t2 = match t1, t2 with 
  | Var { link = TLink t; _}, t' -> if not (equal t t') then raise Terms.Unify
  | Var v1, FunApp(f,_) when v1.unfailing = false && f.f_cat = Failure -> raise Terms.Unify
  | Var v1, Var v2 when v1.unfailing = false  && v2.unfailing -> raise Terms.Unify
  | Var v1, _ -> Terms.link v1 (TLink t2)
  | FunApp(f1,args1), FunApp(f2,args2) -> 
      if f1 != f2 then raise Terms.Unify;
      List.iter2 (match_term_and_gather remaining_equations_ref) args1 args2
  | FAC(f1,margs1), FAC(f2,margs2) ->
      if f1 != f2 then raise Terms.Unify;
      check_total_and_max_multiplicity margs1 margs2;
      remaining_equations_ref :=  (f1,margs1,margs2)::!remaining_equations_ref
  | _ -> raise Terms.Unify
  
(** Solve the system of equations (non-minimal) *)
let rec solve_matching f_next remaining_equations var_op f_AC system_equations =  
  let (matrix_system,variables,_,constants,ground_constant_status) = MatrixGeneration.from_matching_equations f_AC system_equations in
  
  let nb_constants = Array.length constants in
  let nb_variables = Array.length variables in

  (* Ac_config.debug_matching (fun () ->
    Printf.printf "** After generating the matrix:\n";
    print_string "Matrix =\n";
    display_matrix string_of_int matrix_system;
    Printf.printf "Variables (%d) = " nb_variables;
    display_vector string_of_variable variables;
    Printf.printf "Constants (%d) = " nb_variables;
    display_vector string_of_term constants;
    flush_all ();
    Printf.printf "Ground constants = ";
    display_vector (function None -> "true" | _ -> "false") ground_constant_status;
    flush_all ();
  ); *)

  let generate_bitvectors_fun = match var_op with 
    | None -> DiophantineSolutions.generate_bitvectors
    | Some x -> DiophantineSolutions.generate_bitvectors_with_optional_variable variables x
  in

  if nb_variables = 0 && nb_constants = 0 
  then 
    (* The system is trivially true *)
    matching_remaining_equations f_next remaining_equations
  else
    begin 
      (* Solving the matrix system of diophantine_equations *)
      let solutions = solve_system_diophantine_equations nb_constants None ground_constant_status matrix_system in
    
      let nb_solutions = solutions.DiophantineSolutions.nb_elts in

      if nb_solutions > Sys.int_size - 2
      then failwith "Limit on the number of solutions reached";
    
      if nb_solutions = 0 then raise Terms.Unify;
    
      let finalized_solutions = DiophantineSolutions.finalize nb_constants nb_variables solutions in      
      (* Bit presentation to subset of solutions *)
      let (constant_bitvectors,all_bitvectors) = generate_bitvectors_fun ground_constant_status finalized_solutions in

      HullotTree.dfs (fun f_next_dfs p ->
        try 
          Terms.auto_cleanup_noreset (fun () ->
            DiophantineSolutions.suitable_bitsubset_to_substitution finalized_solutions f_AC constants variables ground_constant_status p;

            (* We retrieve the new equations to solve equations. *)
            let remaining_equations_ref = ref remaining_equations in

            for i = 0 to nb_constants - 1 do
              match ground_constant_status.(i) with
              | None -> ()
              | Some ref_t ->
                  if !ref_t == dummy
                  then internal_error __POS__ "[solve_for_minimal_unification] Since the term is not ground, it must have been paired with some other term.";
                  match_term_and_gather remaining_equations_ref constants.(i) !ref_t
            done;
            matching_remaining_equations f_next !remaining_equations_ref
          )
        with Terms.Unify -> f_next_dfs ()
      ) nb_solutions all_bitvectors constant_bitvectors None
      
    end

and matching_remaining_equations f_next = function
  | [] -> f_next ()
  | ((f,_,_) :: _) as remaining_equations ->
      let same_f_equations, other_equations = partition_system_equations f remaining_equations in
      solve_matching f_next other_equations None f same_f_equations

let match_terms f_next eq_list = 
  Ac_config.debug_incr_matching ();
  Terms.auto_cleanup_noreset (fun () ->
    let remain_ref = ref [] in
    List.iter (fun (t1,t2) -> match t1,t2 with
      | Var v, FunApp(f,_) when f.f_cat = Failure && v.unfailing = false -> raise Terms.Unify
      | Var v, Var v' when not v.unfailing && v'.unfailing -> raise Terms.Unify
      | _ -> ()
    ) eq_list;
    List.iter (fun (t1,t2) ->
      match_term_and_gather remain_ref t1 t2
    ) eq_list;
    matching_remaining_equations f_next !remain_ref
  )

(** Match_redundant_hyp_terms *)

let rec mark_redundant_hyp_variables = function
  | Var v ->
      begin match v.link with
        | TLink _ -> raise Terms.Unify
        | VLink _ -> ()
        | NoLink -> Terms.link v (VLink v)
        | _ -> Parsing_helper.internal_error "[AC_unify.ml >> mark_variables] Unexpected links"
      end
  | FunApp(_,args) -> List.iter mark_redundant_hyp_variables args
  | FAC(_,margs) -> List.iter (fun (t,_) -> mark_redundant_hyp_variables t) margs

let mark_redundant_hyp_variables_fact = function
  | Pred(_,args) -> List.iter mark_redundant_hyp_variables args

(** [match_term_and_gather remaining_equations_ref t1 t2] matching the terms [t1] and [t2] unless
    they corresponds to an AC equation. In this case, it stores the equations in [remaining_equations_ref].*)
let rec match_redundant_hyp_term_and_gather apply_mark remaining_equations_ref t1 t2 = match t1, t2 with 
  | Var v, Var v' when v == v' -> 
      ()
      (* if apply_mark then mark_redundant_hyp_variables t2 *)
  | Var { link = TLink t; _}, t' -> if not (equal t t') then raise Terms.Unify
  | Var { link = VLink t; _}, t' -> 
      (* Since the variable has been marked, it can't be used in the substitution.
         The only possible case is when t1 = t2 which is already covered. *)
        raise Terms.Unify
  | Var v1, Var v2 when v1.unfailing = false  && v2.unfailing -> raise Terms.Unify
  | Var v1, FunApp(f,_) when v1.unfailing = false && f.f_cat = Failure -> raise Terms.Unify
  | Var v1, _ -> 
      Terms.link v1 (TLink t2);
      if apply_mark then mark_redundant_hyp_variables t2
  | FunApp(f1,args1), FunApp(f2,args2) -> 
      if f1 != f2 then raise Terms.Unify;
      List.iter2 (match_redundant_hyp_term_and_gather apply_mark remaining_equations_ref) args1 args2
  | FAC(f1,margs1), FAC(f2,margs2) ->
      if f1 != f2 then raise Terms.Unify;
      check_total_and_max_multiplicity margs1 margs2;
      remaining_equations_ref :=  (f1,margs1,margs2)::!remaining_equations_ref
  | _ -> raise Terms.Unify
  
(** Solve the system of equations (non-minimal) *)
let rec solve_redundant_hyp_matching f_next apply_mark remaining_equations var_op f_AC system_equations =  
  let (matrix_system,variables,_,constants,ground_constant_status) = MatrixGeneration.from_matching_equations f_AC system_equations in
  
  let nb_constants = Array.length constants in
  let nb_variables = Array.length variables in

  (* Ac_config.debug_matching (fun () ->
    Printf.printf "** After generating the matrix:\n";
    print_string "Matrix =\n";
    display_matrix string_of_int matrix_system;
    Printf.printf "Variables (%d) = " nb_variables;
    display_vector string_of_variable variables;
    Printf.printf "Constants (%d) = " nb_variables;
    display_vector string_of_term constants;
    flush_all ();
    Printf.printf "Ground constants = ";
    display_vector (function None -> "true" | _ -> "false") ground_constant_status;
    flush_all ();
  ); *)

  let generate_bitvectors_fun = match var_op with 
    | None -> DiophantineSolutions.generate_bitvectors
    | Some x -> DiophantineSolutions.generate_bitvectors_with_optional_variable variables x
  in

  if nb_variables = 0 && nb_constants = 0 
  then 
    (* The system is trivially true *)
    matching_remaining_equations f_next remaining_equations
  else
    begin 
      (* Solving the matrix system of diophantine_equations *)
      let solutions = solve_system_diophantine_equations nb_constants None ground_constant_status matrix_system in
    
      let nb_solutions = solutions.DiophantineSolutions.nb_elts in

      if nb_solutions > Sys.int_size - 2
      then failwith "Limit on the number of solutions reached";
    
      if nb_solutions = 0 then raise Terms.Unify;
    
      let finalized_solutions = DiophantineSolutions.finalize nb_constants nb_variables solutions in      
      (* Bit presentation to subset of solutions *)
      let (constant_bitvectors,all_bitvectors) = generate_bitvectors_fun ground_constant_status finalized_solutions in

      HullotTree.dfs (fun f_next_dfs p ->
        try 
          Terms.auto_cleanup (fun () ->
            DiophantineSolutions.suitable_bitsubset_to_substitution ~apply_mark:true finalized_solutions f_AC constants variables ground_constant_status p;
            (* We retrieve the new equations to solve equations. *)
            let remaining_equations_ref = ref remaining_equations in
            for i = 0 to nb_constants - 1 do
              match ground_constant_status.(i) with
              | None -> ()
              | Some ref_t ->
                  if !ref_t == dummy
                  then internal_error __POS__ "[solve_for_minimal_unification] Since the term is not ground, it must have been paired with some other term.";
                  match_redundant_hyp_term_and_gather apply_mark remaining_equations_ref constants.(i) !ref_t
            done;
            matching_redundant_hyp_remaining_equations f_next apply_mark !remaining_equations_ref
          )
        with Terms.Unify -> f_next_dfs ()
      ) nb_solutions all_bitvectors constant_bitvectors None
      
    end

and matching_redundant_hyp_remaining_equations f_next apply_mark = function
  | [] -> f_next ()
  | ((f,_,_) :: _) as remaining_equations ->
      let same_f_equations, other_equations = partition_system_equations f remaining_equations in
      solve_redundant_hyp_matching f_next apply_mark other_equations None f same_f_equations

let match_redundant_hyp_terms f_next apply_mark eq_list = 
  Ac_config.debug_incr_matching ();
  Terms.auto_cleanup (fun () ->
    let remain_ref = ref [] in
    List.iter (fun (t1,t2) -> match t1,t2 with
      | Var v, FunApp(f,_) when f.f_cat = Failure && v.unfailing = false -> raise Terms.Unify
      | Var v, Var v' when not v.unfailing && v'.unfailing -> raise Terms.Unify
      | _ -> ()
    ) eq_list;
    List.iter (fun (t1,t2) ->
      match_redundant_hyp_term_and_gather apply_mark remain_ref t1 t2
    ) eq_list;
    matching_redundant_hyp_remaining_equations f_next apply_mark !remain_ref
  )

let match_redundant_hyp_facts f_next apply_mark f1 f2 = match f1, f2 with
  | Pred(p1,t1), Pred(p2,t2) ->
      if p1 != p2 then raise Terms.Unify;
      match_redundant_hyp_terms f_next apply_mark (List.combine t1 t2)

(** [are_terms_matched_non_strict f_next t1 t2] will match [t1] with [t2] or [t1 + t] with [t2] for some AC symbol [+]
    and some [t]. The function [f_next] takes as arguments [Some t] when such [t] exists and [None] otherwise. *)
(* let match_terms_non_strict f_next t1 t2 = match t2 with 
  | FAC(f,margs2) ->
      let x = Terms.new_var_def Param.bitstring_type in 
      solve_for_minimal_matching (fun () ->
        match x.link with 
        | NoLink -> f_next None
        | TLink t -> f_next (Some t)
        | _ -> internal_error __POS__ "[match_terms_non_strict] Unexpected link."
      ) [] [] (Some x) f [[(t1,1);(Var x,1)],margs2] 
  | _ -> match_terms (fun () -> f_next None) [t1,t2] *)

let are_terms_matched_non_strict t1 t2 = match t2 with 
  | FAC(f,margs2) ->
      let x = Terms.new_var_def Param.bitstring_type in 
      begin try 
        match_terms (fun () ->
          true
        ) [t1,t2]
      with Terms.Unify ->
        try
          match_terms (fun () ->
            true
          ) [apply_symbol f [Var x;t1],t2]
          with Terms.Unify -> false
      end
      (* solve_for_minimal_matching (fun () ->
        match x.link with 
        | NoLink -> f_next None
        | TLink t -> f_next (Some t)
        | _ -> internal_error __POS__ "[match_terms_non_strict] Unexpected link."
      ) [] [] (Some x) f [[(t1,1);(Var x,1)],margs2]  *)
  | _ -> 
    try 
      match_terms (fun () -> true) [t1,t2]
    with Terms.Unify -> false

let are_terms_matched t1 t2 = 
  try 
    match_terms (fun () -> true) [t1,t2]
  with Terms.Unify -> false

let are_facts_matched fact1 fact2 = match fact1,fact2 with
  | Pred(f1,args1), Pred(f2,args2) ->
      if f1 == f2 
      then
        try match_terms (fun () -> true) (List.combine args1 args2)
        with Terms.Unify -> false
      else false

let match_facts f_next fact1 fact2 = match fact1,fact2 with
  | Pred(f1,args1), Pred(f2,args2) ->
      if f1 == f2 
      then
        match_terms f_next (List.combine args1 args2)
      else raise Terms.Unify

(* Same as match_facts except that f1 of phase n can be matched with f2 of phase m with n >= m when they are attacker facts.
   Used to apply Lemmas. *)
let match_facts_phase_geq f_next f1 f2 = match f1,f2 with
  | Pred(p1,args1), Pred(p2, args2) ->
      if not (Terms.is_sub_predicate p1 p2) then raise Terms.Unify;
      match_terms f_next (List.combine args1 args2)

let match_facts_phase_leq f_next f1 f2 = match f1,f2 with
  | Pred(p1,args1), Pred(p2, args2) ->
      if not (Terms.is_sub_predicate p2 p1) then raise Terms.Unify;
      match_terms f_next (List.combine args1 args2)

let match_facts_unblock f_next f1 f2 = match f1,f2 with
  | Pred(p1,args1), Pred(p2, args2) ->
      if (Terms.unblock_predicate p1) != (Terms.unblock_predicate p2) then raise Terms.Unify;
      match_terms f_next (List.combine args1 args2)

let match_facts_unblock_phase_geq f_next f1 f2 = match f1,f2 with
  | Pred(p1,args1), Pred(p2, args2) ->
      if not (Terms.is_sub_predicate (Terms.unblock_predicate p1) (Terms.unblock_predicate p2)) then raise Terms.Unify;
      match_terms f_next (List.combine args1 args2)

let rec occurs_test_loop seen_vars v t = match t with
  | Var v' ->
      begin
      if List.memq v' (!seen_vars) 
      then false 
      else
        begin
        seen_vars := v' :: (!seen_vars);
        if v == v' 
        then true 
        else
          match v'.link with
          | NoLink -> false
          | TLink t' -> occurs_test_loop seen_vars v t'
          | _ -> Parsing_helper.internal_error "unexpected link in occur_check"
        end
      end
  | FunApp(_,l) -> List.exists (occurs_test_loop seen_vars v) l
  | FAC(_,margs) -> List.exists (fun (t,_) -> occurs_test_loop seen_vars v t) margs


let match_facts_strict f1 f2 = 
  assert (!Terms.current_bound_vars == []);
  try 
    match_facts (fun () ->
      (* If a variable v is instantiated in the match into
        a term that is not a variable and that contains v, then
        by repeated resolution, the term will be instantiated into
        an infinite number of different terms obtained by
        iterating the substitution. We should adjust the selection
        function to avoid this non-termination. 
        
        As there may be several most general substitutions,
        we return [true] if that property holds for at least one of 
        the substitutions. *)
      if 
        List.exists (fun v -> 
          match v.link with
          | TLink (Var _) -> false
          | TLink t -> occurs_test_loop (ref []) v t
          | _ -> false) (!Terms.current_bound_vars) 
      then true
      else raise Terms.Unify
    ) f1 f2
  with Terms.Unify -> false 

(* Main matching functions *)

(* let exists_match ?(minimal=false) eq_list =
  try 
    Terms.auto_cleanup (fun () ->
      let remain_ref = ref [] in
      List.iter (fun (t1,t2) ->
        match_term_and_gather remain_ref t1 t2
      ) eq_list;
      if minimal 
      then matching_minimal_remaining_equations (fun () -> true) [] !remain_ref
      else matching_remaining_equations (fun () -> true) !remain_ref
    )
  with Terms.Unify -> false

let exists_match_fact fact1 fact2 = match fact1,fact2 with
  | Pred(f1,args1), Pred(f2,args2) ->
      if f1 == f2 
      then
        exists_match (List.combine args1 args2)
      else false

let find_one_match ?(minimal=false) vars eq_list =
  Ac_config.debug_incr_matching ();

  let build_subst () = 
    Some (List.filter_map (fun v -> match v.link with
      | NoLink -> None
      | TLink t -> Some (v,t)
      | _ -> internal_error __POS__ "[subst_implies] Unexpected link."
    ) !Terms.current_bound_vars)
  in

  try 
    Terms.auto_cleanup (fun () ->
      let remain_ref = ref [] in
      List.iter (fun (t1,t2) ->
        match_term_and_gather remain_ref t1 t2
      ) eq_list;
      if minimal 
      then matching_minimal_remaining_equations build_subst [] !remain_ref
      else matching_remaining_equations build_subst !remain_ref
    )
  with Terms.Unify -> None *)

(* let find_one_match ?(minimal=true) vars eq_list = 
  let t = Unix.times () in
  let start_time = (t.tms_utime +. t.tms_stime) in
  let res = find_one_match ~minimal vars eq_list in
  let t = Unix.times () in
  let end_time = (t.tms_utime +. t.tms_stime) in
  time_recorded := end_time -. start_time +. !time_recorded;
  res *)

(*********************
   Unification          
**********************)

(* let rec retrieved_margs f n t = match t with
  | Var { link = TLink t'; _ } -> retrieved_margs f n t'
  | Var _ 
  | FunApp _ -> [t,n]
  | FAC(f',margs) when f == f' -> 
      List.fold_left (fun acc' (t',n') ->
        List.rev_append (retrieved_margs f (n'*n) t') acc' 
      ) [] margs
  | _ -> [t,n]

let retrieved_margs_list f l = 
  List.fold_left (fun acc (t,n) ->
    List.rev_append (retrieved_margs f n t) acc 
  ) [] l *)

(** [unify_term_and_gather remaining_equations_ref t1 t2] unifies the terms [t1] and [t2] unless
    they corresponds to an AC equation. In this case, it stores the equations in [remaining_equations_ref].*)
let rec unify_term_and_gather remaining_equations_ref t1 t2 = match t1, t2 with 
  | Var v1, Var v2 when v1 == v2 -> ()
  | Var { link = TLink t; _}, t' 
  | t', Var { link = TLink t; _} -> unify_term_and_gather remaining_equations_ref t t'
  | Var v1, Var _ when v1.unfailing -> Terms.link v1 (TLink t2)
  | Var v1, Var v2 when v2.unfailing -> Terms.link v2 (TLink t1)
  | Var v1, FunApp (f_symb,_) when f_symb.f_cat = Failure && v1.unfailing = false -> raise Terms.Unify
  | FunApp(f_symb,_), Var v when v.unfailing = false && f_symb.f_cat = Failure -> raise Terms.Unify
  | Var v, t 
  | t, Var v -> 
      occurs_check v t;
      Terms.link v (TLink t)
  | FunApp(f1,args1), FunApp(f2,args2) -> 
      if f1 != f2 then raise Terms.Unify;
      List.iter2 (unify_term_and_gather remaining_equations_ref) args1 args2
  | FAC(f1,margs1), FAC(f2,margs2) ->
      if f1 != f2 then raise Terms.Unify;
      remaining_equations_ref :=  (f1, margs1, margs2)::!remaining_equations_ref
  | _ -> raise Terms.Unify

(** Solve the system of equations with Occur (non minimal) *)
let rec solve_for_unification f_next remaining_equations f_AC system_equations = 
  let (matrix_system,variables,constants,occur_variables,ground_constant_status) = MatrixGeneration.from_unification_equations f_AC system_equations in
  let nb_constants = Array.length constants in
  let nb_variables = Array.length variables in

  Ac_config.debug_unification (fun () -> 
    Printf.printf "** After generating the matrix:\n";
    print_string "Matrix =\n";
    display_matrix string_of_int matrix_system;
    Printf.printf "Variables (%d) = " nb_variables;
    display_vector string_of_variable variables;
    Printf.printf "Constants (%d) = " nb_constants;
    display_vector string_of_term constants;
    flush_all ();
    Printf.printf "Occur_variables = ";
    display_vector (fun (l,bit) -> Printf.sprintf "(%s,%s)" (List.string_of string_of_int "[" "]" ";"  l) (int2bin nb_variables bit)) occur_variables;
    Printf.printf "Ground constants = ";
    display_vector (function None -> "true" | _ -> "false") ground_constant_status;
    flush_all ()
  );

  if nb_variables = 0 && nb_constants = 0 
  then 
    (* The system is trivially true *)
    unify_remaining_equations f_next remaining_equations
  else
    begin 
      (* Solving the matrix system of diophantine_equations *)
      let solutions = solve_system_diophantine_equations nb_constants (Some occur_variables) ground_constant_status matrix_system in
    
      Ac_config.debug_unification (fun () -> 
        Printf.printf "\nAfter solving Diophantine equations:\n";
        DiophantineSolutions.display_unfrozen solutions;
        flush_all ()
      );

      let nb_solutions = solutions.DiophantineSolutions.nb_elts in

      if nb_solutions > Sys.int_size - 2
      then failwith "Limit on the number of solutions reached";
    
      if nb_solutions = 0 then raise Terms.Unify;
    
      let finalized_solutions = DiophantineSolutions.finalize nb_constants nb_variables solutions in 
      
      (* Ac_config.debug_unification (fun () -> 
        Printf.printf "** Finalized solutions\n";
        DiophantineSolutions.display finalized_solutions
      ); *)

      (* Bit presentation to subset of solutions *)
      let (constant_bitvectors,all_bitvectors) = DiophantineSolutions.generate_bitvectors ground_constant_status finalized_solutions in
      let occurence_data = DiophantineSolutions.generate_occurrence_data occur_variables finalized_solutions in

      Ac_config.debug_unification (fun () ->  
        Printf.printf "\n** Constant bitvectors\n";
        List.iter (fun p ->
          Printf.printf "bit = %s\n" (int2bin nb_solutions p)
        ) constant_bitvectors;
        Printf.printf "\n** All bitvectors\n";
        List.iter (fun p ->
          Printf.printf "bit = %s\n" (int2bin nb_solutions p)
        ) all_bitvectors;
        HullotTree.display_occurrence_data finalized_solutions.nb_elts_t occurence_data;
        flush_all ();
      );

      HullotTree.dfs (fun f_next_dfs p ->
        try 
          Terms.auto_cleanup_noreset (fun () ->
            Ac_config.debug_unification (fun () ->  
              Printf.printf "Building the substitution with %s\n" (int2bin nb_solutions p);
              flush_all ()
            );

            (* No need to occur check when linking the variables. It has been verified during the DFS of Hullot tree. *)
            DiophantineSolutions.suitable_bitsubset_to_substitution finalized_solutions f_AC constants variables ground_constant_status p;

            (* Ac_config.debug_unification (fun () -> 
              Printf.printf "Subst after suuitable_bitsubset: %s\n" (string_of_subst ());
              flush_all ();
            ); *)

            (* We retrieve the new equations to solve equations. *)
            let remaining_equations_ref = ref remaining_equations in
            
            for i = 0 to nb_constants - 1 do
              match ground_constant_status.(i) with
              | None -> ()
              | Some ref_t ->
                  if !ref_t != dummy
                  then 
                    begin 
                      (* Ac_config.debug_unification (fun () -> 
                        Printf.printf "unify_term_and_gather on the term %s and %s\n" (string_of_term constants.(i)) (string_of_term !ref_t);
                        flush_all ()
                      ); *)
                      unify_term_and_gather remaining_equations_ref constants.(i) !ref_t
                    end
            done;

            unify_remaining_equations f_next !remaining_equations_ref
          )
        with Terms.Unify -> f_next_dfs ()
      ) nb_solutions all_bitvectors constant_bitvectors (Some occurence_data)
      
    end

and unify_remaining_equations f_next = function 
  | [] -> f_next ()
  | ((f,_,_) :: _) as remaining_problems ->
      let same_f_equations, other_equations = partition_system_equations f remaining_problems in
      solve_for_unification f_next other_equations f same_f_equations

let unify_terms f_next eq_list = 
  Terms.auto_cleanup (fun () ->
    let remain_ref = ref [] in
    List.iter (fun (t1,t2) -> match t1,t2 with
      | Var v, FunApp(f,_) | FunApp(f,_), Var v when f.f_cat = Failure && v.unfailing = false -> raise Terms.Unify
      | _ -> ()
    ) eq_list;
    List.iter (fun (t1,t2) ->
      unify_term_and_gather remain_ref t1 t2
    ) eq_list;
    unify_remaining_equations f_next !remain_ref
    (* unify_minimal_remaining_equations f_next [] !remain_ref *)
  )

let unify_facts f_next f1 f2 = match f1,f2 with
  | Pred(p1,args1), Pred(p2,args2) ->
      if p1 == p2
      then unify_terms f_next (List.combine args1 args2)
      else raise Terms.Unify

let unify_facts_phase_leq f_next f1 f2 =
  match (f1,f2) with
    Pred(chann1, args1),Pred(chann2,args2) ->
      if not (Terms.is_sub_predicate chann2 chann1) then raise Terms.Unify;
      unify_terms f_next (List.combine args1 args2)

let are_facts_unifiable f1 f2 = match f1,f2 with
  | Pred(p1,args1), Pred(p2,args2) ->
      if p1 == p2
      then unify_terms (fun () -> true) (List.combine args1 args2)
      else false


(** Unification for lemma *)

(** [unify_term_and_gather remaining_equations_ref t1 t2] unifies the terms [t1] and [t2] unless
    they corresponds to an AC equation. In this case, it stores the equations in [remaining_equations_ref].*)
let rec unify_for_lemma_term_and_gather priority_vars remaining_equations_ref t1 t2 = match t1, t2 with 
  | Var v1, Var v2 when v1 == v2 -> ()
  | Var { link = TLink t; _}, t' 
  | t', Var { link = TLink t; _} -> unify_for_lemma_term_and_gather priority_vars remaining_equations_ref t t'
  | Var v1, Var v2 when v1.unfailing -> 
      if List.memq v2 priority_vars && v2.unfailing
      then Terms.link v2 (TLink t1)
      else Terms.link v1 (TLink t2)
  | Var v1, Var v2 when v2.unfailing -> Terms.link v2 (TLink t1)
  | Var v1, FunApp (f_symb,_) when f_symb.f_cat = Failure && v1.unfailing = false -> raise Terms.Unify
  | Var v1, Var v2 when v2.vname.name = Param.def_var_name ->
      if List.memq v1 priority_vars && not (List.memq v2 priority_vars)
      then Terms.link v1 (TLink t2)
      else Terms.link v2 (TLink t1)
  | Var v1, Var v2 -> 
      if List.memq v2 priority_vars
      then Terms.link v2 (TLink t1)
      else Terms.link v1 (TLink t2)
  | FunApp(f_symb,_), Var v when v.unfailing = false && f_symb.f_cat = Failure -> raise Terms.Unify
  | Var v, t 
  | t, Var v -> 
      occurs_check v t;
      Terms.link v (TLink t)
  | FunApp(f1,args1), FunApp(f2,args2) -> 
      if f1 != f2 then raise Terms.Unify;
      List.iter2 (unify_for_lemma_term_and_gather priority_vars remaining_equations_ref) args1 args2
  | FAC(f1,margs1), FAC(f2,margs2) ->
      if f1 != f2 then raise Terms.Unify;
      remaining_equations_ref :=  (f1, margs1, margs2)::!remaining_equations_ref
  | _ -> raise Terms.Unify

(** Solve the system of equations with Occur (non minimal) *)
let rec solve_for_lemma_for_unification f_next priority_vars remaining_equations f_AC system_equations = 
  let (matrix_system,variables,constants,occur_variables,ground_constant_status) = MatrixGeneration.from_unification_equations f_AC system_equations in
  let nb_constants = Array.length constants in
  let nb_variables = Array.length variables in

  Ac_config.debug_unification (fun () -> 
    Printf.printf "** After generating the matrix:\n";
    print_string "Matrix =\n";
    display_matrix string_of_int matrix_system;
    Printf.printf "Variables (%d) = " nb_variables;
    display_vector string_of_variable variables;
    Printf.printf "Constants (%d) = " nb_constants;
    display_vector string_of_term constants;
    flush_all ();
    Printf.printf "Occur_variables = ";
    display_vector (fun (l,bit) -> Printf.sprintf "(%s,%s)" (List.string_of string_of_int "[" "]" ";"  l) (int2bin nb_variables bit)) occur_variables;
    Printf.printf "Ground constants = ";
    display_vector (function None -> "true" | _ -> "false") ground_constant_status;
    flush_all ()
  );

  if nb_variables = 0 && nb_constants = 0 
  then 
    (* The system is trivially true *)
    unify_for_lemma_remaining_equations f_next priority_vars remaining_equations
  else
    begin 
      (* Solving the matrix system of diophantine_equations *)
      let solutions = solve_system_diophantine_equations nb_constants (Some occur_variables) ground_constant_status matrix_system in
    
      Ac_config.debug_unification (fun () -> 
        Printf.printf "\nAfter solving Diophantine equations:\n";
        DiophantineSolutions.display_unfrozen solutions;
        flush_all ()
      );

      let nb_solutions = solutions.DiophantineSolutions.nb_elts in

      if nb_solutions > Sys.int_size - 2
      then failwith "Limit on the number of solutions reached";
    
      if nb_solutions = 0 then raise Terms.Unify;
    
      let finalized_solutions = DiophantineSolutions.finalize nb_constants nb_variables solutions in 
      
      (* Ac_config.debug_unification (fun () -> 
        Printf.printf "** Finalized solutions\n";
        DiophantineSolutions.display finalized_solutions
      ); *)

      (* Bit presentation to subset of solutions *)
      let (constant_bitvectors,all_bitvectors) = DiophantineSolutions.generate_bitvectors ground_constant_status finalized_solutions in
      let occurence_data = DiophantineSolutions.generate_occurrence_data occur_variables finalized_solutions in

      Ac_config.debug_unification (fun () ->  
        Printf.printf "\n** Constant bitvectors\n";
        List.iter (fun p ->
          Printf.printf "bit = %s\n" (int2bin nb_solutions p)
        ) constant_bitvectors;
        Printf.printf "\n** All bitvectors\n";
        List.iter (fun p ->
          Printf.printf "bit = %s\n" (int2bin nb_solutions p)
        ) all_bitvectors;
        HullotTree.display_occurrence_data finalized_solutions.nb_elts_t occurence_data;
        flush_all ();
      );

      HullotTree.dfs (fun f_next_dfs p ->
        try 
          Terms.auto_cleanup_noreset (fun () ->
            Ac_config.debug_unification (fun () ->  
              Printf.printf "Building the substitution with %s\n" (int2bin nb_solutions p);
              flush_all ()
            );

            (* No need to occur check when linking the variables. It has been verified during the DFS of Hullot tree. *)
            DiophantineSolutions.suitable_bitsubset_to_substitution ~exists_vars:(Some priority_vars) finalized_solutions f_AC constants variables ground_constant_status p;

            (* Ac_config.debug_unification (fun () -> 
              Printf.printf "Subst after suuitable_bitsubset: %s\n" (string_of_subst ());
              flush_all ();
            ); *)

            (* We retrieve the new equations to solve equations. *)
            let remaining_equations_ref = ref remaining_equations in
            
            for i = 0 to nb_constants - 1 do
              match ground_constant_status.(i) with
              | None -> ()
              | Some ref_t ->
                  if !ref_t != dummy
                  then 
                    begin 
                      (* Ac_config.debug_unification (fun () -> 
                        Printf.printf "unify_term_and_gather on the term %s and %s\n" (string_of_term constants.(i)) (string_of_term !ref_t);
                        flush_all ()
                      ); *)
                      unify_for_lemma_term_and_gather priority_vars remaining_equations_ref constants.(i) !ref_t
                    end
            done;

            unify_for_lemma_remaining_equations f_next priority_vars !remaining_equations_ref
          )
        with Terms.Unify -> f_next_dfs ()
      ) nb_solutions all_bitvectors constant_bitvectors (Some occurence_data)
      
    end

and unify_for_lemma_remaining_equations f_next priority_vars = function 
  | [] -> f_next ()
  | ((f,_,_) :: _) as remaining_problems ->
      let same_f_equations, other_equations = partition_system_equations f remaining_problems in
      solve_for_lemma_for_unification f_next priority_vars other_equations f same_f_equations

let unify_for_lemma_terms f_next priority_vars eq_list = 
  Terms.auto_cleanup (fun () ->
    let remain_ref = ref [] in
    List.iter (fun (t1,t2) -> match t1,t2 with
      | Var v, FunApp(f,_) | FunApp(f,_), Var v when f.f_cat = Failure && v.unfailing = false -> raise Terms.Unify
      | _ -> ()
    ) eq_list;
    List.iter (fun (t1,t2) ->
      unify_for_lemma_term_and_gather priority_vars remain_ref t1 t2
    ) eq_list;
    unify_for_lemma_remaining_equations f_next priority_vars !remain_ref
  )

let unify_terms_record_fresh_variables f_next l =
  let l' = List.map (fun (t1,t2) -> Terms.copy_term4 t1, Terms.copy_term4 t2) l in
  let vars = ref [] in
  List.iter (fun (t1,t2) -> Terms.get_vars vars t1; Terms.get_vars vars t2) l';

  unify_terms (fun () ->
    let fresh_vars = ref [] in
    List.iter (fun v -> Terms.get_vars_not_in_follow_link2 fresh_vars !vars (Var v)) !vars;
    f_next !fresh_vars
  ) l'