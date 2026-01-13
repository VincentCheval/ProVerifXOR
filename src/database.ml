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
open Terms
open Types
open Pitypes

(** Subsumption of clauses w.r.t. to set and queue of clauses *)

(* [remove_ground_public_terms] removes attacker
   facts (including attackerbin and attacker guess) that
   contain only public ground terms. *)

(* All elements in hypl are public ground terms *)
let rec remove_sure_ground_public_terms accu hypl =
  List.fold_right (fun hyp1 (hypl,nl,histl) -> match hyp1 with
  | Pred(chann,((FunApp(f,_)::_) as l0)),_ ->
      let l = reorganize_fun_app f l0 in
      begin match History.get_rule_hist (RApplyFunc(f,chann)) with
      | Rule(_, _, hyp, _, _) as hist_dec ->
          remove_sure_ground_public_terms (hypl, nl+(List.length l)-1, (Resolution(hist_dec, nl, histl)))
            (List.map2 (fun (Pred(p',_),_) x -> Pred(p', x),NoMarking) hyp l)
      | _ -> Parsing_helper.internal_error "[rules.ml >> remove_sure_ground_public_terms] Unexpected history."
      end
  | Pred(chann,FAC(f,margs)::_),_ ->
      let t1,t2 = match margs with
        | [] | [(_,1)] -> Parsing_helper.internal_error "[rules.ml >> remove_sure_ground_public_terms] Unexpected margs"
        | [(t1,1);(t2,1)] -> t1,t2
        | [t1,2] -> t1,t1
        | (t1,1)::q -> t1, FAC(f,q)
        | (t1,k)::q -> t1, FAC(f,(t1,k)::q)
      in
      begin match History.get_rule_hist (RApplyFunc(f,chann)) with
      | Rule(_, _, hyp, _, _) as hist_dec ->
          remove_sure_ground_public_terms (hypl, nl+1, (Resolution(hist_dec, nl, histl)))
            (List.map2 (fun (Pred(p',_),_) t -> Pred(p', [t]),NoMarking) hyp [t1;t2])
      | _ -> Parsing_helper.internal_error "[rules.ml >> remove_sure_ground_public_terms] Unexpected history."
      end
  | _ -> Parsing_helper.internal_error "[rules.ml >> remove_sure_ground_public_terms] Unexpected terms."
	) hypl accu

let rec remove_ground_public_terms_rec accu hypl =
  List.fold_right (fun hyp1 (hypl,nl,histl) -> match hyp1 with
  | Pred(chann,t::q),mk ->
      if mk = NoMarking && chann.p_prop land Param.pred_ATTACKER != 0 && is_ground_public t && List.for_all (equal_terms t) q
      then remove_sure_ground_public_terms (hypl,nl,histl) [hyp1]
      else (hyp1::hypl, nl-1, histl)
  | _ -> (hyp1::hypl, nl-1, histl)
	) hypl accu

let remove_ground_public_terms ((hypl, concl, hist, constra, variant) as rule:marked_reduction) =
  let (hypl',_,histl') =
    remove_ground_public_terms_rec ([],(List.length hypl)-1,hist) hypl
  in
  if hist == histl' 
  then rule
  else ((hypl',concl,histl',constra, variant):marked_reduction)

(* Raise NoMatch when the subsumption does not hold. *)
let rec implies_ordering_function (ord_fun1:ordering_function) (ord_fun2:ordering_function) =
  match ord_fun1, ord_fun2 with
  | [], _ -> ()
  | _, [] -> raise Unify
  | (i1,_)::q1, (i2,_)::q2 when i2 > i1 -> raise Unify
  | (i1,_)::q1, (i2,_)::q2 when i2 < i1 -> implies_ordering_function ord_fun1 q2
      (* At this point, both lists start with (i,_) for the same i *)
  | (_,Less)::q1, (_,Leq)::q2 -> raise Unify
  | _::q1, _::q2 -> implies_ordering_function q1 q2

(* Functions to compute the size of facts and terms.
   Follows links.*)

let rec count_multiplicity = function 
  | [] -> 0
  | (_,n)::q -> n + count_multiplicity q 

let rec term_size = function
  | Var { link = TLink t } -> term_size t
  | Var _ -> 0
  | FunApp(_,args) -> 1 + term_list_size args
  | FAC(_,margs) -> count_multiplicity margs - 1 + mterm_list_size margs

and term_list_size = function
  | [] -> 0
  | a::l -> term_size a + term_list_size l

and mterm_list_size = function
  | [] -> 0
  | (t,n)::q -> (term_size t) * n + mterm_list_size q


let fact_size = function
  | Pred(_,args) -> 1 + term_list_size args

(* Functions to compute the size of facts and terms.
   Records at the same time if there is a variable without link.
   Does not follow links.*)

let rec term_size_unbound has_unbound = function
  | Var v ->
      if v.link = NoLink
      then has_unbound := true;
      0
  | FunApp(_,args) -> 1 + term_list_size_unbound has_unbound args
  | FAC(_,margs) -> count_multiplicity margs - 1 + mterm_list_size_unbound has_unbound margs


and term_list_size_unbound has_unbound = function
  | [] -> 0
  | a::l -> term_size_unbound has_unbound a + term_list_size_unbound has_unbound l

and mterm_list_size_unbound has_unbound = function
  | [] -> 0
  | (t,n)::q -> (term_size_unbound has_unbound t) * n +  mterm_list_size_unbound has_unbound q

let fact_size_unbound has_unbound = function
  | Pred(_,args) -> 1 + term_list_size_unbound has_unbound args

(* Addition in a sorted list of pairs, in decreasing order of the first component *)
let rec add_in_sorted_list n f l = match l with
  | [] -> [n,f]
  | (n',f')::q -> if n >= n' then (n,f)::l else (n',f')::(add_in_sorted_list n f q)

(********************************************
Check usage of may-fail variables and fail
*********************************************)

let rec check_no_fail = function
    Var v -> assert(not v.unfailing)
  | FunApp(f,l) ->
      assert(f.f_cat != Failure);
      List.iter check_no_fail l
  | FAC(_,margs) -> List.iter (fun (t,_) -> check_no_fail t) margs

let check_top_fail = function
    Var v -> ()
  | FunApp(f,l) -> List.iter check_no_fail l
  | FAC(_,margs) -> List.iter (fun (t,_) -> check_no_fail t) margs

let check_fact_fail = function
    Pred({p_info = TestUnifP _}, [t1;t2]) ->
      begin
        (* testunif: allow fail at the top, plus possibly inside a tuple *)
        match (t1,t2) with
          FunApp(f1,l1), FunApp(f2,l2) when f1 == f2 && f1.f_cat == Tuple ->
            List.iter check_top_fail l1;
            List.iter check_top_fail l2
        | _ ->
            check_top_fail t1;
            check_top_fail t2
      end
  | Pred(p,l) ->
      (* attacker predicates: allow fail at the top
         other predicates: don't allow fail at all *)
      begin
        match (unblock_predicate p).p_info with
          Attacker _ | AttackerBin _ | AttackerGuess _  (* attacker *) ->
            List.iter check_top_fail l
        | UserPred _ (* user-defined *)
        | OtherInternalPred (* event_pred, inj_event_pred, bad_pred, ... *)
        | Equal _ (* equal; used in user-defined clauses *)
        | Mess _ | InputP _ | OutputP _ | MessBin _ | InputPBin _
           | OutputPBin _ | Table _ | TableBin _ | Compromise _ | Combined _ | Subterm _  ->
            List.iter check_no_fail l
        | _ -> Parsing_helper.internal_error "Terms.check_rule: unexpected predicate info"
      end

let check_rule ((hyp, concl, hist, constra, variant) as r:marked_reduction) =
  try
    List.iter (fun (fact,_) -> check_fact_fail fact) hyp;
    check_fact_fail concl;
    iter_constraints check_no_fail constra
  with x ->
    Display.Text.display_rule_indep r;
    raise x

let check_rule_ordered ord_rule = check_rule ord_rule.rule

(***********************************
    Clauses
************************************)

module type ClauseSig =
  sig

    (* the type [hyp_fact] will correspond to either [Types.fact] in the case of a [reduction]
       or to [Types.fact * ordering_function] in the case of an [ordered_reduction] *)
    type hyp_fact

    type t

    val empty_clause : t

    val get_reduction : t -> marked_reduction

    val is_variant_AC : t -> bool

    (**
      [match_facts f_next comply_with_marking hyp1 hyp2] apply [f_next] on each most general substition [\sigma] 
      such that [hyp1\sigma =_AC hyp2]. When [comply_with_marking = true] then [hyp1] has static (resp. dynamic)
      marking implies that [hyp2] also has static (resp. dynamic) marking.
      @raise Terms.Unify when the facts cannot be matched.
      
      In the case of [ordered_reduction], [match_facts hfact1 hhfact2] it will also check that
      the ordering function of [hfact1] subsumes the ordering function of [hfact2]
    *)
    val match_facts : (unit -> 'a) -> bool -> hyp_fact -> hyp_fact -> 'a

    (** Same as [match_facts] but on closed hypotheses (more efficient). *)
    val match_closed_fact : bool -> hyp_fact -> hyp_fact -> unit

    val fact_of_hyp_fact : hyp_fact -> fact

    val get_clause_with_hyp_fact : t -> (hyp_fact list * fact * history * constraints * bool)

    (* [simplify_remove_hyp] simplifies a clause by removing some of its
       hypotheses, so that the obtained clause subsumes the original one.
       In practice, we remove attacker facts containing ground public terms *)
    val simplify_remove_hyp : t -> t

    val remove_marking : t -> t

    val check : t -> unit

    val display : t -> unit

    val display_indep : t -> unit

    val display_hyp_fact : hyp_fact -> unit
  end

(***********************************
    Subsumption
************************************)

(** Additional data depending on whether the clause is solved or not. *)
type additional_data = 
  | Solved of bool (** [true] when it can be used for global redundancy *)
  | Unsolved of int (** Index of selected fact *) * marking (** Marking on the selected fact *)

module type SubsumptionSig =
  sig
    type hyp_fact
    type clause

    type subsumption_data =
      {
        (* For an element (s,hfact) in the lists, [s] is the size of the fact of [hfact]. *)
        bound_facts : (int * hyp_fact) list; (* List are always kept in decreasing order w.r.t. the first projection of the pair *)
        unbound_facts : (int * hyp_fact) list (* List are always kept in decreasing order w.r.t. the first projection of the pair *)
      }

    type sub_annot_clause = clause * subsumption_data * additional_data

    val empty_sub_data : subsumption_data
    val empty_sub_annot_clause : sub_annot_clause

   (* In the following functions, a clause can always be seen as its reduction part and its subsumption data part.
      For instance, when a clause is an ordered_reduction, the subsumption data contains the ordering function of the clause.

      For example, on a reduction R = (H && \phi -> C), the subsumption data [sub_data] of R is such that:
        - [sub_data.bound_facts] is the list of facts in H (with their size) that contains only variables of C
        - [sub_data.unbound_facts] are the remaining facts of H (with their size). Hence all facts in [sub_data.unbound_facts]
          contain a variable not in C.

      When R is an ordered reduction, it's similar except that [sub_data.bound_facts] and [sub_data.unbound_facts] also contain
      the ordering functions associated to the ordered facts in H.

      As mentioned above, [sub_data.bound_facts] and [sub_data.unbound_facts] are sorted by decreasing size.
    *)

    (* [implies r1 r2] returns true iff the rule [r1] implies/subsumes the rule [r2],
       where [r1] and [r2] are clauses with associated subsumption data. *)
    val implies : sub_annot_clause -> sub_annot_clause -> bool

    (* [implies_redundant r1 r2] returns a pair of booleans [(r_implies,block_set_implies)]
       where [r_implies] is true when [r1] implies/subsumes [r2]
       and [block_set_implies] is true when the blocking predicates part [Hblock1] of
       [r1 = Hblock1 && Hother1 -> C1] "subsumes" that part [Hblock2] of
       [r2 = Hblock2 && Hother2 -> C2], i.e. there exists a substitution [sigma] such that
       [sigma C1 = C2] and [sigma Hblock1 \subseteq Hblock2] for set inclusion.
       (When [block_set_implies] is false, subsumption cannot become true
       after future resolutions so we can cut this branch when we determine
       whether a clause is redundant.) *)
    val implies_redundant : (clause * subsumption_data) -> (clause * subsumption_data) -> bool

    (* Similar to [implies] except that we do not apply an initial test on the number of hypotheses in the rule.
       This function is only used in combination with the feature vector. *)
    val implies_no_test : sub_annot_clause -> sub_annot_clause -> bool

    (* [generate_subsumption_data r] generates the subsumption data associated to [r]. *)
    val generate_subsumption_data : clause -> clause * subsumption_data

  end

module MakeSubsumption (C:ClauseSig) =
  struct

    type hyp_fact = C.hyp_fact
    type clause = C.t

    type subsumption_data =
      {
        bound_facts : (int * hyp_fact) list;
        unbound_facts : (int * hyp_fact) list
      }

    type sub_annot_clause = clause * subsumption_data * additional_data

    let empty_sub_data = { bound_facts = []; unbound_facts = [] }
    let empty_sub_annot_clause = (C.empty_clause, empty_sub_data, Solved false)

    (** Functions required for multiset subsumption *)

    (* Functions matching hypotheses that only contain variables
       bound by the conclusion of the clause. *)

    (** [match_fact_bound_with_hyp size1 fact1 passed_hyp hyp2]
       raises [Terms.Unify] when the matching of [fact1] with any fact of [hyp2] fails,
       returns [hyp2'] when it succeeds, where [hyp2'] is the list of
       unused elements of [passed_hyp] and [hyp2].

       [size1] is the size of [fact1] including the links, i.e. [fact1\sigma] *)
    let rec multiset_match_fact_bound_with_hyp size1 fact1 passed_hyp = function
      | [] -> raise Terms.Unify
      | ((size2,fact2) as f2) :: fact_l2 ->
          (* Since [fact1] contains only variables from the conclusion, the instantiation of [fact1] must be
             equal to one of the facts in the hypotheses of the second clause. *)
          if size2 > size1
          then multiset_match_fact_bound_with_hyp size1 fact1 (f2::passed_hyp) fact_l2
          else if size2 = size1
          then
            try
              (* Since [fact1] is bound, the matching actually creates no link *)
              C.match_closed_fact true fact1 fact2;
              List.rev_append passed_hyp fact_l2
            with Terms.Unify ->
              multiset_match_fact_bound_with_hyp size1 fact1 (f2::passed_hyp) fact_l2
          else raise Terms.Unify

    let rec multiset_match_hyp_bound hyp1 hyp2_bound = match hyp1 with
      | [] -> hyp2_bound
      | (_,fact1) :: fact_l1 ->
          let size1 = fact_size (C.fact_of_hyp_fact fact1) in
          let hyp2_bound' = multiset_match_fact_bound_with_hyp size1 fact1 [] hyp2_bound in
          (* Success *)
          (** When [match_fact_bound_with_hyp size1 fact1 [] hyp2_bound] raises [Unify],
             [fact1] could not be matched with any fact in [hyp2_bound], we do not need to
             try the unbound hypotheses of clause 2 [hyp2_unbound] for the following reason.

             If we have a clause R1 = F1 ... -> C1 and F1 is bound and
             a clause R2 = F2 ... -> C2 where F2 is unbound. All
             variables of F1 are in C1. When we match C1 with C2, we
             obtain F1\sigma and all its variables are in C2. Now,
             since F2 is "unbound", F2 contains variables not in C2, so
             F2 cannot be equal to F1\sigma. Conclusion: it is enough
             to match "bound" facts of R1 with bound facts of R2.

             In this case, the whole function call raises [Unify]  *)
          multiset_match_hyp_bound fact_l1 hyp2_bound'
          
    (* Functions matching hypotheses that contain variables
       unbound by the conclusion of the clause. *)

    let rec multiset_match_fact_with_hyp nextf fact1 passed_hyp = function
      | [] -> raise Terms.Unify
      | ((_,fact2) as f2)::fact_l ->
          try
            Terms.auto_cleanup (fun () ->
              C.match_facts (fun () ->
                nextf (List.rev_append passed_hyp fact_l)
              ) true fact1 fact2;
            )
          with Terms.Unify ->
            multiset_match_fact_with_hyp nextf fact1 (f2 :: passed_hyp) fact_l

    let rec multiset_match_hyp nextf hyp1 hyp2 = match hyp1 with
      | [] -> nextf ()
      | (_,fact1) :: fact_l1 -> multiset_match_fact_with_hyp (multiset_match_hyp nextf fact_l1) fact1 [] hyp2

    (** Functions required for set subsumption *)

    (** [size1] is the size of [fact1] including the links, i.e. [fact1\sigma]*)
    let rec set_match_fact_bound_with_hyp size1 fact1 = function
      | [] -> raise Terms.Unify
      | (size2,fact2) :: fact_l2 ->
          (* Since [fact1] contains only variables from the conclusion, the instantiation of [fact1] must be
             equal to one of the facts in the hypotheses of the second clause. *)
          if size2 > size1
          then set_match_fact_bound_with_hyp size1 fact1 fact_l2
          else if size2 = size1
          then
            try
              (* Since [fact1] is bound, the matching actually creates no link *)
              C.match_closed_fact false fact1 fact2;
            with Terms.Unify ->
              set_match_fact_bound_with_hyp size1 fact1 fact_l2
          else raise Terms.Unify

    let set_match_hyp_bound hyp1 hyp2_bound =
      List.iter (fun (_,hyp_fact1) ->
        let size1 = fact_size (C.fact_of_hyp_fact hyp_fact1) in
        set_match_fact_bound_with_hyp size1 hyp_fact1 hyp2_bound
      ) hyp1

    let rec set_match_fact_with_hyp nextf fact1 = function
      | [] -> raise Terms.Unify
      | (_,fact2)::fact_l ->
          try
            Terms.auto_cleanup (fun () ->
              C.match_facts nextf false fact1 fact2;
            )
          with Terms.Unify ->
            set_match_fact_with_hyp nextf fact1  fact_l

    let rec set_match_hyp nextf hyp1 hyp2 = match hyp1 with
      | [] -> nextf ()
      | (_,fact1) :: fact_l1 ->
          set_match_fact_with_hyp (fun () -> set_match_hyp nextf fact_l1 hyp2) fact1 hyp2

    (* Main function for subsumption of two clauses. *)

    let implies_conclusion f_next concl1 concl2 = match concl1 with
      | Pred(p, []) when p == Param.bad_pred -> f_next ()
      | _ -> 
        match concl1, concl2 with 
        | Pred(f1,args1), Pred(f2,args2) ->
            if f1 != f2 then raise Unify;
            AC.Ac_unify.match_terms f_next (List.combine args1 args2)

    let implies_variant_hierarchy variant1 add_data1 variant2 add_data2 = match add_data1, add_data2 with
      | Solved _, _ -> true
      | _, Solved _ -> false
      | _ -> not variant2 || variant1

    let implies_internal ((_,concl1,_,constr1,variant1):marked_reduction) sub_data1 add_data1 ((hyp2,concl2,_,constr2,variant2):marked_reduction) sub_data2 add_data2 =
      match add_data1, add_data2, variant1, variant2 with
      | Solved _, _, _, _
      | Unsolved _, Unsolved _, true, false -> 
          begin try
            (* Set subsumption hence we ignore marking *)
            Terms.auto_cleanup (fun () ->
              let all_hyp2 = sub_data2.bound_facts @ sub_data2.unbound_facts in
              implies_conclusion (fun () ->
                set_match_hyp_bound sub_data1.bound_facts sub_data2.bound_facts;
                (* All facts of [elt1.bound_facts] have been matched. *)
                set_match_hyp (fun () ->
                  TermsEq.implies_constraints_keepvars3 (concl2 :: List.rev_map (fun (f,_) -> f) hyp2) constr2 constr1
                ) sub_data1.unbound_facts all_hyp2;
                true
              ) concl1 concl2
            )
          with Terms.Unify -> false
          end
      | Unsolved _, Unsolved _, _, _ -> 
          begin try
          Terms.auto_cleanup (fun () ->
            implies_conclusion (fun () ->
              let r2_bound_facts = multiset_match_hyp_bound sub_data1.bound_facts sub_data2.bound_facts in
              (* All facts of [elt1.bound_facts] have been matched. *)
              multiset_match_hyp (fun () ->
                TermsEq.implies_constraints_keepvars3 (concl2 :: List.rev_map (fun (f,_) -> f) hyp2) constr2 constr1
              ) sub_data1.unbound_facts (r2_bound_facts @ sub_data2.unbound_facts);
              true
            ) concl1 concl2
          )
        with Terms.Unify -> false
        end
      | _ -> false

    let implies (cl1, sub_data1, add_data1) (cl2, sub_data2, add_data2) =
      let ((hyp1,_,_,_,variant1) as r1) = C.get_reduction cl1 in
      let ((hyp2,_,_,_,variant2) as r2) = C.get_reduction cl2 in
      match add_data1, add_data2, variant1, variant2 with
      | Solved _, _, _, _
      | Unsolved _, Unsolved _, true, false -> 
          implies_internal r1 sub_data1 add_data1 r2 sub_data2 add_data2
      | Unsolved _, Unsolved _, _, _ -> 
          let ((hyp1,_,_,_,_) as r1) = C.get_reduction cl1 in
          let ((hyp2,_,_,_,_) as r2) = C.get_reduction cl2 in
          if List.length hyp1 > List.length hyp2
          then false
          else implies_internal r1 sub_data1 add_data1 r2 sub_data2 add_data2
      | _ -> false

    (* let implies (cl1, sub_data1, add_data1) (cl2, sub_data2, add_data2) =
      let r = implies (cl1, sub_data1, add_data1) (cl2, sub_data2, add_data2) in
      if r 
      then begin
      Printf.printf "** Implies:\n ";
      print_string "  rule 1: ";
      Display.Text.display_rule_indep (C.get_reduction cl1);
      print_string "  rule 2: ";
      Display.Text.display_rule_indep (C.get_reduction cl2);
      Printf.printf "  result: %b\n" r;
      end;
      r *)

    let implies_no_test (cl1, sub_data1, add_data1) (cl2, sub_data2, add_data2) =
      let red1 = C.get_reduction cl1 in
      let red2 = C.get_reduction cl2 in
      implies_internal red1 sub_data1 add_data1 red2 sub_data2 add_data2

    (* let implies_no_test (cl1, sub_data1, add_data1) (cl2, sub_data2, add_data2) =
      let r = implies_no_test (cl1, sub_data1, add_data1) (cl2, sub_data2, add_data2) in
      if r 
      then begin
      Printf.printf "** Implies_no_test:\n ";
      print_string "  rule 1: ";
      Display.Text.display_rule_indep (C.get_reduction cl1);
      print_string "  rule 2: ";
      Display.Text.display_rule_indep (C.get_reduction cl2);
      
      Printf.printf "  result: %b\n" r;
      end;
      r *)

    let implies_redundant (cl1, sub_data1) (cl2, sub_data2) = 
      let (_,concl1,_,constr1,_) = C.get_reduction cl1 in
      let (hyp2,concl2,_,constr2,_) = C.get_reduction cl2 in
      try
        (* Set subsumption hence we ignore marking *)
        Terms.auto_cleanup (fun () ->
          let all_hyp2 = sub_data2.bound_facts @ sub_data2.unbound_facts in
          implies_conclusion (fun () ->
            set_match_hyp_bound sub_data1.bound_facts sub_data2.bound_facts;
            (* All facts of [elt1.bound_facts] have been matched. *)
            set_match_hyp (fun () ->
              TermsEq.implies_constraints_keepvars3 (concl2 :: List.rev_map (fun (f,_) -> f) hyp2) constr2 constr1
            ) sub_data1.unbound_facts all_hyp2;
            true
          ) concl1 concl2
        )
      with Terms.Unify -> false

    (* Function for computing the subsumption data of a clause. *)

    let generate_subsumption_data rule =
      let (hyp,concl,_,_,_) = C.get_clause_with_hyp_fact rule in

      Terms.auto_cleanup (fun () ->
        (* Mark variables in conclusion *)
        Terms.mark_variables_fact concl;

        (* We split the hypotheses in two lists depending on
           whether the fact has unbound variables or not. *)
        let unbound_facts = ref [] in
        let bound_facts = ref [] in

        List.iter (fun fact ->
          let has_unbound = ref false in
          let size = fact_size_unbound has_unbound (C.fact_of_hyp_fact fact) in
          if !has_unbound
          then unbound_facts := add_in_sorted_list size fact !unbound_facts
          else bound_facts := add_in_sorted_list size fact !bound_facts
               ) hyp;

        rule, { bound_facts = !bound_facts; unbound_facts = !unbound_facts })

  end

(***********************************
    Features
************************************)

(* Width of a symbol in a term:
    An occurrence of a symbol f in a term t is at width w if:
      - t = f(t_1,...,t_n) and w = 0
      - t = C[g(r_1,...,r_{i-1},f(t_1,...,t_n),r_{i+1},...,r_m)] and w = i
*)

(* We consider the following features for a clause H -> C and we explain their
   value v. Note that each recorded symbol and predicate has a unique non negative
   identifier (in f.f_record or p.p_record)
    - Bad : v = 0 when the conclusion is bad, otherwise v = 1
    - NbHyp : v = |H|, i.e. number of hypotheses
    - Occ i_f :
        if i_f < 0 then v = number of occurrences in the conclusion of a symbol
          f with identifier -i_f.
        if i_f > 0 then v = number of occurrences in the hypotheses of a symbol
          f with identifier i_f.
    - Depth(i_f,d) :
        if i_f < 0 then v = number of occurrences at depth d in the conclusion
          of a symbol f with identifier -i_f
        if i_f > 0 then v = number of occurrences at depth d in the hypotheses
          of a symbol f with identifier i_f
        if d = -1 then it records the maximal depth of symbol f
    - Width(i_f,w) :
        if i_f < 0 then v = number of occurrences at width w in the conclusion
          of a symbol f with identifier -i_f
        if i_f > 0 then v = number of occurrences at width w in the hypotheses
          of a symbol f with identifier i_f
    - CapAll : v = number of occurrence of all non-recorded symbols in the clause
*)

type feature =
  | Bad
  | NbHyp
  | Occ of int
  | Depth of int * int
  | Width of int * int
  | CapAll

(* We order the features as follows:
  -> Bad < Occ < NhHyp < Depth < Width < CapAll.
  -> Occ(i) < Occ(i') when i < i'
  -> Depth(i_f,d) < Depth(i_f',d') when i_f < i_f' or (i_f = i_f' and d < d')
  -> Width(i_f,w) < Width(i_f',w') when i_f < i_f' or (i_f = i_f' and w < w')
*)

(* We will always assume that a feature_vector is always ordered increasingly
   using the lexicographic order.

   The list represents all the non-zero values of the feature inside a feature vector.
   For example, assume that we have in total [5] features F_1 ... F_5 (according to the order,
   F_1 is Bad and F_2 is NbHyp).

   If a clause has as feature vector (0,2,1,0,3) then its representation would be:
    [(F_2,2);(F_3,1);(F_5,3)]
*)
type feature_vector = (feature * int) list

(***** Recording the function symbols and predicates *****)

(* Record functions *)

let record_counter = ref 0

let record_fun f =
  if !Param.record_funs && f.f_record <= 0
  then
    begin
      incr record_counter;
      f.f_record <- !record_counter
    end

let record_name f =
   if !Param.record_names && f.f_record <= 0
   then
     begin
       incr record_counter;
       f.f_record <- !record_counter
     end

let record_predicate p =
  if !Param.record_predicates && p.p_record == 0
  then
    begin
      incr record_counter;
      p.p_record <- !record_counter
    end

let record_event ev =
  if !Param.record_events && ev.f_record <= 0
  then
    begin
      incr record_counter;
      ev.f_record <- !record_counter
    end

let record_table t =
  if !Param.record_tables && t.f_record <= 0
  then
    begin
      incr record_counter;
      t.f_record <- !record_counter
    end

let get_root f_next t =
  try
    f_next (Terms.get_root t)
  with Not_found -> ()

let record_from_fact = function
  | Pred({ p_info = Table _},[t]) -> get_root record_table t
  | Pred({ p_info = TableBin _},[t1;t2]) ->
      get_root record_table t1;
      get_root record_table t2
  | Pred(p,[t]) when p == Param.event_pred_block || p == Param.event_pred ->
      get_root record_event t
  | Pred(p,[t1;t2]) when p == Param.event2_pred_block || p == Param.event2_pred ->
      get_root record_event t1;
      get_root record_event t2
  | Pred(p,[t;_]) when p == Param.inj_event_pred || p == Param.inj_event_pred_block ->
      get_root record_event t
  | Pred(p,_) -> record_predicate p

let record_from_rule (hypl,concl,_,_,_) = List.iter record_from_fact (concl::(List.map (fun (f,_) -> f) hypl))

(***** Comparison *****)

let compare_feature f1 f2 = match f1, f2 with
  | Bad, Bad -> 0
  | Bad, _ -> -1
  | _, Bad -> 1
  | Occ i, Occ i' -> i - i'
  | Occ _, _ -> -1
  | _, Occ _ -> 1
  | NbHyp, NbHyp -> 0
  | NbHyp, _ -> -1
  | _, NbHyp -> 1
  | Depth(i,d), Depth(i',d') -> let c = i - i' in if c = 0 then d - d' else c
  | Depth _, _ -> -1
  | _, Depth _ -> 1
  | Width(i,w), Width(i',w') -> let c = i - i' in if c = 0 then w - w' else c
  | Width _, _ -> -1
  | _, Width _ -> 1
  | _ -> 0

(***** Display *****)

let display_feature = function
  | Bad -> "Bad"
  | NbHyp -> "NbHyp"
  | Occ i -> Printf.sprintf "Occ %d" i
  | Depth(i,d) -> Printf.sprintf "Depth(%d,%d)" i d
  | Width(i,d) -> Printf.sprintf "Width(%d,%d)" i d
  | CapAll -> "CapAll"

let display_feature_vector =
  Display.Text.display_list (fun (v,i) -> Printf.printf "(%s,%d)" (display_feature v) i) ";"

(***** Generation of feature vector *****)

module Int =
  struct
    type t = int
    let compare x y = -(compare x y)
  end

module IMap = Tree.MakeOne(Int)

module type FeatureGenerationSig =
  sig
    type subsumption_data
    type clause
    type annot_clause = clause * feature_vector * subsumption_data

    (* [initialize ()] needs to be executed before starting saturating clauses. *)
    val initialize : unit -> unit

    val generate_feature_vector_and_subsumption_data : clause -> clause * feature_vector * subsumption_data
  end

module MakeFeatureGeneration (C:ClauseSig) (S:SubsumptionSig with type hyp_fact = C.hyp_fact and type clause = C.t) =
  struct

    type subsumption_data = S.subsumption_data
    type clause = C.t
    type annot_clause = clause * feature_vector * subsumption_data

    let initialize () = ()

    let generate_feature_vector_and_subsumption_data (rule:C.t) =
      let (rule, sub_data) = S.generate_subsumption_data rule in
      ((rule, [], sub_data))
  end

(***********************************
    Feature Trie
************************************)

module FeatureTrie =
  struct

    module FV =
      struct
        type t_fst = feature
        type t_snd = int
        type t = t_fst * t_snd

        let compare_fst fe1 fe2 = - (compare_feature fe1 fe2)
        let compare_snd = compare
      end

    module FVTree = Tree.Make(FV)

    type 'a t =
      | Node of 'a t FVTree.t * 'a list
      | Empty

    let empty = Empty

    let create elt (fe_vec:feature_vector) =

      let rec create_trie = function
        | [] -> Node (FVTree.empty,[elt])
        | fev :: q_vec ->
            let trie = create_trie q_vec in
            Node (FVTree.singleton fev trie, [])
      in

      create_trie fe_vec

    let add t elt (fe_vec:feature_vector) =

      let rec explore_tree t fe_vec = match t, fe_vec with
        | Empty, _ -> create elt fe_vec
        | Node(fe_map,elt_l), [] -> Node(fe_map,elt::elt_l)
        | Node(fe_map,elt_l), fe::q_vec ->
            let fe_map' =
              FVTree.update fe (function
                | None ->
                    (* The feature is not present in the map *)
                    Some (create elt q_vec)
                | Some t' ->
                    (* The feature is present in the map *)
                    Some (explore_tree t' q_vec)
              ) fe_map
            in
            Node(fe_map',elt_l)
      in

      explore_tree t fe_vec

    (* [exists_leq p fe_vec t] returns true if there exists an element of [t] with
       feature vector less or equal to [fe_vec] that satisfies the predicate [p] *)
    let rec exists_leq p fe_vec t = match t, fe_vec with
      | Empty, _ -> false
      | Node(_,elt_l), [] ->
          (* Only the elements with empty feature vector can be less or equal *)
          List.exists p elt_l
      | Node(fe_map,elt_l), (fe,v)::q_vec ->
          (* Since feature_vector are always sorted in increasing order w.r.t. compare_feature, we have
             that [fe_vec] is sorted in decreasing order w.r.t. FV.compare_fst.

             Since we need to find the element with a feature vector [fe_vect'] smaller than [fe_vec],
             we deduce that [fe_vect'] starts with (fe',v') with either
             - fe' = fe but v' <= v : In that case, we compare the rest of the feature_vector [q_vec] with
               the elements associated to [(fe',v')] in [fe_map].
             - fe' > fe : Note that in full representation, fe' > fe implies that the value of fe on the
               elements associated to [(fe',v')] in [fe_map] is necessary 0. Note that fe' > fe implies fe' is
               strictly smaller than fe w.r.t. FV.compare_fst
             - The case fe' < fe is impossible as it would imply that the value of fe' on t would be 0
               and so the feature vector of all elements associated to fe_map would not be smaller than
               [fe_vec].
          *)
          (* We need to look in fe_map the branches that have a feature smaller than fe. *)

          (* The elements with no positive features are smaller *)
          List.exists p elt_l || FVTree.exists_leq (exists_leq p) (fe,v) q_vec fe_map

    let rec iter f_iter = function
      | Empty -> ()
      | Node(fe_map,elt_l) ->
          List.iter f_iter elt_l;
          FVTree.iter (iter f_iter) fe_map

    let rec iter_geq f_iter fe_vec t = match t, fe_vec with
      | _, [] ->
          (* All elements of the trie have a feature vector bigger than fe_vec *)
          iter f_iter t
      | Empty, _ -> ()
      | Node(fe_map,_), (fe,v)::q_vec ->
          (* The elements with no positive features are strictly smaller hence
             we do not apply [f_iter] on them. *)
          FVTree.iter_geq (iter_geq f_iter fe_vec) (iter_geq f_iter q_vec) (fe,v) fe_map

    let rec filter f = function
      | Empty -> Empty
      | Node(fe_map,elt_l) ->
          let elt_l' = List.filter f elt_l in
          let fe_map' =
            FVTree.update_all (fun t ->
              match filter f t with
                | Empty -> None
                | t' -> Some t'
            ) fe_map
          in
          if elt_l' = [] && FVTree.is_empty fe_map'
          then Empty
          else Node(fe_map',elt_l')
  end

(***********************************
    Unification Trie
************************************)

module UnificationTrie =
struct
  type 'a t = 'a list

  let empty = []

  let is_empty t = t = []

  let add t elt _ = elt :: t

  let iter = List.iter 

  let iter_unify f t _ = List.iter f t
  
  let filter = List.filter
end

(***********************************
    Set of clauses
************************************)

module type SetSig =
  sig
    type clause
    type subsumption_data
    type sub_annot_clause = clause * subsumption_data * additional_data
    type annot_clause = clause * feature_vector * subsumption_data * additional_data

    type active_status = Active | Inactive | Removed

    type element =
      {
        mutable annot_clause: sub_annot_clause;
        mutable selected_fact: fact;
        mutable active : active_status;
      }

    type t

    (* The empty set *)
    val create : unit -> t

    (* Should not be applied on an element that is already active. *)
    val activate : t -> element -> unit

    (* Should not be applied on an element that is already inactive. *)
    val deactivate : t -> element -> unit

    (* [add set annot_cl uni_fact] adds to [set] the annotated clause [cl].
       (An annotated clause is a clause with associated feature vector
       and subsumption data.)
       [uni_fact] is the selected fact of [cl].
       Note that [cl] is active in the resulting set. *)
    val add : t -> annot_clause -> fact -> unit

    (* [implies set annot_cl] checks whether an active clause from [set] implies
       the annotated clause [cl]. *)
    val implies : t -> annot_clause -> bool

    (* [deactivate_implied_by empty_add_data set annot_cl] deactivates the clauses from [set]
       that are implied by the annotated clause [annot_cl].
       [empty_add_data] is a empty additional data value, that replaces the additional
       data of deactivated clauses. *)
    val deactivate_implied_by : t -> annot_clause -> unit

    (* [cleanup_deactivated set] removes the deactivated clauses in [set] *)
    val cleanup_deactivated : t -> unit

    (* [iter f set] applies [f] to all active clauses *)
    val iter : (element -> unit) -> t -> unit

    (* [iter_unifiable f set fact] applies [f] to all active clauses in [set]
       whose selected fact may be unifiable with [fact] *)
    val iter_unifiable : (element -> unit) -> t -> fact -> unit

    (* [length set] returns the number of active clauses in [set]. *)
    val length : t -> int

    (* [to_list set] returns the list of active clauses in [set]. *)
    val to_list : t -> clause list

    (* [exists f set] returns [true] if there exists an active clause [cl] in [set]
       such that [f cl = true]. *)
    val exists : (clause -> bool) -> t -> bool
  end

module MakeSet (C:ClauseSig) (S:SubsumptionSig with type hyp_fact = C.hyp_fact and type clause = C.t) =
  struct
    type clause = C.t
    type subsumption_data = S.subsumption_data
    type sub_annot_clause = clause * subsumption_data * additional_data
    type annot_clause = clause * feature_vector * subsumption_data * additional_data

    type active_status = Active | Inactive | Removed

    type element =
      {
        mutable annot_clause: sub_annot_clause;
        mutable selected_fact: fact;
        mutable active : active_status
      }

    type t =
      {
        mutable trie : element FeatureTrie.t;
        mutable unify_trie : (predicate * (element  UnificationTrie.t)) list;
        mutable elt_list : element list;
        mutable nb_total : int;
        mutable nb_deactive : int
      }

    let create () = { trie = FeatureTrie.empty; unify_trie = []; elt_list = []; nb_total = 0; nb_deactive = 0 }

    let activate set elt =
      assert (elt.active == Inactive);
      elt.active <- Active;
      set.nb_deactive <- set.nb_deactive - 1

    let deactivate set elt =
      assert (elt.active == Active);
      elt.active <- Inactive;
      set.nb_deactive <- set.nb_deactive + 1

    let rec update_in_list p f = function
      | [] -> [p,f (UnificationTrie.empty)]
      | (p',tree)::q when p == p' -> (p',f tree)::q
      | t::q -> t::(update_in_list p f q)

    let add set ((cl, vector, sub_data, add_data):annot_clause) sel_fact  =
      let elt = { annot_clause = (cl, sub_data, add_data); selected_fact = sel_fact; active = Active } in
      let Pred(p,args) = sel_fact in
      set.unify_trie <- update_in_list p (fun tree -> UnificationTrie.add tree elt args) set.unify_trie;
      if !Param.feature then
        set.trie <- FeatureTrie.add set.trie elt vector;
      set.elt_list <- elt :: set.elt_list;
      set.nb_total <- set.nb_total + 1


    (* [implies set vector cl] checks whether a clause from [set] implies (w.r.t. [f_implies])
       the clause [cl] that have [vertor] as feature vector. *)
    let implies set ((cl, vector, sub_data, add_data):annot_clause) =
      let test_fun elt =
        elt.active == Active && S.implies_no_test elt.annot_clause (cl, sub_data, add_data)
      in
      if !Param.feature then
	      FeatureTrie.exists_leq test_fun vector set.trie
      else
	      List.exists test_fun set.elt_list

    let deactivate_implied_by set (cl, vector, sub_data, add_data) =
      if !Param.feature then
        FeatureTrie.iter_geq (fun elt ->
          if elt.active == Active && S.implies_no_test (cl, sub_data, add_data) elt.annot_clause
          then
            begin
              elt.annot_clause <- S.empty_sub_annot_clause; (* Remove the clause, so that it can be garbage collected *)
              elt.selected_fact <- Param.dummy_fact;
              elt.active <- Removed;
              set.nb_deactive <- set.nb_deactive + 1
            end
	      ) vector set.trie
      else
        set.elt_list <- List.filter (fun elt ->
          match elt.active with
          | Removed -> assert false
          | Inactive -> true
          | Active ->
              if S.implies_no_test (cl, sub_data, add_data) elt.annot_clause
              then
                begin
                  set.nb_total <- set.nb_total - 1;
                  false
                end
              else
                true
        ) set.elt_list

    let rec cleanup_deactivated_unify_trie = function
      | [] -> []
      | (p,t)::q ->
          let t' = UnificationTrie.filter (fun elt -> elt.active == Active) t in
          if UnificationTrie.is_empty t'
          then cleanup_deactivated_unify_trie q
          else (p,t')::(cleanup_deactivated_unify_trie q)

    let cleanup_deactivated set =
      if set.nb_total != 0 && (set.nb_deactive * 100) / set.nb_total > !Param.cleanup_threshold
      then
        begin
          let f elt = (elt.active == Active) in
	  if !Param.feature then
            set.trie <- FeatureTrie.filter f set.trie;
          set.unify_trie <- cleanup_deactivated_unify_trie set.unify_trie;
          set.elt_list <- List.filter f set.elt_list;
          set.nb_total <- set.nb_total - set.nb_deactive;
          set.nb_deactive <- 0
        end

    let iter f set =
      List.iter (fun elt ->
	      if elt.active == Active then f elt
	    ) set.elt_list

    let iter_unifiable f set = function
      | Pred(p,args) ->
          try
            let tree = List.assq p set.unify_trie in
            UnificationTrie.iter_unify (fun elt ->
              if elt.active == Active then f elt
            ) tree args
          with Not_found -> ()

    let length set = set.nb_total - set.nb_deactive

    let to_list set =
      let rec to_list_rec acc = function
        | [] -> List.rev acc
        | elt::q ->
            if elt.active == Active then
              let (clause, _, _) = elt.annot_clause in
              to_list_rec (clause::acc) q
            else
	            to_list_rec acc q
      in
      to_list_rec [] set.elt_list

    let exists f set = 
      List.exists (fun elt -> 
        elt.active == Active && 
        let (cl,_,_) = elt.annot_clause in 
        f cl
      ) set.elt_list
  end

(***********************************
    Queue of clauses
************************************)

module type QueueSig =
  sig

    type clause
    type subsumption_data
    type annot_clause = clause * feature_vector * subsumption_data * additional_data
    type t

    (* Generate a new queue *)
    val new_queue : unit -> t

    (* [add q annot_cl] adds to the queue [q] the annotated clause [cl] *)
    val add : t -> annot_clause -> unit

    (* [get q] takes the first clause of the queue with its respective feature
      vector and implication data. Note that the resulting clause is always activated. *)
    val get : t -> annot_clause option

    (* [implies q annot_cl] checks whether an active clause from [q] implies the
       annotated clause [cl]. *)
    val implies : t -> annot_clause -> bool

    (* [deactivate_implied_by q annot_cl] deactivates the clauses from [q]
       that are implied by the annotated clause [cl] *)
    val deactivate_implied_by : t -> annot_clause -> unit

    (* [cleanup_deactivated q] removes the deactivated clauses in [q]. *)
    val cleanup_deactivated : t -> unit

    (* [iter f q] applies [f] on each active clause of the queue [q]. *)
    val iter : (annot_clause -> unit) -> t -> unit

    (* [length q] returns the number of clauses in [q]. *)
    val length : t -> int
  end

module MakeQueue (C:ClauseSig) (S:SubsumptionSig with type hyp_fact = C.hyp_fact and type clause = C.t) =
  struct

    type clause = C.t
    type subsumption_data = S.subsumption_data
    type annot_clause = clause * feature_vector * subsumption_data * additional_data

    type element =
      {
        mutable prev : element option;
        mutable next : element option;
        mutable active : bool;
	      mutable annot_clause : annot_clause
      }

    type t =
      {
        mutable qstart : element option;
        mutable qend : element option;
        mutable trie : element FeatureTrie.t;
        mutable nb_total : int;
        mutable nb_deactive : int
      }

    let empty_annot_clause = ((C.empty_clause, [], S.empty_sub_data, Solved true):annot_clause)

    let new_queue () = { qstart = None; qend = None; trie = FeatureTrie.empty; nb_total = 0; nb_deactive = 0 }

    let add queue ((_, vector, _, _) as annot_cl:annot_clause) = match queue.qend with
      | None ->
          let elt = { prev = None; next = None; active = true; annot_clause = annot_cl } in
          queue.qstart <- Some elt;
          queue.qend <- Some elt;
	        if !Param.feature then
            queue.trie <- FeatureTrie.add queue.trie elt vector;
          queue.nb_total <- queue.nb_total + 1
      | Some q ->
          let elt = { prev = Some q; next = None; active = true; annot_clause = annot_cl } in
          q.next <- Some elt;
          queue.qend <- Some elt;
	        if !Param.feature then
            queue.trie <- FeatureTrie.add queue.trie elt vector;
          queue.nb_total <- queue.nb_total + 1

    let get queue = match queue.qstart with
      | None -> None
      | Some q ->
          match q.next with
            | None ->
                queue.qend <- None;
                queue.qstart <- None;
                queue.trie <- FeatureTrie.empty;
                queue.nb_total <- 0;
                queue.nb_deactive <- 0;
                Some q.annot_clause
            | Some q' ->
                q.active <- false;
                queue.qstart <- q.next;
                q'.prev <- None;
                queue.nb_deactive <- queue.nb_deactive + 1;
                Some q.annot_clause

    let length queue = queue.nb_total - queue.nb_deactive

    let iter f queue =
      let rec iterrec = function
        | None -> ()
        | Some q ->
            f q.annot_clause;
            iterrec q.next
      in
      iterrec queue.qstart

    let implies queue ((cl, vector, sub_data, additional_data):annot_clause) =
      let test_fun elt =
	      let (elt_cl,_,elt_sub_data, elt_additional_data) = elt.annot_clause in
        elt.active && S.implies_no_test (elt_cl,elt_sub_data, elt_additional_data) (cl, sub_data, additional_data)
      in
      if !Param.feature then
	      FeatureTrie.exists_leq test_fun vector queue.trie
      else
        let rec existsrec q = match q with
          | None -> false
          | Some q' -> (test_fun q') || (existsrec q'.next)
        in
	      existsrec queue.qstart

    let deactivate_implied_by queue ((cl, vector, sub_data, additional_data):annot_clause) =
      let iter_fun elem =
	      let (elt_cl,_,elt_sub_data, elt_additional_data) = elem.annot_clause in
        if elem.active && S.implies_no_test (cl, sub_data, additional_data) (elt_cl,elt_sub_data, elt_additional_data)
        then
          begin
            (* Clause need to be removed *)
	          elem.annot_clause <- empty_annot_clause; (* Remove the clause, so that it can be garbage collected *)
            elem.active <- false;
            queue.nb_deactive <- queue.nb_deactive + 1;
            match elem.prev, elem.next with
              | None, None ->
                  (* The queue contains a unique element *)
                  queue.qstart <- None;
                  queue.qend <- None
              | Some elem', None ->
                  (* [elem] is the last element of the queue so
                  [elem'] becomes the last element *)
                  queue.qend <- elem.prev;
                  elem'.next <- elem.next
              | None, Some elem' ->
                  (* [elem] is the first element of the queue so
                  [elem'] becomes the first element *)
                  queue.qstart <- elem.next;
                  elem'.prev <- elem.prev
              | Some elem_p, Some elem_n ->
                  elem_p.next <- elem.next;
                  elem_n.prev <- elem.prev
          end
      in
      if !Param.feature then
	      FeatureTrie.iter_geq iter_fun vector queue.trie
      else
        let rec iterrec = function
          | None -> ()
          | Some q ->
              let next = q.next in
              iter_fun q;
              iterrec next
        in
        iterrec queue.qstart

    let cleanup_deactivated queue =
      if queue.nb_total != 0 && (queue.nb_deactive * 100) / queue.nb_total > !Param.cleanup_threshold
      then
        begin
	        if !Param.feature then
            queue.trie <- FeatureTrie.filter (fun elt -> elt.active) queue.trie;
          queue.nb_total <- queue.nb_total - queue.nb_deactive;
          queue.nb_deactive <- 0
        end
  end

(* Database *)

module type DBSig =
  sig
    type clause
    type queue
    type set
    type subsumption_data

    type t =
      {
        queue : queue;
        mutable count : int;
        mutable base_solved : set;
        mutable base_unsolved : set
      }

    val create : unit -> t

    val add_rule : t -> (set -> queue -> clause * subsumption_data  -> bool) -> (clause -> int * clause) -> (clause -> bool) -> clause -> unit

    val subsumption_for_newly_solved : t -> (clause * feature_vector * subsumption_data * additional_data) -> unit

    val display_initial_queue : t -> unit

    val display_rule_during_completion : t -> (clause * additional_data) -> unit

    val display_dynamic_statistics : t -> unit
  end

module MakeDatabase
  (C:ClauseSig)
  (S:SubsumptionSig with type hyp_fact = C.hyp_fact and type clause = C.t)
  (F:FeatureGenerationSig with type clause = C.t and type subsumption_data = S.subsumption_data)
  (Set:SetSig with type clause = C.t and type subsumption_data = S.subsumption_data)
  (Queue:QueueSig with type clause = C.t and type subsumption_data = S.subsumption_data)
  =
  struct
    type clause = C.t
    type queue = Queue.t
    type set = Set.t
    type subsumption_data = S.subsumption_data

    type t =
      {
        queue : Queue.t;
        mutable count : int;
        mutable base_solved : Set.t; 
        mutable base_unsolved : Set.t
      }

    let create () =
      {
        queue = Queue.new_queue ();
        count = 0;
        base_solved = Set.create ();
        base_unsolved = Set.create ();
      }

    let get_stat_string database =
      let size_base_ns = Set.length database.base_solved in
      let size_base_sel = Set.length database.base_unsolved in
      Printf.sprintf "%d rules inserted. Base: %d rules (%d with conclusion selected). Queue: %d rules."
        database.count
        (size_base_ns + size_base_sel)
        size_base_ns
        (Queue.length database.queue)
      
    let display_dynamic_statistics database =
      if !Param.verbose_dynamic_statistics
      then 
        Display.dynamic_display (get_stat_string database)

    let add_rule database redundant_fun selfun used_for_redundant rule =
      (* Remove bound terms *)
      let simplified_rule = C.simplify_remove_hyp rule in

      let (rule1,additional_data1,was_simplified) =
        if simplified_rule == rule
        then 
          let (sel_index,rule') = selfun rule in
          let (hyp, _, _, _, _) = C.get_reduction rule' in
          if sel_index = -1
          then 
            C.remove_marking rule', Solved (used_for_redundant rule'), false
          else
            let mark = snd (List.nth hyp sel_index) in
            rule', Unsolved (sel_index,mark), false
        else rule, Unsolved (0,NoMarking), true
      in
      let (_,feat_vertex1,sub_data1) = F.generate_feature_vector_and_subsumption_data rule1 in
      let annot_cl = (rule1,feat_vertex1,sub_data1,additional_data1) in

      let is_unsolved = match additional_data1 with
        | Solved _ -> false
        | _ -> true
      in
      
      (* Check that the rule is not already in the rule base or in the queue *)
      if 
        Set.implies database.base_solved annot_cl ||
        (is_unsolved && Set.implies database.base_unsolved annot_cl) ||
        Queue.implies database.queue annot_cl ||
        redundant_fun database.base_solved database.queue (rule1,sub_data1)
      then ()
      else
        begin
          let annot_cl',is_unsolved' = 
            if was_simplified
            then
              let (sel_index,rule') = selfun simplified_rule in
              let (hyp, _, _, _, _) = C.get_reduction rule' in
              let simp_additional_data, simp_is_unsolved, rule'' = 
                if sel_index = -1
                then Solved (used_for_redundant rule'), false, C.remove_marking rule'
                else
                  let mark = snd (List.nth hyp sel_index) in
                  Unsolved (sel_index,mark), true, rule'
              in
              let (_,simp_feat_vertex,simp_sub_data) = F.generate_feature_vector_and_subsumption_data rule'' in
              let simp_annot_cl = (rule'',simp_feat_vertex,simp_sub_data,simp_additional_data) in
              simp_annot_cl, simp_is_unsolved
            else annot_cl,is_unsolved
          in
          (* We deactivate the clauses that are implied by rule (semantically, it is the same as
             removing the clauses but for efficiency, they are not always directly removed
             from the database but only deactivated.) *)
          if is_unsolved' then Set.deactivate_implied_by database.base_solved annot_cl';
          Set.deactivate_implied_by database.base_unsolved annot_cl';
          Queue.deactivate_implied_by database.queue annot_cl';

          (* We check the rule *)
          C.check rule;

          (* We add the rule *)
          Queue.add database.queue annot_cl';

          (* Cleanup that will remove the deactivated clauses when needed. *)
          Set.cleanup_deactivated database.base_solved;
          Set.cleanup_deactivated database.base_unsolved;
          Queue.cleanup_deactivated database.queue;

          (* Display statistics *)
          display_dynamic_statistics database
        end

    let subsumption_for_newly_solved database ((cl,_,_,_) as annot_cl) = 
      let variant_AC = C.is_variant_AC cl in
      Set.deactivate_implied_by database.base_solved annot_cl;
      if not variant_AC then Set.deactivate_implied_by database.base_unsolved annot_cl;
      Queue.deactivate_implied_by database.queue annot_cl;

      (* Cleanup that will remove the deactivated clauses when needed. *)
      Set.cleanup_deactivated database.base_solved;
      if not variant_AC then Set.cleanup_deactivated database.base_unsolved;
      Queue.cleanup_deactivated database.queue

    let display_base_sel database =
      let count = ref 1 in
      Set.iter (fun { annot_clause = (clause, _, additional_data); active = active; selected_fact; _ } ->
        let sel = match additional_data with 
          | Unsolved(sel,_) -> sel
          | Solved _ -> Parsing_helper.internal_error "Should only contain unsolved clauses in this set."
        in
        Display.auto_cleanup_display (fun () ->
          Display.Text.print_string ((string_of_int !count)^" -- (hyp "^(string_of_int sel)^" selected: ");
          Display.Text.display_fact selected_fact;
          Display.Text.print_line "):";
          C.display clause
	    );
        incr count
	  ) database.base_unsolved

    let display_base_ns database =
      let count = ref 1 in
      Set.iter (fun { annot_clause = (clause, _, _); active = active } ->
        Display.Text.print_string ((string_of_int !count)^" -- ");
        C.display_indep clause;
        incr count
  	    ) database.base_solved

    let display_initial_queue database =
      Display.Text.print_line "------------ Initial queue ----------";
      let count = ref 0 in
      Queue.iter (fun (rule, _, _,_) ->
        Display.Text.print_string ((string_of_int (!count + 1))^" -- ");
        C.display_indep rule;
        incr count;
      ) database.queue;
      Display.Text.print_line "------------------------------------"

    let display database =
      Display.Text.print_line "------------ Resulting base and rules added in queue ----------";
      Display.Text.print_line "*** Rules with the conclusion selected";
      display_base_ns database;
      Display.Text.print_line "*** Rules with an hypothesis selected";
      display_base_sel database;
      Display.Text.print_line "*** Rules in queue";
      let count = ref 0 in
      Queue.iter (fun (rule, _, _, _) ->
        Display.Text.print_string ((string_of_int (!count + 1))^" -- ");
        C.display_indep rule;
        incr count;
      ) database.queue;
      Display.Text.print_line "------------------------------------"

    let display_rule_during_completion database (rule,add_data) =
      let display_stat () =
	      print_string (get_stat_string database);
        Display.Text.newline()
      in

      (* Display the rule *)
      if !Param.verbose_rules || !Param.verbose_base
      then
        begin
	        Display.stop_dynamic_display ();
          Display.auto_cleanup_display (fun () ->
            begin match add_data with
            | Unsolved(sel_index,_) ->
                let (hypl,_,_,_,_) = C.get_reduction rule in
                Display.Text.newline ();
                Display.Text.print_string ("Rule with hypothesis fact "^(string_of_int sel_index)^" selected: ");
                Display.Text.display_marked_fact (List.nth hypl sel_index);
                Display.Text.newline ();
            | Solved _ -> 
                Display.Text.newline ();
                Display.Text.print_line "Rule with conclusion selected:";
            end;

            C.display rule;
            database.count <- database.count + 1;
            display_stat ()
          );

          if !Param.verbose_base then display database
        end
      else
        begin
          database.count <- database.count + 1;
          if database.count mod 200 = 0
          then
	    begin
	      Display.stop_dynamic_display ();
	      display_stat ()
	    end
        end
  end

(* The generated modules *)

module Clause : ClauseSig with type hyp_fact = fact * marking and type t = marked_reduction =
  struct
    type hyp_fact = fact * marking
    type t = marked_reduction
    let empty_clause = ([], Param.dummy_fact, Empty(Param.dummy_fact), { neq = []; is_nat = []; is_not_nat = []; geq = [] },false)
    let get_reduction r = r

    let is_variant_AC (_,_,_,_,variant) = variant

    let match_facts f_next comply_with_marking (fact1,mk1) (fact2,mk2) = 
      if comply_with_marking && not (Marking.match_marking mk1 mk2) then raise Terms.Unify;

      AC.Ac_unify.match_facts f_next fact1 fact2

    let match_closed_fact comply_with_marking (fact1,mk1) (fact2,mk2) = 
      if comply_with_marking && not (Marking.match_marking mk1 mk2) then raise Terms.Unify;

      let fact1' = Terms.copy_fact3 fact1 in
      if not (Terms.equal_facts fact1' fact2) then raise Terms.Unify

    let remove_marking ((hypl,concl,hist,const,variant) as cl:marked_reduction) = 
      let hypl' = 
        Terms.mapq_list (fun hyp -> match hyp with
          | _,NoMarking -> hyp
          | fact,_ -> fact,NoMarking
        ) hypl
      in
      if hypl' == hypl then cl else (hypl',concl,hist,const,variant)

    let fact_of_hyp_fact (f,_) = f
    let get_clause_with_hyp_fact r = r
    let simplify_remove_hyp = remove_ground_public_terms
    let check = check_rule
    let display = Display.Text.display_rule
    let display_indep = Display.Text.display_rule_indep
    let display_hyp_fact = Display.Text.display_marked_fact
  end
module SubClause = MakeSubsumption(Clause)
module FeatureGenClause = MakeFeatureGeneration(Clause)(SubClause)
module SetClause = MakeSet(Clause)(SubClause)
module QueueClause = MakeQueue(Clause)(SubClause)
module DB = MakeDatabase(Clause)(SubClause)(FeatureGenClause)(SetClause)(QueueClause)

module OrdClause : ClauseSig with type hyp_fact = fact * marking * ordering_function and type t = ordered_reduction =
  struct
    type hyp_fact = fact * marking * ordering_function
    type t = ordered_reduction

    let empty_clause = { rule = Clause.empty_clause; order_data = None }
    let get_reduction r = r.rule

    let is_variant_AC r = 
      let (_,_,_,_,variant) = r.rule in 
      variant

    let match_facts f_next comply_with_marking (f1,mk1,ord_fun1) (f2,mk2,ord_fun2) =
      if comply_with_marking && not (Marking.match_marking mk1 mk2) then raise Terms.Unify;
      implies_ordering_function ord_fun1 ord_fun2;

      AC.Ac_unify.match_facts f_next f1 f2

    let match_closed_fact comply_with_marking (fact1,mk1,ord_fun1) (fact2,mk2,ord_fun2) = 
      if comply_with_marking && not (Marking.match_marking mk1 mk2) then raise Terms.Unify;
      implies_ordering_function ord_fun1 ord_fun2;
      let fact1' = Terms.copy_fact3 fact1 in
      if not (Terms.equal_facts fact1' fact2) then raise Terms.Unify
      
    let fact_of_hyp_fact (f,_,_) = f

    let remove_marking ord_rule = 
      let (hypl,concl,hist,const,variant) = ord_rule.rule in 
      let hypl' = 
        Terms.mapq_list (fun hyp -> match hyp with
          | _,NoMarking -> hyp
          | fact,_ -> fact,NoMarking
        ) hypl
      in
      if hypl' == hypl then ord_rule else { ord_rule with rule = (hypl',concl,hist,const,variant) }

    let get_clause_with_hyp_fact r =
      let (hypl,concl,hist,constra,variant) = r.rule in
      let hypl' = match r.order_data with
        | None -> List.map (fun (f,mk) -> f,mk,[]) hypl
        | Some ord_data -> List.map2 (fun (f,mk) (ord_fun,_) -> (f,mk,ord_fun)) hypl ord_data
      in
      (hypl',concl,hist,constra,variant)

    let rec ord_remove_ground_public_terms_rec accu hypl ordl =
      List.fold_right2 (fun hyp1 ord1 (hypl,ordl,nl,histl) -> match hyp1 with
        | Pred(chann,t::q), mk ->
            if mk = NoMarking && chann.p_prop land Param.pred_ATTACKER != 0 && is_ground_public t && List.for_all (equal_terms t) q
            then
              let (hypl',nl',histl') = remove_sure_ground_public_terms (hypl,nl,histl) [hyp1] in
              (hypl',ordl,nl',histl')
            else (hyp1::hypl, ord1::ordl, nl-1, histl)
        | _ -> (hyp1::hypl, ord1::ordl, nl-1, histl)
	    ) hypl ordl accu

    let simplify_remove_hyp r = match r.order_data with
      | None -> 
          let rule' = remove_ground_public_terms r.rule in
          if rule' == r.rule
          then r
          else { rule = remove_ground_public_terms r.rule; order_data = None }
      | Some ord_data ->
          let (hypl,concl,hist,constra,variant) = r.rule in
          let (hypl',ordl',_,hist') = ord_remove_ground_public_terms_rec ([],[],(List.length hypl)-1,hist) hypl ord_data in
          if hist' == hist
          then r
          else { rule = (hypl',concl,hist',constra,variant); order_data = Some ordl' }

    let check = check_rule_ordered

    let display = Display.Text.display_ordered_rule

    let display_indep = Display.Text.display_ordered_rule_indep

    let display_hyp_fact (fact,mk,_) = Display.Text.display_marked_fact (fact,mk)
  end
module SubOrdClause = MakeSubsumption(OrdClause)
module FeatureGenOrdClause = MakeFeatureGeneration(OrdClause)(SubOrdClause)
module SetOrdClause = MakeSet(OrdClause)(SubOrdClause)
module QueueOrdClause = MakeQueue(OrdClause)(SubOrdClause)
module DBOrd = MakeDatabase(OrdClause)(SubOrdClause)(FeatureGenOrdClause)(SetOrdClause)(QueueOrdClause)

(* A specific module for Saturated clause. It is typically a subset of function from SetClause
   where we only need to work with unification *)

module SetSatClause =
  struct

    type t = (predicate * (saturated_reduction UnificationTrie.t)) list

    let empty = []

    let rec update_in_list p f = function
      | [] -> [p,f (UnificationTrie.empty)]
      | (p',tree)::q when p == p' -> (p',f tree)::q
      | t::q -> t::(update_in_list p f q)

    let of_list sat_rules =
      List.fold_left (fun acc_tree ({ sat_rule = (_,Pred(p,args),_,_,_); _ } as sat_rule) ->
        update_in_list p (fun tree -> UnificationTrie.add tree sat_rule args) acc_tree;
      ) [] sat_rules

    let iter_unifiable f set = function
      | Pred(p,args) ->
          try
            let tree = List.assq p set in
            UnificationTrie.iter_unify f tree args
          with Not_found -> ()
  end
