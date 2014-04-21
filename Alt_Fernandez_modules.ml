open Graph

module type LTS_STATE_TYPE =
sig
  include Sig.COMPARABLE
  val state_name: t -> string
end

module type LTS_ACTION_TYPE = 
sig
  include Sig.ORDERED_TYPE_DFT
  type action = t
  val action_name: action -> string
end
  
module type LTS_TYPE =
sig
  module A: LTS_ACTION_TYPE
  include Sig.P with type E.label = A.t
  type action = E.label
  val graph_attributes : t -> Graphviz.DotAttributes.graph list
  val default_vertex_attributes : t -> Graphviz.DotAttributes.vertex list
  val vertex_name : V.t -> string
  val vertex_attributes : V.t -> Graphviz.DotAttributes.vertex list
  val get_subgraph : V.t -> Graphviz.DotAttributes.subgraph option
  val default_edge_attributes : t -> Graphviz.DotAttributes.edge list
  val edge_attributes : E.t -> Graphviz.DotAttributes.edge list
end

module LTS_Functor = 
  functor (S : LTS_STATE_TYPE) -> 
    functor (A : LTS_ACTION_TYPE) ->
      (struct

        module Base = Persistent.Digraph.ConcreteBidirectionalLabeled
          (S) (A)
        include Base

        module A = A
          
        let vertex_name = S.state_name

        type action = A.t

        let graph_attributes g  = []

        let default_vertex_attributes g = []

        let vertex_attributes v = []

        let get_subgraph v = None

        let default_edge_attributes g = []

        let edge_attributes (_, a, _) = [`Label (A.action_name a)]
       end
         : LTS_TYPE  with type V.t = S.t
                     and type V.label = S.t
                     and type A.t = A.t
      )

module LTS_Dot_Functor =
  functor (LTS: LTS_TYPE) ->
struct
  include Graphviz.Dot (LTS)
end

module NK_yes_table_functor =
  functor (LTS: LTS_TYPE) ->
    (struct

      module StatePairMap = Map.Make(
        struct
          type t = LTS.V.t * LTS.V.t
          let compare (p1, q1) (p2, q2) =
            let
                temp1 = LTS.V.compare p1 p2
            in
            if
              temp1 = 0
            then
              LTS.V.compare q1 q2
            else
              temp1
        end
      )
        
      include StatePairMap

      let conditional_add
          ((p, q):LTS.V.t * LTS.V.t)
          ((n, k): int * int)
          (m: ((int * int) list) t) : (((int * int) list) t) =
        let redundant _ _ = false
        in
        try
          (let
              l = find (p, q) m
           in
           if
             (redundant (n, k) l)
           then
             m
           else
             add (p, q) ((n, k)::l) m
          )
        with
        | Not_found -> add (p, q) [(n, k)] m

      let conditional_remove
          ((p, q):LTS.V.t * LTS.V.t)
          ((n, k): int * int)
          (m: ((int * int) list) t) : (((int * int) list) t) =
        try
          (let
              l = find (p, q) m
           in
           add (p, q) (List.filter (Pervasives.(<>) (n, k)) l) m
          )
        with
        | Not_found -> m

     end)

module HM_Formula =
  functor (LTS: LTS_TYPE) ->
    (struct

      type hm_formula =
      | DIAMOND of LTS.A.t * hm_formula
      | BOX of LTS.A.t * hm_formula
      | AND of hm_formula list (*AND [] is true.*)
      | OR of hm_formula list (* OR [] is false.*)

      let rec negation formula =
        match formula with
        | DIAMOND (a, formula) -> BOX (a, negation formula)
        | BOX (a, formula) -> DIAMOND (a, negation formula)
        | AND formula_list -> OR (List.map negation formula_list)
        | OR formula_list -> AND (List.map negation formula_list)

      let rec minimise (formula:hm_formula):hm_formula =
        let f e extract_e terminator formula_list =
          let
              (should_terminate, formula_list) =
            List.fold_left
              (fun (should_terminate, formula_list) formula ->
                if
                  should_terminate
                then
                  (should_terminate, formula_list)
                else
                  (let
                      formula = minimise formula
                  in
                  if
                    formula = terminator
                  then
                    (true, [])
                  else
                    (false,
                     match
                       (extract_e formula)
                     with
                     | Some partial_formula_list ->
                       partial_formula_list @ formula_list
                     | None ->
                       formula::formula_list)))
              (false, [])
              formula_list
          in
          if
            should_terminate
          then
            terminator
          else
            match
              formula_list
            with
            | [formula] -> formula
            | formula_list -> e formula_list
        in
        match
          formula
        with
        | DIAMOND (a, formula) -> DIAMOND (a, minimise formula)
        | BOX (a, formula) -> BOX (a, minimise formula)
        | AND formula_list ->
          f
            (function formula_list -> AND formula_list)
            (function
            | AND formula_list -> Some formula_list
            | _ -> None)
            (OR [])
            formula_list
        | OR formula_list ->
          f
            (function formula_list -> OR formula_list)
            (function
            | OR formula_list -> Some formula_list
            | _ -> None)
            (AND [])
            formula_list

      let rec translate formula =
        match
          formula
        with
        | DIAMOND (a, formula) ->
          "<" ^ (LTS.A.action_name a) ^ ">" ^ (translate formula)
        | BOX (a, formula) ->
          "[" ^ (LTS.A.action_name a) ^ "]" ^ (translate formula)
        | AND [] -> "tt"
        | AND formula_list ->
          "(" ^
            (String.concat
               " && "
               (List.map translate formula_list))
          ^ ")"
        | OR [] -> "ff"
        | OR formula_list ->
          "(" ^ 
            (String.concat
               " || "
               (List.map translate formula_list))
          ^ ")"

     end)

module NK_Rel =
  functor (LTS: LTS_TYPE) ->
    (struct

      include HM_Formula(LTS)

      let check_entry_yes_table yes_table p q n k =
        List.exists
          (function (p1, q1, n1, k1) ->
            (p1 = p) && (q1 = q) && (n1 >= n) && (k1 >= k))
          yes_table

      let fetch_entries_no_table no_table p q n k =
        List.map
          (function (_, _, n1, k1, f1) -> (n1, k1, f1))
          (List.filter
             (function (p1, q1, n1, k1, f1) ->
               (p1 = p) && (q1 = q) && (n1 <= n) && (k1 <= k))
             no_table)

      let add_entry_yes_table yes_table p q n k =
        if
          (List.exists
             (function (p1, q1, n1, k1) ->
               (p1 = p) && (q1 = q) && (n1 >= n) && (k1 >= k))
             yes_table)
        then
          yes_table
        else
        (p, q, n, k)::
          (List.filter
             (function (p1, q1, n1, k1) ->
               (p1 <> p) || (q1 <> q) || (n1 > n) || (k1 > k))
             yes_table)

      let add_entry_no_table no_table p q n k f =
        if
          (List.exists
             (function (p1, q1, n1, k1, f1) ->
               (p1 = p) && (q1 = q) && (n1 <= n) && (k1 <= k))
             no_table)
        then
          no_table
        else
          ((p, q, n, k, f)::
              (List.filter
                 (function (p1, q1, n1, k1, f1) ->
                   (p1 <> p) || (q1 <> q) || (n1 < n) || (k1 < k))
                 no_table))

      let remove_entry_yes_table yes_table p q n k =
        List.filter
          (function (p1, q1, n1, k1) ->
            (p1 <> p) || (q1 <> q) || (n1 < n) || (k1 < k))
          yes_table

      let create_yes_table () = []

      let create_no_table () = []

      (* we assume that p is the challenger's position in lts1 and q is
         the defender's position in lts2. thus, if the challenger switches to
         q now and makes a move in lts2, then we use up one alternation,
         otherwise we have the same number of alternations remaining.*)
      let rec
	  get_distinguishing_formulae
	  lts1
	  lts2
	  p
	  q
	  n
	  k
          yes_table
          no_table
          (* rel is some specific relation, can be a prebisim or a
             simulation equivalence or a bisimulation *)
	  rel = 
        let
            () =
          Printf.printf
            "pushed p = %s, q = %s, n = %s, k = %s\n"
            (LTS.vertex_name p)
            (LTS.vertex_name q)
            (string_of_int n)
            (string_of_int k)
        in
        let
            result = (
          if k = 0 then ([], yes_table, no_table)
          else if check_entry_yes_table yes_table p q n k  
          then ([], yes_table, no_table)
          else
            match
              fetch_entries_no_table no_table p q n k
            with
            | hd::tl -> (hd::tl, yes_table, no_table) 
            | [] -> (
	      let yes_table = add_entry_yes_table yes_table p q n k in
	    (* for each successor p' of p, check if that is simulated by
               a successor q' of q *)
	      let
	          (v_p, l_p, yes_table, no_table) =
              (* This fold deals with all the successors of p,
                 universal quantification.*)
                (LTS.fold_succ_e
	           (fun e_p (partial_v_p, partial_l_p, yes_table, no_table) ->
                     let
                         (match_found, v_q, l_q,
                          yes_table,
                          no_table) =
                       (* This fold deals with all the successors of q,
                          existential quantification.*)
                       (LTS.fold_succ_e
		          (fun e_q
                            (partial_match_found,
                             partial_v_q,
                             partial_l_q,
                             yes_table,
                             no_table) ->
                              if (LTS.A.compare (LTS.E.label e_p) (LTS.E.label e_q) <> 0)
                              then
                                (partial_match_found,
                                 partial_v_q,
                                 partial_l_q,
                                 yes_table,
                                 no_table)
                              else
                                let
                                  (* this is when we do not switch sides.*)
                                    (l_pp,
                                     yes_table,
                                     no_table) =
                                  (get_distinguishing_formulae
		                     lts1
		                     lts2
		                     (LTS.E.dst e_p)
		                     (LTS.E.dst e_q)
		                     (n)
		                     (k - 1)
                                     yes_table
                                     no_table
		                     rel)
                                in
                                let
                                    v_pp =
                                  (match
                                      l_pp
                                   with
                                   | [] -> true
                                   | _ -> false
                                  )
                                in
                                let
                                    l_pp =
                                  (List.map
                                     (fun (n1, k1, f1) ->
                                       (n1, k1 + 1, f1))
                                     l_pp) (* one more round. *)
                                in
                                let
                                    (* this is when we switch sides.*)
                                    (l_qq,
                                     yes_table,
                                     no_table) =
                                  if
                                    (n = 0)
                                  then
                                    ([],
                                     yes_table,
                                     no_table)
                                  else
                                    (get_distinguishing_formulae
		                       lts2
		                       lts1
		                       (LTS.E.dst e_q)
		                       (LTS.E.dst e_p)
		                       (n - 1)
		                       (k - 1)
                                       yes_table
                                       no_table
		                       rel)
                                in
                                let
                                    v_qq =
                                  (match
                                      l_qq
                                   with
                                   | [] -> true
                                   | _ -> false
                                  )
                                in
                                let
                                    l_qq =
                                  (List.map
                                     (fun (n1, k1, f1) ->
                                       (n1 + 1, k1 + 1, negation f1))
                                     l_qq) (* one more round, one more alternation. *)
                                in
                                let
                                    l_pp_qq =
                                  List.fold_left
                                    (fun partial_l_pp_qq (n, k, f) ->
                                      if
                                        List.exists
                                          (fun (n1, k1, f1) ->
                                            (n1 <= n) && (k1 <= k))
                                          partial_l_pp_qq
                                      then
                                        partial_l_pp_qq
                                      else
                                        (n, k, f) ::
                                          (List.filter
                                             (fun (n1, k1, f1) ->
                                               (n1 < n) || (k1 < k))
                                             partial_l_pp_qq)
                                    )
                                    []
                                    (l_pp @ l_qq)
                                in
                                let
                                    partial_v_q = partial_v_q || (v_pp && v_qq)
                                in
                                let
                                    partial_l_q =
                                  (if
                                      partial_v_q
                                   then
                                      []
                                   else
                                      (List.concat
                                         (List.map
                                            (function (n, k, f) ->
                                              List.map
                                                (function
                                              (max_n,
                                               max_k,
                                               formula_list) ->
                                                ((if
                                                    max_n < n
                                                  then n
                                                  else max_n),
                                                 (if
                                                     max_k < k
                                                  then k
                                                  else max_k),
                                                 f::formula_list))
                                                partial_l_q
                                            )
                                            l_pp_qq)))
                                in
                                (* this is where we get rid of cruft
                                   in the cartesian product we have
                                   built so far.*)
                                let
                                    partial_l_q =
                                  (List.fold_left
                                     (fun partial_l_q (n, k, f) ->
                                       if
                                         List.exists
                                           (fun (n1, k1, f1) ->
                                             (n1 <= n) && (k1 <= k))
                                           partial_l_q
                                       then
                                         partial_l_q
                                       else
                                         (n, k, f)::
                                           (List.filter
                                              (fun (n1, k1, f1) ->
                                                (n1 < n) || (k1 < k))
                                              partial_l_q
                                           )
                                     )
                                     []
                                     partial_l_q)
                                in
		                (true,
                                 partial_v_q,
                                 partial_l_q,
                                 yes_table,
                                 no_table
                                )
		          )
		          lts2
		          q
		          (false, false, [(0, 0, [])], yes_table, no_table)
	               )
                     in
                     let
                         l_q
                         =
                       if
                         (not match_found)
                       then
                         (* this is the base case for entry into the
                            no_table. The challenger can perform one move
                            right here which the defender cannot
                            replicate. *)
                         (* [(0, 1, [DIAMOND(LTS.E.label e_p, AND[])])] *)
                         [(0, 1, [AND[]])]
                       else
                         l_q
                     in
	             (partial_v_p && v_q, (* this expression works
                                             fine even for the case
                                             where we have
                                             match_found = false,
                                             because there is a
                                             false in the base case
                                             which makes the and
                                             thingy false as well. *)
                      List.fold_left
                        (fun partial_l_p (n, k, formula_list) ->
                          if
                            (List.exists
                               (fun (n1, k1, f1) ->
                                 (n1 <= n) && (k1 <= k))
                               partial_l_p)
                          then
                            partial_l_p
                          else
                            (n, k, DIAMOND (LTS.E.label e_p, AND formula_list)) ::
                              (List.filter
                                 (fun (n1, k1, f1) ->
                                   (n1 < n) || (k1 < k))
                                 partial_l_p)
                        )
                        partial_l_p
                        l_q,  
                      yes_table,
                      no_table
                     )
	           )
	           lts1
	           p
	           (true, [], yes_table, no_table)
	        )
              in
              if
                v_p
              then
	        ([], (* earlier this was l_p, which seems wrong.*)
                 yes_table,
                 no_table)
              else
	        (l_p, (* we need to return a list of pairs of the form (n,
                         k) which denotes the various pairs of values of n
                         and k for which the challenger wins.*)
                 remove_entry_yes_table yes_table p q n k,
                 List.fold_left
                   (fun no_table (n1, k1, f1) ->
                     add_entry_no_table no_table p q n1 k1 f1)
                   no_table
                   l_p
                )
            )
        )
        in
        let
            () =
          Printf.printf
            "about to pop p = %s, q = %s, n = %s, k = %s\n, \
 defender_won = %s, \n"
            (LTS.vertex_name p)
            (LTS.vertex_name q)
            (string_of_int n)
            (string_of_int k)
            (match result with
            | ([], _, _) -> "true"
            | (_, _, _) -> "false"
            )
        in
        result

      let rec
	  checknkRel
	  lts1
	  lts2
	  p
	  q
	  n
	  k
          yes_table
          no_table
          (* rel is some specific relation, can be a prebisim or a
             simulation equivalence or a bisimulation *)
	  rel = 
        match
          (get_distinguishing_formulae
	    lts1
	    lts2
	    p
	    q
	    n
	    k
            yes_table
            no_table
            rel
          )
        with
        | ([], _, _) -> true
        | (_, _, _) -> false

      let
	  get_distinguishing_formulae1
	    lts1
	    lts2
	    p
	    q
	    n
	    k
	  =
	let
	    (yes_table, no_table) = (create_yes_table (), create_no_table ())
	in
	let
	    (l1, yes_table, no_table) = 
	  get_distinguishing_formulae
	    lts1
	    lts2
	    p
	    q
	    n
	    k
            yes_table
            no_table
	    ()
	in
	l1

      let
	  get_distinguishing_formulae2
	    lts1
	    lts2
	    p
	    q
	    n
	    k
	  =
	let
	    (yes_table, no_table) = (create_yes_table (), create_no_table ())
	in
	let
	    (l1, yes_table, no_table) = 
	  get_distinguishing_formulae
	    lts1
	    lts2
	    p
	    q
	    n
	    k
            yes_table
            no_table
	    ()
	in
	let
	    (l2, yes_table, no_table) = 
	  get_distinguishing_formulae
	    lts2
	    lts1
	    q
	    p
	    n
	    k
            yes_table
            no_table
	    ()
	in
	List.fold_left
	  (fun list (n, k, f) ->
	    if
	      (List.exists
		 (fun (n1, k1, f1) -> (n1 <= n) && (k1 <= k))
		 list)
	    then
	      list
	    else
	      (n, k, f) ::
		(List.filter
		   (fun (n1, k1, f1) -> (n1 < n) || (k1 < k))
		   list))
	  []
	  (l1 @ l2)

      let
	  get_nk_pairs
	    f
	    lts1
	    lts2
	    p
	    q
	    n
	    k
	  =
	List.map
	  (fun (n, k, f) -> (n, k))
	  (f
	     lts1
	     lts2
	     p
	     q
	     n
	     k)

      let
	  get_nk_pairs1
	  =
	get_nk_pairs
	  get_distinguishing_formulae1

      let
	  get_nk_pairs2
	  =
	get_nk_pairs
	  get_distinguishing_formulae2

      let
	  get_nk_relation
	    f
	    lts1
	    lts2
	    p
	    q
	    n
	    k
	  =
	match
	  (f
	     lts1
	     lts2
	     p
	     q
	     n
	     k)
	with
	| [] -> true
	| _ -> false

      let
	  get_nk_relation1
	  =
	get_nk_relation
	  get_distinguishing_formulae1

      let
	  get_nk_relation2
	  =
	get_nk_relation
	  get_distinguishing_formulae2

     end)

module IntV =
  (struct
    type t = int
    let compare = Pervasives.compare
    let hash = Hashtbl.hash
    let equal = Pervasives.(=)
    let state_name = string_of_int
   end)

module IntE =
  (struct
    type t = int
    let compare = Pervasives.compare
    let default = 0
    type action = t
    let action_name = string_of_int
   end)

module IntIntLTS = LTS_Functor (IntV) (IntE)

module IntIntLTSDot = LTS_Dot_Functor (IntIntLTS)

module IntIntLTSDotParse =
  Dot.Parse
    (Builder.P (IntIntLTS))
    (struct
      let node (id, _) _ =
        match
          id
        with
        | Dot_ast.Number s
        | Dot_ast.Ident s
        | Dot_ast.Html s
        | Dot_ast.String s -> (int_of_string s)

      let edge attr_list =
        try
          (let
              (_, id) =
             List.find
               (function
               | (Dot_ast.Number s, _)
               | (Dot_ast.Ident s, _)
               | (Dot_ast.Html s, _)
               | (Dot_ast.String s, _) -> s = "action")
               (List.concat attr_list)
           in
           match
             id
           with
           | Some (Dot_ast.Number s)
           | Some (Dot_ast.Ident s)
           | Some (Dot_ast.Html s)
           | Some (Dot_ast.String s) -> (int_of_string s)
           | None -> raise Not_found)
        with
        | Not_found -> IntE.default
     end)

module IntIntLTSNK_Rel = NK_Rel (IntIntLTS)

module Test =
  (struct

    let test93 =
      try
        match
          IntIntLTS.add_edge IntIntLTS.empty 0 1
        with
        | _ -> "test93 passed"
      with
      | Invalid_argument _ -> "test93 failed"

    let test94 =
      try
        match
          IntIntLTS.add_edge_e IntIntLTS.empty (IntIntLTS.E.create 0 0 1)
        with
        | _ -> "test94 passed"
      with
      | Invalid_argument _ -> "test94 failed"

    let test95 =
      try
        match
          IntIntLTS.add_edge_e IntIntLTS.empty (IntIntLTS.E.create 0 (-1) 1)
        with
        | _ -> "test95 failed"
      with
      | Invalid_argument _ -> "test95 passed"

    let test96 =
      try
        match
          IntIntLTS.add_edge IntIntLTS.empty 0 1
        with
        | g -> "test96 failed"
      with
      | Invalid_argument _ -> "test96 passed"

    let test97 =
      try
        match
          IntIntLTS.add_edge_e IntIntLTS.empty (IntIntLTS.E.create 0 3 1)
        with
        | g -> "test97 passed"
      with
      | Invalid_argument _ -> "test97 failed"

    let l01 =
      List.fold_left
        (fun g (src, label, dst) -> IntIntLTS.add_edge_e g (IntIntLTS.E.create src label dst))
        (IntIntLTS.add_vertex IntIntLTS.empty 7)
        [(0, 0, 1); (1, 0, 1); (2, 1, 3); (3, 1, 4); (4, 1, 2); (5, 0, 0);
         (6, 0, 3); (5, 1, 6)]

    (* l03 and l04 correspond to 3alternations.pdf *)

    let l03 =
      IntIntLTSDotParse.parse "test/l03.dot"

    let l04 =
      IntIntLTSDotParse.parse "test/l04.dot"

    let l05 =
      IntIntLTSDotParse.parse "test/l05.dot"

    let l06 =
      IntIntLTSDotParse.parse "test/l06.dot"

    (* l07 and l08 correspond to Exercise 3.5 in Reactive Systems. *)

    let l07 =
      IntIntLTSDotParse.parse "test/l07.dot"

    let l08 =
      IntIntLTSDotParse.parse "test/l08.dot"

    let l09 =
      IntIntLTSDotParse.parse "test/l09.dot"

    let l10 =
      IntIntLTSDotParse.parse "test/l10.dot"

    let l11 =
      IntIntLTSDotParse.parse "test/l11.dot"

    let l12 =
      IntIntLTSDotParse.parse "test/l12.dot"

    (* l13 and l14 correspond to the file 0alternation.pdf. *)
    let l13 =
      IntIntLTSDotParse.parse "test/l13.dot"

    let l14 =
      IntIntLTSDotParse.parse "test/l14.dot"

    let l15 =
      IntIntLTSDotParse.parse "test/l15.dot"

    let l16 =
      IntIntLTSDotParse.parse "test/l16.dot"

    let l17 =
      IntIntLTSDotParse.parse "test/l17.dot"

    let l18 =
      IntIntLTSDotParse.parse "test/l18.dot"

    let l19 =
      List.fold_left
        (fun g (src, label, dst) -> IntIntLTS.add_edge_e g (IntIntLTS.E.create src label dst))
        IntIntLTS.empty
        [(62, 0, 63);
         (63, 0, 64);
         (64, 1, 65);
         (65, 2, 66);
         (62, 0, 67);
         (67, 1, 68)]

    let l20 =
      List.fold_left
        (fun g (src, label, dst) -> IntIntLTS.add_edge_e g (IntIntLTS.E.create src label dst))
        IntIntLTS.empty
        [(69, 0, 70);
         (69, 0, 71);
         (70, 0, 72);
         (71, 0, 73);
         (72, 1, 74);
         (73, 1, 75);
         (73, 3, 76)]

    let l21 =
      List.fold_left
        (fun g (src, label, dst) -> IntIntLTS.add_edge_e g (IntIntLTS.E.create src label dst))
        IntIntLTS.empty
        [(69, 0, 70);
         (69, 0, 71);
         (70, 0, 72);
         (71, 0, 73);
         (72, 1, 74);
         (73, 1, 75);
         (73, 3, 76);
         (75, 2, 77)]

    let l22 =
      List.fold_left
        (fun g (src, label, dst) -> IntIntLTS.add_edge_e g (IntIntLTS.E.create src label dst))
        IntIntLTS.empty
        [(69, 0, 70);
         (69, 0, 71);
         (70, 0, 72);
         (71, 0, 73);
         (73, 1, 75);
         (73, 3, 76)]

    let l23 =
      List.fold_left
        (fun g (src, label, dst) -> IntIntLTS.add_edge_e g (IntIntLTS.E.create src label dst))
        IntIntLTS.empty
        [(78, 0, 79);
         (79, 0, 80);
         (80, 1, 81);
         (81, 2, 82);
         (78, 0, 83);
         (83, 0, 84);
	 (84, 2, 85)]

    let l24 =
      List.fold_left
        (fun g (src, label, dst) -> IntIntLTS.add_edge_e g (IntIntLTS.E.create src label dst))
        IntIntLTS.empty
        [(86, 0, 87);
	 (87, 1, 88);
	 (87, 2, 89)]

    let l25 =
      List.fold_left
        (fun g (src, label, dst) -> IntIntLTS.add_edge_e g (IntIntLTS.E.create src label dst))
        IntIntLTS.empty
        [(90, 0, 91);
	 (90, 0, 92);
	 (91, 1, 93);
	 (92, 2, 94)]

    let () =
      IntIntLTS.iter_vertex
        (function v ->
          Printf.printf
            "v = %s\n"
            (string_of_int v)
        )
        l04

    let test120 =
      match
        IntIntLTSNK_Rel.checknkRel
	  l03
	  l04
	  0
	  14
	  3
	  4
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
	  ()
      with
      | false -> "test120 passed"
      | true -> "test120 failed"

    (* Shibashis: I assume that true means the defender has won
       and the relation holds when the challenger starts with l03 in
       the first round *)
        
    let test121 =  (* Shibashis: Challenger chooses now l04 in the
    first round *)
      match
        IntIntLTSNK_Rel.checknkRel
	  l04
	  l03
	  14
	  0
	  3
	  4
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
	  ()
      with
      | true -> "test121 passed"
      | false -> "test121 failed"

    let test122 =
      match
        IntIntLTSNK_Rel.checknkRel
	  l03
	  l04
	  0
	  14
	  2
	  4
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
	  ()
      with
      | true -> "test122 passed"
      | false -> "test122 failed"

    (* Shibashis: I assume that true means the defender has won
       and the relation holds when the challenger starts with l03 in
       the first round *)
        
    let test123 =  (* Shibashis: Challenger chooses now l04 in the
    first round *)
      match
        IntIntLTSNK_Rel.checknkRel
	  l04
	  l03
	  14
	  0
	  2
	  4
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
	  ()
      with
      | true -> "test123 passed"
      | false -> "test123 failed"

    let test124 =
      match
        IntIntLTSNK_Rel.checknkRel
	  l03
	  l04
	  0
	  14
	  3
	  6
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
	  ()
      with
      | false -> "test124 passed"
      | true -> "test124 failed"

    (* Shibashis: I assume that true means the defender has won
       and the relation holds when the challenger starts with l03 in
       the first round *)
        
    let test125 =  (* Shibashis: Challenger chooses now l04 in the
    first round *)
      match
        IntIntLTSNK_Rel.checknkRel
	  l04
	  l03
	  14
	  0
	  3
	  6
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
	  ()
      with
      | true -> "test125 passed"
      | false -> "test125 failed"

    let test126 =
      match
        IntIntLTSNK_Rel.checknkRel
	  l03
	  l04
	  0
	  14
	  2
	  6
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
	  ()
      with
      | true -> "test126 passed"
      | false -> "test126 failed"

    (* Shibashis: I assume that true means the defender has won
       and the relation holds when the challenger starts with l03 in
       the first round *)
        
    let test127 =  (* Shibashis: Challenger chooses now l04 in the
    first round *)
      match
        IntIntLTSNK_Rel.checknkRel
	  l04
	  l03
	  14
	  0
	  2
	  6
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
	  ()
      with
      | true -> "test127 passed"
      | false -> "test127 failed"

    let test128 =
      match
        IntIntLTSNK_Rel.checknkRel
	  l05
	  l06
	  23
	  25
	  1
	  2
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
	  ()
      with
      | false -> "test128 passed"
      | true -> "test128 failed"

    let test129 =
      match
        IntIntLTSNK_Rel.checknkRel
          l05
          l06
          23
          25
          0
          2
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
          ()
      with
      | true -> "test129 passed"
      | false -> "test129 failed"

    let test130 =
      match
        IntIntLTSNK_Rel.checknkRel
          l05
          l06
          23
          25
          0
          5
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
          ()
      with
      | true -> "test130 passed"
      | false -> "test130 failed"

    let test131 =
      match
        IntIntLTSNK_Rel.checknkRel
          l06
          l05
          25
          23
          1
          2
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
          ()
      with
      | true -> "test131 passed"
      | false -> "test131 failed"

    let test132 =
      match
        IntIntLTSNK_Rel.checknkRel
          l06
          l05
          25
          23
          2
          3
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
          ()
      with
      | false -> "test132 passed"
      | true -> "test132 failed"

    let test133 =
      match
        IntIntLTSNK_Rel.checknkRel
          l06
          l05
          25
          23
          4
          10
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
          ()
      with
      | false -> "test133 passed"
      | true -> "test133 failed"

    let test134 =
      match
        IntIntLTSNK_Rel.checknkRel
          l07
          l08
          26
          31
          10
          20
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
          ()
      with
      | true -> "test134 passed"
      | false -> "test134 failed"

    let test135 =
      match
        IntIntLTSNK_Rel.checknkRel
          l08
          l07
          32
          28
          0
          1
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
          ()
      with
      | false -> "test135 passed"
      | true -> "test135 failed"

    let f01 =
      IntIntLTSNK_Rel.DIAMOND
        (0,
         IntIntLTSNK_Rel.BOX
           (1,
            IntIntLTSNK_Rel.DIAMOND
              (2,
               IntIntLTSNK_Rel.AND [])))

    let f02 =
      IntIntLTSNK_Rel.BOX
        (0,
         IntIntLTSNK_Rel.DIAMOND
           (1,
            IntIntLTSNK_Rel.BOX
              (2,
               IntIntLTSNK_Rel.OR [])))

    let test136 =
      if
        (IntIntLTSNK_Rel.negation f01 = f02)
      then
        "test136 passed"
      else
        "test136 failed"

    let test137 =
      if
        (IntIntLTSNK_Rel.negation f02 = f01)
      then
        "test137 passed"
      else
        "test137 failed"

    let f03 =
      (let
          sf01 =
         IntIntLTSNK_Rel.DIAMOND
           (1,
            IntIntLTSNK_Rel.BOX
              (2,
               IntIntLTSNK_Rel.DIAMOND
                 (3,
                  IntIntLTSNK_Rel.AND [])))
       in
       let
           sf02 =
         IntIntLTSNK_Rel.AND
           [IntIntLTSNK_Rel.BOX (4, IntIntLTSNK_Rel.OR []);
            IntIntLTSNK_Rel.BOX (5, IntIntLTSNK_Rel.OR [])]
       in
       IntIntLTSNK_Rel.BOX
         (0,
          IntIntLTSNK_Rel.OR
            [sf01;
             IntIntLTSNK_Rel.BOX
               (1, sf02)]))

    let f04 =
      (let
          sf01 =
         IntIntLTSNK_Rel.BOX
           (1,
            IntIntLTSNK_Rel.DIAMOND
              (2,
               IntIntLTSNK_Rel.BOX
                 (3,
                  IntIntLTSNK_Rel.OR [])))
       in
       let
           sf02 =
         IntIntLTSNK_Rel.OR
           [IntIntLTSNK_Rel.DIAMOND (4, IntIntLTSNK_Rel.AND []);
            IntIntLTSNK_Rel.DIAMOND (5, IntIntLTSNK_Rel.AND [])]
       in
       IntIntLTSNK_Rel.DIAMOND
         (0,
          IntIntLTSNK_Rel.AND
            [sf01;
             IntIntLTSNK_Rel.DIAMOND
               (1, sf02)]))

    let test138 =
      if
        (IntIntLTSNK_Rel.negation f03 = f04)
      then
        "test138 passed"
      else
        "test138 failed"

    let test139 =
      if
        (IntIntLTSNK_Rel.negation f04 = f03)
      then
        "test139 passed"
      else
        "test139 failed"

    let test140 =
      match
        IntIntLTSNK_Rel.checknkRel
          l13
          l14
          40
          45
          2
          5
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
          ()
      with
      | false -> "test140 passed"
      | true -> "test140 failed"

    let test141 =
      match
        IntIntLTSNK_Rel.checknkRel
          l15
          l14
          52
          45
          2
          5
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
          ()
      with
      | false -> "test141 passed"
      | true -> "test141 failed"

    let test142 =
      match
        IntIntLTSNK_Rel.checknkRel
          l16
          l17
          59
          61
          2
          5
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
          ()
      with
      | false -> "test142 passed"
      | true -> "test142 failed"

    let test143 =
      match
        IntIntLTSNK_Rel.checknkRel
          l18
          l20
          62
          69
          2
          5
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
          ()
      with
      | false -> "test143 passed"
      | true -> "test143 failed"

    let test144 =
      match
        IntIntLTSNK_Rel.checknkRel
          l18
          l21
          62
          69
          2
          5
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
          ()
      with
      | false -> "test144 passed"
      | true -> "test144 failed"

    let test145 =
      match
        IntIntLTSNK_Rel.checknkRel
          l19
          l20
          62
          69
          2
          5
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
          ()
      with
      | false -> "test145 passed"
      | true -> "test145 failed"

    let test146 =
      match
        IntIntLTSNK_Rel.checknkRel
          l18
          l22
          62
          69
          2
          5
          (IntIntLTSNK_Rel.create_yes_table ())
          (IntIntLTSNK_Rel.create_no_table ())
          ()
      with
      | false -> "test146 passed"
      | true -> "test146 failed"

    let example_sim_eq =
      IntIntLTSNK_Rel.get_distinguishing_formulae2
	l24
	l25
	86
	90
	2
	5

    let example01 = 
      IntIntLTSNK_Rel.get_distinguishing_formulae1
	l03
	l04
	0
	14
	3
	5

    let example02 = 
      IntIntLTSNK_Rel.get_distinguishing_formulae1
	l07
	l08
	26
	31
	10
	20

    let example03 = 
      IntIntLTSNK_Rel.get_distinguishing_formulae1
	l05
	l06
	23
	25
	2
	5

    let example04 = 
      IntIntLTSNK_Rel.get_distinguishing_formulae1
	l18
	l20
	62
	69
	2
	5

    let example05 = 
      IntIntLTSNK_Rel.get_distinguishing_formulae1
	l18
	l22
	62
	69
	2
	5

    let example06 = 
      IntIntLTSNK_Rel.get_distinguishing_formulae2
	l19
	l22
	62
	69
	2
	5

    let f05 = IntIntLTSNK_Rel.DIAMOND (0, IntIntLTSNK_Rel.OR [])

    let f06 =
      (IntIntLTSNK_Rel.AND
         [IntIntLTSNK_Rel.AND [];
          IntIntLTSNK_Rel.DIAMOND
            (0,
             IntIntLTSNK_Rel.AND
               [IntIntLTSNK_Rel.DIAMOND (0, IntIntLTSNK_Rel.AND []);
                IntIntLTSNK_Rel.OR []])])

    let test147 =
      if
        f05 = IntIntLTSNK_Rel.minimise f06
      then
        "test147 passed"
      else
        "test147 failed"

    let f07 = IntIntLTSNK_Rel.BOX (0, IntIntLTSNK_Rel.AND [])

    let f08 =
      (IntIntLTSNK_Rel.OR
         [IntIntLTSNK_Rel.OR [];
          IntIntLTSNK_Rel.BOX
            (0,
             IntIntLTSNK_Rel.OR
               [IntIntLTSNK_Rel.BOX (0, IntIntLTSNK_Rel.OR []);
                IntIntLTSNK_Rel.AND []])])

    let test148 =
      if
        f07 = IntIntLTSNK_Rel.minimise f08
      then
        "test148 passed"
      else
        "test148 failed"

    let f09 =
      IntIntLTSNK_Rel.AND
        [IntIntLTSNK_Rel.DIAMOND (0, IntIntLTSNK_Rel.AND []);
         IntIntLTSNK_Rel.DIAMOND (1, IntIntLTSNK_Rel.AND []);
         IntIntLTSNK_Rel.DIAMOND (2, IntIntLTSNK_Rel.AND []);
         IntIntLTSNK_Rel.DIAMOND (3, IntIntLTSNK_Rel.AND [])]

    let f10 =
      (IntIntLTSNK_Rel.AND
         [IntIntLTSNK_Rel.AND
             [IntIntLTSNK_Rel.DIAMOND (3, IntIntLTSNK_Rel.AND []);
              IntIntLTSNK_Rel.DIAMOND (2, IntIntLTSNK_Rel.AND [])];
          IntIntLTSNK_Rel.AND
            [IntIntLTSNK_Rel.DIAMOND (1, IntIntLTSNK_Rel.AND []);
             IntIntLTSNK_Rel.DIAMOND (0, IntIntLTSNK_Rel.AND [])]
         ])

    let test149 =
      if
        f09 = IntIntLTSNK_Rel.minimise f10
      then
        "test149 passed"
      else
        "test149 failed"

    let f11 =
      IntIntLTSNK_Rel.OR
        [IntIntLTSNK_Rel.BOX (0, IntIntLTSNK_Rel.OR []);
         IntIntLTSNK_Rel.BOX (1, IntIntLTSNK_Rel.OR []);
         IntIntLTSNK_Rel.BOX (2, IntIntLTSNK_Rel.OR []);
         IntIntLTSNK_Rel.BOX (3, IntIntLTSNK_Rel.OR [])]

    let f12 =
      (IntIntLTSNK_Rel.OR
         [IntIntLTSNK_Rel.OR
             [IntIntLTSNK_Rel.BOX (3, IntIntLTSNK_Rel.OR []);
              IntIntLTSNK_Rel.BOX (2, IntIntLTSNK_Rel.OR [])];
          IntIntLTSNK_Rel.OR
            [IntIntLTSNK_Rel.BOX (1, IntIntLTSNK_Rel.OR []);
             IntIntLTSNK_Rel.BOX (0, IntIntLTSNK_Rel.OR [])]
         ])

    let test150 =
      if
        f11 = IntIntLTSNK_Rel.minimise f12
      then
        "test150 passed"
      else
        "test150 failed"

    let f13 =
      IntIntLTSNK_Rel.AND
        [IntIntLTSNK_Rel.DIAMOND (0, IntIntLTSNK_Rel.AND []);
         IntIntLTSNK_Rel.OR
           [IntIntLTSNK_Rel.BOX(1, IntIntLTSNK_Rel.OR []);
            IntIntLTSNK_Rel.AND []];
         IntIntLTSNK_Rel.DIAMOND
           (2,
            IntIntLTSNK_Rel.DIAMOND
              (3,
               IntIntLTSNK_Rel.OR
                 [IntIntLTSNK_Rel.BOX(4, IntIntLTSNK_Rel.OR []);
                  IntIntLTSNK_Rel.BOX(5, IntIntLTSNK_Rel.OR [])]))]

    let f14 =
      IntIntLTSNK_Rel.OR
        [IntIntLTSNK_Rel.BOX (0, IntIntLTSNK_Rel.OR []);
         IntIntLTSNK_Rel.AND
           [IntIntLTSNK_Rel.DIAMOND(1, IntIntLTSNK_Rel.AND []);
            IntIntLTSNK_Rel.OR []];
         IntIntLTSNK_Rel.BOX
           (2,
            IntIntLTSNK_Rel.BOX
              (3,
               IntIntLTSNK_Rel.AND
                 [IntIntLTSNK_Rel.DIAMOND(4, IntIntLTSNK_Rel.AND []);
                  IntIntLTSNK_Rel.DIAMOND(5, IntIntLTSNK_Rel.AND [])]))]

      end)
