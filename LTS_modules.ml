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

      let remove_entry_yes_table yes_table p q n k =
        List.filter
          (function (p1, q1, n1, k1) ->
            (p1 <> p) || (q1 <> q) || (n1 < n) || (k1 < k))
          yes_table

      let create_yes_table () = []

      module Strategy_with_formula = (struct

        type strategy = int * int * hm_formula

        type strategy_options = int * int * hm_formula list

        type no_table_entry = LTS.V.t * LTS.V.t * strategy

        type no_table = no_table_entry list

        let add_entry_no_table
            no_table
            p
            q
            (n, k, f) =
          if
            (List.exists
               (function (p1, q1, (n1, k1, f1)) ->
                 (p1 = p) && (q1 = q) && (n1 <= n) && (k1 <= k))
               no_table)
          then
            no_table
          else
            ((p, q, (n, k, f))::
                (List.filter
                   (function (p1, q1, (n1, k1, f1)) ->
                     (p1 <> p) || (q1 <> q) || (n1 < n) || (k1 < k))
                   no_table))

        let fetch_entries_no_table no_table p q n k =
          List.map
            (function (_, _, (n1, k1, f1)) -> (n1, k1, f1))
            (List.filter
               (function (p1, q1, (n1, k1, f1)) ->
                 (p1 = p) && (q1 = q) && (n1 <= n) && (k1 <= k))
               no_table)

        let create_no_table () = []

        let add_winning_strategy list (n, k, f) =
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
            list

        let add_optimal_winning_strategy, add_optimal_winning_strategy_options =
          let g
              list
              (n, k, f) =
            if
              List.exists
                (fun (n1, k1, f1) ->
                  (n1 <= n) && (k1 <= k))
                list
            then
              list
            else
              (n, k, f) ::
                (List.filter
                   (fun (n1, k1, f1) ->
                     (n1 < n) || (k1 < k))
                   list)
          in
          g, g

        let add_formula_base_case
            label
            list
            (n, k, formula_list) =
          if
            (List.exists
               (fun (n1, k1, f1) ->
                 (n1 <= n) && (k1 <= k))
               list)
          then
            list
          else
            (n, k, DIAMOND (label, AND formula_list)) ::
              (List.filter
                 (fun (n1, k1, f1) ->
                   (n1 < n) || (k1 < k))
                 list)

        let add_round (n1, k1, f1) = (n1, k1 + 1, f1)

        let add_round_and_alternation (n1, k1, f1) = (n1 + 1, k1 + 1, negation f1)

        let base_case_strategy = (0, 1, [AND[]])

        let base_case_strategy_options = (0, 0, [])

      end)

      module Strategy_without_formula = (struct

        type strategy = int * int

        type strategy_options = int * int

        type no_table_entry = LTS.V.t * LTS.V.t * strategy

        type no_table = no_table_entry list

        let add_entry_no_table
            no_table
            p
            q
            (n, k) =
          if
            (List.exists
               (function (p1, q1, (n1, k1)) ->
                 (p1 = p) && (q1 = q) && (n1 <= n) && (k1 <= k))
               no_table)
          then
            no_table
          else
            ((p, q, (n, k))::
                (List.filter
                   (function (p1, q1, (n1, k1)) ->
                     (p1 <> p) || (q1 <> q) || (n1 < n) || (k1 < k))
                   no_table))

        let fetch_entries_no_table no_table p q n k =
          List.map
            (function (_, _, (n1, k1)) -> (n1, k1))
            (List.filter
               (function (p1, q1, (n1, k1)) ->
                 (p1 = p) && (q1 = q) && (n1 <= n) && (k1 <= k))
               no_table)

        let create_no_table () = []

        let add_winning_strategy list (n, k) =
          List.map
            (function
          (max_n,
           max_k) ->
            ((if
                max_n < n
              then n
              else max_n),
             (if
                 max_k < k
              then k
              else max_k)))
            list

        let add_optimal_winning_strategy, add_optimal_winning_strategy_options =
          let g
              list
              (n, k) =
            if
              List.exists
                (fun (n1, k1) ->
                  (n1 <= n) && (k1 <= k))
                list
            then
              list
            else
              (n, k) ::
                (List.filter
                   (fun (n1, k1) ->
                     (n1 < n) || (k1 < k))
                   list)
          in
          g, g

        let add_formula_base_case
            label
            list
            (n, k) =
          if
            (List.exists
               (fun (n1, k1) ->
                 (n1 <= n) && (k1 <= k))
               list)
          then
            list
          else
            (n, k) ::
              (List.filter
                 (fun (n1, k1) ->
                   (n1 < n) || (k1 < k))
                 list)

        let add_round (n1, k1) = (n1, k1 + 1)

        let add_round_and_alternation (n1, k1) = (n1 + 1, k1 + 1)

        let base_case_strategy = (0, 1)

        let base_case_strategy_options = (0, 0)

      end)

      module Relation_functor = functor
          (Strategy: sig
            type strategy
            type no_table_entry
            type no_table
            type strategy_options
            val add_entry_no_table:
              no_table ->
              LTS.V.t ->
              LTS.V.t ->
              strategy ->
              no_table
            val fetch_entries_no_table:
              no_table ->
              LTS.V.t ->
              LTS.V.t ->
              int ->
              int ->
              strategy list
            val create_no_table:
              unit ->
              no_table
            val add_winning_strategy:
              strategy_options list ->
              strategy ->
              strategy_options list
            val add_optimal_winning_strategy:
              strategy list -> strategy -> strategy list
            val add_optimal_winning_strategy_options:
              strategy_options list -> strategy_options -> strategy_options list
            val add_formula_base_case:
              LTS.A.t ->
              strategy list ->
              strategy_options ->
              strategy list
            val add_round: strategy -> strategy
            val add_round_and_alternation: strategy -> strategy
            val base_case_strategy: strategy_options
            val base_case_strategy_options: strategy_options
          end) -> (struct
            open Strategy

            (* we assume that p is the challenger's position in lts1 and q is
               the defender's position in lts2. thus, if the challenger switches to
               q now and makes a move in lts2, then we use up one alternation,
               otherwise we have the same number of alternations remaining.*)
            let rec
	        get_strategies
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
	        rel = (
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
                                      (get_strategies
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
                                         add_round
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
                                        (get_strategies
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
                                         add_round_and_alternation
                                         l_qq) (* one more round, one more alternation. *)
                                    in
                                    let
                                        l_pp_qq =
                                      List.fold_left
                                        add_optimal_winning_strategy
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
                                                (add_winning_strategy partial_l_q)
                                                l_pp_qq)))
                                    in
                                    (* this is where we get rid of cruft
                                       in the cartesian product we have
                                       built so far.*)
                                    let
                                        partial_l_q =
                                      (List.fold_left
                                         add_optimal_winning_strategy_options
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
		              (false, false, [base_case_strategy_options], yes_table, no_table)
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
                             [base_case_strategy]
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
                            (add_formula_base_case
                               (LTS.E.label e_p))
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
                       (fun no_table ->
                         add_entry_no_table no_table p q)
                       no_table
                       l_p
                    )
                )
            )

            let
	        get_strategies1
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
	        get_strategies
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
	        get_strategies2
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
	        get_strategies
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
	        get_strategies
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
	        add_optimal_winning_strategy
	        []
	        (l1 @ l2)

          end)

      module Relations_with_formulae = Relation_functor(Strategy_with_formula)
      module Relations_without_formulae = Relation_functor(Strategy_without_formula)

      let get_distinguishing_formulae = Relations_with_formulae.get_strategies

      let get_distinguishing_formulae1 = Relations_with_formulae.get_strategies1

      let get_distinguishing_formulae2 = Relations_with_formulae.get_strategies2

      let get_nk_pairs1 = Relations_without_formulae.get_strategies1

      let get_nk_pairs2 = Relations_without_formulae.get_strategies2

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
