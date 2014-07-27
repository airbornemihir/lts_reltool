open LTS_modules

let _ =
  let
      n = ref (-1)
  in
  let
      k = ref (-1)
  in
  let
      lts1 = ref ""
  in
  let
      lts2 = ref ""
  in
  let
      p = ref (-1)
  in
  let
      q = ref (-1)
  in
  let
      relation = ref false
  in
  let
      pairs = ref false
  in
  let
      equivalence = ref false
  in
  let
      () =
    Arg.parse
      [("-n", Arg.Set_int n, "number of alternations allowed.");
       ("-k", Arg.Set_int k, "number of rounds allowed.");
       ("--lts1", Arg.Set_string lts1, "lts where challenger begins.");
       ("--lts2", Arg.Set_string lts2, "lts where defender begins.");
       ("-p", Arg.Set_int p, "initial state in lts1.");
       ("-q", Arg.Set_int q, "initial state in lts2.");
       ("--pairs", Arg.Set pairs, "print (n, k) pairs only.");
       ("--relation", Arg.Set relation, "print existence of relation only.");
       ("--equivalence", Arg.Set equivalence, "use the equivalence relation.")]
      (fun (argument:string) -> ())
      "-n, -k, --lts1, --lts2, -p and -q are mandatory arguments."
  in
  if
    !pairs || !relation
  then
    (let
        result =
       (if
	   !equivalence
        then
	   IntIntLTSNK_Rel.get_nk_pairs2
        else
	   IntIntLTSNK_Rel.get_nk_pairs1)
         (IntIntLTSDotParse.parse !lts1)
         (IntIntLTSDotParse.parse !lts2)
         !p
         !q
         !n
         !k
     in
     let
         () =
       Printf.printf "%s\n"
         (match
	     result
          with
          | [] -> "The relation holds."
          | _ -> "The relation does not hold."
         )
     in
     let
         () =
       if
	 !pairs
       then
         (List.iter
            (function ((n:int), (k:int)) ->
	      Printf.printf
                "n = %s, k = %s\n"
                (string_of_int n)
                (string_of_int k)
            )
            result)
       else
	 ()
     in
     exit 0)
  else
    (let
        result =
       (if
	   !equivalence
        then
	   IntIntLTSNK_Rel.get_distinguishing_formulae2
        else
	   IntIntLTSNK_Rel.get_distinguishing_formulae1)
         (IntIntLTSDotParse.parse !lts1)
         (IntIntLTSDotParse.parse !lts2)
         !p
         !q
         !n
         !k
     in
     let
         () =
       Printf.printf "%s\n"
         (match
	     result
          with
          | [] -> "The relation holds."
          | _ -> "The relation does not hold."
         )
     in
     let
         () =
       (List.iter
          (function ((n:int), (k:int), (f:IntIntLTSNK_Rel.hm_formula)) ->
	    Printf.printf
              "n = %s, k = %s, f = %s\n"
              (string_of_int n)
              (string_of_int k)
              (IntIntLTSNK_Rel.translate (IntIntLTSNK_Rel.minimise f)))
          result)
     in
     exit 0);;
