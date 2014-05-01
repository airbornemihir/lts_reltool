open LTS_modules
  
let test94 =
  exit
    (try
       match
	 IntIntLTS.add_edge_e IntIntLTS.empty (IntIntLTS.E.create 0 0 1)
       with
       | _ -> 0
     with
     | Invalid_argument _ -> 1)
