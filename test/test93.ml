open LTS_modules

let test93 =
  exit
    (try
       match
	 IntIntLTS.add_edge IntIntLTS.empty 0 1
       with
       | _ -> 0
     with
     | Invalid_argument _ -> 1)
