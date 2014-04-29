open LTS_modules.ml

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
  IntIntLTSDotParse.parse "test/l19.dot"

let l20 =
  IntIntLTSDotParse.parse "test/l20.dot"

let l21 =
  IntIntLTSDotParse.parse "test/l21.dot"

let l22 =
  IntIntLTSDotParse.parse "test/l22.dot"

let l23 =
  IntIntLTSDotParse.parse "test/l23.dot"

let l24 =
  IntIntLTSDotParse.parse "test/l24.dot"

let l25 =
  IntIntLTSDotParse.parse "test/l25.dot"

    (* Debugging output. *)
    (* let () = *)
    (*   IntIntLTS.iter_vertex *)
    (*     (function v -> *)
    (*       Printf.printf *)
    (*         "v = %s\n" *)
    (*         (string_of_int v) *)
    (*     ) *)
    (*     l04 *)

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
