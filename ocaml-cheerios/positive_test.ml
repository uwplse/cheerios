open Positive_extracted

let rec print_positive p =
  match p with
  | XI p -> Printf.printf "XI "; print_positive p
  | XO p -> Printf.printf "XO "; print_positive p
  | XH -> Printf.printf "XH"
;;
  
let make_positive n =
  let rec aux n flag k =
    if n = 0
    then k XH
    else aux (n - 1) (not flag) (if flag
                                 then fun p -> XI (k p)
                                 else fun p -> XO (k p)) in
  aux n true (fun p -> p)
;;

let rec serialize_positive_two p =
  match p with
  | XI (XI p) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\000')
                                  (serialize_positive_two p)
  | XI (XO p) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\001')
                                  (serialize_positive_two p)
  | XO (XI p) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\002')
                                  (serialize_positive_two p)
  | XO (XO p) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\003')
                                  (serialize_positive_two p)
  | XI p ->
     Serializer_primitives.append (ascii_Serializer.serialize '\004')
                                  (serialize_positive_two p)
  | XO p ->
     Serializer_primitives.append (ascii_Serializer.serialize '\005')
                                  (serialize_positive_two p)
  | XH -> ascii_Serializer.serialize '\006'
;;

(* unverified and doesn't correspond to any deserializer *)
let rec serialize_positive_three p =
  match p with
  | XI (XI (XI p)) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\014')
                                  (serialize_positive_three p)
  | XI (XI (XO p)) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\013')
                                  (serialize_positive_three p)
  | XI (XO (XI p)) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\012')
                                  (serialize_positive_three p)
  | XI (XO (XO p)) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\011')
                                  (serialize_positive_three p)
  | XO (XI (XI p)) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\010')
                                  (serialize_positive_three p)
  | XO (XI (XO p)) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\009')
                                  (serialize_positive_three p)
  | XO (XO (XI p)) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\008')
                                  (serialize_positive_three p)
  | XO (XO (XO p)) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\007')
                                  (serialize_positive_three p)
  | XI (XI p) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\006')
                                  (serialize_positive_three p)
  | XI (XO p) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\005')
                                  (serialize_positive_three p)
  | XO (XI p) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\004')
                                  (serialize_positive_three p)
  | XO (XO p) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\003')
                                  (serialize_positive_three p)
  | XI p ->
     Serializer_primitives.append (ascii_Serializer.serialize '\002')
                                  (serialize_positive_three p)
  | XO p ->
     Serializer_primitives.append (ascii_Serializer.serialize '\001')
                                  (serialize_positive_three p)
  | XH -> ascii_Serializer.serialize '\000'
;;

let rec serialize_positive_four p =
  match p with
  | XI (XI (XI (XI p))) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\030')
                                  (serialize_positive_four p)
  | XI (XI (XI (XO p))) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\029')
                                  (serialize_positive_four p)
  | XI (XI (XO (XI p))) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\028')
                                  (serialize_positive_four p)
  | XI (XI (XO (XO p))) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\027')
                                  (serialize_positive_four p)
  | XI (XO (XI (XI p))) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\026')
                                  (serialize_positive_four p)
  | XI (XO (XI (XO p))) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\025')
                                  (serialize_positive_four p)
  | XI (XO (XO (XI p))) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\024')
                                  (serialize_positive_four p)
  | XI (XO (XO (XO p))) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\023')
                                  (serialize_positive_four p)
  | XO (XI (XI (XI p))) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\022')
                                  (serialize_positive_four p)
  | XO (XI (XI (XO p))) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\021')
                                  (serialize_positive_four p)
  | XO (XI (XO (XI p))) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\020')
                                  (serialize_positive_four p)
  | XO (XI (XO (XO p))) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\019')
                                  (serialize_positive_four p)
  | XO (XO (XI (XI p))) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\018')
                                  (serialize_positive_four p)
  | XO (XO (XI (XO p))) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\017')
                                  (serialize_positive_four p)
  | XO (XO (XO (XI p))) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\016')
                                  (serialize_positive_four p)
  | XO (XO (XO (XO p))) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\015')
                                  (serialize_positive_four p)
  | XI (XI (XI p)) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\014')
                                  (serialize_positive_four p)
  | XI (XI (XO p)) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\013')
                                  (serialize_positive_four p)
  | XI (XO (XI p)) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\012')
                                  (serialize_positive_four p)
  | XI (XO (XO p)) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\011')
                                  (serialize_positive_four p)
  | XO (XI (XI p)) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\010')
                                  (serialize_positive_four p)
  | XO (XI (XO p)) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\009')
                                  (serialize_positive_four p)
  | XO (XO (XI p)) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\008')
                                  (serialize_positive_four p)
  | XO (XO (XO p)) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\007')
                                  (serialize_positive_four p)
  | XI (XI p) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\006')
                                  (serialize_positive_four p)
  | XI (XO p) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\005')
                                  (serialize_positive_four p)
  | XO (XI p) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\004')
                                  (serialize_positive_four p)
  | XO (XO p) ->
     Serializer_primitives.append (ascii_Serializer.serialize '\003')
                                  (serialize_positive_four p)
  | XI p ->
     Serializer_primitives.append (ascii_Serializer.serialize '\002')
                                  (serialize_positive_four p)
  | XO p ->
     Serializer_primitives.append (ascii_Serializer.serialize '\001')
                                  (serialize_positive_four p)
  | XH -> ascii_Serializer.serialize '\000'
;;

let test_positive p print = 
  let _ = Printf.printf "Serializing/deserializing ";
          print p;
          Printf.printf "... " in
  let w = Bit_vector.makeWriter () in
  let _ = serialize_positive p w in
  let r = Bit_vector.writerToReader w in
  let p' = deserialize_positive r in
  let true = p = p' in
  Printf.printf "success\n"
;;

let test_main max =
  let rec loop n =
    if n < max
    then (test_positive (make_positive n)
                        (fun _ -> Printf.printf "make_positive %d" n);
          loop (n + 1))
  in loop 0
;;

(*
let _ = test_main 1000;;
 *)
(* benchmarking *)
  
let time_serialize (p : positive) (serialize : positive -> unit) : float =
  let start = Sys.time () in
  let _ = serialize p in
  let stop = Sys.time () in
  stop -. start
;;

let rec time_serialize_loop size n serialize =
  let rec loop i acc = 
    if i = n
    then acc
    else loop (i + 1)
              (time_serialize (make_positive size) serialize :: acc)
  in loop 0 []
;;

let avg l =
  (List.fold_left (+.) 0.0 l) /. (float_of_int (List.length l))
;;

let compare_cheerios_marshall size n =
  let cheerios_avg =
    avg (time_serialize_loop size n
                             (fun p ->
                               let w = Bit_vector.makeWriter ()
                               in (serialize_positive p w); ())) in
  let two_avg =
    avg (time_serialize_loop size n
                             (fun p ->
                               let w = Bit_vector.makeWriter ()
                               in (serialize_positive_two p w); ())) in

  let three_avg =
    avg (time_serialize_loop size n
                             (fun p ->
                               let w = Bit_vector.makeWriter ()
                               in (serialize_positive_three p w); ())) in
(*
  let four_avg =
    avg (time_serialize_loop size n
                             (fun p ->
                               let w = Bit_vector.makeWriter ()
                               in (serialize_positive_four p w); ())) in
 *)
  let marshal_avg =
    avg (time_serialize_loop size n
                             (fun p -> ignore (Marshal.to_bytes p [])))
  in Printf.printf
       "size: %d, cheerios: %f, two: %f, three: %f, marshal: %f\n"
                   size cheerios_avg two_avg three_avg marshal_avg
;;

let compare_main max interval =
  let rec loop n =
    if n < max
    then let num_tries = 500 in
         (compare_cheerios_marshall n num_tries;
          loop (n + interval)) in
  loop 0
;;

let _ = compare_main 150000 20000
