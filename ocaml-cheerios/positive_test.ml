open Positive_extracted

let rec print_positive p =
  match p with
  | XI p -> Printf.printf "XI "; print_positive p
  | XO p -> Printf.printf "XO "; print_positive p
  | XH -> Printf.printf "XH"
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

let make_positive n =
  let rec aux n flag k =
    if n = 0
    then k XH
    else aux (n - 1) (not flag) (if flag
                                 then fun p -> XI (k p)
                                 else fun p -> XO (k p)) in
  aux n true (fun p -> p)
;;

let test_main max =
  let rec loop n =
    if n = max
    then ()
    else (test_positive (make_positive n)
                        (fun _ -> Printf.printf "make_positive %d" n);
          loop (n + 1))
  in loop 0;;

  
(*
let _ = test_main 100;;
 *)

(* benchmarking *)
let time_serialize (p : positive)
                            (serialize : positive -> unit)  : float =
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
  let marshal_avg =
    avg (time_serialize_loop size n
                             (fun p -> ignore (Marshal.to_bytes p [])))
  in Printf.printf "size: %d, cheerios: %f, marshal: %f\n"
                   size cheerios_avg marshal_avg
;;

let compare_main max interval =
  let rec loop n =
    if n < max
    then  let num_tries = 300 in
          (compare_cheerios_marshall n num_tries;
          loop (n + interval))
    else () in
  loop 0
;;

let _ = compare_main 10000 2000
