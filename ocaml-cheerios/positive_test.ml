open Positive_extracted

let rec print_positive p =
  match p with
  | XI p -> Printf.printf "XI "; print_positive p
  | XO p -> Printf.printf "XO "; print_positive p
  | XH -> Printf.printf "XH"
;;
  
let test_positive p = 
  let _ = Printf.printf "Serializing/deserializing ";
          print_positive p;
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
  
let _ = test_positive XH;
        test_positive (XI XH);
        test_positive (XO XH);
        test_positive (XI (XI XH));
        test_positive (XO (XI XH));
        test_positive (XI (XI (XO (XO XH))));
        test_positive (XI (XI (XO (XI (XO (XO (XO XH)))))));;

(* benchmarking *)
let time_cheerios_serialize_once (p : positive) : float =
  let start = Sys.time () in
  let _ = serialize_positive p in
  let stop = Sys.time () in
  stop -. start
;;

let rec time_cheerios_loop max =
  let interval = 50 in
  let rec loop n = 
    if n = max
    then ()
    else Printf.printf "Time for size %d: %f"
                       n
                       (time_cheerios_serialize_once (make_positive (n * interval)));
    loop (n + 1) in
  loop 0
;;


(* 
  
let marshalled =
  Marshal.to_bytes XH []
;;

let p = Marshal.from_bytes marshalled 0;;
let _ = print_positive p;;
 *)

let _ = Printf.printf "Time: %f\n" (time_cheerios_serialize_once
                                      (make_positive 100000))
;;
