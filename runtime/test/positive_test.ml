open Positive_serializer
open Test_utils

let rec print_positive p =
  match p with
  | XI p -> Printf.printf "XI "; print_positive p
  | XO p -> Printf.printf "XO "; print_positive p
  | XH -> Printf.printf "XH"
  
let make_positive n =
  let rec aux n flag k =
    if n = 0
    then k XH
    else aux (n - 1) (not flag) (if flag
                                 then fun p -> XI (k p)
                                 else fun p -> XO (k p)) in
  aux n true (fun p -> p)

let test_cheerios p print =
  test_serialize_deserialize p
                             positive_serialize_iostream_top
                             (fun w -> match positive_deserialize_iostream_top w with
                                       | Some p -> p
                                       | None -> failwith "Deserialization failed")
                             print

let test_main max =
  let rec loop n =
    if n < max
    then (test_cheerios (make_positive n)
                        (fun _ -> Printf.printf "make_positive %d%!" n);
          loop (n + 1))
  in loop 0

(* benchmarking *)
let bench_main () =
  compare_time_loop make_positive
                    200000 20000 100
                    positive_serialize_iostream_top
                    (fun w -> match positive_deserialize_iostream_top w with
                              | Some p -> p
                              | None -> failwith "Deserialization failed")

let _ = test_main 1000;
        bench_main ()
