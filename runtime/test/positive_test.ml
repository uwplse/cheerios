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

let rec serialize_positive_three p =
  match p with
  | XI (XI (XI p)) -> fun w ->
                      (byte_Serializer.serialize '\014' w;
                       serialize_positive_three p w)
  | XI (XI (XO p)) -> fun w ->
                      (byte_Serializer.serialize '\013' w;
                       serialize_positive_three p w)
  | XI (XO (XI p)) -> fun w ->
                      (byte_Serializer.serialize '\012' w;
                       serialize_positive_three p w)
  | XI (XO (XO p)) -> fun w ->
                      (byte_Serializer.serialize '\011' w;
                       serialize_positive_three p w)
  | XO (XI (XI p)) -> fun w ->
                      (byte_Serializer.serialize '\010' w;
                       serialize_positive_three p w)
  | XO (XI (XO p)) -> fun w ->
                      (byte_Serializer.serialize '\009' w;
                       serialize_positive_three p w)
  | XO (XO (XI p)) -> fun w ->
                      (byte_Serializer.serialize '\008' w;
                       serialize_positive_three p w)
  | XO (XO (XO p)) -> fun w ->
                      (byte_Serializer.serialize '\007' w;
                       serialize_positive_three p w)
  | XI (XI p) -> fun w ->
                 (byte_Serializer.serialize '\006' w;
                  serialize_positive_three p w)
  | XI (XO p) -> fun w ->
                 (byte_Serializer.serialize '\005' w;
                  serialize_positive_three p w)
  | XO (XI p) -> fun w ->
                 (byte_Serializer.serialize '\004' w;
                  serialize_positive_three p w)
  | XO (XO p) -> fun w ->
                 (byte_Serializer.serialize '\003' w;
                  serialize_positive_three p w)
  | XI p -> fun w ->
            (byte_Serializer.serialize '\002' w;
             serialize_positive_three p w)
  | XO p -> fun w ->
            (byte_Serializer.serialize '\001' w;
             serialize_positive_three p w)
  | XH -> fun w -> byte_Serializer.serialize '\000' w

let test_cheerios p print =
  test_serialize_deserialize p
(*
                             (fun p -> Serializer_primitives.wire_wrap
                                         (serialize_positive_three p))
 *)
                             positive_serialize_top
                             (fun w -> match positive_deserialize_top w with
                                       | Some p -> p
                                       | None -> failwith "Deserialization failed")
                             print

let test_main max =
  let rec loop n =
    if n < max
    then (test_cheerios (make_positive n)
                        (fun _ -> Printf.printf "make_positive %d" n);
          loop (n + 1))
  in loop 0

let _ = test_main 1000

(* benchmarking *)
  
let _ = compare_time_loop make_positive
                          200000 20000 50

                          (*
                          positive_serialize_top
                           *)

                          (*
                          (fun p -> Serializer_primitives.wire_wrap
                                      (serialize_positive_three p))
                           *)

                          positive_serialize_top                          
                          (fun w -> match positive_deserialize_top w with
                                    | Some p -> p
                                    | None -> failwith "Deserialization failed")
