open Positive_serializer
open Test_utils

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
     Serializer_primitives.append (byte_Serializer.serialize '\000')
                                  (serialize_positive_two p)
  | XI (XO p) ->
     Serializer_primitives.append (byte_Serializer.serialize '\001')
                                  (serialize_positive_two p)
  | XO (XI p) ->
     Serializer_primitives.append (byte_Serializer.serialize '\002')
                                  (serialize_positive_two p)
  | XO (XO p) ->
     Serializer_primitives.append (byte_Serializer.serialize '\003')
                                  (serialize_positive_two p)
  | XI p ->
     Serializer_primitives.append (byte_Serializer.serialize '\004')
                                  (serialize_positive_two p)
  | XO p ->
     Serializer_primitives.append (byte_Serializer.serialize '\005')
                                  (serialize_positive_two p)
  | XH -> byte_Serializer.serialize '\006'
;;

(* unverified and doesn't correspond to any deserializer *)
let rec serialize_positive_three p =
  match p with
  | XI (XI (XI p)) ->
     Serializer_primitives.append (byte_Serializer.serialize '\014')
                                  (serialize_positive_three p)
  | XI (XI (XO p)) ->
     Serializer_primitives.append (byte_Serializer.serialize '\013')
                                  (serialize_positive_three p)
  | XI (XO (XI p)) ->
     Serializer_primitives.append (byte_Serializer.serialize '\012')
                                  (serialize_positive_three p)
  | XI (XO (XO p)) ->
     Serializer_primitives.append (byte_Serializer.serialize '\011')
                                  (serialize_positive_three p)
  | XO (XI (XI p)) ->
     Serializer_primitives.append (byte_Serializer.serialize '\010')
                                  (serialize_positive_three p)
  | XO (XI (XO p)) ->
     Serializer_primitives.append (byte_Serializer.serialize '\009')
                                  (serialize_positive_three p)
  | XO (XO (XI p)) ->
     Serializer_primitives.append (byte_Serializer.serialize '\008')
                                  (serialize_positive_three p)
  | XO (XO (XO p)) ->
     Serializer_primitives.append (byte_Serializer.serialize '\007')
                                  (serialize_positive_three p)
  | XI (XI p) ->
     Serializer_primitives.append (byte_Serializer.serialize '\006')
                                  (serialize_positive_three p)
  | XI (XO p) ->
     Serializer_primitives.append (byte_Serializer.serialize '\005')
                                  (serialize_positive_three p)
  | XO (XI p) ->
     Serializer_primitives.append (byte_Serializer.serialize '\004')
                                  (serialize_positive_three p)
  | XO (XO p) ->
     Serializer_primitives.append (byte_Serializer.serialize '\003')
                                  (serialize_positive_three p)
  | XI p ->
     Serializer_primitives.append (byte_Serializer.serialize '\002')
                                  (serialize_positive_three p)
  | XO p ->
     Serializer_primitives.append (byte_Serializer.serialize '\001')
                                  (serialize_positive_three p)
  | XH -> byte_Serializer.serialize '\000'
;;

let rec serialize_positive_four p =
  match p with
  | XI (XI (XI (XI p))) ->
     Serializer_primitives.append (byte_Serializer.serialize '\030')
                                  (serialize_positive_four p)
  | XI (XI (XI (XO p))) ->
     Serializer_primitives.append (byte_Serializer.serialize '\029')
                                  (serialize_positive_four p)
  | XI (XI (XO (XI p))) ->
     Serializer_primitives.append (byte_Serializer.serialize '\028')
                                  (serialize_positive_four p)
  | XI (XI (XO (XO p))) ->
     Serializer_primitives.append (byte_Serializer.serialize '\027')
                                  (serialize_positive_four p)
  | XI (XO (XI (XI p))) ->
     Serializer_primitives.append (byte_Serializer.serialize '\026')
                                  (serialize_positive_four p)
  | XI (XO (XI (XO p))) ->
     Serializer_primitives.append (byte_Serializer.serialize '\025')
                                  (serialize_positive_four p)
  | XI (XO (XO (XI p))) ->
     Serializer_primitives.append (byte_Serializer.serialize '\024')
                                  (serialize_positive_four p)
  | XI (XO (XO (XO p))) ->
     Serializer_primitives.append (byte_Serializer.serialize '\023')
                                  (serialize_positive_four p)
  | XO (XI (XI (XI p))) ->
     Serializer_primitives.append (byte_Serializer.serialize '\022')
                                  (serialize_positive_four p)
  | XO (XI (XI (XO p))) ->
     Serializer_primitives.append (byte_Serializer.serialize '\021')
                                  (serialize_positive_four p)
  | XO (XI (XO (XI p))) ->
     Serializer_primitives.append (byte_Serializer.serialize '\020')
                                  (serialize_positive_four p)
  | XO (XI (XO (XO p))) ->
     Serializer_primitives.append (byte_Serializer.serialize '\019')
                                  (serialize_positive_four p)
  | XO (XO (XI (XI p))) ->
     Serializer_primitives.append (byte_Serializer.serialize '\018')
                                  (serialize_positive_four p)
  | XO (XO (XI (XO p))) ->
     Serializer_primitives.append (byte_Serializer.serialize '\017')
                                  (serialize_positive_four p)
  | XO (XO (XO (XI p))) ->
     Serializer_primitives.append (byte_Serializer.serialize '\016')
                                  (serialize_positive_four p)
  | XO (XO (XO (XO p))) ->
     Serializer_primitives.append (byte_Serializer.serialize '\015')
                                  (serialize_positive_four p)
  | XI (XI (XI p)) ->
     Serializer_primitives.append (byte_Serializer.serialize '\014')
                                  (serialize_positive_four p)
  | XI (XI (XO p)) ->
     Serializer_primitives.append (byte_Serializer.serialize '\013')
                                  (serialize_positive_four p)
  | XI (XO (XI p)) ->
     Serializer_primitives.append (byte_Serializer.serialize '\012')
                                  (serialize_positive_four p)
  | XI (XO (XO p)) ->
     Serializer_primitives.append (byte_Serializer.serialize '\011')
                                  (serialize_positive_four p)
  | XO (XI (XI p)) ->
     Serializer_primitives.append (byte_Serializer.serialize '\010')
                                  (serialize_positive_four p)
  | XO (XI (XO p)) ->
     Serializer_primitives.append (byte_Serializer.serialize '\009')
                                  (serialize_positive_four p)
  | XO (XO (XI p)) ->
     Serializer_primitives.append (byte_Serializer.serialize '\008')
                                  (serialize_positive_four p)
  | XO (XO (XO p)) ->
     Serializer_primitives.append (byte_Serializer.serialize '\007')
                                  (serialize_positive_four p)
  | XI (XI p) ->
     Serializer_primitives.append (byte_Serializer.serialize '\006')
                                  (serialize_positive_four p)
  | XI (XO p) ->
     Serializer_primitives.append (byte_Serializer.serialize '\005')
                                  (serialize_positive_four p)
  | XO (XI p) ->
     Serializer_primitives.append (byte_Serializer.serialize '\004')
                                  (serialize_positive_four p)
  | XO (XO p) ->
     Serializer_primitives.append (byte_Serializer.serialize '\003')
                                  (serialize_positive_four p)
  | XI p ->
     Serializer_primitives.append (byte_Serializer.serialize '\002')
                                  (serialize_positive_four p)
  | XO p ->
     Serializer_primitives.append (byte_Serializer.serialize '\001')
                                  (serialize_positive_four p)
  | XH -> byte_Serializer.serialize '\000'
;;


let test_cheerios p print =
  test_serialize_deserialize p
                             positive_serialize_top
                             (fun w -> match positive_deserialize_top w with
                                       | Some p -> p
                                       | None -> failwith "Deserialization failed")
                             print
;;

let test_main max =
  let rec loop n =
    if n < max
    then (test_cheerios (make_positive n)
                        (fun _ -> Printf.printf "make_positive %d" n);
          loop (n + 1))
  in loop 0
;;

let _ = test_main 1000;;

(* benchmarking *)
  
let compare_cheerios_marshal_time make size n
                                  serialize deserialize =
  let cheerios_results : (float * float) list =
    time_serialize_deserialize_loop
      make size n
      serialize deserialize
  in
  let marshal_results : (float * float) list =
    time_serialize_deserialize_loop
      make size n
      (fun p -> Marshal.to_bytes p [])
      (fun b -> (Marshal.from_bytes b 0))
       in
  let cheerios_serialize_avg = avg (List.map fst cheerios_results) in
  let marshal_serialize_avg =  avg (List.map fst marshal_results) in
  let cheerios_deserialize_avg = avg (List.map snd cheerios_results) in
  let marshal_deserialize_avg =  avg (List.map snd marshal_results) in
  Printf.printf "size %d - serialize: cheerios %f, marshal %f"
                size cheerios_serialize_avg marshal_serialize_avg;
  Printf.printf " || deserialize: cheerios %f, marshal %f\n"
                cheerios_deserialize_avg marshal_deserialize_avg
;;

let _ = compare_time_loop make_positive 50000 20000 positive_serialize_top
                     (fun w -> match positive_deserialize_top w with
                               | Some p -> p
                               | None -> failwith "Deserialization failed")
                     
