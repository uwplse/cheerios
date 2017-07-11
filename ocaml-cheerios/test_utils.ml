let test_serialize_deserialize (v : 'a)
                               (serialize : 'a -> 'b)
                               (deserialize : 'b -> 'a)
                               (print : 'a -> unit) = 
  let _ = Printf.printf "Serializing/deserializing ";
          print v;
          Printf.printf "... " in
  let serialized = serialize v in
  let v' = deserialize serialized in 
  (assert (v = v'));  Printf.printf "success\n"
;;

(* benchmarking *)
  
let time_serialize_deserialize (p : 'a)
                               (serialize : 'a -> 'b)
                               (deserialize: 'b -> 'a) : float * float =
  let serialize_start = Sys.time () in
  let serialized = serialize p in
  let serialize_stop = Sys.time () in
  let _ = deserialize serialized in
  let deserialize_stop = Sys.time () in
  (serialize_stop -. serialize_start, deserialize_stop -. serialize_stop)
;;

let rec time_serialize_deserialize_loop make size n
                                        serialize deserialize =
  let rec loop i acc = 
    if i = n
    then acc
    else loop (i + 1)
              (time_serialize_deserialize (make size)
                                          serialize
                                          deserialize :: acc)
  in loop 0 []
;;

let avg l =
  (List.fold_left (+.) 0.0 l) /. (float_of_int (List.length l))
;;
