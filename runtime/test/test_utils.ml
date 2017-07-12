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

let marshal_test make n =
  let rec loop i =
    if i < n
    then let bytes = Marshal.to_bytes (make i) [] in
         let p = Marshal.from_bytes bytes 0 in
         (Printf.printf "testing marshal on make %d...\n" i;
          assert (p = make i);
          loop (i + 1)) in
  loop 0
;;

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

let compare_cheerios_marshal_space make serialize_top size =
  let v = make size in
  let cheerios_size =
    Serializer_primitives.size (serialize_top v) in
  let marshal_size = Marshal.total_size (Marshal.to_bytes v []) 0
  in Printf.printf "size: %d - cheerios: %d bytes, marshal: %d bytes\n"
                   size cheerios_size marshal_size
;;

let compare_time_loop make max interval num_tries serialize deserialize =
  let rec loop n =
    if n < max
    then (compare_cheerios_marshal_time
            make n num_tries
            serialize
            deserialize;
          loop (n + interval)) in
  loop 0
;;