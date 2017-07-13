open Tree_serializer
open Test_utils
       
let rec make elem height width =
  if height = 0
  then Atom elem
  else let rec loop n acc =
         if n = 0
         then acc
         else loop (n - 1) (make elem (height - 1) width :: acc) in
       Node (loop width [])

let test_width max_height width =
  let rec loop i =
    if i < max_height
    then (test_serialize_deserialize (make false i width)
                                     tree_serialize_top
                                     (fun w -> match tree_deserialize_top w with
                                               | Some p -> p
                                               | None -> failwith "Deserialization failed")
                                     (fun _ -> Printf.printf "height %d, width %d"
                                                             i width);
          loop (i + 1)) in
  loop 0

(* main functions *)
let test_main () =
  test_width 15 2;
  test_width 10 3;
  test_width 10 4;
  test_width 8 5

let space_main () =
  let max_height = 10 in
  let rec loop i =
    if i < max_height
    then (compare_cheerios_marshal_space (fun n -> make false n 2) (tree_serialize_top) i;
          loop (i + 1))
  in
  print_string "\nSpace usage tests...\n";
  loop 0

let bench_main () =
  print_string "\nBenchmarks...\n";
  compare_time_loop (fun n -> make false n 2)
                    40 1 2
                    tree_serialize_top
                    (fun w -> match tree_deserialize_top w with
                              | Some p -> p
                              | None -> failwith "Deserialization failed")
                    
                    
let avg_time_height (f : 'a tree -> 'b) (h : int) =
  let num_tries = 100 in
  avg (time_loop (fun n -> make false n 2) h num_tries f)

let compare_map_main () =
  let max_height = 25 in
  let rec loop i =
    if i < max_height
    then let map_avg = avg_time_height (map0 (fun _ -> ())) i in
         let tr_map_avg = avg_time_height (tree_map' (fun _ -> ())) i in
         (Printf.printf "map: %f, tail-rec map: %f \n%!" map_avg tr_map_avg;
          loop (i + 1)) in
  loop 0

let compare_serialize_tr_main () =
  let max_height = 25 in
  let rec loop i =
    if i < max_height
    then let s_avg = avg_time_height (fun t -> t) i in
         let tr_s_avg = avg_time_height tree_serialize_top' i in
         (Printf.printf "height: %d, serialize: %f, tail-rec serialize: %f \n%!"
                        i s_avg tr_s_avg;
          loop (i + 1)) in
  loop 0
                    
let main () = test_main ();
              space_main ();
              bench_main ()

let _ = compare_serialize_tr_main ()
