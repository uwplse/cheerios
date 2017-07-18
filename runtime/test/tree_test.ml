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
                                     tree_serialize_iostream_top
                                     (fun w -> match tree_deserialize_iostream_top w with
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
    then (compare_cheerios_marshal_space (fun n -> make false n 2) (tree_serialize_iostream_top) i;
          loop (i + 1))
  in
  print_string "\nSpace usage tests...\n";
  loop 0

let bench_main () =
  print_string "\nBenchmarks...\n";
  compare_time_loop (fun n -> make false n 2)
                    20 1 10
                    tree_serialize_iostream_top
                    (fun w -> match tree_deserialize_iostream_top w with
                              | Some p -> p
                              | None -> failwith "Deserialization failed")
                    
                    
let avg_time_height (f : 'a tree -> 'b) (h : int) =
  let num_tries = 10 in
  avg (time_loop (fun n -> make false n 2) h num_tries f)

let main () = test_main ();
              space_main ();
              bench_main ()

let _ = main ()
