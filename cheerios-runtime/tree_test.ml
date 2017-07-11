open Tree_extracted
open Test_utils
       
let rec make elem height width =
  if height = 0
  then Atom elem
  else let rec loop n acc =
         if n = 0
         then acc
         else loop (n - 1) (make elem (height - 1) width :: acc) in
       Node (loop width [])
;;

let test_main n width =
  let rec loop i =
    if i < n
    then (test_serialize_deserialize (make false i width)
                                    tree_serialize_top
                                    (fun w -> match tree_deserialize_top w with
                                              | Some p -> p
                                              | None -> failwith "Deserialization failed")
                                    (fun _ -> Printf.printf "height %d, width %d"
                                                            i width);
          loop (i + 1)) in
  loop 0
;;

let _ = test_main 15 2;
        test_main 10 3;
        test_main 10 4;
        test_main 8 5;;

       
                               
