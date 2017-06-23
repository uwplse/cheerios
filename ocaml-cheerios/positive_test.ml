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

let _ = test_positive XH;
        test_positive (XI XH);
        test_positive (XO XH);
        test_positive (XI (XI XH));
        test_positive (XO (XI XH));
        test_positive (XI (XI (XO (XO XH))));
        test_positive (XI (XI (XO (XI (XO (XO (XO XH)))))));;
