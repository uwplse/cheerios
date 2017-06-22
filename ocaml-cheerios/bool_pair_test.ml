let test_pair (x, y) = 
  let w = Bit_vector.makeWriter () in
  let _ = serialize_bool_pair (x, y) w in
  let r = Bit_vector.writerToReader w in
  let (x', y') = deserialize_bool_pair r in
  let true = x = x' && y = y' in
  ()
;;
                             
let _ = test_pair (false, false);;
let _ = test_pair (false, true);;
let _ = test_pair (true, false);;
let _ = test_pair (true, true);;
