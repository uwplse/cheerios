let pair_s : Serializer.t =
  bool_pair_serialize (true, false);;
let w = Bit_vector.makeWriter ();;
let _ = pair_s w;;
let r = Bit_vector.writerToReader w;;
let _ = Bit_vector.dumpReader r;;
let (x, y) = bool_pair_deserialize r;;
let _ = Printf.printf "%b, %b\n" x y
      
