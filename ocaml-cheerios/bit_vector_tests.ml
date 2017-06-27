let test_byte_vector (n : int) (f : int -> char) =
  let rec loop_write w i =
    if not (i = n)
    then (Serializer_primitives.putByte (f i) w;
          loop_write w (i + 1)) in
  let rec loop_read r i =
    if not (i = n)
    then (assert (Serializer_primitives.getByte r = f i);
          loop_read r (i + 1)) in
  let w = Bit_vector.makeWriter () in
  (loop_write w 0;
   let r = Bit_vector.writerToReader w in
   loop_read r 0)
;;

let main n =
  let rec loop i =
    if not (i = n)
    then (Printf.printf "Writing %d bytes...\n" i;
          test_byte_vector i (fun n -> Char.chr (n mod 256));
          loop (i + 1)) in
  loop 0
;;

let _ = main 10000
