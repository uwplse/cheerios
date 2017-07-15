type serializer = Bit_vector.writer -> unit
type 'a deserializer = Bit_vector.reader -> 'a
type wire = bytes

(* serializer *)

let empty : serializer = fun w -> ()

let putByte (b : char) : serializer =
  fun w -> Bit_vector.pushBack w b

let append (m1 : unit -> serializer) (m2 : unit -> serializer) : serializer =
  fun w ->
  m1 () w;
  m2 () w

let putInt (i : int32) : serializer =
  let aux n = putByte (Char.chr ((Int32.to_int i lsr n) land 0xff))
  in append (fun () -> (aux 24))
            (fun () -> (append (fun () -> (aux 16))
                               (fun () -> (append (fun () -> (aux 8))
                                                  (fun () -> (aux 0))))))

(* deserializer *)
  
let getByte =
  Bit_vector.pop

let bind (d : 'a deserializer) (f : 'a -> 'b deserializer) : 'b deserializer =
  fun r -> let v = d r in
           (f v) r
                 
let ret (v : 'a) : 'a deserializer =
  fun r -> v

let getInt : int32 deserializer =
  let aux b n = Char.code b lsl n in
  bind getByte (fun b1 ->
         bind getByte (fun b2 ->
                bind getByte (fun b3 ->
                       bind getByte (fun b4 ->
                              let i = (aux b1 24) lor
                                        (aux b2 16) lor
                                          (aux b3 8) lor
                                            (aux b4 0) in
                                       ret (Int32.of_int i)))))

let fail : 'a deserializer =
  fun r -> failwith "Deserialization failed"
  
type ('s, 'a) fold_state =
  | Done of 'a
  | More of 's
  | Error

let map (f : 'a -> 'b) (d : 'a deserializer) : 'b deserializer =
  bind d (fun a -> ret (f a))

let rec fold (f : char -> 's -> ('s, 'a) fold_state)
                          (s : 's) : 'a deserializer =
  fun r -> let b = getByte r
           in match f b s with
              | Done a -> a
              | More s -> fold f s r
              | Error -> failwith "Fold deserializer error"
  
(* wire *)

let wire_wrap (s : serializer) : wire =
  let w = Bit_vector.makeWriter () in
  (s w;
   Bit_vector.writerToBytes w)

let size : wire -> int =
  Bytes.length

let deserialize_top (dummy: 'b) (d : 'a deserializer) (w : wire) : 'a option =
  Some (d (Bit_vector.bytesToReader w))

let dump (w : wire) : unit =
  let rec loop i =
    if i < Bytes.length w
    then (Printf.printf "%x %!" (Char.code (Bytes.get w i));
          loop (i + 1)) in
  loop 0; Printf.printf "\n%!"
           
