type serializer = Bit_vector.writer -> unit
type 'a deserializer = Bit_vector.reader -> 'a
type wire = bytes

(* serializer *)

let empty : serializer = fun w -> ()
;;

let putByte (b : char) : serializer =
  fun w -> Bit_vector.pushBack w b  
;;

let empty : serializer =
  fun w -> ()
;;

let append (m1 : serializer) (m2 : serializer) : serializer =
  fun w ->
  m1 w;
  m2 w
;;  

(* deserializer *)
  
let getByte : char deserializer =
  Bit_vector.pop
;;

let bind (d : 'a deserializer) (f : 'a -> 'b deserializer) : 'b deserializer =
  fun r -> let v = d r in
           (f v) r
;;  
                 
let ret (v : 'a) : 'a deserializer =
  fun r -> v
;;

let fail : 'a deserializer =
  fun r -> failwith "Deserialization failed"
;;
  
type ('s, 'a) fold_state =
  | Done of 'a
  | More of 's
  | Error
;;

let map (f : 'a -> 'b) (d : 'a deserializer) : 'b deserializer =
  bind d (fun a -> ret (f a))
;;

let rec fold (f : char -> 's -> ('s, 'a) fold_state)
                          (s : 's) : 'a deserializer =
  fun r -> let b = getByte r
           in match f b s with
              | Done a -> a
              | More s -> fold f s r
              | Error -> failwith "Fold deserializer error"
;;    
  
(* wire *)

let wire_wrap (s : serializer) : wire =
  let w = Bit_vector.makeWriter () in
  (s w;
   Bit_vector.writerToBytes w)
;;

let deserialize_top (d : 'a deserializer) (w : wire) : 'a option =
  Some (d (Bit_vector.bytesToReader w))
;;
