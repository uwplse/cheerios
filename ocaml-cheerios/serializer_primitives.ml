type serializer = Bit_vector.writer -> unit
type 'a deserializer = Bit_vector.reader -> 'a

let empty = fun w -> ()
;;

let putBit b : serializer =
  fun w -> Bit_vector.pushBack w b  
;;

let empty : serializer =
  fun w -> ()
;;

let append m1 m2 : serializer =
  fun w ->
  m1 w;
  m2 w
;;  

(* I think we can avoid capturing failure with an option because failure's
   verified not to happen *)

(* bound check, and either throw an exception or return none 

   since our spec says things always deserialize to a Some, we might as well
   not return an option here and just throw an exception when we run into this
   sort of situation *)

let getBit : bool deserializer =
  Bit_vector.pop
;;

(* bind : 'a deserializer -> ('a -> 'b deserializer) -> 'b deserializer *)
let bind (d : 'a deserializer) (f : 'a -> 'b deserializer) : 'b deserializer =
  fun r -> let v = d r in
           (f v) r
;;  
                 
let ret (v : 'a) : 'a deserializer =
  fun r -> v
;;

type ('s, 'a) fold_state =
  | Done of 'a
  | More of 's
  | Error
;;

let rec fold_deserializer (f : bool -> 's -> ('s, 'a) fold_state)
                          (s : 's) : 'a deserializer =
  fun r -> let b = getBit r
           in match f b s with
              | Done a -> a
              | More s -> fold_deserializer f s r
              | Error -> failwith "Fold deserializer error"
;;    
  
(* tests *)

let putByte c w =
  let byte_length = 8 in
  let rec aux i =
    if i = byte_length
    then ()
    else (putBit (Bit_vector.msb c i) w;
          aux (i + 1))
  in aux 0
;;

let rec putBytes n w =
  if n = 0
  then ()
  else (putByte (Char.chr n) w;
        putBytes (n - 1) w)
;;
         
        
    
let testWriter : Bit_vector.writer = Bit_vector.makeWriter ();;
let () = putBytes 0xff testWriter;;
let testReader = Bit_vector.writerToReader testWriter;;
let _ = Bit_vector.dumpReader testReader;;
