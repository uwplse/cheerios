type serializer = Bit_vector.writer -> unit
type 'a deserializer = Bit_vector.reader -> 'a

let empty = fun w -> ()
;;

let putByte b : serializer =
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

let getByte : char deserializer =
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
  
