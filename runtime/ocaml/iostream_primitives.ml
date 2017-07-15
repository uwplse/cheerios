type iostream = 
    | Done
    | WriteByte of char 
    | Seq of (unit -> iostream) * (unit -> iostream)
type wire = bytes

type serializer = iostream

let empty : serializer = Done

let putByte (b : char) : serializer =
  WriteByte b

let append (s1 : unit -> serializer) (s2 : unit -> serializer) : serializer =
  Seq (s1, s2)

(*
let rec positive_serialize p =
  match p with
  | XI p -> append (fun () -> (byte_Serializer.serialize '\002'))
                   (fun () -> positive_serialize p)
  | XO p -> append (fun () -> (byte_Serializer.serialize '\001'))
                   (fun () -> positive_serialize p)
  | xH -> putByte '\000'
 *)
      
(* wire *)
let rec iostream_interp (s : serializer) (w : Bit_vector.writer) =
  match s with
  | Done -> ()
  | WriteByte b -> Bit_vector.pushBack w b
  | Seq (t1, t2) -> (iostream_interp (t1 ()) w;
                   iostream_interp (t2 ()) w)
                    
let wire_wrap (s : serializer) : wire =
  let w = Bit_vector.makeWriter () in
  (iostream_interp s w;
   Bit_vector.writerToBytes w)
