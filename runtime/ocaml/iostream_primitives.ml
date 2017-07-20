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

let putInt (i : int32) : serializer =
  let aux n = putByte (Char.chr ((Int32.to_int i lsr n) land 0xff))
  in append (fun () -> (aux 24))
            (fun () -> (append (fun () -> (aux 16))
                               (fun () -> (append (fun () -> (aux 8))
                                                  (fun () -> (aux 0))))))

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
