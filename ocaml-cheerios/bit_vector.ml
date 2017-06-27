(* serialize -> truncate unused bytes, add one byte to indicate how many bitse of the last byte are padding *)
type writer = {mutable bytes : bytes;
               mutable back : int}
type reader = {bytes : bytes;
               mutable front: int;
               capacity: int}
type bit = bool

let byte_length = 8
;;
             
let makeLength n = {bytes = Bytes.init n (fun _ -> Char.chr 0);
                    back = 0}
;;

let makeWriter () =
  let initialLength = 10
  in makeLength initialLength
;;

let pushBack (w : writer) c =
  let length = Bytes.length w.bytes in
  (if w.back >= length
   then let length' = (length * 2) in
        let bytes' = Bytes.init length' (fun _ -> Char.chr 0) in
        let rec copy i =
          if i = length then ()
          else (Bytes.set bytes' i (Bytes.get w.bytes i);
                copy (i + 1))
        in (copy 0; w.bytes <- bytes')
   else ());  
  Bytes.set w.bytes w.back c;
  w.back <- w.back + 1
;;

let makeReader bytes capacity =
  { bytes = bytes;
    front = 0;
    capacity = capacity
  }
;;

let writerToReader (w : writer) =
  makeReader w.bytes w.back;;
  
let pop (r : reader) : char =
  if r.front >= r.capacity
  then failwith "Bit_vector.pop hit capacity"
  else let byte = Bytes.get r.bytes r.front in
       r.front <- r.front + 1;
       byte
;;
  
let dumpReader (r : reader) =
  let rec aux n =
    if n = Bytes.length r.bytes
    then print_string "\n"
    else (Printf.printf "%x " (Char.code (Bytes.get r.bytes n));
          aux (n + 1))
  in aux 0
;;

let rec pushBytes w n =
  if not (n = 0)
  then (pushBack w (Char.chr n);
        pushBytes w (n - 1))
;;
  
let w = makeWriter ();;
let _ = pushBytes w 100;
        dumpReader (writerToReader w);;
  
        
