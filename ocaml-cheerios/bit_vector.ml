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
  let initialLength = 100
  in makeLength initialLength
;;


(* layer: indexed bits on top of indexed bytes *)

(* takes index i
   returns (j, o) such that the i'th bit is the o'th bit of the j'th byte *)
let getBitIndex i = (i / byte_length, i mod byte_length)
;;

  (* gives ith most significant bit (0th most significant being the leftmost)
     in c 
     assumes 0 <= i < byte_length *)
let msb c i =
  let shifted = (Char.code c) lsr (byte_length - i - 1) in
  match shifted land 1 with
  | 0 -> false
  | 1 -> true
  | _ -> raise (Invalid_argument "byte outside of 0-255 range")
;;

let setMsb c i bit =
  Char.chr ((Char.code c) lor
               ((if bit then 1 else 0) lsl (byte_length - i - 1)))
           
                        
(* raises Invalid_argument *)                        
let getBit bytes i =
  let (j, o) = getBitIndex i in
  msb (Bytes.get bytes j) o
;;

let pushBack v bit =
  let (j, o) = getBitIndex v.back in
  let length = Bytes.length v.bytes in
  (if v.back >= length * byte_length
   then let length' = (length * 2) in
        let bytes' = Bytes.init length' (fun _ -> Char.chr 0) in
        let rec copy i =
          if i = length then ()
          else (Bytes.set bytes' i (Bytes.get v.bytes i);
                copy (i + 1))
        in (copy 0; v.bytes <- bytes')
   else ());  
               let c = setMsb (Bytes.get v.bytes j) o bit in
  Bytes.set v.bytes j c;
  v.back <- v.back + 1
;;

let makeReader bytes capacity =
  { bytes = bytes;
    front = 0;
    capacity = capacity
  }
;;

let writerToReader (w : writer) =
  makeReader w.bytes w.back;;
  
let pop (r : reader) : bool =
  if r.front >= r.capacity
  then failwith "Bit_vector.pop hit capacity"
  else let bit = getBit r.bytes r.front in
       r.front <- r.front + 1;
       bit
;;
  
let dumpReader (r : reader) =
  let rec aux n =
    if n = Bytes.length r.bytes
    then print_string "\n"
    else (Printf.printf "%x " (Char.code (Bytes.get r.bytes n));
          aux (n + 1))
  in aux 0

(* internal tests *)
let test_char1 = 'a';; (* 0110 0001 *)
let [false; true; true; false;    false; false; false; true] =
  [msb test_char1 0; msb test_char1 1; msb test_char1 2; msb test_char1 3;
   msb test_char1 4; msb test_char1 5; msb test_char1 6; msb test_char1 7]

let (0, 0) = getBitIndex 0;;
let (0, 1) = getBitIndex 1;;
let (1, 0) = getBitIndex 8;;
let (12, 6) = getBitIndex 102;;
let (14, 7) = getBitIndex 119;;
                         
