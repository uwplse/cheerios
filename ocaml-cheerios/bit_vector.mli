type writer
type reader
type bit = bool
             
val makeWriter : unit -> writer
val makeReader : bytes -> int -> reader

val pushBack : writer -> bit -> unit
val pop : reader -> bit

(* for testing *)
val msb : char -> int -> bool

val writerToReader : writer -> reader
val dumpReader : reader -> unit
