type writer
type reader
             
val makeWriter : unit -> writer
val makeReader : bytes -> int -> reader

val pushBack : writer -> char -> unit
val pop : reader -> char

(* for testing *)
val writerToReader : writer -> reader
val dumpReader : reader -> unit
