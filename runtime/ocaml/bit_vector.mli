type writer
type reader
             
exception Out_of_bounds

val makeWriter : unit -> writer

val pushBack : writer -> char -> unit
val pop : reader -> char

val writerToBytes : writer -> bytes
val bytesToReader : bytes -> reader

(* for testing *)
val numBytes : writer -> int
