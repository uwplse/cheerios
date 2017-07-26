type serializer
type 'a deserializer
type wire = bytes

type ('s, 'a) fold_state =
  | Done of 'a
  | More of 's
  | Error

(* serializer *)
val empty : serializer
val putByte : char -> serializer
val putInt : int32 -> serializer
val putChars : char list -> serializer
val append : (unit -> serializer) -> (unit -> serializer) -> serializer

  
  (* deserializer *)
val getByte : char deserializer
val getInt : int32 deserializer
val bind : 'a deserializer -> ('a -> 'b deserializer) -> 'b deserializer
val ret : 'a -> 'a deserializer
val fail : 'a deserializer
val map : ('a -> 'b) -> 'a deserializer -> 'b deserializer
val fold : (char -> 's -> ('s, 'a) fold_state) -> 's -> 'a deserializer
val getChars : int -> (char list) deserializer
(* wire *)
val wire_wrap : serializer -> wire
val size : wire -> int
val dump : wire -> unit
val deserialize_top : 'b -> 'a deserializer -> wire -> 'a option
