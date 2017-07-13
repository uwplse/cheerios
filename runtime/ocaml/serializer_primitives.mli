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
val append : serializer -> serializer -> serializer

  (* deserializer *)
val getByte : char deserializer
val getInt : int32 deserializer
val bind : 'a deserializer -> ('a -> 'b deserializer) -> 'b deserializer
val ret : 'a -> 'a deserializer
val fail : 'a deserializer
val map : ('a -> 'b) -> 'a deserializer -> 'b deserializer
val fold : (char -> 's -> ('s, 'a) fold_state) -> 's -> 'a deserializer
  
(* wire *)
val wire_wrap : serializer -> wire
val size : wire -> int
val deserialize_top : 'a deserializer -> wire -> 'a option
