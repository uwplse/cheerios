module type Serializer = sig
  type t
  val serialize: t -> bool list
  val deserialize: bool list -> (t * bool list) option
end
