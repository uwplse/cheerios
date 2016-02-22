let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let implode l =
  let res = String.create (List.length l) in
  let rec imp i = function
  | [] -> res
  | c :: l -> res.[i] <- c; imp (i + 1) l in
  imp 0 l

module String_Serializer = struct
  type t = string
  module Char_List_Serializer = Combinators.List_Serializer(BasicSerializers.Char_Serializer)
  let serialize s =
    Char_List_Serializer.serialize (explode s)
  let deserialize bin =
    match Char_List_Serializer.deserialize bin with
    | Some (chars, rest) -> Some ((implode chars), rest)
    | None -> None
end
