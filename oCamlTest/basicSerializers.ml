module Bool_Serializer = struct
  type t = bool
  let serialize b =
    [b]
  let deserialize bin =
    match bin with
    | [] -> None
    | h::t -> Some (h, t)
end

module Int_Serializer = struct
  type t = int
  let serialize i =
    Binary.int_to_binary i
  let deserialize bin =
    Binary.binary_to_int bin
end

module Char_Serializer = struct
  type t = char
  let serialize c =
    Binary.char_to_binary c
  let deserialize bin =
    Binary.binary_to_char bin
end

