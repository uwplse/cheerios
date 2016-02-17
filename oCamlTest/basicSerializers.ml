

module Int32_Serializer : Types.Serializer = struct
  type t = int32
  let serialize i =
    Binary.int32_to_binary i
  let deserialize bytes =
    binary_to_int32 bytes
end
