module Pair_Serializer
    (Fst_Serializer : Types.Serializer)
    (Snd_Serializer : Types.Serializer) = struct
  type t = Fst_Serializer.t * Snd_Serializer.t
  let serialize (fst, snd) =
    (Fst_Serializer.serialize fst) @ (Snd_Serializer.serialize snd)
  let deserialize bin =
    match Fst_Serializer.deserialize bin with
    | None -> None
    | Some (fst, rest) ->
    match Snd_Serializer.deserialize rest with
    | None -> None
    | Some (snd, remainder) ->
      Some ((fst, snd), remainder)
end

module Triple_Serializer
    (Fst_Serializer : Types.Serializer)
    (Snd_Serializer : Types.Serializer)
    (Thrd_Serializer : Types.Serializer) = struct
  type t = Fst_Serializer.t * Snd_Serializer.t * Thrd_Serializer.t
  let serialize (fst, snd, thrd) =
    (Fst_Serializer.serialize fst) @ (Snd_Serializer.serialize snd) @ (Thrd_Serializer.serialize thrd)
  let deserialize bin =
    match Fst_Serializer.deserialize bin with
    | None -> None
    | Some (fst, rest) ->
    match Snd_Serializer.deserialize rest with
    | None -> None
    | Some (snd, rest) ->
    match Thrd_Serializer.deserialize rest with
    | None -> None
    | Some (thrd, remainder) ->
      Some ((fst, snd, thrd), remainder)
end

module List_Serializer (Element_Serializer : Types.Serializer) = struct
  type t = Element_Serializer.t list
  let serialize lst =
    let rec loop lst =
      match lst with
      | el :: rest -> (Element_Serializer.serialize el) @ (loop rest)
      | [] -> []
    in
    (Binary.int_to_binary (List.length lst)) @ (loop lst)
  let deserialize bin =
    match BasicSerializers.Int_Serializer.deserialize bin with
    | None -> None
    | Some (count, rest) ->
    let rec loop count bin =
      match count with
      | 0 -> Some ([], bin)
      | n ->
      match Element_Serializer.deserialize bin with
      | None -> None
      | Some (e, rest) ->
      match loop (n - 1) rest with
      | None -> None
      | Some (elements, rest) -> Some ((e :: elements), rest)
    in
    loop count rest
end
