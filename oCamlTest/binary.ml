(* Most of this has equivalents in the standard library, but I need to rewrite
   it because there are no equivalents in the coq standard library. *)

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n ->
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a)

let take c xs =
  let rec loop acc c xs =
    match c with
    | 0 -> Some (List.rev acc, xs)
    | i when i < 0 -> None
    | i ->
      match xs with
      | [] -> None
      | x::xs -> loop (x :: acc) (c - 1) xs
  in
  loop [] c xs

let add_zeroes bin length =
  if (List.length bin) >= length then
    bin
  else
    let rec loop length_left =
      match length_left with
      | 0 -> bin
      | _ -> false :: (loop (length_left - 1))
    in
    loop (length - (List.length bin))

let num_to_binary n =
    let rec loop n =
      match n with
      | 0 -> []
      | _ -> (n mod 2 == 1) :: loop (n / 2)
    in
    List.rev (loop n)

let binary_to_num bin =
    let rec loop bin =
      match bin with
      | [] -> 0
      | hd::bin ->
        (match hd with
        | true -> 1
        | false -> 0) + 2 * (loop bin)
    in
    loop (List.rev bin)

let int_to_binary i =
  add_zeroes (num_to_binary i) 31

let binary_to_int bin =
  match take 31 bin with
  | Some (bin, rest) -> Some (binary_to_num bin, rest)
  | None -> None

let char_to_binary char =
  add_zeroes (num_to_binary (Char.code char)) 8

let binary_to_char bin =
  match take 8 bin with
  | Some (bin, rest) -> Some (Char.chr (binary_to_num bin), rest)
  | None -> None
