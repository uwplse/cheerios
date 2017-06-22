type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type positive =
| XI of positive
| XO of positive
| XH

module type SERIALIZER =
 sig
  type t

  val empty : t

  val append : t -> t -> t

  val putBit : bool -> t

  val unwrap : t -> bool list
 end

module Serializer =
 struct
  type t = Serializer_primitives.serializer

  (** val empty : t **)

  let empty = Serializer_primitives.empty

  (** val putBit : bool -> t **)

  let putBit = Serializer_primitives.putBit

  (** val append : t -> t -> t **)

  let append = Serializer_primitives.append

  (** val unwrap : t -> bool list **)

  let unwrap = Obj.magic

  (** val empty_unwrap : __ **)

  let empty_unwrap =
    __

  (** val putBit_unwrap : __ **)

  let putBit_unwrap =
    __

  (** val append_unwrap : __ **)

  let append_unwrap =
    __
 end

module type DESERIALIZER =
 sig
  type 'x t

  val getBit : bool t

  val unwrap : 'a1 t -> bool list -> ('a1 * bool list) option

  val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t

  val ret : 'a1 -> 'a1 t

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val fold : (bool -> 'a1 -> ('a1, 'a2) Serializer_primitives.fold_state) -> 'a1 -> 'a2 t
 end

module Deserializer =
 struct
  type 'a t = 'a Serializer_primitives.deserializer

  (** val unwrap : 'a1 t -> 'a1 t **)

  let unwrap = Obj.magic

  (** val getBit : bool list -> (bool * bool list) option **)

  let getBit = Serializer_primitives.getBit

  (** val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t **)

  let bind = Serializer_primitives.bind

  (** val ret : 'a1 -> 'a1 t **)

  let ret = Serializer_primitives.ret

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f d =
    bind d (fun a -> ret (f a))

  (** val getBit_unwrap : __ **)

  let getBit_unwrap =
    __

  (** val bind_unwrap : __ **)

  let bind_unwrap =
    __

  (** val fold :
      (bool -> 'a1 -> ('a1, 'a2) Serializer_primitives.fold_state) -> 'a1 -> bool list ->
      ('a2 * bool list) option **)

  let rec fold = Serializer_primitives.fold

  (** val ret_unwrap : __ **)

  let ret_unwrap =
    __

  (** val map_unwrap : __ **)

  let map_unwrap =
    __

  (** val fold_unwrap : __ **)

  let fold_unwrap =
    __
 end

type 'a serializer = { serialize : ('a -> Serializer.t); deserialize : 'a Deserializer.t }

(** val serialize : 'a1 serializer -> 'a1 -> Serializer.t **)

let serialize x = x.serialize

(** val bool_Serializer : bool serializer **)

let bool_Serializer =
  { serialize = Serializer.putBit; deserialize = Deserializer.getBit }

(** val serialize_positive : positive -> Serializer.t **)

let rec serialize_positive = function
| XI p0 ->
  Serializer.append (bool_Serializer.serialize true)
    (Serializer.append (bool_Serializer.serialize true) (serialize_positive p0))
| XO p0 ->
  Serializer.append (bool_Serializer.serialize true)
    (Serializer.append (bool_Serializer.serialize false) (serialize_positive p0))
| XH -> bool_Serializer.serialize false

(** val deserialize_positive_step :
    bool -> (bool * (positive -> positive)) -> (bool * (positive -> positive), positive)
    Serializer_primitives.fold_state **)

let deserialize_positive_step b = function
| (is_digit, k) ->
  if is_digit
  then Serializer_primitives.More (false, (fun p -> k (if b then XI p else XO p)))
  else if b
       then Serializer_primitives.More (true, k)
       else Serializer_primitives.Done (k XH)

(** val deserialize_positive : positive Deserializer.t **)

let deserialize_positive =
  Deserializer.fold deserialize_positive_step (false, (fun p -> p))
let rec print_positive p =
  match p with
  | XI p -> Printf.printf "XI "; print_positive p
  | XO p -> Printf.printf "XO "; print_positive p
  | XH -> Printf.printf "XH\n"
;;

let test_positive p = 
  let w = Bit_vector.makeWriter () in
  let _ = serialize_positive p w in
  let r = Bit_vector.writerToReader w in
  let p' = deserialize_positive r in
  let true = p = p' in
  ()
;;

let _ = test_positive XH;
        test_positive (XI XH);
        test_positive (XO XH);
        test_positive (XI (XO (XI (XI XH))));
