Require Import ZArith.

Require Import Cheerios.BasicSerializers.
Require Import Cheerios.Core.
Require Import Cheerios.Types.
Require Import Cheerios.IOStream.

Extract Constant
        IOStream.t => "Iostream_primitives.serializer".
Extract Constant
        IOStream.wire => "Iostream_primitives.wire".

Extract Constant IOStream.putByte => "Iostream_primitives.putByte".
Extract Constant IOStream.empty => "Iostream_primitives.empty".
Extract Constant IOStream.append => "Iostream_primitives.append".
Extract Constant IOStream.wire_wrap => "Iostream_primitives.wire_wrap".
Extract Constant IOStream.wire_eq_dec => "(=)".

Extract Constant IOStream.empty_unwrap => "Obj.magic".
Extract Constant IOStream.putByte_unwrap => "Obj.magic".
Extract Constant IOStream.append_unwrap => "Obj.magic".
Extract Constant IOStream.wire_wrap_unwrap => "Obj.magic".

Extract Constant IOStream.unwrap => "Obj.magic".
Extract Constant IOStream.wire_unwrap => "Obj.magic".

Extract Inlined Constant IOStreamSerializer.deserialize_top =>
"Serializer_primitives.deserialize_top".
