Require Import ZArith.

Require Import Cheerios.BasicSerializers.
Require Import Cheerios.Core.
Require Import Cheerios.Types.

Extract Constant
        IOStreamWriter.t => "Iostream_primitives.serializer".
Extract Constant
        IOStreamWriter.wire => "Iostream_primitives.wire".

Extract Constant IOStreamWriter.putByte => "Iostream_primitives.putByte".
Extract Constant IOStreamWriter.empty => "Iostream_primitives.empty".
Extract Constant IOStreamWriter.append => "Iostream_primitives.append".
Extract Constant IOStreamWriter.wire_wrap => "Iostream_primitives.wire_wrap".
Extract Constant IOStreamWriter.wire_eq_dec => "(=)".

Extract Constant IOStreamWriter.empty_unwrap => "Obj.magic".
Extract Constant IOStreamWriter.putByte_unwrap => "Obj.magic".
Extract Constant IOStreamWriter.append_unwrap => "Obj.magic".
Extract Constant IOStreamWriter.wire_wrap_unwrap => "Obj.magic".

Extract Constant IOStreamWriter.unwrap => "Obj.magic".
Extract Constant IOStreamWriter.wire_unwrap => "Obj.magic".
