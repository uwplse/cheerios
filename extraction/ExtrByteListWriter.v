Require Import Cheerios.Core.

Extract Constant
        ByteListWriter.t => "Serializer_primitives.serializer".
Extract Constant
        ByteListWriter.wire => "Serializer_primitives.wire".

Extract Constant ByteListWriter.putByte => "Serializer_primitives.putByte".
Extract Constant ByteListWriter.empty => "Serializer_primitives.empty".
Extract Constant ByteListWriter.append => "Serializer_primitives.append".
Extract Constant ByteListWriter.wire_wrap => "Serializer_primitives.wire_wrap".
Extract Constant ByteListWriter.wire_eq_dec => "(=)".

Extract Constant ByteListWriter.empty_unwrap => "Obj.magic".
Extract Constant ByteListWriter.putByte_unwrap => "Obj.magic".
Extract Constant ByteListWriter.append_unwrap => "Obj.magic".
Extract Constant ByteListWriter.wire_wrap_unwrap => "Obj.magic".

Extract Constant ByteListWriter.unwrap => "Obj.magic".
Extract Constant ByteListWriter.wire_unwrap => "Obj.magic".
