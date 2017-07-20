Require Import Cheerios.Core.

Extract Constant ByteListReader.t "'a"  => "'a Serializer_primitives.deserializer".

Extract Constant ByteListReader.getByte => "Serializer_primitives.getByte".
Extract Constant ByteListReader.bind => "Serializer_primitives.bind".
Extract Constant ByteListReader.error => "Serializer_primitives.fail".
Extract Constant ByteListReader.map => "Serializer_primitives.map".
Extract Constant ByteListReader.ret => "Serializer_primitives.ret".
Extract Constant ByteListReader.fold => "Serializer_primitives.fold".

Extract Constant ByteListReader.getByte_unwrap => "Obj.magic".
Extract Constant ByteListReader.bind_unwrap => "Obj.magic".
Extract Constant ByteListReader.ret_unwrap => "Obj.magic".
Extract Constant ByteListReader.map_unwrap => "Obj.magic".
Extract Constant ByteListReader.fold_unwrap => "Obj.magic".

Extract Constant ByteListReader.unwrap => "Obj.magic".

Extract Inlined Constant deserialize_top =>
"Serializer_primitives.deserialize_top".
