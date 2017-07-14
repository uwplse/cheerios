Require Import List.

Require Import Cheerios.DeserializerMonad.
Require Import Cheerios.IOStream.
Require Import Cheerios.Types.

Ltac cheerios_crush := intros; autorewrite with cheerios; auto.

Module WriterRewrite (Writer : WRITER).
  Hint Rewrite app_ass 
       Writer.empty_unwrap Writer.putByte_unwrap
       Writer.append_unwrap : cheerios.
End WriterRewrite.

Module ReaderRewrite (Reader : READER).
  Hint Rewrite Reader.getByte_unwrap Reader.bind_unwrap Reader.ret_unwrap
       Reader.map_unwrap @Reader.fold_unwrap : cheerios.
End ReaderRewrite.
