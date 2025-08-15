module DGL.Protocol.Total

open Comparse
open DY.Core
open DY.Lib

type message1 = {
  client: principal;
}

%splice [ps_message1] (gen_parser (`message1))
%splice [ps_message1_is_well_formed] (gen_is_well_formed_lemma (`message1))

[@@ with_bytes bytes]
type message2 = {
  server : principal;
  code : bytes;
}

%splice [ps_message2] (gen_parser (`message2))
%splice [ps_message2_is_well_formed] (gen_is_well_formed_lemma (`message2))

[@@ with_bytes bytes]
type message =
  | Msg1 : message1 -> message
  | Msg2 : message2 -> message

%splice [ps_message] (gen_parser (`message))
%splice [ps_message_is_well_formed] (gen_is_well_formed_lemma (`message))

instance parseable_serializeable_bytes_message : parseable_serializeable bytes message =
  mk_parseable_serializeable ps_message

(*** Message 1***)

/////  User requests some code from a server
// val compute_message1 : principal -> principal -> bytes
// let compute_message1 client server =
//   let msg = Msg1 {server} in
//   serialize message msg

// val decode_message1 : principal -> bytes -> option message1
// let decode_message1 server msg1_msg =
//   let?
