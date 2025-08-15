module DGL.Protocol.Stateful

open Comparse
open DY.Core
open DY.Lib

open DY.Lib.Label.DynamicGeneralLabel
open DY.Lib.Label.DynamicGeneralLabelEvent

open DGL.Protocol.Total

[@@with_bytes bytes]
type client_init_state = {
  server:principal;
  cmeta_data: comm_meta_data
}

%splice [ps_client_init_state] (gen_parser (`client_init_state))
%splice [ps_client_init_state_is_well_formed] (gen_is_well_formed_lemma (`client_init_state))

[@@with_bytes bytes]
type client_final_state = {
  server:principal;
  cmeta_data: comm_meta_data;
  code:bytes
}

%splice [ps_client_final_state] (gen_parser (`client_final_state))
%splice [ps_client_final_state_is_well_formed] (gen_is_well_formed_lemma (`client_final_state))


[@@with_bytes bytes]
type server_state = {
  client: principal;
  token: bytes;
}

%splice [ps_server_state] (gen_parser (`server_state))
%splice [ps_server_state_is_well_formed] (gen_is_well_formed_lemma (`server_state))

[@@with_bytes bytes]
type protocol_state =
  | ClientSendRequest: client_init_state -> protocol_state
  | ServerReceiveRequest: server_state -> protocol_state
  | ClientReceiveResponse: client_final_state -> protocol_state

%splice [ps_protocol_state] (gen_parser (`protocol_state))
%splice [ps_protocol_state_is_well_formed] (gen_is_well_formed_lemma (`protocol_state))

instance parseable_serializeable_bytes_protocol_state: parseable_serializeable bytes protocol_state
  = mk_parseable_serializeable ps_protocol_state

instance local_state_protocol_state: local_state protocol_state = {
  tag = "Protocol.State";
  format = parseable_serializeable_bytes_protocol_state;
}


(*** Protocol Functions ***)

val client_send_request:
  communication_keys_sess_ids ->
  principal -> principal ->
  traceful (option (state_id & timestamp))
let client_send_request comm_keys_ids client server =
  let payload = Msg1 {client} in
  let*? (msg_id, cmeta_data) = send_request comm_keys_ids client server payload in
  let* sid = new_session_id client in
  set_state client sid (ClientSendRequest { server; cmeta_data } <: protocol_state);*
  return (Some (sid, msg_id))

val server_receive_request_send_response:
  {|crypto_usages|} ->
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option timestamp)
let server_receive_request_send_response #cu comm_keys_ids server msg_id =
  let*? (msg, req_meta_data) = receive_request comm_keys_ids server msg_id in
  guard_tr (Msg1? msg);*?
  let Msg1 req = msg in
  let* sid = new_session_id server in

  // Generate code
  let* tr = get_trace in
  let* i = get_time in

  let* user_code = mk_rand NoUsage (reveal_general_label tr i) 32 in

  // Reveal to shared key
  trigger_reveal_general_event server req_meta_data.key i;*

  set_state server sid (ServerReceiveRequest ({ client=req.client; token=user_code } <: server_state ) <: protocol_state);*
  let*? msg_id = send_response server req_meta_data (Msg2 {server; code=user_code}) in
  return (Some msg_id)

val client_receive_response:
  principal -> state_id -> timestamp ->
  traceful (option unit)
let client_receive_response client sid msg_id =
  let*? cstate = get_state client sid in
  guard_tr (ClientSendRequest? cstate);*?
  let ClientSendRequest { server; cmeta_data } = cstate in
  let*? (msg, _) = receive_response client cmeta_data msg_id in
  guard_tr (Msg2? msg);*?
  let Msg2 res = msg in
  set_state client sid (ClientReceiveResponse { server; cmeta_data; code=res.code } <: protocol_state);*
  return (Some ())
