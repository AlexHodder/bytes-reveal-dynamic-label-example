module DGL.Protocol.Stateful.Proof

open Comparse
open DY.Core
open DY.Lib

open DGL.Protocol.Total
open DGL.Protocol.Stateful
open DGL.Protocol.Total.Proof

open DY.Lib.Label.DynamicGeneralLabel
open DY.Lib.Label.DynamicGeneralLabelEvent

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

#push-options "--ifuel 3 --fuel 3 --z3rlimit 20"
let state_predicate_protocol: local_state_predicate protocol_state = {
  pred = (fun tr prin sess_id st ->
    match st with
    | ClientSendRequest {server; cmeta_data} -> (
      let client = prin in
      comm_meta_data_knowable tr client cmeta_data
    )
    | ServerReceiveRequest {client; token} -> (
      let server = prin in
      Rand? token /\
      (exists tr'.
        tr' <$ tr /\
        is_secret (reveal_general_label tr' (Rand?.time token)) tr token
      ) /\
      is_knowable_by (principal_label server) tr token
    )
    | ClientReceiveResponse {server; cmeta_data; code} -> (
      let client = prin in
      comm_meta_data_knowable tr client cmeta_data /\
      is_knowable_by (join (principal_label client) (principal_label server)) tr code
    )
  );
  pred_later = (fun tr1 tr2 prin sess_id st -> (
    match st with
    | ClientSendRequest {server; cmeta_data} -> (
      ()
    )
    | ServerReceiveRequest {client; token} -> (
      ()
    )
    | ClientReceiveResponse {server; cmeta_data; code} -> (
      ()
    )
  ));
  pred_knowable = (fun tr prin sess_id st -> ());
}
#pop-options

val protocol_state_tag: string
let protocol_state_tag = "Protocol.State"

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  state_predicates_communication_layer_and_tag;
  (|protocol_state_tag, local_state_predicate_to_local_bytes_state_predicate state_predicate_protocol|);
]

(*** Event Predicates ***)

#push-options "--ifuel 2"
val comm_layer_event_preds: comm_reqres_higher_layer_event_preds message
let comm_layer_event_preds = {
  default_comm_reqres_higher_layer_event_preds message with
  send_request = (fun tr client server (payload:message) key_label ->
    match payload with
    | Msg1 {client=client'} -> client' = client
    | Msg2 {server=server'; code} -> (
      server = server' /\
      Rand? code /\
      (exists tr'.
        tr' <$ tr /\
        is_secret (reveal_general_label tr' (Rand?.time code)) tr code
      )
    )
  );
  send_request_later = (fun tr1 tr2 client server payload key_label -> ())
}
#pop-options

let reveal_event_pred : reveal_general_event_predicate =
  default_reveal_event_predicate #crypto_invariants_protocol

let all_events =
  (mk_event_tag_and_pred reveal_event_pred) ::
  (event_predicate_communication_layer_reqres_and_tag comm_layer_event_preds)


(*** Combine all Invariants ***)

/// Create the global trace invariants.

let trace_invariants_protocol: trace_invariants = {
  state_pred = mk_state_pred all_sessions;
  event_pred = mk_event_pred all_events;
}

instance protocol_invariants_protocol: protocol_invariants = {
  crypto_invs = crypto_invariants_protocol;
  trace_invs = trace_invariants_protocol;
}

/// Lemmas that the global predicates contain all the local ones

val all_sessions_has_all_sessions: unit -> Lemma (norm [delta_only [`%all_sessions; `%List.Tot.for_allP]; iota; zeta] (List.Tot.for_allP has_local_bytes_state_predicate all_sessions))
let all_sessions_has_all_sessions () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map dfst (all_sessions)));
  mk_state_pred_correct all_sessions;
  norm_spec [delta_only [`%all_sessions; `%List.Tot.for_allP]; iota; zeta] (List.Tot.for_allP has_local_bytes_state_predicate all_sessions)

val protocol_invariants_protocol_has_communication_layer_state_invariant: squash (has_local_state_predicate state_predicates_communication_layer)
let protocol_invariants_protocol_has_communication_layer_state_invariant = all_sessions_has_all_sessions ()


let _ = do_split_boilerplate mk_state_pred_correct all_sessions
#push-options "--ifuel 2 --fuel 2"
let _ = do_split_boilerplate mk_event_pred_correct all_events
#pop-options

open FStar.List.Tot

val all_events_has_all_events: unit -> Lemma (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP has_compiled_event_pred all_events))
let all_events_has_all_events () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_events)));
  mk_event_pred_correct all_events;
  norm_spec [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP has_compiled_event_pred all_events);
  let dumb_lemma (x:prop) (y:prop): Lemma (requires x /\ x == y) (ensures y) = () in
  dumb_lemma (for_allP has_compiled_event_pred all_events) (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP has_compiled_event_pred all_events))

val protocol_invariants_has_communication_layer_event_invariants: squash (has_event_pred (event_predicate_communication_layer request_response_event_preconditions))
let protocol_invariants_has_communication_layer_event_invariants = all_events_has_all_events ()


#push-options "--fuel 1"
val protocol_invariants_protocol_communication_layer_reqres_event_invariant: squash (has_event_pred (event_predicate_communication_layer_reqres comm_layer_event_preds))
let protocol_invariants_protocol_communication_layer_reqres_event_invariant = all_events_has_all_events ()
#pop-options

(*** Proofs ***)

#push-options "--z3rlimit 10"
val client_send_request_proof :
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  client:principal -> server:principal ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = client_send_request comm_keys_ids client server tr in
    trace_invariant tr_out
  ))
let client_send_request_proof tr comm_keys_ids client server =
  let payload = Msg1 {client} in
  send_request_proof tr comm_keys_ids comm_layer_event_preds client server payload;
  match send_request comm_keys_ids client server payload tr with
  | Some (msg, req_metadata), tr_out ->
    let (sid , tr_out) = new_session_id client tr_out in
    let st : protocol_state = ClientSendRequest { server; cmeta_data=req_metadata } in
    set_state_invariant state_predicate_protocol client sid st tr_out
  | _ -> ()
#pop-options

// %splice [ps_bytes] (gen_parser (`bytes))
// %splice [ps_bytes_is_well_formed] (gen_is_well_formed_lemma (`bytes))

instance parseable_serializeable_bytes_bytes : parseable_serializeable bytes bytes =
  mk_parseable_serializeable ps_bytes

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
val server_receive_request_send_response_proof :
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  server:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = server_receive_request_send_response comm_keys_ids server msg_id tr in
    trace_invariant tr_out
  ))
let server_receive_request_send_response_proof tr comm_keys_ids server msg_id =
  receive_request_proof tr comm_keys_ids comm_layer_event_preds server msg_id;
  match receive_request comm_keys_ids server msg_id tr with
  | Some (msg, comm_metadata), tr2 -> (
    assert(trace_invariant tr2);
    match guard_tr (Msg1? msg) tr2 with
    | Some (), tr3 -> (

      let e = CommServerReceiveRequest server (serialize message msg) comm_metadata.key in

      // assert(event_triggered tr3 server e);
      // assert(exists tr_pre. tr_pre <$ tr3 ==> is_knowable_by (get_label tr_pre comm_metadata.key) tr_pre (serialize message msg));

      // assert(exists tr_pre. tr_pre <$ tr3 ==> is_knowable_by (principal_label server) tr_pre comm_metadata.key);
      // assert(is_knowable_by (principal_label server) tr3 comm_metadata.key);


      let Msg1 req = msg in

      let sid, tr_out = new_session_id server tr3 in
      let tr_out_witness, tr_out' = get_trace tr_out in
      // assert(trace_invariant tr_out);
      let i, tr_out = get_time tr_out in


      reveal_opaque (`%mk_rand) (mk_rand);
      let user_code, tr_out = mk_rand NoUsage (reveal_general_label tr_out_witness i) 32 tr_out in
      // assert(trace_invariant tr_out);

      mk_rand_rand_gen_at_end NoUsage (reveal_general_label tr_out_witness i) 32 tr_out_witness;

      // assert(get_label tr_out comm_metadata.key `can_flow tr_out` principal_label server);

      // assert(rand_generated_at tr_out i user_code);
      // admit();
      // assert(default_reveal_event_predicate #crypto_invariants_protocol tr_out server {new_label=comm_metadata.key; point=i;});

      trigger_event_trace_invariant reveal_event_pred server {new_label=comm_metadata.key; point=i;} tr_out;
      trigger_event_event_triggered server {new_label=comm_metadata.key; point=i;} tr_out;
      reveal_opaque (`%trigger_reveal_general_event) (trigger_reveal_general_event);
      reveal_opaque (`%reveal_general_event_triggered_at) (reveal_general_event_triggered_at);

      let _, tr_out = trigger_reveal_general_event server comm_metadata.key i tr_out in
      // assert(event_triggered tr_out server {new_label=comm_metadata.key; point=i});
      // assert(reveal_general_event_triggered tr_out server comm_metadata.key i);

      // admit();

      // assert(reveal_general_event_triggered tr_out server comm_metadata.key i);
      reveal_general_label_can_flow_to_general_label tr_out tr_out_witness server comm_metadata.key i;

      // assert(reveal_general_label tr_out_witness i `can_flow tr_out` (get_label tr_out comm_metadata.key));


      // assert(is_knowable_by (principal_label server) tr_out comm_metadata.key);
      // assert(get_label tr_out comm_metadata.key `can_flow tr_out` principal_label server);

      // assert(is_secret (reveal_general_label tr_out_witness i) tr_out user_code);



      // assert(exists tr'.
      //   tr' <$ tr_out /\
      //   is_secret (reveal_general_label tr' (Rand?.time user_code)) tr_out user_code
      // );
      // assert(is_knowable_by (get_label tr_out comm_metadata.key) tr_out user_code);
      // assert(is_knowable_by (principal_label server) tr_out user_code);

      let st : protocol_state = ServerReceiveRequest {client=req.client; token=user_code} in

      // assert(state_predicate_protocol.pred tr_out server sid st);

      set_state_invariant state_predicate_protocol server sid st tr_out;
      let (), tr_out = set_state server sid st tr_out in
      // assert(trace_invariant tr_out);

      let response : message = Msg2 {server; code=user_code} in

      assert(get_response_label tr_out comm_metadata == get_label tr_out comm_metadata.key);
      assert(is_knowable_by (get_response_label tr_out comm_metadata) tr_out user_code);

      let pre' = is_knowable_by (get_response_label tr_out comm_metadata) tr_out in


      // assume(is_well_formed_prefix ps_bytes pre' user_code);
      // assume(is_well_formed_prefix ps_principal pre' server);
      // admit();

      // ps_message2_is_well_formed pre' {server; code=user_code};
      // assert(is_well_formed_prefix ps_message2 pre' {server; code=user_code});

      // ps_message_is_well_formed pre' response;
      // assert(is_well_formed_prefix ps_message pre' response);

      // assume(is_knowable_by (get_response_label tr_out comm_metadata) tr_out (serialize _ response));

      assume(is_well_formed message pre' response);

      send_response_proof tr_out comm_layer_event_preds server comm_metadata response;


      match send_response server comm_metadata response tr_out with
      | Some msg_id, tr_out_final ->
        assert(trace_invariant tr_out_final)
      | _, _ -> ()
    )
    | _ -> ()
  )
  | _ -> ()
#pop-options
