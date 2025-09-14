module DGL.Protocol.SecurityProperties

open Comparse
open DY.Core
open DY.Lib

open DGL.Protocol.Total
open DGL.Protocol.Stateful
open DGL.Protocol.Total.Proof
open DGL.Protocol.Stateful.Proof

open DY.Lib.Label.DynamicBytesLabel
open DY.Lib.Label.DynamicBytesLabelEvent

// the problem here is that we don't know anything about the well-formedness of the key we reveal to, therefore the get_label_later lemma is not triggered (and therefore I can't see how we can remove this existential from the property).
val code_secrecy :
  tr:trace ->
  client:principal -> server:principal -> cmeta_data:comm_meta_data ->
  client_id:state_id -> server_id:state_id ->
  code:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    state_was_set tr client client_id (ClientReceiveResponse { server; cmeta_data; code }) /\
    state_was_set tr server server_id (ServerReceiveRequest {client; token=code}) /\
    attacker_knows tr code /\
    Rand? code
  )
  (ensures
    exists prin key tr'.
      tr' <$ tr /\
      reveal_to_bytes_label_event_triggered tr prin key (Rand?.time code) /\
      is_corrupt tr (get_label tr' key)
  )
let code_secrecy tr client server cmeta_data client_id server_id code =
  state_was_set_implies_pred tr state_predicate_protocol server server_id (ServerReceiveRequest {client; token=code});
  assert(
    exists tr'.
      tr' <$ tr /\
      is_secret (reveal_to_bytes_label tr' (Rand?.time code)) tr code
  );
  attacker_only_knows_publishable_values tr code
