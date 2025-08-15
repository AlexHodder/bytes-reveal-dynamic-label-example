module DGL.Protocol.Total.Proof

open Comparse
open DY.Core
open DY.Lib

open DGL.Protocol.Total
open DGL.Protocol.Stateful

open FStar.List.Tot

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

val crypto_usages_protocol : crypto_usages
instance crypto_usages_protocol = default_crypto_usages

val pke_pred_list_protocol : list (string & pke_crypto_predicate)
let pke_pred_list_protocol = [ pke_crypto_predicates_communication_layer_and_tag ]

val sign_pred_list_protocol : list (string & sign_crypto_predicate)
let sign_pred_list_protocol = [ sign_crypto_predicates_communication_layer_and_tag ]

val aead_pred_list_protocol : list (string & aead_crypto_predicate)
let aead_pred_list_protocol = [ aead_crypto_predicates_communication_layer_and_tag ]

val crypto_predicates_protocol : crypto_predicates
let crypto_predicates_protocol = {
  default_crypto_predicates with

    pke_pred = mk_pke_predicate pke_pred_list_protocol;

    sign_pred = mk_sign_predicate sign_pred_list_protocol;

    aead_pred = mk_aead_predicate aead_pred_list_protocol;

}

instance crypto_invariants_protocol: crypto_invariants = {
  usages = crypto_usages_protocol;
  preds = crypto_predicates_protocol;
}

#push-options "--ifuel 0 --fuel 1"
val pke_pred_has_all_pke_preds:
  unit ->
  Lemma
  (ensures
    norm [delta_only [`%pke_pred_list_protocol; `%for_allP]; iota; zeta] (
      for_allP has_pke_predicate pke_pred_list_protocol
    )
  )
let pke_pred_has_all_pke_preds () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (pke_pred_list_protocol)));
  mk_pke_predicate_correct pke_pred_list_protocol;
  norm_spec [delta_only [`%pke_pred_list_protocol; `%for_allP]; iota; zeta] (for_allP has_pke_predicate pke_pred_list_protocol);
  ()

val sign_pred_has_all_sign_preds:
  unit ->
  Lemma
  (ensures
    norm [delta_only [`%sign_pred_list_protocol; `%for_allP]; iota; zeta] (
      for_allP has_sign_predicate sign_pred_list_protocol
    )
  )
let sign_pred_has_all_sign_preds () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (sign_pred_list_protocol)));
  mk_sign_predicate_correct sign_pred_list_protocol;
  norm_spec [delta_only [`%sign_pred_list_protocol; `%for_allP]; iota; zeta] (for_allP has_sign_predicate sign_pred_list_protocol);
  ()

val aead_pred_has_all_aead_preds:
  unit ->
  Lemma
  (ensures
    norm [delta_only [`%aead_pred_list_protocol; `%for_allP]; iota; zeta] (
      for_allP has_aead_predicate aead_pred_list_protocol
    )
  )
let aead_pred_has_all_aead_preds () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (aead_pred_list_protocol)));
  mk_aead_predicate_correct aead_pred_list_protocol;
  norm_spec [delta_only [`%aead_pred_list_protocol; `%for_allP]; iota; zeta] (for_allP has_aead_predicate aead_pred_list_protocol);
  ()
#pop-options

val protocol_crypto_invariants_has_communication_layer_crypto_predicates: squash has_communication_layer_reqres_crypto_predicates
let protocol_crypto_invariants_has_communication_layer_crypto_predicates =
  pke_pred_has_all_pke_preds ();
  sign_pred_has_all_sign_preds ();
  aead_pred_has_all_aead_preds ()
