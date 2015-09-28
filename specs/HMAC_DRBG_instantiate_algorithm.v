Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import HMAC_DRBG_update.
Require Import DRBG_working_state.

Fixpoint list_of_length (length: nat) (value: list Z): (list Z) :=
  match length with
    | O => []
    | S n => value ++ list_of_length n value
  end.

Definition initial_key: list Z := list_of_length 16 [0;0].

Definition initial_value: list Z := list_of_length 16 [0;1].

Definition HMAC_DRBG_instantiate_algorithm (HMAC: list Z -> list Z -> list Z) (entropy_input nonce personalization_string: list Z): DRBG_working_state :=
  let seed_material := entropy_input ++ nonce ++ personalization_string in
  let key := initial_key in
  let value := initial_value in
  let (key, value) := HMAC_DRBG_update HMAC seed_material key value in
  let reseed_counter := 1 in
  (value, key, reseed_counter).