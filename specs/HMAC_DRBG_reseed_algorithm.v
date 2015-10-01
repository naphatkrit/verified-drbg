Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import DRBG_working_state.
Require Import HMAC_DRBG_update.

Definition HMAC_DRBG_reseed_algorithm (HMAC: list Z -> list Z -> list Z) (working_state: DRBG_working_state) (entropy_input additional_input: list Z): DRBG_working_state :=
  let '(v, key, _) := working_state in
  let seed_material := entropy_input ++ additional_input in
  let (key, v) := HMAC_DRBG_update HMAC seed_material key v in
  let reseed_counter := 1 in
  (v, key, reseed_counter).