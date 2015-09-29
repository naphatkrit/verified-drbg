Require Import Recdef.
Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import DRBG_working_state.
Require Import HMAC_DRBG_update.

Inductive DRBG_generate_result :=
| generate_result_reseed_required: DRBG_generate_result
| generate_result_success: list Z -> DRBG_working_state -> DRBG_generate_result.

Function HMAC_DRBG_generate_helper (HMAC: list Z -> list Z -> list Z) (key v: list Z) (requested_number_of_bits: Z) {measure Z.to_nat requested_number_of_bits}: (list Z * list Z) :=
  if Z.geb 0 requested_number_of_bits then (v, [])
  else
    let v := HMAC key v in
    let temp := v in
    let len := 32%nat in (* TODO get this from property of HMAC *)
    let (v, rest) := HMAC_DRBG_generate_helper HMAC key v (requested_number_of_bits - (Z.of_nat len)) in
    (v, temp ++ v).
Proof.
  intros. rewrite Z2Nat.inj_sub by omega.
  rewrite Nat2Z.id.
  assert ((0 <? requested_number_of_bits) = true). admit. (* TODO *)
  apply Zlt_is_lt_bool in H.
  apply Z2Nat.inj_lt in H; omega.
Qed.

Definition HMAC_DRBG_generate_algorithm (reseed_interval: Z) (HMAC: list Z -> list Z -> list Z) (working_state: DRBG_working_state) (requested_number_of_bits: Z) (additional_input: list Z): DRBG_generate_result :=
  let '(v, key, reseed_counter) := working_state in
  let (key, v) := match additional_input with
                    | [] => (key, v)
                    | _::_ => HMAC_DRBG_update HMAC additional_input key v
                  end in
  let (v, temp) := HMAC_DRBG_generate_helper HMAC key v requested_number_of_bits in
  (* TODO get leftmost x number of bits *)
  let returned_bits := temp in
  let (key, v) := HMAC_DRBG_update HMAC additional_input key v in
  let reseed_counter := reseed_counter + 1 in
  generate_result_success returned_bits (v, key, reseed_counter).
      