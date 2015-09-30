Require Import Recdef.
Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import DRBG_working_state.
Require Import HMAC_DRBG_update.
Require Import DRBG_generate_algorithm_result.

Function HMAC_DRBG_generate_helper (HMAC: list Z -> list Z -> list Z) (key v: list Z) (requested_number_of_bytes: Z) {measure Z.to_nat requested_number_of_bytes}: (list Z * list Z) :=
  if Z.geb 0 requested_number_of_bytes then (v, [])
  else
    let v := HMAC key v in
    let temp := v in
    let len := 32%nat in (* TODO get this from property of HMAC *)
    let (v, rest) := HMAC_DRBG_generate_helper HMAC key v (requested_number_of_bytes - (Z.of_nat len)) in
    (v, temp ++ v).
Proof.
  intros. rewrite Z2Nat.inj_sub by omega.
  rewrite Nat2Z.id.
  assert ((0 <? requested_number_of_bytes) = true). admit. (* TODO *)
  apply Zlt_is_lt_bool in H.
  apply Z2Nat.inj_lt in H; omega.
Qed.

Fixpoint leftmost_items {A: Type} (items: list A) (count: Z) :=
  if Z.geb 0 count then []
  else
    match items with
      | [] => []
      | hd::tl => hd::leftmost_items tl (count - 1)
    end.

Definition HMAC_DRBG_generate_algorithm (reseed_interval: Z) (HMAC: list Z -> list Z -> list Z) (working_state: DRBG_working_state) (requested_number_of_bytes: Z) (additional_input: list Z): DRBG_generate_algorithm_result :=
  let '(v, key, reseed_counter) := working_state in
  if Z.gtb reseed_counter reseed_interval then generate_algorithm_reseed_required
  else
    let (key, v) := match additional_input with
                      | [] => (key, v)
                      | _::_ => HMAC_DRBG_update HMAC additional_input key v
                    end in
    let (v, temp) := HMAC_DRBG_generate_helper HMAC key v requested_number_of_bytes in
    let returned_bits := leftmost_items temp requested_number_of_bytes in
    let (key, v) := HMAC_DRBG_update HMAC additional_input key v in
    let reseed_counter := reseed_counter + 1 in
    generate_algorithm_success returned_bits (v, key, reseed_counter).      
