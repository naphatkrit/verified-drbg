Require Import Recdef.
Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import DRBG_working_state.
Require Import HMAC_DRBG_update.
Require Import DRBG_generate_algorithm_result.

Function HMAC_DRBG_generate_helper (HMAC: list Z -> list Z -> list Z) (key v: list Z) (requested_number_of_bytes: nat) {measure (fun x => x) requested_number_of_bytes}: (list Z * list Z) :=
  match requested_number_of_bytes with
    | O => (v, [])
    | _ => 
    let len := 32%nat in (* TODO get this from property of HMAC *)
    let (v, rest) := HMAC_DRBG_generate_helper HMAC key v (requested_number_of_bytes - 32)%nat in
    let v := HMAC v key in
    let temp := v in
    (v, rest ++ temp)
  end. 
Proof.
  intros.
  omega.
Defined.

Function HMAC_DRBG_generate_helper_Z (HMAC: list Z -> list Z -> list Z) (key v: list Z) (requested_number_of_bytes: Z) {measure Z.to_nat requested_number_of_bytes}: (list Z * list Z) :=
  if Z.geb 0 requested_number_of_bytes then (v, [])
  else
    let len := 32%nat in (* TODO get this from property of HMAC *)
    let (v, rest) := HMAC_DRBG_generate_helper_Z HMAC key v (requested_number_of_bytes - (Z.of_nat len)) in
    let v := HMAC v key in
    let temp := v in
    (v, rest ++ temp). 
Proof.
  intros. rewrite Z2Nat.inj_sub by omega.
  rewrite Nat2Z.id.
  assert ((0 <? requested_number_of_bytes) = true).
  * 
    rewrite Z.ltb_antisym.
    rewrite <- Z.geb_leb.
    rewrite teq.
    auto.
  *
  apply Zlt_is_lt_bool in H.
  apply Z2Nat.inj_lt in H; omega.
Defined.

Fixpoint HMAC_DRBG_generate_helper_rounds (HMAC: list Z -> list Z -> list Z) (key v: list Z) (rounds: nat): (list Z * list Z) :=
  match rounds with
    | O => (v, [])
    | S rounds' => 
    let (v, rest) := HMAC_DRBG_generate_helper_rounds HMAC key v rounds' in
    let v := HMAC v key in
    let temp := v in
    (v, rest ++ temp)
  end.

Fixpoint HMAC_v_n_times (HMAC: list Z -> list Z -> list Z) key v n :=
  match n with
    | O => v
    | S n' =>
      let v' := HMAC_v_n_times HMAC key v n' in
      HMAC v' key
  end
.

Lemma HMAC_DRBG_generate_helper_rounds_v:
  forall HMAC key v v' n b,
    (v', b) = HMAC_DRBG_generate_helper_rounds HMAC key v n ->
    v' = HMAC_v_n_times HMAC key v n.
Proof.
  intros until n.
  revert HMAC key v v'.
  induction n as [|n']; intros. simpl in H. inv H. reflexivity.
  simpl in H.
  simpl.
  remember (HMAC_DRBG_generate_helper_rounds HMAC key v n') as x; destruct x.
  apply IHn' in Heqx.
  subst.
  inv H.
  reflexivity.
Qed.

Definition HMAC_DRBG_generate_algorithm (HMAC: list Z -> list Z -> list Z) (reseed_interval: Z) (working_state: DRBG_working_state) (requested_number_of_bytes: Z) (additional_input: list Z): DRBG_generate_algorithm_result :=
  let '(v, key, reseed_counter) := working_state in
  if Z.gtb reseed_counter reseed_interval then generate_algorithm_reseed_required
  else
    let (key, v) := match additional_input with
                      | [] => (key, v)
                      | _::_ => HMAC_DRBG_update HMAC additional_input key v
                    end in
    let (v, temp) := HMAC_DRBG_generate_helper_Z HMAC key v requested_number_of_bytes in
    let returned_bits := firstn (Z.to_nat requested_number_of_bytes) temp in
    let (key, v) := HMAC_DRBG_update HMAC additional_input key v in
    let reseed_counter := reseed_counter + 1 in
    generate_algorithm_success returned_bits (v, key, reseed_counter).      
