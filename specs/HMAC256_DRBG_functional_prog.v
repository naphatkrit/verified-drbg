Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import functional_prog.
Require Import HMAC256_functional_prog.
Require Import DRBG_state_handle.
Require Import DRBG_instantiate_function.
Require Import HMAC_DRBG_instantiate_algorithm.
Require Import DRBG_generate_function.
Require Import HMAC_DRBG_generate_algorithm.

Definition HMAC256_DRBG_instantiate_algorithm := HMAC_DRBG_instantiate_algorithm HMAC256.

Definition HMAC256_DRBG_instantiate_function := DRBG_instantiate_function HMAC256_DRBG_instantiate_algorithm.

Definition get_entropy_input_dummy (result: string) (x y z: Z) (b: bool): entropy_result := entropy_success (hexstring_to_Zlist result).

Definition get_nonce_dummy (result: string) (_: unit) := hexstring_to_Zlist result.

Definition test_HMAC256_DRBG_instantiate_function := HMAC256_DRBG_instantiate_function (get_entropy_input_dummy "ca851911349384bffe89de1cbdc46e6831e44d34a4fb935ee285dd14b71a7488") 0 0 (get_nonce_dummy "659ba96c601dc69fc902940805ec0ca8") 256 0 false.

Definition DRBG_instantiate_check (key value: string) :=
  let key := hexstring_to_Zlist key in
  let value := hexstring_to_Zlist value in
  match test_HMAC256_DRBG_instantiate_function 256 false [] with
    | instantiate_success ((value', key', _), _, _) => listZ_eq value value' = true /\ listZ_eq key key' = true
    | _ => False
  end.

Lemma test1: DRBG_instantiate_check "302a4aba78412ab36940f4be7b940a0c728542b8b81d95b801a57b3797f9dd6e" "e75855f93b971ac468d200992e211960202d53cf08852ef86772d6490bfb53f9".
  vm_compute. auto. Qed.

Definition HMAC256_DRBG_generate_algorithm := HMAC_DRBG_generate_algorithm HMAC256 1024.

Definition HMAC256_DRBG_generate_function := DRBG_generate_function HMAC256_DRBG_generate_algorithm.

Definition test_HMAC256_DRBG_generate_function := HMAC256_DRBG_generate_function 128 0.

Fixpoint DRBG_generate_check (state_handle: DRBG_state_handle) (internal_states: list (string * string)) (returned_bits: string) :=
  match internal_states with
    | [] => True
    | (key, v)::[] =>
      let key := hexstring_to_Zlist key in
      let value := hexstring_to_Zlist v in
      let returned_bits := hexstring_to_Zlist returned_bits in
      match test_HMAC256_DRBG_generate_function state_handle 128 256 false [] with
        | generate_success returned_bits' ((value', key', _), _, _) => listZ_eq value value' = true /\ listZ_eq key key' = true /\ listZ_eq returned_bits returned_bits' = true
        | generate_error => False
      end
    | (key, v)::tl =>
      let key := hexstring_to_Zlist key in
      let value := hexstring_to_Zlist v in
      match test_HMAC256_DRBG_generate_function state_handle 128 256 false [] with
        | generate_success _ ((value', key', x), y, z) => listZ_eq value value' = true /\ listZ_eq key key' = true /\ DRBG_generate_check ((value', key', x), y, z) tl returned_bits
        | generate_error => False
      end
  end.

Definition test_state: DRBG_state_handle :=
  match test_HMAC256_DRBG_instantiate_function 256 false [] with
    | instantiate_success x => x
    | _ => (([], [], 0), 0, false)
  end.

Lemma test_generate1: DRBG_generate_check test_state [
                                            ("911bf7cbda4387a172a1a3daf6c9fa8e17c4bfef69cc7eff1341e7eef88d2811"%string, "bfbdcf455d5c82acafc59f339ce57126ff70b67aef910fa25db7617818faeafe"%string);
                                            ("6dd2cd5b1edba4b620d195ce26ad6845b063211d11e591432de37a3ad793f66c"%string, "6b94e773e3469353a1ca8face76b238c5919d62a150a7dfc589ffa11c30b5b94"%string)
                                          ] "e528e9abf2dece54d47c7e75e5fe302149f817ea9fb4bee6f4199697d04d5b89d54fbb978a15b5c443c9ec21036d2460b6f73ebad0dc2aba6e624abf07745bc107694bb7547bb0995f70de25d6b29e2d3011bb19d27676c07162c8b5ccde0668961df86803482cb37ed6d5c0bb8d50cf1f50d476aa0458bdaba806f48be9dcb8".
vm_compute. auto. Qed.