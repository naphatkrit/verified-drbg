Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import functional_prog.
Require Import HMAC256_functional_prog.
Require Import DRBG_instantiate_function.
Require Import HMAC_DRBG_instantiate_algorithm.

Definition HMAC256_DRBG_instantiate_algorithm := HMAC_DRBG_instantiate_algorithm HMAC256.

Definition HMAC256_DRBG_instantiate_function := DRBG_instantiate_function HMAC256_DRBG_instantiate_algorithm.

Definition get_entropy_input_dummy (result: string) (x y z: Z) (b: bool): entropy_result := entropy_success (hexstring_to_Zlist result).

Definition get_nonce_dummy (result: string) (_: unit) := hexstring_to_Zlist result.

Definition test_HMAC256_DRBG_instantiate_function := HMAC256_DRBG_instantiate_function (get_entropy_input_dummy "ca851911349384bffe89de1cbdc46e6831e44d34a4fb935ee285dd14b71a7488") 0 0 (get_nonce_dummy "659ba96c601dc69fc902940805ec0ca8") 256 0 false.

Definition DRBG_instantiate_check (key value: string) :=
  let key := hexstring_to_Zlist key in
  let value := hexstring_to_Zlist value in
  match test_HMAC256_DRBG_instantiate_function 256 false [] with
    | instantiate_success ((value', key', _), _) => listZ_eq value value' = true /\ listZ_eq key key' = true
    | _ => False
  end.

Lemma test1: DRBG_instantiate_check "302a4aba78412ab36940f4be7b940a0c728542b8b81d95b801a57b3797f9dd6e" "e75855f93b971ac468d200992e211960202d53cf08852ef86772d6490bfb53f9".
vm_compute. auto. Qed.