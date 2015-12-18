Require Import Integers.
Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import DRBG_working_state.
Require Import DRBG_state_handle.
Require Import entropy.

Definition DRBG_instantiate_function (instantiate_algorithm: list Z -> list Z -> list Z -> Z -> DRBG_working_state) (min_entropy_length max_entropy_length: Z) (get_nonce: unit -> list Z) (highest_supported_security_strength: Z) (max_personalization_string_length: Z) (prediction_resistance_supported: bool) (entropy_stream: ENTROPY.stream) (requested_instantiation_security_strength: Z) (prediction_resistance_flag: bool) (personalization_string: list Z): ENTROPY.result DRBG_state_handle :=
  if Z.gtb requested_instantiation_security_strength highest_supported_security_strength then ENTROPY.error ENTROPY.generic_error entropy_stream
  else match prediction_resistance_flag, prediction_resistance_supported with
         | true, false => ENTROPY.error ENTROPY.generic_error entropy_stream
         | _,_ =>
           if Z.gtb (Zlength personalization_string) max_personalization_string_length then ENTROPY.error ENTROPY.generic_error entropy_stream
           else
             let security_strength := if requested_instantiation_security_strength <=? 14 then Some 14
                                      else if requested_instantiation_security_strength <=? 16 then Some 16
                                      else if requested_instantiation_security_strength <=? 24 then Some 24
                                      else if requested_instantiation_security_strength <=? 32 then Some 32
                                      else None in
             match security_strength with
               | None => ENTROPY.error ENTROPY.generic_error entropy_stream
               | Some security_strength =>
               match get_entropy security_strength min_entropy_length max_entropy_length prediction_resistance_flag entropy_stream with
                 | ENTROPY.error e s' => ENTROPY.error ENTROPY.catastrophic_error s'
                 | ENTROPY.success entropy_input entropy_stream =>
                   match get_entropy (security_strength/2) (min_entropy_length/2) (max_entropy_length/2) prediction_resistance_flag entropy_stream with
                     | ENTROPY.error e s' => ENTROPY.error ENTROPY.catastrophic_error s'
                     | ENTROPY.success nonce entropy_stream =>
                       
                       let initial_working_state := instantiate_algorithm entropy_input nonce personalization_string security_strength in
                       ENTROPY.success (initial_working_state, security_strength, prediction_resistance_flag) entropy_stream
                   end
               end
             end
       end.
