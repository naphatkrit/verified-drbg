Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import DRBG_working_state.

Inductive DRBG_generate_algorithm_result :=
| generate_algorithm_reseed_required: DRBG_generate_algorithm_result
| generate_algorithm_success: list Z -> DRBG_working_state -> DRBG_generate_algorithm_result.