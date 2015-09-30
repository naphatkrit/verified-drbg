Require Import DRBG_working_state.
Require Import Coqlib.

Definition DRBG_state_handle: Type := (DRBG_working_state * Z)%type. (* state, security_strength *)