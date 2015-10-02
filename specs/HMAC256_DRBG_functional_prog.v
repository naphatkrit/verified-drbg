Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import HMAC256_functional_prog.
Require Import DRBG_instantiate_function.
Require Import HMAC_DRBG_instantiate_algorithm.
Require Import DRBG_generate_function.
Require Import HMAC_DRBG_generate_algorithm.

Definition HMAC256_DRBG_instantiate_algorithm := HMAC_DRBG_instantiate_algorithm HMAC256.

Definition HMAC256_DRBG_instantiate_function := DRBG_instantiate_function HMAC256_DRBG_instantiate_algorithm.

Definition HMAC256_DRBG_generate_algorithm := HMAC_DRBG_generate_algorithm HMAC256 1024.

Definition HMAC256_DRBG_generate_function := DRBG_generate_function HMAC256_DRBG_generate_algorithm.
