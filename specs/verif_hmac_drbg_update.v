Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.
Require Import floyd.sublist.

Require Import hmac_drbg.
Require Import spec_hmac_drbg.

Lemma body_hmac_drbg_update: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs 
       f_mbedtls_hmac_drbg_update hmac_drbg_update_spec.
Proof.
  start_function.
  name ctx' _ctx.
  name add_len' _add_len.
  name additional' _additional.
  rename lvar0 into sep. rename lvar1 into K.
  forward_call tt md_len.
Admitted.