Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.
Require Import floyd.sublist.

Require Import hmac_drbg.
Require Import spec_hmac_drbg.

Lemma body_md_get_size: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_md_get_size md_get_size_spec.
Proof.
  start_function.
  forward.
Qed.

Lemma body_md_update: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_md_hmac_update md_update_spec.
Proof.
  start_function.

  name ctx' _ctx.
  name input' _input.
  name ilen' _ilen.
  
  unfold md_relate; unfold convert_abs; unfold UNDER_SPEC.REP.
  Intros internal_state_abs.
  destruct r as [r1 [r2 internal_r]].
  (* HMAC_CTX * hmac_ctx = ctx->hmac_ctx; *)
  forward.
  {
    (* prove typechecking *)
    assert_PROP (isptr internal_r) as Hisptr_r.
    entailer!.
    unfold field_compatible in H5; destruct H5; assumption.
    entailer!.
  }

  (* HMAC_Update(hmac_ctx, input, ilen); *)
  forward_call (key, internal_r, d, data, data1, kv).
  {
    entailer!.
    destruct input'; try solve [inversion TC0]; reflexivity.
  }
  {
    unfold funspec_hmacNK.OPENSSL_HMAC_ABSTRACT_SPEC.REP.
    unfold spec_sha.data_block.
    Exists internal_state_abs.
    entailer!.
    (* TODO this should not be needed *)
    change
      (@data_at spec_hmacNK.CompSpecs Tsh (tarray tuchar (@Zlength Z data1))
                (@map int val Vint (@map Z int Int.repr data1)) d) with
    (@data_at hmac_drbg_compspecs.CompSpecs Tsh (tarray tuchar (@Zlength Z data1))
         (@map int val Vint (@map Z int Int.repr data1)) d).
    cancel.
  }

  (* return 0 *)
  forward.
  unfold funspec_hmacNK.OPENSSL_HMAC_ABSTRACT_SPEC.REP.
  unfold spec_sha.data_block.
  unfold md_relate; unfold convert_abs; unfold UNDER_SPEC.REP.
  Intros final_internal_state_abs; Exists final_internal_state_abs.
  entailer!.
  (* TODO this should not be needed *)
  change
      (@data_at spec_hmacNK.CompSpecs Tsh (tarray tuchar (@Zlength Z data1))
                (@map int val Vint (@map Z int Int.repr data1)) input') with
    (@data_at hmac_drbg_compspecs.CompSpecs Tsh (tarray tuchar (@Zlength Z data1))
         (@map int val Vint (@map Z int Int.repr data1)) input').
  cancel.
Qed.

Lemma body_md_final: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_md_hmac_finish md_final_spec.
Proof.
  start_function.

  name ctx' _ctx.
  name output' _output.
  
  unfold md_relate; unfold convert_abs; unfold UNDER_SPEC.REP.
  Intros internal_state_abs.
  destruct r as [r1 [r2 internal_r]].
  (* HMAC_CTX * hmac_ctx = ctx->hmac_ctx; *)
  forward.
  {
    (* prove typechecking *)
    assert_PROP (isptr internal_r) as Hisptr_r.
    entailer!.
    unfold field_compatible in H2; destruct H2; assumption.
    entailer!.
  }

  (* HMAC_Final(hmac_ctx, output); *)
  forward_call (data, key, internal_r, md, shmd, kv).
  {
     unfold funspec_hmacNK.OPENSSL_HMAC_ABSTRACT_SPEC.REP.
    unfold spec_sha.data_block.
    Exists internal_state_abs.
    entailer!.
  }

  (* return 0 *)
  forward.
  unfold spec_sha.data_block.
  entailer!.
Qed.

Lemma body_md_reset: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_md_hmac_reset md_reset_spec.
Proof.
  start_function.

  name ctx' _ctx.

  unfold UNDER_SPEC.FULL.
  Intros internal_state_abs.
  unfold spec_hmacNK.hmacstate_PreInitNull.
  Intros internal_state v.
  destruct r as [r1 [r2 internal_r]].
  simpl.
  (* HMAC_CTX * hmac_ctx = ctx->hmac_ctx; *)
  forward.
  {
    (* prove typechecking *)
    assert_PROP (isptr internal_r) as Hisptr_r.
    entailer!.
    unfold field_compatible in H2; destruct H2; assumption.
    entailer!.
  }

  forward_call (internal_r, 32, key, kv).
  {
    unfold funspec_hmacNK.OPENSSL_HMAC_ABSTRACT_SPEC.FULL.
    Exists internal_state_abs.
    unfold spec_hmacNK.hmacstate_PreInitNull.
    Exists internal_state v.
    entailer!.
  }
  forward.
  unfold md_relate.
  unfold convert_abs.
  entailer!.
Qed.