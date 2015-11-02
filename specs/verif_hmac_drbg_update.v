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
  rename lvar0 into info.
  rename lvar1 into sep.
  rename lvar2 into K.
  (* md_len = mbedtls_md_get_size( ctx->md_ctx.md_info ); *)
  forward_call tt md_len.

  (* rounds = ( additional != NULL && add_len != 0 ) ? 2 : 1; *)
  remember (if eq_dec add_len 0 then false else if eq_dec additional nullval then true else false) as non_empty_additional.
  forward_if (
      PROP  ()
      LOCAL  (temp _md_len md_len; lvar _K (tarray tuchar 32) K;
      lvar _sep (tarray tuchar 1) sep;
      lvar _info (Tstruct _mbedtls_md_info_t noattr) info;
      temp _additional additional; temp _add_len (Vint (Int.repr add_len));
      temp 126%positive (Val.of_bool non_empty_additional)
             )
      SEP  (`(data_at_ Tsh (tarray tuchar 32) K);
      `(data_at_ Tsh (tarray tuchar 1) sep);
      `(data_at_ Tsh (Tstruct _mbedtls_md_info_t noattr) info);
      `(data_at Tsh (tarray tuchar add_len) (map Vint contents) additional);
      `(data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx);
      `(hmac256drbg_relate initial_state_abs initial_state))
    ).
  {
    (* show that add_len <> 0 implies the post condition *)
    forward.
    {
      entailer!.
      apply denote_tc_comparable_split.
      {
        destruct additional'; try solve [inv TC].
        inversion TC. subst. solve_valid_pointer.
        admit (* TODO *).
      }
      solve_valid_pointer.
    }
    entailer!.
    rewrite <- H3.
    admit (* TODO *).
  }

  {
    (* show that add_len = 0 implies the post condition *)
    forward.
    entailer!.
  }

  forward_if (
      PROP  ()
      LOCAL  (temp _md_len md_len; lvar _K (tarray tuchar 32) K;
      lvar _sep (tarray tuchar 1) sep;
      lvar _info (Tstruct _mbedtls_md_info_t noattr) info;
      temp _additional additional; temp _add_len (Vint (Int.repr add_len));
      temp 126%positive (Val.of_bool non_empty_additional);
      temp 127%positive (if non_empty_additional then (Vint (Int.repr 2)) else (Vint (Int.repr 1)))
             )
      SEP  (`(data_at_ Tsh (tarray tuchar 32) K);
      `(data_at_ Tsh (tarray tuchar 1) sep);
      `(data_at_ Tsh (Tstruct _mbedtls_md_info_t noattr) info);
      `(data_at Tsh (tarray tuchar add_len) (map Vint contents) additional);
      `(data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx);
      `(hmac256drbg_relate initial_state_abs initial_state))
  ).
  {
    (* non_empty_additional = true *)
    forward.
    entailer!.
  }
  {
    (* non_empty_additional = false *)
    forward.
    entailer!.
  }
  forward.
Admitted.