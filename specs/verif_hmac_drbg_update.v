Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.
Require Import floyd.sublist.

Require Import hmac_drbg.
Require Import spec_hmac_drbg.
Require Import HMAC_DRBG_update.
Require Import sha.HMAC256_functional_prog.

Fixpoint HMAC_DRBG_update_round (HMAC: list Z -> list Z -> list Z) (provided_data K V: list Z) (sep: Z) (round: nat): (list Z * list Z) :=
  match round with
    | O => (K, V)
    | S round' =>
      let K := HMAC (V ++ [sep] ++ provided_data) K in
      let V := HMAC V K in
      HMAC_DRBG_update_round HMAC provided_data K V (sep + 1) round'
  end.

Definition HMAC_DRBG_update_concrete (HMAC: list Z -> list Z -> list Z) (provided_data K V: list Z): (list Z * list Z) :=
  let rounds := match provided_data with
                  | [] => 1%nat
                  | _ => 2%nat
                end in
  HMAC_DRBG_update_round HMAC provided_data K V 0 rounds.

Theorem HMAC_DRBG_update_concrete_correct:
  forall HMAC provided_data K V, HMAC_DRBG_update HMAC provided_data K V = HMAC_DRBG_update_concrete HMAC provided_data K V.
Proof.
  intros.
  destruct provided_data; reflexivity.
Qed.

Definition update_loop_invariant ctx sep provided_data old_key old_value state_abs state i key value :=
  (*
  EX i: _, EX key: _, EX value: _,
   *)
  PROP  ((key, value) = HMAC_DRBG_update_round HMAC256 provided_data old_key old_value 0 i)
  LOCAL  (
    lvar _sep (tarray tuchar 1) sep
         )
  SEP  (
  `(data_at Tsh (tarray tuchar 1) [Vint (Int.repr (Z.of_nat i))] sep);
  `(data_at Tsh t_struct_hmac256drbg_context_st state ctx);
  `(hmac256drbg_relate (hmac256drbgabs_update_key (hmac256drbgabs_update_value state_abs value) key) state)
  ).

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
  remember (if eq_dec add_len 0 then false else if eq_dec additional nullval then false else true) as non_empty_additional.
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
    clear - H3 H1 TC.
    rewrite Zlength_map in *.
    destruct (eq_dec (Zlength contents) 0) as [zlength_eq | zlength_neq].
    assert (contra: False) by (apply H1; apply zlength_eq); inversion contra.
    destruct additional'; try solve [inversion TC]. 
    {
      inv TC.
      destruct (eq_dec (Vint Int.zero) nullval) as [additional_eq | additional_neq].
      auto.
      assert (contra: False) by (apply additional_neq; reflexivity); inversion contra.
    }
    {
      destruct (eq_dec (Vptr b i) nullval) as [additional_eq | additional_neq].
      inversion additional_eq.
      auto.
    }
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

  (* sep[0] = 0 *)
  forward.

  forward.
Admitted.