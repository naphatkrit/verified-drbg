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

Definition update_rounds (non_empty_additional: bool): nat :=
  if non_empty_additional then 2%nat else 1%nat.

Definition update_loop_invariant_SEP (add_len: Z) (ctx additional K: val) (contents: list int) (key value: list Z) (final_state_abs: hmac256drbgabs) :mpred :=
  EX state: _,
  (data_at Tsh t_struct_hmac256drbg_context_st state ctx) *
  (hmac256drbg_relate final_state_abs state) *
  (data_at_ Tsh (tarray tuchar 32) K) *
  (data_at Tsh (tarray tuchar add_len) (map Vint contents) additional).


Definition update_loop_invariant (non_empty_additional: bool) (add_len: Z) (ctx additional sep K md_len: val) (contents: list int) (old_key old_value: list Z) (state_abs: hmac256drbgabs) (state: hmac256drbgstate) :=
  EX i: _, EX key: _, EX value: _, EX final_state_abs: _,
      PROP  (
      (key, value) = HMAC_DRBG_update_round HMAC256 (map Int.signed contents) old_key old_value 0 i;
      le i (update_rounds non_empty_additional);
      key = hmac256drbgabs_key final_state_abs;
      value = hmac256drbgabs_value final_state_abs;
      hmac256drbgabs_metadata_same final_state_abs state_abs
        )
      LOCAL 
      (temp _rounds
         (force_val
            (sem_cast_i2i I8 Unsigned
               (if non_empty_additional
                then Vint (Int.repr 2)
                else Vint (Int.repr 1)))); temp _md_len md_len;
      lvar _K (tarray tuchar 32) K; lvar _sep (tarray tuchar 1) sep;
      temp _additional additional; temp _add_len (Vint (Int.repr add_len));
      temp _sep_value (Vint (Int.repr (Z.of_nat i)))
         )
      SEP  (
        `(update_loop_invariant_SEP add_len ctx additional K contents key value final_state_abs)
         ).

Definition update_loop_pre_incr_invariant (non_empty_additional: bool) (add_len: Z) (ctx additional sep K md_len: val) (contents: list int) (old_key old_value: list Z) (state_abs: hmac256drbgabs) (state: hmac256drbgstate) :=
  EX i: _, EX key: _, EX value: _, EX final_state_abs: _,
      PROP  (
      (key, value) = HMAC_DRBG_update_round HMAC256 (map Int.signed contents) old_key old_value 0 (i + 1);
      lt i (update_rounds non_empty_additional);
      key = hmac256drbgabs_key final_state_abs;
      value = hmac256drbgabs_value final_state_abs;
      hmac256drbgabs_metadata_same final_state_abs state_abs
        )
      LOCAL 
      (temp _rounds
         (force_val
            (sem_cast_i2i I8 Unsigned
               (if non_empty_additional
                then Vint (Int.repr 2)
                else Vint (Int.repr 1)))); temp _md_len md_len;
      lvar _K (tarray tuchar 32) K; lvar _sep (tarray tuchar 1) sep;
      temp _additional additional; temp _add_len (Vint (Int.repr add_len));
      temp _sep_value (Vint (Int.repr (Z.of_nat i)))
         )
      SEP  (
        `(update_loop_invariant_SEP add_len ctx additional K contents key value final_state_abs)
         ).

Definition update_loop_post (non_empty_additional: bool) (add_len: Z) (ctx additional sep K md_len: val) (contents: list int) (old_key old_value: list Z) (state_abs: hmac256drbgabs) (state: hmac256drbgstate) :=
  EX key: _, EX value: _, EX final_state_abs:_,
      PROP  (
          (key, value) = HMAC_DRBG_update_round HMAC256 (map Int.signed contents) old_key old_value 0 (if non_empty_additional then 2%nat else 1%nat);
          key = hmac256drbgabs_key final_state_abs;
      value = hmac256drbgabs_value final_state_abs;
      hmac256drbgabs_metadata_same final_state_abs state_abs
        )
      LOCAL 
      (temp _rounds
         (force_val
            (sem_cast_i2i I8 Unsigned
               (if non_empty_additional
                then Vint (Int.repr 2)
                else Vint (Int.repr 1)))); temp _md_len md_len;
      lvar _K (tarray tuchar 32) K; lvar _sep (tarray tuchar 1) sep;
      temp _additional additional; temp _add_len (Vint (Int.repr add_len))
         )
      SEP  (
        `(update_loop_invariant_SEP add_len ctx additional K contents key value final_state_abs)
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
      temp 127%positive (Val.of_bool non_empty_additional)
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
        destruct contents.
        (* contents = [], contradiction *)
        assert (contra: False) by (apply H1; reflexivity); inversion contra.
        (* contents != [], so pointer must be valid *)
        entailer!.
        rewrite Zlength_cons.
        admit (* TODO *).
      }
      solve_valid_pointer.
    }
    entailer!.
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
      temp 128%positive (if non_empty_additional then (Vint (Int.repr 2)) else (Vint (Int.repr 1)))
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

  (* sep_value = 0 *)
  unfold Sfor.
  forward.

  (* for( ; sep_value < rounds; sep_value++ ) *)
  remember (hmac256drbgabs_key initial_state_abs) as initial_key.
  remember (hmac256drbgabs_value initial_state_abs) as initial_value.
  forward_for
    (update_loop_invariant non_empty_additional add_len ctx additional sep K md_len contents initial_key initial_value initial_state_abs initial_state)
    (update_loop_pre_incr_invariant non_empty_additional add_len ctx additional sep K md_len contents initial_key initial_value initial_state_abs initial_state)
    (update_loop_post non_empty_additional add_len ctx additional sep K md_len contents initial_key initial_value initial_state_abs initial_state).
  {
    (* show that pre-condition implies the invariant *)
    unfold update_loop_invariant.
    apply exp_right with 0%nat.
    apply exp_right with initial_key.
    apply exp_right with initial_value.
    apply exp_right with initial_state_abs.
    unfold update_loop_invariant_SEP.
    entailer!.
    destruct initial_state_abs; unfold hmac256drbgabs_metadata_same; auto.
    apply exp_right with initial_state.
    entailer!.
    admit (* TODO *).
  }
  {
    (* show that the loop check type-checks *)
    entailer!.
  }
  {
    (* prove the loop invariant + loop condition being false the post condition *)
    remember (HMAC_DRBG_update_round HMAC256 (map Int.signed contents) initial_key initial_value 0 (if non_empty_additional then 2%nat else 1%nat)) as key_value_pair.
    unfold update_loop_invariant.
    unfold update_loop_post.
    apply exp_right with (fst key_value_pair).
    apply exp_right with (snd key_value_pair).
    unfold update_loop_invariant_SEP.
    unfold hmac256drbg_relate.
    (*
    entailer.
    (* must intro the existential variables, then prove i = _rounds *)
    entailer.
    assert ((x >= update_rounds
          (if eq_dec (Zlength (map Vint contents)) 0%Z
           then false
           else
            if eq_dec (eval_id _additional rho) nullval then false else true))%nat). admit.
    assert (x = update_rounds
          (if eq_dec (Zlength (map Vint contents)) 0%Z
           then false
           else
            if eq_dec (eval_id _additional rho) nullval then false else true)). admit.
    subst. *)
    admit (* TODO *).
    (*
    entailer.
    {
      repeat split.
      {
        symmetry; apply surjective_pairing.
      }
      {
        destruct (eq_dec add_len 0).
      }
    }
    {
      entailer!.
    }
*)
  }
  {
    (* prove the loop body + loop condition being true implies the loop pre-incr invariant *)
    admit (* TODO *).
  }
  {
    (* prove the pre-incr invariant preserves the invariant *)
    unfold update_loop_pre_incr_invariant.
    unfold update_loop_invariant_SEP.
    admit (* TODO *).    
  }
Admitted.