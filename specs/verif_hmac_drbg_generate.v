Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import sha.HMAC256_functional_prog.
Require Import sha.general_lemmas.
Require Import sha.spec_sha.

Require Import HMAC256_DRBG_functional_prog.
Require Import HMAC_DRBG_generate_algorithm.
Require Import hmac_drbg.
Require Import spec_hmac_drbg.
Require Import DRBG_generate_function.
Require Import entropy.

Lemma body_hmac_drbg_reseed: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs 
       f_mbedtls_hmac_drbg_random_with_add hmac_drbg_generate_spec.
Proof.
  start_function.

  name p_rng' _p_rng.
  name ctx' _ctx.
  name add_len' _len.
  name additional' _additional.
  name out_len' _out_len.
  name output' _output.
  name out' _out.
  
  destruct initial_state_abs.
  destruct initial_state as [md_ctx' [V' [reseed_counter' [entropy_len' [prediction_resistance' reseed_interval']]]]].
  unfold hmac256drbg_relate.
  normalize.
  
  (* mbedtls_hmac_drbg_context *ctx = p_rng; *)
  forward.
  assert_PROP (ctx = (force_val (sem_cast_neutral ctx))) as Hctx by entailer!.
  rewrite <- Hctx; clear Hctx.

  (* int left = out_len *)
  forward.

  (* out = output *)
  forward.

  (* prediction_resistance = ctx->prediction_resistance *)
  forward.
  {
    (* typechecking *)
    entailer!.
    destruct prediction_resistance; constructor.
  }

  (* reseed_counter = ctx->reseed_counter *)
  forward.

  (* reseed_interval = ctx->reseed_interval *)
  forward.

  (* info = ctx->md_ctx.md_info; *)
  forward.

  (* md_len = mbedtls_md_get_size(info); *)
  forward_call tt.
  Intros md_len.

  (* if( out_len > MBEDTLS_HMAC_DRBG_MAX_REQUEST ) *)
  forward_if (PROP  (out_len <= 1024)
      LOCAL  (temp _md_len md_len; temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv)
      SEP  (memory_block Tsh out_len output;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      data_at Tsh t_struct_hmac256drbg_context_st
        (md_ctx',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval))))))
        ctx; md_full md_ctx md_ctx';
      data_at Tsh t_struct_mbedtls_md_info info_contents
        (hmac256drbgstate_md_info_pointer
           (md_ctx',
           (map Vint (map Int.repr V),
           (Vint (Int.repr reseed_counter),
           (Vint (Int.repr entropy_len),
           (Val.of_bool prediction_resistance,
           Vint (Int.repr reseed_interval))))))); Stream s;
      spec_sha.K_vector kv)).
  {
    (* return( MBEDTLS_ERR_HMAC_DRBG_REQUEST_TOO_BIG ); *)
    forward.

    (* prove post condition of the function *)
    unfold hmac_drbg_update_post, get_stream_result, hmac256drbg_relate.
    Exists (HMAC256DRBGabs md_ctx V reseed_counter entropy_len prediction_resistance reseed_interval) (Vint (Int.repr (-3))) (md_ctx',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval)))))).
    destruct md_ctx.
    rewrite andb_negb_r.
    assert (Hout_len: out_len >? 1024 = true).
    {
      rewrite Z.gtb_ltb.
      apply Z.ltb_lt.
      assumption.
    }
    rewrite Hout_len.
    entailer!.
  }
  {
    forward.
    entailer!.
  }

  normalize.
  assert (Hout_len: 0 <= out_len <= 1024) by omega.
  assert (Hout_lenb: out_len >? 1024 = false).
  {
    rewrite Z.gtb_ltb.
    apply Z.ltb_nlt.
    omega.
  }

  (* if( add_len > MBEDTLS_HMAC_DRBG_MAX_INPUT ) *)
  forward_if (PROP  (add_len <= 256)
      LOCAL  (temp _md_len md_len; temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv)
      SEP  (memory_block Tsh out_len output;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      data_at Tsh t_struct_hmac256drbg_context_st
        (md_ctx',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval))))))
        ctx; md_full md_ctx md_ctx';
      data_at Tsh t_struct_mbedtls_md_info info_contents
        (hmac256drbgstate_md_info_pointer
           (md_ctx',
           (map Vint (map Int.repr V),
           (Vint (Int.repr reseed_counter),
           (Vint (Int.repr entropy_len),
           (Val.of_bool prediction_resistance,
           Vint (Int.repr reseed_interval))))))); Stream s;
      spec_sha.K_vector kv)).
  {
    (* return( MBEDTLS_ERR_HMAC_DRBG_INPUT_TOO_BIG ); *)
    forward.

    (* prove function post condition *)
    unfold hmac_drbg_update_post, get_stream_result, hmac256drbg_relate.
    Exists (HMAC256DRBGabs md_ctx V reseed_counter entropy_len prediction_resistance reseed_interval) (Vint (Int.repr (-5))) (md_ctx',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval)))))).
    destruct md_ctx.
    rewrite andb_negb_r.
    rewrite Hout_lenb.
    assert (Hlength_contents: Zlength contents >? 256 = true).
    {
      rewrite Z.gtb_ltb.
      apply Z.ltb_lt.
      assumption.
    }
    replace (Z.of_nat (length contents)) with (Zlength contents) by (rewrite Zlength_correct; auto).
    rewrite Hlength_contents.
    entailer!.
  }
  {
    forward.
    entailer!.
  }
  normalize.
  assert (Hadd_len: 0 <= add_len <= 256) by omega.
  assert (Hadd_lenb: add_len >? 256 = false).
  {
    rewrite Z.gtb_ltb.
    apply Z.ltb_nlt.
    omega.
  }
  remember (orb prediction_resistance (reseed_counter >? reseed_interval)) as should_reseed.
  forward_if (PROP  ()
      LOCAL  (temp _md_len md_len; temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv;
      temp 159%positive (Val.of_bool should_reseed)
             )
      SEP  (memory_block Tsh out_len output;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      data_at Tsh t_struct_hmac256drbg_context_st
        (md_ctx',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval))))))
        ctx; md_full md_ctx md_ctx';
      data_at Tsh t_struct_mbedtls_md_info info_contents
        (hmac256drbgstate_md_info_pointer
           (md_ctx',
           (map Vint (map Int.repr V),
           (Vint (Int.repr reseed_counter),
           (Vint (Int.repr entropy_len),
           (Val.of_bool prediction_resistance,
           Vint (Int.repr reseed_interval))))))); Stream s;
      spec_sha.K_vector kv)).
  {
    forward.
    entailer!.
    
    rename H10 into Hpr.
    destruct prediction_resistance.
    (* true *) reflexivity.
    (* false *)
    inversion Hpr.
  }
  {
    rename H10 into Hpr.
    destruct prediction_resistance; try solve [inversion Hpr].
    simpl in Heqshould_reseed.
    forward.
    subst should_reseed.
    entailer!.
    rewrite <- H11.
    
    rewrite Z.gtb_ltb.
    unfold Int.lt.
    destruct (zlt reseed_interval reseed_counter) as [Hlt | Hlt].
    {
      (* reseed_interval < reseed_counter *)
      assert (Hltb: reseed_interval <? reseed_counter = true) by (rewrite Z.ltb_lt; assumption).
      rewrite Hltb.
      (* TODO *) admit.
    }
    {
      assert (Hltb: reseed_interval <? reseed_counter = false) by (rewrite Z.ltb_nlt; assumption).
      rewrite Hltb.
      (* TODO *) admit.
    }
  }
  unfold hmac256drbgstate_md_info_pointer.
  simpl.
  forward_if (
      PROP  (
      )
      LOCAL  (temp _md_len md_len; temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr (if should_reseed then 0 else add_len))); gvar sha._K256 kv;
      temp 159%positive (Val.of_bool should_reseed))
      SEP  (
        if should_reseed then
          match (mbedtls_HMAC256_DRBG_reseed_function s (HMAC256DRBGabs md_ctx V reseed_counter entropy_len prediction_resistance reseed_interval) contents) with
            | ENTROPY.error _ s' => !!False (* bogus, not used since the function returns *)
            | ENTROPY.success state_handle s' =>
              EX data:_,
              let state_abs := (hmac256drbgabs_convert_state_handle state_handle data entropy_len reseed_interval) in
              !!(Zlength (hmac256drbgabs_value state_abs) = Z.of_nat SHA256.DigestLength
                 /\ Forall isbyteZ (hmac256drbgabs_value state_abs)) &&
                (hmac_drbg_update_post state_abs ctx info_contents
                 * Stream s')
          end
        else
          data_at Tsh t_struct_hmac256drbg_context_st
        (md_ctx',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval))))))
        ctx
          * data_at Tsh t_struct_mbedtls_md_info info_contents (fst md_ctx')
          * md_full md_ctx md_ctx'
          * Stream s
        ;
        memory_block Tsh out_len output;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      spec_sha.K_vector kv)).
  {
    rename H10 into Hshould_reseed.
    (* ret = mbedtls_hmac_drbg_reseed( ctx, additional, add_len ) *)
    forward_call (contents, additional, add_len, ctx,
                  (md_ctx',
           (map Vint (map Int.repr V),
           (Vint (Int.repr reseed_counter),
           (Vint (Int.repr entropy_len),
           (Val.of_bool prediction_resistance,
           Vint (Int.repr reseed_interval)))))),
                  (HMAC256DRBGabs md_ctx V reseed_counter entropy_len prediction_resistance reseed_interval),
                  kv, info_contents, s).
    {
      unfold hmac256drbg_relate.
      entailer!.
    }
    {
      (* prove the PROP clauses *)
      change (Int.max_unsigned) with 4294967295.
      repeat split; auto; omega.
    }
    Intros vret; destruct vret as [state_abs return_value].
    unfold hmac_drbg_update_post. Intros state.
    forward.

    forward_if (PROP  (return_value = Vzero)
      LOCAL  (temp _ret return_value;
      temp 158%positive (snd (state_abs, return_value)); 
      temp _md_len md_len; temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv;
      temp 159%positive (Val.of_bool should_reseed))
      SEP 
      (hmac_drbg_update_post (fst (state_abs, return_value)) ctx
         info_contents;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      Stream
        (get_stream_result
           (mbedtls_HMAC256_DRBG_reseed_function s
              (HMAC256DRBGabs md_ctx V reseed_counter entropy_len
                 prediction_resistance reseed_interval) contents));
      K_vector kv; memory_block Tsh out_len output)).
    {
      (* return_value != 0 *)
      forward.

      rename H10 into Hreseed_result; simpl in Hreseed_result.
      rename H11 into Hreturn_value; simpl in Hreturn_value.
      assert (Hret_not_0: _id0 <> Int.zero).
      {
        clear - H14.
        intros contra. subst.
        inversion H14.
      }
      destruct state_abs.
      destruct state as [md_ctx0' [V' [reseed_counter' [entropy_len' [prediction_resistance' reseed_interval']]]]].

      unfold hmac_drbg_update_post, get_stream_result, hmac256drbg_relate.
      Exists (HMAC256DRBGabs md_ctx V reseed_counter entropy_len prediction_resistance reseed_interval) (Vint _id0) (md_ctx0',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval)))))).
      apply orb_true_iff in Hshould_reseed.
      replace (Z.of_nat (length contents)) with (Zlength contents) by (rewrite Zlength_correct; auto).
      rewrite Hout_lenb in *. rewrite Hadd_lenb in *.
      rewrite andb_negb_r in *.
      destruct md_ctx.
      remember (get_entropy 256 entropy_len entropy_len prediction_resistance s) as get_entropy_result; destruct get_entropy_result.
      {
        (* entropy succeeded - not possible *)
        clear - Hreturn_value Hret_not_0.
        unfold return_value_relate_result in Hreturn_value.
        idtac.
        inv Hreturn_value.
        assert (contra: False) by (apply Hret_not_0; auto); inversion contra.
      }
      (* entropy failed *)
      unfold hmac256drbgabs_relate_reseed_result in Hreseed_result.
      inv Hreseed_result.
      destruct Hshould_reseed as [Hpr | Hcount].
      {
        (* prediction_resistance = true *)
        subst.
        entailer!.
      }
      {
        (* reseed_counter > reseed_interval *)
        destruct prediction_resistance0; [entailer!|].
        unfold HMAC256_DRBG_generate_algorithm.
        unfold HMAC_DRBG_generate_algorithm.
        rename H4 into Hreseed_interval.
        simpl in Hreseed_interval.
        subst reseed_interval0.
        rewrite Hcount.
        unfold HMAC256_DRBG_reseed_function.
        unfold DRBG_reseed_function.DRBG_reseed_function.
        rewrite Hadd_lenb.
        rewrite andb_negb_r.
        rewrite <- Heqget_entropy_result.
        entailer!.
      }
    }
    {
      (* return value = 0 *)
      forward.

      assert (Hret_eq_0: return_value = Vzero).
      {
        clear - H14.
        destruct return_value; inv H14.
        remember (Int.eq i (Int.repr 0)) as i_0; destruct i_0; inv H0.
        apply binop_lemmas2.int_eq_true in Heqi_0.
        rewrite Heqi_0; reflexivity.
      }
      subst return_value.
      unfold hmac_drbg_update_post.
      Exists state.
      entailer!.
    }

    (* add_len = 0; *)
    forward.

    (* prove post condition of if statement *)
    rename H10 into Hreseed_result.
    rename H11 into Hreturn_value.
    subst return_value.
    destruct (mbedtls_HMAC256_DRBG_reseed_function s
             (HMAC256DRBGabs md_ctx V reseed_counter entropy_len
                prediction_resistance reseed_interval) contents); simpl in Hreturn_value.
    Focus 2. destruct e; [inversion Hreturn_value | assert (contra: False) by (apply Hreturn_value; reflexivity); inversion contra].
    destruct state_abs. destruct md_ctx0.
    subst should_reseed. rewrite Hshould_reseed.
    unfold hmac256drbgabs_convert_state_handle.
    unfold hmac256drbgabs_relate_reseed_result in Hreseed_result.
    destruct d as [[[[V1 key1] reseed_counter1] security_strength1] prediction_resistance1].
    simpl in Hreseed_result.
    destruct Hreseed_result as [Hkey1 [HV1 [Hreseed_counter1 [Hentropy_len [Hprediction_resistance1 Hreseed_interval1]]]]].
    subst.
    Exists data.
    entailer!.
  }
  {
    forward.

    rewrite H10.
    entailer!.
  }

  remember (if should_reseed then 0 else add_len) as add_len_new.

  remember (if eq_dec additional nullval then false else if eq_dec add_len_new 0 then false else true) as non_empty_additional.