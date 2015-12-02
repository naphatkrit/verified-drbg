Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.
Require Import floyd.sublist.

Require Import sha.HMAC256_functional_prog.
Require Import sha.general_lemmas.
Require Import sha.spec_sha.

Require Import HMAC256_DRBG_functional_prog.
Require Import HMAC_DRBG_generate_algorithm.
Require Import hmac_drbg.
Require Import spec_hmac_drbg.
Require Import DRBG_generate_function.
Require Import entropy.

Lemma data_at_weak_valid_ptr: forall (sh : Share.t) (t : type) (v : reptype t) (p : val),
       sepalg.nonidentity sh ->
       sizeof cenv_cs t >= 0 -> data_at sh t v p |-- weak_valid_pointer p.
Proof.
Admitted.
Lemma sepcon_weak_valid_pointer2
: forall (P Q : mpred) (p : val),
    P |-- weak_valid_pointer p -> Q * P |-- weak_valid_pointer p.
Proof. Admitted.
Lemma sepcon_weak_valid_pointer1
: forall (P Q : mpred) (p : val),
    P |-- weak_valid_pointer p -> P * Q |-- weak_valid_pointer p.
Proof. Admitted.
Hint Resolve sepcon_weak_valid_pointer1 sepcon_weak_valid_pointer2 data_at_weak_valid_ptr: valid_pointer.
(*
Fixpoint generate_while_loop_rounds (key v: list Z) (left: Z) (rounds: nat): (list Z * list Z) :=
  match rounds with
    | O => (v, [])
    | S rounds' =>
      let use_len := Z.min 32 left in
      let (v, rest) := generate_while_loop_rounds key v (left - use_len) rounds' in
      let v := HMAC256 v key in
      let temp := sublist 0 use_len v in
      (v, rest ++ temp)
  end
.

Lemma generate_while_loop_rounds_correct:
  forall key v z n,
    (Z.to_nat ((z + 31)/32)) = n ->
    generate_while_loop_rounds key v z n = (match HMAC_DRBG_generate_helper_rounds HMAC256 key v n with (v, bytes) => (v, sublist 0 z bytes) end).
Proof.
  intros until n.
  revert key v z.
  induction n as [|n']; intros.
  {
    (* n = 0 *)
    simpl. unfold sublist. change (Z.to_nat 0) with 0%nat. simpl. unfold skipn.
    replace (z - 0) with z by omega.
    destruct (Z.to_nat z); reflexivity.
  }
  simpl.
  SearchAbout Zdiv.
  rewrite IHn'.  
  clear IHn'.
  destruct (Z.min_dec 32 z) as [Hmin | Hmin].
  {
    (* z >= 32 *)
    rewrite Hmin.
    destruct (HMAC_DRBG_generate_helper_rounds HMAC256 key v (z - 32) n').
    replace (sublist 0 (z - 32) l0 ++ sublist 0 32 (HMAC256 l key)) with (sublist 0 z (l0 ++ HMAC256 l key)); [reflexivity|].
    admit (* TODO *).
  }
  {
    (* z < 32 *)
    rewrite Hmin.
    replace (z - z) with 0 by omega.
    remember (HMAC_DRBG_generate_helper_rounds HMAC256 key v 0 n') as x; destruct x.
    remember (HMAC_DRBG_generate_helper_rounds HMAC256 key v (z - 32) n') as x; destruct x.
    pose proof Heqx as Hl.
    pose proof Heqx0 as Hl1.
    apply HMAC_DRBG_generate_helper_rounds_v in Hl.
    apply HMAC_DRBG_generate_helper_rounds_v in Hl1.
    subst l l1.
  }
Qed.

Function generate_while_loop (key v: list Z) (left: nat) {measure (fun x => x) left}: (list Z * list Z) :=
  match left with
    | O => (v, [])
    | _ =>
      let use_len := min 32 left in
      let (v, rest) := generate_while_loop key v (left - use_len) in
      let v := HMAC256 v key in
      let temp := sublist 0 (Z.of_nat use_len) v in
      (v, rest ++ temp)
  end
.
Proof.
  intros.
  remember (S n) as m.
  destruct (Min.min_dec 32 m) as [Hmin | Hmin]; rewrite Hmin; clear Hmin; subst m; omega.
Defined.
Lemma generate_while_loop_correct:
  forall key v n,
    generate_while_loop key v n = (let '(v, bytes) := HMAC_DRBG_generate_helper HMAC256 key v n in
                                      (v, sublist 0 (Z.of_nat n) bytes)).
Proof.
  intros.
  do 32 (induction n as [|n]; [reflexivity|]).
  SearchAbout sublist S.
  simpl.
  unfold generate_while_loop.
  {
    (* left = 0 *)
    reflexivity.
  }
  {
    (* left > 0 *)
    induction p.
    simpl.
  }
  {
    (* left < 0 *)
    reflexivity.
  }
Qed.
*)
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
  unfold hmac256drbgstate_md_info_pointer.
  simpl.

  remember (HMAC256DRBGabs md_ctx V reseed_counter entropy_len prediction_resistance reseed_interval) as initial_state_abs.
  remember (md_ctx',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval)))))) as initial_state.
  
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
  rewrite Heqinitial_state. rewrite <- Heqinitial_state.

  (* if( out_len > MBEDTLS_HMAC_DRBG_MAX_REQUEST ) *)
  forward_if (
      PROP  (out_len <= 1024)
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
      data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx;
      md_full md_ctx md_ctx';
      data_at Tsh t_struct_mbedtls_md_info info_contents (fst md_ctx');
      Stream s; K_vector kv)
    ).
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
    unfold mbedtls_HMAC256_DRBG_generate_function.
    unfold HMAC256_DRBG_generate_function.
    unfold DRBG_generate_function.
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
  forward_if (
      PROP  (add_len <= 256) (* ADDED *)
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
      data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx;
      md_full md_ctx md_ctx';
      data_at Tsh t_struct_mbedtls_md_info info_contents (fst md_ctx');
      Stream s; K_vector kv)
  ).
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
    unfold mbedtls_HMAC256_DRBG_generate_function.
    unfold HMAC256_DRBG_generate_function.
    unfold DRBG_generate_function.
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
    change (0 >? 256) with false.
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
  forward_if (
      PROP  ()
      LOCAL  (temp _md_len md_len; temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv;
      temp 159%positive (Val.of_bool should_reseed) (* ADDED *)
      )
      SEP  (memory_block Tsh out_len output;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx;
      md_full md_ctx md_ctx';
      data_at Tsh t_struct_mbedtls_md_info info_contents (fst md_ctx');
      Stream s; K_vector kv)
    ).
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
      temp _add_len (Vint (Int.repr (if should_reseed then 0 else add_len))); gvar sha._K256 kv; (* ADDED *)
      temp 159%positive (Val.of_bool should_reseed))
      SEP  (
        if should_reseed then
          match (mbedtls_HMAC256_DRBG_reseed_function s initial_state_abs contents) with
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
          data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx
          * data_at Tsh t_struct_mbedtls_md_info info_contents (fst md_ctx')
          * md_full md_ctx md_ctx'
          * Stream s
        ; (* ADDED *)
        memory_block Tsh out_len output;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      spec_sha.K_vector kv)).
  {
    rename H10 into Hshould_reseed.
    (* ret = mbedtls_hmac_drbg_reseed( ctx, additional, add_len ) *)
    forward_call (contents, additional, add_len, ctx, initial_state, initial_state_abs,
                  kv, info_contents, s).
    {
      unfold hmac256drbg_relate.
      rewrite Heqinitial_state, Heqinitial_state_abs.
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

    forward_if (PROP  (return_value = Vzero) (* ADDED *)
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
      unfold mbedtls_HMAC256_DRBG_generate_function.
      unfold HMAC256_DRBG_generate_function.
      unfold DRBG_generate_function.
      unfold DRBG_generate_function_helper.
      unfold mbedtls_HMAC256_DRBG_reseed_function.
      unfold HMAC256_DRBG_reseed_function.
      unfold DRBG_reseed_function.DRBG_reseed_function.
      replace (Z.of_nat (length contents)) with (Zlength contents) by (rewrite Zlength_correct; reflexivity).
      rewrite Hout_lenb in *. rewrite Hadd_lenb in *.
      rewrite andb_negb_r in *.
      destruct md_ctx.
      change (0 >? 256) with false.
      
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
    subst initial_state initial_state_abs.
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

  (* additional != NULL && add_len != 0 *)
  forward_if (PROP  ()
      LOCAL  (temp _md_len md_len; temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len_new)); 
      gvar sha._K256 kv;
      temp 160%positive (Val.of_bool non_empty_additional) (* ADDED *)
             )
      SEP 
      (if should_reseed
       then
        match
          mbedtls_HMAC256_DRBG_reseed_function s initial_state_abs contents
        with
        | ENTROPY.success state_handle s' =>
            EX  data : list Z,
            !!(Zlength
                 (hmac256drbgabs_value
                    (hmac256drbgabs_convert_state_handle state_handle data
                       entropy_len reseed_interval)) =
               Z.of_nat SHA256.DigestLength /\
               Forall isbyteZ
                 (hmac256drbgabs_value
                    (hmac256drbgabs_convert_state_handle state_handle data
                       entropy_len reseed_interval))) &&
            (hmac_drbg_update_post
               (hmac256drbgabs_convert_state_handle state_handle data
                  entropy_len reseed_interval) ctx info_contents * 
             Stream s')
        | ENTROPY.error _ _ => !!False
        end
       else
        data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx *
        data_at Tsh t_struct_mbedtls_md_info info_contents (fst md_ctx') *
        md_full md_ctx md_ctx' * Stream s; memory_block Tsh out_len output;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional; K_vector kv)).
  {
    (* prove that additional is comparable with the null pointer *)
    

    unfold denote_tc_comparable.
    assert (Hsize_of: sizeof cenv_cs (tarray tuchar (Zlength contents)) >= 0).
    {
      pose proof (Zlength_nonneg contents).
      simpl.
      rewrite Z.mul_1_l.
      rewrite Zmax0r by omega.
      omega.
    }
    assert_PROP (isptr additional) as Hisptr by entailer!. destruct additional; try solve [inversion Hisptr]; clear Hisptr.
    entailer!.
    auto 50 with valid_pointer.
  }
  {
    (* additional <> null *)
    forward.
    entailer!.

    rewrite <- H12.
    destruct (eq_dec additional' nullval); try contradiction.
    destruct (prediction_resistance || (reseed_counter >? reseed_interval))%bool.
    auto.
    destruct (eq_dec (Zlength contents) 0).
    rewrite e.
    reflexivity.
    admit (* TODO *).
  }
  {
    (* additional = null *)
    forward.

    entailer!.
    clear.
    destruct (eq_dec nullval nullval).
    reflexivity.
    assert (contra: False) by (apply n; reflexivity); inversion contra.
  }

  remember (if should_reseed
       then
        match
          mbedtls_HMAC256_DRBG_reseed_function s initial_state_abs contents
        with
        | ENTROPY.success state_handle s' =>
            EX  data : list Z,
            !!(Zlength
                 (hmac256drbgabs_value
                    (hmac256drbgabs_convert_state_handle state_handle data
                       entropy_len reseed_interval)) =
               Z.of_nat SHA256.DigestLength /\
               Forall isbyteZ
                 (hmac256drbgabs_value
                    (hmac256drbgabs_convert_state_handle state_handle data
                       entropy_len reseed_interval))) &&
            (hmac_drbg_update_post
               (hmac256drbgabs_convert_state_handle state_handle data
                  entropy_len reseed_interval) ctx info_contents * 
             Stream s')
        | ENTROPY.error _ _ => !!False
        end
       else
        @data_at hmac_drbg_compspecs.CompSpecs Tsh t_struct_hmac256drbg_context_st initial_state ctx *
        @data_at hmac_drbg_compspecs.CompSpecs Tsh t_struct_mbedtls_md_info info_contents (fst md_ctx') *
        md_full md_ctx md_ctx' * Stream s) as drbg_SEP_after_reseed.
  forward_if (PROP  ()
      LOCAL  (temp _md_len md_len; temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len_new)); 
      gvar sha._K256 kv;
      temp 160%positive (Val.of_bool non_empty_additional))
      SEP  (
        if non_empty_additional then
          EX state_abs:_,
        !! (Zlength (snd (HMAC256_DRBG_update contents (hmac256drbgabs_key initial_state_abs) (hmac256drbgabs_value initial_state_abs))) = Z.of_nat SHA256.DigestLength
            /\ fst (HMAC256_DRBG_update contents (hmac256drbgabs_key initial_state_abs) (hmac256drbgabs_value initial_state_abs)) = hmac256drbgabs_key state_abs
            /\ snd (HMAC256_DRBG_update contents (hmac256drbgabs_key initial_state_abs) (hmac256drbgabs_value initial_state_abs)) = hmac256drbgabs_value state_abs
            /\ hmac256drbgabs_metadata_same state_abs initial_state_abs) &&
           (hmac_drbg_update_post state_abs ctx info_contents
            * Stream s
           )
        else drbg_SEP_after_reseed; memory_block Tsh out_len output; (* ADDED *)
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional; K_vector kv)).
  {
    (* mbedtls_hmac_drbg_update( ctx, additional, add_len ); *)
    assert (Hshould_reseed_false: should_reseed = false).
    {
      subst add_len_new non_empty_additional.
      destruct should_reseed.
      destruct (eq_dec additional nullval); inversion Heqnon_empty_additional.
      reflexivity.
    }
    rewrite Hshould_reseed_false in *.
    rewrite Heqadd_len_new.
    forward_call (contents, additional, add_len, ctx,
                 (md_ctx',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
         (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval)))))),
                 initial_state_abs, kv, info_contents
                 ).
    {
      (* match up SEP clauses *)
      rewrite Heqdrbg_SEP_after_reseed.
      unfold hmac256drbg_relate.
      rewrite Heqinitial_state_abs.
      rewrite Heqinitial_state.
      entailer!.
    }
    rewrite H10.
    Intros new_state_abs.
    Exists new_state_abs.
    entailer!.
  }
  {
    forward.
    rewrite H10.
    entailer!.
  }
  
  forward_while (EX out_len1: Z,
      PROP  ()
      LOCAL  (temp _md_len md_len; temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len1)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len_new)); 
      gvar sha._K256 kv;
      temp 160%positive (Val.of_bool non_empty_additional))
      SEP 
      (if non_empty_additional
       then
        EX  state_abs : hmac256drbgabs,
        !!(Zlength
             (snd
                (HMAC256_DRBG_update contents
                   (hmac256drbgabs_key initial_state_abs)
                   (hmac256drbgabs_value initial_state_abs))) =
           Z.of_nat SHA256.DigestLength /\
           fst
             (HMAC256_DRBG_update contents
                (hmac256drbgabs_key initial_state_abs)
                (hmac256drbgabs_value initial_state_abs)) =
           hmac256drbgabs_key state_abs /\
           snd
             (HMAC256_DRBG_update contents
                (hmac256drbgabs_key initial_state_abs)
                (hmac256drbgabs_value initial_state_abs)) =
           hmac256drbgabs_value state_abs /\
           hmac256drbgabs_metadata_same state_abs initial_state_abs) &&
        (hmac_drbg_update_post state_abs ctx info_contents * Stream s)
       else drbg_SEP_after_reseed;
       data_at Tsh (tarray tuchar out_len) (sublist 0 out_len1 (HMAC_DRBG_generate_helper_rounds HMAC key v (Z.to_nat ((requested_number_of_bytes + 31) / 32))) ++ list_repeat (Z.to_nat (out_len - out_len1)) Vundef) output
       ;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional; K_vector kv)
                ).