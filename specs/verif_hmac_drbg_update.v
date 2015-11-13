Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmac_drbg.
Require Import spec_hmac_drbg.
Require Import HMAC_DRBG_update.
Require Import sha.HMAC256_functional_prog.
Require Import sha.spec_sha.

Fixpoint HMAC_DRBG_update_round (HMAC: list Z -> list Z -> list Z) (provided_data K V: list Z) (round: nat): (list Z * list Z) :=
  match round with
    | O => (K, V)
    | S round' =>
      let (K, V) := HMAC_DRBG_update_round HMAC provided_data K V round' in
      let K := HMAC (V ++ [Z.of_nat round'] ++ provided_data) K in
      let V := HMAC V K in
      (K, V)
  end.

Definition HMAC_DRBG_update_concrete (HMAC: list Z -> list Z -> list Z) (provided_data K V: list Z): (list Z * list Z) :=
  let rounds := match provided_data with
                  | [] => 1%nat
                  | _ => 2%nat
                end in
  HMAC_DRBG_update_round HMAC provided_data K V rounds.

Theorem HMAC_DRBG_update_concrete_correct:
  forall HMAC provided_data K V, HMAC_DRBG_update HMAC provided_data K V = HMAC_DRBG_update_concrete HMAC provided_data K V.
Proof.
  intros.
  destruct provided_data; reflexivity.
Qed.

Definition update_rounds (non_empty_additional: bool): Z :=
  if non_empty_additional then 2 else 1.

Definition update_relate_final_state (ctx: val) (final_state_abs: hmac256drbgabs) (info_contents: md_info_state) :mpred :=
  EX final_state: hmac256drbgstate,
  (data_at Tsh t_struct_hmac256drbg_context_st final_state ctx) *
  (data_at Tsh t_struct_mbedtls_md_info info_contents
           (hmac256drbgstate_md_info_pointer final_state)) *
  (hmac256drbg_relate final_state_abs final_state).

Lemma HMAC_DRBG_update_round_incremental:
  forall key V initial_state_abs contents n,
    (key, V) = HMAC_DRBG_update_round HMAC256 contents
                           (hmac256drbgabs_key initial_state_abs)
                           (hmac256drbgabs_value initial_state_abs) n ->
    (HMAC256 (V ++ (Z.of_nat n) :: contents) key,
     HMAC256 V (HMAC256 (V ++ (Z.of_nat n) :: contents) key)) =
    HMAC_DRBG_update_round HMAC256 contents
                           (hmac256drbgabs_key initial_state_abs)
                           (hmac256drbgabs_value initial_state_abs) (n + 1).
Proof.
  intros.
  rewrite plus_comm.
  simpl.
  rewrite <- H.
  reflexivity.
Qed.

Lemma HMAC_DRBG_update_round_incremental_Z:
  forall key V initial_state_abs contents i,
    0 <= i ->
    (key, V) = HMAC_DRBG_update_round HMAC256 contents
                           (hmac256drbgabs_key initial_state_abs)
                           (hmac256drbgabs_value initial_state_abs) (Z.to_nat i) ->
    (HMAC256 (V ++ i :: contents) key,
     HMAC256 V (HMAC256 (V ++ i :: contents) key)) =
    HMAC_DRBG_update_round HMAC256 contents
                           (hmac256drbgabs_key initial_state_abs)
                           (hmac256drbgabs_value initial_state_abs) (Z.to_nat (i + 1)).
Proof.
  intros.
  rewrite <- (Z2Nat.id i) at 1 2 by assumption.
  rewrite Z2Nat.inj_add by (try assumption; try omega).
  simpl.
  apply HMAC_DRBG_update_round_incremental; assumption.
Qed.

(*

Definition update_loop_invariant (non_empty_additional: bool) (add_len: Z) (ctx additional sep K md_len info kv: val) (contents: list int) (old_key old_value: list Z) (state_abs: hmac256drbgabs) (state: hmac256drbgstate) :=
  EX i: Z,
      PROP  (
      (* (key, value) = HMAC_DRBG_update_round HMAC256 (map Int.signed contents) old_key old_value 0 (Z.to_nat i);
      (*
      le i (update_rounds non_empty_additional);
       *)
      key = hmac256drbgabs_key final_state_abs;
      value = hmac256drbgabs_value final_state_abs;
      hmac256drbgabs_metadata_same final_state_abs state_abs *)
        ) 
      LOCAL 
      (temp _rounds
         (force_val
            (sem_cast_i2i I8 Unsigned
               (if non_empty_additional
                then Vint (Int.repr 2)
                else Vint (Int.repr 1)))); temp _md_len md_len;
       lvar _K (tarray tuchar 32) K; lvar _sep (tarray tuchar 1) sep;
       lvar _info (Tstruct _mbedtls_md_info_t noattr) info;
      temp _additional additional; temp _add_len (Vint (Int.repr add_len));
      temp _sep_value (Vint (Int.repr i))
         )
      SEP  (
        `(EX key: list Z, EX value: list Z, EX final_state_abs: hmac256drbgabs,
           !!((key, value) = HMAC_DRBG_update_round HMAC256 (map Int.signed contents) old_key old_value 0 (Z.to_nat i) /\  key = hmac256drbgabs_key final_state_abs /\
      value = hmac256drbgabs_value final_state_abs /\
      hmac256drbgabs_metadata_same final_state_abs state_abs) &&
           (update_relate_final_state ctx final_state_abs)
         );
        (* `(update_relate_final_state ctx final_state_abs); *)
        `(data_at_ Tsh (tarray tuchar 32) K);
        `(data_at Tsh (tarray tuchar add_len) (map Vint contents) additional);
        `(data_at_ Tsh (tarray tuchar 1) sep );
        `(data_at_ Tsh (Tstruct _mbedtls_md_info_t noattr) info);
        `(K_vector kv)
         ).
*)
(*
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
*)

Lemma body_hmac_drbg_update: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs 
       f_mbedtls_hmac_drbg_update hmac_drbg_update_spec.
Proof.
  start_function.
  name ctx' _ctx.
  name add_len' _add_len.
  name additional' _additional.
  rename lvar0 into sep.
  rename lvar1 into K.

  (* info = md_ctx.md_info *)
  forward.
  
  (* md_len = mbedtls_md_get_size( info ); *)
  forward_call tt md_len.

  (* rounds = ( additional != NULL && add_len != 0 ) ? 2 : 1; *)
  remember (if eq_dec add_len 0 then false else if eq_dec additional nullval then false else true) as non_empty_additional.
  forward_if (
      PROP  ()
      LOCAL  (temp _md_len md_len; lvar _K (tarray tuchar 32) K;
      temp _ctx ctx;
      lvar _sep (tarray tuchar 1) sep;
      temp _additional additional; temp _add_len (Vint (Int.repr add_len));
      temp 126%positive (Val.of_bool non_empty_additional);
      gvar sha._K256 kv
             )
      SEP  (`(data_at_ Tsh (tarray tuchar 32) K);
      `(data_at_ Tsh (tarray tuchar 1) sep);
      `(data_at Tsh (tarray tuchar add_len)
          (map Vint (map Int.repr contents)) additional);
      `(data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx);
      `(hmac256drbg_relate initial_state_abs initial_state);
      `(data_at Tsh t_struct_mbedtls_md_info info_contents
          (hmac256drbgstate_md_info_pointer initial_state));
      `(K_vector kv)
       )
    ).
  {
    (* show that add_len <> 0 implies the post condition *)
    forward.
    {
      entailer!.
      assert (sizeof cenv_cs (tarray tuchar (Zlength contents)) > 0).
      {
        simpl.
        destruct contents.
        assert (contra: False) by (apply H5; reflexivity); inversion contra.
        clear.
        repeat rewrite Zlength_map. rewrite Zlength_cons.
        assert (0 <= Zlength contents) by (apply Zlength_nonneg).
        destruct (Zlength contents).
        simpl; omega.
        hnf; auto.
        assert (contra: False) by (apply H; reflexivity); inversion contra.
      }
      apply denote_tc_comparable_split; auto 50 with valid_pointer.
      (* TODO regressoin, this should have solved it *) 
      (*
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer2.
      apply data_at_valid_ptr; auto. *)
    }
    entailer!.
    repeat rewrite Zlength_map in *.
    destruct (eq_dec (Zlength contents) 0) as [zlength_eq | zlength_neq].
    assert (contra: False) by (apply H5; apply zlength_eq); inversion contra.
    destruct additional'; try solve [inversion TC0]. 
    {
      inv TC0.
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
    entailer!. rewrite H5.
    auto.
  }

  remember (update_rounds non_empty_additional) as rounds. unfold update_rounds in Heqrounds.
  
  forward_if (
      PROP  ()
      LOCAL  (temp _md_len md_len; lvar _K (tarray tuchar 32) K;
      temp _ctx ctx;
      lvar _sep (tarray tuchar 1) sep;
      temp _additional additional; temp _add_len (Vint (Int.repr add_len));
      temp 127%positive (Vint (Int.repr rounds));
      gvar sha._K256 kv
             )
      SEP  (`(data_at_ Tsh (tarray tuchar 32) K);
      `(data_at_ Tsh (tarray tuchar 1) sep);
      `(data_at Tsh (tarray tuchar add_len)
          (map Vint (map Int.repr contents)) additional);
      `(data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx);
      `(hmac256drbg_relate initial_state_abs initial_state);
      `(data_at Tsh t_struct_mbedtls_md_info info_contents
                (hmac256drbgstate_md_info_pointer initial_state)); 
      `(K_vector kv)
      )
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

  remember (hmac256drbgabs_key initial_state_abs) as initial_key.
  remember (hmac256drbgabs_value initial_state_abs) as initial_value.
  (* verif_sha_final2.v, @exp (environ -> mpred) *)
  (* for ( sep_value = 0; sep_value < rounds; sep_value++ ) *)
  forward_for_simple_bound rounds (
                              EX i: Z,
      PROP  (
      (* (key, value) = HMAC_DRBG_update_round HMAC256 (map Int.signed contents) old_key old_value 0 (Z.to_nat i);
      (*
      le i (update_rounds non_empty_additional);
       *)
      key = hmac256drbgabs_key final_state_abs;
      value = hmac256drbgabs_value final_state_abs;
      hmac256drbgabs_metadata_same final_state_abs state_abs *)
        ) 
      LOCAL (
       temp _md_len md_len;
       temp _ctx ctx;
       lvar _K (tarray tuchar 32) K; lvar _sep (tarray tuchar 1) sep;
       temp _additional additional; temp _add_len (Vint (Int.repr add_len));
       gvar sha._K256 kv
         )
      SEP  (
        `(EX key: list Z, EX value: list Z, EX final_state_abs: hmac256drbgabs,
          !!(
              (key, value) = HMAC_DRBG_update_round HMAC256 contents initial_key initial_value (Z.to_nat i)
              /\ key = hmac256drbgabs_key final_state_abs
              /\ value = hmac256drbgabs_value final_state_abs
              /\ hmac256drbgabs_metadata_same final_state_abs initial_state_abs
              /\ Zlength value = Z.of_nat SHA256.DigestLength
              /\ Forall general_lemmas.isbyteZ value
            ) &&
           (update_relate_final_state ctx final_state_abs info_contents)
         );
        (* `(update_relate_final_state ctx final_state_abs); *)
        `(data_at_ Tsh (tarray tuchar 32) K);
        `(data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional);
        `(data_at_ Tsh (tarray tuchar 1) sep );
        `(K_vector kv)
         )
  ).
  {
    (* Int.min_signed <= 0 <= rounds *)
    rewrite Heqrounds; destruct non_empty_additional; auto.
  }
  {
    (* rounds <= Int.max_signed *)
    rewrite Heqrounds; destruct non_empty_additional; auto.
  }
  {
    (* pre conditions imply loop invariant *)
    unfold update_relate_final_state.
    normalize.
    entailer!.
    Exists (hmac256drbgabs_key initial_state_abs) (hmac256drbgabs_value initial_state_abs) initial_state_abs.
    normalize. Exists initial_state.
    entailer!. destruct initial_state_abs; simpl; auto.
  }
  {
    (* loop body *)
    change (`(eq (Vint (Int.repr rounds))) (eval_expr (Etempvar _rounds tint))) with (temp _rounds (Vint (Int.repr rounds))).
    unfold update_relate_final_state.
    Intros key value state_abs state.
    forward.
    (*
    unfold hmac256drbgstate_md_FULL.
*)
    unfold_data_at 1%nat.
    rewrite (field_at_data_at _ _ [StructField _md_ctx]); simpl.
    rewrite (field_at_data_at _ _ [StructField _V]); simpl.

    assert (Hfield_md_ctx: forall ctx', isptr ctx' -> field_compatible t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx' -> ctx' = field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx').
    {
      intros ctx'' Hisptr Hfc.
      unfold field_address.
      Check field_compatible_dec.
      destruct (field_compatible_dec t_struct_hmac256drbg_context_st); [|contradiction].
      simpl. change (Int.repr 0) with Int.zero. rewrite offset_val_force_ptr.
      destruct ctx''; inversion Hisptr. reflexivity.
    }
    assert (Hfield_V: forall ctx', isptr ctx' -> field_compatible t_struct_hmac256drbg_context_st [StructField _V] ctx' -> offset_val (Int.repr 12) ctx' = field_address t_struct_hmac256drbg_context_st [StructField _V] ctx').
    {
      intros ctx'' Hisptr Hfc.
      unfold field_address.
      Check field_compatible_dec.
      destruct (field_compatible_dec t_struct_hmac256drbg_context_st); [|contradiction].
      simpl. reflexivity.
    }
    destruct state_abs. destruct md_ctx.
    destruct state as [md_ctx [V' [reseed_counter' [entropy_len' [prediction_resistance' [reseed_interval' [f_entropy' p_entropy']]]]]]].
    simpl in H8.
    assert (Hmdlen_V: md_len = Vint (Int.repr (Zlength V))) by (rewrite H8; assumption).
    simpl; normalize. rewrite <- list_map_compose.
    rewrite <- H8.
    
    forward_call (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx, Zlength key, key, kv) v.
    {
      entailer!.
    }
    {
      (* prove that the (existing) key has the right length *)
      admit (* TODO *).
    }
    subst v.

    forward_call (key, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx, field_address t_struct_hmac256drbg_context_st [StructField _V] ctx, @nil Z, V, kv) v.
    {
      entailer!.
    }
    {
      rewrite H8.
      repeat split; try omega. hnf; auto.
      assumption.
    }

    subst v.
    unfold upd_Znth_in_list.
    simpl.
    unfold sublist. simpl. assert (Int.zero_ext 8 (Int.repr i) = Int.repr i).
    clear - H5 Heqrounds. admit (* TODO *).
    (*
    apply zero_ext_inrange. destruct non_empty_additional. subst. clear - H3.
    SearchAbout Int.unsigned Int.repr.
    rewrite Int.unsigned_repr. hnf; auto. *) 
    forward_call (key, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx, sep, V, [i], kv) v.
    {
      entailer!.
    }
    {
      rewrite H11. simpl. change (Zlength [i]) with 1.
      cancel.
    }
    {
      rewrite H8.
      change (Zlength [i]) with 1.
      repeat split; try omega. hnf; auto.
      unfold general_lemmas.isbyteZ.
      repeat constructor.
      omega. destruct non_empty_additional; subst; omega.
    }
    subst v.
    normalize.
    forward_if (
      PROP  ()
      LOCAL  (temp _sep_value (Vint (Int.repr i));
      temp _rounds (Vint (Int.repr rounds)); temp _md_len md_len;
      temp _ctx ctx; lvar _K (tarray tuchar (Zlength V)) K;
      lvar _sep (tarray tuchar 1) sep; temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv)
      SEP  (`(md_relate (hABS key (V ++ [i] ++ contents)) md_ctx);
      `(data_at Tsh t_struct_md_ctx_st md_ctx
          (field_address t_struct_hmac256drbg_context_st
             [StructField _md_ctx] ctx));
      `(data_at Tsh (tarray tuchar (Zlength [i])) [Vint (Int.repr i)] sep);
      `(K_vector kv);
      `(data_at Tsh (tarray tuchar (Zlength V)) (map Vint (map Int.repr V))
          (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx));
      `(field_at Tsh t_struct_hmac256drbg_context_st
          [StructField _reseed_counter] (Vint (Int.repr reseed_counter)) ctx);
      `(field_at Tsh t_struct_hmac256drbg_context_st
          [StructField _entropy_len] (Vint (Int.repr entropy_len)) ctx);
      `(field_at Tsh t_struct_hmac256drbg_context_st
          [StructField _prediction_resistance] prediction_resistance' ctx);
      `(field_at Tsh t_struct_hmac256drbg_context_st
          [StructField _reseed_interval] (Vint (Int.repr reseed_interval))
          ctx);
      `(field_at Tsh t_struct_hmac256drbg_context_st 
          [StructField _f_entropy] f_entropy' ctx);
      `(field_at Tsh t_struct_hmac256drbg_context_st 
          [StructField _p_entropy] p_entropy' ctx);
      `(data_at Tsh t_struct_mbedtls_md_info info_contents
          (hmac256drbgstate_md_info_pointer
             (md_ctx,
             (map Vint (map Int.repr V),
             (Vint (Int.repr reseed_counter),
             (Vint (Int.repr entropy_len),
             (prediction_resistance',
             (Vint (Int.repr reseed_interval), (f_entropy', p_entropy')))))))));
      `(data_at_ Tsh (tarray tuchar (Zlength V)) K);
      `(data_at Tsh (tarray tuchar (Zlength contents))
          (map Vint (map Int.repr contents)) additional))
    ).
    {
      (* rounds = 2 case *)
      forward_call (key, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx, additional, V ++ [i], contents, kv) v.
      {
        (* prove the parameters match up *)
        entailer!.
      }
      {
        rewrite H1. cancel.
      }
      {
        (* prove the PROP clause matches *)
        rewrite H1 in *. repeat split; try omega.
        rewrite Zlength_app; rewrite H8.
        simpl. clear - H. destruct H. rewrite <- Zplus_assoc; simpl. admit (* TODO *).
        assumption.
      }
      (* prove the post condition of the if statement *)
      rewrite <- app_assoc.
      entailer!.
    }
    {
      (* rounds <> 2 case *)
      forward.
      entailer!.
      destruct contents.
      entailer!.

      (* contents not empty, which is a contradiction *)
      rewrite Zlength_cons in H13.
      destruct (eq_dec (Z.succ (Zlength contents)) 0) as [Zlength_eq | Zlength_neq].
      assert (0 <= Zlength contents) by (apply Zlength_nonneg).
      destruct (Zlength contents); [inversion Zlength_eq| omega | omega].

      assert (Hisptr: isptr additional') by auto.
      destruct (eq_dec additional' nullval) as [additional_null | additional_not_null].
      subst. inversion Hisptr.
      assert (contra: False) by (apply H13; reflexivity); inversion contra.
    }
    rewrite H8.
    forward_call ((V ++ [i] ++ contents), key, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx, K, Tsh, kv) new_key.
    {
      (* prove the parameters match up *)
      entailer!.
    }
    {
      rewrite data_at__memory_block. normalize.
      change (sizeof cenv_cs (tarray tuchar 32)) with 32.
      cancel.
    }
    normalize.
    assert_PROP (isptr K) as HisptrK. entailer!. 
    destruct K; try solve [inversion HisptrK].
    replace_SEP 1 `(UNDER_SPEC.EMPTY (snd (snd md_ctx))). normalize.
    entailer!. apply UNDER_SPEC.FULL_EMPTY.
    forward_call (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx, (Zlength (HMAC256 (V ++ [i] ++ contents) key)), HMAC256 (V ++ [i] ++ contents) key, kv, b, i0) v.
    {
      (* prove the function parameters match up *)
      entailer!. rewrite hmac_common_lemmas.HMAC_Zlength. reflexivity.
    }
    {
      rewrite hmac_common_lemmas.HMAC_Zlength.
      admit (* TODO *).
    }

    subst v.
    forward_call (HMAC256 (V ++ [i] ++ contents) key, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx, field_address t_struct_hmac256drbg_context_st [StructField _V] ctx, @nil Z, V, kv) v.
    {
      (* prove the function parameters match up *)
      entailer!.
    }
    {
      (* prove the function SEP clauses match up *)
      rewrite H8; cancel.
    }
    {
      (* prove the PROP clauses *)
      rewrite H8.
      repeat split; try omega. hnf; auto.
      assumption.
    }
    rewrite H8.
    normalize.
    replace_SEP 2 `(memory_block Tsh (sizeof cenv_cs (tarray tuchar 32)) (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx)); [entailer!; apply data_at_memory_block| ].
    forward_call (V, HMAC256 (V ++ [i] ++ contents) key, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx, field_address t_struct_hmac256drbg_context_st [StructField _V] ctx, Tsh, kv) new_V.
    {
      (* prove the function parameters match up *)
      entailer!.
    }
    {
      simpl; cancel.
    }
    Exists (HMAC256 (V ++ [i] ++ contents) key) (HMAC256 V (HMAC256 (V ++ [i] ++ contents) key))    (HMAC256DRBGabs (hABS (HMAC256 (V ++ [i] ++ contents) key) []) (HMAC256 V (HMAC256 (V ++ [i] ++ contents) key)) reseed_counter entropy_len prediction_resistance reseed_interval).
    entailer!.
    {
      split; [| apply hmac_common_lemmas.HMAC_Zlength].
      (* prove that the new key and value is what we expect *)
      clear - H5 H6; destruct H5; simpl in H6.
      idtac.
      apply HMAC_DRBG_update_round_incremental_Z; assumption.
    }
    unfold update_relate_final_state.
    Exists (md_ctx, (map Vint (map Int.repr (HMAC256 V (HMAC256 (V ++ [i] ++ contents) key))), (Vint (Int.repr reseed_counter), (Vint (Int.repr entropy_len), (prediction_resistance', (Vint (Int.repr reseed_interval), (f_entropy', p_entropy'))))))).
    entailer!.
    unfold hmac256drbgstate_md_FULL.
    unfold_data_at 4%nat.
    unfold hmac256drbg_relate;
    rewrite (field_at_data_at _ _ [StructField _md_ctx]);
    rewrite (field_at_data_at _ _ [StructField _V]); simpl.
    repeat rewrite hmac_common_lemmas.HMAC_Zlength.
    entailer!.
    symmetry; apply list_map_compose.
 (*     (*  (*
    (*
    gather_SEP 0 1 2 3 4 5 6 7.
    replace_SEP 0 `(data_at Tsh t_struct_hmac256drbg_context_st state ctx).
*)
    (*
    forward_call ((field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx), (fst state), l, key, kv).
*) *) *)
    eapply semax_seq'.
    let Frame := fresh "Frame" in
    evar (Frame: list (mpred)).
 match goal with |- @semax ?CS _ _ _ _ _ => 
 eapply (semax_call_id01_wow (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx, (Zlength (HMAC256 (V ++ [i] ++ contents) key)), HMAC256 (V ++ [i] ++ contents) key, kv, b, i0)
 Frame) ;
 [ reflexivity | lookup_spec_and_change_compspecs CS
 | reflexivity | ..(* apply Coq.Init.Logic.I | reflexivity
 | *prove_local2ptree | repeat constructor 
 | try apply local_True_right; entailer!
 | reflexivity
 | prove_local2ptree | repeat constructor 
 | reflexivity | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right at 1 2; cancel
 | cbv beta; extensionality rho; 
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   apply exp_congr; intros ?vret; reflexivity
 | intros; try match goal with  |- extract_trivial_liftx ?A _ =>
        (has_evar A; fail 1) || (repeat constructor)
     end
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto *)
 ] end.
 apply Coq.Init.Logic.I.
 reflexivity.
 lookup_spec_and_change_compspecs CS.

 Focus 2.
 unfold data_block. normalize. unfold fold_right at 1 2; entailer!. cancel.
 simpl. cancel.
 idtac. rewrite H6.
      rewrite list_map_compose. cancel. simpl.
    forward_call_id00_wow ((field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx), (fst state), l, key, kv).
    assert_PROP (spec_hmacNK.has_lengthK l key). admit (* TODO *).
    Print md_reset_spec.
    
    forward_call ((field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx), (fst state), l, key, kv).
    (* TODO *) admit. *)
  }
  unfold update_relate_final_state.
  (* return *)
  forward.

  remember (hmac256drbgabs_key final_state_abs) as key.
  remember (hmac256drbgabs_value final_state_abs) as value.
  (* prove function post condition *)
  Exists K sep key value final_state_abs.
  unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_update.
  rewrite HMAC_DRBG_update_concrete_correct.
  entailer!.
  {
    rewrite H1.
    destruct contents; unfold HMAC_DRBG_update_concrete.
    {
      (* contents = [] *)
      reflexivity.
    }
    {
      repeat rewrite Zlength_map in *.
      destruct (eq_dec (Zlength (z :: contents)) 0) as [Zlength_eq | Zlength_neq].
      rewrite Zlength_cons, Zlength_correct in Zlength_eq; omega.
      destruct (eq_dec additional' nullval) as [additional_eq | additional_neq].
      subst. inversion H10 as [isptr_null H']; inversion isptr_null.
      reflexivity.
    }
  }
  unfold hmac_drbg_update_post.
  Exists final_state.
  entailer!.
  (*
  (* sep_value = 0 *)
  forward.

  (* for( ; sep_value < rounds; sep_value++ ) *)
  remember (hmac256drbgabs_key initial_state_abs) as initial_key.
  remember (hmac256drbgabs_value initial_state_abs) as initial_value.
  (* use forward_for_simple_bound num_iterations *)
  forward_for
    (update_loop_invariant non_empty_additional add_len ctx additional sep K md_len info contents initial_key initial_value initial_state_abs initial_state)
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
    Exists (fst key_value_pair) (snd key_value_pair).
    Intros i key value f.
    unfold update_loop_invariant_SEP.
    unfold hmac256drbg_relate.
    normalize.
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
    unfold update_loop_invariant.
    unfold update_loop_invariant_SEP.

    Intros i key value f.
    rewrite insert_local.
    normalize.
    intros.
    forward.

    (* sep[0] = sep_value; *)
    admit (* TODO *).
  }
  {
    (* prove the pre-incr invariant preserves the invariant *)
    unfold update_loop_pre_incr_invariant.
    unfold update_loop_invariant_SEP.
    admit (* TODO *).    
  }
*)
Qed.