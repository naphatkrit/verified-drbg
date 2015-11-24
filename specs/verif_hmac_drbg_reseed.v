Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmac_drbg.
Require Import spec_hmac_drbg.

Lemma sublist_app_exact1:
  forall X (A B: list X), sublist 0 (Zlength A) (A ++ B) = A.
Proof.
  intros.
  pose proof (Zlength_nonneg A).
  rewrite sublist_app1; try omega.
  rewrite sublist_same; auto.
Qed.

Lemma sublist_app_exact2:
  forall X (A B: list X), sublist (Zlength A) (Zlength A + Zlength B) (A ++ B) = B.
Proof.
  intros.
  pose proof (Zlength_nonneg A).
  pose proof (Zlength_nonneg B).
  rewrite sublist_app2; try omega.
  rewrite sublist_same; auto; omega.
Qed.

Lemma data_at_complete_split:
  forall A B p sh,
    field_compatible (tarray tuchar (Zlength A + Zlength B)) [] p ->
    (data_at sh (tarray tuchar (Zlength A + Zlength B)) (A ++ B) p) |-- (data_at sh (tarray tuchar (Zlength A)) A p) * (data_at sh (tarray tuchar (Zlength B)) B (offset_val (Int.repr (Zlength A)) p)).
Proof.
  intros until sh.
  intros Hfield.
  pose proof (Zlength_nonneg A).
  pose proof (Zlength_nonneg B).
  assert_PROP (isptr p) as Hisptr by (destruct Hfield; entailer!).
  destruct p; try solve [inversion Hisptr]; clear Hisptr.
  unfold tarray.
  rewrite split2_data_at_Tarray_tuchar with (n1:=Zlength A); [|auto|rewrite Zlength_app; reflexivity].
  Focus 2.  
  pose proof (Zlength_nonneg A).
  pose proof (Zlength_nonneg B).
  split.
  auto.
  omega.
  rewrite sublist_app_exact1, sublist_app_exact2.
  replace (Zlength A + Zlength B - Zlength A) with (Zlength B) by omega.
  entailer!.
  replace (field_address0 (Tarray tuchar (Zlength A + Zlength B) noattr) [ArraySubsc (Zlength A)] (Vptr b i)) with (Vptr b (Int.add i (Int.repr (Zlength A)))).
  apply derives_refl. 
  rewrite field_address0_offset.
  simpl. replace (0 + 1 * Zlength A) with (Zlength A) by omega. reflexivity.
  destruct Hfield as [Hfield1 [Hfield2 [Hfield3 [Hfield4 [Hfield5 [Hfield6 [Hfield7 Hfield8]]]]]]].
  unfold field_compatible0; repeat split; try assumption; auto; omega.
Qed.

Lemma data_at_complete_split_reverse:
  forall A B p sh,
    field_compatible (tarray tuchar (Zlength A + Zlength B)) [] p ->
    (data_at sh (tarray tuchar (Zlength A)) A p) * (data_at sh (tarray tuchar (Zlength B)) B (offset_val (Int.repr (Zlength A)) p)) |-- (data_at sh (tarray tuchar (Zlength A + Zlength B)) (A ++ B) p).
Proof.
  intros until sh.
  intros Hfield.
  pose proof (Zlength_nonneg A).
  pose proof (Zlength_nonneg B).
  assert_PROP (isptr p) as Hisptr by (destruct Hfield; entailer!).
  destruct p; try solve [inversion Hisptr]; clear Hisptr.
  unfold tarray.
  rewrite split2_data_at_Tarray_tuchar with (n1:=Zlength A) (n:= Zlength A + Zlength B); [|split; omega|rewrite Zlength_app; reflexivity].
  rewrite sublist_app_exact1, sublist_app_exact2.
  replace (Zlength A + Zlength B - Zlength A) with (Zlength B) by omega.
  entailer!.
  replace (field_address0 (Tarray tuchar (Zlength A + Zlength B) noattr) [ArraySubsc (Zlength A)] (Vptr b i)) with (Vptr b (Int.add i (Int.repr (Zlength A)))).
  apply derives_refl. 
  rewrite field_address0_offset.
  simpl. replace (0 + 1 * Zlength A) with (Zlength A) by omega. reflexivity.
  destruct Hfield as [Hfield1 [Hfield2 [Hfield3 [Hfield4 [Hfield5 [Hfield6 [Hfield7 Hfield8]]]]]]].
  unfold field_compatible0; repeat split; try assumption; auto; omega.
Qed.

Lemma body_hmac_drbg_update: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs 
       f_mbedtls_hmac_drbg_reseed hmac_drbg_reseed_spec.
Proof.
  start_function.
  
  name ctx' _ctx.
  name add_len' _len.
  name additional' _additional.

  rename lvar0 into seed.
  destruct initial_state_abs.
  destruct initial_state as [md_ctx' [V' [reseed_counter' [entropy_len' [prediction_resistance' reseed_interval']]]]].
  unfold hmac256drbg_relate.
  normalize.

  (* entropy_len = ctx->entropy_len *)
  forward.

  remember (if zlt 256 add_len then true else false) as add_len_too_high.

  (* if (len > MBEDTLS_HMAC_DRBG_MAX_INPUT ||
        entropy_len + len > MBEDTLS_HMAC_DRBG_MAX_SEED_INPUT) *)
  forward_if (PROP  ()
      LOCAL  (temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
      temp 146%positive (Val.of_bool add_len_too_high);
      gvar sha._K256 kv)
      SEP  (data_at_ Tsh (tarray tuchar 384) seed;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      data_at Tsh t_struct_hmac256drbg_context_st
        (md_ctx',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (prediction_resistance', Vint (Int.repr reseed_interval)))))) ctx;
      md_full md_ctx md_ctx';
      data_at Tsh t_struct_mbedtls_md_info info_contents
        (hmac256drbgstate_md_info_pointer
           (md_ctx',
           (map Vint (map Int.repr V),
           (Vint (Int.repr reseed_counter),
           (Vint (Int.repr entropy_len),
           (prediction_resistance', Vint (Int.repr reseed_interval)))))));
      Stream s; spec_sha.K_vector kv)
  ).
  {
    rewrite zlt_true in Heqadd_len_too_high by assumption.
    forward.
    entailer!.    
  }
  {
    rewrite zlt_false in Heqadd_len_too_high by assumption.
    forward.
    entailer!.
    rewrite <- H8.
    simpl in H2. subst entropy_len.
    unfold Int.ltu.
    destruct (zlt (Int.unsigned (Int.repr 384))
                 (Int.unsigned (Int.repr (32 + Zlength contents)))).
    rewrite Int.unsigned_repr_eq in l.
    rewrite Zmod_small in l by auto.
    rewrite Int.unsigned_repr_eq in l.
    rewrite Zmod_small in l.
    omega.
    assert (0 <= Zlength contents <= 256) by omega.
    rewrite hmac_pure_lemmas.IntModulus32. simpl.
    change (Z.pow_pos 2 32) with 4294967296.
    omega.
    reflexivity.
  }

  forward_if (PROP  (add_len_too_high = false)
      LOCAL  (temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
      gvar sha._K256 kv)
      SEP  (data_at_ Tsh (tarray tuchar 384) seed;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      data_at Tsh t_struct_hmac256drbg_context_st
        (md_ctx',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (prediction_resistance', Vint (Int.repr reseed_interval)))))) ctx;
      md_full md_ctx md_ctx';
      data_at Tsh t_struct_mbedtls_md_info info_contents
        (hmac256drbgstate_md_info_pointer
           (md_ctx',
           (map Vint (map Int.repr V),
           (Vint (Int.repr reseed_counter),
           (Vint (Int.repr entropy_len),
           (prediction_resistance', Vint (Int.repr reseed_interval)))))));
      Stream s; spec_sha.K_vector kv)
  ).
  {
    forward.
    unfold hmac_drbg_update_post, get_stream_reseed_result, hmac256drbg_relate.
    Exists seed (HMAC256DRBGabs md_ctx V reseed_counter entropy_len prediction_resistance reseed_interval) (Vint (Int.neg (Int.repr 5))) (md_ctx',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (prediction_resistance', Vint (Int.repr reseed_interval)))))).
    destruct md_ctx.
    rewrite andb_negb_r.
    destruct (zlt 256 (Zlength contents)); inv Heqadd_len_too_high.
    rewrite Z.gtb_ltb.
    assert (Hlt: 256 <? Zlength contents = true) by (apply Z.ltb_lt; assumption).
    rewrite Hlt.
    entailer!.
  }
  {
    forward.
    entailer!.
  }
  assert_PROP (0 <= Zlength contents <= 256) as HZlength.
  {
    entailer!. destruct (zlt 256 (Zlength contents)); inv H7. omega.
  }

  (* memset( seed, 0, MBEDTLS_HMAC_DRBG_MAX_SEED_INPUT ); *)
  forward_call (Tsh, seed, 384, Int.zero).
  {
    rewrite data_at__memory_block.
    change (sizeof cenv_cs (tarray tuchar 384)) with 384.
    entailer!.
  }
  Intros vret; subst vret.

  assert_PROP (field_compatible (tarray tuchar 384) [] seed) as Hfield by entailer!.
  replace_SEP 0 ((data_at Tsh (tarray tuchar entropy_len)
         (list_repeat (Z.to_nat entropy_len) (Vint Int.zero)) seed) * (data_at Tsh (tarray tuchar (384 - entropy_len))
         (list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero)) (offset_val (Int.repr entropy_len) seed))).
  {
    simpl in H2.
    subst entropy_len.
    replace (384 - 32) with 352 by omega.
    change (list_repeat (Z.to_nat 384) (Vint Int.zero)) with ((list_repeat (Z.to_nat 32) (Vint Int.zero)) ++ (list_repeat (Z.to_nat 352) (Vint Int.zero))).
    remember (list_repeat (Z.to_nat 32) (Vint Int.zero)) as A.
    remember (list_repeat (Z.to_nat 352) (Vint Int.zero)) as B.                            
    assert (HlengthA: Zlength A = 32) by (subst A; reflexivity).
    assert (HlengthB: Zlength B = 352) by (subst B; reflexivity).
    clear HeqA HeqB.
    change 384 with (32 + 352) in *.
    rewrite <- HlengthA, <- HlengthB in *.
    entailer!.
    apply data_at_complete_split.
    assumption.
  }
  normalize.

  replace_SEP 0 (memory_block Tsh entropy_len seed).
  {
    entailer!.
    simpl in H2; subst entropy_len.
    apply data_at_memory_block.
  }

  (* get_entropy(seed, entropy_len ) *)
  forward_call (Tsh, s, seed, entropy_len).
  {
    simpl in H2; subst entropy_len.
    auto.
  }
  Intros vret.

  gather_SEP 1 2.
  replace_SEP 0 (data_at Tsh (tarray tuchar 384)
         ((map Vint
            (map Int.repr
               (entropy.get_bytes_helper (Z.to_nat entropy_len) s
                  (Z.to_nat entropy_len)))) ++ (list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero))) seed).
  {
    unfold entropy.get_bytes.
    change (fst
               (entropy.get_bytes_helper (Z.to_nat entropy_len) s
                  (Z.to_nat entropy_len),
                fun i : nat => s (Z.to_nat entropy_len + i)%nat)) with
    (entropy.get_bytes_helper (Z.to_nat entropy_len) s
                  (Z.to_nat entropy_len)).
    remember (map Vint
            (map Int.repr
               (entropy.get_bytes_helper (Z.to_nat entropy_len) s
                  (Z.to_nat entropy_len)))) as A.
    remember (list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero)) as B.    
    simpl in H2.
    subst entropy_len.
    change (384 - 32) with 352.
    assert_PROP (Zlength A = 32) as HlengthA by entailer!.
    assert_PROP (Zlength B = 352) as HlengthB by entailer!.
    clear HeqA HeqB.
    change 384 with (32 + 352) in *.
    rewrite <- HlengthA, <- HlengthB in *.
    entailer!.
    apply data_at_complete_split_reverse.
    assumption.
  }
  
  (* if( get_entropy(seed, entropy_len ) != 0 ) *)
  forward_if (
      PROP  (vret = Vzero)
      LOCAL  (
      temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
      gvar sha._K256 kv)
      SEP  (
        data_at Tsh (tarray tuchar 384)
         (map Vint
            (map Int.repr
               (entropy.get_bytes_helper (Z.to_nat entropy_len) s
                  (Z.to_nat entropy_len))) ++
          list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero)) seed;
        Stream (fun i : nat => s (Z.to_nat entropy_len + i)%nat);
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      data_at Tsh t_struct_hmac256drbg_context_st
        (md_ctx',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (prediction_resistance', Vint (Int.repr reseed_interval)))))) ctx;
      md_full md_ctx md_ctx';
      data_at Tsh t_struct_mbedtls_md_info info_contents
        (hmac256drbgstate_md_info_pointer
           (md_ctx',
           (map Vint (map Int.repr V),
           (Vint (Int.repr reseed_counter),
           (Vint (Int.repr entropy_len),
           (prediction_resistance', Vint (Int.repr reseed_interval)))))));
      spec_sha.K_vector kv)
  ).
  {
    (* != 0 case *)
    clear - H7 H8.
    unfold return_value_relate_entropy_result in H7.
    unfold entropy.get_entropy in H7. rewrite H7 in H8.
    inversion H8.
    (* TODO this is a dummy case, since our entropy function never fails *)
  }
  {
    (* = 0 case *)
    forward.
    entailer!.
  }

  (* seedlen = entropy_len; *)
  forward.

  remember (if eq_dec additional nullval then false else if eq_dec add_len 0 then false else true) as non_empty_additional.

  forward_if (
      PROP  ()
      LOCAL  (temp _seedlen (Vint (Int.repr entropy_len));
      temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
      temp 148%positive (Val.of_bool non_empty_additional);
      gvar sha._K256 kv)
      SEP  (
        data_at Tsh (tarray tuchar 384)
         (map Vint
            (map Int.repr
               (entropy.get_bytes_helper (Z.to_nat entropy_len) s
                  (Z.to_nat entropy_len))) ++
          list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero)) seed;
        Stream (fun i : nat => s (Z.to_nat entropy_len + i)%nat);
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      data_at Tsh t_struct_hmac256drbg_context_st
        (md_ctx',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (prediction_resistance', Vint (Int.repr reseed_interval)))))) ctx;
      md_full md_ctx md_ctx';
      data_at Tsh t_struct_mbedtls_md_info info_contents
        (hmac256drbgstate_md_info_pointer
           (md_ctx',
           (map Vint (map Int.repr V),
           (Vint (Int.repr reseed_counter),
           (Vint (Int.repr entropy_len),
           (prediction_resistance', Vint (Int.repr reseed_interval)))))));
      spec_sha.K_vector kv)
  ).
  {
    (* TODO this should be easy with weakly valid pointer *)
    unfold denote_tc_comparable.
    assert_PROP (isptr additional) as Hisptr by entailer!. destruct additional; try solve [inversion Hisptr]; clear Hisptr.
    unfold weak_valid_pointer.
    entailer!.
    admit.
  }
  {
    forward.
    entailer!.
    rewrite <- H10.
    destruct (eq_dec additional' nullval) as [additional_pos | additional_neg].
    subst additional'; assert (contra: False) by (apply H8; reflexivity); inversion contra.
    destruct (eq_dec (Zlength contents) 0) as [Zlength_pos | Zlength_neg].
    rewrite Zlength_pos. reflexivity.
    rewrite Int.eq_false. reflexivity.
    intros contra.
    apply repr_inj_unsigned in contra; omega.
  }
  {
    forward.
    entailer!.
    destruct (eq_dec nullval nullval).
    reflexivity.
    assert (contra: False) by auto; inversion contra.
  }

  forward_if (
      PROP  ()
      LOCAL  (temp _seedlen (Vint (Int.repr (entropy_len + Zlength contents)));
      temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
      gvar sha._K256 kv)
      SEP 
      (data_at Tsh (tarray tuchar 384)
         (map Vint
            (map Int.repr
               (entropy.get_bytes_helper (Z.to_nat entropy_len) s
                  (Z.to_nat entropy_len))) ++ (map Vint (map Int.repr contents)) ++
          list_repeat (Z.to_nat (384 - entropy_len - Zlength contents)) (Vint Int.zero)) seed;
      Stream (fun i : nat => s (Z.to_nat entropy_len + i)%nat);
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      data_at Tsh t_struct_hmac256drbg_context_st
        (md_ctx',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (prediction_resistance', Vint (Int.repr reseed_interval)))))) ctx;
      md_full md_ctx md_ctx';
      data_at Tsh t_struct_mbedtls_md_info info_contents
        (hmac256drbgstate_md_info_pointer
           (md_ctx',
           (map Vint (map Int.repr V),
           (Vint (Int.repr reseed_counter),
           (Vint (Int.repr entropy_len),
           (prediction_resistance', Vint (Int.repr reseed_interval)))))));
      spec_sha.K_vector kv)
  ).
  {
(*
    eapply semax_seq'.
    {
      evar (Frame: list mpred).
      change (_memcpy) with (sha._memcpy).
      Set Printing Implicit.
      eapply(call_memcpy_tuchar
      (*dst*) Tsh (tarray tuchar 384) [] entropy_len
                      (map Vint
               (map Int.repr
                  (entropy.get_bytes_helper (Z.to_nat entropy_len) s
                     (Z.to_nat entropy_len))) ++
             list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero)) seed
      (*src*) Tsh (tarray tuchar (Zlength contents)) [] 0
                      (map Int.repr contents)
                      additional
      (*len*) (Zlength contents)
           Frame).

    } *)
    replace_SEP 0 ((data_at Tsh (tarray tuchar entropy_len)
         (map Vint
            (map Int.repr
               (entropy.get_bytes_helper (Z.to_nat entropy_len) s
                  (Z.to_nat entropy_len)))) seed) * (data_at Tsh (tarray tuchar (384 - entropy_len))
         (list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero)) (offset_val (Int.repr entropy_len) seed))).
    {
      simpl in H2.
      subst entropy_len.
      replace (384 - 32) with 352 by omega.
      remember (map Vint
         (map Int.repr
            (entropy.get_bytes_helper (Z.to_nat 32) s (Z.to_nat 32)))) as A.
      remember (list_repeat (Z.to_nat 352) (Vint Int.zero)) as B.
      assert (HlengthA: Zlength A = 32) by (subst A; reflexivity).
      assert (HlengthB: Zlength B = 352) by (subst B; reflexivity).
      clear HeqA HeqB.
      change 384 with (32 + 352) in *.
      rewrite <- HlengthA, <- HlengthB in *.
      entailer!.
      apply data_at_complete_split.
      assumption.
    }
    normalize.
    assert_PROP (isptr seed) as Hisptr by entailer!. destruct seed; try solve [inversion Hisptr]; change (offset_val (Int.repr entropy_len) (Vptr b i)) with (Vptr b (Int.add i (Int.repr entropy_len))).
    assert_PROP (field_compatible (Tarray tuchar (384 - entropy_len) noattr) 
          [] (Vptr b (Int.add i (Int.repr entropy_len)))) by entailer!.
    replace_SEP 1 ((data_at Tsh (tarray tuchar (Zlength contents))
         (list_repeat (Z.to_nat (Zlength contents)) (Vint Int.zero)) (Vptr b (Int.add i (Int.repr entropy_len)))) * (data_at Tsh (tarray tuchar (384 - entropy_len - Zlength contents))
         (list_repeat (Z.to_nat (384 - entropy_len - Zlength contents)) (Vint Int.zero)) (offset_val (Int.repr (Zlength contents)) (Vptr b (Int.add i (Int.repr entropy_len)))))).
    {
      simpl in H2. subst entropy_len.
      replace (384 - 32) with 352 by omega.
      assert (Hsplit: list_repeat (Z.to_nat 352) (Vint Int.zero) = list_repeat (Z.to_nat (Zlength contents)) (Vint Int.zero) ++ list_repeat (Z.to_nat (352 - (Zlength contents))) (Vint Int.zero)).
      {
        rewrite list_repeat_app.
        rewrite <- Z2Nat.inj_add; try omega.
        replace (Zlength contents + (352 - Zlength contents)) with 352 by omega.
        reflexivity.
      }
      rewrite Hsplit.
      remember (list_repeat (Z.to_nat (Zlength contents)) (Vint Int.zero)) as A.
      remember (list_repeat (Z.to_nat (352 - Zlength contents)) (Vint Int.zero)) as B.
      assert (HlengthA: Zlength A = Zlength contents) by (subst; apply sublist.Zlength_list_repeat; apply Zlength_nonneg).
      assert (HlengthB: Zlength B = 352 - Zlength contents) by (
      subst; apply sublist.Zlength_list_repeat; omega).
      clear HeqA HeqB.
      replace 352 with (Zlength contents + (352 - Zlength contents)) by omega.
      rewrite <- HlengthA, <- HlengthB in *.
      replace (Zlength A + Zlength B - Zlength A) with (Zlength B) by omega.
      remember (Vptr b (Int.add i (Int.repr 32))) as seed'.
      clear Heqseed'.
      entailer!.
      apply data_at_complete_split.
      assumption.
    }
    normalize.
    replace_SEP 0 (memory_block Tsh (Zlength contents) (Vptr b (Int.add i (Int.repr entropy_len)))).
    entailer!. replace (Zlength contents) with (sizeof cenv_cs (tarray tuchar (Zlength contents))) at 2. apply data_at_memory_block. simpl. rewrite Zmax0r by omega. omega.
    forward_call ((Tsh, Tsh), (Vptr b (Int.add i (Int.repr entropy_len))), additional, Zlength contents, map Int.repr contents).
    {
      (* type checking *)
      unfold lvar in H11.
      unfold eval_var.
      destruct (Map.get (ve_of rho) _seed); [|inversion H11].
      destruct p.
      destruct (eqb_type (tarray tuchar 384)); [|inversion H11].
      simpl. constructor.
    }
    {
      (* match up function parameter *)
      simpl in H2; rewrite H2.
      entailer!.
    }
    {
      (* match up SEP clauses *)
      change (fst (Tsh, Tsh)) with Tsh;
      change (snd (Tsh, Tsh)) with Tsh.
      change (@data_at spec_sha.CompSpecs Tsh (tarray tuchar (@Zlength Z contents))
         (@map int val Vint (@map Z int Int.repr contents)) additional) with (@data_at hmac_drbg_compspecs.CompSpecs Tsh (tarray tuchar (@Zlength Z contents))
         (@map int val Vint (@map Z int Int.repr contents)) additional).
      rewrite H1.
      cancel.
    }
    {
      (* prove the PROP clauses *)
      repeat split; auto; omega.
    }
    Intros memcpy_vret. subst memcpy_vret.
    forward.
    change (fst (Tsh, Tsh)) with Tsh;
    change (snd (Tsh, Tsh)) with Tsh.
    change (@data_at spec_sha.CompSpecs Tsh (tarray tuchar (@Zlength Z contents))
         (@map int val Vint (@map Z int Int.repr contents)) additional) with (@data_at hmac_drbg_compspecs.CompSpecs Tsh (tarray tuchar (@Zlength Z contents))
         (@map int val Vint (@map Z int Int.repr contents)) additional).
    gather_SEP 1 2.
    replace_SEP 0 (data_at Tsh (tarray tuchar (384 - entropy_len)) ((map Vint (map Int.repr contents)) ++ (list_repeat (Z.to_nat (384 - entropy_len - Zlength contents)) (Vint Int.zero))) (Vptr b (Int.add i (Int.repr entropy_len)))).
    {
      simpl in H2; subst entropy_len.
      replace (384 - 32) with 352 by omega.
      remember (map Vint (map Int.repr contents)) as A.
      remember (list_repeat (Z.to_nat (352 - Zlength contents)) (Vint Int.zero)) as B.
      assert (HlengthA: Zlength A = Zlength contents) by (subst; repeat rewrite Zlength_map; reflexivity).
      assert (HlengthB: Zlength B = 352 - Zlength contents) by (
      subst; apply sublist.Zlength_list_repeat; omega).
      clear HeqA HeqB.
      replace 352 with (Zlength contents + (352 - Zlength contents)) by omega.
      rewrite <- HlengthA, <- HlengthB in *.
      replace (Zlength A + Zlength B - Zlength A) with (Zlength B) by omega.
      remember (Vptr b (Int.add i (Int.repr 32))) as seed'.
      clear Heqseed'.
      entailer!.
      apply data_at_complete_split_reverse.
      rewrite HlengthA, HlengthB.
      replace (Zlength contents + (352 - Zlength A)) with 352 by omega.
      replace (384 - 32) with 352 in H9 by omega.
      assumption.
    }
    change (Vptr b (Int.add i (Int.repr entropy_len))) with (offset_val (Int.repr entropy_len) (Vptr b i)). remember (Vptr b i) as seed; clear Heqseed.
    gather_SEP 2 0.
    replace_SEP 0 (data_at Tsh (tarray tuchar 384) ((map Vint
         (map Int.repr
            (entropy.get_bytes_helper (Z.to_nat entropy_len) s
               (Z.to_nat entropy_len)))) ++ (map Vint (map Int.repr contents) ++
       list_repeat (Z.to_nat (384 - entropy_len - Zlength contents))
         (Vint Int.zero))) seed).
    {
      simpl in H2;
      subst entropy_len.
      replace (384 - 32) with 352 by omega.
      remember (map Vint
         (map Int.repr
            (entropy.get_bytes_helper (Z.to_nat 32) s (Z.to_nat 32)))) as A.
      remember (map Vint (map Int.repr contents) ++
       list_repeat (Z.to_nat (352 - Zlength contents))
         (Vint Int.zero)) as B.
      assert (HlengthA: Zlength A = 32) by (subst A; reflexivity).
      assert_PROP (Zlength B = 352) as HlengthB by entailer!.
      clear HeqA HeqB.
      change 384 with (32 + 352) in *.
      rewrite <- HlengthA, <- HlengthB in *.
      entailer!.
      apply data_at_complete_split_reverse.
      assumption.
    }
    entailer!.
  }
  {
    forward.
    assert_PROP (contents = []).
    {
      destruct (eq_dec additional nullval). entailer!. destruct H16 as [contra H16']; inversion contra.
      destruct (eq_dec add_len 0). entailer!. destruct contents; [reflexivity|]. rewrite Zlength_correct in e; simpl in e. inversion e.
      rewrite H8 in Heqnon_empty_additional. inversion Heqnon_empty_additional.
    }
    subst contents.
    change (Zlength []) with 0.
    replace (384 - entropy_len - 0) with (384 - entropy_len) by omega.
    entailer!.
  }
  admit (* TODO *).
Qed.
