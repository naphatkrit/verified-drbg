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

Definition update_rounds (non_empty_additional: bool): Z :=
  if non_empty_additional then 2 else 1.

Definition update_relate_final_state (ctx: val) (final_state_abs: hmac256drbgabs) :mpred :=
  EX final_state: _,
  (data_at Tsh t_struct_hmac256drbg_context_st final_state ctx) *
  (hmac256drbg_relate final_state_abs final_state).

Definition update_loop_invariant (non_empty_additional: bool) (add_len: Z) (ctx additional sep K md_len info: val) (contents: list int) (old_key old_value: list Z) (state_abs: hmac256drbgabs) (state: hmac256drbgstate) :=
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
        `(data_at_ Tsh (Tstruct _mbedtls_md_info_t noattr) info)
         ).

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
      assert (sizeof cenv_cs (tarray tuchar (Zlength (map Vint contents))) > 0).
      {
        simpl.
        destruct contents.
        assert (contra: False) by (apply H1; reflexivity); inversion contra.
        clear.
        rewrite Zlength_map. rewrite Zlength_cons.
        Check Zlength_nonneg.
        assert (0 <= Zlength contents) by (apply Zlength_nonneg).
        destruct (Zlength contents).
        simpl; omega.
        simpl. admit (* TODO *).
        assert (contra: False) by (apply H; reflexivity); inversion contra.
      }
      apply denote_tc_comparable_split; auto 50 with valid_pointer.
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

  remember (update_rounds non_empty_additional) as rounds. unfold update_rounds in Heqrounds.
  
  forward_if (
      PROP  ()
      LOCAL  (temp _md_len md_len; lvar _K (tarray tuchar 32) K;
      lvar _sep (tarray tuchar 1) sep;
      lvar _info (Tstruct _mbedtls_md_info_t noattr) info;
      temp _additional additional; temp _add_len (Vint (Int.repr add_len));
      temp 128%positive (Vint (Int.repr rounds))
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

  remember (hmac256drbgabs_key initial_state_abs) as initial_key.
  remember (hmac256drbgabs_value initial_state_abs) as initial_value.
  (* for ( sep_value = 0; sep_value < rounds; sep_value++ ) *)
  forward_for_simple_bound rounds (update_loop_invariant non_empty_additional add_len ctx additional sep K md_len info contents initial_key initial_value initial_state_abs initial_state).
  {
    (* Int.min_signed <= 0 <= rounds *)
    rewrite Heqrounds; destruct non_empty_additional; auto.
  }
  {
    (* rounds <= Int.max_signed *)
    rewrite Heqrounds; destruct non_empty_additional; auto.
  }
  {
    (* TODO *) admit.
  }
  {
    (* pre conditions imply loop invariant *)
    unfold update_relate_final_state.
    normalize.
    entailer!.
    {
      split.
      {
        rewrite Zlength_map in *.
        destruct (eq_dec (Zlength contents) 0); destruct (eq_dec additional' nullval); auto.
      }
      {
        (* TODO sep_value, not provable *) admit.
      }
    }
    Exists (hmac256drbgabs_key initial_state_abs) (hmac256drbgabs_value initial_state_abs) initial_state_abs.
    normalize. Exists initial_state.
    entailer!. destruct initial_state_abs; simpl; auto.
  }
  {
    (* loop body *)
    unfold update_relate_final_state.
    normalize.
    intro key.
    normalize.
    intro value.
    normalize.
    intro state_abs.
    normalize.
    intro state.
    (* TODO this should be one call to normalize *)
    normalize.
    forward.
    (* TODO *) admit.
  }
  unfold update_relate_final_state.
  (* return *)
  forward.

  remember (hmac256drbgabs_key final_state_abs) as key.
  remember (hmac256drbgabs_value final_state_abs) as value.
  (* prove function post condition *)
  Exists K sep info key value final_state_abs.
  unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_update.
  rewrite HMAC_DRBG_update_concrete_correct.
  entailer!.
  {
    rewrite H3.
    destruct contents; unfold HMAC_DRBG_update_concrete.
    {
      (* contents = [] *)
      reflexivity.
    }
    {
      rewrite Zlength_map in *.
      destruct (eq_dec (Zlength (i :: contents)) 0) as [Zlength_eq | Zlength_neq].
      rewrite Zlength_cons, Zlength_correct in Zlength_eq; omega.
      destruct (eq_dec additional' nullval) as [additional_eq | additional_neq].
      subst. inversion H7 as [isptr_null H']; inversion isptr_null.
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