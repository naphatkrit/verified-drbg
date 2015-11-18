Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmac_drbg.
Require Import HMAC256_DRBG_functional_prog.
Require Import sha.spec_hmacNK.
Require Import sha.funspec_hmacNK.
Require Import sha.general_lemmas.

(* mocked_md *)
Require Import sha.HMAC256_functional_prog.
Require Import sha.spec_sha.

Require Import hmac_drbg_compspecs.

Module UNDER_SPEC := OPENSSL_HMAC_ABSTRACT_SPEC.

Inductive HABS := hABS: forall (key data:list Z), HABS.

Definition mdstate: Type := (val * (val * val))%type.

Definition md_info_state: Type := val%type.

Definition t_struct_md_ctx_st := Tstruct _mbedtls_md_context_t noattr.

Definition convert_abs (h: HABS): UNDER_SPEC.HABS :=
  match h with hABS key data => UNDER_SPEC.hABS key data end.

Definition md_relate (h: HABS) (r:mdstate) :=
  UNDER_SPEC.REP (convert_abs h) (snd (snd r)).

Definition md_full (h: HABS) (r:mdstate) :=
  match h with hABS key _ => UNDER_SPEC.FULL key (snd (snd r)) end.

Definition md_get_size_spec :=
  DECLARE _mbedtls_md_get_size
   WITH u:unit
   PRE [ _md_info OF tptr (Tstruct _mbedtls_md_info_t noattr)]
         PROP ()
         LOCAL ()
         SEP ()
  POST [ tuchar ] 
     PROP ()
     LOCAL (temp ret_temp (Vint (Int.repr (Z.of_nat SHA256.DigestLength))))
     SEP ().
 
Definition md_reset_spec :=
  DECLARE _mbedtls_md_hmac_reset
   WITH c : val, r: mdstate, key:list Z, kv:val
   PRE [ _ctx OF tptr (Tstruct _mbedtls_md_context_t noattr)]
         PROP ()
         LOCAL (temp _ctx c; gvar sha._K256 kv)
         SEP (
        (UNDER_SPEC.FULL key (snd (snd r))); (data_at Tsh (Tstruct _mbedtls_md_context_t noattr) r c); (K_vector kv))
  POST [ tint ] 
     PROP ()
     LOCAL (temp ret_temp (Vint (Int.zero)))
     SEP (
       (md_relate (hABS key nil) r);
       (data_at Tsh (Tstruct _mbedtls_md_context_t noattr) r c);
       (K_vector kv)
         ).

Definition md_starts_spec :=
  DECLARE _mbedtls_md_hmac_starts
   WITH c : val, r: mdstate, l:Z, key:list Z, kv:val, b:block, i:Int.int
   PRE [ _ctx OF tptr t_struct_md_ctx_st,
         _key OF tptr tuchar,
         _keylen OF tuint ]
         PROP (has_lengthK l key; Forall isbyteZ key)
         LOCAL (temp _ctx c; temp _key (Vptr b i); temp _keylen (Vint (Int.repr l));
                gvar sha._K256 kv)
         SEP ((UNDER_SPEC.EMPTY (snd (snd r)));
              (data_at Tsh t_struct_md_ctx_st r c);
              (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr b i)); (K_vector kv))
  POST [ tint ] 
     PROP (Forall isbyteZ key)
     LOCAL (temp ret_temp (Vint (Int.zero)))
     SEP ((md_relate (hABS key nil) r);
          (data_at Tsh t_struct_md_ctx_st r c);
          (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr b i));
          (K_vector kv)
         ).

Definition md_update_spec :=
  DECLARE _mbedtls_md_hmac_update
   WITH key: list Z, c : val, r:mdstate, d:val, data:list Z, data1:list Z, kv:val
   PRE [ _ctx OF tptr t_struct_md_ctx_st, 
         _input OF tptr tuchar, 
         _ilen OF tuint]
         PROP (0 <= Zlength data1 <= Int.max_unsigned;
               Zlength data1 + Zlength data + 64 < two_power_pos 61;
               Forall isbyteZ data1)
         LOCAL (temp _ctx c; temp _input d; temp  _ilen (Vint (Int.repr (Zlength data1)));
                gvar sha._K256 kv)
         SEP((md_relate (hABS key data) r);
             (data_at Tsh t_struct_md_ctx_st r c);
             (data_at Tsh (tarray tuchar (Zlength data1)) (map Vint (map Int.repr data1)) d); (K_vector kv))
  POST [ tint ] 
          PROP (Forall isbyteZ data1) 
          LOCAL (temp ret_temp (Vint (Int.zero)))
          SEP((md_relate (hABS key (data ++ data1)) r);
              (data_at Tsh t_struct_md_ctx_st r c); 
              (data_at Tsh (tarray tuchar (Zlength data1)) (map Vint (map Int.repr data1)) d);(K_vector kv)).

Definition md_final_spec :=
  DECLARE _mbedtls_md_hmac_finish
   WITH data:list Z, key:list Z, c : val, r:mdstate, md:val, shmd: share, kv:val
   PRE [ _ctx OF tptr t_struct_md_ctx_st,
         _output OF tptr tuchar ]
       PROP (writable_share shmd) 
       LOCAL (temp _output md; temp _ctx c;
              gvar sha._K256 kv)
       SEP((md_relate (hABS key data) r);
           (data_at Tsh t_struct_md_ctx_st r c);
           (K_vector kv);
           (memory_block shmd 32 md))
  POST [ tint ] 
          PROP (Forall isbyteZ (HMAC256 data key)) 
          LOCAL (temp ret_temp (Vint (Int.zero)))
          SEP((K_vector kv);
              (UNDER_SPEC.FULL key (snd (snd r)));
              (data_at Tsh t_struct_md_ctx_st r c);
              (data_at shmd (tarray tuchar (Zlength (HMAC256 data key))) (map Vint (map Int.repr (HMAC256 data key))) md)).
(* end mocked_md *)

Inductive hmac256drbgabs :=
  HMAC256DRBGabs: forall (md_ctx: HABS) (V: list Z) (reseed_counter entropy_len: Z) (prediction_resistance: bool) (reseed_interval: Z), hmac256drbgabs.

Definition hmac256drbgstate: Type := (mdstate * (list val * (val * (val * (val * (val * (val * val)))))))%type.

Definition hmac256drbg_relate (a: hmac256drbgabs) (r: hmac256drbgstate) : mpred :=
  match a with HMAC256DRBGabs md_ctx V reseed_counter entropy_len prediction_resistance reseed_interval =>
               match r with (md_ctx', (V', (reseed_counter', (entropy_len', (prediction_resistance', (reseed_interval', (f_entropy', p_entropy'))))))) =>
                            md_full md_ctx md_ctx'
                                      && !! (
                                        map Vint (map Int.repr V) = V'
                                        /\ Vint (Int.repr reseed_counter) = reseed_counter'
                                        /\ Vint (Int.repr entropy_len) = entropy_len'
                                        /\ Vint (Int.repr reseed_interval) = reseed_interval'
                                        /\ if prediction_resistance then (prediction_resistance' <> Vint (Int.repr 0)) else (prediction_resistance' = Vint (Int.repr 0))
                                      )
               end
  end.

Definition hmac256drbgstate_md_FULL key (r: hmac256drbgstate) : mpred :=
  UNDER_SPEC.FULL key (snd (snd (fst r))).

Definition hmac256drbgabs_value (a: hmac256drbgabs): list Z :=
  match a with HMAC256DRBGabs _ V _ _ _ _ => V end.

Definition hmac256drbgabs_key (a: hmac256drbgabs): list Z :=
  match a with HMAC256DRBGabs (hABS key _) _ _ _ _ _ => key end.

Definition hmac256drbgabs_update_value (a: hmac256drbgabs) (new_value: list Z): hmac256drbgabs :=
  match a with HMAC256DRBGabs (hABS key data) _ reseed_counter entropy_len prediction_resistance reseed_interval => HMAC256DRBGabs (hABS key data) new_value reseed_counter entropy_len prediction_resistance reseed_interval end.

Definition hmac256drbgabs_update_key (a: hmac256drbgabs) (new_key: list Z): hmac256drbgabs :=
  match a with HMAC256DRBGabs (hABS _ data) V reseed_counter entropy_len prediction_resistance reseed_interval => HMAC256DRBGabs (hABS new_key data) V reseed_counter entropy_len prediction_resistance reseed_interval end.

Definition hmac256drbgabs_empty_md (a: hmac256drbgabs): Prop :=
  match a with
    | HMAC256DRBGabs (hABS _ nil) _ _ _ _ _ => True
    | HMAC256DRBGabs _ _ _ _ _ _ => False
  end.

Definition hmac256drbgabs_make_empty_md (a: hmac256drbgabs): hmac256drbgabs :=
  match a with HMAC256DRBGabs (hABS key _) V reseed_counter entropy_len prediction_resistance reseed_interval => HMAC256DRBGabs (hABS key nil) V reseed_counter entropy_len prediction_resistance reseed_interval end.

Definition hmac256drbgabs_metadata_same (a: hmac256drbgabs) (b: hmac256drbgabs): Prop :=
  match a with HMAC256DRBGabs _ _ reseed_counter entropy_len prediction_resistance reseed_interval =>
               match b with HMAC256DRBGabs _ _ reseed_counter' entropy_len' prediction_resistance' reseed_interval' =>
                            reseed_counter = reseed_counter'
                            /\ entropy_len = entropy_len'
                            /\ prediction_resistance = prediction_resistance'
                            /\ reseed_interval = reseed_interval'
               end
  end.

Definition hmac256drbgstate_md_info_pointer (a: hmac256drbgstate): val := fst (fst a).

Definition t_struct_mbedtls_md_info := Tstruct _mbedtls_md_info_t noattr.

Definition t_struct_hmac256drbg_context_st := Tstruct _mbedtls_hmac_drbg_context noattr.

Definition hmac_drbg_update_post (final_state_abs: hmac256drbgabs) (ctx: val) (info_contents: reptype t_struct_mbedtls_md_info): mpred :=
  EX final_state: hmac256drbgstate,
                  (data_at Tsh t_struct_hmac256drbg_context_st final_state ctx) *
                  (data_at Tsh t_struct_mbedtls_md_info info_contents (hmac256drbgstate_md_info_pointer final_state)) *
                  (hmac256drbg_relate final_state_abs final_state).

Definition hmac_drbg_update_spec :=
  DECLARE _mbedtls_hmac_drbg_update
   WITH contents: list Z,
        additional: val, add_len: Z,
        ctx: val, initial_state: hmac256drbgstate,
        initial_state_abs: hmac256drbgabs,
        kv: val, info_contents: md_info_state
    PRE [ _ctx OF (tptr t_struct_hmac256drbg_context_st), _additional OF (tptr tuchar), _add_len OF tuint ]
       PROP (
         0 <= add_len <= Int.max_unsigned;
         Zlength (hmac256drbgabs_value initial_state_abs) = Z.of_nat SHA256.DigestLength;
         add_len = Zlength contents;
         Forall isbyteZ (hmac256drbgabs_value initial_state_abs);
         Forall isbyteZ contents
       )
       LOCAL (temp _ctx ctx; temp _additional additional; temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv)
       SEP (
         (data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional);
         (data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx);
         (hmac256drbg_relate initial_state_abs initial_state);
         (data_at Tsh t_struct_mbedtls_md_info info_contents (hmac256drbgstate_md_info_pointer initial_state));
         (K_vector kv)
           )
    POST [ tvoid ]
       EX key': list Z, EX value': list Z, EX final_state_abs:_,
       PROP (
           (key', value') = HMAC256_DRBG_update contents (hmac256drbgabs_key initial_state_abs) (hmac256drbgabs_value initial_state_abs);
           key' = hmac256drbgabs_key final_state_abs;
           value' = hmac256drbgabs_value final_state_abs;
           hmac256drbgabs_metadata_same final_state_abs initial_state_abs;
           Zlength value' = Z.of_nat SHA256.DigestLength;
           add_len = Zlength contents;
           Forall isbyteZ value';
           Forall isbyteZ contents
         )
       LOCAL ()
       SEP (
         (hmac_drbg_update_post final_state_abs ctx info_contents);
         (data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional);
         (K_vector kv)
       ).
(* TODO isbyte, data_block *)

Definition HmacDrbgVarSpecs : varspecs := (sha._K256, tarray tuint 64)::nil.

Definition HmacDrbgFunSpecs : funspecs := 
  hmac_drbg_update_spec::
  md_reset_spec::md_final_spec::md_update_spec::md_starts_spec::
  md_get_size_spec::
  OPENSSL_HMAC_ABSTRACT_SPEC.hmac_update_spec::
  OPENSSL_HMAC_ABSTRACT_SPEC.hmac_final_spec::
  OPENSSL_HMAC_ABSTRACT_SPEC.hmac_reset_spec::
  OPENSSL_HMAC_ABSTRACT_SPEC.hmac_starts_spec::
  memcpy_spec_data_at:: memset_spec::
  sha256init_spec::sha256update_spec::sha256final_spec::(*SHA256_spec::*)
  HMAC_Init_spec:: HMAC_Update_spec::HMAC_Cleanup_spec::
  HMAC_Final_spec:: HMAC_spec ::nil.

Lemma hmac256drbgabs_update_key_ident:
  forall a key, key = hmac256drbgabs_key a -> hmac256drbgabs_update_key a key = a.
Proof.
  intros.
  destruct a; destruct md_ctx.
  simpl in H; subst.
  reflexivity.
Qed.

Lemma hmac256drbgabs_update_value_ident:
  forall a value, value = hmac256drbgabs_value a -> hmac256drbgabs_update_value a value = a.
Proof.
  intros.
  destruct a; destruct md_ctx.
  simpl in H; subst.
  reflexivity.
Qed.

Lemma hmac256drbgabs_update_key_update_value_commute:
  forall a key value, hmac256drbgabs_update_value (hmac256drbgabs_update_key a key) value = hmac256drbgabs_update_key (hmac256drbgabs_update_value a value) key.
Proof.
  destruct a. destruct md_ctx.
  reflexivity.
Qed.

Lemma hmac256drbgabs_update_key_value_ident:
  forall a1 a2 key value, key = hmac256drbgabs_key a1 -> value = hmac256drbgabs_value a1 -> hmac256drbgabs_metadata_same a1 a2 -> hmac256drbgabs_empty_md a1 -> hmac256drbgabs_empty_md a2 -> hmac256drbgabs_update_key (hmac256drbgabs_update_value a2 value) key = a1.
Proof.
  intros.
  destruct a1, a2. destruct md_ctx, md_ctx0.
  simpl. hnf in H1.
  destruct H1 as [H'  [H'' [H''' H'''']]].
  unfold hmac256drbgabs_empty_md in H2, H3.
  destruct data; try solve [inversion H2].
  destruct data0; try solve [inversion H3].
  subst.
  reflexivity.
Qed.

Lemma hmac256drbgabs_update_key_md_empty:
  forall a key, hmac256drbgabs_empty_md a -> hmac256drbgabs_empty_md (hmac256drbgabs_update_key a key).
Proof.
  intros. destruct a. destruct md_ctx.
  auto.
Qed.

Lemma hmac256drbgabs_update_value_md_empty:
  forall a value, hmac256drbgabs_empty_md a -> hmac256drbgabs_empty_md (hmac256drbgabs_update_value a value).
Proof.
  intros. destruct a. destruct md_ctx.
  auto.
Qed.

Lemma hmac256drbgabs_update_key_make_empty_md_commute:
  forall a key, hmac256drbgabs_update_key (hmac256drbgabs_make_empty_md a) key = hmac256drbgabs_make_empty_md (hmac256drbgabs_update_key a key).
Proof.
  destruct a. destruct md_ctx. reflexivity.
Qed.

Lemma hmac256drbgabs_update_value_make_empty_md_commute:
  forall a value, hmac256drbgabs_update_value (hmac256drbgabs_make_empty_md a) value = hmac256drbgabs_make_empty_md (hmac256drbgabs_update_value a value).
Proof.
  destruct a. destruct md_ctx. reflexivity.
Qed.