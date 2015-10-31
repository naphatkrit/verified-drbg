Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmac_drbg.
Require Import HMAC256_DRBG_functional_prog.
Require Import sha.spec_hmacNK.
Require Import sha.funspec_hmacNK.

(* mocked_md *)
Require Import sha.HMAC256_functional_prog.
Require Import sha.spec_sha.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

(*
Definition CompSpecs' : compspecs.
Proof. make_compspecs1 prog. Defined.
Instance CompSpecs : compspecs.
Proof. make_compspecs2 CompSpecs'. Defined.
*)

Module UNDER_SPEC := OPENSSL_HMAC_ABSTRACT_SPEC.

Inductive HABS := hABS: forall (key data:list Z), HABS.

Definition mdstate: Type := (val * (val * val))%type.

Definition t_struct_md_ctx_st := Tstruct _mbedtls_md_context_t noattr.

Definition convert_abs (h: HABS): UNDER_SPEC.HABS :=
  match h with hABS key data => UNDER_SPEC.hABS key data end.

Definition md_relate (h: HABS) (r:mdstate) :=
  UNDER_SPEC.REP (convert_abs h) (snd (snd r)).

Definition REP (h: HABS) (c: val): mpred :=
  EX r: mdstate,
        (md_relate h r && data_at Tsh t_struct_md_ctx_st r c).

Definition FULL key c:mpred :=
  EX r: mdstate,
        (UNDER_SPEC.FULL key (snd (snd r)) && data_at Tsh t_struct_md_ctx_st r c).

Definition EMPTY c :=
  EX r: mdstate,
        (UNDER_SPEC.EMPTY (snd (snd r)) && data_at Tsh t_struct_md_ctx_st r c).

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
   WITH c : val, l:Z, key:list Z, kv:val, d:list Z
   PRE [ _ctx OF tptr t_struct_md_ctx_st]
         PROP (has_lengthK l key)
         LOCAL (temp _ctx c; gvar sha._K256 kv)
         SEP ( `(FULL key c); `(K_vector kv))
  POST [ tint ] 
     PROP ()
     LOCAL ()
     SEP (`(REP (hABS key nil) c); `(K_vector kv)).

Definition md_starts_spec :=
  DECLARE _mbedtls_md_hmac_starts
   WITH c : val, l:Z, key:list Z, kv:val, b:block, i:Int.int
   PRE [ _ctx OF tptr t_struct_md_ctx_st,
         _key OF tptr tuchar,
         _keylen OF tint ]
         PROP (has_lengthK l key)
         LOCAL (temp _ctx c; temp _key (Vptr b i); temp _keylen (Vint (Int.repr l));
                gvar sha._K256 kv)
         SEP (`(EMPTY c); 
              `(data_block Tsh key (Vptr b i)); `(K_vector kv))
  POST [ tvoid ] 
     PROP ()
     LOCAL ()
     SEP (`(REP (hABS key nil) c); `(data_block Tsh key (Vptr b i)); `(K_vector kv)).

Definition md_update_spec :=
  DECLARE _mbedtls_md_hmac_update
   WITH key: list Z, c : val, d:val, data:list Z, data1:list Z, kv:val
   PRE [ _ctx OF tptr t_struct_md_ctx_st, 
         _input OF tptr tvoid, 
         _ilen OF tuint]
         PROP (0 <= Zlength data1 <= Int.max_unsigned /\
               Zlength data1 + Zlength data + 64 < two_power_pos 61) 
         LOCAL (temp _ctx c; temp _input d; temp  _ilen (Vint (Int.repr (Zlength data1)));
                gvar sha._K256 kv)
         SEP(`(REP (hABS key data) c); `(data_block Tsh data1 d); `(K_vector kv))
  POST [ tvoid ] 
          PROP () 
          LOCAL ()
          SEP(`(REP (hABS key (data++data1)) c); 
              `(data_block Tsh data1 d);`(K_vector kv)).

Definition md_final_spec :=
  DECLARE _mbedtls_md_hmac_finish
   WITH data:list Z, key:list Z, c : val, md:val, shmd: share, kv:val
   PRE [ _ctx OF tptr t_struct_md_ctx_st,
         _output OF tptr tuchar ]
       PROP (writable_share shmd) 
       LOCAL (temp _output md; temp _ctx c;
              gvar sha._K256 kv)
       SEP(`(REP (hABS key data) c); `(K_vector kv);
           `(memory_block shmd 32 md))
  POST [ tvoid ] 
          PROP () 
          LOCAL ()
          SEP(`(K_vector kv);
              `(FULL key c);
              `(data_block shmd (HMAC256 data key) md)).
(* end mocked_md *)

Inductive hmac256drbgabs :=
  HMAC256DRBGabs: forall (md_ctx: HABS) (V: list Z) (reseed_counter entropy_len: Z) (prediction_resistance: bool) (reseed_interval: Z), hmac256drbgabs.

Definition hmac256drbgstate: Type := (mdstate * (list val * (val * (val * (val * (val * (val * val)))))))%type.

Definition hmac256drbg_relate (a: hmac256drbgabs) (r: hmac256drbgstate) : mpred :=
  match a with HMAC256DRBGabs md_ctx V reseed_counter entropy_len prediction_resistance reseed_interval =>
               match r with (md_ctx', (V', (reseed_counter', (entropy_len', (prediction_resistance', (reseed_interval', (f_entropy', p_entropy'))))))) =>
                            md_relate md_ctx md_ctx'
                                      && !! (
                                        map (fun x => Vint (Int.repr x)) V = V'
                                        /\ Vint (Int.repr reseed_counter) = reseed_counter'
                                        /\ Vint (Int.repr entropy_len) = entropy_len'
                                        /\ Vint (Int.repr reseed_interval) = reseed_interval'
                                        /\ if prediction_resistance then (prediction_resistance' <> Vint (Int.repr 0)) else (prediction_resistance' = Vint (Int.repr 0))
                                      )
               end
  end.

Definition hmac256drbgabs_value (a: hmac256drbgabs): list Z :=
  match a with HMAC256DRBGabs _ V _ _ _ _ => V end.

Definition hmac256drbgabs_key (a: hmac256drbgabs): list Z :=
  match a with HMAC256DRBGabs (hABS key _) _ _ _ _ _ => key end.

Definition hmac256drbgabs_metadata_same (a: hmac256drbgabs) (b: hmac256drbgabs): Prop :=
  match a with HMAC256DRBGabs _ _ reseed_counter entropy_len prediction_resistance reseed_interval =>
               match b with HMAC256DRBGabs _ _ reseed_counter' entropy_len' prediction_resistance' reseed_interval' =>
                            reseed_counter = reseed_counter'
                            /\ entropy_len = entropy_len'
                            /\ prediction_resistance = prediction_resistance'
                            /\ reseed_interval = reseed_interval'
               end
  end.

Definition t_struct_hmac256drbg_context_st := Tstruct _mbedtls_hmac_drbg_context noattr.

Definition hmac_drbg_update_post (final_state_abs: hmac256drbgabs) (ctx: val): mpred :=
  EX final_state: hmac256drbgstate,
                  (data_at Tsh t_struct_hmac256drbg_context_st final_state ctx) *
                  (hmac256drbg_relate final_state_abs final_state).

Definition hmac_drbg_update_spec :=
  DECLARE _mbedtls_hmac_drbg_update
   WITH contents: list int,
        additional: val, add_len: Z,
        ctx: val, initial_state: hmac256drbgstate,
        initial_state_abs: hmac256drbgabs
    PRE [ _ctx OF (tptr t_struct_hmac256drbg_context_st), _additional OF (tptr tuchar), _add_len OF tuint ]
       PROP (
         0 <= add_len <= Int.max_unsigned
       )
       LOCAL (temp _additional additional; temp _add_len (Vint (Int.repr add_len)))
       SEP (
         `(data_at Tsh (tarray tuchar add_len) (map Vint contents) additional);
         `(data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx);
         `(hmac256drbg_relate initial_state_abs initial_state)
           )
    POST [ tvoid ]
       EX key': list Z, EX value': list Z, EX final_state_abs:_,
       PROP (
           (key', value') = HMAC256_DRBG_update (map Int.signed contents) (hmac256drbgabs_key initial_state_abs) (hmac256drbgabs_value initial_state_abs);
           value' = hmac256drbgabs_value final_state_abs;
           key' = hmac256drbgabs_key final_state_abs;
           hmac256drbgabs_metadata_same initial_state_abs final_state_abs
         )
       LOCAL ()
       SEP (
         `(hmac_drbg_update_post final_state_abs ctx)
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
