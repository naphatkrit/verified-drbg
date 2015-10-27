Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmac_drbg.
Require Import HMAC256_DRBG_functional_prog.
Require Import spec_mocked_md.
Require Import sha.spec_hmacNK.
Require Import sha.funspec_hmacNK.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

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
    PRE [ _ctx OF (tptr t_struct_hmac256drbg_context_st), _additional OF (tptr tuchar), _add_len OF tint ]
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
  OPENSSL_HMAC_ABSTRACT_SPEC.hmac_update_spec::
  OPENSSL_HMAC_ABSTRACT_SPEC.hmac_final_spec::
  OPENSSL_HMAC_ABSTRACT_SPEC.hmac_reset_spec::
  OPENSSL_HMAC_ABSTRACT_SPEC.hmac_starts_spec::
  memcpy_spec_data_at:: memset_spec::
  sha256init_spec::sha256update_spec::sha256final_spec::(*SHA256_spec::*)
  HMAC_Init_spec:: HMAC_Update_spec::HMAC_Cleanup_spec::
  HMAC_Final_spec:: HMAC_spec ::nil.