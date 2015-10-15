Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmac_drbg.
Require Import HMAC256_DRBG_functional_prog.
Require Import spec_mocked_md.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Inductive hmac256drbgabs :=
  HMAC256DRBGabs: forall (md_ctx: mdabs) (V: list Z) (reseed_counter entropy_len: Z) (prediction_resistance: bool) (reseed_interval: Z) (f_entropy p_entropy: int), hmac256drbgabs.

Definition hmac256drbgstate: Type := (mdstate * (list val * (val * (val * (val * (val * (val * val)))))))%type.

Definition hmac256drbg_relate (a: hmac256drbgabs) (r: hmac256drbgstate) :=
  match a with HMAC256DRBGabs md_ctx V reseed_counter entropy_len prediction_resistance reseed_interval f_entropy p_entropy =>
               match r with (md_ctx', (V', (reseed_counter', (entropy_len', (prediction_resistance', (reseed_interval', (f_entropy', p_entropy'))))))) =>
                            md_relate md_ctx md_ctx'
                            /\ map (fun x => Vint (Int.repr x)) V = V'
                            /\ Vint (Int.repr reseed_counter) = reseed_counter'
                            /\ Vint (Int.repr entropy_len) = entropy_len'
                            /\ (match prediction_resistance with | true => prediction_resistance' <> Vint (Int.repr 0) | false => prediction_resistance' = Vint (Int.repr 0) end)
                            /\ Vint (Int.repr reseed_interval) = reseed_interval'
                            /\ Vint f_entropy = f_entropy'
                            /\ Vint p_entropy = p_entropy'

               end
  end.

Definition hmac256drbgabs_value (a: hmac256drbgabs): list Z :=
  match a with HMAC256DRBGabs _ V _ _ _ _ _ _ => V end.

Definition t_struct_hmac256drbg_context_st := Tstruct _mbedtls_hmac_drbg_context noattr.

Definition hmac_drbg_update_spec :=
  DECLARE _mbedtls_hmac_drbg_update
   WITH contents: list int, key: list Z, value: list Z,
        key': list Z, value': list Z, additional: val, add_len: Z,
        ctx: val, initial_state: hmac256drbgstate, final_state: hmac256drbgstate,
        initial_state_abs: hmac256drbgabs, final_state_abs: hmac256drbgabs
    PRE [ _ctx OF (tptr t_struct_hmac256drbg_context_st), _additional OF (tptr tuchar), _add_len OF tint ]
       PROP (0 <= add_len <= Int.max_signed; hmac256drbg_relate initial_state_abs initial_state)
       LOCAL (temp _additional additional; temp _add_len (Vint (Int.repr add_len)))
       SEP (
         `(data_at Tsh (tarray tint add_len) (map Vint contents) additional);
         `(data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx)
           )
    POST [ tvoid ]
       PROP ((key', value') = HMAC256_DRBG_update (map Int.signed contents) key value; hmac256drbg_relate final_state_abs final_state; value' = hmac256drbgabs_value final_state_abs)
       LOCAL ()
       SEP (
         `(data_at Tsh t_struct_hmac256drbg_context_st final_state ctx)
       ).
