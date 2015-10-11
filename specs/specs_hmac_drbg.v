Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmac_drbg.
Require Import HMAC256_DRBG_functional_prog.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Definition hmac_drbg_update_spec :=
  DECLARE _mbedtls_hmac_drbg_update
   WITH sh: share, contents: list int, key: list Z, value: list Z, key': list Z, value': list Z, additional: val, add_len: Z
   PRE [ _additional OF (tptr tuchar), _add_len OF tint ]
       PROP (0 <= add_len <= Int.max_signed; readable_share sh)
       LOCAL (temp _additional additional; temp _add_len (Vint (Int.repr add_len)))
       SEP (`(data_at sh (tarray tint add_len) (map Vint contents) additional))
    POST [ tvoid ]
       PROP ((key', value') = HMAC256_DRBG_update (map Int.signed contents) key value)
       LOCAL ()
       SEP ().
