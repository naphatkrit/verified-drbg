Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import mocked_md.
Require Import spec_hmacNK.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Inductive mdabs :=
  MDabs: forall (h: hmacabs), mdabs.

Definition mdstate: Type := (val * (val * val))%type.

Definition md_relate (a: mdabs) (r: mdstate): mpred :=
  match a with MDabs h =>
               hmacstate_ h (snd (snd r))
  end.

Inductive hmac_has_key (k: list Z) (h: hmacabs): Prop :=
| Init: hmacInit k h -> hmac_has_key k h
| Update: forall h' data, hmac_has_key k h' -> hmacUpdate data h' h -> hmac_has_key k h
| Final: forall h' digest, hmac_has_key k h' -> hmacFinal h' digest h -> hmac_has_key k h.

Definition md_has_key (k: list Z) (m: mdabs) :=
  match m with MDabs h => hmac_has_key k h end.

Definition t_struct_md_ctx_st := Tstruct _mbedtls_md_context_t noattr.