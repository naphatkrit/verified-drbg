Require Import Coqlib.
Require Import List. Import ListNotations.

Require Import spec_hmac_drbg.
Require Import HMAC256_DRBG_functional_prog.
Require Import DRBG_functions.
Require Import HMAC_DRBG_algorithms.
Require Import entropy.
Require Import sha.spec_hmacNK.
Require Import sha.funspec_hmacNK.
Require Import sha.general_lemmas.
Require Import sha.HMAC256_functional_prog.


Lemma hmac256drbgabs_hmac_drbg_update_any_prop_key:
  forall (P: list Z -> Prop) a additional_data,
    (forall x y, P (HMAC256 x y)) ->
    P (hmac256drbgabs_key (hmac256drbgabs_hmac_drbg_update a additional_data)).
Proof.
  intros.
  destruct a; simpl.
  unfold HMAC256_DRBG_update, HMAC_DRBG_update.
  destruct additional_data; apply H.  
Qed.

Lemma hmac256drbgabs_hmac_drbg_update_any_prop_V:
  forall (P: list Z -> Prop) a additional_data,
    (forall x y, P (HMAC256 x y)) ->
    P (hmac256drbgabs_value (hmac256drbgabs_hmac_drbg_update a additional_data)).
Proof.
  intros.
  destruct a; simpl.
  unfold HMAC256_DRBG_update, HMAC_DRBG_update.
  destruct additional_data; apply H.  
Qed.

Lemma hmac256drbgabs_hmac_drbg_update_Zlength_key:
  forall a additional_data,
    Zlength (hmac256drbgabs_key (hmac256drbgabs_hmac_drbg_update a additional_data)) = Z.of_nat SHA256.DigestLength.
Proof.
  intros.
  apply hmac256drbgabs_hmac_drbg_update_any_prop_key.
  apply hmac_common_lemmas.HMAC_Zlength.
Qed.

Lemma hmac256drbgabs_hmac_drbg_update_Zlength_V:
  forall a additional_data,
    Zlength (hmac256drbgabs_value (hmac256drbgabs_hmac_drbg_update a additional_data)) = Z.of_nat SHA256.DigestLength.
Proof.
  intros.
  apply hmac256drbgabs_hmac_drbg_update_any_prop_V.
  apply hmac_common_lemmas.HMAC_Zlength.
Qed.

Lemma hmac256drbgabs_hmac_drbg_update_isbyteZ_key:
  forall a additional_data,
    Forall isbyteZ (hmac256drbgabs_key (hmac256drbgabs_hmac_drbg_update a additional_data)).
Proof.
  intros.
  apply hmac256drbgabs_hmac_drbg_update_any_prop_key.
  apply hmac_common_lemmas.isbyte_hmac.
Qed.

Lemma hmac256drbgabs_hmac_drbg_update_isbyteZ_V:
  forall a additional_data,
    Forall isbyteZ (hmac256drbgabs_value (hmac256drbgabs_hmac_drbg_update a additional_data)).
Proof.
  intros.
  apply hmac256drbgabs_hmac_drbg_update_any_prop_V.
  apply hmac_common_lemmas.isbyte_hmac.
Qed.

Lemma hmac256drbgabs_reseed_any_prop_key:
  forall (P: list Z -> Prop) a s additional_data,
    P (hmac256drbgabs_key a) ->
    (forall x y, P (HMAC256 x y)) ->
    P (hmac256drbgabs_key (hmac256drbgabs_reseed a s additional_data)).
Proof.
  intros.
  destruct a; simpl.
  destruct ((prediction_resistance && negb prediction_resistance)%bool); auto.
  destruct (Zlength additional_data >? 256); auto.
  destruct (get_entropy 256 entropy_len entropy_len prediction_resistance s); auto.
  unfold HMAC_DRBG_update.
  unfold hmac256drbgabs_key.
  destruct (l ++ additional_data); auto.
Qed.

Lemma hmac256drbgabs_reseed_any_prop_V:
  forall (P: list Z -> Prop) a s additional_data,
    P (hmac256drbgabs_value a) ->
    (forall x y, P (HMAC256 x y)) ->
    P (hmac256drbgabs_value (hmac256drbgabs_reseed a s additional_data)).
Proof.
  intros.
  destruct a; simpl.
  destruct ((prediction_resistance && negb prediction_resistance)%bool); auto.
  destruct (Zlength additional_data >? 256); auto.
  destruct (get_entropy 256 entropy_len entropy_len prediction_resistance s); auto.
  unfold HMAC_DRBG_update.
  unfold hmac256drbgabs_value.
  destruct (l ++ additional_data); auto.
Qed.

Lemma hmac256drbgabs_reseed_Zlength_key:
  forall a s additional_data,
    Zlength (hmac256drbgabs_key a) = Z.of_nat SHA256.DigestLength ->
    Zlength (hmac256drbgabs_key (hmac256drbgabs_reseed a s additional_data)) = Z.of_nat SHA256.DigestLength.
Proof.
  intros.
  apply hmac256drbgabs_reseed_any_prop_key; auto.
  apply hmac_common_lemmas.HMAC_Zlength.
Qed.

Lemma hmac256drbgabs_reseed_Zlength_V:
  forall a s additional_data,
    Zlength (hmac256drbgabs_value a) = Z.of_nat SHA256.DigestLength ->
    Zlength (hmac256drbgabs_value (hmac256drbgabs_reseed a s additional_data)) = Z.of_nat SHA256.DigestLength.
Proof.
  intros.
  apply hmac256drbgabs_reseed_any_prop_V; auto.
  apply hmac_common_lemmas.HMAC_Zlength.
Qed.

Lemma hmac256drbgabs_reseed_isbyteZ_key:
  forall a s additional_data,
    Forall isbyteZ (hmac256drbgabs_key a) ->
    Forall isbyteZ (hmac256drbgabs_key (hmac256drbgabs_reseed a s additional_data)).
Proof.
  intros.
  apply hmac256drbgabs_reseed_any_prop_key; auto.
  apply hmac_common_lemmas.isbyte_hmac.
Qed.

Lemma hmac256drbgabs_reseed_isbyteZ_V:
  forall a s additional_data,
    Forall isbyteZ (hmac256drbgabs_value a) ->
    Forall isbyteZ (hmac256drbgabs_value (hmac256drbgabs_reseed a s additional_data)).
Proof.
  intros.
  apply hmac256drbgabs_reseed_any_prop_V; auto.
  apply hmac_common_lemmas.isbyte_hmac.
Qed.

Lemma hmac256drbgabs_update_key_ident:
  forall a key, key = hmac256drbgabs_key a -> hmac256drbgabs_update_key a key = a.
Proof.
  intros.
  destruct a.
  simpl in H; subst.
  reflexivity.
Qed.

Lemma hmac256drbgabs_update_value_ident:
  forall a value, value = hmac256drbgabs_value a -> hmac256drbgabs_update_value a value = a.
Proof.
  intros.
  destruct a.
  simpl in H; subst.
  reflexivity.
Qed.

Lemma hmac256drbgabs_update_key_update_value_commute:
  forall a key value, hmac256drbgabs_update_value (hmac256drbgabs_update_key a key) value = hmac256drbgabs_update_key (hmac256drbgabs_update_value a value) key.
Proof.
  destruct a.
  reflexivity.
Qed.