Require Import Coqlib.
Require Import List. Import ListNotations.

Definition HMAC_DRBG_update_abstract (HMAC: list Z -> list Z -> list Z) (provided_data K V: list Z): (list Z * list Z) :=
  let K := HMAC (V ++ [0] ++ provided_data) K in
  let V := HMAC V K in
  match provided_data with
    | [] => (K, V)
    | _::_ =>
      let K := HMAC (V ++ [1] ++ provided_data) K in
      let V := HMAC V K in
      (K, V)
  end.

Fixpoint HMAC_DRBG_update_helper (HMAC: list Z -> list Z -> list Z) (provided_data K V: list Z) (sep: Z) (round: nat): (list Z * list Z) :=
  match round with
    | O => (K, V)
    | S round' =>
      let K := HMAC (V ++ [sep] ++ provided_data) K in
      let V := HMAC V K in
      HMAC_DRBG_update_helper HMAC provided_data K V (sep + 1) round'
  end.

Definition HMAC_DRBG_update (HMAC: list Z -> list Z -> list Z) (provided_data K V: list Z): (list Z * list Z) :=
  let rounds := match provided_data with
                  | [] => 1%nat
                  | _ => 2%nat
                end in
  HMAC_DRBG_update_helper HMAC provided_data K V 0 rounds.

Theorem HMAC_DRBG_update_correct:
  forall HMAC provided_data K V, HMAC_DRBG_update HMAC provided_data K V = HMAC_DRBG_update_abstract HMAC provided_data K V.
Proof.
  intros.
  destruct provided_data; reflexivity.
Qed.