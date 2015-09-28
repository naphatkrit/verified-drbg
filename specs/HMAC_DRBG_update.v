Require Import Coqlib.
Require Import List. Import ListNotations.

Definition HMAC_DRBG_update (HMAC: list Z -> list Z -> list Z) (provided_data K V: list Z): (list Z * list Z) :=
  let K := HMAC K (V ++ [0;0;0;0] ++ provided_data) in
  let V := HMAC K V in
  match provided_data with
    | [] => (K, V)
    | _::_ =>
      let K := HMAC K (V ++ [0;0;0;1] ++ provided_data) in
      let V := HMAC K V in
      (K, V)
  end.