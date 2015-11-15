Require Import floyd.proofauto.
Require Import hmac_drbg.

Definition CompSpecs' : compspecs.
Proof.
  Time make_compspecs1 prog. (* 4843 *)
Time Defined. (* 598 *)
Instance CompSpecs : compspecs.
Proof.
  Time make_compspecs2 CompSpecs'. (* 525 *)
Time Defined. (* 596 *)
