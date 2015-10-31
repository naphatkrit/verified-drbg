Require Import floyd.proofauto.
Require Import hmac_drbg.

Definition CompSpecs' : compspecs.
Proof. make_compspecs1 prog. Defined.
Instance CompSpecs : compspecs.
Proof. make_compspecs2 CompSpecs'. Defined.
