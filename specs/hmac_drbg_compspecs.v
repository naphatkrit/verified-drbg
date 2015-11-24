Require Import floyd.proofauto.
Require Import hmac_drbg.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined. 
