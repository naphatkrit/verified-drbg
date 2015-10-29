Require Import floyd.proofauto.
Require Import mocked_md.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.
