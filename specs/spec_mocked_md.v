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

Definition t_struct_md_ctx_st := Tstruct _mbedtls_md_context_t noattr.