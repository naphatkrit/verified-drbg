Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import mocked_md.
Require Import spec_hmacNK.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Inductive mdabs :=
  MDabs: forall (md_info_ptr md_ctx_ptr hmac_ctx_ptr: int), mdabs.

Definition mdstate: Type := (val * (val * val))%type.

Definition md_relate (a: mdabs) (r: mdstate): Prop :=
  match a with MDabs md_info_ptr md_ctx_ptr hmac_ctx_ptr =>
               Vint md_info_ptr = fst r
               /\ Vint md_ctx_ptr = fst (snd r)
               /\ Vint hmac_ctx_ptr = snd (snd r)
  end.

Definition t_struct_md_ctx_st := Tstruct __243 noattr.