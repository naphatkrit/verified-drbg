Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import DRBG_entropy_result.

Definition stream: Type := nat -> Z.

Fixpoint get_bytes_helper (k: nat) (s: stream) (max: nat): (list Z) :=
  match k with
    | O => []
    | S k' => (s (max - k)%nat)::(get_bytes_helper k' s max)
  end.

Definition get_bytes (k: nat) (s: stream): (list Z * stream) :=
  (get_bytes_helper k s k, fun i => s (k + i)%nat).

Lemma get_bytes_helper_n:
  forall k s n, get_bytes_helper k s (n + k) = get_bytes_helper k (fun i => s (n + i)%nat) k.
Proof.
  intros k.
  induction k as [|k'].
  reflexivity.
  intros s n.
  simpl.
  replace (n + S k' - S k')%nat with n by omega.
  replace (n + (k' - k'))%nat with n by omega.
  replace (n + S k')%nat with ((n + 1) + k')%nat by omega.
  rewrite IHk' with (n:=(n+1)%nat).
  rewrite IHk' with (n:=1%nat).
  replace (fun i : nat => s (n + 1 + i)%nat) with (fun i : nat => s (n + (1 + i))%nat).
  reflexivity.
  extensionality i.
  rewrite plus_assoc.
  reflexivity.
Qed.

Fixpoint get_bytes_helper_abstract k (s: stream) :=
  match k with
    | O => []
    | S k' => get_bytes_helper_abstract k' s ++ [s k']
  end.

Lemma get_bytes_helper_correct:
  forall k s, get_bytes_helper k s k = get_bytes_helper_abstract k s.
Proof.
  intros k.
  induction k as [|k']; [reflexivity | ].
  intros s.
  simpl.
  rewrite get_bytes_helper_n with (n:=1%nat).
  rewrite IHk'.
  clear.
  replace (k' - k')%nat with O by omega.
  revert s.
  induction k' as [|k'']; [reflexivity | ].
  intros.
  simpl.
  simpl in IHk''.
  rewrite <- IHk'' with s.
  simpl.
  reflexivity.
Qed.

Theorem get_bytes_additive:
  forall l1 l2 k1 k2 s s' s'',
    (l1, s') = get_bytes k1 s ->
    (l2, s'') = get_bytes k2 s' ->
    (l1 ++ l2, s'') = get_bytes (k1 + k2) s.
Proof.
  intros l1 l2 k1. revert l1 l2.
  induction k1 as [| k1'].
  {
    (* k1 = 0 *)
    intros.
    unfold get_bytes in *; simpl in *.
    assert (Hl1: l1 = []) by (change l1 with (fst (l1, s')); rewrite H; reflexivity).
    assert (Hs': s' = s) by (change s' with (snd (l1, s')); rewrite H; simpl; extensionality i; reflexivity).
    subst; clear H.
    assumption.
  }
  (* k1 = S k1' *)
  unfold get_bytes in *; simpl in *.
  assert (IHK1l: forall (l1 l2 : list Z) (k2 : nat) (s s' s'' : stream),
          (l1, s') =
          (get_bytes_helper k1' s k1', fun i : nat => s (k1' + i)%nat) ->
          (l2, s'') =
          (get_bytes_helper k2 s' k2, fun i : nat => s' (k2 + i)%nat) ->
          l1 ++ l2 =
          get_bytes_helper (k1' + k2) s (k1' + k2)).
  {
    clear - IHk1'.
    intros.
    specialize (IHk1' l1 l2 k2 s s' s'').
    change (l1 ++ l2) with (fst (l1 ++ l2, s'')).
    rewrite IHk1'; try assumption. reflexivity.
  }
  assert (IHK1s: forall (l1 l2 : list Z) (k2 : nat) (s s' s'' : stream),
          (l1, s') =
          (get_bytes_helper k1' s k1', fun i : nat => s (k1' + i)%nat) ->
          (l2, s'') =
          (get_bytes_helper k2 s' k2, fun i : nat => s' (k2 + i)%nat) ->
          s'' =
          fun i : nat => s (k1' + k2 + i)%nat).
  {
    clear - IHk1'.
    intros.
    specialize (IHk1' l1 l2 k2 s s' s'').
    change s'' with (snd (l1 ++ l2, s'')).
    rewrite IHk1'; try assumption. reflexivity.
  }
  clear IHk1'.

  intros.
  replace (k1' + k2 - (k1' + k2))%nat with O by omega.
  assert (Hl1: l1 = s (k1' - k1')%nat :: get_bytes_helper k1' s (S k1')) by
  (change l1 with (fst (l1, s')); rewrite H; reflexivity).
  assert (Hs': s' = fun i : nat => s (S (k1' + i))) by
  (change s' with (snd (l1, s')); rewrite H; reflexivity).
  assert (Hl2: l2 = get_bytes_helper k2 s' k2) by
  (change l2 with (fst (l2, s'')); rewrite H0; reflexivity).
  assert (Hs'': s'' = fun i : nat => s' (k2 + i)%nat) by
  (change s'' with (snd (l2, s'')); rewrite H0; reflexivity).
  destruct l1 as [|hd1 tl1]; [inversion Hl1|].
  simpl.
  rewrite IHK1l with (k2:=k2) (s:=fun i => s (S i)) (s':=s') (s'':=s''); try assumption.
  Focus 2.
  inv Hl1.
  rewrite get_bytes_helper_n with (n:=1%nat).
  replace (fun i : nat => s (S i)) with (fun i : nat => s (1 + i)%nat); [reflexivity | extensionality i; reflexivity].
  inv Hl1. replace (k1' - k1')%nat with O by omega.
  rewrite get_bytes_helper_n with (n:=1%nat).
  replace (fun i : nat => s (S i)) with (fun i : nat => s (1 + i)%nat) by (extensionality i; reflexivity).
  replace (fun i : nat => s (S (k1' + (k2 + i)))) with (fun i : nat => s (S (k1' + k2 + i))) by (extensionality i; rewrite plus_assoc; reflexivity).
  reflexivity.
Qed.

Inductive entropy_result :=
| entropy_error: entropy_result
| entropy_success: (list Z * stream) -> entropy_result.

Definition get_bytes_entropy_result k s := entropy_success (get_bytes k s).