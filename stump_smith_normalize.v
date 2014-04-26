Require Export Basics.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(* some helpful arithmetic Proofs *)

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".     reflexivity.
  Case "n = S n'".  simpl. rewrite -> IHn'. reflexivity.  Qed.

Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof. 
  intros n m.  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n'].
  Case "n = 0".
    rewrite plus_0_r. reflexivity.
  Case "n = S n'".
    simpl. 
    rewrite IHn'. 
    rewrite -> plus_n_Sm. reflexivity.
Qed.

Definition neq_0_b (n :nat) : bool := 
  match n with 
    |0 => false 
    |S _ => true 
end.

Theorem neq_0_dist :
  forall (n m : nat),
  neq_0_b (n + m) = orb (neq_0_b n) (neq_0_b m).
Proof.
  intros. destruct n. reflexivity. reflexivity.
Qed.  

(* bin is defined here *)

Inductive bin : Type :=
| Zero : bin
| D : bin -> bin
| P : bin -> bin.

Fixpoint inc (n : bin) : bin :=
  match n with
   | Zero => P Zero
   | D n' => P n'
   | P n' => D (inc n')
  end.

Fixpoint gt_Zero (n : bin) : bool :=
  match n with
    |Zero => false
    |D n' => gt_Zero n'
    |P n' => true
  end.

Fixpoint toUnary (n : bin) : nat :=
  match n with
    |Zero => O
    |D n' => 2 * toUnary n'
    |P n' => S (2 * toUnary n')
  end.

Fixpoint fromUnary (n : nat) : bin :=
  match n with
    |O => Zero
    |S n' => inc (fromUnary n')
end.

Theorem comm_inc_binunary :
  forall (n : bin),
  toUnary (inc n) = S (toUnary n).
Proof.
  induction n. reflexivity.
  reflexivity.
  simpl. rewrite IHn.
  simpl. rewrite <- plus_n_Sm.
  reflexivity.
Qed.

Theorem leftInv : 
  forall (x : nat),
  toUnary (fromUnary x) = x.
Proof.
  induction x. Case "base". reflexivity.
  simpl. rewrite comm_inc_binunary.
  rewrite IHx.
  reflexivity.
Qed.

(* Here is the definition of normalize *)

Fixpoint dropZeros (n: bin) :bin :=
  match n with
    | Zero => Zero
    | D n' => dropZeros n'
    | P n' => P n'
end.

Fixpoint conj (n: bin) (con: bin -> bin) : bin :=
  match n with
    | Zero => con Zero
    | D n' => D (conj n' con)
    | P n' => P (conj n' con)
  end.

(* this is slower than reverse with an accumulator, but easier to reason about *)
Fixpoint reverse (n : bin) : bin :=
  match n with
    | Zero => Zero
    | D n' => conj (reverse n') D
    | P n' => conj (reverse n') P
end.

Fixpoint normalize (n : bin) :bin :=
  reverse ( dropZeros ( reverse n)).


Lemma conj_revD : 
  forall (b : bin),
  reverse (conj b D) = D (reverse b).
Proof.
  intros. induction b. reflexivity.
  simpl.  rewrite IHb. reflexivity.
  simpl.  rewrite IHb. reflexivity.
Qed.

Lemma conj_revP : 
  forall (b : bin),
  reverse (conj b P) = P (reverse b).
Proof.
  intros. induction b. reflexivity.
  simpl.  rewrite IHb. reflexivity.
  simpl.  rewrite IHb. reflexivity.
Qed.

Theorem rev_inv_rev:
  forall (x : bin),
  reverse (reverse x) = x.
Proof.
  intros. induction x. reflexivity.
  simpl. rewrite conj_revD. rewrite IHx. reflexivity.
  simpl. rewrite conj_revP. rewrite IHx. reflexivity.
Qed.

Theorem toUnary_distD:
  forall (x : bin),
  toUnary (D x) = (toUnary x) + (toUnary x) .
Proof.    
  intros. induction x. simpl. reflexivity.
  simpl. rewrite plus_0_r. rewrite plus_0_r. reflexivity.
  simpl. rewrite plus_0_r. rewrite plus_0_r. reflexivity.
Qed.  

Theorem toUnary_distP:
  forall (x : bin),
  toUnary (P x) = S (toUnary x + toUnary x).
Proof.
  induction x. simpl. reflexivity.
  simpl. rewrite plus_0_r. rewrite plus_0_r. reflexivity.
  simpl. rewrite plus_0_r. rewrite plus_0_r. reflexivity.
Qed.

(* Here I used inversion. Basically if you have an absurd 
premise you can derive an absurd conclusion. *)
Theorem fromUnary_distD:
  forall (n : nat),
  neq_0_b n = true -> D (fromUnary n) = fromUnary(n + n).  
Proof.
  intros. induction n. inversion H.
  simpl. rewrite <- plus_n_Sm. simpl. destruct n. reflexivity. 
  rewrite <- IHn. simpl. reflexivity. reflexivity.
Qed.

Theorem fromUnary_distP:
  forall (n : nat),
  P (fromUnary n) = inc (fromUnary(n + n)).
Proof.
  induction n. reflexivity.
  simpl. rewrite <- plus_comm. simpl. rewrite <- IHn. simpl. reflexivity.
Qed.

Theorem has_P_not_zero:
  forall (x : bin),
  neq_0_b (toUnary (conj x P)) = true.
Proof.
  induction x. reflexivity.
  simpl. rewrite plus_0_r. rewrite neq_0_dist. rewrite IHx. reflexivity.
  reflexivity.
Qed.

Theorem trailing_P_is_normal:
  forall (y : bin),
  fromUnary (toUnary (conj y P)) = conj y P.
Proof.
  induction y. reflexivity.
  simpl. rewrite plus_0_r. rewrite <- fromUnary_distD. rewrite IHy. reflexivity.
  rewrite has_P_not_zero. reflexivity.
  simpl. rewrite plus_0_r. rewrite <- fromUnary_distP. rewrite IHy. reflexivity.
Qed.

Theorem toUnary_drop_trailing_D :
  forall (y : bin),
  toUnary (conj y D) = toUnary y.
Proof.
  intros. induction y. reflexivity.
  simpl. rewrite IHy. reflexivity.
  simpl. rewrite IHy. reflexivity.
Qed.

Theorem dropFront :
  forall (x : bin),
  reverse (dropZeros x) = (fromUnary (toUnary (reverse x))).
Proof.
 induction x. reflexivity.
 simpl. rewrite toUnary_drop_trailing_D. rewrite IHx. reflexivity.
 simpl. rewrite trailing_P_is_normal. reflexivity.
Qed.

Theorem rightInv:
  forall (z : bin),
  fromUnary (toUnary z) = normalize z.
Proof.
  destruct z. reflexivity.
  simpl. rewrite plus_0_r.
  rewrite dropFront. rewrite conj_revD. rewrite rev_inv_rev. rewrite toUnary_distD. reflexivity.
  simpl. rewrite plus_0_r.
  rewrite dropFront. rewrite conj_revP. rewrite rev_inv_rev. rewrite toUnary_distP. reflexivity.
Qed.


(* Things I didn't end up needing *)
 
Theorem fromUnary_inj :
  forall (x y: nat),
  fromUnary x = fromUnary y -> x = y.
Proof.
  intros. rewrite <- leftInv. rewrite <- H. rewrite leftInv. reflexivity.
Qed.  


Fixpoint rev (n: bin) (acc : bin) : bin :=
  match n with
    | Zero => acc
    | D n' => rev n' (D acc)
    | P n' => rev n' (P acc)
end.

(* this reverse uses an accumulator and is O(n) instead of O(n^2) *)
Definition reverse_fast (n : bin) : bin :=
  rev n Zero.

(* never got around to proving this *)
Theorem rev_eq_rev_fast :
  forall (n : bin), reverse n = reverse_fast n.
Proof.
Abort.

(* this is another normalize function I defined I belive it should be a bit faster, 
 but looks hard to reason about. *)

Fixpoint revpend (n: bin) (m: bin) : bin :=
  match n with
    |Zero => m
    |D n' => D (revpend n' m)
    |P n' => P (revpend n' m)
  end.

Fixpoint nml (n : bin) (acc : bin) : bin :=
  match n with
    |Zero => Zero
    |D n' => nml n' (D acc)
    |P n' => revpend (D acc) (nml n' Zero)
  end.

Definition normalize' (n : bin) : bin := 
  nml n Zero.


