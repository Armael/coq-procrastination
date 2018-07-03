Require Import Procrastination.Procrastination.
Require Import Nat Arith Omega Psatz Eomega.

Goal True.
  begin procrastination assuming a b c.

  assert (a <= b + 1). procrastinate.
  assert (b = c + 2). procrastinate.
  simpl in g.
  exact I.

  (* [end procrastination] gives back the subgoals that have been
     procrastinated. *)
  end procrastination.
  exists 0, 2, 0. omega.
Qed.

Goal True.
  begin procrastination.
  assert (H1: 1 + 1 = 2) by procrastinate.
  assert (H2: 1 + 2 = 3) by procrastinate.
  (* [procrastinate H: foo group g] is a shorthand for
     [assert (H: foo) by (procrastinate group g)] *)
  procrastinate H3: (1 + 3 = 4).

  tauto.
  end procrastination.
  repeat split; reflexivity.
Qed.

Goal True.
  (* It's also possible to explicitly name and refer to the "procrastination
     group". *)
  begin procrastination group g assuming a b c.
  (* [procrastinate] chooses by default the last group of the context. *)
  assert (a = b) by procrastinate.
  assert (b = c) by (procrastinate group g). simpl in g.
  exact I.

  end procrastination.
  exists 0, 0, 0. omega.
Qed.

(* Variants of the tactics named after "defer" (hence a bit easier to type) are
   also available.
*)
Goal True.
  begin deferring assuming a b c.
  defer: (a + b = c). exact I.
  end deferring.
  exists 0, 0, 0. reflexivity.
Qed.

Lemma dup : forall P, P -> P -> P. auto. Qed.

Goal exists (x: nat), x >= 2 /\ x <= 5 /\ x >= 1.
  begin procrastination assuming x.
  - exists x. (* We can use the [x] we got as a witness *)
    repeat split.
    + procrastinate.
    + procrastinate.
    + (* This case is interesting: we can prove this subgoal from the
         first side-condition we procrastinated earlier.

         There are several ways of doing that.
       *)

      (* omega alone is not able to fetch the fact from the group *)
      Fail omega.

      apply dup.
      (* [with procrastinated do ...] iterates on already procrastinated subgoals *)
      { with procrastinated do (fun H => generalize H). omega. }

      apply dup.
      (* [with procrastinated] adds the procrastinated facts to the context *)
      { with procrastinated. omega. }

      (* finally, [already procrastinated: H] adds H if it has already been
         procrastinated. *)
      already procrastinated: (x >= 2). omega.

  - end procrastination.
  (* The [eomega] tactic (from Eomega.v) finds instantiations by using a
     bruteforce strategy. *)
  eomega.
Qed.


(* More realistic example, inspired by the proof of asymptotic complexity for
   the binary search program below.

   See the manual for a more detailed description.
*)

(*
let rec bsearch (arr: int array) v i j =
  if j <= i then -1 else begin
    let m = i + (j - i) / 2 in
    if v = arr.(m) then m
    else if v < arr.(m) then
      bsearch arr v i m
    else
      bsearch arr v (m+1) j
  end
*)

Lemma log2_step:
  forall n,
  2 <= n ->
  1 + log2 (n/2) = log2 n.
Admitted.

Definition monotonic (f : nat -> nat) :=
  forall x y, x <= y -> f x <= f y.

Lemma solve_cost_ineqs_clean :
 exists (f: nat -> nat),
  1 <= f 0 /\
  monotonic f /\
  forall n, 0 < n -> 2 + f (n / 2) <= f n.
Proof.
  begin procrastination assuming a b c.
  exists (fun n => if zerop n then c else a * log2 n + b).
  repeat split.
  { simpl. procrastinate. }
  { intros x y ?. repeat (destruct zerop); try omega.
    - enough (c <= b) by lia. simpl in g. procrastinate.
    - pose proof (Nat.log2_le_mono x y). clear g; nia. }
  { intros n Hn.
    destruct (zerop n) as [|_]; [ exfalso; omega |].
    destruct (zerop (n / 2)) as [E|].
    - assert (n = 1). { rewrite Nat.div_small_iff in E; omega. }
      subst n. change (log2 1) with 0. rewrite Nat.mul_0_r, Nat.add_0_l.
      simpl in g. procrastinate.
    - assert (2 <= n). { rewrite (Nat.div_mod n 2); omega. }
      rewrite <-(log2_step n) by auto. rewrite Nat.mul_add_distr_l.
      enough (2 <= a) by omega. simpl in g. procrastinate. }
  end procrastination.
  eomega.
Qed.

Lemma solve_cost_ineq :
 exists (f: nat -> nat),
   forall n,
   1 + (if zerop n then 0 else 1 + max (f (n / 2)) (f (n - (n / 2) - 1))) <= f n.
Proof.
  begin procrastination assuming f. exists f.
  intro n.
  destruct (zerop n) as [|H].
  { subst n. simpl. procrastinate. }
  { rewrite max_l; swap 1 2.
    { simpl in g. procrastinate M: (monotonic f). apply M.
      rewrite (Nat.div_mod n 2) at 1; [| omega].
      pose proof (Nat.mod_upper_bound n 2); omega. }

    { rewrite Nat.add_assoc. change (1+1) with 2.
      simpl in g. revert n H. procrastinate. } }
  end procrastination.

  apply solve_cost_ineqs_clean.
Qed.
