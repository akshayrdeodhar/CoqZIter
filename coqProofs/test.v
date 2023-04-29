From Coq Require Import ZArith.
Require Import Coq.Init.Logic.
Require Import Coq.Logic.Classical_Prop.
Require Import BinPos BinInt BinNums Decidable Zcompare Znumtheory Zorder.
Require Import Arith_base.
Require Import Coq.micromega.Lia.
Require Import Field.

Local Open Scope Z_scope.


(* Prove that addition is commutative *)
Theorem commutative_addition : forall a b : Z, a + b = b + a.
Proof.
    apply Z.add_comm.
Qed.

Inductive MySet : Type :=
    | Inclusive (a : Z) (b: Z). (* set of integers including a and b *)

Definition inMySet (x : Z) (A : MySet) : Prop :=
    match A with
    | Inclusive a b => a <= x /\ x <= b
    end.

    (* TODO: Step must be positive *)

Inductive Iterator : Type :=
    | iterator (_start _end _step : Z).

Definition inIterator (x : Z) (I : Iterator) :=
    match I with 
    | iterator _start _end _step => 
        match _step with
        | Z0 => x = _start 
        | Zpos _ => (_start <= x /\ x <= _end) /\ (_step | (x - _start))
        | Zneg _ => (_end <= x /\ x <= _start) /\ (_step | (_start - x))
        end
    end.

Check (inIterator 8 (iterator 1 10 1)).
Theorem ex_in_iterator : (inIterator 8 (iterator 1 10 1)).
Proof. simpl. split. 
    - split.
        + discriminate.
        + discriminate.
    - exists 7. reflexivity.
Qed.

Theorem ex_notin_iterator :  ~ (inIterator 8 (iterator 1 (-10) (-1))).
Proof. simpl. unfold not. intro H. destruct H. 
    - destruct H. destruct H1. reflexivity.
Qed.

Definition iteratorMin (I : Iterator) : Z :=
    match I with
    | iterator _start _end _step => 
        match _step with 
        | Zneg _ => _end
        | _ => _start
        end
    end.

Definition myIterator : Iterator := iterator 1 10 1.
Definition myNegIterator : Iterator := iterator 10 1 (-1).

Compute iteratorMin myIterator.
Compute iteratorMin myNegIterator.

Lemma always_leq : forall x : Z, x <= x. 
Proof.
    intros. induction x.
    - discriminate.
    - induction p. assumption. assumption. discriminate.
    - induction p. assumption. assumption. discriminate.
Qed.

Lemma min_of_iter : forall x : Z, forall I : Iterator, (inIterator x I) -> (iteratorMin I) <= x.
Proof.
    intros. unfold inIterator in H. unfold iteratorMin. destruct I. destruct _step.
    destruct H.
    - apply always_leq.
    - destruct H. destruct H. assumption.
    - destruct H. destruct H. assumption.
Qed.
 
Definition iteratorMax (I: Iterator) : Z := 
    match I with 
    | iterator _start _end _step =>
        match _step  with
        | Zpos _ => _end
        | _ => _start
        end
    end.

Check iteratorMax myIterator = 10.
Check iteratorMax myNegIterator = 10.

Lemma always_geq : forall x : Z, x >= x.
Proof. intros x. apply Z.ge_le_iff. apply always_leq.
Qed.

Lemma max_of_iter: forall x : Z, forall I : Iterator, (inIterator x I) -> x <= (iteratorMax I).
Proof. intros x I H. unfold inIterator in H. unfold iteratorMax.
    destruct I. destruct _step. destruct H.
    - apply always_leq.
    - destruct H. destruct H. assumption.
    - destruct H. destruct H. assumption.
Qed.
    

Definition iteratorStep  (I: Iterator) : Z := 
    match I with 
    | iterator _ _ _step => _step
    end.

Definition iteratorStart (I: Iterator) : Z := 
    match I with 
    | iterator _start _ _ => _start
    end.

Definition iteratorEnd (I: Iterator) : Z := 
    match I with 
    | iterator _ _end _ => _end
    end.

Compute iteratorStep myIterator.
Compute iteratorStart myIterator.
Compute iteratorEnd myIterator.

(* Lemma mul_comm : forall a b : Z, a * b = b * a.
Proof.
    intros.
    induction a.
    - induction b.
        + reflexivity.
        + 

Lemma mul_assoc : forall a b c : Z, (a * b) * c = a * (b * c).
Proof.
    intros. induction a.
    - reflexivity.
    - simpl.
     *)

Lemma add_of_iter : forall x c: Z, forall I: Iterator,
      (inIterator x I) -> 
      (inIterator (x + c) 
        (iterator ((iteratorStart I) + c) 
                  ((iteratorEnd I) + c)
                  (iteratorStep I))).
Proof.
        intros. destruct I.
        (* destruct I _now_ because we want the same _start, _end, _step
           in hypothesis and consequent*)
        unfold inIterator in H. 
        unfold iteratorStart. unfold iteratorEnd. unfold iteratorStep.
        unfold inIterator. destruct _step. 
            (* todo: x = _start is the first case, I want 
                preconditions for the other two cases too!*)
            - rewrite H. reflexivity.
            - destruct H as [H0 H2]. destruct H0 as [H0 H1]. repeat split.
                + apply Zplus_le_compat_r. assumption.
                + apply Zplus_le_compat_r. assumption.
                + assert (x + c - (_start + c) = x - _start). ring.
                  rewrite H. assumption.
            - destruct H as [H0 H2]. destruct H0 as [H0 H1]. repeat split.
                + apply Zplus_le_compat_r. assumption.
                + apply Zplus_le_compat_r. assumption.
                + assert (_start + c - (x + c) = _start - x). ring. 
                  rewrite H. assumption.
Qed.

Lemma mod_of_iter : forall x  c : Z, forall I : Iterator,
    (c | (iteratorStep I)) /\ (inIterator x I) -> x mod c = (iteratorStart I) mod c.
Proof.
    intros. destruct H. destruct I. unfold iteratorStep in H. 
    unfold iteratorStart. unfold inIterator in H0. destruct _step.

    - rewrite -> H0. reflexivity.
    - destruct H0. destruct H1. assert (c | x0 * Z.pos p). 
        + apply Zdivide_mult_r. assumption.
        + assert (c | x - _start). rewrite H1. assumption.
            ++ destruct H3. assert (x = _start  + x1 * c). rewrite <- H3. ring.
               rewrite -> H4. apply Z_mod_plus_full.
    - destruct H0. destruct H1. assert (c | x0 * Z.neg p).
        + apply Zdivide_mult_r. assumption.
        + assert (c | _start - x). rewrite H1. assumption.
            ++ destruct H3. assert (_start = x + x1 * c). rewrite <- H3. ring.
               rewrite -> H4. symmetry. apply Z_mod_plus_full.
Qed.
    (* apply Zdivide_mod in H. apply Zdivide_mod in H1. *)

    (* unfold Z.modulo in H1. unfold Z.modulo in H. *)
    (* - destruct H0. unfold Z.divide in H1. unfold Z.divide in H. *)


Lemma div_of_iter : forall x c : Z, forall I : Iterator,
    (c <> 0) /\ (c | (iteratorStep I)) /\ (inIterator x I) /\ 
        (inIterator (iteratorEnd I) I) -> 
    (inIterator (x / c) 
        (iterator ((iteratorStart I) / c) 
                  ((iteratorEnd I) / c) 
                  ((iteratorStep I) / c))).
Proof.
    intros. destruct H as [H0 [H1 [H2 H3]]]. destruct I. 
    unfold iteratorStep in H1. 
    unfold iteratorEnd in H3. 
    unfold iteratorStart. unfold iteratorEnd. unfold iteratorStep.
    (* common steps taken out *)
    destruct H1 as [step_by_c H1].
    rewrite H1.
    (* rewrite using lemma instead of trying to apply the lemma *)
    rewrite Z_div_mult_full.
    (* prove the second goal first as it is easy *)
    2: assumption.
    (* go on as usual *)
    unfold inIterator in H2. 
    unfold inIterator in H3.
    unfold inIterator.
    induction _step as [ | step | step ].
    (* easy when step is 0 *)
    - assert (step_by_c = 0) as H4. nia.
      rewrite H4. rewrite H2. simpl. reflexivity.
    (* now step is positive *)
    - destruct H2 as [[H21 H22] H23]. destruct H3 as [[H31 H32] H33].
      destruct H23 as [x_minus_start_by_step H23].
      rewrite H1 in H23.
      assert (x = _start + x_minus_start_by_step * step_by_c * c) 
        as H4 by nia.
      assert (x / c = _start / c + x_minus_start_by_step * step_by_c)
        as H5.
        rewrite H4. apply Z_div_plus_full. assumption.
      (* induction directly on step_by_c *)
      induction step_by_c as [ | step_by_c | step_by_c ].
      (* step by c = 0 is invalid since step is positive *)
      + discriminate.
      (* step by c is positive *)
      + repeat split.
        (* lower bound *)
        -- apply Z_div_le. nia. assumption.
        (* upper bound *)
        -- apply Z_div_le. nia. assumption.
        (* divisibility *)
        -- exists x_minus_start_by_step. rewrite H5. ring.
      (* step by c is negative *)
      + repeat split.
        (* lower bound *)
        -- assert (-_end / -c <= -x / -c) as H6.
            apply Z_div_le. nia. nia.
           repeat rewrite Zdiv_opp_opp in H6. assumption.
        (* upper bound *)
        -- assert (-x / -c <= -_start / -c) as H6.
            apply Z_div_le. nia. nia.
           repeat rewrite Zdiv_opp_opp in H6. assumption.
        (* divisibility *)
        -- exists (-x_minus_start_by_step). rewrite H5. ring.
    (* now step is negative *)
    - destruct H2 as [[H21 H22] H23]. destruct H3 as [[H31 H32] H33].
      destruct H23 as [x_minus_start_by_step H23].
      rewrite H1 in H23.
      assert (x = _start + (- x_minus_start_by_step) * step_by_c * c) 
        as H4 by nia.
      assert (x / c = _start / c + (- x_minus_start_by_step) * step_by_c)
        as H5.
        rewrite H4. apply Z_div_plus_full. assumption.
      (* induction directly on step by c *)
      induction step_by_c as [ | step_by_c | step_by_c ].
      (* step by c = 0 is invalid since step is negative *)
      + discriminate.
      (* step by c is positive *)
      + repeat split.
        (* lower bound *)
        -- assert (-_start / -c <= -x / -c) as H6.
            apply Z_div_le. nia. nia.
          repeat rewrite Zdiv_opp_opp in H6. assumption.
        (* upper bound *)
        -- assert (-x / -c <= -_end / -c) as H6.
            apply Z_div_le. nia. nia.
          repeat rewrite Zdiv_opp_opp in H6. assumption.
        (* divisibility *)
        -- exists (-x_minus_start_by_step). rewrite H5. ring.
      (* step by c is negative *)
      + repeat split.
        (* lower bound *)
        -- apply Z_div_le. nia. assumption.
        (* upper bound *)
        -- apply Z_div_le. nia. assumption.
        (* divisibility *)
        -- exists x_minus_start_by_step. rewrite H5. ring.
Qed.

Definition kthIterVal (k : Z) (I : Iterator) :=
  (iteratorStart I) + (k-1) * (iteratorStep I).

Compute kthIterVal 3 (iterator 2 100 3).

Inductive Interval : Type :=
    | interval (_start _end : Z).

Definition intervalStart (I: Interval) : Z :=
    match I with
    interval _start _ => _start
    end.

Definition intervalEnd (I: Interval) : Z := 
    match I with
    interval _ _end => _end
    end.

Notation intervalMin := intervalStart.
Notation intervalMax := intervalEnd.


Definition inInterval (x: Z) (I: Interval) :=
    match I with
    interval _start _end => _start <= x <= _end
    end.


Definition myInterval : Interval := interval (-5) 10.

Remark is_in_myinterval : (inInterval 0 myInterval).
Proof. simpl. split. discriminate. discriminate.
Qed.

Remark not_in_myinterval : ~ (inInterval 12 myInterval).
Proof. unfold not. intros H. destruct H as [H0 H1].
    destruct H1. reflexivity.
Qed.


(* Does defining intervals as special cases of Iterator with step 1 help ? *)

Theorem interval_add : forall a b : Z, forall A B : Interval, 
    (inInterval a A) /\ (inInterval b B) -> 
    (inInterval (a + b) 
        (interval ((intervalStart A) + (intervalStart B))
                  ((intervalEnd A) + (intervalEnd B)))).
Proof.
    intros a b A B H. destruct H as [H0 H1]. unfold inInterval.
    destruct A as [aStart aEnd]. destruct B as [bStart bEnd]. 
    unfold intervalStart. unfold intervalEnd. 
    unfold inInterval in H0. unfold inInterval in H1.
    destruct H1 as [H2 H3]. destruct H0 as [H0 H1].
    split; apply Zplus_le_compat. all: assumption.
Qed.

Theorem interval_sub: forall a b : Z, forall A B : Interval,
    (inInterval a A) /\ (inInterval b B) -> 
    (inInterval (a - b)
        (interval ((intervalStart A) - (intervalEnd B))
                  ((intervalEnd A) - (intervalStart B)))).
Proof.
    intros a b A B H. destruct H as [H0 H1]. unfold inInterval.
    destruct A as [aStart aEnd]. destruct B as [bStart bEnd].
    unfold intervalStart. unfold intervalEnd.
    unfold inInterval in H0. unfold inInterval in H1.
    destruct H1 as [H2 H3]. destruct H0 as [H0 H1].
    split.
    - apply Zplus_le_compat.
        + assumption.
        + apply Zle_minus_le_0 in H3. apply Zle_0_minus_le.
            assert ((- b -- bEnd) = (bEnd - b)). ring.
            destruct H. assumption.
    - apply Zplus_le_compat.
        + assumption. 
        + apply Zle_minus_le_0 in H2. apply Zle_0_minus_le.
            assert ((- bStart - - b) = (b - bStart)). ring.
            destruct H. assumption.
Qed.


Lemma iterator_to_interval : forall x : Z, forall It : Iterator,
    (inIterator x It) -> (inInterval x (interval (iteratorMin It) (iteratorMax It))).
Proof.
    intros x It. intros H. unfold inIterator in H.  unfold inInterval.
    unfold iteratorMin. unfold iteratorMax. destruct It. destruct _step.
    - split. all: rewrite <- H. all: apply always_leq.
    - destruct H. assumption.
    - destruct H. assumption.
Qed.

(* Iterator Interval Equivalency *)

Lemma iterator_interval_eq : forall x : Z, forall In : Interval, 
    (inInterval x In) -> 
    (inIterator x (iterator (intervalStart In) (intervalEnd In) 1)).
Proof.
    intros. destruct In. unfold inInterval in H.
    unfold intervalStart. unfold intervalEnd.
    unfold inIterator. split.
    - assumption.
    - exists (x - _start). ring.
Qed.

Lemma interval_div : forall x c : Z, forall In : Interval,
    (inInterval x In) /\ ((intervalStart In) / c) = ((intervalEnd In) / c) 
    /\ c <> 0 ->
    x / c = (intervalStart In) / c.
Proof.
    intros. destruct H as [H0 [H1 H2]]. destruct In.
    unfold intervalMin in H1. unfold intervalMax in H1.
    unfold inInterval in H0. destruct H0 as [H3 H4]. unfold intervalMin.
    induction c.
        - contradiction. (* c is nonzero *)
        - apply (@Z_div_le _ _ (Z.pos p)) in H3. 
          apply (@Z_div_le _ _ (Z.pos p)) in H4.
          rewrite <- H1 in H4. nia. nia. nia.
        - assert ( - Z.neg p > 0). nia.
          assert (-x <= -_start) as H5. nia.
          assert (-_end <= -x) as H6. nia.
          apply (@Z_div_le _ _ (- Z.neg p)) in H5.
          apply (@Z_div_le _ _ (- Z.neg p)) in H6.
          repeat rewrite Zdiv_opp_opp in H5.
          repeat rewrite Zdiv_opp_opp in H6.
          rewrite <- H1 in H6. nia. nia. nia.
Qed.
(* Maybe this does not work if the divisor is negative *)
