From Coq Require Import ZArith.
Require Import Coq.Init.Logic.
Require Import Coq.Logic.Classical_Prop.
Require Import BinPos BinInt Decidable Zcompare Znumtheory Zorder.
Require Import Arith_base.

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

(*
Theorem interval_mul: forall x y xl xr yl yr prodmin prodmax: Z, forall X Y : Interval,
    xl = intervalMin X /\ xr = intervalMax X /\ yl = intervalMin Y /\ yr = intervalMax Y /\ 
    prodmin = (Z.min (Z.min (xl * yl) (xl * yr)) (Z.min (xr * yl) (xr * yr))) /\
    prodmax = (Z.max (Z.max (xl * yl) (xl * yr)) (Z.max (xr * yl) (xr * yr))) /\
    (inInterval x X) /\ (inInterval y Y)  ->
    (inInterval (x * y) (interval prodmin prodmax)).
Proof.
    intros x y xl xr yl yr prodmin prodmax X Y. intros H.
    unfold intervalMin in H. unfold intervalMax in H. 
    unfold inInterval in H. 
    destruct X in H. destruct Y in H.
    destruct H as [H0 [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]].
    unfold inInterval. split.
    - rewrite H4. rewrite <- H0 in H6. rewrite <- H1 in H6.
      rewrite <- H2 in H7. rewrite <- H3 in H7. induction x.
      destruct H6. destruct H7.
      + induction y.
        -- simpl. unfold Z.min.
           assert (0 <= (xl * yl)). 
           { induction xl. 
            { discriminate. }
            { discriminate H.
           assert ((xl * yr) <= 0).
           assert (0 <= (xr * yr)).
           assert ((xr * yl) <= 0). 
           ++ 
*)
