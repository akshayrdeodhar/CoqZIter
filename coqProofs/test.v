From Coq Require Import ZArith.
Local Open Scope Z_scope.

(* Prove that addition is commutative *)
Theorem commutative_addition : forall a b : Z, a + b = b + a.
Proof.
    apply Z.add_comm.
Qed.

Inductive MySet : Type :=
    | Inclusive (a : Z) (b: Z). (* set of integers including a and b *)

    (* TODO: Step must be positive *)
Inductive Iterator : Type :=
    | iterator (_start _end _step : Z).

Definition inMySet (x : Z) (A : MySet) : Prop :=
    match A with
    | Inclusive a b => a <= x /\ x <= b
    end.

Definition inIterator (x : Z) (I : Iterator) :=
    match I with 
    | iterator _start _end _step => 
        match _step with
        | Z0 => x = _start 
        | Zpos _ => _start <= x /\ x <= _end /\ (_step | (x - _start))
        | Zneg _ => _end <= x /\ x <= _start /\ (_step | (_start - x))
        end
    end.

Check (inIterator 8 (iterator 1 10 1)).
Theorem in_iterator : (inIterator 8 (iterator 1 10 1)).
Proof. simpl. split. 
    - discriminate.
    - split.
        + discriminate.
        + exists 7. reflexivity.
Qed.

