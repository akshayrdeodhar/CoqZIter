---
title: Correctness of address expression transformations
subtitle: Formally proving the correctness of integer arithmetic rewrite rules for optimizing address expressions using Coq
author: "Akshay Deodhar and Sparsh Jain"
date: "1 May 2023"
geometry: margin=2cm
colorlinks: "true"
header-includes:
    - \usepackage{amsthm}
    - \usepackage{amsmath}
    - \usepackage{amsfonts}
    - \usepackage{thmtools}
---

\newtheorem{theorem}{Lemma}

# Problem Statement

This project aims to achieve the following goals. (TODO: goals or problems statement?)

1. Evaluate the feasibility of using a theorem prover for proving arithmetic expression rewrite rules.

2. Write checked proofs, or disprove a set of rules, adding stronger preconditions to correct the incorrect rules.

3. Create a set of lemmas or a methodology for developing proofs for new rules.

The rewrite rules that we set out to prove will give significant performance improvements in standard CPU-based loop nests. In a sense, they are analogous to strength reduction, or induction variable elimination. The rules that we select are different from these optimizations due to the following factors-

1. Unlike strength reduction, which merely reduces expensive arithmetic operations in a loop nest, these are built to be applied in a reconfigurable scalar datapath with a limited number of stages, with some operations being _unavailable_. In some cases, such transformations are necessary for a buffer to _fit_ within a given number of memory units, while in others, they eliminate operations which are incomputable on the hardware. 

2. Because the workloads being compiled have long runtimes, this is a situation where a longer compile time can be traded off for better performance at runtime.[^1]

[^1]: Note that Coq itself _does not execute_ at compile time. The compile time overhead is due to the fact that the compiler will carry out a dataflow-style bounds analysis pass for establishing the intervals within which values of variables lie, and carry out multiple precondition checks before replacing an arithmetic expression with another (cheaper) expression.

3. These rules are primarily concerned with _iterators_, _intervals_, and the _division_ and _modulo_ arithmetic operations.

Specifically we shall,

1. Evaluate the feasibility of using the **Coq** proof assistant for proving arithmetic expression rewrite rules designed for reducing reconfigurable scalar datapath stages by eliminating arithmetic operations, or replacing them with simpler operations.

2. Prove and disprove theorems of the following forms, on **integers**.
    - The value of an expression $e \in [L({subexpression\_bounds}), R({subexpression\_bounds})]$, where ${subexpression\_bounds}$ is the set of conservative bounds for the subexpressions of $e$, where $e$ is of the form $e = e1 op e2$.
    - If $e = f(e_1, e_2, .. e_{n_1})$ and conditions $C_1, C_2, C_3, .. C_m$ hold, then $e = f'(e_1', e_2', ... e_{n_2}')$. (that is, $f$ can be safely replaced with $f'$ in the program. Note that the reverse transformation may not always be correct).[^2]

[^2]: We shall refer to $f$ as the _original expression_ and $f'$ as the _replacement expression_.

3. Enable (TODO: new theorem proofs) by:
    - Define primitives for expressing intervals and iterators.
    - Lay the foundation for a Coq library of results about bounds and transformations.
    - Extracting results repeatedly used in Coq proofs as independent Lemmas.
    - Document proof and tactic usage patterns that commonly occur in proofs of the above two kinds.

# Solution Overview

We start with proposing a set of theorems that can serve as a basis for analysis and transformations by the compiler once proven correct. These are provided in \autoref{theorems}.

As address expressions calculate byte offsets, and iterators take integer values, all of our transformations can be expressed as theorems on Integers. Hence, we utilize the `Zarith` module of the Coq Standard Library which defines the abstract binary integer type `Z`, operations on `Z`, and further contains a rich set of useful lemmas.

We define our **Iterator** in terms of its _start_, _end_, and _step_ values over `Z`. The definition is meant to characterize the _set of integer values that the iterator may take_, and can be used to represent a loop iterator of the form `FOR I = _START, _END, _STEP`{.f} or a hardware counter of the form `(_START until _END by _STEP)`{.py}.

```{.v}
Inductive Iterator : Type :=
    | iterator (_start _end _step : Z).
```

However, we don't wish to reason about the iterator itself, but the _values_ that an iterator might take. So we define what it means for a value to _belong_ to an iterator, as follows.

```{.v}
Definition inIterator (x : Z) (I : Iterator) :=
    match I with 
    | iterator _start _end _step => 
        match _step with
        | Z0 => x = _start 
        | Zpos _ => (_start <= x /\ x <= _end) /\ (_step | (x - _start))
        | Zneg _ => (_end <= x /\ x <= _start) /\ (_step | (_start - x))
        end
    end.
```

Notice the two conditions: the value must lie between the iterator bounds, and must be obtained by adding an integer multiple of `_step` to `_start`. We also define trivial getters to extract the value of `_start`, `_end`, `_step`, `min`, or `max` of an iterator. For example, the following function extracts the minimum value an iterator may take:

```{.v}
Definition iteratorMin (I : Iterator) : Z :=
match I with
| iterator _start _end _step => 
        match _step with 
        | Zneg _ => _end
        | _ => _start
        end
    end.
```

Similarly, we define our **Interval** in terms of its _start_ and _end_ values over `Z`. The definition is meant to characterize the bounds within which the value of an expression will lie.

```{.v}
Inductive Interval : Type :=
    | interval (_start _end : Z).

Definition inInterval (x: Z) (I: Interval) :=
    match I with
    interval _start _end => _start <= x <= _end
    end.
```

For a strength reduction or the use of a _parallel counter chain_[^3], we need to to ensure that the _replacement expression_ takes the same value as the _original expression_ for every step of the iterator. Hence, we define the following function to get the value of an iterator in its $k^{th}$ iteration[^4].

[^3]: B is a counter chain parallel to A if it executes in lock-step with A, and terminates when A terminates. Note that this is similar to _strength reduction_ with an auxiliary variable being updated every loop iteration.

[^4]: Note that our $k$ is zero-indexed.

```{.v}
Definition kthIterVal (k : Z) (I : Iterator) :=
  (iteratorStart I) + k * (iteratorStep I).
```

Now, we can formally define theorems for useful transformations in Coq. Below is a formalization of the following _Iterator Replacement_ transformation:

If $(c | step) \wedge x \in I(start, end, step)$, then

- $x / c \in I(start/c, end/c, step/c)$
- $\forall k \in Z, k^{th}Iter ~k~ I(start/c, end/c, step/c) = k^{th}Iter ~k~ I(start, end, step)$

```{.v}
Theorem div_of_iter : forall x c : Z, forall I : Iterator,
    (c <> 0) /\ (c | (iteratorStep I)) /\ (inIterator x I) -> 
    (inIterator (x / c) 
        (iterator ((iteratorStart I) / c) 
                  ((iteratorEnd I) / c) 
                  ((iteratorStep I) / c))).
```

```{.v}
Theorem div_of_iter_kth_val : forall x c k : Z, forall I : Iterator,
    (c <> 0) /\ (c | (iteratorStep I)) /\ (inIterator x I) -> 
    (kthIterVal k I) / c = kthIterVal k 
        (iterator ((iteratorStart I) / c) 
                  ((iteratorEnd I) / c) 
                  ((iteratorStep I) / c)).
```

The proof of these theorems implies the legality of the following transformation[^5]:

[^5]: Note that these theorems are stating facts about integers and hence any transformations they enable are platform agnostic.

```{.c}
for (x = 2; x <= 10000; x += 6) {
    ...
    y = x/3;
    foo(y);
    ...
}
```

Now, the compiler can match $x \in iterator(2, 100, 6)$ and $c = 3$ to generate the following transformed code eliminating a division operation in lieu of an addition in every iteration. If a code similar to this were running on a reconfigurable scalar datapath, we would eliminating a division stage in exchange for a parallel counter.

```{.c}
for (x = 2, y = 0; x <= 10000; x += 6, y += 2) {
    ...
    foo(y);
    ...
}
```

We then prove our set of theorems in Coq. For example, here is the proof of `Theorem div_of_iter_kth_val`{.v}. Some of our interesting `Theorems` and their proofs can be found in \autoref{proofs}. The rest are available on [github](https://gitfront.io/r/user-8813495/NSEjGqe31hHN/cs6245proj/).

```{.v}
Proof.
    intros. destruct H as [H0 [H1 H2]].
    destruct I. unfold iteratorStep in H1.
    unfold iteratorStart. unfold iteratorEnd. unfold iteratorStep.
    destruct H1 as [step_by_c H1].
    unfold inIterator in H2.
    unfold kthIterVal. unfold iteratorStart. unfold iteratorStep.
    rewrite H1. rewrite Z.mul_assoc. 
    rewrite Z_div_plus_full. 2: assumption.
    rewrite Z_div_mult_full. 2: assumption.
    reflexivity.
Qed.
```

During the course of our project, we observed some recurring patterns while using Coq to formalize our proofs which made our lives easier. We believe that the following strategies will be useful for proofs of a similar nature.

1. One of the most useful tactics was `assert`. It is in our best interest to first 

**Ideas about documentation**

- Use of assert (create a hand-written proof, and use that to guide your search for existing results about integers in the coq library, use steps of your proof as "waypoints" in the mechanical proof)
- Ring, Nia, Lia, Auto, Remember
- Judicious use of destruct (know when to destruct what)
- Judicious use of induction (when there are multiple cases that you want to consider, don't immediately do a cross product of all cases, .. ?)
    - Try to use general lemmas already available in the library rather than going to the _lowest level_ (aka expand all operations and induction on all variables). That becomes tedious to keep track of.
- How to search for results (download coq source, use comments to guide your search for a particular *kind* of fact, or facts about a particular operation)
- Sometimes, when you are unsure about a rule, you might:
    - Think you reached a goal in coq for which you can find a counterexample
    - start thinking that the goal is wrong, but if coq checks your proof, its guaranteed to be correct.
- Intuitions about integers _can_ be wrong, and that becomes apparent when you try to prove your "intuitive" facts using theorems from Zarith.
- Libraries (from ZArith)
    - BinInt (results about arithmetic operations, identities, sundry arithmetic lemmas)
    - Zorder (operations on both sides of <= / >=, 
    - Zcompare (lemmas about comparison _operators_ Gt?)
    - Znumbertheory: results about divisibility, gcd, modulo)
    - Zdiv: (results about integer division)
    - ZArith.Zarith (for ***ring***)
    - Coq.nicromega.Lia (Nia: nonlinear integer arithmetic (solver?))

```
1. an overview of your solution approach, 

2. demonstration of the practicality of your approach through a prototype implementation in a compiler framework or through performance studies of handcoded examples, and 

3. a comparison with related work.
```

# Appendix A: Theorems {#theorems}

## Sundry Transformations

1. Division Folding
    - If $x \in \mathbb{Z} \wedge a > 0 \wedge b > 0$
      - $(x / a) / b = x / (a * b)$

## Bounds

1. Bounds Computation
    - If $x \in [a, b] \wedge y \in [c, d]$, then
      - $x + y \in [a + c, b + d]$
      - $x - y \in [a - d, b - c]$

2. Expression Reduction using bounds
    - If $x \in [a, b]$ then
      - $x / k \to$ ? (constant or zero?)
      - $x \% k \to$ ? (x or x + some constant?)

## Iterators

- Let $I$ be an iterator $(start, end, step)$
- $x \in I$ if $(start <= x <= end) \wedge (step | (x - start))$
- $k^{th}Iter : (k : Z) (I : (start, end, step)) \to Z := start + k\times step$

1. Modulo Simplification
    - If $x \in I(start, end, step)$
      - $(c | step) \implies x \% c = start \% c$

2. Iterator Replacement
    - If $x \in I(start, end, step)$
      - $x + c \in$ I(start + c, end + c, step)
      - $\forall k \in Z, k^{th}Iter ~k~ I(start + c, end + c, step) = k^{th}Iter ~k~ I(start, end, step)$
    - If $(c | step) \wedge x \in I(start, end, step)$
      - $x / c \in I(start/c, end/c, step/c)$
      - $\forall k \in Z, k^{th}Iter ~k~ I(start/c, end/c, step/c) = k^{th}Iter ~k~ I(start, end, step)$

# Appendix B: Proofs (#proofs)

```{.v}
Theorem div_of_iter : forall x c : Z, forall I : Iterator,
    (c <> 0) /\ (c | (iteratorStep I)) /\ (inIterator x I) -> 
    (inIterator (x / c) 
        (iterator ((iteratorStart I) / c) 
                  ((iteratorEnd I) / c) 
                  ((iteratorStep I) / c))).
Proof.
    intros. destruct H as [H0 [H1 H2]]. destruct I. 
    unfold iteratorStep in H1. 
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
    unfold inIterator.
    induction _step as [ | step | step ].
    (* easy when step is 0 *)
    - assert (step_by_c = 0) as H4. nia.
      rewrite H4. rewrite H2. simpl. reflexivity.
    (* now step is positive *)
    - destruct H2 as [[H21 H22] H23].
      destruct H23 as [x_minus_start_by_step H23].
      rewrite H1 in H23.
      (* Intermediate lemma *)
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
    - destruct H2 as [[H21 H22] H23].
      destruct H23 as [x_minus_start_by_step H23].
      rewrite H1 in H23.
      (* Same intermediate lemma as above *)
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
```

```{.v}
Theorem interval_mod : forall x c : Z, forall In : Interval,
    (inInterval x In) /\ ((intervalStart In) / c) = ((intervalEnd In) / c) 
    /\ c <> 0 ->
    (x mod c) = ((intervalStart In) mod c) + (x - (intervalStart In)).
Proof.
    intros. apply interval_div in H as H0.
    destruct H as [H1 [H2 H3]]. destruct In.
    unfold intervalMin in H2. unfold intervalMax in H2.
    unfold inInterval in H1. unfold intervalMin in H0.
    unfold intervalMin. repeat rewrite Zmod_eq_full.
    rewrite H0. nia. assumption. assumption.
Qed.
```
