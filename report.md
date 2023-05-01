---
title: Correctness of address expression transformations
subtitle: Formally proving the correctness of integer arithmetic rewrite rules for optimizing address expressions using Coq
author: "Akshay Deodhar and Sparsh Jain"
date: "1 May 2023"
geometry: margin=2cm
colorlinks: "true"
---

## Problem Statement

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

## Solution Overview

We define an **Iterator** in terms of its _start_, _end_, and _step_. The definition is meant to characterize the _set of integer values that the iterator may take_, and can be used to represent a loop iterator of the form `FOR I = _START, _END, _STEP`{.f} or a hardware counter of the form `(_START until _END by _STEP)`{.py}

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

Notice the two conditions- the value must lie between the iterator bounds, and obtained by adding an integer multiple of `_step` to `_start`.

We define abstractions that will help us state theorems about iterators. 

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

We create similar definitions for *iteratorStep* and *iteratorMax*.

For a strength reduction or the use of a _parallel counter chain_[^3], we need to to ensure that the _replacement expression_ takes the same value as the _original expression_ for every step of the iterator.

```
(* k-th iteration may not be a valid iteration in the sense 
   that the value may not lie within the bounds. 
   This function accepts all integer values of k, including
   negative values. *)

```{.v}
Definition kthIterVal (k : Z) (I : Iterator) :=
  (iteratorStart I) + k * (iteratorStep I).
```



[^3]: B is a counter chain parallel to A if it executes in lock-step with A, and terminates when A terminates. Note that this is similar to _strength reduction_ with an auxiliary variable being updated every loop iteration.

```{.v}
Lemma div_of_iter_kth_val : forall x c k : Z, forall I : Iterator,
```

This is 





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
2. an overview of your solution approach, 

3. demonstration of the practicality of your approach through a prototype implementation in a compiler framework or through performance studies of handcoded examples, and 

4. a comparison with related work.
```
