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
bibliography: "references.bib"
nocite: |
  @*
---

\newtheorem{theorem}{Lemma}

# Motivation

Plasticine [@plasticine] is a coarse-grained reconfigurable architecture for deep learning training and inference workloads. The architecture consists of a grid of Pattern Compute Units (PCUs) and Pattern Memory Units (PMUs) connected by an on-chip programmable switching fabric. Off-chip memory access is carried out using Address Generator and Coalescing Units (AGCUs).The hardware can be programmed using a \emph{template DSL}. Address calculations in the PMU and AGCU are done using a reconfigurable scalar datapath.[@plasticine] Loop induction variables are programmed using a set of counter chains, where counter start, step and bound can be configured. The number of stages on the datapath are limited. Multidimensional tensor accesses and software-defined banking (where a single large tensor is partitioned over multiple PMUs) lead to complicated address or control expressions for which the available stages are insufficient. Handling this requires the use of an extra PMU purely for address calculations. The DSL compiler, therefore has a set of arithmetic rewrite rules which replace address expressions with simpler expressions that use less operations or datapath stages. Rewrite rules are also used for supporting operations such as $/$ or $\%$, which are not supported in the hardware, but can be transformed into $>>$ or $\&$ in special cases. These rules are not standard mathematical identities- they check certain constraints on the values involved in the expression based on information that is known at compile time. The rules can be applied when the constraints are satisfied. If the correctness of a rule has not been proven before addition to the compiler, an incorrect rewrite rule might, in some specific case, replace an expression with another which is not equivalent to the original.

Complex array access expressions also occur in general nested loop programs. Previous work[@strength] has investigated strength reduction for optimizing complicated array index expressions. If loop bounds are known at compile time, the same rewrite rules can be applied to general nested loop programs.

<!--- the "rough" problem statement concludes the motivation -->

This project aims to achieve the following goals.

1. Evaluate the feasibility of using a theorem prover for proving arithmetic expression rewrite rules.

2. Write checked proofs, or disprove a set of rules, and add stronger preconditions to correct the incorrect rules.

3. Create a set of lemmas or a methodology for developing proofs for new rules.

# Problem Statement

Our _concrete_ problem statement is the following:

1. Evaluate the feasibility of using the **Coq** proof assistant for proving arithmetic expression rewrite rules designed for reducing reconfigurable scalar datapath stages by eliminating arithmetic operations, or replacing them with simpler operations.

2. Prove and disprove theorems of the following forms, on **integers**.
    - The value of an expression $e \in [L({subexpression\_bounds}), R({subexpression\_bounds})]$, where ${subexpression\_bounds}$ is the set of conservative bounds for the subexpressions of $e$, where $e$ is of the form $e = e_1 {op} e_2, and $L$ and $R$ are functions that define the bounds of $e$ in terms of ${subexpression\_bounds}$.
    - If $e = f(e_1, e_2, .. e_{n_1})$ and conditions $C_1, C_2, C_3, .. C_m$ hold, then $e = f'(e_1', e_2', ... e_{n_2}')$. (that is, $f$ can be safely replaced with $f'$ in the program. Note that the reverse transformation may not always be correct).[^2]

[^2]: We shall refer to $f$ as the _original expression_ and $f'$ as the _replacement expression_.

3. Enable more proofs of the same kind by:
    - Defining primitives for expressing intervals and iterators.
    - Laying the foundation for a Coq library of results about bounds and transformations.
    - Extracting results repeatedly used in Coq proofs as independent Lemmas.
    - Documenting proof and tactic usage patterns that commonly occur in proofs of the above two kinds.

# Solution Overview

## Formalizing Transformations

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

```{label=originaldiv .c}
for (x = 2; x <= 10000; x += 6) {
    ...
    y = x/3;
    foo(y);
    ...
}
```

Now, the compiler can match $x \in iterator(2, 10000, 6)$ and $c = 3$ to generate the following transformed code eliminating a division operation in lieu of an addition in every iteration. If a code similar to this were running on a reconfigurable scalar datapath, we would eliminating a division stage in exchange for a parallel counter.

```{label=transformeddiv .c}
for (x = 2, y = 0; x <= 10000; x += 6, y += 2) {
    ...
    foo(y);
    ...
}
```

We then prove our set of theorems in Coq. For example, here is the proof of `Theorem div_of_iter_kth_val`{.v}. Some of our interesting `Theorems` and their proofs can be found in \autoref{proofs}. The rest are available on [github](https://github.com/akshayrdeodhar/cs6245proj).

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

## Proof Strategies

We observed some recurring patterns while using Coq to formalize our proofs which made our lives easier. We believe that the following strategies will be useful for proofs of a similar nature.

1. While simpler lemmas can be proven by repeated use of `destruct` and `unfold` (making the granularity of abstraction finer and finer) upon which the goals become easily apparent. For more involved proofs, however, a "guided" approach is necessary. It is better to create a proof sketch by hand, identify intermediate "goals" which make sense _intuitively_. Then, one can use lemmas from Coq libraries to reach these intermediate goals by:
    i. Breaking down existing Coq goals.
    ii. Reducing available hypotheses.
    iii. Alternatively, simply `assert` the intermediate goal that you seek to prove, to add it to the Coq goals. Then prove it like a normal goal, upon which it gets added to the hypotheses set.

2. There will be junctures where goals are reduced to arithmetic identities or results which intuitively make sense. It can however be cumbersome to track down a sequence of theorems to apply to prove these. Such goals usually are trivially proven by one of the following tactics:
    i. `ring`: For solving _equations_ involving _ring_ arithmetic operations. (+, -, $\times$).
    ii. `nia`: For solving _inequations_, trivially does manipulations on both sides of an inequality.
    iii. `remember`: For substituting a variable in place of a subexpression. (eg. Define a new $p$ as $p = z \times z'$ for a given $z$ and $z'$.

3. At some junctures, it seems that a particular Lemma from a library _is_ applicable, but Coq is unable to match it with existing hypotheses. Here, one can _explicitly_ specify which subexpressions Coq should try to match the lemma with. For example, the lemma `Z_div_le` makes a statement about 3 integers  `a, b, c`. One can match a particular subexpression `e` as `c` by invoking `apply (@Z_div_le _ _ e)`.

4. Use `destruct` judiciously. The `destruct` tactic breaks down conjunctions and disjunctions, expands inductive type definitions, or applies a hypothesis to all applicable cases and destroys it.
    i. Expanding type definitions in the correct order will result in smaller subgoals, and a succinct proof. Improper orders land you in limbo.
    ii. Be careful when destroying hypotheses! You might need them at a later point!

5. Use `induction` judiciously. While one can try to _brute-force_ a proof by cases by going down the rabbit hole of induction over all variables, this will mean reinventing the wheel, and will result in an explosion of subgoals, which can become tedious to keep track of. Proofs can be done succinctly and intuitively by using existing high-level theorems instead.

6. Intuitive non-trivial results are hard to find in the Coq library documents. Another approach here is to download the Coq source, and grep[^6] the results and the comments directly. Thankfully, lemmas in the `ZArith` module are peppered with useful comments, making this feasible.

[^6]: search

7. Intuitions about integers _can_ be wrong, and that becomes apparent when you try to prove your "intuitive" facts using theorems from `ZArith`.

8. The following libraries provide useful results that we used in our proofs:
    i. BinInt: results about arithmetic operations, identities, sundry arithmetic lemmas.
    ii. Zorder: operations on both sides of $\le$, $\ge$, $<$, $>$.
    iii. Znumbertheory: results about divisibility, gcd, modulo.
    iv. Zdiv: results about integer division. (The _division folding_ theorem that we set out to prove was an existing lemma in `Zdiv`).
    v. ZArith.Zarith (for `ring`).
    vi. Coq.micromega.Lia (for `nia`).

# Utility

This project aims to prevent the addtion of incorrect arithmetic rewrite rules (~peephole optimizations) to a compiler. The rules being considered are _general_, and only require compile time _precondition_ checks, rather than brute-force enumeration of all possible values. An incorrect rule might replace some original program expression with a _replacement expression_ which takes a different value for some corner case value of inputs. A developer might debug such a compiler bug by enumerating all values of the iterators involved in the corner case for which the rule fails, and fixing that specific corner case. Such ad-hoc fixes will not guarantee the correctness of the rule since the addition of new preconditions will end up fixing only the _specific instance_ where it fails, and there might be many more such "corner cases". What we truly want is to implement a general rule.

We show that such rules can be proved as theorems about numbers _before_ a developer adds them to the compiler. With a Coq-checked proof, we have a guarantee that the rule will hold, and the transformation will be correct as long as its preconditions are satisfied.
Such general rules only require a few precondition checks at compile time, as opposed to transformations checked by compile-time enumeration by a solver such as Z3.

The previous section demonstrates the usage of one Coq-checked rewrite rule by the compiler. Simple usage illustrations for other theorems/rules can be found in \autoref{theorems}.

## Workflow

We envision the usage of our idea by a compiler developer in the following workflow.

1. The developer finds a recurring expression pattern, and concocts a way to replace it with a cheaper expression. 

2. They express this optimization as a transformation rule with preconditions, and formalize it as a theorem of the form $precondition \implies e_{original} = e_{replacement}$ in Coq.

3. They attempt to prove the theorem using Coq standard library theorems, and lemmas that they have previously proven (somewhat like the library that we have developed).
   i. If the proof is successful, the rule may safely be implemented as a transformation in the compiler. 
   ii. If the proof leads to a contradiction, they repair their transformation by adding a stronger precondition.
  
4. If the proof does not _terminate_, there is no guarantee about its correctness. The developer might still choose to implement the the transformation, (for example, in cases where it is necessary for making a kernel work on a particular hardware platform), _with the knowledge that it might be incorrect_. If the developer encounters a corner case bug, they may choose to incorporate its fix into the theorem preconditions, and attempt to prove the rule again. 

We hope that this demonstration encourages the development of such Coq modules for different kinds of transformations.

# Related Work

Alive[@alive] is a verifier for peephole optimizations in LLVM built using Z3[@z3]. Alive converts converts LLVM optimization _left hand sides_ and _right hand sides_ to logical formulas, and verifies their equivalence over all possible cases using the Z3 SMT solver. Alive either proves validity, or outputs a counterexample.

Research on verification and synthesis of Halide _term rewrite rules_[@halide] also uses the Z3 SMT solver, but uses Coq for proving a subset of the rules by hand. The authors mention that the majority of rules for which Z3 times out involve the division and modulo operations.

The Peek[@peek] framework for CompCert[@compcert] proves a set of standard peephole peephole optimizations in Coq, in addition to a global proof that the application of these optimizations, in _combination_ produces a correct program.

The rewrite rules that we set out to prove will _not_ give significant performance improvements in standard CPU-based loop nests. In a sense, they are analogous to strength reduction[@strength], or induction variable elimination. The rules that we select are different from these optimizations due to the following factors-

Unlike strength reduction, which merely reduces expensive arithmetic operations in a loop nest, these are built to be applied in a reconfigurable scalar datapath with a limited number of stages, with some operations being _unavailable_. In some cases, such transformations are necessary for a buffer to _fit_ within a given number of memory units, while in others, they eliminate operations which are incomputable on the hardware. These rules are primarily concerned with _iterators_, _intervals_, and the _division_ and _modulo_ arithmetic operations.

\newpage

# Appendix A: Theorems, and their application {#theorems}

## Sundry Transformations

1. Division Folding
    - If $x \in \mathbb{Z} \wedge a > 0 \wedge b > 0$
      - $(x / a) / b = x / (a * b)$
    - Example: Scratchpad-match calculations might lead to multiple division operations on an address offset. An expression of the form $(x / 1024) / 4$ may be transformed to $x / (1024 * 4)$, which can be folded to $(x / 4096)$, saving a division operation.

## Bounds

1. Bounds Computation
    - If $x \in [a, b] \wedge y \in [c, d]$, then
      - $x + y \in [a + c, b + d]$
      - $x - y \in [a - d, b - c]$
    - Example:
  
      ```{.c}
        for (i = 205; i <= 250; i += 5) {
          for (j = 2; j <= 30; j += 4) {
            ...
            x = input();
            ...
            a = (j - x % 8 + 200) + i;
            index = a / 100;
            offset = a % 100;
            ...
          }
        }
      ```

      The bounds of $i$ and $j$ are known at compile time: $i \in [205, 250]$, $j \in [2, 30]$. Conservative bounds for $x \% 8$ are also known to be $[0, 7]$. Thus, $j - x \% 8 \in [-2, 30]$, $j - x \% 8 + 200 \in [198, 230]$, and $a \in [403, 480]$.

2. Expression Reduction using bounds
    - If $x \in [a, b] \wedge (a/c = b/c)$ then
      - $x / c = a/c$
      - $x \% c = a \% c + (x - a)$
    - Example:
        Continuing with the example above, since $a \in [403, 480]$, the compiler can replace $a/100$ with $4$ and $a \% 100$ with $3 + (x - 403)$. Depending on the rest of the program, the computation of $a$ might turn out to be dead code now, providing even further optimization opportunities.

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

- Example:
  
  ```{.c}
    for (i = 64; i <= 256; i+= 16) {
      bank = (i + 1) % 8;
    }
  ```

  In this example, $i \in I(64, 256, 16)$, with _iterator replacement_, the compiler concludes that $(i+1) \in I(65, 257, 16)$. Since $(8 | 16)$, $(i + 1) \% 8 = 65 \% 8 = 1$ by _modulo simplification_. This makes `bank` a loop independent constant, and can then be propagated out of the loop.

\newpage

# Appendix B: Selected Proofs {#proofs}

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

\newpage

# References
