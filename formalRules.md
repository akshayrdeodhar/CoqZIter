# Theorems

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
      - $\forall k \in Z, k^{th}Iter ~k~ I(start/c, end/c, step/c) k^{th}Iter ~k~ I(start, end, step)$
