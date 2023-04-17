1. If $x \in [a, b] \wedge y \in [c, d]$
    - $x + y \in [a + c, b + d]$
    - $x - y \in [a - d, b - c]$
    - $x * y \in $
    - $x / y \in $

2. If $x \in [a, b]$ then
    - $x / k$ => ? (constant or zero?)
    - $x \% k$ => ? (x or x + some constant?)

3. **Iterators**
    - Let I be an iterator (start, end, step)
    - $x \in I$ if $\exists n < (end - start) / step, x = start + n * step$

4. Iterator simplifications
    - If $x \in I(start, end, step)$
        - If $c | step$, then $x % c = start % c$
    - If $x = I$
        - If $c | step$ then $x / c = I(start / c, end / c, step / c)$
    - If $x = I$
        - $x + c$ = I(start + c, end, step)

5. Division simplifications
    - If $x \in I \wedge {something}$
    - $x / a / b = x / (a * b)$

6. Distributive properties:
    - Under _some_ conditions,
        - $(x + y) % c = $x % c + y % c + {constant}$
        - $(x + y) / c = $x / c + y / c + {constant}$
    - TODO: figure out which condition
    - Has something to do with the gcds of the steps of x and y, and whether the "ring" of modulos remains in [0, c - 1]


7. Inequalities
    - When you have knowledge about


