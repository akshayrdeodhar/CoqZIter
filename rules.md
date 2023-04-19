
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
        - If $c | step$, then $x \% c = start \% c$
    - If $x = I$
        - If $c | step$ then $x / c = I(start / c, end / c, step / c)$
    - If $x = I$%
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

    - If $x % c + y % c \in [k * c, (k + 1) * c) \forall x, y$ then $(x + y) / c = x / c + y / c + k$ 
        - For this case, $k \in {0, 1}$.

    - If $x_1 % c + x_2 % c + ... x_{n - 1} % c \in [k * c, (k + 1) * c) \forall x_1, x_2, x_3, .. x_n then $(x_1 + x_2 + .. x_n) / c = (x_1 + x_2 + .. x_{n - 1}) / c + x_n / y + k
    - $x_1 % c + x_2 % c + ... x_{n - 1} % c \in [k * c, (k + 1) * c]$ \forall x_1, x_2, .. x_n$ is equivalent to:
    - $(x_1 + x_2 + .. x_{n - 1}) % c + x_n % c \in [k * c, (k + 1) * c]$ \forall (x_1 + x_2 + .. x_{n - 1}) % c, x_n % c
    - TODO: prove that the "ring" formed by $(a_1 + a_2 + .. a_{n - 1}) % c$ with $g = gcd(d_1, d_2, .. d_{n - 1}$
    - $\forall x_1, x_2, .. x_n, (x_1 + x_2 + .. x_{n - 1}) % c = (
    - Idea: show that (x_1 + x_2) is of the form (a_1 + a_2 + n_1 * d_1 + n_2 * d_2) aka (a_1 + a_2 + n_1 * g * d_1' + n_2 * g * d_2')

7. Inequalities
    - When you have knowledge about


