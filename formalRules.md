
- If $x \in [a, b] \wedge y \in [c, d]$
  - $x + y \in [a + c, b + d]$
  - $x - y \in [a - d, b - c]$

- If $x \in [a, b]$ then
  - $x / k \to$ ? (constant or zero?)
  - $x \% k \to$ ? (x or x + some constant?)

- **Iterators**
  - Let $I$ be an iterator $(start, end, step)$
  - $x \in I$ if $(start <= x <= end) \wedge (step | (x - start))$

- If $x \in I(start, end, step)$
  - $(c | step) \implies x \% c = start \% c$
- If $x \in I$
  - $x + c \in$ I(start + c, end + c, step)

- If $x \in \mathbb{Z}$
  - $x / a / b = x / (a * b)$

