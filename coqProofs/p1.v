From Coq Require Import ZArith.
Local Open Scope Z_scope.


Definition interval(start, step, end: Z): bool := 
  