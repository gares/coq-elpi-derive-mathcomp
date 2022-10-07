
## Coq-Elpi's derive for MathComp

This package links the derivations in `elpi.apps.derive` to
structures of the Mathematical Components library.

```coq
From elpi.apps.derive.mathcomp Require Import std.

From mathcomp Require Import ssrbool ssrfun eqtype.

#[only(eqType)] derive nat.

Check forall x : nat, x == x.
```
