From elpi.apps Require Import derive.mathcomp.std.

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype.

#[only(eqType)] derive nat.

Check forall x : nat, x == x.
