From elpi.apps.derive.mathcomp Require Import std.

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype.

#[only(eqType)] derive nat.

Check forall x : nat, x == x.
