From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype.
From elpi.apps Require Import derive.
From elpi.apps.derive Require Import eqb_core_defs tag fields eqb eqbcorrect eqbOK.

From elpi.apps.derive.mathcomp Extra Dependency "eqbP.elpi" as eqbP.
From elpi.apps.derive Extra Dependency "derive_hook.elpi" as derive_hook.

Elpi Command derive.eqbP.
Elpi Accumulate Db derive.eqbcorrect.db.
Elpi Accumulate Db derive.eqb.db.
Elpi Accumulate Db derive.eqbOK.db.
Elpi Accumulate File derive_hook.
Elpi Accumulate File eqbP.
Elpi Accumulate lp:{{
 main [str I, str O] :- !, 
    coq.locate I (indt GR), 
    Prefix is O ^ "_",
    derive.eqbP.main GR Prefix _.

  main [str I] :- !, 
    coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.eqbP.main GR Prefix _.

  main _ :- usage.
   
  usage :- coq.error "Usage: derive.eqb <inductive name> [<prefix>]".

}}.
Elpi Typecheck.

Elpi Accumulate derive lp:{{

dep1 "eqType" "eqbOK".
derivation T Prefix (derive "eqType" (derive.eqbP.main T Prefix)).

}}.
Elpi Accumulate derive File eqbP.
