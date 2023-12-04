Declare ML Module "repro.plugin".
From Ltac2 Require Import Ltac2 Printf.

Ltac2 @ external push : unit -> int := "repro" "push".
Ltac2 @ external pop : int -> unit := "repro" "pop".
Ltac2 @ external reset : unit -> unit := "repro" "reset".

From Ltac2Compiler Require Import Ltac2Compiler.

Ltac2 test1 () :=
  let outer := push () in
  let inner := push () in
  ltac1:(assert False) >
  [pop inner; pop outer|printf "test"; let outer := push () in pop outer].

Ltac2 test2 () :=
  let outer := push () in
  let inner := push () in
  ltac1:(assert False) >
  [pop inner; pop outer|let outer := push () in pop outer].

Ltac2 Compile test1 test2.

Goal True /\ True.
  Succeed test1 ().
  reset ().
  Fail test2 ().
