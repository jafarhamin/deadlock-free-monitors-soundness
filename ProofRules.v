Require Import Qcanon.
Require Import ZArith.
Require Import List.
Require Import Coq.Sorting.Permutation.
Require Import Util_Z.
Require Import Util_list.
Require Import Programs.
Require Import Assertions.
Require Import WeakestPrecondition.
Require Import PrecedenceRelation.

Set Implicit Arguments.

Open Local Scope Z.

Definition correct a c a' R I L M P X :=
 a |= weakest_pre c a' id R I L M P X.
