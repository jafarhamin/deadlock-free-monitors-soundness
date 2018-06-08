Require Import ZArith.
Require Import Util_Z.
Require Import Programs.
Require Import Assertions.
Require Import ProofRules.
Require Import Soundness.
Require Import UnprovedLemmas.


Notation "x '::=' c1 ';;' c2" := 
  (Let x c1 c2)(at level 50).

Notation "c1 ';' c2" := 
  (Let 0 c1 c2)(at level 50).

Notation "'[<' x '>]'" := 
  (Lookup x)(at level 50).

Notation "'[<<' x '>>]'" := 
  (Lookup (Evar x))(at level 50).

Notation "x '[:=]' y" := 
  (Mutate x y)(at level 50).

Notation "x '<+>' y" := 
  (Eplus x y)(at level 40).


Local Notation x := 1%Z.
Local Notation y := 2%Z.
Local Notation z := 3%Z.
Local Notation front := 4%Z.
Local Notation rear := 5%Z.

(** # <font size="5"><b> Queue </b></font> # *)

Example Newqueue (n: nat) : cmd := 
  x ::= Cons(n+2) ;;(
  (Evar x) [:=] (Enum 0) ;(
  ((Evar x) <+> (Enum 1)) [:=] (Enum 0);
  Val (Evar x))).

Example inc (e: exp) :=
  x ::= [< e >] ;;(
  e [:=] (Eplus (Evar x) (Enum 1))).

Example Enqueue (q: exp) (z: exp) : cmd := 
  rear ::= [< q <+> (Enum 1) >] ;;(
  q <+> (Enum 2) [:=] (q <+> Enum 2 <+> (Evar rear));(
  inc (Evar rear))).

Example Dequeue (q: exp) : cmd := 
  front ::= [< q <+> (Enum 2) >] ;;(
  x ::= [< q <+> Enum 2 <+> (Evar front) >] ;;(
  inc (Evar front) ;(
  Val (Evar x)))).

Example queue_example1 : cmd :=
  x ::= Newqueue 100 ;;(
  Enqueue (Evar x) (Enum 10) ;(
  y ::= Dequeue (Evar x) ;;(
  Val (Enum y)))).

(** # <font size="5"><b> Safety </b></font> # *)

Definition this_program_is_safe program :=
  forall n id,
    safe n (upd Z.eq_dec (emp (cmd * context)) id (Some (program, done))) (emp Z).
