Require Import ZArith.
Require Import List.
Require Import Coq.Sorting.Permutation.
Require Import Util_Z.
Require Import Util_list.

Definition prc (o:Z) (O: list Z) (R: Z -> Z) (L: Z -> Z) (P: Z -> bool) (X: Z -> list Z): bool :=
  andb (orb (negb (ifb (In_dec Z.eq_dec (R o) (X (L o)))))
            (andb (leb (length (filter (fun x => ifb (In_dec Z.eq_dec (R x) (X (L o)))) O)) 1)
                  (forallb (fun x => orb (negb (ifb (In_dec Z.eq_dec (R x) (X (L o)))))
                                         (Z.eqb (L x) (L o))) O)))
       (orb (forallb (fun x => Z.ltb (R o) (R x)) O)
            (andb (P o)
                  (andb (ifb (In_dec Z.eq_dec (R o) (X (L o))))
                        (forallb (fun x => orb (Z.ltb (R o) (R x)) 
                                               (andb (ifb (In_dec Z.eq_dec (R x) (X (L o))))
                                                     (andb (Z.eqb (L x) (L o))
                                                           (Z.leb (R o) (R x + 1))))) O)))).

Lemma prc_perm:
  forall O O' o R L P X
         (PRC: prc o O R L P X = true)
         (PERM: Permutation O' O),
    prc o O' R L P X = true.
Proof.
  unfold prc.
  intros.
  apply Coq.Bool.Bool.andb_true_iff in PRC.
  destruct PRC as (PRC1,PRC2).
  apply Coq.Bool.Bool.orb_true_iff in PRC1.
  apply Coq.Bool.Bool.orb_true_iff in PRC2.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  apply Coq.Bool.Bool.orb_true_iff.
  destruct PRC1 as [PRC1|PRC1].
  left.
  assumption.
  right.
  apply Coq.Bool.Bool.andb_true_iff in PRC1.
  destruct PRC1 as (PRC1,PRC1').
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  apply Nat.leb_le.
  apply Nat.leb_le in PRC1.
  rewrite prem_length_eq with (l':=O).
  assumption.
  assumption. 
  apply forallb_forall.
  intros.
  apply forallb_forall with (x:=x) in PRC1'.
  apply PRC1'.
  apply Permutation_in with O'.
  assumption.
  assumption.
  apply Coq.Bool.Bool.orb_true_iff.
  destruct PRC2 as [PRC2|PRC2].
  left.
  apply forallb_forall.
  intros.
  apply forallb_forall with (x:=x) in PRC2.
  apply PRC2.
  apply Permutation_in with O'.
  assumption.
  assumption.
  right.
  apply Coq.Bool.Bool.andb_true_iff in PRC2.
  destruct PRC2 as (PRC2, PRC2').
  apply Coq.Bool.Bool.andb_true_iff in PRC2'.
  destruct PRC2' as (PRC2', PRC2'').
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  assumption.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  assumption.
  apply forallb_forall.
  intros.
  apply forallb_forall with (x:=x) in PRC2''.
  apply PRC2''.
  apply Permutation_in with O'.
  assumption.
  assumption.
Qed.
