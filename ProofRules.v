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

Theorem rule_Let a a'' c1 c2 x R I L M P X:
  forall a'
         (RULE1: correct a c1 a' R I L M P X)
         (RULE2: forall z, correct (a' z) (subs c2 (subse x z)) a'' R I L M P X),
    correct a (Let x c1 c2) a'' R I L M P X.
Proof.
  unfold correct.
  simpl.
  intros.
  eapply sat_weak_imp.
  assumption.
  apply RULE1.
  assumption.
  assumption.
  intros.
  unfold id.
  simpl.
  specialize RULE2 with (z:=z).
  apply RULE2 in SAT0.
  apply sat_pre_subs3 in SAT0.
  assumption.
  assumption.
  assumption.
Qed.

Theorem rule_conseq a1 a2 c R I L M P X:
  forall a1' a2' (RULE: correct a1 c a2 R I L M P X)
         (IMP1: a1' |= a1)
         (IMP2: forall z, a2 z |= a2' z),
    correct a1' c a2' R I L M P X.
Proof.
  unfold correct.
  intros.
  apply sat_weak_imp with a2. 
  assumption.
  apply RULE.
  assumption.
  apply IMP1.
  assumption.
  assumption.
  intros.
  apply IMP2.
  assumption.
  assumption.
Qed. 

Theorem rule_fork c o o' a R I L M P X:
  correct (Aobs o' ** a) c (fun _ => Aobs nil) R I L M P X ->
    correct (Aobs (o ++ o') ** a ) (Fork c) (fun _ => Aobs o) R I L M P X.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(opo1o2,rest))))))))))).
  destruct rest as (rest,(satp2,(p1p2,c1c2))).
  destruct rest as (p1N,(d1N,op)).
  exists o, o'.
  exists (emp knowledge), p.
  exists.
  apply phpdef_comm.
  apply phpdef_emp.
  exists.
  apply boundph_emp.
  exists.
  assumption.
  exists.
  rewrite phplus_comm.
  rewrite phplus_emp.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  exists (Some (o++o')), None.
  exists empb, C.
  exists.
  inversion op.
  rewrite <- H2 in opo1o2.
  inversion opo1o2.
  apply fs_op.
  apply Permutation_trans with o'0.
  assumption.
  assumption.
  split.
  exists (emp knowledge), (emp knowledge).
  exists.
  apply phpdef_emp.
  exists.
  apply boundph_emp.
  exists.
  apply boundph_emp.
  exists.
  apply boundph_emp.
  exists (Some (o++o')), None.
  exists empb, empb.
  exists.
  apply fs_op.
  apply Permutation_refl.
  split.
  split.
  reflexivity.
  split.
  reflexivity.
  apply fs_op.
  apply Permutation_refl.
  split.
  intros.
  destruct SAT as (p'N,(C'N,opoO')).
  rewrite p'N, C'N in *.
  split.
  apply phplus_emp.
  split.
  apply bplus_emp.
  inversion opoO'.
  rewrite <- H2 in OPLUS.
  inversion OPLUS.
  apply fs_op.
  apply Permutation_trans with o'0.
  assumption.
  assumption.
  split.
  apply phplus_emp.
  apply bplus_emp.
  assert (o2N: o2 = None).
  {
  inversion op.
  rewrite <- H2 in opo1o2.
  inversion opo1o2.
  reflexivity.
  }
  rewrite o2N in *.
  assert (G: sat p (Some o') C (weakest_pre c (fun _ => Aobs nil) id R I L M P X)).
  apply H.
  assumption.
  exists (emp knowledge), p2.
  exists.
  apply phpdef_comm.
  apply phpdef_emp.
  exists.
  apply boundph_emp.
  exists bp2.
  exists.
  rewrite phplus_comm.
  rewrite phplus_emp.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  exists (Some o'), None.
  exists empb, c2.
  split.
  apply fs_op.
  apply Permutation_refl.
  split.
  split.
  reflexivity.
  split.
  reflexivity.
  apply fs_op.
  apply Permutation_refl.
  rewrite d1N in c1c2.
  rewrite bplus_comm in c1c2.
  rewrite bplus_emp in c1c2.
  rewrite <- c1c2.
  rewrite bplus_comm.
  rewrite bplus_emp.
  rewrite phplus_comm.
  rewrite phplus_emp.
  rewrite p1N in p1p2.
  rewrite phplus_comm in p1p2.
  rewrite phplus_emp in p1p2.
  rewrite <- p1p2.
  auto.
  apply phpdef_comm.
  apply phpdef_emp.
  apply phpdef_comm.
  apply phpdef_emp.
  split.
  intros.
  destruct SAT as (p'N,(C'N,opo'O)).
  rewrite p'N.
  rewrite phplus_emp.
  rewrite C'N.
  rewrite bplus_emp.
  inversion opo'O.
  rewrite <- H2 in OPLUS.
  inversion OPLUS.
  apply sat_O_perm with o'.
  apply Permutation_trans with o'0.
  assumption.
  assumption.
  assumption.
  rewrite phplus_comm.
  rewrite phplus_emp.
  rewrite bplus_comm.
  rewrite bplus_emp.
  auto.
  apply phpdef_comm.
  apply phpdef_emp.
Qed.

Theorem rule_Cons e R I L M P X:
  correct (Abool true) (Cons e) (fun r => Apointsto 1 r ([[e]])) R I L M P X.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT0 as (f', p'v).
  unfold phplusdef in PHPDEF.
  specialize PHPDEF with v.
  unfold phplus.
  rewrite p'v.
  rewrite p'v in PHPDEF.
  destruct (p v) eqn:pv.
  destruct k;
  try contradiction.
  rewrite PHPDEF.
  exists (f+f')%Qc.
  rewrite Qcplus_comm.
  rewrite <- Qcplus_assoc.
  replace (f' + f)%Qc with (f + f')%Qc.
  reflexivity.
  apply Qcplus_comm.
  exists f'.
  reflexivity.
Qed.

Theorem rule_Newlock R I L M P X r x:
  correct (Abool true) Newlock 
             (fun l => Abool (andb (Z.eqb (R l) r)(ifb (list_eq_dec Z.eq_dec (X l) x))) &* Aulock l empb empb empb) R I L M P X.
Proof.
  unfold correct.
  intros.
  simpl.
  intros.
  exists r,x.
  intros.
  destruct SAT0 as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(C1,(C2,(opo1o2,tmp))))))))))).
  destruct tmp as (bl,(p1v,(p1p2,C1C2))).
  rewrite <- p1p2 in PHPDEF.
  assert (phpdefpp1p2: phplusdef p p1 /\ phplusdef p p2).
  {
  apply phpdef_dist'.
  assumption.
  assumption.
  }

  split.
  assumption.
  rewrite <- p1p2.
  rewrite <- phplus_assoc.
  rewrite phplus_comm.
  apply phplus_ulock.
  apply phpdef_assoc.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  tauto.
  {
  apply phpdef_pair'.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  tauto.
  }
  tauto.
  {
  apply phpdef_pair'.
  tauto.
  tauto.
  tauto.
  }
  tauto.
  tauto.
  tauto.
Qed.
