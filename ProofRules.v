Require Import Qcanon.
Require Import ZArith.
Require Import List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sorting.Permutation.
Require Import Util_Z.
Require Import Util_list.
Require Import Programs.
Require Import Assertions.
Require Import WeakestPrecondition.

Set Implicit Arguments.

Open Local Scope Z.

Definition correct a c a' invs :=
 a |= weakest_pre c a' id invs.

Theorem rule_g_ctrinc invs gc n: correct 
  (Actr gc n) 
  (g_ctrinc gc)
  (fun _ => Actr gc (S n)%nat ** Atic gc) invs.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT as (n0,ggc).
  exists n, (emp knowledge), p.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, o.
  exists (upd Z.eq_dec g ([[gc]]) (Some (Some n, n0))).
  exists (upd Z.eq_dec (emp (option nat*nat)) ([[gc]]) (Some (None, O))).
  exists.
  unfold ghplusdef.
  unfold upd.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  trivial.
  unfold emp.
  destruct (g x); trivial.
  destruct p0.
  destruct o0; trivial.
  exists.
  unfold boundgh.
  unfold upd.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  symmetry in H.
  inversion H.
  apply bg with ([[gc]]).
  assumption.
  apply bg with x.
  assumption.
  exists.
  unfold boundgh.
  unfold upd.
  unfold emp.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  inversion H.
  inversion H.
  exists.
  unfold boundgh.
  unfold upd.
  unfold emp.
  unfold ghplus.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  symmetry in H.
  inversion H.
  apply bg with ([[gc]]).
  replace (n0 + 0)%nat with n0.
  assumption.
  omega.
  destruct (g x) eqn:gx.
  destruct p0.
  apply bg with x.
  symmetry in H.
  inversion H.
  rewrite H1.
  assumption.
  inversion H.
  exists.
  destruct o.
  apply sn_op.
  apply Permutation_refl.
  apply None_op.
  exists.
  exists n0.
  unfold upd.
  rewrite eqz.
  reflexivity.
  exists.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest))))))))))))))).
  exists p, p', PHPDEF, bp, BP',BPP', o, O'.
  exists c1, c2, ghpdefc1c2, bc1, bc2, bc12.
  exists OPLUS.
  cnj_.
  exists. assumption.
  exists. assumption.
  exists. reflexivity.
  rewrite rest_2_2_2.
  unfold ghplus.
  unfold upd.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e.
  destruct (g' ([[gc]])) eqn:g'gc.
  destruct p0.
  reflexivity.
  rewrite <- rest_2_2_2 in g'gc.
  unfold ghplus in g'gc.
  destruct rest_1 as (n1,c1gc).
  unfold id in *.
  rewrite c1gc in g'gc.
  destruct (c2 ([[gc]])).
  destruct p0.
  inversion g'gc.
  inversion g'gc.
  unfold emp.
  reflexivity.
  rewrite phplus_comm; repeat php_.
  split.
  reflexivity.
  unfold emp.
  unfold ghplus.
  unfold upd.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e.
  rewrite ggc.
  replace (n0 + 0)%nat with n0.
  reflexivity.
  omega.
  destruct (g x).
  destruct p0.
  reflexivity.
  reflexivity.
Qed.

Theorem rule_g_ctrdec invs c n: correct
  (Actr c n ** Atic c) 
  (g_ctrdec c) 
  (fun _ => Actr c (n-1)%nat &* Abool (Nat.ltb 0 n)) invs.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest))))))))))))))).
  destruct rest as (tmp1,(tmp2,tmp3)).
  exists n, p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split.
  tauto.
  split.
  exists (emp knowledge), p2.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, o2.
  exists c2, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  destruct o2.
  apply sn_op.
  apply Permutation_refl.
  apply None_op.
  split.
  assumption.
  split.
  intros.
  split.
  rewrite ghplus_comm.
  rewrite ghplus_emp.
  unfold id in *.
  destruct SAT as (n0,rest).
  exists n0.
  assumption.
  repeat php_.
  destruct tmp1 as (n0,c1c).
  destruct tmp2 as (n1,c2c).
  unfold boundgh in bc12.
  unfold ghplus in bc12.
  specialize bc12 with (x:=([[c]])).
  rewrite c1c in bc12.
  rewrite c2c in bc12.
  apply Nat.ltb_lt.
  apply le_trans with (n0 + S n1)%nat.
  omega.
  apply bc12.
  reflexivity.
  rewrite phplus_comm.
  rewrite phplus_emp.
  rewrite ghplus_emp.
  auto.
  repeat php_.
  auto.
Qed.

Theorem rule_g_newctr invs: correct 
  (Abool true) 
  g_newctr
  (fun _ => EX gc, Actr (Enum gc) 0) invs.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT0 as (n,EQ).
  exists v.
  unfold ghplus.
  unfold ghplusdef in GHPDEF.
  specialize GHPDEF with v.
  rewrite EQ in *.
  destruct (g v) eqn:CV.
  destruct p0.
  destruct o0.
  contradiction.
  exists (plus n0 n).
  unfold lift'.
  reflexivity.
  exists n.
  exists.
Qed.

Theorem rule_NotifyAll invs ev v l wt ot: correct 
  ((Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (Z.eqb ([[ev]]) ([[Aof v]]))) &* 
    Aprop (subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb) = Aemp)) ** Acond v ** Alocked l wt ot)
  (NotifyAll ev)
  (fun _ => Acond v ** Alocked l (upd Z.eq_dec wt ([[Aof v]]) 0%nat) ot) invs.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,(p12,c12)))))))))))))))))).
  exists wt, ot, l, v.
  exists p1,p2,phpdefp1p2,bp1,bp2,bp12,o1,o2,C1,C2,ghpdefC1C2,BC1,BC2,BC1C2,opo1o2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp3,(tmp4,(p34,c34)))))))))))))))))).
  exists p3,p4,phpdefp3p4,bp3,bp4,bp34,O3,O4,C3,C4,BC3,BC4,ghpdefC3C4,bc34,opO3O4.
  split.
  assumption.
  split.
  exists p4, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, O4, C4, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  destruct O4.
  apply sn_op.
  apply Permutation_refl.
  apply None_op.
  split. assumption.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp7,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, None, O'', C5, C6, ghpdefC5C6, BC5, BC6, bc56.
  exists.
  destruct O''.
  apply sn_op.
  apply Permutation_refl.
  apply None_op.
  tauto.
  split; repeat php_.
  split; assumption. 
  split; assumption.
Qed.

Theorem rule_Acquire invs el l (O: list locatione): correct
  (Abool (andb (Z.eqb ([[el]]) ([[Aof l]]))(prcl (evall l) (map evall O))) &* Alock l ** Aobs O)
  (Acquire el) 
  (fun _ => EX wt, (EX ot, (Aobs (l::O) ** Alocked l wt ot ** (subsas (snd (Iof l)) (invs (fst (Iof l)) wt ot))))) invs.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT as (EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,(p12,c12))))))))))))))))))).
  subst.
  unfold id in *.

  assert (o1n: o1 = None).
  {
  inversion tmp2.
  rewrite <- H1 in opo1o2.
  inversion opo1o2.
  reflexivity.
  }
  rewrite o1n in *.

  exists O, l.
  exists p1, p2.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists o2, None, C1, C2.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. apply oplus_comm. assumption.
  exists.
  split. assumption.
  exists p1, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, (Some (map evall O)), C1, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply oplus_comm. assumption.
  split.
  assumption.
  split.
  apply fs_op.
  apply Permutation_refl.
  repeat php_.
  split; reflexivity.
  split.
  intros.
  exists v, v0.
  destruct SAT as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp3,(tmp4,(p34,c34)))))))))))))))))).
  subst.

  assert (phpdefp23p24: phplusdef p2 p3 /\ phplusdef p2 p4). repeat php_.
  assert (ghpdefp23p24: ghplusdef C2 C3 /\ ghplusdef C2 C4). repeat php_.

  assert (o4n: O4 = None).
  {
  inversion tmp3.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  reflexivity.
  }
  rewrite o4n in *.

  exists (phplus p2 p3), p4.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (evall l :: map evall O)), None, (ghplus C2 C3), C4.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  inversion OPLUS.
  rewrite <- H0 in opO3O4.
  inversion opO3O4.
  rewrite <- H in tmp3.
  inversion tmp3.
  rewrite <- H0 in *.
  rewrite <- H1 in *.
  inversion OPLUS.
  inversion tmp3.
  rewrite <- H5 in opO3O4.
  inversion opO3O4.
  apply fs_op.
  apply Permutation_trans with o'1.
  assumption.
  apply Permutation_trans with o0.
  assumption.
  assumption.
  split.
  apply fs_op.
  apply Permutation_refl.
  split.
  assumption.
  split.
  rewrite phplus_assoc; repeat php_.
  repeat php_.
  split; reflexivity.
Qed.

Theorem rule_g_chrg invs ev v l wt ot O: correct
  (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (Z.eqb ([[ev]]) ([[Aof v]]))) &* Acond v ** Aobs O ** Alocked l wt ot) 
  (g_chrg ev)
  (fun _ => Acond v ** Aobs (v::O) ** Alocked l wt (upd Z.eq_dec ot ([[ev]]) (ot ([[ev]]) + 1)%nat)) invs.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT as (EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,(p12,c12))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp2,(tmp4,(p34,c34)))))))))))))))))).
  subst.

  assert (o4n: O4 = None).
  {
  inversion tmp2.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  reflexivity.
  }
  rewrite o4n in *.

  exists O, wt, ot, l, v.
  split.
  assumption.
  exists p1, (phplus p3 p4).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o1, o2, C1, (ghplus C3 C4).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists p3, p4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists O3, None.
  exists C3, C4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists.
  exists p4, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, None.
  exists C4, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  apply None_op.
  split. assumption.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp7,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56.
  split.
  inversion OPLUS.
  rewrite <- H0 in opO5O6.
  inversion opO5O6.
  apply None_op.
  eapply oplus_trans with o0.
  rewrite H0.
  assumption.
  assumption.
  split. assumption.
  split. assumption.
  repeat php_.
  split.
  repeat php_.
  repeat php_.
  split; reflexivity.
  split; reflexivity.
Qed.

Theorem rule_g_chrgu invs ev v l wt ot O:
  correct (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (Z.eqb ([[ev]]) ([[Aof v]]))) &*
    Acond v ** Aobs O ** Aulock l wt ot)
  (g_chrgu ev)
  (fun _ => Acond v ** Aobs (v::O) ** Aulock l wt (upd Z.eq_dec ot ([[ev]]) (ot ([[ev]]) + 1)%nat)) invs.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT as (EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,(p12,c12))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp2,(tmp4,(p34,c34)))))))))))))))))).
  subst.

  assert (o4n: O4 = None).
  {
  inversion tmp2.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  reflexivity.
  }
  rewrite o4n in *.

  exists O, wt, ot, l, v.
  split.
  assumption.
  exists p1, (phplus p3 p4).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o1, o2, C1, (ghplus C3 C4).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists p3, p4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists O3, None.
  exists C3, C4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists.
  exists p4, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, None.
  exists C4, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  apply None_op.
  split. assumption.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp7,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56.
  split.
  inversion OPLUS.
  rewrite <- H0 in opO5O6.
  inversion opO5O6.
  apply None_op.
  eapply oplus_trans with o0.
  rewrite H0.
  assumption.
  assumption.
  split. assumption.
  split. assumption.
  repeat php_.
  split.
  repeat php_.
  repeat php_.
  split; reflexivity.
  split; reflexivity.
Qed.

Theorem rule_g_disch invs ev v l wt ot O: correct
  (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (andb (Z.eqb ([[ev]]) ([[Aof v]]))
    (andb (safe_obs (evall v) (wt ([[ev]])) ((ot ([[ev]]) - 1))) (Nat.ltb 0 (ot ([[ev]])))))) &*
    Acond v ** Aobs (v::O) ** Alocked l wt ot)
  (g_disch ev)
  (fun _ => Acond v ** Aobs O ** Alocked l wt (upd Z.eq_dec ot ([[ev]]) (ot ([[ev]]) - 1)%nat)) invs.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT as (EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,(p12,c12))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp2,(tmp4,(p34,c34)))))))))))))))))).
  subst.

  assert (o4n: O4 = None).
  {
  inversion tmp2.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  reflexivity.
  }
  rewrite o4n in *.

  exists O, wt, ot, l, v.
  split.
  assumption.
  exists p1, (phplus p3 p4).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o1, o2, C1, (ghplus C3 C4).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists p3, p4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists O3, None.
  exists C3, C4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists.
  exists p4, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, None.
  exists C4, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  apply None_op.
  split. assumption.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp7,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56.
  split.
  inversion OPLUS.
  rewrite <- H0 in opO5O6.
  inversion opO5O6.
  apply None_op.
  eapply oplus_trans with o0.
  rewrite H0.
  assumption.
  assumption.
  split. assumption.
  split. assumption.
  repeat php_.
  split.
  repeat php_.
  repeat php_.
  split; reflexivity.
  split; reflexivity.
Qed.

Theorem rule_g_dischu invs ev v l wt ot O: correct
  (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (andb (Z.eqb ([[ev]]) ([[Aof v]]))
    (andb (safe_obs (evall v) (wt ([[ev]])) ((ot ([[ev]]) - 1))) (Nat.ltb 0 (ot ([[ev]])))))) &*
    Acond v ** Aobs (v::O) ** Aulock l wt ot)
  (g_dischu ev)
  (fun _ => Acond v ** Aobs O ** Aulock l wt (upd Z.eq_dec ot ([[ev]]) (ot ([[ev]]) - 1)%nat)) invs.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT as (EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,(p12,c12))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp2,(tmp4,(p34,c34)))))))))))))))))).
  subst.

  assert (o4n: O4 = None).
  {
  inversion tmp2.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  reflexivity.
  }
  rewrite o4n in *.

  exists O, wt, ot, l, v.
  split.
  assumption.
  exists p1, (phplus p3 p4).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o1, o2, C1, (ghplus C3 C4).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists p3, p4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists O3, None.
  exists C3, C4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists.
  exists p4, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, None.
  exists C4, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  apply None_op.
  split. assumption.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp7,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56.
  split.
  inversion OPLUS.
  rewrite <- H0 in opO5O6.
  inversion opO5O6.
  apply None_op.
  eapply oplus_trans with o0.
  rewrite H0.
  assumption.
  assumption.
  split. assumption.
  split. assumption.
  repeat php_.
  split.
  repeat php_.
  repeat php_.
  split; reflexivity.
  split; reflexivity.
Qed.

Theorem rule_Newlock invs r x: correct 
  (Abool (negb (ifb (In_dec Z.eq_dec r x))))
  Newlock 
  (fun l => Aulock (Enum l,r,(0,nil),Enum l,x,(0,nil),false) empb empb) invs.
Proof.
  unfold correct.
  intros.
  simpl.
  intros.
  exists r,x.
  simpl in SAT.
  split.
  assumption.
  intros.
  rewrite phplus_comm.
  unfold phplus.
  rewrite SAT0.
  reflexivity.
  assumption.
Qed.

Theorem rule_Release invs e l O wt ot: correct
   (Abool (Z.eqb ([[e]]) ([[Aof l]])) &* Aobs (l::O) ** Alocked l wt ot ** (subsas (snd (Iof l)) (invs (fst (Iof l)) wt ot)))
   (Release e)
   (fun _ => Aobs O ** Alock l) invs.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT as (EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,tmp3)))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp2,(tmp4,tmp5))))))))))))))))).
  subst.
  assert (tmp: oplus (Some (evall l :: map evall O)) None o /\ O4 = None).
  {
  inversion tmp1.
  rewrite <- H1 in opo1o2.
  inversion opo1o2.
  split.
  apply fs_op.
  apply Permutation_trans with o'; assumption.
  rewrite <- H3 in opO3O4.
  inversion opO3O4.
  reflexivity.
  }
  destruct tmp as (opo,o4n).
  rewrite o4n in *.

  exists O, l, wt, ot.
  exists p2, p1.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. rewrite phplus_comm; repeat php_.
  exists (Some (evall l :: map evall O)), None, C2, C1.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. rewrite ghplus_comm; repeat php_.
  exists opo.
  split.
  split.
  assumption.
  exists (emp knowledge), p2.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (evall l :: map evall O)), None.
  exists (emp (option nat*nat)), C2.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply fs_op. apply Permutation_refl.
  split. apply fs_op. apply Permutation_refl.
  split.
  exists p3, p4.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, None, C3, C4.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply None_op.
  tauto.
  repeat php_. tauto.
  exists.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp7,(tmp6,p5p6))))))))))))))))).
  cnj_.
  subst.
  assert (phpdefp15p16: phplusdef p1 p5 /\ phplusdef p1 p6). repeat php_.
  assert (ghpdefp15p16: ghplusdef C1 C5 /\ ghplusdef C1 C6). repeat php_.
  exists (phplus p1 p5), p6.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (map evall O)), None.
  exists (ghplus C1 C5), C6.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. inversion tmp7.
  rewrite <- H1 in opO5O6.
  inversion opO5O6.
  rewrite <- H4 in OPLUS.
  inversion OPLUS.
  apply fs_op.
  apply Permutation_trans with o'.
  assumption.
  apply Permutation_trans with o'0.
  assumption.
  assumption.
  exists.
  apply fs_op. apply Permutation_refl.
  exists. assumption.
  rewrite phplus_assoc; repeat php_.
  rewrite ghplus_assoc; repeat php_.
  tauto.
  rewrite phplus_comm; repeat php_.
  rewrite ghplus_comm; repeat php_.
Qed.

Theorem rule_Notify invs ev v l O wt ot: correct
  (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (Z.eqb ([[ev]]) ([[Aof v]]))) &* 
    (subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb)) ** Acond v ** Alocked l wt ot ** Aobs (O))
  (Notify ev)
  (fun _ => Acond v ** Alocked l (upd Z.eq_dec wt ([[Aof v]]) (wt ([[Aof v]]) - 1)%nat) ot **
    (subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb) |* Abool (Nat.ltb 0 (wt ([[Aof v]])))) ** Aobs (O)) invs.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT as (EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,tmp3)))))))))))))))))).
  exists O, wt, ot, l, v.
  split.
  tauto.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, o1, o2, C1, C2, ghpdefC1C2, BC1, BC2, BC1C2, opo1o2.
  split.
  tauto.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp2,(tmp4,tmp5))))))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, BC3, BC4, ghpdefC3C4, bc34, opO3O4.
  split.
  tauto.
  split.
  destruct tmp4 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp7,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56, opO5O6.
  split.
  tauto.
  split.
  exists p6, (emp knowledge).
  exists.
  apply phpdef_emp.
  exists bp6, boundph_emp.
  exists.
  rewrite phplus_emp.
  assumption.
  exists O6, None.
  exists C6, (emp (option nat*nat)).
  exists.
  apply ghpdef_emp.
  exists BC6, boundgh_emp.
  exists.
  rewrite ghplus_emp.
  assumption.
  exists.
  destruct O6.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  split.
  assumption.
  split.
  intros.
  destruct SAT as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(tmp9,(tmp8,p7p8))))))))))))))))).
  exists p7, p8, phpdefp7p8, bp7, bp8, bp78, O7, O8, C7, C8, ghpdefC7C8, BC7, BC8, bc78.
  exists.
  inversion OPLUS.
  rewrite <- H0 in opO7O8.
  inversion opO7O8.
  apply None_op.
  apply oplus_trans with o0.
  rewrite H0.
  assumption.
  assumption.
  split.
  assumption.
  split.
  assumption.
  tauto.
  rewrite phplus_emp.
  rewrite ghplus_emp.
  tauto.
  tauto.
  tauto.
  tauto.
Qed.

Theorem rule_Wait invs l v el ev O wt ot: correct
  ((Abool (andb (Z.eqb ([[ev]]) ([[Aof v]]))
    (andb (Z.eqb ([[el]]) ([[Aof l]]))
    (andb (Z.eqb ([[Lof v]]) ([[Aof l]]))
    (andb (safe_obs (evall v) (S (wt ([[Aof v]]))) (ot ([[Aof v]])))
    (andb (prcl (evall v) (map evall O))
    (prcl (evall l) (map evall O))))))) &* 
    ((subsas (snd (Iof l)) (invs (fst (Iof l)) (upd Z.eq_dec wt ([[Aof v]]) (S (wt ([[Aof v]])))) ot)) ** 
    Aobs (l::O) ** Acond v ** Alocked l wt ot)))
  (Wait ev el) 
  (fun _ => EX wt', (EX ot', (Aobs (l::O) ** Alocked l wt' ot' **
    (subsas (snd (Iof l)) (invs (fst (Iof l)) wt' ot')) ** 
    (subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb))))) invs.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT as (EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,tmp3)))))))))))))))))).
  exists O, l, v.
  exists p, (emp knowledge).
  exists.
  apply phpdef_emp.
  exists bp, boundph_emp.
  exists.
  rewrite phplus_emp.
  assumption.
  exists o, None, g, (emp (option nat*nat)).
  exists.
  apply ghpdef_emp.
  exists bg, boundgh_emp.
  exists.
  rewrite ghplus_emp.
  assumption.
  exists.
  destruct o.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  split.
  exists wt, ot.
  split.
  tauto.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, o1, o2, C1, C2, ghpdefC1C2, BC1, BC2, BC1C2, opo1o2.
  split.
  assumption.
  tauto.
  split.
  intros.
  exists v0, v1.
  replace (phplus (emp knowledge) p') with p'.
  replace (ghplus (emp (option nat * nat)) g') with g'.
  destruct SAT as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(ops78,(tmp5,(p78,C78)))))))))))))))))).
  exists p7, p8, phpdefp7p8, bp7, bp8, bp78, O7, O8, C7, C8, ghpdefC7C8, BC7, BC8, bc78.
  exists.
  inversion OPLUS.
  rewrite <- H0 in opO7O8.
  inversion opO7O8.
  apply None_op.
  apply oplus_trans with o0.
  rewrite H0. 
  assumption.
  assumption.
  tauto.
  rewrite ghplus_comm.
  symmetry.
  apply ghplus_emp.
  apply ghpdef_comm.
  apply ghpdef_emp.
  rewrite phplus_comm.
  symmetry.
  apply phplus_emp.
  apply phpdef_comm.
  apply phpdef_emp.
  rewrite phplus_emp.
  rewrite ghplus_emp.
  tauto.
Qed.

Theorem rule_Let a a' a'' c1 c2 x invs:
  forall (C1: correct a c1 a' invs)
         (C2: forall z, correct (a' z) (subs c2 (subse x z)) a'' invs),
    correct a (Let x c1 c2) a'' invs.
Proof.
  unfold correct.
  simpl.
  intros.
  eapply sat_weak_imp.
  assumption.
  assumption.
  apply C1.
  assumption.
  assumption.
  assumption.
  intros.
  unfold id.
  simpl.
  specialize C2 with (z:=z).
  apply C2 in SAT0.
  apply sat_pre_subs3 in SAT0;
  try tauto.
  assumption.
  assumption.
Qed.

Theorem rule_conseq a1 a2 a1' a2' c invs:
  forall (C: correct a1 c a2 invs)
         (IMP1: a1' |= a1)
         (IMP2: forall z, a2 z |= a2' z),
    correct a1' c a2' invs.
Proof.
  unfold correct.
  intros.
  apply sat_weak_imp with a2. 
  assumption.
  assumption.
  apply C.
  assumption.
  assumption.
  apply IMP1.
  assumption.
  assumption.
  assumption.
  intros.
  apply IMP2.
  assumption.
  assumption.
  assumption.
Qed.

Theorem rule_fork c o o' a invs:
  forall (C: correct (Aobs o' ** a) c (fun _ => Aobs nil) invs),
    correct (Aobs (o ++ o') ** a ) (Fork c) (fun _ => Aobs o) invs.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest))))))))))))))).
  destruct rest as (op,(satp2,(p1p2,c1c2))).
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
  exists (Some (map evall o ++ map evall o')), None.
  exists (emp (option nat * nat)), g.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  inversion op.
  rewrite <- H1 in opo1o2.
  inversion opo1o2.
  apply fs_op.
  apply Permutation_trans with o'0.
  rewrite <- map_app.
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
  exists (Some (map evall o ++ map evall o')), None.
  exists (emp (option nat * nat)), (emp (option nat * nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  apply fs_op.
  apply Permutation_refl.
  split.
  apply fs_op.
  rewrite map_app.
  apply Permutation_refl.
  split.
  intros.
  inversion SAT.
  rewrite <- H1 in OPLUS.
  inversion OPLUS.
  apply fs_op.
  apply Permutation_trans with o'0.
  assumption.
  assumption.
  split.
  apply phplus_emp.
  repeat php_.
  assert (o2N: o2 = None).
  {
  inversion op.
  rewrite <- H1 in opo1o2.
  inversion opo1o2.
  reflexivity.
  }
  rewrite o2N in *.
  assert (G: sat p (Some (map evall o')) g (weakest_pre c (fun _ => Aobs nil) id invs)).
  apply C.
  assumption.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp1p2.
  exists (Some (map evall o')), None.
  exists c1, c2, ghpdefc1c2, bc1, bc2, bc12.
  exists.
  apply fs_op.
  apply Permutation_refl.
  split.
  apply fs_op.
  apply Permutation_refl.
  tauto.
  split.
  intros.
  rewrite <- p1p2 in *.
  rewrite <- c1c2 in *.
  assert (phpdefp1p'p2p': phplusdef p1 p' /\ phplusdef p2 p'). repeat php_.
  assert (ghpdefp1p'p2p': ghplusdef c1 g' /\ ghplusdef c2 g'). repeat php_.
  apply C; repeat php_.

  assert (bp1p'p2: boundph (phplus (phplus p1 p') p2)).
  {
  rewrite phplus_comm; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  replace (phplus p2 p1) with (phplus p1 p2); repeat php_.
  }

  assert (bgp1p'p2: boundgh (ghplus (ghplus c1 g') c2)).
  {
  rewrite ghplus_comm; repeat php_.
  rewrite <- ghplus_assoc; repeat php_.
  replace (ghplus c2 c1) with (ghplus c1 c2); repeat php_.
  }

  exists (phplus p1 p'), p2.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists O'', None.
  exists (ghplus c1 g'), c2.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  destruct O''.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  inversion SAT.
  rewrite <- H1 in OPLUS.
  inversion OPLUS.
  exists.
  apply fs_op.
  apply Permutation_trans with o'0.
  assumption.
  assumption.
  split. assumption.
  split; repeat php_.
  split; repeat php_.
Qed.

Theorem rule_g_initl invs e l wt ot O i params:
  correct (Abool (Z.eqb ([[e]]) ([[Aof l]])) &* Aulock l wt ot ** subsas params (invs i wt ot) ** Aobs O)
  (g_initl e) (fun _ => Alock (Aof l, Rof l, (i,params), Lof l, Xof l, Mof l, Pof l) ** Aobs O) invs.
Proof.
  unfold correct.
  intros.
  simpl in *.
  destruct SAT as (EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest)))))))))))))))).
  destruct rest as (tmp1,(tmp2,tmp3)).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp3p4,(o3,(o4,(c3,(c4,(ghpdefc3c4,(bc3,(bc4,(bc34,(opo3o4,rest1))))))))))))))).
  exists l, O, wt, ot, i, params.
  split.
  unfold id.
  tauto.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split.
  tauto.
  split.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp3p4, o3, o4, c3, c4, ghpdefc3c4, bc3, bc4, bc34, opo3o4.
  split.
  tauto.
  split.
  exists p4, (emp knowledge).
  exists.
  apply phpdef_emp.
  exists bp4, boundph_emp.
  exists.
  rewrite phplus_emp.
  tauto.
  exists (Some (map evall O)), None.
  exists c4, (emp (option nat*nat)).
  exists.
  apply ghpdef_emp.
  exists bc4, boundgh_emp.
  exists.
  rewrite ghplus_emp.
  tauto.
  exists.
  tauto.
  split.
  apply fs_op.
  apply Permutation_refl.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp5p6,(o5,(o6,(c5,(c6,(ghpdefc5c6,(bc5,(bc6,(bc56,(opo5o6,rest2))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp5p6, o5, o6, c5, c6.
  exists ghpdefc5c6, bc5, bc6, bc56.
  exists.
  inversion OPLUS.
  rewrite <- H0 in opo5o6.
  tauto.
  rewrite <- H0 in opo5o6.
  inversion opo5o6.
  apply fs_op.
  apply Permutation_trans with o0.
  assumption.
  assumption.
  apply sn_op.
  apply Permutation_trans with o0.
  assumption.
  assumption.
  tauto.
  rewrite phplus_emp.
  rewrite ghplus_emp.
  tauto.
  tauto.
  tauto.
Qed.

Theorem rule_Newcond invs r M P l wt ot:
  correct (Aulock l wt ot) Newcond (fun v => Aulock l wt ot ** Acond (Enum v,r,(0,nil),Aof l,Xof l,M,P)) invs.
Proof.
  unfold correct.
  simpl.
  intros.
  exists r, l, M, P, wt, ot.
  exists p, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o, None, g, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  destruct o.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  exists. assumption.
  split.
  intros.
  destruct SAT0 as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest))))))))))))))).
  exists p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12.
  exists.
  inversion OPLUS.
  rewrite H0.
  assumption.
  rewrite <- H0 in opo1o2.
  apply oplus_trans with o0;
  assumption.
  replace (phplus (emp knowledge) p') with p'; repeat php_.
  rewrite phplus_emp.
  rewrite ghplus_emp.
  auto.
Qed.


Theorem rule_dupl l:
  Alock l |= Alock l ** Alock l.
Proof.
  simpl.
  intros.
  exists p, (upd location_eq_dec (emp knowledge) (evall l) (Some Lock)).
  exists.
  unfold phplusdef.
  intros.
  unfold upd.
  destruct (location_eq_dec x (evall l)).
  rewrite e.
  destruct SAT.
  rewrite H.
  trivial.
  destruct H as (wt,(ot,H)).
  rewrite H.
  trivial.
  unfold emp.
  destruct (p x).
  destruct k;
  trivial.
  trivial.
  exists bp.
  exists.
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  exists.
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1,(v2,(CO,rest))).
  inversion CO.
  unfold phplusdef.
  intros.
  unfold upd.
  destruct (location_eq_dec x (evall l)).
  rewrite e.
  destruct SAT as [S|S].
  rewrite S.
  trivial.
  destruct S as (wt,(ot,S)).
  rewrite S.
  trivial.
  unfold emp.
  destruct (p x).
  destruct k;
  trivial.
  trivial.
  exists o, None.
  exists g, (emp (option nat*nat)).
  exists.
  apply ghpdef_emp.
  exists bg.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  destruct o.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  split.
  assumption.
  split.
  left.
  unfold upd.
  destruct (location_eq_dec (evall l) (evall l)).
  reflexivity.
  contradiction.
  split.
  apply functional_extensionality.
  intros.
  unfold phplus.
  unfold upd.
  destruct (location_eq_dec x (evall l)).
  rewrite e.
  destruct SAT.
  rewrite H.
  reflexivity.
  destruct H as (wt,(ot,pl)).
  rewrite pl.
  reflexivity.
  unfold emp.
  destruct (p x).
  destruct k;
  trivial.
  reflexivity.
  repeat php_.
Qed.
