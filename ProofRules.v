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

(*
Theorem rule_frame a a' c R I L M P X:
  forall f (RULE: correct a c a' R I L M P X),
    correct (a ** f) c (fun z => a' z ** f) R I L M P X.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(C1,(C2,(opO1O2,(sat1,(sat2,(p1p2,C1C2)))))))))))))). 
  assert (sata:=sat1).
  apply RULE in sata.
  rewrite <- p1p2.
  rewrite <- C1C2.
  apply sat_frame with o1 o2.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

Theorem rule_g_initl R I L M P X l wt ot ct O:
  correct (Abool (andb (negb (P ([[l]])))(andb (Z.eqb (L ([[l]])) ([[l]]))
  (negb (ifb (In_dec Z.eq_dec (R ([[l]])) (X (L ([[l]])))))))) &* Aulock ([[l]]) wt ot ct ** (Alasn (I ([[l]]) wt ot ct)) ** Aobs O)
  (g_initl l) (fun _ => Alock ([[l]]) ** Aobs O) R I L M P X.
Proof.
  unfold correct.
  intros.
  simpl in SAT.
  destruct SAT as (bl,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(opo1o2,(tmp1,(tmp2,tmp3)))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(o3,(o4,(C3,(C4,(opo3o4,(tmp4,(tmp5,tmp6))))))))))))).
  exists O, i, wt, ot, ct.
  simpl.
  split.
  assumption.
  exists p1, p2.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists o1, o2.
  exists C1, C2.
  exists.
admit.
  split.
  assumption.
  exists.
  exists p3, p4.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists o3, o4.
  exists C3, C4.
  exists.
admit.
  split.
  assumption.
  exists.
  exists (emp knowledge), p4.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists (Some O), None.
  exists empb, C4.
  exists.
admit.
  exists.
admit.
  exists.
  intros.
  destruct SAT as (il,(p5,(p6,(phpdefp5p6,(bp5,(bp6,(o5,(o6,(C5,(C6,(opo5o6,(tmp7,(tmp8,tmp9))))))))))))).
  split.
  assumption.
  exists (phplus p4 p').
  exists (emp knowledge).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists None, (Some O).
  exists (bagplus C4 C'), empb.
  exists.
admit.
  exists.
admit.
admit.
admit.
admit.
admit.
Admitted.

Theorem rule_Acquire R I L M P X l O:
  correct (Abool (prc ([[l]]) O R L P X) &* Alock ([[l]]) ** Aobs O) (Acquire l) 
  (fun _ => EX wt, (EX ot, (EX ct, (Aobs ([[l]]::O) ** Alocked ([[l]]) wt ot ct ** (Alasn (I ([[l]]) wt ot ct)))))) R I L M P X.
Proof.
  unfold correct.
  intros.
  simpl in SAT.
  simpl.
  destruct SAT as (PRC,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(o1,(o2,(C1,(C2,(opo1o2,(tmp1,(tmp2,tmp3))))))))))))).
  exists O.
  exists p1, (emp knowledge).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists (Some O), None.
  exists C1, empb.
  exists.
admit.
  split.
  split.
  assumption.
  exists p1, (emp knowledge).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists None, (Some O).
  exists C1, empb.
  exists.
admit.
  exists.
  assumption.
admit.
  exists.
  intros.
  exists v, v0, v1.
  destruct SAT as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opo3o4,(tmp4,(tmp5,tmp6)))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(o5,(o6,(C5,(C6,(opo5o6,(tmp7,(tmp8,tmp9)))))))))))).
  exists (emp knowledge), p'.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists (Some (([[l]]) :: O)), None.
  exists empb, C'.
  exists.
admit.
  exists.
admit.
  exists.
  exists p5, p6.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists None, None.
  exists C5, C6.
  exists.
admit.
admit.
Admitted.

Theorem rule_Release R I L M P X l O wt ot ct:
  correct ((Alocked ([[l]]) wt ot ct) ** (Alasn (I ([[l]]) wt ot ct)) ** Aobs (([[l]])::O)) (Release l) 
  (fun _ => (Alock ([[l]])) ** Aobs O) R I L M P X.
Proof.
  unfold correct.
  intros.
  simpl in SAT.
  simpl.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(o1,(o2,(C1,(C2,(opo1o2,(tmp1,(tmp2,tmp3)))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opo3o4,(tmp4,(tmp5,tmp6)))))))))))).

  exists O, wt, ot, ct, (phplus p1 p3), (emp knowledge).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists (Some (([[l]])::O)), None.
  exists (bagplus C1 C3), empb.
  exists.
admit.
  exists.
  exists (emp knowledge), (phplus p1 p3).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists (Some (([[l]])::O)), None.
  exists empb, (bagplus C1 C3).
  exists.
admit.
  exists.
admit.
  exists.
  exists p1, p3.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists None, None.
  exists C1, C3.
  exists.
admit.
admit.
admit.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(o5,(o6,(C5,(C6,(opo5o6,(tmp7,(tmp8,tmp9)))))))))))).
  exists p', (emp knowledge).
  exists.
admit.
  exists.
admit.
  exists.
admit.

  exists None, (Some O).
  exists C', empb.
  exists.
admit.
  split.
admit.
admit.
admit.
Admitted.

Theorem rule_Newcond R I L M P X r l m b:
  correct (Abool true) Newcond (fun v => Abool (andb (Z.eqb (R l) r)(andb (Z.eqb (L (v)) l)
  (andb (Coq.Bool.Bool.eqb (M (v)) m) (Coq.Bool.Bool.eqb (P (v)) b)))) &* Acond v) R I L M P X.
Proof.
  unfold correct.
  simpl.
  intros.
  exists r, l, m, b.
  intros.
  destruct SAT0 as (bl,p'v).
  split.
  assumption.
  rewrite phplus_comm.
  apply phplus_Cond.
  apply phpdef_comm.
  assumption.
  assumption.
  assumption.
Qed.

Theorem rule_Wait R I L M P X l v O wt ot ct:
  correct (Abool (andb (Z.eqb (L ([[v]])) ([[l]]))
                    (andb (safe_obs ([[v]]) (S (wt ([[v]]))) (ot ([[v]])) R L P X)
                    (andb (prc ([[v]]) O R L P X)
                          (prc ([[l]]) O R L P X)))) &*
             (Aobs (([[l]])::O) ** Acond ([[v]]) ** Alocked ([[l]]) wt ot ct ** (Alasn (I ([[l]]) (incb wt ([[v]])) ot ct)))) (Wait v l)
             (fun _ => EX wt', (EX ot', (EX ct' ,(Aobs (([[l]])::O) ** Alocked ([[l]]) wt' ot' ct' ** 
                       (Alasn (I ([[l]]) wt' ot' ct')) ** (Alasn (M_to_crd (M ([[v]])) ([[v]]))))))) R I L M P X.
Proof.
  unfold correct.
  intros.
  simpl in SAT.
  destruct SAT as (bl,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(o1,(o2,(C1,(C2,(opo1o2,(tmp1,(tmp2,tmp3))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opo3o4,(tmp4,(tmp5,tmp6)))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(o5,(o6,(C5,(C6,(opo5o6,(tmp7,(tmp8,tmp9)))))))))))).
  simpl.
  intros.
  exists O.
  exists p2, (emp knowledge).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists (Some (([[l]])::O)), None.
  exists C2, empb.
  exists.
admit.
  exists.
  exists wt, ot, ct.
  split.
  assumption.
  exists (emp knowledge), p2.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists (Some (([[l]])::O)), None.
  exists empb, C2.
  exists.
admit.
  exists.
admit.
  exists.
  exists p3, (phplus p5 p6).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists None, None.
  exists C3, (bagplus C5 C6).
  exists.
admit.
  exists.
  assumption.
  exists.
  exists p5, p6.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists None, None.
  exists C5, C6.
  exists.
admit.
  auto.
admit.
admit.
  split.
  intros.
  exists v0, v1, v2.
  destruct SAT as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(o7,(o8,(C7,(C8,(opo7o8,(tmp10,(tmp11,tmp12)))))))))))).
  destruct tmp11 as (p9,(p0,(phpdefp9p0,(bp9,(bp0,(o9,(o0,(C9,(C0,(opo9o0,(tmp13,(tmp14,tmp15)))))))))))).
  destruct tmp14 as (p91,(p01,(phpdefp91p01,(bp91,(bp01,(o91,(o01,(C91,(C01,(opo9o01,(tmp16,(tmp17,tmp18)))))))))))).
  exists p7, p8, phpdefp7p8, bp7, bp8, o7, o8, C7, C8.
  exists.
admit.
  split.
  assumption.
  exists.
  exists p9, p0.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists (Some (([[l]])::O)), None.
  exists C9, C0.
  exists.
admit.
  exists.
admit.
  exists.
  exists p91, p01.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists None, None.
  exists C91,C01.
  exists.
admit.
  split.
  assumption.
  exists.
  assumption.
  assumption.
  assumption.
  assumption.
admit.
Admitted.


Theorem rule_Notify R I L M P X v wt ot ct:
  correct (Acond ([[v]]) ** Alocked (L ([[v]])) wt ot ct ** (Alasn (M_to_crd (M ([[v]])) ([[v]])))) (Notify v)
             (fun _ => Alocked (L ([[v]])) (decb wt ([[v]])) ot ct ** 
                     ((Alasn (M_to_crd (M ([[v]])) ([[v]]))) |* Abool (Nat.ltb 0 (wt ([[v]]))))) R I L M P X.
Proof.
  unfold correct.
  intros.
  simpl in SAT.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(o1,(o2,(C1,(C2,(opo1o2,(tmp1,(tmp2,tmp3)))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opo3o4,(tmp4,(tmp5,tmp6)))))))))))).
  simpl.
  exists wt, ot, ct.
  exists p1, p2.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists o, None.
  exists empb, C.
  exists.
admit.
  split.
  assumption.
  exists.
  exists p3, p4.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists None, None.
  exists empb, C.
  exists.
admit.
  split.
  assumption.
  exists.
  exists p4, (emp knowledge).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists None, None.
  exists C4, (bagplus C1 C3).
  exists.
admit.
  split.
  assumption.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(o5,(o6,(C5,(C6,(opo5o6,(tmp7,(tmp8,tmp9)))))))))))).
  exists p5, p6.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists o5, o6.
  exists (bagplus (bagplus C1 C3) C5), C6.
  exists.
admit.
  split.
  assumption.
  exists.
  assumption.
admit.
admit.
admit.
admit.
Admitted.

Theorem rule_NotifyAll R I L M P X v wt ot ct:
  correct (Abool (negb (M ([[v]]))) &* Acond ([[v]]) ** Alocked (L ([[v]])) wt ot ct) (NotifyAll v)
             (fun _ => Alocked (L ([[v]])) (rstb wt ([[v]])) ot ct) R I L M P X.
Proof.
  unfold correct.
  intros.
  simpl in SAT.
  destruct SAT as (bl,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(o1,(o2,(C1,(C2,(opo1o2,(tmp1,(tmp2,tmp3))))))))))))).
  simpl.
  exists wt, ot, ct.
  split.
  assumption.
  exists p1, p2.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists o, None.
  exists empb, C.
  exists.
admit.
  split.
  assumption.
  exists.
  exists p2, (emp knowledge).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists None, None.
  exists empb, C.
  exists.
admit.
  split.
  assumption.
  exists.
  intros.
  destruct SAT as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opo3o4,(tmp4,(tmp5,tmp6)))))))))))).
admit.
admit.
admit.
Admitted.



Theorem rule_g_dupl R I L M P X l:
  correct (Alock ([[l]])) (g_dupl l) (fun _ => Alock ([[l]]) ** Alock ([[l]])) R I L M P X.
Proof.
  unfold correct.
  intros.
  simpl in SAT.
  simpl.
  exists p, (emp knowledge).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists o, None.
  exists C, empb.
  exists.
admit.
  exists.
  assumption.
  exists.
  intros.
  destruct SAT0 as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(o1,(o2,(C1,(C2,(opo1o2,(tmp1,(tmp2,tmp3)))))))))))).
  exists p1, p2.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists o1, o2.
  exists C1, C2.
  exists.
admit.
  auto.
admit.
Admitted.

Theorem rule_g_chrg R I L M P X v wt ot ct O:
  correct (Acond ([[v]]) ** Aobs O ** Alocked (L ([[v]])) wt ot ct) (g_chrg v) (fun _ => Aobs (([[v]])::O) ** Alocked (L ([[v]])) wt (incb ot ([[v]])) ct) R I L M P X.
Proof.
  unfold correct.
  intros.
  simpl in SAT.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(o1,(o2,(C1,(C2,(opo1o2,(tmp1,(tmp2,tmp3)))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opo3o4,(tmp4,(tmp5,tmp6)))))))))))).
  simpl.
  exists O, wt, ot, ct.
  exists p1, p2.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists o1, o2.
  exists C1, C2.
  exists.
admit.
  split.
  assumption.
  exists.
  exists p3, p4.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists o3, o4.
  exists C3, C4.
  exists.
admit.
  exists.
  assumption.
  exists.
  exists p4, (emp knowledge).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists o4, None.
  exists C4, empb.
  exists.
admit.
  split.
  assumption.
  exists.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(o5,(o6,(C5,(C6,(opo5o6,(tmp7,(tmp8,tmp9)))))))))))).
  exists p5, p6.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists o5, o6.
  exists C5, C6.
  exists.
admit.
  exists.
  assumption.
  exists.
  assumption.
admit.
admit.
admit.
admit.
Admitted.


Theorem rule_g_chrgu R I L M P X v wt ot ct O:
  correct (Acond ([[v]]) ** Aobs O ** Aulock (L ([[v]])) wt ot ct) (g_chrgu v) (fun _ => Acond ([[v]]) ** Aobs (([[v]])::O) ** Aulock (L ([[v]])) wt (incb ot ([[v]])) ct) R I L M P X.
Proof.
Admitted.

Theorem rule_g_disch R I L M P X v wt ot ct O:
  correct (Abool (andb (safe_obs ([[v]]) (wt ([[v]])) ((ot ([[v]]) - 1)) R L P X) (Nat.ltb 0 (ot ([[v]]))))
  &* Acond ([[v]]) ** Aobs (([[v]])::O) ** Alocked (L ([[v]])) wt ot ct) (g_dischu v)
  (fun _ => Aobs O ** Alocked (L ([[v]])) wt (decb ot ([[v]])) ct) R I L M P X.
Proof.
Admitted.

Theorem rule_g_dischu R I L M P X v wt ot ct O:
  correct (Abool (andb (safe_obs ([[v]]) (wt ([[v]])) ((ot ([[v]]) - 1)) R L P X) (Nat.ltb 0 (ot ([[v]]))))
  &* Acond ([[v]]) ** Aobs (([[v]])::O) ** Aulock (L ([[v]])) wt ot ct) (g_dischu v)
  (fun _ => Aobs O ** Aulock (L ([[v]])) wt (decb ot ([[v]])) ct) R I L M P X.
Proof.
Admitted.

Theorem rule_g_gain R I L M P X v wt ot ct:
  correct (Acond ([[v]]) ** Alocked (L ([[v]])) wt ot ct) (g_gain v) (fun _ => Alocked (L ([[v]])) wt ot (incb ct ([[v]])) ** Acredit ([[v]])) R I L M P X.
Proof.
Admitted.

Theorem rule_g_gainu R I L M P X v wt ot ct:
  correct (Acond ([[v]]) ** Aulock (L ([[v]])) wt ot ct) (g_gain v) (fun _ => Aulock (L ([[v]])) wt ot (incb ct ([[v]])) ** Acredit ([[v]])) R I L M P X.
Proof.
Admitted.

Theorem rule_g_lose R I L M P X v wt ot ct:
  correct (Abool (Nat.ltb 0 (ct ([[v]]))) &* Acond ([[v]]) ** Alocked (L ([[v]])) wt ot ct ** Acredit ([[v]])) (g_lose v) 
  (fun _ => Alocked (L ([[v]])) wt ot (decb ct ([[v]]))) R I L M P X.
Proof.
Admitted.

Theorem rule_g_loseu R I L M P X v wt ot ct:
  correct (Abool (Nat.ltb 0 (ct ([[v]]))) &* Acond ([[v]]) ** Aulock (L ([[v]])) wt ot ct ** Acredit ([[v]])) (g_loseu v) 
  (fun _ => Aulock (L ([[v]])) wt ot (decb ct ([[v]]))) R I L M P X.
Proof.
Admitted.

Theorem rule_g_info R I L M P X v wt ot ct:
  correct (Acond ([[v]]) ** Alocked (L ([[v]])) wt ot ct ** Acredit ([[v]])) (g_info v) 
  (fun _ => Abool (Nat.ltb O (ct ([[v]]))) &* Alocked (L ([[v]])) wt ot ct) R I L M P X.
Proof.
Admitted.

Theorem rule_g_infou R I L M P X v wt ot ct:
  correct (Acond ([[v]]) ** Aulock (L ([[v]])) wt ot ct ** Acredit ([[v]])) (g_info v) 
  (fun _ => Abool (Nat.ltb O (ct ([[v]]))) &* Aulock (L ([[v]])) wt ot ct) R I L M P X.
Proof.
Admitted.

Theorem rule_Lookup R I L M P X f e z:
  correct (Apointsto f ([[e]]) z) (Lookup e) (fun r => Apointsto f ([[e]]) z &* Abool (Z.eqb r z)) R I L M P X.
Proof.
Admitted.

Theorem rule_Mutate R I L M P X e1 e2 z:
  correct (Apointsto 1 ([[e1]]) z) (Mutate e1 e2) (fun _ => Apointsto 1 ([[e1]]) ([[e2]])) R I L M P X.
Proof.
Admitted.*)

