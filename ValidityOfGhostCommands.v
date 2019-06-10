Add LoadPath "proofs".

Require Import Coq.Bool.Bool.
Require Import Qcanon.
Require Import ZArith.
Require Import Coq.Init.Nat.
Require Import List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sorting.Permutation.
Require Import Util_Z.
Require Import Util_list.
Require Import Programs.
Require Import Assertions.
Require Import WeakestPrecondition.
Require Import RelaxedPrecedenceRelation.
Require Import ValidityOfConfigurations.

Set Implicit Arguments.

Local Open Scope nat.

Definition validk0 (n: nat) (sp: bool) (T: list (cmd * context * pheap * list (olocation Z) * gheap * Z)) (Ginv Gleak: gheap) (h:heap) (invs: Z -> inv) :=
  exists (locs: list (location Z))
         (Pinv: pheap) (Pleak: pheap) (Ainv: list (assn * (location Z)))  
         (INF: inf_capacity (fold_left ghplus (map gof T) (ghplus Ginv Gleak)) /\ inf_capacity h)
         (SPUR: spur_ok (fold_left phplus (map pof T) (phplus Pinv Pleak)) sp invs (map cmdof T))
         (PHsOK: pheaps_heap (map (fun x => (pof x, snd x)) T) Pinv Pleak h)
         (GHsOK: gheaps_ok (map (fun x => (gof x, snd x)) T) Ginv Gleak)
         (NDPT: NoDup (map snd T))
         (INVsOK: invs_ok Ainv Pinv Ginv (fold_left phplus (map pof T) (phplus Pinv Pleak)) h (map cmdof T) (concat (map Aoof T)) locs invs)
         (LOCsOK: locations_ok locs (fold_left phplus (map pof T) (phplus Pinv Pleak)) (concat (map oof T)))
         (LOCKsOK: locks_ok (fold_left phplus (map pof T) (phplus Pinv Pleak)) (concat (map oof T)) h)
         (WTsOTsOK: forall l wt ot 
           (ULOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) l = Some (Locked wt ot) \/ 
                     fold_left phplus (map pof T) (phplus Pinv Pleak) l = Some (Ulock wt ot)),
                     wt = WTs l (map cmdof T) locs /\ ot = OBs l (concat (map Aoof T)) locs),
    forall id c tx p O C (ING: In (c,tx,p,O,C,id) T),
      wellformed (c,tx) /\ sat p (Some O) C (weakest_pre_ct n sp (c,tx) invs) /\
      forall ev el (W4COND: c = Waiting4cond ev el),
        exists v l (IN: In v locs) (INl: In l locs) (EQv: (Aof v) = ([[ev]])) (EQl: (Aof l) = ([[el]])),
          safe_obs v (WTs l (map cmdof T) locs([[ev]])) (OBs l (concat (map Aoof T)) locs ([[ev]])) = true.


Lemma g_ctrinc_preserves_validity0:
  forall m sp h T id tx p O C (Cinv Cleak: gheap) t1 m1 gc invs
         (CMD: In (nop, tx, p, O, C, id) T)
         (Cgc: C ([[gc]]) = Some (Some t1, m1))
         (SAT: sat p (Some O) (upd Z.eq_dec C ([[gc]]) (Some (Some (S t1), S m1))) (weakest_pre_ct (S m) sp (tt, tx) invs))
         (VALID: validk0 (S m) sp T Cinv Cleak h invs),
    validk0 m sp (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some (S t1), S m1)), id)) Cinv Cleak h invs.
Proof.
  intros.
  unfold validk0 in VALID.
  destruct VALID as (locs,(Pinv,(Pleak,(Ainv,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS))))))))))))).
  unfold validk0.
  unfold pheaps_heap in *.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  unfold locations_ok in *.
  destruct LOCsOK as (INJ,(LCOM,(LOCs,OBsOK))).
  unfold invs_ok in *.
  destruct INVsOK as (NDPA,(AinvOK,(INAOK,SATAOK))).
  unfold locks_ok.
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.

  unfold validk0.

  assert (inc: In C (map gof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (incid: In (C, id) (map (fun x => (gof x, snd x)) T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (inp: In p (map pof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (bp: boundph p).
  {
  apply BPE.
  assumption.
  }

  assert (bc: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  left.
  assumption.
  }

  assert (tmp:=CMD).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  exists locs, Pinv, Pleak, Ainv.

  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (p0gc: forall id' C' o n (NEQ: id' <> id) 
    (IN: In (C',id') (map (fun x => (gof x, snd x)) T))
    (C'gc: C' ([[gc]]) = Some (o,n)), o = None).
  {
  intros.
  assert (ghpdefcc': ghplusdef C C').
  {
  apply DEFLg with id id'.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  assumption.
  }
  unfold ghplusdef in ghpdefcc'.
  specialize ghpdefcc' with ([[gc]]).
  rewrite Cgc in ghpdefcc'.
  rewrite C'gc in ghpdefcc'.
  destruct o.
  contradiction.
  reflexivity.
  }

  assert (Cinvgc: forall o n (C'gc: Cinv ([[gc]]) = Some (o,n)), o = None).
  {
  intros.
  assert (ghpdefcci: ghplusdef C Cinv).
  {
  apply GHPD.
  assumption.
  }
  unfold ghplusdef in ghpdefcci.
  specialize ghpdefcci with ([[gc]]).
  rewrite Cgc in ghpdefcci.
  rewrite C'gc in ghpdefcci.
  destruct o.
  contradiction.
  reflexivity.
  }

  assert (Cleakgc: forall o n (C'gc: Cleak ([[gc]]) = Some (o,n)), o = None).
  {
  intros.
  assert (ghpdefcci: ghplusdef C Cleak).
  {
  apply GHPD.
  assumption.
  }
  unfold ghplusdef in ghpdefcci.
  specialize ghpdefcci with ([[gc]]).
  rewrite Cgc in ghpdefcci.
  rewrite C'gc in ghpdefcci.
  destruct o.
  contradiction.
  reflexivity.
  }

  assert (ghpdefcup': forall p' id' (NEQ: id <> id')
    (IN: In (p',id') (map (fun x => (gof x, snd x)) T)),
    ghplusdef p' (upd Z.eq_dec C ([[gc]]) (Some (Some (S t1), S m1)))).
  {
  unfold ghplusdef.
  unfold upd.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e.
  destruct (p' ([[gc]])) eqn:p2gc.
  destruct p0.
  apply p0gc with (id':=id') in p2gc.
  rewrite p2gc.
  trivial.
  omega.
  assumption.
  trivial.
  assert (ghpdefcp2: ghplusdef C p').
  {
  apply DEFLg with id id'.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  assumption.
  }
  apply ghpdef_comm in ghpdefcp2.
  apply ghpdefcp2.
  }

  assert (ghpdefcui: ghplusdef (upd Z.eq_dec C ([[gc]]) (Some (Some (S t1), S m1))) Cinv).
  {
  unfold ghplusdef.
  unfold upd.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e.
  destruct (Cinv ([[gc]])) eqn:p2gc.
  destruct p0.
  rewrite Cinvgc with o n.
  trivial.
  reflexivity.
  trivial.
  apply GHPD.
  assumption.
  }

  assert (ghpdefcul: ghplusdef (upd Z.eq_dec C ([[gc]]) (Some (Some (S t1), S m1))) Cleak).
  {
  unfold ghplusdef.
  unfold upd.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e.
  destruct (Cleak ([[gc]])) eqn:p2gc.
  destruct p0.
  rewrite Cleakgc with o n.
  trivial.
  reflexivity.
  trivial.
  apply GHPD.
  assumption.
  }

  assert (EQHI: map (fun x => (pof x, snd x)) (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some (S t1), S m1)), id)) =
    map (fun x => (pof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQH: map pof (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some (S t1), S m1)), id)) =
    map pof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (ghpdefp0il: forall p0 : gheap, In p0 (map gof T) -> ghplusdef p0 (ghplus Cinv Cleak)).
  {
  intros.
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  }

  assert (fold1gc: exists t2 m2, fold_left ghplus (map gof T) (ghplus Cinv Cleak) ([[gc]]) = Some (Some t2, m2)).
  {
  eapply fold_ctr_some' with (x:=(nop, tx, p, O, C, id)); repeat php_.
  apply gofs.
  exists t1, m1.
  assumption.
  }
  destruct fold1gc as (t2,(m2,fold1gc)).

  assert (fold2gc: fold_left ghplus (map gof (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some (S t1), S m1)), id)))
    (ghplus Cinv Cleak) ([[gc]]) = (Some (Some (S t2), S m2))).
  {
  apply fold_ctr_inc with (C:=C) (t1:=t1) (m1:=m1); repeat php_.
  apply gofs.
  auto.
  }

  assert (EQG: forall gc' (NEQ: gc' <> ([[gc]])),
    fold_left ghplus  (map gof (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some (S t1), S m1)), id))) (ghplus Cinv Cleak) gc' =
    fold_left ghplus  (map gof T) (ghplus Cinv Cleak) gc').
  {
  intros.
  apply eqg_heap with (z:=([[gc]])) (p:=C) (v:=Some (Some (S t1), S m1)); repeat php_.
  apply gofs.
  omega.
  }

  assert (EQC: forall v, filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some (S t1), S m1)), id))) = filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)).
  {
  intros.
  symmetry.
  apply filter_updl_eq.
  repeat dstr_.
  unfold elem.
  intros.
  apply filter_In in IN.
  destruct IN as (INx',EQx').
  apply Z.eqb_eq in EQx'.
  destruct x' as (((((c1,tx1),p1),O1),C1),id1).
  assert (EQA: ((((c1,tx1),p1),O1),C1) = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- EQx'.
  assumption.

  }
  rewrite EQA.
  unfold cmdof.
  simpl.
  destruct ((opZ_eq_dec None (Some v))).
  inversion e.
  reflexivity.
  }

  assert (EQWT: forall l, filterb (xOf (fun x => Lof x) locs) (Aof l)
    (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some (S t1), S m1)), id))))) =
    filterb (xOf (fun x => Lof x) locs) (Aof l)
    (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof T)))).
  {
  intros.
  unfold filterb.
  apply functional_extensionality.
  intros.
  rewrite EQC.
  reflexivity.
  }

  assert (EQAO: map Aoof (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some (S t1), S m1)), id)) =
    map Aoof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; repeat php_.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQO: map oof (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some (S t1), S m1)), id)) =
    map oof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; repeat php_.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  rewrite EQHI.
  rewrite EQH.
  rewrite EQAO.
  rewrite EQO.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  unfold inf_capacity in *.
  destruct INF1 as (x,INF1).
  exists x.
  intros.
  apply INF1 in LE.
  destruct (Z.eq_dec y ([[gc]])).
  rewrite e in LE.
  rewrite fold1gc in LE.
  inversion LE.
  rewrite EQG.
  assumption.
  assumption.
  assumption.
  }

  exists.
  {
  split.
  {
  intros.
  eapply SPUR1 with (c:=c).
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  destruct (Z.eq_dec (snd y) id).
  unfold cmdof in EQy.
  rewrite <- EQy in WASW.
  inversion WASW.
  apply in_map_iff.
  exists y.
  auto.
  apply WASW.
  }
  assumption.
  }

  exists. tauto.
  exists.
  {
  split.
  {
  unfold updl.
  rewrite map_map.
  unfold defl.
  intros.
  apply in_map_iff in IN1.
  destruct IN1 as ((x1,id'),(EQx1,INx1)).
  simpl in *.
  destruct (Z.eq_dec id' id).
  unfold gof in EQx1.
  simpl in EQx1.
  inversion EQx1.
  apply in_map_iff in IN2.
  destruct IN2 as ((x2,id2'),(EQx2,INx2)).
  simpl in *.
  destruct (Z.eq_dec id2' id).
  unfold gof in EQx2.
  simpl in EQx2.
  inversion EQx2.
  omega.
  {
  apply ghpdef_comm.
  apply ghpdefcup' with id2'.
  omega.
  apply in_map_iff.
  exists (x2, id2').
  inversion EQx2.
  rewrite <- H3.
  auto.
  }
  apply in_map_iff in IN2.
  destruct IN2 as ((x2,id2'),(EQx2,INx2)).
  simpl in *.
  destruct (Z.eq_dec id2' id).
  unfold gof in EQx2.
  simpl in EQx2.
  inversion EQx2.
  apply ghpdefcup' with id'.
  omega.
  apply in_map_iff.
  exists (x1, id').
  inversion EQx1.
  rewrite <- H3.
  auto.
  apply DEFLg with id1 id2.
  assumption.
  apply in_map_iff.
  exists (x1, id').
  auto.
  apply in_map_iff.
  exists (x2, id2').
  auto.
  }
  exists.
  {
  unfold updl.
  rewrite map_map.
  intros.
  apply in_map_iff in IN.
  destruct IN as ((x,id2'),(EQx,INx)).
  simpl in *.
  destruct (Z.eq_dec id2' id).
  unfold gof in EQx.
  simpl in EQx.
  rewrite <- EQx.
  split. assumption.
  assumption.
  apply GHPD.
  rewrite <- EQx.
  apply in_map.
  assumption.
  }
  split. assumption.
  unfold boundgh.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e in H.
  rewrite fold2gc in H.
  inversion H.
  unfold boundgh in BGT.
  apply BGT in fold1gc.
  omega.
  rewrite EQG in H.
  apply BGT in H.
  assumption.
  assumption.
  }
  exists.
  {
  apply NoDup_updl.
  assumption.
  }
  exists.
  {
  split. assumption.
  split. assumption.
  split.
  intros.
  rewrite EQWT.
  apply INAOK; assumption. assumption.
  }
  exists. tauto.
  exists. tauto.
  exists. intros. rewrite EQWT. apply WTsOTsOK; assumption.
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as ((x,id2'),(EQx,INx)).
  simpl in *.
  destruct (Z.eq_dec id2' id).
  {
  symmetry in EQx.
  inversion EQx.
  split. unfold wellformed. simpl. tauto.
  split.
  assert (bg: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  left.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id) .
  split. reflexivity. assumption.
  }

  assert (bgupd: boundgh (upd Z.eq_dec C ([[gc]]) (Some (Some (S t1), S m1)))).
  {
  apply boundgh_upd; repeat php_.
  intros.
  inversion H.
  unfold boundgh in bg.
  apply bg in Cgc.
  omega.
  }
  eapply sat_weak_imp1; try assumption.
  apply SAT.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  }
  destruct x as ((((c1,tx1),p1),O1),C1).
  symmetry in EQx.
  inversion EQx.
  assert (tmp:=INx).
  apply SOBS in tmp.
  destruct tmp as (WF1,(SAT1,SOBS1)).
  split. assumption.
  split.

  assert (bp0: boundph p1).
  {
  apply BPE.
  apply in_map_iff.
  exists (c1, tx1, p1, O1, C1, id2').
  split. reflexivity. assumption.
  }

  assert (bg0: boundgh C1).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  left.
  apply in_map_iff.
  exists (c1, tx1, p1, O1, C1, id2').
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  apply SAT1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  apply SOBS1 in W4COND.
  destruct W4COND as (v,(l,(inv,(eqv,(eql,sobs1))))).
  exists v, l, inv, eqv, eql.
  rewrite EQWT.
  assumption.
Qed.


Lemma g_initl_preserves_validity0:
  forall m sp h T id tx p O C Cinv Cleak invs (ll: location Z) p1 p2 wt ot C1 C2 i e'
         (INT: In (nop, tx, p, O, C, id) T)           
         (GHPDc1c2: ghplusdef C1 C2)
         (EQl: Aof ll = ([[e']]))
         (BP1: boundph p1)
         (BP2: boundph p2)
         (phpdp1p2: phplusdef p1 p2)
         (p1p2: p = phplus p1 p2)
         (C1C2: C = ghplus C1 C2) 
         (P1l: p1 ll = Some (Ulock wt ot))
         (p2inv: sat p2 None C2 (subsas (snd i) (invs (fst i) wt ot)))
         (SAT: sat (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p1 ll None)
           (Oof ll, i, Mof ll, M'of ll) (Some Lock)) (Some O) C1 (weakest_pre_ct (S m) sp (tt, tx) invs))
         (VALID: validk0 (S m) sp T Cinv Cleak h invs),
    validk0 m sp (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p1 ll None)
      (Oof ll, i, Mof ll, M'of ll) (Some Lock), O, C1, id)) (ghplus Cinv C2) Cleak h invs.
Proof.
  intros.
  unfold validk0 in VALID.
  destruct VALID as (locs,(Pinv,(Pleak,(Ainv,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS))))))))))))).
  unfold validk0.
  unfold pheaps_heap in *.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  unfold locations_ok in *.
  destruct LOCsOK as (INJ,(LCOM,(LOCs,OBsOK))).
  unfold invs_ok in *.
  destruct INVsOK as (NDPA,(AinvOK,(INAOK,SATAOK))).
  unfold locks_ok.
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.
  unfold validk0.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  rewrite p1p2 in *.
  rewrite C1C2 in *.
  assert (INpT: In (phplus p1 p2) (map pof T)).
  {
  apply in_map_iff.
  exists (nop, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  }
  assert (phpdefp1Pinv: phplusdef p1 Pinv).
  {
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply PHPD.
  assumption.
  apply phpdef_comm.
  assumption.
  }
  assert (phpdefp2Pinv: phplusdef p2 Pinv).
  {
  apply phpdef_assoc_mon with p1.
  assumption.
  apply PHPD.
  assumption.
  }
  assert (LOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Ulock wt ot)).
  {
  apply fold_ulock.
  apply pofs.
  assumption.
  assumption.
  intros.
  apply PHPD in IN.
  apply phpdef_pair;
  tauto.
  right.
  exists (phplus p1 p2), INpT.
  apply phplus_ulock.
  assumption.
  assumption.
  }

  assert (NONE1: (Oof ll, i, Mof ll, M'of ll) <> ll -> 
    fold_left phplus (map pof T) (phplus Pinv Pleak) (Oof ll, i, Mof ll, M'of ll) = None).
  {
  intros.
  destruct (fold_left phplus (map pof T) (phplus Pinv Pleak) (Oof ll, i, Mof ll, M'of ll)) eqn:fl1.
  assert (CO: (Oof ll, i, Mof ll, M'of ll) = ll).
  {
  apply INJ.
  rewrite fl1.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  reflexivity.
  }
  contradiction.
  reflexivity.
  }

  assert (phpdefppipl: In (phplus p1 p2) (map pof T)).
  {
  apply in_map_iff.
  exists (nop, tx, phplus p1 p2, O, ghplus C1 C2, id).
  tauto.
  }

  apply PHPD in phpdefppipl.

  assert (phpdefp1pip2pi: phplusdef p1 Pinv /\ phplusdef p2 Pinv).
  {
  apply phpdef_dist.
  tauto.
  tauto.
  }

  assert (phpdefp1plp2pl: phplusdef p1 Pleak /\ phplusdef p2 Pleak).
  {
  apply phpdef_dist.
  tauto.
  tauto.
  }

  assert (EQh: phplus (phplus Pinv p2) Pleak = phplus (phplus Pinv Pleak) p2).
  {
  rewrite phplus_comm;
  try tauto.
  rewrite <- phplus_assoc;
  try tauto.
  replace (phplus Pleak Pinv) with (phplus Pinv Pleak);
  try tauto.
  apply phplus_comm;
  try tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_pair';
  try tauto.
  apply phpdef_comm.
  tauto.
  }

  assert (LOCK: ((Oof ll, i, Mof ll, M'of ll) <> ll -> 
    fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p1 ll None) (Oof ll, i, Mof ll, M'of ll) (Some Lock), O, C1, id)))
    (phplus (phplus Pinv p2) Pleak) ll = None) /\
    fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p1 ll None) (Oof ll, i, Mof ll, M'of ll) (Some Lock), O, C1, id)))
    (phplus (phplus Pinv p2) Pleak) (Oof ll, i, Mof ll, M'of ll) = Some Lock).
  {
  rewrite EQh.
  apply lock_initl with p1; repeat php_.
  apply pofs.
  intros.
  apply PHPD in IN.
  apply phpdef_pair;
  tauto.
  apply in_map_iff.
  exists (nop, tx, phplus p1 p2, O, ghplus C1 C2, id).
  tauto.
  exists wt, ot.
  assumption.
  intros.
  apply NONE1.
  unfold not.
  intros.
  rewrite H0 in H.
  contradiction.
  }
  destruct LOCK as (NONE,LOCK).

  assert (EQH: forall l0 (NEQ: ll <> l0) (NEQ: (Oof ll, i, Mof ll, M'of ll) <> l0), 
    fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p1 ll None) (Oof ll, i, Mof ll, M'of ll) (Some Lock),
    O, C1, id))) (phplus (phplus Pinv p2) Pleak) l0 = 
    fold_left phplus (map pof T) (phplus Pinv Pleak) l0).
  {
  rewrite EQh.
  intros.
  apply eq_heap_initl with (z:=ll) (z':=(Oof ll, i, Mof ll, M'of ll)) (p1:=p1); try tauto.
  apply pofs.
  intros.
  apply PHPD in IN.
  apply phpdef_pair;
  tauto.
  apply in_map_iff.
  exists (nop, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  exists wt, ot.
  assumption.
  intros.
  apply NONE1.
  unfold not.
  intros.
  rewrite H0 in H.
  contradiction.
  }

  assert (hl1: h (Aof ll) = Some 1%Z).
  {
  apply ULOCKOK with wt ot.
  assumption.
  }

  exists ((Oof ll, i, Mof ll, M'of ll)::(remove (location_eq_dec Z.eq_dec) ll locs)).
  exists (phplus Pinv p2), Pleak.
  exists (((subsas (snd i) (invs (fst i) wt ot)),(Oof ll, i, Mof ll, M'of ll))::Ainv).

  assert (COMPl: comp locs (fun x0 => Aof x0)).
  {
  unfold comp.
  unfold inj.
  intros.
  apply INJ.
  apply LOCs in IN.
  assumption.
  apply LOCs in IN0.
  assumption.
  assumption.
  }


  assert (EQWT': forall l0 p O C, filterb (xOf (fun x  => Lof x) locs) l0 (fun v => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) 
    = filterb (xOf (fun x  => Lof x) ((Oof ll, i, Mof ll, M'of ll)::(remove (location_eq_dec Z.eq_dec) ll locs))) l0 (fun v => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof
    (updl T id (tt, tx, p, O, C, id)))))).
  {
  intros.
  unfold filterb.
  apply functional_extensionality.
  intros.

  rewrite <- eq_xof.
  destruct (xOf (fun x0 => Lof x0) locs x).
  destruct (Z.eq_dec x l0).
  reflexivity.
  destruct (Z.eq_dec z l0).
  erewrite <- filter_updl_eq.
  reflexivity.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some x)).
  inversion e0.
  reflexivity.
  intros.
  assert (EQ: x' = (nop, tx, phplus p1 p2, O, ghplus C1 C2,id)).
  {
  apply in_elem with T; assumption.
  }
  rewrite EQ.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some x)).
  inversion e0.
  reflexivity.
  reflexivity.
  reflexivity.
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }

  assert (EQO: forall p, map oof (updl T id (tt, tx, p, O, C1, id)) = map oof T).
  {
  intros.
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, phplus p1 p2, O, ghplus C1 C2)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQAO: forall p C, map Aoof (updl T id (tt, tx, p, O, C, id)) = map Aoof T).
  {
  intros.
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, phplus p1 p2, O, ghplus C1 C2)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  reflexivity.
  reflexivity.
  }


  assert (EQOT': forall l0 p C, filterb (xOf (fun x  => Lof x) locs) l0 (count_occ Z.eq_dec (concat (map Aoof T))) =
    filterb (xOf (fun x  => Lof x) ((Oof ll, i, Mof ll, M'of ll)::(remove (location_eq_dec Z.eq_dec) ll locs)))
    l0 (count_occ Z.eq_dec (concat (map Aoof (updl T id (tt, tx, p, O, C, id)))))).
  {
  intros.
  unfold filterb.
  apply functional_extensionality.
  intros.
  rewrite <- eq_xof.
  destruct (xOf (fun x0 => Lof x0) locs x).
  destruct (Z.eq_dec x l0).
  reflexivity.
  destruct (Z.eq_dec z l0).
  rewrite EQAO.
  reflexivity.
  reflexivity.
  reflexivity.
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }

  assert (phpdefpi2pl: phplusdef (phplus Pinv p2) Pleak).
  {
  apply phpdef_pair';
  try tauto.
  apply phpdef_comm.
  auto.
  }

  assert (phpdefup1pl: phplusdef (upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock)) Pleak).
  {
  apply phpdef_locked_lock;
  try tauto.
  exists wt, ot.
  right.
  assumption.
  }

  assert (phpdefp0il: forall p0 : pheap, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  apply phpdef_pair; try tauto.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  }

  assert (pilN: (Oof ll, i, Mof ll, M'of ll) <> ll ->
    (phplus Pinv Pleak) (Oof ll, i, Mof ll, M'of ll) = None).
  {
  intros.
  apply fold_None with (m:=pof) (l:=T) (b:=phplus Pinv Pleak); try tauto.
  }

  assert (p12N: (Oof ll, i, Mof ll, M'of ll) <> ll ->
    (phplus p1 p2) (Oof ll, i, Mof ll, M'of ll) = None).
  {
  intros.
  apply fold_None with (m:=pof) (l:=T) (b:=phplus Pinv Pleak); try tauto.
  }

  assert (p2N: (Oof ll, i, Mof ll, M'of ll) <> ll ->
    p2 (Oof ll, i, Mof ll, M'of ll) = None).
  {
  intros.
  apply phplus_None with p1.
  rewrite phplus_comm; try tauto.
  repeat php_.
  }

  assert (piN: (Oof ll, i, Mof ll, M'of ll) <> ll ->
    Pinv (Oof ll, i, Mof ll, M'of ll) = None).
  {
  intros.
  apply phplus_None with Pleak.
  apply pilN.
  assumption.
  }

  assert (plN: (Oof ll, i, Mof ll, M'of ll) <> ll ->
    Pleak (Oof ll, i, Mof ll, M'of ll) = None).
  {
  intros.
  apply phplus_None with Pinv.
  rewrite phplus_comm; repeat php_.
  apply pilN.
  assumption.
  }

  assert (phpdefpnpi: phplusdef (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p1 ll None)
    (Oof ll, i, Mof ll, M'of ll) (Some Lock)) Pinv).
  {
  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) ll).
  rewrite e.
  rewrite upd_upd.
  apply phpdef_locked_lock; repeat php_.
  exists wt, ot.
  right.
  assumption.
  apply phpdef_v.
  apply phpdef_none; repeat php_.
  apply piN.
  assumption.
  }

  assert (phpdefpnp2: phplusdef (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p1 ll None)
    (Oof ll, i, Mof ll, M'of ll) (Some Lock)) p2).
  {
  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) ll).
  rewrite e.
  rewrite upd_upd.
  apply phpdef_locked_lock; repeat php_.
  exists wt, ot.
  right.
  assumption.
  apply phpdef_v.
  apply phpdef_none; repeat php_.
  apply p2N.
  assumption.
  }

  assert (phpdefpnpl: phplusdef (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p1 ll None)
    (Oof ll, i, Mof ll, M'of ll) (Some Lock)) Pleak).
  {
  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) ll).
  rewrite e.
  rewrite upd_upd.
  apply phpdef_locked_lock; repeat php_.
  exists wt, ot.
  right.
  assumption.
  apply phpdef_v.
  apply phpdef_none; repeat php_.
  apply plN.
  assumption.
  }

  assert (bpilp: boundph (phplus (phplus Pinv Pleak) (phplus p1 p2))).
  {
  apply boundph_fold with (m:=pof) (l:=T); repeat php_.
  }

  assert (bpip2pl: boundph (phplus (phplus Pinv p2) Pleak)).
  {
  rewrite phplus_comm; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  apply boundph_mon with p1; repeat php_.
  rewrite phplus_assoc; repeat php_.
  replace (phplus p2 p1) with (phplus p1 p2); repeat php_.
  replace (phplus Pleak Pinv) with (phplus Pinv Pleak); repeat php_.
  }

  assert (bpip2: boundph (phplus Pinv p2)).
  {
  apply boundph_mon with Pleak; repeat php_.
  }

  assert (bpn: boundph (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p1 ll None)
    (Oof ll, i, Mof ll, M'of ll) (Some Lock))).
  {
  apply boundph_upd.
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (ghpdefC12il: ghplusdef (ghplus C1 C2) Cinv /\ ghplusdef (ghplus C1 C2) Cleak).
  {
  apply GHPD.
  apply in_map_iff.
  exists (nop, tx, phplus p1 p2, O, ghplus C1 C2, id).
  tauto.
  }

  assert (ghpdefc1ic2i: ghplusdef C1 Cinv /\ ghplusdef C2 Cinv).
  {
  apply ghpdef_dist.
  tauto.
  tauto.
  }

  assert (ghpdefc1lc2l: ghplusdef C1 Cleak /\ ghplusdef C2 Cleak).
  {
  apply ghpdef_dist; repeat php_.
  }

  assert (EQc: ghplus (ghplus Cinv C2) Cleak = ghplus (ghplus Cinv Cleak) C2).
  {
  rewrite ghplus_assoc; repeat php_.
  }

  assert (bgil12: boundgh (ghplus (ghplus Cinv Cleak) (ghplus C1 C2))).
  {
  apply boundgh_fold with (m:=gof) (l:=T); repeat php_.
  intros.
  apply GHPD in IN.
  apply ghpdef_pair; repeat php_.
  apply in_map_iff.
  exists (nop, tx, phplus p1 p2, O, ghplus C1 C2, id).
  tauto.
  }

  assert (bgi2: boundgh (ghplus Cinv C2)).
  {
  rewrite ghplus_comm; repeat php_.
  apply boundgh_mon with Cleak; repeat php_.
  rewrite ghplus_assoc; repeat php_.
  rewrite ghplus_comm; repeat php_.
  rewrite ghplus_assoc; repeat php_.
  replace (ghplus C2 C1) with (ghplus C1 C2); repeat php_.
  }

  assert (bci: boundgh Cinv).
  {
  apply boundgh_mon with Cleak.
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  right.
  reflexivity.
  }

  assert (bc2: boundgh C2).
  {
  apply boundgh_mon with C1; repeat php_.
  rewrite ghplus_comm; repeat php_.
  }

  assert (bc1: boundgh C1).
  {
  apply boundgh_mon with C2; repeat php_.
  }

  rewrite EQO.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  rewrite EQc.
  rewrite eq_gheap_Wait with (p1:=C1); repeat php_.
  apply gofs.
  intros.
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  apply in_map_iff.
  exists (nop, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  assumption.
  }

  exists.
  {
  split.
  {
  intros.
  eapply SPUR1 with (c:=c).
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  destruct (Z.eq_dec (snd y) id).
  unfold cmdof in EQy.
  rewrite <- EQy in WASW.
  inversion WASW.
  apply in_map_iff.
  exists y.
  auto.
  apply WASW.
  }

  intros.
  rewrite EQH in CONDv.
  apply SPUR2 in CONDv.
  destruct CONDv as (a,(b,(c,d))).
  destruct (location_eq_dec Z.eq_dec ll a).
  {
  rewrite <- e in *.
  rewrite LOCKED in c.
  destruct c as [c|c].
  inversion c.
  destruct c as (wt',(ot',c)).
  inversion c.
  }
  exists a, b.
  exists.
  destruct (location_eq_dec Z.eq_dec (Oof ll, i, Mof ll, M'of ll) a).
  left.
  rewrite <- e.
  rewrite LOCK.
  reflexivity.
  rewrite EQH.
  assumption.
  assumption.
  assumption.
  assumption.
  unfold not.
  intros CO.
  rewrite <- CO in CONDv.
  destruct (location_eq_dec Z.eq_dec (Oof ll, i, Mof ll, M'of ll) ll).
  rewrite e in *.
  rewrite LOCK in CONDv.
  inversion CONDv.
  rewrite NONE in CONDv.
  inversion CONDv.
  assumption.
  unfold not.
  intros CO.
  rewrite <- CO in CONDv.
  rewrite LOCK in CONDv.
  inversion CONDv.
  }

  exists.
  {
  exists.
  {
  apply defl_initl with (p1:=p1) (p2:=p2) (z:=ll) (z':=(Oof ll, i, Mof ll, M'of ll)) (b:=phplus Pinv Pleak);  repeat php_.
  apply in_map_iff.
  exists (nop, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  exists wt, ot.
  assumption.
  intros.
  apply NONE1.
  unfold not.
  intros.
  rewrite H0 in H.
  contradiction.
  }
  exists. tauto.
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  rewrite <- EQ.
  split.
  apply phpdef_pair; repeat php_.
  apply phpdef_comm; repeat php_.
  simpl in EQ.
  rewrite EQ in IN.
  split.
  apply phpdef_pair; repeat php_.
  apply PHPD.
  apply in_map_iff.
  exists (x1, x2, p0, x4, x5, x6).
  auto.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1. 
  assumption.
  apply DEFL with id x6.
  omega.
  apply in_map_iff.
  exists (nop, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, p0, x4, x5, x6).
  auto.
  apply PHPD.
  apply in_map_iff.
  exists (x1, x2, p0, x4, x5, x6).
  auto.
  }

  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  rewrite <- EQ.
  assumption.
  simpl in EQ.
  rewrite <- EQ.
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  exists.
  tauto.
  exists. tauto.
  exists.
  repeat php_.
  rewrite EQh.
  exists.
  {
  unfold boundph.
  intros.
  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) x).
  rewrite <- e in H.
  rewrite <- EQh in H.
  rewrite LOCK in H.
  inversion H.
  destruct ((location_eq_dec Z.eq_dec) ll x).
  rewrite <- e in H.
  rewrite <- EQh in H.
  rewrite NONE in H.
  inversion H.
  rewrite e in *.
  assumption.
  rewrite <- EQh in H.
  rewrite EQH in H.
  unfold boundph in BPT.
  eapply BPT.
  apply H.
  assumption.
  assumption.
  }

  unfold phtoh in *.
  intros.
  destruct PH2H as (PH2H,PH2H2).
  split.
  intros.
  specialize PH2H with l.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite <- EQh.
  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) ll) as [eqll|eqll].
  rewrite eqll in *.
  rewrite LOCK.
  assumption.
  rewrite NONE.
  trivial.
  assumption.
  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) l).
  rewrite <- e.
  rewrite <- EQh.
  rewrite LOCK.
  assumption.
  rewrite <- EQh.
  rewrite EQH.
  assumption.
  assumption.
  assumption.
  intros.
  apply PH2H2.
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  assert (CO: Aof (Oof ll, i, Mof ll, M'of ll) = z).
  {
  rewrite <- e in EQ.
  assumption.
  }
  apply NONE0 in CO.
  rewrite <- EQh in CO.
  rewrite LOCK in CO.
  inversion CO.
  apply NONE0 in EQ.
  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) l).
  rewrite <- e.
  apply NONE1.
  rewrite e.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  rewrite <- EQH.
  rewrite EQh.
  assumption.
  assumption.
  assumption.
  }
  exists.
  {
  exists.
  {
  apply deflg_Wait with C1 C2; repeat php_.
  apply in_map_iff.
  exists (nop, tx, phplus p1 p2, O, ghplus C1 C2, id).
  tauto.
  }
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold gof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  rewrite <- EQ.
  split.
  apply ghpdef_pair; repeat php_.
  apply ghpdef_comm; repeat php_.
  simpl in EQ.
  rewrite <- EQ.
  split.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  apply ghpdef_comm; repeat php_.
  apply ghpdef_assoc_mon with C1. repeat php_.
  apply DEFLg with id x6.
  omega.
  apply in_map_iff.
  exists (nop, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  apply proj2 with (ghplusdef x5 Cinv).
  apply GHPD.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  exists.
  {
  apply ghpdef_pair'; repeat php_.
  }
  rewrite EQc.
  rewrite eq_gheap_Wait with (p1:=C1); repeat php_.
  apply gofs.
  intros.
  apply GHPD in IN.
  apply ghpdef_pair; repeat php_.
  apply in_map_iff.
  exists (nop, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  }

  exists.
  {
  apply NoDup_updl.
  assumption.
  }

  exists.
  {
  exists.
  {
  simpl.
  apply NoDup_cons.
  unfold not.
  intros.
  apply AinvOK in H.
  destruct H as (CO1,CO2).
  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) ll).
  rewrite e in CO1.
  rewrite LOCKED in CO1.
  inversion CO1.
  rewrite NONE1 in CO1.
  inversion CO1.
  assumption.
  assumption.
  }
  exists.
  {
  simpl.
  intros.
  destruct IN as [EQ|IN].
  rewrite <- EQ.
  split.
  assumption.
  assumption.
  apply AinvOK in IN.
  destruct IN as (EQ1,EQ2).
  destruct ((location_eq_dec Z.eq_dec) l ll).
  rewrite e in EQ1.
  rewrite LOCKED in EQ1.
  inversion EQ1.
  rewrite EQH.
  split.
  assumption.
  assumption.
  unfold not.
  intros.
  apply n.
  symmetry.
  assumption.
  unfold not.
  intros.
  rewrite <- H in EQ1.
  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) ll).
  rewrite e in EQ1.
  rewrite LOCKED in EQ1.
  inversion EQ1.
  rewrite NONE1 in EQ1.
  inversion EQ1.
  assumption.
  }

  exists.
  {
  intros.

  rewrite <- EQWT'.
  rewrite <- EQOT'.

  unfold upd in NOTHELD.
  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) l).
  rewrite <- e.
  left.
  assert (wot: wt = filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) /\
    ot = filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))).
  {
  apply WTsOTsOK.
  right.
  assumption.
  }
  destruct wot as (wteq,oteq).
  rewrite wteq.
  rewrite oteq.
  reflexivity.

  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in LOCK0.
  rewrite NONE in LOCK0.
  inversion LOCK0.
  rewrite e in *.
  assumption.
  right.
  apply INAOK.
  rewrite <- EQH; try assumption.
  assumption.
  }

  simpl.
  apply fold_left_g_can.
  unfold cang.
  split.
  intros.
  apply sat_comm.
  assumption.
  simpl.
  intros.
  apply sat_perm with (l:=l);
  try assumption.
  apply sat_comm.
  apply sat_plus with None None; repeat php_.
  apply None_op.
  }

  exists.
  {
  unfold injph.
  unfold inj.
  intros.

  assert (G: forall x1 (NEQ: (Oof ll, i, Mof ll, M'of ll) <> x1),
    fold_left phplus (map pof (updl T id (tt, tx, (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p1 ll None)
    (Oof ll, i, Mof ll, M'of ll) (Some Lock)), O, C1, id)))
    (phplus (phplus Pinv p2) Pleak) x1 <> None -> 
    fold_left phplus (map pof T) (phplus Pinv Pleak) x1 <> None).
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll x1).
  rewrite <- e.
  rewrite LOCKED.
  apply some_none.
  rewrite <- EQH.
  assumption.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) x1).
  rewrite <- e in *.
  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) x2).
  rewrite <- e0 in *.
  reflexivity.
  destruct ((location_eq_dec Z.eq_dec) ll x2).
  rewrite <- e0 in *.
  rewrite NONE in px2.
  contradiction.
  assumption.
  assert (CO: ll = x2).
  {
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  apply G.
  assumption.
  assumption.
  rewrite <- H.
  reflexivity.
  }
  contradiction.
  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) x2).
  rewrite <- e in *.
  destruct ((location_eq_dec Z.eq_dec) ll x1).
  rewrite <- e0 in *.
  rewrite NONE in px1.
  contradiction.
  assumption.
  assert (CO: ll = x1).
  {
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  apply G.
  assumption.
  assumption.
  rewrite H.
  reflexivity.
  }
  contradiction.

  apply INJ.
  apply G; try assumption.
  apply G; try assumption.
  assumption.
  }

  assert (tmp: Lof ll = Aof ll /\ Pof ll = false /\ Xof ll = None /\
    (h (Aof ll) <> Some 1%Z -> In (Oof ll) (concat (map oof T)))).
  {
  apply LOCKOK.
  right.
  exists wt, ot.
  right.
  assumption.
  }
  destruct tmp as (lofll,rest).

  exists.
  {
  unfold lcomp.
  simpl.
  intros.
  destruct IN as [EQ|IN].
  rewrite <- EQ.
  unfold Lof in *.
  unfold Oof in *.
  simpl in *.
  rewrite lofll.
  left.
  reflexivity.
  apply in_remove_in in IN.
  apply LCOM in IN.
  apply in_map_iff in IN.
  destruct IN as (x',(EQ',IN')).
  destruct ((location_eq_dec Z.eq_dec) x' ll).
  rewrite e in *.
  left.
  assumption.
  right.
  apply in_map_iff.
  exists x'.
  split.
  assumption.
  apply in_in_remove.
  assumption.
  assumption.
  }
  split.
  {
  split.
  intros.
  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) l).
  left.
  assumption.
  right.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite e in *.
  rewrite NONE in H.
  contradiction.
  assumption.
  apply in_in_remove.
  unfold not.
  intros.
  rewrite H0 in n0.
  contradiction.
  apply LOCs.
  rewrite <- EQH.
  assumption.
  assumption.
  assumption.
  intros.
  destruct H as [EQ|IN].
  rewrite <- EQ.
  rewrite LOCK.
  apply some_none.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  assert (CO: ~ In ll (remove (location_eq_dec Z.eq_dec) ll locs)).
  apply remove_In.
  contradiction.
  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) l).
  rewrite <- e.
  rewrite LOCK.
  apply some_none.
  rewrite EQH.
  apply LOCs.
  eapply in_remove_in.
  apply IN.
  assumption.
  assumption.
  }
  intros.
  assert (IN':=IN).
  apply OBsOK in IN.
  destruct IN as (l',(EQl',pl')).
  exists l', EQl'.
  destruct ((location_eq_dec Z.eq_dec) ll l').
  apply ULOCKOK in LOCKED.
  destruct LOCKED.
  rewrite <- EQl' in IN'.
  rewrite <-e in IN'.
  contradiction.

  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) l').
  rewrite <- e.
  rewrite LOCK.
  apply some_none.
  rewrite EQH; assumption.
  }
  exists.
  {
  exists.
  {
  intros.
  assert (tmp: Lof ll = Aof ll /\ Pof ll = false /\ Xof ll = None /\
    (h (Aof ll) <> Some 1%Z -> In (Oof ll) (concat (map oof T)))).
  {
  apply LOCKOK.
  right.
  exists wt, ot. right. assumption.
  }

  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) l).
  rewrite <- e.
  unfold Lof, Aof, Rof, Xof, Mof, Pof in *.
  tauto.

  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite NONE in LOCK0.
  destruct LOCK0 as [CO|CO].
  inversion CO.
  destruct CO as (wt',(ot',CO)).
  destruct CO as [CO|CO];
  inversion CO.
  assumption.
  apply LOCKOK.
  rewrite <- EQH.
  assumption.
  assumption.
  assumption.
  }
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) ll).
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite e in *.
  rewrite <- e0 in ULOCK.
  rewrite LOCK in ULOCK.
  inversion ULOCK.
  rewrite EQH in ULOCK.
  apply ULOCKOK with wt0 ot0; try assumption.
  assumption.
  rewrite e.
  assumption.
  assert (n1:=n).
  assert (n2:=n).
  apply NONE in n.
  apply NONE1 in n1.
  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) l).
  rewrite <- e.
  split.
  unfold Aof in *.
  unfold Oof in *.
  assumption.
  apply ULOCKOK in LOCKED.
  destruct LOCKED.
  assumption.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e.
  apply ULOCKOK with wt ot; assumption.
  apply ULOCKOK with wt0 ot0.
  rewrite <- EQH; try assumption.
  }
  intros.

  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) l).
  rewrite <- e in UCOND.
  rewrite LOCK in UCOND.
  inversion UCOND.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e.
  apply ULOCKOK in LOCKED.
  tauto.
  apply UCONDOK.
  rewrite <- EQH; assumption.
  }
  exists.
  {
  intros.
  rewrite <- EQWT'.
  rewrite <- EQOT'.
  destruct ((location_eq_dec Z.eq_dec) ll l) as [ll0|ll0].
  rewrite <- ll0 in ULOCKED.

  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) ll).
  rewrite e in *.
  rewrite LOCK in ULOCKED.
  destruct ULOCKED as [U1|U1];
  inversion U1.
  rewrite NONE in ULOCKED.
  destruct ULOCKED as [U1|U1];
  inversion U1.
  assumption.

  destruct ((location_eq_dec Z.eq_dec) (Oof ll, i, Mof ll, M'of ll) l).

  rewrite <- e in ULOCKED.
  rewrite LOCK in ULOCKED.
  destruct ULOCKED as [U1|U1];
  inversion U1.

  apply WTsOTsOK.
  rewrite <- EQH.
  assumption.
  assumption.
  assumption.
  }

  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  {
(* ==================== x6 = id ===========*)
  symmetry in EQ.
  inversion EQ.
  exists.
  assumption.
  exists.
  eapply sat_weak_imp1; try assumption.
  apply SAT.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  }
(* ==================== x6 <> id ===========*)
  symmetry in EQ.
  inversion EQ.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF1,(WP1,VOBS1)).
  exists.
  assumption.
  exists.
  assert (bx3: boundph x3).
  {
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  split. reflexivity. assumption.
  }

  assert (bgx5: boundgh x5).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  split. reflexivity. assumption.
  }
  eapply sat_ct_weak_imp; try assumption.
  apply WP1.
  omega.
  intros.
  assert (W:=W4COND).
  apply VOBS1 in W4COND.
  destruct W4COND as (v,(l1,(inv,(inl,(eqv,(eql,safev)))))).

  assert (NEQ: v <> ll).
  {
  rewrite W in IN.
  assert (IN':=IN).
  apply SOBS in IN.
  destruct IN as (WP2,(SAT1,rest)).
  apply sat_wait4cond in SAT1.

  destruct SAT1 as (l3,(v1,(eql1,(eqv1,(x3v,(x3l,(lov1,rest'))))))).

  assert (fv: fold_left phplus (map pof T) (phplus Pinv Pleak) v1 = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (Waiting4cond ev el, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }

  assert (eqvv1: v = v1).
  {
  apply INJ.
  apply LOCs.
  assumption.
  rewrite fv.
  apply some_none.
  rewrite eqv.
  omega.
  }
  rewrite <- eqvv1 in fv.
  unfold not.
  intros.
  rewrite H in fv.
  rewrite LOCKED in fv.
  inversion fv.
  }

  exists v, l1. 
  exists.
  right.
  apply in_in_remove.
  assumption.
  assumption.
  exists.
  {
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  {
  assert (tmp:=IN).
  rewrite W in *.
  apply SOBS in tmp.
  destruct tmp as (wf3,(sat3,rest)).
  apply sat_wait4cond in sat3.
  destruct sat3 as (l',(v',(eql',(eqv',(x3v,(x3l,rest')))))).

  assert (LOCKED': fold_left phplus (map pof T) (phplus Pinv Pleak) l' = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) l' = Some (Locked wt ot)).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  right.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (Waiting4cond ev el, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }

  assert (EQ1: l' = l1).
  {
  apply INJ.
  destruct LOCKED' as [L|L].
  rewrite L.
  apply some_none.
  destruct L as (wt',(ot',L)).
  rewrite L.
  apply some_none.
  apply LOCs.
  assumption.
  omega.
  }
  rewrite EQ1 in LOCKED'.
  rewrite e in LOCKED'.
  rewrite LOCKED in LOCKED'.
  destruct LOCKED' as [L|L].
  inversion L.
  destruct L as (wt',(ot',L)).
  inversion L.
  }
  right.
  apply in_in_remove; assumption.
  }
  exists eqv, eql.
  unfold WTs, OBs in safev.
  rewrite <- EQWT'.
  rewrite <- EQOT'.
  assumption.
Qed.


Lemma g_initc_preserves_validity0:
  forall m sp h T id tx p O C Cinv Cleak invs (ll: location Z) ml m'l lk wt ot l
         (INT: In (nop, tx, p, O, C, id) T)
         (eql: Aof ll = ([[l]]))
         (pl: p ll = Some Ucond)
         (plk: p lk = Some (Ulock wt ot))
         (SAT: sat (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p ll None)
           ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) (Some Icond)) (Some O) C (weakest_pre_ct (S m) sp (tt, tx) invs))
         (VALID: validk0 (S m) sp T Cinv Cleak h invs),
    validk0 m sp (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p ll None) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) (Some Icond), O, C, id)) Cinv Cleak h invs.
Proof.
  intros.
  unfold validk0 in VALID.
  destruct VALID as (locs,(Pinv,(Pleak,(Ainv,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS))))))))))))).
  unfold validk0.
  unfold pheaps_heap in *.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  unfold locations_ok in *.
  destruct LOCsOK as (INJ,(LCOM,(LOCs,OBsOK))).
  unfold invs_ok in *.
  destruct INVsOK as (NDPA,(AinvOK,(INAOK,SATAOK))).
  unfold locks_ok.
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.
  unfold validk0.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  assert (injp: injph p).
  {
  unfold injph.
  unfold inj.
  intros.
  assert (xs: forall x1, p x1 <> None -> fold_left phplus (map pof T) (phplus Pinv Pleak) x1 <> None).
  {
  intros.
  apply fold_some; repeat php_.
  apply pofs.
  intros.
  apply PHPD in IN.
  apply phpdef_pair; repeat php_.
  exists p.
  exists.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  assumption.
  } 
  apply INJ.
  apply xs.
  assumption.
  apply xs.
  assumption.
  assumption.
  }
  assert (neqlkll: lk <> ll).
  {
  unfold not.
  intros.
  rewrite H in plk.
  rewrite pl in plk.
  inversion plk.
  }

  assert (INpT: In p (map pof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (ULOCK: fold_left phplus (map pof T) (phplus Pinv Pleak) lk = Some (Ulock wt ot)).
  {
  apply fold_ulock; repeat php_.
  apply pofs.
  intros.
  apply PHPD in IN.
  apply phpdef_pair; repeat php_.
  right.
  exists p.
  exists.
  assumption.  
  assumption.  
  }

  assert (UCOND: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some Ucond).
  {
  apply fold_ucond.
  apply pofs.
  assumption.
  assumption.
  intros.
  apply PHPD in IN.
  apply phpdef_pair;
  tauto.
  right.
  exists p, INpT.
  assumption.
  }

  assert (NONE1: ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) <> ll -> 
    fold_left phplus (map pof T) (phplus Pinv Pleak) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) = None).
  {
  intros.
  destruct (fold_left phplus (map pof T) (phplus Pinv Pleak) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l)) eqn:fl1.
  assert (CO: ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) = ll).
  {
  apply INJ.
  rewrite fl1.
  apply some_none.
  rewrite UCOND.
  apply some_none.
  reflexivity.
  }
  contradiction.
  reflexivity.
  }

  assert (phpdefppipl: In p (map pof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  tauto.
  }

  apply PHPD in phpdefppipl.

  assert (COND: (((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) <> ll -> 
    fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p ll None) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) (Some Icond), O, C, id)))
    (phplus Pinv Pleak) ll = None) /\
    fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p ll None) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) (Some Icond), O, C, id)))
    (phplus Pinv Pleak) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) = Some Icond).
  {
  apply cond_initc with p; repeat php_.
  apply pofs.
  intros.
  apply PHPD in IN.
  apply phpdef_pair;
  tauto.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  tauto.
  intros.
  apply NONE1.
  unfold not.
  intros.
  rewrite H0 in H.
  contradiction.
  }
  destruct COND as (NONE,COND).

  assert (EQH: forall l0 (NEQ: ll <> l0) (NEQ: ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) <> l0), 
    fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p ll None) 
   ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) (Some Icond), O, C, id))) (phplus Pinv Pleak) l0 = 
    fold_left phplus (map pof T) (phplus Pinv Pleak) l0).
  {
  intros.
  apply eq_heap_initc with (z:=ll) (z':=((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l)) (p:=p);
  repeat php_.
  apply pofs.
  intros.
  apply PHPD in IN.
  apply phpdef_pair;
  tauto.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  intros.
  apply NONE1.
  unfold not.
  intros.
  rewrite H0 in H.
  contradiction.
  auto.
  }

  assert (EQC: map gof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p ll None)
    ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) (Some Icond), O, C, id)) = map gof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  assumption.
  assumption.
  }
  inversion EQX.
  reflexivity.
  reflexivity.
  }

  assert (EQC': map (fun x => (gof x, snd x)) (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p ll None)
    ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) (Some Icond), O, C, id)) = map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  assumption.
  assumption.
  }
  inversion EQX.
  reflexivity.
  reflexivity.
  }

  exists (((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l)::(remove (location_eq_dec Z.eq_dec) ll locs)).
  exists Pinv, Pleak, Ainv.

  rewrite EQC.
  rewrite EQC'.

  assert (COMPl: comp locs (fun x0 => Aof x0)).
  {
  unfold comp.
  unfold inj.
  intros.
  apply INJ.
  apply LOCs in IN.
  assumption.
  apply LOCs in IN0.
  assumption.
  assumption.
  }

  assert (LEN0: length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some (Aof ll))))
    (map cmdof T)) = 0).
  {
  destruct ((filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some (Aof ll))))
   (map cmdof T))) eqn:fil.
  reflexivity.
  assert (CO: In c (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some (Aof ll))))
    (map cmdof T))).
  {
  rewrite fil.
  left.
  reflexivity.
  }
  apply filter_In in CO.
  destruct CO as (CO1,CO2).
  destruct (opZ_eq_dec (waiting_for_cond c) (Some (Aof ll))).
  Focus 2.
  inversion CO2.
  apply in_map_iff in CO1.
  destruct CO1 as (x',(eqx',inx')).
  destruct x' as (((((x1,x2),x3),x4),x5),x6).
  unfold cmdof in eqx'.
  simpl in eqx'.
  rewrite eqx' in inx'.
  destruct c;
  inversion e.
  {
  assert (inx'':=inx').
  apply SOBS in inx'.
  destruct inx' as (wf',(sat',rest)).
  apply sat_wait4cond in sat'.
  destruct sat' as (l',(v',(eql',(eqv',(x3v',rest'))))).

  assert (COND':fold_left phplus (map pof T) (phplus Pinv Pleak) v' = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  intros.
  apply PHPD in IN.
  apply phpdef_pair; repeat php_.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (Waiting4cond v l1, x2, x3, x4, x5, x6).
  tauto.
  assumption.
  }

  assert (eqv'll: v' = ll).
  {
  apply INJ.
  rewrite COND'.
  apply some_none.
  rewrite UCOND.
  apply some_none.
  omega.
  }
  rewrite eqv'll in COND'.
  rewrite UCOND in COND'.
  inversion COND'.
  }

  {
  assert (inx'':=inx').
  apply SOBS in inx'.
  destruct inx' as (wf',(sat',rest)).
  apply sat_WasWaiting4cond in sat'.
  destruct sat' as (ll',(lv',(eqll',(eqlv',(lofv',(pl',(pv',(prcl',SAT1')))))))).

  assert (COND':fold_left phplus (map pof T) (phplus Pinv Pleak) lv' = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  intros.
  apply PHPD in IN.
  apply phpdef_pair; repeat php_.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (WasWaiting4cond v l1, x2, x3, x4, x5, x6).
  tauto.
  assumption.
  }

  assert (eqv'll: lv' = ll).
  {
  apply INJ.
  rewrite COND'.
  apply some_none.
  rewrite UCOND.
  apply some_none.
  omega.
  }
  rewrite eqv'll in COND'.
  rewrite UCOND in COND'.
  inversion COND'.
  }
  }

  assert (LEN1: forall p0 O0 C0, length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some (Aof ll))))
    (map cmdof (updl T id (tt, tx, p0, O0, C0, id)))) = 0).
  {
  intros.
  erewrite <- filter_updl_eq.
  assumption.
  simpl.
  destruct (opZ_eq_dec None (Some (Aof ll))).
  inversion e.
  reflexivity.
  intros.
  simpl.
  assert (EQ: x' = (nop, tx, p, O, C,id)).
  {
  apply in_elem with T; assumption.
  }
  rewrite EQ.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some (Aof ll))).
  inversion e.
  reflexivity.
  }

  assert (EQWT': forall l0 p O C, filterb (xOf (fun x => Lof x) locs) l0 (fun v => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) 
    = filterb (xOf (fun x  => Lof x) (((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l)::(remove (location_eq_dec Z.eq_dec) ll locs))) l0 (fun v => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof
    (updl T id (tt, tx, p, O, C, id)))))).
  {
  intros.
  unfold filterb.
  apply functional_extensionality.
  intros.
  simpl.
  unfold Aof at 1.
  unfold Oof.
  unfold Aofo.
  unfold Lof.
  unfold Lofo.
  simpl.
  destruct (Z.eq_dec x (Aof ll)).
  rewrite e in *.
  {
  rewrite LEN0.
  rewrite LEN1.
  destruct (Z.eq_dec (Aof ll) l0).

  destruct (xOf (fun x0 : location Z => snd (fst (fst (Oof x0)))) locs (Aof ll));
  try reflexivity.
  destruct (xOf (fun x0 : location Z => snd (fst (fst (Oof x0)))) locs (Aof ll)).
  destruct (Z.eq_dec z l0);
  destruct (Z.eq_dec (Aof lk) l0); reflexivity.
  destruct (Z.eq_dec (Aof lk) l0); reflexivity.
  }
  rewrite <- eq_xof0.
  unfold Lof.
  unfold Oof.
  unfold Lofo.
  unfold Aofo.
  simpl.
  destruct (xOf (fun x0 : location Z => snd (fst (fst (fst (fst (fst x0)))))) locs x).
  destruct (Z.eq_dec x l0).
  reflexivity.
  destruct (Z.eq_dec z l0).
  erewrite <- filter_updl_eq.
  reflexivity.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some x)).
  inversion e0.
  reflexivity.
  intros.
  assert (EQ: x' = (nop, tx, p, O, C,id)).
  {
  apply in_elem with T; assumption.
  }
  rewrite EQ.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some x)).
  inversion e0.
  reflexivity.
  reflexivity.
  reflexivity.
  assumption.
  }

  assert (EQO: forall p, map oof (updl T id (tt, tx, p, O, C, id)) = map oof T).
  {
  intros.
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQAO: forall p C, map Aoof (updl T id (tt, tx, p, O, C, id)) = map Aoof T).
  {
  intros.
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  assert (CNT0: count_occ Z.eq_dec (concat (map Aoof T)) (Aof ll) = 0).
  {
  assert (G: ~ In (Oof ll) (concat (map oof T))).
  {
  apply UCONDOK.
  assumption.
  }
  apply count_occ_not_In.
  unfold not.
  intros.
  apply G.
  rewrite <- flat_map_concat_map.
  rewrite <- flat_map_concat_map in H.
  apply in_flat_map.
  apply in_flat_map in H.
  destruct H as (x1,(INx1,INx2)).
  exists x1.
  split.
  assumption.
  unfold Aoof in INx2.
  apply in_map_iff in INx2.
  destruct INx2 as (x3,(EQx3,INx3)).
  unfold oof.
  assert (eq1:x3=Oof ll).
  {
  assert (G1: In x3 (concat (map oof T))).
  {
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists x1.
  tauto.
  }
  apply OBsOK in G1.
  destruct G1 as (l',(EQl,pl')).
  rewrite <- EQl.
  apply injo.
  apply INJ.
  assumption.
  rewrite UCOND.
  apply some_none.
  rewrite EQl.
  rewrite EQx3.
  reflexivity.
  }
  rewrite <- eq1.
  assumption.
  }

  assert (EQOT': forall l0 p C, filterb (xOf (fun x  => Lof x) locs) l0 (count_occ Z.eq_dec (concat (map Aoof T))) =
    filterb (xOf (fun x  => Lof x) (((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l)::(remove (location_eq_dec Z.eq_dec) ll locs)))
    l0 (count_occ Z.eq_dec (concat (map Aoof (updl T id (tt, tx, p, O, C, id)))))).
  {
  intros.
  unfold filterb.
  apply functional_extensionality.
  intros.
  rewrite EQAO.
  simpl.
  unfold Aof at 1.
  unfold Lof at 2.
  unfold Aofo.
  unfold Lofo.
  unfold Oof.
  simpl.
  destruct (Z.eq_dec x (Aof ll)).
  rewrite e in *.
  rewrite CNT0.

  destruct (xOf (fun x0 => Lof x0) locs (Aof ll)) eqn:xof1.
  destruct (Z.eq_dec z (Aof lk)).
  rewrite e0.
  reflexivity.
  destruct (Z.eq_dec (Aof ll) l0).
  reflexivity.
  destruct (Z.eq_dec z l0);
  destruct (Z.eq_dec (Aof lk) l0); reflexivity.
  destruct (Z.eq_dec (Aof ll) l0).
  reflexivity.
  destruct (Z.eq_dec (Aof lk) l0); reflexivity.
  rewrite <- eq_xof0.
  reflexivity.
  assumption.
  }

  assert (phpdefup1pl: phplusdef (upd (location_eq_dec Z.eq_dec) p ll (Some Cond)) Pleak).
  {
  apply phpdef_ucond; repeat php_.
  }

  assert (phpdefp0il: forall p0 : pheap, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  apply phpdef_pair; try tauto.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  }

  assert (pilN: ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) <> ll ->
    (phplus Pinv Pleak) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) = None).
  {
  intros.
  apply fold_None with (m:=pof) (l:=T) (b:=phplus Pinv Pleak); try tauto.
  }

  assert (p12N: ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) <> ll ->
    p ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) = None).
  {
  intros.
  apply fold_None with (m:=pof) (l:=T) (b:=phplus Pinv Pleak); try tauto.
  }

  assert (piN: ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) <> ll ->
    Pinv ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) = None).
  {
  intros.
  apply phplus_None with Pleak.
  apply pilN.
  assumption.
  }

  assert (plN: ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) <> ll ->
    Pleak ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) = None).
  {
  intros.
  apply phplus_None with Pinv.
  rewrite phplus_comm; repeat php_.
  apply pilN.
  assumption.
  }

  assert (phpdefpnpi: phplusdef (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p ll None)
    ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) (Some Icond)) Pinv).
  {
  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) ll).
  rewrite e.
  rewrite upd_upd.
  apply phpdef_icond; repeat php_.
  apply phpdef_v.
  apply phpdef_none; repeat php_.
  apply piN.
  assumption.
  }

  assert (phpdefpnpl: phplusdef (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p ll None)
    ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) (Some Icond)) Pleak).
  {
  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) ll).
  rewrite e.
  rewrite upd_upd.
  apply phpdef_icond; repeat php_.
  apply phpdef_v.
  apply phpdef_none; repeat php_.
  apply plN.
  assumption.
  }

  assert (bpilp: boundph (phplus (phplus Pinv Pleak) p)).
  {
  apply boundph_fold with (m:=pof) (l:=T); repeat php_.
  }

  assert (bp: boundph p).
  {
  apply BPE.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (bpn: boundph (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p ll None)
    ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) (Some Icond))).
  {
  apply boundph_upd.
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bgil12: boundgh (ghplus (ghplus Cinv Cleak) C)).
  {
  apply boundgh_fold with (m:=gof) (l:=T); repeat php_.
  intros.
  apply GHPD in IN.
  apply ghpdef_pair; repeat php_.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  tauto.
  }

  assert (bci: boundgh Cinv).
  {
  apply boundgh_mon with Cleak.
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  right.
  reflexivity.
  }

  assert (bg: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  rewrite EQO.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  assumption.
  }
  exists.
  {
  unfold spur_ok.
  split.
  intros.
  {
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  rewrite WASW in EQx.
  inversion EQx.
  eapply SPUR1 with (c:=c).
  apply in_map_iff.
  exists x.
  auto.
  apply WASW.
  }
  intros.
  destruct (location_eq_dec Z.eq_dec (Aof ll, Rof ll, Aof lk, Xof ll, Pof ll, Iof ll, ml, m'l) v) as [eql1|eql1].
  rewrite <- eql1 in *.
  rewrite COND in CONDv.
  inversion CONDv.
  rewrite EQH in CONDv; try assumption.
  assert (SP1:=CONDv).
  apply SPUR2 in SP1.
  destruct SP1 as (a,(b,(c,d))).
  exists a, b.
  exists.
  rewrite EQH.
  assumption.
  unfold not.
  intros CO.
  rewrite <- CO in *.
  rewrite UCOND in c.
  destruct c as [c|c].
  inversion c.
  destruct c as (wt',(ot',c)).
  inversion c.
  unfold not.
  intros CO.
  rewrite <- CO in *.
  destruct (location_eq_dec Z.eq_dec (Aof ll, Rof ll, Aof lk, Xof ll, Pof ll, Iof ll, ml, m'l) ll).
  rewrite e in c.
  rewrite UCOND in c.
  destruct c as [c|c].
  inversion c.
  destruct c as (wt',(ot',c)).
  inversion c.
  rewrite NONE1 in c; try assumption.
  destruct c as [c|c].
  inversion c.
  destruct c as (wt',(ot',c)).
  inversion c.
  assumption.
  unfold not.
  intros CO.
  rewrite <- CO in *.
  rewrite NONE in CONDv.
  inversion CONDv.
  assumption.
  }

  exists.
  {
  exists.
  {
  unfold defl.
  intros.
  unfold updl in *.
  rewrite map_map in *.
  apply in_map_iff in IN1.
  apply in_map_iff in IN2.
  destruct IN1 as (x1,(EQ1,IN1)).
  destruct IN2 as (x2,(EQ2,IN2)).
  destruct (Z.eq_dec (snd x1) id).
  inversion EQ1.
  destruct (Z.eq_dec (snd x2) id).
  inversion EQ2.
  omega.
  inversion EQ2.
  unfold pof at 1.
  simpl.
  rewrite H2.

  assert (phpdefpp2: phplusdef p p2).
  {
  apply DEFL with id id2.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists x2.
  auto.
  }

  assert (p2ll: p2 ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) = None).
  {
  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) ll).
  rewrite e0 in *.
  unfold phplusdef in phpdefpp2.
  specialize phpdefpp2 with ll.
  rewrite pl in *.
  destruct (p2 ll).
  contradiction.
  reflexivity.
  apply fold_None with (m:=pof) (l:=T) (b:=phplus Pinv Pleak); repeat php_.
  apply NONE1.
  assumption.
  left.
  apply in_map_iff.
  exists x2.
  auto.
  }
  apply phpdef_upd_none; try assumption.
  apply phpdef_none; try assumption.

  inversion EQ1.
  destruct (Z.eq_dec (snd x2) id).
  inversion EQ2.
  unfold pof at 2.
  simpl.
  rewrite H0.

  assert (phpdefpp1: phplusdef p p1).
  {
  apply DEFL with id id1.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists x1.
  auto.
  }
  assert (p1ll: p1 ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) = None).
  {
  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) ll).
  rewrite e0 in *.
  unfold phplusdef in phpdefpp1.
  specialize phpdefpp1 with ll.
  rewrite pl in *.
  destruct (p1 ll).
  contradiction.
  reflexivity.
  apply fold_None with (m:=pof) (l:=T) (b:=phplus Pinv Pleak); repeat php_.
  apply NONE1.
  assumption.
  left.
  apply in_map_iff.
  exists x1.
  auto.
  }
  apply phpdef_comm.
  apply phpdef_upd_none; try assumption.
  apply phpdef_none; try assumption.

  apply DEFL with id1 id2.
  assumption.
  apply in_map_iff.
  exists x1.
  inversion EQ1.
  auto.
  apply in_map_iff.
  exists x2.
  inversion EQ2.
  auto.
  }
  exists. tauto.
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  rewrite <- EQ.
  split.

  apply phpdef_comm; repeat php_.
  apply phpdef_comm; repeat php_.
  simpl in EQ.
  rewrite EQ in IN.
  apply PHPD.
  apply in_map_iff.
  exists (x1, x2, p0, x4, x5, x6).
  auto.
  }
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  rewrite <- EQ.
  assumption.
  simpl in EQ.
  rewrite <- EQ.
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  exists.
  tauto.
  exists. tauto.
  exists.
  repeat php_.
  exists.
  {
  unfold boundph.
  intros.
  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) x).
  rewrite <- e in H.
  rewrite COND in H.
  inversion H.
  destruct ((location_eq_dec Z.eq_dec) ll x).
  rewrite <- e in H.
  rewrite NONE in H.
  inversion H.
  rewrite e in *.
  assumption.
  rewrite EQH in H.
  unfold boundph in BPT.
  eapply BPT.
  apply H.
  assumption.
  assumption.
  }

  unfold phtoh in *.
  intros.
  destruct PH2H as (PH2H,PH2H2).
  split.
  intros.
  assert (PH2H':=PH2H).
  specialize PH2H with l0.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) ll) as [eqll|eqll].
  rewrite eqll in *.
  rewrite COND.
  rewrite UCOND in PH2H.
  assumption.
  rewrite NONE.
  trivial.
  assumption.
  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) l0).
  rewrite <- e.
  rewrite COND.
  specialize PH2H' with ll.
  rewrite UCOND in PH2H'.
  assumption.
  rewrite EQH.
  assumption.
  assumption.
  assumption.
  intros.
  apply PH2H2.
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  assert (CO: Aof ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) = z).
  {
  rewrite <- e in EQ.
  assumption.
  }
  apply NONE0 in CO.
  rewrite COND in CO.
  inversion CO.
  apply NONE0 in EQ.
  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) l0).
  rewrite <- e.
  apply NONE1.
  rewrite e.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  rewrite <- EQH.
  assumption.
  assumption.
  assumption.
  }
  exists.
  {
  exists. assumption.
  exists. assumption.
  exists. assumption.
  assumption.
  }
  exists.
  {
  apply NoDup_updl.
  assumption.
  }

  exists.
  {
  exists. assumption.
  exists.
  {
  simpl.
  intros.
  split.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in IN.
  apply AinvOK in IN.
  destruct IN as (CO,IN).
  rewrite UCOND in CO.
  inversion CO.
  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) l0).
  rewrite <- e in IN.
  apply AinvOK in IN.
  destruct IN as (CO,IN).
  rewrite NONE1 in CO.
  inversion CO.
  unfold not.
  intros.
  apply n.
  rewrite <- e.
  rewrite <- H.
  reflexivity.
  rewrite EQH.
  apply AinvOK.
  assumption.
  assumption.
  assumption.
  apply AinvOK.
  assumption.
  }
  exists.
  {
  intros.

  rewrite <- EQWT'.
  rewrite <- EQOT'.
  apply INAOK.
  rewrite <- EQH.
  assumption.
  unfold not.
  intros.
  rewrite <- H in LOCK.
  rewrite NONE in LOCK.
  inversion LOCK.
  unfold not.
  intros.
  rewrite H0 in *.
  rewrite COND in LOCK.
  inversion LOCK.
  unfold not.
  intros.
  rewrite <- H in LOCK.
  rewrite COND in LOCK.
  inversion LOCK.
  assumption.
  }
  assumption.
  }

  exists.
  {
  unfold injph.
  unfold inj.
  intros.

  assert (G: forall x1 (NEQ: ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) <> x1),
    fold_left phplus (map pof (updl T id (tt, tx, (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p ll None)
    ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) (Some Icond)), O, C, id)))
    (phplus Pinv Pleak) x1 <> None -> 
    fold_left phplus (map pof T) (phplus Pinv Pleak) x1 <> None).
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll x1).
  rewrite <- e.
  rewrite UCOND.
  apply some_none.
  rewrite <- EQH.
  assumption.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) x1).
  rewrite <- e in *.
  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) x2).
  rewrite <- e0 in *.
  reflexivity.
  destruct ((location_eq_dec Z.eq_dec) ll x2).
  rewrite <- e0 in *.
  rewrite NONE in px2.
  contradiction.
  assumption.
  assert (CO: ll = x2).
  {
  apply INJ.
  rewrite UCOND.
  apply some_none.
  apply G.
  assumption.
  assumption.
  rewrite <- H.
  reflexivity.
  }
  contradiction.
  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) x2).
  rewrite <- e in *.
  destruct ((location_eq_dec Z.eq_dec) ll x1).
  rewrite <- e0 in *.
  rewrite NONE in px1.
  contradiction.
  assumption.
  assert (CO: ll = x1).
  {
  apply INJ.
  rewrite UCOND.
  apply some_none.
  apply G.
  assumption.
  assumption.
  rewrite H.
  reflexivity.
  }
  contradiction.

  apply INJ.
  apply G; try assumption.
  apply G; try assumption.
  assumption.
  }
  exists.
  {
  unfold lcomp.
  simpl.
  intros.
  destruct IN as [EQ|IN].
  rewrite <- EQ.
  right.
  unfold Lof.
  simpl.
  apply in_map_iff.
  exists lk.
  split.
  reflexivity.
  apply in_in_remove.
  assumption.
  apply LOCs.
  rewrite ULOCK.
  apply some_none.
  unfold Aof at 1.
  simpl.
  destruct (Z.eq_dec (Aof ll) (Lof x)).
  left.
  assumption.
  right.
  apply in_map_iff.
  apply in_remove_in in IN.
  apply LCOM in IN.
  apply in_map_iff in IN.
  destruct IN as (x0,(EQ0,IN0)).
  exists x0.
  split.
  assumption.
  apply in_in_remove.
  unfold not.
  intros.
  rewrite H in *.
  contradiction.
  assumption.
  }
  exists.
  {
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) l0).
  left.
  assumption.
  right.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite e in *.
  rewrite NONE in H.
  contradiction.
  assumption.
  apply in_in_remove.
  unfold not.
  intros.
  rewrite H0 in n0.
  contradiction.
  apply LOCs.
  rewrite <- EQH.
  assumption.
  assumption.
  assumption.
  }
  intros.
  destruct H as [EQ|IN].
  rewrite <- EQ.
  rewrite COND.
  apply some_none.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  assert (CO: ~ In ll (remove (location_eq_dec Z.eq_dec) ll locs)).
  apply remove_In.
  contradiction.
  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) l0).
  rewrite <- e.
  rewrite COND.
  apply some_none.
  rewrite EQH.
  apply LOCs.
  eapply in_remove_in.
  apply IN.
  assumption.
  assumption.
  }
  intros.
  assert (IN':=IN).
  apply OBsOK in IN.
  destruct IN as (l',(EQl',pl')).
  rewrite <- EQl' in IN'.
  exists l', EQl'.
  assert (neq1: ll <> l').
  {
  unfold not.
  intros.
  rewrite <- H in IN'.
  apply UCONDOK in UCOND.
  contradiction.
  }
  rewrite EQH.
  assumption.
  assumption.
  unfold not.
  intros.
  rewrite <- H in pl'.
  rewrite NONE1 in pl'.
  contradiction.
  unfold not.
  intros.
  rewrite <- H in neq1.
  rewrite <- H0 in neq1.
  contradiction.
  }
  exists.
  {
  exists.
  {
  intros.

  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) l0).
  rewrite <- e in LOCK.
  destruct LOCK as [CO|CO].
  rewrite COND in CO.
  inversion CO.
  rewrite COND in CO.
  destruct CO as (wt',(ot',CO)).
  destruct CO as [CO|CO];
  inversion CO.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  rewrite NONE in LOCK.
  destruct LOCK as [CO|CO].
  inversion CO.
  destruct CO as (wt',(ot',CO)).
  destruct CO as [CO|CO];
  inversion CO.
  assumption.
  apply LOCKOK.
  rewrite <- EQH.
  assumption.
  assumption.
  assumption.
  }
  split.
  {
  intros.
  apply ULOCKOK with wt0 ot0.
  rewrite <- EQH.
  assumption.
  unfold not.
  intros.
  rewrite <- H in ULOCK0.
  rewrite NONE in ULOCK0.
  inversion ULOCK0.
  unfold not.
  intros.
  rewrite H0 in *.
  rewrite COND in ULOCK0.
  inversion ULOCK0.
  unfold not.
  intros.
  rewrite H in *.
  rewrite COND in ULOCK0.
  inversion ULOCK0.
  }
  intros.
  apply UCONDOK.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e.
  assumption.
  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) l0).
  rewrite <- e in *.
  rewrite COND in UCOND0.
  inversion UCOND0.
  rewrite <- EQH.
  assumption.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  rewrite <- EQWT'.
  rewrite <- EQOT'.
  destruct ((location_eq_dec Z.eq_dec) ll l0) as [ll0|ll0].
  rewrite <- ll0 in ULOCKED.

  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) ll).
  rewrite e in *.
  rewrite COND in ULOCKED.
  destruct ULOCKED as [U1|U1];
  inversion U1.
  rewrite NONE in ULOCKED.
  destruct ULOCKED as [U1|U1];
  inversion U1.
  assumption.

  destruct ((location_eq_dec Z.eq_dec) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) l0).

  rewrite <- e in ULOCKED.
  rewrite COND in ULOCKED.
  destruct ULOCKED as [U1|U1];
  inversion U1.

  apply WTsOTsOK.
  rewrite <- EQH.
  assumption.
  assumption.
  assumption.
  }

  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  {
(* ==================== x6 = id ===========*)
  symmetry in EQ.
  inversion EQ.
  exists.
  assumption.
  exists.
  eapply sat_weak_imp1; try assumption.
  apply SAT.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  }
(* ==================== x6 <> id ===========*)
  symmetry in EQ.
  inversion EQ.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF1,(WP1,VOBS1)).
  exists.
  assumption.
  exists.

  assert (bx3: boundph x3).
  {
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  split. reflexivity. assumption.
  }

  assert (bx5: boundgh x5).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=(ghplus Cinv Cleak)); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  split. reflexivity. assumption.
  }

  eapply sat_weak_imp1; try assumption.
  apply WP1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  assert (W:=W4COND).
  apply VOBS1 in W4COND.
  destruct W4COND as (v,(l1,(inv,(inl,(eqv,(eql',safev)))))).

  assert (NEQ: v <> ll).
  {
  rewrite W in IN.
  assert (IN':=IN).
  apply SOBS in IN.
  destruct IN as (WP2,(SAT1,rest)).
  apply sat_wait4cond in SAT1.

  destruct SAT1 as (l3,(v1,(eql1,(eqv1,(x3v,(x3l,(lov1,rest'))))))).

  assert (fv: fold_left phplus (map pof T) (phplus Pinv Pleak) v1 = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (Waiting4cond ev el, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }

  assert (eqvv1: v = v1).
  {
  apply INJ.
  apply LOCs.
  assumption.
  rewrite fv.
  apply some_none.
  rewrite eqv.
  omega.
  }
  rewrite <- eqvv1 in fv.
  unfold not.
  intros.
  rewrite H in fv.
  rewrite UCOND in fv.
  inversion fv.
  }

  exists v, l1. 
  exists.
  right.
  apply in_in_remove.
  assumption.
  assumption.
  exists.
  {
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  {
  assert (tmp:=IN).
  rewrite W in *.
  apply SOBS in tmp.
  destruct tmp as (wf3,(sat3,rest)).
  apply sat_wait4cond in sat3.
  destruct sat3 as (l',(v',(eql'',(eqv',(x3v,(x3l,rest')))))).

  assert (LOCKED': fold_left phplus (map pof T) (phplus Pinv Pleak) l' = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) l' = Some (Locked wt ot)).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  right.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (Waiting4cond ev el, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }

  assert (EQ1: l' = l1).
  {
  apply INJ.
  destruct LOCKED' as [L|L].
  rewrite L.
  apply some_none.
  destruct L as (wt',(ot',L)).
  rewrite L.
  apply some_none.
  apply LOCs.
  assumption.
  omega.
  }
  rewrite EQ1 in LOCKED'.
  rewrite e in LOCKED'.
  rewrite UCOND in LOCKED'.
  destruct LOCKED' as [L|L].
  inversion L.
  destruct L as (wt',(ot',L)).
  inversion L.
  }
  right.
  apply in_in_remove; assumption.
  }
  exists eqv, eql'.
  unfold WTs, OBs in safev.
  rewrite <- EQWT'.
  rewrite <- EQOT'.
  assumption.
Qed.


Lemma g_finlc_preserves_validity0:
  forall m sp h T id tx p O C Cinv Cleak invs lv lk v
         (INT: In (nop, tx, p, O, C, id) T)
         (aolv: Aof lv = ([[v]]))
         (loflv: Lof lv = Aof lk)
         (plv: p lv = Some Icond)
         (plk: p lk = Some Lock \/ exists wt ot, p lk = Some (Locked wt ot))
         (spurlv: spurious_ok sp lk lv invs)
         (sat1: sat (upd (location_eq_dec Z.eq_dec) p lv (Some Cond)) (Some O) C
           (weakest_pre_ct (S m) sp (tt, tx) invs))
         (VALID: validk0 (S m) sp T Cinv Cleak h invs),
    validk0 m sp (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p lv (Some Cond), O, C, id)) Cinv Cleak h invs.
Proof.
  intros.
  unfold validk0 in VALID.
  destruct VALID as (locs,(Pinv,(Pleak,(Ainv,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS))))))))))))).
  unfold validk0.
  unfold pheaps_heap in *.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  unfold locations_ok in *.
  destruct LOCsOK as (INJ,(LCOM,(LOCs,OBsOK))).
  unfold invs_ok in *.
  destruct INVsOK as (NDPA,(AinvOK,(INAOK,SATAOK))).
  unfold locks_ok.
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.
  unfold validk0.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  exists locs, Pinv, Pleak, Ainv.

  assert (phpdefp0: forall p0, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  apply phpdef_pair;
  try tauto.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  }

  assert (inp: In p (map pof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (pnpid: In (p, id) (map (fun x => (pof x, snd x)) T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (LOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) lk = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) lk = Some (Locked wt ot)).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  right.
  right.
  exists p, inp.
  assumption.
  }

  assert (UCOND: fold_left phplus (map pof T) (phplus Pinv Pleak) lv = Some Icond).
  {
  eapply fold_icond with (m:=pof) (l:=T); repeat php_.
  apply pofs.
  right.
  exists p, inp.
  assumption.
  }

  assert (COND: fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p lv (Some Cond), O, C, id))) (phplus Pinv Pleak) lv = Some Cond).
  {
  apply cond_finlc with (z:=lv)(p:=p); repeat php_.
  apply pofs.
  }

  assert (NONE: forall p0 id' (NEQ: id <> id')
    (IN: In (p0, id') (map (fun x => (pof x, snd x)) T)), p0 lv = None).
  {
  intros.
  assert (phpd: phplusdef p p0).
  {
  apply DEFL with id id'; assumption.
  }
  unfold phplusdef in phpd.
  specialize phpd with lv.
  rewrite plv in phpd.
  destruct (p0 lv).
  contradiction.
  reflexivity.
  }

  assert (NONEi: Pinv lv = None).
  {
  assert (phpd: phplusdef p Pinv).
  {
  apply PHPD.
  assumption.
  }
  unfold phplusdef in phpd.
  specialize phpd with lv.
  rewrite plv in phpd.
  destruct (Pinv lv).
  contradiction.
  reflexivity.
  }

  assert (NONEl: Pleak lv = None).
  {
  assert (phpd: phplusdef p Pleak).
  {
  apply PHPD.
  assumption.
  }
  unfold phplusdef in phpd.
  specialize phpd with lv.
  rewrite plv in phpd.
  destruct (Pleak lv).
  contradiction.
  reflexivity.
  }

  assert (NONEil: phplus Pinv Pleak lv = None).
  {
  unfold phplus.
  rewrite NONEi.
  rewrite NONEl.
  reflexivity.
  }

  assert (EQH: forall l (NEQ: l <> lv),
    fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p lv (Some Cond), O, C, id))) (phplus Pinv Pleak) l =
    fold_left phplus (map pof T) (phplus Pinv Pleak) l).
  {
  intros.
  apply eq_heap with (z:=lv)(p:=p)(v:=Some Cond); try tauto.
  apply pofs.
  intros.
  apply phpdef_comm.
  apply phpdef_v.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ,IN)).
  inversion EQ.
  apply DEFL with id (snd x1).
  omega.
  unfold pof.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  tauto.
  apply in_map_iff.
  exists x1.
  auto.
  apply NONE with id'; assumption.
  apply phpdef_v; repeat php_.
  apply PHPD; assumption.
  apply PHPD; assumption.
  unfold not.
  intros CO.
  rewrite CO in NEQ.
  contradiction.
  }

  assert (EQ_3: map oof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p lv (Some Cond), O, C, id)) = map oof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (nop, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQ_3': map Aoof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p lv (Some Cond), O, C, id)) = map Aoof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (nop, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQ_4: map gof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p lv (Some Cond), O, C, id)) = map gof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (nop, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQ_4': map (fun x => (gof x, snd x)) (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p lv (Some Cond), O, C, id)) = map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (nop, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQ_5: forall v, filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T) =
          filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p lv (Some Cond), O, C, id)) )).
  {
  intros.
  apply filter_updl_eq.
  simpl.
  destruct (opZ_eq_dec None (Some v0)).
  inversion e.
  reflexivity.
  intros.
  unfold elem in IN.
  apply filter_In in IN.
  destruct IN as (IN,EQ).
  destruct x' as (((((x1',x2'),x3'),x4'),x5'),x6').
  simpl in EQ.
  apply Z.eqb_eq in EQ.
  rewrite EQ in *.  
  assert (EQa: (x1',x2',x3',x4',x5') = (nop, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN.
  assumption.
  assumption.
  inversion EQa.
  simpl.
  destruct (opZ_eq_dec None (Some v0)).
  inversion e.
  reflexivity.
  }
  assert (EQ_6: (fun v0 : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0)))
           (map cmdof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p lv (Some Cond), O, C, id)) ))) =
           (fun v0 : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0)))
           (map cmdof T)))).
  {
  apply functional_extensionality.
  intros.
  rewrite EQ_5.
  reflexivity.
  }

  assert (NEQ: lk <> lv).
  {
  unfold not.
  intros CO.
  rewrite <- CO in UCOND.
  rewrite UCOND in LOCKED.
  destruct LOCKED as [L|L].
  inversion L.
  destruct L as (wt,(ot,L)).
  inversion L.
  }

  assert (phpdefppi: phplusdef p Pinv).
  {
  apply PHPD.
  assumption.
  }

  assert (phpdefppl: phplusdef p Pleak).
  {
  apply PHPD.
  assumption.
  }

  assert (bp: boundph p).
  {
  apply BPE.
  assumption.
  }

  assert (bupd: boundph (upd (location_eq_dec Z.eq_dec) p lv (Some Cond))).
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bg: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  rewrite EQ_3.
  rewrite EQ_3'.
  rewrite EQ_4.
  rewrite EQ_4'.
  rewrite EQ_6.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  assumption.
  }

  exists.
  {
  split.
  {
  intros.
  eapply SPUR1 with (c:=c).
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  destruct (Z.eq_dec (snd y) id).
  unfold cmdof in EQy.
  simpl in EQy.
  rewrite <- EQy in WASW.
  inversion WASW.
  apply in_map_iff.
  exists y.
  auto.
  apply WASW.
  }
  intros.
  destruct (location_eq_dec Z.eq_dec v0 lv).
  {
  exists lk.
  rewrite e in *.
  exists. assumption.
  exists.
  rewrite EQH; assumption.
  assumption.
  }
  rewrite EQH in CONDv.
  apply SPUR2 in CONDv.
  destruct CONDv as (a,(b,(c,d))).
  exists a, b.
  exists.
  rewrite EQH; try assumption.
  unfold not.
  intros CO.
  rewrite CO in c.
  rewrite UCOND in c.
  destruct c as [c|c].
  inversion c.
  destruct c as (wt',(ot',c)).
  inversion c.
  assumption.
  assumption.
  }

  exists.
  {
  split.
  {
  unfold defl.
  intros.
  unfold updl in *.
  rewrite map_map in *.
  apply in_map_iff in IN1.
  apply in_map_iff in IN2.
  destruct IN1 as (x1,(EQ1,IN1)).
  destruct IN2 as (x2,(EQ2,IN2)).
  destruct (Z.eq_dec (snd x1) id).
  inversion EQ1.
  destruct (Z.eq_dec (snd x2) id).
  inversion EQ2.
  omega.
  inversion EQ2.
  unfold pof at 1.
  simpl.
  rewrite H2.

  assert (phpdefpp2: phplusdef p p2).
  {
  apply DEFL with id id2.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists x2.
  auto.
  }

  apply phpdef_v.
  assumption.
  apply NONE with id2.
  omega.
  apply in_map_iff.
  exists x2.
  auto.

  inversion EQ1.
  destruct (Z.eq_dec (snd x2) id).
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  apply phpdef_comm.

  assert (phpdefpp1: phplusdef p p1).
  {
  apply DEFL with id id1.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists x1.
  auto.
  }

  apply phpdef_v.
  rewrite H0.
  assumption.
  apply NONE with id1.
  omega.
  apply in_map_iff.
  exists x1.
  rewrite H1.
  auto.

  inversion EQ2.
  apply DEFL with id1 id2.
  omega.
  apply in_map_iff.
  exists x1.
  rewrite H1.
  auto.
  apply in_map_iff.
  exists x2.
  rewrite H3.
  auto.
  }
  exists. tauto.
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  rewrite <- EQ.
  split.
  apply phpdef_v; try assumption.
  apply phpdef_v; try assumption.
  simpl in EQ.
  rewrite EQ in IN.
  apply PHPD.
  apply in_map_iff.
  exists (x1, x2, p0, x4, x5, x6).
  auto.
  }
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  rewrite <- EQ.
  assumption.
  simpl in EQ.
  rewrite <- EQ.
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  {
  unfold boundph.
  intros.
  destruct ((location_eq_dec Z.eq_dec) x lv).
  rewrite e in H.
  rewrite COND in H.
  inversion H.
  rewrite EQH in H.
  unfold boundph in BPT.
  eapply BPT.
  apply H.
  assumption.
  }
  unfold phtoh in *.
  intros.
  destruct PH2H as (PH2H,PH2H2).
  split.
  intros.
  assert (PH2H':=PH2H).
  destruct ((location_eq_dec Z.eq_dec) l lv).
  specialize PH2H' with lv.
  rewrite <- e in *.
  rewrite COND.
  rewrite UCOND in PH2H'.
  assumption.
  specialize PH2H' with l.
  rewrite EQH; assumption.
  intros.
  apply PH2H2.
  intros.
  rewrite <- EQH.
  apply NONE0.
  assumption.
  unfold not.
  intros CO.
  rewrite CO in EQ.
  specialize NONE0 with lv.
  rewrite COND in NONE0.
  apply NONE0 in EQ.
  inversion EQ.
  }
  exists. tauto.
  exists.
  {
  apply NoDup_updl.
  assumption.
  }
  exists.
  {
  split. assumption.
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) l lv).
  rewrite e in IN.
  apply AinvOK in IN.
  destruct IN as (CO,IN).
  rewrite UCOND in CO.
  inversion CO.
  rewrite EQH.
  apply AinvOK; assumption.
  assumption.
  }
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) l lv).
  rewrite e in LOCK.
  rewrite COND in LOCK.
  inversion LOCK.
  apply INAOK.
  rewrite <- EQH.
  assumption.
  assumption.
  assumption.
  }
  assumption.
  }
  exists.
  {
  split.
  {
  unfold injph.
  unfold inj.
  intros.
  destruct ((location_eq_dec Z.eq_dec) x1 lv).
  rewrite e in *.
  destruct ((location_eq_dec Z.eq_dec) x2 lv).
  rewrite e0 in *.
  reflexivity.
  rewrite EQH in px2.
  apply INJ; try assumption.
  rewrite UCOND.
  apply some_none.
  assumption.
  rewrite EQH in px1; try assumption.
  destruct ((location_eq_dec Z.eq_dec) x2 lv).
  rewrite e in *.
  apply INJ; try assumption.
  rewrite UCOND.
  apply some_none.
  rewrite EQH in px2; try assumption.
  apply INJ; try assumption.
  }
  split. assumption.
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) l lv).
  rewrite e.
  split.
  intros.
  apply LOCs.
  rewrite UCOND.
  apply some_none.
  intros.
  rewrite COND.
  apply some_none.
  rewrite EQH; try assumption.
  apply LOCs.
  }
  intros.
  apply OBsOK in IN.
  destruct IN as (l,(oofl,pl)).
  destruct ((location_eq_dec Z.eq_dec) l lv).
  rewrite e in *.
  exists lv, oofl.
  rewrite COND.
  apply some_none.
  exists l, oofl.
  rewrite EQH; assumption.
  }
  exists.
  {
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) l lv).
  rewrite e in *.
  rewrite COND in LOCK.
  destruct LOCK as [CO|CO].
  inversion CO.
  destruct CO as (wt,(ot,CO)).
  destruct CO as [CO|CO];
  inversion CO.
  apply LOCKOK.
  rewrite <- EQH; assumption.
  }
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) l lv).
  rewrite e in *.
  rewrite COND in ULOCK.
  inversion ULOCK.
  apply ULOCKOK with wt ot.
  rewrite <- EQH; assumption.
  }
  intros.
  destruct ((location_eq_dec Z.eq_dec) l lv).
  rewrite e in *.
  rewrite COND in UCOND0.
  inversion UCOND0.
  apply UCONDOK.
  rewrite <- EQH; assumption.
  }
  exists.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) l lv).
  rewrite e in *.
  rewrite COND in ULOCKED.
  destruct ULOCKED as [CO|CO]; inversion CO.
  apply WTsOTsOK.
  rewrite <- EQH; assumption.
  }
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  {
  inversion EQx.
  rewrite <- H1.
  rewrite <- H3.
  rewrite <- H4.
  split.
  trivial.
  split.
  eapply sat_weak_imp1; try assumption.
  apply sat1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  }
  rewrite EQx in INx.
  assert (IN2:=INx).
  apply SOBS in INx.
  destruct INx as (WF1,(SAT1,rest)).
  split. assumption.
  split.

  assert (bp0: boundph p0).
  {
  apply BPE.
  apply in_map_iff.
  exists (c, tx0, p0, O0, C0, id0).
  split. reflexivity. assumption.
  }

  assert (bg0: boundgh C0).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (c, tx0, p0, O0, C0, id0).
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  apply SAT1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  assumption.
Qed.


Lemma g_chrg_preserves_validity0:
  forall m sp h T id tx p O C Cinv Cleak invs wt ot lv ll v
         (INT: In (nop, tx, p, O, C, id) T)
         (eqlv: Aof lv = ([[v]]))
         (eqll: Aof ll = Lof lv)
         (pl: p ll = Some (Locked wt ot))
         (pv: p lv = Some Cond)
         (SAT: sat (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)%nat))))
           (Some (Oof lv::O)) C (weakest_pre_ct (S m) sp (tt, tx) invs))
         (VALID: validk0 (S m) sp T Cinv Cleak h invs),
    validk0 m sp (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll
    (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))), Oof lv::O, C, id)) Cinv Cleak h invs.
Proof.
  intros.
  unfold validk0 in VALID.
  destruct VALID as (locs,(Pinv,(Pleak,(Ainv,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS))))))))))))).
  unfold validk0.
  unfold pheaps_heap in *.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  unfold locations_ok in *.
  destruct LOCsOK as (INJ,(LCOM,(LOCs,OBsOK))).
  unfold invs_ok in *.
  destruct INVsOK as (NDPA,(AinvOK,(INAOK,SATAOK))).
  unfold locks_ok.
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.
  unfold validk0.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  destruct WF as (WF1,WF2).
  exists locs, Pinv, Pleak, Ainv.
  subst.

  assert (INpT: In p (map pof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (phpdefp0il: forall p0 : pheap, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  apply phpdef_pair.
  assumption.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  }

  assert (COND: fold_left phplus (map pof T) (phplus Pinv Pleak) lv = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists p, INpT.
  assumption.
  }
 
  assert (LOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked wt ot)).
  {
  apply fold_locked; repeat php_.
  apply pofs.
  right.
  exists p, INpT.
  assumption.
  }

  assert (NEQlvll: lv <> ll).
  {
  unfold not.
  intros.
  rewrite H in COND.
  rewrite COND in LOCKED.
  inversion LOCKED.
  }

  assert (NEQvlv: ([[v]]) <> Lof lv).
  {
  unfold not.
  intros.
  assert (CO: lv = ll).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  omega.
  }
  contradiction.
  }

  assert (LOCK: fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)%nat))),
    Oof lv::O, C, id))) (phplus Pinv Pleak) ll = Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)%nat))).
  {
  apply locked_disch with p; repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  exists wt, ot.
  assumption.
  }

  assert (EQH: forall l0 (NEQ: ll <> l0), fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)%nat))),
    Oof lv::O, C, id))) (phplus Pinv Pleak) l0 = fold_left phplus (map pof T) (phplus Pinv Pleak) l0).
  {
  intros.
  apply eq_heap_disch with (p:=p) (z:=ll); repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  exists wt, ot.
  assumption.
  eexists.
  eexists.
  reflexivity.
  }

  assert (tmp: Lof ll = Aof ll /\ Pof ll = false /\ Xof ll = None /\
    (h (Aof ll) <> Some 1%Z -> In (Oof ll) (concat (map oof T)))).
  {
  apply LOCKOK.
  right.
  exists wt, ot.
  left.
  assumption.
  }
  destruct tmp as (lll,(plf,(ninrlxll,inlt))).

  assert (p0l: forall p0 id' (NEQ: id <> id') (IN: In (p0,id') (map (fun x => (pof x, snd x)) T)), p0 ll = Some Lock \/ p0 ll = None).
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  assert (PHPDp0: phplusdef p p0).
  {
  apply DEFL with id x6.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  rewrite <- H0.
  auto.
  }

  unfold phplusdef in PHPDp0.
  specialize PHPDp0 with ll.
  rewrite pl in PHPDp0.
  destruct (p0 ll) eqn:p0l.
  destruct k;
  try contradiction.
  left.
  reflexivity.
  right.
  reflexivity.
  }

  assert (phpdefpil: phplusdef p Pinv /\ phplusdef p Pleak).
  {
  apply PHPD.
  assumption.
  }

  assert (pinvl: phplus Pinv Pleak ll = Some Lock \/ phplus Pinv Pleak ll = None).
  {
  assert (PHPDppi: phplusdef p (phplus Pinv Pleak)).
  repeat php_.
  unfold phplusdef in PHPDppi.
  specialize PHPDppi with ll.
  rewrite pl in PHPDppi.
  destruct (phplus Pinv Pleak ll).
  destruct k;
  try contradiction.
  left.
  reflexivity.
  right.
  reflexivity.
  }

  assert (EQWT: forall l0 p O C, filterb (xOf (fun x  => Lof x) locs) (Aof l0) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) =
    filterb (xOf (fun x  => Lof x) locs) (Aof l0)(fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof
    (updl T id (tt, tx, p, O, C, id)))))).
  {
  intros.
  apply filterb_updl_eq.
  intros.
  split.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some v0)).
  inversion e.
  reflexivity.
  intros.
  assert (X': x' = (nop, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  destruct ((opZ_eq_dec None (Some v0))).
  inversion e.
  reflexivity.
  }


  assert (EQO: forall l p (NEQ: l <> ll)
    (fln: fold_left phplus (map pof T) (phplus Pinv Pleak) l <> None),
    filterb (xOf (fun x  => Lof x) locs) (Aof l) (count_occ Z.eq_dec (concat (map Aoof (updl T id
    (tt, tx, p, Oof lv::O, C, id)))))
     = filterb (xOf (fun x  => Lof x) locs) (Aof l) (count_occ Z.eq_dec (concat (map Aoof T)))).
  {
  intros.
  symmetry.
  apply filterb_updl_obs_eq.
  intros.
  assert (X': x' = (nop, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold Aoof.
  simpl.
  destruct (Z.eq_dec (Aofo (Oof lv)) v0).
  assert (lovv: Lof lv = Aof l).
  {
  assert (G: xOf (fun x  => Lof x) locs (Aof lv) = Some (Lof lv)).
  {
  apply xOf_same.
  apply in_map.
  apply LOCs.
  rewrite COND.
  apply some_none.
  apply comp_cons.
  apply LOCs.
  rewrite COND.
  apply some_none.
  unfold comp.
  intros.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  }
  rewrite <- e in IN.
  unfold Aof in G.
  rewrite IN in G.
  inversion G.
  reflexivity.
  }
  assert (l = ll).
  {
  apply INJ.
  assumption.
  rewrite LOCKED.
  apply some_none.
  omega.
  }
  contradiction.

  reflexivity.
  }

  assert (ODEC: count_occ Z.eq_dec (concat (map Aoof T)) ([[v]]) + 1 = count_occ Z.eq_dec (concat
    (map Aoof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)%nat))),
    Oof lv::O, C, id)))) ([[v]])).
  {
  eapply count_updl_incr'.
  assumption.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  split.
  reflexivity.
  assumption.
  unfold Aoof.
  simpl.
  unfold Aof in eqlv.
  rewrite eqlv.
  reflexivity.
  }

  assert (tmp: wt = WTs ll (map cmdof T) locs /\
           ot = OBs ll (concat (map Aoof T)) locs).
  {
  apply WTsOTsOK.
  left.
  assumption.
  }
  destruct tmp as (WT1,OT1).

  assert (FIL1: upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1) =
    filterb (xOf (fun x  => Lof x) locs) (Aof ll)
    (count_occ Z.eq_dec (concat (map Aoof (updl T id
    (tt, tx,  upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))),
    Oof lv::O, C, id)))))).
  {
  apply functional_extensionality.
  intros.
  unfold upd at 1.

  assert (XOF: xOf (fun x0 => Lof x0) locs ([[v]]) = Some (Lof lv)).
  {
  rewrite <- eqlv.
  apply xOf_same.
  apply in_map.
  apply LOCs.
  rewrite COND.
  apply some_none.
  apply comp_cons.
  apply LOCs.
  rewrite COND.
  apply some_none.
  unfold comp.
  intros.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  }

  destruct (Z.eq_dec x ([[v]])).
  rewrite e in *.
  apply eq_trans with (OBs ll (concat (map Aoof T)) locs ([[v]]) + 1).
  rewrite OT1.
  reflexivity.
  unfold OBs.
  unfold filterb.
  rewrite XOF.
  destruct (Z.eq_dec ([[v]]) (Aof ll)).
  omega.
  destruct (Z.eq_dec (Lof lv) (Aof ll)).
  assumption.
  omega.
  apply eq_trans with (OBs ll (concat (map Aoof T)) locs x).
  rewrite OT1.
  reflexivity.
  unfold OBs.
  unfold filterb.
  destruct (xOf (fun x0 => Lof x0) locs x).
  destruct (Z.eq_dec x (Aof ll)).
  reflexivity.
  destruct (Z.eq_dec z (Aof ll)).
  apply count_updl_eq.
  intros.
  assert (X': x' = (nop, tx, p, O, C, id)).
  apply in_elem with T; assumption.
  rewrite X'.
  unfold Aoof.
  simpl.
  destruct (Z.eq_dec (Aofo (Oof lv)) x).
  rewrite <- eqlv in *.
  rewrite <- e0 in n.
  contradiction.
  reflexivity.
  reflexivity.
  reflexivity.
  }

  assert (EQG: map gof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))), Oof lv::O, C, id)) =
    map gof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  assumption.
  assumption.
  }
  inversion EQX.
  reflexivity.
  reflexivity.
  }
  assert (EQGI: map (fun x => (gof x, snd x)) (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll
    (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))), Oof lv::O,C, id)) = map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  assumption.
  assumption.
  }
  inversion EQX.
  reflexivity.
  reflexivity.
  }

  assert (INOB: forall l (IN: In l (concat (map oof T))),
    In l (concat (map oof (updl T id (tt, tx,
    upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))),
    Oof lv::O, C, id))))).
  {
  intros.
  rewrite <- flat_map_concat_map in IN.
  apply in_flat_map in IN.
  destruct IN as (x,(INx,INl0)).
  unfold updl.
  rewrite map_map.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists x.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  }
  inversion EQX.
  unfold oof in *.
  simpl in *.
  split.
  assumption.
  right.
  rewrite <- H3.
  assumption.
  auto.
  }

  assert (INOB': forall l (NEQ: Oof lv <> l) (IN: In l (concat (map oof (updl T id (tt, tx,
    upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))),
    Oof lv::O, C, id))))), In l (concat (map oof T))).
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  rewrite <- flat_map_concat_map in IN.
  apply in_flat_map in IN.
  destruct IN as (x,(INx,INl0)).
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  }
  inversion EQX.
  exists (nop, tx, p, O, C, id).
  split.
  assumption.
  unfold oof in *.
  simpl in *.
  destruct INl0.
  contradiction.
  assumption.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }

  assert (bpupd: boundph (upd (location_eq_dec Z.eq_dec) p ll
    (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))))).
  {
  apply boundph_upd.
  apply BPE.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  rewrite EQG.
  rewrite EQGI.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  assumption.
  }

  exists.
  {
  split.
  {
  intros.
  eapply SPUR1 with (c:=c).
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  destruct (Z.eq_dec (snd y) id).
  unfold cmdof in EQy.
  rewrite <- EQy in WASW.
  inversion WASW.
  apply in_map_iff.
  exists y.
  auto.
  apply WASW.
  }

  intros.
  rewrite EQH in CONDv.
  apply SPUR2 in CONDv.
  destruct CONDv as (a,(b,(c,d))).
  exists a, b.
  exists.
  destruct (location_eq_dec Z.eq_dec ll a).
  right.
  eexists.
  eexists.
  rewrite <- e.
  rewrite LOCK.
  reflexivity.
  rewrite EQH.
  assumption.
  assumption.
  assumption.
  unfold not.
  intros CO.
  rewrite <- CO in CONDv.
  rewrite LOCK in CONDv.
  inversion CONDv.
  }

  exists.
  {
  split.
  {
  unfold defl.
  intros.
  unfold updl in IN1.
  rewrite map_map in IN1.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  destruct x1 as (((((a1,a2),a3),a4),a5),a6).
  simpl in EQ1.
  unfold updl in IN2.
  rewrite map_map in IN2.
  apply in_map_iff in IN2.
  destruct IN2 as (x2,(EQ2,IN2)).
  destruct x2 as (((((y1,y2),y3),y4),y5),y6).
  simpl in EQ2.
  destruct (Z.eq_dec a6 id).
  rewrite e in *.
  unfold pof in EQ1.
  simpl in EQ1.
  inversion EQ1.
  destruct (Z.eq_dec y6 id).
  rewrite e0 in *.
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  omega.
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  apply phpdef_upd_locked.
  apply DEFL with id y6.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  rewrite <- H2.
  auto.
  apply p0l with y6.
  omega.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  rewrite <- H2.
  auto.
  unfold pof in EQ1.
  simpl in EQ1.
  inversion EQ1.
  destruct (Z.eq_dec y6 id).
  rewrite e in *.
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  apply phpdef_comm.
  apply phpdef_upd_locked.
  apply DEFL with id a6.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (a1, a2, a3, a4, a5, a6).
  rewrite <- H0.
  auto.
  apply p0l with a6.
  omega.
  apply in_map_iff.
  exists (a1, a2, a3, a4, a5, a6).
  rewrite <- H0.
  auto.
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  apply DEFL with a6 y6.
  omega.
  apply in_map_iff.
  exists (a1, a2, a3, a4, a5, a6).
  rewrite <- H0.
  auto.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  rewrite <- H2.
  auto.
  }

  exists. assumption.
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  rewrite <- EQ.
  apply phpdef_dist'.
  apply phpdef_upd_locked.
  repeat php_.
  assumption.
  assumption.
  simpl in EQ.
  rewrite <- EQ.
  apply PHPD.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  rewrite <- EQ.
  assumption.
  simpl in EQ.
  rewrite <- EQ.
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists.
  {
  apply boundph_disch with (p:=p) (z:=ll); repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  exists wt, ot.
  assumption.
  exists wt.
  eexists.
  reflexivity.
  }
  assert (PH:=PH2H).
  unfold phtoh in *.
  destruct PH as (PH1,PH2).
  split.
  {
  intros.
  specialize PH1 with l.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.

  rewrite LOCK.
  rewrite LOCKED in PH1.
  assumption.
  rewrite EQH.
  assumption.
  assumption.
  }
  intros.
  apply PH2.
  intros.
  apply NONE in EQ.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite LOCK in EQ.
  inversion EQ.
  rewrite <- EQH.
  assumption.
  assumption.
  }
  exists.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
  exists.
  {
  apply NoDup_updl.
  assumption.
  }
  exists.
  {
  split. assumption.
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  apply AinvOK in IN.
  destruct IN as (CO,tmp).
  rewrite LOCKED in CO.
  inversion CO.
  rewrite EQH.
  apply AinvOK.
  assumption.
  assumption.
  }
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) l ll).
  rewrite e in *.
  rewrite LOCK in LOCK0.
  inversion LOCK0.
  rewrite EQH in LOCK0.
  apply INAOK in LOCK0.
  rewrite <- EQWT.
  rewrite EQO.
  assumption.
  assumption.
  assert (tmp: In l (map snd Ainv)).
  {
  apply in_map_iff.
  exists (subsas (snd (Iof l))
             (invs (fst (Iof l)) (WTs l (map cmdof T) locs)
                (OBs l (concat (map Aoof T)) locs)), l).
  auto.
  }
  apply AinvOK in tmp.
  destruct tmp as (tmp1,tmp2).
  rewrite tmp1.
  apply some_none.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  }
  assumption.
  }
  exists.
  {
  split.
  {
  assert (G: forall x, fold_left phplus (map pof (updl T id
    (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))),
    Oof lv::O, C, id))) (phplus Pinv Pleak) x <> None ->
    fold_left phplus (map pof T) (phplus Pinv Pleak) x <> None).
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll x).
  rewrite <- e.
  rewrite LOCKED.
  apply some_none.
  rewrite <- EQH.
  assumption.
  assumption.
  }
  unfold injph.
  intros.
  apply INJ.
  apply G.
  assumption.
  apply G.
  assumption.
  }
  split. assumption.
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e.
  split.
  intros.
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  intros.
  rewrite LOCK.
  apply some_none.
  rewrite EQH.
  apply LOCs.
  assumption.
  }
  intros.
  destruct ((olocation_eq_dec Z.eq_dec) (Oof lv) o).
  exists lv, e.
  rewrite EQH.
  rewrite COND.
  apply some_none.
  unfold not.
  intros.
  rewrite H in NEQlvll.
  contradiction.
  apply INOB' in IN.
  apply OBsOK in IN.
  destruct IN as (l',(EQl',pl')).
  exists l', EQl'.
  destruct (location_eq_dec Z.eq_dec ll l').
  rewrite <- e.
  rewrite LOCK.
  apply some_none.
  rewrite EQH.
  assumption.
  assumption.
  assumption.
  }
  exists.
  {
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  split. assumption.
  split. assumption.
  split. assumption.
  intros.
  apply inlt in H.
  apply INOB.
  assumption.

  rewrite EQH in LOCK0.
  assert (LOCK':=LOCK0).
  apply LOCKOK in LOCK0.
  destruct LOCK0 as (L1,(L2,(L3,L4))).
  split. assumption.
  split. assumption.
  split. assumption.
  intros.
  apply L4 in H.
  apply INOB.
  assumption.
  assumption.
  }
  split.
  {
  intros.
  assert (ULOCK0:=ULOCK).
  destruct ((location_eq_dec Z.eq_dec) lv l).
  rewrite <- e in *.
  rewrite EQH in ULOCK.
  rewrite COND in ULOCK.
  inversion ULOCK.
  unfold not.
  intros.
  rewrite H in NEQlvll.
  contradiction.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite LOCK in ULOCK.
  inversion ULOCK.
  rewrite EQH in ULOCK.
  apply ULOCKOK in ULOCK.
  destruct ULOCK as (U1,U2).
  split. assumption.
  unfold not.
  intros.
  apply U2.
  apply INOB'.
  unfold not.
  intros.
  assert (COlvl: lv = l).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  rewrite <- EQH.
  rewrite ULOCK0.
  apply some_none.
  assumption.
  unfold Aof.
  rewrite H0.
  reflexivity.
  }
  contradiction.
  assumption.
  assumption.
  }
  intros.
  assert (ULOCK0:=UCOND).
  destruct ((location_eq_dec Z.eq_dec) lv l).
  rewrite <- e in *.
  rewrite EQH in UCOND.
  rewrite COND in UCOND.
  inversion UCOND.
  unfold not.
  intros.
  rewrite H in NEQlvll.
  contradiction.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite LOCK in UCOND.
  inversion UCOND.
  rewrite EQH in UCOND.
  apply UCONDOK in UCOND.
  unfold not.
  intros.
  apply UCOND.
  apply INOB'.
  unfold not.
  intros.
  assert (CO: lv = l).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  rewrite <- EQH.
  rewrite ULOCK0.
  apply some_none.
  assumption.
  unfold Aof.
  rewrite H0.
  reflexivity.
  }
  contradiction.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  rewrite <- EQWT.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite LOCK in ULOCKED.
  destruct ULOCKED as [U1|U1].
  {
  inversion U1.
  rewrite <- H0.
  split.
  rewrite WT1.
  reflexivity.
  assumption.
  }
  inversion U1.
  rewrite EQO.
  apply WTsOTsOK.
  rewrite <- EQH.
  assumption.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  rewrite <- EQH.
  destruct ULOCKED as [U|U];
  rewrite U;
  apply some_none.
  assumption.
  }

  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  {
(* ==================== x6 = id ===========*)
  simpl in EQ.
  symmetry in EQ.
  inversion EQ.
  split.
  unfold wellformed.
  auto.
  exists.
  assert (bg: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  apply SAT.
  intros.
  eapply sat_tx_weak_imp1; try assumption.

  intros.
  inversion W4COND.
  }
(* ==================== x6 <> id ===========*)
  symmetry in EQ.
  inversion EQ.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF3,(WP3,VOBS3)).
  exists. assumption.
  exists.
  assert (bx3: boundph x3).
  {
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  split. reflexivity. assumption.
  }

  assert (bx5: boundgh x5).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=(ghplus Cinv Cleak)); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  apply WP3.
  intros.
  eapply sat_tx_weak_imp1; try assumption.

  intros.
  rewrite W4COND in WP3.
  apply sat_wait4cond in WP3.
  destruct WP3 as (l0,(v0,(eql0,(eqv,(p'v,(p'l0,(lofl0,(prcv0,(prcv,SAT2))))))))).

  assert (COND': fold_left phplus (map pof T) (phplus Pinv Pleak) v0 = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }

  assert (LOCK': fold_left phplus (map pof T) (phplus Pinv Pleak) l0 = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) l0 = Some (Locked wt ot)).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  right.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }

  apply VOBS3 in W4COND.
  destruct W4COND as (v',(l',(inv',(inl',(eqv',(eql',sobs')))))).
  exists v', l', inv', inl', eqv', eql'.
  rewrite <- EQWT.

  assert (EQv'v0: v' = v0).
  {
  apply INJ.
  apply LOCs.
  assumption.
  rewrite COND'.
  apply some_none.
  omega.
  }

  assert (EQl'l0: l' = l0).
  {
  apply INJ.
  apply LOCs.
  assumption.
  destruct LOCK' as [L|L].
  rewrite L.
  apply some_none.
  destruct L as (wt',(ot',L)).
  rewrite L.
  apply some_none.
  omega.
  }

  destruct ((location_eq_dec Z.eq_dec) l' ll).
  rewrite e in *.
  {
  rewrite <- FIL1.
  unfold WTs in WT1.
  unfold upd.
  destruct (Z.eq_dec ([[ev]]) ([[v]])).
  rewrite e0 in *.
  assert (EQv'lv: v' = lv).
  {
  rewrite EQv'v0.
  apply INJ.
  rewrite COND'.
  apply some_none.
  rewrite COND.
  apply some_none.
  omega.
  }
  rewrite EQv'lv in *.
  rewrite <- WT1.
  assert (G: safe_obs lv (wt ([[v]])) (ot ([[v]])) = true).
  {
  unfold WTs in *.
  unfold OBs in *.
  rewrite <- WT1 in sobs'.
  rewrite <- OT1 in sobs'.
  assumption.
  }
  apply safe_obs_ot_weak with (ot ([[v]])).
  omega.
  assumption.
  unfold WTs, OBs in *.
  rewrite OT1.
  assumption.
  }

  rewrite EQO.
  assumption.
  assumption.
  rewrite EQl'l0.
  destruct LOCK' as [L|L].
  rewrite L.
  apply some_none.
  destruct L as (wt',(ot',L)).
  rewrite L.
  apply some_none.
Qed.


Lemma g_chrgu_preserves_validity0:
  forall m sp h T id tx p O C Cinv Cleak invs wt ot lv ll v
         (INT: In (nop, tx, p, O, C, id) T)
         (eqlv: Aof lv = ([[v]]))
         (eqll: Aof ll = Lof lv)
         (pl: p ll = Some (Ulock wt ot))
         (pv: p lv = Some Icond)
         (SAT: sat (upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)%nat))))
           (Some (Oof lv::O)) C (weakest_pre_ct (S m) sp (tt, tx) invs))
         (VALID: validk0 (S m) sp T Cinv Cleak h invs),
    validk0 m sp (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll
    (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))), Oof lv::O, C, id)) Cinv Cleak h invs.
Proof.
  intros.
  unfold validk0 in VALID.
  destruct VALID as (locs,(Pinv,(Pleak,(Ainv,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS))))))))))))).
  unfold validk0.
  unfold pheaps_heap in *.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  unfold locations_ok in *.
  destruct LOCsOK as (INJ,(LCOM,(LOCs,OBsOK))).
  unfold invs_ok in *.
  destruct INVsOK as (NDPA,(AinvOK,(INAOK,SATAOK))).
  unfold locks_ok.
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.
  unfold validk0.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  destruct WF as (WF1,WF2).

  exists locs, Pinv, Pleak, Ainv.

  subst.

  assert (INpT: In p (map pof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (phpdefp0il: forall p0 : pheap, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  apply phpdef_pair.
  assumption.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  }

  assert (p0zn: forall p0 id0 (NEQ: id <> id0)
    (IN: In (p0, id0) (map (fun x => (pof x, snd x)) T)),
    p0 ll = None).
  {
  intros.
  assert (pd: phplusdef p0 p).
  {
  apply DEFL with id0 id.
  omega.
  assumption.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }
  unfold phplusdef in pd.
  specialize pd with ll.
  rewrite pl in pd.
  destruct (p0 ll).
  destruct k; contradiction.
  reflexivity.
  }

  assert (pilll: phplus Pinv Pleak ll = None).
  {
  assert (pd: phplusdef p (phplus Pinv Pleak)).
  {
  apply phpdef_pair.
  assumption.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  }
  unfold phplusdef in pd.
  specialize pd with ll.
  rewrite pl in pd.
  destruct (phplus Pinv Pleak ll).
  destruct k; contradiction.
  reflexivity.
  }

  assert (COND: fold_left phplus (map pof T) (phplus Pinv Pleak) lv = Some Icond).
  {
  apply fold_icond; repeat php_.
  apply pofs.
  right.
  exists p, INpT.

  assumption.
  }
 
  assert (LOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Ulock wt ot)).
  {
  apply fold_ulock; repeat php_.
  apply pofs.
  right.
  exists p, INpT.
  assumption.
  }

  assert (NEQlvll: lv <> ll).
  {
  unfold not.
  intros.
  rewrite H in COND.
  rewrite COND in LOCKED.
  inversion LOCKED.
  }

  assert (NEQvlv: ([[v]]) <> Lof lv).
  {
  unfold not.
  intros.
  assert (CO: lv = ll).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  omega.
  }
  contradiction.
  }

  assert (LOCK: fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)%nat))),
    Oof lv::O, C, id))) (phplus Pinv Pleak) ll = Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)%nat))).
  {
  apply ulock_dischu with p; repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  exists wt, ot.

  assumption.
  }

  assert (EQH: forall l0 (NEQ: ll <> l0), fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)%nat))),
    Oof lv::O, C, id))) (phplus Pinv Pleak) l0 = fold_left phplus (map pof T) (phplus Pinv Pleak) l0).
  {
  intros.
  apply eq_heap_dischu with (p:=p) (z:=ll); repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  exists wt, ot.

  assumption.
  eexists.
  eexists.
  reflexivity.
  }

  assert (tmp: Lof ll = Aof ll /\ Pof ll = false /\ Xof ll = None /\
    (h (Aof ll) <> Some 1%Z -> In (Oof ll) (concat (map oof T)))).
  {
  apply LOCKOK.
  right.
  exists wt, ot.
  right.
  assumption.
  }
  destruct tmp as (lll,(plf,(ninrlxll,inlt))).

  assert (p0l: forall p0 id' (NEQ: id <> id') (IN: In (p0,id') (map (fun x => (pof x, snd x)) T)), p0 ll = Some Lock \/ p0 ll = None).
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  assert (PHPDp0: phplusdef p p0).
  {
  apply DEFL with id x6.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  rewrite <- H0.
  auto.
  }

  unfold phplusdef in PHPDp0.
  specialize PHPDp0 with ll.
  rewrite pl in PHPDp0.
  destruct (p0 ll) eqn:p0l.
  destruct k;
  try contradiction.
  right.
  reflexivity.
  }

  assert (phpdefpil: phplusdef p Pinv /\ phplusdef p Pleak).
  {
  apply PHPD.
  assumption.
  }

  assert (pinvl: phplus Pinv Pleak ll = Some Lock \/ phplus Pinv Pleak ll = None).
  {
  assert (PHPDppi: phplusdef p (phplus Pinv Pleak)).
  repeat php_.
  unfold phplusdef in PHPDppi.
  specialize PHPDppi with ll.
  rewrite pl in PHPDppi.
  destruct (phplus Pinv Pleak ll).
  destruct k;
  try contradiction.
  right.
  reflexivity.
  }

  assert (EQWT: forall l0 p O C, filterb (xOf (fun x  => Lof x) locs) (Aof l0) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) =
    filterb (xOf (fun x  => Lof x) locs) (Aof l0)(fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof
    (updl T id (tt, tx, p, O, C, id)))))).
  {
  intros.
  apply filterb_updl_eq.
  intros.
  split.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some v0)).
  inversion e.
  reflexivity.
  intros.
  assert (X': x' = (nop, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  destruct ((opZ_eq_dec None (Some v0))).
  inversion e.
  reflexivity.
  }


  assert (EQO: forall l p (NEQ: l <> ll)
    (fln: fold_left phplus (map pof T) (phplus Pinv Pleak) l <> None),
    filterb (xOf (fun x  => Lof x) locs) (Aof l) (count_occ Z.eq_dec (concat (map Aoof (updl T id
    (tt, tx, p, Oof lv::O, C, id)))))
     = filterb (xOf (fun x  => Lof x) locs) (Aof l) (count_occ Z.eq_dec (concat (map Aoof T)))).
  {
  intros.
  symmetry.
  apply filterb_updl_obs_eq.
  intros.
  assert (X': x' = (nop, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold Aoof.
  simpl.
  destruct (Z.eq_dec (Aofo (Oof lv)) v0).
  assert (lovv: Lof lv = Aof l).
  {
  assert (G: xOf (fun x  => Lof x) locs (Aof lv) = Some (Lof lv)).
  {
  apply xOf_same.
  apply in_map.
  apply LOCs.
  rewrite COND.
  apply some_none.
  apply comp_cons.
  apply LOCs.
  rewrite COND.
  apply some_none.
  unfold comp.
  intros.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  }
  rewrite <- e in IN.
  unfold Aof in G.
  rewrite IN in G.
  inversion G.
  reflexivity.
  }
  assert (l = ll).
  {
  apply INJ.
  assumption.
  rewrite LOCKED.
  apply some_none.
  omega.
  }
  contradiction.
  reflexivity.
  }

  assert (ODEC: count_occ Z.eq_dec (concat (map Aoof T)) ([[v]]) + 1 = count_occ Z.eq_dec (concat
    (map Aoof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)%nat))),
    Oof lv::O, C, id)))) ([[v]])).
  {
  eapply count_updl_incr'.
  assumption.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  split.
  reflexivity.
  assumption.
  unfold Aoof.
  simpl.
  unfold Aof in eqlv.
  rewrite eqlv.
  reflexivity.
  }

  assert (tmp: wt = WTs ll (map cmdof T) locs /\
           ot = OBs ll (concat (map Aoof T)) locs).
  {
  apply WTsOTsOK.
  right.
  assumption.
  }
  destruct tmp as (WT1,OT1).

  assert (FIL1: upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1) =
    filterb (xOf (fun x  => Lof x) locs) (Aof ll)
    (count_occ Z.eq_dec (concat (map Aoof (updl T id
    (tt, tx,  upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))),
    Oof lv::O, C, id)))))).
  {
  apply functional_extensionality.
  intros.
  unfold upd at 1.

  assert (XOF: xOf (fun x0 => Lof x0) locs ([[v]]) = Some (Lof lv)).
  {
  rewrite <- eqlv.
  apply xOf_same.
  apply in_map.
  apply LOCs.
  rewrite COND.
  apply some_none.
  apply comp_cons.
  apply LOCs.
  rewrite COND.
  apply some_none.
  unfold comp.
  intros.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  }

  destruct (Z.eq_dec x ([[v]])).
  rewrite e in *.
  apply eq_trans with (OBs ll (concat (map Aoof T)) locs ([[v]]) + 1).
  rewrite OT1.
  reflexivity.
  unfold OBs.
  unfold filterb.
  rewrite XOF.
  destruct (Z.eq_dec ([[v]]) (Aof ll)).
  omega.
  destruct (Z.eq_dec (Lof lv) (Aof ll)).
  assumption.
  omega.
  apply eq_trans with (OBs ll (concat (map Aoof T)) locs x).
  rewrite OT1.
  reflexivity.
  unfold OBs.
  unfold filterb.
  destruct (xOf (fun x0 => Lof x0) locs x).
  destruct (Z.eq_dec x (Aof ll)).
  reflexivity.
  destruct (Z.eq_dec z (Aof ll)).
  apply count_updl_eq.
  intros.
  assert (X': x' = (nop, tx, p, O, C, id)).
  apply in_elem with T; assumption.
  rewrite X'.
  unfold Aoof.
  simpl.
  destruct (Z.eq_dec (Aofo (Oof lv)) x).
  rewrite <- e0 in n.
  rewrite <- eqlv in *.
  contradiction.
  reflexivity.
  reflexivity.
  reflexivity.
  }

  assert (EQG: map gof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))), Oof lv::O, C, id)) =
    map gof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  assumption.
  assumption.
  }
  inversion EQX.
  reflexivity.
  reflexivity.
  }
  assert (EQGI: map (fun x => (gof x, snd x)) (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll
    (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))), Oof lv::O,C, id)) = map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  assumption.
  assumption.
  }
  inversion EQX.
  reflexivity.
  reflexivity.
  }

  assert (INOB: forall l (IN: In l (concat (map oof T))),
    In l (concat (map oof (updl T id (tt, tx,
    upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))),
    Oof lv::O, C, id))))).
  {
  intros.
  rewrite <- flat_map_concat_map in IN.
  apply in_flat_map in IN.
  destruct IN as (x,(INx,INl0)).
  unfold updl.
  rewrite map_map.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists x.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  }
  inversion EQX.
  unfold oof in *.
  simpl in *.
  split.
  assumption.
  right.
  rewrite <- H3.
  assumption.
  auto.
  }

  assert (INOB': forall l (NEQ: Oof lv <> l) (IN: In l (concat (map oof (updl T id (tt, tx,
    upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))),
    Oof lv::O, C, id))))), In l (concat (map oof T))).
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  rewrite <- flat_map_concat_map in IN.
  apply in_flat_map in IN.
  destruct IN as (x,(INx,INl0)).
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  }
  inversion EQX.
  exists (nop, tx, p, O, C, id).
  split.
  assumption.
  unfold oof in *.
  simpl in *.
  destruct INl0.
  contradiction.
  assumption.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }

  assert (bpupd: boundph (upd (location_eq_dec Z.eq_dec) p ll
    (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))))).
  {
  apply boundph_upd.
  apply BPE.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bg: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  split. reflexivity. assumption.
  }
  rewrite EQG.
  rewrite EQGI.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  assumption.
  }

  exists.
  {
  split.
  {
  intros.
  eapply SPUR1 with (c:=c).
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  destruct (Z.eq_dec (snd y) id).
  unfold cmdof in EQy.
  rewrite <- EQy in WASW.
  inversion WASW.
  apply in_map_iff.
  exists y.
  auto.
  apply WASW.
  }
  intros.
  rewrite EQH in CONDv.
  apply SPUR2 in CONDv.
  destruct CONDv as (a,(b,(c,d))).
  exists a, b.
  exists.
  destruct (location_eq_dec Z.eq_dec ll a).
  rewrite <- e in *.
  rewrite LOCKED in c.
  destruct c as [c|c].
  inversion c.
  destruct c as (wt',(ot',c)).
  inversion c.
  rewrite EQH.
  assumption.
  assumption.
  assumption.
  unfold not.
  intros CO.
  rewrite <- CO in CONDv.
  rewrite LOCK in CONDv.
  inversion CONDv.
  }
  exists.
  {
  split.
  {
  unfold defl.
  intros.
  unfold updl in IN1.
  rewrite map_map in IN1.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  destruct x1 as (((((a1,a2),a3),a4),a5),a6).
  simpl in EQ1.
  unfold updl in IN2.
  rewrite map_map in IN2.
  apply in_map_iff in IN2.
  destruct IN2 as (x2,(EQ2,IN2)).
  destruct x2 as (((((y1,y2),y3),y4),y5),y6).
  simpl in EQ2.
  destruct (Z.eq_dec a6 id).
  rewrite e in *.
  unfold pof in EQ1.
  simpl in EQ1.
  inversion EQ1.
  destruct (Z.eq_dec y6 id).
  rewrite e0 in *.
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  omega.
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  apply phpdef_ulock.
  apply DEFL with id y6.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  rewrite <- H2.
  auto.
  apply p0zn with id2; try assumption.
  omega.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  rewrite <- H2.
  rewrite <- H3.
  auto.
  unfold pof in EQ1.
  simpl in EQ1.
  inversion EQ1.
  destruct (Z.eq_dec y6 id).
  rewrite e in *.
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  apply phpdef_comm.
  apply phpdef_ulock.
  apply DEFL with id a6.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (a1, a2, a3, a4, a5, a6).
  rewrite <- H0.
  auto.
  apply p0zn with id1; try assumption.
  omega.
  apply in_map_iff.
  exists (a1, a2, a3, a4, a5, a6).
  rewrite <- H0.
  rewrite <- H1.
  auto.
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  apply DEFL with a6 y6.
  omega.
  apply in_map_iff.
  exists (a1, a2, a3, a4, a5, a6).
  rewrite <- H0.
  auto.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  rewrite <- H2.
  auto.
  }

  exists. assumption.
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  rewrite <- EQ.
  apply phpdef_dist'.
  apply phpdef_ulock.
  repeat php_.
  assumption.
  assumption.
  simpl in EQ.
  rewrite <- EQ.
  apply PHPD.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  rewrite <- EQ.
  assumption.
  simpl in EQ.
  rewrite <- EQ.
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists.
  {
  apply boundph_dischu with (p:=p) (z:=ll); repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  exists wt, ot.
  assumption.
  exists wt.
  eexists.
  reflexivity.
  }
  assert (PH:=PH2H).
  unfold phtoh in *.
  destruct PH as (PH1,PH2).
  split.
  {
  intros.
  specialize PH1 with l.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.

  rewrite LOCK.
  rewrite LOCKED in PH1.
  assumption.
  rewrite EQH.
  assumption.
  assumption.
  }
  intros.
  apply PH2.
  intros.
  apply NONE in EQ.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite LOCK in EQ.
  inversion EQ.
  rewrite <- EQH.
  assumption.
  assumption.
  }
  exists.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
  exists.
  {
  apply NoDup_updl.
  assumption.
  }
  exists.
  {
  split. assumption.
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  apply AinvOK in IN.
  destruct IN as (CO,tmp).
  rewrite LOCKED in CO.
  inversion CO.
  rewrite EQH.
  apply AinvOK.
  assumption.
  assumption.
  }
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) l ll).
  rewrite e in *.
  rewrite LOCK in LOCK0.
  inversion LOCK0.
  rewrite EQH in LOCK0.
  apply INAOK in LOCK0.
  rewrite <- EQWT.
  rewrite EQO.
  assumption.
  assumption.
  assert (tmp: In l (map snd Ainv)).
  {
  apply in_map_iff.
  exists (subsas (snd (Iof l))
             (invs (fst (Iof l)) (WTs l (map cmdof T) locs)
                (OBs l (concat (map Aoof T)) locs)), l).
  auto.
  }
  apply AinvOK in tmp.
  destruct tmp as (tmp1,tmp2).
  rewrite tmp1.
  apply some_none.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  }
  assumption.
  }
  exists.
  {
  split.
  {
  assert (G: forall x, fold_left phplus (map pof (updl T id
    (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))),
    Oof lv::O, C, id))) (phplus Pinv Pleak) x <> None ->
    fold_left phplus (map pof T) (phplus Pinv Pleak) x <> None).
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll x).
  rewrite <- e.
  rewrite LOCKED.
  apply some_none.
  rewrite <- EQH.
  assumption.
  assumption.
  }
  unfold injph.
  intros.
  apply INJ.
  apply G.
  assumption.
  apply G.
  assumption.
  }
  split. assumption.
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e.
  split.
  intros.
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  intros.
  rewrite LOCK.
  apply some_none.
  rewrite EQH.
  apply LOCs.
  assumption.
  }
  intros.
  destruct ((olocation_eq_dec Z.eq_dec) (Oof lv) o).
  exists lv, e.
  rewrite EQH.
  rewrite COND.
  apply some_none.
  unfold not.
  intros.
  rewrite H in NEQlvll.
  contradiction.
  apply INOB' in IN.
  apply OBsOK in IN.
  destruct IN as (l',(EQl',pl')).
  exists l', EQl'.
  destruct ((location_eq_dec Z.eq_dec) ll l').
  rewrite <- e.
  rewrite LOCK.
  apply some_none.
  rewrite EQH.
  assumption.
  assumption.
  assumption.
  }
  exists.
  {
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  split. assumption.
  split. assumption.
  split. assumption.
  intros.
  apply inlt in H.
  apply INOB.
  assumption.

  rewrite EQH in LOCK0.
  assert (LOCK':=LOCK0).
  apply LOCKOK in LOCK0.
  destruct LOCK0 as (L1,(L2,(L3,L4))).
  split. assumption.
  split. assumption.
  split. assumption.
  intros.
  apply L4 in H.
  apply INOB.
  assumption.
  assumption.
  }
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) lv l).
  {
  rewrite <- e in *.
  rewrite EQH in ULOCK.
  rewrite COND in ULOCK.
  inversion ULOCK.
  unfold not.
  intros.
  rewrite H in NEQlvll.
  contradiction.
  }
  destruct ((location_eq_dec Z.eq_dec) ll l).
  {
  rewrite <- e in *.
  rewrite LOCK in ULOCK.
  inversion ULOCK.
  assert (L0:=LOCKED).
  apply ULOCKOK in LOCKED.
  destruct LOCKED as (L1,L2).
  split. assumption.
  unfold not.
  intros.
  apply L2.
  apply INOB'.
  unfold not.
  intros.
  assert (CO: lv = ll).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  rewrite L0.
  apply some_none.
  unfold Aof.
  rewrite H2.
  reflexivity.
  }
  contradiction.
  rewrite H0.
  assumption.
  }
  rewrite EQH in ULOCK.
  assert (U0:=ULOCK).
  apply ULOCKOK in ULOCK.
  destruct ULOCK as (U1,U2).
  split.
  assumption.
  unfold not.
  intros.
  apply U2.
  apply INOB'.
  unfold not.
  intros.
  assert (CO: lv = l).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  rewrite U0.
  apply some_none.
  unfold Aof.
  rewrite H0.
  reflexivity.
  }
  contradiction.
  assumption.
  assumption.
  }
  intros.
  destruct ((location_eq_dec Z.eq_dec) lv l).
  rewrite <- e in *.
  rewrite EQH in UCOND.
  rewrite COND in UCOND.
  inversion UCOND.
  unfold not.
  intros.
  rewrite H in NEQlvll.
  contradiction.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite LOCK in UCOND.
  inversion UCOND.
  rewrite EQH in UCOND.
  assert (U0:=UCOND).
  apply UCONDOK in UCOND.
  unfold not.
  intros.
  apply UCOND.
  apply INOB'.
  unfold not.
  intros.
  assert (CO: lv = l).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  rewrite U0.
  apply some_none.
  unfold Aof.
  rewrite H0.
  reflexivity.
  }
  contradiction.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  rewrite <- EQWT.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite LOCK in ULOCKED.
  destruct ULOCKED as [U1|U1].
  inversion U1.
  {
  inversion U1.
  rewrite <- H0.
  split.
  rewrite WT1.
  reflexivity.
  assumption.
  }
  rewrite EQO.
  apply WTsOTsOK.
  rewrite <- EQH.
  assumption.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  rewrite <- EQH.
  destruct ULOCKED as [U|U];
  rewrite U;
  apply some_none.
  assumption.
  }

  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  {
(* ==================== x6 = id ===========*)
  simpl in EQ.
  symmetry in EQ.
  inversion EQ.
  split.
  unfold wellformed.
  auto.
  exists.
  eapply sat_weak_imp1; try assumption.
  apply SAT.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  }
(* ==================== x6 <> id ===========*)
  symmetry in EQ.
  inversion EQ.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF3,(WP3,VOBS3)).
  exists. assumption.
  exists.

  assert (bx3: boundph x3).
  {
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  split. reflexivity. assumption.
  }

  assert (bx5: boundgh x5).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=(ghplus Cinv Cleak)); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  split. reflexivity. assumption.
  }

  eapply sat_weak_imp1; try assumption.
  apply WP3.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  rewrite W4COND in WP3.
  apply sat_wait4cond in WP3.
  destruct WP3 as (l0,(v0,(eql0,(eqv,(p'v,(p'l0,(lofl0,(prcv0,(prcv,SAT2))))))))).

  assert (COND': fold_left phplus (map pof T) (phplus Pinv Pleak) v0 = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }

  assert (LOCK': fold_left phplus (map pof T) (phplus Pinv Pleak) l0 = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) l0 = Some (Locked wt ot)).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  right.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }

  apply VOBS3 in W4COND.
  destruct W4COND as (v',(l',(inv',(inl',(eqv',(eql',sobs')))))).
  exists v', l', inv', inl', eqv', eql'.
  rewrite <- EQWT.

  assert (EQv'v0: v' = v0).
  {
  apply INJ.
  apply LOCs.
  assumption.
  rewrite COND'.
  apply some_none.
  omega.
  }

  assert (EQl'l0: l' = l0).
  {
  apply INJ.
  apply LOCs.
  assumption.
  destruct LOCK' as [L|L].
  rewrite L.
  apply some_none.
  destruct L as (wt',(ot',L)).
  rewrite L.
  apply some_none.
  omega.
  }

  destruct ((location_eq_dec Z.eq_dec) l' ll).
  rewrite e in *.
  {
  rewrite <- FIL1.
  unfold WTs in WT1.
  unfold upd.
  destruct (Z.eq_dec ([[ev]]) ([[v]])).
  rewrite e0 in *.
  assert (EQv'lv: v' = lv).
  {
  rewrite EQv'v0.
  apply INJ.
  rewrite COND'.
  apply some_none.
  rewrite COND.
  apply some_none.
  omega.
  }
  rewrite EQv'lv in *.
  rewrite <- WT1.
  assert (G: safe_obs lv (wt ([[v]])) (ot ([[v]])) = true).
  {
  unfold WTs in *.
  unfold OBs in *.
  rewrite <- WT1 in sobs'.
  rewrite <- OT1 in sobs'.
  assumption.
  }
  apply safe_obs_ot_weak with (ot ([[v]])).
  omega.
  assumption.
  unfold WTs, OBs in *.
  rewrite OT1.
  assumption.
  }

  rewrite EQO.
  assumption.
  assumption.
  rewrite EQl'l0.
  destruct LOCK' as [L|L].
  rewrite L.
  apply some_none.
  destruct L as (wt',(ot',L)).
  rewrite L.
  apply some_none.
Qed.


Lemma g_disch_preserves_validity0:
  forall m sp h T id tx p O C Cinv Cleak invs wt ot O1 lv ll v
         (INT: In (nop, tx, p, O, C, id) T)
         (O1eq: Permutation O (Oof lv::O1))
         (eqlv: Aof lv = ([[v]]))
         (eqll: Aof ll = Lof lv)
         (pl: p ll = Some (Locked wt ot))
         (pv: p lv = Some Cond)
         (INO: In (Oof lv) O)
         (SAFE: safe_obs lv (wt ([[v]])) ((ot ([[v]])) - 1) = true)
         (SAT: sat (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)%nat))))
           (Some O1) C (weakest_pre_ct (S m) sp (tt, tx) invs))
         (VALID: validk0 (S m) sp T Cinv Cleak h invs),
    validk0 m sp (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll
    (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))), O1, C, id)) Cinv Cleak h invs.
Proof.
  intros.
  unfold validk0 in VALID.
  destruct VALID as (locs,(Pinv,(Pleak,(Ainv,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS))))))))))))).
  unfold validk0.
  unfold pheaps_heap in *.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  unfold locations_ok in *.
  destruct LOCsOK as (INJ,(LCOM,(LOCs,OBsOK))).
  unfold invs_ok in *.
  destruct INVsOK as (NDPA,(AinvOK,(INAOK,SATAOK))).
  unfold locks_ok.
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.
  unfold validk0.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  destruct WF as (WF1,WF2).

  exists locs, Pinv, Pleak, Ainv.
  subst.

  assert (INpT: In p (map pof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (phpdefp0il: forall p0 : pheap, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  apply phpdef_pair.
  assumption.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  }

  assert (COND: fold_left phplus (map pof T) (phplus Pinv Pleak) lv = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists p, INpT.
  assumption.
  }
 
  assert (LOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked wt ot)).
  {
  apply fold_locked; repeat php_.
  apply pofs.
  right.
  exists p, INpT.
  assumption.
  }

  assert (NEQlvll: lv <> ll).
  {
  unfold not.
  intros.
  rewrite H in COND.
  rewrite COND in LOCKED.
  inversion LOCKED.
  }

  assert (NEQvlv: ([[v]]) <> Lof lv).
  {
  unfold not.
  intros.
  assert (CO: lv = ll).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  omega.
  }
  contradiction.
  }

  assert (LOCK: fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)%nat))),
    O1, C, id))) (phplus Pinv Pleak) ll = Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)%nat))).
  {
  apply locked_disch with p; repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  exists wt, ot.
  assumption.
  }

  assert (EQH: forall l0 (NEQ: ll <> l0), fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)%nat))),
    O1, C, id))) (phplus Pinv Pleak) l0 = fold_left phplus (map pof T) (phplus Pinv Pleak) l0).
  {
  intros.
  apply eq_heap_disch with (p:=p) (z:=ll); repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  exists wt, ot.
  assumption.
  eexists.
  eexists.
  reflexivity.
  }


  assert (tmp: Lof ll = Aof ll /\ Pof ll = false /\ Xof ll = None /\
    (h (Aof ll) <> Some 1%Z -> In (Oof ll) (concat (map oof T)))).
  {
  apply LOCKOK.
  right.
  exists wt, ot.
  left.
  assumption.
  }
  destruct tmp as (lll,(plf,(ninrlxll,inlt))).

  assert (p0l: forall p0 id' (NEQ: id <> id') (IN: In (p0,id') (map (fun x => (pof x, snd x)) T)), p0 ll = Some Lock \/ p0 ll = None).
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  assert (PHPDp0: phplusdef p p0).
  {
  apply DEFL with id x6.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  rewrite <- H0.
  auto.
  }
  unfold phplusdef in PHPDp0.
  specialize PHPDp0 with ll.
  rewrite pl in PHPDp0.
  destruct (p0 ll) eqn:p0l.
  destruct k;
  try contradiction.
  left.
  reflexivity.
  right.
  reflexivity.
  }

  assert (phpdefpil: phplusdef p Pinv /\ phplusdef p Pleak).
  {
  apply PHPD.
  assumption.
  }

  assert (pinvl: phplus Pinv Pleak ll = Some Lock \/ phplus Pinv Pleak ll = None).
  {
  assert (PHPDppi: phplusdef p (phplus Pinv Pleak)).
  repeat php_.
  unfold phplusdef in PHPDppi.
  specialize PHPDppi with ll.
  rewrite pl in PHPDppi.
  destruct (phplus Pinv Pleak ll).
  destruct k;
  try contradiction.
  left.
  reflexivity.
  right.
  reflexivity.
  }

  assert (EQWT: forall l0 p O C, filterb (xOf (fun x  => Lof x) locs) (Aof l0) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) =
    filterb (xOf (fun x  => Lof x) locs) (Aof l0)(fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof
    (updl T id (tt, tx, p, O, C, id)))))).
  {
  intros.
  apply filterb_updl_eq.
  intros.
  split.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some v0)).
  inversion e.
  reflexivity.
  intros.
  assert (X': x' = (nop, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  destruct ((opZ_eq_dec None (Some v0))).
  inversion e.
  reflexivity.
  }


  assert (EQO: forall l p (NEQ: l <> ll)
    (fln: fold_left phplus (map pof T) (phplus Pinv Pleak) l <> None),
    filterb (xOf (fun x  => Lof x) locs) (Aof l) (count_occ Z.eq_dec (concat (map Aoof (updl T id
    (tt, tx, p, O1, C, id)))))
     = filterb (xOf (fun x  => Lof x) locs) (Aof l) (count_occ Z.eq_dec (concat (map Aoof T)))).
  {
  intros.
  symmetry.
  apply filterb_updl_obs_eq.
  intros.
  assert (X': x' = (nop, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold Aoof.
  simpl.
  erewrite count_perm1 with (l2:= map (fun x => Aofo x) (Oof lv :: O1)).
  simpl.
  destruct (Z.eq_dec (Aofo (Oof lv)) v0).
  assert (lovv: Lof lv = Aof l).
  {
  assert (G: xOf (fun x  => Lof x) locs (Aof lv) = Some (Lof lv)).
  {
  apply xOf_same.
  apply in_map.
  apply LOCs.
  rewrite COND.
  apply some_none.
  apply comp_cons.
  apply LOCs.
  rewrite COND.
  apply some_none.
  unfold comp.
  intros.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  }
  rewrite <- e in IN.
  unfold Aof in G.
  rewrite IN in G.
  inversion G.
  reflexivity.
  }
  assert (l = ll).
  {
  apply INJ.
  assumption.
  rewrite LOCKED.
  apply some_none.
  omega.
  }
  contradiction.
  reflexivity.
  apply Permutation_map.
  assumption.
  }

  assert (ODEC: count_occ Z.eq_dec (concat (map Aoof T)) ([[v]]) - 1 = count_occ Z.eq_dec (concat
    (map Aoof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)%nat))),
    O1, C, id)))) ([[v]])).
  {
  eapply count_updl_decr' with (O':= map (fun x => Aofo x) O) (O0:=map (fun x => Aofo x) O1).
  assumption.
  simpl.
  replace (([[v]]) :: map (fun x => Aofo x) O1) with (map (fun x => Aofo x) (Oof lv::O1)).
  apply Permutation_map.
  assumption.
  simpl.
  unfold Aof in eqlv.
  rewrite eqlv.
  reflexivity.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  split.
  reflexivity.
  assumption.
  reflexivity.
  }

  assert (tmp: wt = WTs ll (map cmdof T) locs /\
           ot = OBs ll (concat (map Aoof T)) locs).
  {
  apply WTsOTsOK.
  left.
  assumption.
  }
  destruct tmp as (WT1,OT1).

  assert (FIL1: upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1) =
    filterb (xOf (fun x  => Lof x) locs) (Aof ll)
    (count_occ Z.eq_dec (concat (map Aoof (updl T id
    (tt, tx,  upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))),
    O1, C, id)))))).
  {
  apply functional_extensionality.
  intros.
  unfold upd at 1.
  destruct (Z.eq_dec x ([[v]])).
  rewrite e in *.
  apply eq_trans with (OBs ll (concat (map Aoof T)) locs ([[v]]) - 1).
  rewrite OT1.
  reflexivity.
  unfold OBs.
  unfold filterb.
  destruct (xOf (fun x0 => Lof x0) locs ([[v]])).
  destruct (Z.eq_dec ([[v]]) (Aof ll)).
  omega.
  destruct (Z.eq_dec z (Aof ll)).
  assumption.
  reflexivity.
  reflexivity.
  apply eq_trans with (OBs ll (concat (map Aoof T)) locs x).
  rewrite OT1.
  reflexivity.
  unfold OBs.
  unfold filterb.
  destruct (xOf (fun x0 => Lof x0) locs x).
  destruct (Z.eq_dec x (Aof ll)).
  reflexivity.
  destruct (Z.eq_dec z (Aof ll)).
  apply count_updl_eq.
  intros.
  assert (X': x' = (nop, tx, p, O, C, id)).
  apply in_elem with T; assumption.
  rewrite X'.
  unfold Aoof.
  simpl.
  erewrite count_perm1 with (l2:= map (fun x => Aofo x) (Oof lv :: O1)).
  unfold Oof.
  simpl.
  
  destruct (Z.eq_dec (Aofo (fst (fst (fst lv)))) x).
  rewrite <- eqlv in *.
  unfold Aof in n.
  unfold Oof in n.
  rewrite <- e0 in n.
  contradiction.
  omega.
  apply Permutation_map.
  assumption.
  reflexivity.
  reflexivity.
  }

  assert (EQG: map gof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))), O1, C, id)) =
    map gof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  assumption.
  assumption.
  }
  inversion EQX.
  reflexivity.
  reflexivity.
  }
  assert (EQGI: map (fun x => (gof x, snd x)) (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll
    (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))), O1,C, id)) = map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  assumption.
  assumption.
  }
  inversion EQX.
  reflexivity.
  reflexivity.
  }

  assert (INOB: forall l (NEQ: Oof lv <> l) (IN: In l (concat (map oof T))),
    In l (concat (map oof (updl T id (tt, tx,
    upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))),
    O1, C, id))))).
  {
  intros.
  rewrite <- flat_map_concat_map in IN.
  apply in_flat_map in IN.
  destruct IN as (x,(INx,INl0)).
  unfold updl.
  rewrite map_map.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists x.
  split.
  assumption.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  }
  inversion EQX.
  unfold oof in *.
  simpl in *.
  rewrite H3 in INl0.
  apply Permutation_in with (l':=Oof lv :: O1) in INl0.
  destruct INl0 as [IN|IN].
  contradiction.
  assumption.
  assumption.
  assumption.
  }

  assert (INOB': forall l (IN: In l (concat (map oof (updl T id (tt, tx,
    upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))),
    O1, C, id))))), In l (concat (map oof T))).
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  rewrite <- flat_map_concat_map in IN.
  apply in_flat_map in IN.
  destruct IN as (x,(INx,INl0)).
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  }
  inversion EQX.
  exists (nop, tx, p, O, C, id).
  split.
  assumption.
  unfold oof in *.
  simpl in *.
  apply Permutation_in with (Oof lv :: O1).
  apply Permutation_sym.
  assumption.
  right.
  assumption.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }

  assert (bpu: boundph (upd (location_eq_dec Z.eq_dec) p ll
    (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))))).
  {
  apply boundph_upd.
  apply BPE.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bg: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  rewrite EQG.
  rewrite EQGI.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  assumption.
  }

  exists.
  {
  split.
  {
  intros.
  eapply SPUR1 with (c:=c).
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  destruct (Z.eq_dec (snd y) id).
  unfold cmdof in EQy.
  rewrite <- EQy in WASW.
  inversion WASW.
  apply in_map_iff.
  exists y.
  auto.
  apply WASW.
  }
  intros.
  rewrite EQH in CONDv.
  apply SPUR2 in CONDv.
  destruct CONDv as (a,(b,(c,d))).
  exists a, b.
  exists.
  destruct (location_eq_dec Z.eq_dec ll a).
  right.
  eexists.
  eexists.
  rewrite <- e.
  rewrite LOCK.
  reflexivity.
  rewrite EQH.
  assumption.
  assumption.
  assumption.
  unfold not.
  intros CO.
  rewrite <- CO in CONDv.
  rewrite LOCK in CONDv.
  inversion CONDv.
  }

  exists.
  {
  split.
  {
  unfold defl.
  intros.
  unfold updl in IN1.
  rewrite map_map in IN1.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  destruct x1 as (((((a1,a2),a3),a4),a5),a6).
  simpl in EQ1.
  unfold updl in IN2.
  rewrite map_map in IN2.
  apply in_map_iff in IN2.
  destruct IN2 as (x2,(EQ2,IN2)).
  destruct x2 as (((((y1,y2),y3),y4),y5),y6).
  simpl in EQ2.
  destruct (Z.eq_dec a6 id).
  rewrite e in *.
  unfold pof in EQ1.
  simpl in EQ1.
  inversion EQ1.
  destruct (Z.eq_dec y6 id).
  rewrite e0 in *.
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  omega.
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  apply phpdef_upd_locked.
  apply DEFL with id y6.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  rewrite <- H2.
  auto.
  apply p0l with y6.
  omega.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  rewrite <- H2.
  auto.
  unfold pof in EQ1.
  simpl in EQ1.
  inversion EQ1.
  destruct (Z.eq_dec y6 id).
  rewrite e in *.
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  apply phpdef_comm.
  apply phpdef_upd_locked.
  apply DEFL with id a6.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (a1, a2, a3, a4, a5, a6).
  rewrite <- H0.
  auto.
  apply p0l with a6.
  omega.
  apply in_map_iff.
  exists (a1, a2, a3, a4, a5, a6).
  rewrite <- H0.
  auto.
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  apply DEFL with a6 y6.
  omega.
  apply in_map_iff.
  exists (a1, a2, a3, a4, a5, a6).
  rewrite <- H0.
  auto.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  rewrite <- H2.
  auto.
  }

  exists. assumption.
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  rewrite <- EQ.
  apply phpdef_dist'.
  apply phpdef_upd_locked.
  repeat php_.
  assumption.
  assumption.
  simpl in EQ.
  rewrite <- EQ.
  apply PHPD.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  rewrite <- EQ.
  assumption.
  simpl in EQ.
  rewrite <- EQ.
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists.
  {
  apply boundph_disch with (p:=p) (z:=ll); repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  exists wt, ot.
  assumption.
  exists wt.
  eexists.
  reflexivity.
  }
  assert (PH:=PH2H).
  unfold phtoh in *.
  destruct PH as (PH1,PH2).
  split.
  {
  intros.
  specialize PH1 with l.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite LOCK.
  rewrite LOCKED in PH1.
  assumption.
  rewrite EQH.
  assumption.
  assumption.
  }
  intros.
  apply PH2.
  intros.
  apply NONE in EQ.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite LOCK in EQ.
  inversion EQ.
  rewrite <- EQH.
  assumption.
  assumption.
  }
  exists.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
  exists.
  {
  apply NoDup_updl.
  assumption.
  }
  exists.
  {
  split. assumption.
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  apply AinvOK in IN.
  destruct IN as (CO,tmp).
  rewrite LOCKED in CO.
  inversion CO.
  rewrite EQH.
  apply AinvOK.
  assumption.
  assumption.
  }
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) l ll).
  rewrite e in *.
  rewrite LOCK in LOCK0.
  inversion LOCK0.
  rewrite EQH in LOCK0.
  apply INAOK in LOCK0.
  rewrite <- EQWT.
  rewrite EQO.
  assumption.
  assumption.
  assert (tmp: In l (map snd Ainv)).
  {
  apply in_map_iff.
  exists (subsas (snd (Iof l))
             (invs (fst (Iof l)) (WTs l (map cmdof T) locs)
                (OBs l (concat (map Aoof T)) locs)), l).
  auto.
  }
  apply AinvOK in tmp.
  destruct tmp as (tmp1,tmp2).
  rewrite tmp1.
  apply some_none.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  }
  assumption.
  }
  exists.
  {
  split.
  {
  assert (G: forall x, fold_left phplus (map pof (updl T id
    (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))),
    O1, C, id))) (phplus Pinv Pleak) x <> None ->
    fold_left phplus (map pof T) (phplus Pinv Pleak) x <> None).
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll x).
  rewrite <- e.
  rewrite LOCKED.
  apply some_none.
  rewrite <- EQH.
  assumption.
  assumption.
  }
  unfold injph.
  intros.
  apply INJ.
  apply G.
  assumption.
  apply G.
  assumption.
  }
  split. assumption.
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e.
  split.
  intros.
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  intros.
  rewrite LOCK.
  apply some_none.
  rewrite EQH.
  apply LOCs.
  assumption.
  }
  intros.

  destruct ((olocation_eq_dec Z.eq_dec) (Oof ll) o).
  exists ll, e.
  rewrite LOCK.
  apply some_none.
  apply INOB' in IN.
  apply OBsOK in IN.
  destruct IN as (l',(EQl',pl')).
  exists l', EQl'.
  rewrite EQH.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  rewrite EQl' in n.
  contradiction.
  }
  exists.
  {
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  split. assumption.
  split. assumption.
  split. assumption.
  intros.
  apply inlt in H.
  apply INOB.
  unfold not.
  intros.
  assert (CO: lv = ll).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  unfold Aof.
  rewrite H0.
  reflexivity.
  }
  contradiction.
  assumption.

  rewrite EQH in LOCK0.
  assert (LOCK':=LOCK0).
  apply LOCKOK in LOCK0.
  destruct LOCK0 as (L1,(L2,(L3,L4))).
  split. assumption.
  split. assumption.
  split. assumption.
  intros.
  apply L4 in H.
  apply INOB.
  unfold not.
  intros.
  assert (CO: lv = l).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  destruct LOCK' as [CO|CO].
  rewrite CO.
  apply some_none.
  destruct CO as (wt',(ot',CO)).
  destruct CO as [CO|CO];
  rewrite CO;
  apply some_none.
  unfold Aof.
  rewrite H0.
  reflexivity.
  }
  rewrite <- CO in LOCK'.
  rewrite COND in LOCK'.
  destruct LOCK' as [CO1|CO1].
  inversion CO1.
  destruct CO1 as (wt',(ot',CO1)).
  destruct CO1 as [CO1|CO1].
  inversion CO1.
  inversion CO1.
  assumption.
  assumption.
  }
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite LOCK in ULOCK.
  inversion ULOCK.
  rewrite EQH in ULOCK.
  apply ULOCKOK in ULOCK.
  destruct ULOCK as (U1,U2).
  split. assumption.
  unfold not.
  intros.
  apply U2.
  apply INOB'.
  assumption.
  assumption.
  }
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite LOCK in UCOND.
  inversion UCOND.
  rewrite EQH in UCOND.
  apply UCONDOK in UCOND.
  unfold not.
  intros.
  apply UCOND.
  apply INOB'.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  rewrite <- EQWT.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite LOCK in ULOCKED.
  destruct ULOCKED as [U1|U1].
  {
  inversion U1.
  rewrite <- H0.
  split.
  rewrite WT1.
  reflexivity.
  assumption.
  }
  inversion U1.
  rewrite EQO.
  apply WTsOTsOK.
  rewrite <- EQH.
  assumption.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  rewrite <- EQH.
  destruct ULOCKED as [U|U];
  rewrite U;
  apply some_none.
  assumption.
  }

  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  {
(* ==================== x6 = id ===========*)
  simpl in EQ.
  symmetry in EQ.
  inversion EQ.
  split.
  unfold wellformed.
  auto.
  exists.
  eapply sat_weak_imp1; try assumption.
  apply SAT.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  }
(* ==================== x6 <> id ===========*)
  symmetry in EQ.
  inversion EQ.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF3,(WP3,VOBS3)).
  exists. assumption.
  exists.

  assert (bx3: boundph x3).
  {
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  split. reflexivity. assumption.
  }

  assert (bx5: boundgh x5).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=(ghplus Cinv Cleak)); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  split. reflexivity. assumption.
  }

  eapply sat_weak_imp1; try assumption.
  apply WP3.
  intros.
  eapply sat_tx_weak_imp1; try assumption.

  intros.
  rewrite W4COND in WP3.
  apply sat_wait4cond in WP3.
  destruct WP3 as (l0,(v0,(eql0,(eqv,(p'v,(p'l0,(lofl0,(prcv0,(prcv,SAT2))))))))).

  assert (COND': fold_left phplus (map pof T) (phplus Pinv Pleak) v0 = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }

  assert (LOCK': fold_left phplus (map pof T) (phplus Pinv Pleak) l0 = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) l0 = Some (Locked wt ot)).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  right.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }

  apply VOBS3 in W4COND.
  destruct W4COND as (v',(l',(inv',(inl',(eqv',(eql',sobs')))))).
  exists v', l', inv', inl', eqv', eql'.
  rewrite <- EQWT.

  assert (EQv'v0: v' = v0).
  {
  apply INJ.
  apply LOCs.
  assumption.
  rewrite COND'.
  apply some_none.
  omega.
  }

  assert (EQl'l0: l' = l0).
  {
  apply INJ.
  apply LOCs.
  assumption.
  destruct LOCK' as [L|L].
  rewrite L.
  apply some_none.
  destruct L as (wt',(ot',L)).
  rewrite L.
  apply some_none.
  omega.
  }

  destruct ((location_eq_dec Z.eq_dec) l' ll).
  rewrite e in *.
  {
  rewrite <- FIL1.
  unfold WTs in WT1.
  unfold upd.
  destruct (Z.eq_dec ([[ev]]) ([[v]])).
  rewrite e0 in *.
  assert (EQv'lv: v' = lv).
  {
  rewrite EQv'v0.
  apply INJ.
  rewrite COND'.
  apply some_none.
  rewrite COND.
  apply some_none.
  omega.
  }
  rewrite EQv'lv in *.
  rewrite <- WT1.

  assumption.
  unfold WTs, OBs in *.
  rewrite OT1.
  assumption.
  }

  rewrite EQO.
  assumption.
  assumption.
  rewrite EQl'l0.
  destruct LOCK' as [L|L].
  rewrite L.
  apply some_none.
  destruct L as (wt',(ot',L)).
  rewrite L.
  apply some_none.
Qed.


Lemma g_dischu_preserves_validity0:
  forall m sp h T id tx p O C invs Cinv Cleak wt ot O1 lv ll v
         (INT: In (nop, tx, p, O, C, id) T)
         (O1eq: Permutation O (Oof lv::O1))
         (eqlv: Aof lv = ([[v]]))
         (eqll: Aof ll = Lof lv)
         (pl: p ll = Some (Ulock wt ot))
         (pv: p lv = Some Icond)
         (INO: In (Oof lv) O)
         (SAFE: safe_obs lv (wt ([[v]])) ((ot ([[v]])) - 1) = true)
         (SAT: sat (upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)%nat))))
           (Some O1) C (weakest_pre_ct (S m) sp (tt, tx) invs))
         (VALID: validk0 (S m) sp T Cinv Cleak h invs),
    validk0 m sp (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll
    (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))), O1, C, id)) Cinv Cleak h invs.
Proof.
  intros.
  unfold validk0 in VALID.
  destruct VALID as (locs,(Pinv,(Pleak,(Ainv,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS))))))))))))).
  unfold validk0.
  unfold pheaps_heap in *.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  unfold locations_ok in *.
  destruct LOCsOK as (INJ,(LCOM,(LOCs,OBsOK))).
  unfold invs_ok in *.
  destruct INVsOK as (NDPA,(AinvOK,(INAOK,SATAOK))).
  unfold locks_ok.
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.
  unfold validk0.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  destruct WF as (WF1,WF2).

  exists locs, Pinv, Pleak, Ainv.
  subst.

  assert (INpT: In p (map pof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (phpdefpil: phplusdef p Pinv /\ phplusdef p Pleak).
  {
  apply PHPD.
  assumption.
  }

  assert (p0zn: forall p0 id0 (NEQ: id <> id0)
    (IN: In (p0, id0) (map (fun x => (pof x, snd x)) T)),
    p0 ll = None).
  {
  intros.
  assert (pd: phplusdef p0 p).
  {
  apply DEFL with id0 id.
  omega.
  assumption.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }
  unfold phplusdef in pd.
  specialize pd with ll.
  rewrite pl in pd.
  destruct (p0 ll).
  destruct k; contradiction.
  reflexivity.
  }

  assert (pilll: phplus Pinv Pleak ll = None).
  {
  assert (pd: phplusdef p (phplus Pinv Pleak)).
  {
  apply phpdef_pair.
  assumption.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  }
  unfold phplusdef in pd.
  specialize pd with ll.
  rewrite pl in pd.
  destruct (phplus Pinv Pleak ll).
  destruct k; contradiction.
  reflexivity.
  }

  assert (phpdefp0il: forall p0 : pheap, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  apply phpdef_pair.
  assumption.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  }

  assert (COND: fold_left phplus (map pof T) (phplus Pinv Pleak) lv = Some Icond).
  {
  apply fold_icond; repeat php_.
  apply pofs.
  right.
  exists p, INpT.
  assumption.
  }
 
  assert (LOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Ulock wt ot)).
  {
  apply fold_ulock; repeat php_.
  apply pofs.
  right.
  exists p, INpT.
  assumption.
  }

  assert (NEQlvll: lv <> ll).
  {
  unfold not.
  intros.
  rewrite H in COND.
  rewrite COND in LOCKED.
  inversion LOCKED.
  }

  assert (NEQvlv: ([[v]]) <> Lof lv).
  {
  unfold not.
  intros.
  assert (CO: lv = ll).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  omega.
  }
  contradiction.
  }

  assert (LOCK: fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)%nat))),
    O1, C, id))) (phplus Pinv Pleak) ll = Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)%nat))).
  {
  apply ulock_dischu with p; repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  exists wt, ot.
  assumption.
  }

  assert (EQH: forall l0 (NEQ: ll <> l0), fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)%nat))),
    O1, C, id))) (phplus Pinv Pleak) l0 = fold_left phplus (map pof T) (phplus Pinv Pleak) l0).
  {
  intros.
  apply eq_heap_dischu with (p:=p) (z:=ll); repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  exists wt, ot.
  assumption.
  eexists.
  eexists.
  reflexivity.
  }

  assert (tmp: Lof ll = Aof ll /\ Pof ll = false /\ Xof ll = None /\
    (h (Aof ll) <> Some 1%Z -> In (Oof ll) (concat (map oof T)))).
  {
  apply LOCKOK.
  right.
  exists wt, ot.
  right.
  assumption.
  }
  destruct tmp as (lll,(plf,(ninrlxll,inlt))).

  assert (p0l: forall p0 id' (NEQ: id <> id') (IN: In (p0,id') (map (fun x => (pof x, snd x)) T)), p0 ll = Some Lock \/ p0 ll = None).
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  assert (PHPDp0: phplusdef p p0).
  {
  apply DEFL with id x6.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  rewrite <- H0.
  auto.
  }
  unfold phplusdef in PHPDp0.
  specialize PHPDp0 with ll.
  rewrite pl in PHPDp0.
  destruct (p0 ll) eqn:p0l.
  destruct k;
  try contradiction.
  right.
  reflexivity.
  }

  assert (pinvl: phplus Pinv Pleak ll = Some Lock \/ phplus Pinv Pleak ll = None).
  {
  assert (PHPDppi: phplusdef p (phplus Pinv Pleak)).
  repeat php_.
  unfold phplusdef in PHPDppi.
  specialize PHPDppi with ll.
  rewrite pl in PHPDppi.
  destruct (phplus Pinv Pleak ll).
  destruct k;
  try contradiction.
  right.
  reflexivity.
  }

  assert (EQWT: forall l0 p O C, filterb (xOf (fun x  => Lof x) locs) (Aof l0) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) =
    filterb (xOf (fun x  => Lof x) locs) (Aof l0)(fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof
    (updl T id (tt, tx, p, O, C, id)))))).
  {
  intros.
  apply filterb_updl_eq.
  intros.
  split.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some v0)).
  inversion e.
  reflexivity.
  intros.
  assert (X': x' = (nop, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  destruct ((opZ_eq_dec None (Some v0))).
  inversion e.
  reflexivity.
  }


  assert (EQO: forall l p (NEQ: l <> ll)
    (fln: fold_left phplus (map pof T) (phplus Pinv Pleak) l <> None),
    filterb (xOf (fun x  => Lof x) locs) (Aof l) (count_occ Z.eq_dec (concat (map Aoof (updl T id
    (tt, tx, p, O1, C, id)))))
     = filterb (xOf (fun x  => Lof x) locs) (Aof l) (count_occ Z.eq_dec (concat (map Aoof T)))).
  {
  intros.
  symmetry.
  apply filterb_updl_obs_eq.
  intros.
  assert (X': x' = (nop, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold Aoof.
  simpl.
  erewrite count_perm1 with (l2:= map (fun x => Aofo x) (Oof lv :: O1)).
  simpl.
  destruct (Z.eq_dec (Aofo (Oof lv)) v0).
  assert (lovv: Lof lv = Aof l).
  {
  assert (G: xOf (fun x  => Lof x) locs (Aof lv) = Some (Lof lv)).
  {
  apply xOf_same.
  apply in_map.
  apply LOCs.
  rewrite COND.
  apply some_none.
  apply comp_cons.
  apply LOCs.
  rewrite COND.
  apply some_none.
  unfold comp.
  intros.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  }
  rewrite <- e in IN.
  unfold Aof in G.
  rewrite IN in G.
  inversion G.
  reflexivity.
  }
  assert (l = ll).
  {
  apply INJ.
  assumption.
  rewrite LOCKED.
  apply some_none.
  omega.
  }
  contradiction.

  reflexivity.
  apply Permutation_map.
  assumption.
  }

  assert (ODEC: count_occ Z.eq_dec (concat (map Aoof T)) ([[v]]) - 1 = count_occ Z.eq_dec (concat
    (map Aoof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)%nat))),
    O1, C, id)))) ([[v]])).
  {
  eapply count_updl_decr' with (O':= map (fun x => Aofo x) O) (O0:=map (fun x => Aofo x) O1).
  assumption.
  simpl.
  replace (([[v]]) :: map (fun x => Aofo x) O1) with (map (fun x => Aofo x) (Oof lv::O1)).
  apply Permutation_map.
  assumption.
  simpl.
  unfold Aof in eqlv.
  rewrite eqlv.
  reflexivity.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  split.
  reflexivity.
  assumption.
  reflexivity.
  }

  assert (tmp: wt = WTs ll (map cmdof T) locs /\
           ot = OBs ll (concat (map Aoof T)) locs).
  {
  apply WTsOTsOK.
  right.
  assumption.
  }
  destruct tmp as (WT1,OT1).

  assert (FIL1: upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1) =
    filterb (xOf (fun x  => Lof x) locs) (Aof ll)
    (count_occ Z.eq_dec (concat (map Aoof (updl T id
    (tt, tx,  upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))),
    O1, C, id)))))).
  {
  apply functional_extensionality.
  intros.
  unfold upd at 1.
  destruct (Z.eq_dec x ([[v]])).
  rewrite e in *.
  apply eq_trans with (OBs ll (concat (map Aoof T)) locs ([[v]]) - 1).
  rewrite OT1.
  reflexivity.
  unfold OBs.
  unfold filterb.
  destruct (xOf (fun x0 => Lof x0) locs ([[v]])).
  destruct (Z.eq_dec ([[v]]) (Aof ll)).
  omega.
  destruct (Z.eq_dec z (Aof ll)).
  assumption.
  reflexivity.
  reflexivity.
  apply eq_trans with (OBs ll (concat (map Aoof T)) locs x).
  rewrite OT1.
  reflexivity.
  unfold OBs.
  unfold filterb.
  destruct (xOf (fun x0 => Lof x0) locs x).
  destruct (Z.eq_dec x (Aof ll)).
  reflexivity.
  destruct (Z.eq_dec z (Aof ll)).
  apply count_updl_eq.
  intros.
  assert (X': x' = (nop, tx, p, O, C, id)).
  apply in_elem with T; assumption.
  rewrite X'.
  unfold Aoof.
  simpl.
  erewrite count_perm1 with (l2:= map (fun x => Aofo x) (Oof lv :: O1)).
  simpl.
  destruct (Z.eq_dec (Aofo (Oof lv)) x).
  rewrite <- eqlv in *.
  rewrite <- e0 in n.
  contradiction.
  reflexivity.
  apply Permutation_map.
  assumption.
  reflexivity.
  reflexivity.
  }


  assert (EQG: map gof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))), O1, C, id)) =
    map gof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  assumption.
  assumption.
  }
  inversion EQX.
  reflexivity.
  reflexivity.
  }
  assert (EQGI: map (fun x => (gof x, snd x)) (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll
    (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))), O1,C, id)) = map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  assumption.
  assumption.
  }
  inversion EQX.
  reflexivity.
  reflexivity.
  }

  assert (INOB: forall l (NEQ: Oof lv <> l) (IN: In l (concat (map oof T))),
    In l (concat (map oof (updl T id (tt, tx,
    upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))),
    O1, C, id))))).
  {
  intros.
  rewrite <- flat_map_concat_map in IN.
  apply in_flat_map in IN.
  destruct IN as (x,(INx,INl0)).
  unfold updl.
  rewrite map_map.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists x.
  split.
  assumption.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  }
  inversion EQX.
  unfold oof in *.
  simpl in *.
  rewrite H3 in INl0.
  apply Permutation_in with (l':=Oof lv :: O1) in INl0.
  destruct INl0 as [IN|IN].
  contradiction.
  assumption.
  assumption.
  assumption.
  }

  assert (INOB': forall l (IN: In l (concat (map oof (updl T id (tt, tx,
    upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))),
    O1, C, id))))), In l (concat (map oof T))).
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  rewrite <- flat_map_concat_map in IN.
  apply in_flat_map in IN.
  destruct IN as (x,(INx,INl0)).
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (nop, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  }
  inversion EQX.
  exists (nop, tx, p, O, C, id).
  split.
  assumption.
  unfold oof in *.
  simpl in *.
  apply Permutation_in with (Oof lv :: O1).
  apply Permutation_sym.
  assumption.
  right.
  assumption.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }

  assert (bpupd: boundph (upd (location_eq_dec Z.eq_dec) p ll
    (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))))).
  {
  apply boundph_upd.
  apply BPE.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bg: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  rewrite EQG.
  rewrite EQGI.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  assumption.
  }

  exists.
  {
  split.
  {
  intros.
  eapply SPUR1 with (c:=c).
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  destruct (Z.eq_dec (snd y) id).
  unfold cmdof in EQy.
  rewrite <- EQy in WASW.
  inversion WASW.
  apply in_map_iff.
  exists y.
  auto.
  apply WASW.
  }
  intros.
  rewrite EQH in CONDv.
  apply SPUR2 in CONDv.
  destruct CONDv as (a,(b,(c,d))).
  exists a, b.
  exists.
  destruct (location_eq_dec Z.eq_dec ll a).
  rewrite <- e in *.
  rewrite LOCKED in c.
  destruct c as [c|c].
  inversion c.
  destruct c as (wt',(ot',c));
  inversion c.
  rewrite EQH.
  assumption.
  assumption.
  assumption.
  unfold not.
  intros CO.
  rewrite <- CO in CONDv.
  rewrite LOCK in CONDv.
  inversion CONDv.
  }

  exists.
  {
  split.
  {
  unfold defl.
  intros.
  unfold updl in IN1.
  rewrite map_map in IN1.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  destruct x1 as (((((a1,a2),a3),a4),a5),a6).
  simpl in EQ1.
  unfold updl in IN2.
  rewrite map_map in IN2.
  apply in_map_iff in IN2.
  destruct IN2 as (x2,(EQ2,IN2)).
  destruct x2 as (((((y1,y2),y3),y4),y5),y6).
  simpl in EQ2.
  destruct (Z.eq_dec a6 id).
  rewrite e in *.
  unfold pof in EQ1.
  simpl in EQ1.
  inversion EQ1.
  destruct (Z.eq_dec y6 id).
  rewrite e0 in *.
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  omega.
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  apply phpdef_ulock.
  apply DEFL with id y6.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  rewrite <- H2.
  auto.
  apply p0zn with id2; try assumption.
  omega.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  auto.
  unfold pof in EQ1.
  simpl in EQ1.
  inversion EQ1.
  destruct (Z.eq_dec y6 id).
  rewrite e in *.
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  apply phpdef_comm.
  apply phpdef_ulock.
  apply DEFL with id a6.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (a1, a2, a3, a4, a5, a6).
  rewrite <- H0.
  auto.
  apply p0zn with id1; try assumption.
  omega.
  apply in_map_iff.
  exists (a1, a2, a3, a4, a5, a6).
  auto.
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  apply DEFL with a6 y6.
  omega.
  apply in_map_iff.
  exists (a1, a2, a3, a4, a5, a6).
  rewrite <- H0.
  auto.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  rewrite <- H2.
  auto.
  }

  exists. assumption.
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  rewrite <- EQ.
  apply phpdef_dist'.
  apply phpdef_ulock.
  repeat php_.
  assumption.
  assumption.
  simpl in EQ.
  rewrite <- EQ.
  apply PHPD.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  rewrite <- EQ.
  assumption.
  simpl in EQ.
  rewrite <- EQ.
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists.
  {
  apply boundph_dischu with (p:=p) (z:=ll); repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  exists wt, ot.
  assumption.
  exists wt.
  eexists.
  reflexivity.
  }
  assert (PH:=PH2H).
  unfold phtoh in *.
  destruct PH as (PH1,PH2).
  split.
  {
  intros.
  specialize PH1 with l.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite LOCK.
  rewrite LOCKED in PH1.
  assumption.
  rewrite EQH.
  assumption.
  assumption.
  }
  intros.
  apply PH2.
  intros.
  apply NONE in EQ.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite LOCK in EQ.
  inversion EQ.
  rewrite <- EQH.
  assumption.
  assumption.
  }
  exists.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
  exists.
  {
  apply NoDup_updl.
  assumption.
  }
  exists.
  {
  split. assumption.
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  apply AinvOK in IN.
  destruct IN as (CO,tmp).
  rewrite LOCKED in CO.
  inversion CO.
  rewrite EQH.
  apply AinvOK.
  assumption.
  assumption.
  }
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) l ll).
  rewrite e in *.
  rewrite LOCK in LOCK0.
  inversion LOCK0.
  rewrite EQH in LOCK0.
  apply INAOK in LOCK0.
  rewrite <- EQWT.
  rewrite EQO.
  assumption.
  assumption.
  assert (tmp: In l (map snd Ainv)).
  {
  apply in_map_iff.
  exists (subsas (snd (Iof l))
             (invs (fst (Iof l)) (WTs l (map cmdof T) locs)
                (OBs l (concat (map Aoof T)) locs)), l).
  auto.
  }
  apply AinvOK in tmp.
  destruct tmp as (tmp1,tmp2).
  rewrite tmp1.
  apply some_none.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  }
  assumption.
  }
  exists.
  {
  split.
  {
  assert (G: forall x, fold_left phplus (map pof (updl T id
    (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))),
    O1, C, id))) (phplus Pinv Pleak) x <> None ->
    fold_left phplus (map pof T) (phplus Pinv Pleak) x <> None).
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll x).
  rewrite <- e.
  rewrite LOCKED.
  apply some_none.
  rewrite <- EQH.
  assumption.
  assumption.
  }
  unfold injph.
  intros.
  apply INJ.
  apply G.
  assumption.
  apply G.
  assumption.
  }
  split. assumption.
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e.
  split.
  intros.
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  intros.
  rewrite LOCK.
  apply some_none.
  rewrite EQH.
  apply LOCs.
  assumption.
  }
  intros.
  destruct ((olocation_eq_dec Z.eq_dec) (Oof ll) o).
  exists ll, e.
  rewrite LOCK.
  apply some_none.
  apply INOB' in IN.
  apply OBsOK in IN.
  destruct IN as (l',(EQl',pl')).
  exists l', EQl'.
  destruct ((location_eq_dec Z.eq_dec) ll l').
  rewrite <- e.
  rewrite LOCK.
  apply some_none.
  rewrite EQH.
  assumption.
  assumption.
  }
  exists.
  {
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  split. assumption.
  split. assumption.
  split. assumption.
  intros.
  apply inlt in H.
  apply INOB.
  unfold not.
  intros.
  assert (CO: lv = ll).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  unfold Aof.
  rewrite H0.
  reflexivity.
  }
  contradiction.
  assumption.

  rewrite EQH in LOCK0.
  assert (LOCK':=LOCK0).
  apply LOCKOK in LOCK0.
  destruct LOCK0 as (L1,(L2,(L3,L4))).
  split. assumption.
  split. assumption.
  split. assumption.
  intros.
  apply L4 in H.
  apply INOB.
  unfold not.
  intros.
  assert (CO1: lv = l).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  destruct LOCK' as [CO|CO].
  rewrite CO.
  apply some_none.
  destruct CO as (wt',(ot',CO)).
  destruct CO as [CO|CO];
  rewrite CO;
  apply some_none.
  unfold Aof.
  rewrite H0.
  reflexivity.
  }
  rewrite <- CO1 in LOCK'.
  rewrite COND in LOCK'.
  destruct LOCK' as [CO|CO].
  inversion CO.
  destruct CO as (wt',(ot',CO)).
  destruct CO as [CO|CO].
  inversion CO.
  inversion CO.
  assumption.
  assumption.
  }
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite LOCK in ULOCK.
  inversion ULOCK.
  apply ULOCKOK in LOCKED.
  destruct LOCKED as (L1,L2).
  split. assumption.
  unfold not.
  intros.
  apply L2.
  apply INOB'.
  rewrite H0.
  assumption.
  rewrite EQH in ULOCK.
  apply ULOCKOK in ULOCK.
  destruct ULOCK as (U1,U2).
  split. assumption.
  unfold not.
  intros.
  apply U2.
  apply INOB'.
  assumption.
  assumption.
  }
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite LOCK in UCOND.
  inversion UCOND.
  rewrite EQH in UCOND.
  apply UCONDOK in UCOND.
  unfold not.
  intros.
  apply UCOND.
  apply INOB'.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  rewrite <- EQWT.
  destruct ((location_eq_dec Z.eq_dec) ll l).
  rewrite <- e in *.
  rewrite LOCK in ULOCKED.
  destruct ULOCKED as [U1|U1].
  inversion U1.
  {
  inversion U1.
  rewrite <- H0.
  split.
  rewrite WT1.
  reflexivity.
  assumption.
  }
  rewrite EQO.
  apply WTsOTsOK.
  rewrite <- EQH.
  assumption.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  rewrite <- EQH.
  destruct ULOCKED as [U|U];
  rewrite U;
  apply some_none.
  assumption.
  }

  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  {
(* ==================== x6 = id ===========*)
  simpl in EQ.
  symmetry in EQ.
  inversion EQ.
  split.
  unfold wellformed.
  auto.
  exists.
  eapply sat_weak_imp1; try assumption.
  apply SAT.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  }
(* ==================== x6 <> id ===========*)
  symmetry in EQ.
  inversion EQ.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF3,(WP3,VOBS3)).
  exists. assumption.
  exists. 

  assert (bx3: boundph x3).
  {
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  split. reflexivity. assumption.
  }

  assert (bx5: boundgh x5).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=(ghplus Cinv Cleak)); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  split. reflexivity. assumption.
  }

  eapply sat_weak_imp1; try assumption.
  apply WP3.
  intros.
  eapply sat_tx_weak_imp1; try assumption.

  intros.
  rewrite W4COND in WP3.
  apply sat_wait4cond in WP3.
  destruct WP3 as (l0,(v0,(eql0,(eqv,(p'v,(p'l0,(lofl0,(prcv0,(prcv,SAT2))))))))).

  assert (COND': fold_left phplus (map pof T) (phplus Pinv Pleak) v0 = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }

  assert (LOCK': fold_left phplus (map pof T) (phplus Pinv Pleak) l0 = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) l0 = Some (Locked wt ot)).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  right.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }

  apply VOBS3 in W4COND.
  destruct W4COND as (v',(l',(inv',(inl',(eqv',(eql',sobs')))))).
  exists v', l', inv', inl', eqv', eql'.
  rewrite <- EQWT.

  assert (EQv'v0: v' = v0).
  {
  apply INJ.
  apply LOCs.
  assumption.
  rewrite COND'.
  apply some_none.
  omega.
  }

  assert (EQl'l0: l' = l0).
  {
  apply INJ.
  apply LOCs.
  assumption.
  destruct LOCK' as [L|L].
  rewrite L.
  apply some_none.
  destruct L as (wt',(ot',L)).
  rewrite L.
  apply some_none.
  omega.
  }

  destruct ((location_eq_dec Z.eq_dec) l' ll).
  rewrite e in *.
  {
  rewrite <- FIL1.
  unfold WTs in WT1.
  unfold upd.
  destruct (Z.eq_dec ([[ev]]) ([[v]])).
  rewrite e0 in *.
  assert (EQv'lv: v' = lv).
  {
  rewrite EQv'v0.
  apply INJ.
  rewrite COND'.
  apply some_none.
  rewrite COND.
  apply some_none.
  omega.
  }
  rewrite EQv'lv in *.
  rewrite <- WT1.

  assumption.
  unfold WTs, OBs in *.
  rewrite OT1.
  assumption.
  }

  rewrite EQO.
  assumption.
  assumption.
  rewrite EQl'l0.
  destruct LOCK' as [L|L].
  rewrite L.
  apply some_none.
  destruct L as (wt',(ot',L)).
  rewrite L.
  apply some_none.
Qed.


Lemma g_newctr_preserves_validity0:
  forall m sp h T id tx p O C Cinv Cleak invs gc
         (INT: In (nop, tx, p, O, C, id) T)
         (NONE: fold_left ghplus (map gof T) (ghplus Cinv Cleak) gc = None)
         (SAT: sat p (Some O) (upd Z.eq_dec C gc (Some (Some 0%nat,0%nat))) (weakest_pre_ct (S m) sp (tt, tx) invs))
         (VALID: validk0 (S m) sp T Cinv Cleak h invs),
    validk0 m sp (updl T id (tt, tx, p, O, upd Z.eq_dec C gc (Some (Some 0, 0)), id)) Cinv Cleak h invs.
Proof.
  intros.
  unfold validk0 in VALID.
  destruct VALID as (locs,(Pinv,(Pleak,(Ainv,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS))))))))))))).
  unfold validk0.
  unfold pheaps_heap in *.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  unfold locations_ok in *.
  destruct LOCsOK as (INJ,(LCOM,(LOCs,OBsOK))).
  unfold invs_ok in *.
  destruct INVsOK as (NDPA,(AinvOK,(INAOK,SATAOK))).
  unfold locks_ok.
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.
  unfold validk0.

  exists locs, Pinv, Pleak, Ainv.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (inc: In C (map gof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (incid: In (C, id) (map (fun x => (gof x, snd x)) T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (inp: In p (map pof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (bp: boundph p).
  {
  apply BPE.
  assumption.
  }

  assert (bc: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  left.
  assumption.
  }

  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP11,VOBS)).

  unfold wellformed in WF.
  simpl in WF.


  assert (c0gc: forall C (IN: In C (map gof T)), C gc = None).
  {
  intros.
  apply foldg_None with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.

  left.
  assumption.
  }

  assert (Cgc: C gc = None).
  {
  apply c0gc.
  assumption.
  }

  assert (Cilgc: ghplus Cinv Cleak gc = None).
  {
  intros.
  apply foldg_None with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.

  right.
  reflexivity.
  }

  assert (Cigc: Cinv gc = None).
  {
  apply ghplus_None with Cleak.
  assumption.
  }

  assert (Clgc: Cleak gc = None).
  {
  apply ghplus_None' with Cinv.
  assumption.
  }

  assert (EQHid: map (fun x => (pof x, snd x)) (updl T id (tt, tx, p, O, upd Z.eq_dec C gc (Some (Some 0, 0)), id)) =
    map (fun x => (pof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQH: map pof (updl T id (tt, tx, p, O, upd Z.eq_dec C gc (Some (Some 0, 0)), id)) = map pof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (ghpdefp0il: forall p0 : gheap, In p0 (map gof T) -> ghplusdef p0 (ghplus Cinv Cleak)).
  {
  intros.
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  }

  assert (ghpdefp0cu: forall p0 id', id <> id' ->
    In (p0, id') (map (fun x => (gof x, snd x)) T) ->
    ghplusdef p0 (upd Z.eq_dec C gc (Some (Some 0, 0)))).
  {
  intros.
  apply ghpdef_comm.
  apply ghpdef_v.
  apply DEFLg with id id'.
  omega.
  assumption.
  assumption.
  apply c0gc.
  apply in_map_iff in H0.
  destruct H0 as (x,(EQx,INx)).
  inversion EQx.
  apply in_map_iff.
  exists x.
  auto.
  }

  assert (ghpdefcuil: ghplusdef (upd Z.eq_dec C gc (Some (Some 0, 0))) Cinv /\ ghplusdef (upd Z.eq_dec C gc (Some (Some 0, 0))) Cleak).
  {
  unfold ghplusdef.
  split.
  intros.
  unfold upd.
  destruct (Z.eq_dec x gc).
  rewrite e.
  rewrite Cigc.
  trivial.
  apply GHPD.
  assumption.
  intros.
  unfold upd.
  destruct (Z.eq_dec x gc).
  rewrite e.
  rewrite Clgc.
  trivial.
  apply GHPD.
  assumption.
  }
  destruct ghpdefcuil as (ghpdefcui,ghpdefcul).

  assert (fold2gc: fold_left ghplus  (map gof (updl T id (tt, tx, p, O, upd Z.eq_dec C gc (Some (Some 0, 0)), id)))
    (ghplus Cinv Cleak) gc = (Some (Some 0, 0))).
  {
  apply fold_ctr; repeat php_.
  apply gofs.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  split.
  unfold gof.
  simpl.
  unfold upd.
  rewrite eqz.
  reflexivity.
  reflexivity.
  }

  assert (EQG: forall gc' (NEQ: gc' <> gc),
    fold_left ghplus  (map gof (updl T id (tt, tx, p, O, upd Z.eq_dec C gc (Some (Some 0, 0)), id))) (ghplus Cinv Cleak) gc' =
    fold_left ghplus  (map gof T) (ghplus Cinv Cleak) gc').
  {
  intros.
  apply eqg_heap with (z:=gc) (p:=C) (v:=Some (Some 0, 0)); repeat php_.
  apply gofs.
  omega.
  }

  assert (EQC: forall v, filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof (updl T id (tt, tx, p, O, upd Z.eq_dec C gc (Some (Some 0, 0)), id))) = filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)).
  {
  intros.
  symmetry.
  apply filter_updl_eq.
  repeat dstr_.
  unfold elem.
  intros.
  apply filter_In in IN.
  destruct IN as (INx',EQx').
  apply Z.eqb_eq in EQx'.
  destruct x' as (((((c1,tx1),p1),O1),C1),id1).
  assert (EQA: ((((c1,tx1),p1),O1),C1) = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- EQx'.
  assumption.
  }
  rewrite EQA.
  unfold cmdof.
  simpl.
  destruct ((opZ_eq_dec None (Some v))).
  inversion e.
  reflexivity.
  }

  assert (EQWT: forall l, filterb (xOf (fun x => Lof x) locs) (Aof l)
    (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof (updl T id (tt, tx, p, O, upd Z.eq_dec C gc (Some (Some 0, 0)), id))))) =
    filterb (xOf (fun x => Lof x) locs) (Aof l)
    (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof T)))).
  {
  intros.
  unfold filterb.
  apply functional_extensionality.
  intros.
  rewrite EQC.
  reflexivity.
  }

  assert (EQAO: map Aoof (updl T id (tt, tx, p, O, upd Z.eq_dec C gc (Some (Some 0, 0)), id)) =
    map Aoof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; repeat php_.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQO: map oof (updl T id (tt, tx, p, O, upd Z.eq_dec C gc (Some (Some 0, 0)), id)) =
    map oof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; repeat php_.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  rewrite EQHid.
  rewrite EQH.
  rewrite EQAO.
  rewrite EQO.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  unfold inf_capacity in *.
  destruct INF1 as (x,INF1).

  destruct (Z_lt_dec gc x).
  exists (x+1)%Z.
  intros.
  destruct (Z.eq_dec y gc).
  omega.
  rewrite EQG.
  apply INF1.
  omega.
  assumption.
  exists (gc+1)%Z.
  intros.
  destruct (Z.eq_dec y gc).
  omega.
  rewrite EQG.
  apply INF1.
  omega.
  assumption.
  assumption.
  }

  exists.
  {
  split.
  {
  intros.
  eapply SPUR1 with (c:=c).
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  destruct (Z.eq_dec (snd y) id).
  unfold cmdof in EQy.
  rewrite <- EQy in WASW.
  inversion WASW.
  apply in_map_iff.
  exists y.
  auto.
  apply WASW.
  }
  assumption.
  }

  exists. tauto.
  exists.
  {
  split.
  {
  unfold updl.
  rewrite map_map.
  unfold defl.
  intros.
  apply in_map_iff in IN1.
  destruct IN1 as ((x1,id'),(EQx1,INx1)).
  simpl in *.
  destruct (Z.eq_dec id' id).
  unfold gof in EQx1.
  simpl in EQx1.
  inversion EQx1.
  apply in_map_iff in IN2.
  destruct IN2 as ((x2,id2'),(EQx2,INx2)).
  simpl in *.
  destruct (Z.eq_dec id2' id).
  unfold gof in EQx2.
  simpl in EQx2.
  inversion EQx2.
  omega.
  apply ghpdef_v.
  apply DEFLg with id id2.
  omega.
  assumption.
  apply in_map_iff.
  exists (x2, id2').
  rewrite EQx2.
  auto.
  apply c0gc.
  apply in_map_iff.
  exists (x2, id2').
  inversion EQx2.
  rewrite <- H3.
  auto.
  apply in_map_iff in IN2.
  destruct IN2 as ((x2,id2'),(EQx2,INx2)).
  simpl in *.
  destruct (Z.eq_dec id2' id).
  unfold gof in EQx2.
  simpl in EQx2.
  inversion EQx2.
  apply ghpdef_comm.
  apply ghpdef_v.
  apply DEFLg with id id1.
  omega.
  assumption.
  apply in_map_iff.
  exists (x1, id').
  auto.
  apply c0gc.
  apply in_map_iff.
  exists (x1, id').
  inversion EQx1.
  rewrite <- H3.
  auto.
  apply DEFLg with id1 id2.
  assumption.
  apply in_map_iff.
  exists (x1, id').
  auto.
  apply in_map_iff.
  exists (x2, id2').
  auto.
  }
  exists.
  unfold updl.
  rewrite map_map.
  intros.
  apply in_map_iff in IN.
  destruct IN as ((x,id2'),(EQx,INx)).
  simpl in *.
  destruct (Z.eq_dec id2' id).
  unfold gof in EQx.
  simpl in EQx.
  rewrite <- EQx.
  split.
  apply ghpdef_v.
  apply GHPD.
  assumption.
  assumption.
  apply ghpdef_v.
  apply GHPD.
  assumption.
  assumption.
  apply GHPD.
  apply in_map_iff.
  exists (x, id2').
  auto.
  split.
  assumption.
  unfold boundgh.
  intros.
  destruct (Z.eq_dec x gc).
  rewrite e in H.
  rewrite fold2gc in H.
  inversion H.
  omega.
  rewrite EQG in H.
  unfold boundgh in BGT.
  apply BGT with x.
  assumption.
  assumption.
  }
  exists.
  {
  apply NoDup_updl.
  assumption.
  }
  exists.
  {
  split. assumption.
  split. assumption.
  split.
  intros.
  rewrite EQWT.
  apply INAOK;
  assumption.
  assumption.
  }
  exists. tauto.
  exists.
  {
  split. assumption.
  split. assumption.
  assumption.
  }
  exists.
  {
  intros.
  rewrite EQWT.
  apply WTsOTsOK.
  assumption.
  }
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as ((x,id2'),(EQx,INx)).
  simpl in *.
  destruct (Z.eq_dec id2' id).
  {
  symmetry in EQx.
  inversion EQx.
  split. unfold wellformed. tauto.
  split.

  eapply sat_weak_imp1; try assumption.
  apply boundgh_upd; repeat php_.
  intros.
  inversion H.
  omega.
  apply SAT.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  }
  destruct x as ((((c1,tx1),p1),O1),C1).
  symmetry in EQx.
  inversion EQx.
  assert (tmp:=INx).
  apply SOBS in tmp.
  destruct tmp as (WF1,(SAT1,SOBS1)).
  split. assumption.
  split.

  assert (bp0: boundph p1).
  {
  apply BPE.
  apply in_map_iff.
  exists (c1, tx1, p1, O1, C1, id2').
  split. reflexivity. assumption.
  }

  assert (bg0: boundgh C1).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  left.
  apply in_map_iff.
  exists (c1, tx1, p1, O1, C1, id2').
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  apply SAT1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  apply SOBS1 in W4COND.
  destruct W4COND as (v,(l,(inv,(eqv,(eql,sobs1))))).
  exists v, l, inv, eqv, eql.
  rewrite EQWT.
  assumption.
Qed.


Lemma g_ctrdec_preserves_validity0:
  forall m sp h T id tx p O C invs Cinv Cleak gc t1 m1
         (INT: In (nop, tx, p, O, C, id) T)
         (Cgc: C ([[gc]]) = Some (Some (S t1),S m1))
         (SAT: sat p (Some O) (upd Z.eq_dec C ([[gc]]) (Some (Some t1,m1))) (weakest_pre_ct (S m) sp (tt, tx) invs))
         (VALID: validk0 (S m) sp T Cinv Cleak h invs),
    validk0 m sp (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some t1,m1)), id)) Cinv Cleak h invs.
Proof.
  intros.
  unfold validk0 in VALID.
  destruct VALID as (locs,(Pinv,(Pleak,(Ainv,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS))))))))))))).
  unfold validk0.
  unfold pheaps_heap in *.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  unfold locations_ok in *.
  destruct LOCsOK as (INJ,(LCOM,(LOCs,OBsOK))).
  unfold invs_ok in *.
  destruct INVsOK as (NDPA,(AinvOK,(INAOK,SATAOK))).
  unfold locks_ok.
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.
  unfold validk0.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (inc: In C (map gof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (incid: In (C, id) (map (fun x => (gof x, snd x)) T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (inp: In p (map pof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (bp: boundph p).
  {
  apply BPE.
  assumption.
  }

  assert (bc: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  left.
  assumption.
  }

  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.

  exists locs, Pinv, Pleak, Ainv.

  assert (p0gc: forall id' C' o n (NEQ: id' <> id) 
    (IN: In (C',id') (map (fun x => (gof x, snd x)) T))
    (C'gc: C' ([[gc]]) = Some (o,n)), o = None).
  {
  intros.
  assert (ghpdefcc': ghplusdef C C').
  {
  apply DEFLg with id id'.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  assumption.
  }
  unfold ghplusdef in ghpdefcc'.
  specialize ghpdefcc' with ([[gc]]).
  rewrite Cgc in ghpdefcc'.
  rewrite C'gc in ghpdefcc'.
  destruct o.
  contradiction.
  reflexivity.
  }

  assert (Cinvgc: forall o n (C'gc: Cinv ([[gc]]) = Some (o,n)), o = None).
  {
  intros.
  assert (ghpdefcci: ghplusdef C Cinv).
  {
  apply GHPD.
  assumption.
  }
  unfold ghplusdef in ghpdefcci.
  specialize ghpdefcci with ([[gc]]).
  rewrite Cgc in ghpdefcci.
  rewrite C'gc in ghpdefcci.
  destruct o.
  contradiction.
  reflexivity.
  }

  assert (Cleakgc: forall o n (C'gc: Cleak ([[gc]]) = Some (o,n)), o = None).
  {
  intros.
  assert (ghpdefcci: ghplusdef C Cleak).
  {
  apply GHPD.
  assumption.
  }
  unfold ghplusdef in ghpdefcci.
  specialize ghpdefcci with ([[gc]]).
  rewrite Cgc in ghpdefcci.
  rewrite C'gc in ghpdefcci.
  destruct o.
  contradiction.
  reflexivity.
  }

  assert (ghpdefcup': forall p' id' (NEQ: id <> id')
    (IN: In (p',id') (map (fun x => (gof x, snd x)) T)),
    ghplusdef p' (upd Z.eq_dec C ([[gc]]) (Some (Some t1, m1)))).
  {
  unfold ghplusdef.
  unfold upd.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e.
  destruct (p' ([[gc]])) eqn:p2gc.
  destruct p0.
  apply p0gc with (id':=id') in p2gc.
  rewrite p2gc.
  trivial.
  omega.
  assumption.
  trivial.
  assert (ghpdefcp2: ghplusdef C p').
  {
  apply DEFLg with id id'.
  omega.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  assumption.
  }
  apply ghpdef_comm in ghpdefcp2.
  apply ghpdefcp2.
  }

  assert (ghpdefcui: ghplusdef (upd Z.eq_dec C ([[gc]]) (Some (Some t1, m1))) Cinv).
  {
  unfold ghplusdef.
  unfold upd.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e.
  destruct (Cinv ([[gc]])) eqn:p2gc.
  destruct p0.
  rewrite Cinvgc with o n.
  trivial.
  reflexivity.
  trivial.
  apply GHPD.
  assumption.
  }

  assert (ghpdefcul: ghplusdef (upd Z.eq_dec C ([[gc]]) (Some (Some t1, m1))) Cleak).
  {
  unfold ghplusdef.
  unfold upd.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e.
  destruct (Cleak ([[gc]])) eqn:p2gc.
  destruct p0.
  rewrite Cleakgc with o n.
  trivial.
  reflexivity.
  trivial.
  apply GHPD.
  assumption.
  }

  assert (EQHI: map (fun x => (pof x, snd x)) (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some t1, m1)), id)) =
    map (fun x => (pof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQH: map pof (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some t1, m1)), id)) =
    map pof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (ghpdefp0il: forall p0 : gheap, In p0 (map gof T) -> ghplusdef p0 (ghplus Cinv Cleak)).
  {
  intros.
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  }

  assert (fold1gc: exists t2 m2, fold_left ghplus (map gof T) (ghplus Cinv Cleak) ([[gc]]) = Some (Some (S t2), S m2)).
  {
  eapply fold_ctr_some with (x:=(nop, tx, p, O, C, id)); repeat php_.
  apply gofs.
  exists t1, m1.
  assumption.
  }
  destruct fold1gc as (t2,(m2,fold1gc)).

  assert (fold2gc: fold_left ghplus (map gof (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some t1, m1)), id)))
    (ghplus Cinv Cleak) ([[gc]]) = (Some (Some t2, m2))).
  {
  apply fold_ctr_dec with (C:=C) (t1:=t1) (m1:=m1); repeat php_.
  apply gofs.
  auto.
  }

  assert (EQG: forall gc' (NEQ: gc' <> ([[gc]])),
    fold_left ghplus  (map gof (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some t1, m1)), id))) (ghplus Cinv Cleak) gc' =
    fold_left ghplus  (map gof T) (ghplus Cinv Cleak) gc').
  {
  intros.
  apply eqg_heap with (z:=([[gc]])) (p:=C) (v:=Some (Some t1, m1)); repeat php_.
  apply gofs.
  omega.
  }

  assert (EQC: forall v, filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some t1, m1)), id))) = filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)).
  {
  intros.
  symmetry.
  apply filter_updl_eq.
  repeat dstr_.
  unfold elem.
  intros.
  apply filter_In in IN.
  destruct IN as (INx',EQx').
  apply Z.eqb_eq in EQx'.
  destruct x' as (((((c1,tx1),p1),O1),C1),id1).
  assert (EQA: ((((c1,tx1),p1),O1),C1) = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- EQx'.
  assumption.
  }
  rewrite EQA.
  unfold cmdof.
  simpl.
  destruct ((opZ_eq_dec None (Some v))).
  inversion e.
  reflexivity.
  }

  assert (EQWT: forall l, filterb (xOf (fun x => Lof x) locs) (Aof l)
    (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some t1, m1)), id))))) =
    filterb (xOf (fun x => Lof x) locs) (Aof l)
    (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof T)))).
  {
  intros.
  unfold filterb.
  apply functional_extensionality.
  intros.
  rewrite EQC.
  reflexivity.
  }

  assert (EQAO: map Aoof (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some t1, m1)), id)) =
    map Aoof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; repeat php_.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQO: map oof (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some t1, m1)), id)) =
    map oof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; repeat php_.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  rewrite EQHI.
  rewrite EQH.
  rewrite EQAO.
  rewrite EQO.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  unfold inf_capacity in *.
  destruct INF1 as (x,INF1).
  exists x.
  intros.
  apply INF1 in LE.
  destruct (Z.eq_dec y ([[gc]])).
  rewrite e in LE.
  rewrite fold1gc in LE.
  inversion LE.
  rewrite EQG.
  assumption.
  assumption.
  assumption.
  }
  exists.
  {
  split.
  {
  intros.
  eapply SPUR1 with (c:=c).
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  destruct (Z.eq_dec (snd y) id).
  unfold cmdof in EQy.
  rewrite <- EQy in WASW.
  inversion WASW.
  apply in_map_iff.
  exists y.
  auto.
  apply WASW.
  }
  assumption.
  }

  exists. tauto.
  exists.
  {
  split.
  {
  unfold updl.
  rewrite map_map.
  unfold defl.
  intros.
  apply in_map_iff in IN1.
  destruct IN1 as ((x1,id'),(EQx1,INx1)).
  simpl in *.
  destruct (Z.eq_dec id' id).
  unfold gof in EQx1.
  simpl in EQx1.
  inversion EQx1.
  apply in_map_iff in IN2.
  destruct IN2 as ((x2,id2'),(EQx2,INx2)).
  simpl in *.
  destruct (Z.eq_dec id2' id).
  unfold gof in EQx2.
  simpl in EQx2.
  inversion EQx2.
  omega.
  {
  apply ghpdef_comm.
  apply ghpdefcup' with id2'.
  omega.
  apply in_map_iff.
  exists (x2, id2').
  inversion EQx2.
  rewrite <- H3.
  auto.
  }
  apply in_map_iff in IN2.
  destruct IN2 as ((x2,id2'),(EQx2,INx2)).
  simpl in *.
  destruct (Z.eq_dec id2' id).
  unfold gof in EQx2.
  simpl in EQx2.
  inversion EQx2.
  apply ghpdefcup' with id'.
  omega.
  apply in_map_iff.
  exists (x1, id').
  inversion EQx1.
  rewrite <- H3.
  auto.
  apply DEFLg with id1 id2.
  assumption.
  apply in_map_iff.
  exists (x1, id').
  auto.
  apply in_map_iff.
  exists (x2, id2').
  auto.
  }
  exists.
  {
  unfold updl.
  rewrite map_map.
  intros.
  apply in_map_iff in IN.
  destruct IN as ((x,id2'),(EQx,INx)).
  simpl in *.
  destruct (Z.eq_dec id2' id).
  unfold gof in EQx.
  simpl in EQx.
  rewrite <- EQx.
  split. assumption.
  assumption.
  apply GHPD.
  rewrite <- EQx.
  apply in_map.
  assumption.
  }
  split. assumption.
  unfold boundgh.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e in H.
  rewrite fold2gc in H.
  inversion H.
  unfold boundgh in BGT.
  apply BGT in fold1gc.
  omega.
  rewrite EQG in H.
  apply BGT in H.
  assumption.
  assumption.
  }
  exists.
  {
  apply NoDup_updl.
  assumption.
  }
  exists.
  {
  split. assumption.
  split. assumption.
  split.
  intros.
  rewrite EQWT.
  apply INAOK; assumption. assumption.
  }
  exists. tauto.
  exists. tauto.
  exists. intros. rewrite EQWT. apply WTsOTsOK; assumption.
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as ((x,id2'),(EQx,INx)).
  simpl in *.
  destruct (Z.eq_dec id2' id).
  {
  symmetry in EQx.
  inversion EQx.
  split. unfold wellformed. tauto.
  split.
  assert (bg: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  left.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id) .
  split. reflexivity. assumption.
  }

  assert (bgu: boundgh (upd Z.eq_dec C ([[gc]]) (Some (Some t1, m1)))).
  {
  apply boundgh_upd; repeat php_.
  intros.
  inversion H.
  unfold boundgh in bg.
  apply bg in Cgc.
  omega.
  }
  eapply sat_weak_imp1; try assumption.
  apply SAT.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  }
  destruct x as ((((c1,tx1),p1),O1),C1).
  symmetry in EQx.
  inversion EQx.
  assert (tmp:=INx).
  apply SOBS in tmp.
  destruct tmp as (WF1,(SAT1,SOBS1)).
  split. assumption.
  split.
  assert (bp0: boundph p1).
  {
  apply BPE.
  apply in_map_iff.
  exists (c1, tx1, p1, O1, C1, id2').
  split. reflexivity. assumption.
  }

  assert (bg0: boundgh C1).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  left.
  apply in_map_iff.
  exists (c1, tx1, p1, O1, C1, id2').
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  apply SAT1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  apply SOBS1 in W4COND.
  destruct W4COND as (v,(l,(inv,(eqv,(eql,sobs1))))).
  exists v, l, inv, eqv, eql.
  rewrite EQWT.
  assumption.
Qed.


Lemma nop_preserves_validity0:
  forall m sp h T id tx p O C invs Cinv Cleak
         (INT: In (nop, tx, p, O, C, id) T)
         (SAT: sat p (Some O) C (weakest_pre_ct (S m) sp (tt, tx) invs))
         (VALID: validk0 (S m) sp T Cinv Cleak h invs),
    validk0 m sp (updl T id (tt, tx, p, O, C, id)) Cinv Cleak h invs.
Proof.
  intros.
  unfold validk0 in VALID.
  destruct VALID as (locs,(Pinv,(Pleak,(Ainv,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS))))))))))))).
  unfold validk0.
  unfold pheaps_heap in *.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  unfold locations_ok in *.
  destruct LOCsOK as (INJ,(LCOM,(LOCs,OBsOK))).
  unfold invs_ok in *.
  destruct INVsOK as (NDPA,(AinvOK,(INAOK,SATAOK))).
  unfold locks_ok.
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.
  unfold validk0.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (inc: In C (map gof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (incid: In (C, id) (map (fun x => (gof x, snd x)) T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (inp: In p (map pof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  auto.
  }

  assert (bp: boundph p).
  {
  apply BPE.
  assumption.
  }

  assert (bc: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  left.
  assumption.
  }

  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.

  exists locs, Pinv, Pleak, Ainv.

  assert (EQHI: map (fun x => (pof x, snd x)) (updl T id (tt, tx, p, O, C, id)) =
    map (fun x => (pof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQH: map pof (updl T id (tt, tx, p, O, C, id)) = map pof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (ghpdefp0il: forall p0 : gheap, In p0 (map gof T) -> ghplusdef p0 (ghplus Cinv Cleak)).
  {
  intros.
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  }

  assert (EQGI: map (fun x => (gof x, snd x)) (updl T id (tt, tx, p, O, C, id)) =
    map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQG: map gof (updl T id (tt, tx, p, O, C, id)) = map gof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQC: forall v, filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof (updl T id (tt, tx, p, O, C, id))) = filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)).
  {
  intros.
  symmetry.
  apply filter_updl_eq.
  repeat dstr_.
  unfold elem.
  intros.
  apply filter_In in IN.
  destruct IN as (INx',EQx').
  apply Z.eqb_eq in EQx'.
  destruct x' as (((((c1,tx1),p1),O1),C1),id1).
  assert (EQA: ((((c1,tx1),p1),O1),C1) = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- EQx'.
  assumption.
  }
  rewrite EQA.
  unfold cmdof.
  simpl.
  destruct ((opZ_eq_dec None (Some v))).
  inversion e.
  reflexivity.
  }

  assert (EQWT: forall l, filterb (xOf (fun x => Lof x) locs) (Aof l)
    (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof (updl T id (tt, tx, p, O, C, id))))) =
    filterb (xOf (fun x => Lof x) locs) (Aof l)
    (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof T)))).
  {
  intros.
  unfold filterb.
  apply functional_extensionality.
  intros.
  rewrite EQC.
  reflexivity.
  }

  assert (EQAO: map Aoof (updl T id (tt, tx, p, O, C, id)) =
    map Aoof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; repeat php_.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQO: map oof (updl T id (tt, tx, p, O, C, id)) =
    map oof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (nop, tx, p, O, C)).
  {
  apply unique_key_eq with T id; repeat php_.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  rewrite EQHI.
  rewrite EQH.
  rewrite EQGI.
  rewrite EQG.
  rewrite EQAO.
  rewrite EQO.

  exists. assumption.
  exists.
  {
  split.
  {
  intros.
  eapply SPUR1 with (c:=c).
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  destruct (Z.eq_dec (snd y) id).
  unfold cmdof in EQy.
  rewrite <- EQy in WASW.
  inversion WASW.
  apply in_map_iff.
  exists y.
  auto.
  apply WASW.
  }
  assumption.
  }

  exists. tauto.
  exists.
  {
  split. assumption.
  split. assumption.
  split; assumption.
  }
  exists. apply NoDup_updl. assumption.
  exists.
  {
  split. assumption.
  split. assumption.
  split.
  intros.
  rewrite EQWT.
  apply INAOK; assumption. assumption.
  }
  exists. tauto.
  exists. tauto.
  exists. intros. rewrite EQWT. apply WTsOTsOK; assumption.
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as ((x,id2'),(EQx,INx)).
  simpl in *.
  destruct (Z.eq_dec id2' id).
  {
  symmetry in EQx.
  inversion EQx.
  split. unfold wellformed. tauto.
  split.
  assert (bg: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  left.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id) .
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  apply SAT.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  }
  destruct x as ((((c1,tx1),p1),O1),C1).
  symmetry in EQx.
  inversion EQx.
  assert (tmp:=INx).
  apply SOBS in tmp.
  destruct tmp as (WF1,(SAT1,SOBS1)).
  split. assumption.
  split.
  assert (bp0: boundph p1).
  {
  apply BPE.
  apply in_map_iff.
  exists (c1, tx1, p1, O1, C1, id2').
  split. reflexivity. assumption.
  }

  assert (bg0: boundgh C1).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  left.
  apply in_map_iff.
  exists (c1, tx1, p1, O1, C1, id2').
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  apply SAT1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  apply SOBS1 in W4COND.
  destruct W4COND as (v,(l,(inv,(eqv,(eql,sobs1))))).
  exists v, l, inv, eqv, eql.
  rewrite EQWT.
  assumption.
Qed.

Definition validk1 (n: nat) (sp: bool) (t:thrds) (h:heap) :=
  exists (T: list (cmd * context * pheap * list (olocation Z) * gheap * Z)) (invs: Z -> inv)
         (TOK: forall id c tx, t id = Some (c,tx) <-> exists p O g, In (c,tx,p,O,g,id) T)
         (INF: inf_capacity t)
         (Ginv Gleak: gheap),
    validk0 n sp T Ginv Gleak h invs.

Lemma nop_preserves_validity1:
  forall m sp h t id tx
         (CMD: t id = Some (nop, tx))
         (VALID1: validk1 (S m) sp t h),
    validk1 m sp (upd Z.eq_dec t id (Some (tt, tx))) h.
Proof.
  intros.
  destruct VALID1 as (T,(invs,(TOK,(INF,(Cinv,(Cleak,VALID)))))).
  assert (valid':=VALID).
  unfold validk0 in VALID.
  destruct VALID as (locs,(Pinv,(Pleak,(Ainv,(INF1,((SPUR1,SPUR2),(PHsOK,(GHsOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS))))))))))))).
  assert (tmp: exists p O C, In (nop, tx, p, O, C, id) T).
  {
  apply TOK.
  assumption.
  }

  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(SAT,rest)).
  unfold validk1.
  destruct SAT as [SAT|g_chrgu].
  destruct SAT as [SAT|g_chrg].
  destruct SAT as [SAT|g_dischu].
  destruct SAT as [SAT|g_disch].
  destruct SAT as [SAT|g_ctrinc].
  destruct SAT as [SAT|g_ctrdec].
  destruct SAT as [SAT|g_newctr].
  destruct SAT as [SAT|g_finlc].
  destruct SAT as [SAT|g_initc].
  destruct SAT as [NOP|g_initl].
  {
  simpl in NOP.
  exists (updl T id (tt, tx, p, O, C, id)), invs.
  exists.
  intros.
  apply upd_updl; try assumption.
  exists (nop, tx, p, O, C). assumption.
  exists.
  apply steps_preserve_inf_capacity1 with sp t h h; try assumption.
  apply red_nop; assumption.
  exists Cinv, Cleak.
  apply nop_preserves_validity0; try assumption.
  apply NOP.
  }

  {
  apply sat_initl in g_initl.
  destruct g_initl as (ll,(p1,(p2,(wt,(ot,(C1,(C2,(i,(l,(GHPDC1C2,(eql0,(bp1,(bp2,(phpdefp1p2,
    (p1p2,(C1C2,(p1l,(satp2,SAT)))))))))))))))))).
  exists (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p1 ll None)
      (Oof ll, i, Mof ll, M'of ll) (Some Lock), O, C1, id)).
  exists invs.
  exists.
  intros.
  apply upd_updl; try assumption.
  exists (nop, tx, p, O, C).
  assumption.
  exists.
  apply steps_preserve_inf_capacity1 with sp t h h; try assumption.
  apply red_nop; assumption.
  exists (ghplus Cinv C2), Cleak.
  apply g_initl_preserves_validity0 with p C p2 wt ot l; try assumption.
  {
  unfold locations_ok in *.
  destruct LOCsOK as (LOCsOK,rest1).
  unfold injph in LOCsOK.
  unfold injph.
  unfold pheaps_heap in PHsOK.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.
  intros.
  apply LOCsOK; try assumption.
  {
  apply fold_some; repeat php_.
  apply pofs.
  intros.
  apply phpdef_pair; try assumption.
  apply PHPD; try assumption.
  apply PHPD; try assumption.
  exists p.
  exists.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  split. reflexivity. assumption. assumption.
  }
  {
  apply fold_some; repeat php_.
  apply pofs.
  intros.
  apply phpdef_pair; try assumption.
  apply PHPD; try assumption.
  apply PHPD; try assumption.
  exists p.
  exists.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  split. reflexivity. assumption. assumption.
  }
  }
  }
  {
  apply sat_initc in g_initc.
  destruct g_initc as (ll,(ml,(m'l,(lk,(wt,(ot,(l,(eql,(pl,(plk,SAT)))))))))).
  exists (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p ll None) ((Aof ll, Rof ll, Aof lk, Xof ll, Pof ll), Iof ll, ml, m'l) (Some Icond), O, C, id)).
  exists invs.
  exists.
  intros.
  apply upd_updl; try assumption.
  exists (nop, tx, p, O, C).
  assumption.
  exists.
  apply steps_preserve_inf_capacity1 with sp t h h; try assumption.
  apply red_nop; assumption.
  exists Cinv, Cleak.
  apply g_initc_preserves_validity0 with wt ot l; try assumption.
  {
  unfold locations_ok in *.
  destruct LOCsOK as (LOCsOK,rest1).
  unfold injph in LOCsOK.
  unfold injph.
  unfold pheaps_heap in PHsOK.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.
  intros.
  apply LOCsOK; try assumption.
  {
  apply fold_some; repeat php_.
  apply pofs.
  intros.
  apply phpdef_pair; try assumption.
  apply PHPD; try assumption.
  apply PHPD; try assumption.
  exists p.
  exists.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  split. reflexivity. assumption. assumption.
  }
  {
  apply fold_some; repeat php_.
  apply pofs.
  intros.
  apply phpdef_pair; try assumption.
  apply PHPD; try assumption.
  apply PHPD; try assumption.
  exists p.
  exists.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  split. reflexivity. assumption. assumption.
  }
  }
  }

  {
  apply sat_g_finlc in g_finlc.
  destruct g_finlc as (lv,(lk,(v,(aolv,(loflv,(plv,(plk,(spurlv,sat1)))))))).
  exists (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p lv (Some Cond), O, C, id)).
  exists invs. exists. intros.
  apply upd_updl; try assumption.
  exists (nop, tx, p, O, C). assumption.
  exists.
  apply steps_preserve_inf_capacity1 with sp t h h; try assumption.
  apply red_nop; assumption.
  exists Cinv, Cleak.
  apply g_finlc_preserves_validity0 with lk v; try assumption.
  }

  {
  assert (tmp: exists gc, fold_left ghplus (map gof T) (ghplus Cinv Cleak) gc = None).
  {
  destruct INF1 as (INF1,INF2).
  unfold inf_capacity in INF1.
  destruct INF1 as (x,inf1).
  exists (x+1)%Z.
  apply inf1.
  omega.
  }
  destruct tmp as (gc,fgc).

  unfold pheaps_heap in PHsOK.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (INP: In p (map pof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id). split. reflexivity. assumption.
  }

  assert (INC: In C (map gof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id). split. reflexivity. assumption.
  }

  assert (bp: boundph p).
  {
  apply BPE; try assumption.
  }

  assert (bg: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  assert (c0gc: forall C (IN: In C (map gof T)), C gc = None).
  {
  intros.
  apply foldg_None with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  left.
  assumption.
  }

  assert (Cgc: C gc = None).
  {
  apply c0gc.
  assumption.
  }

  apply sat_g_newctr with (gc:=gc) in g_newctr; try assumption.
  exists (updl T id (tt, tx, p, O, upd Z.eq_dec C gc (Some (Some 0, 0)), id)).
  exists invs. exists. intros.
  apply upd_updl; try assumption.
  exists (nop, tx, p, O, C). assumption.
  exists.
  apply steps_preserve_inf_capacity1 with sp t h h; try assumption.
  apply red_nop; assumption.
  exists Cinv, Cleak.
  apply g_newctr_preserves_validity0; try assumption.
  }

  {
  unfold pheaps_heap in PHsOK.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (INP: In p (map pof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id). split. reflexivity. assumption.
  }

  assert (INC: In C (map gof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id). split. reflexivity. assumption.
  }

  assert (bp: boundph p).
  {
  apply BPE; try assumption.
  }

  assert (bg: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  apply sat_g_ctrdec in g_ctrdec; try assumption.
  destruct g_ctrdec as (gc,(t1,(m1,(Cgc,sat1)))).
  exists (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some t1,m1)), id)).
  exists invs. exists. intros.
  apply upd_updl; try assumption.
  exists (nop, tx, p, O, C). assumption.
  exists.
  apply steps_preserve_inf_capacity1 with sp t h h; try assumption.
  apply red_nop; assumption.
  exists Cinv, Cleak.
  apply g_ctrdec_preserves_validity0; try assumption.
  }

  {
  unfold pheaps_heap in PHsOK.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (INP: In p (map pof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id). split. reflexivity. assumption.
  }

  assert (INC: In C (map gof T)).
  {
  apply in_map_iff.
  exists (nop, tx, p, O, C, id). split. reflexivity. assumption.
  }

  assert (bp: boundph p).
  {
  apply BPE; try assumption.
  }

  assert (bg: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (nop, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  apply sat_g_ctrinc in g_ctrinc; try assumption.
  destruct g_ctrinc as (t1,(m1,(gc,(Cgc,SAT)))).
  exists (updl T id (tt, tx, p, O, upd Z.eq_dec C ([[gc]]) (Some (Some (S t1), S m1)), id)).
  exists invs.
  exists.
  intros.
  apply upd_updl; try assumption.
  exists (nop, tx, p, O, C).
  assumption.
  exists.
  apply steps_preserve_inf_capacity1 with sp t h h; try assumption.
  apply red_nop; assumption.
  exists Cinv, Cleak.
  apply g_ctrinc_preserves_validity0; try assumption.
  }

  {
  apply sat_disch in g_disch.
  destruct g_disch as (wt,(ot,(O1,(lv,(ll,(v,(O1eq,(eqlv,(eqll,(pl,(pv,(INO,(SAFE,SAT))))))))))))).
  exists (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll
    (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))), O1, C, id)).
  exists invs. exists. intros.
  apply upd_updl; try assumption.
  exists (nop, tx, p, O, C). assumption.
  exists.
  apply steps_preserve_inf_capacity1 with sp t h h; try assumption.
  apply red_nop; assumption.
  exists Cinv, Cleak.
  apply g_disch_preserves_validity0 with O lv; try assumption.
  }

  {
  apply sat_dischu in g_dischu.
  destruct g_dischu as (wt,(ot,(O1,(lv,(ll,(v,(O1eq,(eqlv,(eqll,(pl,(pv,(INO,(SAFE,SAT))))))))))))).
  exists (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll
    (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)))), O1, C, id)).
  exists invs. exists. intros.
  apply upd_updl; try assumption.
  exists (nop, tx, p, O, C). assumption.
  exists.
  apply steps_preserve_inf_capacity1 with sp t h h; try assumption.
  apply red_nop; assumption.
  exists Cinv, Cleak.
  apply g_dischu_preserves_validity0 with O lv; try assumption.
  }

  {
  apply sat_chrg in g_chrg.
  destruct g_chrg as (wt,(ot,(lv,(ll,(v,(eqlv,(eqll,(pl,(pv,SAT))))))))).
  exists (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll
    (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))), Oof lv::O, C, id)).
  exists invs. exists. intros.
  apply upd_updl; try assumption.
  exists (nop, tx, p, O, C). assumption.
  exists.
  apply steps_preserve_inf_capacity1 with sp t h h; try assumption.
  apply red_nop; assumption.
  exists Cinv, Cleak.
  apply g_chrg_preserves_validity0; try assumption.
  }

  {
  apply sat_chrgu in g_chrgu.
  destruct g_chrgu as (wt,(ot,(lv,(ll,(v,(eqlv,(eqll,(pl,(pv,SAT))))))))).
  exists (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll
    (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)))), Oof lv::O, C, id)).
  exists invs. exists. intros.
  apply upd_updl; try assumption.
  exists (nop, tx, p, O, C). assumption.
  exists.
  apply steps_preserve_inf_capacity1 with sp t h h; try assumption.
  apply red_nop; assumption.
  exists Cinv, Cleak.
  apply g_chrgu_preserves_validity0; try assumption.
  }
Qed.


Lemma valid1_valid:
  forall m sp t h (VALID1: validk1 m sp t h),
    validk m sp t h.
Proof.
  intros.
  destruct VALID1 as (T,(invs,(TOK,(INF,(Ginv,(Gleak,VALID)))))).
  destruct VALID as (locs,(Pinv,(Pleak,(Ainv,((INF1,INF2),(SPUR,(PHsOK,(GHsOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS))))))))))))).
  unfold validk.
  exists T, invs, locs, Pinv, Pleak, Ainv, Ginv, Gleak.
  exists. split; try assumption.
  split; assumption.
  exists SPUR, PHsOK, GHsOK.
  exists. assumption.
  exists NDPT, INVsOK, LOCsOK, LOCKsOK, WTsOTsOK. 
  assumption.
Qed.


Lemma valid_valid1:
  forall m sp t h (VALID: validk m sp t h),
    validk1 m sp t h.
Proof.
  intros.
  destruct VALID as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,((INF1,(INF2,INF3)),(SPUR,(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
  unfold validk1.
  exists T,invs.
  exists. assumption.
  exists. assumption.
  unfold validk0.
  exists Cinv,Cleak,locs,Pinv,Pleak,Ainv.
  exists.
  split; assumption.
  exists SPUR,PHsOK,GHsOK,NDPT,INVsOK,LOCsOK,LOCKsOK,WTsOTsOK.
  assumption.
Qed.


Lemma nop_preserves_validity:
  forall m sp h t id tx
         (CMD: t id = Some (nop, tx))
         (VALID: validk (S m) sp t h),
    validk m sp (upd Z.eq_dec t id (Some (tt, tx))) h.
Proof.
  intros.
  apply valid1_valid.
  apply nop_preserves_validity1; try assumption.
  apply valid_valid1; assumption.
Qed.
