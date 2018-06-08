Require Import ZArith.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Init.Nat.
Require Import List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Util_Z.
Require Import Util_list.
Require Import Programs.
Require Import Assertions.
Require Import WeakestPrecondition.
Require Import ProofRules.
Require Import ValidityOfConfigurations.
Require Import Wait4Graph.
Require Import UnprovedLemmas.

Set Implicit Arguments.

Theorem initial_configuration_is_valid:
  forall c id invs
         (WELLFORMED: wellformed_cmd c)
         (VERIFIED: correct (Aobs nil) c (fun _ => Aobs nil) invs),
    validk (upd Z.eq_dec (emp (cmd * context)) id (Some (c,done))) (emp Z).
Proof.
  unfold correct.
  unfold validk.
  unfold pheaps_heap.
  unfold gheaps_ok.
  unfold locations_ok.
  unfold invs_ok.
  unfold locks_ok.

  intros.
  assert (SAT: sat (emp knowledge) (Some nil) (emp (option nat * nat)) (weakest_pre c (fun _ : Z => Aobs nil) Datatypes.id invs)). 
  apply VERIFIED.
  apply boundph_emp.
  apply boundgh_emp.
  simpl.
  apply fs_op.
  apply perm_nil.
  exists ((c,done,emp knowledge,nil,emp (option nat * nat),id)::nil).
  exists invs, nil, (emp knowledge), (emp knowledge), nil, (emp (option nat * nat)), (emp (option nat * nat)).
  simpl.
  exists.
  {
  unfold inf_capacity.
  split.
  exists (id+1)%Z.
  intros.
  unfold upd.
  destruct (Z.eq_dec y id).
  omega.
  reflexivity.
  split.
  exists (id+1)%Z.
  intros.
  unfold upd.
  destruct (Z.eq_dec y id).
  omega.
  reflexivity.
  exists 0%Z.
  reflexivity.
  }
  exists.
  {
  exists.
  {
  unfold defl.
  intros.
  simpl in IN1.
  destruct IN1 as [EQ|CO].
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  apply phpdef_comm.
  apply phpdef_emp.
  inversion CO.
  }
  exists.
  {
  apply phpdef_emp.
  }
  exists.
  {
  intros.
  split;
  apply phpdef_emp.
  }
  exists.
  {
  intros.
  destruct IN as [EQ|CO].
  unfold pof in EQ.
  simpl in EQ.
  rewrite <- EQ.
  apply boundph_emp.
  contradiction.
  }
  exists.
  apply boundph_emp.
  split.
  apply boundph_emp.
  split.
  apply boundph_emp.
  unfold pof.
  rewrite phplus_emp.
  split.
  apply boundph_emp.
  rewrite phplus_emp.
  unfold phtoh.
  split.
  reflexivity.
  intros.
  reflexivity.
  }
  exists.
  {
  exists.
  {
  unfold defl.
  intros.
  simpl in IN1.
  destruct IN1 as [EQ|CO].
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  apply ghpdef_comm.
  apply ghpdef_emp.
  inversion CO.
  }
  exists.
  {
  intros.
  split;
  apply ghpdef_emp.
  }
  exists.
  apply ghpdef_emp.
  rewrite ghplus_emp.
  apply boundgh_emp.
  }
  exists.
  {
  split.
  intros.
  exists (emp knowledge), nil, (emp (option nat * nat)).
  unfold upd in H.
  destruct (Z.eq_dec id0 id).
  inversion H.
  rewrite e.
  left.
  reflexivity.
  unfold emp in H.
  inversion H.
  intros.
  destruct H as (p,(o,(d,FAL))).
  destruct FAL as [EQ|FAL].
  inversion EQ.
  unfold upd.
  destruct (Z.eq_dec id0 id0).
  reflexivity.
  contradiction.
  contradiction.
  }
  exists.
  apply NoDup_cons.
  unfold not.
  intros.
  inversion H.
  apply NoDup_nil.
  exists.
  {
  exists.
  {
  apply NoDup_nil.
  }
  exists.
  {
  intros.
  contradiction.
  }  
  exists.
  {
  unfold emp.
  intros.
  inversion NOTHELD.
  }
  reflexivity.
  }
  exists.
  {
  exists.
  {
  unfold injph.
  simpl.
  intros.
  contradiction.
  }
  exists.
  {
  unfold xcomp.
  simpl.
  intros.
  contradiction.
  }
  exists.
  {
  unfold lcomp.
  simpl.
  intros.
  contradiction.
  }
  exists.
  {
  intros.
  unfold phplus.
  unfold pof.
  unfold emp.
  simpl.
  split.
  intros.
  contradiction.
  intros.
  contradiction.
  }
  intros.
  contradiction.
  }
  exists.
  {
  exists.
  {
  unfold phplus.
  unfold pof.
  unfold emp.
  simpl.
  intros.
  destruct LOCK as [LOCK|LOCK].
  inversion LOCK.
  destruct LOCK as (wt,(ot,CO)).
  destruct CO as [CO|CO];
  inversion CO.
  }
  unfold phplus.
  unfold pof.
  unfold emp.
  simpl.
  intros.
  inversion ULOCK.
  }
  exists.
  {
  simpl.
  intros.
  destruct ULOCKED as [CO|CO].
  inversion CO.
  inversion CO.
  }
  exists.
  {
  intros.
  destruct ING as [EQ|FAL].
  Focus 2.
  contradiction.
  inversion EQ.
  rewrite <- H0.
  unfold wellformed.
  simpl.
  auto.
  }
  destruct ING as [EQ|CO].
  {
  inversion EQ.
  rewrite <- H0.
  exists.
  {
  unfold weakest_pre_ct.
  simpl.
  assumption.
  }
  intros.
  rewrite W4COND in SAT.
  apply sat_wait4cond with (tx:=done) (p:=emp knowledge) in SAT.
  destruct SAT as (lv, (ll, (EQlv, (EQll, (EQemp, rest))))).
  inversion EQemp.
  }
  contradiction.
Qed.

Theorem valid_configuration_is_not_deadlock:
  forall t h (VALIDK: validk t h) (HAS_THREAD: exists id, t id <> None),
    exists id c (TID: t id = Some c), waiting_for h (fst c) = None.
Proof.
  unfold validk.
  intros.
  destruct VALIDK as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS))))))))))))))))).
  unfold validk.
  unfold pheaps_heap in *.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  unfold locations_ok in *.
  destruct LOCsOK as (INJ,(XCOM,(LCOM,(LOCs,OBsOK)))).
  unfold invs_ok in *.
  destruct INVsOK as (NDPA,(AinvOK,(INAOK,SATAOK))).
  unfold locks_ok.
  destruct LOCKsOK as (LOCKOK,ULOCKOK).
  rewrite map_map in *.
  simpl in *.
  change (fun x : cmd * context * pheap * list location * gheap * Z => pof x) with pof in *.

  destruct (In_dec opZ_eq_dec None (map (wof h) T)) as [IN|NIN].
  apply in_map_iff in IN.
  destruct IN as (x,(w4,INT)).
  destruct x as (((((c,ct),p),O),C),id).
  simpl in *.
  exists id, (c, ct).
  exists.
  apply TOK.
  exists p, O, C.
  assumption.
  assumption.

  assert (G1: exists (R: Z -> Z) (L: Z -> Z) (P: Z -> bool) (X: Z -> list Z)
         (ONE: forall z o O (IN: In (o,O,z) (map (fun x => (lift 0%Z (wof h x), oof x, snd x)) T)), one_ob (map (fun x => (fst (fst x), map (fun x => Aof x) (snd (fst x)), snd x)) (map (fun x => (lift 0%Z (wof h x), oof x, snd x)) T)) o)
         (SPARE: forall z o O (IN: In (o,O,z) (map (fun x => (lift 0%Z (wof h x), oof x, snd x)) T)) (Po: P o = true), spare_ob (map (fun x => (fst (fst x), map (fun x => Aof x) (snd (fst x)), snd x)) (map (fun x => (lift 0%Z (wof h x), oof x, snd x)) T)) o)
         (OWN: forall z o O (IN: In (o,O,z) (map (fun x => (lift 0%Z (wof h x), oof x, snd x)) T)) (INX: In (R o) (X (L o))), own_ob (map (fun x => (fst (fst x), map (fun x => Aof x) (snd (fst x)), snd x)) (map (fun x => (lift 0%Z (wof h x), oof x, snd x)) T)) o)
         (PRC: forall z o O (ING: In (o,O,z) (map (fun x => (lift 0%Z (wof h x), oof x, snd x)) T)), prc o (map (fun x => Aof x) O) R L P X = true), True).
  {
  apply validK_validG with locs;
  try tauto.
  {
  intros.
  unfold comp.
  intros.
  apply INJ.
  apply LOCs in IN.
  assumption.
  apply LOCs in IN0.
  assumption.
  }
  {
  intros.
  apply LOCs.
  apply OBsOK.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  apply in_map_iff in ING.
  destruct ING as (x,(EQx,INx)).
  exists x.
  inversion EQx.
  rewrite H1.
  tauto.
  }
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  inversion EQx.
  destruct (wof h x) eqn:wofhx.
  Focus 2.
  exfalso.
  apply NIN.
  apply in_map_iff.
  exists x.
  tauto.
  destruct x as (((((c,tx),p),Os),C),id).
  assert (WOFX:=wofhx).
  unfold wof in wofhx.
  simpl in *.
  apply waiting_for_lock_cond in wofhx.
  destruct wofhx as (e,(EQe,wofhx)).
  rewrite EQe in *.
  destruct wofhx as [WL|WC].
  {
  rewrite WL in *.
  assert (VT:=INx).
  apply SOBS in VT.
  destruct VT as (WF,(WP,VOS)).
  apply sat_wait4lock in WP.
  destruct WP as (ll, (EQll, (pll,prcll))).
  assert (LOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some Lock \/
    (exists wt ot : bag, fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked wt ot))).
  {
  apply fold_lock_ed;
  try tauto.
  apply pofs.
  intros.
  apply PHPD in IN.
  apply phpdef_pair;
  try tauto.
  right.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Waiting4lock e, tx, p, Os, C, id).
  tauto.
  assumption.
  }
  assert (G: Lof ll = Aof ll /\ Pof ll = false /\ ~ In (Rof ll) (Xof ll) /\
    (h (Aof ll) <> Some 1%Z -> In ll (concat (map oof T)))).
  {
  apply LOCKOK.
  destruct LOCKED.
  left.
  assumption.
  right.
  destruct H as (wt,(ot,L)).
  exists wt, ot.
  left.
  assumption.
  }
  destruct G as (g1,(g2,(g3,g4))).
  exists ll.
  exists.
  apply LOCs.
  destruct LOCKED as [L1|L1].
  rewrite L1.
  unfold not.
  intros.
  inversion H.
  destruct L1 as (wt,(ot,L1)).
  rewrite L1.
  unfold not.
  intros.
  inversion H.
  exists EQll.
  unfold safe_obs.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  {
  rewrite map_map.
  rewrite map_map.
  apply Coq.Bool.Bool.orb_true_iff.
  rewrite Nat.ltb_lt.
  rewrite Nat.eqb_eq.
  destruct (filter (fun x => ifb (Z.eq_dec x ([[e]])))
   (map (fun x => fst (fst (lift 0%Z (wof h x), oof x, snd x))) T)) eqn:FIL.
  left.
  simpl.
  reflexivity.
  assert (INz1: In z1 (filter (fun x => ifb (Z.eq_dec x ([[e]])))
   (map (fun x => fst (fst (lift 0%Z (wof h x), oof x, snd x))) T))).
  {
  rewrite FIL.
  left.
  reflexivity.
  }
  apply filter_In in INz1.
  destruct INz1 as (INz1,EQz1).
  unfold ifb in EQz1.
  destruct (Z.eq_dec z1 ([[e]])).
  Focus 2.
  inversion EQz1.
  rewrite e0 in *.
  right.
  rewrite <- EQll in *.
  apply in_map_iff in INz1.
  destruct INz1 as (x1,(EQx1,INx1)).
  simpl in *.
  apply count_occ_In.
  apply g4.
  unfold wof in WOFX.
  simpl in WOFX.
  destruct (opZ_eq_dec (h ([[e]])) (Some 1%Z)).
  inversion WOFX.
  rewrite EQll.
  assumption.
  }
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  {
  apply Coq.Bool.Bool.orb_true_iff.
  left.
  rewrite g2.
  reflexivity.
  }
  {
  apply Coq.Bool.Bool.orb_true_iff.
  left.
  destruct (in_dec Z.eq_dec (Rof ll) (Xof ll)).
  contradiction.
  reflexivity.
  }
  }
  destruct WC as (l,WC).
  rewrite WC in *.
  assert (VT:=INx).
  apply SOBS in VT.
  destruct VT as (WF,(WP,VOS)).
  apply sat_wait4cond in WP.
  destruct WP as (lv,(ll,(EQlv,(EQll,(plv,(pll,(lvl,(prcll,(prclv,sat1))))))))).

  specialize VOS with e l.
  pose proof (VOS eq_refl) as tmp.

  destruct tmp as (v,(l',(INv,(INl,(EQv,(EQL,SAFE)))))).
  exists v, INv, EQv.
  unfold wof.
  rewrite map_map.
  rewrite map_map.
  rewrite <- EQv in *.
  simpl.

  rewrite length_filter_map_eq with (m2:=cmdof) (f2:=(fun c : cmd =>
    ifb (opZ_eq_dec (waiting_for h c) (Some (Aof v))))).
  rewrite <- count_map_eq.
  {
  unfold WTs in SAFE.
  unfold OBs in SAFE.
  unfold filterb in SAFE.

  assert (CO2: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some Cond).
  {
  apply fold_cond;
  try tauto.
  apply pofs.
  intros.
  apply PHPD in IN.
  apply phpdef_pair;
  tauto.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Waiting4cond e l, tx, p, Os, C, id).
  tauto.
  assumption.
  }

  assert (CO3: fold_left phplus (map pof T) (phplus Pinv Pleak) lv = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) lv = Some (Locked wt ot)).
  {
  apply fold_lock_ed;
  try tauto.
  apply pofs.
  intros.
  apply PHPD in IN.
  apply phpdef_pair;
  tauto.
  right.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Waiting4cond e l, tx, p, Os, C, id).
  tauto.
  assumption.
  }

  assert (eqvll: v = ll).
  {
  apply INJ.
  apply LOCs.
  assumption.
  rewrite CO2.
  apply some_none.
  symmetry.
  assumption.
  }

  rewrite eqvll in *.

  assert (Lofv: xOf (fun x : location => Lof x) locs (Aof ll) = Some ([[l]])).
  {
  rewrite <- lvl.
  apply xOf_same.
  apply in_map.
  assumption.
  apply comp_cons.
  assumption.
  unfold comp.
  intros.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  }
  rewrite Lofv in SAFE.
  assert (NEQ1: Aof v <> Aof l').
  {
  subst.
  rewrite EQL.
  rewrite <- EQlv.
  unfold not.
  intros.

  assert (eqlllv: ll = lv).
  {
  apply INJ.
  rewrite CO2.
  apply some_none.
  destruct CO3 as [CO3|CO3].
  rewrite CO3.
  apply some_none.
  destruct CO3 as (wt,(ot,CO3)).
  rewrite CO3.
  apply some_none.
  assumption.
  }

  rewrite eqlllv in *.
  rewrite CO2 in CO3.
  destruct CO3 as [CO3|CO3].
  inversion CO3.
  destruct CO3 as (wt,(ot,CO3)).
  inversion CO3.
  }

  rewrite eqvll in *.
  destruct (Z.eq_dec (Aof ll) (Aof l')).
  omega.
  rewrite EQL in *.
  rewrite eqz in SAFE.
  rewrite eqz in SAFE.
  rewrite filter_filter_eq with (f2:=(fun c : cmd =>
                ifb (opZ_eq_dec (waiting_for_cond c) (Some (Aof v))))).
  rewrite eqvll in *.
  assumption.
  intros.
  unfold ifb.
  destruct (opZ_eq_dec (waiting_for_cond x) (waiting_for h x)).
  rewrite e0.
  rewrite eqvll in *.
  reflexivity.
  apply waiting_for_cond_neq in n0.
  destruct n0 as (lx,eqx).
  rewrite eqx in *.
  simpl.
  destruct (opZ_eq_dec (h ([[lx]])) (Some 1%Z)).
  rewrite eqvll in *.
  reflexivity.
  destruct (opZ_eq_dec None (Some (Aof v))).
  inversion e0.
  destruct (opZ_eq_dec (Some ([[lx]])) (Some (Aof ll))).
  inversion e0.
  apply in_map_iff in IN.
  destruct IN as (tr,(eqtr,intr)).
  destruct tr as (((((c1,x1),p1),O1),g1),z1).
  unfold cmdof in eqtr.
  simpl in eqtr.
  inversion eqtr.
  rewrite eqtr in intr.
  assert (intr1:=intr).
  apply SOBS in intr.
  destruct intr as (wf1,(sat11,sobs1)).
  apply sat_wait4lock in sat11.
  destruct sat11 as (ll1,(eqll,(p1ll,prcll1))).
  rewrite <- eqll in H3.

  assert (CO1: fold_left phplus (map pof T) (phplus Pinv Pleak) ll1 = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) ll1 = Some (Locked wt ot)).
  {
  apply fold_lock_ed;
  try tauto.
  apply pofs.
  intros.
  apply PHPD in IN.
  apply phpdef_pair;
  tauto.
  right.
  right.
  exists p1.
  exists.
  apply in_map_iff.
  exists (Waiting4lock lx, x1, p1, O1, g1, z1).
  tauto.
  assumption.
  }

  assert (CO: ll1 = v).
  {
  apply INJ.
  destruct CO1 as [CO1|CO1].
  rewrite CO1.
  apply some_none.
  destruct CO1 as (wt,(ot,CO1)).
  rewrite CO1.
  apply some_none.
  apply LOCs.
  rewrite eqvll in *.
  assumption.
  rewrite eqvll in *.
  assumption.
  }

  rewrite CO in CO1.
  rewrite eqvll in CO1.
  rewrite CO2 in CO1.
  destruct CO1 as [CO1|CO1].
  inversion CO1.
  destruct CO1 as (wt,(ot,CO1)).
  inversion CO1.
  reflexivity.
  }
  unfold comp.
  intros.
  destruct IN as [EQ1|IN1].
  rewrite <- EQ1 in *.
  destruct IN0 as [EQ0|IN0].
  rewrite <- EQ0 in *.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  apply INJ.
  apply LOCs.
  assumption.
  apply OBsOK.
  assumption.
  destruct IN0 as [EQ0|IN0].
  rewrite <- EQ0 in *.
  apply INJ.
  apply OBsOK.
  assumption.
  apply LOCs.
  assumption.
  apply INJ.
  apply OBsOK.
  assumption.
  apply OBsOK.
  assumption.

  intros.
  simpl.
  destruct a as (((((c1,tx1),p1),O1),C1),id1).
  unfold cmdof.
  simpl.
  destruct (waiting_for h c1) eqn:wait.
  simpl.
  destruct (Z.eq_dec z1 (Aof v)).
  rewrite e0.
  destruct (opZ_eq_dec (Some (Aof v)) (Some (Aof v))).
  reflexivity.
  contradiction.
  destruct (opZ_eq_dec (Some z1) (Some (Aof v))).
  inversion e0.
  contradiction.
  reflexivity.
  exfalso.
  apply NIN.
  apply in_map_iff.
  exists (c1, tx1, p1, O1, C1, id1).
  tauto.
  }
  intros.
  apply in_map_iff in ING.
  destruct ING as (x,(EQx,INx)).
  inversion EQx.
  destruct (wof h x) eqn:WOF.
  Focus 2.
  exfalso.
  apply NIN.
  apply in_map_iff.
  exists x.
  tauto.
  simpl in *.
  destruct x as (((((c,tx),p),Os),C),id).
  unfold wof in WOF.
  simpl in *.
  apply waiting_for_lock_cond in WOF.
  destruct WOF as (e,(EQe,wofhx)).
  rewrite EQe in *.
  destruct wofhx as [WL|WC].
  {
  rewrite WL in *.
  assert (VT:=INx).
  apply SOBS in VT.
  destruct VT as (WF,(WP,VOS)).
  apply sat_wait4lock in WP.

  destruct WP as (ll, (EQll, (pll,(prcll,rest)))).

  assert (LOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some Lock \/
    (exists wt ot : bag, fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked wt ot))).
  {
  apply fold_lock_ed;
  try tauto.
  apply pofs.
  intros.
  apply PHPD in IN.
  apply phpdef_pair;
  tauto.
  right.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Waiting4lock e, tx, p, Os, C, id).
  tauto.
  assumption.
  }

  exists ll.
  exists.
  apply LOCs.
  destruct LOCKED as [L1|L1].
  rewrite L1.
  unfold not.
  intros.
  inversion H.
  destruct L1 as (wt,(ot,L1)).
  rewrite L1.
  unfold not.
  intros.
  inversion H.
  exists EQll.
  unfold oof.
  assumption.
  }
  destruct WC as (l,WC).
  rewrite WC in *.
  assert (VT:=INx).
  apply SOBS in VT.
  destruct VT as (WF,(WP,VOS)).
  apply sat_wait4cond in WP.
  destruct WP as (ll,(lv,(EQlv,(EQll,(plv,(pll,(lvl,(prcll,(prclv,sat1))))))))).
  exists lv.
  exists.
  apply LOCs.
  rewrite fold_cond;
  try tauto.
  apply some_none.
  apply pofs.
  intros.
  apply PHPD in IN.
  apply phpdef_pair;
  tauto.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Waiting4cond e l, tx, p, Os, C, id).
  tauto.
  assumption.
  exists EQll.
  unfold oof.
  assumption.
  }

  destruct G1 as (R,(L,(P,(X,(ONE,(SPARE,(OWN,(PRC,TR1)))))))).
  rewrite map_map in *.
  assert (GOAL: (map (fun x => (lift 0%Z (wof h x), map (fun x => Aof x) (oof x), snd x)) T) = nil).
  {
  apply valid_graph_is_deadlock_free with (length T) R L P X.
  rewrite map_map.
  simpl.
  assumption.
  apply length_map.
  intros.
  {
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  inversion EQx.
  apply ONE with (snd x) (oof x).
  apply in_map_iff.
  exists x.
  tauto.
  }
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  inversion EQx.
  apply SPARE with (snd x) (oof x).
  apply in_map_iff.
  exists x.
  tauto.
  rewrite H0.
  assumption.
  }
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  inversion EQx.
  apply OWN with (snd x) (oof x).
  apply in_map_iff.
  exists x.
  tauto.
  rewrite H0.
  assumption.
  }
  {
  intros.
  apply in_map_iff in ING.
  destruct ING as (x,(EQx,INx)).
  inversion EQx.
  apply PRC with (snd x).
  apply in_map_iff.
  exists x.
  tauto.
  }
  }
  destruct HAS_THREAD as (id,tid).
  destruct (t id) eqn:TID.
  Focus 2.
  destruct tid.
  reflexivity.
  destruct p.
  apply TOK in TID.
  destruct TID as (p,(O,(C,INT))).
  destruct T.
  inversion INT.
  inversion GOAL.
Qed.

Open Local Scope nat.

Theorem valid_configuration_reduces:
  forall t h 
         (VALIDK: validk t h)
         (NOT_TERMINATED: exists id, t id <> None),
    ~ data_race t /\ exists t' h', red t h t' h'.
Proof.
  intros.
  destruct NOT_TERMINATED as (id0,tid0).
  destruct (t id0) eqn:TID0.
  Focus 2.
  contradiction.
  destruct p as (c0,tx0).
  split.
  {
  unfold not.
  intros.
  apply valid_configuration_does_not_abort in VALIDK.
  apply VALIDK.
  apply aborts_Race.
  assumption.
  }
  assert (NOWAITING: exists id c (TID: t id = Some c), waiting_for h (fst c) = None).
  {
  apply valid_configuration_is_not_deadlock;
  try assumption.
  exists id0.
  rewrite TID0.
  assumption.
  }
  destruct NOWAITING as (id,(c,(tid,NOWAITING))).
  destruct c as (c,tx).
  assert (VK:=VALIDK).
  unfold validk in VK.
  destruct VK as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS))))))))))))))))).
  unfold pheaps_heap in *.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  unfold locations_ok in *.
  destruct LOCsOK as (INJ,(XCOM,(LCOM,(LOCs,OBsOK)))).
  unfold invs_ok in *.
  destruct INVsOK as (NDPA,(AinvOK,(INAOK,SATAOK))).
  unfold locks_ok.
  destruct LOCKsOK as (LOCKOK,ULOCKOK).
  rewrite map_map in *.
  simpl in *.
  change (fun x : cmd * context * pheap * list location * gheap * Z => pof x) with pof in *.

  destruct INF as (INF0,(INF1,INF2)).
  destruct c.
  destruct tx.
  exists (upd Z.eq_dec t id None), h.
  apply red_Terminate with e.
  assumption.
  destruct (Z.leb ([[e]]) 0) eqn:LE.
  apply Z.leb_le in LE.
  exists (upd Z.eq_dec t id (Some (c2,tx))), h.
  apply red_If_false with e c1.
  assumption.
  assumption.
  apply Z_leb_falseL in LE.
  exists (upd Z.eq_dec t id (Some (c1,tx))), h.
  apply red_If_true with e c2.
  assumption.
  assumption.
  exists (upd Z.eq_dec t id (Some (subs c (subse x ([[e]])),tx))), h.
  apply red_Val.
  assumption.
  unfold inf_capacity in INF2.
  destruct INF2 as (a,INF).
  exists (upd Z.eq_dec t id (Some (tt,tx))), (dstr_cells h (map (fun x => (a + (Z.of_nat x))%Z) (seq O n)) (Some 0%Z)).
  apply red_Cons.
  assumption.
  intros.
  apply INF.
  assert (0 <= z')%Z.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  omega.
  omega.
  destruct (h ([[e]])) eqn:he.
  exists (upd Z.eq_dec t id (Some (Val (Enum z),tx))), h.
  apply red_Lookup with e.
  assumption.
  assumption.
  apply valid_configuration_does_not_abort in VALIDK.
  exfalso.
  apply VALIDK.
  apply aborts_Lookup with e id tx.
  assumption.
  assumption.
  destruct (h ([[e1]])) eqn:he1.
  exists (upd Z.eq_dec t id (Some (tt,tx))), (upd Z.eq_dec h ([[e1]]) (Some ([[e2]]))).
  apply red_Mutate with z.
  assumption.
  assumption.
  apply valid_configuration_does_not_abort in VALIDK.
  exfalso.
  apply VALIDK.
  apply aborts_Mutate with e1 e2 id tx.
  assumption.
  assumption.
  unfold inf_capacity in INF1.
  destruct INF1 as (id',INF).
  exists (upd Z.eq_dec (upd Z.eq_dec t id (Some (tt,tx))) id' (Some (c,done))), h.
  apply red_Fork.
  assumption.
  apply INF.
  omega.
  exists (upd Z.eq_dec t id (Some (c1,Let' x c2 tx))), h.
  apply red_Let.
  assumption.
  exists (upd Z.eq_dec t id (Some (c1,If' c2 c3 tx))), h.
  apply red_If.
  assumption.
  assert (G: exists x, is_free (While c1 c2) x = false).
  {
  apply inf_var.
  }
  destruct G as (x,ISFREE).
  exists (upd Z.eq_dec t id (Some (If c1 (Let x c2 (While c1 c2)) tt, tx))), h.
  apply red_While.
  assumption.
  assumption.
  unfold inf_capacity in INF2.
  destruct INF2 as (a,INF).
  exists (upd Z.eq_dec t id (Some (Val (Enum a),tx))), (upd Z.eq_dec h a (Some 1%Z)).
  apply red_Newlock.
  assumption.
  apply INF.
  omega.
  destruct (h ([[e]])) eqn:he.
  destruct (Z.eq_dec z 1).
  rewrite e0 in *.
  exists (upd Z.eq_dec t id (Some (tt,tx))), (upd Z.eq_dec h ([[e]]) (Some 0%Z)).
  apply red_Acquire.
  assumption.
  assumption.
  exists (upd Z.eq_dec t id (Some (Waiting4lock e,tx))), h.
  apply red_Acquire0.
  assumption.
  unfold not.
  intros.
  rewrite he in H.
  inversion H.
  contradiction.
  apply valid_configuration_does_not_abort in VALIDK.
  exfalso.
  apply VALIDK.
  apply aborts_Acquire with e id tx.
  assumption.
  assumption.
  exists (upd Z.eq_dec t id (Some (tt,tx))), (upd Z.eq_dec h ([[e]]) (Some 1%Z)).
  assert (HE: h ([[e]]) <> None /\ h ([[e]]) <> Some 1%Z).
  {
  apply valid_configuration_does_not_abort in VALIDK.
  destruct (h ([[e]])) eqn:he.
  destruct (Z.eq_dec z 1%Z).
  rewrite e0 in *.
  exfalso.
  apply VALIDK.
  apply aborts_Release with e id tx.
  right.
  assumption.
  assumption.
  split.
  unfold not.
  intros.
  inversion H.
  unfold not.
  intros.
  inversion H.
  contradiction.
  exfalso.
  apply VALIDK.
  apply aborts_Release with e id tx.
  left.
  assumption.
  assumption.
  }
  apply red_Release.
  assumption.
  tauto.
  tauto.
  destruct (h ([[l]])) eqn:hl.
  destruct (Z.eq_dec z 1%Z).
  rewrite e in *.
  exists (upd Z.eq_dec t id (Some (tt,tx))), (upd Z.eq_dec h ([[l]]) (Some 0%Z)).
  apply red_Acquire1.
  assumption.
  assumption.
  simpl in NOWAITING.
  rewrite hl in NOWAITING.
  destruct (opZ_eq_dec (Some z) (Some 1%Z)).
  inversion e.
  contradiction.
  inversion NOWAITING.
  apply valid_configuration_does_not_abort in VALIDK.
  exfalso.
  apply VALIDK.
  apply aborts_Waiting4lock with l id tx.
  assumption.
  assumption.
  unfold inf_capacity in INF2.
  destruct INF2 as (a,INF).
  exists (upd Z.eq_dec t id (Some (Val (Enum a),tx))), (upd Z.eq_dec h a (Some 0%Z)).
  apply red_Newcond.
  assumption.
  apply INF.
  omega.
  exists (upd Z.eq_dec t id (Some (Waiting4cond x l,tx))), (upd Z.eq_dec h ([[l]]) (Some 1%Z)).
  assert (G: h ([[l]]) <> None /\ h ([[x]]) <> None /\ h ([[l]]) <> Some 1%Z).
  {
  apply valid_configuration_does_not_abort in VALIDK.
  destruct (h ([[l]])) eqn:hl.
  destruct (Z.eq_dec z 1%Z).
  rewrite e in *.
  exfalso.
  apply VALIDK.
  apply aborts_Wait with x l id tx.
  right.
  left.
  assumption.
  assumption.
  split.
  unfold not.
  intros.
  inversion H.
  split.
  destruct (h ([[x]])) eqn:hx.
  unfold not.
  intros.
  inversion H.
  exfalso.
  apply VALIDK.
  apply aborts_Wait with x l id tx.
  right.
  right.
  assumption.
  assumption.
  unfold not.
  intros.
  inversion H.
  contradiction.
  exfalso.
  apply VALIDK.
  apply aborts_Wait with x l id tx.
  left.
  assumption.
  assumption.
  }
  apply red_Wait;
  try tauto.
  assert (G: (exists idvltx, ([[x]]) = ([[(snd (fst (fst idvltx)))]]) /\ t (fst (fst (fst idvltx))) = Some (Waiting4cond (snd (fst (fst idvltx))) (snd (fst idvltx)), snd idvltx)) \/
    ~ exists idvltx, ([[x]]) = ([[(snd (fst (fst idvltx)))]]) /\ t (fst (fst (fst idvltx))) = Some (Waiting4cond (snd (fst (fst idvltx))) (snd (fst idvltx)), snd idvltx)).
  {
  apply classic.
  }
  apply valid_configuration_does_not_abort in VALIDK.
  destruct G.
  destruct H as (idvltx,(EQ1,EQ2)).
  destruct idvltx as (((id',v'),l'),tx').
  simpl in *.
  exists (upd Z.eq_dec (upd Z.eq_dec t id (Some (tt,tx))) id' (Some (Waiting4lock l',tx'))), h.
  apply red_Notify with x v';
  try tauto.
  destruct (h ([[x]])) eqn:hx.
  unfold not.
  intros.
  inversion H.
  exfalso.
  apply VALIDK.
  apply aborts_Notify with x id tx.
  assumption.
  assumption.
  exists (upd Z.eq_dec t id (Some (tt,tx))), h.
  apply red_Notify0 with x;
  try tauto.
  destruct (h ([[x]])) eqn:hx.
  unfold not.
  intros.
  inversion H0.
  exfalso.
  apply VALIDK.
  apply aborts_Notify with x id tx.
  assumption.
  assumption.
  unfold not.
  intros.
  apply H.
  destruct H0 as (id',(v',(l',(tx',(EQ1,EQ2))))).
  exists (id',v',l',tx').
  tauto.
  exists (upd Z.eq_dec (wakeupthrds ([[x]]) t) id (Some (tt,tx))), h.
  apply red_NotifyAll.
  assumption.
  destruct (h ([[x]])) eqn:hx.
  unfold not.
  intros.
  inversion H.
  exfalso.
  apply valid_configuration_does_not_abort in VALIDK.
  apply VALIDK.
  apply aborts_NotifyAll with x id tx.
  assumption.
  assumption.
  inversion NOWAITING.

  exists (upd Z.eq_dec t id (Some (tt,tx))), h.
  apply red_g_initl with x.
  assumption.
  exists (upd Z.eq_dec t id (Some (tt,tx))), h.
  apply red_g_dupl with x.
  assumption.
  exists (upd Z.eq_dec t id (Some (tt,tx))), h.
  apply red_g_chrg with x.
  assumption.
  exists (upd Z.eq_dec t id (Some (tt,tx))), h.
  apply red_g_chrgu with x.
  assumption.
  exists (upd Z.eq_dec t id (Some (tt,tx))), h.
  apply red_g_disch with x.
  assumption.
  exists (upd Z.eq_dec t id (Some (tt,tx))), h.
  apply red_g_dischu with x.
  assumption.
  exists (upd Z.eq_dec t id (Some (tt,tx))), h.
  apply red_g_newctr.
  assumption.
  exists (upd Z.eq_dec t id (Some (tt,tx))), h.
  apply red_g_ctrinc with x.
  assumption.
  exists (upd Z.eq_dec t id (Some (tt,tx))), h.
  apply red_g_ctrdec with x.
  assumption.
Qed.

Hint Resolve Let_preserves_validity.
Hint Resolve Val_preserves_validity.
Hint Resolve Val_done_preserves_validity.
Hint Resolve Fork_preserves_validity.
Hint Resolve Newlock_preserves_validity.
Hint Resolve Acquire_preserves_validity.
Hint Resolve Acquire0_preserves_validity.
Hint Resolve Waiting4lock_preserves_validity.
Hint Resolve Release_preserves_validity.
Hint Resolve Newcond_preserves_validity.
Hint Resolve Wait_preserves_validity.
Hint Resolve Notify_preserves_validity.
Hint Resolve Notify0_preserves_validity.
Hint Resolve NotifyAll_preserves_validity.
Hint Resolve g_initl_preserves_validity.
Hint Resolve g_chrg_preserves_validity.
Hint Resolve g_chrgu_preserves_validity.
Hint Resolve g_disch_preserves_validity.
Hint Resolve g_dischu_preserves_validity.
Hint Resolve g_newctr_preserves_validity.
Hint Resolve g_ctrinc_preserves_validity.
Hint Resolve g_ctrdec_preserves_validity.
Hint Resolve Cons_preserves_validity.
Hint Resolve Lookup_preserves_validity.
Hint Resolve Mutate_preserves_validity.
Hint Resolve If_preserves_validity.
Hint Resolve If1_preserves_validity.
Hint Resolve If2_preserves_validity.
Hint Resolve While_preserves_validity.
Hint Resolve g_dupl_preserves_validity.

Theorem steps_preserve_validity:
  forall t h t' h' 
         (VALIDK: validk t h) (STEP: red t h t' h'),
    validk t' h'.
Proof.
  intros.
  destruct STEP; try eauto.
Qed.

Inductive safe: nat -> thrds -> heap -> Prop :=
  | Base: forall t h, safe O t h
  | Terminated: forall n t h (TER: forall id, t id = None), safe n t h
  | Running: forall n t h (NO_RACE: ~ data_race t)
                          (REDUCES: exists t' h', red t h t' h')
                          (SAFE: forall t' h' (RED: red t h t' h'), safe n t' h'),
               safe (S n) t h.

Theorem valid_configuration_is_safe:
  forall n t h (VALIDK: validk t h),
    safe n t h.
Proof.
  induction n.
  intros.
  apply Base.
  intros.
  assert (THRD: (forall id, t id = None) \/ ~ (forall id, t id = None)).
  apply classic.
  destruct THRD as [THRD|THRD].
  eapply Terminated.
  assumption.
  assert (tmp: exists id, t id <> None).
  apply not_all_not_ex.
  unfold not.
  intros.
  apply THRD.
  intros.
  specialize H with id.
  destruct (t id).
  exfalso.
  apply H.
  intros.
  inversion H0.
  reflexivity.
  assert (G: ~ data_race t /\ exists t' h', red t h t' h').
  {
  apply valid_configuration_reduces;
  try tauto.
  }
  destruct G as (norace,(t',(h',red))).
  apply Running.
  tauto.
  exists t', h'.
  tauto.
  intros.
  apply IHn;
  try tauto.
  apply steps_preserve_validity with t h; assumption.
Qed.

Theorem verified_program_is_safe:
  forall c id invs
         (WELLFORMED: wellformed_cmd c)
         (VERIFIED: correct (Aobs nil) c (fun _ => Aobs nil) invs) n,
    safe n (upd Z.eq_dec (emp (cmd * context)) id (Some (c,done))) (emp Z).
Proof.
  intros.
  apply valid_configuration_is_safe.
  apply initial_configuration_is_valid with invs; assumption.
Qed.
