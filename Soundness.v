Require Import Qcanon.
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
Require Import RelaxedPrecedenceRelation.

Set Implicit Arguments.

(** # <font size="5"><b> Validity of Configurations </b></font> # *)

Theorem valid_configuration_does_not_abort:
  forall sp t h (VALIDK: validk sp t h),
    ~ aborts t h.
Proof.
  intros.
  unfold not.
  intros ABORT.
  destruct VALIDK as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
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
  rewrite map_map in *.
  simpl in *.
  change (fun x : cmd * context * pheap * list (olocation Z) * gheap * Z => pof x) with pof in *.

  assert (phpdefp0: forall p0 : pheap, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  repeat php_.
  apply PHPD. assumption.
  apply PHPD. assumption.
  }

  inversion ABORT.
  {
  unfold data_race in *.
  destruct RACE as (id,(id',(c,(c',(tx,(tx',(NEQ,(tid,(tid',(NEQW,EQW)))))))))).

  destruct (write c) eqn:wrc.
  Focus 2.
  contradiction.
  destruct c;
  inversion wrc.
  apply TOK in tid.
  destruct tid as (p,(O,(C,IN))).
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF,(SAT,rest)).
  assert (G1: exists l1 (EQl: Aof l1 = z) (pl: exists v, p l1 = Some (Cell full v)),
    sat (upd (location_eq_dec Z.eq_dec) p l1 (Some (Cell full ([[e2]])))) (Some O) C (weakest_pre_ct sp (tt, tx) invs)).
  {
  rewrite <- H2.
  eapply sat_mutate.
  apply SAT.
  }
  apply TOK in tid'.
  destruct tid' as (p',(O',(C',IN'))).
  assert (tmp':=IN').
  apply SOBS in tmp'.
  destruct tmp' as (WF',(SAT',rest')).
  assert (G': exists l' v f (LT: Qclt 0 f) (EQ: Aof l' = z), p' l' = Some (Cell f v)).
  {
  destruct c';
  inversion EQW.
  assert (G1': exists v0 ll (EQ: ([[e]]) = ([[Aof ll]]))
    (pv: exists f' (f'le : 0 < f'), p' (evall ll) = Some (Cell f' v0)),
    sat p' (Some O') C' (weakest_pre_ct sp (Val (Enum v0), tx') invs)).
  {
  apply sat_lookup.
  apply SAT'.
  }
  destruct G1' as (v0,(ll,(eq,(pv',sat1)))).
  destruct pv' as (f',(lef',pv')).
  exists (evall ll), v0, f', lef'.
  exists. symmetry. assumption. assumption.
  assert (G2': exists l1 (EQl: Aof l1 = z) (pl: exists v, p' l1 = Some (Cell full v)),
    sat (upd (location_eq_dec Z.eq_dec) p' l1 (Some (Cell full ([[e3]])))) (Some O') C' (weakest_pre_ct sp (tt, tx') invs)).
  {
  rewrite H3.
  eapply sat_mutate.
  apply SAT'.
  }
  destruct G2' as (l1,(eq1,(pv1',sat1))).
  destruct pv1' as (v,pv1').
  exists l1, v, full.
  exists.
  apply proj1 with (full <= 1).
  apply full_bound.
  rewrite <- H3.
  exists eq1. assumption.
  }
  destruct G1 as (l1,(eq1,(pv1,sat1))).
  destruct pv1 as (v1,pv1).
  destruct G' as (l2,(v2,(f2,(lef2,(EQ2,pl2))))).
  assert (EQL: l1 = l2).
  {
  apply INJ.
  apply LOCs.
  apply LOCs.
  assert (G: exists f, (fold_left phplus (map pof T) (phplus Pinv Pleak)) l1 = Some (Cell f v1)).
  {
  apply fold_cell;
  try tauto.
  apply pofs.
  intros.
  exists 1.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Mutate e1 e2, tx, p, O, C, id).
  tauto.
  assumption.
  }
  destruct G as (f',foldl1).
  rewrite foldl1.
  apply some_none.
  assert (G: exists f, (fold_left phplus (map pof T) (phplus Pinv Pleak)) l2 = Some (Cell f v2)).
  {
  apply fold_cell;
  try tauto.
  apply pofs.
  exists f2.
  right.
  exists p'.
  exists.
  apply in_map_iff.
  exists (c', tx', p', O', C', id').
  tauto.
  assumption.
  }
  destruct G as (f',foldl1).
  rewrite foldl1.
  apply some_none.
  rewrite EQ2.
  assumption.
  }
  rewrite <- EQL in *.
  assert (bp': boundph p').
  {
  apply BPE.
  apply in_map_iff.
  exists (c', tx', p', O', C', id').
  tauto.
  }
  assert (co: boundph (phplus p p')).
  {
  apply boundph_fold1 with (l:=T)(m:=pof)(b:=(phplus Pinv Pleak))(id1:=id)(id2:=id'); repeat php_.
  apply in_map_iff.
  exists (Mutate e1 e2, tx, p, O, C, id). auto.
  apply in_map_iff.
  exists (c', tx', p', O', C', id'). auto.
  }
  unfold boundph in co.
  unfold phplus in co.
  specialize co with (x:=l1) (f:=1+f2)(z:=v1).
  rewrite pv1 in co.
  rewrite pl2 in co.
  pose proof co as [co1 co2].
  reflexivity.
  apply qcpluslelt with f2.
  assumption.
  unfold boundph in bp'.
  pose proof bp' as [bp''].
  apply pl2.
  tauto.
  }
  {
  apply TOK in CMD.
  destruct CMD as (p,(O,(C,IN))).
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF,(SAT,rest)).
  assert (G1': exists v0 ll (EQ: ([[e]]) = ([[Aof ll]]))
    (pv: exists f' (f'le : 0 < f'), p (evall ll) = Some (Cell f' v0)),
    sat p (Some O) C (weakest_pre_ct sp (Val (Enum v0), tx) invs)).
  {
  apply sat_lookup. assumption.
  }
  destruct G1' as (v0,(ll,(eq,(pv',sat1)))).
  destruct pv' as (f',(lef',pv')).

  assert (G': exists f, (fold_left phplus (map pof T) (phplus Pinv Pleak)) (evall ll) = Some (Cell f v0)).
  {
  apply fold_cell; repeat php_.
  apply pofs.
  exists f'.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Lookup e, tx, p, O, C, tid).
  tauto.
  assumption.
  }
  destruct G' as (f'',foldl2).
  unfold phtoh in PH2H.
  destruct PH2H as (PH2H,PH2H1).
  specialize PH2H with (evall ll).
  rewrite foldl2 in PH2H.
  rewrite eq in *.
  replace (Aof (evall ll)) with ([[Aof ll]]) in *.
  rewrite PH2H in NUL.
  inversion NUL.
  reflexivity.
  }

  {
  apply TOK in CMD.
  destruct CMD as (p,(O,(C,IN))).
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF,(SAT,rest)).
  assert (G2': exists l1 (EQl: Aof l1 = ([[e1]])) (pl: exists v, p l1 = Some (Cell full v)),
    sat (upd (location_eq_dec Z.eq_dec) p l1 (Some (Cell full ([[e2]])))) (Some O) C (weakest_pre_ct sp (tt, tx) invs)).
  {
  eapply sat_mutate. assumption.
  }
  destruct G2' as (l1,(eq1,(pv1',sat1))).
  destruct pv1' as (v,pv1').

  assert (G': exists f, (fold_left phplus (map pof T) (phplus Pinv Pleak)) l1 = Some (Cell f v)).
  {
  apply fold_cell; repeat php_.
  apply pofs.
  exists full.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Mutate e1 e2, tx, p, O, C, tid).
  tauto.
  assumption.
  }
  destruct G' as (f',foldl2).
  unfold phtoh in PH2H.
  destruct PH2H as (PH2H,PH2H1).
  specialize PH2H with l1.
  rewrite foldl2 in PH2H.
  rewrite eq1 in *.
  rewrite PH2H in NUL.
  inversion NUL.
  }

  {
  apply TOK in CMD.
  destruct CMD as (p,(O,(C,IN))).
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF,(SAT,rest)).
  apply sat_acquire0 in SAT.
  destruct SAT as (ll,(eqll,(pll,rest1))).

  assert (fll: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked wt ot)).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  right. right.
  exists p. exists.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, tid). auto. assumption.
  }
  destruct PH2H as (PH2H,PH2H1).
  specialize PH2H with ll.
  rewrite eqll in *.
  rewrite NUL in PH2H.
  destruct fll as [fll|fll].
  rewrite fll in PH2H.
  inversion PH2H.
  destruct fll as (wt,(ot,fll)).
  rewrite fll in PH2H.
  inversion PH2H.
  }

  {
  apply TOK in CMD.
  destruct CMD as (p,(O,(C,IN))).
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF,(SAT,rest)).
  apply sat_wait4lock in SAT.
  destruct SAT as (ll,(eqll,(pll,rest1))).

  assert (fll: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked wt ot)).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  right. right.
  exists p. exists.
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, tid). auto. assumption.
  }
  destruct PH2H as (PH2H,PH2H1).
  specialize PH2H with ll.
  rewrite eqll in *.
  rewrite NUL in PH2H.
  destruct fll as [fll|fll].
  rewrite fll in PH2H.
  inversion PH2H.
  destruct fll as (wt,(ot,fll)).
  rewrite fll in PH2H.
  inversion PH2H.
  }

  {
  apply TOK in CMD.
  destruct CMD as (p,(O,(C,IN))).
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF,(SAT,rest)).
  apply sat_WasWaiting4cond in SAT.
  destruct SAT as (ll,(lv,(eqll,(eqlv,(loflv,(pll,(plv,rest1))))))).

  assert (fll: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked wt ot)).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  right. right.
  exists p. exists.
  apply in_map_iff.
  exists (WasWaiting4cond v l, tx, p, O, C, tid). auto. assumption.
  }

  assert (flv: fold_left phplus (map pof T) (phplus Pinv Pleak) lv = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists p. exists.
  apply in_map_iff.
  exists (WasWaiting4cond v l, tx, p, O, C, tid). auto. assumption.
  }

  destruct PH2H as (PH2H,PH2H1).
  destruct NUL as [NUL|NUL].
  specialize PH2H with ll.
  rewrite eqll in *.
  rewrite NUL in PH2H.
  destruct fll as [fll|fll].
  rewrite fll in PH2H.
  inversion PH2H.
  destruct fll as (wt,(ot,fll)).
  rewrite fll in PH2H.
  inversion PH2H.
  specialize PH2H with lv.
  rewrite eqlv in *.
  rewrite NUL in PH2H.
  rewrite flv in PH2H.
  contradiction.
  }

  {
  apply TOK in CMD.
  destruct CMD as (p,(O,(C,IN))).
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF,(SAT,rest)).
  apply sat_release in SAT.
  destruct SAT as (ll,(p1,(p2,(wt,(ot,(C1,(C2,(O1,(eqll,(PERM,(bp1,(bp2,(bc1,(bc2,(p1p2,(c1c2,(p1p2',(c1c2',(p1ll,rest1))))))))))))))))))).

  assert (fll: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked wt ot)).
  {
  apply fold_locked; repeat php_.
  apply pofs.
  right.
  exists p. exists.
  apply in_map_iff.
  exists (Release l, tx, p, O, C, tid). auto. rewrite p1p2'.
  unfold phplus. rewrite p1ll. reflexivity.
  }

  destruct PH2H as (PH2H,PH2H1).
  specialize PH2H with ll.
  rewrite eqll in *.
  destruct NUL as [NUL|NUL].
  rewrite NUL in PH2H.
  rewrite fll in PH2H.
  inversion PH2H.
  rewrite fll in PH2H.
  inversion PH2H.
  rewrite NUL in PH2H.
  inversion PH2H.
  }

  {
  apply TOK in CMD.
  destruct CMD as (p,(O,(C,IN))).
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF,(SAT,rest)).
  apply sat_wait in SAT.
  destruct SAT as (lv,(ll,(p1,(p2,(wt,(ot,(C1,(C2,(O1,(eqll,(eqlv,(PERM,(bp1,(bp2,(p1p2,(p1p2',(c1c2,(c1c2',(p1lv,(p1ll,rest1)))))))))))))))))))).

  assert (fll: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked wt ot)).
  {
  apply fold_locked; repeat php_.
  apply pofs.
  right.
  exists p. exists.
  apply in_map_iff.
  exists (Wait v l, tx, p, O, C, tid). auto. rewrite p1p2'.
  unfold phplus. rewrite p1lv. reflexivity.
  }

  assert (flv: fold_left phplus (map pof T) (phplus Pinv Pleak) lv = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists p. exists.
  apply in_map_iff.
  exists (Wait v l, tx, p, O, C, tid). auto.
  rewrite p1p2'. unfold phplus. rewrite p1ll. reflexivity.
  }

  destruct PH2H as (PH2H,PH2H1).
  destruct NUL as [NUL|NUL].
  specialize PH2H with ll.
  rewrite eqll in *.
  rewrite NUL in PH2H.
  rewrite fll in PH2H.
  inversion PH2H.
  destruct NUL as [NUL|NUL].
  specialize PH2H with ll.
  rewrite eqll in *.
  rewrite NUL in PH2H.
  rewrite fll in PH2H.
  inversion PH2H.
  specialize PH2H with lv.
  rewrite eqlv in *.
  rewrite flv in PH2H.
  rewrite NUL in PH2H.
  contradiction.
  }

  {
  apply TOK in CMD.
  destruct CMD as (p,(O,(C,IN))).
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF,(SAT,rest)).
  apply sat_wait4cond in SAT.

  destruct SAT as (ll,(lv,(eqll,(eqlv,(plv,(pll,rest1)))))).

  assert (fll: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked wt ot)).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  right. right.
  exists p. exists.
  apply in_map_iff.
  exists (Waiting4cond v l, tx, p, O, C, tid). auto. assumption.
  }

  assert (flv: fold_left phplus (map pof T) (phplus Pinv Pleak) lv = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists p. exists.
  apply in_map_iff.
  exists (Waiting4cond v l, tx, p, O, C, tid). auto. assumption.
  }

  destruct PH2H as (PH2H,PH2H1).
  destruct NUL as [NUL|NUL].
  specialize PH2H with ll.
  rewrite eqll in *.
  rewrite NUL in PH2H.
  destruct fll as [fll|fll].
  rewrite fll in PH2H.
  inversion PH2H.
  destruct fll as (wt,(ot,fll)).
  rewrite fll in PH2H.
  inversion PH2H.
  specialize PH2H with lv.
  rewrite eqlv in *.
  rewrite NUL in PH2H.
  rewrite flv in PH2H.
  contradiction.
  }

  {
  apply TOK in CMD.
  destruct CMD as (p,(O,(C,IN))).
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF,(SAT,rest)).
  apply sat_notify in SAT.
  destruct SAT as (p1,(pm,(C1,(Cm,(wt,(ot,(lv,(ll,(Or,(PERMOr,(bp1,(bpm,(bp1pm,(phpdefp1pm,(p1pm,(ghpdefC1Cm,(C1Cm,(eqlv,(eqll,(p1ll,(p1lv,rest1))))))))))))))))))))).

  assert (flv: fold_left phplus (map pof T) (phplus Pinv Pleak) lv = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists p. exists.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, tid). auto. 
  rewrite p1pm. unfold phplus. rewrite p1lv. reflexivity.
  }

  destruct PH2H as (PH2H,PH2H1).
  specialize PH2H with lv.
  rewrite eqlv in *.
  rewrite NIN in PH2H.
  rewrite flv in PH2H.
  contradiction.
  }

  {
  apply TOK in CMD.
  destruct CMD as (p,(O,(C,IN))).
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF,(SAT,rest)).
  apply sat_notifyAll in SAT.
  destruct SAT as (wt,(ot,(lv,(ll,(M'nil,(eqlv,(eqll,(pl,(pv,(EMP,sat1)))))))))).

  assert (flv: fold_left phplus (map pof T) (phplus Pinv Pleak) lv = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists p. exists.
  apply in_map_iff.
  exists (NotifyAll v, tx, p, O, C, tid). auto. assumption.
  }

  destruct PH2H as (PH2H,PH2H1).
  specialize PH2H with lv.
  rewrite eqlv in *.
  rewrite NIN in PH2H.
  rewrite flv in PH2H.
  contradiction.
  }
Qed.

Theorem valid_configuration_is_not_deadlock:
  forall sp t h (VALIDK: validk sp t h) (HAS_THREAD: exists id, t id <> None),
    exists id c (TID: t id = Some c), waiting_for h (fst c) = None.
Proof.
  unfold validk.
  intros.
  destruct VALIDK as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,(SPUR,(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
  unfold validk.
  unfold pheaps_heap in *.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  unfold locations_ok in *.
  destruct LOCsOK as (INJ,(LCOM,(LOCs,OBsOK))).
  unfold invs_ok in *.
  destruct INVsOK as (NDPA,(AinvOK,(INAOK,SATAOK))).
  unfold locks_ok.
  destruct LOCKsOK as (LOCKOK,ULOCKOK).
  rewrite map_map in *.
  simpl in *.
  change (fun x : cmd * context * pheap * list (olocation Z) * gheap * Z => pof x) with pof in *.

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
  assert (G1: exists (R: Z -> Z) (P: Z -> bool) (X: Z -> option Z)
         (ONE: forall z o O (IN: In (o,O,z) (map (fun x => (lift 0%Z (wof h x), oof x, snd x)) T)), one_ob (map (fun x => (fst (fst x), map (fun x => Aofo x) (snd (fst x)), snd x)) (map (fun x => (lift 0%Z (wof h x), oof x, snd x)) T)) o)
         (SPARE: forall z o O (IN: In (o,O,z) (map (fun x => (lift 0%Z (wof h x), oof x, snd x)) T)) (Po: P o = true), spare_ob (map (fun x => (fst (fst x), map (fun x => Aofo x) (snd (fst x)), snd x)) (map (fun x => (lift 0%Z (wof h x), oof x, snd x)) T)) o)
         (OWN: forall z o O (IN: In (o,O,z) (map (fun x => (lift 0%Z (wof h x), oof x, snd x)) T)) (INX: X o <> None), own_ob (map (fun x => (fst (fst x), map (fun x => Aofo x) (snd (fst x)), snd x)) (map (fun x => (lift 0%Z (wof h x), oof x, snd x)) T)) o)
         (PRC: forall z o O (ING: In (o,O,z) (map (fun x => (lift 0%Z (wof h x), oof x, snd x)) T)), prc o (map (fun x => Aofo x) O) R P X = true), True).
  {
  apply validConfiguration_validWaitForGraph with locs;
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
  assert (G: In o' (concat (map oof T))).
  {
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  apply in_map_iff in ING.
  destruct ING as (x,(EQx,INx)).
  exists x.
  inversion EQx.
  rewrite H1.
  tauto.
  }
  apply OBsOK in G.
  destruct G as (l,(EQl,pl)).
  apply in_map_iff.
  exists l.
  split.
  assumption.
  apply LOCs.
  assumption.
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
  assert (G: Lof ll = Aof ll /\ Pof ll = false /\ Xof ll = None /\
    (h (Aof ll) <> Some 1%Z -> In (Oof ll) (concat (map oof T)))).
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
  destruct (opZ_eq_dec (Xof ll) None).
  reflexivity.
  contradiction.
  }
  }
  destruct WC as (l,WC).
  assert (VT:=INx).
  apply SOBS in VT.
  destruct VT as (WF,(WP,VOS)).

  destruct WC as [WC1|WC2].
  {
  rewrite WC1 in *.
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
  rewrite <- count_map_eqo.
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

  assert (Lofv: xOf (fun x => Lof x) locs (Aof ll) = Some ([[l]])).
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



  apply safe_obs_wt_weak with (length
            (filter
               (fun c : cmd =>
                ifb (opZ_eq_dec (waiting_for_cond c) (Some (Aof ll))))
               (map cmdof T))); try assumption.
  apply filter_filter_le.
  intros.
  unfold ifb in F1.
  destruct (opZ_eq_dec (waiting_for h x) (Some (Aof ll))).
  Focus 2.
  inversion F1.
  apply waiting_for_lock_cond in e0.
  destruct e0 as (e',(EQe',We')).
  destruct We' as [We'|We'].
  {
  rewrite We' in *.
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
  rewrite <- eqll in EQe'.

  assert (CO1: fold_left phplus (map pof T) (phplus Pinv Pleak) ll1 = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) ll1 = Some (Locked wt ot)).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  intros.
  apply PHPD in IN.
  apply phpdef_pair; repeat php_.
  right.
  right.
  exists p1.
  exists.
  apply in_map_iff.
  exists (Waiting4lock e', x1, p1, O1, g1, z1).
  auto.
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
  rewrite EQe'.
  reflexivity.
  }

  rewrite CO in CO1.
  rewrite eqvll in CO1.
  rewrite CO2 in CO1.
  destruct CO1 as [CO1|CO1].
  inversion CO1.
  destruct CO1 as (wt,(ot,CO1)).
  inversion CO1.
  }
  destruct We' as (ll',We').
  rewrite EQe'.
  destruct We' as [We'|We'].
  rewrite We'.
  simpl.
  destruct (opZ_eq_dec (Some ([[e']])) (Some ([[e']]))).
  reflexivity.
  contradiction.
  {
  rewrite We' in *.
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
  apply sat_WasWaiting4cond in sat11.
  destruct sat11 as (ll1,(lv1,(EQll1,(EQlv1,(Loflv1,(pll1,(plv1,(prcll1,satll1)))))))).
  rewrite <- EQll1 in EQe'.

  assert (CO1: fold_left phplus (map pof T) (phplus Pinv Pleak) ll1 = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) ll1 = Some (Locked wt ot)).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  intros.
  apply PHPD in IN.
  apply phpdef_pair; repeat php_.
  right.
  right.
  exists p1.
  exists.
  apply in_map_iff.
  exists (WasWaiting4cond ll' e', x1, p1, O1, g1, z1).
  auto.
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
  rewrite EQe'.
  reflexivity.
  }

  rewrite CO in CO1.
  rewrite eqvll in CO1.
  rewrite CO2 in CO1.
  destruct CO1 as [CO1|CO1].
  inversion CO1.
  destruct CO1 as (wt,(ot,CO1)).
  inversion CO1.
  }
  }

  unfold comp.
  intros.
  destruct IN as [EQ1|IN1].
  rewrite <- EQ1 in *.
  destruct IN0 as [EQ0|IN0].
  rewrite <- EQ0 in *.
  unfold injph in INJ.
  apply injo.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  apply OBsOK in IN0.
  destruct IN0 as (l1,(EQl,pl)).
  rewrite <- EQl.
  apply injo.
  apply INJ.
  apply LOCs.
  assumption.
  assumption.
  destruct IN0 as [EQ0|IN0].
  rewrite <- EQ0 in *.
  apply OBsOK in IN1.
  destruct IN1 as (l1,(EQl,pl)).
  rewrite <- EQl.
  apply injo.
  apply INJ.
  apply LOCs.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  apply OBsOK in IN0.
  destruct IN0 as (l1,(EQl,pl)).
  rewrite <- EQl.
  apply OBsOK in IN1.
  destruct IN1 as (l2,(EQ2,pl2)).
  rewrite <- EQ2.
  apply injo.
  apply INJ.
  apply LOCs.
  apply LOCs.
  assumption.
  apply LOCs.
  apply LOCs.
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
  {
  rewrite WC2 in *.
  assert (VT:=INx).
  apply SOBS in VT.
  apply sat_WasWaiting4cond in WP.
  destruct WP as (ll,(lv,(EQll,(EQlv,(Loflv,(pll,(plv,(prcll,satll)))))))).
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
  exists (WasWaiting4cond l e, tx, p, Os, C, id).
  auto.
  assumption.
  }
  assert (G: Lof ll = Aof ll /\ Pof ll = false /\ Xof ll = None /\
    (h (Aof ll) <> Some 1%Z -> In (Oof ll) (concat (map oof T)))).
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
  destruct (opZ_eq_dec (Xof ll) None).
  reflexivity.
  contradiction.
  }
  }
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
  assert (VT:=INx).
  apply SOBS in VT.
  destruct VT as (WF,(WP,VOS)).
  destruct WC as [WC1|WC2].
  {
  rewrite WC1 in *.
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
  {
  rewrite WC2 in *.
  apply sat_WasWaiting4cond in WP.
  destruct WP as (ll,(lv,(EQll,(EQlv,(Loflv,(pll,(plv,(prcll,satll)))))))).
  exists ll.
  exists.
  apply LOCs.
  assert (LKED: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some Lock \/
       (exists wt ot : bag,
          fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked wt ot))).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  intros.
  apply PHPD in IN.
  apply phpdef_pair; repeat php_.
  right.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (WasWaiting4cond l e, tx, p, Os, C, id).
  auto.
  assumption.
  }
  destruct LKED as [LKED|LKED].
  rewrite LKED.
  apply some_none.
  destruct LKED as (wt,(ot,LKED)).
  rewrite LKED.
  apply some_none.
  exists EQll.
  unfold oof.
  assumption.
  }
  }
  destruct G1 as (R,(P,(X,(ONE,(SPARE,(OWN,(PRC,TR1))))))).
  rewrite map_map in *.
  assert (GOAL: (map (fun x => (lift 0%Z (wof h x), map (fun x => Aofo x) (oof x), snd x)) T) = nil).
  {
  apply valid_graph_is_deadlock_free with (length T) R P X.
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

Theorem valid_configuration_reduces:
  forall sp t h 
         (VALIDK: validk sp t h)
         (NOT_TERMINATED: exists id, t id <> None),
    ~ data_race t /\ exists t' h', red sp t h t' h'.
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
  apply valid_configuration_is_not_deadlock with sp;
  try assumption.
  exists id0.
  rewrite TID0.
  assumption.
  }
  destruct NOWAITING as (id,(c,(tid,NOWAITING))).
  destruct c as (c,tx).
  assert (VK:=VALIDK).
  unfold validk in VK.
  destruct VK as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,(SPUR,(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
  unfold pheaps_heap in *.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  unfold locations_ok in *.
  destruct LOCsOK as (INJ,(LCOM,(LOCs,OBsOK))).
  unfold invs_ok in *.
  destruct INVsOK as (NDPA,(AinvOK,(INAOK,SATAOK))).
  unfold locks_ok.
  destruct LOCKsOK as (LOCKOK,ULOCKOK).
  rewrite map_map in *.
  simpl in *.
  change (fun x : cmd * context * pheap * list (olocation Z) * gheap * Z => pof x) with pof in *.

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
  exists (upd Z.eq_dec t id (Some (Val (Enum a),tx))), (dstr_cells h (map (fun x => (a + (Z.of_nat x))%Z) (seq O n)) (Some 0%Z)).
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
  {
  apply valid_configuration_does_not_abort in VALIDK.
  destruct G as [G|G].
  {
  destruct G as (idvltx,(EQ1,EQ2)).
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
  }

  assert (G': (exists idvltx, ([[x]]) = ([[(snd (fst (fst idvltx)))]]) /\ t (fst (fst (fst idvltx))) = Some (WasWaiting4cond (snd (fst (fst idvltx))) (snd (fst idvltx)), snd idvltx)) \/
    ~ exists idvltx, ([[x]]) = ([[(snd (fst (fst idvltx)))]]) /\ t (fst (fst (fst idvltx))) = Some (WasWaiting4cond (snd (fst (fst idvltx))) (snd (fst idvltx)), snd idvltx)).
  {
  apply classic.
  }
  destruct G' as [G'|G'].
  {
  destruct G' as (idvltx,(eqx,tidv)).

  exists (upd Z.eq_dec (upd Z.eq_dec t id (Some (tt,tx))) (fst (fst (fst idvltx))) (Some (Waiting4lock (snd (fst idvltx)),snd idvltx))), h.
  apply red_Notify01 with x;
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
  unfold not.
  intros.
  apply G.
  destruct H as (id',(v',(l',(tx',(EQ1,EQ2))))).
  exists (id',v',l',tx').
  tauto.
  unfold not.
  intros.
  exists (snd (fst (fst idvltx))).
  exists eqx.
  assumption.
  }

  exists (upd Z.eq_dec t id (Some (tt,tx))), h.
  apply red_Notify0 with x;
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
  unfold not.
  intros.
  apply G.
  destruct H as (id',(v',(l',(tx',(EQ1,EQ2))))).
  exists (id',v',l',tx').
  tauto.
  unfold not.
  intros.
  apply G'.
  destruct H as (id',(v',(l,(tx',(eqx',tid'))))).
  exists (id', v', l, tx').
  rewrite eqx'.
  split.
  reflexivity.
  assumption.
  }

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

  destruct (h ([[l]])) eqn:hl.
  destruct (Z.eq_dec z 1%Z).
  rewrite e in *.
  exists (upd Z.eq_dec t id (Some (tt,tx))), (upd Z.eq_dec h ([[l]]) (Some 0%Z)).
  apply red_WasWait with v.
  assumption.
  assumption.
  simpl in NOWAITING.
  destruct (opZ_eq_dec (h ([[l]])) (Some 1%Z)).
  rewrite e in *.
  inversion hl.
  rewrite H0 in n.
  contradiction.
  inversion NOWAITING.
  apply valid_configuration_does_not_abort in VALIDK.
  exfalso.
  apply VALIDK.
  apply aborts_WasWaiting4cond with v l id tx.
  left.
  assumption.
  assumption.
  exists (upd Z.eq_dec t id (Some (tt,tx))), h.
  apply red_g_initl with x.
  assumption.
  exists (upd Z.eq_dec t id (Some (tt,tx))), h.
  apply red_g_initc with x.
  assumption.
  exists (upd Z.eq_dec t id (Some (tt,tx))), h.
  apply red_g_finlc with x.
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

Theorem initial_configuration_is_valid:
  forall c id invs sp
         (WELLFORMED: wellformed_cmd c)
         (VERIFIED: correct (Aobs nil) c (fun _ => Aobs nil) invs sp),
    validk sp (upd Z.eq_dec (emp (cmd * context)) id (Some (c,done))) (emp Z).
Proof.
  unfold correct.
  unfold validk.
  unfold pheaps_heap.
  unfold gheaps_ok.
  unfold locations_ok.
  unfold invs_ok.
  unfold locks_ok.

  intros.
  assert (SAT: sat (emp knowledge) (Some nil) (emp (option nat * nat)) (weakest_pre sp c (fun _ : Z => Aobs nil) Datatypes.id invs)). 
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
  intros.
  unfold emp in *.
  unfold phplus in *.
  unfold spur_ok.
  split.
  intros.
  destruct IN as [EQ|CO].
  unfold cmdof in EQ.
  simpl in EQ.
  rewrite <- EQ in WASW.
  rewrite WASW in *.
  simpl in SAT.
  destruct SAT as (v0,(v1,(v2,(eql,rest)))).
  apply Coq.Bool.Bool.andb_true_iff in eql.
  destruct eql.
  assumption.
  inversion CO.
  intros.
  unfold emp in *.
  unfold phplus in *.
  inversion CONDv.
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
  split.
  {
  unfold phplus.
  unfold pof.
  unfold emp.
  simpl.
  intros.
  inversion ULOCK.
  }
  unfold phplus.
  unfold emp.
  unfold pof.
  intros.
  inversion UCOND.
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
Hint Resolve WasWait_preserves_validity.
Hint Resolve Notify_preserves_validity.
Hint Resolve Notify0_preserves_validity.
Hint Resolve Notify01_preserves_validity1.
Hint Resolve NotifyAll_preserves_validity.
Hint Resolve SpuriousWakeup_preserves_validity.
Hint Resolve g_initl_preserves_validity.
Hint Resolve g_initc_preserves_validity.
Hint Resolve g_finlc_preserves_validity.
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

Theorem steps_preserve_validity:
  forall sp t h t' h' 
         (VALIDK: validk sp t h) (STEP: red sp t h t' h'),
    validk sp t' h'.
Proof.
  intros.
  destruct STEP; try eauto.
Qed.


(** # <font size="5"><b> Soundness Proof </b></font> # *)

Inductive safe: nat -> thrds -> heap -> Prop :=
  | Base: forall t h, safe O t h
  | Terminated: forall n t h (TER: forall id, t id = None), safe n t h
  | Running: forall n sp t h (NO_RACE: ~ data_race t)
                    (REDUCES: exists t' h', red sp t h t' h')
                    (SAFE: forall t' h' (RED: red sp t h t' h'), safe n t' h'),
               safe (S n) t h.

Theorem valid_configuration_is_safe:
  forall n sp t h (VALIDK: validk sp t h),
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
  assert (G: ~ data_race t /\ exists t' h', red sp t h t' h').
  {
  apply valid_configuration_reduces;
  try tauto.
  }
  destruct G as (norace,(t',(h',red))).
  apply Running with sp.
  tauto.
  exists t', h'.
  tauto.
  intros.
  apply IHn with sp;
  try tauto.
  apply steps_preserve_validity with t h; assumption.
Qed.

Theorem verified_program_is_safe:
  forall n c id invs sp
         (WELLFORMED: wellformed_cmd c)
         (VERIFIED: correct (Aobs nil) c (fun _ => Aobs nil) invs sp),
    safe n (upd Z.eq_dec (emp (cmd * context)) id (Some (c,done))) (emp Z).
Proof.
  intros.
  apply valid_configuration_is_safe with sp.
  apply initial_configuration_is_valid with invs; assumption.
Qed.
