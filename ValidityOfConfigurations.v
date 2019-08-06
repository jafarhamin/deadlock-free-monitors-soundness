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

Set Implicit Arguments.

Local Open Scope nat.

Definition cmdof (athread: (cmd * context * pheap * list (olocation Z) * gheap * Z)) : cmd :=
  fst (fst (fst (fst (fst athread)))).

Definition pof (athread: (cmd * context * pheap * list (olocation Z) * gheap * Z)) : pheap :=
  snd (fst (fst (fst athread))).

Definition oof (athread: (cmd * context * pheap * list (olocation Z) * gheap * Z)) : list (olocation Z) :=
  snd (fst (fst athread)).

Definition Aoof (athread: (cmd * context * pheap * list (olocation Z) * gheap * Z)) : list Z :=
  map (fun x => Aofo x) (snd (fst (fst athread))).

Definition gof (athread: (cmd * context * pheap * list (olocation Z) * gheap * Z)) : gheap :=
  snd (fst athread).

(** # <font size="5"><b> Validity of Configurations </b></font> # *)

Definition pheaps_heap (Pthreads: list (pheap * Z)) (Pinv Pleak: pheap) (h: heap) :=
         defl phplusdef Pthreads /\
         phplusdef Pinv Pleak /\
         (forall p (IN: In p (map fst Pthreads)), phplusdef p Pinv /\ phplusdef p Pleak) /\
         (forall p (IN: In p (map fst Pthreads)), boundph p) /\
         boundph Pinv /\ boundph Pleak /\ boundph (phplus Pinv Pleak) /\
         boundph (fold_left phplus (map fst Pthreads) (phplus Pinv Pleak)) /\
         phtoh (fold_left phplus (map fst Pthreads) (phplus Pinv Pleak)) h.

Definition gheaps_ok (Gthreads: list (gheap * Z)) (Glocks Gleak: gheap) :=
         (defl ghplusdef Gthreads) /\
         (forall g (IN: In g (map fst Gthreads)), ghplusdef g Glocks /\ ghplusdef g Gleak) /\
         (ghplusdef Glocks Gleak) /\
         (boundgh (fold_left ghplus (map fst Gthreads) (ghplus Glocks Gleak))).

Definition locations_ok locations pheaps obs :=
         (injph pheaps) /\
         lcomp locations /\
         (forall l, pheaps l <> None <-> In l locations) /\
         (forall o (IN: In o obs), exists l (EQL: Oof l = o), pheaps l <> None).

Definition locks_ok (pheaps: pheap) obs h :=
         (forall l (LOCK: pheaps l = Some Lock \/  exists wt ot, pheaps l = Some (Locked wt ot) \/ pheaps l = Some (Ulock wt ot)),
            Lof l = Aof l /\ Pof l = false /\ Xof l = None /\ (h (Aof l) <> Some 1%Z -> In (Oof l) obs)) /\
         (forall l wt ot (ULOCK: pheaps l = Some (Ulock wt ot)), h (Aof l) = Some 1%Z /\ ~ In (Oof l) obs) /\
         (forall l (UCOND: pheaps l = Some Ucond), ~ In (Oof l) obs).

Definition spur_ok (p: pheap) sp invs cmds :=
  (forall c v l (IN: In c cmds) (WASW: c = WasWaiting4cond v l), sp = true) /\
  forall v (CONDv: p v = Some Cond),
    exists l (LOF: Lof v = Aof l)
           (pl: p l = Some Lock \/ exists wt ot, p l = Some (Locked wt ot)),
      spurious_ok sp l v invs.

Definition WTs l cmds locs :=
 filterb (xOf (fun x => Lof x) locs) (Aof l) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) cmds)).

Definition OBs l obs locs :=
 filterb (xOf (fun x => Lof x) locs) (Aof l) (count_occ Z.eq_dec obs).

Definition invs_ok Ainv Pinv Ginv (pheaps: pheap) h cmds obs locs invs :=
         NoDup (map snd Ainv) /\
         (forall l (IN: In l (map snd Ainv)), pheaps l = Some Lock /\ h (Aof l) = Some (1%Z)) /\
         (forall l (LOCK: pheaps l = Some Lock) (NOTHELD: h (Aof l) = Some (1%Z)), 
           In (subsas (snd (Iof l)) (invs (fst (Iof l)) (WTs l cmds locs) (OBs l obs locs)),l) Ainv) /\
         (sat Pinv None Ginv (fold_left Astar (map fst Ainv) (Abool true))).

Definition validk (n: nat) (sp: bool) (t:thrds) (h:heap) :=
  exists (T: list (cmd * context * pheap * list (olocation Z) * gheap * Z)) (invs: Z -> inv) (locs: list (location Z))
         (Pinv: pheap) (Pleak: pheap) (Ainv: list (assn * (location Z))) (Ginv: gheap) (Gleak: gheap) 
         (INF: inf_capacity (fold_left ghplus (map gof T) (ghplus Ginv Gleak)) /\ inf_capacity t /\ inf_capacity h)
         (SPUR: spur_ok (fold_left phplus (map pof T) (phplus Pinv Pleak)) sp invs (map cmdof T))
         (PHsOK: pheaps_heap (map (fun x => (pof x, snd x)) T) Pinv Pleak h)
         (GHsOK: gheaps_ok (map (fun x => (gof x, snd x)) T) Ginv Gleak)
         (TOK: forall id c tx, t id = Some (c,tx) <-> exists p O g, In (c,tx,p,O,g,id) T)
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

(** # <font size="5"><b> Steps Preserve Validity of Configurations </b></font> # *)

Definition ctxof (athread: (cmd * context * pheap * list (olocation Z) * gheap * Z)) : context :=
  snd (fst (fst (fst (fst athread)))).

Definition wof h (athread: (cmd * context * pheap * list (olocation Z) * gheap * Z)) : option Z :=
  waiting_for h (fst (fst (fst (fst (fst athread))))).

Lemma pofs:
  forall z p,
    exists x, pof (x, z) = p.
Proof.
  intros.
  exists (Val (Enum 0), done, p, nil, emp (option nat * nat)).
  reflexivity.
Qed.

Lemma gofs:
  forall z g,
    exists x, gof (x, z) = g.
Proof.
  intros.
  exists (Val (Enum 0), done, emp knowledge, nil, g).
  reflexivity.
Qed.

Lemma upd_updl:
  forall (T: list (cmd * context * pheap * list (olocation Z) * gheap * Z)) t id c tx p O C id' c' tx'
         (IN: exists x', In (x', id) T)
         (AUT : forall id c tx, t id = Some (c, tx) <->
                  exists p O C, In (c, tx, p, O, C, id) T),
    upd Z.eq_dec t id (Some (c, tx)) id' = Some (c', tx') <->
   (exists p' O' C', In (c', tx', p', O', C', id') (updl T id (c, tx, p, O, C, id))).
Proof.
  split.
  unfold upd.
  destruct (Z.eq_dec id' id).
  intros.
  rewrite e.
  inversion H.
  exists p, O, C.
  apply in_updl_eq.
  assumption.
  intros.
  apply AUT in H.
  destruct H as (p0, (O0, (C0, IN0))).
  exists p0, O0, C0.
  apply in_updl_neq.
  omega.
  assumption.
  intros.
  destruct H as (p0, (O0, (C0, IN0))).
  unfold upd.
  destruct (Z.eq_dec id' id).
  rewrite e in IN0.
  eapply eq_in_updl_eq in IN0.
  inversion IN0.
  reflexivity.
  apply AUT.
  exists p0, O0, C0.
  eapply in_in_updl_neq.
  apply n.
  apply IN0.
Qed.


(** # <font size="5"><b> Valid Configurations - Valid Wait for Graphs </b></font> # *)

Theorem validConfiguration_validWaitForGraph:
  forall (G: list (Z * list (olocation Z) * Z))
         (locs: list (location Z))
         (COMP: comp locs (fun x => Aof x))
         (INL: forall z o O o' (ING: In (o,O,z) G) (INO: In o' O), In o' (map (fun x => Oof x) locs))
         (SAFE_OBS: forall z o O (IN: In (o,O,z) G),
           exists l (IN: In l locs) (EQ: (Aof l) = o), safe_obs l (length (filter (fun x => ifb (Z.eq_dec x o)) (map (fun x => fst (fst x)) G)))
                (count_occ (olocation_eq_dec Z.eq_dec) (concat (map (fun x => snd (fst x)) G)) (Oof l)) = true)
         (PRCL: forall z o O (ING: In (o,O,z) G), exists l (IN: In l locs) (EQ: (Aof l) = o), prcl (Oof l) O),
    exists (R: Z -> Qc) (P: Z -> bool) (X: Z -> option Qc)
         (ONE: forall z o O (IN: In (o,O,z) G), one_ob (map (fun x => (fst (fst x), map (fun x => Aofo x) (snd (fst x)), snd x)) G) o)
         (SPARE: forall z o O (IN: In (o,O,z) G) (Po: P o = true), spare_ob (map (fun x => (fst (fst x), map (fun x => Aofo x) (snd (fst x)), snd x)) G) o)
         (OWN: forall z o O (IN: In (o,O,z) G) (INX: X o <> None), own_ob (map (fun x => (fst (fst x), map (fun x => Aofo x) (snd (fst x)), snd x)) G) o)
         (PRC: forall z o O (ING: In (o,O,z) G), prc Qc Qlt_bool order_Qc' o (map (fun x => Aofo x) O) R P X), True.
Proof.
  intros.
  assert (COMPOL: comp (map (fun x => Oof x) locs) (fun x => Aofo x)).
  {
  unfold comp in *.
  unfold inj in *.
  intros.
  apply in_map_iff in IN0.
  destruct IN0 as (x1',(EQ1,IN1)).
  apply in_map_iff in IN.
  destruct IN as (x2',(EQ2,IN2)).
  rewrite <- EQ1.
  rewrite <- EQ2.
  assert (G1: x1' = x2').
  {
  apply COMP; try assumption.
  unfold Aof in *.
  unfold Aofo in *.
  simpl.
  rewrite <- EQ1 in H.
  rewrite <- EQ2 in H.
  symmetry.
  assumption.
  }
  rewrite G1.
  reflexivity.
  }

  assert (COMP1: forall l y (IN: In l locs) (IN: In y G), comp (Oof l :: snd (fst y)) (fun x : olocation Z => Aofo x)).
  {
  intros.
  destruct y as ((y1,y2),y3).
  unfold comp in *.
  intros.
  apply COMPOL.
  destruct IN1 as [EQ1|IN1].
  rewrite <- EQ1.
  apply in_map.
  assumption.
  eapply INL.
  apply IN0.
  assumption.
  destruct IN2 as [EQ2|IN2].
  rewrite <- EQ2.
  apply in_map.
  assumption.
  eapply INL.
  apply IN0.
  assumption.
  }

  exists (fun x => lift 0%Qc (xOf (fun x => Rof x) locs x)).
  exists (fun x => lift false (xOf (fun x => Pof x) locs x)).
  exists (fun x => lift None (xOf (fun x => Xof x) locs x)).
  exists.
  {
  intros.
  assert (SA:=IN).
  apply SAFE_OBS in SA.
  destruct SA as (l,(INl,(Aofl,SA))).
  unfold safe_obs in SA.
  unfold one_ob.
  apply Coq.Bool.Bool.andb_true_iff in SA.
  destruct SA as (SA1,SA2).
  rewrite map_map.
  apply Coq.Bool.Bool.orb_true_iff in SA1.
  destruct SA1 as [SA1|SA1].
  apply Nat.eqb_eq in SA1.
  assert (CO: In o (filter (fun x : Z => ifb (Z.eq_dec x o))
           (map (fun x : Z * list (olocation Z) * Z => fst (fst x)) G))).
  {
  apply filter_In.
  split.
  apply in_map_iff.
  exists (o,O,z).
  tauto.
  unfold ifb.
  rewrite eqz.
  reflexivity.
  }
  destruct (filter (fun x : Z => ifb (Z.eq_dec x o))
           (map (fun x : Z * list (olocation Z) * Z => fst (fst x)) G)) eqn:FIL.
  inversion CO.
  inversion SA1.

  apply Nat.ltb_lt in SA1.
  apply count_occ_In in SA1.
  rewrite <- flat_map_concat_map in SA1.
  apply in_flat_map in SA1.
  destruct SA1 as (x,(INx,INxl)).
  apply count_occ_In.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists x.
  split.
  assumption.
  simpl.
  apply in_map_iff.
  exists (Oof l).
  tauto.
  }

  exists.
  {
  intros.
  assert (SA:=IN).
  apply SAFE_OBS in SA.
  destruct SA as (l,(INl,(Aofl,SA))).
  unfold safe_obs in SA.
  unfold one_ob.
  apply Coq.Bool.Bool.andb_true_iff in SA.
  destruct SA as (SA1,SA2).
  apply Coq.Bool.Bool.andb_true_iff in SA2.
  destruct SA2 as (SA2,SA3).
  unfold spare_ob.
  apply Coq.Bool.Bool.orb_true_iff in SA2.
  destruct SA2 as [SA2|SA2].
  {
  unfold negb in SA2.
  rewrite <- Aofl in Po.
  rewrite xOf_same in Po;
  try tauto.
  simpl in Po.
  rewrite Po in SA2.
  inversion SA2.
  apply in_map. assumption.
  apply comp_cons;
  try tauto.
  }

  rewrite map_map.
  apply Coq.Bool.Bool.orb_true_iff in SA2.
  destruct SA2 as [SA2|SA2].
  apply Nat.eqb_eq in SA2.
  assert (CO: In o (filter (fun x : Z => ifb (Z.eq_dec x o))
           (map (fun x : Z * list (olocation Z) * Z => fst (fst x)) G))).
  {
  apply filter_In.
  split.
  apply in_map_iff.
  exists (o,O,z).
  tauto.
  unfold ifb.
  rewrite eqz.
  reflexivity.
  }
  destruct (filter (fun x : Z => ifb (Z.eq_dec x o))
           (map (fun x : Z * list (olocation Z) * Z => fst (fst x)) G)) eqn:FIL.
  inversion CO.
  inversion SA2.
  apply Nat.ltb_lt in SA2.
  rewrite map_map.
  simpl.
  apply le_lt_trans with (length (filter (fun x => ifb (Z.eq_dec x o))
   (map (fun x => fst (fst x)) G))).
  apply count_filter_len.
  unfold ifb.
  rewrite eqz.
  reflexivity.
  eapply lt_le_trans with (count_occ (olocation_eq_dec Z.eq_dec) (concat (map (fun x : Z * list (olocation Z) * Z => snd (fst x)) G)) (Oof l)).
  assumption.
  rewrite count_occ_concat_eq with (eq_dec2:=Z.eq_dec) (f3:=(fun x => Aofo x)).
  replace (Aofo (Oof l)) with (Aof l).
  rewrite Aofl.
  unfold location.
  omega.
  unfold comp.
  reflexivity.
  intros.
  apply COMP1; assumption.
  }

  exists.
  {
  intros.
  assert (SA:=IN).
  apply SAFE_OBS in SA.
  destruct SA as (l,(INl,(Aofl,SA))).
  unfold safe_obs in SA.
  apply Coq.Bool.Bool.andb_true_iff in SA.
  destruct SA as (SA1,SA2).
  apply Coq.Bool.Bool.andb_true_iff in SA2.
  destruct SA2 as (SA2,SA3).
  apply Coq.Bool.Bool.orb_true_iff in SA3.
  destruct SA3 as [SA3|SA3].
  destruct (opQc_eq_dec (Xof l) None).
  rewrite <- Aofl in INX.
  rewrite xOf_same in INX.
  contradiction.
  apply in_map. assumption.
  apply comp_cons;
  try tauto.
  inversion SA3.
  unfold own_ob.
  rewrite map_map.
  rewrite map_map.
  simpl.
  simpl in SA3.
  apply Nat.leb_le in SA3.
  apply le_trans with (length (filter (fun x => ifb (Z.eq_dec x o)) (map (fun x => fst (fst x)) G))).
  apply count_filter_len.
  unfold ifb.
  rewrite eqz.
  reflexivity.
  apply le_trans with (count_occ (olocation_eq_dec Z.eq_dec) (concat (map (fun x => snd (fst x)) G)) (Oof l)).
  assumption.
  rewrite count_occ_concat_eq with (eq_dec2:=Z.eq_dec) (f3:=(fun x => Aofo x)).
  replace (Aofo (Oof l)) with (Aof l).
  rewrite Aofl.
  unfold location.
  omega.
  unfold comp.
  reflexivity.
  intros.
  apply COMP1; assumption.
  }

  exists.
  Focus 2.
  trivial.
  intros.
  assert (PRC:=ING).
  apply PRCL in PRC.
  destruct PRC as (l,(INl,(Aofl,PRCL1))).
  rewrite <- Aofl.
  assert (COMPL: comp (l :: locs) (fun x => Aof x)).
  {
  apply comp_cons;
  try tauto.
  }

  unfold prc.
  unfold prcl in PRCL1.
  destruct (xOf (fun x : location Z => Xof x) locs (Aof l)) eqn:xof.
  {
  simpl.
  assert (xof1:=xof).
  rewrite xOf_same in xof1.
  unfold Xof in xof1.
  inversion xof1.
  rewrite H0 in *.
  destruct o0.
  {
  destruct PRCL1 as (PR1,PR2).
  destruct PR2 as (PR2,PR3).
  split.
  {

  rewrite filter_filter_map_eq with (f2:= fun x => negb (Qlt_bool (Rof l) (Rofo x)) || negb (Qlt_bool q (Rofo x))).
  assumption.
  unfold comp.
  intros.
  apply COMPOL.
  apply INL with z o O;
  try tauto.
  apply INL with z o O;
  try tauto.
  intros.
  rewrite xOf_same;
  try tauto.
  simpl.
  rewrite xOf_sameo with (f':= (fun x => Rofo x));
  try tauto.
  apply INL with z o O;
  try tauto.
  apply comp_conso;
  try tauto.
  apply INL with z o O;
  try tauto.
  simpl.
  apply in_map.
  assumption.
  }
  split.
  {
  intros.
  apply in_map_iff in INX.
  destruct INX as (x0,(EQx0,INx0)).
  assert (INx1:=INx0).
  assert (INx0l: In x0 (map (fun x : location Z => Oof x) locs)).
  {
  apply INL with z o O;
  try tauto.
  }
  apply PR2 in INx0.
  destruct INx0 as [NEG|NEG].
  left.
  rewrite xOf_same;
  try tauto.
  simpl.
  rewrite <- EQx0.
  rewrite xOf_sameo with (f':= fun x => Rofo x);
  try tauto.
  simpl.
  apply comp_conso;
  try tauto.
  apply in_map. assumption.
  right.
  unfold lift.
  simpl.
  rewrite <- EQx0.
  rewrite xOf_same; try tauto.
  rewrite xOf_sameo with (f':= fun x => Xofo x); try tauto.
  apply comp_conso;
  try tauto.
  apply in_map. assumption.
  }

  destruct PR3 as [PR3|PR3].
  left.
  {
  rewrite forallb_forall.
  rewrite forallb_forall in PR3.
  intros.
  apply in_map_iff in H.
  destruct H as (x0,(EQx0,INx0)).
  assert (INx0l: In x0 (map (fun x : location Z => Oof x) locs)).
  {
  apply INL with z o O;
  try tauto.
  }
  assert (LT:=INx0).
  apply PR3 in LT.
  rewrite <- EQx0.
  rewrite xOf_same;
  try tauto.
  rewrite xOf_sameo with (f':= fun x => Rofo x);
  try tauto.
  apply comp_conso;
  try tauto.
  apply in_map. assumption.
  }
  right.
  rewrite xOf_same;
  try tauto.
  apply in_map. assumption.
  }
  rewrite forallb_forall.
  rewrite forallb_forall in PRCL1.
  intros.
  apply in_map_iff in H.
  destruct H as (x0,(EQx0,INx0)).
  assert (INx0l: In x0 (map (fun x : location Z => Oof x) locs)).
  {
  apply INL with z o O;
  try tauto.
  }
  assert (LT:=INx0).
  rewrite <- EQx0.
  rewrite xOf_same;
  try tauto.
  rewrite xOf_sameo with (f':= fun x => Rofo x);
  try tauto.
  simpl.
  apply PRCL1.
  assumption.
  apply comp_conso;
  try tauto.
  apply in_map. assumption.
  apply in_map. assumption.
  apply comp_cons;
  try tauto.
  }
  simpl.
  assert (xof1:=xof).
  rewrite xOf_same in xof1.
  inversion xof1.
  apply in_map. assumption.
  apply comp_cons;
  try tauto.
Qed.

Lemma Cons_preserves_validity:
  forall m sp h t id a n tx
         (VALIDK: validk (S m) sp t h)
         (CMD: t id = Some (Cons n, tx))
         (NIN: forall z' : Z, In z' (map Z.of_nat (seq 0 n)) -> h (a + z')%Z = None),
    validk m sp (upd Z.eq_dec t id (Some (Val (Enum a), tx)))
      (dstr_cells h (map (fun x : nat => (a + Z.of_nat x)%Z) (seq 0 n)) (Some 0%Z)).
Proof.
  intros.
  unfold validk in VALIDK.
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
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.

  assert (tmp: exists p O C, In (Cons n, tx, p, O, C, id) T).
  {
  apply TOK.
  assumption.
  }

  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  destruct WF as (WF1,WF2).
  exists (updl T id (Val (Enum a), tx, dstr_cells' p 
    (map (fun x => (((a + (Z.of_nat x))%Z, 0%Qc, (a + (Z.of_nat x))%Z, None, false), (0%Z,nil), (0%Z,nil), nil)) (seq 0 n))
    (Some (Cell full 0)), O, C, id)).

  exists invs, ((map (fun x => (((a + (Z.of_nat x))%Z, 0%Qc, (a + (Z.of_nat x))%Z, None, false), (0%Z,nil), (0%Z,nil), nil)) (seq 0 n)) ++ locs), Pinv, Pleak, Ainv, Cinv, Cleak.
  simpl in *.
  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.
  subst.

  assert (inp: In p (map pof T)).
  {
  apply in_map_iff.
  exists (Cons n, tx, p, O, C, id).
  tauto.
  }

  assert (inpid: In (p, id) (map (fun x0 => (pof x0, snd x0)) T)).
  {
  apply in_map_iff.
  exists (Cons n, tx, p, O, C, id).
  tauto.
  }

  assert (phpdp0il: forall p0 : pheap, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  apply phpdef_pair; try tauto.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  }

  assert (bp: boundph p).
  {
  apply BPE.
  assumption.
  }

  assert (bg: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); try tauto.
  intros.
  apply ghpdef_pair; try tauto.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (Cons n, tx, p, O, C, id).
  tauto.
  }

  assert (NONE: forall z' (IN: In (Aof z') (map (fun x => ((a + (Z.of_nat x))%Z)) (seq 0 n))),
    fold_left phplus (map pof T) (phplus Pinv Pleak) z' = None).
  {
  assert (PH:=PH2H).
  unfold phtoh in PH.
  destruct PH as (PH,PH1).
  intros.
  specialize PH with z'.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  rewrite <- EQx in *.
  unfold Aof in PH.
  unfold Oof in PH.
  unfold Aofo in PH.
  simpl in PH.

  rewrite NIN in PH.
  destruct (fold_left phplus (map pof T) (phplus Pinv Pleak) z') eqn:fl.
  destruct k; try inversion PH; try contradiction.
  reflexivity.
  apply in_map.
  assumption.
  }

  assert (NONE1: forall p z' (INp: In p (map pof T)) (IN: In (Aof z') (map (fun x => ((a + (Z.of_nat x))%Z)) (seq 0 n))),
    p z' = None).
  {
  intros.
  apply fold_None with (m:=pof) (l:=T) (b:=phplus Pinv Pleak); try tauto.
  apply NONE.
  assumption.
  }

  assert (phpdefpi: phplusdef p Pinv).
  {
  apply PHPD.
  assumption.
  }

  assert (phpdefpl: phplusdef p Pleak).
  {
  apply PHPD.
  assumption.
  }

  assert (pilN: forall z' (IN: In (Aof z') (map (fun x => ((a + (Z.of_nat x))%Z)) (seq 0 n))),
    phplus Pinv Pleak z' = None).
  {
  intros.
  apply fold_None with (m:=pof) (l:=T) (b:=phplus Pinv Pleak); try tauto.
  apply NONE.
  assumption.
  }

  assert (piN: forall z' (IN: In (Aof z') (map (fun x => ((a + (Z.of_nat x))%Z)) (seq 0 n))),
    Pinv z' = None).
  {
  intros.
  apply phplus_None with Pleak.
  apply pilN.
  assumption.
  }

  assert (plN: forall z' (IN: In (Aof z') (map (fun x => ((a + (Z.of_nat x))%Z)) (seq 0 n))),
    Pleak z' = None).
  {
  intros.
  apply phplus_None with Pinv.
  rewrite phplus_comm.
  apply pilN.
  assumption.
  repeat php_.
  }

  assert (NODUP1: NoDup (map snd (updl T id (Val (Enum a), tx, dstr_cells' p 
    (map (fun x => (((a + (Z.of_nat x))%Z, 0%Qc, (a + (Z.of_nat x))%Z, None, false), (0%Z,nil), (0%Z,nil), nil)) (seq 0 n))
    (Some (Cell full 0)), O, C, id)))).
  {
  apply NoDup_updl.
  assumption.
  }

  assert (defl1: defl phplusdef (map (fun x0 => (pof x0, snd x0)) (updl T id (Val (Enum a), tx, dstr_cells' p 
    (map (fun x => (((a + (Z.of_nat x))%Z, 0%Qc, (a + (Z.of_nat x))%Z, None, false), (0%Z,nil), (0%Z,nil), nil)) (seq 0 n))
    (Some (Cell full 0)), O, C, id)))).
  {
  unfold defl.
  unfold updl.
  rewrite map_map.
  intros.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  apply in_map_iff in IN2.
  destruct IN2 as (x2,(EQ2,IN2)).
  unfold pof in *.
  simpl in *.
  destruct (Z.eq_dec (snd x1) id).
  inversion EQ1.
  destruct (Z.eq_dec (snd x2) id).
  inversion EQ2.
  omega.
  inversion EQ2.
  {
  unfold phplusdef.
  intros.
  unfold dstr_cells'.
  destruct (in_dec (location_eq_dec Z.eq_dec) x).
  rewrite NONE1.
  trivial.
  apply in_map_iff.
  exists x2.
  auto.
  apply in_map_iff in i.
  destruct i as (i1,(i2,i3)).
  apply in_map_iff.
  exists i1.
  rewrite <- i2.
  auto.
  apply DEFL with id (snd x2).
  omega.
  assumption.
  apply in_map_iff.
  exists x2.
  auto.
  }

  inversion EQ1.
  destruct (Z.eq_dec (snd x2) id).
  simpl in *.
  inversion EQ2.

  {
  unfold phplusdef.
  intros.
  unfold dstr_cells'.
  destruct (in_dec (location_eq_dec Z.eq_dec) x).
  rewrite NONE1.
  trivial.
  apply in_map_iff.
  exists x1.
  auto.
  apply in_map_iff in i.
  destruct i as (i1,(i2,i3)).
  apply in_map_iff.
  exists i1.
  rewrite <- i2.
  auto.
  apply DEFL with (snd x1) id.
  omega.
  apply in_map_iff.
  exists x1.
  auto.
  assumption.
  }

  inversion EQ2.
  apply DEFL with (snd x1) (snd x2).
  omega.
  apply in_map_iff.
  exists x1.
  auto.
  apply in_map_iff.
  exists x2.
  auto.
  }

  assert (phpdefpil: phplusdef p (phplus Pinv Pleak)).
  {
  apply phpdef_pair; try tauto;
  apply PHPD; try tauto.
  }

  assert (phpdefp0il: forall p0, In p0 (map pof (updl T id (Val (Enum a), tx, dstr_cells' p 
    (map (fun x => (((a + (Z.of_nat x))%Z, 0%Qc, (a + (Z.of_nat x))%Z, None, false), (0%Z,nil), (0%Z,nil), nil)) (seq 0 n))
    (Some (Cell full 0)), O, C, id))) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  unfold updl.
  rewrite map_map.
  intros.
  apply in_map_iff in H.
  destruct H as (x0,(EQ,IN)).
  destruct (Z.eq_dec (snd x0) id).
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  {
  unfold phplusdef.
  intros.
  unfold dstr_cells'.
  destruct (in_dec (location_eq_dec Z.eq_dec) x).
  rewrite pilN; try assumption.
  apply in_map_iff in i.
  destruct i as (i1,(i2,i3)).
  apply in_map_iff.
  exists i1.
  rewrite <- i2.
  auto.
  apply phpdp0il; try assumption.
  }
  apply phpdp0il; try assumption.
  apply in_map_iff.
  exists x0.
  auto.
  }

  assert (ina: forall x (IN: In x (map (fun x : nat => ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))),
    In (Aof x) (map (fun x0 : nat => (a + Z.of_nat x0)%Z) (seq 0 n))).
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (y1,(y2,y3)).
  rewrite <- y2.
  apply in_map_iff.
  exists y1.
  auto.
  }


  assert (CELL: forall z' (IN: In z' (map (fun x => (((a + (Z.of_nat x))%Z, 0%Qc, (a + (Z.of_nat x))%Z, None, false), (0%Z,nil), (0%Z,nil), nil)) (seq 0 n))),
    fold_left phplus (map pof (updl T id (Val (Enum a), tx, dstr_cells' p 
    (map (fun x => (((a + (Z.of_nat x))%Z, 0%Qc, (a + (Z.of_nat x))%Z, None, false), (0%Z,nil), (0%Z,nil), nil)) (seq 0 n))
    (Some (Cell full 0)), O, C, id))) (phplus Pinv Pleak)
    z' = Some (Cell full 0)).
  {
  intros.
  apply fold_cell_full with (dstr_cells' p
       (map
          (fun x : nat =>
           ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
           (0%Z, nil), (0%Z, nil), nil)) (seq 0 n)) (Some (Cell full 0))) id; repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (Val (Enum a), tx, dstr_cells' p (map (fun x : nat =>
    ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n)) (Some (Cell full 0)), O, C, id).
  split. reflexivity.
  unfold updl.
  apply in_map_iff.
  exists (Cons n, tx, p, O, C, id).
  simpl.
  rewrite eqz.
  auto.
  unfold dstr_cells'.
  destruct (in_dec (location_eq_dec Z.eq_dec) z'  (map
    (fun x : nat => ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  reflexivity.
  contradiction.
  intros.
  apply NONE1.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  inversion EQx.
  omega.
  inversion EQx.
  apply in_map_iff.
  exists x. auto.
  apply ina.
  assumption.
  unfold phplus.
  rewrite piN, plN.
  reflexivity.
  apply ina. assumption.
  apply ina. assumption.
  }

  assert (phpdpsi: phplusdef (dstr_cells' p (map (fun x : nat =>
    ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n)) (Some (Cell full 0))) Pinv).
  {
  unfold phplusdef.
  intros.
  unfold dstr_cells'.
  destruct (in_dec (location_eq_dec Z.eq_dec) x).
  rewrite piN.
  trivial.
  apply ina.
  assumption.
  apply PHPD.
  assumption.
  }

  assert (phpdpsl: phplusdef (dstr_cells' p (map (fun x : nat =>
    ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n)) (Some (Cell full 0))) Pleak).
  {
  unfold phplusdef.
  intros.
  unfold dstr_cells'.
  destruct (in_dec (location_eq_dec Z.eq_dec) x).
  rewrite plN.
  trivial.
  apply ina.
  assumption.
  apply PHPD.
  assumption.
  }

  assert (phpp0il: forall p0 : pheap, In p0 (map pof (updl T id (Val (Enum a), tx,
     dstr_cells' p (map (fun x : nat => ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
     (0%Z, nil), (0%Z, nil), nil)) (seq 0 n)) (Some (Cell full 0)),
     O, C, id))) -> phplusdef p0 Pinv /\ phplusdef p0 Pleak).
  {
  unfold updl.
  rewrite map_map.
  intros.
  apply in_map_iff in H.
  destruct H as (x1,(EQ,IN)).
  destruct (Z.eq_dec (snd x1) id).
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  auto.
  rewrite <- EQ.
  apply PHPD.
  apply in_map.
  assumption.
  }

  assert (EQH: forall z' (NIN: ~ In z' (map (fun x => (((a + (Z.of_nat x))%Z, 0%Qc, (a + (Z.of_nat x))%Z, None, false), (0%Z,nil), (0%Z,nil), nil)) (seq 0 n))),
    fold_left phplus (map pof (updl T id (Val (Enum a), tx, dstr_cells' p 
    (map (fun x => (((a + (Z.of_nat x))%Z, 0%Qc, (a + (Z.of_nat x))%Z, None, false), (0%Z,nil), (0%Z,nil), nil)) (seq 0 n))
    (Some (Cell full 0)), O, C, id))) (phplus Pinv Pleak)
    z' = fold_left phplus (map pof T) (phplus Pinv Pleak) z').
  {
  intros.
  apply eq_heap_dstr with (p:=p) (a:=a) (n:= n); repeat php_.
  apply pofs.
  intros.
  unfold phplusdef.
  intros.
  unfold dstr_cells'.
  destruct (in_dec (location_eq_dec Z.eq_dec) x).
  rewrite NONE1.
  trivial.
  apply in_map_iff.
  apply in_map_iff in IN.
  destruct IN as (y1,(y2,y3)).
  inversion y2.
  exists y1.
  auto.
  apply ina.
  assumption.
  apply DEFL with id' id.
  omega.
  assumption.
  assumption.
  }

  assert (bfp: boundph (fold_left phplus (map pof (updl T id
   (Val (Enum a), tx, dstr_cells' p (map (fun x : nat => ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
   (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))(Some (Cell full 0)), O, C, id))) (phplus Pinv Pleak))).
  {
  unfold boundph.
  unfold dstr_cells'.
  intros.
  destruct (In_dec (location_eq_dec Z.eq_dec ) x (map (fun x : nat =>
    ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  {
  rewrite CELL in H.
  inversion H.
  unfold full;
  simpl;
  unfold Qcanon.Qclt;
  unfold QArith_base.Qlt;
  unfold Qcanon.Qcle;
  unfold QArith_base.Qle;
  simpl;
  omega.
  assumption.
  }
  rewrite EQH in H; try assumption.
  eapply BPT.
  apply H.
  }

  assert (EQG: map (fun x0 => (gof x0, snd x0))
    (updl T id (Val (Enum a), tx, dstr_cells' p 
    (map (fun x => (((a + (Z.of_nat x))%Z, 0%Qc, (a + (Z.of_nat x))%Z, None, false), (0%Z,nil), (0%Z,nil), nil)) (seq 0 n))
    (Some (Cell full 0)), O, C, id)) =
    map (fun x0 => (gof x0, snd x0)) T).
  {
  unfold updl.
  rewrite map_map.
  unfold gof.
  simpl.
  apply map_ext_in.
  intros.
  destruct a0 as (a0,id').
  simpl.
  destruct (Z.eq_dec id' id).
  rewrite e.

  assert (EQA: a0 = (Cons n, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }

  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQG': map gof (updl T id (Val (Enum a), tx, dstr_cells' p 
    (map (fun x => (((a + (Z.of_nat x))%Z, 0%Qc, (a + (Z.of_nat x))%Z, None, false), (0%Z,nil), (0%Z,nil), nil)) (seq 0 n))
    (Some (Cell full 0)), O, C, id)) = map gof T).
  {
  unfold updl.
  rewrite map_map.
  unfold gof.
  simpl.
  apply map_ext_in.
  intros.
  destruct a0 as (a0,id').
  simpl.
  destruct (Z.eq_dec id' id).

  assert (EQA: a0 = (Cons n, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }

  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQO: forall p, map oof (updl T id (Val (Enum a), tx, p, O, C, id)) = map oof T).
  {
  intros.
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a0 as (a0,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a0 = (Cons n, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQAO: forall p, map Aoof (updl T id (Val (Enum a), tx, p, O, C, id)) = map Aoof T).
  {
  intros.
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a0 as (a0,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a0 = (Cons n, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQFIL: forall x p, length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) x))
    (map cmdof (updl T id (Val (Enum a), tx, p, O, C, id)))) = 
    length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) x)) (map cmdof T))).
  {
  intros.
  unfold updl.
  rewrite map_map.
  apply filter_map_eq.
  intros.
  destruct x0 as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  rewrite e in *.
  assert (EQX: (a1, a2, a3, a4, a5) = (Cons n, tx, p, O, C)).
  apply unique_key_eq with T a6; try tauto.
  rewrite e.
  assumption.
  rewrite e.
  assumption.
  inversion EQX.
  reflexivity.
  reflexivity.
  }

  assert (WT0: forall d0 (IND: In d0 (map (fun x0 => ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))),
    length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some (Aof d0))))
     (map cmdof T)) = 0%nat).
  {
  intros.
  destruct (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some (Aof d0))))
    (map cmdof T)) eqn:FIL.
  reflexivity.
  assert (CO: In c (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some (Aof d0))))
    (map cmdof T))).
  {
  rewrite FIL.
  left.
  reflexivity.
  }
  apply filter_In in CO.
  destruct CO as (CO,CO1).
  unfold ifb in CO1.

  destruct (opZ_eq_dec (waiting_for_cond c) (Some (Aof d0))).
  {
  destruct c;
  inversion e.
  {
  apply in_map_iff in CO.
  destruct CO as (y,(EQy,INy)).
  destruct y as (((((y1,y2),y3),y4),y5),y6).
  unfold cmdof in EQy.
  simpl in EQy.
  rewrite EQy in *.
  assert (tmp:=INy).
  apply SOBS in tmp.
  destruct tmp as (wf1,(sat1,sobs1)).

  apply sat_wait4cond in sat1.
  destruct sat1 as (ll,(v0,(aofl,(aofv0,(pv0,rest))))).
  rewrite H0 in aofv0.
  rewrite <- aofv0 in *.
  rewrite NONE1 in pv0.
  inversion pv0.
  apply in_map_iff.
  exists (Waiting4cond v l0, y2, y3, y4, y5, y6).
  auto.
  apply in_map_iff in IND.
  destruct IND as (d1,(d2,d3)).
  apply in_map_iff.
  exists d1.
  rewrite aofv0.
  rewrite <- d2.
  auto.
  }
  {
  apply in_map_iff in CO.
  destruct CO as (y,(EQy,INy)).
  destruct y as (((((y1,y2),y3),y4),y5),y6).
  unfold cmdof in EQy.
  simpl in EQy.
  rewrite EQy in *.
  assert (tmp:=INy).
  apply SOBS in tmp.
  destruct tmp as (wf1,(sat1,sobs1)).
  apply sat_WasWaiting4cond in sat1.
  destruct sat1 as (ll,(lv,(aofll,(aoflv,(loflv,(pll,(plv,rest))))))).
  rewrite H0 in aoflv.
  rewrite <- aoflv in *.
  rewrite NONE1 in plv.
  inversion plv.
  apply in_map_iff.
  exists (WasWaiting4cond v l0, y2, y3, y4, y5, y6).
  auto.
  apply in_map_iff in IND.
  destruct IND as (d1,(d2,d3)).
  apply in_map_iff.
  exists d1.
  rewrite aoflv.
  rewrite <- d2.
  auto.
  }
  }
  inversion CO1.
  }

  assert (EQWT: forall l0, WTs l0 (map cmdof (updl T id (Val (Enum a), tx, dstr_cells' p 
    (map (fun x => (((a + (Z.of_nat x))%Z, 0%Qc, (a + (Z.of_nat x))%Z, None, false), (0%Z,nil), (0%Z,nil), nil)) (seq 0 n))
    (Some (Cell full 0)), O, C, id)))
    ((map (fun x => (((a + (Z.of_nat x))%Z, 0%Qc, (a + (Z.of_nat x))%Z, None, false), (0%Z,nil), (0%Z,nil), nil)) (seq 0 n)) ++ locs) =
    WTs l0 (map cmdof T) locs).
  {
  unfold WTs.
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.
  rewrite EQFIL.
  destruct (xOf (fun x1 => Lof x1) locs x) eqn:xof.

  assert (xof1: xOf (fun x1 => Lof x1)
    (map (fun x0 : nat => ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n) ++ locs) x = Some z).
  {
  apply xof_mon'.
  assumption.
  unfold comp.
  intros.
  apply in_app_iff in IN.
  apply in_app_iff in IN0.
  destruct IN as [IN1|IN1].
  destruct IN0 as [IN2|IN2].
  apply INJ;
  apply LOCs; assumption.
  unfold inj.
  intros.
  apply LOCs in IN1.
  rewrite NONE in IN1.
  contradiction.
  rewrite H.
  apply in_map_iff in IN2.
  destruct IN2 as (x3,(EQx,INx)).
  apply in_map_iff.
  exists x3.
  inversion EQx.
  auto.
  destruct IN0 as [IN2|IN2].
  unfold inj.
  intros.
  apply LOCs in IN2.
  rewrite NONE in IN2.
  contradiction.
  rewrite <- H.
  apply in_map_iff in IN1.
  destruct IN1 as (x3,(EQx,INx)).
  apply in_map_iff.
  exists x3.
  inversion EQx.
  auto.

  unfold inj.
  intros.
  apply in_map_iff in IN1.
  destruct IN1 as (x3,(EQx,INx)).
  apply in_map_iff in IN2.
  destruct IN2 as (x4,(EQx4,INx4)).
  inversion EQx.
  inversion EQx4.
  rewrite <- H0 in H.
  rewrite <- H1 in H.
  unfold Aof, Aofo, Oof in H.
  simpl in H.
  rewrite H.
  reflexivity.
  }
  rewrite xof1.
  reflexivity.

  assert (G: xOf (fun x0 => Lof x0) (map (fun x0 : nat => ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n) ++ locs) x =
    xOf (fun x0 => Lof x0) (map (fun x0 : nat => ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n)) x \/
    xOf (fun x0 => Lof x0) (map (fun x0 : nat => ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n) ++ locs) x =
    xOf (fun x0 => Lof x0) locs x).
  {
  apply xof_app_or.
  }
  destruct G as [G|G].
  Focus 2.
  rewrite G.
  rewrite xof.
  reflexivity.
  rewrite G.


  destruct (xOf (fun x0 : location Z => Lof x0) (map (fun x0 : nat =>
    ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n)) x) eqn:xof2; try reflexivity.
  destruct (Z.eq_dec x (Aof l0)); try reflexivity.
  destruct (Z.eq_dec z (Aof l0)); try reflexivity.
  assert (G1: exists x' (IN: In x' (map (fun x0 : nat =>
   ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
   (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))) (EQ1: Aof x' = x), Lof x' = z).
  {
  apply xOf_exists.
  assumption.
  }
  destruct G1 as (d,(INd,(Aofd,Lofd))).
  rewrite <- Aofd in *.

  apply WT0.
  assumption.
  }

  assert (EQCNT: forall p x, count_occ Z.eq_dec (concat (map Aoof (updl T id (Val (Enum a), tx, p, O, C, id)))) x =
    count_occ Z.eq_dec (concat (map Aoof T)) x).
  {
  intros.
  symmetry.
  apply count_updl_eq.
  intros.
  assert (X': x' = (Cons n, tx, p, O, C, id)).
  apply in_elem with T; try assumption.
  rewrite X'.
  reflexivity.
  }

  assert (EQOT: forall l0,
    OBs l0 (concat (map Aoof T)) ((map (fun x => (((a + (Z.of_nat x))%Z, 0%Qc, (a + (Z.of_nat x))%Z, None, false), (0%Z,nil), (0%Z,nil), nil)) (seq 0 n)) ++ locs) =
    OBs l0 (concat (map Aoof T)) locs).
  {
  unfold OBs.
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.
  destruct (xOf (fun x1 => Lof x1) locs x) eqn:xof.
  {
  assert (xof1: xOf (fun x0 : location Z => Lof x0)
    (map (fun x0 : nat => ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n) ++ locs) x = Some z).
  {
  apply xof_mon'.
  assumption.
  unfold comp.
  unfold inj.
  intros.
  apply in_app_iff in IN.
  apply in_app_iff in IN0.
  destruct IN as [IN1|IN1].
  destruct IN0 as [IN2|IN2].
  apply INJ; try assumption.
  apply LOCs; assumption.
  apply LOCs; assumption.
  apply LOCs in IN1.
  rewrite NONE in IN1.
  contradiction.
  rewrite H.
  apply ina. assumption.
  destruct IN0 as [IN2|IN2].
  apply LOCs in IN2.
  rewrite NONE in IN2.
  contradiction.
  rewrite <- H.
  apply ina. assumption.
  apply in_map_iff in IN1.
  destruct IN1 as (y1,(y2,y3)).
  apply in_map_iff in IN2.
  destruct IN2 as (y4,(y5,y6)).
  rewrite <- y2 in *.
  rewrite <- y5 in *.
  unfold Aof, Aofo, Oof in H.
  inversion H.
  reflexivity.
  }
  rewrite xof1.
  reflexivity.
  }

  assert (G: xOf (fun x0 => Lof x0) (map (fun x0 : nat => ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n) ++ locs) x =
    xOf (fun x0 => Lof x0) (map (fun x0 : nat => ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n)) x \/
    xOf (fun x0 => Lof x0) (map (fun x0 : nat => ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n) ++ locs) x =
    xOf (fun x0 => Lof x0) locs x).
  {
  apply xof_app_or.
  }
  destruct G as [G|G].
  Focus 2.
  rewrite G.
  rewrite xof.
  reflexivity.
  rewrite G.

  destruct (xOf (fun x0 : location Z => Lof x0) (map
    (fun x0 : nat => ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n)) x) eqn:xof2.
  destruct (Z.eq_dec x (Aof l0)); try reflexivity.
  destruct (Z.eq_dec z (Aof l0)); try reflexivity.
  assert (G1: exists x' (IN: In x' (map (fun x0 : nat =>
   ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
   (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))) (EQ1: Aof x' = x), Lof x' = z).
  {
  apply xOf_exists.
  assumption.
  }
  destruct G1 as (d,(INd,(Aofd,Lofd))).
  apply count_occ_not_In.
  unfold not.
  intros.
  rewrite <- flat_map_concat_map in H.
  apply in_flat_map in H.
  destruct H as (y1,(y2,y3)).
  rewrite <- Aofd in y3.
  unfold Aoof in y3.
  apply in_map_iff in y3.
  destruct y3 as (y3,(y4,y5)).

  assert (G2: exists (l : location Z) (_ : Oof l = y3),
    fold_left phplus (map pof T) (phplus Pinv Pleak) l <> None).
  {
  apply OBsOK.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists y1.
  auto.
  }
  destruct G2 as (ll,(oofll,CO)).
  rewrite NONE in CO.
  contradiction.
  apply in_map_iff.
  apply in_map_iff in INd.
  destruct INd as (d1,(d2,d3)).
  exists d1.
  rewrite <- d2 in *.
  unfold Aof, Aofo, Oof in y4.
  simpl in y4.
  rewrite <- y4.
  rewrite <- oofll.
  auto.
  reflexivity.
  }

  rewrite EQG.
  rewrite EQG'.
  rewrite EQO.
  rewrite EQAO.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.

  apply red_Cons; try assumption.
  }

  exists.
  {
  destruct SPUR as (SPUR1,SPUR2).
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
  destruct (In_dec (location_eq_dec Z.eq_dec ) v (map (fun x : nat =>
    ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  {
  rewrite CELL in CONDv.
  inversion CONDv.
  assumption.
  }
  rewrite EQH in CONDv; try assumption.
  apply SPUR2 in CONDv.
  destruct CONDv as (l,(lofv,(lkd,spr))).
  exists l, lofv.
  rewrite EQH.
  exists lkd.
  assumption.
  unfold not.
  intros.
  rewrite NONE in lkd.
  destruct lkd as [CO|CO].
  inversion CO.
  destruct CO as (wt,(ot,CO)).
  inversion CO.
  apply in_map_iff in H.
  destruct H as (y1,(y2,y3)).
  apply in_map_iff.
  exists y1.
  rewrite <- y2.
  auto.
  }

  exists.
  {
  exists. assumption.
  exists. tauto.
  exists. assumption.
  split.
  unfold updl.
  rewrite map_map.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ,IN)).
  destruct (Z.eq_dec (snd x1) id).
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  {
  unfold boundph.
  unfold dstr_cells'.
  intros.
  destruct (in_dec (location_eq_dec Z.eq_dec) x).
  inversion H0.
  split;
  unfold full;
  simpl;
  unfold Qcanon.Qclt;
  unfold QArith_base.Qlt;
  unfold Qcanon.Qcle;
  unfold QArith_base.Qle;
  simpl;
  omega.
  apply BPE with p x z; assumption.
  }
  rewrite <- EQ.
  apply BPE.
  apply in_map_iff.
  exists x1. auto.
  split. auto.
  split. auto.
  split. auto.
  split. assumption.

  assert (PH:=PH2H).
  destruct PH as (PH,PH1).
  split.
  {
  intros.
  specialize PH with l.
  destruct (In_dec (location_eq_dec Z.eq_dec ) l (map (fun x : nat =>
    ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  {
  rewrite CELL; try assumption.
  unfold dstr_cells.
  simpl.
  destruct (in_dec Z.eq_dec (Aof l) (map (fun x : nat => (a + Z.of_nat x)%Z) (seq 0 n))).
  reflexivity.
  exfalso.
  apply n0.
  apply ina.
  assumption.
  }
  rewrite EQH; try assumption.
  unfold dstr_cells.
  destruct (in_dec Z.eq_dec (Aof l)
        (map (fun x : nat => (a + Z.of_nat x)%Z) (seq 0 n))).
  rewrite NONE; try assumption.
  assumption.
  }
  intros.
  unfold dstr_cells.
  destruct (in_dec Z.eq_dec z (map (fun x : nat => (a + Z.of_nat x)%Z) (seq 0 n))).

  specialize NONE0 with (z, 0%Qc, z, None, false, (0%Z, nil), (0%Z, nil), nil).
  rewrite CELL in NONE0.
  assert (CO: Some (Cell full 0) = None).
  apply NONE0.
  reflexivity.
  inversion CO.
  apply in_map_iff in i.
  destruct i as (y1,(y2,y3)).
  apply in_map_iff.
  exists y1.
  rewrite <- y2.
  auto.
  apply PH1.
  intros.
  rewrite <- EQH.
  apply NONE0.
  assumption.
  unfold not.
  intros.
  apply n0.
  rewrite <- EQ.
  apply ina.
  assumption.
  }

  exists.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  assumption.
  exists.
  intros.
  apply upd_updl. exists (Cons n, tx, p, O, C). tauto. assumption.
  exists. assumption.
  exists.
  exists. assumption.
  exists.
  {
  intros.
  apply AinvOK in IN.
  destruct IN as (IN1,IN2).
  destruct (In_dec (location_eq_dec Z.eq_dec ) l (map (fun x : nat =>
    ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  {
  rewrite NONE in IN1; try assumption.
  inversion IN1.
  apply ina; assumption.
  }
  rewrite EQH; try assumption.
  split. assumption.
  unfold dstr_cells.
  destruct (in_dec Z.eq_dec (Aof l) (map (fun x : nat => (a + Z.of_nat x)%Z) (seq 0 n))).
  rewrite NONE in IN1; try assumption.
  inversion IN1.
  assumption.
  }
  exists.
  {
  intros.
  unfold WTs in EQWT.
  rewrite EQWT.
  unfold OBs in EQOT.
  rewrite EQOT.
  apply INAOK.
  rewrite <- EQH.
  assumption.
  unfold not.
  intros.
  rewrite CELL in LOCK; try assumption.
  inversion LOCK.
  unfold dstr_cells in NOTHELD.
  destruct (in_dec Z.eq_dec (Aof l)).
  inversion NOTHELD.
  assumption.
  }
  assumption.
  exists.
  {
  exists.
  {
  unfold injph.
  unfold inj.
  intros.
  destruct (In_dec (location_eq_dec Z.eq_dec ) x1 (map (fun x : nat =>
    ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  {
  destruct (In_dec (location_eq_dec Z.eq_dec ) x2 (map (fun x : nat =>
    ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  {
  apply in_map_iff in i.
  destruct i as (y1,(y2,y3)).
  rewrite <- y2 in *.
  apply in_map_iff in i0.
  destruct i0 as (y4,(y5,y6)).
  rewrite <- y5 in *.
  unfold Aof, Aofo, Oof in H.
  simpl in H.
  rewrite H.
  reflexivity.
  }
  rewrite EQH in px2; try assumption.
  rewrite NONE in px2; try assumption.
  contradiction.
  rewrite <- H.
  apply ina.
  assumption.
  }
  rewrite EQH in px1; try assumption.
  destruct (In_dec (location_eq_dec Z.eq_dec ) x2 (map (fun x : nat =>
    ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  {
  rewrite NONE in px1; try assumption.
  contradiction.
  rewrite H.
  apply ina.
  assumption.
  }
  rewrite EQH in px2; try assumption.
  apply INJ; try assumption.
  }
  exists.
  {
  unfold lcomp.
  simpl.
  intros.
  apply in_app_iff in IN.
  destruct IN as [IN|IN].
  apply in_map_iff.
  exists x.
  split.
  apply in_map_iff in IN.
  destruct IN as (y1,(y2,y3)).
  rewrite <- y2.
  reflexivity.
  apply in_app_iff.
  left.
  assumption.
  apply LCOM in IN.
  apply in_map_iff in IN.
  destruct IN as (y1,(y2,y3)).
  rewrite <- y2.
  apply in_map_iff.
  exists y1.
  split.
  reflexivity.
  apply in_app_iff.
  right.
  assumption.
  }
  exists.
  {
  intros.
  destruct (In_dec (location_eq_dec Z.eq_dec ) l (map (fun x : nat =>
    ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  split.
  intros.
  {
  apply in_app_iff.
  left. assumption.
  }
  intros.
  rewrite CELL; try assumption.
  apply some_none.
  rewrite EQH; try assumption.
  split.
  intros.
  apply LOCs in H.
  apply in_app_iff.
  right. assumption.
  intros.
  apply LOCs.
  apply in_app_iff in H.
  destruct H.
  contradiction.
  assumption.
  }
  intros.
  apply OBsOK in IN.
  destruct IN as (l',(EQl',pl')).
  exists l', EQl'.
  destruct (In_dec (location_eq_dec Z.eq_dec ) l' (map (fun x : nat =>
    ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  rewrite CELL; try assumption.
  apply some_none.
  rewrite EQH; try assumption.
  }
  exists.
  {
  exists.
  {
  intros.
  destruct (In_dec (location_eq_dec Z.eq_dec ) l (map (fun x : nat =>
    ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  rewrite CELL in LOCK; try assumption.
  destruct LOCK as [CO|CO].
  inversion CO.
  destruct CO as (wt,(ot,CO)).
  destruct CO as [CO|CO];
  inversion CO.
  rewrite EQH in LOCK; try assumption.
  assert (tmp:=LOCK).
  apply LOCKOK in LOCK.
  destruct LOCK as (l1,(l2,(l3,l4))).
  split. assumption.
  split. assumption.
  split. assumption.
  intros.
  apply l4.
  unfold dstr_cells in H.
  destruct (in_dec Z.eq_dec (Aof l) (map (fun x : nat => (a + Z.of_nat x)%Z) (seq 0 n))).
  rewrite NONE in tmp; try assumption.
  destruct tmp as [CO|CO].
  inversion CO.
  destruct CO as (wt,(ot,CO)).
  destruct CO as [CO|CO];
  inversion CO.
  assumption.
  }
  split.
  {
  intros.
  destruct (In_dec (location_eq_dec Z.eq_dec ) l (map (fun x : nat =>
    ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  rewrite CELL in ULOCK; try assumption.
  inversion ULOCK.
  rewrite EQH in ULOCK; try assumption.
  unfold dstr_cells.
  destruct (in_dec Z.eq_dec (Aof l) (map (fun x : nat => (a + Z.of_nat x)%Z) (seq 0 n))).
  rewrite NONE in ULOCK; try assumption.
  inversion ULOCK.
  apply ULOCKOK with wt ot; try assumption.
  }
  intros.
  destruct (In_dec (location_eq_dec Z.eq_dec ) l (map (fun x : nat =>
    ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  rewrite CELL in UCOND; try assumption.
  inversion UCOND.
  rewrite EQH in UCOND; try assumption.
  apply UCONDOK; assumption.
  }
  exists.
  {
  intros.
  destruct (In_dec (location_eq_dec Z.eq_dec ) l (map (fun x : nat =>
    ((a + Z.of_nat x)%Z, 0%Qc, (a + Z.of_nat x)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  {
  rewrite CELL in ULOCKED; try assumption.
  destruct ULOCKED as [CO|CO]; inversion CO.
  }
  rewrite EQH in ULOCKED; try assumption.
  unfold WTs in EQWT.
  rewrite EQWT.
  unfold OBs in EQOT.
  rewrite EQOT.
  apply WTsOTsOK; assumption.
  }
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  {
  inversion EQx.
  rewrite <- H1.
  split. unfold wellformed. simpl. split. trivial. assumption.
  split.
  {
  rewrite <- H3, <- H4.
  destruct m; try reflexivity.
  apply sat_Cons; repeat php_.
  intros.
  apply NONE1; try assumption.
  apply ina. assumption.
  simpl.
  intros.
  apply sat_tx_weak_imp1; try assumption.
  apply WP with O'; try assumption.
  }
  intros.
  inversion W4COND.
  }
  rewrite EQx in INx.
  assert (IN1:=INx).
  apply SOBS in INx.
  destruct INx as (wf1,(sat1,safe1)).
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
  apply sat1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.

  intros.
  apply safe1 in W4COND.
  destruct W4COND as (v,(l,(inv,(inl,(aovv,(aovl,safeo1)))))).
  exists v,l.
  exists.
  apply in_app_iff. right. assumption.
  exists.
  apply in_app_iff. right. assumption.
  exists aovv,aovl.
  unfold WTs in EQWT.
  rewrite EQWT.
  unfold OBs in EQOT.
  rewrite EQOT.
  assumption.
Qed.


Lemma Lookup_preserves_validity:
  forall m sp h t id tx e vl
         (VALIDK: validk (S m) sp t h)
         (CMD: t id = Some (Lookup e, tx))
         (ALC: h ([[e]]) = Some vl),
    validk m sp (upd Z.eq_dec t id (Some (Val (Enum vl), tx))) h.
Proof.
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
  unfold WTs, OBs.
  unfold validk.

  assert (tmp: exists p O C, In (Lookup e, tx, p, O, C, id) T).
  apply TOK.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.

  exists (updl T id (Val (Enum vl), tx, p, O, C, id)).
  exists invs, locs, Pinv, Pleak, Ainv, Cinv, Cleak.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (EQC: map gof (updl T id (Val (Enum vl), tx, p, O, C, id)) = map gof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Lookup e, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQC': map (fun x => (gof x, snd x)) (updl T id (Val (Enum vl), tx, p, O, C, id)) = map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Lookup e, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e0.
  reflexivity.
  reflexivity.
  }

  assert (EQH: map pof (updl T id (Val (Enum vl), tx, p, O, C, id)) = map pof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Lookup e, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQH': map (fun x => (pof x, snd x)) (updl T id (Val (Enum vl), tx, p, O, C, id)) = map (fun x => (pof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Lookup e, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e0.
  reflexivity.
  reflexivity.
  }

  assert (EQAO: map Aoof (updl T id (Val (Enum vl), tx, p, O, C, id)) = map Aoof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Lookup e, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQOO: map oof (updl T id (Val (Enum vl), tx, p, O, C, id)) = map oof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Lookup e, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQFIL: forall e, length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some e))) (map cmdof T)) =
    length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some e))) (map cmdof (updl T id (Val (Enum vl), tx, p, O, C, id))))).
  {
  unfold updl.
  rewrite map_map.
  intros.
  apply length_filter_map_eq.
  intros.
  destruct (Z.eq_dec (snd a) id).
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl in e1.
  assert (EQA: (a1,a2,a3,a4,a5) = (Lookup e, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply IN.
  rewrite e1.
  assumption.
  assumption.
  }
  inversion EQA.
  unfold cmdof. simpl.
  reflexivity. reflexivity.
  }

  assert (EQWT: forall l, WTs l (map cmdof T) locs = 
    WTs l (map cmdof (updl T id (Val (Enum vl), tx, p, O, C, id))) locs).
  {
  unfold WTs.
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.
  destruct (xOf (fun x : location Z => Lof x) locs x); try reflexivity.
  destruct (Z.eq_dec x (Aof l)); try reflexivity.
  destruct (Z.eq_dec z (Aof l)).
  apply EQFIL. reflexivity.
  }

  rewrite EQH, EQH', EQC, EQC', EQAO, EQOO.
  simpl in *.

  assert (bp: boundph p).
  {
  apply BPE.
  apply in_map_iff.
  exists (Lookup e, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  assert (bg0: boundgh C).
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
  exists (Lookup e, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  apply red_Lookup with e; try assumption.
  }
  exists.
  {
  unfold spur_ok.
  destruct SPUR as (SPUR1,SPUR2).
  split; intros.
  eapply SPUR1 with (c:=c).
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  unfold cmdof in EQx.
  simpl in EQx.
  inversion EQx.
  rewrite <- H in *.
  inversion WASW.
  rewrite <- EQx.
  apply in_map. assumption.
  apply WASW.
  apply SPUR2. assumption.
  }
  exists. tauto.
  exists. tauto.
  exists.
  {
  intros.
  apply upd_updl.
  exists (Lookup e, tx, p, O, C). auto.
  assumption.
  }

  exists.
  {
  apply NoDup_updl. assumption.
  }
  exists.
  {
  split. assumption.
  split. assumption.
  split.
  intros.
  unfold WTs, OBs in *.
  rewrite <- EQWT.
  apply INAOK. assumption.
  assumption. assumption.
  }
  exists. tauto.
  exists. tauto.
  exists. 
  {
  intros.
  unfold WTs in *.
  rewrite <- EQWT.
  apply WTsOTsOK. assumption.
  }
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  {
  symmetry in EQx.
  inversion EQx.
  split.
  unfold wellformed. simpl. tauto.
  split.
  {
  apply sat_lookup in WP; try assumption.
  destruct WP as (v0,(ll,(eqll,(pv,sat1)))).

  assert (eqvl: vl = v0).
  {
  rewrite eqll in ALC.
  destruct pv as (f',(lef',pll)).
  assert (CELL: exists f', fold_left phplus (map pof T) (phplus Pinv Pleak) (evall ll) = Some (Cell f' v0)).
  {
  apply fold_cell; repeat php_.
  apply pofs.
  intros.
  repeat php_.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  exists f'.
  right. exists p.
  exists.
  apply in_map_iff.
  exists (Lookup e, tx, p, O, C, id). auto.
  assumption.
  }
  destruct CELL as (f'',CELL).




  destruct PH2H as (PH1,PH2).
  specialize PH1 with (evall ll).
  rewrite CELL in PH1.

  replace ([[Aof ll]]) with (Aof (evall ll)) in ALC.
  rewrite PH1 in ALC.
  inversion ALC.
  reflexivity.
  reflexivity.
  }
  rewrite eqvl.
  eapply sat_weak_imp1; try assumption.
  apply sat1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  }
  intros.
  inversion W4COND.
  }
  rewrite EQx in INx.
  assert (tmp:=INx).
  apply SOBS in tmp.
  destruct tmp as (WF',(SAT',SAFE')).
  split. assumption.
  split.

  assert (bp0: boundph p0).
  {
  apply BPE.
  apply in_map_iff.
  exists (c, tx0, p0, O0, C0, id0).
  split. reflexivity. assumption.
  }

  assert (bg00: boundgh C0).
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
  apply SAT'.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  assert (tmp:= W4COND).
  apply SAFE' in W4COND.
  destruct W4COND as (v,(l,(inv,(inl,(aov,(aol,safe')))))).
  exists v, l, inv, inl, aov, aol.
  unfold WTs in *.
  rewrite <- EQWT.
  assumption.
Qed.


Lemma Mutate_preserves_validity:
  forall m sp h t id tx e1 e2 
         (VALIDK: validk (S m) sp t h)
         (CMD: t id = Some (Mutate e1 e2, tx)),
    validk m sp (upd Z.eq_dec t id (Some (tt, tx))) (upd Z.eq_dec h ([[e1]]) (Some ([[e2]]))).
Proof.
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
  unfold WTs, OBs.
  unfold validk.


  assert (tmp: exists p O C, In (Mutate e1 e2, tx, p, O, C, id) T).
  apply TOK.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  apply sat_mutate in WP.
  destruct WP as (l,(aol,((vl,pl),sat1))).
  rewrite <- aol in *.

  exists (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p l (Some (Cell full ([[e2]]))), O, C, id)).
  exists invs, locs, Pinv, Pleak, Ainv, Cinv, Cleak.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (EQC: map gof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p l (Some (Cell full ([[e2]]))), O, C, id)) = map gof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Mutate e1 e2, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQC': map (fun x => (gof x, snd x)) (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p l (Some (Cell full ([[e2]]))), O, C, id)) =
    map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Mutate e1 e2, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQOO: map oof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p l (Some (Cell full ([[e2]]))), O, C, id)) = map oof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Mutate e1 e2, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQAO: map Aoof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p l (Some (Cell full ([[e2]]))), O, C, id)) = map Aoof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Mutate e1 e2, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQFIL: forall e, length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some e))) (map cmdof T)) =
    length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some e))) (map cmdof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p l (Some (Cell full ([[e2]]))), O, C, id))))).
  {
  unfold updl.
  rewrite map_map.
  intros.
  apply length_filter_map_eq.
  intros.
  destruct (Z.eq_dec (snd a) id).
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl in e0.
  assert (EQA: (a1,a2,a3,a4,a5) = (Mutate e1 e2, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply IN.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  unfold cmdof. simpl.
  reflexivity. reflexivity.
  }

  assert (EQWT: forall l', WTs l' (map cmdof T) locs = 
    WTs l' (map cmdof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p l (Some (Cell full ([[e2]]))), O, C, id))) locs).
  {
  unfold WTs.
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.
  destruct (xOf (fun x : location Z => Lof x) locs x); try reflexivity.
  destruct (Z.eq_dec x (Aof l')); try reflexivity.
  destruct (Z.eq_dec z (Aof l')).
  apply EQFIL. reflexivity.
  }

  assert (phpdefp0il: forall p0 : pheap, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  repeat php_.
  apply PHPD. assumption.
  apply PHPD. assumption.
  }

  assert (inpid: In (p, id) (map (fun x => (pof x, snd x)) T)).
  {
  apply in_map_iff.
  exists (Mutate e1 e2, tx, p, O, C, id).
  auto.
  }

  assert (p0l: forall p0 id' (NEQ: id <> id') 
    (IN : In (p0, id') (map (fun x => (pof x, snd x)) T)),
    p0 l = None).
  {
  intros.
  assert (bp: boundph (phplus p p0)).
  {
  apply boundph_fold1 with (m:=pof)(l:=T)(b:=phplus Pinv Pleak)(id1:=id)(id2:=id'); repeat php_.
  }
  assert (phpd: phplusdef p p0).
  {
  apply DEFL with id id'; try assumption.
  }
  unfold boundph in bp.
  unfold phplusdef in phpd.
  specialize bp with (x:=l).
  specialize phpd with l.
  unfold phplus in bp.
  rewrite pl in *.
  destruct (p0 l) eqn:p0l.
  destruct k; inversion phpd.
  assert (CO: Qclt 0 (full + f) /\ Qcle (full + f) 1).
  eapply bp. reflexivity.
  destruct CO as (CO,CO1).
  assert (CO2: Qclt 0 f /\ Qcle f 1).
  eapply BPE with (p:=p0).
  apply in_map_iff.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  exists x. inversion EQx. auto.
  apply p0l.
  destruct CO2 as (CO2,CO3).
  exfalso.
  apply qcpluslelt with f; assumption.
  reflexivity.
  }

  assert (inp: In p (map pof T)).
  {
  apply in_map_iff.
  exists (Mutate e1 e2, tx, p, O, C, id). auto.
  }

  assert (phpdefpi: phplusdef p Pinv).
  {
  apply PHPD. assumption.
  }

  assert (phpdefpl: phplusdef p Pleak).
  {
  apply PHPD. assumption.
  }

  assert (bpil: boundph (phplus p (phplus Pinv Pleak))).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_fold with (m:=pof) (l:=T); repeat php_.
  }

  assert (bp: boundph p).
  {
  apply BPE. assumption.
  }

  assert (bpi: boundph (phplus p Pinv)).
  {
  apply boundph_mon with Pleak; repeat php_.
  }

  assert (bpl: boundph (phplus p Pleak)).
  {
  apply boundph_mon with Pinv; repeat php_.
  rewrite phplus_assoc; repeat php_.
  replace (phplus Pleak Pinv) with (phplus Pinv Pleak); repeat php_.
  }

  assert (piNone: Pinv l = None).
  {
  unfold boundph in bpi.
  unfold phplus in bpi.
  specialize bpi with (x:=l).
  unfold phplusdef in phpdefpi.
  specialize phpdefpi with l.
  rewrite pl in *.
  destruct (Pinv l) eqn:pi.
  destruct k; inversion phpdefpi.
  assert (CO: Qclt 0 (full + f) /\ Qcle (full + f) 1).
  eapply bpi. reflexivity.
  destruct CO as (CO,CO1).
  assert (CO2: Qclt 0 f /\ Qcle f 1).
  eapply BPI.
  apply pi.
  destruct CO2 as (CO2,CO3).
  exfalso.
  apply qcpluslelt with f; assumption.
  reflexivity.
  }

  assert (plNone: Pleak l = None).
  {
  unfold boundph in bpl.
  unfold phplus in bpl.
  specialize bpl with (x:=l).
  unfold phplusdef in phpdefpl.
  specialize phpdefpl with l.
  rewrite pl in *.
  destruct (Pleak l) eqn:plk.
  destruct k; inversion phpdefpl.
  assert (CO: Qclt 0 (full + f) /\ Qcle (full + f) 1).
  eapply bpl. reflexivity.
  destruct CO as (CO,CO1).
  assert (CO2: Qclt 0 f /\ Qcle f 1).
  eapply BPL.
  apply plk.
  destruct CO2 as (CO2,CO3).
  exfalso.
  apply qcpluslelt with f; assumption.
  reflexivity.
  }

  assert (EQH: forall l' (NEQ: l <> l'), fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p l (Some (Cell full ([[e2]]))), O, C, id))) (phplus Pinv Pleak) l' =
    fold_left phplus (map pof T) (phplus Pinv Pleak) l').
  {
  intros.
  eapply eq_heap with (p:=p)(z:=l)(v:=Some (Cell full ([[e2]]))); repeat php_.
  apply pofs.
  intros.
  apply phpdef_comm.
  apply phpdef_v.
  apply DEFL with id id'; try assumption.
  apply p0l with id'; assumption.
  apply phpdef_v; try assumption.
  apply phpdef_v; repeat php_.
  }

  assert (CELL1: fold_left phplus (map pof T) (phplus Pinv Pleak) l = Some (Cell full vl)).
  {
  apply fold_cell_full with p id; repeat php_.
  apply pofs.
  unfold phplus.
  rewrite piNone, plNone.
  reflexivity.
  }

  assert (DEFL1: defl phplusdef (map (fun x => (pof x, snd x)) (updl T id
    (tt, tx, upd (location_eq_dec Z.eq_dec) p l (Some (Cell full ([[e2]]))), O, C, id)))).
  {
  unfold defl.
  unfold updl.
  rewrite map_map.
  unfold pof.
  intros.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  apply in_map_iff in IN2.
  destruct IN2 as (x2,(EQ2,IN2)).
  destruct (Z.eq_dec (snd x1) id).
  simpl in *.
  inversion EQ1.
  simpl in *.
  destruct (Z.eq_dec (snd x2) id).
  inversion EQ2.
  omega.
  inversion EQ2.
  apply phpdef_v; repeat php_.
  apply DEFL with id (snd x2); try assumption.
  omega.
  apply in_map_iff.
  exists x2. auto.
  apply p0l with (snd x2); try assumption.
  omega.
  apply in_map_iff.
  exists x2. auto.
  simpl in *.
  inversion EQ1.
  destruct (Z.eq_dec (snd x2) id).
  inversion EQ2.
  apply phpdef_comm; repeat php_.
  apply phpdef_v; repeat php_.
  apply DEFL with id (snd x1); try assumption.
  omega.
  apply in_map_iff.
  exists x1. auto.
  apply p0l with (snd x1); try assumption.
  omega.
  apply in_map_iff.
  exists x1. auto.
  inversion EQ2.
  apply DEFL with (snd x1) (snd x2); try assumption.
  omega.
  apply in_map_iff.
  exists x1. auto.
  apply in_map_iff.
  exists x2. auto.
  }

  assert (phpdefp0: forall p0 (IN: In p0 (map pof (updl T id
    (tt, tx, upd (location_eq_dec Z.eq_dec) p l (Some (Cell full ([[e2]]))), O, C, id)))),
    phplusdef p0 Pinv /\ phplusdef p0 Pleak).
  {
  unfold updl.
  rewrite map_map.
  unfold pof.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  simpl in *.
  inversion EQ1.
  split; apply phpdef_v; repeat php_.
  rewrite <- EQ1.
  apply PHPD.
  apply in_map_iff.
  exists x1. auto.
  }

  assert (CELL2: fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p l (Some (Cell full ([[e2]]))), O, C, id))) (phplus Pinv Pleak) l =
    Some (Cell full ([[e2]]))).
  {
  apply fold_cell_full with (upd (location_eq_dec Z.eq_dec) p l (Some (Cell full ([[e2]])))) id; repeat php_.
  apply pofs.
  apply NoDup_updl.
  assumption.
  unfold updl.
  rewrite map_map.
  apply in_map_iff.
  exists (Mutate e1 e2, tx, p, O, C, id).
  simpl. rewrite eqz. auto.
  unfold upd.
  destruct (location_eq_dec Z.eq_dec l l). reflexivity. contradiction.
  intros.
  apply p0l with id0.
  assumption.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  simpl in EQx. inversion EQx. omega.
  inversion EQx.
  apply in_map_iff.
  exists x. auto.
  unfold phplus.
  rewrite piNone, plNone.
  reflexivity.
  intros.
  repeat php_.
  apply phpdefp0; assumption.
  apply phpdefp0; assumption.
  }

  assert (bpupd: boundph (upd (location_eq_dec Z.eq_dec) p l (Some (Cell full ([[e2]]))))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',eq').
  inversion eq'.
  apply full_bound.
  }

  assert (bg1: boundgh C).
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
  exists (Mutate e1 e2, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  rewrite EQC, EQC', EQAO, EQOO.
  simpl in *.
  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  rewrite aol in *.
  apply red_Mutate; try assumption.
  }
  exists.
  {
  unfold spur_ok.
  destruct SPUR as (SPUR1,SPUR2).
  split; intros.
  eapply SPUR1 with (c:=c).
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  unfold cmdof in EQx.
  simpl in EQx.
  inversion EQx.
  rewrite <- H in *.
  inversion WASW.
  rewrite <- EQx.
  apply in_map. assumption.
  apply WASW.

  destruct (location_eq_dec Z.eq_dec l v).
  rewrite <- e in *.
  rewrite CELL2 in CONDv.
  inversion CONDv.
  rewrite EQH in CONDv; try assumption.
  apply SPUR2 in CONDv.
  destruct CONDv as (l1,(lofv,(LK,SPR))).
  exists l1, lofv.
  exists.
  destruct (location_eq_dec Z.eq_dec l l1).
  rewrite <- e in *.
  rewrite CELL1 in LK.
  destruct LK as [LK|LK]. inversion LK.
  destruct LK as (wt,(ot,LK)). inversion LK.
  rewrite EQH; assumption.
  assumption.
  }
  exists.
  {
  split. assumption.
  split. assumption.
  split. assumption.
  split.
  {
  unfold updl.
  rewrite map_map.
  unfold pof.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  simpl in *.
  inversion EQ1.
  assumption.
  rewrite <- EQ1.
  apply BPE; try assumption.
  apply in_map_iff.
  exists x1. auto.
  }
  split. assumption.
  split. assumption.
  split. assumption.
  split.
  {
  unfold boundph.
  intros.
  destruct (location_eq_dec Z.eq_dec l x).
  rewrite <- e in *.
  rewrite CELL2 in H.
  inversion H.
  apply full_bound.
  rewrite EQH in H.
  eapply BPT with (z:=z) (x:=x); try assumption.
  assumption.
  }
  assert (PH:=PH2H).
  destruct PH as (PH1,PH2).
  split.
  {
  intros.
  destruct (location_eq_dec Z.eq_dec l l0).
  specialize PH1 with l.
  rewrite <- e in *.
  rewrite CELL1 in PH1.
  rewrite CELL2.
  unfold upd. rewrite eqz. reflexivity.
  rewrite EQH; try assumption.
  unfold upd.

  destruct (Z.eq_dec (Aof l0) (Aof l)).
  destruct (fold_left phplus (map pof T) (phplus Pinv Pleak) l0) eqn:pl0.
  exfalso.
  apply n.
  apply INJ.
  rewrite CELL1. apply some_none.
  rewrite pl0. apply some_none.
  omega.
  trivial.
  apply PH1.
  }
  intros.
  unfold upd.
  destruct (Z.eq_dec z (Aof l)).
  symmetry in e.
  apply NONE in e.
  rewrite CELL2 in e.
  inversion e.
  apply PH2.
  intros.
  rewrite <- EQH.
  apply NONE.
  assumption.
  unfold not.
  intros.
  apply n.
  rewrite H, EQ.
  reflexivity.
  }
  exists. tauto.
  exists.
  {
  intros.
  apply upd_updl.
  exists (Mutate e1 e2, tx, p, O, C);
  assumption. assumption.
  }
  exists.
  {
  apply NoDup_updl. assumption.
  }
  exists.
  {
  split. assumption.
  split.
  {
  intros.
  apply AinvOK in IN.
  destruct IN as (IN1,IN2).
  destruct (location_eq_dec Z.eq_dec l l0).
  rewrite <- e in *.
  rewrite CELL1 in IN1.
  inversion IN1.
  rewrite EQH; try assumption.
  split. assumption.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) (Aof l)).
  exfalso.
  apply n.
  apply INJ.
  rewrite CELL1. apply some_none.
  rewrite IN1. apply some_none.
  rewrite e. reflexivity.
  assumption.
  }
  split.
  {
  intros.
  unfold WTs in EQWT.
  rewrite <- EQWT.
  unfold upd in NOTHELD.
  destruct (Z.eq_dec (Aof l0) (Aof l)).
  inversion NOTHELD.
  destruct (location_eq_dec Z.eq_dec l l0).
  rewrite <- e0 in *.
  rewrite CELL2 in LOCK.
  inversion LOCK.
  apply INAOK.
  rewrite <- EQH; try assumption.
  exfalso.
  apply n.
  apply INJ.
  rewrite CELL1. apply some_none.
  rewrite <- EQH; try assumption.
  rewrite LOCK. apply some_none.
  symmetry. assumption.
  apply INAOK.
  rewrite <- EQH; try assumption.
  unfold not.
  intros.
  apply n.
  rewrite H. reflexivity.
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
  destruct (location_eq_dec Z.eq_dec l x1).
  rewrite <- e in *.
  destruct (location_eq_dec Z.eq_dec l x2).
  rewrite <- e0 in *.
  reflexivity.
  apply INJ.
  rewrite CELL1. apply some_none.
  rewrite <- EQH; try assumption. assumption.
  destruct (location_eq_dec Z.eq_dec l x2).
  rewrite <- e in *.
  apply INJ.
  rewrite <- EQH; try assumption.
  rewrite CELL1. apply some_none. assumption.
  apply INJ.
  rewrite <- EQH; try assumption.
  rewrite <- EQH; try assumption.
  assumption.
  }
  split. assumption.
  split.
  {
  intros.
  destruct (location_eq_dec Z.eq_dec l l0).
  rewrite <- e in *.
  split.
  intros.
  apply LOCs.
  rewrite CELL1. apply some_none.
  intros.
  rewrite CELL2. apply some_none.
  rewrite EQH; try assumption.
  apply LOCs.
  }
  intros.
  apply OBsOK in IN.
  destruct IN as (l',(ol',pl')).
  destruct (location_eq_dec Z.eq_dec l l').
  rewrite <- e in *.
  exists l, ol'.
  rewrite CELL2. apply some_none.
  exists l', ol'.
  rewrite EQH; try assumption.
  }
  exists.
  {
  split.
  {
  intros.
  destruct (location_eq_dec Z.eq_dec l l0).
  rewrite <- e in *.
  rewrite CELL2 in LOCK.
  destruct LOCK as [CO|CO].
  inversion CO.
  destruct CO as (wt,(ot,CO)).
  destruct CO as [CO|CO]; inversion CO.
  rewrite EQH in LOCK; try assumption.
  assert (tmp:=LOCK).
  apply LOCKOK in LOCK.
  destruct LOCK as (L1,(L2,(L3,L4))).
  split. assumption.
  split. assumption.
  split. assumption.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) (Aof l)).
  exfalso.
  apply n.
  apply INJ.
  rewrite CELL1. apply some_none.
  destruct tmp as [t1|t1].
  rewrite t1. apply some_none.
  destruct t1 as (wt,(ot,t1)).
  destruct t1 as [t1|t1];
  rewrite t1; apply some_none.
  symmetry. assumption.
  assumption.
  }
  split.
  {
  intros.
  destruct (location_eq_dec Z.eq_dec l l0).
  rewrite <- e in *.
  rewrite CELL2 in ULOCK.
  inversion ULOCK.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) (Aof l)).
  exfalso.
  apply n.
  apply INJ.
  rewrite CELL1. apply some_none.
  rewrite <- EQH; try assumption.
  rewrite ULOCK. apply some_none.
  symmetry. assumption.
  eapply ULOCKOK.
  rewrite EQH in ULOCK; try assumption.
  apply ULOCK.
  }
  intros.
  destruct (location_eq_dec Z.eq_dec l l0).
  rewrite <- e in *.
  rewrite CELL2 in UCOND.
  inversion UCOND.
  apply ULOCKOK.
  rewrite <- EQH; try assumption.
  }
  exists.
  {
  intros.
  destruct (location_eq_dec Z.eq_dec l l0).
  rewrite <- e in *.
  rewrite CELL2 in ULOCKED.
  destruct ULOCKED as [U|U]; inversion U.
  unfold WTs in EQWT.
  rewrite <- EQWT.
  apply WTsOTsOK.
  rewrite <- EQH; try assumption.
  }
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  {
  symmetry in EQx.
  inversion EQx.
  split. auto.
  split.
  eapply sat_weak_imp1; try assumption.
  apply sat1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  }
  rewrite EQx in INx.
  assert (tmp:=INx).
  apply SOBS in tmp.
  destruct tmp as (WF1,(SAT1,SAFE1)).
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
  intros.
  apply SAFE1 in W4COND.
  destruct W4COND as (v',(l',(inv,(inl,(aov,(aol',safe')))))).
  exists v', l', inv, inl, aov, aol'.
  unfold WTs in EQWT.
  rewrite <- EQWT.
  assumption.
Qed.


Lemma Fork_preserves_validity:
  forall m sp h t id id' c tx
         (CMD: t id = Some (Fork c, tx))
         (NIN: t id' = None)
         (VALID: validk (S m) sp t h),
    validk m sp (upd Z.eq_dec (upd Z.eq_dec t id (Some (tt, tx))) id' (Some (c, done))) h.
Proof.
  intros.
  unfold validk.

  destruct VALID as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
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
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.

  assert (tmp: exists p O C, In (Fork c, tx, p, O, C, id) T).
  {
  apply TOK.
  assumption.
  }

  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  destruct WF as (WF1,WF2).
  apply sat_fork in WP.
  destruct WP as (p1,(p2,(O1,(O2,(C1,(C2,(ghpdefC1C2,(bp1,(bp2,(PHPDp1p2,(bp1p2,(p1p2,(O1O2,(C1C2,(SAT1,(SAT2,TR12)))))))))))))))).
  exists ((c,done,p2,O2,C2,id')::updl T id (tt, tx, p1, O1, C1, id)).

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (NEQ_1: id <> id').
  unfold not.
  intros.
  rewrite H in CMD.
  rewrite CMD in NIN.
  inversion NIN.
  assert (PHPp2pinv: phplusdef p2 Pinv).
  {
  apply phpdef_assoc_mon with p1.
  assumption.
  apply PHPD.
  apply in_map_iff.
  exists (Fork c, tx, p, O, C, id).
  rewrite <- p1p2.
  auto.
  }

  subst.

  assert (inp12: In (phplus p1 p2) (map pof T)).
  {
  apply in_map_iff.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  }

  assert (phpdefp0il: forall p0, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  apply phpdef_pair.
  assumption.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  }

  assert (phpdefp12pil: phplusdef (phplus p1 p2) (phplus Pinv Pleak)).
  {
  apply phpdef_pair.
  assumption.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  }

  assert (tmp: phplusdef (phplus p1 p2) Pinv /\ phplusdef (phplus p1 p2) Pleak).
  {
  apply phpdef_dist'; repeat php_.
  }
  destruct tmp as (phpdefp12pi,phpdefp12pl).

  assert (tmp: phplusdef p1 Pinv /\ phplusdef p2 Pinv).
  {
  apply phpdef_dist; repeat php_.
  }
  destruct tmp as (phpdefp1i,phpdefp2i).

  assert (tmp: phplusdef p1 Pleak /\ phplusdef p2 Pleak).
  {
  apply phpdef_dist; repeat php_.
  }
  destruct tmp as (phpdefp1l,phpdefp2l).

  assert (inc12: In (ghplus C1 C2) (map gof T)).
  {
  apply in_map_iff.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  }

  assert (ghpdefp12pil: ghplusdef (ghplus C1 C2) (ghplus Cinv Cleak)).
  {
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  }

  assert (tmp: ghplusdef (ghplus C1 C2) Cinv /\ ghplusdef (ghplus C1 C2) Cleak).
  {
  apply ghpdef_dist'; repeat php_.
  }
  destruct tmp as (ghpdefp12pi,ghpdefp12pl).

  assert (tmp: ghplusdef C1 Cinv /\ ghplusdef C2 Cinv).
  {
  apply ghpdef_dist; repeat php_.
  }
  destruct tmp as (ghpdefp1i,ghpdefp2i).

  assert (tmp: ghplusdef C1 Cleak /\ ghplusdef C2 Cleak).
  {
  apply ghpdef_dist; repeat php_.
  }
  destruct tmp as (ghpdefp1l,ghpdefp2l).

  assert (EQP: fold_left phplus (map pof (updl T id (tt, tx, p1, O1, C1, id)))
    (phplus (phplus Pinv Pleak) (pof (c, done, p2, O2, C2, id'))) = 
    fold_left phplus (map pof T) (phplus Pinv Pleak)).
  {
  rewrite phplus_comm.
  unfold pof at 2.
  simpl.
  apply fold_phplus_Fork with p1; repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  repeat php_.
  }

  assert (DEFL1: defl ghplusdef (map (fun x => (gof x, snd x)) (updl T id (tt, tx, p1, O1, C1, id)))).
  {
  unfold updl.
  unfold defl.
  rewrite map_map.
  intros.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQx1,INx1)).
  apply in_map_iff in IN2.
  destruct IN2 as (x2,(EQx2,INx2)).
  unfold gof in EQx1, EQx2.
  simpl in *.
  destruct (Z.eq_dec (snd x1) id).
  simpl in *.
  inversion EQx1.
  rewrite <- H0.
  destruct (Z.eq_dec (snd x2) id).
  simpl in *.
  inversion EQx2.
  omega.
  simpl in *.
  inversion EQx2.
  apply ghpdef_assoc_mon with C2.
  repeat php_.
  apply DEFLg with id (snd x2).
  omega.
  rewrite ghplus_comm; repeat php_.
  apply in_map_iff.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply in_map_iff.
  exists x2.
  auto.
  destruct (Z.eq_dec (snd x2) id).
  simpl in *.
  inversion EQx2.
  rewrite <- H0.
  apply ghpdef_comm.
  apply ghpdef_assoc_mon with C2.
  repeat php_.
  apply DEFLg with id (snd x1).
  omega.
  rewrite ghplus_comm; repeat php_.
  apply in_map_iff.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply in_map_iff.
  exists x1.
  inversion EQx1.
  auto.
  apply DEFLg with id1 id2.
  omega.
  apply in_map_iff.
  exists x1.
  auto.
  apply in_map_iff.
  exists x2.
  auto.
  }

  assert (EQC: fold_left ghplus (map gof (updl T id (tt, tx, p1, O1, C1, id)))
    (ghplus (ghplus Cinv Cleak) (gof (c, done, p2, O2, C2, id'))) =
    fold_left ghplus (map gof T) (ghplus Cinv Cleak)).
  {
  rewrite ghplus_comm.
  rewrite fold_left_f_m_def with (def:=ghplusdef); repeat php_.
  symmetry.
  apply fold_left_move_m_eq with (def:=ghplusdef) (x1:= C1); repeat php_.
  apply can_ghpdef.
  intros.
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  apply in_map_iff.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply can_ghpdef.
  apply NoDup_updl.
  assumption.
  unfold updl.
  rewrite map_map.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQx,INx)).
  destruct (Z.eq_dec (snd x1) id).
  unfold gof in EQx.
  simpl in EQx.
  rewrite <- EQx.
  split.
  repeat php_.
  repeat php_.
  rewrite <- EQx.
  split.
  unfold gof.
  simpl.
  apply ghpdef_comm.
  apply ghpdef_assoc_mon with C1.
  repeat php_.
  apply DEFLg with id (snd x1).
  omega.
  apply in_map_iff.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply in_map_iff.
  exists x1.
  auto.
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  apply in_map.
  assumption.
  apply GHPD.
  apply in_map.
  assumption.
  repeat php_.
  }

  assert (EQAO: count_occ Z.eq_dec (Aoof (c, done, p2, O2, C2, id') ++
    concat (map Aoof (updl T id (tt, tx, p1, O1, C1, id)))) =
    count_occ Z.eq_dec (concat (map Aoof T))).
  {
  simpl.
  unfold Aoof at 1.
  simpl.
  symmetry.
  eapply concat_move_eq with (map (fun x => Aofo x) O) (map (fun x => Aofo x) O1).
  assumption.
  rewrite <- map_app.
  apply Permutation_map.
  assumption.
  apply in_map_iff.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  split.
  reflexivity.
  unfold elem.
  apply filter_In.
  simpl.
  split.
  assumption.
  apply Z.eqb_eq.
  reflexivity.
  reflexivity.
  }

  assert (EQWC: forall l, filterb (xOf (fun x  => Lof x) locs) (Aof l) (fun v : Z => length (filter
    (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) (Some v)))
    (map cmdof ((c, done, p2, O2, C2, id') :: updl T id (tt, tx, p1, O1, C1, id))))) =
    filterb (xOf (fun x  => Lof x) locs) (Aof l) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof T)))).
  {
  intros.
  unfold filterb.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x (Aof l)).
  reflexivity.
  destruct (xOf (fun x0 => Lof x0) locs x).
  destruct (Z.eq_dec z (Aof l)).
  unfold cmdof.
  simpl.
  rewrite not_waiting_cond_none.
  destruct ((opZ_eq_dec None (Some x))).
  inversion e0.
  simpl.
  symmetry.
  unfold updl.
  rewrite map_map.
  apply filter_map_eq.
  intros.
  destruct x0 as (((((x1,x2),x3),x4),x5),x6).
  simpl.
  destruct (Z.eq_dec x6 id).
  rewrite e0 in IN.
  assert (EQ1: (x1, x2, x3, x4, x5) = (Fork c, tx, phplus p1 p2, O, ghplus C1 C2)).
  simpl in *.
  eapply unique_key_eq.
  apply IN.
  assumption.
  assumption.
  inversion EQ1.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  destruct WF1.
  assumption.
  reflexivity.
  reflexivity.
  }

  assert (INO: forall o, In o (oof (c, done, p2, O2, C2, id') ++
    concat (map oof (updl T id (tt, tx, p1, O1, C1, id)))) <->
    In o (concat (map oof T))).
  {
  split.
  intros.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  apply in_app_iff in H.
  destruct H as [IN|IN].
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  split. assumption.
  unfold oof in *.
  simpl in *.
  apply Permutation_in with (O1++O2).
  assumption.
  apply in_app_iff.
  right.
  assumption.
  unfold updl in IN.
  rewrite map_map in IN.
  rewrite <- flat_map_concat_map in IN.
  apply in_flat_map in IN.
  destruct IN as (x,(INx,EQx)).
  destruct (Z.eq_dec (snd x) id).
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  split. assumption.
  unfold oof in *.
  simpl in *.
  apply Permutation_in with (O1++O2).
  assumption.
  apply in_app_iff.
  left.
  assumption.
  exists x.
  auto.

  intros.
  rewrite <- flat_map_concat_map in H.
  apply in_flat_map in H.
  destruct H as (x,(INx,EQx)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  destruct (Z.eq_dec x6 id).
  {
  rewrite e in *.
  assert (EQ1: (x1, x2, x3, x4, x5) = (Fork c, tx, phplus p1 p2, O, ghplus C1 C2)).
  {
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  }
  rewrite EQ1 in *.
  apply Permutation_in with (l':=O1++O2) in EQx.
  apply in_app_iff in EQx.
  destruct EQx as [IN|IN].
  apply in_app_iff.
  right.
  unfold updl.
  rewrite map_map.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  rewrite eqz.
  auto.
  apply in_app_iff.
  left.
  assumption.
  apply Permutation_sym.
  assumption.
  }
  apply in_app_iff.
  right.
  unfold updl.
  rewrite map_map.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists (x1, x2, x3, x4, x5, x6).
  simpl.
  destruct (Z.eq_dec x6 id).
  contradiction.
  auto.
  }

  exists invs, locs, Pinv, Pleak, Ainv, Cinv, Cleak.

  rewrite EQP.
  rewrite EQC.
  rewrite EQAO.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  apply red_Fork.
  assumption.
  assumption.
  }

  exists.
  {
  split.
  {
  intros.
  destruct IN as [EQ|IN].
  unfold cmdof in EQ.
  simpl in EQ.
  rewrite <- EQ in *.
  rewrite WASW in WF1.
  simpl in WF1.
  destruct WF1.
  contradiction.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  destruct (Z.eq_dec (snd y) id).
  unfold cmdof in EQy.
  rewrite <- EQy in WASW.
  inversion WASW.
  eapply SPUR1 with (c:=c0).
  apply in_map_iff.
  exists y.
  auto.
  apply WASW.
  }
  assumption.
  }

  exists.
  {
  exists.
  {
  unfold defl in *.
  simpl.
  intros.
  destruct IN1 as [EQ1|IN1].
  unfold pof in EQ1.
  simpl in EQ1.
  inversion EQ1.
  destruct IN2 as [EQ2| IN2].
  inversion EQ2.
  omega.
  rewrite <- H0.
  unfold updl in IN2.
  rewrite map_map in IN2.
  apply in_map_iff in IN2.
  destruct IN2 as (x,(EQ2,IN2)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ2.
  simpl in EQ2.
  destruct (Z.eq_dec x6 id).
  simpl in EQ2.
  inversion EQ2.
  rewrite <- H2.
  apply phpdef_comm.
  assumption.
  simpl in EQ2.
  inversion EQ2.
  rewrite <- H2.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply DEFL with id x6.
  omega.
  apply in_map_iff.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  destruct IN2 as [EQ2| IN2].
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  unfold updl in IN1.
  rewrite map_map in IN1.
  apply in_map_iff in IN1.
  destruct IN1 as (x,(EQ1,IN1)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ1.
  simpl in EQ1.
  destruct (Z.eq_dec x6 id).
  simpl in EQ1.
  inversion EQ1.
  rewrite <- H0.
  rewrite <- H2.
  assumption.
  simpl in EQ1.
  inversion EQ1.
  rewrite <- H0.
  rewrite <- H2.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply DEFL with id x6.
  omega.
  apply in_map_iff.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  unfold updl in IN1.
  rewrite map_map in IN1.
  apply in_map_iff in IN1.
  destruct IN1 as (x,(EQ1,IN1)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ1.
  simpl in EQ1.
  destruct (Z.eq_dec x6 id).
  simpl in EQ1.
  inversion EQ1.
  rewrite <- H0.
  unfold updl in IN2.
  rewrite map_map in IN2.
  apply in_map_iff in IN2.
  destruct IN2 as (x,(EQ2,IN2)).
  destruct x as (((((y1,y2),y3),y4),y5),y6).
  unfold pof in EQ2.
  simpl in EQ2.
  destruct (Z.eq_dec y6 id).
  simpl in EQ2.
  inversion EQ2.
  omega.
  simpl in EQ2.
  inversion EQ2.
  rewrite <- H2.
  apply phpdef_assoc_mon2 with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply DEFL with id y6.
  omega.
  apply in_map_iff.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  auto.
  apply phpdef_comm.
  assumption.
  simpl in EQ1.
  inversion EQ1.
  rewrite <- H0.
  unfold updl in IN2.
  rewrite map_map in IN2.
  apply in_map_iff in IN2.
  destruct IN2 as (x,(EQ2,IN2)).
  destruct x as (((((y1,y2),y3),y4),y5),y6).
  unfold pof in EQ2.
  simpl in EQ2.
  destruct (Z.eq_dec y6 id).
  simpl in EQ2.
  inversion EQ2.
  rewrite <- H2.
  apply phpdef_comm.
  apply phpdef_assoc_mon2 with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply DEFL with id x6.
  omega.
  apply in_map_iff.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  apply phpdef_comm.
  assumption.
  simpl in EQ2.
  inversion EQ2.
  rewrite <- H2.
  apply DEFL with x6 y6.
  omega.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  auto.
  }
  split. assumption.
  split.
  {
  simpl.
  intros.
  destruct IN as [EQ|IN].
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  rewrite <- EQ.
  split. assumption.
  assumption.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((y1,y2),y3),y4),y5),y6).
  unfold pof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec y6 id).
  simpl in EQ.
  rewrite <- EQ.
  split. assumption.
  assumption.
  apply PHPD.
  rewrite <- EQ.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  auto.
  }
  split.
  {
  intros.
  destruct IN as [EQ|IN].
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  rewrite <- EQ.
  assumption.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((y1,y2),y3),y4),y5),y6).
  unfold pof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec y6 id).
  simpl in EQ.
  rewrite <- EQ.
  assumption.
  simpl in EQ.
  rewrite <- EQ.
  apply BPE.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  auto.
  }
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
  }

  exists.
  {
  split.
  {
  unfold defl in *.
  simpl.
  intros.
  destruct IN1 as [EQ1|IN1].
  unfold gof in EQ1.
  simpl in EQ1.
  inversion EQ1.
  destruct IN2 as [EQ2| IN2].
  inversion EQ2.
  omega.
  rewrite <- H0.
  unfold updl in IN2.
  rewrite map_map in IN2.
  apply in_map_iff in IN2.
  destruct IN2 as (x,(EQ2,IN2)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ2.
  simpl in EQ2.
  destruct (Z.eq_dec x6 id).
  simpl in EQ2.
  inversion EQ2.
  rewrite <- H2.
  repeat php_.
  unfold gof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  rewrite <- H2.
  apply ghpdef_assoc_mon with C1.
  assumption.
  apply DEFLg with id x6.
  omega.
  apply in_map_iff.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  destruct IN2 as [EQ2| IN2].
  unfold pof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  unfold updl in IN1.
  rewrite map_map in IN1.
  apply in_map_iff in IN1.
  destruct IN1 as (x,(EQ1,IN1)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold gof in EQ1.
  simpl in EQ1.
  destruct (Z.eq_dec x6 id).
  simpl in EQ1.
  inversion EQ1.
  rewrite <- H0.
  rewrite <- H2.
  assumption.
  simpl in EQ1.
  inversion EQ1.
  rewrite <- H0.
  rewrite <- H2.
  apply ghpdef_comm.
  apply ghpdef_assoc_mon with C1.
  assumption.
  apply DEFLg with id x6.
  omega.
  apply in_map_iff.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  unfold updl in IN1.
  rewrite map_map in IN1.
  apply in_map_iff in IN1.
  destruct IN1 as (x,(EQ1,IN1)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold gof in EQ1.
  simpl in EQ1.
  destruct (Z.eq_dec x6 id).
  simpl in EQ1.
  inversion EQ1.
  rewrite <- H0.
  unfold updl in IN2.
  rewrite map_map in IN2.
  apply in_map_iff in IN2.
  destruct IN2 as (x,(EQ2,IN2)).
  destruct x as (((((y1,y2),y3),y4),y5),y6).
  unfold pof in EQ2.
  simpl in EQ2.
  destruct (Z.eq_dec y6 id).
  simpl in EQ2.
  inversion EQ2.
  omega.
  simpl in EQ2.
  inversion EQ2.
  rewrite <- H2.
  apply ghpdef_assoc_mon2 with C2.
  repeat php_.
  rewrite ghplus_comm.
  apply DEFLg with id y6.
  omega.
  apply in_map_iff.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  auto.
  repeat php_.
  simpl in EQ1.
  inversion EQ1.
  rewrite <- H0.
  unfold updl in IN2.
  rewrite map_map in IN2.
  apply in_map_iff in IN2.
  destruct IN2 as (x,(EQ2,IN2)).
  destruct x as (((((y1,y2),y3),y4),y5),y6).
  unfold pof in EQ2.
  simpl in EQ2.
  destruct (Z.eq_dec y6 id).
  simpl in EQ2.
  inversion EQ2.
  rewrite <- H2.
  apply ghpdef_comm.
  apply ghpdef_assoc_mon2 with C2.
  repeat php_.
  rewrite ghplus_comm.
  apply DEFLg with id x6.
  omega.
  apply in_map_iff.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  repeat php_.
  simpl in EQ2.
  inversion EQ2.
  rewrite <- H2.
  apply DEFLg with x6 y6.
  omega.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  auto.
  }
  split.
  {
  intros.
  destruct IN as [EQ|IN].
  unfold gof in EQ.
  simpl in EQ.
  rewrite <- EQ.
  split. assumption.
  assumption.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((y1,y2),y3),y4),y5),y6).
  unfold pof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec y6 id).
  rewrite <- EQ.
  split. assumption.
  assumption.
  simpl in EQ.
  rewrite <- EQ.
  apply GHPD.
  apply in_map.
  assumption.
  }
  split. assumption.
  assumption.
  }

  exists.
  {
  unfold upd.
  split.
  intros.
  destruct (Z.eq_dec id0 id').
  rewrite e.
  symmetry in H.
  inversion H.
  exists p2, O2, C2.
  left.
  reflexivity.
  destruct (Z.eq_dec id0 id).
  rewrite e.
  symmetry in H.
  inversion H.
  exists p1, O1, C1.
  right.
  apply in_map_iff.
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  split.
  simpl.
  rewrite eqz.
  reflexivity.
  assumption.
  apply TOK in H.
  destruct H as (p',(O',(C',IN'))).
  exists p', O', C'.
  right.
  apply in_map_iff.
  exists (c0, tx0,p',O',C',id0).
  simpl.
  split.
  destruct (Z.eq_dec id0 id).
  contradiction.
  reflexivity.
  assumption.
  intros.
  destruct H as (p',(O',(C',IN'))).
  destruct (Z.eq_dec id0 id').
  simpl in *.
  destruct IN' as [EQ'|IN'].
  inversion EQ'.
  reflexivity.
  unfold updl in IN'.
  apply in_map_iff in IN'.
  destruct IN' as (x,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x) id).
  inversion EQ1.
  rewrite e in H5.
  contradiction.
  rewrite e in EQ1.
  rewrite EQ1 in IN1.
  assert (CO: t id' = Some (c0,tx0)).
  apply TOK.
  exists p',O',C'.
  assumption.
  rewrite CO in NIN.
  inversion NIN.
  simpl in IN'.
  destruct (Z.eq_dec id0 id).
  destruct IN' as [EQ'|IN'].
  inversion EQ'.
  symmetry in H5.
  contradiction.
  rewrite e in IN'.
  unfold updl in IN'.
  apply in_map_iff in IN'.
  destruct IN' as (x,(EQ',IN')).
  destruct (Z.eq_dec (snd x) id).
  inversion EQ'.
  reflexivity.
  rewrite EQ' in n0.
  contradiction.
  destruct IN' as [EQ'|IN'].
  inversion EQ'.
  symmetry in H5.
  contradiction.
  unfold updl in IN'.
  apply in_map_iff in IN'.
  destruct IN' as (x,(EQ',IN')).
  destruct (Z.eq_dec (snd x) id).
  inversion EQ'.
  symmetry in H5.
  contradiction.
  apply TOK.
  exists p', O', C'.
  rewrite EQ' in IN'.
  assumption.
  }
  exists.
  {
  simpl.
  apply NoDup_cons.
  unfold not.
  intros.
  apply in_map_iff in H.
  destruct H as (x,(EQ',IN')).
  unfold updl in IN'.
  apply in_map_iff in IN'.
  destruct IN' as (x',(EQ'',IN'')).
  destruct (Z.eq_dec (snd x') id).
  rewrite <- EQ'' in EQ'.
  simpl in EQ'.
  contradiction.
  rewrite EQ'' in IN''.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  assert (CO: t id' = Some (x1,x2)).
  apply TOK.
  exists x3,x4,x5.
  unfold snd in EQ'.
  inversion EQ'.
  rewrite <- EQ'.
  assumption.
  rewrite CO in NIN.
  inversion NIN.
  apply NoDup_updl.
  assumption.
  }
  exists.
  {
  split. assumption.
  split. assumption.
  split.
  intros.
  rewrite EQWC.
  apply INAOK.
  assumption.
  assumption.
  assumption.
  }

  exists.
  {
  split. assumption.
  split. assumption.
  split. assumption.
  intros.
  apply OBsOK.
  apply INO.
  assumption.
  }
  exists.
  {
  split.
  intros.
  apply LOCKOK in LOCK.
  destruct LOCK as (L1,(L2,(L3,L4))).
  split. assumption.
  split. assumption.
  split. assumption.
  intros.
  apply INO.
  apply L4.
  assumption.
  split.
  {
  intros.
  apply ULOCKOK in ULOCK.
  destruct ULOCK as (U1,U2).
  split. assumption.
  unfold not.
  intros.
  apply U2.
  apply INO.
  assumption.
  }
  intros.
  apply UCONDOK in UCOND.
  unfold not.
  intros.
  apply UCOND.
  apply INO.
  assumption.
  }
  exists.
  {
  intros.
  rewrite EQWC.
  apply WTsOTsOK.
  assumption.
  }

  intros.  
  destruct ING as [EQ1|ING1].
  {
(* ==================== id0 = id' ===========*)
  symmetry in EQ1.
  inversion EQ1.
  exists.
  unfold wellformed.
  split.
  destruct WF1 as (WF1',WF2').
  destruct c;
  try assumption.
  trivial.
  exists.
  assumption.
  intros.
  destruct WF1 as (WF1',WF2').
  apply not_waiting_cond_none in WF1'.
  rewrite W4COND in WF1'.
  inversion WF1'.
  }

(* ==================== id0 in T ===========*)
  unfold updl in ING1.
  apply in_map_iff in ING1.
  destruct ING1 as (x,(EQ,IN)).
  
  destruct (Z.eq_dec (snd x) id).
  {
  symmetry in EQ.
  inversion EQ.
  exists.
  unfold wellformed.
  auto.
  exists.
  rewrite <- H4.


  assert (bgc1c2: boundgh (ghplus C1 C2)).
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
  exists (Fork c, tx, phplus p1 p2, O, ghplus C1 C2, id).
  split. reflexivity. assumption.
  }

  assert (bgc1: boundgh C1).
  {
  apply boundgh_mon with C2; try assumption.
  }

  rewrite H4.
  eapply sat_weak_imp1; try assumption.
  apply SAT1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  }
  rewrite EQ in IN.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF1',(WP1',VOBS1')).
  exists. assumption.
  exists.
  assert (bp0: boundph p).
  {
  apply BPE.
  apply in_map_iff.
  exists (c0, tx0, p, O0, C, id0).
  split. reflexivity. assumption.
  }

  assert (bg0: boundgh C).
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
  exists (c0, tx0, p, O0, C, id0).
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  apply WP1'.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  apply VOBS1' in W4COND.
  destruct W4COND as (v,(l,(inv,(eqv,(eql,sobs1))))).
  exists v, l, inv, eqv, eql.
  rewrite EQWC.
  assumption.
Qed.


Lemma Let_preserves_validity:
  forall m sp h t id x c1 c2 tx
         (CMD: t id = Some (Let x c1 c2, tx))
         (VALID: validk (S m) sp t h),
    validk m sp (upd Z.eq_dec t id (Some (c1, Let' x c2 tx))) h.
Proof.
  intros.
  unfold validk in VALID.
  destruct VALID as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
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
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.

  unfold validk.
  assert (tmp: exists p O C, In (Let x c1 c2, tx, p, O, C, id) T).
  {
  apply TOK.
  assumption.
  }

  destruct tmp as (p,(O,(C,INT))).
  exists (updl T id (c1, Let' x c2 tx, p, O, C, id)).
  exists invs, locs, Pinv, Pleak, Ainv, Cinv, Cleak.

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
  destruct WF as ((WF1,WF2),WF3).
  assert (EQ_1: map pof (updl T id (c1, Let' x c2 tx, p, O, C, id)) = map pof T).
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Let x c1 c2, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  assert (EQ_2: map (fun x => (pof x, snd x)) (updl T id (c1, Let' x c2 tx, p, O, C, id)) = map (fun x => (pof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Let x c1 c2, tx, p, O, C)).
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
  assert (EQ_2': map (fun x => (gof x, snd x)) (updl T id (c1, Let' x c2 tx, p, O, C, id)) = map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Let x c1 c2, tx, p, O, C)).
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
  assert (EQ_3: map oof (updl T id (c1, Let' x c2 tx, p, O, C, id)) = map oof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Let x c1 c2, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  }
  assert (EQ_3': map Aoof (updl T id (c1, Let' x c2 tx, p, O, C, id)) = map Aoof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Let x c1 c2, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  }
  assert (EQ_4: map gof (updl T id (c1, Let' x c2 tx, p, O, C, id)) = map gof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Let x c1 c2, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQ_5: forall v, filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
         (map cmdof (updl T id (c1, Let' x c2 tx, p, O, C, id))) =
         filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
         (map cmdof T)).
  {
  intros.
  symmetry.
  apply filter_updl_eq.
  unfold cmdof.
  simpl.
  rewrite not_waiting_cond_none.
  repeat dstr_.
  tauto.
  intros.
  assert (X':x' = (Let x c1 c2, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  inversion X'.
  unfold cmdof.
  simpl.
  repeat dstr_.
  }

  assert (EQ_6: forall l, filterb (xOf (fun x  => Lof x) locs) (Aof l) 
         (fun v => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
         (map cmdof (updl T id (c1, Let' x c2 tx, p, O, C, id))))) =
         filterb (xOf (fun x  => Lof x) locs) (Aof l) (fun v => length (filter
         (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))(map cmdof T)))).
  {
  intros.
  symmetry.
  apply filterb_updl_eq.
  intros.
  split.
  unfold cmdof.
  simpl.
  rewrite not_waiting_cond_none.
  repeat dstr_.
  tauto.
  intros.
  assert (X':x' = (Let x c1 c2, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  inversion X'.
  unfold cmdof.
  simpl.
  repeat dstr_.
  }
  assert (EQ_5': map (wof h) (updl T id (c1, Let' x c2 tx, p, O, C, id)) = map (wof h) T).
  {
  unfold updl.
  rewrite map_map.
  rewrite map_list_upd.
  reflexivity.
  simpl.
  intros.
  destruct x0 as (((((c01,tx01),p01),O01),C01),id01).
  simpl in EQ.
  rewrite EQ in INx.
  assert (EQ1: (c01, tx01, p01, O01, C01) = (Let x c1 c2, tx, p, O, C)).
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  inversion EQ1.
  unfold wof.
  simpl.
  symmetry.
  apply not_waiting_none.
  tauto.
  }

  assert (bp0: boundph p).
  {
  apply BPE.
  apply in_map_iff.
  exists (Let x c1 c2, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  assert (bg0: boundgh C).
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
  exists (Let x c1 c2, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  rewrite EQ_1.
  rewrite EQ_2.
  rewrite EQ_2'.
  rewrite EQ_3.
  rewrite EQ_3'.
  rewrite EQ_4.
  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  apply red_Let; try assumption.
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
  rewrite <- EQy in *.
  destruct WF2 as (WF21,(WF22,WF23)).
  rewrite WASW in WF22.
  contradiction.
  apply in_map_iff.
  exists y.
  auto.
  apply WASW.
  }
  assumption.
  }

  exists. tauto.
  exists. tauto.
  exists.
  {
  intros.
  apply upd_updl.
  exists (Let x c1 c2, tx, p, O, C).
  tauto.
  tauto.
  }
  exists.
  {
  apply NoDup_updl.
  assumption.
  }
  exists.
  {
  exists. tauto.
  exists. tauto.
  exists.
  {
  intros.
  rewrite EQ_6.
  apply INAOK.
  assumption.
  assumption.
  }
  tauto.
  }
  exists. tauto.
  exists. tauto.
  exists.
  {
  intros.
  rewrite EQ_6.
  apply WTsOTsOK.
  auto.
  }
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x00,(EQ,IN)).
  destruct x00 as (((((y1,y2),y3),y4),y5),y6).
  unfold pof in EQ. unfold oof in EQ. unfold gof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec y6 id).
(* ==================== y6 = id ===========*)
  rewrite e in IN.
  inversion EQ.
  rewrite <- H2.
  rewrite <- H3.
  rewrite <- H4.
  rewrite <- H0.
  assert (tmp: (y1, y2, y3, y4, y5) = (Let x c1 c2, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN.
  assumption.
  assumption.
  inversion tmp.
  simpl in *.
  exists.
  unfold wellformed in *.
  simpl.
  split.
  destruct c1; try auto.
  simpl. tauto.
  exists.
  unfold weakest_pre_ct in *.
  simpl in *.
  assert (WWP:=WP).
  {
  eapply sat_weak_imp with (n:=m); try assumption.
  apply WWP.
  intros.
  eapply sat_pre_subs2 with (n:=m); try assumption.
  eapply sat_weak_imp with (n:=m); try assumption.
  apply SAT.
  intros.
  eapply sat_tx_weak_imp1 with (n:=m); try assumption.
  omega. omega. omega.
  }
  intros.
  destruct WF2 as (WF21,(WF22,WF23)).
  rewrite W4COND in WF22.
  inversion WF22.
(* ==================== z <> id ===========*)
  inversion EQ.
  rewrite H0 in IN.
  rewrite H1 in IN.
  rewrite H2 in IN.
  rewrite H3 in IN.
  rewrite H4 in IN.
  rewrite H5 in IN.
  assert (IN2:=IN).
  apply SOBS in IN.
  destruct IN as (WF,(WP1,VOBS1)).
  exists.
  assumption.
  exists.

  assert (bp1: boundph p0).
  {
  apply BPE.
  apply in_map_iff.
  exists (c, tx0, p0, O0, C0, id0).
  split. reflexivity. assumption.
  }
  assert (bg1: boundgh C0).
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
  apply WP1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  unfold WTs, OBs in *.
  apply VOBS1 in W4COND.
  destruct W4COND as (v,(l,(inv,(inl,(eqv,(eql,safe1)))))).
  exists v, l, inv, inl, eqv, eql.
  replace (filterb (xOf (fun x0 => Lof x0) locs) (Aof l) 
    (fun v0 : Z => length (filter (fun c0 => ifb (opZ_eq_dec (waiting_for_cond c0) (Some v0)))
    (map cmdof (updl T id (c1, Let' x c2 tx, p, O, C, id))))) ([[ev]])) with 
    (filterb (xOf (fun x  => Lof x) locs) (Aof l)
    (fun v : Z => length (filter (fun c : cmd =>
    ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) ([[ev]])).
  assumption.
  unfold filterb.
  repeat dstr_.
  rewrite EQ_5.
  reflexivity.
Qed.


Lemma Val_preserves_validity:
  forall m sp h t id x e c tx
         (CMD: t id = Some (Val e, Let' x c tx))
         (VALID: validk (S m) sp t h),
    validk m sp (upd Z.eq_dec t id (Some (subs c (subse x ([[e]])), tx))) h.
Proof.
  intros.
  unfold validk in VALID.
  destruct VALID as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
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
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.
  rewrite map_map in *.

  assert (tmp: exists p O C, In (Val e, Let' x c tx, p, O, C, id) T).
  apply TOK.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  exists (updl T id (subs c (subse x ([[e]])), tx, p, O, C, id)).
  exists invs, locs, Pinv, Pleak, Ainv, Cinv, Cleak.


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
  destruct WF as (WF1,(WF2,(WF3,WF4))).
  assert (EQ_1: map pof (updl T id (subs c (subse x ([[e]])), tx, p, O, C, id)) = map pof T).
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, Let' x c tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  assert (EQ_2: map (fun x => (pof x, snd x)) (updl T id (subs c (subse x ([[e]])), tx, p, O, C, id)) = map (fun x => (pof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, Let' x c tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  inversion EQA.
  rewrite e0.
  reflexivity.
  reflexivity.
  }
  assert (EQ_2': map (fun x => (gof x, snd x)) (updl T id (subs c (subse x ([[e]])), tx, p, O, C, id)) = map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, Let' x c tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  inversion EQA.
  rewrite e0.
  reflexivity.
  reflexivity.
  }
  assert (EQ_3: map oof (updl T id (subs c (subse x ([[e]])), tx, p, O, C, id)) = map oof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, Let' x c tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  }
  assert (EQ_3': map Aoof (updl T id (subs c (subse x ([[e]])), tx, p, O, C, id)) = map Aoof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, Let' x c tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  }
  assert (EQ_4: map gof (updl T id (subs c (subse x ([[e]])), tx, p, O, C, id)) = map gof T).
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, Let' x c tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  assert (EQ_5: forall v, filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) (Some v)))
          (map cmdof (updl T id (subs c (subse x ([[e]])), tx, p, O, C, id))) =
          filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
          (map cmdof T)).
  {
  intros.
  symmetry.
  apply filter_updl_eq.
  unfold cmdof.
  simpl.
  rewrite not_waiting_cond_none.
  repeat dstr_.
  apply not_waiting_subs.
  assumption.
  intros.
  assert (X':x' = (Val e, Let' x c tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  inversion X'.
  unfold cmdof.
  simpl.
  repeat dstr_.
  } 
  assert (EQ_6: forall l, filterb (xOf (fun x  => Lof x) locs) (Aof l) (fun v => length
         (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) (Some v)))
         (map cmdof (updl T id (subs c (subse x ([[e]])), tx, p, O, C, id))))) =
         filterb (xOf (fun x  => Lof x) locs) (Aof l) (fun v => length
         (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
         (map cmdof T)))).
  {
  intros.
  symmetry.
  apply filterb_updl_eq.
  intros.
  split.
  unfold cmdof.
  simpl.
  rewrite not_waiting_cond_none.
  repeat dstr_.
  apply not_waiting_subs.
  assumption.
  intros.
  assert (X':x' = (Val e, Let' x c tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  inversion X'.
  unfold cmdof.
  simpl.
  repeat dstr_.
  }
  assert (EQ_5': map (wof h) (updl T id (subs c (subse x ([[e]])), tx, p, O, C, id)) = map (wof h) T).
  {
  unfold updl.
  rewrite map_map.
  rewrite map_list_upd.
  reflexivity.
  simpl.
  intros.
  destruct x0 as (((((c01,tx01),p01),O01),C01),id01).
  simpl in EQ.
  rewrite EQ in INx.
  assert (EQ1: (c01, tx01, p01, O01, C01) = (Val e, Let' x c tx, p, O, C)).
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  inversion EQ1.
  unfold wof.
  simpl.
  symmetry.
  unfold not_waiting_in in *.
  induction c;
  try reflexivity.
  inversion WF3.
  inversion WF3.
  inversion WF3.
  }

  assert (bp: boundph p).
  {
  apply BPE.
  apply in_map_iff.
  exists (Val e, Let' x c tx, p, O, C, id).
  split. reflexivity. assumption.
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
  exists (Val e, Let' x c tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  rewrite EQ_1.
  rewrite EQ_2.
  rewrite EQ_2'.
  rewrite EQ_3.
  rewrite EQ_3'.
  rewrite EQ_4.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  apply red_Val; try assumption.
  }

  exists.
  {
  split.
  {
  intros.
  eapply SPUR1 with (c:=c0).
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  destruct (Z.eq_dec (snd y) id).
  unfold cmdof in EQy.
  simpl in EQy.
  rewrite <- EQy in *.
  destruct c;
  inversion WASW.
  contradiction.
  apply in_map_iff.
  exists y.
  auto.
  apply WASW.
  }
  assumption.
  }

  exists. tauto.
  exists. tauto.
  exists.
  {
  intros.
  apply upd_updl.
  exists (Val e, Let' x c tx, p, O, C).
  tauto.
  tauto.
  }
  exists.
  {
  apply NoDup_updl.
  assumption.
  }
  exists.
  exists. tauto.
  exists. tauto.
  exists.
  intros.
  rewrite EQ_6.
  apply INAOK; try  assumption.
  assumption.
  exists. tauto.
  exists. tauto.
  exists.
  {
  intros.
  rewrite EQ_6.
  apply WTsOTsOK.
  tauto.
  }

  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x00,(EQ,IN)).
  destruct x00 as (((((y1,y2),y3),y4),y5),y6).
  unfold pof in EQ. unfold oof in EQ. unfold gof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec y6 id).
(* ==================== y6 = id ===========*)
  rewrite e0 in IN.
  inversion EQ.
  rewrite <- H1.
  rewrite <- H2.
  rewrite <- H3.
  rewrite <- H4.
  assert (tmp: (y1, y2, y3, y4, y5) = (Val e, Let' x c tx, p, O, C)).
  eapply unique_key_eq.
  apply IN.
  assumption.
  assumption.
  inversion tmp.
  simpl in *.
  exists.
  unfold wellformed in *.
  simpl in *.
  split.
  destruct c; simpl in *; try assumption.
  split. apply not_waiting_subs; assumption.
  destruct WF2. apply wellformed_cmd_subs; assumption.
  destruct WF2 as (W1,(W2,(N1,N2))).
  split. apply wellformed_cmd_subs; assumption.
  split. apply wellformed_cmd_subs; assumption.
  split. apply not_waiting_subs; assumption.
  apply not_waiting_subs; assumption.
  destruct WF2 as (W1,(W2,(W3,(N1,(N2,N3))))).
  split. apply wellformed_cmd_subs; assumption.
  split. apply wellformed_cmd_subs; assumption.
  split. apply wellformed_cmd_subs; assumption.
  split. apply not_waiting_subs; assumption.
  split. apply not_waiting_subs; assumption.
  apply not_waiting_subs; assumption.
  destruct WF2 as (W1,(W2,(N1,N2))).
  split. apply wellformed_cmd_subs; assumption.
  split. apply wellformed_cmd_subs; assumption.
  split. apply not_waiting_subs; assumption.
  apply not_waiting_subs; assumption.
  assumption.
  exists.
  unfold weakest_pre_ct in *.

  eapply sat_weak_imp1; try assumption.
  apply WP.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  eapply not_waiting_subs with (se:= subse x ([[e]])) in WF3.
  rewrite W4COND in WF3.
  inversion WF3.
  trivial.
(* ==================== z <> id ===========*)
  inversion EQ.
  rewrite H0 in IN.
  rewrite H1 in IN.
  rewrite H2 in IN.
  rewrite H3 in IN.
  rewrite H4 in IN.
  rewrite H5 in IN.
  assert (IN2:=IN).
  apply SOBS in IN.
  destruct IN as (WF,(WP1,VOBS1)).
  exists.
  assumption.
  exists.
  assert (bp0: boundph p0).
  {
  apply BPE.
  apply in_map_iff.
  exists (c0, tx0, p0, O0, C0, id0).
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
  exists (c0, tx0, p0, O0, C0, id0).
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  apply WP1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.

  intros.
  unfold WTs, OBs in *.
  apply VOBS1 in W4COND.
  destruct W4COND as (v,(l,(inv,(inl,(eqv,(eql,safe1)))))).
  exists v, l, inv, inl, eqv, eql.
  replace (filterb (xOf (fun x0 => Lof x0) locs) (Aof l) 
    (fun v0 : Z => length (filter (fun c0 => ifb (opZ_eq_dec (waiting_for_cond c0) (Some v0)))
    (map cmdof (updl T id (subs c (subse x ([[e]])), tx, p, O, C, id))))) ([[ev]])) with 
    (filterb (xOf (fun x  => Lof x) locs) (Aof l)
    (fun v : Z => length (filter (fun c : cmd =>
    ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) ([[ev]])).
  assumption.
  unfold filterb.
  repeat dstr_.
  rewrite EQ_5.
  reflexivity.
Qed.


Lemma Val_done_preserves_validity:
  forall m sp h t id z
         (CMD: t id = Some (Val z, done))
         (VALID: validk (S m) sp t h),
    validk m sp (upd Z.eq_dec t id None) h.
Proof.
  intros.
  unfold validk in VALID.
  destruct VALID as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
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
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.
  rewrite map_map in *.


  exists (filter (fun xx => negb (Z.eqb (snd xx) id)) T).

  assert (tmp: exists p O C, In (Val z, done, p, O, C, id) T).
  {
  apply TOK.
  assumption.
  }
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  simpl in WP.
  inversion WP.
  rename H0 into oN.
  rename H into o'O.
  apply Permutation_nil in PERM.
  rewrite PERM in *.

  exists invs, locs, Pinv, (phplus Pleak p), Ainv, Cinv, (ghplus Cleak C).

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.


  assert (phpdefpinvleak: phplusdef p Pinv /\ phplusdef p Pleak).
  {
  apply PHPD.
  apply in_map_iff.
  exists (Val z, done, p, nil, C, id).
  tauto.
  }

  assert (EQ_1: fold_left phplus (map pof (filter (fun xx => negb (snd xx =? id)%Z) T)) (phplus Pinv (phplus Pleak p)) = 
                fold_left phplus (map pof T) (phplus Pinv Pleak)).
  {
  replace (phplus Pinv (phplus Pleak p)) with (phplus (phplus Pinv Pleak) p).
  apply eq_heap_Val;
  try tauto.
  intros.
  apply PHPD in IN.
  apply phpdef_pair;
  tauto.
  apply in_map_iff.
  exists (Val z, done, p, nil, C, id).
  tauto.
  apply phplus_assoc;
  try tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  }

  assert (ghpdefcinvleak: ghplusdef C Cinv /\ ghplusdef C Cleak).
  {
  apply GHPD.
  apply in_map_iff.
  exists (Val z, done, p, nil, C, id).
  tauto.
  }

  assert (EQ_1': fold_left ghplus (map gof (filter (fun xx => negb (snd xx =? id)%Z) T)) (ghplus Cinv (ghplus Cleak C)) = 
                fold_left ghplus (map gof T) (ghplus Cinv Cleak)).
  {
  replace (ghplus Cinv (ghplus Cleak C)) with (ghplus (ghplus Cinv Cleak) C).
  apply eq_gheap_Val;
  try tauto.
  intros.
  apply GHPD in IN.
  apply ghpdef_pair;
  tauto.
  apply in_map_iff.
  exists (Val z, done, p, nil, C, id).
  tauto.
  apply ghplus_assoc;
  try tauto.
  apply ghpdef_comm.
  tauto.
  apply ghpdef_comm.
  tauto.
  }

  assert (EQ_2: concat (map oof (filter (fun xx => negb (snd xx =? id)%Z) T)) = concat (map oof T)).
  {
  apply concat_map_filter.
  intros.
  unfold negb in H.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct ((x6 =? id)%Z) eqn:x6id.
  apply Z.eqb_eq in x6id.
  assert (EQ1: (x1, x2, x3, x4, x5) = (Val z, done, p, nil, C)).
  eapply unique_key_eq.
  apply IN.
  rewrite x6id.
  assumption.
  assumption.
  inversion EQ1.
  reflexivity.
  inversion H.
  }

  assert (EQ_2': concat (map Aoof (filter (fun xx => negb (snd xx =? id)%Z) T)) = concat (map Aoof T)).
  {
  apply concat_map_filter.
  intros.
  unfold negb in H.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct ((x6 =? id)%Z) eqn:x6id.
  apply Z.eqb_eq in x6id.
  assert (EQ1: (x1, x2, x3, x4, x5) = (Val z, done, p, nil, C)).
  eapply unique_key_eq.
  apply IN.
  rewrite x6id.
  assumption.
  assumption.
  inversion EQ1.
  reflexivity.
  inversion H.
  }

  assert (FIL: forall x, length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some x)))
    (map cmdof (filter (fun xx => negb (snd xx =? id)%Z) T))) =
    length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some x))) (map cmdof T))).
  {
  intros.
  rewrite <- map_filter with (f2:=(fun xx => ifb (opZ_eq_dec (waiting_for_cond (cmdof xx)) (Some x)))).
  rewrite <- map_filter with (f2:=(fun xx => ifb (opZ_eq_dec (waiting_for_cond (cmdof xx)) (Some x)))).
  rewrite filter_filter with (f3:=(fun xx => ifb (opZ_eq_dec (waiting_for_cond (cmdof xx)) (Some x)))).
  reflexivity.
  intros.
  simpl.
  destruct (negb (snd x0 =? id)%Z) eqn:x0id.
  simpl.
  rewrite Coq.Bool.Bool.andb_true_r.
  reflexivity.
  unfold negb in x0id.
  destruct (snd x0 =? id)%Z eqn:xid.
  apply Z.eqb_eq in xid.
  destruct x0 as (((((x1,x2),x3),x4),x5),x6).
  assert (EQ1: (x1, x2, x3, x4, x5) = (Val z, done, p, nil, C)).
  simpl in *.
  eapply unique_key_eq.
  apply INx.
  rewrite xid.
  assumption.
  assumption.
  inversion EQ1.
  unfold cmdof.
  simpl.
  repeat dstr_.
  inversion x0id.
  intros.
  reflexivity.
  intros.
  reflexivity.
  }
  assert (FILB: forall l, filterb (xOf (fun x  => Lof x) locs) (Aof l) (fun v => length
    (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof (filter (fun xx => negb (snd xx =? id)%Z) T)))) = 
    filterb (xOf (fun x  => Lof x) locs) (Aof l) (fun v => length (filter
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))).
  {
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.
  destruct (xOf (fun x0 => Lof x0) locs x).
  destruct (Z.eq_dec x (Aof l)).
  reflexivity.
  destruct (Z.eq_dec z0 (Aof l)).
  Focus 2.
  reflexivity.
  apply FIL.
  reflexivity.
  }

  assert (FIL2: forall x, length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some x)))
    (map cmdof (filter (fun xx =>
    negb (snd xx =? id)%Z) T))) =
    length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some x)))
    (map cmdof T))).
  {
  intros.
  rewrite <- map_filter with (f2:=(fun xx => ifb (opZ_eq_dec (waiting_for_cond (cmdof xx)) (Some x)))).
  rewrite <- map_filter with (f2:=(fun xx => ifb (opZ_eq_dec (waiting_for_cond (cmdof xx)) (Some x)))).
  rewrite filter_filter with (f3:=(fun xx => ifb (opZ_eq_dec (waiting_for_cond (cmdof xx)) (Some x)))).
  reflexivity.
  intros.
  simpl.
  destruct (negb (snd x0 =? id)%Z) eqn:x0id.
  simpl.
  rewrite Coq.Bool.Bool.andb_true_r.
  reflexivity.
  unfold negb in x0id.
  destruct (snd x0 =? id)%Z eqn:xid.
  apply Z.eqb_eq in xid.
  destruct x0 as (((((x1,x2),x3),x4),x5),x6).
  assert (EQ1: (x1, x2, x3, x4, x5) = (Val z, done, p, nil, C)).
  simpl in *.
  eapply unique_key_eq.
  apply INx.
  rewrite xid.
  assumption.
  assumption.
  inversion EQ1.
  unfold cmdof.
  simpl.
  repeat dstr_.
  inversion x0id.
  reflexivity.
  reflexivity.
  }

  rewrite EQ_1.
  rewrite EQ_1'.
  rewrite EQ_2.
  rewrite EQ_2'.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  apply red_Terminate with z; try assumption.
  }

  exists.
  {
  split.
  {
  intros.
  eapply SPUR1 with (c:=c).
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  apply filter_In in INy.
  destruct INy as (INy,INEQy).
  unfold negb in INEQy.
  destruct (snd y =? id)%Z.
  inversion INEQy.
  apply in_map_iff.
  exists y.
  auto.
  apply WASW.
  }
  assumption.
  }

  exists.
  {
  exists.
  {
  unfold defl in *.
  intros.
  apply DEFL with id1 id2.
  assumption.
  rewrite map_filter with (f3:=(fun xx =>  negb (snd xx =? id)%Z)) in IN1.
  eapply in_filter_in_l.
  apply IN1.
  intros.
  reflexivity.
  rewrite map_filter with (f3:=(fun xx =>  negb (snd xx =? id)%Z)) in IN2.
  eapply in_filter_in_l.
  apply IN2.
  intros.
  reflexivity.
  }

  exists. repeat php_. cnj_. repeat php_.
  cnj_. repeat php_.
  exists.
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  apply filter_In in INx.
  destruct INx as (INx,NEQ).
  destruct (snd x =? id)%Z eqn:xid.
  inversion NEQ.
  apply neqb_neq in xid.
  assert (G: phplusdef p0 Pinv /\ phplusdef p0 Pleak).
  {
  apply PHPD.
  apply in_map_iff.
  exists x.
  tauto.
  }
  split.
  tauto.
  apply phpdef_pair;
  try tauto.
  apply phpdef_comm.
  tauto.
  apply DEFL with (snd x) id.
  assumption.
  apply in_map_iff.
  exists x.
  inversion EQx.
  tauto.
  apply in_map_iff.
  exists (Val z, done, p, nil, C, id).
  tauto.
  }
  exists.
  {
  intros.
  apply BPE.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  apply filter_In in IN.
  destruct IN as (IN,NEQ).
  apply in_map_iff.
  exists x.
  auto.
  }
  split.
  assumption.
  split.
  apply boundph_mon with Pinv;
  try tauto.
  apply BPE.
  apply in_map_iff.
  exists (Val z, done, p, nil, C, id).
  tauto.
  replace (phplus (phplus Pleak p) Pinv) with (phplus (phplus Pinv Pleak) p).
  apply boundph_fold with (m:=pof) (l:=T);
  try tauto.
  intros.
  apply PHPD in IN.
  apply phpdef_pair;
  tauto.
  apply in_map_iff.
  exists (Val z, done, p, nil, C, id).
  tauto.
  rewrite phplus_assoc;
  try tauto.
  apply phplus_comm;
  try tauto.
  apply phpdef_pair;
  try tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  split.
  replace (phplus Pinv (phplus Pleak p)) with (phplus (phplus Pinv Pleak) p).
  apply boundph_fold with (m:=pof) (l:=T);
  try tauto.
  intros.
  apply PHPD in IN.
  apply phpdef_pair;
  tauto.
  apply in_map_iff.
  exists (Val z, done, p, nil, C, id).
  tauto.
  rewrite phplus_assoc;
  try tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  tauto.
  }
  exists.
  {
  exists.
  {
  unfold defl in *.
  intros.
  apply DEFLg with id1 id2.
  assumption.
  rewrite map_filter with (f3:=(fun xx =>  negb (snd xx =? id)%Z)) in IN1.
  eapply in_filter_in_l.
  apply IN1.
  intros.
  reflexivity.
  rewrite map_filter with (f3:=(fun xx =>  negb (snd xx =? id)%Z)) in IN2.
  eapply in_filter_in_l.
  apply IN2.
  intros.
  reflexivity.
  }
  exists.
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  apply filter_In in INx.
  destruct INx as (INx,NEQ).
  destruct (snd x =? id)%Z eqn:xid.
  inversion NEQ.
  apply neqb_neq in xid.
  assert (G: ghplusdef g Cinv /\ ghplusdef g Cleak).
  {
  apply GHPD.
  apply in_map_iff.
  exists x.
  tauto.
  }
  split.
  tauto.
  apply ghpdef_pair;
  try tauto.
  apply ghpdef_comm.
  tauto.
  apply DEFLg with (snd x) id.
  assumption.
  apply in_map_iff.
  exists x.
  inversion EQx.
  tauto.
  apply in_map_iff.
  exists (Val z, done, p, nil, C, id).
  tauto.
  }
  exists.
  {
  apply ghpdef_pair;
  try tauto.
  apply ghpdef_comm.
  tauto.
  apply ghpdef_comm.
  tauto.
  }
  assumption.
  }

  exists.
  {
  intros.
  unfold upd.
  split.
  intros.
  destruct (Z.eq_dec id0 id).
  inversion H.
  apply TOK in H.
  destruct H as (p',(O'',(C',IN'))).
  exists p',O'',C'.
  apply filter_In.
  split.
  assumption.
  unfold negb.
  unfold snd.
  simpl.
  destruct (id0 =? id)%Z eqn:id0id.
  apply Z.eqb_eq in id0id.
  contradiction.
  reflexivity.
  intros.
  destruct H as (p1,(O1,(C1,IN1))).
  destruct (Z.eq_dec id0 id).
  rewrite e in IN1.
  apply filter_In in IN1.
  destruct IN1 as (IN1,CO).
  unfold negb in CO.
  unfold snd in CO.
  simpl in CO.
  destruct (id =? id)%Z eqn:idid.
  inversion CO.
  apply neqb_neq in idid.
  contradiction.
  apply TOK.
  exists p1, O1, C1.
  eapply in_filter_in_l.
  apply IN1.
  }
  exists.
  {
  rewrite map_filter with (f3:=fun x => if (x =? id)%Z then false else true).
  apply nodup_filter.
  assumption.
  intros.
  unfold negb.
  reflexivity.
  }
  exists.
  {
  exists. assumption.
  exists. assumption.
  exists.
  {
  intros.
  rewrite FILB.
  apply INAOK.
  assumption.
  assumption.
  }
  assumption.
  }
  exists. tauto.
  exists. tauto.
  exists.
  {
  intros.
  apply WTsOTsOK in ULOCKED.
  destruct ULOCKED as (wteq,oteq).
  rewrite wteq.
  rewrite oteq.
  rewrite FILB.
  tauto.
  }

  intros.
  apply filter_In in ING.
  destruct ING as (ING, idid0).
  unfold negb in idid0.
  unfold snd in idid0.
  simpl in idid0. 
  destruct (id0 =? id)%Z eqn:id0id.
  inversion idid0.
  apply neqb_neq in id0id.
  assert (tmp:=ING).
  apply SOBS in tmp.
  destruct tmp as (WF1,(WP1,VOBS1)).
  exists.
  assumption.
  exists.

  assert (bp0: boundph p0).
  {
  apply BPE.
  apply in_map_iff.
  exists (c, tx, p0, O0, C0, id0).
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
  exists (c, tx, p0, O0, C0, id0).
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  apply WP1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  apply VOBS1 in W4COND.
  destruct W4COND as (v,(l,(inv,(inl,(eqv,(eql,safe1)))))).
  exists v, l, inv, inl, eqv, eql.
  unfold WTs, OBs in *.
  replace (filterb (xOf (fun x0 => Lof x0) locs) (Aof l) 
    (fun v0 : Z => length (filter (fun c0 => ifb (opZ_eq_dec (waiting_for_cond c0) (Some v0)))
    (map cmdof (filter (fun xx  => negb (snd xx =? id)%Z) T)))) ([[ev]])) with 
    (filterb (xOf (fun x  => Lof x) locs) (Aof l)
    (fun v : Z => length (filter (fun c : cmd =>
    ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) ([[ev]])).
  assumption.
  unfold filterb.
  repeat dstr_.
  rewrite FIL2.
  reflexivity.
Qed.


Lemma If1_preserves_validity:
  forall m sp h t id tx e c1 c2
         (VALIDK: validk (S m) sp t h)
         (CMD: t id = Some (Val e, If' c1 c2 tx))
         (TRUE: (0 < ([[e]]))%Z),
    validk m sp (upd Z.eq_dec t id (Some (c1, tx))) h.
Proof.
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
  unfold WTs, OBs.
  unfold validk.


  assert (tmp: exists p O C, In (Val e, If' c1 c2 tx, p, O, C, id) T).
  apply TOK.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  destruct WF as (WF1,(WF2,(WF3,(WF4,(WF5,WF6))))).

  exists (updl T id (c1, tx, p, O, C, id)).
  exists invs, locs, Pinv, Pleak, Ainv, Cinv, Cleak.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (EQC: map gof (updl T id (c1, tx, p, O, C, id)) = map gof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, If' c1 c2 tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQC': map (fun x => (gof x, snd x)) (updl T id (c1, tx, p, O, C, id)) = map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, If' c1 c2 tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e0.
  reflexivity.
  reflexivity.
  }

  assert (EQH: map pof (updl T id (c1, tx, p, O, C, id)) = map pof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, If' c1 c2 tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQH': map (fun x => (pof x, snd x)) (updl T id (c1, tx, p, O, C, id)) = map (fun x => (pof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, If' c1 c2 tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e0.
  reflexivity.
  reflexivity.
  }

  assert (EQAO: map Aoof (updl T id (c1, tx, p, O, C, id)) = map Aoof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, If' c1 c2 tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQOO: map oof (updl T id (c1, tx, p, O, C, id)) = map oof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, If' c1 c2 tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQFIL: forall e, length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some e))) (map cmdof T)) =
    length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some e))) (map cmdof (updl T id (c1, tx, p, O, C, id))))).
  {
  unfold updl.
  rewrite map_map.
  intros.
  apply length_filter_map_eq.
  intros.
  destruct (Z.eq_dec (snd a) id).
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl in e1.
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, If' c1 c2 tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply IN.
  rewrite e1.
  assumption.
  assumption.
  }
  inversion EQA.
  unfold cmdof. simpl.
  rewrite not_waiting_cond_none.
  reflexivity. assumption. reflexivity.
  }

  assert (EQWT: forall l, WTs l (map cmdof T) locs = 
    WTs l (map cmdof (updl T id (c1, tx, p, O, C, id))) locs).
  {
  unfold WTs.
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.
  destruct (xOf (fun x : location Z => Lof x) locs x); try reflexivity.
  destruct (Z.eq_dec x (Aof l)); try reflexivity.
  destruct (Z.eq_dec z (Aof l)).
  apply EQFIL. reflexivity.
  }

  assert (bp0: boundph p).
  {
  apply BPE.
  apply in_map_iff.
  exists (Val e, If' c1 c2 tx, p, O, C, id).
  split. reflexivity. assumption.
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
  exists (Val e, If' c1 c2 tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  rewrite EQH, EQH', EQC, EQC', EQAO, EQOO.
  simpl in *.
  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  apply red_If_true with e c2; try assumption.
  }
  exists.
  {
  unfold spur_ok.
  destruct SPUR as (SPUR1,SPUR2).
  split; intros.
  eapply SPUR1 with (c:=c).
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  unfold cmdof in EQx.
  simpl in EQx.
  inversion EQx.
  rewrite <- H in *.
  rewrite WASW in WF4.
  inversion WF4.
  rewrite <- EQx.
  apply in_map. assumption.
  apply WASW.
  apply SPUR2. assumption.
  }
  exists. tauto.
  exists. tauto.
  exists.
  {
  intros.
  apply upd_updl.
  exists (Val e, If' c1 c2 tx, p, O, C). auto.
  assumption.
  }
  exists.
  {
  apply NoDup_updl. assumption.
  }
  exists.
  {
  split. assumption.
  split. assumption.
  split.
  intros.
  unfold WTs, OBs in *.
  rewrite <- EQWT.
  apply INAOK. assumption.
  assumption. assumption.
  }
  exists. tauto.
  exists. tauto.
  exists. 
  {
  intros.
  unfold WTs in *.
  rewrite <- EQWT.
  apply WTsOTsOK. assumption.
  }
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  {
  symmetry in EQx.
  inversion EQx.
  split.
  unfold wellformed. simpl. tauto.
  split.
  assert (WP':=WP).
  unfold weakest_pre_ct in *.
  unfold Datatypes.id in *.
  simpl in *.
  destruct ((0 <? ([[e]]))%Z) eqn:lt_e.
  eapply sat_weak_imp1; try assumption.
  apply WP.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  apply Z_ltb_falseL in lt_e.
  omega.
  intros.
  rewrite W4COND in WF4. inversion WF4.
  }
  rewrite EQx in INx.
  assert (tmp:=INx).
  apply SOBS in tmp.
  destruct tmp as (WF',(SAT',SAFE')).
  split. assumption.
  split.

  assert (bp1: boundph p0).
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
  apply SAT'.
  intros.
  eapply sat_tx_weak_imp1; try assumption.

  intros.
  assert (tmp:= W4COND).
  apply SAFE' in W4COND.
  destruct W4COND as (v,(l,(inv,(inl,(aov,(aol,safe')))))).
  exists v, l, inv, inl, aov, aol.
  unfold WTs in *.
  rewrite <- EQWT.
  assumption.
Qed.


Lemma If2_preserves_validity:
  forall m sp h t id tx e c1 c2
         (VALIDK: validk (S m) sp t h)
         (CMD: t id = Some (Val e, If' c1 c2 tx))
         (False: (([[e]]) <= 0)%Z),
    validk m sp (upd Z.eq_dec t id (Some (c2, tx))) h.
Proof.
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
  unfold WTs, OBs.
  unfold validk.


  assert (tmp: exists p O C, In (Val e, If' c1 c2 tx, p, O, C, id) T).
  apply TOK.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  destruct WF as (WF1,(WF2,(WF3,(WF4,(WF5,WF6))))).

  exists (updl T id (c2, tx, p, O, C, id)).
  exists invs, locs, Pinv, Pleak, Ainv, Cinv, Cleak.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (EQC: map gof (updl T id (c2, tx, p, O, C, id)) = map gof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, If' c1 c2 tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQC': map (fun x => (gof x, snd x)) (updl T id (c2, tx, p, O, C, id)) = map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, If' c1 c2 tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e0.
  reflexivity.
  reflexivity.
  }

  assert (EQH: map pof (updl T id (c2, tx, p, O, C, id)) = map pof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, If' c1 c2 tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQH': map (fun x => (pof x, snd x)) (updl T id (c2, tx, p, O, C, id)) = map (fun x => (pof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, If' c1 c2 tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e0.
  reflexivity.
  reflexivity.
  }

  assert (EQAO: map Aoof (updl T id (c2, tx, p, O, C, id)) = map Aoof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, If' c1 c2 tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQOO: map oof (updl T id (c2, tx, p, O, C, id)) = map oof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, If' c1 c2 tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQFIL: forall e, length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some e))) (map cmdof T)) =
    length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some e))) (map cmdof (updl T id (c2, tx, p, O, C, id))))).
  {
  unfold updl.
  rewrite map_map.
  intros.
  apply length_filter_map_eq.
  intros.
  destruct (Z.eq_dec (snd a) id).
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl in e1.
  assert (EQA: (a1,a2,a3,a4,a5) = (Val e, If' c1 c2 tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply IN.
  rewrite e1.
  assumption.
  assumption.
  }
  inversion EQA.
  unfold cmdof. simpl.
  rewrite not_waiting_cond_none.
  reflexivity. assumption. reflexivity.
  }

  assert (EQWT: forall l, WTs l (map cmdof T) locs = 
    WTs l (map cmdof (updl T id (c2, tx, p, O, C, id))) locs).
  {
  unfold WTs.
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.
  destruct (xOf (fun x : location Z => Lof x) locs x); try reflexivity.
  destruct (Z.eq_dec x (Aof l)); try reflexivity.
  destruct (Z.eq_dec z (Aof l)).
  apply EQFIL. reflexivity.
  }

  assert (bp: boundph p).
  {
  apply BPE.
  apply in_map_iff.
  exists (Val e, If' c1 c2 tx, p, O, C, id).
  split. reflexivity. assumption.
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
  exists (Val e, If' c1 c2 tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  rewrite EQH, EQH', EQC, EQC', EQAO, EQOO.
  simpl in *.
  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  apply red_If_false with e c1; try assumption.
  }
  exists.
  {
  unfold spur_ok.
  destruct SPUR as (SPUR1,SPUR2).
  split; intros.
  eapply SPUR1 with (c:=c).
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  unfold cmdof in EQx.
  simpl in EQx.
  inversion EQx.
  rewrite <- H in *.
  rewrite WASW in WF5.
  inversion WF5.
  rewrite <- EQx.
  apply in_map. assumption.
  apply WASW.
  apply SPUR2. assumption.
  }
  exists. tauto.
  exists. tauto.
  exists.
  {
  intros.
  apply upd_updl.
  exists (Val e, If' c1 c2 tx, p, O, C). auto.
  assumption.
  }
  exists.
  {
  apply NoDup_updl. assumption.
  }
  exists.
  {
  split. assumption.
  split. assumption.
  split.
  intros.
  unfold WTs, OBs in *.
  rewrite <- EQWT.
  apply INAOK. assumption.
  assumption. assumption.
  }
  exists. tauto.
  exists. tauto.
  exists. 
  {
  intros.
  unfold WTs in *.
  rewrite <- EQWT.
  apply WTsOTsOK. assumption.
  }
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  {
  symmetry in EQx.
  inversion EQx.
  split.
  unfold wellformed. simpl. tauto.
  split.
  assert (WP':=WP).
  unfold weakest_pre_ct in *.
  unfold Datatypes.id in *.
  simpl in *.

  destruct ((0 <? ([[e]]))%Z) eqn:lt_e.
  apply Z.ltb_lt in lt_e.
  omega.
  eapply sat_weak_imp1; try assumption.
  apply WP'.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  rewrite W4COND in WF5. inversion WF5.
  }
  rewrite EQx in INx.
  assert (tmp:=INx).
  apply SOBS in tmp.
  destruct tmp as (WF',(SAT',SAFE')).
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
  apply SAT'.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  assert (tmp:= W4COND).
  apply SAFE' in W4COND.
  destruct W4COND as (v,(l,(inv,(inl,(aov,(aol,safe')))))).
  exists v, l, inv, inl, aov, aol.
  unfold WTs in *.
  rewrite <- EQWT.
  assumption.
Qed.


Lemma If_preserves_validity:
  forall m sp h t id tx c c1 c2
         (VALIDK: validk (S m) sp t h)
         (CMD: t id = Some (If c c1 c2, tx)),
    validk m sp (upd Z.eq_dec t id (Some (c, If' c1 c2 tx))) h.
Proof.
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
  unfold WTs, OBs.
  unfold validk.


  assert (tmp: exists p O C, In (If c c1 c2, tx, p, O, C, id) T).
  apply TOK.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  destruct WF as ((WF1,(WF2,(WF3,(WF4,WF5)))),WF6).

  exists (updl T id (c, If' c1 c2 tx, p, O, C, id)).
  exists invs, locs, Pinv, Pleak, Ainv, Cinv, Cleak.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (EQC: map gof (updl T id (c, If' c1 c2 tx, p, O, C, id)) = map gof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (If c c1 c2, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQC': map (fun x => (gof x, snd x)) (updl T id (c, If' c1 c2 tx, p, O, C, id)) = map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (If c c1 c2, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQH: map pof (updl T id (c, If' c1 c2 tx, p, O, C, id)) = map pof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (If c c1 c2, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQH': map (fun x => (pof x, snd x)) (updl T id (c, If' c1 c2 tx, p, O, C, id)) = map (fun x => (pof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (If c c1 c2, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQAO: map Aoof (updl T id (c, If' c1 c2 tx, p, O, C, id)) = map Aoof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (If c c1 c2, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQOO: map oof (updl T id (c, If' c1 c2 tx, p, O, C, id)) = map oof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (If c c1 c2, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQFIL: forall e, length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some e))) (map cmdof T)) =
    length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some e))) (map cmdof (updl T id (c, If' c1 c2 tx, p, O, C, id))))).
  {
  unfold updl.
  rewrite map_map.
  intros.
  apply length_filter_map_eq.
  intros.
  destruct (Z.eq_dec (snd a) id).
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl in e0.
  assert (EQA: (a1,a2,a3,a4,a5) = (If c c1 c2, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply IN.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  unfold cmdof. simpl.
  rewrite not_waiting_cond_none.
  reflexivity. assumption. reflexivity.
  }

  assert (EQWT: forall l, WTs l (map cmdof T) locs = 
    WTs l (map cmdof (updl T id (c, If' c1 c2 tx, p, O, C, id))) locs).
  {
  unfold WTs.
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.
  destruct (xOf (fun x : location Z => Lof x) locs x); try reflexivity.
  destruct (Z.eq_dec x (Aof l)); try reflexivity.
  destruct (Z.eq_dec z (Aof l)).
  apply EQFIL. reflexivity.
  }

  assert (bp: boundph p).
  {
  apply BPE.
  apply in_map_iff.
  exists (If c c1 c2, tx, p, O, C, id).
  split. reflexivity. assumption.
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
  exists (If c c1 c2, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  rewrite EQH, EQH', EQC, EQC', EQAO, EQOO.
  simpl in *.
  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  apply red_If; try assumption.
  }
  exists.
  {
  unfold spur_ok.
  destruct SPUR as (SPUR1,SPUR2).
  split; intros.
  eapply SPUR1 with (c:=c0).
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  unfold cmdof in EQx.
  simpl in EQx.
  inversion EQx.
  rewrite <- H in *.
  rewrite WASW in WF4.
  inversion WF4.
  rewrite <- EQx.
  apply in_map. assumption.
  apply WASW.
  apply SPUR2. assumption.
  }
  exists. tauto.
  exists. tauto.
  exists.
  {
  intros.
  apply upd_updl.
  exists (If c c1 c2, tx, p, O, C). auto.
  assumption.
  }
  exists.
  {
  apply NoDup_updl. assumption.
  }
  exists.
  {
  split. assumption.
  split. assumption.
  split.
  intros.
  unfold WTs, OBs in *.
  rewrite <- EQWT.
  apply INAOK. assumption.
  assumption. assumption.
  }
  exists. tauto.
  exists. tauto.
  exists. 
  {
  intros.
  unfold WTs in *.
  rewrite <- EQWT.
  apply WTsOTsOK. assumption.
  }
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  {
  symmetry in EQx.
  inversion EQx.
  split.
  unfold wellformed. simpl. tauto.
  split.
  unfold weakest_pre_ct in WP.
  simpl in WP.
  unfold weakest_pre_ct.
  eapply sat_weak_imp; try assumption.
  apply WP.
  intros.
  simpl in SAT.
  simpl.
  destruct (0 <? z)%Z.
  eapply sat_weak_imp; try assumption.
  apply SAT.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  omega.
  eapply sat_weak_imp; try assumption.
  apply SAT.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  omega.
  omega.
  intros.
  rewrite W4COND in WF4. inversion WF4.
  }
  rewrite EQx in INx.
  assert (tmp:=INx).
  apply SOBS in tmp.
  destruct tmp as (WF',(SAT',SAFE')).
  split. assumption.
  split.
  assert (bp0: boundph p0).
  {
  apply BPE.
  apply in_map_iff.
  exists (c0, tx0, p0, O0, C0, id0).
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
  exists (c0, tx0, p0, O0, C0, id0).
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  apply SAT'.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  assert (tmp:= W4COND).
  apply SAFE' in W4COND.
  destruct W4COND as (v,(l,(inv,(inl,(aov,(aol,safe')))))).
  exists v, l, inv, inl, aov, aol.
  unfold WTs in *.
  rewrite <- EQWT.
  assumption.
Qed.


Lemma While_preserves_validity:
  forall m sp h t id tx x c c1
         (VALIDK: validk (S m) sp t h)
         (CMD: t id = Some (While c c1,tx))
         (NOTFREE: is_free (While c c1) x = false),
    validk m sp (upd Z.eq_dec t id (Some (If c (Let x c1 (While c c1)) tt, tx))) h.
Proof.
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
  unfold WTs, OBs.
  unfold validk.

  assert (tmp: exists p O C, In (While c c1, tx, p, O, C, id) T).
  apply TOK.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  destruct WF as (WF1,WF5).
  destruct WF1 as (WF1,(WF2,(WF3,WF4))).
  exists (updl T id (If c (Let x c1 (While c c1)) tt, tx, p, O, C, id)).
  exists invs, locs, Pinv, Pleak, Ainv, Cinv, Cleak.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (EQC: map gof (updl T id (If c (Let x c1 (While c c1)) tt, tx, p, O, C, id)) = map gof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (While c c1, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQC': map (fun x => (gof x, snd x)) (updl T id (If c (Let x c1 (While c c1)) tt, tx, p, O, C, id)) = map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (While c c1, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQH: map pof (updl T id (If c (Let x c1 (While c c1)) tt, tx, p, O, C, id)) = map pof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (While c c1, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQH': map (fun x => (pof x, snd x)) (updl T id (If c (Let x c1 (While c c1)) tt, tx, p, O, C, id)) = map (fun x => (pof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (While c c1, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQAO: map Aoof (updl T id (If c (Let x c1 (While c c1)) tt, tx, p, O, C, id)) = map Aoof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (While c c1, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.

  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQOO: map oof (updl T id (If c (Let x c1 (While c c1)) tt, tx, p, O, C, id)) = map oof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (While c c1, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQFIL: forall e, length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some e))) (map cmdof T)) =
    length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some e))) (map cmdof (updl T id (If c (Let x c1 (While c c1)) tt, tx, p, O, C, id))))).
  {
  unfold updl.
  rewrite map_map.
  intros.
  apply length_filter_map_eq.
  intros.
  destruct (Z.eq_dec (snd a) id).
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl in e0.
  assert (EQA: (a1,a2,a3,a4,a5) = (While c c1, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply IN.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  unfold cmdof. simpl.
  reflexivity.
  reflexivity.
  }

  assert (EQWT: forall l, WTs l (map cmdof T) locs = 
    WTs l (map cmdof (updl T id (If c (Let x c1 (While c c1)) tt, tx, p, O, C, id))) locs).
  {
  unfold WTs.
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.
  destruct (xOf (fun x1 : location Z => Lof x1) locs x0); try reflexivity.
  destruct (Z.eq_dec x0 (Aof l)); try reflexivity.
  destruct (Z.eq_dec z (Aof l)).
  apply EQFIL. reflexivity.
  }

  assert (inp: In p (map pof T)).
  {
  apply in_map_iff.
  exists (While c c1, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  assert (inc: In C (map gof T)).
  {
  apply in_map_iff.
  exists (While c c1, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  assert (bp: boundph p).
  {
  apply BPE; try assumption.
  }

  assert (bgc: boundgh C).
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
  exists (While c c1, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  rewrite EQH, EQH', EQC, EQC', EQAO, EQOO.
  simpl in *.
  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  apply red_While; try assumption.
  }
  exists.
  {
  unfold spur_ok.
  destruct SPUR as (SPUR1,SPUR2).
  split; intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x4,(EQx,INx)).
  destruct (Z.eq_dec (snd x4) id).
  unfold cmdof in EQx.
  simpl in EQx.
  inversion EQx.
  rewrite <- H in *.
  inversion WASW.
  eapply SPUR1 with (c:=c0).
  rewrite <- EQx.
  apply in_map. assumption.
  apply WASW.
  apply SPUR2. assumption.
  }
  exists. tauto.
  exists. tauto.
  exists.
  {
  intros.
  apply upd_updl.
  exists (While c c1, tx, p, O, C). auto.
  assumption.
  }
  exists.
  {
  apply NoDup_updl. assumption.
  }
  exists.
  {
  split. assumption.
  split. assumption.
  split.
  intros.
  unfold WTs, OBs in *.
  rewrite <- EQWT.
  apply INAOK. assumption.
  assumption. assumption.
  }
  exists. tauto.
  exists. tauto.
  exists. 
  {
  intros.
  unfold WTs in *.
  rewrite <- EQWT.
  apply WTsOTsOK. assumption.
  }
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x4,(EQx,INx)).
  destruct (Z.eq_dec (snd x4) id).
  {
  symmetry in EQx.
  inversion EQx.
  split.
  unfold wellformed. simpl.
  tauto.
  split.
  {
  assert (WP':=WP).

  unfold weakest_pre_ct in *.
  unfold Datatypes.id in *.
  simpl in WP'.
  simpl.
  destruct m.
  reflexivity.
  simpl.
  eapply sat_weak_imp; try assumption.
  apply WP'.
  intros.
  destruct m.
  destruct (0 <? z)%Z eqn:zz; reflexivity.
  destruct (0 <? z)%Z eqn:zz.
  simpl.
  eapply sat_weak_imp; try assumption.
  apply SAT.
  intros.
  eapply sat_weak_imp with (n:=S m); try assumption.
  apply wp_subst_free; try assumption.
  simpl.
  rewrite subsc_id. rewrite subsc_id. assumption.
  {
  eapply sat_weak_imp; try assumption.
  apply SAT0.
  simpl.
  intros.
  apply SAT1.
  omega.
  }
  intros.
  simpl.
  eapply sat_tx_weak_imp; try assumption.
  apply SAT1.
  omega.
  omega.
  omega.
  simpl.
  eapply sat_tx_weak_imp; try assumption.
  apply SAT.
  omega.
  omega.
  }
  intros.
  inversion W4COND.
  }
  rewrite EQx in INx.
  assert (tmp:=INx).
  apply SOBS in tmp.
  destruct tmp as (WF',(SAT',SAFE')).
  split. assumption.

  assert (bp0: boundph p0).
  {
  apply BPE.
  apply in_map_iff.
  exists (c0, tx0, p0, O0, C0, id0).
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
  exists (c0, tx0, p0, O0, C0, id0).
  split. reflexivity. assumption.
  }
  split.
  eapply sat_ct_weak_imp; try assumption.
  apply SAT'.
  omega.
  intros.
  assert (tmp:= W4COND).
  apply SAFE' in W4COND.
  destruct W4COND as (v,(l,(inv,(inl,(aov,(aol,safe')))))).
  exists v, l, inv, inl, aov, aol.
  unfold WTs in *.
  rewrite <- EQWT.
  assumption.
Qed.


Lemma Newlock_preserves_validity:
  forall m sp h t id tx l
         (VALIDK: validk (S m) sp t h)
         (CMD : t id = Some (Newlock, tx))
         (FRE: h l = None),
    validk m sp (upd Z.eq_dec t id (Some (Val (Enum l),tx))) (upd Z.eq_dec h l (Some 1%Z)).
Proof.
  intros.
  unfold validk in VALIDK.
  destruct VALIDK as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
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
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONOK)).
  rewrite map_map in *.

  assert (tmp: exists p O C, In (Newlock, tx, p, O, C, id) T).
  {
  apply TOK.
  assumption.
  }

  destruct tmp as (p,(O,(C,INT))).

  assert (inp: In p (map pof T)).
  {
  apply in_map_iff.
  exists (Newlock, tx, p, O, C, id).
  tauto.
  }

  assert (inpid: In (p, id) (map (fun x0 => (pof x0, snd x0)) T)).
  {
  apply in_map_iff.
  exists (Newlock, tx, p, O, C, id).
  tauto.
  }

  assert (phpdp0il: forall p0 : pheap, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  apply phpdef_pair; try tauto.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  }

  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,SOBS1)).
  unfold wellformed in WF.
  simpl in WF.

  assert (bp: boundph p).
  {
  apply BPE.
  assumption.
  }

  assert (bg: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); try tauto.
  intros.
  apply ghpdef_pair; try tauto.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (Newlock, tx, p, O, C, id).
  tauto.
  }

  apply sat_newlock with (l:=l) in WP; try tauto.
  Focus 2.
  intros.
  assert (PH:=PH2H).
  unfold phtoh in PH.
  destruct PH as (PH,PH1).

  specialize PH with ll.
  rewrite EQA in PH.
  simpl in PH.
  rewrite FRE in PH.
  destruct (fold_left phplus (map (fun x => pof x) T) (phplus Pinv Pleak) ll) eqn:fl.
  destruct k; try inversion PH; try contradiction.
  apply fold_None with (m:=pof) (l:=T) (b:=phplus Pinv Pleak); try tauto.

  destruct WP as (r,sat1).

  exists (updl T id (Val (Enum l), tx, upd (location_eq_dec Z.eq_dec) p ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) (Some (Ulock empb empb)), O, C, id)).
  exists invs, (((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil)::locs), Pinv, Pleak, Ainv, Cinv, Cleak.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (NONE: forall R I L X M M' P, fold_left phplus (map pof T) (phplus Pinv Pleak) (l, R, I, L, X, M, M', P) = None).
  {
  assert (PH:=PH2H).
  unfold phtoh in PH.
  destruct PH as (PH,PH1).
  intros.
  specialize PH with (l, R, I, L, X, M, M', P).
  unfold Aof in PH.
  unfold Oof in PH.
  unfold Aofo in PH.
  simpl in PH.
  rewrite FRE in PH.
  destruct (fold_left phplus (map (fun x => pof x) T) (phplus Pinv Pleak) (l, R, I, L, X, M, M', P)) eqn:fl.
  destruct k; try inversion PH; try contradiction.
  reflexivity.
  }

  assert (phpdefpi: phplusdef p Pinv).
  {
  apply PHPD.
  assumption.
  }

  assert (phpdefpl: phplusdef p Pleak).
  {
  apply PHPD.
  assumption.
  }

  assert (pilN: phplus Pinv Pleak ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) = None).
  {
  apply fold_None with (m:=pof) (l:=T) (b:=phplus Pinv Pleak); try tauto.
  apply NONE.
  }

  assert (piN: Pinv ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) = None).
  {
  apply phplus_None with Pleak.
  assumption.
  }

  assert (plN: Pleak ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) = None).
  {
  apply phplus_None with Pinv.
  rewrite phplus_comm.
  assumption.
  repeat php_.
  }

  assert (NODUP1: NoDup (map snd (updl T id (Val (Enum l), tx, upd (location_eq_dec Z.eq_dec) p ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) (Some (Ulock empb empb)), O, C, id)))).
  {
  apply NoDup_updl.
  assumption.
  }

  assert (defl1: defl phplusdef (map (fun x0 => (pof x0, snd x0)) (updl T id
   (Val (Enum l), tx, upd (location_eq_dec Z.eq_dec) p ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil)(Some (Ulock empb empb)), O, C, id)))).
  {
  apply defl_New with (b:=phplus Pinv Pleak) (z:=((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil)) (p:=p) (v:=(Some (Ulock empb empb))); try tauto.
  intros.
  apply phpdef_comm.
  apply phpdef_v.
  apply DEFL with id id0.
  omega.
  assumption.
  assumption.
  apply fold_None with (m:=pof) (l:=T) (b:=phplus Pinv Pleak); repeat php_.
  left.
  apply in_map_iff.
  apply in_map_iff in IN.
  destruct IN as (x',(EQx,INx)).
  exists x'.
  inversion EQx.
  auto.
  apply NONE.
  }

  assert (phpdefpil: phplusdef p (phplus Pinv Pleak)).
  {
  apply phpdef_pair; try tauto;
  apply PHPD; try tauto.
  }

  assert (phpdefp0il: forall p0, In p0 (map pof (updl T id
    (Val (Enum l), tx, upd (location_eq_dec Z.eq_dec) p ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil)
    (Some (Ulock empb empb)), O, C, id))) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  unfold updl.
  rewrite map_map.
  intros.
  apply in_map_iff in H.
  destruct H as (x0,(EQ,IN)).
  destruct (Z.eq_dec (snd x0) id).
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  apply phpdef_ulock; try tauto.
  apply phpdp0il.
  rewrite <- EQ.
  inm_.
  }

  assert (ULOCK: fold_left phplus (map pof (updl T id (Val (Enum l), tx, upd (location_eq_dec Z.eq_dec) p ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) (Some (Ulock empb empb)), O, C, id))) (phplus Pinv Pleak)
    ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) = Some (Ulock empb empb)).
  {
  apply fold_ulock; try tauto.
  apply pofs.
  right.
  exists (upd (location_eq_dec Z.eq_dec) p ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil)
    (Some (Ulock empb empb))).
  unfold updl.
  rewrite map_map.
  exists.
  apply in_map_iff.
  exists (Newlock, tx, p, O, C, id).
  simpl.
  rewrite eqz.
  tauto.
  repeat dstr_.
  }

  assert (EQH: forall z (NEQ: z <> ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil)), 
    fold_left phplus (map pof (updl T id (Val (Enum l), tx, upd (location_eq_dec Z.eq_dec) p ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) (Some (Ulock empb empb)), O, C, id))) (phplus Pinv Pleak) z
    = fold_left phplus (map pof T) (phplus Pinv Pleak) z).
  {
  intros.
  apply eq_heap with (z:=((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil))(p:=p)(v:=Some (Ulock empb empb)); try tauto.
  apply pofs.
  intros.
  apply phpdef_comm.
  apply phpdef_ulock.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ,IN)).
  inversion EQ.
  apply DEFL with id (snd x1).
  omega.
  unfold pof.
  apply in_map_iff.
  exists (Newlock, tx, p, O, C, id).
  tauto.
  apply in_map_iff.
  exists x1.
  tauto.
  apply fold_None with (m:=pof) (l:=T) (b:=phplus Pinv Pleak); try tauto.
  apply NONE.
  left.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ,IN)).
  inversion EQ.
  apply in_map_iff.
  exists x1; tauto.
  apply phpdef_ulock; try tauto.
  unfold not.
  intros.
  rewrite H in NEQ.
  contradiction.
  }

  assert (NINL: ~ In ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) locs).
  {
  unfold not.
  intros.
  apply LOCs in H.
  rewrite NONE in H.
  contradiction.
  }

  assert (EQG: map (fun x0 => (gof x0, snd x0))
    (updl T id (Val (Enum l), tx, upd (location_eq_dec Z.eq_dec) p ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) (Some (Ulock empb empb)), O, C, id)) =
    map (fun x0 => (gof x0, snd x0)) T).
  {
  unfold updl.
  rewrite map_map.
  unfold gof.
  simpl.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  rewrite e.

  assert (EQA: a = (Newlock, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }

  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQG': map gof (updl T id (Val (Enum l), tx,
    upd (location_eq_dec Z.eq_dec) p ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil)
   (Some (Ulock empb empb)), O, C, id)) = map gof T).
  {
  unfold updl.
  rewrite map_map.
  unfold gof.
  simpl.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).

  assert (EQA: a = (Newlock, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }

  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQFIL: forall x p, length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) x))
    (map cmdof (updl T id (Val (Enum l), tx, p, O, C, id)))) = 
    length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) x)) (map cmdof T))).
  {
  intros.
  unfold updl.
  rewrite map_map.
  apply filter_map_eq.
  intros.
  destruct x0 as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  rewrite e in *.
  assert (EQX: (a1, a2, a3, a4, a5) = (Newlock, tx, p, O, C)).
  apply unique_key_eq with T a6; try tauto.
  rewrite e.
  assumption.
  rewrite e.
  assumption.
  inversion EQX.
  reflexivity.
  reflexivity.
  }

  assert (EQWT: forall l0, WTs l0 (map cmdof (updl T id (Val (Enum l), tx, upd (location_eq_dec Z.eq_dec) p
   ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) (Some (Ulock empb empb)), O, C, id)))
   (((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) :: locs) =
   WTs l0 (map cmdof T) locs).
  {
  unfold WTs.
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.
  destruct (xOf (fun x1 => Lof x1) locs x) eqn:xof.
  assert (xof1: xOf (fun x1 => Lof x1)
    (((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) :: locs) x = Some z).
  {
  apply xof_mon.
  assumption.
  unfold not.
  intros.
  apply LOCs in H.
  destruct l' as (((((((x1,x2),x3),x4),x5),x6),x7),x8).
  unfold Aof in EQ.
  unfold Aofo in EQ.
  simpl in EQ.
  inversion EQ.
  rewrite EQ in H.
  rewrite NONE in H.
  contradiction.
  }

  rewrite xof1.
  destruct (Z.eq_dec x (Aof l0)).
  reflexivity.
  destruct (Z.eq_dec z (Aof l0)).
  Focus 2.
  reflexivity.
  apply EQFIL.
  simpl.
  unfold Aof.
  unfold Aofo.
  unfold Lof.
  unfold Oof.
  unfold Lofo.
  simpl.
  destruct (Z.eq_dec x l).

  destruct (Z.eq_dec x (fst (fst (fst (fst (fst (fst (fst l0)))))))).
  reflexivity.
  destruct (Z.eq_dec l (fst (fst (fst (fst (fst (fst (fst l0)))))))).
  omega.
  reflexivity.
  unfold Lof in xof.
  unfold Oof in xof.
  unfold Lofo in xof.
  rewrite xof.
  reflexivity.
  }

  assert (EQCNT: forall p x, count_occ Z.eq_dec (concat (map Aoof (updl T id (Val (Enum l), tx, p, O, C, id)))) x =
    count_occ Z.eq_dec (concat (map Aoof T)) x).
  {
  intros.
  symmetry.
  apply count_updl_eq.
  intros.
  assert (X': x' = (Newlock, tx, p, O, C, id)).
  apply in_elem with T; try assumption.
  rewrite X'.
  reflexivity.
  }

  assert (EQOT: forall l0 p, OBs l0 (concat (map Aoof (updl T id
    (Val (Enum l), tx, p, O, C, id)))) (((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) :: locs) =
    OBs l0 (concat (map Aoof T)) locs).
  {
  unfold OBs.
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.

  destruct (xOf (fun x1 => Lof x1) locs x) eqn:xof.
  assert (xof1: xOf (fun x1 => Lof x1)
    (((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) :: locs) x = Some z).
  {
  apply xof_mon.
  assumption.
  unfold not.
  intros.
  apply LOCs in H.
  destruct l' as (((((((x1,x2),x3),x4),x5),x6),x7),x8).
  unfold Aof in EQ.
  unfold Aofo in EQ.
  simpl in EQ.
  inversion EQ.
  rewrite EQ in H.
  rewrite NONE in H.
  contradiction.
  }

  rewrite xof1.
  destruct (Z.eq_dec x (Aof l0)).
  reflexivity.
  destruct (Z.eq_dec z (Aof l0)).
  Focus 2.
  reflexivity.
  apply EQCNT.
  simpl.
  unfold Aof.
  unfold Aofo.
  unfold Lof.
  unfold Oof.
  unfold Lofo.
  simpl.
  destruct (Z.eq_dec x l).
  destruct (Z.eq_dec x (fst (fst (fst (fst (fst (fst (fst l0)))))))).

  reflexivity.
  destruct (Z.eq_dec l (fst (fst (fst (fst (fst (fst (fst l0)))))))).
  omega.
  reflexivity.
  unfold Lof in xof.
  unfold Oof in xof.
  unfold Lofo in xof.

  rewrite xof.
  reflexivity.
  }

  assert (EQO: forall p, map oof (updl T id (Val (Enum l), tx, p, O, C, id)) = map oof T).
  {
  unfold updl.
  intros.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (Newlock, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  assert (WTemp: WTs ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) (map cmdof T) locs = empb).
  {
  unfold WTs.
  unfold filterb.
  unfold empb.
  apply functional_extensionality.
  intros.
  destruct (xOf (fun x0 : location Z => Lof x0) locs x) eqn:XOF.
  unfold Aof.
  unfold Aofo.
  simpl.
  destruct (Z.eq_dec x l).
  reflexivity.
  destruct (Z.eq_dec z l).
  rewrite e in XOF.
  Focus 2.
  reflexivity.
  Focus 2.
  reflexivity.
  destruct (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some x)))(map cmdof T)) eqn:fil.
  reflexivity.
  assert (IN1: In c (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some x)))(map cmdof T))).
  rewrite fil.
  left.
  reflexivity.
  apply filter_In in IN1.
  destruct IN1 as (IN,EQ).
  unfold ifb in EQ.
  destruct (opZ_eq_dec (waiting_for_cond c) (Some x)).
  Focus 2.
  inversion EQ.
  destruct c; inversion e0.
  {
  apply in_map_iff in IN.
  destruct IN as (x1,(EQx,INx)).
  destruct x1 as (((((x1,x2),x3),x4),x5),x6).
  unfold cmdof in EQx.
  simpl in EQx.
  rewrite EQx in *.
  assert (tmp:=INx).
  apply SOBS in tmp.
  destruct tmp as (WF1,(SAT1,REST)).
  apply sat_wait4cond in SAT1.
  destruct SAT1 as (l3,(v1,(eql1,(eqv1,(x3v,(x3l,(lov1,rest))))))).
  rewrite <- H0 in XOF.
  rewrite <- eqv1 in XOF.

  assert (fv1: fold_left phplus (map pof T) (phplus Pinv Pleak) v1 = Some Cond).
  {
  apply fold_cond; try tauto.
  apply pofs.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (Waiting4cond v l1, x2, x3, x4, x5, x6).
  tauto.
  assumption.
  }

  assert (invl: In v1 locs).
  {
  apply LOCs.
  rewrite fv1.
  apply some_none.
  }

  assert (XOF1: xOf (fun x0 : location Z => Lof x0) locs (Aof v1) = Some ([[l1]])).
  {
  rewrite <- lov1.
  apply xOf_same; try assumption.
  apply in_map. assumption.
  apply comp_cons; try tauto.
  unfold comp.
  intros.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  }
  rewrite XOF in XOF1.
  inversion XOF1.

  assert (fl3: fold_left phplus (map pof T) (phplus Pinv Pleak) l3 = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) l3 = Some (Locked wt ot)).
  {
  apply fold_lock_ed; try tauto.
  apply pofs.
  right.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (Waiting4cond v l1, x2, x3, x4, x5, x6).
  tauto.
  assumption.
  }

  rewrite <- H1 in eql1.
  destruct l3 as (((((((x1',x2'),x3'),x4'),x5'),x6'),x7'),x8').
  unfold Aof in eql1.
  unfold Aofo in eql1.
  simpl in eql1.
  rewrite eql1 in *.
  rewrite NONE in fl3.
  destruct fl3 as [CO|CO].
  inversion CO.
  destruct CO as (wt',(ot',CO)).
  inversion CO.
  }

  {
  apply in_map_iff in IN.
  destruct IN as (x1,(EQx,INx)).
  destruct x1 as (((((x1,x2),x3),x4),x5),x6).
  unfold cmdof in EQx.
  simpl in EQx.
  rewrite EQx in *.
  assert (tmp:=INx).
  apply SOBS in tmp.
  destruct tmp as (WF1,(SAT1,REST)).
  apply sat_WasWaiting4cond in SAT1.
  destruct SAT1 as (l3,(v1,(eql1,(eqlv1,(lov1,(x3v,(x3l,(prcl',SAT1')))))))).
  rewrite <- H0 in XOF.
  rewrite <- eqlv1 in XOF.

  assert (fv1: fold_left phplus (map pof T) (phplus Pinv Pleak) v1 = Some Cond).
  {
  apply fold_cond; try tauto.
  apply pofs.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (WasWaiting4cond v l1, x2, x3, x4, x5, x6).
  tauto.
  assumption.
  }

  assert (invl: In v1 locs).
  {
  apply LOCs.
  rewrite fv1.
  apply some_none.
  }

  assert (XOF1: xOf (fun x0 : location Z => Lof x0) locs (Aof v1) = Some ([[l1]])).
  {
  rewrite <- lov1.
  apply xOf_same; try assumption.
  apply in_map. assumption.
  apply comp_cons; try tauto.
  unfold comp.
  intros.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  }
  rewrite XOF in XOF1.
  inversion XOF1.

  assert (fl3: fold_left phplus (map pof T) (phplus Pinv Pleak) l3 = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) l3 = Some (Locked wt ot)).
  {
  apply fold_lock_ed; try tauto.
  apply pofs.
  right.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (WasWaiting4cond v l1, x2, x3, x4, x5, x6).
  tauto.
  assumption.
  }

  rewrite <- H1 in eql1.
  destruct l3 as (((((((x1',x2'),x3'),x4'),x5'),x6'),x7'),x8').
  unfold Aof in eql1.
  unfold Aofo in eql1.
  simpl in eql1.
  rewrite eql1 in *.
  rewrite NONE in fl3.
  destruct fl3 as [CO|CO].
  inversion CO.
  destruct CO as (wt',(ot',CO)).
  inversion CO.
  }
  }

  assert (OTemp: OBs ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) (concat (map Aoof T)) locs = empb).
  {
  unfold OBs.
  unfold filterb.
  unfold empb.
  apply functional_extensionality.
  intros.
  destruct (xOf (fun x0 : location Z => Lof x0) locs x) eqn:XOF.
  unfold Aof.
  unfold Aofo.
  simpl.
  destruct (Z.eq_dec x l).
  reflexivity.
  destruct (Z.eq_dec z l).
  Focus 2.
  reflexivity.
  Focus 2.
  reflexivity.
  rewrite e in XOF.
  apply count_occ_not_In.
  unfold not.
  rewrite <- flat_map_concat_map.
  intros NIN.
  apply in_flat_map in NIN.
  destruct NIN as (x1,(INx,EQ1)).
  destruct x1 as (((((x1',x2'),x3'),x4'),x5'),x6').
  unfold Aoof in EQ1.
  simpl in EQ1.
  apply in_map_iff in EQ1.
  destruct EQ1 as (y,(EQy,INy)).
  rewrite <- EQy in XOF.

  assert (INC: In y (concat (map oof T))).
  {
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists (x1', x2', x3', x4', x5', x6').
  auto.
  }
  apply OBsOK in INC.
  destruct INC as (l',(EQl',pl')).

  apply LOCs in pl'.

  assert (XOF1: xOf (fun x0 : location Z => Lof x0) locs (Aofo y) = Some (Lofo y)).
  {
  apply xOf_sameo; try tauto.
  apply in_map_iff.
  exists l'.
  auto.
  apply comp_conso.
  apply in_map_iff.
  exists l'.
  auto.
  unfold comp.
  intros.
  apply in_map_iff in IN.
  destruct IN as (a1,(EQ1,IN1)).
  rewrite <- EQ1.
  apply in_map_iff in IN0.
  destruct IN0 as (a2,(EQ2,IN2)).
  rewrite <- EQ2.
  apply injo.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  }

  rewrite XOF in XOF1.
  inversion XOF1.
  assert (lcm:=LCOM).
  unfold lcomp in lcm.
  apply lcm in pl'.
  apply in_map_iff in pl'.
  destruct pl' as (x0',(eq1',in1')).
  apply LOCs in in1'.
  destruct x0' as (((((((a1',a2'),a3'),a4'),a5'),a6'),a7'),a8').
  unfold Aof in eq1'.
  unfold Aofo in eq1'.
  unfold Oof in eq1'.
  simpl in eq1'.
  rewrite eq1' in in1'.
  rewrite <- EQl' in H0.
  unfold Lof in in1'.
  rewrite <- H0 in in1'.
  rewrite NONE in in1'.
  contradiction.
  }

  assert (bpupd: boundph (upd (location_eq_dec Z.eq_dec) p (l, r, l, None, false, (0%Z, nil), (0%Z, nil), nil) (Some (Ulock empb empb)))).
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  rewrite EQG.
  rewrite EQG'.
  rewrite EQO.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  apply red_Newlock; try assumption.
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
  unfold upd in CONDv.
  destruct (location_eq_dec Z.eq_dec v (l, r, l, None, false, (0%Z, nil), (0%Z, nil), nil)).
  rewrite e in CONDv.
  unfold upd in *.
  rewrite ULOCK in CONDv.
  inversion CONDv.
  rewrite EQH in CONDv.
  apply SPUR2 in CONDv.
  destruct CONDv as (a,(b,(c,d))).
  exists a, b.
  exists.
  rewrite EQH.
  assumption.
  unfold not.
  intros CO.
  rewrite CO in c.
  rewrite NONE in c.
  destruct c as [c|c].
  inversion c.
  destruct c as (wt',(ot',c)).
  inversion c.
  assumption.
  assumption.
  }

  exists.
  {
  exists. assumption.
  exists. tauto.
  exists.
  unfold updl.
  rewrite map_map.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ,IN)).
  destruct (Z.eq_dec (snd x1) id).
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  split.
  apply phpdef_ulock; try tauto.
  apply phpdef_ulock; try tauto.
  apply PHPD.
  rewrite <- EQ.
  inm_.
  split.
  unfold updl.
  rewrite map_map.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ,IN)).
  destruct (Z.eq_dec (snd x1) id).
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  assumption.
  rewrite <- EQ.
  apply BPE.
  inm_.
  split. tauto.
  split. tauto.
  split. tauto.
  split.
  unfold boundph.
  intros.
  assert (EQ:=H).
  rewrite EQH in H.
  unfold boundph in BPT.
  eapply BPT.
  apply H.
  unfold not.
  intros.
  rewrite H0 in EQ.
  rewrite ULOCK in EQ.
  inversion EQ.

  assert (PH:=PH2H).
  destruct PH as (PH,PH1).
  split.
  intros.
  specialize PH with l0.

  destruct ((location_eq_dec Z.eq_dec) ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil) l0).
  rewrite <- e in *.
  rewrite ULOCK.
  unfold upd.
  rewrite eqz.
  reflexivity.
  rewrite EQH.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) l).
  rewrite e in PH.
  destruct (fold_left phplus (map pof T) (phplus Pinv Pleak) l0) eqn:fl0.
  rewrite FRE in PH.
  destruct k; try inversion PH; try contradiction.
  trivial.
  assumption.
  congruence.
  intros.
  unfold upd.
  destruct (Z.eq_dec z l).
  specialize NONE0 with ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil).
  symmetry in e.
  apply NONE0 in e.
  rewrite ULOCK in e.
  inversion e.
  apply PH1.
  intros.
  rewrite <- EQH.
  apply NONE0.
  assumption.
  unfold not.
  intros.
  rewrite H in EQ.
  unfold Aof in EQ.
  rewrite <- EQ in n.
  contradiction.
  }

  exists.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  assumption.
  exists.
  intros.
  apply upd_updl. exists (Newlock, tx, p, O, C). tauto. assumption.
  exists. assumption.
  exists.
  exists. assumption.
  exists.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) l0 ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil)).
  rewrite e in IN.
  apply AinvOK in IN.
  rewrite NONE in IN.
  destruct IN as (CO,IN).
  inversion CO.
  rewrite EQH.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) l).
  split.
  apply AinvOK.
  assumption.
  reflexivity.
  apply AinvOK.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  rewrite EQWT.
  rewrite EQOT.
  apply INAOK.
  rewrite <- EQH.
  assumption.
  unfold not.
  intros.
  rewrite H in LOCK.
  rewrite ULOCK in LOCK.
  inversion LOCK.
  unfold upd in NOTHELD.
  destruct ((location_eq_dec Z.eq_dec) l0 ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil)).
  rewrite e in LOCK.
  rewrite ULOCK in LOCK.
  inversion LOCK.
  rewrite EQH in LOCK.
  destruct (Z.eq_dec (Aof l0) l).
  destruct l0 as (((((((x1,x2),x3),x4),x5),x6),x7),x8).
  unfold Aof in e.
  unfold Aofo in e.
  simpl in e.
  rewrite e in LOCK.
  rewrite NONE in LOCK.
  inversion LOCK.
  assumption.
  assumption.
  }
  assumption.
  exists.
  {
  exists.
  {
  unfold injph.
  unfold inj.
  intros.
  destruct ((location_eq_dec Z.eq_dec) x1 ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil)).
  destruct ((location_eq_dec Z.eq_dec) x2 ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil)).
  rewrite e, e0.
  reflexivity.
  rewrite EQH in px2.
  destruct x2 as (((((((x1',x2),x3),x4),x5),x6),x7),x8).
  rewrite e in H.
  unfold Aof in H.
  unfold Aofo in H.
  simpl in H.
  inversion H.
  rewrite <- H0 in px2.
  rewrite NONE in px2.
  contradiction.
  assumption.

  destruct ((location_eq_dec Z.eq_dec) x2 ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil)).
  rewrite EQH in px1.
  destruct x1 as (((((((x1,x2'),x3),x4),x5),x6),x7),x8).
  rewrite e in H.
  unfold Aof in H.
  unfold Aofo in H.
  simpl in H.
  inversion H.
  rewrite H0 in px1.
  rewrite NONE in px1.
  contradiction.
  assumption.

  rewrite EQH in px1.
  rewrite EQH in px2.
  apply INJ; try assumption.
  assumption.
  assumption.
  }
  exists.
  {
  unfold lcomp.
  simpl.
  intros.
  destruct IN as [EQ|IN].
  rewrite <- EQ.
  left.
  reflexivity.
  right.
  apply LCOM; assumption.
  }
  exists.
  {
  split.
  intros.
  destruct ((location_eq_dec Z.eq_dec) l0 ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil)).
  rewrite e.
  auto.
  rewrite EQH in H.
  right.
  apply LOCs; assumption.
  assumption.
  intros.
  destruct H as [EQ|IN].
  rewrite <- EQ.
  rewrite ULOCK.
  apply some_none.
  destruct ((location_eq_dec Z.eq_dec) l0 ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil)).
  rewrite e in IN.
  contradiction.
  rewrite EQH.
  apply LOCs.
  assumption.
  assumption.
  }
  intros.
  apply OBsOK in IN.
  destruct IN as (l',(EQl',pl')).
  exists l', EQl'.
  destruct ((location_eq_dec Z.eq_dec) l' ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil)).
  rewrite e.
  rewrite ULOCK.
  apply some_none.
  rewrite EQH.
  assumption.
  assumption.
  }
  exists.
  {
  exists.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) l0 ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil)).
  rewrite e in *.
  exists. trivial.
  exists. trivial.
  exists. trivial.
  unfold upd.
  unfold Aof.
  simpl.
  rewrite eqz.
  intros.
  contradiction.
  rewrite EQH in LOCK.
  replace (upd Z.eq_dec h l (Some 1%Z) (Aof l0)) with (h (Aof l0)).
  apply LOCKOK.
  assumption.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) l).
  destruct l0 as (((((((x1,x2),x3),x4),x5),x6),x7),x8).
  unfold Aof in e.
  unfold Aofo in e.
  simpl in e.
  rewrite e in LOCK.
  rewrite NONE in LOCK.
  destruct LOCK as [CO|CO].
  inversion CO.
  destruct CO as (wt,(ot,CO)).
  destruct CO as [CO|CO].
  inversion CO.
  inversion CO.
  reflexivity.
  assumption.
  }
  split.
  {
  intros.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) l).
  split.
  reflexivity.
  unfold not.
  intros.
  apply OBsOK in H.
  destruct l0 as (((((((x1',x2),x3),x4),x5),x6),x7),x8).
  unfold Aof in e.
  unfold Aofo in e.
  simpl in e.
  rewrite e in H.

  destruct H as (l',(EQl0,pl0)).
  destruct l' as (((((((a1,a2),a3),a4),a5),a6),a7),a8).
  inversion EQl0.
  rewrite H0 in pl0.
  rewrite NONE in pl0.
  contradiction.
  apply ULOCKOK with wt ot.
  rewrite <- EQH.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  }
  intros.
  destruct (Z.eq_dec (Aof l0) l).
  unfold not.
  intros.
  apply OBsOK in H.
  destruct l0 as (((((((x1',x2),x3),x4),x5),x6),x7),x8).
  unfold Aof in e.
  unfold Aofo in e.
  simpl in e.
  rewrite e in H.
  destruct H as (l',(EQl',pl')).
  destruct l' as (((((((a1,a2),a3),a4),a5),a6),a7),a8).
  inversion EQl'.
  rewrite H0 in pl'.
  rewrite NONE in pl'.
  contradiction.
  apply UCONOK.
  rewrite <- EQH.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  }
  
  exists.
  {
  intros.
  rewrite EQWT.
  rewrite EQOT.
  destruct ((location_eq_dec Z.eq_dec) l0 ((l,r,l,None,false),(0%Z,nil),(0%Z,nil),nil)).
  rewrite e in *.
  rewrite WTemp.
  rewrite OTemp.
  rewrite ULOCK in ULOCKED.
  destruct ULOCKED as [U|U];
  inversion U.
  tauto.
  apply WTsOTsOK.
  rewrite <- EQH.
  assumption.
  assumption.
  }

  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x0,(EQ0,IN0)).
  destruct x0 as (x0,id').
  simpl in *.
  destruct (Z.eq_dec id' id).
  {
  (* ==================== id' = id ===========*)
  symmetry in EQ0.
  inversion EQ0.
  exists. trivial.
  exists.
  eapply sat_weak_imp1; try assumption.
  apply sat1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  }
  (* ==================== id' <> id ===========*)
  inversion EQ0.
  rewrite H0 in *.
  assert (IN2:=IN0).
  apply SOBS in IN0.
  destruct IN0 as (WF1,(SAT1,SOBS1')).
  exists. trivial.
  exists.

  assert (bp0: boundph p0).
  {
  apply BPE.
  apply in_map_iff.
  exists (c, tx0, p0, O0, C0, id').
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
  exists (c, tx0, p0, O0, C0, id').
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  apply SAT1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.

  intros.
  apply SOBS1' in W4COND.
  destruct W4COND as (v',(l',(inv',(inl',(eqv',(eql',sobs')))))).
  exists v', l'.
  exists. tauto.
  exists. tauto.
  exists eqv', eql'.
  rewrite EQWT.
  rewrite EQOT.
  assumption.
Qed.


Lemma Acquire0_preserves_validity:
  forall m sp h t id l tx
         (VALIDK: validk (S m) sp t h)
         (CMD : t id = Some (Acquire l, tx))
         (NON: h ([[l]]) <> Some 1%Z),
    validk m sp (upd Z.eq_dec t id (Some (Waiting4lock l, tx))) h.
Proof.
  intros.
  unfold validk in VALIDK.
  destruct VALIDK as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
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
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.

  assert (tmp: exists p O C, In (Acquire l, tx, p, O, C, id) T).
  {
  apply TOK.
  assumption.
  }

  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  destruct WF as (WF1,WF2).
  apply sat_acquire0 in WP.
  destruct WP as (ll,(eqll,(pl,(prcl,SAT1)))).
  exists (updl T id (Waiting4lock l, tx, p, O, C, id)).
  exists invs, locs, Pinv, Pleak, Ainv, Cinv, Cleak.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  subst.

  assert (EQ_1: map pof (updl T id (Waiting4lock l, tx, p, O, C, id)) = map pof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Acquire l, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQ_2: map (fun x => (pof x, snd x)) (updl T id (Waiting4lock l, tx, p, O, C, id)) = map (fun x => (pof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Acquire l, tx, p, O, C)).
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
  assert (EQ_3: map oof (updl T id (Waiting4lock l, tx, p, O, C, id)) = map oof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Acquire l, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  }
  assert (EQ_3': map Aoof (updl T id (Waiting4lock l, tx, p, O, C, id)) = map Aoof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Acquire l, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  }
  assert (EQ_4: map gof (updl T id (Waiting4lock l, tx, p, O, C, id)) = map gof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Acquire l, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  }
  assert (EQ_4': map (fun x => (gof x, snd x)) (updl T id (Waiting4lock l, tx, p, O, C, id)) = map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Acquire l, tx, p, O, C)).
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
  assert (EQF: forall l0, filterb (xOf (fun x  => Lof x) locs) (Aof l0) (fun v => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
  (map cmdof (updl T id (Waiting4lock l, tx, p, O, C, id))))) =
  filterb (xOf (fun x  => Lof x) locs) (Aof l0) (fun v => length (filter (fun c : cmd => 
  ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))).
  {
  symmetry.
  apply filterb_updl_eq.
  intros.
  split.
  simpl.
  destruct ((opZ_eq_dec None (Some v))).
  inversion e.
  reflexivity.
  intros.
  assert (X': x' = (Acquire l, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  simpl.
  destruct ((opZ_eq_dec None (Some v))).
  inversion e.
  reflexivity.
  }

  assert (bp: boundph p).
  {
  apply BPE.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  split. reflexivity. assumption.
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
  exists (Acquire l, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  rewrite EQ_1.
  rewrite EQ_2.
  rewrite EQ_3.
  rewrite EQ_3'.
  rewrite EQ_4.
  rewrite EQ_4'.
  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  apply red_Acquire0.
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
  exists. tauto.
  exists.
  {
  intros.
  apply upd_updl.
  exists (Acquire l, tx, p, O, C).
  auto.
  assumption.
  }
  exists.
  {
  apply NoDup_updl.
  assumption.
  }
  exists.
  split. assumption.
  split. assumption.
  split.
  intros.
  rewrite EQF.
  apply INAOK.
  assumption.
  assumption.
  assumption.
  split. tauto.
  exists. tauto.
  exists.
  intros.
  rewrite EQF.
  apply WTsOTsOK.
  assumption.

  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x00,(EQ,IN)).
  destruct x00 as (((((y1,y2),y3),y4),y5),y6).
  unfold pof in EQ. unfold oof in EQ. unfold gof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec y6 id).
  {
(* ==================== y6 = id ===========*)
  rewrite e in IN.
  symmetry in EQ.
  inversion EQ.
  split. unfold wellformed. simpl. tauto.
  exists.
  eapply sat_weak_imp1; try assumption.
  apply SAT1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  }
(* ==================== z <> id ===========*)
  symmetry in EQ.
  inversion EQ.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF3,(WP3,VOBS3)).
  exists. assumption.
  exists.
  assert (bpy3: boundph y3).
  {
  apply BPE.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  split. reflexivity. assumption.
  }

  assert (bgy5: boundgh y5).
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
  exists (y1, y2, y3, y4, y5, y6).
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  apply WP3.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  assert (tmp:=W4COND).
  apply VOBS3 in tmp.
  destruct tmp as (v',(l',(inv',(inl',(eqv,(eql,sobs1)))))).
  exists v', l', inv', inl', eqv, eql.

  assert (FIL: forall v, length (filter (fun c0 => ifb (opZ_eq_dec (waiting_for_cond c0) (Some v)))
    (map cmdof (updl T id (Waiting4lock l, tx, p, O, C, id)))) =
    length (filter (fun c0 => ifb (opZ_eq_dec (waiting_for_cond c0) (Some v))) (map cmdof T))).
  {
  unfold updl.
  rewrite map_map.
  intros.
  apply filter_map_eq.
  intros.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl.
  destruct (Z.eq_dec x6 id).
  assert (EQX: (x1, x2, x3, x4, x5) = (Acquire l, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply IN0.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQX.
  unfold cmdof.
  reflexivity.
  reflexivity.
  }
  replace ((filterb (xOf (fun x  => Lof x) locs) (Aof l')
     (fun v => length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) (Some v)))
     (map cmdof (updl T id (Waiting4lock l, tx, p, O, C, id))))) ([[ev]])))
  with (filterb (xOf (fun x  => Lof x) locs) (Aof l')
     (fun v => length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) (Some v)))
     (map cmdof T))) ([[ev]])).
  assumption.
  unfold filterb.
  rewrite FIL.
  reflexivity.
Qed.


Lemma Acquire_preserves_validity:
  forall m sp h t id l tx
         (VALIDK: validk (S m) sp t h)
         (CMD : t id = Some (Acquire l, tx))
         (NON: h ([[l]]) = Some 1%Z),
    validk m sp (upd Z.eq_dec t id (Some (tt, tx))) (upd Z.eq_dec h ([[l]]) (Some 0%Z)).
Proof.
  intros.
  unfold validk in VALIDK.
  destruct VALIDK as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
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
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.

  assert (tmp: exists p O C, In (Acquire l, tx, p, O, C, id) T).
  {
  apply TOK.
  assumption.
  }

  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  destruct WF as (WF1,WF2).
  apply sat_acquire in WP.
  destruct WP as (ll,(eqll,(pl,(prcl,SAT1)))).
  rewrite <- eqll in *.

  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (EQFOLD: fold_left phplus (map pof T) (phplus Pinv Pleak) = phplus Pinv (fold_left phplus (map pof T) Pleak)).
  {
  apply fold_left_f_m_def with (def:=phplusdef); repeat php_.
  apply can_phpdef.
  }

  assert (INpT: In p (map pof T)).
  {
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  }

  assert (ghpdefg0il: forall g, In g (map gof T) -> ghplusdef g (ghplus Cinv Cleak)).
  {
  intros.
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  }

  assert (bcil: boundgh (ghplus Cinv Cleak)).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  right. reflexivity.
  }

  assert (bci: boundgh Cinv).
  {
  apply boundgh_mon with Cleak.
  assumption.
  }

  assert (bcl: boundgh Cleak).
  {
  apply boundgh_mon with Cinv.
  rewrite ghplus_comm; repeat php_.
  }

  assert (phpdefp0pil: forall p0, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  apply phpdef_pair.
  assumption.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  }

  assert (LOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some Lock).
  {
  assert (tmp: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some Lock \/
    (exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) ll =
    Some (Locked wt ot))).
  {
  apply fold_lock_ed.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  right.
  exists p, INpT.
  assumption.
  }

  destruct tmp as [LK|LKED].
  assumption.
  destruct LKED as (wt,(ot,LKED)).
  assert (CO:=PH2H).
  destruct CO as (CO1,CO2).
  specialize CO1 with ll.
  rewrite LKED in CO1.
  rewrite NON in CO1.
  inversion CO1.
  }

  destruct pl as [pl|pl].
  Focus 2.
  destruct pl as (WT',(OT',pl)).
  assert (CO: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked WT' OT')).
  {
  apply fold_locked; repeat php_.
  apply pofs.
  right.
  exists p, INpT.
  assumption.
  }
  rewrite CO in LOCKED.
  inversion LOCKED.
  assert (tmp: Lof ll = Aof ll /\ Pof ll = false /\ Xof ll = None /\
   (h (Aof ll) <> Some 1%Z -> In (Oof ll) (concat (map oof T)))).
  {
  apply LOCKOK.
  left.
  assumption.
  }
  destruct tmp as (lll,(plf,(ninrlxll,inlt))).

  assert (PERM: Permutation Ainv (((subsas (snd (Iof ll)) (invs (fst (Iof ll)) 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))))), ll)
     :: filter (fun x => negb (ifb ((location_eq_dec Z.eq_dec) (snd x) ll))) Ainv)).
  {
  apply perm_filter.
  assumption.
  apply INAOK.
  assumption.
  assumption.
  unfold negb.
  simpl.
  destruct ((location_eq_dec Z.eq_dec) ll ll).
  reflexivity.
  contradiction.
  intros.
  unfold negb.
  simpl.
  destruct ((location_eq_dec Z.eq_dec) z' ll).
  contradiction.
  reflexivity.
  }

  assert (SATA2: sat Pinv None Cinv (fold_left Astar (map fst 
    (((subsas (snd (Iof ll)) (invs (fst (Iof ll)) 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))))), ll)
     :: filter (fun x => negb (ifb ((location_eq_dec Z.eq_dec) (snd x) ll))) Ainv))(Abool true))).
  {
  apply sat_perm with (map fst Ainv).
  apply Permutation_map.
  assumption.
  assumption.
  assumption.
  assumption.
  }

  simpl in SATA2.
  assert (SATA3: sat Pinv None Cinv 
    (Astar (subsas (snd (Iof ll)) (invs (fst (Iof ll)) 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))
    (fold_left Astar (map fst 
    (filter (fun x => negb (ifb ((location_eq_dec Z.eq_dec) (snd x) ll))) Ainv))
    (Abool true)))).
  {
  apply fold_left_g_can2.
  unfold cang.
  split.
  intros.
  apply sat_comm.
  assumption.
  simpl.
  intros.
  apply sat_perm with (l:=l0); assumption.
  assumption.
  }
  simpl in SATA3.
  destruct SATA3 as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(bc1,(bc2,(bc1c2,(opo1o2,(SATp1,(SATp2,(p1p2,C1C2)))))))))))))))))).
  assert (tmp: O1 = None /\ O2 = None).
  {
  inversion opo1o2.
  split; reflexivity.
  }
  destruct tmp as (o1n,o2n).
  rewrite o1n, o2n in *.
  subst.

  assert (phpdeff: phplusdef (fold_left phplus (map pof T) Pleak) (phplus p1 p2)).
  {
  apply phpdef_fold; repeat php_.
  intros.
  apply PHPD.
  assumption.
  intros.
  apply PHPD.
  assumption.
  }

  assert (PHPDpp1: phplusdef p p1).
  {
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply phpdef_comm.
  apply PHPD.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  apply phpdef_comm.
  assumption.
  }
  assert (PHPDpp2: phplusdef p p2).
  {
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply phpdef_comm.
  apply PHPD.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  }

  assert (p12ll: phplus (phplus p1 p2) Pleak ll = Some Lock \/ phplus (phplus p1 p2) Pleak ll = None).
  {
  apply or_comm.
  apply locked_fold_phtoheap with (m:=pof) (l:=T) (id:=id) (p:=p) (b:=phplus (phplus p1 p2) Pleak) (h:=h); repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  right.
  reflexivity.
  }

  assert (p12l: phplus p1 p2 ll = Some Lock \/ phplus p1 p2 ll = None).
  {
  apply phplus_lock_none with Pleak.
  assumption.
  }

  assert (p1l: p1 ll = Some Lock \/ p1 ll = None).
  {
  apply phplus_lock_none with p2.
  assumption.
  }

  assert (p2l: p2 ll = Some Lock \/ p2 ll = None).
  {
  apply phplus_lock_none with p1.
  rewrite phplus_comm; repeat php_.
  }

  assert (pll: Pleak ll = Some Lock \/ Pleak ll = None).
  {
  apply phplus_lock_none with (phplus p1 p2).
  rewrite phplus_comm; repeat php_.
  }

  assert (p0l: forall p0 (IN: In p0 (map pof T)), p0 ll = Some Lock \/ p0 ll = None).
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  rewrite <- EQ.
  destruct (Z.eq_dec x6 id).
  rewrite e in IN.
  assert (EQX: (x1, x2, x3, x4, x5) = (Acquire l, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN.
  assumption.
  assumption.
  inversion EQX.
  left.
  assumption.
  rewrite EQ in *.
  assert (PHPDp0: phplusdef p p0).
  {
  apply DEFL with id x6.
  omega.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  rewrite EQ.
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
  assert (CO:=PH2H).
  destruct CO as (CO,CO1).
  unfold phtoh in CO.
  specialize CO with ll.
  rewrite NON in CO.
  erewrite fold_locked in CO; repeat php_.
  inversion CO.
  apply pofs.
  right.
  exists p0.
  exists.
  apply in_map_iff.
  exists (x1, x2, p0, x4, x5, x6).
  auto.
  apply p0l.
  right.
  reflexivity.
  }
  assert (PHPDUp1: forall wt ot, phplusdef (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt ot))) p1).
  {
  intros.
  apply phpdef_upd_locked.
  assumption.
  assumption.
  }
  assert (PHPDUp2: forall wt ot, phplusdef (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt ot))) p2).
  {
  intros.
  apply phpdef_upd_locked.
  assumption.
  assumption.
  }
  assert (EQP: phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1 = 
    upd (location_eq_dec Z.eq_dec) (phplus p p1) ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))).
  {
  apply phplus_upd.
  unfold not.
  intros.
  destruct H as (v,(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
  }

  exists (updl T id (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, (Oof ll)::O, ghplus C C1, id)).
  exists invs, locs, p2, Pleak.
  exists (filter (fun x => negb (ifb ((location_eq_dec Z.eq_dec) (snd x) ll))) Ainv).
  exists C2, Cleak.

  assert (EQWT: forall l0 p O C, filterb (xOf (fun x  => Lof x) locs) (Aof l0) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) =
    filterb (xOf (fun x  => Lof x) locs) (Aof l0) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof
    (updl T id (tt, tx, p, O, C, id)))))).
  {
  intros.
  apply filterb_updl_eq.
  intros.
  split.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some v)).
  inversion e.
  reflexivity.
  intros.
  assert (X': x' = (Acquire l, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some v)).
  inversion e.
  reflexivity.
  }
  assert (EQOT: forall l0 c p C, filterb (xOf (fun x  => Lof x) locs) (Aof l0) (count_occ Z.eq_dec (concat (map Aoof T))) =
    filterb (xOf (fun x  => Lof x) locs) (Aof l0) (count_occ Z.eq_dec (concat (map Aoof (updl T id
    (c, tx, p, Oof ll :: O, C, id)))))).
  {
  intros.
  apply filterb_updl_obs_eq.
  intros.
  assert (X': x' = (Acquire l, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold Aoof.
  unfold Oof.
  simpl.
  destruct (Z.eq_dec (Aofo (fst (fst (fst ll)))) v).
  rewrite <- e in *.
  assert (XOF: xOf (fun x  => Lof x) locs (Aofo (fst (fst (fst ll)))) = Some (Lof ll)).
  {
  apply xOf_same.
  apply in_map.
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  apply comp_cons.
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  unfold comp.
  intros.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  }
  rewrite IN in XOF.
  inversion XOF.
  rewrite lll in *.
  rewrite H0 in NEQ.
  unfold Aof in *.
  unfold Aofo in *.
  unfold Oof in *.
  contradiction.
  reflexivity.
  }

  assert (ghpdefc1lc2l: ghplusdef C1 Cleak /\ ghplusdef C2 Cleak). repeat php_.

  assert (ghpdefxc1xc2l: forall x : gheap, In x (map gof T) -> 
    ghplusdef x C1 /\ ghplusdef x (ghplus C2 Cleak)).
  {
  intros.
  apply GHPD in H.
  assert (tmp: ghplusdef x C1 /\ ghplusdef x C2). repeat php_.
  split.
  repeat php_.
  repeat php_.
  }

  assert (EQCT: fold_left ghplus (map gof (updl T id (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll::O, ghplus C C1, id)))
    (ghplus C2 Cleak) = fold_left ghplus (map gof T) ((ghplus (ghplus C1 C2) Cleak))).
  {
  rewrite <- fold_left_move_m_eq2 with (def:=ghplusdef) (x1:=C) (x2:=C1); repeat php_.
  rewrite ghplus_assoc; repeat php_.
  rewrite <- fold_left_f_m_def with (def:=ghplusdef); repeat php_.
  apply can_ghpdef.
  apply can_ghpdef.
  apply ghpdefxc1xc2l.
  apply ghpdefxc1xc2l.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id). auto.
  }

  assert (p0ln: forall p0, In p0 (map pof T) \/ p0 = phplus p1 p2 -> p0 ll = None \/ p0 ll = Some Lock).
  {
  intros.
  destruct H as [IN|IN].
  apply or_comm.
  apply p0l.
  assumption.
  rewrite IN.
  unfold phplus.
  destruct p1l as [p1l|p1l].
  rewrite p1l.
  destruct p2l as [p2l|p2l].
  rewrite p2l.
  right.
  reflexivity.
  rewrite p2l.
  right.
  reflexivity.
  rewrite p1l.
  destruct p2l as [p2l|p2l].
  rewrite p2l.
  right.
  reflexivity.
  rewrite p2l.
  left.
  reflexivity.
  }

  assert (phpdefp1lp2l: phplusdef p1 Pleak /\ phplusdef p2 Pleak). repeat php_.
  assert (phpdefp01p02l: forall p0, In p0 (map pof T) -> phplusdef p0 p1 /\ phplusdef p0 p2 /\ phplusdef p0 Pleak).
  {
  intros.
  apply PHPD in H.
  assert (tmp: phplusdef p0 p1 /\ phplusdef p0 p2). repeat php_.
  split;
  repeat php_.
  split;
  repeat php_.
  }

  assert (ghpdefp01p02l: forall p0, In p0 (map gof T) -> ghplusdef p0 C1 /\ 
    ghplusdef p0 C2 /\ ghplusdef p0 Cleak).
  {
  intros.
  apply GHPD in H.
  assert (tmp: ghplusdef p0 C1 /\ ghplusdef p0 C2). repeat php_.
  split;
  repeat php_.
  split;
  repeat php_.
  }

  assert (p0ln': forall p0, In p0 (map pof T) \/ p0 = phplus p1 (phplus p2 Pleak) -> p0 ll = None \/ p0 ll = Some Lock).
  {
  intros.
  apply locked_fold_phtoheap with (m:=pof) (l:=T) (id:=id) (p:=p) (b:=phplus (phplus p1 p2) Pleak) (h:=h); repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  rewrite phplus_assoc; repeat php_.
  }

  assert (EQH0: forall l0 (NEQ: ll <> l0),
    fold_left phplus (map pof T) (phplus p1 p2) l0 =
    fold_left phplus (map pof (updl T id
    (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll :: O, ghplus C C1, id))) p2 l0).
  {
  symmetry.
  apply eq_heap_Acquire with (z:=ll) (p:=p); repeat php_.
  apply pofs.
  apply PHPD.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  eexists.
  eexists.
  reflexivity.
  }

  assert (EQH: forall l0 (NEQ: ll <> l0),
    fold_left phplus (map pof T) (phplus (phplus p1 p2) Pleak) l0 =
    fold_left phplus (map pof (updl T id
    (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll :: O, ghplus C C1, id))) (phplus p2 Pleak) l0).
  {
  rewrite phplus_assoc; repeat php_.
  symmetry.
  apply eq_heap_Acquire with (z:=ll) (p:=p); repeat php_.
  apply pofs.
  intros.
  apply phpdefp01p02l in IN.
  repeat php_.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  eexists.
  eexists.
  reflexivity.
  }

  assert (LOCKEDU: fold_left phplus (map pof (updl T id
    (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll :: O, ghplus C C1, id))) (phplus p2 Pleak) ll = 
    Some (Locked (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))))).
  {
  apply locked_Acquire with p p1; repeat php_.
  apply pofs.
  intros.
  apply phpdefp01p02l in IN.
  repeat php_.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  }

  assert (INl01: forall l0 (IN: In l0 (concat (map oof T))),
    In l0 (concat (map oof (updl T id (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll::O, ghplus C C1, id))))).
  {
  intros.
  rewrite <- flat_map_concat_map in IN.
  apply in_flat_map in IN.
  destruct IN as (x,(INx,INl0)).
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (Acquire l, tx, p, O, C)).
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  inversion EQX.
  exists (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll :: O, ghplus C C1, id).
  split.
  apply in_updl_eq.
  exists (Acquire l, tx, p, O, C).
  auto.
  unfold oof.
  simpl.
  right.
  rewrite <- H3.
  assumption.
  exists (x1, x2, x3, x4, x5, x6).
  split.
  apply in_updl_neq.
  omega.
  assumption.
  assumption.
  }

  assert (INl02: forall o0 (NEQ: Oof ll <> o0) (IN: In o0 (concat (map oof (updl T id (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll::O, ghplus C C1, id))))),
    In o0 (concat (map oof T))).
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
  unfold oof in INl0.
  simpl in INl0.
  assert (EQX: (x1, x2, x3, x4, x5) = (Acquire l, tx, p, O, C)).
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  inversion EQX.
  destruct INl0 as [CO|INl0].
  contradiction.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }

  assert (inc: In C (map gof T)).
  {
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  }

  assert (ghpdefCC1: ghplusdef C C1).
  {
  apply ghpdef_comm.
  apply ghpdef_assoc_mon with C2.
  repeat php_.
  apply ghpdef_comm.
  rewrite ghplus_comm.
  apply GHPD.
  assumption.
  repeat php_.
  }

  assert (incid: In (C, id) (map (fun x => (gof x, snd x)) T)).
  {
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  }

  assert (ghpdefCC12: ghplusdef C (ghplus C1 C2)).
  {
  apply GHPD.
  assumption.
  }

  assert (ghpdefCC2: ghplusdef C C2).
  {
  apply ghpdef_comm.
  apply ghpdef_assoc_mon with C1; repeat php_.
  }

  assert (ghpdefCCl: ghplusdef C Cleak).
  {
  apply GHPD.
  assumption.
  }

  assert (ghpdefC2Cl: ghplusdef C2 Cleak).
  {
  apply ghpdef_assoc_mon with C1; repeat php_.
  }

  assert (bp: boundph p).
  {
  apply BPE.
  assumption.
  }

  assert (phpdefppl: phplusdef p Pleak).
  {
  apply PHPD.
  assumption.
  }

  assert (bp12plp: boundph (phplus (phplus (phplus p1 p2) Pleak) p)).
  {
  apply boundph_fold with (m:=pof) (l:=T); repeat php_.
  }

  assert (bp12p: boundph (phplus (phplus p1 p2) p)).
  {
  apply boundph_mon with Pleak; repeat php_.
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_assoc in bp12plp; repeat php_.
  replace (phplus p Pleak) with (phplus Pleak p); repeat php_.
  }

  assert (bpp1: boundph (phplus p p1)).
  {
  apply boundph_mon with p2; repeat php_.
  rewrite phplus_assoc; repeat php_.
  }

  assert (phpdefupp1: phplusdef (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll)
    (fun v : Z => length (filter (fun c : cmd =>
    ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
   (map cmdof T)))) (filterb (xOf (fun x  => Lof x) locs) (Aof ll)
   (count_occ Z.eq_dec (concat (map Aoof T))))))) p1).
  {
  apply phpdef_locked'; repeat php_.
  }

  assert (phpdefuppl: phplusdef Pleak (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll)
    (fun v : Z => length (filter (fun c : cmd =>
    ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
   (map cmdof T)))) (filterb (xOf (fun x  => Lof x) locs) (Aof ll)
   (count_occ Z.eq_dec (concat (map Aoof T)))))))).
  {
  apply phpdef_comm.
  apply phpdef_locked'; repeat php_.
  }

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (bupd: boundph (phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked
    (filterb (xOf (fun x : location Z => Lof x) locs) (Aof ll) (fun v : Z =>
    length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) (Some v)))
    (map cmdof T)))) (filterb (xOf (fun x : location Z => Lof x) locs) (Aof ll)
    (count_occ Z.eq_dec (concat (map Aoof T))))))) p1)).
  {
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1,(v2,(CO,rest))).
  inversion CO.
  }

  rewrite EQCT.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  rewrite eqll.
  apply red_Acquire.
  assumption.
  rewrite <- eqll.
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
  rewrite <- EQH in CONDv.
  apply SPUR2 in CONDv.
  destruct CONDv as (a,(b,(c,d))).
  exists a, b.
  exists.
  destruct (location_eq_dec Z.eq_dec ll a).
  right.
  eexists.
  eexists.
  rewrite <- e.
  rewrite LOCKEDU.
  reflexivity.
  rewrite <- EQH.
  assumption.
  assumption.
  assumption.
  unfold not.
  intros CO.
  rewrite <- CO in CONDv.
  rewrite LOCKEDU in CONDv.
  inversion CONDv.
  }

  exists.
  {
  split.
  {
  apply defl_Acquire with (p:=p) (p1:=p1) (p2:=p2) (z:=ll); repeat php_.
  apply pofs.
  apply PHPD.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  eexists.
  eexists.
  reflexivity.
  }
  exists. repeat php_.
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
  apply phpdef_comm.
  apply phpdef_pair.
  apply PHPDUp1.
  apply phpdef_comm.
  apply PHPDUp2.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  apply phpdef_pair.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2; repeat php_.
  simpl in EQ.
  rewrite EQ in IN.
  assert (G: In p0 (map pof T)).
  {
  apply in_map_iff.
  exists (x1, x2, p0, x4, x5, x6).
  auto.
  }
  apply phpdefp01p02l in G.
  split; repeat php_.
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
  rewrite EQP.
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  simpl in EQ.
  rewrite EQ in IN.
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, p0, x4, x5, x6).
  auto.
  }
  exists. assumption.
  exists. assumption.
  exists.

  assert (bp2l: boundph (phplus p2 Pleak)).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_mon with p1; repeat php_.
  rewrite phplus_assoc; repeat php_.
  replace (phplus p2 p1) with (phplus p1 p2); repeat php_.
  }

  assumption.
  split.
  {
  apply boundph_Acquire with (p:=p) (p1:=p1) (z:=ll); repeat php_.
  apply pofs.
  intros.
  apply phpdefp01p02l in IN.
  repeat php_.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  eexists.
  eexists.
  reflexivity.
  left.
  assumption.
  rewrite <- phplus_assoc; repeat php_.
  }
  unfold phtoh in *.
  destruct PH2H as (PH1,PH2).
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  {
  rewrite <- e in *.
  rewrite LOCKEDU.
  unfold upd.
  rewrite eqz.
  reflexivity.
  }
  rewrite <- EQH.
  specialize PH1 with l0.
  destruct (fold_left phplus (map pof T) (phplus (phplus p1 p2) Pleak) l0) eqn:fl0.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  assert (CO: ll = l0).
  {
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite fl0.
  apply some_none.
  symmetry.
  assumption.
  }
  contradiction.
  assumption.
  trivial.
  assumption.
  }
  intros.
  unfold upd.
  destruct (Z.eq_dec z (Aof ll)).
  symmetry in e.
  apply NONE in e.
  rewrite LOCKEDU in e.
  inversion e.
  apply PH2.
  intros.
  rewrite EQH.
  apply NONE.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  omega.
  }
  exists.
  {
  split.
  {
  unfold defl.
  unfold updl.
  rewrite map_map.
  unfold gof.
  simpl.
  intros.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  apply in_map_iff in IN2.
  destruct IN2 as (x2,(EQ2,IN2)).
  destruct (Z.eq_dec (snd x1) id).
  simpl in EQ1.
  inversion EQ1.
  destruct (Z.eq_dec (snd x2) id).
  simpl in EQ2.
  inversion EQ2.
  omega.
  inversion EQ2.
  apply ghpdef_pair'; repeat php_.

  apply DEFLg with id (snd x2).
  omega.
  assumption.
  apply in_map_iff.
  exists x2.
  auto.
  assert (G: In (snd (fst x2)) (map gof T)).
  {
  apply in_map_iff.
  exists x2.
  auto.
  }
  apply ghpdefp01p02l in G.
  repeat php_.

  inversion EQ1.
  destruct (Z.eq_dec (snd x2) id).
  simpl in EQ2.
  inversion EQ2.

  assert (G: In (snd (fst x1)) (map gof T)).
  {
  apply in_map_iff.
  exists x1.
  auto.
  }
  apply ghpdefp01p02l in G.
  apply ghpdef_pair; repeat php_.
  apply DEFLg with (snd x1) id.
  omega.
  apply in_map_iff.
  exists x1.
  auto.
  assumption.
  inversion EQ2.
  apply DEFLg with (snd x1) (snd x2).
  omega.
  apply in_map_iff.
  exists x1.
  auto.
  apply in_map_iff.
  exists x2.
  auto.
  }
  split.
  {
  unfold updl.
  rewrite map_map.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  unfold gof in EQ1.
  simpl in EQ1.
  inversion EQ1.

  split; repeat php_.
  inversion EQ1.
  assert (G: In (gof x1) (map gof T)).
  {
  apply in_map_iff.
  exists x1.
  auto.
  }
  apply ghpdefp01p02l in G.
  split; repeat php_.
  }
  split; assumption.
  }
  exists.
  {
  intros.
  apply upd_updl.
  exists (Acquire l, tx, p, O, C).
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
  split.
  {
  erewrite map_filter with (f3:= fun x => (if if (location_eq_dec Z.eq_dec) x ll then true else false then false else true)).
  apply nodup_filter.
  assumption.
  intros.
  reflexivity.
  }
  split.
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  apply filter_In in IN.
  destruct IN as (EQ1,EQ2).
  unfold negb in EQ2.
  unfold ifb in EQ2.
  destruct ((location_eq_dec Z.eq_dec) (snd x) ll).
  inversion EQ2.
  assert (G: fold_left phplus (map pof T) (phplus (phplus p1 p2) Pleak) l0 =
         Some Lock /\ h (Aof l0) = Some 1%Z).
  {
  apply AinvOK.
  apply in_map_iff.
  exists x.
  auto.
  }
  destruct G as (G1,G2).
  rewrite <- EQH.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  exfalso.
  apply n.
  rewrite EQ.
  apply INJ.
  rewrite G1.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  assumption.
  split; assumption.
  unfold not.
  intros.
  rewrite H in n.
  rewrite EQ in n.
  contradiction.
  }
  split.
  {
  unfold upd.
  intros.
  rewrite <- EQWT.
  rewrite <- EQOT.  
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  inversion NOTHELD.
  apply filter_In.
  split.
  apply INAOK.
  rewrite EQH.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  assumption.
  simpl.
  destruct ((location_eq_dec Z.eq_dec) l0 ll).
  rewrite e in n.
  contradiction.
  reflexivity.
  }
  assumption.
  }
  exists.
  {
  split.
  {
  unfold injph.
  intros.
  apply INJ.
  destruct ((location_eq_dec Z.eq_dec) ll x1).
  rewrite <- e in *.
  rewrite LOCKED.
  apply some_none.
  rewrite EQH.
  assumption.
  assumption.
  destruct ((location_eq_dec Z.eq_dec) ll x2).
  rewrite <- e in *.
  rewrite LOCKED.
  apply some_none.
  rewrite EQH.
  assumption.
  assumption.
  }
  split. assumption.
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  split.
  intros.
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  intros.
  rewrite LOCKEDU.
  apply some_none.
  rewrite <- EQH.
  apply LOCs.
  assumption.
  }
  intros.
  destruct ((olocation_eq_dec Z.eq_dec) (Oof ll) o).
  rewrite <- e in *.
  exists ll.
  exists.
  reflexivity.
  rewrite LOCKEDU.
  apply some_none.
  apply INl02 in IN.
  apply OBsOK in IN.
  destruct IN as (l',(EQl',pl')).
  exists l', EQl'.
  rewrite <- EQH.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  rewrite <- EQl' in n.
  contradiction.
  assumption.
  }
  exists.
  {
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  unfold upd.
  rewrite eqz.
  split. assumption.
  split. assumption.
  split. assumption.
  intros.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll :: O, ghplus C C1, id).
  split.
  apply in_updl_eq.
  exists (Acquire l, tx, p, O, C).
  auto.
  unfold oof.
  simpl.
  left.
  reflexivity.
  rewrite <- EQH in LOCK.
  assert (tmp1:=LOCK).
  apply LOCKOK in LOCK.
  destruct LOCK as (L1,(L2,(L3,L4))).
  split. assumption.
  split. assumption.
  split. assumption.
  unfold upd.
  intros.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  exfalso.
  apply n.
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  destruct tmp1 as [tmp1|tmp1].
  rewrite tmp1.
  apply some_none.
  destruct tmp1 as (wt1,(ot1,tmp1)).
  destruct tmp1 as [tmp1|tmp1].
  rewrite tmp1.
  apply some_none.
  rewrite tmp1.
  apply some_none.
  symmetry.
  assumption.
  apply L4 in H.
  apply INl01.
  assumption.
  assumption.
  }
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  rewrite LOCKEDU in *.
  inversion ULOCK.
  rewrite <- EQH in ULOCK.
  assert (tmp1:=ULOCK).
  apply ULOCKOK in ULOCK.
  destruct ULOCK as (U1,U2).
  split.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  exfalso.
  apply n.
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite tmp1.
  apply some_none.
  symmetry. assumption.
  assumption.
  unfold not.
  intros.
  apply U2.
  apply INl02.
  unfold not.
  intros.
  assert (CO: ll = l0).
  {
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite tmp1.
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
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  rewrite LOCKEDU in *.
  inversion UCOND.
  rewrite <- EQH in UCOND.
  assert (tmp1:=UCOND).
  apply UCONDOK in UCOND.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  exfalso.
  apply n.
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite tmp1.
  apply some_none.
  symmetry. assumption.
  unfold not.
  intros.
  apply UCOND.
  apply INl02; try assumption.
  unfold Aof in n0.
  unfold not.
  intros.
  rewrite H0 in n0.
  contradiction.
  assumption.
  }
  exists.
  {
  intros.
  rewrite <- EQOT.
  rewrite <- EQWT.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  rewrite LOCKEDU in *.
  destruct ULOCKED as [U1|U2].
  {
  inversion U1.
  split; reflexivity.
  }
  inversion U2.
  rewrite <- EQH in ULOCKED.
  apply WTsOTsOK.
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
  {
  simpl in EQ.
(* ==================== x6 = id ===========*)
  symmetry in EQ.
  inversion EQ.
  exists.
  unfold wellformed.
  simpl. tauto.
  split.

  assert (bp1pp2: boundph (phplus (phplus p1 p) p2)).
  {
  rewrite phplus_comm; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  replace (phplus p2 p1) with (phplus p1 p2); repeat php_.
  }

  assert (bgcc12l: boundgh (ghplus (ghplus (ghplus C1 C2) Cleak) C)).
  {
  apply boundgh_fold with (m:=gof) (l:=T); repeat php_.
  }

  assert (bgc12c: boundgh (ghplus (ghplus C1 C2) C)).
  {
  apply boundgh_mon with Cleak.
  rewrite ghplus_assoc; repeat php_.
  rewrite ghplus_assoc in bgcc12l; repeat php_.
  replace (ghplus C Cleak) with (ghplus Cleak C); repeat php_.
  }

  assert (bgc1c: boundgh (ghplus C1 C)).
  {
  rewrite ghplus_comm; repeat php_.
  apply boundgh_mon with C2.
  rewrite ghplus_assoc; repeat php_.
  }
  eapply sat_weak_imp1; try assumption.
  repeat php_.
  apply SAT1; repeat php_.
  apply p0l.
  assumption.
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
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=(ghplus (ghplus C1 C2) Cleak)); repeat php_.
  intros.
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

  destruct WP3 as (l',(v',(eql',(eqv',(pv0',(pl0',(lvl0',(prcl0',(prcv0',SAT0'))))))))).

  apply VOBS3 in W4COND.
  destruct W4COND as (v0,(l0,(inv0,(inl0,(eqv0,(eql0,sob1)))))).
  exists v0, l0, inv0, inl0, eqv0, eql0.
  rewrite <- EQOT.
  rewrite <- EQWT.
  assumption.
Qed.


Lemma Waiting4lock_preserves_validity:
  forall m sp h t id l tx
         (VALIDK: validk (S m) sp t h)
         (CMD : t id = Some (Waiting4lock l, tx))
         (NON: h ([[l]]) = Some 1%Z),
    validk m sp (upd Z.eq_dec t id (Some (tt, tx))) (upd Z.eq_dec h ([[l]]) (Some 0%Z)).
Proof.
  intros.
  unfold validk in VALIDK.
  destruct VALIDK as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
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
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.

  assert (tmp: exists p O C, In (Waiting4lock l, tx, p, O, C, id) T).
  {
  apply TOK.
  assumption.
  }

  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  destruct WF as (WF1,WF2).
  apply sat_wait4lock in WP.

  destruct WP as (ll,(eqll,(pl,(prcl,SAT1)))).
  rewrite <- eqll in *.

  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (EQFOLD: fold_left phplus (map pof T) (phplus Pinv Pleak) = phplus Pinv (fold_left phplus (map pof T) Pleak)).
  {
  apply fold_left_f_m_def with (def:=phplusdef); repeat php_.
  apply can_phpdef.
  }

  assert (INpT: In p (map pof T)).
  {
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  }

  assert (ghpdefg0il: forall g, In g (map gof T) -> ghplusdef g (ghplus Cinv Cleak)).
  {
  intros.
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  }

  assert (bcil: boundgh (ghplus Cinv Cleak)).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  right. reflexivity.
  }

  assert (bci: boundgh Cinv).
  {
  apply boundgh_mon with Cleak.
  assumption.
  }

  assert (bcl: boundgh Cleak).
  {
  apply boundgh_mon with Cinv.
  rewrite ghplus_comm; repeat php_.
  }

  assert (phpdefp0pil: forall p0, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  apply phpdef_pair.
  assumption.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  }

  assert (LOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some Lock).
  {
  assert (tmp: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some Lock \/
    (exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) ll =
    Some (Locked wt ot))).
  {
  apply fold_lock_ed.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  right.
  exists p, INpT.
  assumption.
  }

  destruct tmp as [LK|LKED].
  assumption.
  destruct LKED as (wt,(ot,LKED)).
  assert (CO:=PH2H).
  destruct CO as (CO1,CO2).
  specialize CO1 with ll.
  rewrite LKED in CO1.
  rewrite NON in CO1.
  inversion CO1.
  }

  destruct pl as [pl|pl].
  Focus 2.
  destruct pl as (WT',(OT',pl)).
  assert (CO: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked WT' OT')).
  {
  apply fold_locked; repeat php_.
  apply pofs.
  right.
  exists p, INpT.
  assumption.
  }
  rewrite CO in LOCKED.
  inversion LOCKED.

  assert (tmp: Lof ll = Aof ll /\ Pof ll = false /\ Xof ll = None /\
   (h (Aof ll) <> Some 1%Z -> In (Oof ll) (concat (map oof T)))).
  {
  apply LOCKOK.
  left.
  assumption.
  }
  destruct tmp as (lll,(plf,(ninrlxll,inlt))).

  assert (PERM: Permutation Ainv (((subsas (snd (Iof ll)) (invs (fst (Iof ll)) 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))))), ll)
     :: filter (fun x => negb (ifb ((location_eq_dec Z.eq_dec) (snd x) ll))) Ainv)).
  {
  apply perm_filter.
  assumption.
  apply INAOK.
  assumption.
  assumption.
  unfold negb.
  simpl.
  destruct ((location_eq_dec Z.eq_dec) ll ll).
  reflexivity.
  contradiction.
  intros.
  unfold negb.
  simpl.
  destruct ((location_eq_dec Z.eq_dec) z' ll).
  contradiction.
  reflexivity.
  }

  assert (SATA2: sat Pinv None Cinv (fold_left Astar (map fst 
    (((subsas (snd (Iof ll)) (invs (fst (Iof ll)) 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))))), ll)
     :: filter (fun x => negb (ifb ((location_eq_dec Z.eq_dec) (snd x) ll))) Ainv))(Abool true))).
  {
  apply sat_perm with (map fst Ainv).
  apply Permutation_map.
  assumption.
  assumption.
  assumption.
  assumption.
  }

  simpl in SATA2.
  assert (SATA3: sat Pinv None Cinv 
    (Astar (subsas (snd (Iof ll)) (invs (fst (Iof ll)) 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))
    (fold_left Astar (map fst 
    (filter (fun x => negb (ifb ((location_eq_dec Z.eq_dec) (snd x) ll))) Ainv))
    (Abool true)))).
  {
  apply fold_left_g_can2.
  unfold cang.
  split.
  intros.
  apply sat_comm.
  assumption.
  simpl.
  intros.
  apply sat_perm with (l:=l0); assumption.
  assumption.
  }
  simpl in SATA3.
  destruct SATA3 as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(bc1,(bc2,(bc1c2,(opo1o2,(SATp1,(SATp2,(p1p2,C1C2)))))))))))))))))).
  assert (tmp: O1 = None /\ O2 = None).
  {
  inversion opo1o2.
  split; reflexivity.
  }
  destruct tmp as (o1n,o2n).
  rewrite o1n, o2n in *.
  subst.

  assert (phpdeff: phplusdef (fold_left phplus (map pof T) Pleak) (phplus p1 p2)).
  {
  apply phpdef_fold; repeat php_.
  intros.
  apply PHPD.
  assumption.
  intros.
  apply PHPD.
  assumption.
  }

  assert (PHPDpp1: phplusdef p p1).
  {
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply phpdef_comm.
  apply PHPD.
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  apply phpdef_comm.
  assumption.
  }
  assert (PHPDpp2: phplusdef p p2).
  {
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply phpdef_comm.
  apply PHPD.
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  }

  assert (p12ll: phplus (phplus p1 p2) Pleak ll = Some Lock \/ phplus (phplus p1 p2) Pleak ll = None).
  {
  apply or_comm.
  apply locked_fold_phtoheap with (m:=pof) (l:=T) (id:=id) (p:=p) (b:=phplus (phplus p1 p2) Pleak) (h:=h); repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  right.
  reflexivity.
  }

  assert (p12l: phplus p1 p2 ll = Some Lock \/ phplus p1 p2 ll = None).
  {
  apply phplus_lock_none with Pleak.
  assumption.
  }

  assert (p1l: p1 ll = Some Lock \/ p1 ll = None).
  {
  apply phplus_lock_none with p2.
  assumption.
  }

  assert (p2l: p2 ll = Some Lock \/ p2 ll = None).
  {
  apply phplus_lock_none with p1.
  rewrite phplus_comm; repeat php_.
  }

  assert (pll: Pleak ll = Some Lock \/ Pleak ll = None).
  {
  apply phplus_lock_none with (phplus p1 p2).
  rewrite phplus_comm; repeat php_.
  }

  assert (p0l: forall p0 (IN: In p0 (map pof T)), p0 ll = Some Lock \/ p0 ll = None).
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  rewrite <- EQ.
  destruct (Z.eq_dec x6 id).
  rewrite e in IN.
  assert (EQX: (x1, x2, x3, x4, x5) = (Waiting4lock l, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN.
  assumption.
  assumption.
  inversion EQX.
  left.
  assumption.
  rewrite EQ in *.
  assert (PHPDp0: phplusdef p p0).
  {
  apply DEFL with id x6.
  omega.
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  rewrite EQ.
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
  assert (CO:=PH2H).
  destruct CO as (CO,CO1).
  unfold phtoh in CO.
  specialize CO with ll.
  rewrite NON in CO.
  erewrite fold_locked in CO; repeat php_.
  inversion CO.
  apply pofs.
  right.
  exists p0.
  exists.
  apply in_map_iff.
  exists (x1, x2, p0, x4, x5, x6).
  auto.
  apply p0l.
  right.
  reflexivity.
  }
  assert (PHPDUp1: forall wt ot, phplusdef (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt ot))) p1).
  {
  intros.
  apply phpdef_upd_locked.
  assumption.
  assumption.
  }
  assert (PHPDUp2: forall wt ot, phplusdef (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt ot))) p2).
  {
  intros.
  apply phpdef_upd_locked.
  assumption.
  assumption.
  }
  assert (EQP: phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1 = 
    upd (location_eq_dec Z.eq_dec) (phplus p p1) ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))).
  {
  apply phplus_upd.
  unfold not.
  intros.
  destruct H as (v,(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
  }

  exists (updl T id (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll::O, ghplus C C1, id)).
  exists invs, locs, p2, Pleak.
  exists (filter (fun x => negb (ifb ((location_eq_dec Z.eq_dec) (snd x) ll))) Ainv).
  exists C2, Cleak.

  assert (EQWT: forall l0 p O C, filterb (xOf (fun x  => Lof x) locs) (Aof l0) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) =
    filterb (xOf (fun x  => Lof x) locs) (Aof l0) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof
    (updl T id (tt, tx, p, O, C, id)))))).
  {
  intros.
  apply filterb_updl_eq.
  intros.
  split.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some v)).
  inversion e.
  reflexivity.
  intros.
  assert (X': x' = (Waiting4lock l, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some v)).
  inversion e.
  reflexivity.
  }
  assert (EQOT: forall l0 c p C, filterb (xOf (fun x  => Lof x) locs) (Aof l0) (count_occ Z.eq_dec (concat (map Aoof T))) =
    filterb (xOf (fun x  => Lof x) locs) (Aof l0) (count_occ Z.eq_dec (concat (map Aoof (updl T id
    (c, tx, p, Oof ll :: O, C, id)))))).
  {
  intros.
  apply filterb_updl_obs_eq.
  intros.
  assert (X': x' = (Waiting4lock l, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold Aoof.
  unfold Oof.
  simpl.
  destruct (Z.eq_dec (Aofo (fst (fst (fst ll)))) v).
  rewrite <- e in *.
  assert (XOF: xOf (fun x  => Lof x) locs (Aofo (fst (fst (fst ll)))) = Some (Lof ll)).
  {
  apply xOf_same.
  apply in_map.
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  apply comp_cons.
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  unfold comp.
  intros.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  }
  rewrite IN in XOF.
  inversion XOF.
  rewrite lll in *.
  rewrite H0 in NEQ.
  contradiction.
  reflexivity.
  }

  assert (ghpdefc1lc2l: ghplusdef C1 Cleak /\ ghplusdef C2 Cleak). repeat php_.

  assert (ghpdefxc1xc2l: forall x : gheap, In x (map gof T) -> 
    ghplusdef x C1 /\ ghplusdef x (ghplus C2 Cleak)).
  {
  intros.
  apply GHPD in H.
  assert (tmp: ghplusdef x C1 /\ ghplusdef x C2). repeat php_.
  split.
  repeat php_.
  repeat php_.
  }

  assert (EQCT: fold_left ghplus (map gof (updl T id (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll::O, ghplus C C1, id)))
    (ghplus C2 Cleak) = fold_left ghplus (map gof T) ((ghplus (ghplus C1 C2) Cleak))).
  {
  rewrite <- fold_left_move_m_eq2 with (def:=ghplusdef) (x1:=C) (x2:=C1); repeat php_.
  rewrite ghplus_assoc; repeat php_.
  rewrite <- fold_left_f_m_def with (def:=ghplusdef); repeat php_.
  apply can_ghpdef.
  apply can_ghpdef.
  apply ghpdefxc1xc2l.
  apply ghpdefxc1xc2l.
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id). auto.
  }

  assert (p0ln: forall p0, In p0 (map pof T) \/ p0 = phplus p1 p2 -> p0 ll = None \/ p0 ll = Some Lock).
  {
  intros.
  destruct H as [IN|IN].
  apply or_comm.
  apply p0l.
  assumption.
  rewrite IN.
  unfold phplus.
  destruct p1l as [p1l|p1l].
  rewrite p1l.
  destruct p2l as [p2l|p2l].
  rewrite p2l.
  right.
  reflexivity.
  rewrite p2l.
  right.
  reflexivity.
  rewrite p1l.
  destruct p2l as [p2l|p2l].
  rewrite p2l.
  right.
  reflexivity.
  rewrite p2l.
  left.
  reflexivity.
  }

  assert (phpdefp1lp2l: phplusdef p1 Pleak /\ phplusdef p2 Pleak). repeat php_.
  assert (phpdefp01p02l: forall p0, In p0 (map pof T) -> phplusdef p0 p1 /\ phplusdef p0 p2 /\ phplusdef p0 Pleak).
  {
  intros.
  apply PHPD in H.
  assert (tmp: phplusdef p0 p1 /\ phplusdef p0 p2). repeat php_.
  split;
  repeat php_.
  split;
  repeat php_.
  }

  assert (ghpdefp01p02l: forall p0, In p0 (map gof T) -> ghplusdef p0 C1 /\ 
    ghplusdef p0 C2 /\ ghplusdef p0 Cleak).
  {
  intros.
  apply GHPD in H.
  assert (tmp: ghplusdef p0 C1 /\ ghplusdef p0 C2). repeat php_.
  split;
  repeat php_.
  split;
  repeat php_.
  }

  assert (p0ln': forall p0, In p0 (map pof T) \/ p0 = phplus p1 (phplus p2 Pleak) -> p0 ll = None \/ p0 ll = Some Lock).
  {
  intros.
  apply locked_fold_phtoheap with (m:=pof) (l:=T) (id:=id) (p:=p) (b:=phplus (phplus p1 p2) Pleak) (h:=h); repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  rewrite phplus_assoc; repeat php_.
  }

  assert (EQH0: forall l0 (NEQ: ll <> l0),
    fold_left phplus (map pof T) (phplus p1 p2) l0 =
    fold_left phplus (map pof (updl T id
    (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll :: O, ghplus C C1, id))) p2 l0).
  {
  symmetry.
  apply eq_heap_Acquire with (z:=ll) (p:=p); repeat php_.
  apply pofs.
  apply PHPD.
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  eexists.
  eexists.
  reflexivity.
  }

  assert (EQH: forall l0 (NEQ: ll <> l0),
    fold_left phplus (map pof T) (phplus (phplus p1 p2) Pleak) l0 =
    fold_left phplus (map pof (updl T id
    (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll :: O, ghplus C C1, id))) (phplus p2 Pleak) l0).
  {
  rewrite phplus_assoc; repeat php_.
  symmetry.
  apply eq_heap_Acquire with (z:=ll) (p:=p); repeat php_.
  apply pofs.
  intros.
  apply phpdefp01p02l in IN.
  repeat php_.
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  eexists.
  eexists.
  reflexivity.
  }

  assert (LOCKEDU: fold_left phplus (map pof (updl T id
    (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll :: O, ghplus C C1, id))) (phplus p2 Pleak) ll = 
    Some (Locked (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))))).
  {
  apply locked_Acquire with p p1; repeat php_.
  apply pofs.
  intros.
  apply phpdefp01p02l in IN.
  repeat php_.
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  }

  assert (INl01: forall l0 (IN: In l0 (concat (map oof T))),
    In l0 (concat (map oof (updl T id (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll::O, ghplus C C1, id))))).
  {
  intros.
  rewrite <- flat_map_concat_map in IN.
  apply in_flat_map in IN.
  destruct IN as (x,(INx,INl0)).
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (Waiting4lock l, tx, p, O, C)).
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  inversion EQX.
  exists (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll :: O, ghplus C C1, id).
  split.
  apply in_updl_eq.
  exists (Waiting4lock l, tx, p, O, C).
  auto.
  unfold oof.
  simpl.
  right.
  rewrite <- H3.
  assumption.
  exists (x1, x2, x3, x4, x5, x6).
  split.
  apply in_updl_neq.
  omega.
  assumption.
  assumption.
  }

  assert (INl02: forall o0 (NEQ: Oof ll <> o0) (IN: In o0 (concat (map oof (updl T id (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll::O, ghplus C C1, id))))),
    In o0 (concat (map oof T))).
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
  unfold oof in INl0.
  simpl in INl0.
  assert (EQX: (x1, x2, x3, x4, x5) = (Waiting4lock l, tx, p, O, C)).
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  inversion EQX.
  destruct INl0 as [CO|INl0].
  contradiction.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }

  assert (inc: In C (map gof T)).
  {
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  }

  assert (ghpdefCC1: ghplusdef C C1).
  {
  apply ghpdef_comm.
  apply ghpdef_assoc_mon with C2.
  repeat php_.
  apply ghpdef_comm.
  rewrite ghplus_comm.
  apply GHPD.
  assumption.
  repeat php_.
  }

  assert (incid: In (C, id) (map (fun x => (gof x, snd x)) T)).
  {
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  }

  assert (ghpdefCC12: ghplusdef C (ghplus C1 C2)).
  {
  apply GHPD.
  assumption.
  }

  assert (ghpdefCC2: ghplusdef C C2).
  {
  apply ghpdef_comm.
  apply ghpdef_assoc_mon with C1; repeat php_.
  }

  assert (ghpdefCCl: ghplusdef C Cleak).
  {
  apply GHPD.
  assumption.
  }

  assert (ghpdefC2Cl: ghplusdef C2 Cleak).
  {
  apply ghpdef_assoc_mon with C1; repeat php_.
  }

  assert (bp: boundph p).
  {
  apply BPE.
  assumption.
  }

  assert (phpdefppl: phplusdef p Pleak).
  {
  apply PHPD.
  assumption.
  }

  assert (bp12plp: boundph (phplus (phplus (phplus p1 p2) Pleak) p)).
  {
  apply boundph_fold with (m:=pof) (l:=T); repeat php_.
  }

  assert (bp12p: boundph (phplus (phplus p1 p2) p)).
  {
  apply boundph_mon with Pleak; repeat php_.
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_assoc in bp12plp; repeat php_.
  replace (phplus p Pleak) with (phplus Pleak p); repeat php_.
  }

  assert (bpp1: boundph (phplus p p1)).
  {
  apply boundph_mon with p2; repeat php_.
  rewrite phplus_assoc; repeat php_.
  }

  assert (phpdefupp1: phplusdef (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll)
    (fun v : Z => length (filter (fun c : cmd =>
    ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
   (map cmdof T)))) (filterb (xOf (fun x  => Lof x) locs) (Aof ll)
   (count_occ Z.eq_dec (concat (map Aoof T))))))) p1).
  {
  apply phpdef_locked'; repeat php_.
  }

  assert (phpdefuppl: phplusdef Pleak (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll)
    (fun v : Z => length (filter (fun c : cmd =>
    ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
   (map cmdof T)))) (filterb (xOf (fun x  => Lof x) locs) (Aof ll)
   (count_occ Z.eq_dec (concat (map Aoof T)))))))).
  {
  apply phpdef_comm.
  apply phpdef_locked'; repeat php_.
  }

  assert (bupd: boundph (phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked
    (filterb (xOf (fun x : location Z => Lof x) locs) (Aof ll) (fun v : Z =>
    length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) (Some v)))
    (map cmdof T)))) (filterb (xOf (fun x : location Z => Lof x) locs) (Aof ll)
    (count_occ Z.eq_dec (concat (map Aoof T))))))) p1)).
  {
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1,(v2,(CO,rest))).
  inversion CO.
  }

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  rewrite EQCT.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  rewrite eqll.
  apply red_Acquire1.
  assumption.
  rewrite <- eqll.
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
  rewrite <- EQH in CONDv.
  apply SPUR2 in CONDv.
  destruct CONDv as (a,(b,(c,d))).
  exists a, b.
  exists.
  destruct (location_eq_dec Z.eq_dec ll a).
  right.
  eexists.
  eexists.
  rewrite <- e.
  rewrite LOCKEDU.
  reflexivity.
  rewrite <- EQH.
  assumption.
  assumption.
  assumption.
  unfold not.
  intros CO.
  rewrite <- CO in CONDv.
  rewrite LOCKEDU in CONDv.
  inversion CONDv.
  }

  exists.
  {
  split.
  {
  apply defl_Acquire with (p:=p) (p1:=p1) (p2:=p2) (z:=ll); repeat php_.
  apply pofs.
  apply PHPD.
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  eexists.
  eexists.
  reflexivity.
  }
  exists. repeat php_.
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
  apply phpdef_comm.
  apply phpdef_pair.
  apply PHPDUp1.
  apply phpdef_comm.
  apply PHPDUp2.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  apply phpdef_pair.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2; repeat php_.
  simpl in EQ.
  rewrite EQ in IN.
  assert (G: In p0 (map pof T)).
  {
  apply in_map_iff.
  exists (x1, x2, p0, x4, x5, x6).
  auto.
  }
  apply phpdefp01p02l in G.
  split; repeat php_.
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
  rewrite EQP.
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  simpl in EQ.
  rewrite EQ in IN.
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, p0, x4, x5, x6).
  auto.
  }
  exists. assumption.
  exists. assumption.
  exists.

  assert (bp2l: boundph (phplus p2 Pleak)).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_mon with p1; repeat php_.
  rewrite phplus_assoc; repeat php_.
  replace (phplus p2 p1) with (phplus p1 p2); repeat php_.
  }

  assumption.
  split.
  {
  apply boundph_Acquire with (p:=p) (p1:=p1) (z:=ll); repeat php_.
  apply pofs.
  intros.
  apply phpdefp01p02l in IN.
  repeat php_.
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  eexists.
  eexists.
  reflexivity.
  left.
  assumption.
  rewrite <- phplus_assoc; repeat php_.
  }
  unfold phtoh in *.
  destruct PH2H as (PH1,PH2).
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  {
  rewrite <- e in *.
  rewrite LOCKEDU.
  unfold upd.
  rewrite eqz.
  reflexivity.
  }
  rewrite <- EQH.
  specialize PH1 with l0.
  destruct (fold_left phplus (map pof T) (phplus (phplus p1 p2) Pleak) l0) eqn:fl0.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  assert (CO: ll = l0).
  {
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite fl0.
  apply some_none.
  symmetry.
  assumption.
  }
  contradiction.
  assumption.
  trivial.
  assumption.
  }
  intros.
  unfold upd.
  destruct (Z.eq_dec z (Aof ll)).
  symmetry in e.
  apply NONE in e.
  rewrite LOCKEDU in e.
  inversion e.
  apply PH2.
  intros.
  rewrite EQH.
  apply NONE.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  omega.
  }
  exists.
  {
  split.
  {
  unfold defl.
  unfold updl.
  rewrite map_map.
  unfold gof.
  simpl.
  intros.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  apply in_map_iff in IN2.
  destruct IN2 as (x2,(EQ2,IN2)).
  destruct (Z.eq_dec (snd x1) id).
  simpl in EQ1.
  inversion EQ1.
  destruct (Z.eq_dec (snd x2) id).
  simpl in EQ2.
  inversion EQ2.
  omega.
  inversion EQ2.
  apply ghpdef_pair'; repeat php_.

  apply DEFLg with id (snd x2).
  omega.
  assumption.
  apply in_map_iff.
  exists x2.
  auto.
  assert (G: In (snd (fst x2)) (map gof T)).
  {
  apply in_map_iff.
  exists x2.
  auto.
  }
  apply ghpdefp01p02l in G.
  repeat php_.

  inversion EQ1.
  destruct (Z.eq_dec (snd x2) id).
  simpl in EQ2.
  inversion EQ2.

  assert (G: In (snd (fst x1)) (map gof T)).
  {
  apply in_map_iff.
  exists x1.
  auto.
  }
  apply ghpdefp01p02l in G.
  apply ghpdef_pair; repeat php_.
  apply DEFLg with (snd x1) id.
  omega.
  apply in_map_iff.
  exists x1.
  auto.
  assumption.
  inversion EQ2.
  apply DEFLg with (snd x1) (snd x2).
  omega.
  apply in_map_iff.
  exists x1.
  auto.
  apply in_map_iff.
  exists x2.
  auto.
  }
  split.
  {
  unfold updl.
  rewrite map_map.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  unfold gof in EQ1.
  simpl in EQ1.
  inversion EQ1.

  split; repeat php_.
  inversion EQ1.
  assert (G: In (gof x1) (map gof T)).
  {
  apply in_map_iff.
  exists x1.
  auto.
  }
  apply ghpdefp01p02l in G.
  split; repeat php_.
  }
  split; assumption.
  }
  exists.
  {
  intros.
  apply upd_updl.
  exists (Waiting4lock l, tx, p, O, C).
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
  split.
  {
  erewrite map_filter with (f3:= fun x => (if if (location_eq_dec Z.eq_dec) x ll then true else false then false else true)).
  apply nodup_filter.
  assumption.
  intros.
  reflexivity.
  }
  split.
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  apply filter_In in IN.
  destruct IN as (EQ1,EQ2).
  unfold negb in EQ2.
  unfold ifb in EQ2.
  destruct ((location_eq_dec Z.eq_dec) (snd x) ll).
  inversion EQ2.
  assert (G: fold_left phplus (map pof T) (phplus (phplus p1 p2) Pleak) l0 =
         Some Lock /\ h (Aof l0) = Some 1%Z).
  {
  apply AinvOK.
  apply in_map_iff.
  exists x.
  auto.
  }
  destruct G as (G1,G2).
  rewrite <- EQH.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  exfalso.
  apply n.
  rewrite EQ.
  apply INJ.
  rewrite G1.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  assumption.
  split; assumption.
  unfold not.
  intros.
  rewrite H in n.
  rewrite EQ in n.
  contradiction.
  }
  split.
  {
  unfold upd.
  intros.
  rewrite <- EQWT.
  rewrite <- EQOT.  
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  inversion NOTHELD.
  apply filter_In.
  split.
  apply INAOK.
  rewrite EQH.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  assumption.
  simpl.
  destruct ((location_eq_dec Z.eq_dec) l0 ll).
  rewrite e in n.
  contradiction.
  reflexivity.
  }
  assumption.
  }
  exists.
  {
  split.
  {
  unfold injph.
  intros.
  apply INJ.
  destruct ((location_eq_dec Z.eq_dec) ll x1).
  rewrite <- e in *.
  rewrite LOCKED.
  apply some_none.
  rewrite EQH.
  assumption.
  assumption.
  destruct ((location_eq_dec Z.eq_dec) ll x2).
  rewrite <- e in *.
  rewrite LOCKED.
  apply some_none.
  rewrite EQH.
  assumption.
  assumption.
  }
  split. assumption.
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  split.
  intros.
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  intros.
  rewrite LOCKEDU.
  apply some_none.
  rewrite <- EQH.
  apply LOCs.
  assumption.
  }
  intros.
  destruct ((olocation_eq_dec Z.eq_dec) (Oof ll) o).
  rewrite <- e in *.
  exists ll.
  exists.
  reflexivity.
  rewrite LOCKEDU.
  apply some_none.
  apply INl02 in IN.
  apply OBsOK in IN.
  destruct IN as (l',(EQl',pl')).
  exists l', EQl'.
  rewrite <- EQH.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  rewrite <- EQl' in n.
  contradiction.
  assumption.
  }
  exists.
  {
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  unfold upd.
  rewrite eqz.
  split. assumption.
  split. assumption.
  split. assumption.
  intros.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll :: O, ghplus C C1, id).
  split.
  apply in_updl_eq.
  exists (Waiting4lock l, tx, p, O, C).
  auto.
  unfold oof.
  simpl.
  left.
  reflexivity.
  rewrite <- EQH in LOCK.
  assert (tmp1:=LOCK).
  apply LOCKOK in LOCK.
  destruct LOCK as (L1,(L2,(L3,L4))).
  split. assumption.
  split. assumption.
  split. assumption.
  unfold upd.
  intros.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  exfalso.
  apply n.
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  destruct tmp1 as [tmp1|tmp1].
  rewrite tmp1.
  apply some_none.
  destruct tmp1 as (wt1,(ot1,tmp1)).
  destruct tmp1 as [tmp1|tmp1].
  rewrite tmp1.
  apply some_none.
  rewrite tmp1.
  apply some_none.
  symmetry.
  assumption.
  apply L4 in H.
  apply INl01.
  assumption.
  assumption.
  }
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  rewrite LOCKEDU in *.
  inversion ULOCK.
  rewrite <- EQH in ULOCK.
  assert (tmp1:=ULOCK).
  apply ULOCKOK in ULOCK.
  destruct ULOCK as (U1,U2).
  split.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  exfalso.
  apply n.
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite tmp1.
  apply some_none.
  symmetry. assumption.
  assumption.
  unfold not.
  intros.
  apply U2.
  apply INl02; try assumption.
  unfold not.
  intros.
  assert (CO: ll = l0).
  {
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite tmp1.
  apply some_none.
  unfold Aof.
  rewrite H0.
  reflexivity.
  }
  contradiction.
  assumption.
  }
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  rewrite LOCKEDU in *.
  inversion UCOND.
  rewrite <- EQH in UCOND.
  assert (tmp1:=UCOND).
  apply UCONDOK in UCOND.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  exfalso.
  apply n.
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite tmp1.
  apply some_none.
  symmetry. assumption.
  unfold not.
  intros.
  apply UCOND.
  apply INl02; try assumption.
  unfold Aof in n0.
  unfold not.
  intros.
  rewrite H0 in n0.
  contradiction. 
  assumption.
  }
  exists.
  {
  intros.
  rewrite <- EQOT.
  rewrite <- EQWT.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  rewrite LOCKEDU in *.
  destruct ULOCKED as [U1|U2].
  {
  inversion U1.
  split; reflexivity.
  }
  inversion U2.
  rewrite <- EQH in ULOCKED.
  apply WTsOTsOK.
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
  {
  simpl in EQ.
(* ==================== x6 = id ===========*)
  symmetry in EQ.
  inversion EQ.
  exists.
  unfold wellformed.
  simpl. tauto.
  split.

  assert (bp1pp2: boundph (phplus (phplus p1 p) p2)).
  {
  rewrite phplus_comm; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  replace (phplus p2 p1) with (phplus p1 p2); repeat php_.
  }

  assert (bgcc12l: boundgh (ghplus (ghplus (ghplus C1 C2) Cleak) C)).
  {
  apply boundgh_fold with (m:=gof) (l:=T); repeat php_.
  }

  assert (bgc12c: boundgh (ghplus (ghplus C1 C2) C)).
  {
  apply boundgh_mon with Cleak.
  rewrite ghplus_assoc; repeat php_.
  rewrite ghplus_assoc in bgcc12l; repeat php_.
  replace (ghplus C Cleak) with (ghplus Cleak C); repeat php_.
  }

  assert (bgc1c: boundgh (ghplus C1 C)).
  {
  rewrite ghplus_comm; repeat php_.
  apply boundgh_mon with C2.
  rewrite ghplus_assoc; repeat php_.
  }
  eapply sat_weak_imp1; try assumption.
  repeat php_.
  apply SAT1; repeat php_.
  apply p0l.
  assumption.
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
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=(ghplus (ghplus C1 C2) Cleak)); repeat php_.
  intros.
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

  destruct WP3 as (l',(v',(eql',(eqv',(pv0',(pl0',(lvl0',(prcl0',(prcv0',SAT0'))))))))).

  apply VOBS3 in W4COND.
  destruct W4COND as (v0,(l0,(inv0,(inl0,(eqv0,(eql0,sob1)))))).
  exists v0, l0, inv0, inl0, eqv0, eql0.
  rewrite <- EQOT.
  rewrite <- EQWT.
  assumption.
Qed.


Lemma Release_preserves_validity:
  forall m sp h t id l tx
         (VALIDK: validk (S m) sp t h)
         (CMD : t id = Some (Release l, tx)),
    validk m sp (upd Z.eq_dec t id (Some (tt, tx))) (upd Z.eq_dec h ([[l]]) (Some 1%Z)).
Proof.
  intros.
  unfold validk in VALIDK.
  destruct VALIDK as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
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
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).

  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.

  assert (tmp: exists p O C, In (Release l, tx, p, O, C, id) T).
  {
  apply TOK.
  assumption.
  }
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,SOBS1)).
  unfold wellformed in WF.
  simpl in WF.

  apply sat_release in WP.
  destruct WP as (ll,(p1,(p2,(wt,(ot,(C1,(C2,(O1,(eqll,(O1eq,(bp1,(bp2,(bc1,(bc2,(phpdefp1p2,(ghpdefc1c2,(p1p2,(C1C2,(p1l,(satp2,SAT)))))))))))))))))))).
  subst.

  assert (INpT: In (phplus p1 p2) (map pof T)).
  {
  apply in_map_iff.
  exists (Release l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  }

  assert (phpdefp1pil: phplusdef (phplus p1 p2) (phplus Pinv Pleak)).
  {
  apply phpdef_pair;
  try tauto.
  apply PHPD; tauto.
  apply PHPD; tauto.
  }

  assert (phpdefp1ilp2il: phplusdef p1 (phplus Pinv Pleak) /\ phplusdef p2 (phplus Pinv Pleak)).
  {
  apply phpdef_dist;
  try tauto.
  }

  assert (phpdefp1Pinv: phplusdef p1 Pinv /\ phplusdef p1 Pleak).
  {
  apply phpdef_dist';
  tauto.
  }

  assert (phpdefp2Pinv: phplusdef p2 Pinv /\ phplusdef p2 Pleak).
  {
  apply phpdef_dist';
  tauto.
  }

  assert (phpdefp0: forall p0, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  apply phpdef_pair;
  try tauto.
  apply PHPD.
  tauto.
  apply PHPD.
  tauto.
  }

  assert (inc1c2': In (ghplus C1 C2, id) (map (fun x => (gof x, snd x)) T)).
  {
  apply in_map_iff.
  exists (Release l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  tauto.
  }

  assert (inc1c2: In (ghplus C1 C2) (map gof T)).
  {
  apply in_map_iff.
  exists (Release l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  tauto.
  }

  assert (ghpdefp1pil: ghplusdef (ghplus C1 C2) (ghplus Cinv Cleak)).
  {
  apply ghpdef_pair;
  try tauto.
  apply GHPD; tauto.
  apply GHPD; tauto.
  }

  assert (ghpdefp1ilp2il: ghplusdef C1 (ghplus Cinv Cleak) /\ ghplusdef C2 (ghplus Cinv Cleak)).
  {
  apply ghpdef_dist;
  try tauto.
  }

  assert (ghpdefp1Pinv: ghplusdef C1 Cinv /\ ghplusdef C1 Cleak).
  {
  apply ghpdef_dist';
  tauto.
  }

  assert (ghpdefp2Pinv: ghplusdef C2 Cinv /\ ghplusdef C2 Cleak).
  {
  apply ghpdef_dist';
  tauto.
  }

  assert (ghpdefp0: forall p0, In p0 (map gof T) -> ghplusdef p0 (ghplus Cinv Cleak)).
  {
  intros.
  apply ghpdef_pair;
  try tauto.
  apply GHPD.
  tauto.
  apply GHPD.
  tauto.
  }

  assert (LOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked wt ot)).
  {
  apply fold_locked;
  try tauto.
  apply pofs.
  right.
  exists (phplus p1 p2), INpT.
  apply phplus_locked.
  assumption.
  assumption.
  }
  assert (LOCK: fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock),
           O1, C1, id))) (phplus (phplus Pinv Pleak) p2) ll = Some Lock).
  {
  apply lock_Wait with p1;
  try tauto.
  apply pofs.
  apply in_map_iff.
  exists (Release l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  tauto.
  eauto.
  }

  assert (EQh1: phplus (phplus Pinv p2) Pleak = phplus (phplus Pinv Pleak) p2).
  {
  repeat php_.
  }

  assert (LOCK1: fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock),
           O1, C1, id))) (phplus (phplus Pinv p2) Pleak) ll = Some Lock).
  {
  rewrite EQh1.
  repeat php_.
  }

  assert (EQH0: forall l0 (NEQ: ll <> l0), fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock),
    O1, C1, id))) (phplus (phplus Pinv Pleak) p2) l0 = 
    fold_left phplus (map pof T) (phplus Pinv Pleak) l0).
  {
  intros.
  apply eq_heap_Wait with (z:=ll) (p1:=p1);
  try tauto.
  apply pofs.
  apply in_map_iff.
  exists (Release l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  exists wt, ot.
  left.
  assumption.
  }

  assert (EQH: forall l0 (NEQ: ll <> l0), fold_left phplus (map pof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock),
    O1, C1, id))) (phplus (phplus Pinv p2) Pleak) l0 = 
    fold_left phplus (map pof T) (phplus Pinv Pleak) l0).
  {
  intros.
  rewrite EQh1.
  apply EQH0.
  tauto.
  }

  assert (EQgh1: ghplus (ghplus Cinv Cleak) C2 = ghplus (ghplus Cinv C2) Cleak).
  {
  cnj_; repeat php_.
  }

  assert (EQGH0: fold_left ghplus (map gof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock),
    O1, C1, id))) (ghplus (ghplus Cinv Cleak) C2) = 
    fold_left ghplus (map gof T) (ghplus Cinv Cleak)).
  {
  rewrite eq_gheap_Wait with (p1:=C1);
  try tauto.
  apply gofs.
  }

  assert (EQGH: fold_left ghplus (map gof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock),
    O1, C1, id))) (ghplus (ghplus Cinv C2) Cleak) = 
    fold_left ghplus (map gof T) (ghplus Cinv Cleak)).
  {
  rewrite <- EQgh1; tauto.
  }

  assert (tmp: Lof ll = Aof ll /\ Pof ll = false /\
    Xof ll = None /\ (h (Aof ll) <> Some 1%Z -> In (Oof ll) (concat (map oof T)))).
  {
  apply LOCKOK.
  right.
  exists wt, ot.
  left.
  assumption.
  }
  destruct tmp as (lll,(plf,(ninrlxll,inlt))).

  assert (inllocs: In ll locs).
  {
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  }

  assert (complllocs: comp (ll :: locs) (fun x  => Aof x)).
  {
  unfold comp in *.
  intros.
  apply INJ.
  destruct IN as [IN|IN].
  rewrite <- IN.
  rewrite LOCKED.
  apply some_none.
  apply LOCs.
  assumption.
  destruct IN0 as [IN0|IN0].
  rewrite <- IN0.
  rewrite LOCKED.
  apply some_none.
  apply LOCs.
  assumption.
  }

  assert (bpilp12: boundph (phplus (phplus Pinv Pleak) (phplus p1 p2))).
  {
  apply boundph_fold with (m:=pof) (l:=T);
  try tauto.
  }

  assert (bpilp2: boundph (phplus (phplus Pinv Pleak) p2)).
  {
  repeat php_.
  rewrite phplus_assoc; repeat php_.
  replace (phplus p2 p1) with (phplus p1 p2); repeat php_.
  }

  assert (bpi2pl: boundph (phplus (phplus Pinv p2) Pleak)).
  {
  rewrite EQh1.
  tauto.
  }

  assert (bpi2: boundph (phplus Pinv p2)).
  {
  apply boundph_mon with Pleak;
  try tauto.
  }

  assert (bpinvp12: boundph (phplus (phplus Pinv Pleak) (phplus p2 p1))).
  {
  replace (phplus p2 p1) with (phplus p1 p2).
  {
  apply boundph_fold with (m:=pof) (l:=T);
  try tauto.
  }
  apply phplus_comm.
  tauto.
  }

  assert (bgpinvp12: boundgh (ghplus (ghplus Cinv Cleak) (ghplus C1 C2))).
  {
  apply boundgh_fold with (m:=gof) (l:=T);
  try tauto.
  }

  assert (bgpilp2: boundgh (ghplus (ghplus Cinv Cleak) C2)).
  {
  repeat php_.
  rewrite ghplus_assoc; repeat php_.
  replace (ghplus C2 C1) with (ghplus C1 C2); repeat php_.
  }

  assert (bgpi2pl: boundgh (ghplus (ghplus Cinv C2) Cleak)).
  {
  rewrite <- EQgh1.
  tauto.
  }

  assert (bgpi2: boundgh (ghplus Cinv C2)).
  {
  apply boundgh_mon with Cleak;
  try tauto.
  }

  assert (bgpinvp21: boundgh (ghplus (ghplus Cinv Cleak) (ghplus C2 C1))).
  {
  replace (ghplus C2 C1) with (ghplus C1 C2); repeat php_.
  }

  assert (bppinv2: boundph (phplus (phplus Pinv Pleak) p2)).
  {
  apply boundph_mon with p1;
  try tauto.
  cnj_.
  rewrite phplus_assoc; repeat php_.
  }

  assert (bgpilp12: boundgh (ghplus (ghplus Cinv Cleak) (ghplus C1 C2))).
  {
  apply boundgh_fold with (m:=gof) (l:=T);
  try tauto.
  }

  assert (EQWT: forall l0 p O C, filterb (xOf (fun x  => Lof x) locs) (Aof l0) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) =
    filterb (xOf (fun x  => Lof x) locs) (Aof l0) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof
    (updl T id (tt, tx, p, O, C, id)))))).
  {
  intros.
  apply filterb_updl_eq.
  intros.
  split.
  unfold cmdof.
  simpl.
  repeat dstr_.
  intros.
  assert (X': x' = (Release l, tx, phplus p1 p2, O, ghplus C1 C2, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  repeat dstr_.
  }

  assert (INOB': forall l (IN: In l (concat (map oof (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock), O1, C1,
          id))))), In l (concat (map oof T))).
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
  assert (EQX: (x1, x2, x3, x4, x5) = (Release l, tx, phplus p1 p2, O, ghplus C1 C2)).
  {
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  }
  inversion EQX.
  exists (Release l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  split.
  assumption.
  unfold oof in *.
  simpl in *.
  apply Permutation_in with (Oof ll :: O1).
  apply Permutation_sym.
  assumption.
  right.
  assumption.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }

  assert (bgil: boundgh (ghplus Cinv Cleak)).
  {
  apply boundgh_mon with C2;
  try tauto.
  }

  assert (bgi: boundgh Cinv).
  {
  apply boundgh_mon with Cleak;
  try tauto.
  }

  assert (EQOT: forall l0 c p C, filterb (xOf (fun x  => Lof x) locs) (Aof l0) (count_occ Z.eq_dec (concat (map Aoof T))) =
    filterb (xOf (fun x  => Lof x) locs) (Aof l0) (count_occ Z.eq_dec (concat (map Aoof (updl T id
    (c, tx, p, O1, C, id)))))).
  {
  intros.
  apply filterb_updl_obs_eq.
  intros.
  assert (X': x' = (Release l, tx, phplus p1 p2, O, ghplus C1 C2, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.

  unfold Aoof.
  simpl.
  destruct (Z.eq_dec (Aof ll) v).
  rewrite <- e in IN.

  assert (XOF1: xOf (fun x  => Lof x) locs (Aof ll) = Some (Lof ll)).
  {
  apply xOf_same.
  apply in_map.
  assumption.
  assumption.
  }

  rewrite IN in XOF1.
  inversion XOF1.
  rewrite lll in *.
  omega.
  apply eq_trans with (count_occ Z.eq_dec (map (fun x => Aofo x) (Oof ll::O1)) v).
  apply count_perm1.
  apply Permutation_map.
  assumption.
  apply count_occ_cons_neq.
  assumption.
  }

  assert (bupd: boundph (upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock))).
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  exists (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock), O1, C1, id)).
  exists invs, locs, (phplus Pinv p2), Pleak, ((subsas (snd (Iof ll)) (invs (fst (Iof ll)) wt ot),ll)::Ainv), (ghplus Cinv C2), Cleak.
  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  rewrite EQGH.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  apply red_Release; try assumption.
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
  unfold upd in CONDv.
  destruct (location_eq_dec Z.eq_dec ll v).
  rewrite <- e in CONDv.
  unfold upd in *.
  rewrite EQh1 in CONDv.
  rewrite LOCK in CONDv.
  inversion CONDv.
  rewrite EQH in CONDv.
  apply SPUR2 in CONDv.
  destruct CONDv as (a,(b,(c,d))).
  exists a, b.
  exists.
  destruct (location_eq_dec Z.eq_dec ll a).
  rewrite <- e.
  rewrite EQh1.
  rewrite LOCK.
  left.
  reflexivity.
  rewrite EQH.
  assumption.
  assumption.
  assumption.
  assumption.
  }

  exists.
  {
  exists.
  {
  apply defl_Wait with (p1:=p1) (p2:=p2) (z:=ll);
  try tauto.
  apply in_map_iff.
  exists (Release l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  exists wt, ot.
  left.
  assumption.
  }
  exists.
  {
  cnj_; repeat php_.
  }
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in *.
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
  apply phpdef_locked_lock.
  apply phpdef_pair;
  try tauto.
  apply phpdef_comm; tauto.
  exists wt, ot.
  left.
  assumption.
  apply phpdef_locked_lock.
  tauto.
  exists wt, ot.
  left.
  assumption.
  simpl in EQ.
  rewrite <- EQ.
  split.
  apply phpdef_pair.
  apply phpdef_comm; tauto.
  apply PHPD.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1; try tauto.
  apply DEFL with id x6.
  omega.
  apply in_map_iff.
  exists (Release l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  tauto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  tauto.
  apply PHPD.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  tauto.
  }
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in *.
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
  {
  cnj_; repeat php_.
  }
  exists. tauto.
  exists. tauto.
  exists.
  {
  rewrite map_map in *.
  rewrite EQh1.
  apply boundph_Wait with (p1:=p1) (z:=ll);
  try tauto.
  apply pofs.
  apply in_map_iff.
  exists (Release l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  exists wt, ot.
  left.
  assumption.
  }
  {
  unfold phtoh in *.
  assert (PHTOH:=PH2H).
  destruct PHTOH as (PHTOH,PHTOH1).
  split.
  intros.
  specialize PHTOH with l0.
  unfold upd at 2 3 4 5 6 7 8.
  destruct ((location_eq_dec Z.eq_dec) l0 ll).
  rewrite e in *.
  rewrite eqll.
  rewrite eqz.
  rewrite EQh1.
  rewrite map_map in *.
  unfold pof.
  unfold pof in LOCK.
  simpl in *.
  rewrite LOCK.
  reflexivity.
  rewrite <- eqll.
  rewrite map_map.
  simpl.
  rewrite EQH.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  destruct (fold_left phplus (map pof T) (phplus Pinv Pleak) l0) eqn:ll0.
  assert (CO: l0 = ll).
  {
  apply INJ.
  rewrite ll0.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }
  contradiction.
  trivial.
  assumption.
  unfold not.
  intros.
  symmetry in H.
  contradiction.
  intros.
  unfold upd.
  rewrite <- eqll.
  destruct (Z.eq_dec z (Aof ll)).
  symmetry in e.
  apply NONE in e.
  rewrite map_map in e.
  unfold pof in *.
  simpl in *.
  rewrite LOCK1 in e.
  inversion e.
  apply PHTOH1.
  intros.
  rewrite <- EQH.
  rewrite map_map in NONE.
  unfold pof in *.
  apply NONE.
  assumption.
  unfold not.
  intros.
  rewrite <- H in EQ.
  rewrite <- EQ in n.
  contradiction.
  }
  }
  exists.
  exists.
  {
  apply deflg_Wait with C1 C2;
  try tauto.
  }
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQx,INx)).
  destruct (Z.eq_dec (snd x1) id).
  unfold gof in EQx; simpl in EQx; rewrite <- EQx.
  split; try tauto.
  apply ghpdef_pair; try tauto.
  apply ghpdef_comm; tauto.
  rewrite <- EQx; split.
  apply ghpdef_pair; try tauto.
  apply ghpdef_comm; tauto.
  apply GHPD. simpl. apply in_map; tauto.
  apply ghpdef_comm.
  apply ghpdef_assoc_mon with C1; try tauto.
  apply DEFLg with id (snd x1); try tauto.
  omega.
  apply in_map_iff.
  exists x1; tauto.
  apply GHPD.
  simpl.
  apply in_map; tauto.
  }
  exists.
  {
  apply ghpdef_pair'; try tauto.
  apply ghpdef_comm; tauto.
  }
  {
  rewrite map_map.
  simpl.
  change (fun x => gof x) with gof.
  rewrite EQGH.
  assumption.
  }
  exists.
  {
  intros.
  apply upd_updl.
  exists (Release l, tx, phplus p1 p2, O, ghplus C1 C2).
  assumption.
  assumption.
  }
  exists.
  {
  apply NoDup_updl; tauto.
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
  destruct H as (CO,hl1).
  rewrite LOCKED in CO.
  inversion CO.
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
  unfold upd.
  rewrite eqll.
  rewrite eqz.
  reflexivity.
  apply AinvOK in IN.
  unfold upd.
  rewrite <- eqll in *.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  assert (EQL: l0 = ll).
  {
  apply INJ.
  destruct IN as (EQ1,IN1).
  rewrite EQ1.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }
  rewrite EQL.
  tauto.
  rewrite EQH.
  tauto.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  }
  exists.
  {
  unfold WTs, OBs.
  intros.
  rewrite <- EQWT.
  rewrite <- EQOT.
  unfold upd in NOTHELD.
  destruct (Z.eq_dec (Aof l0) ([[l]])).
  rewrite e.
  assert (eqll0: l0 = ll).
  {
  destruct ((location_eq_dec Z.eq_dec) l0 ll).
  assumption.
  apply INJ.
  rewrite <- EQH.
  rewrite LOCK0.
  apply some_none.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  rewrite LOCKED.
  apply some_none.
  rewrite eqll.
  assumption.
  }
  rewrite eqll0 in *.
  assert (wot: wt = filterb (xOf (fun x  => Lof x) locs) (Aof ll)
    (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) /\
    ot = filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))).
  {
  apply WTsOTsOK.
  left.
  assumption.
  }
  destruct wot as (wteq,oteq).
  rewrite wteq.
  rewrite oteq.
  left.
  rewrite eqll.
  reflexivity.
  right.
  apply INAOK.
  rewrite <- EQH.
  assumption.
  rewrite <- eqll in *.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  assumption.
  }

  replace (fold_left Astar (map fst ((subsas (snd (Iof ll)) (invs (fst (Iof ll)) wt ot), ll) :: Ainv)) (Abool true)) with 
    (fold_left Astar (map fst Ainv) (Astar (Abool true) (subsas (snd (Iof ll)) (invs (fst (Iof ll)) wt ot)))).
  {
  simpl.
  apply fold_left_g_can.
  unfold cang.
  split.
  intros.
  apply sat_comm.
  assumption.
  simpl.
  intros.
  apply sat_perm with (l:=l0);
  try tauto.
  cnj_.
  repeat php_.
  apply sat_comm.
  apply sat_plus with None None; cnj_; repeat php_.
  apply None_op.
  }
  reflexivity.
  }
  exists.
  {
  exists.
  {
  unfold injph.
  unfold inj.
  intros.
  assert (pxN: forall x1, fold_left phplus (map pof (updl T id
   (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock), O1, C1, id)))
   (phplus (phplus Pinv p2) Pleak) x1 <> None ->
   fold_left phplus (map pof T) (phplus Pinv Pleak) x1 <> None).
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll x0).
  rewrite <- e.
  rewrite LOCKED.
  apply some_none.
  rewrite <- EQH.
  assumption.
  assumption.
  }
  apply INJ;
  try apply pxN;
  try assumption.
  }
  exists. assumption.
  exists.
  {
  split.
  intros.
  apply LOCs.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e.
  rewrite LOCKED.
  apply some_none.
  rewrite <- EQH.
  assumption.
  assumption.
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e.
  rewrite EQh1.
  rewrite LOCK.
  apply some_none.
  rewrite EQH.
  apply LOCs.
  assumption.
  assumption.
  }
  intros.
  apply INOB' in IN.
  apply OBsOK in IN.
  destruct IN as (l',(EQl',pl')).
  exists l', EQl'.
  destruct ((location_eq_dec Z.eq_dec) ll l').
  rewrite <- e.
  rewrite EQh1.
  rewrite LOCK.
  apply some_none.
  rewrite EQH;
  assumption.
  }
  exists.
  {
  exists.
  {
  intros.

  assert (tmp: Lof l0 = Aof l0 /\
        Pof l0 = false /\
        Xof l0 = None /\
        (h (Aof l0) <> Some 1%Z -> In (Oof l0) (concat (map oof T)))).
  {
  apply LOCKOK.
  destruct ((location_eq_dec Z.eq_dec) l0 ll).
  rewrite e.
  right.
  exists wt, ot.
  left.
  assumption.
  rewrite EQH in LOCK0.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  }
  destruct tmp as (ll0,(pl0,(ninl0,inl0))).
  split.
  assumption.
  split.
  assumption.
  split.
  assumption.
  intros.
  unfold upd in H.
  destruct (Z.eq_dec (Aof l0) ([[l]])).
  contradiction.
  apply inl0 in H.
  rewrite <- flat_map_concat_map in H.
  apply in_flat_map in H.
  destruct H as (x,(INx,INl0)).
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (Release l, tx, phplus p1 p2, O, ghplus C1 C2)).
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  inversion EQX.
  exists (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock), O1, C1, id).
  split.
  apply in_updl_eq.
  exists (Release l, tx, phplus p1 p2, O, ghplus C1 C2).
  tauto.
  unfold oof.
  simpl.
  unfold oof in INl0.
  simpl in INl0.
  rewrite H3 in INl0.

  assert (INl1: In (Oof l0) (Oof ll::O1)).
  {
  apply Permutation_in with O; try assumption.
  }
  
  destruct INl1 as [INl1|INl1].
  rewrite <- eqll in *.
  unfold Aof in n.
  rewrite INl1 in n.
  contradiction.
  assumption.
  exists (x1, x2, x3, x4, x5, x6).
  split.
  apply in_updl_neq.
  omega.
  assumption.
  assumption.
  }
  split.
  {
  intros.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) ([[l]])).
  split.
  reflexivity.
  assert (CO: ll = l0).
  {
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  assumption.
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite <- EQH.
  rewrite ULOCK.
  apply some_none.
  assumption.
  omega.
  }
  rewrite <- CO in ULOCK.
  rewrite LOCK1 in ULOCK.
  inversion ULOCK.
  rewrite EQH in ULOCK.
  apply ULOCKOK in ULOCK.
  destruct ULOCK as (U1,U2).
  split.
  assumption.
  unfold not.
  intros.
  apply U2.
  rewrite <- flat_map_concat_map in *.
  apply in_flat_map in H.
  destruct H as (x,(INx,INl0)).
  unfold updl in INx.
  apply in_map_iff in INx.
  destruct INx as ((x0,id'),(EQx0,INx0)).
  simpl in *.
  destruct (Z.eq_dec id' id).
  assert (EQA: x0 = (Release l, tx, phplus p1 p2, O, ghplus C1 C2)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }

  rewrite EQA in *.

  rewrite <- EQx0 in INl0.
  unfold oof in INl0.
  simpl in INl0.
  apply in_flat_map.
  exists (Release l, tx, phplus p1 p2, O, ghplus C1 C2,id).
  split.
  assumption.
  unfold oof.
  simpl.
  apply Permutation_in with (Oof ll :: O1).
  apply Permutation_sym.
  assumption.
  right.
  assumption.
  rewrite <- EQx0 in INl0.
  apply in_flat_map.
  exists (x0, id').
  auto.
  unfold not.
  intros.
  rewrite <- H in n.
  omega.
  }

  intros.
  destruct ((location_eq_dec Z.eq_dec) l0 ll).
  rewrite e in UCOND.
  rewrite LOCK1 in UCOND.
  inversion UCOND.
  rewrite EQH in UCOND.
  apply UCONDOK in UCOND.
  unfold not.
  intros.
  apply UCOND.
  rewrite <- flat_map_concat_map in *.
  apply in_flat_map in H.
  destruct H as (x,(INx,INl0)).
  unfold updl in INx.
  apply in_map_iff in INx.
  destruct INx as ((x0,id'),(EQx0,INx0)).
  simpl in *.
  destruct (Z.eq_dec id' id).
  assert (EQA: x0 = (Release l, tx, phplus p1 p2, O, ghplus C1 C2)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }

  rewrite EQA in *.

  rewrite <- EQx0 in INl0.
  unfold oof in INl0.
  simpl in INl0.
  apply in_flat_map.
  exists (Release l, tx, phplus p1 p2, O, ghplus C1 C2,id).
  split.
  assumption.
  unfold oof.
  simpl.
  apply Permutation_in with (Oof ll :: O1).
  apply Permutation_sym.
  assumption.
  right.
  assumption.
  rewrite <- EQx0 in INl0.
  apply in_flat_map.
  exists (x0, id').
  auto.
  unfold not.
  intros.
  rewrite <- H in n.
  contradiction.
  }

  exists.
  {
  intros.
  unfold WTs, OBs.
  rewrite <- EQWT.
  rewrite <- EQOT.
  destruct ((location_eq_dec Z.eq_dec) ll l0) as [ll0|ll0].
  rewrite <- ll0 in ULOCKED.
  rewrite EQh1 in ULOCKED.
  rewrite LOCK in ULOCKED.
  destruct ULOCKED as [U1|U2].
  inversion U1.
  inversion U2.
  apply WTsOTsOK.
  rewrite <- EQH.
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
  {
  intros.
  inversion W4COND.
  }
  trivial.
(* ==================== x6 <> id ===========*)
  symmetry in EQ.
  inversion EQ.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF1,(WP1,SOBS2)).
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
  assert (SOBS':=W4COND).
  apply SOBS2 in SOBS'.
  destruct SOBS' as (v',(l',(IN',(INl',(EQv',(EQl',SOBS')))))).
  exists v', l', IN', INl', EQv', EQl'.

  unfold OBs, WTs.
  unfold filterb.
  unfold WTs, OBs in SOBS'.
  unfold filterb in SOBS'.
  simpl.

  rewrite W4COND in WP1.
  apply sat_wait4cond in WP1.

  destruct WP1 as (l1',(v1',(eql',(eqv',(x3v,(x3l,(lv1',(prcl',(prcv',sat'))))))))).


  assert (CO1: fold_left phplus (map pof T) (phplus Pinv Pleak) v1' = Some Cond).
  {
  apply fold_cond;
  try tauto.
  apply pofs.
  right.
  exists x3.
  split.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }

  assert (LK: fold_left phplus (map pof T) (phplus Pinv Pleak) l1' = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) l1' = Some (Locked wt ot)).
  {
  apply fold_lock_ed;
  try tauto.
  apply pofs.
  right.
  right.
  exists x3.
  exists.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  tauto.
  tauto.
  }

  assert (NEQ'lv: Aof l' <> ([[ev]])).
  {
  rewrite EQl'.
  rewrite <- eql'.
  rewrite <- eqv'.
  unfold not.
  intros.
  assert (CO: l1' = v1').
  {
  apply INJ.
  destruct LK as [LK|LK].
  rewrite LK.
  apply some_none.
  destruct LK as (wt1,(ot1,LK)).
  rewrite LK.
  apply some_none.
  rewrite CO1.
  apply some_none.
  assumption.
  }
  rewrite CO in LK.
  rewrite CO1 in LK.
  destruct LK as [LK|LK].
  inversion LK.
  destruct LK as (wt1,(ot1,LK)).
  inversion LK.
  }

  assert (NEQlv: Aof ll <> ([[ev]])).
  {
  unfold not.
  intros.
  assert (CO2: ll = v1').
  {
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite CO1.
  apply some_none.
  rewrite eqv'.
  assumption.
  }

  rewrite <- CO2 in CO1.
  rewrite LOCKED in CO1.
  inversion CO1.
  }

  assert (EQCNT: forall c tx p C, (count_occ Z.eq_dec (concat (map Aoof (updl T id (c, tx, p, O1, C, id)))) ([[ev]]))
    = count_occ Z.eq_dec (concat (map Aoof T)) ([[ev]])).
  {
  intros.
  symmetry.
  apply count_updl_eq.
  intros.
  assert (X': x' = (Release l, tx, phplus p1 p2, O, ghplus C1 C2, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold oof.
  simpl.
  destruct (Z.eq_dec (Aof ll) ([[ev]])).
  omega.
  unfold Aoof.
  simpl.
  apply eq_trans with (count_occ Z.eq_dec (map (fun x => Aofo x) (Oof ll::O1)) ([[ev]])).
  apply count_perm1.
  apply Permutation_map.
  assumption.
  apply count_occ_cons_neq.
  assumption.
  }

  assert (LOFV: xOf (fun x  => Lof x) locs ([[ev]]) = Some ([[el]])).
  {
  rewrite <- lv1'.
  rewrite <- eqv'.
  apply xOf_same;
  try tauto.
  apply in_map.
  apply LOCs.
  rewrite CO1.
  apply some_none.
  apply comp_cons.
  apply LOCs.
  rewrite CO1.
  apply some_none.
  unfold comp.
  intros.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  }

  rewrite LOFV in *.
  rewrite EQCNT.
  destruct (Z.eq_dec ([[ev]]) (Aof l')).
  rewrite e in NEQ'lv.
  contradiction.
  rewrite EQl' in *.
  rewrite eqz in *.
  rewrite eqz in *.

  assert (EQFIL: forall p O C, length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[ev]])))) (map cmdof T)) =
    length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0)
    (Some ([[ev]])))) (map cmdof (updl T id (tt, tx, p, O, C, id))))).
  {
  intros.
  unfold updl.
  rewrite map_map.
  apply filter_map_eq.
  intros.
  destruct x as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  rewrite e in *.
  assert (EQX: (a1, a2, a3, a4, a5) = (Release l, tx, phplus p1 p2, O, ghplus C1 C2)).
  eapply unique_key_eq.
  apply IN0.
  assumption.
  assumption.
  inversion EQX.
  reflexivity.
  reflexivity.
  }
  rewrite <- EQFIL.
  assumption.
Qed.


Lemma Newcond_preserves_validity:
  forall m sp h t id tx v
         (VALIDK: validk (S m) sp t h)
         (CMD : t id = Some (Newcond, tx))
         (FRE: h v = None),
    validk m sp (upd Z.eq_dec t id (Some (Val (Enum v),tx))) (upd Z.eq_dec h v (Some 0%Z)).
Proof.
  intros.
  unfold validk in VALIDK.
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
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  rewrite map_map in *.

  assert (tmp: exists p O C, In (Newcond, tx, p, O, C, id) T).
  {
  apply TOK.
  assumption.
  }

  destruct tmp as (p,(O,(C,INT))).

  assert (inp: In p (map pof T)).
  {
  apply in_map_iff.
  exists (Newcond, tx, p, O, C, id).
  tauto.
  }

  assert (inpid: In (p, id) (map (fun x0 => (pof x0, snd x0)) T)).
  {
  apply in_map_iff.
  exists (Newcond, tx, p, O, C, id).
  tauto.
  }

  assert (phpdp0il: forall p0 : pheap, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  apply phpdef_pair; try tauto.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  }

  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,SOBS1)).
  unfold wellformed in WF.
  simpl in WF.

  assert (bp: boundph p).
  {
  apply BPE.
  assumption.
  }

  assert (bg: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); try tauto.
  intros.
  apply ghpdef_pair; try tauto.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (Newcond, tx, p, O, C, id).
  tauto.
  }

  apply sat_newcond with (v:=v) in WP; try tauto.
  Focus 2.
  intros.
  assert (PH:=PH2H).
  unfold phtoh in PH.
  destruct PH as (PH,PH1).
  specialize PH with (v, r, I, L, X, M, M', P).
  unfold Aof in PH.
  unfold Aofo in PH.
  simpl in PH.
  rewrite FRE in PH.
  destruct (fold_left phplus (map (fun x => pof x) T) (phplus Pinv Pleak) (v, r, I, L, X, M, M', P)) eqn:fl.
  destruct k; try inversion PH; try contradiction.
  apply fold_None with (m:=pof) (l:=T) (b:=phplus Pinv Pleak); try tauto.
  destruct WP as (r,(X,(P,sat1))).

  exists (updl T id (Val (Enum v), tx, upd (location_eq_dec Z.eq_dec) p ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) (Some Ucond), O, C, id)).
  exists invs, (((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil)::locs), Pinv, Pleak, Ainv, Cinv, Cleak.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (NONE: forall l (EQL: Aof l = v), fold_left phplus (map pof T) (phplus Pinv Pleak) l = None).
  {
  assert (PH:=PH2H).
  unfold phtoh in PH.
  destruct PH as (PH,PH1).
  intros.
  specialize PH with l.
  rewrite EQL in PH.
  simpl in PH.
  rewrite FRE in PH.
  destruct (fold_left phplus (map (fun x => pof x) T) (phplus Pinv Pleak) l) eqn:fl.
  destruct k; try inversion PH; try contradiction.
  reflexivity.
  }

  assert (NONE': forall l (EQL: Aof l = v) p0 (IN: In p0 (map pof T)), p0 l = None).
  {
  intros.
  apply fold_None with (m:=pof) (l:=T) (b:=phplus Pinv Pleak); try tauto.
  apply NONE.
  assumption.
  }

  assert (phpdefpi: phplusdef p Pinv).
  {
  apply PHPD.
  assumption.
  }

  assert (phpdefpl: phplusdef p Pleak).
  {
  apply PHPD.
  assumption.
  }

  assert (pilN: phplus Pinv Pleak ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) = None).
  {
  apply fold_None with (m:=pof) (l:=T) (b:=phplus Pinv Pleak); try tauto.
  apply NONE.
  reflexivity.
  }

  assert (piN: Pinv ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil)  = None).
  {
  apply phplus_None with Pleak.
  assumption.
  }

  assert (plN: Pleak ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil)  = None).
  {
  apply phplus_None with Pinv.
  rewrite phplus_comm.
  assumption.
  repeat php_.
  }

  assert (NODUP1: NoDup (map snd (updl T id (Val (Enum v), tx, upd (location_eq_dec Z.eq_dec) p ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) (Some Ucond), O, C, id)))).
  {
  apply NoDup_updl.
  assumption.
  }

  assert (defl1: defl phplusdef (map (fun x0 => (pof x0, snd x0)) (updl T id
   (Val (Enum v), tx, upd (location_eq_dec Z.eq_dec) p ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) (Some Ucond), O, C, id)))).
  {
  apply defl_New with (b:=phplus Pinv Pleak) (z:=((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil)) (p:=p) (v:=Some Ucond); try tauto.
  intros.
  apply phpdef_comm.
  apply phpdef_v.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  inversion EQx.
  apply DEFL with id (snd x); try tauto.
  omega.
  inm_.
  apply NONE'.
  reflexivity.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  inversion EQy.
  apply in_map_iff.
  exists y.
  tauto.
  apply NONE.
  reflexivity.
  }

  assert (phpdefpil: phplusdef p (phplus Pinv Pleak)).
  {
  apply phpdef_pair; try tauto;
  apply PHPD; try tauto.
  }

  assert (phpdefp0il: forall p0, In p0 (map pof (updl T id
    (Val (Enum v), tx, upd (location_eq_dec Z.eq_dec) p ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) (Some Ucond), O, C, id))) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  unfold updl.
  rewrite map_map.
  intros.
  apply in_map_iff in H.
  destruct H as (x0,(EQ,IN)).
  destruct (Z.eq_dec (snd x0) id).
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  apply phpdef_v; try tauto.
  apply phpdp0il.
  rewrite <- EQ.
  inm_.
  }

  assert (ULOCK: fold_left phplus (map pof (updl T id (Val (Enum v), tx, upd (location_eq_dec Z.eq_dec) p ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) (Some Ucond), O, C, id))) (phplus Pinv Pleak)
    ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) = Some Ucond).
  {
  apply fold_ucond; try tauto.
  apply pofs.
  right.
  exists (upd (location_eq_dec Z.eq_dec) p ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) (Some Ucond)).
  unfold updl.
  rewrite map_map.
  exists.
  apply in_map_iff.
  exists (Newcond, tx, p, O, C, id).
  simpl.
  rewrite eqz.
  tauto.
  repeat dstr_.
  }

  assert (EQH: forall z (NEQ: z <> ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil)), 
    fold_left phplus (map pof (updl T id (Val (Enum v), tx, upd (location_eq_dec Z.eq_dec) p ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) (Some Ucond), O, C, id))) (phplus Pinv Pleak) z
    = fold_left phplus (map pof T) (phplus Pinv Pleak) z).
  {
  intros.
  apply eq_heap with (z:=((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil))(p:=p)(v:=Some Ucond); try tauto.
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
  exists (Newcond, tx, p, O, C, id).
  tauto.
  apply in_map_iff.
  exists x1.
  tauto.
  apply fold_None with (m:=pof) (l:=T) (b:=phplus Pinv Pleak); try tauto.
  apply NONE.
  reflexivity.
  left.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ,IN)).
  inversion EQ.
  apply in_map_iff.
  exists x1; tauto.
  apply phpdef_v; try tauto.
  unfold not.
  intros.
  rewrite H in NEQ.
  contradiction.
  }

  assert (NINL: ~ In ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) locs).
  {
  unfold not.
  intros.
  apply LOCs in H.
  rewrite NONE in H.
  contradiction.
  reflexivity.
  }

  assert (EQG: map (fun x0 => (gof x0, snd x0))
    (updl T id (Val (Enum v), tx, upd (location_eq_dec Z.eq_dec) p ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) (Some Ucond), O, C, id)) =
    map (fun x0 => (gof x0, snd x0)) T).
  {
  unfold updl.
  rewrite map_map.
  unfold gof.
  simpl.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  rewrite e.

  assert (EQA: a = (Newcond, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }

  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQG': map gof (updl T id (Val (Enum v), tx,
    upd (location_eq_dec Z.eq_dec) p ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil)
   (Some Ucond), O, C, id)) = map gof T).
  {
  unfold updl.
  rewrite map_map.
  unfold gof.
  simpl.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).

  assert (EQA: a = (Newcond, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }

  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQFIL: forall x p, length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) x))
    (map cmdof (updl T id (Val (Enum v), tx, p, O, C, id)))) = 
    length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) x)) (map cmdof T))).
  {
  intros.
  unfold updl.
  rewrite map_map.
  apply filter_map_eq.
  intros.
  destruct x0 as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  rewrite e in *.
  assert (EQX: (a1, a2, a3, a4, a5) = (Newcond, tx, p, O, C)).
  apply unique_key_eq with T a6; try tauto.
  rewrite e.
  assumption.
  rewrite e.
  assumption.
  inversion EQX.
  reflexivity.
  reflexivity.
  }

  assert (EQWT: forall l0, WTs l0 (map cmdof (updl T id (Val (Enum v), tx, upd (location_eq_dec Z.eq_dec) p
   ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) (Some Ucond), O, C, id)))
   (((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) :: locs) =
   WTs l0 (map cmdof T) locs).
  {
  unfold WTs.
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.
  destruct (xOf (fun x1 => Lof x1) locs x) eqn:xof.
  assert (xof1: xOf (fun x1 => Lof x1)
    (((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) :: locs) x = Some z).
  {
  apply xof_mon.
  assumption.
  unfold not.
  intros.
  apply LOCs in H.
  destruct l' as (((((((x1,x2),x3),x4),x5),x6),x7),x8).
  unfold Aof in EQ.
  unfold Aofo in EQ.
  simpl in EQ.
  inversion EQ.
  rewrite EQ in H.
  rewrite NONE in H.
  contradiction.
  reflexivity.
  }

  rewrite xof1.
  destruct (Z.eq_dec x (Aof l0)).
  reflexivity.
  destruct (Z.eq_dec z (Aof l0)).
  Focus 2.
  reflexivity.
  apply EQFIL.
  simpl.
  unfold Aof.
  unfold Aofo.
  unfold Lof.
  unfold Oof.
  unfold Lof.
  unfold Lofo.
  simpl.
  destruct (Z.eq_dec x v).
  destruct (Z.eq_dec x (fst (fst (fst (fst (fst (fst (fst l0)))))))).
  reflexivity.
  destruct (Z.eq_dec v (fst (fst (fst (fst (fst (fst (fst l0)))))))).
  rewrite e.
  unfold updl.
  rewrite map_map.
  destruct (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map (fun x0 => cmdof (if Z.eq_dec (snd x0) id
    then (Val (Enum v), tx, upd (location_eq_dec Z.eq_dec) p ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) (Some Ucond), O, C, id) else x0)) T)) eqn:fil.
  reflexivity.
  assert (CO: In c (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map (fun x0 => cmdof (if Z.eq_dec (snd x0) id
    then (Val (Enum v), tx, upd (location_eq_dec Z.eq_dec) p ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) (Some Ucond), O, C, id) else x0)) T))).
  {
  rewrite fil.
  left.
  reflexivity.
  }
  apply filter_In in CO.
  destruct CO as (IN,CO).
  unfold ifb in CO.
  destruct (opZ_eq_dec (waiting_for_cond c) (Some v)).
  Focus 2.
  inversion CO.
  destruct c; inversion e1.
  {
  apply in_map_iff in IN.
  destruct IN as (x1,(EQx,INx)).
  destruct x1 as (x1,id').
  simpl in *.
  destruct (Z.eq_dec id' id).
  unfold cmdof in EQx.
  inversion EQx.
  unfold cmdof in EQx.
  destruct x1 as ((((x1,x2),x3),x4),x5).
  simpl in *.
  rewrite EQx in INx.
  assert (tmp:=INx).
  apply SOBS in tmp.
  destruct tmp as (WF1,(SAT1,REST)).
  apply sat_wait4cond in SAT1.
  destruct SAT1 as (l3,(v1,(eql1,(eqv1,(x3v,(x3l,(lov1,rest))))))).
  destruct v1 as (((((((a1,a2),a3),a4),a5),a6),a7),a8).
  unfold Aof in eqv1.
  unfold Aofo in eqv1.
  simpl in eqv1.
  rewrite eqv1 in x3v.
  rewrite H0 in x3v.
  rewrite NONE' in x3v.
  inversion x3v.
  reflexivity.
  apply in_map_iff.
  exists (Waiting4cond v0 l1, x2, x3, x4, x5, id'). tauto.
  }
  {
  apply in_map_iff in IN.
  destruct IN as (x1,(EQx,INx)).
  destruct x1 as (x1,id').
  simpl in *.
  destruct (Z.eq_dec id' id).
  unfold cmdof in EQx.
  inversion EQx.
  unfold cmdof in EQx.
  destruct x1 as ((((x1,x2),x3),x4),x5).
  simpl in *.
  rewrite EQx in INx.
  assert (tmp:=INx).
  apply SOBS in tmp.
  destruct tmp as (WF1,(SAT1,REST)).
  apply sat_WasWaiting4cond in SAT1.
  destruct SAT1 as (ll,(lv,(eqll,(eqlv,(lofv,(pl,(pv,(prcl,SAT1)))))))).
  destruct lv as (((((((a1,a2),a3),a4),a5),a6),a7),a8).
  unfold Aof in eqlv.
  unfold Aofo in eqlv.
  simpl in eqlv.
  rewrite eqlv in pv.
  rewrite H0 in pv.
  rewrite NONE' in pv.
  inversion pv.
  reflexivity.
  apply in_map_iff.
  exists (WasWaiting4cond v0 l1, x2, x3, x4, x5, id'). auto.
  }
  reflexivity.
  unfold Lof in xof.
  unfold Oof in xof.
  unfold Lofo in xof.
  rewrite xof.
  reflexivity.
  }

  assert (EQCNT: forall p x, count_occ Z.eq_dec (concat (map Aoof (updl T id (Val (Enum v), tx, p, O, C, id)))) x =
    count_occ Z.eq_dec (concat (map Aoof T)) x).
  {
  intros.
  symmetry.
  apply count_updl_eq.
  intros.
  assert (X': x' = (Newcond, tx, p, O, C, id)).
  apply in_elem with T; try assumption.
  rewrite X'.
  reflexivity.
  }

  assert (EQOT: forall l0 p, OBs l0 (concat (map Aoof (updl T id
    (Val (Enum v), tx, p, O, C, id)))) (((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) :: locs) =
    OBs l0 (concat (map Aoof T)) locs).
  {
  unfold OBs.
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.

  destruct (xOf (fun x1 => Lof x1) locs x) eqn:xof.
  assert (xof1: xOf (fun x1 => Lof x1)
    (((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) :: locs) x = Some z).
  {
  apply xof_mon.
  assumption.
  unfold not.
  intros.
  apply LOCs in H.
  destruct l' as (((((((x1,x2),x3),x4),x5),x6),x7),x8).
  unfold Aof in EQ.
  unfold Aofo in EQ.
  simpl in EQ.
  inversion EQ.
  rewrite EQ in H.
  rewrite NONE in H.
  contradiction.
  reflexivity.
  }

  rewrite xof1.
  destruct (Z.eq_dec x (Aof l0)).
  reflexivity.
  destruct (Z.eq_dec z (Aof l0)).
  Focus 2.
  reflexivity.
  apply EQCNT.
  simpl.
  unfold Aof.
  unfold Aofo.
  unfold Lof.
  unfold Oof.
  unfold Lofo.
  simpl.
  destruct (Z.eq_dec x v).
  destruct (Z.eq_dec x (fst (fst (fst (fst (fst (fst (fst l0)))))))).
  reflexivity.
  destruct (Z.eq_dec v (fst (fst (fst (fst (fst (fst (fst l0)))))))).
  rewrite e.
  apply count_occ_not_In.
  unfold not.
  rewrite <- flat_map_concat_map.
  intros NIN.
  apply in_flat_map in NIN.
  destruct NIN as (x1,(INx,EQ1)).
  destruct x1 as (((((x1',x2'),x3'),x4'),x5'),x6').
  unfold Aoof in EQ1.
  simpl in EQ1.
  apply in_map_iff in EQ1.
  destruct EQ1 as (y,(EQy,INy)).
  unfold updl in INx.
  apply in_map_iff in INx.
  destruct INx as ((y1,id'),(EQy1,INy1)).
  simpl in *.

  assert (INOC: In y (concat (map oof T))).
  {
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists (y1,id').
  destruct (Z.eq_dec id' id).
  inversion EQy1.
  assert (EQA: y1 = (Newcond, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e1.
  assumption.
  }
  rewrite EQA.
  rewrite <- H3 in INy.
  rewrite e1.
  tauto.
  inversion EQy1.
  rewrite H0 in INy1.
  rewrite <- H1.
  tauto.
  }

  apply OBsOK in INOC.
  destruct INOC as (ly,(EQly,ply)).

  destruct ly as (((((((a1',a2'),a3'),a4'),a5'),a6'),a7'),a8').
  unfold Oof in EQly.
  simpl in EQly.
  rewrite EQly in ply.
  rewrite NONE in ply.
  contradiction.
  assumption.
  reflexivity.
  unfold Lof in xof.
  unfold Lofo in xof.
  unfold Oof in xof.
  rewrite xof.
  reflexivity.
  }

  assert (EQO: forall p, map oof (updl T id (Val (Enum v), tx, p, O, C, id)) = map oof T).
  {
  unfold updl.
  intros.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (a,id').
  simpl.
  destruct (Z.eq_dec id' id).
  assert (EQA: a = (Newcond, tx, p, O, C)).
  {
  apply unique_key_eq with T id; try tauto.
  rewrite <- e.
  assumption.
  }
  rewrite EQA.
  reflexivity.
  reflexivity.
  }

  assert (bpupd: boundph (upd (location_eq_dec Z.eq_dec) p
    (v, r, v, X, P, (0%Z, nil), (0%Z, nil), nil) (Some Ucond))).
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  rewrite EQG.
  rewrite EQG'.
  rewrite EQO.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  apply red_Newcond; try assumption.
  }
  exists.
  {
  destruct SPUR as (SPUR0,SPUR).
  unfold spur_ok.
  split.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  rewrite WASW in EQx.
  inversion EQx.
  eapply SPUR0 with (c:=c).
  apply in_map_iff.
  exists x.
  auto.
  apply WASW.
  }
  intros.
  assert (NEQv0: v0 <> (v, r, v, X, P, (0%Z, nil), (0%Z, nil), nil)).
  {
  unfold not.
  intros CO.
  rewrite CO in CONDv.
  rewrite ULOCK in CONDv.
  inversion CONDv.
  }
  rewrite EQH in CONDv.
  apply SPUR in CONDv.
  destruct CONDv as (a,(b,(c,d))).
  exists a, b.
  exists.
  destruct (location_eq_dec Z.eq_dec a (v, r, v, X, P, (0%Z, nil), (0%Z, nil), nil)).
  rewrite e in *.
  rewrite NONE in c.
  destruct c as [c|c].
  inversion c.
  destruct c as (wt,(ot,c)).
  inversion c.
  reflexivity.
  rewrite EQH; try assumption.
  assumption.
  assumption.
  }
  exists.
  {
  exists. assumption.
  exists. tauto.
  exists.
  unfold updl.
  rewrite map_map.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ,IN)).
  destruct (Z.eq_dec (snd x1) id).
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  split.
  apply phpdef_v; try tauto.
  apply phpdef_v; try tauto.
  apply PHPD.
  rewrite <- EQ.
  inm_.
  split.
  unfold updl.
  rewrite map_map.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ,IN)).
  destruct (Z.eq_dec (snd x1) id).
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  assumption.
  rewrite <- EQ.
  apply BPE.
  inm_.
  split. tauto.
  split. tauto.
  split. tauto.
  split.
  unfold boundph.
  intros.
  assert (EQ:=H).
  rewrite EQH in H.
  unfold boundph in BPT.
  eapply BPT.
  apply H.
  unfold not.
  intros.
  rewrite H0 in EQ.
  rewrite ULOCK in EQ.
  inversion EQ.

  assert (PH:=PH2H).
  destruct PH as (PH,PH1).
  split.
  intros.
  specialize PH with l.

  destruct ((location_eq_dec Z.eq_dec) ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil) l).
  rewrite <- e in *.
  rewrite ULOCK.
  unfold upd.
  rewrite eqz.
  apply some_none.
  rewrite EQH.
  unfold upd.
  destruct (Z.eq_dec (Aof l) v).
  rewrite e in PH.
  destruct (fold_left phplus (map pof T) (phplus Pinv Pleak) l) eqn:fl0.
  rewrite FRE in PH.
  destruct k; try inversion PH; try contradiction.
  trivial.
  assumption.
  congruence.
  intros.
  unfold upd.
  destruct (Z.eq_dec z v).
  specialize NONE0 with ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil).
  symmetry in e.
  apply NONE0 in e.
  rewrite ULOCK in e.
  inversion e.
  apply PH1.
  intros.
  rewrite <- EQH.
  apply NONE0.
  assumption.
  unfold not.
  intros.
  rewrite H in EQ.
  unfold Aof in EQ.
  rewrite <- EQ in n.
  contradiction.
  }

  exists.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  assumption.
  exists.
  intros.
  apply upd_updl. exists (Newcond, tx, p, O, C). tauto. assumption.
  exists. assumption.
  exists.
  exists. assumption.
  exists.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) l ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil)).
  rewrite e in IN.
  apply AinvOK in IN.
  rewrite NONE in IN.
  destruct IN as (CO,IN).
  inversion CO.
  reflexivity.
  rewrite EQH.
  unfold upd.
  destruct (Z.eq_dec (Aof l) v).
  apply AinvOK in IN.
  destruct IN as (fl,hl).
  destruct l as (((((((x1',x2'),x3'),x4'),x5'),x6'),x7'),x8').
  unfold Aof in e.
  unfold Aofo in e.
  simpl in e.
  rewrite e in fl.
  rewrite NONE in fl.
  inversion fl.
  reflexivity.
  apply AinvOK.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  rewrite EQWT.
  rewrite EQOT.
  apply INAOK.
  rewrite <- EQH.
  assumption.
  unfold not.
  intros.
  rewrite H in LOCK.
  rewrite ULOCK in LOCK.
  inversion LOCK.
  unfold upd in NOTHELD.
  destruct ((location_eq_dec Z.eq_dec) l ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil)).
  rewrite e in LOCK.
  rewrite ULOCK in LOCK.
  inversion LOCK.
  rewrite EQH in LOCK.
  destruct (Z.eq_dec (Aof l) v).
  destruct l as (((((((x1,x2),x3),x4),x5),x6),x7),x8).
  unfold Aof in e.
  unfold Aofo in e.
  simpl in e.
  rewrite e in LOCK.
  rewrite NONE in LOCK.
  inversion LOCK.
  reflexivity.
  assumption.
  assumption.
  }
  assumption.
  exists.
  {
  exists.
  {
  unfold injph.
  unfold inj.
  intros.
  destruct ((location_eq_dec Z.eq_dec) x1 ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil)).
  destruct ((location_eq_dec Z.eq_dec) x2 ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil)).
  rewrite e, e0.
  reflexivity.
  rewrite EQH in px2.
  destruct x2 as (((((((x1',x2),x3),x4),x5),x6),x7),x8).
  rewrite e in H.
  unfold Aof in H.
  unfold Aofo in H.
  simpl in H.
  inversion H.
  rewrite <- H0 in px2.
  rewrite NONE in px2.
  contradiction.
  reflexivity.
  assumption.

  destruct ((location_eq_dec Z.eq_dec) x2 ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil)).
  rewrite EQH in px1.
  destruct x1 as (((((((x1,x2'),x3),x4),x5),x6),x7),x8).
  rewrite e in H.
  unfold Aof in H.
  unfold Aofo in H.
  simpl in H.
  inversion H.
  rewrite H0 in px1.
  rewrite NONE in px1.
  contradiction.
  reflexivity.
  assumption.

  rewrite EQH in px1.
  rewrite EQH in px2.
  apply INJ; try assumption.
  assumption.
  assumption.
  }
  split.
  {
  unfold lcomp.
  simpl.
  intros.
  destruct IN as [EQ|IN].
  rewrite <- EQ.
  left.
  reflexivity.
  right.
  apply LCOM.
  assumption.
  }
  exists.
  {
  split.
  intros.
  destruct ((location_eq_dec Z.eq_dec) l ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil)).
  rewrite e.
  auto.
  rewrite EQH in H.
  right.
  apply LOCs; assumption.
  assumption.
  intros.
  destruct H as [EQ|IN].
  rewrite <- EQ.
  rewrite ULOCK.
  apply some_none.
  destruct ((location_eq_dec Z.eq_dec) l ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil)).
  rewrite e in IN.
  contradiction.
  rewrite EQH.
  apply LOCs.
  assumption.
  assumption.
  }
  intros.
  apply OBsOK in IN.
  destruct IN as (l,(EQl,pl)).
  exists l.
  exists EQl.
  rewrite EQH.
  assumption.
  unfold not.
  intros.
  rewrite H in pl.
  rewrite NONE in pl.
  contradiction.
  reflexivity.
  }
  exists.
  {
  exists.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) l ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil)).
  {
  rewrite e in LOCK.
  rewrite ULOCK in LOCK.
  destruct LOCK as [CO|CO].
  inversion CO.
  destruct CO as (wt,(ot,CO)).
  destruct CO as [CO|CO].
  inversion CO.
  inversion CO.
  }
  replace (upd Z.eq_dec h v (Some 0%Z) (Aof l)) with (h (Aof l)).
  apply LOCKOK.
  rewrite <- EQH.
  assumption.
  assumption.
  unfold upd.
  destruct (Z.eq_dec (Aof l) v).
  destruct l as (((((((x1,x2),x3),x4),x5),x6),x7),x8).
  unfold Aof in e.
  unfold Aofo in e.
  simpl in e.
  rewrite e in LOCK.
  rewrite EQH in LOCK.
  rewrite NONE in LOCK.
  destruct LOCK as [CO|CO].
  inversion CO.
  destruct CO as (wt,(ot,CO)).
  destruct CO as [CO|CO].
  inversion CO.
  inversion CO.
  rewrite e in n.
  reflexivity.
  rewrite e in n.
  assumption.
  reflexivity.
  }
  split.
  {
  intros.
  unfold upd.
  destruct (Z.eq_dec (Aof l) v).
  destruct ((location_eq_dec Z.eq_dec) l ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil)).
  rewrite e0 in ULOCK0.
  rewrite ULOCK in ULOCK0.
  inversion ULOCK0.
  rewrite EQH in ULOCK0.
  rewrite NONE in ULOCK0.
  inversion ULOCK0.
  assumption.
  assumption.
  apply ULOCKOK with wt ot.
  rewrite <- EQH.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  }
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) l ((v, r, v, X, P, (0%Z, nil), (0%Z, nil), nil))).
  unfold not.
  intros.
  apply OBsOK in H.
  rewrite e in H.
  destruct H as (l',(EQl',pl')).
  rewrite NONE in pl'.
  contradiction.
  unfold Aof.
  unfold Oof in *.
  rewrite EQl'.
  reflexivity.
  apply UCONDOK.
  rewrite <- EQH; assumption.
  }
  }
  exists.
  {
  intros.
  rewrite EQWT.
  rewrite EQOT.
  destruct ((location_eq_dec Z.eq_dec) l ((v,r,v,X,P),(0%Z,nil),(0%Z,nil),nil)).
  rewrite e in *.
  rewrite ULOCK in ULOCKED.
  destruct ULOCKED as [U|U];
  inversion U.
  apply WTsOTsOK.
  rewrite <- EQH.
  assumption.
  assumption.
  }

  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x0,(EQ0,IN0)).
  destruct x0 as (x0,id').
  simpl in *.
  destruct (Z.eq_dec id' id).
  {
  (* ==================== id' = id ===========*)
  symmetry in EQ0.
  inversion EQ0.
  exists. trivial.
  exists.
  eapply sat_weak_imp1; try assumption.
  apply sat1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  }
  (* ==================== id' <> id ===========*)
  inversion EQ0.
  rewrite H0 in *.
  assert (IN2:=IN0).
  apply SOBS in IN0.
  destruct IN0 as (WF1,(SAT1,SOBS1')).
  exists. trivial.
  exists.

  assert (bx3: boundph p0).
  {
  apply BPE.
  apply in_map_iff.
  exists (c, tx0, p0, O0, C0, id').
  split. reflexivity. assumption.
  }

  assert (bx5: boundgh C0).
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
  exists (c, tx0, p0, O0, C0, id').
  split. reflexivity. assumption.
  }

  eapply sat_weak_imp1; try assumption.
  apply SAT1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.

  intros.
  apply SOBS1' in W4COND.
  destruct W4COND as (v',(l',(inv',(inl',(eqv',(eql',sobs')))))).
  exists v', l'.
  exists. tauto.
  exists. tauto.
  exists eqv', eql'.
  rewrite EQWT.
  rewrite EQOT.
  assumption.
Qed.


Lemma Wait_preserves_validity:
  forall m sp h t id v l tx
         (CMD: t id = Some (Wait v l, tx))
         (VALID: validk (S m) sp t h),
    validk m sp (upd Z.eq_dec t id (Some (Waiting4cond v l, tx)))(upd Z.eq_dec h ([[l]]) (Some 1%Z)).
Proof.
  intros.
  unfold validk in VALID.
  destruct VALID as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
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
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.

  rewrite map_map in *.
  unfold validk.
  assert (tmp: exists p O C, In (Wait v l, tx, p, O, C, id) T).
  apply TOK.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.

  apply sat_wait in WP.
  destruct WP as (lv,(ll,(p1,(p2,(wt,(ot,(C1,(C2,(O1,(eql,(eqv,(O1eq,(BP1,(BP2,(phpdp1p2,(p1p2,(ghpdefC1C2,(C1C2,(p1l,(p1v,(p2inv,(prcv,(prcl,(NEQvl,(Lvl,(SAFE_OBS,SATp1)))))))))))))))))))))))))).
  rewrite <- eql in *.
  subst.

  exists (updl T id (Waiting4cond v l, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock), O1, C1, id)).
  exists invs, locs.
  exists (phplus Pinv p2), Pleak.
  exists ((subsas (snd (Iof ll))(invs (fst (Iof ll)) (upd Z.eq_dec wt (Aof lv) (S (wt (Aof lv)))) ot),ll)::Ainv).
  exists (ghplus Cinv C2), Cleak.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (inp1p2id: In (phplus p1 p2, id) (map (fun x => (pof x, snd x)) T)).
  {
  apply in_map_iff.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  }

  assert (inp1p2: In (phplus p1 p2) (map pof T)).
  {
  apply in_map_iff.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  }
  
  assert (Pl: (phplus p1 p2) ll = Some (Locked wt ot)).
  {
  apply phplus_locked.
  assumption.
  assumption.
  }

  assert (phpdefp0pi: forall p0 : pheap, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros p0 IN.
  apply PHPD in IN.
  apply phpdef_pair;
  tauto.
  }

  assert (COND: fold_left phplus (map pof T) (phplus Pinv Pleak) lv = Some Cond).
  {
  eapply fold_cond with (m:=pof) (l:=T);
  try tauto.
  apply pofs.
  right.
  exists (phplus p1 p2).
  exists.
  assumption.
  unfold pof.
  simpl.
  apply phplus_Cond.
  assumption.
  assumption.
  }

  assert (LOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked wt ot)).
  {
  apply fold_locked;
  try tauto.
  apply pofs.
  right.
  exists (phplus p1 p2).
  exists.
  assumption.
  assumption.
  }

  assert (LOCK: fold_left phplus (map pof (updl T id (Waiting4cond v l, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock), O1, C1, id))) (phplus (phplus Pinv Pleak) p2) ll = Some Lock).
  {
  apply lock_Wait with p1;
  try tauto.
  apply pofs.
  exists wt, ot.
  left.
  assumption.
  }

  assert (tmp: Lof ll = Aof ll /\
        Pof ll = false /\
        Xof ll = None /\
        (h (Aof ll) <> Some 1%Z -> In (Oof ll) (concat (map oof T)))).
  {
  apply LOCKOK.
  right.
  exists wt, ot.
  tauto.
  }

  destruct tmp as (lll,(plf,(ninrl,linobs))).

  assert (p2Pinv: phplusdef p2 Pinv).
  {
  apply phpdef_assoc_mon with p1.
  assumption.
  apply PHPD.
  apply in_map_iff.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  }

  assert (wot: wt = filterb (xOf (fun x => Lof x) locs) (Aof ll) (fun v => length (filter
           (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
           (map cmdof T))) /\
           ot = filterb (xOf (fun x => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))).
  {
  apply WTsOTsOK.
  left.
  assumption.
  }

  destruct wot as (wteq,oteq).

  assert (EQW: (fun a : Z => if Z.eq_dec a ([[v]]) then S (wt (Aof lv)) else wt a) = 
    (filterb (xOf (fun x => Lof x) locs) (Aof ll) (fun v0 => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0)))
    (map cmdof (updl T id (Waiting4cond v l, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock), O1, C1, id))))))).
  {
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x ([[v]])) as [xv|xv].
  rewrite xv.
  rewrite wteq.
  simpl.
  unfold filterb.
  rewrite <- eqv.
  destruct (xOf (fun x0 => Lof x0) locs (Aof lv)) eqn:XOF.
  assert (XOFE: xOf (fun x => Lof x) locs (Aof lv) = Some (Lof lv)).
  {
  assert (INlv: In lv locs).
  {
  apply LOCs.
  rewrite COND.
  apply some_none.
  }
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
  rewrite XOF in XOFE.
  inversion XOFE.
  rewrite H0 in *.

  destruct (Z.eq_dec (Aof lv) (Aof ll)).
  assert (CO: lv = ll).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }
  contradiction.
  rewrite <- filter_updl_dec.
  rewrite Lvl.
  rewrite eqz.
  rewrite eqz.
  reflexivity.
  assumption.
  unfold cmdof.
  simpl.
  rewrite eqv.
  destruct (opZ_eq_dec (Some ([[v]])) (Some ([[v]]))).
  reflexivity.
  contradiction.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  exists.
  unfold elem.
  apply filter_In.
  split.
  assumption.
  simpl.
  apply Z.eqb_eq.
  reflexivity.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some (Aof lv))).
  inversion e.
  reflexivity.
  assert (CO: ~ exists x (IN: In x locs), Aof x = Aof lv).
  {
  eapply xOf_exists1.
  apply XOF.
  }
  exfalso.
  apply CO.
  exists lv.
  exists.
  apply LOCs.
  rewrite COND.
  apply some_none.
  reflexivity.

  rewrite wteq.
  simpl.
  apply filterbv_updl_eq.
  unfold ifb.
  split.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec (Some ([[v]])) (Some x)).
  inversion e.
  omega.
  reflexivity.
  intros.
  assert (X':x' = (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  inversion X'.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some x)).
  inversion e.
  reflexivity.
  }

  assert (EQO: ot = (filterb (xOf (fun x => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof (updl T id
    (Waiting4cond v l, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock), O1, C1, id))))))).
  {
  rewrite oteq.
  apply filterb_updl_obs_eq.
  intros.
  assert (X':x' = (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  inversion X'.
  unfold Aof.
  unfold Aoof.
  simpl.
  rewrite count_map_perm with (l2:=Oof ll::O1).
  simpl.
  destruct (Z.eq_dec (Aofo (Oof ll)) v0).
  symmetry in e.
  contradiction.
  reflexivity.
  assumption.
  }

  assert (LOCKU: fold_left phplus (map pof (updl T id (Waiting4cond v l, tx,
                 upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock), O1, C1, id))) (phplus (phplus Pinv Pleak) p2) ll = Some Lock).
  {
  apply lock_Wait with p1;
  try tauto.
  apply pofs.
  exists wt, ot.
  left.
  assumption.
  }
  assert (EQH: forall l0 (NEQ: ll <> l0), fold_left phplus (map pof (updl T id (Waiting4cond v l, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock),
    O1, C1, id))) (phplus (phplus Pinv Pleak) p2) l0 = 
    fold_left phplus (map pof T) (phplus Pinv Pleak) l0).
  {
  intros.
  apply eq_heap_Wait with (z:=ll) (p1:=p1); try tauto.
  apply pofs.
  exists wt, ot.
  left.
  assumption.
  }

  assert (SAFE': safe_obs lv (length (filter (fun c0 : cmd => ifb
   (opZ_eq_dec (waiting_for_cond c0) (Some ([[v]]))))
   (map cmdof (updl T id (Waiting4cond v l, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock), O1, C1, id)))))
   (count_occ Z.eq_dec (concat (map Aoof (updl T id (Waiting4cond v l, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock), O1, C1, id)))) ([[v]])) = true).
  {
  unfold filterb in EQW.
  apply equal_f with (x:=([[v]])) in EQW.
  rewrite eqz in EQW.
  destruct (xOf (fun x  => Lof x) locs ([[v]])) eqn:XOF.
  rewrite <- eqv in *.
  assert (XOFE: xOf (fun x => Lof x) locs (Aof lv) = Some (Lof lv)).
  {
  assert (INlv: In lv locs).
  {
  apply LOCs.
  rewrite COND.
  apply some_none.
  }
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
  assert (XOF1:=XOF).
  rewrite XOFE in XOF1.
  inversion XOF1.
  rewrite <- H0 in *.

  destruct (Z.eq_dec (Aof lv) (Aof ll)).
  inversion EQW.
  rewrite <- Lvl in EQW.
  rewrite eqz in EQW.
  rewrite filter_filter_eq with (f2:=(fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0)
    (Some ([[v]]))))) in EQW.
  rewrite eqv in *.
  rewrite eql in *.
  rewrite <- EQW.
  unfold filterb in EQO.
  apply equal_f with (x:=([[v]])) in EQO.
  destruct (Z.eq_dec ([[v]]) ([[l]])).
  contradiction.
  rewrite XOF in EQO.
  rewrite <- Lvl in EQO.
  rewrite eqz in EQO.
  rewrite <- EQO.
  assumption.
  intros.
  rewrite eqv.
  reflexivity.
  inversion EQW.
  }

  assert (INp1p2: In (phplus p1 p2) (map pof T)).
  {
  apply in_map_iff.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  tauto.
  }

  assert (phpdefp12ip12l: phplusdef (phplus p1 p2) Pinv /\ phplusdef (phplus p1 p2) Pleak).
  {
  apply PHPD.
  tauto.
  }

  assert (phpdefp1ip2i: phplusdef p1 Pinv /\ phplusdef p2 Pinv).
  {
  apply phpdef_dist;
  tauto.
  }

  assert (phpdefp1lp2l: phplusdef p1 Pleak /\ phplusdef p2 Pleak).
  {
  apply phpdef_dist;
  tauto.
  }

  assert (bpilp12: boundph (phplus (phplus Pinv Pleak) (phplus p1 p2))).
  {
  apply boundph_fold with (m:=pof) (l:=T);
  try tauto.
  }

  assert (bpilp2: boundph (phplus (phplus Pinv Pleak) p2)).
  {
  apply boundph_mon with p1;
  try tauto.
  rewrite phplus_assoc; repeat php_.
  replace (phplus p2 p1) with (phplus p1 p2); repeat php_.
  }

  assert (bpip2: boundph (phplus Pinv p2)).
  {
  rewrite phplus_comm;
  try tauto.
  apply boundph_mon with Pleak;
  try tauto.
  rewrite phplus_assoc;
  try tauto.
  rewrite phplus_comm;
  try tauto.
  apply phpdef_pair;
  try tauto.
  apply phpdef_comm.
  tauto.
  }

  assert (bpi2pl: boundph (phplus (phplus Pinv p2) Pleak)).
  {
  replace (phplus Pinv p2) with (phplus p2 Pinv);
  try tauto.
  rewrite phplus_assoc;
  try tauto.
  rewrite phplus_comm;
  try tauto.
  apply phpdef_pair;
  try tauto.
  apply phplus_comm;
  tauto.
  }

  assert (EQh: phplus (phplus Pinv p2) Pleak = phplus (phplus Pinv Pleak) p2).
  {
  rewrite phplus_comm;
  try tauto.
  rewrite <- phplus_assoc.
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

  assert (INOB': forall o (IN: In o (concat (map oof (updl T id (Waiting4cond v l, tx,
          upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock), O1, C1, id))))), In o (concat (map oof T))).
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
  unfold oof in *.
  simpl in *.
  destruct (Z.eq_dec x6 id).
  simpl in *.
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2)).
  {
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  }
  inversion EQX.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  split.
  assumption.
  apply Permutation_in with (Oof ll :: O1).
  apply Permutation_sym.
  assumption.
  right.
  assumption.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  assert (INC1C2: In (ghplus C1 C2) (map gof T)).
  {
  apply in_map_iff.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  tauto.
  }

  assert (ghpdefp12ip12l: ghplusdef (ghplus C1 C2) Cinv /\ ghplusdef (ghplus C1 C2) Cleak).
  {
  apply GHPD.
  tauto.
  }

  assert (ghpdefp1ip2i: ghplusdef C1 Cinv /\ ghplusdef C2 Cinv).
  {
  apply ghpdef_dist;
  tauto.
  }

  assert (ghpdefp1lp2l: ghplusdef C1 Cleak /\ ghplusdef C2 Cleak).
  {
  apply ghpdef_dist;
  tauto.
  }

  assert (EQc: ghplus (ghplus Cinv C2) Cleak = ghplus (ghplus Cinv Cleak) C2).
  {
  rewrite ghplus_comm;
  try tauto.
  rewrite <- ghplus_assoc.
  try tauto.
  replace (ghplus Cleak Cinv) with (ghplus Cinv Cleak);
  try tauto.
  apply ghplus_comm;
  try tauto.
  apply ghpdef_comm.
  tauto.
  apply ghpdef_comm.
  tauto.
  apply ghpdef_comm.
  tauto.
  apply ghpdef_pair';
  try tauto.
  apply ghpdef_comm.
  tauto.
  }

  assert (GHPD': forall p0 : gheap, In p0 (map gof T) -> ghplusdef p0 (ghplus Cinv Cleak)).
  {
  intros.
  apply GHPD in H.
  apply ghpdef_pair;
  try tauto.
  }

  assert (bgpilp12: boundgh (ghplus (ghplus Cinv Cleak) (ghplus C1 C2))).
  {
  apply boundgh_fold with (m:=gof) (l:=T);
  try tauto.
  }

  assert (bgpilp2: boundgh (ghplus (ghplus Cinv Cleak) C2)).
  {
  apply boundgh_mon with C1;
  try tauto.
  rewrite ghplus_assoc.
  replace (ghplus C2 C1) with (ghplus C1 C2);
  try tauto.
  apply ghplus_comm;
  try tauto.
  apply ghpdef_pair';
  try tauto.
  apply ghpdef_comm.
  tauto.
  apply ghpdef_comm.
  tauto.
  apply ghpdef_pair';
  try tauto.
  apply ghpdef_comm.
  tauto.
  apply ghpdef_comm.
  tauto.
  apply ghpdef_comm.
  tauto.
  }

  assert (bgpip2: boundgh (ghplus Cinv C2)).
  {
  rewrite ghplus_comm;
  try tauto.
  apply boundgh_mon with Cleak;
  try tauto.
  rewrite ghplus_assoc;
  try tauto.
  rewrite ghplus_comm;
  try tauto.
  apply ghpdef_pair;
  try tauto.
  apply ghpdef_comm.
  tauto.
  }

  assert (bgpi2pl: boundgh (ghplus (ghplus Cinv C2) Cleak)).
  {
  replace (ghplus Cinv C2) with (ghplus C2 Cinv);
  try tauto.
  rewrite ghplus_assoc;
  try tauto.
  rewrite ghplus_comm;
  try tauto.
  apply ghpdef_pair;
  try tauto.
  apply ghplus_comm;
  tauto.
  }

  assert (bupd: boundph (upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock))).
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bc12: boundgh (ghplus C1 C2)).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  left.
  apply in_map_iff.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  split. reflexivity. assumption.
  }

  assert (bc1: boundgh C1).
  {
  apply boundgh_mon with C2; try assumption.
  }

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  unfold inf_capacity in *.
  destruct INF1 as (x,INF1).
  exists x.
  intros.
  rewrite EQc.
  rewrite eq_gheap_Wait with (p1:=C1);
  try tauto.
  apply INF1.
  assumption.
  apply gofs.
  apply in_map_iff.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  rewrite eql.
  apply red_Wait; try assumption.
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
  rewrite EQh in CONDv.
  rewrite EQH in CONDv.
  apply SPUR2 in CONDv.
  destruct CONDv as (a,(b,(c,d))).
  exists a, b.
  exists.
  destruct (location_eq_dec Z.eq_dec ll a).
  left.
  rewrite <- e.
  rewrite EQh.
  rewrite LOCKU.
  reflexivity.
  rewrite EQh.
  rewrite EQH.
  assumption.
  assumption.
  assumption.
  unfold not.
  intros CO.
  rewrite <- CO in CONDv.
  rewrite LOCKU in CONDv.
  inversion CONDv.
  }

  exists.
  {
  exists.
  {
  apply defl_Wait with ll p1 p2; repeat php_.
  exists wt, ot.
  left.
  assumption.
  }

  exists.
  {
  cnj_; apply phpdef_pair'; repeat php_.
  }

  exists.
  {
  intros.
  split.
  apply phpdef_pair.
  apply phpdef_comm.
  assumption.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQx.
  simpl in EQx.
  rewrite <- EQx.
  destruct (Z.eq_dec x6 id) as [x6id|x6id].
  rewrite x6id in INx.
  apply eq_in_updl_eq in INx.
  inversion INx.
  apply phpdef_locked_lock.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply PHPD.
  apply in_map_iff.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply phpdef_comm.
  assumption.
  exists wt, ot.
  left.
  assumption.
  apply PHPD.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  split.
  reflexivity.
  eapply in_in_updl_neq.
  apply x6id.
  apply INx.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQx.
  simpl in EQx.
  rewrite <- EQx.
  destruct (Z.eq_dec x6 id) as [x6id|x6id].
  rewrite x6id in INx.
  apply eq_in_updl_eq in INx.
  inversion INx.
  apply phpdef_locked_lock.
  assumption.
  exists wt, ot.
  left.
  assumption.
  apply phpdef_comm.
  apply phpdef_assoc_mon2 with p1.
  assumption.
  unfold defl in DEFL.
  apply DEFL with id x6.
  omega.
  apply in_map_iff.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  split.
  reflexivity.
  eapply in_in_updl_neq.
  apply x6id.
  apply INx.


  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQx.
  simpl in EQx.
  rewrite <- EQx.
  destruct (Z.eq_dec x6 id) as [x6id|x6id].
  rewrite x6id in INx.
  apply eq_in_updl_eq in INx.
  inversion INx.
  apply phpdef_locked_lock.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply PHPD.
  apply in_map_iff.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  auto.
  apply phpdef_comm.
  assumption.
  exists wt, ot.
  left.
  assumption.
  apply PHPD.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  split.
  reflexivity.
  eapply in_in_updl_neq.
  apply x6id.
  apply INx.
  }
  exists.
  {
  intros.
  apply boundph_updl with (m:=pof)(l:=T)(z:=id)(x:=(Waiting4cond v l, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock), O1, C1, id)).
  assumption.
  assumption.
  unfold pof.
  simpl.
  assumption.
  }
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  {
  rewrite EQh.
  apply boundph_Wait with ll p1;
  try tauto.
  apply pofs.
  exists wt, ot.
  left.
  assumption.
  }
  rewrite EQh.
  assert (PH:=PH2H).
  destruct PH as (PH, PH1).
  split.
  {
  intros.
  specialize PH with l0.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e.
  rewrite LOCK.
  unfold upd.
  rewrite eqz.
  reflexivity.
  rewrite EQH.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  destruct (fold_left phplus (map pof T) (phplus Pinv Pleak) l0) eqn:fl0.
  assert (CO: ll = l0).
  {
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite fl0.
  apply some_none.
  omega.
  }
  contradiction.
  trivial.
  assumption.
  assumption.
  }
  intros.
  unfold upd.
  destruct (Z.eq_dec z (Aof ll)).
  symmetry in e.
  apply NONE in e.
  rewrite LOCK in e.
  inversion e.
  apply PH1.
  intros.
  rewrite <- EQH.
  apply NONE.
  assumption.
  unfold not.
  intros.
  rewrite <- H in EQ.
  rewrite <- EQ in n.
  contradiction.
  }

  exists.
  {
  exists.
  {
  apply deflg_Wait with C1 C2;
  try tauto.
  apply in_map_iff.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  tauto.
  }
  exists.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold gof in EQx.
  simpl in EQx.
  rewrite <- EQx.
  destruct (Z.eq_dec x6 id) as [x6id|x6id].
  simpl in *.
  split.
  apply ghpdef_pair;
  try tauto.
  apply ghpdef_comm;
  tauto.
  tauto.
  simpl.
  split.
  apply ghpdef_pair;
  try tauto.
  apply ghpdef_comm.
  tauto.
  apply GHPD.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  tauto.
  apply ghpdef_comm.
  apply ghpdef_assoc_mon with C1;
  try tauto.
  apply DEFLg with id x6.
  omega.
  apply in_map_iff.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  tauto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  tauto.
  apply proj2 with (ghplusdef x5 Cinv).
  apply GHPD.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  tauto.
  }
  exists.
  {
  apply ghpdef_pair';
  try tauto.
  apply ghpdef_comm.
  tauto.
  }

  rewrite EQc.
  rewrite eq_gheap_Wait with (p1:=C1);
  try tauto.
  apply gofs.
  intros.
  apply in_map_iff.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id).
  tauto.
  }

  exists.
  {
  intros.
  apply upd_updl.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2).
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
  exists.
  {
  simpl.
  apply NoDup_cons.
  unfold not.
  intros.
  apply AinvOK in H.
  destruct H as (CO,hl1).
  rewrite LOCKED in CO.
  inversion CO.
  assumption.
  }
  exists.
  {
  simpl.
  intros.
  destruct IN as [EQ|IN].
  rewrite <- EQ.
  split.
  rewrite EQh.
  assumption.
  unfold upd.
  rewrite eqz.
  reflexivity.
  apply AinvOK in IN.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  assert (EQL: l0 = ll).
  {
  apply INJ.
  destruct IN as (EQ1,IN1).
  rewrite EQ1.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }
  rewrite EQL.
  rewrite EQh.
  tauto.
  rewrite EQh.
  rewrite EQH.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  }

  exists. 
  {
  unfold upd at 2.
  intros.
  destruct (Z.eq_dec (Aof l0) (Aof ll)) as [l0l|l0l].
  rewrite l0l.
  left.
  assert (EQll: ll = l0).
  {
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  assumption.
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite EQh in LOCK0.
  rewrite EQH in LOCK0.
  rewrite LOCK0.
  apply some_none.
  assumption.
  omega.
  }
  rewrite <- EQll.
  {
  rewrite <- EQW.
  rewrite <- EQO.
  rewrite eqv.
  reflexivity.
  }
  right.

  assert (INA: In (subsas (snd (Iof l0)) (invs (fst (Iof l0))
    (filterb (xOf (fun x  => Lof x) locs) (Aof l0) (fun v : Z => length
    (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof T)))) (filterb (xOf (fun x  => Lof x) locs) (Aof l0)
    (count_occ Z.eq_dec (concat (map Aoof T))))), l0) Ainv).
  {
  apply INAOK.
  rewrite EQh in LOCK0.
  rewrite EQH in LOCK0.
  assumption.
  unfold not.
  intros.
  rewrite H in l0l.
  omega.
  assumption.
  }

  assert (EQwt: (filterb (xOf (fun x  => Lof x) locs) (Aof l0) (fun v0 : Z => length (filter
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0))) (map cmdof
    (updl T id (Waiting4cond v l, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock), O1, C1, id)))))) =  
    (filterb (xOf (fun x  => Lof x) locs) (Aof l0) (fun v : Z => length (filter 
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))).
  {
  symmetry.
  apply filterb_updl_eq.
  intros.
  split.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec (Some ([[v]])) (Some v0)).
  inversion e.
  rewrite <- H0 in IN.
  rewrite <- eqv in *.
  assert (XOF: xOf (fun x => Lof x) locs (Aof lv) = Some (Lof lv)).
  {
  assert (INlv: In lv locs).
  {
  apply LOCs.
  rewrite COND.
  apply some_none.
  }
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
  rewrite IN in XOF.
  rewrite Lvl in XOF.
  inversion XOF.
  contradiction.
  reflexivity.
  intros.
  assert (X':x' = (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  inversion X'.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some v0)).
  inversion e.
  reflexivity.
  }
  rewrite EQwt.
  assert (EQot: (filterb (xOf (fun x  => Lof x) locs) (Aof l0) (count_occ Z.eq_dec (concat (map Aoof T)))) =
    (filterb (xOf (fun x  => Lof x) locs) (Aof l0) (count_occ Z.eq_dec (concat (map Aoof (updl T id
    (Waiting4cond v l, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock), O1, C1, id))))))).
  {
  apply filterb_updl_obs_eq.
  intros.
  assert (XOF: xOf (fun x => Lof x) locs (Aof ll) = Some (Lof ll)).
  {
  assert (INlv: In ll locs).
  {
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  }
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
  assert (X':x' = (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id)).
  {
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  }
  inversion X'.
  unfold oof.
  unfold Aoof.
  simpl.
  rewrite count_map_perm with (l2:=Oof ll::O1).
  simpl.
  rewrite eql in *.
  destruct (Z.eq_dec (Aofo (Oof ll)) v0).
  rewrite <- e in IN.
  rewrite <- eql in *.
  unfold Aof in XOF.
  rewrite IN in XOF.
  rewrite lll in *.
  inversion XOF.
  contradiction.
  reflexivity.
  assumption.
  }
  rewrite <- EQot.
  assumption.
  }

  replace (fold_left Astar (map fst ((subsas (snd (Iof ll))
    (invs (fst (Iof ll)) (upd Z.eq_dec wt (Aof lv) (S (wt (Aof lv)))) ot), ll) :: Ainv)) (Abool true)) with 
    (fold_left Astar (map fst Ainv) (Abool true ** (subsas (snd (Iof ll))
    (invs (fst (Iof ll)) (upd Z.eq_dec wt (Aof lv) (S (wt (Aof lv)))) ot)))).
  Focus 2.
  reflexivity.
  simpl.
  apply fold_left_g_can.
  unfold cang.
  split.
  intros.
  apply sat_comm.
  assumption.
  simpl.
  intros.
  apply sat_perm with (l:=l0);
  try tauto.
  apply sat_comm.
  apply sat_plus with None None;
  try tauto.
  apply phpdef_comm.
  assumption.
  apply ghpdef_comm.
  tauto.
  apply boundgh_mon with Cleak.
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak);
  try tauto.
  apply boundgh_mon with C1.
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak);
  try tauto.
  left.
  rewrite ghplus_comm.
  assumption.
  apply ghpdef_comm.
  assumption.
  apply None_op.
  }
  exists.
  {
  exists.
  {
  unfold injph.
  unfold inj.
  intros.
  assert (pxN: forall x1, fold_left phplus (map pof (updl T id
   (Waiting4cond v l, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock), O1, C1, id)))
   (phplus (phplus Pinv p2) Pleak) x1 <> None ->
   fold_left phplus (map pof T) (phplus Pinv Pleak) x1 <> None).
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll x0).
  rewrite <- e.
  rewrite LOCKED.
  apply some_none.
  rewrite <- EQH.
  rewrite <- EQh.
  assumption.
  assumption.
  }
  apply INJ;
  try apply pxN;
  try assumption.
  }
  split. assumption.
  split.
  {
  split.
  intros.
  apply LOCs.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e.
  rewrite LOCKED.
  apply some_none.
  rewrite <- EQH.
  rewrite <- EQh.
  assumption.
  assumption.
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e.
  rewrite EQh.
  rewrite LOCK.
  apply some_none.
  rewrite EQh.
  rewrite EQH.
  apply LOCs.
  assumption.
  assumption.
  }
  intros.
  apply INOB' in IN.
  apply OBsOK in IN.
  destruct IN as (l',(EQl',pl')).
  exists l', EQl'.
  destruct ((location_eq_dec Z.eq_dec) ll l').
  rewrite <- e.
  rewrite EQh.
  rewrite LOCK.
  apply some_none.
  rewrite EQh.
  rewrite EQH.
  assumption.
  assumption.
  }
  exists.
  {
  exists.
  {
  intros.
  assert (tmp: Lof l0 = Aof l0 /\
        Pof l0 = false /\
        Xof l0 = None /\
        (h (Aof l0) <> Some 1%Z -> In (Oof l0) (concat (map oof T)))).
  {
  apply LOCKOK.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e.
  right.
  exists wt, ot.
  left.
  assumption.
  rewrite EQh in LOCK0.
  rewrite EQH in LOCK0.
  assumption.
  assumption.
  }
  destruct tmp as (tm1,(tm2,(tm3,tm4))).
  split.
  assumption.
  split.
  assumption.
  split.
  assumption.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  intros.
  contradiction.
  intros.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  apply tm4 in H.
  rewrite <- flat_map_concat_map in H.
  apply in_flat_map in H.
  destruct H as (x,(INx,INl)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  destruct (Z.eq_dec x6 id) as [x6id|x6id].
  rewrite x6id in INx.
  assert (EQA: (x1,x2,x3,x4,x5) = (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2)).
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  symmetry in EQA.
  inversion EQA.
  exists (Waiting4cond v l, x2, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock),O1, C1, id).
  split.
  apply in_updl_eq.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2).
  assumption.
  unfold oof.
  simpl.
  unfold oof in INl.
  simpl in INl.
  rewrite <- H3 in INl.
  rewrite O1eq in INl.
  destruct INl as [INl|INl].
  unfold Aof in n.
  rewrite INl in n.
  omega.
  assumption.
  exists (x1, x2, x3, x4, x5, x6).
  split.
  apply in_updl_neq.
  omega.
  assumption.
  assumption.
  }
  split.
  {
  unfold upd.
  intros.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  split.
  reflexivity.
  assert (CO: ll = l0).
  {
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  assumption.
  rewrite EQh in ULOCK.
  rewrite EQH in ULOCK.
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite ULOCK.
  apply some_none.
  omega.
  assumption.
  }
  rewrite <- CO in ULOCK.
  rewrite EQh in ULOCK.
  unfold upd in *.
  rewrite LOCK in ULOCK.
  inversion ULOCK.

  rewrite EQh in ULOCK.
  rewrite EQH in ULOCK.
  apply ULOCKOK in ULOCK.
  destruct ULOCK as (U1,U2).
  split.
  assumption.
  unfold not.
  intros.
  apply U2.
  rewrite <- flat_map_concat_map in *.
  apply in_flat_map in H.
  destruct H as (x,(INx,INl0)).
  unfold updl in INx.
  apply in_map_iff in INx.
  destruct INx as ((x0,id'),(EQx0,INx0)).
  simpl in *.
  destruct (Z.eq_dec id' id).
  assert (EQA: x0 = (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2)).
  {
  apply unique_key_eq with T id; repeat php_.
  rewrite <- e.
  assumption.
  }

  rewrite EQA in *.

  rewrite <- EQx0 in INl0.
  unfold oof in INl0.
  simpl in INl0.
  apply in_flat_map.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2,id).
  split.
  assumption.
  unfold oof.
  simpl.
  apply Permutation_in with (Oof ll :: O1).
  apply Permutation_sym.
  assumption.
  right.
  assumption.
  rewrite <- EQx0 in INl0.
  apply in_flat_map.
  exists (x0, id').
  auto.
  unfold not.
  intros.
  rewrite <- H in n.
  omega.
  }
  intros.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  assert (CO: ll = l0).
  {
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  assumption.
  rewrite EQh in UCOND.
  rewrite EQH in UCOND.
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite UCOND.
  apply some_none.
  omega.
  assumption.
  }
  rewrite <- CO in UCOND.
  rewrite EQh in UCOND.
  unfold upd in *.
  rewrite LOCK in UCOND.
  inversion UCOND.

  rewrite EQh in UCOND.
  rewrite EQH in UCOND.
  apply UCONDOK in UCOND.
  unfold not.
  intros.
  apply UCOND.
  rewrite <- flat_map_concat_map in *.
  apply in_flat_map in H.
  destruct H as (x,(INx,INl0)).
  unfold updl in INx.
  apply in_map_iff in INx.
  destruct INx as ((x0,id'),(EQx0,INx0)).
  simpl in *.
  destruct (Z.eq_dec id' id).
  assert (EQA: x0 = (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2)).
  {
  apply unique_key_eq with T id; repeat php_.
  rewrite <- e.
  assumption.
  }

  rewrite EQA in *.

  rewrite <- EQx0 in INl0.
  unfold oof in INl0.
  simpl in INl0.
  apply in_flat_map.
  exists (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2,id).
  split.
  assumption.
  unfold oof.
  simpl.
  apply Permutation_in with (Oof ll :: O1).
  apply Permutation_sym.
  assumption.
  right.
  assumption.
  rewrite <- EQx0 in INl0.
  apply in_flat_map.
  exists (x0, id').
  auto.
  unfold not.
  intros.
  rewrite <- H in n.
  omega.
  }

  exists.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) l0 ll) as [ll0|ll0].
  {
  rewrite ll0 in ULOCKED.
  rewrite EQh in ULOCKED.
  rewrite LOCK in ULOCKED.
  destruct ULOCKED as [CO1|CO1].
  inversion CO1.
  inversion CO1.
  }
  assert (wot: wt0 = filterb (xOf (fun x => Lof x) locs) (Aof l0) (fun v => length (filter
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) /\
    ot0 = filterb (xOf (fun x => Lof x) locs) (Aof l0) (count_occ Z.eq_dec (concat (map Aoof T)))).
  {
  apply WTsOTsOK.
  rewrite EQh in ULOCKED.
  rewrite EQH in ULOCKED.
  assumption.
  unfold not.
  intros.
  symmetry in H.
  contradiction.
  }
  destruct wot as (wt0eq,ot0eq).
  split.

  rewrite <- filterb_updl_eq.
  assumption.
  intros.
  split.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec (Some ([[v]])) (Some v0)).
  inversion e.
  rewrite <- eqv in *.
  rewrite <- Lvl in *.

  assert (XOF: xOf (fun x => Lof x) locs v0 = Some (Lof lv)).
  {
  rewrite <- H0.
  assert (INlv: In lv locs).
  {
  apply LOCs.
  rewrite COND.
  apply some_none.
  }
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

  rewrite IN in XOF.
  inversion XOF.
  rewrite Lvl in H1.
  assert (CO: l0 = ll).
  {
  apply INJ.
  rewrite EQh in ULOCKED.
  rewrite EQH in ULOCKED.
  destruct ULOCKED as [U|U];
  rewrite U;
  apply some_none.
  unfold not.
  intros.
  symmetry in H.
  contradiction.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }
  contradiction.

  reflexivity.
  intros.
  assert (EQx': x' = (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id)).
  apply in_elem with (l:=T).
  assumption.
  assumption.
  assumption.
  inversion EQx'.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some v0)).
  inversion e.
  reflexivity.
  rewrite <- filterb_updl_obs_eq.
  assumption.
  intros.
  assert (EQx': x' = (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id)).
  apply in_elem with (l:=T).
  assumption.
  assumption.
  assumption.
  inversion EQx'.
  unfold oof.
  unfold Aoof.
  simpl.
  rewrite count_map_perm with (l2:=Oof ll::O1).
  simpl.
  destruct (Z.eq_dec (Aofo (Oof ll)) v0).
  rewrite <- e in IN.
  assert (XOF: xOf (fun x => Lof x) locs (Aof ll) = Some (Lof ll)).
  {

  assert (INlv: In ll locs).
  {
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  }
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
  unfold Aof in XOF.
  rewrite IN in XOF.
  inversion XOF.
  assert (CO: l0 = ll).
  {
  apply INJ.
  rewrite EQh in ULOCKED.
  rewrite EQH in ULOCKED.
  destruct ULOCKED as [U|U];
  rewrite U;
  apply some_none.
  unfold not.
  intros.
  symmetry in H0.
  contradiction.
  rewrite LOCKED.
  apply some_none.
  rewrite <- lll.
  assumption.
  }
  contradiction.

  reflexivity.
  assumption.
  }

  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold snd in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  {
(* ==================== x6 = id ===========*)
  symmetry in EQ.
  inversion EQ.
  exists.
  trivial.
  exists.
  unfold weakest_pre_ct.
  assert (S:=SATp1).

  eapply sat_weak_imp1; try assumption.
  apply S.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  symmetry in W4COND.
  inversion W4COND.
  exists lv, ll.
  exists.
  apply LOCs.
  rewrite COND.
  apply some_none.
  exists.
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  exists eqv, eql.
  unfold WTs, OBs in *.
  unfold filterb.
  assert (Lofv: xOf (fun x  => Lof x) locs ([[v]]) = Some ([[l]])).
  {
  rewrite <- eqv.
  rewrite <- eql.
  rewrite <- Lvl.
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

  rewrite Lofv.
  rewrite eql in *.
  assert (NEQvl': ([[v]]) <> ([[l]])).
  {
  rewrite <- eqv.
  rewrite <- eql.
  unfold not.
  intros.
  assert (CO: lv = ll).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }
  rewrite CO in COND.
  rewrite COND in LOCKED.
  inversion LOCKED.
  }

  destruct (Z.eq_dec ([[v]]) ([[l]])).
  contradiction.
  rewrite eqz.
  rewrite eqz.
  assumption.
  }
(* ==================== x6 <> id ===========*)
  inversion EQ.
  rewrite H0 in IN.
  rewrite H1 in IN.
  rewrite H2 in IN.
  rewrite H3 in IN.
  rewrite H4 in IN.
  rewrite H5 in IN.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF1,(WP1,VOBS1)).
  exists.
  assumption.
  exists.
  assert (bp0: boundph p).
  {
  apply BPE.
  apply in_map_iff.
  exists (c, tx0, p, O0, C, id0).
  split. reflexivity. assumption.
  }

  assert (bg0: boundgh C).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  left.
  apply in_map_iff.
  exists (c, tx0, p, O0, C, id0).
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  apply WP1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  assert (W4C:= W4COND).
  apply VOBS1 in W4C.
  destruct W4C as (v1,(l1,(INv,(INl,(EQv,(EQl,SAFE1)))))).
  exists v1, l1, INv, INl, EQv, EQl.

  rewrite W4COND in WP1.
  apply sat_wait4cond in WP1.
  destruct WP1 as (ll',(lv',(eql',(eqv',(pv',(pl',(eqlv',rest))))))).
  assert (lv'cond: fold_left phplus (map pof T) (phplus Pinv Pleak) lv' = Some Cond).
  {
  apply fold_cond;
  try tauto.
  apply pofs.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (c, tx0, p, O0, C, id0).
  tauto.
  assumption.
  }
  assert (NEQ1: Aof ll <> ([[ev]])).
  {
  rewrite <- eqv' in *.
  unfold not.
  intros.
  assert (CO: ll = lv').
  {
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite lv'cond.
  apply some_none.
  assumption.
  }
  rewrite <- CO in lv'cond.
  rewrite LOCKED in lv'cond.
  inversion lv'cond.
  }

  assert (eqv1lv': v1 = lv').
  {
  apply INJ.
  apply LOCs.
  assumption.
  rewrite lv'cond.
  apply some_none.
  omega.
  }

  assert (Lofv: xOf (fun x  => Lof x) locs ([[ev]]) = Some ([[el]])).
  {
  rewrite <- EQv.
  rewrite <- eqlv'.
  rewrite <- eqv1lv'.
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

  assert (LK: fold_left phplus (map pof T) (phplus Pinv Pleak) ll' = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) ll' = Some (Locked wt ot)).
  {
  apply fold_lock_ed;
  try tauto.
  apply pofs.
  right.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (c, tx0, p, O0, C, id0).
  tauto.
  tauto.
  }

  assert (NEQevelL: ([[ev]]) <> ([[el]])).
  {
  rewrite <- eql'.
  rewrite <- EQv.
  rewrite eqv1lv'.
  unfold not.
  intros.
  assert (CO: lv' = ll').
  {
  apply INJ.
  rewrite lv'cond.
  apply some_none.
  destruct LK as [LK|LK].
  rewrite LK.
  apply some_none.
  destruct LK as (wt1,(ot1,LK)).
  rewrite LK.
  apply some_none.
  assumption.
  }
  rewrite CO in lv'cond.
  rewrite lv'cond in LK.
  destruct LK as [LK|LK].
  inversion LK.
  destruct LK as (wt1,(ot1,LK)).
  inversion LK.
  }


  destruct (Z.eq_dec (Aof v1) (Aof lv)).
  {
  assert (EQvlv: v1 = lv).
  {
  apply INJ.
  apply LOCs.
  assumption.
  rewrite COND.
  apply some_none.
  assumption.
  }
  rewrite EQvlv.

  assert (EQev: ([[ev]] = ([[v]]))).
  {
  rewrite <- EQv.
  rewrite <- eqv.
  assumption.
  }
  unfold filterb.
  rewrite EQl in *.
  rewrite Lofv.
  destruct (Z.eq_dec ([[ev]]) ([[el]])).
  contradiction.
  rewrite EQev.
  rewrite eqz.
  rewrite eqz.
  assumption.
  }

  assert (NEQ2: ([[v]]) <> ([[ev]])).
  {
  rewrite <- eqv.
  rewrite <- EQv.

  omega.
  }

  assert (EQwt': filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[ev]]))))
    (map cmdof T) =
    filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0)
    (Some ([[ev]])))) (map cmdof (updl T id (Waiting4cond v l, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock), O1, C1, id)))).
  {
  rewrite <- filter_updl_eq.
  reflexivity.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec (Some ([[v]])) (Some ([[ev]]))).
  inversion e.
  omega.
  reflexivity.
  intros.
  assert (X':x' = (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  inversion X'.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some ([[ev]]))).
  inversion e.
  reflexivity.
  }

  unfold filterb.
  unfold WTs, OBs in SAFE1.
  unfold filterb in SAFE1.
  rewrite Lofv in *.
  rewrite EQl in *.
  destruct (Z.eq_dec ([[ev]]) ([[el]])).
  contradiction.
  rewrite eqz in *.
  rewrite eqz in *.

  rewrite <- EQwt'.
  assert (EQot: (count_occ Z.eq_dec (concat (map Aoof T)) ([[ev]])) =
    (count_occ Z.eq_dec (concat (map Aoof (updl T id
    (Waiting4cond v l, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock),
    O1, C1, id)))) ([[ev]]))).
  {
  apply count_updl_eq.
  intros.
  assert (X':x' = (Wait v l, tx, phplus p1 p2, O, ghplus C1 C2, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  inversion X'.
  unfold oof.
  unfold Aoof.
  rewrite count_map_perm with (l2:=Oof ll::O1).
  simpl.
  destruct (Z.eq_dec (Aofo (Oof ll)) ([[ev]])).
  rewrite <- e in NEQ1.
  contradiction.
  reflexivity.
  assumption.
  }
  rewrite <- EQot.
  assumption.
Qed.


Lemma Notify_preserves_validity:
  forall m sp h t id id' v v' l tx tx'
         (EQvv': ([[v]]) = ([[v']]))
         (CMD: t id = Some (Notify v, tx))
         (CMD': t id' = Some (Waiting4cond v' l, tx'))
         (VALID: validk (S m) sp t h),
    validk m sp (upd Z.eq_dec (upd Z.eq_dec t id (Some (tt, tx))) id' (Some (Waiting4lock l, tx'))) h.
Proof.
  intros.
  unfold validk in VALID.

  destruct VALID as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
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
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.

  rewrite map_map in *.

  assert (NEQidid': id <> id').
  unfold not.
  intros.
  rewrite H in CMD.
  rewrite CMD in CMD'.
  inversion CMD'.
  assert (tmp: exists p O C, In (Notify v, tx, p, O, C, id) T).
  apply TOK.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  apply sat_notify in WP.

  destruct WP as (p1,(pm,(C1,(Cm,(wt,(ot,(lv,(ll,(Or,(PERMOr,(bp1,(bpm,(bp1pm,(phpdefp1pm,
    (p1pm,(ghpdefC1Cm,(C1Cm,(eqlv,(eqll,(p1ll,(p1lv,(satm,(satp1,satp1m))))))))))))))))))))))).

  assert (tmp: exists p' O' C', In (Waiting4cond v' l, tx', p', O', C', id') T).
  apply TOK.
  assumption.
  destruct tmp as (p',(O',(C',INT'))).
  assert (tmp:=INT').
  apply SOBS in tmp.
  destruct tmp as (WF',(WP',VOBS')).
  unfold wellformed in WF'.
  simpl in WF'.
  apply sat_wait4cond in WP'.
  destruct WP' as (l0,(v0,(eql0,(eqv,(p'v,(p'l0,(lofl0,(prcv0,(prcv,SAT2))))))))).
  assert (bp: boundph p).
  {
  apply BPE.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  auto.
  }
  assert (bp': boundph p').
  {
  apply BPE.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  auto.
  }

  assert (PHPD0: forall p0 : pheap, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  apply PHPD in H.
  apply phpdef_pair;
  tauto.
  }

  assert (pll: p ll = Some (Locked wt ot)).
  {
  rewrite p1pm.
  apply phplus_locked; repeat php_.
  }

  assert (plv: p lv = Some Cond).
  {
  rewrite p1pm.
  apply phplus_Cond;
  try tauto.
  }

  assert (LOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked wt ot)).
  {
  apply fold_locked.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  auto.
  assumption.
  }

  assert (COND: fold_left phplus (map pof T) (phplus Pinv Pleak) lv = Some Cond).
  {
  apply fold_cond;
  try tauto.
  apply pofs.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  tauto.
  assumption.
  }

  assert (neqvl: lv <> ll).
  {
  unfold not.
  intros.
  rewrite H in COND.
  rewrite COND in LOCKED.
  inversion LOCKED.
  }

  assert (neqavl: ([[v]]) <> Aof ll).
  {
  unfold not.
  intros.
  rewrite <- eqlv in H.
  assert (CO: lv = ll).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }
  contradiction.
  }

  assert (INlv: In lv locs).
  {
  apply LOCs.
  rewrite COND.
  apply some_none.
  }

  assert (COMPll: comp (ll :: locs) (fun x  => Aof x)).
  {
  unfold comp.
  intros.
  apply INJ.
  destruct IN as [EQ1|IN1].
  rewrite <- EQ1.
  rewrite LOCKED.
  apply some_none.
  apply LOCs.
  assumption.
  destruct IN0 as [EQ1|IN1].
  rewrite <- EQ1.
  rewrite LOCKED.
  apply some_none.
  apply LOCs.
  assumption.
  }

  assert (INll: In ll locs).
  {
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  }

  assert (COMPlv: comp (lv :: locs) (fun x  => Aof x)).
  {
  unfold comp.
  intros.
  apply INJ.
  destruct IN as [EQ1|IN1].
  rewrite <- EQ1.
  rewrite COND.
  apply some_none.
  apply LOCs.
  assumption.
  destruct IN0 as [EQ1|IN1].
  rewrite <- EQ1.
  rewrite COND.
  apply some_none.
  apply LOCs.
  assumption.
  }

  assert (wtv: lt 0 (wt ([[v]]))).
  {
  assert (tmp: wt = filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v : Z => length (filter
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof T))) /\
    ot = filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))).
  {
  apply WTsOTsOK.
  left.
  assumption.
  }
  destruct tmp as (wt1,ot1).
  rewrite wt1.
  unfold filterb.
  destruct (xOf (fun x  => Lof x) locs ([[v]])) eqn:XOF.
  assert (XOF1: xOf (fun x  => Lof x) locs ([[v]]) = Some (Lof lv)).
  {

  rewrite <- eqlv.
  apply xOf_same.
  apply in_map.
  assumption.
  assumption.
  }
  rewrite XOF in XOF1.
  inversion XOF1.
  destruct (Z.eq_dec ([[v]]) (Aof ll)).
  contradiction.
  rewrite <- eqll.
  rewrite eqz.
  assert (IN1: In (Waiting4cond v' l) (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[v]]))))
     (map cmdof T))).
  {
  apply filter_In.
  split.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  auto.
  simpl.
  rewrite EQvv'.
  destruct (opZ_eq_dec (Some ([[v']])) (Some ([[v']]))).
  reflexivity.
  contradiction.
  }

  destruct (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[v]]))))
           (map cmdof T)).
  inversion IN1.
  simpl.
  omega.
  apply xOf_exists1 in XOF.
  exfalso.
  apply XOF.
  exists lv.
  exists.
  apply LOCs.
  rewrite COND.
  apply some_none.
  omega.
  }

  rewrite eqlv in PERMOr.
  destruct (0 <? wt ([[v]])) eqn:wt00.
  Focus 2.
  apply Nat.ltb_lt in wtv.
  rewrite wt00 in wtv.
  inversion wtv.

  assert (tmp: Lof ll = Aof ll /\
        Pof ll = false /\
        Xof ll = None /\
        (h (Aof ll) <> Some 1%Z -> In (Oof ll) (concat (map oof T)))).
  {
  apply LOCKOK.
  right.
  exists wt, ot.
  tauto.
  }
  destruct tmp as (lll,(plf,(ninrlxll,inlt))).

  exists (updl (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some (Locked (upd Z.eq_dec wt ([[v]]) ((wt ([[v]]) - 1)%nat)) ot)), Or, C1, id))
          id' (Waiting4lock l, tx',phplus p' pm, M'of lv ++ O', ghplus C' Cm, id')).

  exists invs, locs, Pinv, Pleak, Ainv, Cinv, Cleak.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (EQ3: count_occ Z.eq_dec (concat (map Aoof (updl (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)), Or, C1, id))
    id' (Waiting4lock l, tx', phplus p' pm, M'of lv ++ O', ghplus C' Cm, id')))) =
    count_occ Z.eq_dec (concat (map Aoof T))).
  {
  rewrite concat_move_eq with (O:=map (fun x : olocation Z => Aofo x) (M'of lv ++ O')) 
    (O1:=map (fun x : olocation Z => Aofo x) O') (O2:=map (fun x : olocation Z => Aofo x) (M'of lv)) (id:=id')
    (x:=((Waiting4lock l, tx', p', O', C', id'))); repeat php_.
  rewrite updl_updl.
  rewrite concat_move_eq with (O:=map (fun x : olocation Z => Aofo x) O) 
    (O1:=map (fun x : olocation Z => Aofo x) Or) (O2:=map (fun x : olocation Z => Aofo x) (M'of lv)) (id:=id)
    (x:=(tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)),
    Or, C1, id)); repeat php_.
  apply functional_extensionality.
  intros.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite <- map_updl_eq.
  reflexivity.
  apply NoDup_updl.
  assumption.
  intros.
  unfold updl in IN.
  apply in_map_iff in IN.
  destruct IN as ((a,aid),(EQa,INa)).
  simpl in *.
  destruct (Z.eq_dec aid id).
  inversion EQa.
  omega.
  inversion EQa.
  rewrite H1 in *.
  rewrite <- H0 in *.
  assert (EQa': a = (Waiting4cond v' l, tx', p', O', C')).
  {
  apply unique_key_eq with T id'; try assumption.
  }
  rewrite EQa'.
  reflexivity.
  rewrite <- map_app.
  apply Permutation_map.
  apply Permutation_trans with (M'of lv ++ Or).
  apply Permutation_app_comm.
  assumption.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  split.
  reflexivity.
  unfold elem.
  apply filter_In.
  split.
  assumption.
  apply Z.eqb_eq.
  reflexivity.
  apply NoDup_updl.
  apply NoDup_updl.
  assumption.
  rewrite <- map_app.
  apply Permutation_map.
  apply Permutation_app_comm.
  unfold elem.
  unfold updl.
  rewrite map_map.
  apply in_map_iff.
  exists (Waiting4lock l, tx', phplus p' pm, M'of lv ++ O', ghplus C' Cm, id').
  split.
  reflexivity.
  apply filter_In.
  split.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  simpl.
  destruct (Z.eq_dec id' id).
  omega.
  simpl.
  rewrite eqz.
  auto.
  apply Z.eqb_eq.
  reflexivity.
  }

  assert (INO: forall o p1 p2 C (IN: In o (concat (map oof (updl (updl T id
    (tt, tx, p1, Or, C1, id)) id' (Waiting4lock l, tx', p2, M'of lv ++ O', C, id'))))),
    In o (concat (map oof T))).
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  rewrite map_map in IN.
  rewrite <- flat_map_concat_map in IN.
  apply in_flat_map in IN.
  destruct IN as (x,(INx,INl0)).
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold oof in *.
  simpl in *.
  destruct (Z.eq_dec x6 id).
  simpl in *.
  rewrite e in *.
  destruct (Z.eq_dec id id').
  omega.
  assert (EQX: (x1, x2, x3, x4, x5) = (Notify v, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  }
  inversion EQX.
  exists (Notify v, tx, p, O, C, id).
  split.
  assumption.
  apply Permutation_in with (M'of lv ++ Or).
  simpl.
  assumption.
  apply in_app_iff.
  right.
  assumption.
  simpl in *.
  destruct (Z.eq_dec x6 id').
  apply in_app_iff in INl0.
  destruct INl0 as [IN|IN].
  exists (Notify v, tx, p, O, C, id).
  split.
  assumption.
  apply Permutation_in with (M'of lv ++ Or).
  simpl.
  assumption.
  apply in_app_iff.
  left.
  assumption.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  auto.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }

  assert (INO': forall o p1 p2 C (IN: In o (concat (map oof T))),
    In o (concat (map oof (updl (updl T id
    (tt, tx, p1, Or, C1, id)) id' (Waiting4lock l, tx', p2, M'of lv ++ O', C, id'))))).
  {
  intros.
  unfold updl.
  rewrite map_map.
  rewrite map_map.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  rewrite <- flat_map_concat_map in IN.
  apply in_flat_map in IN.
  destruct IN as (x,(INx,INl0)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold oof in *.
  simpl in *.
  destruct (Z.eq_dec x6 id).
  simpl in *.
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (Notify v, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  }
  inversion EQX.
  rewrite H3 in INl0.
  apply Permutation_in with (l':=M'of lv ++ Or) in INl0.
  apply in_app_iff in INl0.
  destruct INl0 as [IN|IN].
  exists (Waiting4cond v' l, tx', p', O', C', id').
  split.
  assumption.
  simpl.
  destruct (Z.eq_dec id id').
  omega.
  destruct (Z.eq_dec id' id).
  omega.
  rewrite eqz.
  apply in_app_iff.
  left.
  assumption.
  exists (Notify v, tx, p, O, C, id).
  split.
  assumption.
  rewrite eqz.
  simpl.
  destruct (Z.eq_dec id id').
  omega.
  assumption.
  apply Permutation_sym.
  assumption.
  destruct (Z.eq_dec x6 id').
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (Waiting4cond v' l, tx', p', O', C')).
  {
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  }
  inversion EQX.
  rewrite H3 in INl0.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  split.
  assumption.
  simpl.
  destruct (Z.eq_dec id' id).
  omega.
  rewrite eqz.
  apply in_app_iff.
  right.
  assumption.
  exists (x1, x2, x3, x4, x5, x6).
  split.
  assumption.
  simpl.
  destruct (Z.eq_dec x6 id).
  omega.
  simpl.
  destruct (Z.eq_dec x6 id').
  omega.
  assumption.
  }

  assert (FILw: forall l0 (ll0: l0 <> (Aof ll)),
    (filterb (xOf (fun x  => Lof x) locs) l0 (fun v : Z => length (filter (fun c : cmd =>
    ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))) =
    (filterb (xOf (fun x  => Lof x) locs) l0 (fun v0 : Z => length (filter (fun c : cmd => 
    ifb (opZ_eq_dec (waiting_for_cond c) (Some v0)))
    (map cmdof (updl (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some (Locked (upd Z.eq_dec wt ([[v]]) ((wt ([[v]]) - 1)%nat)) ot)), Or, C1, id))
    id' (Waiting4lock l, tx', phplus p' pm, M'of lv ++ O', ghplus C' Cm, id'))))))).
  {
  intros.
  unfold filterb.
  apply functional_extensionality.
  intros.
  destruct (xOf (fun x0 => Lof x0) locs x) eqn:XOF.
  destruct (Z.eq_dec x l1) as [xl0|xl0].
  reflexivity.
  destruct (Z.eq_dec z l1) as [lxl0|lxl0].
  Focus 2.
  reflexivity.
  destruct (Z.eq_dec x (Aof ll)) as [xl|xl].
  assert (XOF1: xOf (fun x0 => Lof x0) locs x = Some (Lof ll)).
  {
  rewrite xl.
  apply xOf_same.
  apply in_map.
  assumption.
  assumption.
  }
  rewrite XOF in XOF1.
  inversion XOF1.
  omega.
  destruct (Z.eq_dec x ([[v]])) as [xv|xv].
  assert (XOF1: xOf (fun x0 => Lof x0) locs x = Some (Lof lv)).
  {
  rewrite xv.
  rewrite <- eqlv.
  apply xOf_same.
  apply in_map.
  assumption.
  assumption.
  }
  rewrite XOF in XOF1.
  inversion XOF1.
  omega.

  rewrite <- filter_updl_eq.
  rewrite <- filter_updl_eq.
  reflexivity.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some x)).
  inversion e.
  reflexivity.
  intros.
  assert (X': x' = (Notify v, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some x)).
  inversion e.
  reflexivity.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some x)).
  inversion e.
  reflexivity.
  intros.
  assert (X': x' = (Waiting4cond v' l, tx', p', O', C', id')).
  apply in_elem with (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)), Or, C1, id)).
  apply NoDup_updl.
  assumption.
  apply in_updl_neq.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec (Some ([[v']])) (Some x)).
  inversion e.
  rewrite <- EQvv' in H0.
  rewrite H0 in xv.
  contradiction.
  reflexivity.
  reflexivity.
  }

  assert (EQ_5: fold_left phplus (map pof (updl (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)), Or, C1, id))
           id' (Waiting4lock l, tx', phplus p' pm, M'of lv ++ O', ghplus C' Cm, id'))) (phplus Pinv Pleak) = 
           upd (location_eq_dec Z.eq_dec) (fold_left phplus (map pof T) (phplus Pinv Pleak)) ll (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot))).
  {
  apply fold_left_upd_Notify with p1 pm p'; repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  rewrite <- p1pm.
  repeat php_.
  auto.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  repeat php_.
  auto.
  exists wt, ot.
  assumption.
  }

  assert (EQ_6: fold_left ghplus (map gof (updl (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)), Or, C1, id))
           id' (Waiting4lock l, tx', phplus p' pm, M'of lv ++ O', ghplus C' Cm, id'))) (ghplus Cinv Cleak) = 
           fold_left ghplus (map gof T) (ghplus Cinv Cleak)).
  {
  apply foldg_left_upd_Notify with C1 Cm C'; repeat php_.
  apply gofs.
  intros.
  apply ghpdef_pair.
  repeat php_.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  rewrite <- C1Cm.
  repeat php_.
  auto.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  auto.
  }

  assert (phpdefpipl: phplusdef p Pinv /\ phplusdef p Pleak).
  {
  apply PHPD.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  repeat php_.
  auto.
  }

  assert (phpdefp1pipmi: phplusdef p1 Pinv /\ phplusdef pm Pinv).
  {
  apply phpdef_dist.
  rewrite <- p1pm.
  repeat php_.
  auto.
  }

  assert (phpdefp1plpml: phplusdef p1 Pleak /\ phplusdef pm Pleak).
  {
  apply phpdef_dist.
  rewrite <- p1pm.
  repeat php_.
  auto.
  }

  assert (phpdefp'ipl: phplusdef p' Pinv /\ phplusdef p' Pleak).
  {
  apply PHPD.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  auto.
  }

  assert (phpdefpp': phplusdef p p').
  {
  apply DEFL with id id';   repeat php_.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).  repeat php_.
  auto.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  repeat php_.
  auto.
  }

  assert (phpdefp'm: phplusdef p' pm).
  {
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  repeat php_.
  rewrite <- p1pm.  repeat php_.
  }

  assert (phpdefp1p': phplusdef p1 p').
  {
  apply phpdef_assoc_mon with pm.
  apply phpdef_comm.
  repeat php_.
  rewrite phplus_comm.
  rewrite <- p1pm.  repeat php_.
  apply phpdef_comm.
  repeat php_.
  }

  assert (bp'pm: boundph (phplus p' pm)).
  {
  apply boundph_mon with p1;
  repeat php_.
  rewrite phplus_assoc;  repeat php_.
  replace (phplus pm p1) with (phplus p1 pm);  repeat php_.
  rewrite <- p1pm.
  apply boundph_fold1 with (l:=T) (m:=pof) (b:= phplus Pinv Pleak) (id1:=id') (id2:=id);
  repeat php_.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  auto.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  repeat php_.
  auto.
  omega.
  }

  assert (ghpdefpipl: ghplusdef C Cinv /\ ghplusdef C Cleak).
  {
  apply GHPD.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  auto.
  }

  assert (ghpdefp1pipmi: ghplusdef C1 Cinv /\ ghplusdef Cm Cinv).
  {
  apply ghpdef_dist.
  rewrite <- C1Cm.
  repeat php_.
  auto.
  }

  assert (ghpdefp1plpml: ghplusdef C1 Cleak /\ ghplusdef Cm Cleak).
  {
  apply ghpdef_dist.
  rewrite <- C1Cm.
  repeat php_.
  auto.
  }

  assert (ghpdefp'ipl: ghplusdef C' Cinv /\ ghplusdef C' Cleak).
  {
  apply GHPD.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  auto.
  }

  assert (ghpdefpp': ghplusdef C C').
  {
  apply DEFLg with id id';  repeat php_.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  auto.
  }

  assert (ghpdefp'm: ghplusdef C' Cm).
  {
  apply ghpdef_comm.
  apply ghpdef_assoc_mon with C1.
  repeat php_.
  rewrite <- C1Cm.
  repeat php_.
  }

  assert (ghpdefp1p': ghplusdef C1 C').
  {
  apply ghpdef_assoc_mon with Cm.
  apply ghpdef_comm.
  repeat php_.
  rewrite ghplus_comm.
  rewrite <- C1Cm.
  repeat php_.
  apply ghpdef_comm.
  repeat php_.
  }

  assert (bcmc1: boundgh (ghplus Cm C1)).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:= ghplus Cinv Cleak);
  repeat php_.
  intros.
  apply ghpdef_pair;
  repeat php_.
  apply GHPD.
  repeat php_.
  apply GHPD.
  repeat php_.
  left.
  rewrite ghplus_comm.
  apply in_map_iff.
  rewrite <- C1Cm.
  exists (Notify v, tx, p, O, C, id).
  auto.
  apply ghpdef_comm.
  repeat php_.
  }

  assert (bcmc': boundgh (ghplus Cm C')).
  {
  rewrite ghplus_comm.
  apply boundgh_mon with C1.
  rewrite ghplus_assoc;
  repeat php_.
  apply boundgh_fold1 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak) (id1:=id')(id2:=id);
  repeat php_.
  intros.
  apply ghpdef_pair;
  repeat php_.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak);
  repeat php_.
  intros.
  apply ghpdef_pair;
  repeat php_.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  auto.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  auto.
  apply in_map_iff.
  rewrite ghplus_comm.
  rewrite <- C1Cm.
  exists (Notify v, tx, p, O, C, id).
  auto.
  apply ghpdef_comm.
  repeat php_.
  omega.
  apply ghpdef_comm.
  repeat php_.
  }

  assert (bpupd: boundph (upd (location_eq_dec Z.eq_dec) p1 ll
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)))).
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bc1m: boundgh (ghplus C1 Cm)).
  {
  rewrite <- C1Cm.
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  intros.
  apply ghpdef_pair; repeat php_.
  apply GHPD.
  inm_.
  apply GHPD.
  inm_.
  left.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  assert (bc1: boundgh C1).
  {
  apply boundgh_mon with Cm; try assumption.
  }

  rewrite EQ3.
  rewrite EQ_5.
  rewrite EQ_6.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  apply red_Notify with v v'; try assumption.
  }
  exists.
  {
  split.
  {
  intros.
  eapply SPUR1 with (c:=c).
  unfold updl in IN.
  rewrite map_map in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  destruct (Z.eq_dec (snd y) id).
  unfold cmdof in EQy.
  simpl in EQy.
  destruct (Z.eq_dec id id').
  omega.
  simpl in EQy.
  rewrite <- EQy in WASW.
  inversion WASW.
  destruct (Z.eq_dec (snd y) id').
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
  unfold upd in CONDv.
  destruct (location_eq_dec Z.eq_dec v1 ll).
  inversion CONDv.
  apply SPUR2 in CONDv.
  destruct CONDv as (a,(b,(c,d))).
  exists a, b.
  exists.
  unfold upd.
  destruct (location_eq_dec Z.eq_dec a ll).
  right.
  eexists.
  eexists.
  reflexivity.
  assumption.
  assumption.
  }

  exists.
  {
  exists.
  {
  apply defl_Notify with (z:=ll) (p1:=p1) (pm:=pm) (p':=p') (wt:=(upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1))) (ot:=ot);
  repeat php_.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  rewrite <- p1pm.
  auto.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  auto.
  exists wt, ot.
  assumption.
  }
  exists. assumption.
  exists.
  {
  intros.
  split.
  unfold updl in IN.
  rewrite map_map in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct x as (((((c2,tx2),p2),O2),g2),id2).
  simpl in *.
  destruct (Z.eq_dec id2 id).
  simpl in EQx.
  destruct (Z.eq_dec id id').
  contradiction.
  unfold pof in EQx.
  simpl in EQx.
  rewrite <- EQx.
  apply phpdef_locked.
  repeat php_.
  exists wt, ot.
  assumption.
  unfold pof in EQx.
  simpl in EQx.
  destruct (Z.eq_dec id2 id').
  simpl in EQx.
  rewrite <- EQx.
  apply phpdef_pair';
  repeat php_.
  simpl in EQx.
  rewrite <- EQx.
  apply PHPD.
  apply in_map_iff.
  exists (c2, tx2, p2, O2, g2, id2).
  auto.

  unfold updl in IN.
  rewrite map_map in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct x as (((((c2,tx2),p2),O2),g2),id2).
  simpl in *.
  destruct (Z.eq_dec id2 id).
  simpl in EQx.
  destruct (Z.eq_dec id id').
  contradiction.
  unfold pof in EQx.
  simpl in EQx.
  rewrite <- EQx.
  apply phpdef_locked.
  repeat php_.
  exists wt, ot.
  assumption.
  unfold pof in EQx.
  simpl in EQx.
  destruct (Z.eq_dec id2 id').
  simpl in EQx.
  rewrite <- EQx.
  apply phpdef_pair';
  repeat php_.
  simpl in EQx.
  rewrite <- EQx.
  apply PHPD.
  apply in_map_iff.
  exists (c2, tx2, p2, O2, g2, id2).
  auto.
  }
  exists.
  {
  intros.
  apply boundph_updl with (m:=pof) (l:=updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)), Or, C1, id)) (z:=id') (x:=(Waiting4lock l, tx', phplus p' pm, M'of lv ++ O', ghplus C' Cm, id')).
  intros.
  apply boundph_updl with (m:=pof) (l:=T) (z:=id) (x:=(tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)), Or, C1, id)).
  assumption.
  assumption.
  unfold pof.
  simpl.
  assumption.

  assumption.
  unfold pof.
  simpl.
  assumption.
  }
  exists.
  assumption.
  exists. assumption.
  exists. assumption.
  exists. 
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  apply phtoh_upd_locked'.
  exists wt, ot.
  repeat php_.
  assumption.
  }
  exists.
  {
  exists.
  {
  apply deflg_Notify with C1 Cm C';
  repeat php_.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  rewrite <- C1Cm.
  auto.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  auto.
  }
  exists.
  {
  unfold updl.
  rewrite map_map.
  rewrite map_map.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  simpl in EQx.
  destruct (Z.eq_dec id id').
  omega.
  unfold gof in EQx.
  simpl in EQx.
  rewrite <- EQx.
  repeat php_.
  tauto.
  destruct (Z.eq_dec (snd x) id').
  unfold gof in EQx.
  simpl in EQx.
  rewrite <- EQx.
  split.
  repeat php_.
  repeat php_.
  split.
  apply GHPD.
  rewrite <- EQx.
  apply in_map.
  auto.
  apply GHPD.
  rewrite <- EQx.
  apply in_map.
  auto.
  }
  exists. tauto.
  assumption.
  }
  exists.
  {
  intros.
  apply upd_updl.
  exists (Waiting4cond v' l, tx', p', O', C').
  apply in_updl_neq.
  assumption.
  assumption.
  intros.
  apply upd_updl.
  exists (Notify v, tx, p, O, C).
  assumption.
  assumption.
  }
  exists.
  {
  apply NoDup_updl.
  apply NoDup_updl.
  assumption.
  }
  exists.
  {
  exists. assumption.
  exists.
  {
  intros.
  apply AinvOK in IN.
  destruct IN as (EQ1,EQ2).
  unfold upd.
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  rewrite e in EQ1.
  rewrite LOCKED in EQ1.
  inversion EQ1.
  auto.
  }
  exists.
  {
  unfold upd at 1.
  intros.
  assert (ll0: l1 <> ll).
  {
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  inversion LOCK.
  assumption.
  }
  assert (INIL: In (subsas (snd (Iof l1)) (invs (fst (Iof l1)) (filterb (xOf (fun x  => Lof x) locs) (Aof l1)
    (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof l1) (count_occ Z.eq_dec (concat (map Aoof T))))), l1) Ainv).
  {
  apply INAOK.
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  contradiction.
  assumption.
  assumption.
  }
  rewrite <- FILw.
  assumption.
  unfold not.
  intros.
  assert (CO: l1 = ll).
  {
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  assumption.
  apply INJ.
  rewrite LOCK.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }
  contradiction.
  }
  assumption.
  }
  exists.
  {
  unfold injph.
  unfold inj.
  intros.

  assert (pxN: forall x1, upd (location_eq_dec Z.eq_dec) (fold_left phplus (map pof T) (phplus Pinv Pleak)) ll
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)) x1 <> None ->
    fold_left phplus (map pof T) (phplus Pinv Pleak) x1 <> None).
  {
  unfold upd.
  intros.
  destruct ((location_eq_dec Z.eq_dec) x1 ll).
  rewrite e.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }
  exists.
  {
  intros.
  apply INJ;
  try apply pxN;
  try assumption.
  }
  split. assumption.
  split.
  unfold upd.
  intros.  
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  split.
  intros.
  apply LOCs.
  rewrite e.
  rewrite LOCKED.
  apply some_none.
  intros.
  apply some_none.
  apply LOCs.
  intros.
  unfold upd.
  apply INO in IN.
  apply OBsOK in IN.
  destruct IN as (l',(EQl',pl')).
  exists l', EQl'.
  destruct ((location_eq_dec Z.eq_dec) l' ll).
  apply some_none.
  assumption.
  }
  exists.
  {
  exists.
  {
  unfold upd.
  intros.
  assert (G: Lof l1 = Aof l1 /\ Pof l1 = false /\ Xof l1 = None /\
    (h (Aof l1) <> Some 1%Z ->
    In (Oof l1) (concat (map oof T)))).
  {
  apply LOCKOK.
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  rewrite e.
  right.
  exists wt, ot.
  left.
  assumption.
  assumption.
  }
  destruct G as (G1,(G2,(G3,G4))).
  repeat split; try assumption.
  intros.
  apply INO'.
  apply G4.
  assumption.
  }
  exists.
  {
  unfold upd.
  intros.
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  inversion ULOCK.
  apply ULOCKOK in ULOCK.
  destruct ULOCK as (U1,U2).
  split.
  assumption.
  unfold not.
  intros.
  apply U2.
  eapply INO.
  apply H.
  }
  unfold upd.
  intros.
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  inversion UCOND.
  apply UCONDOK in UCOND.
  unfold not.
  intros.
  apply UCOND.
  eapply INO.
  apply H.
  }
  exists.
  {
  unfold upd.
  intros.
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  {
  rewrite e.
  assert (tmp: wt0 = upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1) /\ ot0 = ot).
  {
  split.
  destruct ULOCKED as [U|U].
  inversion U.
  reflexivity.
  inversion U.
  destruct ULOCKED as [U|U].
  inversion U.
  auto.
  inversion U.
  }
  destruct tmp as(eqwt,eqot).
  rewrite eqwt, eqot.

  assert (tmp: wt = filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v : Z => length (filter
           (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
           (map cmdof T))) /\
           ot = filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))).
  {
  apply WTsOTsOK.
  left.
  tauto.
  }
  destruct tmp as (wt1,ot1).
  split.
  apply functional_extensionality.
  intros.
  unfold upd.
  destruct (Z.eq_dec x ([[v]])).
  rewrite e0.
  unfold filterb.
  simpl.
  destruct (xOf (fun x0 => Lof x0) locs ([[v]])) eqn:XOF.
  assert (XOF1: xOf (fun x0 => Lof x0) locs ([[v]]) = Some (Lof lv)).
  {
  rewrite <- eqlv.
  apply xOf_same.
  apply in_map.
  assumption.
  assumption.
  }
  rewrite XOF in XOF1.
  inversion XOF1.
  destruct (Z.eq_dec ([[v]]) (Aof ll)).
  omega.
  rewrite <- eqll.
  rewrite eqz.
  rewrite wt1.
  unfold filterb.
  rewrite XOF.
  rewrite H0.
  rewrite <- eqll.
  destruct (Z.eq_dec ([[v]]) (Aof ll)).
  omega.
  rewrite eqz.
  rewrite updl_updl_neq.
  rewrite <- filter_updl_eq.
  simpl.
  apply filter_updl_inc.
  assumption.
  simpl.
  destruct (opZ_eq_dec None (Some ([[v]]))).
  inversion e1. 
  reflexivity.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  exists.
  unfold elem.
  apply filter_In.
  split.
  assumption.
  simpl.
  destruct (id' =? id')%Z eqn:zz.
  reflexivity.
  apply neqb_neq in zz.
  contradiction.
  intros.
  rewrite EQvv'.
  simpl.
  destruct (opZ_eq_dec (Some ([[v']])) (Some ([[v']]))).
  reflexivity.
  contradiction.
  simpl.
  destruct (opZ_eq_dec None (Some ([[v]]))).
  inversion e1.
  reflexivity.
  intros.
  simpl.
  unfold elem in IN.
  apply filter_In in IN.
  destruct IN as (IN,EQ).
  destruct x' as (((((x1,x2),x3),x4),x5),x6).
  simpl in EQ.
  apply Z.eqb_eq in EQ.
  rewrite EQ.  
  assert (EQa: (x1,x2,x3,x4,x5) = (Notify v, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN.
  apply in_updl_neq.
  rewrite EQ.
  omega.
  rewrite EQ.  
  assumption.
  apply NoDup_updl.
  assumption.
  inversion EQa.
  simpl.
  destruct (opZ_eq_dec None (Some ([[v]]))).
  inversion e1.
  reflexivity.
  assumption.
  rewrite wt1.
  apply xOf_exists1 in XOF.
  exfalso.
  apply XOF.
  exists lv, INlv.
  omega.

  rewrite wt1.
  unfold filterb.
  destruct (xOf (fun x0 => Lof x0) locs x) eqn:XOF.
  destruct (Z.eq_dec x (Aof ll)).
  reflexivity.
  destruct (Z.eq_dec z (Aof ll)).
  rewrite <- filter_updl_eq.
  rewrite <- filter_updl_eq.
  reflexivity.
  simpl.
  destruct (opZ_eq_dec None (Some x)).
  inversion e1.
  reflexivity.
  intros.
  unfold elem in IN.
  apply filter_In in IN.
  destruct IN as (IN,EQ).
  destruct x' as (((((x1,x2),x3),x4),x5),x6).
  simpl in EQ.
  apply Z.eqb_eq in EQ.
  rewrite EQ.  
  assert (EQa: (x1,x2,x3,x4,x5) = (Notify v, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN.
  rewrite EQ.
  assumption.
  assumption.
  rewrite EQa.
  simpl.
  destruct (opZ_eq_dec None (Some x)).
  inversion e1.
  reflexivity.
  simpl.
  destruct (opZ_eq_dec None (Some x)).
  inversion e1.
  reflexivity.
  intros.
  simpl.
  unfold elem in IN.
  apply filter_In in IN.
  destruct IN as (IN,EQ).
  destruct x' as (((((x1,x2),x3),x4),x5),x6).
  simpl in EQ.
  apply Z.eqb_eq in EQ.
  rewrite EQ in *.  
  assert (EQa: (x1,x2,x3,x4,x5) = (Waiting4cond v' l, tx', p', O', C')).
  eapply unique_key_eq.
  apply IN.
  apply in_updl_neq.
  assumption.
  assumption.
  apply NoDup_updl.
  assumption.
  inversion EQa.
  simpl.
  destruct (opZ_eq_dec (Some ([[v']])) (Some x)).
  inversion e1.
  omega.
  reflexivity.
  reflexivity.
  reflexivity.
  assumption.
  }

  assert (ULOCKED0:=ULOCKED).
  apply WTsOTsOK in ULOCKED.
  destruct ULOCKED as (wt1,ot1).
  rewrite wt1.
  split.
  unfold WTs.
  apply FILw.
  unfold not.
  intros.
  assert (CO: l1 = ll).
  {
  apply INJ.
  destruct ULOCKED0 as [U|U];
  rewrite U;
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }
  contradiction.
  assumption.
  }


  intros.
  unfold updl in ING.
  rewrite map_map in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold snd in EQ.
  simpl in EQ.
  unfold ctxof in EQ.
  unfold pof in EQ.
  unfold oof in EQ.
  unfold gof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  destruct (Z.eq_dec id id').
  contradiction.
(* ==================== x6 = id ===========*)
  rewrite e in IN.
  symmetry in EQ.
  inversion EQ.
  assert (EQX: (x1, x2, x3, x4, x5) = (Notify v, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN.
  assumption.
  assumption.
  inversion EQX.
  rewrite H6 in IN.
  rewrite H7 in IN.
  rewrite H8 in IN.
  rewrite H9 in IN.
  rewrite H10 in IN.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF1,(WP1,VOBS1)).
  exists.
  assumption.
  exists.
  unfold weakest_pre_ct.
  simpl.
  eapply sat_weak_imp1; try assumption.
  apply satp1m.
  intros.


  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  trivial.
  simpl in EQ.
  destruct (Z.eq_dec x6 id').
(* ==================== x6 = id' ===========*)
  rewrite e in IN.
  symmetry in EQ.
  inversion EQ.
  assert (EQX: (x1, x2, x3, x4, x5) = (Waiting4cond v' l, tx', p', O', C')).
  eapply unique_key_eq.
  apply IN.
  assumption.
  assumption.
  inversion EQX.
  rewrite H6 in IN.
  rewrite H7 in IN.
  rewrite H8 in IN.
  rewrite H9 in IN.
  rewrite H10 in IN.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF1,(WP1,VOBS1)).
  exists.
  assumption.

  assert (EQv0: v0 = lv).
  {
  apply INJ.
  rewrite fold_cond;
  try tauto.
  apply some_none.
  apply pofs.
  right.
  exists p'.
  exists.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  tauto.
  tauto.
  rewrite COND.
  apply some_none.
  omega.
  }
  rewrite EQv0 in *.
  exists.

  eapply sat_weak_imp1; try assumption.
  repeat php_.
  apply SAT2; repeat php_.
  apply boundgh_mon with C1.
  assumption.
  apply satm.
  assumption.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
(* ==================== x6 <> id id' ===========*)
  inversion EQ.
  rewrite H0 in IN.
  rewrite H1 in IN.
  rewrite H2 in IN.
  rewrite H3 in IN.
  rewrite H4 in IN.
  rewrite H5 in IN.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF1,(WP1,VOBS1)).
  exists.
  assumption.
  exists.

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
  apply WP1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  assert (tmp:=IN).
  rewrite W4COND in tmp.
  apply SOBS in tmp.
  destruct tmp as (WF'',(WP'',VOBS'')).
  apply sat_wait4cond in WP''.
  destruct WP'' as (l0',(v0',(eql0',(eqv',(p'v',(p'l0',(lofl0',(prcv0',(prcv',SAT2'))))))))).
  unfold WTs, OBs in VOBS''.

  assert (G: exists v l (_ : In v locs) (_ : In l locs) (_ : Aof v = ([[ev]])) (_ : Aof l = ([[el]])),
    safe_obs v (filterb (xOf (fun x  => Lof x) locs) (Aof l) (fun v0 : Z => length (filter
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0))) (map cmdof T))) ([[ev]]))
    (filterb (xOf (fun x  => Lof x) locs) (Aof l) (count_occ Z.eq_dec (concat (map Aoof T))) ([[ev]])) = true).
  {
  apply VOBS''.
  reflexivity.
  }

  destruct G as (v5,(l5,(INv5,(inl5,(eqv5,(eql5,safe5)))))).
  exists v5, l5, INv5, inl5, eqv5, eql5.

  assert (LK: fold_left phplus (map pof T) (phplus Pinv Pleak) l0 = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) l0 = Some (Locked wt ot)).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  right.
  right.
  exists p'.
  exists.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  auto.
  auto.
  }

  assert (CN: fold_left phplus (map pof T) (phplus Pinv Pleak) v0' = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists p0.
  exists.
  apply in_map_iff.
  exists (c, tx0, p0, O0, C0, id0).
  auto.
  auto.
  }

  assert (LK': fold_left phplus (map pof T) (phplus Pinv Pleak) l0' = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) l0' = Some (Locked wt ot)).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  right.
  right.
  exists p0.
  exists.
  apply in_map_iff.
  exists (c, tx0, p0, O0, C0, id0).
  auto.
  auto.
  }

  unfold filterb.
  unfold filterb in safe5.

  rewrite eql5 in *.

  assert (Lofv: xOf (fun x  => Lof x) locs ([[ev]]) = Some ([[el]])).
  {
  rewrite <- lofl0'.
  rewrite <- eqv'.
  apply xOf_same.
  apply in_map.
  apply LOCs.
  rewrite CN.
  apply some_none.
  apply comp_cons.
  apply LOCs.
  rewrite CN.
  apply some_none.
  unfold comp.
  intros.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  }
  rewrite Lofv in *.
  assert (NEQ1: ([[ev]]) <> ([[el]])).
  {
  rewrite <- eql0'.
  rewrite <- eqv'.
  unfold not.
  intros.
  assert (CO: v0' = l0').
  {
  apply INJ.
  rewrite CN.
  apply some_none.
  destruct LK' as [LK'|LK'].
  rewrite LK'.
  apply some_none.
  destruct LK' as (wt',(ot',LK')).
  rewrite LK'.
  apply some_none.
  assumption.
  }
  rewrite CO in CN.
  rewrite CN in LK'.
  destruct LK' as [LK'|LK'].
  inversion LK'.
  destruct LK' as (wt',(ot',LK')).
  inversion LK'.
  }

  destruct (Z.eq_dec ([[ev]]) ([[el]])).
  contradiction.
  rewrite eqz in *.
  rewrite eqz in *.

  assert (EQLEN2: length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) (Some ([[ev]]))))
    (map cmdof (updl (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)), Or, C1, id)) id'
    (Waiting4lock l, tx', phplus p' pm, M'of lv ++ O', ghplus C' Cm, id')))) <= (length (filter (fun c : cmd =>
    ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[ev]])))) (map cmdof T)))).
  {
  simpl.
  assert (NEQlev: ([[l]]) <> ([[ev]])).
  {
  unfold not.
  intros.
  assert (CO: l0 = v0').
  {
  apply INJ.
  destruct LK as [LK|LK].
  rewrite LK.
  apply some_none.
  destruct LK as (wt0,(ot0,LK)).
  rewrite LK.
  apply some_none.
  rewrite CN.
  apply some_none.
  omega.
  }
  rewrite <- CO in CN.
  rewrite CN in LK.
  destruct LK as [LK|LK].
  inversion LK.
  destruct LK as (wt1,(ot1,LK)).
  inversion LK.
  }

  destruct (Z.eq_dec ([[ev]]) ([[v]])) as [evv|evv].
  {
  rewrite <- filter_updl_inc.
  rewrite <- filter_updl_eq.
  omega.
  simpl.
  destruct (opZ_eq_dec None (Some ([[ev]]))).
  inversion e.
  reflexivity.
  intros.
  unfold elem in IN0.
  apply filter_In in IN0.
  destruct IN0 as (IN0,EQ1).
  destruct x' as (((((x1',x2'),x3'),x4'),x5'),x6').
  simpl in EQ1.
  apply Z.eqb_eq in EQ1.
  rewrite EQ1 in *.  
  assert (EQa: (x1',x2',x3',x4',x5') = (Notify v, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN0.
  assumption.
  assumption.
  inversion EQa.
  simpl.
  destruct (opZ_eq_dec None (Some ([[ev]]))).
  inversion e.
  reflexivity.
  apply NoDup_updl.
  assumption.
  simpl.
  destruct (opZ_eq_dec None (Some ([[ev]]))) .
  inversion e.
  reflexivity.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  exists.
  unfold elem.
  apply filter_In.
  split.
  apply in_updl_neq.
  assumption.
  assumption.
  simpl.
  apply Z.eqb_eq.
  reflexivity.
  simpl.
  rewrite <- EQvv'.
  rewrite evv.
  destruct (opZ_eq_dec (Some ([[v]])) (Some ([[v]]))).
  reflexivity.
  contradiction.
  }
  rewrite <- filter_updl_eq.
  rewrite <- filter_updl_eq.
  omega.
  simpl.
  destruct (opZ_eq_dec None (Some ([[ev]]))).
  inversion e.
  reflexivity.
  intros.
  unfold elem in IN0.
  apply filter_In in IN0.
  destruct IN0 as (IN0,EQ1).
  destruct x' as (((((x1',x2'),x3'),x4'),x5'),x6').
  simpl in EQ1.
  apply Z.eqb_eq in EQ1.
  rewrite EQ1 in *.  
  assert (EQa: (x1',x2',x3',x4',x5') = (Notify v, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN0.
  assumption.
  assumption.
  inversion EQa.
  simpl.
  destruct (opZ_eq_dec None (Some ([[ev]]))).
  inversion e.
  reflexivity.
  simpl.
  destruct (opZ_eq_dec None (Some ([[ev]]))) .
  inversion e.
  reflexivity.

  intros.
  unfold elem in IN0.
  apply filter_In in IN0.
  destruct IN0 as (IN0,EQ1).
  destruct x' as (((((x1',x2'),x3'),x4'),x5'),x6').
  simpl in EQ1.
  apply Z.eqb_eq in EQ1.
  rewrite EQ1 in *.  
  assert (EQa: (x1',x2',x3',x4',x5') = (Waiting4cond v' l, tx', p', O', C')).
  eapply unique_key_eq.
  apply IN0.
  apply in_updl_neq.
  assumption.
  assumption.
  apply NoDup_updl.
  assumption.
  inversion EQa.
  simpl.
  destruct (opZ_eq_dec None (Some ([[ev]]))).
  inversion e.
  rewrite <- EQvv'.
  destruct (opZ_eq_dec (Some ([[v]])) (Some ([[ev]]))).
  inversion e.
  omega.
  reflexivity.
  }
  eapply safe_obs_wt_weak.
  apply EQLEN2.
  assumption.
Qed.


Lemma Notify0_preserves_validity:
  forall m sp h t id v tx
         (CMD: t id = Some (Notify v, tx))
         (NWT : ~ (exists id' v' l tx' (EQvv': eval v = eval v'), t id' = Some (Waiting4cond v' l, tx')))
         (NWWT : ~ (exists id' v' l tx' (EQvv': eval v = eval v'), t id' = Some (WasWaiting4cond v' l, tx')))
         (VALID: validk (S m) sp t h),
    validk m sp (upd Z.eq_dec t id (Some (tt, tx))) h.
Proof.
  intros.
  unfold validk in VALID.
  destruct VALID as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
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
  unfold WTs, OBs.

  assert (tmp: exists p O C, In (Notify v, tx, p, O, C, id) T).
  {
  apply TOK.
  assumption.
  }

  destruct tmp as (p,(O,(C,INT))).
  exists (updl T id (tt, tx, p, O, C, id)).
  exists invs, locs, Pinv, Pleak, Ainv, Cinv, Cleak.

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
  apply sat_notify in WP.

  destruct WP as (p1,(pm,(C1,(Cm,(wt,(ot,(lv,(ll,(Or,(PERMOr,(bp1,(bpm,(bp1pm,(phpdefp1pm,(p1pm,(ghpdefC1Cm,(C1Cm,(eqlv,(eqll,(p1ll,(p1lv,(satm,(satp1,satp1m))))))))))))))))))))))).

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

  assert (pll: p ll = Some (Locked wt ot)).
  {
  rewrite p1pm.
  apply phplus_locked;
  try tauto.
  }

  assert (plv: p lv = Some Cond).
  {
  rewrite p1pm.
  unfold phplus.
  rewrite p1lv.
  reflexivity.
  }

  assert (LOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked wt ot)).
  {
  apply fold_locked;
  try tauto.
  apply pofs.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  auto.
  assumption.
  }

  assert (COND: fold_left phplus (map pof T) (phplus Pinv Pleak) lv = Some Cond).
  {
  eapply fold_cond with (m:=pof) (l:=T);
  try tauto.
  apply pofs.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  tauto.
  assumption.
  }

  assert (wtv: wt ([[v]]) = 0).
  {
  assert (tmp:wt = filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v : Z => length (filter
           (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) /\
           ot = filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))).
  {
  apply WTsOTsOK.
  left.
  assumption.
  }
  destruct tmp as (wteq,rest).
  rewrite wteq.
  simpl.
  unfold filterb.
  destruct (Z.eq_dec ([[v]]) (Aof ll)).
  destruct (xOf (fun x  => Lof x) locs ([[v]]));
  reflexivity.
  destruct (xOf (fun x  => Lof x) locs ([[v]])).
  destruct (Z.eq_dec z (Aof ll)).
  destruct (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[v]]))))
     (map cmdof T)) eqn:flt.
  reflexivity.
  assert (CO: In c (filter
        (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[v]]))))
        (map cmdof T))).
  {
  rewrite flt.
  left.
  reflexivity.
  }
  apply filter_In in CO.
  destruct CO as [INCO WC].
  exfalso.
  apply in_map_iff in INCO.
  destruct INCO as (x,(cx,INx)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  assert (tmp: t x6 = Some (x1,x2)).
  apply TOK.
  exists x3,x4,x5.
  assumption.
  unfold cmdof in cx.
  simpl in cx.
  rewrite cx in tmp.
  simpl in cx.
  unfold ifb in WC.
  destruct (opZ_eq_dec (waiting_for_cond c) (Some ([[v]]))).
  Focus 2.
  inversion WC.
  rewrite cx in INx.
  assert (wflc:=e0).
  destruct c;
  simpl in wflc;
  inversion wflc.
  {
  apply NWT.
  exists x6, v0, l0, x2.
  exists.
  symmetry.
  assumption.
  assumption.
  }
  {
  apply NWWT.
  exists x6, v0, l0, x2.
  exists.
  symmetry.
  assumption.
  assumption.
  }
  reflexivity.
  reflexivity.
  }
  rewrite eqlv in PERMOr.
  rewrite wtv in PERMOr.
  destruct (0 <? 0) eqn:cont.
  apply Nat.ltb_lt in cont.
  omega.

  assert (EQ_1: map pof (updl T id (tt, tx, p, O, C, id)) = map pof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Notify v, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQ_2:map (fun x => (pof x, snd x)) (updl T id (tt, tx, p, O, C, id)) =
               map (fun x => (pof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Notify v, tx, p, O, C)).
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

  assert (EQ_3: map oof (updl T id (tt, tx, p, O, C, id)) = map oof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Notify v, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQ_3': map Aoof (updl T id (tt, tx, p, O, C, id)) = map Aoof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Notify v, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQ_4: map gof (updl T id (tt, tx, p, O, C, id)) = map gof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Notify v, tx, p, O, C)).
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

  assert (EQ_4': map (fun x => (gof x, snd x)) (updl T id (tt, tx, p, O, C, id)) = map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Notify v, tx, p, O, C)).
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
          filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof (updl T id (tt, tx, p, O, C, id)) )).
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
  assert (EQa: (x1',x2',x3',x4',x5') = (Notify v, tx, p, O, C)).
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
           (map cmdof (updl T id (tt, tx, p, O, C, id)) ))) =
           (fun v0 : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0)))
           (map cmdof T)))).
  {
  apply functional_extensionality.
  intros.
  rewrite EQ_5.
  reflexivity.
  }

  assert (bp: boundph p).
  {
  apply BPE.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  split. reflexivity. assumption.
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
  exists (Notify v, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  rewrite EQ_1.
  rewrite EQ_2.
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
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  apply red_Notify0 with v; try assumption.

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
  assumption.
  }

  exists. tauto.
  exists. tauto.
  exists.
  {
  intros. 
  apply upd_updl; try tauto.
  exists (Notify v, tx, p, O, C).
  tauto.
  }
  exists.
  {
  apply NoDup_updl.
  assumption.
  }
  exists. tauto.
  exists. tauto.
  exists. tauto.
  exists. tauto.
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold snd in EQ.
  simpl in EQ.
  unfold ctxof in EQ.
  unfold pof in EQ.
  unfold oof in EQ.
  unfold gof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
(* ==================== x6 = id ===========*)
  rewrite e in IN.
  symmetry in EQ.
  inversion EQ.
  assert (EQX: (x1, x2, x3, x4, x5) = (Notify v, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN.
  assumption.
  assumption.
  inversion EQX.
  rewrite H6 in IN.
  rewrite H7 in IN.
  rewrite H8 in IN.
  rewrite H9 in IN.
  rewrite H10 in IN.
  exists.
  assumption.
  exists.
  assert (pmcm: pm = emp knowledge /\ Cm = emp (option nat * nat)).
  {
  apply satp1. omega.
  }
  destruct pmcm as (pmem,cmem).
  rewrite pmem, cmem in *.
  replace (upd (location_eq_dec Z.eq_dec) p1 ll (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot))) with p in satp1m.
  replace C1 with C in satp1m.
  apply sat_O_perm with Or; try assumption.
  eapply sat_weak_imp1; repeat php_.
  apply satp1m.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  rewrite C1Cm. repeat php_.
  rewrite p1pm. rewrite phplus_emp.
  unfold upd at 1.
  apply functional_extensionality.
  intros.
  destruct ((location_eq_dec Z.eq_dec) x ll).
  rewrite wtv.
  simpl.
  rewrite e0.
  rewrite upd_eq.
  tauto.
  tauto.
  reflexivity.
  intros.
  inversion W4COND.
  trivial.

(* ==================== x6 <> id ===========*)
  inversion EQ.
  rewrite H0 in IN.
  rewrite H1 in IN.
  rewrite H2 in IN.
  rewrite H3 in IN.
  rewrite H4 in IN.
  rewrite H5 in IN.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF1,(WP1,VOBS1)).
  exists.
  assumption.
  exists.

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
  apply WP1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  assumption.
Qed.


Lemma Notify01_preserves_validity1:
  forall m sp h t id id' v l tx tx'
         (CMD: t id = Some (Notify v, tx))
         (NWT: ~ exists id' v' l tx' (EQvv': ([[v]]) = ([[v']])), t id' = Some (Waiting4cond v' l,tx'))
         (WWT: exists v' (EQv' : ([[v]]) = ([[v']])), t id' = Some (WasWaiting4cond v' l, tx'))
         (VALID: validk (S m) sp t h),
    validk m sp (upd Z.eq_dec (upd Z.eq_dec t id (Some (tt, tx))) id' (Some (Waiting4lock l, tx'))) h.
Proof.
  intros.
  unfold validk in VALID.

  destruct VALID as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,((SPUR1,SPUR2),(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
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
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.

  rewrite map_map in *.


  destruct WWT as (v',(EQvv',CMD')).
  assert (NEQidid': id <> id').
  {
  unfold not.
  intros.
  rewrite H in CMD.
  rewrite CMD in CMD'.
  inversion CMD'.
  }

  assert (tmp: exists p O C, In (Notify v, tx, p, O, C, id) T).
  apply TOK.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  apply sat_notify in WP.

  destruct WP as (p1,(pm,(C1,(Cm,(wt,(ot,(lv,(ll,(Or,(PERMOr,(bp1,(bpm,(bp1pm,(phpdefp1pm,
    (p1pm,(ghpdefC1Cm,(C1Cm,(eqlv,(eqll,(p1ll,(p1lv,(satm,(satp1,satp1m))))))))))))))))))))))).

  assert (tmp: exists p' O' C', In (WasWaiting4cond v' l, tx', p', O', C', id') T).
  {
  apply TOK.
  assumption.
  }
  destruct tmp as (p',(O',(C',INT'))).

  assert (spt: sp = true).
  {
  eapply SPUR1 with (c:=WasWaiting4cond v' l).
  apply in_map_iff.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  auto.
  reflexivity.
  }
  rewrite spt in *.

  assert (tmp:=INT').
  apply SOBS in tmp.
  destruct tmp as (WF',(WP',VOBS')).
  unfold wellformed in WF'.
  simpl in WF'.
  apply sat_wait4cond in WP'.
  destruct WP' as (l0,(v0,(eql0,(eqv,(p'v,(p'l0,(lofl0,(prcv0,(prcv,SAT2))))))))).
  assert (bp: boundph p).
  {
  apply BPE.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  auto.
  }
  assert (bp': boundph p').
  {
  apply BPE.
  apply in_map_iff.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  auto.
  }

  assert (PHPD0: forall p0 : pheap, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  apply PHPD in H.
  apply phpdef_pair;
  tauto.
  }

  assert (pll: p ll = Some (Locked wt ot)).
  {
  rewrite p1pm.
  apply phplus_locked; repeat php_.
  }

  assert (plv: p lv = Some Cond).
  {
  rewrite p1pm.
  apply phplus_Cond;
  try tauto.
  }

  assert (LOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked wt ot)).
  {
  apply fold_locked.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  auto.
  assumption.
  }

  assert (COND: fold_left phplus (map pof T) (phplus Pinv Pleak) lv = Some Cond).
  {
  apply fold_cond;
  try tauto.
  apply pofs.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  tauto.
  assumption.
  }

  assert (neqvl: lv <> ll).
  {
  unfold not.
  intros.
  rewrite H in COND.
  rewrite COND in LOCKED.
  inversion LOCKED.
  }

  assert (neqavl: ([[v]]) <> Aof ll).
  {
  unfold not.
  intros.
  rewrite <- eqlv in H.
  assert (CO: lv = ll).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }
  contradiction.
  }

  assert (INlv: In lv locs).
  {
  apply LOCs.
  rewrite COND.
  apply some_none.
  }

  assert (COMPll: comp (ll :: locs) (fun x  => Aof x)).
  {
  unfold comp.
  intros.
  apply INJ.
  destruct IN as [EQ1|IN1].
  rewrite <- EQ1.
  rewrite LOCKED.
  apply some_none.
  apply LOCs.
  assumption.
  destruct IN0 as [EQ1|IN1].
  rewrite <- EQ1.
  rewrite LOCKED.
  apply some_none.
  apply LOCs.
  assumption.
  }

  assert (INll: In ll locs).
  {
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  }

  assert (COMPlv: comp (lv :: locs) (fun x  => Aof x)).
  {
  unfold comp.
  intros.
  apply INJ.
  destruct IN as [EQ1|IN1].
  rewrite <- EQ1.
  rewrite COND.
  apply some_none.
  apply LOCs.
  assumption.
  destruct IN0 as [EQ1|IN1].
  rewrite <- EQ1.
  rewrite COND.
  apply some_none.
  apply LOCs.
  assumption.
  }

  assert (wtv: lt 0 (wt ([[v]]))).
  {
  assert (tmp: wt = filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v : Z => length (filter
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof T))) /\
    ot = filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))).
  {
  apply WTsOTsOK.
  left.
  assumption.
  }
  destruct tmp as (wt1,ot1).
  rewrite wt1.
  unfold filterb.
  destruct (xOf (fun x  => Lof x) locs ([[v]])) eqn:XOF.
  assert (XOF1: xOf (fun x  => Lof x) locs ([[v]]) = Some (Lof lv)).
  {

  rewrite <- eqlv.
  apply xOf_same.
  apply in_map.
  assumption.
  assumption.
  }
  rewrite XOF in XOF1.
  inversion XOF1.
  destruct (Z.eq_dec ([[v]]) (Aof ll)).
  contradiction.
  rewrite <- eqll.
  rewrite eqz.
  assert (IN1: In (WasWaiting4cond v' l) (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[v]]))))
    (map cmdof T))).
  {
  apply filter_In.
  split.
  apply in_map_iff.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  auto.
  simpl.

  rewrite EQvv'.
  destruct (opZ_eq_dec (Some ([[v']])) (Some ([[v']]))).
  reflexivity.
  contradiction.
  }

  destruct (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[v]]))))
           (map cmdof T)).
  inversion IN1.
  simpl.
  omega.
  apply xOf_exists1 in XOF.
  exfalso.
  apply XOF.
  exists lv.
  exists.
  apply LOCs.
  rewrite COND.
  apply some_none.
  omega.
  }

  rewrite eqlv in PERMOr.
  destruct (0 <? wt ([[v]])) eqn:wt00.
  Focus 2.
  apply Nat.ltb_lt in wtv.
  rewrite wt00 in wtv.
  inversion wtv.

  assert (tmp: Lof ll = Aof ll /\
        Pof ll = false /\
        Xof ll = None /\
        (h (Aof ll) <> Some 1%Z -> In (Oof ll) (concat (map oof T)))).
  {
  apply LOCKOK.
  right.
  exists wt, ot.
  tauto.
  }
  destruct tmp as (lll,(plf,(ninrlxll,inlt))).

  exists (updl (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some (Locked (upd Z.eq_dec wt ([[v]]) ((wt ([[v]]) - 1)%nat)) ot)), Or, C1, id))
          id' (Waiting4lock l, tx',phplus p' pm, M'of lv ++ O', ghplus C' Cm, id')).

  exists invs, locs, Pinv, Pleak, Ainv, Cinv, Cleak.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (EQ3: count_occ Z.eq_dec (concat (map Aoof (updl (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)), Or, C1, id))
    id' (Waiting4lock l, tx', phplus p' pm, M'of lv ++ O', ghplus C' Cm, id')))) =
    count_occ Z.eq_dec (concat (map Aoof T))).
  {
  rewrite concat_move_eq with (O:=map (fun x : olocation Z => Aofo x) (M'of lv ++ O')) 
    (O1:=map (fun x : olocation Z => Aofo x) O') (O2:=map (fun x : olocation Z => Aofo x) (M'of lv)) (id:=id')
    (x:=((Waiting4lock l, tx', p', O', C', id'))); repeat php_.
  rewrite updl_updl.
  rewrite concat_move_eq with (O:=map (fun x : olocation Z => Aofo x) O) 
    (O1:=map (fun x : olocation Z => Aofo x) Or) (O2:=map (fun x : olocation Z => Aofo x) (M'of lv)) (id:=id)
    (x:=(tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)),
    Or, C1, id)); repeat php_.
  apply functional_extensionality.
  intros.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite <- map_updl_eq.
  reflexivity.
  apply NoDup_updl.
  assumption.
  intros.
  unfold updl in IN.
  apply in_map_iff in IN.
  destruct IN as ((a,aid),(EQa,INa)).
  simpl in *.
  destruct (Z.eq_dec aid id).
  inversion EQa.
  omega.
  inversion EQa.
  rewrite H1 in *.
  rewrite <- H0 in *.
  assert (EQa': a = (WasWaiting4cond v' l, tx', p', O', C')).
  {
  apply unique_key_eq with T id'; try assumption.
  }
  rewrite EQa'.
  reflexivity.
  rewrite <- map_app.
  apply Permutation_map.
  apply Permutation_trans with (M'of lv ++ Or).
  apply Permutation_app_comm.
  assumption.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  split.
  reflexivity.
  unfold elem.
  apply filter_In.
  split.
  assumption.
  apply Z.eqb_eq.
  reflexivity.
  apply NoDup_updl.
  apply NoDup_updl.
  assumption.
  rewrite <- map_app.
  apply Permutation_map.
  apply Permutation_app_comm.
  unfold elem.
  unfold updl.
  rewrite map_map.
  apply in_map_iff.
  exists (Waiting4lock l, tx', phplus p' pm, M'of lv ++ O', ghplus C' Cm, id').
  split.
  reflexivity.
  apply filter_In.
  split.
  apply in_map_iff.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  simpl.
  destruct (Z.eq_dec id' id).
  omega.
  simpl.
  rewrite eqz.
  auto.
  apply Z.eqb_eq.
  reflexivity.
  }

  assert (INO: forall o p1 p2 C (IN: In o (concat (map oof (updl (updl T id
    (tt, tx, p1, Or, C1, id)) id' (Waiting4lock l, tx', p2, M'of lv ++ O', C, id'))))),
    In o (concat (map oof T))).
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  rewrite map_map in IN.
  rewrite <- flat_map_concat_map in IN.
  apply in_flat_map in IN.
  destruct IN as (x,(INx,INl0)).
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold oof in *.
  simpl in *.
  destruct (Z.eq_dec x6 id).
  simpl in *.
  rewrite e in *.
  destruct (Z.eq_dec id id').
  omega.
  assert (EQX: (x1, x2, x3, x4, x5) = (Notify v, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  }
  inversion EQX.
  exists (Notify v, tx, p, O, C, id).
  split.
  assumption.
  apply Permutation_in with (M'of lv ++ Or).
  simpl.
  assumption.
  apply in_app_iff.
  right.
  assumption.
  simpl in *.
  destruct (Z.eq_dec x6 id').
  apply in_app_iff in INl0.
  destruct INl0 as [IN|IN].
  exists (Notify v, tx, p, O, C, id).
  split.
  assumption.
  apply Permutation_in with (M'of lv ++ Or).
  simpl.
  assumption.
  apply in_app_iff.
  left.
  assumption.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  auto.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }

  assert (INO': forall o p1 p2 C (IN: In o (concat (map oof T))),
    In o (concat (map oof (updl (updl T id
    (tt, tx, p1, Or, C1, id)) id' (Waiting4lock l, tx', p2, M'of lv ++ O', C, id'))))).
  {
  intros.
  unfold updl.
  rewrite map_map.
  rewrite map_map.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  rewrite <- flat_map_concat_map in IN.
  apply in_flat_map in IN.
  destruct IN as (x,(INx,INl0)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold oof in *.
  simpl in *.
  destruct (Z.eq_dec x6 id).
  simpl in *.
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (Notify v, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  }
  inversion EQX.
  rewrite H3 in INl0.
  apply Permutation_in with (l':=M'of lv ++ Or) in INl0.
  apply in_app_iff in INl0.
  destruct INl0 as [IN|IN].
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  split.
  assumption.
  simpl.
  destruct (Z.eq_dec id id').
  omega.
  destruct (Z.eq_dec id' id).
  omega.
  rewrite eqz.
  apply in_app_iff.
  left.
  assumption.
  exists (Notify v, tx, p, O, C, id).
  split.
  assumption.
  rewrite eqz.
  simpl.
  destruct (Z.eq_dec id id').
  omega.
  assumption.
  apply Permutation_sym.
  assumption.
  destruct (Z.eq_dec x6 id').
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (WasWaiting4cond v' l, tx', p', O', C')).
  {
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  }
  inversion EQX.
  rewrite H3 in INl0.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  split.
  assumption.
  simpl.
  destruct (Z.eq_dec id' id).
  omega.
  rewrite eqz.
  apply in_app_iff.
  right.
  assumption.
  exists (x1, x2, x3, x4, x5, x6).
  split.
  assumption.
  simpl.
  destruct (Z.eq_dec x6 id).
  omega.
  simpl.
  destruct (Z.eq_dec x6 id').
  omega.
  assumption.
  }

  assert (FILw: forall l0 (ll0: l0 <> (Aof ll)),
    (filterb (xOf (fun x  => Lof x) locs) l0 (fun v : Z => length (filter (fun c : cmd =>
    ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))) =
    (filterb (xOf (fun x  => Lof x) locs) l0 (fun v0 : Z => length (filter (fun c : cmd => 
    ifb (opZ_eq_dec (waiting_for_cond c) (Some v0)))
    (map cmdof (updl (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some (Locked (upd Z.eq_dec wt ([[v]]) ((wt ([[v]]) - 1)%nat)) ot)), Or, C1, id))
    id' (Waiting4lock l, tx', phplus p' pm, M'of lv ++ O', ghplus C' Cm, id'))))))).
  {
  intros.
  unfold filterb.
  apply functional_extensionality.
  intros.
  destruct (xOf (fun x0 => Lof x0) locs x) eqn:XOF.
  destruct (Z.eq_dec x l1) as [xl0|xl0].
  reflexivity.
  destruct (Z.eq_dec z l1) as [lxl0|lxl0].
  Focus 2.
  reflexivity.
  destruct (Z.eq_dec x (Aof ll)) as [xl|xl].
  assert (XOF1: xOf (fun x0 => Lof x0) locs x = Some (Lof ll)).
  {
  rewrite xl.
  apply xOf_same.
  apply in_map.
  assumption.
  assumption.
  }
  rewrite XOF in XOF1.
  inversion XOF1.
  omega.
  destruct (Z.eq_dec x ([[v]])) as [xv|xv].
  assert (XOF1: xOf (fun x0 => Lof x0) locs x = Some (Lof lv)).
  {
  rewrite xv.
  rewrite <- eqlv.
  apply xOf_same.
  apply in_map.
  assumption.
  assumption.
  }
  rewrite XOF in XOF1.
  inversion XOF1.
  omega.

  rewrite <- filter_updl_eq.
  rewrite <- filter_updl_eq.
  reflexivity.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some x)).
  inversion e.
  reflexivity.
  intros.
  assert (X': x' = (Notify v, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some x)).
  inversion e.
  reflexivity.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some x)).
  inversion e.
  reflexivity.
  intros.
  assert (X': x' = (WasWaiting4cond v' l, tx', p', O', C', id')).
  apply in_elem with (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)), Or, C1, id)).
  apply NoDup_updl.
  assumption.
  apply in_updl_neq.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec (Some ([[v']])) (Some x)).
  inversion e.
  rewrite <- EQvv' in H0.
  rewrite H0 in xv.
  contradiction.
  reflexivity.
  reflexivity.
  }

  assert (EQ_5: fold_left phplus (map pof (updl (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)), Or, C1, id))
           id' (Waiting4lock l, tx', phplus p' pm, M'of lv ++ O', ghplus C' Cm, id'))) (phplus Pinv Pleak) = 
           upd (location_eq_dec Z.eq_dec) (fold_left phplus (map pof T) (phplus Pinv Pleak)) ll (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot))).
  {
  apply fold_left_upd_Notify with p1 pm p'; repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  rewrite <- p1pm.
  repeat php_.
  auto.
  apply in_map_iff.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  repeat php_.
  auto.
  exists wt, ot.
  assumption.
  }

  assert (EQ_6: fold_left ghplus (map gof (updl (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)), Or, C1, id))
           id' (Waiting4lock l, tx', phplus p' pm, M'of lv ++ O', ghplus C' Cm, id'))) (ghplus Cinv Cleak) = 
           fold_left ghplus (map gof T) (ghplus Cinv Cleak)).
  {
  apply foldg_left_upd_Notify with C1 Cm C'; repeat php_.
  apply gofs.
  intros.
  apply ghpdef_pair.
  repeat php_.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  rewrite <- C1Cm.
  repeat php_.
  auto.
  apply in_map_iff.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  auto.
  }

  assert (phpdefpipl: phplusdef p Pinv /\ phplusdef p Pleak).
  {
  apply PHPD.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  repeat php_.
  auto.
  }

  assert (phpdefp1pipmi: phplusdef p1 Pinv /\ phplusdef pm Pinv).
  {
  apply phpdef_dist.
  rewrite <- p1pm.
  repeat php_.
  auto.
  }

  assert (phpdefp1plpml: phplusdef p1 Pleak /\ phplusdef pm Pleak).
  {
  apply phpdef_dist.
  rewrite <- p1pm.
  repeat php_.
  auto.
  }

  assert (phpdefp'ipl: phplusdef p' Pinv /\ phplusdef p' Pleak).
  {
  apply PHPD.
  apply in_map_iff.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  auto.
  }

  assert (phpdefpp': phplusdef p p').
  {
  apply DEFL with id id';   repeat php_.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).  repeat php_.
  auto.
  apply in_map_iff.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  repeat php_.
  auto.
  }

  assert (phpdefp'm: phplusdef p' pm).
  {
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  repeat php_.
  rewrite <- p1pm.  repeat php_.
  }

  assert (phpdefp1p': phplusdef p1 p').
  {
  apply phpdef_assoc_mon with pm.
  apply phpdef_comm.
  repeat php_.
  rewrite phplus_comm.
  rewrite <- p1pm.  repeat php_.
  apply phpdef_comm.
  repeat php_.
  }

  assert (bp'pm: boundph (phplus p' pm)).
  {
  apply boundph_mon with p1;
  repeat php_.
  rewrite phplus_assoc;  repeat php_.
  replace (phplus pm p1) with (phplus p1 pm);  repeat php_.
  rewrite <- p1pm.
  apply boundph_fold1 with (l:=T) (m:=pof) (b:= phplus Pinv Pleak) (id1:=id') (id2:=id);
  repeat php_.
  apply in_map_iff.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  auto.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  repeat php_.
  auto.
  omega.
  }

  assert (ghpdefpipl: ghplusdef C Cinv /\ ghplusdef C Cleak).
  {
  apply GHPD.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  auto.
  }

  assert (ghpdefp1pipmi: ghplusdef C1 Cinv /\ ghplusdef Cm Cinv).
  {
  apply ghpdef_dist.
  rewrite <- C1Cm.
  repeat php_.
  auto.
  }

  assert (ghpdefp1plpml: ghplusdef C1 Cleak /\ ghplusdef Cm Cleak).
  {
  apply ghpdef_dist.
  rewrite <- C1Cm.
  repeat php_.
  auto.
  }

  assert (ghpdefp'ipl: ghplusdef C' Cinv /\ ghplusdef C' Cleak).
  {
  apply GHPD.
  apply in_map_iff.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  auto.
  }

  assert (ghpdefpp': ghplusdef C C').
  {
  apply DEFLg with id id';  repeat php_.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  auto.
  }

  assert (ghpdefp'm: ghplusdef C' Cm).
  {
  apply ghpdef_comm.
  apply ghpdef_assoc_mon with C1.
  repeat php_.
  rewrite <- C1Cm.
  repeat php_.
  }

  assert (ghpdefp1p': ghplusdef C1 C').
  {
  apply ghpdef_assoc_mon with Cm.
  apply ghpdef_comm.
  repeat php_.
  rewrite ghplus_comm.
  rewrite <- C1Cm.
  repeat php_.
  apply ghpdef_comm.
  repeat php_.
  }

  assert (bcmc1: boundgh (ghplus Cm C1)).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:= ghplus Cinv Cleak);
  repeat php_.
  intros.
  apply ghpdef_pair;
  repeat php_.
  apply GHPD.
  repeat php_.
  apply GHPD.
  repeat php_.
  left.
  rewrite ghplus_comm.
  apply in_map_iff.
  rewrite <- C1Cm.
  exists (Notify v, tx, p, O, C, id).
  auto.
  apply ghpdef_comm.
  repeat php_.
  }

  assert (bcmc': boundgh (ghplus Cm C')).
  {
  rewrite ghplus_comm.
  apply boundgh_mon with C1.
  rewrite ghplus_assoc;
  repeat php_.
  apply boundgh_fold1 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak) (id1:=id')(id2:=id);
  repeat php_.
  intros.
  apply ghpdef_pair;
  repeat php_.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak);
  repeat php_.
  intros.
  apply ghpdef_pair;
  repeat php_.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  auto.
  apply in_map_iff.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  auto.
  apply in_map_iff.
  rewrite ghplus_comm.
  rewrite <- C1Cm.
  exists (Notify v, tx, p, O, C, id).
  auto.
  apply ghpdef_comm.
  repeat php_.
  omega.
  apply ghpdef_comm.
  repeat php_.
  }

  assert (bupd: boundph (upd (location_eq_dec Z.eq_dec) p1 ll
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)))).
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bg: boundgh C').
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
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  split. reflexivity. assumption.
  }

  rewrite EQ3.
  rewrite EQ_5.
  rewrite EQ_6.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  apply red_Notify01 with v; try assumption.
  exists v'.
  exists. assumption.
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
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  destruct (Z.eq_dec (snd y) id).
  unfold cmdof in EQy.
  simpl in EQy.
  destruct (Z.eq_dec id id').
  omega.
  simpl in EQy.
  rewrite <- EQy in WASW.
  inversion WASW.
  destruct (Z.eq_dec (snd y) id').
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
  unfold upd in CONDv.
  destruct (location_eq_dec Z.eq_dec v1 ll).
  inversion CONDv.
  apply SPUR2 in CONDv.
  destruct CONDv as (a,(b,(c,d))).
  exists a, b.
  exists.
  unfold upd.
  destruct (location_eq_dec Z.eq_dec a ll).
  right.
  eexists.
  eexists.
  reflexivity.
  assumption.
  assumption.
  }

  exists.
  {
  exists.
  {
  apply defl_Notify with (z:=ll) (p1:=p1) (pm:=pm) (p':=p') (wt:=(upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1))) (ot:=ot);
  repeat php_.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  rewrite <- p1pm.
  auto.
  apply in_map_iff.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  auto.
  exists wt, ot.
  assumption.
  }
  exists. assumption.
  exists.
  {
  intros.
  split.
  unfold updl in IN.
  rewrite map_map in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct x as (((((c2,tx2),p2),O2),g2),id2).
  simpl in *.
  destruct (Z.eq_dec id2 id).
  simpl in EQx.
  destruct (Z.eq_dec id id').
  contradiction.
  unfold pof in EQx.
  simpl in EQx.
  rewrite <- EQx.
  apply phpdef_locked.
  repeat php_.
  exists wt, ot.
  assumption.
  unfold pof in EQx.
  simpl in EQx.
  destruct (Z.eq_dec id2 id').
  simpl in EQx.
  rewrite <- EQx.
  apply phpdef_pair';
  repeat php_.
  simpl in EQx.
  rewrite <- EQx.
  apply PHPD.
  apply in_map_iff.
  exists (c2, tx2, p2, O2, g2, id2).
  auto.

  unfold updl in IN.
  rewrite map_map in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct x as (((((c2,tx2),p2),O2),g2),id2).
  simpl in *.
  destruct (Z.eq_dec id2 id).
  simpl in EQx.
  destruct (Z.eq_dec id id').
  contradiction.
  unfold pof in EQx.
  simpl in EQx.
  rewrite <- EQx.
  apply phpdef_locked.
  repeat php_.
  exists wt, ot.
  assumption.
  unfold pof in EQx.
  simpl in EQx.
  destruct (Z.eq_dec id2 id').
  simpl in EQx.
  rewrite <- EQx.
  apply phpdef_pair';
  repeat php_.
  simpl in EQx.
  rewrite <- EQx.
  apply PHPD.
  apply in_map_iff.
  exists (c2, tx2, p2, O2, g2, id2).
  auto.
  }
  exists.
  {
  intros.
  apply boundph_updl with (m:=pof) (l:=updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)), Or, C1, id)) (z:=id') (x:=(Waiting4lock l, tx', phplus p' pm, M'of lv ++ O', ghplus C' Cm, id')).
  intros.
  apply boundph_updl with (m:=pof) (l:=T) (z:=id) (x:=(tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)), Or, C1, id)).
  assumption.
  assumption.
  unfold pof.
  simpl.
  assumption.
  assumption.
  unfold pof.
  simpl.
  assumption.
  }
  exists.
  assumption.
  exists. assumption.
  exists. assumption.
  exists. 
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  apply phtoh_upd_locked'.
  exists wt, ot.
  repeat php_.
  assumption.
  }
  exists.
  {
  exists.
  {
  apply deflg_Notify with C1 Cm C';
  repeat php_.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  rewrite <- C1Cm.
  auto.
  apply in_map_iff.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  auto.
  }
  exists.
  {
  unfold updl.
  rewrite map_map.
  rewrite map_map.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  simpl in EQx.
  destruct (Z.eq_dec id id').
  omega.
  unfold gof in EQx.
  simpl in EQx.
  rewrite <- EQx.
  repeat php_.
  tauto.
  destruct (Z.eq_dec (snd x) id').
  unfold gof in EQx.
  simpl in EQx.
  rewrite <- EQx.
  split.
  repeat php_.
  repeat php_.
  split.
  apply GHPD.
  rewrite <- EQx.
  apply in_map.
  auto.
  apply GHPD.
  rewrite <- EQx.
  apply in_map.
  auto.
  }
  exists. tauto.
  assumption.
  }
  exists.
  {
  intros.
  apply upd_updl.
  exists (WasWaiting4cond v' l, tx', p', O', C').
  apply in_updl_neq.
  assumption.
  assumption.
  intros.
  apply upd_updl.
  exists (Notify v, tx, p, O, C).
  assumption.
  assumption.
  }
  exists.
  {
  apply NoDup_updl.
  apply NoDup_updl.
  assumption.
  }
  exists.
  {
  exists. assumption.
  exists.
  {
  intros.
  apply AinvOK in IN.
  destruct IN as (EQ1,EQ2).
  unfold upd.
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  rewrite e in EQ1.
  rewrite LOCKED in EQ1.
  inversion EQ1.
  auto.
  }
  exists.
  {
  unfold upd at 1.
  intros.
  assert (ll0: l1 <> ll).
  {
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  inversion LOCK.
  assumption.
  }
  assert (INIL: In (subsas (snd (Iof l1)) (invs (fst (Iof l1)) (filterb (xOf (fun x  => Lof x) locs) (Aof l1)
    (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof l1) (count_occ Z.eq_dec (concat (map Aoof T))))), l1) Ainv).
  {
  apply INAOK.
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  contradiction.
  assumption.
  assumption.
  }
  rewrite <- FILw.
  assumption.
  unfold not.
  intros.
  assert (CO: l1 = ll).
  {
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  assumption.
  apply INJ.
  rewrite LOCK.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }
  contradiction.
  }
  assumption.
  }
  exists.
  {
  unfold injph.
  unfold inj.
  intros.

  assert (pxN: forall x1, upd (location_eq_dec Z.eq_dec) (fold_left phplus (map pof T) (phplus Pinv Pleak)) ll
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)) x1 <> None ->
    fold_left phplus (map pof T) (phplus Pinv Pleak) x1 <> None).
  {
  unfold upd.
  intros.
  destruct ((location_eq_dec Z.eq_dec) x1 ll).
  rewrite e.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }
  exists.
  {
  intros.
  apply INJ;
  try apply pxN;
  try assumption.
  }
  split. assumption.
  split.
  unfold upd.
  intros.  
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  split.
  intros.
  apply LOCs.
  rewrite e.
  rewrite LOCKED.
  apply some_none.
  intros.
  apply some_none.
  apply LOCs.
  intros.
  unfold upd.
  apply INO in IN.
  apply OBsOK in IN.
  destruct IN as (l',(EQl',pl')).
  exists l', EQl'.
  destruct ((location_eq_dec Z.eq_dec) l' ll).
  apply some_none.
  assumption.
  }
  exists.
  {
  exists.
  {
  unfold upd.
  intros.
  assert (G: Lof l1 = Aof l1 /\ Pof l1 = false /\ Xof l1 = None /\
    (h (Aof l1) <> Some 1%Z ->
    In (Oof l1) (concat (map oof T)))).
  {
  apply LOCKOK.
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  rewrite e.
  right.
  exists wt, ot.
  left.
  assumption.
  assumption.
  }
  destruct G as (G1,(G2,(G3,G4))).
  repeat split; try assumption.
  intros.
  apply INO'.
  apply G4.
  assumption.
  }
  exists.
  {
  unfold upd.
  intros.
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  inversion ULOCK.
  apply ULOCKOK in ULOCK.
  destruct ULOCK as (U1,U2).
  split.
  assumption.
  unfold not.
  intros.
  apply U2.
  eapply INO.
  apply H.
  }
  unfold upd.
  intros.
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  inversion UCOND.
  apply UCONDOK in UCOND.
  unfold not.
  intros.
  apply UCOND.
  eapply INO.
  apply H.
  }
  exists.
  {
  unfold upd.
  intros.
  destruct ((location_eq_dec Z.eq_dec) l1 ll).
  {
  rewrite e.
  assert (tmp: wt0 = upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1) /\ ot0 = ot).
  {
  split.
  destruct ULOCKED as [U|U].
  inversion U.
  reflexivity.
  inversion U.
  destruct ULOCKED as [U|U].
  inversion U.
  auto.
  inversion U.
  }
  destruct tmp as(eqwt,eqot).
  rewrite eqwt, eqot.

  assert (tmp: wt = filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v : Z => length (filter
           (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
           (map cmdof T))) /\
           ot = filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))).
  {
  apply WTsOTsOK.
  left.
  tauto.
  }
  destruct tmp as (wt1,ot1).
  split.
  apply functional_extensionality.
  intros.
  unfold upd.
  destruct (Z.eq_dec x ([[v]])).
  rewrite e0.
  unfold filterb.
  simpl.
  destruct (xOf (fun x0 => Lof x0) locs ([[v]])) eqn:XOF.
  assert (XOF1: xOf (fun x0 => Lof x0) locs ([[v]]) = Some (Lof lv)).
  {
  rewrite <- eqlv.
  apply xOf_same.
  apply in_map.
  assumption.
  assumption.
  }
  rewrite XOF in XOF1.
  inversion XOF1.
  destruct (Z.eq_dec ([[v]]) (Aof ll)).
  omega.
  rewrite <- eqll.
  rewrite eqz.
  rewrite wt1.
  unfold filterb.
  rewrite XOF.
  rewrite H0.
  rewrite <- eqll.
  destruct (Z.eq_dec ([[v]]) (Aof ll)).
  omega.
  rewrite eqz.
  rewrite updl_updl_neq.
  rewrite <- filter_updl_eq.
  simpl.
  apply filter_updl_inc.
  assumption.
  simpl.
  destruct (opZ_eq_dec None (Some ([[v]]))).
  inversion e1. 
  reflexivity.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  exists.
  unfold elem.
  apply filter_In.
  split.
  assumption.
  simpl.
  destruct (id' =? id')%Z eqn:zz.
  reflexivity.
  apply neqb_neq in zz.
  contradiction.
  intros.
  rewrite EQvv'.
  simpl.
  destruct (opZ_eq_dec (Some ([[v']])) (Some ([[v']]))).
  reflexivity.
  contradiction.
  simpl.
  destruct (opZ_eq_dec None (Some ([[v]]))).
  inversion e1.
  reflexivity.
  intros.
  simpl.
  unfold elem in IN.
  apply filter_In in IN.
  destruct IN as (IN,EQ).
  destruct x' as (((((x1,x2),x3),x4),x5),x6).
  simpl in EQ.
  apply Z.eqb_eq in EQ.
  rewrite EQ.  
  assert (EQa: (x1,x2,x3,x4,x5) = (Notify v, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN.
  apply in_updl_neq.
  rewrite EQ.
  omega.
  rewrite EQ.  
  assumption.
  apply NoDup_updl.
  assumption.
  inversion EQa.
  simpl.
  destruct (opZ_eq_dec None (Some ([[v]]))).
  inversion e1.
  reflexivity.
  assumption.
  rewrite wt1.
  apply xOf_exists1 in XOF.
  exfalso.
  apply XOF.
  exists lv, INlv.
  omega.

  rewrite wt1.
  unfold filterb.
  destruct (xOf (fun x0 => Lof x0) locs x) eqn:XOF.
  destruct (Z.eq_dec x (Aof ll)).
  reflexivity.
  destruct (Z.eq_dec z (Aof ll)).
  rewrite <- filter_updl_eq.
  rewrite <- filter_updl_eq.
  reflexivity.
  simpl.
  destruct (opZ_eq_dec None (Some x)).
  inversion e1.
  reflexivity.
  intros.
  unfold elem in IN.
  apply filter_In in IN.
  destruct IN as (IN,EQ).
  destruct x' as (((((x1,x2),x3),x4),x5),x6).
  simpl in EQ.
  apply Z.eqb_eq in EQ.
  rewrite EQ.  
  assert (EQa: (x1,x2,x3,x4,x5) = (Notify v, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN.
  rewrite EQ.
  assumption.
  assumption.
  rewrite EQa.
  simpl.
  destruct (opZ_eq_dec None (Some x)).
  inversion e1.
  reflexivity.
  simpl.
  destruct (opZ_eq_dec None (Some x)).
  inversion e1.
  reflexivity.
  intros.
  simpl.
  unfold elem in IN.
  apply filter_In in IN.
  destruct IN as (IN,EQ).
  destruct x' as (((((x1,x2),x3),x4),x5),x6).
  simpl in EQ.
  apply Z.eqb_eq in EQ.
  rewrite EQ in *.  
  assert (EQa: (x1,x2,x3,x4,x5) = (WasWaiting4cond v' l, tx', p', O', C')).
  eapply unique_key_eq.
  apply IN.
  apply in_updl_neq.
  assumption.
  assumption.
  apply NoDup_updl.
  assumption.
  inversion EQa.
  simpl.
  destruct (opZ_eq_dec (Some ([[v']])) (Some x)).
  inversion e1.
  omega.
  reflexivity.
  reflexivity.
  reflexivity.
  assumption.
  }

  assert (ULOCKED0:=ULOCKED).
  apply WTsOTsOK in ULOCKED.
  destruct ULOCKED as (wt1,ot1).
  rewrite wt1.
  split.
  unfold WTs.
  apply FILw.
  unfold not.
  intros.
  assert (CO: l1 = ll).
  {
  apply INJ.
  destruct ULOCKED0 as [U|U];
  rewrite U;
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }
  contradiction.
  assumption.
  }


  intros.
  unfold updl in ING.
  rewrite map_map in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold snd in EQ.
  simpl in EQ.
  unfold ctxof in EQ.
  unfold pof in EQ.
  unfold oof in EQ.
  unfold gof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  simpl in EQ.
  destruct (Z.eq_dec id id').
  contradiction.
(* ==================== x6 = id ===========*)
  rewrite e in IN.
  symmetry in EQ.
  inversion EQ.
  assert (EQX: (x1, x2, x3, x4, x5) = (Notify v, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN.
  assumption.
  assumption.
  inversion EQX.
  rewrite H6 in IN.
  rewrite H7 in IN.
  rewrite H8 in IN.
  rewrite H9 in IN.
  rewrite H10 in IN.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF1,(WP1,VOBS1)).
  exists.
  assumption.
  exists.
  unfold weakest_pre_ct.
  simpl.
  eapply sat_weak_imp1; try assumption.
  apply boundgh_mon with Cm; repeat php_.
  apply satp1m.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  trivial.
  simpl in EQ.
  destruct (Z.eq_dec x6 id').
(* ==================== x6 = id' ===========*)
  rewrite e in IN.
  symmetry in EQ.
  inversion EQ.
  assert (EQX: (x1, x2, x3, x4, x5) = (WasWaiting4cond v' l, tx', p', O', C')).
  eapply unique_key_eq.
  apply IN.
  assumption.
  assumption.
  inversion EQX.
  rewrite H6 in IN.
  rewrite H7 in IN.
  rewrite H8 in IN.
  rewrite H9 in IN.
  rewrite H10 in IN.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF1,(WP1,VOBS1)).
  exists.
  assumption.

  assert (EQv0: v0 = lv).
  {
  apply INJ.
  rewrite fold_cond;
  try tauto.
  apply some_none.
  apply pofs.
  right.
  exists p'.
  exists.
  apply in_map_iff.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  tauto.
  tauto.
  rewrite COND.
  apply some_none.
  omega.
  }
  rewrite EQv0 in *.
  exists.
  eapply sat_weak_imp1; try assumption.
  repeat php_.
  apply SAT2; repeat php_.
  apply boundgh_mon with C1.
  assumption.
  intros.
  apply satm.
  omega.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
(* ==================== x6 <> id id' ===========*)
  inversion EQ.
  rewrite H0 in IN.
  rewrite H1 in IN.
  rewrite H2 in IN.
  rewrite H3 in IN.
  rewrite H4 in IN.
  rewrite H5 in IN.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF1,(WP1,VOBS1)).
  exists.
  assumption.
  exists.

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
  apply WP1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  assert (tmp:=IN).
  rewrite W4COND in tmp.
  apply SOBS in tmp.
  destruct tmp as (WF'',(WP'',VOBS'')).
  apply sat_wait4cond in WP''.
  destruct WP'' as (l0',(v0',(eql0',(eqv',(p'v',(p'l0',(lofl0',(prcv0',(prcv',SAT2'))))))))).
  unfold WTs, OBs in VOBS''.

  assert (G: exists v l (_ : In v locs) (_ : In l locs) (_ : Aof v = ([[ev]])) (_ : Aof l = ([[el]])),
    safe_obs v (filterb (xOf (fun x  => Lof x) locs) (Aof l) (fun v0 : Z => length (filter
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0))) (map cmdof T))) ([[ev]]))
    (filterb (xOf (fun x  => Lof x) locs) (Aof l) (count_occ Z.eq_dec (concat (map Aoof T))) ([[ev]])) = true).
  {
  apply VOBS''.
  reflexivity.
  }

  destruct G as (v5,(l5,(INv5,(inl5,(eqv5,(eql5,safe5)))))).
  exists v5, l5, INv5, inl5, eqv5, eql5.

  assert (LK: fold_left phplus (map pof T) (phplus Pinv Pleak) l0 = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) l0 = Some (Locked wt ot)).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  right.
  right.
  exists p'.
  exists.
  apply in_map_iff.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  auto.
  auto.
  }

  assert (CN: fold_left phplus (map pof T) (phplus Pinv Pleak) v0' = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists p0.
  exists.
  apply in_map_iff.
  exists (c, tx0, p0, O0, C0, id0).
  auto.
  auto.
  }

  assert (LK': fold_left phplus (map pof T) (phplus Pinv Pleak) l0' = Some Lock \/
    exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) l0' = Some (Locked wt ot)).
  {
  apply fold_lock_ed; repeat php_.
  apply pofs.
  right.
  right.
  exists p0.
  exists.
  apply in_map_iff.
  exists (c, tx0, p0, O0, C0, id0).
  auto.
  auto.
  }

  unfold filterb.
  unfold filterb in safe5.

  rewrite eql5 in *.

  assert (Lofv: xOf (fun x  => Lof x) locs ([[ev]]) = Some ([[el]])).
  {
  rewrite <- lofl0'.
  rewrite <- eqv'.
  apply xOf_same.
  apply in_map.
  apply LOCs.
  rewrite CN.
  apply some_none.
  apply comp_cons.
  apply LOCs.
  rewrite CN.
  apply some_none.
  unfold comp.
  intros.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  }
  rewrite Lofv in *.
  assert (NEQ1: ([[ev]]) <> ([[el]])).
  {
  rewrite <- eql0'.
  rewrite <- eqv'.
  unfold not.
  intros.
  assert (CO: v0' = l0').
  {
  apply INJ.
  rewrite CN.
  apply some_none.
  destruct LK' as [LK'|LK'].
  rewrite LK'.
  apply some_none.
  destruct LK' as (wt',(ot',LK')).
  rewrite LK'.
  apply some_none.
  assumption.
  }
  rewrite CO in CN.
  rewrite CN in LK'.
  destruct LK' as [LK'|LK'].
  inversion LK'.
  destruct LK' as (wt',(ot',LK')).
  inversion LK'.
  }

  destruct (Z.eq_dec ([[ev]]) ([[el]])).
  contradiction.
  rewrite eqz in *.
  rewrite eqz in *.

  assert (EQLEN2: length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) (Some ([[ev]]))))
    (map cmdof (updl (updl T id (tt, tx, upd (location_eq_dec Z.eq_dec) p1 ll (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)) ot)), Or, C1, id)) id'
    (Waiting4lock l, tx', phplus p' pm, M'of lv ++ O', ghplus C' Cm, id')))) <= (length (filter (fun c : cmd =>
    ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[ev]])))) (map cmdof T)))).
  {
  simpl.
  assert (NEQlev: ([[l]]) <> ([[ev]])).
  {
  unfold not.
  intros.
  assert (CO: l0 = v0').
  {
  apply INJ.
  destruct LK as [LK|LK].
  rewrite LK.
  apply some_none.
  destruct LK as (wt0,(ot0,LK)).
  rewrite LK.
  apply some_none.
  rewrite CN.
  apply some_none.
  omega.
  }
  rewrite <- CO in CN.
  rewrite CN in LK.
  destruct LK as [LK|LK].
  inversion LK.
  destruct LK as (wt1,(ot1,LK)).
  inversion LK.
  }

  destruct (Z.eq_dec ([[ev]]) ([[v]])) as [evv|evv].
  {
  rewrite <- filter_updl_inc.
  rewrite <- filter_updl_eq.
  omega.
  simpl.
  destruct (opZ_eq_dec None (Some ([[ev]]))).
  inversion e.
  reflexivity.
  intros.
  unfold elem in IN0.
  apply filter_In in IN0.
  destruct IN0 as (IN0,EQ1).
  destruct x' as (((((x1',x2'),x3'),x4'),x5'),x6').
  simpl in EQ1.
  apply Z.eqb_eq in EQ1.
  rewrite EQ1 in *.  
  assert (EQa: (x1',x2',x3',x4',x5') = (Notify v, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN0.
  assumption.
  assumption.
  inversion EQa.
  simpl.
  destruct (opZ_eq_dec None (Some ([[ev]]))).
  inversion e.
  reflexivity.
  apply NoDup_updl.
  assumption.
  simpl.
  destruct (opZ_eq_dec None (Some ([[ev]]))) .
  inversion e.
  reflexivity.
  exists (WasWaiting4cond v' l, tx', p', O', C', id').
  exists.
  unfold elem.
  apply filter_In.
  split.
  apply in_updl_neq.
  assumption.
  assumption.
  simpl.
  apply Z.eqb_eq.
  reflexivity.
  simpl.
  rewrite <- EQvv'.
  rewrite evv.
  destruct (opZ_eq_dec (Some ([[v]])) (Some ([[v]]))).
  reflexivity.
  contradiction.
  }
  rewrite <- filter_updl_eq.
  rewrite <- filter_updl_eq.
  omega.
  simpl.
  destruct (opZ_eq_dec None (Some ([[ev]]))).
  inversion e.
  reflexivity.
  intros.
  unfold elem in IN0.
  apply filter_In in IN0.
  destruct IN0 as (IN0,EQ1).
  destruct x' as (((((x1',x2'),x3'),x4'),x5'),x6').
  simpl in EQ1.
  apply Z.eqb_eq in EQ1.
  rewrite EQ1 in *.  
  assert (EQa: (x1',x2',x3',x4',x5') = (Notify v, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN0.
  assumption.
  assumption.
  inversion EQa.
  simpl.
  destruct (opZ_eq_dec None (Some ([[ev]]))).
  inversion e.
  reflexivity.
  simpl.
  destruct (opZ_eq_dec None (Some ([[ev]]))) .
  inversion e.
  reflexivity.

  intros.
  unfold elem in IN0.
  apply filter_In in IN0.
  destruct IN0 as (IN0,EQ1).
  destruct x' as (((((x1',x2'),x3'),x4'),x5'),x6').
  simpl in EQ1.
  apply Z.eqb_eq in EQ1.
  rewrite EQ1 in *.  
  assert (EQa: (x1',x2',x3',x4',x5') = (WasWaiting4cond v' l, tx', p', O', C')).
  eapply unique_key_eq.
  apply IN0.
  apply in_updl_neq.
  assumption.
  assumption.
  apply NoDup_updl.
  assumption.
  inversion EQa.
  simpl.
  destruct (opZ_eq_dec None (Some ([[ev]]))).
  inversion e.
  rewrite <- EQvv'.
  destruct (opZ_eq_dec (Some ([[v]])) (Some ([[ev]]))).
  inversion e.
  omega.
  reflexivity.
  }
  eapply safe_obs_wt_weak.
  apply EQLEN2.
  assumption.
Qed.


Definition wkupmap z t : (cmd * context * pheap * list (olocation Z) * gheap * Z) :=
  (wakeupcmd z (cmdof t), ctxof t, pof t, oof t, gof t, snd t).

Lemma NotifyAll_preserves_validity:
  forall m sp h t id v tx
         (VALID: validk (S m) sp t h)
         (CMD : t id = Some (NotifyAll v, tx)),
    validk m sp (upd Z.eq_dec (wakeupthrds ([[v]]) t) id (Some (tt,tx))) h.
Proof.
  intros.
  unfold validk in VALID.
  destruct VALID as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,(SPUR,(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS)))))))))))))))))).
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
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.

  assert (tmp: exists p O C, In (NotifyAll v, tx, p, O, C, id) T).
  {
  apply TOK.
  assumption.
  }

  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  destruct WF as (WF1,WF2).
  apply sat_notifyAll in WP.

  destruct WP as (wt,(ot,(lv,(ll,(M'nil,(eqlv,(eqll,(pl,(pv,(EMP,sat1)))))))))).

  exists (updl (map (wkupmap ([[v]])) T) id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Locked (upd Z.eq_dec wt ([[v]]) 0%nat) ot)), O, C, id)).
  exists invs, locs, Pinv, Pleak, Ainv, Cinv, Cleak.

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  subst.

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

  assert (LOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked wt ot)).
  {
  apply fold_locked; repeat php_.
  apply pofs.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (NotifyAll v, tx, p, O, C, id).
  auto.
  assumption.
  }

  assert (COND: fold_left phplus (map pof T) (phplus Pinv Pleak) lv = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (NotifyAll v, tx, p, O, C, id).
  auto.
  assumption.
  }


  assert (neqvl: lv <> ll).
  {
  unfold not.
  intros.
  rewrite H in COND.
  rewrite COND in LOCKED.
  inversion LOCKED.
  }

  assert (EQ_2: fold_left phplus (map pof (updl (map (wkupmap ([[v]])) T) id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll
   (Some (Locked (upd Z.eq_dec wt ([[v]]) 0%nat) ot)), O, C, id))) (phplus Pinv Pleak) = 
    upd (location_eq_dec Z.eq_dec) (fold_left phplus (map pof T) (phplus Pinv Pleak)) ll (Some (Locked (upd Z.eq_dec wt ([[v]]) 0%nat) ot))).
  {
  apply fold_left_upd_NotifyAll with p; repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (NotifyAll v, tx, p, O, C, id).
  auto.
  exists wt, ot.
  assumption.
  intros.
  unfold wkupmap.
  unfold pof.
  simpl.
  split; reflexivity.
  }

  assert (COND': fold_left phplus (map pof (updl (map (wkupmap ([[v]])) T) id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll
   (Some (Locked (upd Z.eq_dec wt ([[v]]) 0%nat) ot)), O, C, id))) (phplus Pinv Pleak) lv = Some Cond).
  {
  rewrite EQ_2.
  unfold upd.
  destruct ((location_eq_dec Z.eq_dec) lv ll).
  contradiction.
  assumption.
  }

  assert (EQ_3: map oof (updl (map (wkupmap ([[v]])) T) id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Locked (upd Z.eq_dec wt ([[v]]) 0%nat) ot)), O, C, id)) = map oof T).
  {
  unfold updl.
  rewrite map_map.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  simpl.
  assert (EQa: (a1,a2,a3,a4,a5) = (NotifyAll v, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQa.
  reflexivity.
  simpl.
  reflexivity.
  }
  assert (EQ_3': map Aoof (updl (map (wkupmap ([[v]])) T) id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Locked (upd Z.eq_dec wt ([[v]]) 0%nat) ot)), O, C, id)) = map Aoof T).
  {
  unfold updl.
  rewrite map_map.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  simpl.
  assert (EQa: (a1,a2,a3,a4,a5) = (NotifyAll v, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQa.
  reflexivity.
  simpl.
  reflexivity.
  }
  assert (EQ_4: map gof (updl (map (wkupmap ([[v]])) T) id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Locked (upd Z.eq_dec wt ([[v]]) 0%nat) ot)), O, C, id)) =
                map gof T).
  {
  unfold updl.
  rewrite map_map.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  simpl.
  assert (EQa: (a1,a2,a3,a4,a5) = (NotifyAll v, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQa.
  reflexivity.
  simpl.
  reflexivity.
  }
  assert (EQ_4': map (fun x => (gof x, snd x)) (updl (map (wkupmap ([[v]])) T) id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Locked (upd Z.eq_dec wt ([[v]]) 0%nat) ot)), O, C, id)) =
                map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  simpl.
  assert (EQa: (a1,a2,a3,a4,a5) = (NotifyAll v, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQa.
  rewrite e.
  reflexivity.
  simpl.
  reflexivity.
  }

  assert (EQW: forall x ot0 (NEQ:x <> ([[v]])), length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some x))) (map cmdof T)) =
    length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some x))) (map cmdof
    (updl (map (wkupmap ([[v]])) T) id (tt, tx, fun a => if (location_eq_dec Z.eq_dec) a ll then
    Some (Locked (fun a0 : Z => if Z.eq_dec a0 ([[v]]) then 0%nat else WTs ll (map cmdof T) locs a0) ot0) else p a, O, C, id))))).
  {
  unfold updl.
  intros.
  rewrite map_map.
  rewrite map_map.
  apply filter_map_eq.
  intros.
  destruct x0 as (((((x1,x2),x3),x4),x5),x6).
  unfold cmdof.
  simpl.
  destruct (Z.eq_dec x6 id).
  assert (EQX: (x1, x2, x3, x4, x5) = (NotifyAll v, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply IN.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQX.
  simpl.
  reflexivity.
  simpl.
  destruct x1;
  simpl;
  try reflexivity.

  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  simpl.
  destruct ((opZ_eq_dec (Some ([[v0]])) (Some x))).
  inversion e0.
  omega.
  destruct ((opZ_eq_dec None (Some x))).
  inversion e0.
  reflexivity.
  reflexivity.

  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  simpl.
  destruct ((opZ_eq_dec (Some ([[v0]])) (Some x))).
  inversion e0.
  omega.
  destruct ((opZ_eq_dec None (Some x))).
  inversion e0.
  reflexivity.
  reflexivity.
  }

  assert (len0: forall p', length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) (Some ([[v]]))))
    (map cmdof (updl (map (wkupmap ([[v]])) T) id (tt, tx, p', O, C, id)))) = 0%nat).
  {
  intros.
  destruct (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[v]]))))
   (map cmdof (updl (map (wkupmap ([[v]])) T) id (tt, tx, p', O, C, id)))) eqn:fil.
  reflexivity.
  assert (CO: In c (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[v]]))))
    (map cmdof (updl (map (wkupmap ([[v]])) T) id (tt, tx, p', O, C, id))))).
  {
  rewrite fil.
  left.
  reflexivity.
  }
  apply filter_In in CO.
  destruct CO as (CO1,CO2).
  unfold updl in CO1.
  rewrite map_map in CO1.
  rewrite map_map in CO1.
  apply in_map_iff in CO1.
  destruct CO1 as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd (wkupmap ([[v]]) x1)) id).
  unfold cmdof in EQ1.
  simpl in EQ1.
  rewrite <- EQ1 in CO2.
  simpl in CO2.
  destruct ((opZ_eq_dec None (Some ([[v]])))).
  inversion e0.
  inversion CO2.
  rewrite <- EQ1 in CO2.
  unfold wkupmap in CO2.
  unfold cmdof in CO2.
  simpl in CO2.
  rewrite wfwk in CO2.
  inversion CO2.
  }

  assert (FIL: forall l (NEQ:l <> ll)
    (fl: fold_left phplus (map pof T) (phplus Pinv Pleak) l <> None),
    filterb (xOf (fun x  => Lof x) locs) (Aof l)
    (fun v0 : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0)))
    (map cmdof T))) = filterb (xOf (fun x  => Lof x) locs) (Aof l) (fun v0 : Z => length
    (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0)))
    (map cmdof (updl (map (wkupmap ([[v]])) T) id (tt, tx, upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (upd Z.eq_dec wt ([[v]]) 0%nat) ot)), O, C, id)))))).
  intros.
  rewrite <- filterb_updl_eq.
  {
  rewrite map_map.
  unfold filterb.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x (Aof l)).
  reflexivity.
  destruct (xOf (fun x0 => Lof x0) locs x) eqn:XOF.
  destruct (Z.eq_dec z (Aof l)).
  rewrite e in XOF.
  apply filter_map_eq.
  intros.
  destruct x0 as (((((x1,x2),x3),x4),x5),x6).
  unfold cmdof.
  simpl.
  destruct x1;
  simpl;
  try reflexivity.

  {
  destruct ((opZ_eq_dec (Some ([[v0]])) (Some x))).
  inversion e0.
  destruct (Z.eq_dec ([[v0]]) ([[v]])).

  assert (XOF1: xOf (fun x0 => Lof x0) locs x = Some (Aof ll)).
  {
  rewrite <- H0.
  rewrite e1.

  rewrite <- eqlv.
  rewrite eqll.
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
  rewrite XOF in XOF1.
  {
  exfalso.
  apply NEQ.
  apply INJ.
  assumption.
  rewrite LOCKED.
  apply some_none.
  inversion XOF1.
  reflexivity.
  }
  simpl.
  rewrite e0.
  destruct (opZ_eq_dec (Some x) (Some x)).
  reflexivity.
  contradiction.

  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  simpl.
  symmetry.
  destruct ((opZ_eq_dec None (Some x))).
  inversion e1.
  reflexivity.
  simpl.
  destruct (opZ_eq_dec (Some ([[v0]])) (Some x)).
  contradiction.
  reflexivity.
  }

  {
  destruct ((opZ_eq_dec (Some ([[v0]])) (Some x))).
  inversion e0.
  destruct (Z.eq_dec ([[v0]]) ([[v]])).

  assert (XOF1: xOf (fun x0 => Lof x0) locs x = Some (Aof ll)).
  {
  rewrite <- H0.
  rewrite e1.

  rewrite <- eqlv.
  rewrite eqll.
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
  rewrite XOF in XOF1.
  {
  exfalso.
  apply NEQ.
  apply INJ.
  assumption.
  rewrite LOCKED.
  apply some_none.
  inversion XOF1.
  reflexivity.
  }
  simpl.
  rewrite e0.
  destruct (opZ_eq_dec (Some x) (Some x)).
  reflexivity.
  contradiction.

  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  simpl.
  symmetry.
  destruct ((opZ_eq_dec None (Some x))).
  inversion e1.
  reflexivity.
  simpl.
  destruct (opZ_eq_dec (Some ([[v0]])) (Some x)).
  contradiction.
  reflexivity.
  }
  reflexivity.
  reflexivity.
  }
  {
  intros.
  split.
  unfold cmdof.
  simpl.
  destruct ((opZ_eq_dec None (Some v0))).
  inversion e.
  reflexivity.
  intros.
  assert (X': x' = (NotifyAll v, tx, p, O, C, id)).
  apply in_elem with (map (wkupmap ([[v]])) T).
  rewrite map_map.
  assumption.
  apply in_elem_in.
  unfold elem.
  apply filter_In.
  split.
  apply in_map_iff.
  exists (NotifyAll v, tx, p, O, C, id).
  auto.
  simpl.
  apply Z.eqb_eq.
  reflexivity.
  assumption.
  rewrite X'.
  simpl.
  destruct ((opZ_eq_dec None (Some v0))).
  inversion e.
  reflexivity.
  }

  assert (bupd: boundph (upd (location_eq_dec Z.eq_dec) p ll
   (Some (Locked (upd Z.eq_dec wt ([[v]]) 0) ot)))).
  {
  apply boundph_upd.
  apply BPE.
  apply in_map_iff.
  exists (NotifyAll v, tx, p, O, C, id).
  auto.
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
  exists (NotifyAll v, tx, p, O, C, id).
  split. reflexivity. assumption.
  }

  rewrite EQ_2.
  rewrite EQ_3.
  rewrite EQ_3'.
  rewrite EQ_4.
  rewrite EQ_4'.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with sp t h.
  assumption.
  apply red_NotifyAll.
  assumption.
  }

  exists.
  {
  unfold spur_ok.
  destruct SPUR as (SPUR0,SPUR).
  split.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd (wkupmap ([[v]]) x)) id).
  rewrite WASW in EQx.
  inversion EQx.
  eapply SPUR0 with (c:=c).
  apply in_map_iff.
  exists x.
  split.
  destruct x as (((((a1,a2),a3),a4),a5),a6).
  unfold cmdof in EQx.
  simpl in EQx.
  unfold cmdof in *.
  simpl in *.
  rewrite WASW in *.
  destruct a1;
  inversion EQx.
  destruct (Z.eq_dec ([[v1]]) ([[v]])).
  inversion H0.
  reflexivity.
  destruct (Z.eq_dec ([[v1]]) ([[v]])).
  inversion H0.
  reflexivity.
  assumption.
  apply WASW.
  }
  
  intros.
  unfold upd at 1 in CONDv.
  destruct (location_eq_dec Z.eq_dec v0 ll).
  inversion CONDv.
  apply SPUR in CONDv.
  destruct CONDv as (a,(b,(c,d))).
  exists a, b.
  exists.
  unfold upd.
  destruct (location_eq_dec Z.eq_dec a ll).
  right.
  eexists.
  eexists.
  reflexivity.
  assumption.
  assumption.
  }
  exists.
  {
  split.
  {
  apply defl_NotifyAll with (z:=ll) (p:=p) (wt:=(upd Z.eq_dec wt ([[v]]) 0%nat)) (ot:=ot); repeat php_.
  apply in_map_iff.
  exists (NotifyAll v, tx, p, O, C, id).
  auto.
  exists wt, ot.
  assumption.
  }
  split. assumption.
  split.
  {
  intros.
  unfold updl in IN.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  unfold pof in EQ.
  simpl in EQ.
  rewrite <- EQ.
  split.
  apply phpdef_locked.
  apply PHPD.
  apply in_map_iff.
  exists (NotifyAll v, tx, p, O, C, id).
  auto.
  exists wt, ot.
  assumption.
  apply phpdef_locked.
  apply PHPD.
  apply in_map_iff.
  exists (NotifyAll v, tx, p, O, C, id).
  auto.
  exists wt, ot.
  assumption.
  unfold pof in EQ.
  simpl in EQ.
  rewrite <- EQ.
  apply PHPD.
  apply in_map_iff in IN.
  destruct IN as (x',(EQ',IN)).
  apply in_map_iff.
  exists x'.
  unfold wkupmap in EQ'.
  simpl in EQ'.
  inversion EQ'.
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
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
  unfold pof in EQ.
  simpl in EQ.
  rewrite <- EQ.
  assumption.
  apply in_map_iff in IN.
  destruct IN as (x',(EQ',IN)).
  unfold wkupmap in EQ'.
  unfold pof in EQ.
  simpl in EQ.
  rewrite <- EQ.
  simpl in EQ'.
  inversion EQ'.
  apply BPE.
  apply in_map_iff.
  exists x'.
  auto.
  }
  exists.
  assumption.
  split. assumption.
  split. assumption.
  split.
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }
  assert (PH:=PH2H).
  unfold phtoh in *.
  destruct PH as (PH1, PH2).
  unfold phtoh.
  split.
  intros.
  specialize PH1 with l.
  unfold upd.
  destruct ((location_eq_dec Z.eq_dec) l ll).
  rewrite e in *.
  rewrite LOCKED in PH1.
  assumption.
  assumption.
  intros.
  apply PH2.
  intros.
  apply NONE in EQ.
  unfold upd in EQ.
  destruct ((location_eq_dec Z.eq_dec) l ll).
  inversion EQ.
  assumption.
  }
  exists.
  {
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
  }
  exists.
  {
  intros.
  apply upd_updl.
  exists (NotifyAll v, tx, p, O, C).
  apply in_map_iff.
  exists (NotifyAll v, tx, p, O, C, id).
  auto.
  intros.
  split.
  intros.
  unfold wakeupthrds in H.
  unfold wakeupthrd in H.
  destruct (t id1) eqn:tid1.
  destruct p0.
  inversion H.
  apply TOK in tid1.
  destruct tid1 as (p1,(O1,(C1,IN1))).
  exists p1, O1, C1.
  apply in_map_iff.
  exists (c1, c2, p1, O1, C1, id1).
  rewrite H2 in *.
  auto.
  inversion H.
  intros.
  destruct H as (p1,(O1,(C1,IN1))).
  unfold wakeupthrds.
  unfold wakeupthrd.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  destruct x1 as (((((x1,x2),x3),x4),x5),x6).
  unfold wkupmap in EQ1.
  simpl in EQ1.
  inversion EQ1.
  rewrite H5 in IN1.
  assert (tid1: t id1 = Some (x1, x2)).
  apply TOK.
  exists x3, x4, x5.
  assumption.
  rewrite tid1.
  rewrite <- H1.
  reflexivity.
  }
  exists.
  {
  apply NoDup_updl.
  rewrite map_map.
  unfold wkupmap.
  assumption.
  }
  exists.
  {
  split. assumption.
  split.
  {
  intros.
  unfold upd.
  destruct ((location_eq_dec Z.eq_dec) l ll).
  rewrite e in *.
  apply AinvOK in IN.
  destruct IN as (CO,IN).
  rewrite LOCKED in CO.
  inversion CO.
  apply AinvOK.
  assumption.
  }
  split.
  {
  intros.
  unfold upd in LOCK.
  destruct ((location_eq_dec Z.eq_dec) l ll).
  inversion LOCK.
  rewrite <- FIL.
  apply INAOK.
  assumption.
  assumption.
  assumption.
  rewrite LOCK.
  apply some_none.
  }
  assumption.
  }
  exists.
  {
  split.
  {
  unfold injph.
  unfold upd.
  intros.
  apply INJ.
  destruct ((location_eq_dec Z.eq_dec) x1 ll).
  rewrite e in *.
  rewrite LOCKED.
  apply some_none.
  assumption.
  destruct ((location_eq_dec Z.eq_dec) x2 ll).
  rewrite e in *.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }
  split. assumption.
  split.
  intros.
  unfold upd.
  destruct ((location_eq_dec Z.eq_dec) l ll).
  rewrite e in *.
  split.
  intros.
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  intros.
  apply some_none.
  apply LOCs.
  intros.
  unfold upd.
  apply OBsOK in IN.
  destruct IN as (l',(EQl',pl')).
  exists l', EQl'.
  destruct ((location_eq_dec Z.eq_dec) l' ll).
  apply some_none.
  assumption.
  }
  exists.
  {
  split.
  {
  unfold upd.
  intros.
  destruct ((location_eq_dec Z.eq_dec) l ll).
  rewrite e in *.
  apply LOCKOK.
  right.
  exists wt, ot.
  left.
  assumption.
  apply LOCKOK.
  assumption.
  }
  split.
  {
  unfold upd.
  intros.
  destruct ((location_eq_dec Z.eq_dec) l ll).
  rewrite e in *.
  inversion ULOCK.
  apply ULOCKOK with wt0 ot0.
  assumption.
  }
  unfold upd.
  intros.
  destruct ((location_eq_dec Z.eq_dec) l ll).
  rewrite e in *.
  inversion UCOND.
  apply UCONDOK.
  assumption.
  }
  exists.
  {
  unfold upd.
  intros.
  destruct ((location_eq_dec Z.eq_dec) l ll).
  {
  rewrite e in *.
  assert (G: wt = WTs ll (map cmdof T) locs /\
           ot = OBs ll (concat (map Aoof T)) locs).
  {
  apply WTsOTsOK.
  left.
  assumption.
  }
  destruct G as (G1,G2).
  destruct ULOCKED as [U|U].
  {
  inversion U.
  replace (fun a : Z => if Z.eq_dec a ([[v]]) then 0%nat else wt a) with
    (fun a : Z => if Z.eq_dec a ([[v]]) then 0%nat else (WTs ll (map cmdof T) locs) a).
  unfold WTs at 1.
  unfold filterb in *.
  split.
  {
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x ([[v]])).
  rewrite e0 in *.
  destruct (xOf (fun x0 => Lof x0) locs ([[v]])).
  destruct (Z.eq_dec ([[v]]) (Aof ll)).
  reflexivity.
  destruct (Z.eq_dec z (Aof ll)).
  rewrite len0.
  reflexivity.
  reflexivity.
  reflexivity.
  destruct (xOf (fun x0 => Lof x0) locs x) eqn:XOF.
  destruct (Z.eq_dec x (Aof ll)).
  reflexivity.
  destruct (Z.eq_dec z (Aof ll)).
  apply EQW.
  assumption.
  reflexivity.
  reflexivity.
  }
  rewrite <- H1.
  assumption.
  rewrite G1.
  reflexivity.
  }
  inversion U.
  }
  rewrite <- FIL.
  apply WTsOTsOK.
  assumption.
  assumption.
  destruct ULOCKED as [U|U].
  rewrite U.
  apply some_none.
  rewrite U.
  apply some_none.
  }


  intros.
  unfold updl in ING.
  rewrite map_map in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in EQ.

  destruct (Z.eq_dec x6 id).
  {
  simpl in EQ.
(* ==================== x6 = id ===========*)
  rewrite e in IN.
  symmetry in EQ.
  inversion EQ.
  assert (EQX: (x1, x2, x3, x4, x5) = (NotifyAll v, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN.
  assumption.
  assumption.
  inversion EQX.
  exists.
  unfold wellformed.
  auto.
  exists.
  unfold weakest_pre_ct.
  simpl.

  eapply sat_weak_imp1; try assumption.
  apply sat1.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  }
(* ==================== x6 <> id ===========*)


  inversion EQ.
  unfold ctxof in H1.
  unfold pof in H2.
  unfold oof in H3.
  unfold gof in H4.
  simpl in *.
  rewrite H1 in IN.
  rewrite H2 in IN.
  rewrite H3 in IN.
  rewrite H4 in IN.
  rewrite H5 in IN.
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF3,(WP3,VOBS3)).
  exists.
  destruct x1;
  simpl;
  try assumption.
  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  trivial.
  trivial.
  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  trivial.
  trivial.
  split.
  {
  unfold cmdof.
  simpl.
  destruct (cmd_eq_dec (wakeupcmd ([[v]]) x1) x1).
  rewrite e.

  assert (bp0: boundph p0).
  {
  apply BPE.
  apply in_map_iff.
  exists (x1, tx0, p0, O0, C0, id0).
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
  exists (x1, tx0, p0, O0, C0, id0).
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  apply WP3.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  destruct x1;
  try contradiction.
  {
  simpl in n0.
  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  {
  rewrite <- e.
  simpl.
  rewrite eqz.
  apply sat_wait4cond in WP3.
  destruct WP3 as (l',(v',(eql',(eqv',(pv0',(pl0',(lvl0',(prcl0',(prcv0',SAT0'))))))))).

  assert (CONDV': fold_left phplus (map pof T) (phplus Pinv Pleak) v' = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists p0.
  exists.
  apply in_map_iff.
  exists (Waiting4cond v0 l, tx0, p0, O0, C0, id0).
  auto.
  assumption.
  }

  assert (eqv'lv: v' = lv).
  {
  apply INJ.
  rewrite CONDV'.
  apply some_none.
  rewrite COND.
  apply some_none.
  omega.
  }
  rewrite eqv'lv in *.
  assert (SAT'1: sat p0 (Some O0) C0 (weakest_pre_ct m sp (Waiting4lock l, tx0) invs)).
  {
  replace p0 with (phplus p0 (emp knowledge)).
  replace C0 with (ghplus C0 (emp (option nat*nat))).
  rewrite M'nil in SAT0'.

  assert (bp0: boundph p0).
  {
  apply BPE.
  apply in_map_iff.
  exists (Waiting4cond v0 l, tx0, p0, O0, C0, id0).
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
  exists (Waiting4cond v0 l, tx0, p0, O0, C0, id0).
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  repeat php_.
  repeat php_.
  apply SAT0'; repeat php_.
  rewrite EMP.
  reflexivity.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  repeat php_.
  repeat php_.
  }
  assumption.
  }
  contradiction.
  }
  {
  simpl in n0.
  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  {
  rewrite <- e.
  simpl.
  rewrite eqz.

  assert (spt: sp = true).
  {
  destruct SPUR as (SPUR0,SPUR).
  eapply SPUR0 with (c:=WasWaiting4cond v0 l).
  apply in_map_iff.
  exists (WasWaiting4cond v0 l, tx0, p0, O0, C0, id0).
  auto.
  reflexivity.
  }
  rewrite spt in *.

  apply sat_wait4cond in WP3.
  destruct WP3 as (l',(v',(eql',(eqv',(pv0',(pl0',(lvl0',(prcl0',(prcv0',SAT0'))))))))).

  assert (CONDV': fold_left phplus (map pof T) (phplus Pinv Pleak) v' = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists p0.
  exists.
  apply in_map_iff.
  exists (WasWaiting4cond v0 l, tx0, p0, O0, C0, id0).
  auto.
  assumption.
  }

  assert (eqv'lv: v' = lv).
  {
  apply INJ.
  rewrite CONDV'.
  apply some_none.
  rewrite COND.
  apply some_none.
  omega.
  }

  rewrite eqv'lv in *.

  replace p0 with (phplus p0 (emp knowledge)).
  replace C0 with (ghplus C0 (emp (option nat*nat))).
  rewrite M'nil in SAT0'.
  replace sp with true.

  assert (bp0: boundph p0).
  {
  apply BPE.
  apply in_map_iff.
  exists (WasWaiting4cond v0 l, tx0, p0, O0, C0, id0).
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
  exists (WasWaiting4cond v0 l, tx0, p0, O0, C0, id0).
  split. reflexivity. assumption.
  }

  eapply sat_weak_imp1; try assumption.
  repeat php_.
  repeat php_.
  apply SAT0'; repeat php_.
  rewrite EMP.
  simpl.
  reflexivity.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  repeat php_.
  repeat php_.
  }
  contradiction.
  }
  }

  intros.
  unfold cmdof in W4COND.
  simpl in W4COND.
  destruct x1;
  inversion W4COND.

  {
  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  inversion H6.
  inversion H6.
  apply VOBS3 in H6.
  destruct H6 as (v',(l',(inv',(inl',(eqv',(eql',sobs')))))).
  exists v', l', inv', inl', eqv', eql'.
  destruct ((location_eq_dec Z.eq_dec) l' ll).
  rewrite e in *.
  {
  unfold WTs in sobs'.
  assert (forall p', filterb (xOf (fun x  => Lof x) locs) (Aof ll)
     (fun v1 : Z => length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) (Some v1)))
     (map cmdof (updl (map (wkupmap ([[v]])) T) id (tt, tx, p', O, C, id))))) ([[ev]]) = 
     (filterb (xOf (fun x  => Lof x) locs) (Aof ll)
     (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
     (map cmdof T))) ([[ev]]))).
  {
  intros.
  unfold filterb.
  destruct (xOf (fun x  => Lof x) locs ([[ev]])) eqn:XOF2.
  destruct (Z.eq_dec ([[ev]]) (Aof ll)).
  reflexivity.
  destruct (Z.eq_dec z (Aof ll)).
  {
  unfold updl.
  intros.
  rewrite map_map.
  rewrite map_map.
  apply filter_map_eq.
  intros.
  destruct x as (((((a1,a2),a3),a4),a5),a6).
  unfold cmdof.
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQX: (a1, a2, a3, a4, a5) = (NotifyAll v, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply IN0.
  rewrite e1.
  assumption.
  assumption.
  }
  inversion EQX.
  simpl.
  reflexivity.
  simpl.
  destruct a1;
  simpl;
  try reflexivity.
  {
  destruct (Z.eq_dec ([[v1]]) ([[v]])).
  simpl.
  destruct ((opZ_eq_dec (Some ([[v1]])) (Some ([[ev]])))).
  inversion e2.
  rewrite e1 in H6.
  rewrite H7 in n0.
  omega.
  destruct ((opZ_eq_dec None (Some ([[ev]])))).
  inversion e2.
  reflexivity.
  reflexivity.
  }
  {
  destruct (Z.eq_dec ([[v1]]) ([[v]])).
  simpl.
  destruct ((opZ_eq_dec (Some ([[v1]])) (Some ([[ev]])))).
  inversion e2.
  rewrite e1 in H6.
  rewrite H7 in n0.
  omega.
  destruct ((opZ_eq_dec None (Some ([[ev]])))).
  inversion e2.
  reflexivity.
  reflexivity.
  }
  }
  reflexivity.
  reflexivity.
  }
  rewrite H.
  assumption.
  }
  rewrite <- FIL.
  assumption.
  assumption.
  apply LOCs.
  assumption.
  }

  {
  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  inversion H6.
  inversion H6.
  }
Qed.


Lemma SpuriousWakeup_preserves_validity:
  forall m h t id v l tx
         (VALIDK: validk (S m) true t h)
         (CMD: t id = Some (Waiting4cond v l,tx)),
    validk m true (upd Z.eq_dec t id (Some (WasWaiting4cond v l,tx))) h.
Proof.
  intros.
  unfold validk in VALIDK.

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
  unfold WTs, OBs.
  unfold validk.


  assert (tmp: exists p O C, In (Waiting4cond v l, tx, p, O, C, id) T).
  apply TOK.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.

  exists (updl T id (WasWaiting4cond v l, tx, p, O, C, id)).
  exists invs, locs, Pinv, Pleak, Ainv, Cinv, Cleak.

  assert (EQC: map gof (updl T id (WasWaiting4cond v l, tx, p, O, C, id)) = map gof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Waiting4cond v l, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  reflexivity.
  }

  assert (EQC': map (fun x => (gof x, snd x)) (updl T id (WasWaiting4cond v l, tx, p, O, C, id)) =
    map (fun x => (gof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Waiting4cond v l, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQH: map pof (updl T id (WasWaiting4cond v l, tx, p, O, C, id)) =
    map pof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Waiting4cond v l, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQH': map (fun x => (pof x, snd x)) (updl T id (WasWaiting4cond v l, tx, p, O, C, id)) =
    map (fun x => (pof x, snd x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Waiting4cond v l, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

   assert (EQLEN: forall v0, length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0)))
     (map (fun x0 => cmdof (if Z.eq_dec (snd x0) id  then (WasWaiting4cond v l, tx, p, O, C, id) else x0)) T)) =
     length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0))) (map cmdof T))).
  {
  intros.
  unfold updl.
  apply length_filter_map_eq.
  intros.
  destruct (Z.eq_dec (snd a) id).
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Waiting4cond v l, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply IN.
  rewrite e0.
  assumption.
  assumption.
  }
  inversion EQA.
  reflexivity.
  contradiction.
  reflexivity.
  }

  assert (EQW: forall l0, filterb (xOf (fun x : location Z => Lof x) locs) (Aof l0)
    (fun v0 => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0)))
    (map cmdof (updl T id (WasWaiting4cond v l, tx, p, O, C, id))))) =
    filterb (xOf (fun x : location Z => Lof x) locs) (Aof l0)
    (fun v0 => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0)))
    (map cmdof T)))).
  {
  intros.
  unfold filterb.
  apply functional_extensionality.
  intros.
  unfold updl.
  rewrite map_map.
  rewrite EQLEN.
  reflexivity.
  }

  assert (EQAoof: map Aoof (updl T id (WasWaiting4cond v l, tx, p, O, C, id)) = map Aoof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Waiting4cond v l, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  assert (EQoof: map oof (updl T id (WasWaiting4cond v l, tx, p, O, C, id)) = map oof T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Waiting4cond v l, tx, p, O, C)).
  {
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  }
  inversion EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  }

  rewrite EQC.
  rewrite EQC'.
  rewrite EQH.
  rewrite EQH'.
  rewrite EQAoof.
  rewrite EQoof.

  rewrite map_map in *.
  rewrite map_map in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  exists.
  {
  destruct INF as (INF1,INF2).
  split. assumption.
  apply steps_preserve_inf_capacity with true t h.
  assumption.
  apply red_SpuriousWakeup; try assumption.
  }
  exists.
  {
  unfold spur_ok.
  split.
  intros.
  reflexivity.
  intros.
  apply SPUR.
  assumption.
  }
  exists.
  {
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
  }
  exists.
  {
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
  }
  exists.
  {
  intros.
  apply upd_updl.
  exists (Waiting4cond v l, tx, p, O, C).
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
  {
  intros.
  rewrite EQW.
  apply INAOK.
  assumption.
  assumption.
  }
  assumption.
  }
  exists.
  {
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
  }
  exists.
  {
  split. assumption.
  assumption.
  }
  exists.
  {
  intros.
  rewrite EQW.
  apply WTsOTsOK.
  assumption.
  }
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  {
  symmetry in EQx.
  inversion EQx.
  split. trivial.
  split.
  assert (bp: boundph p).
  {
  apply BPE.
  apply in_map_iff.
  exists (Waiting4cond v l, tx, p, O, C, id).
  split. reflexivity. assumption.
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
  exists (Waiting4cond v l, tx, p, O, C, id).
  split. reflexivity. assumption.
  }
  eapply sat_weak_imp1; try assumption.
  apply WP.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  inversion W4COND.
  }
  rewrite EQx in *.
  assert (IN2:=INx).
  apply SOBS in INx.
  destruct INx as (wf',(sat',safe')).
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
  apply sat'.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  intros.
  apply safe' in W4COND.
  destruct W4COND as (v',(l',(inv',(inl',(eqv',(eql',safe'1)))))).
  exists v',l',inv',inl',eqv',eql'.
  rewrite EQW.
  assumption.
Qed.


Lemma WasWait_preserves_validity:
  forall m sp h t id vv l tx
         (VALIDK: validk (S m) sp t h)
         (NON: h ([[l]]) = Some 1%Z)
         (CMD: t id = Some (WasWaiting4cond vv l,tx)),
    validk m sp (upd Z.eq_dec t id (Some (tt,tx))) (upd Z.eq_dec h ([[l]]) (Some 0%Z)).
Proof.
  intros.
  unfold validk in VALIDK.

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
  destruct LOCKsOK as (LOCKOK,(ULOCKOK,UCONDOK)).
  unfold WTs, OBs.
  unfold validk.


  assert (tmp: exists p O C, In (WasWaiting4cond vv l, tx, p, O, C, id) T).
  apply TOK.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply SOBS in tmp.
  destruct tmp as (WF,(WP,VOBS)).
  unfold wellformed in WF.
  simpl in WF.
  destruct WF as (WF1,WF2).
  apply sat_WasWaiting4cond in WP.
  destruct WP as (ll,(lv,(eqll,(eqlv,(lofv,(pl,(pv,(prcl,SAT1)))))))).
  rewrite <- eqll in *.
  rewrite <- eqlv in *.

  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  assert (spt: sp = true).
  {
  destruct SPUR as (SPUR1,SPUR2).
  eapply SPUR1 with (c:=WasWaiting4cond vv l).
  apply in_map_iff.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  auto.
  reflexivity.
  }

  assert (EQFOLD: fold_left phplus (map pof T) (phplus Pinv Pleak) = phplus Pinv (fold_left phplus (map pof T) Pleak)).
  {
  apply fold_left_f_m_def with (def:=phplusdef); repeat php_.
  apply can_phpdef.
  }

  assert (INpT: In p (map pof T)).
  {
  apply in_map_iff.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  auto.
  }

  assert (ghpdefg0il: forall g, In g (map gof T) -> ghplusdef g (ghplus Cinv Cleak)).
  {
  intros.
  apply ghpdef_pair.
  assumption.
  apply GHPD.
  assumption.
  apply GHPD.
  assumption.
  }

  assert (bcil: boundgh (ghplus Cinv Cleak)).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=ghplus Cinv Cleak); repeat php_.
  right. reflexivity.
  }

  assert (bci: boundgh Cinv).
  {
  apply boundgh_mon with Cleak.
  assumption.
  }

  assert (bcl: boundgh Cleak).
  {
  apply boundgh_mon with Cinv.
  rewrite ghplus_comm; repeat php_.
  }

  assert (phpdefp0pil: forall p0, In p0 (map pof T) -> phplusdef p0 (phplus Pinv Pleak)).
  {
  intros.
  apply phpdef_pair.
  assumption.
  apply PHPD.
  assumption.
  apply PHPD.
  assumption.
  }

  assert (LOCKED: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some Lock).
  {
  assert (tmp: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some Lock \/
    (exists wt ot, fold_left phplus (map pof T) (phplus Pinv Pleak) ll =
    Some (Locked wt ot))).
  {
  apply fold_lock_ed.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  right.
  exists p, INpT.
  assumption.
  }

  destruct tmp as [LK|LKED].
  assumption.
  destruct LKED as (wt,(ot,LKED)).
  assert (CO:=PH2H).
  destruct CO as (CO1,CO2).
  specialize CO1 with ll.
  rewrite LKED in CO1.

  rewrite NON in CO1.
  inversion CO1.
  }

  destruct pl as [pl|pl].
  Focus 2.
  destruct pl as (WT',(OT',pl)).
  assert (CO: fold_left phplus (map pof T) (phplus Pinv Pleak) ll = Some (Locked WT' OT')).
  {
  apply fold_locked; repeat php_.
  apply pofs.
  right.
  exists p, INpT.
  assumption.
  }
  rewrite CO in LOCKED.
  inversion LOCKED.

  assert (tmp: Lof ll = Aof ll /\ Pof ll = false /\ Xof ll = None /\
   (h (Aof ll) <> Some 1%Z -> In (Oof ll) (concat (map oof T)))).
  {
  apply LOCKOK.
  left.
  assumption.
  }
  destruct tmp as (lll,(plf,(ninrlxll,inlt))).

  assert (PERM: Permutation Ainv (((subsas (snd (Iof ll)) (invs (fst (Iof ll)) 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))))), ll)
     :: filter (fun x => negb (ifb ((location_eq_dec Z.eq_dec) (snd x) ll))) Ainv)).
  {
  apply perm_filter.
  assumption.
  apply INAOK.
  assumption.
  assumption.
  unfold negb.
  simpl.
  destruct ((location_eq_dec Z.eq_dec) ll ll).
  reflexivity.
  contradiction.
  intros.
  unfold negb.
  simpl.
  destruct ((location_eq_dec Z.eq_dec) z' ll).
  contradiction.
  reflexivity.
  }

  assert (SATA2: sat Pinv None Cinv (fold_left Astar (map fst 
    (((subsas (snd (Iof ll)) (invs (fst (Iof ll)) 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))))), ll)
     :: filter (fun x => negb (ifb ((location_eq_dec Z.eq_dec) (snd x) ll))) Ainv))(Abool true))).
  {
  apply sat_perm with (map fst Ainv).
  apply Permutation_map.
  assumption.
  assumption.
  assumption.
  assumption.
  }

  simpl in SATA2.
  assert (SATA3: sat Pinv None Cinv 
    (Astar (subsas (snd (Iof ll)) (invs (fst (Iof ll)) 
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))
    (fold_left Astar (map fst 
    (filter (fun x => negb (ifb ((location_eq_dec Z.eq_dec) (snd x) ll))) Ainv))
    (Abool true)))).
  {
  apply fold_left_g_can2.
  unfold cang.
  split.
  intros.
  apply sat_comm.
  assumption.
  simpl.
  intros.
  apply sat_perm with (l:=l0); assumption.
  assumption.
  }
  simpl in SATA3.
  destruct SATA3 as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(bc1,(bc2,(bc1c2,(opo1o2,(SATp1,(SATp2,(p1p2,C1C2)))))))))))))))))).
  assert (tmp: O1 = None /\ O2 = None).
  {
  inversion opo1o2.
  split; reflexivity.
  }
  destruct tmp as (o1n,o2n).
  rewrite o1n, o2n in *.
  subst.

  assert (phpdeff: phplusdef (fold_left phplus (map pof T) Pleak) (phplus p1 p2)).
  {
  apply phpdef_fold; repeat php_.
  intros.
  apply PHPD.
  assumption.
  intros.
  apply PHPD.
  assumption.
  }

  assert (PHPDpp1: phplusdef p p1).
  {
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply phpdef_comm.
  apply PHPD.
  apply in_map_iff.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  auto.
  apply phpdef_comm.
  assumption.
  }
  assert (PHPDpp2: phplusdef p p2).
  {
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply phpdef_comm.
  apply PHPD.
  apply in_map_iff.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  auto.
  }

  assert (p12ll: phplus (phplus p1 p2) Pleak ll = Some Lock \/ phplus (phplus p1 p2) Pleak ll = None).
  {
  apply or_comm.
  apply locked_fold_phtoheap with (m:=pof) (l:=T) (id:=id) (p:=p) (b:=phplus (phplus p1 p2) Pleak) (h:=h); repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  right.
  reflexivity.
  }

  assert (p12l: phplus p1 p2 ll = Some Lock \/ phplus p1 p2 ll = None).
  {
  apply phplus_lock_none with Pleak.
  assumption.
  }

  assert (p1l: p1 ll = Some Lock \/ p1 ll = None).
  {
  apply phplus_lock_none with p2.
  assumption.
  }

  assert (p2l: p2 ll = Some Lock \/ p2 ll = None).
  {
  apply phplus_lock_none with p1.
  rewrite phplus_comm; repeat php_.
  }

  assert (pll: Pleak ll = Some Lock \/ Pleak ll = None).
  {
  apply phplus_lock_none with (phplus p1 p2).
  rewrite phplus_comm; repeat php_.
  }

  assert (p0l: forall p0 (IN: In p0 (map pof T)), p0 ll = Some Lock \/ p0 ll = None).
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold pof in EQ.
  simpl in EQ.
  rewrite <- EQ.
  destruct (Z.eq_dec x6 id).
  rewrite e in IN.
  assert (EQX: (x1, x2, x3, x4, x5) = (WasWaiting4cond vv l, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN.
  assumption.
  assumption.
  inversion EQX.
  left.
  assumption.
  rewrite EQ in *.
  assert (PHPDp0: phplusdef p p0).
  {
  apply DEFL with id x6.
  omega.
  apply in_map_iff.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  rewrite EQ.
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
  assert (CO:=PH2H).
  destruct CO as (CO,CO1).
  unfold phtoh in CO.
  specialize CO with ll.
  rewrite NON in CO.
  erewrite fold_locked in CO; repeat php_.
  inversion CO.
  apply pofs.
  right.
  exists p0.
  exists.
  apply in_map_iff.
  exists (x1, x2, p0, x4, x5, x6).
  auto.
  apply p0l.
  right.
  reflexivity.
  }
  assert (PHPDUp1: forall wt ot, phplusdef (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt ot))) p1).
  {
  intros.
  apply phpdef_upd_locked.
  assumption.
  assumption.
  }
  assert (PHPDUp2: forall wt ot, phplusdef (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt ot))) p2).
  {
  intros.
  apply phpdef_upd_locked.
  assumption.
  assumption.
  }
  assert (EQP: phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
   (upd Z.eq_dec (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    ([[vv]]) ((filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))) ([[vv]])-1))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1 = 
    upd (location_eq_dec Z.eq_dec) (phplus p p1) ll (Some (Locked 
    (upd Z.eq_dec (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    ([[vv]]) ((filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))) ([[vv]])-1))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))).
  {
  apply phplus_upd.
  unfold not.
  intros.
  destruct H as (v,(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
  }

  exists (updl T id (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (upd Z.eq_dec (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    ([[vv]]) ((filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))) ([[vv]])-1))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll::O, ghplus C C1, id)).
  exists invs, locs, p2, Pleak.
  exists (filter (fun x => negb (ifb ((location_eq_dec Z.eq_dec) (snd x) ll))) Ainv).
  exists C2, Cleak.

  assert (COND: fold_left phplus (map pof T) (phplus (phplus p1 p2) Pleak) lv = Some Cond).
  {
  apply fold_cond; repeat php_.
  apply pofs.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  auto.
  assumption.
  }

  assert (EQWT: forall l0 p O C (NEQ: l0 <> ll) (SOME: fold_left phplus (map pof T) (phplus (phplus p1 p2) Pleak) l0 <> None), 
    filterb (xOf (fun x  => Lof x) locs) (Aof l0) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) =
    filterb (xOf (fun x  => Lof x) locs) (Aof l0) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof
    (updl T id (tt, tx, p, O, C, id)))))).
  {
  intros.
  apply filterb_updl_eq.
  intros.
  split.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some v)).
  inversion e.
  reflexivity.
  intros.
  assert (X': x' = (WasWaiting4cond vv l, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec (Some ([[vv]])) (Some v)).
  inversion e.
  rewrite <- H0 in IN.
  rewrite <- eqlv in *.
  rewrite xOf_same in IN.
  rewrite lofv in IN.
  inversion IN.
  assert (CO: l0 = ll).
  {
  apply INJ.
  assumption.
  rewrite LOCKED.
  apply some_none.
  rewrite H1.
  reflexivity.
  }
  contradiction.
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
  reflexivity.
  }


  assert (FIL1: forall p, filterb (xOf (fun x0 => Lof x0) locs) (Aof ll)
    (fun v => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof T))) ([[vv]]) - 1 =
    filterb (xOf (fun x0 : location Z => Lof x0) locs) (Aof ll) 
    (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof (updl T id (tt, tx, p, Oof ll :: O, ghplus C C1, id))))) ([[vv]])).
  {
  intros.
  unfold filterb.
  assert (XOF: xOf (fun x0 : location Z => Lof x0) locs ([[vv]]) = Some (Aof ll)).
  {
  rewrite <- eqlv.
  rewrite xOf_same.
  rewrite lofv.
  reflexivity.
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
  rewrite XOF.
  destruct (Z.eq_dec ([[vv]]) (Aof ll)).
  {
  rewrite <- eqlv in e.
  assert (CO: lv = ll).
  {
  apply INJ.
  rewrite COND.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  assumption.
  }
  rewrite CO in COND.
  rewrite COND in LOCKED.
  inversion LOCKED.
  }
  rewrite eqz.
  rewrite eqz.
  apply filter_updl_inc.
  assumption.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some ([[vv]]))).
  inversion e.
  reflexivity.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  exists.
  unfold elem.
  apply filter_In.
  split.
  assumption.
  apply Z.eqb_eq.
  reflexivity.
  simpl.
  destruct (opZ_eq_dec (Some ([[vv]])) (Some ([[vv]]))).
  reflexivity.
  contradiction.
  }
  assert (FIL2: forall p a (NEQ: a <> ([[vv]])), 
    filterb (xOf (fun x0 => Lof x0) locs) (Aof ll)
    (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof T))) a =
    filterb (xOf (fun x0 => Lof x0) locs) (Aof ll)
    (fun v => length  (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof (updl T id (tt, tx, p, Oof ll :: O, ghplus C C1, id))))) a).
  {
  intros.
  unfold filterb.
  destruct (xOf (fun x0 : location Z => Lof x0) locs a) eqn:XOF.
  destruct (Z.eq_dec a (Aof ll)).
  reflexivity.
  destruct (Z.eq_dec z (Aof ll)).
  rewrite <- filter_updl_eq.
  reflexivity.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some a)).
  inversion e0.
  reflexivity.
  intros.
  assert (X': x' = (WasWaiting4cond vv l, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec (Some ([[vv]])) (Some a)).
  inversion e0.
  rewrite H0 in NEQ.
  contradiction.
  reflexivity.
  reflexivity.
  reflexivity.
  }

  assert (EQOT: forall l0 c p C, filterb (xOf (fun x  => Lof x) locs) (Aof l0) (count_occ Z.eq_dec (concat (map Aoof T))) =
    filterb (xOf (fun x  => Lof x) locs) (Aof l0) (count_occ Z.eq_dec (concat (map Aoof (updl T id
    (c, tx, p, Oof ll :: O, C, id)))))).
  {
  intros.
  apply filterb_updl_obs_eq.
  intros.
  assert (X': x' = (WasWaiting4cond vv l, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold Aoof.
  unfold Oof.
  simpl.
  destruct (Z.eq_dec (Aofo (fst (fst (fst ll)))) v).
  rewrite <- e in *.
  assert (XOF: xOf (fun x  => Lof x) locs (Aofo (fst (fst (fst ll)))) = Some (Lof ll)).
  {
  apply xOf_same.
  apply in_map.
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  apply comp_cons.
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  unfold comp.
  intros.
  apply INJ.
  apply LOCs.
  assumption.
  apply LOCs.
  assumption.
  }
  rewrite IN in XOF.
  inversion XOF.
  rewrite lll in *.
  rewrite H0 in NEQ.
  contradiction.
  reflexivity.
  }

  assert (ghpdefc1lc2l: ghplusdef C1 Cleak /\ ghplusdef C2 Cleak). repeat php_.

  assert (ghpdefxc1xc2l: forall x : gheap, In x (map gof T) -> 
    ghplusdef x C1 /\ ghplusdef x (ghplus C2 Cleak)).
  {
  intros.
  apply GHPD in H.
  assert (tmp: ghplusdef x C1 /\ ghplusdef x C2). repeat php_.
  split.
  repeat php_.
  repeat php_.
  }

  assert (EQCT: fold_left ghplus (map gof (updl T id (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (upd Z.eq_dec (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    ([[vv]]) ((filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))) ([[vv]])-1))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll::O, ghplus C C1, id)))
    (ghplus C2 Cleak) = fold_left ghplus (map gof T) ((ghplus (ghplus C1 C2) Cleak))).
  {
  rewrite <- fold_left_move_m_eq2 with (def:=ghplusdef) (x1:=C) (x2:=C1); repeat php_.
  rewrite ghplus_assoc; repeat php_.
  rewrite <- fold_left_f_m_def with (def:=ghplusdef); repeat php_.
  apply can_ghpdef.
  apply can_ghpdef.
  apply ghpdefxc1xc2l.
  apply ghpdefxc1xc2l.
  apply in_map_iff.
  exists (WasWaiting4cond vv l, tx, p, O, C, id). auto.
  }

  assert (p0ln: forall p0, In p0 (map pof T) \/ p0 = phplus p1 p2 -> p0 ll = None \/ p0 ll = Some Lock).
  {
  intros.
  destruct H as [IN|IN].
  apply or_comm.
  apply p0l.
  assumption.
  rewrite IN.
  unfold phplus.
  destruct p1l as [p1l|p1l].
  rewrite p1l.
  destruct p2l as [p2l|p2l].
  rewrite p2l.
  right.
  reflexivity.
  rewrite p2l.
  right.
  reflexivity.
  rewrite p1l.
  destruct p2l as [p2l|p2l].
  rewrite p2l.
  right.
  reflexivity.
  rewrite p2l.
  left.
  reflexivity.
  }

  assert (phpdefp1lp2l: phplusdef p1 Pleak /\ phplusdef p2 Pleak). repeat php_.
  assert (phpdefp01p02l: forall p0, In p0 (map pof T) -> phplusdef p0 p1 /\ phplusdef p0 p2 /\ phplusdef p0 Pleak).
  {
  intros.
  apply PHPD in H.
  assert (tmp: phplusdef p0 p1 /\ phplusdef p0 p2). repeat php_.
  split;
  repeat php_.
  split;
  repeat php_.
  }

  assert (ghpdefp01p02l: forall p0, In p0 (map gof T) -> ghplusdef p0 C1 /\ 
    ghplusdef p0 C2 /\ ghplusdef p0 Cleak).
  {
  intros.
  apply GHPD in H.
  assert (tmp: ghplusdef p0 C1 /\ ghplusdef p0 C2). repeat php_.
  split;
  repeat php_.
  split;
  repeat php_.
  }

  assert (p0ln': forall p0, In p0 (map pof T) \/ p0 = phplus p1 (phplus p2 Pleak) -> p0 ll = None \/ p0 ll = Some Lock).
  {
  intros.
  apply locked_fold_phtoheap with (m:=pof) (l:=T) (id:=id) (p:=p) (b:=phplus (phplus p1 p2) Pleak) (h:=h); repeat php_.
  apply pofs.
  apply in_map_iff.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  rewrite phplus_assoc; repeat php_.
  }

  assert (EQH0: forall l0 (NEQ: ll <> l0),
    fold_left phplus (map pof T) (phplus p1 p2) l0 =
    fold_left phplus (map pof (updl T id
    (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (upd Z.eq_dec (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    ([[vv]]) ((filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))) ([[vv]])-1))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll :: O, ghplus C C1, id))) p2 l0).
  {
  symmetry.
  apply eq_heap_Acquire with (z:=ll) (p:=p); repeat php_.
  apply pofs.
  apply PHPD.
  apply in_map_iff.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  eexists.
  eexists.
  reflexivity.
  }

  assert (EQH: forall l0 (NEQ: ll <> l0),
    fold_left phplus (map pof T) (phplus (phplus p1 p2) Pleak) l0 =
    fold_left phplus (map pof (updl T id
    (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (upd Z.eq_dec (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    ([[vv]]) ((filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))) ([[vv]])-1))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll :: O, ghplus C C1, id))) (phplus p2 Pleak) l0).
  {
  rewrite phplus_assoc; repeat php_.
  symmetry.
  apply eq_heap_Acquire with (z:=ll) (p:=p); repeat php_.
  apply pofs.
  intros.
  apply phpdefp01p02l in IN.
  repeat php_.
  apply in_map_iff.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  eexists.
  eexists.
  reflexivity.
  }

  assert (LOCKEDU: fold_left phplus (map pof (updl T id
    (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (upd Z.eq_dec (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    ([[vv]]) ((filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))) ([[vv]])-1))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll :: O, ghplus C C1, id))) (phplus p2 Pleak) ll = 
    Some (Locked 
    (upd Z.eq_dec (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    ([[vv]]) ((filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))) ([[vv]])-1))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))))).
  {
  apply locked_Acquire with p p1; repeat php_.
  apply pofs.
  intros.
  apply phpdefp01p02l in IN.
  repeat php_.
  apply in_map_iff.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  }

  assert (INl01: forall l0 (IN: In l0 (concat (map oof T))),
    In l0 (concat (map oof (updl T id (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (upd Z.eq_dec (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    ([[vv]]) ((filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))) ([[vv]])-1))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll::O, ghplus C C1, id))))).
  {
  intros.
  rewrite <- flat_map_concat_map in IN.
  apply in_flat_map in IN.
  destruct IN as (x,(INx,INl0)).
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (WasWaiting4cond vv l, tx, p, O, C)).
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  inversion EQX.
  exists (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (upd Z.eq_dec (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    ([[vv]]) ((filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))) ([[vv]])-1))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll :: O, ghplus C C1, id).
  split.
  apply in_updl_eq.
  exists (WasWaiting4cond vv l, tx, p, O, C).
  auto.
  unfold oof.
  simpl.
  right.
  rewrite <- H3.
  assumption.
  exists (x1, x2, x3, x4, x5, x6).
  split.
  apply in_updl_neq.
  omega.
  assumption.
  assumption.
  }

  assert (INl02: forall o0 (NEQ: Oof ll <> o0) (IN: In o0 (concat (map oof (updl T id (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (upd Z.eq_dec (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    ([[vv]]) ((filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))) ([[vv]])-1))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll::O, ghplus C C1, id))))),
    In o0 (concat (map oof T))).
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
  unfold oof in INl0.
  simpl in INl0.
  assert (EQX: (x1, x2, x3, x4, x5) = (WasWaiting4cond vv l, tx, p, O, C)).
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  inversion EQX.
  destruct INl0 as [CO|INl0].
  contradiction.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  auto.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }

  assert (inc: In C (map gof T)).
  {
  apply in_map_iff.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  auto.
  }

  assert (ghpdefCC1: ghplusdef C C1).
  {
  apply ghpdef_comm.
  apply ghpdef_assoc_mon with C2.
  repeat php_.
  apply ghpdef_comm.
  rewrite ghplus_comm.
  apply GHPD.
  assumption.
  repeat php_.
  }

  assert (incid: In (C, id) (map (fun x => (gof x, snd x)) T)).
  {
  apply in_map_iff.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  auto.
  }

  assert (ghpdefCC12: ghplusdef C (ghplus C1 C2)).
  {
  apply GHPD.
  assumption.
  }

  assert (ghpdefCC2: ghplusdef C C2).
  {
  apply ghpdef_comm.
  apply ghpdef_assoc_mon with C1; repeat php_.
  }

  assert (ghpdefCCl: ghplusdef C Cleak).
  {
  apply GHPD.
  assumption.
  }

  assert (ghpdefC2Cl: ghplusdef C2 Cleak).
  {
  apply ghpdef_assoc_mon with C1; repeat php_.
  }

  assert (bp: boundph p).
  {
  apply BPE.
  assumption.
  }

  assert (phpdefppl: phplusdef p Pleak).
  {
  apply PHPD.
  assumption.
  }

  assert (bp12plp: boundph (phplus (phplus (phplus p1 p2) Pleak) p)).
  {
  apply boundph_fold with (m:=pof) (l:=T); repeat php_.
  }

  assert (bp12p: boundph (phplus (phplus p1 p2) p)).
  {
  apply boundph_mon with Pleak; repeat php_.
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_assoc in bp12plp; repeat php_.
  replace (phplus p Pleak) with (phplus Pleak p); repeat php_.
  }

  assert (bpp1: boundph (phplus p p1)).
  {
  apply boundph_mon with p2; repeat php_.
  rewrite phplus_assoc; repeat php_.
  }

  assert (phpdefupp1: phplusdef (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked
    (upd Z.eq_dec (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    ([[vv]]) ((filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))) ([[vv]])-1))(filterb (xOf (fun x  => Lof x) locs) (Aof ll)
    (count_occ Z.eq_dec (concat (map Aoof T))))))) p1).
  {
  apply phpdef_locked'; repeat php_.
  }

  assert (phpdefuppl: phplusdef Pleak (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked
    (upd Z.eq_dec (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    ([[vv]]) ((filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))) ([[vv]])-1))   (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T)))))))).
  {
  apply phpdef_comm.
  apply phpdef_locked'; repeat php_.
  }

  assert (SPUR1: spurious_ok true ll lv invs).
  {
  unfold spur_ok in SPUR.
  assert (SP1:=COND).
  apply SPUR in SP1.
  destruct SP1 as (a,(b,(c,d))).
  assert (eqall: a = ll).
  {
  apply INJ.
  destruct c as [c|c].
  rewrite c.
  apply some_none.
  destruct c as (wt',(ot',c)).
  rewrite c.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  rewrite lofv in *.
  symmetry.
  assumption.
  }
  rewrite <- eqall.
  assumption.
  }

  rewrite map_map in *.
  rewrite map_map in *.
  simpl in *.
  change (fun x => pof x) with pof in *.
  change (fun x => gof x) with gof in *.
  change (fun x => cmdof x) with cmdof in *.

  rewrite EQCT.

  exists.
  {
  destruct INF as (INF1,INF2).
  split.
  assumption.
  apply steps_preserve_inf_capacity with true t h.
  assumption.
  rewrite eqll.
  apply red_WasWait with vv.
  assumption.
  rewrite <- eqll.
  assumption.
  }
  exists.
  {
  unfold spur_ok.
  split.
  intros.
  reflexivity.
  intros.
  destruct (location_eq_dec Z.eq_dec ll v).
  rewrite <- e in *.
  rewrite LOCKEDU in CONDv.
  inversion CONDv.
  rewrite <- EQH in CONDv.
  apply SPUR in CONDv.
  destruct CONDv as (a,(b,(c,d))).
  exists a, b.
  exists.
  destruct (location_eq_dec Z.eq_dec ll a).
  rewrite <- e.
  right.
  eexists.
  eexists.
  apply LOCKEDU.
  rewrite <- EQH; try assumption.
  assumption.
  assumption.
  }
  exists.
  {
  split.
  {
  apply defl_Acquire with (p:=p) (p1:=p1) (p2:=p2) (z:=ll); repeat php_.
  apply pofs.
  apply PHPD.
  apply in_map_iff.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  eexists.
  eexists.
  reflexivity.
  }
  exists. repeat php_.
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
  apply phpdef_comm.
  apply phpdef_pair.
  apply PHPDUp1.
  apply phpdef_comm.
  apply PHPDUp2.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  apply phpdef_pair.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2; repeat php_.
  simpl in EQ.
  rewrite EQ in IN.
  assert (G: In p0 (map pof T)).
  {
  apply in_map_iff.
  exists (x1, x2, p0, x4, x5, x6).
  auto.
  }
  apply phpdefp01p02l in G.
  split; repeat php_.
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

  rewrite EQP.
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  simpl in EQ.
  rewrite EQ in IN.
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, p0, x4, x5, x6).
  auto.
  }
  exists. assumption.
  exists. assumption.
  exists.

  assert (bp2l: boundph (phplus p2 Pleak)).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_mon with p1; repeat php_.
  rewrite phplus_assoc; repeat php_.
  replace (phplus p2 p1) with (phplus p1 p2); repeat php_.
  }

  assumption.
  split.
  {
  apply boundph_Acquire with (p:=p) (p1:=p1) (z:=ll); repeat php_.
  apply pofs.
  intros.
  apply phpdefp01p02l in IN.
  repeat php_.
  apply in_map_iff.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  auto.
  eexists.
  eexists.
  reflexivity.
  left.
  assumption.
  rewrite <- phplus_assoc; repeat php_.
  }
  unfold phtoh in *.
  destruct PH2H as (PH1,PH2).
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  {
  rewrite <- e in *.
  rewrite LOCKEDU.
  unfold upd.
  rewrite eqz.
  reflexivity.
  }
  rewrite <- EQH.
  specialize PH1 with l0.
  destruct (fold_left phplus (map pof T) (phplus (phplus p1 p2) Pleak) l0) eqn:fl0.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  assert (CO: ll = l0).
  {
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite fl0.
  apply some_none.
  symmetry.
  assumption.
  }
  contradiction.
  assumption.
  trivial.
  assumption.
  }
  intros.
  unfold upd.
  destruct (Z.eq_dec z (Aof ll)).
  symmetry in e.
  apply NONE in e.
  rewrite LOCKEDU in e.
  inversion e.
  apply PH2.
  intros.
  rewrite EQH.
  apply NONE.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  omega.
  }
  exists.
  {
  split.
  {
  unfold defl.
  unfold updl.
  rewrite map_map.
  unfold gof.
  simpl.
  intros.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  apply in_map_iff in IN2.
  destruct IN2 as (x2,(EQ2,IN2)).
  destruct (Z.eq_dec (snd x1) id).
  simpl in EQ1.
  inversion EQ1.
  destruct (Z.eq_dec (snd x2) id).
  simpl in EQ2.
  inversion EQ2.
  omega.
  inversion EQ2.
  apply ghpdef_pair'; repeat php_.

  apply DEFLg with id (snd x2).
  omega.
  assumption.
  apply in_map_iff.
  exists x2.
  auto.
  assert (G: In (snd (fst x2)) (map gof T)).
  {
  apply in_map_iff.
  exists x2.
  auto.
  }
  apply ghpdefp01p02l in G.
  repeat php_.

  inversion EQ1.
  destruct (Z.eq_dec (snd x2) id).
  simpl in EQ2.
  inversion EQ2.

  assert (G: In (snd (fst x1)) (map gof T)).
  {
  apply in_map_iff.
  exists x1.
  auto.
  }
  apply ghpdefp01p02l in G.
  apply ghpdef_pair; repeat php_.
  apply DEFLg with (snd x1) id.
  omega.
  apply in_map_iff.
  exists x1.
  auto.
  assumption.
  inversion EQ2.
  apply DEFLg with (snd x1) (snd x2).
  omega.
  apply in_map_iff.
  exists x1.
  auto.
  apply in_map_iff.
  exists x2.
  auto.
  }
  split.
  {
  unfold updl.
  rewrite map_map.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  unfold gof in EQ1.
  simpl in EQ1.
  inversion EQ1.

  split; repeat php_.
  inversion EQ1.
  assert (G: In (gof x1) (map gof T)).
  {
  apply in_map_iff.
  exists x1.
  auto.
  }
  apply ghpdefp01p02l in G.
  split; repeat php_.
  }
  split; assumption.
  }
  exists.
  {
  intros.
  apply upd_updl.
  exists (WasWaiting4cond vv l, tx, p, O, C).
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
  split.
  {
  erewrite map_filter with (f3:= fun x => (if if (location_eq_dec Z.eq_dec) x ll then true else false then false else true)).
  apply nodup_filter.
  assumption.
  intros.
  reflexivity.
  }
  split.
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  apply filter_In in IN.
  destruct IN as (EQ1,EQ2).
  unfold negb in EQ2.
  unfold ifb in EQ2.
  destruct ((location_eq_dec Z.eq_dec) (snd x) ll).
  inversion EQ2.
  assert (G: fold_left phplus (map pof T) (phplus (phplus p1 p2) Pleak) l0 =
         Some Lock /\ h (Aof l0) = Some 1%Z).
  {
  apply AinvOK.
  apply in_map_iff.
  exists x.
  auto.
  }
  destruct G as (G1,G2).
  rewrite <- EQH.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  exfalso.
  apply n.
  rewrite EQ.
  apply INJ.
  rewrite G1.
  apply some_none.
  rewrite LOCKED.
  apply some_none.
  assumption.
  split; assumption.
  unfold not.
  intros.
  rewrite H in n.
  rewrite EQ in n.
  contradiction.
  }
  split.
  {
  intros.
  rewrite <- EQOT.
  unfold upd in NOTHELD.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  inversion NOTHELD.
  rewrite <- EQWT.
  apply filter_In.
  split.
  apply INAOK.
  rewrite EQH.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  assumption.
  simpl.
  destruct ((location_eq_dec Z.eq_dec) l0 ll).
  rewrite e in n.
  contradiction.
  reflexivity.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
  rewrite EQH.
  rewrite LOCK.
  apply some_none.
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
  unfold injph.
  intros.
  apply INJ.
  destruct ((location_eq_dec Z.eq_dec) ll x1).
  rewrite <- e in *.
  rewrite LOCKED.
  apply some_none.
  rewrite EQH.
  assumption.
  assumption.
  destruct ((location_eq_dec Z.eq_dec) ll x2).
  rewrite <- e in *.
  rewrite LOCKED.
  apply some_none.
  rewrite EQH.
  assumption.
  assumption.
  }
  split. assumption.
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  split.
  intros.
  apply LOCs.
  rewrite LOCKED.
  apply some_none.
  intros.
  rewrite LOCKEDU.
  apply some_none.
  rewrite <- EQH.
  apply LOCs.
  assumption.
  }
  intros.
  destruct ((olocation_eq_dec Z.eq_dec) (Oof ll) o).
  rewrite <- e in *.
  exists ll.
  exists.
  reflexivity.
  rewrite LOCKEDU.
  apply some_none.
  apply INl02 in IN.
  apply OBsOK in IN.
  destruct IN as (l',(EQl',pl')).
  exists l', EQl'.
  rewrite <- EQH.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  rewrite <- EQl' in n.
  contradiction.
  assumption.
  }
  exists.
  {
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  unfold upd.
  rewrite eqz.
  split. assumption.
  split. assumption.
  split. assumption.
  intros.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists (tt, tx, phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked 
    (upd Z.eq_dec (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    ([[vv]]) ((filterb (xOf (fun x  => Lof x) locs) (Aof ll) (fun v => length (filter 
    (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))) ([[vv]])-1))
    (filterb (xOf (fun x  => Lof x) locs) (Aof ll) (count_occ Z.eq_dec (concat (map Aoof T))))))) p1, Oof ll :: O, ghplus C C1, id).
  split.
  apply in_updl_eq.
  exists (WasWaiting4cond vv l, tx, p, O, C).
  auto.
  unfold oof.
  simpl.
  left.
  reflexivity.
  rewrite <- EQH in LOCK.
  assert (tmp1:=LOCK).
  apply LOCKOK in LOCK.
  destruct LOCK as (L1,(L2,(L3,L4))).
  split. assumption.
  split. assumption.
  split. assumption.
  unfold upd.
  intros.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  exfalso.
  apply n.
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  destruct tmp1 as [tmp1|tmp1].
  rewrite tmp1.
  apply some_none.
  destruct tmp1 as (wt1,(ot1,tmp1)).
  destruct tmp1 as [tmp1|tmp1].
  rewrite tmp1.
  apply some_none.
  rewrite tmp1.
  apply some_none.
  symmetry.
  assumption.
  apply L4 in H.
  apply INl01.
  assumption.
  assumption.
  }
  split.
  {
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  rewrite LOCKEDU in *.
  inversion ULOCK.
  rewrite <- EQH in ULOCK.
  assert (tmp1:=ULOCK).
  apply ULOCKOK in ULOCK.
  destruct ULOCK as (U1,U2).
  split.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  exfalso.
  apply n.
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite tmp1.
  apply some_none.
  symmetry. assumption.
  assumption.
  unfold not.
  intros.
  apply U2.
  apply INl02; try assumption.
  unfold not.
  intros.
  assert (CO: ll = l0).
  {
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite tmp1.
  apply some_none.
  unfold Aof.
  rewrite H0.
  reflexivity.
  }
  contradiction.
  assumption.
  }
  intros.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  rewrite LOCKEDU in *.
  inversion UCOND.
  rewrite <- EQH in UCOND.
  assert (tmp1:=UCOND).
  apply UCONDOK in UCOND.
  unfold upd.
  destruct (Z.eq_dec (Aof l0) (Aof ll)).
  exfalso.
  apply n.
  apply INJ.
  rewrite LOCKED.
  apply some_none.
  rewrite tmp1.
  apply some_none.
  symmetry. assumption.
  unfold not.
  intros.
  apply UCOND.
  apply INl02; try assumption.
  unfold Aof in n0.
  unfold not.
  intros.
  rewrite H0 in n0.
  contradiction. 
  assumption.
  }
  exists.
  {
  intros.
  rewrite <- EQOT.
  destruct ((location_eq_dec Z.eq_dec) ll l0).
  rewrite <- e in *.
  rewrite LOCKEDU in *.
  destruct ULOCKED as [U1|U2].
  {
  inversion U1.
  split.
  {
  apply functional_extensionality.
  intros.
  unfold upd at 1.
  destruct (Z.eq_dec x ([[vv]])).
  {
  rewrite e0 in *.
  rewrite <- FIL1.
  reflexivity.
  }
  rewrite <- FIL2.
  reflexivity.
  assumption.
  }
  reflexivity.
  }
  inversion U2.
  rewrite <- EQH in ULOCKED.
  rewrite <- EQWT.
  apply WTsOTsOK.
  assumption.
  unfold not.
  intros.
  rewrite H in n.
  contradiction.
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
  simpl in EQ.
(* ==================== x6 = id ===========*)
  symmetry in EQ.
  inversion EQ.
  exists.
  unfold wellformed.
  simpl. tauto.
  split.

  assert (bp1pp2: boundph (phplus (phplus p1 p) p2)).
  {
  rewrite phplus_comm; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  replace (phplus p2 p1) with (phplus p1 p2); repeat php_.
  }

  assert (bgcc12l: boundgh (ghplus (ghplus (ghplus C1 C2) Cleak) C)).
  {
  apply boundgh_fold with (m:=gof) (l:=T); repeat php_.
  }

  assert (bgc12c: boundgh (ghplus (ghplus C1 C2) C)).
  {
  apply boundgh_mon with Cleak.
  rewrite ghplus_assoc; repeat php_.
  rewrite ghplus_assoc in bgcc12l; repeat php_.
  replace (ghplus C Cleak) with (ghplus Cleak C); repeat php_.
  }

  assert (NEQAlvll: Aof lv <> Aof ll).
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
  rewrite CO in pv.
  rewrite pv in pl.
  inversion pl.
  }

  assert (bgc1c: boundgh (ghplus C1 C)).
  {
  rewrite ghplus_comm; repeat php_.
  apply boundgh_mon with C2.
  rewrite ghplus_assoc; repeat php_.
  }
  {
  rewrite <- eqlv.

  eapply sat_weak_imp1; try assumption.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1,(v2,(CO,rest))).
  inversion CO.
  repeat php_.
  apply SAT1; repeat php_.
  apply p0l.
  assumption.
  unfold filterb.
  rewrite xOf_same.
  rewrite lofv.
  rewrite eqz.
  destruct (Z.eq_dec (Aof lv) (Aof ll)).
  contradiction.

  assert (CO: In (WasWaiting4cond vv l) (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) (Some (Aof lv))))
     (map cmdof T))).
  {
  apply filter_In.
  split.
  apply in_map_iff.
  exists (WasWaiting4cond vv l, tx, p, O, C, id).
  auto.
  simpl.
  rewrite eqlv.
  destruct (opZ_eq_dec (Some ([[vv]])) (Some ([[vv]]))).
  reflexivity.
  contradiction.
  }
  destruct (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) (Some (Aof lv))))
     (map cmdof T)) eqn:FILT.
  inversion CO.
  simpl.
  omega.
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
  unfold spurious_ok in SPUR1.
  destruct SPUR1 as [G|G].
  inversion G.
  destruct G;
  assumption.
  intros.
  eapply sat_tx_weak_imp1; try assumption.
  }
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

  assert (bp0: boundph x3).
  {
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  split. reflexivity. assumption.
  }

  assert (bg0: boundgh x5).
  {
  apply boundgh_fold0 with (m:=gof) (l:=T) (b:=(ghplus (ghplus C1 C2) Cleak)); repeat php_.
  intros.
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
  apply VOBS3 in W4COND.
  destruct W4COND as (v0,(l0,(inv0,(inl0,(eqv0,(eql0,sob1)))))).
  exists v0, l0, inv0, inl0, eqv0, eql0.
  rewrite <- EQOT.
  destruct (location_eq_dec Z.eq_dec l0 ll).
  {
  rewrite e.
  apply safe_obs_wt_weak with (WTs l0 (map cmdof T) locs ([[ev]])).
  rewrite e.
  unfold WTs.
  destruct (Z.eq_dec ([[ev]]) ([[vv]])).
  rewrite e0.
  rewrite <- FIL1.
  omega.
  rewrite <- FIL2.
  omega.
  assumption.
  rewrite <- e.
  assumption.
  }
  rewrite <- EQWT; try assumption.
  apply LOCs.
  assumption.
Qed.
