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

Set Implicit Arguments.

Open Local Scope nat.

Definition cmdof (athread: (cmd * context * pheap * list Z * bag * Z)) : cmd :=
  fst (fst (fst (fst (fst athread)))).

Definition ctxof (athread: (cmd * context * pheap * list Z * bag * Z)) : context :=
  snd (fst (fst (fst (fst athread)))).

Definition pof (athread: (cmd * context * pheap * list Z * bag * Z)) : pheap :=
  snd (fst (fst (fst athread))).

Definition oof (athread: (cmd * context * pheap * list Z * bag * Z)) : list Z :=
  snd (fst (fst athread)).

Definition cof (athread: (cmd * context * pheap * list Z * bag * Z)) : bag :=
  snd (fst athread).

Definition idof (athread: (cmd * context * pheap * list Z * bag * Z)) : Z :=
  snd athread.

Definition wof h (athread: (cmd * context * pheap * list Z * bag * Z)) : option Z :=
  waiting_for h (fst (fst (fst (fst (fst athread))))).


Definition validk (t:thrds) (h:heap) :=
  exists (T: list (cmd * context * pheap * list Z * bag * Z)) (R: Z -> Z) (I: Z -> inv) (L: Z -> Z) (M: Z -> bool) (P: Z -> bool) (X: Z -> list Z)
         (Pinv: pheap) (Ainv: list (lassn * Z)) Cinv (UNQAinv: NoDup (map snd Ainv))
         (Ainvl: forall l (IN: In l (map snd Ainv)), (fold_left phplus (map pof T) Pinv) l = Some Lock /\ h l = Some (1%Z))
         (PHPDL: defl phplusdef (map (fun x => (pof x, idof x)) T))
         (PHPD: forall p (IN: In p (map pof T)), phplusdef p Pinv)
         (BPE: forall p (IN: In p (map pof T)), boundph p) 
         (BPA: boundph Pinv) 
         (BPT: boundph (fold_left phplus (map pof T) Pinv))
         (SATA: lsat Pinv Cinv (fold_left Lastar (map fst Ainv) (Labool true)))
         (PH2H: h = phtoh (fold_left phplus (map pof T) Pinv))
         (AUT: forall id c tx, t id = Some (c,tx) <-> exists p O C, In (c,tx,p,O,C,id) T)
         (UNQ: NoDup (map idof T))
         (VLOCK: forall l (LOCK: (fold_left phplus (map pof T) Pinv) l = Some Lock \/ 
                           exists wt ot ct, (fold_left phplus (map pof T) Pinv) l = Some (Locked wt ot ct)),
                   L l = l /\ P l = false /\ ~ In (R l) (X (L l)) /\ (h l <> Some 1%Z -> In l (concat (map oof T))))
         (VULOCK: forall l wt ot ct (ULOCK: (fold_left phplus (map pof T) Pinv) l = Some (Ulock wt ot ct)), h l = Some 1%Z)
         (WOT: forall l wt ot ct (ULOCKED: (fold_left phplus (map pof T) Pinv) l = Some (Locked wt ot ct) \/ (fold_left phplus (map pof T) Pinv) l = Some (Ulock wt ot ct)), 
                  wt = filterb L l (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) /\
                  ot = filterb L l (count_occ Z.eq_dec (concat (map oof T))) /\
                  ct = filterb L l (fold_left bagplus (map cof T) Cinv))
         (LINV: forall l (LOCK: (fold_left phplus (map pof T) Pinv) l = Some Lock) (NOTHELD: h l = Some (1%Z)), In ((I l) 
           (filterb L l (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
           (filterb L l (count_occ Z.eq_dec (concat (map oof T))))
           (filterb L l (fold_left bagplus (map cof T) Cinv)),l) Ainv)
         (VALIDT: forall id c tx p O C (ING: In (c,tx,p,O,C,id) T), exists
           (WF: wellformed (c,tx))
           (WP: sat p (Some O) C (weakest_pre_ct (c,tx) R I L M P X))
           (VOBS: forall v l (W4COND: c = Waiting4cond v l),
              safe_obs (eval v) (length (filter (fun c => ifb (opZ_eq_dec (waiting_for h c) (Some (eval v)))) (map cmdof T)))
                (count_occ Z.eq_dec (concat (map oof T)) (eval v)) R L P X = true), True), True.

Lemma upd_updl:
  forall (T: list (cmd * context * pheap * list Z * bag * Z)) t id c tx p O C id' c' tx'
         (IN: exists x', In (x', id) T)
         (AUT : forall id c tx, t id = Some (c, tx) <->
                  exists p O C, In (c, tx, p, O, C, id) T),
    upd t id (Some (c, tx)) id' = Some (c', tx') <->
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

Lemma pofs:
  forall z p,
    exists x, pof (x, z) = p.
Proof.
  intros.
  exists (Val 0, done, p, nil, empb).
  reflexivity.
Qed.

Lemma g_initl_preserves_validity:
  forall h t id l tx
         (VALIDK: validk t h)
         (CMD : t id = Some (g_initl l, tx)),
    validk (upd t id (Some (Val 0, tx))) h.
Proof.
Admitted.
(*
  intros.
  unfold validk in VALIDK.
  destruct VALIDK as (T,(R,(I,(L,(M,(P,(X,(Pinv,(Ainv,(Cinv,(NODUPA,(Ainvl,(PHPDL,(PHPD,(BPE,(BPA,(BPT,(SATA,(PH2H,(AUT,(UNQ,(VLOCK,(VULOCK,(WOT,(LINV,(OLC,(LCN,(VALIDT,TR)))))))))))))))))))))))))))).
  unfold validk.
  assert (tmp: exists p O C, In (g_initl l, tx, p, O, C, id) T).
  apply AUT.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply VALIDT in tmp.
  destruct tmp as (WF,(WP,(VOBS,TR1))).
  unfold wellformed in WF.
  simpl in WF.
  apply sat_initl in WP.
  destruct WP as (p1,(p2,(wt,(ot,(ct,(C1,(C2,(bp1,(bp2,(phpdefp1p2,(p1p2,(C1C2,(p1l,(satp2,(lll,(plf,(ninx,SAT))))))))))))))))).
  rewrite p1p2 in *.
  assert (INpT: In (phplus p1 p2) (map pof T)).
  {
  apply in_map_iff.
  exists (g_initl l, tx, phplus p1 p2, O, C, id).
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
  assert (LOCKED: fold_left phplus (map pof T) Pinv ([[l]]) = Some (Ulock wt ot ct)).
  {
  apply fold_ulock.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists (phplus p1 p2), INpT.
  apply phplus_ulock.
  assumption.
  assumption.
  }
  assert (LOCK: fold_left phplus (map pof (updl T id (Val 0, tx, upd p1 ([[l]]) (Some Lock), O, C1, id))) (phplus Pinv p2) ([[l]]) = Some Lock).
  {
  apply lock_Wait with p1.
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (g_initl l, tx, phplus p1 p2, O, C, id).
  auto.
  exists wt, ot, ct.
  right.
  assumption.
  reflexivity.
  }
  assert (EQH: forall l0 (NEQ: ([[l]]) <> l0), fold_left phplus (map pof (updl T id (Val 0, tx, upd p1 ([[l]]) (Some Lock),
    O, C1, id))) (phplus Pinv p2) l0 = 
    fold_left phplus (map pof T) Pinv l0).
  {
  intros.
  apply eq_heap_Wait with (z:=([[l]])) (p1:=p1).
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (g_initl l, tx, phplus p1 p2, O, C, id).
  auto.
  exists wt, ot, ct.
  right.
  assumption.
  reflexivity.
  assumption.
  }
  assert (hl1: h ([[l]]) = Some 1%Z).
  {
  apply VULOCK with wt ot ct.
  assumption.
  }
  exists (updl T id (Val 0, tx, upd p1 ([[l]]) (Some Lock), O, C1, id)).
  exists R, I, L, M, P, X.
  exists (phplus Pinv p2), ((I ([[l]]) wt ot ct,([[l]]))::Ainv), (bagplus Cinv C2).
  assert (EQWT: forall l0 p O C, filterb L l0 (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) =
    filterb L l0 (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof
    (updl T id (Val 0, tx, p, O, C, id)))))).
  {
  intros.
  apply filterb_updl_eq.
  intros.
  split.
  unfold cmdof.
  simpl.
  apply ifboneq.
  intros.
  assert (X': x' = (g_initl l, tx, phplus p1 p2, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  apply ifboneq.
  }
  assert (EQOT: forall l0 c p C, filterb L l0 (count_occ Z.eq_dec (concat (map oof T))) =
    filterb L l0 (count_occ Z.eq_dec (concat (map oof (updl T id (c, tx, p, O, C, id)))))).
  {
  intros.
  apply filterb_updl_obs_eq.
  intros.
  assert (X': x' = (g_initl l, tx, phplus p1 p2, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold oof.
  simpl.
  reflexivity.
  }
  assert (EQCT: forall l0, 
    filterb L l0 (fold_left bagplus (map cof T) Cinv) =
    filterb L l0 (fold_left bagplus (map cof (updl T id
    (Val 0, tx, upd p1 ([[l]]) (Some Lock), O, C1, id))) (bagplus Cinv C2))).
  {
  intros.
  rewrite fold_left_move_m_eq with (def:=bagdef) (x1:=C1) (x2:=C2) (id:=id)
    (x:=(Val 0, tx, upd p1 ([[l]]) (Some Lock), O, C1)).
  rewrite <- fold_left_f with (def:=bagdef).
  rewrite bplus_comm.
  reflexivity.
  apply canbag.
  trivial.
  apply canbag.
  assumption.
  unfold defl.
  trivial.
  assumption.
  trivial.
  rewrite <- C1C2.
  apply in_map_iff.
  exists (g_initl l, tx, phplus p1 p2, O, C, id).
  auto.
  reflexivity.
  }
  assert (bpinvp12: boundph (phplus Pinv (phplus p2 p1))).
  {
  replace (phplus p2 p1) with (phplus p1 p2).
  {
  apply boundph_fold with (m:=pof) (l:=T).
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  apply phplus_comm.
  assumption.
  }
  assert (bppinv2: boundph (phplus Pinv p2)).
  {
  apply boundph_mon with p1.
  assumption.
  assumption.
  assumption.
  rewrite phplus_assoc.
  assumption.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  assumption.
  }
  exists.
  {
  simpl.
  apply NoDup_cons.
  unfold not.
  intros.
  apply Ainvl in H.
  destruct H as (CO1,CO2).
  rewrite LOCKED in CO1.
  inversion CO1.
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
  apply Ainvl in IN.
  destruct IN as (EQ1,EQ2).
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite e in EQ1.
  rewrite LOCKED in EQ1.
  inversion EQ1.
  rewrite EQH.
  split.
  assumption.
  assumption.
  omega.
  }
  exists.
  {
  apply defl_Wait with (p1:=p1) (p2:=p2) (z:=([[l]])).
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (g_initl l, tx, phplus p1 p2, O, C, id).
  auto.
  exists wt, ot, ct.
  right.
  assumption.
  reflexivity.
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
  apply phpdef_pair.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply PHPD.
  assumption.
  apply phpdef_locked_lock.
  assumption.
  exists wt, ot, ct.
  right.
  assumption.
  apply phpdef_locked_lock.
  assumption.
  exists wt, ot, ct.
  right.
  assumption.
  simpl in EQ.
  rewrite <- EQ.
  apply phpdef_pair.
  apply phpdef_comm.
  assumption.
  apply PHPD.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply PHPDL with id x6.
  omega.
  apply in_map_iff.
  exists (g_initl l, tx, phplus p1 p2, O, C, id).
  auto.
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
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  simpl in EQ.
  rewrite <- EQ.
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  exists.
  {
  apply boundph_mon with p1.
  assumption.
  assumption.
  assumption.
  apply bph_assoc.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  assumption.
  }
  exists.
  {
  apply boundph_Wait with (p1:=p1) (z:=([[l]])).
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (g_initl l, tx, phplus p1 p2, O, C, id).
  auto.
  exists wt, ot, ct.
  right.
  assumption.
  reflexivity.
  assumption.
  }
  exists.
  {
  replace (fold_left Lastar (map fst ((I ([[l]]) wt ot ct, [[l]]) :: Ainv)) (Labool true))
     with (fold_left Lastar (map fst Ainv) (Lastar (Labool true) (I ([[l]]) wt ot ct))).
  Focus 2.
  reflexivity.
  simpl.
  apply fold_left_g_can.
  unfold cang.
  split.
  intros.
  apply lsat_comm.
  assumption.
  simpl.
  intros.
  apply lsat_perm with (l:=l0).
  assumption.
  assumption.
  assumption.
  apply lsat_comm.
  apply lsat_plus.
  apply phpdef_comm.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  exists.
  {
  apply functional_extensionality.
  intros.
  unfold upd at 1.
  destruct (Z.eq_dec x ([[l]])).
  rewrite e.
  unfold phtoh.
  unfold upd in LOCK.
  rewrite LOCK.
  assumption.
  unfold phtoh.
  rewrite EQH.
  rewrite PH2H.
  reflexivity.
  omega.
  }
  exists.
  {
  intros.
  apply upd_updl.
  exists (g_initl l, tx, phplus p1 p2, O, C).
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
  intros.
  assert (tmp: L l0 = l0 /\ P l0 = false /\ nexc l0 R X L /\
    (h l0 <> Some 1%Z -> In l0 (concat (map oof T)))).
  {
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite e.
  split.
  assumption.
  split.
  assumption.
  split.
  assumption.
  intros.
  contradiction.
  apply VLOCK.
  rewrite EQH in LOCK0.
  assumption.
  omega.
  }
  destruct tmp as (ll0,(pl0,(ninl0,inl0))).
  split.
  assumption.
  split.
  assumption.
  split.
  assumption.
  intros.
  apply inl0 in H.
  rewrite <- flat_map_concat_map in H.
  apply in_flat_map in H.
  destruct H as (x,(INx,INl0)).
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (g_initl l, tx, phplus p1 p2, O, C)).
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  inversion EQX.
  exists (Val 0, tx, upd p1 ([[l]]) (Some Lock), O, C1, id).
  split.
  apply in_updl_eq.
  exists (g_initl l, tx, phplus p1 p2, O, C).
  auto.
  unfold oof.
  simpl.
  rewrite <- H3.
  assumption.
  exists (x1, x2, x3, x4, x5, x6).
  split.
  apply in_updl_neq.
  omega.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite e.
  assumption.
  apply VULOCK with wt0 ot0 ct0.
  rewrite <- EQH.
  assumption.
  omega.
  }
  exists.
  {
  intros.
  rewrite <- EQWT.
  rewrite <- EQOT.
  rewrite <- EQCT.
  destruct (Z.eq_dec ([[l]]) l0) as [ll0|ll0].
  rewrite <- ll0 in ULOCKED.
  rewrite LOCK in ULOCKED.
  destruct ULOCKED as [U1|U2].
  inversion U1.
  inversion U2.
  apply WOT.
  rewrite <- EQH.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  rewrite <- EQWT.
  rewrite <- EQOT.
  rewrite <- EQCT.
  unfold upd in NOTHELD.
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite e.
  left.
  assert (wot: wt = filterb L ([[l]]) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) /\
    ot = filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))) /\
    ct = filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)).
  {
  apply WOT.
  right.
  assumption.
  }
  destruct wot as (wteq,(oteq,cteq)).
  rewrite wteq.
  rewrite oteq.
  rewrite cteq.
  reflexivity.
  right.
  apply LINV.
  rewrite <- EQH.
  assumption.
  omega.
  assumption.
  }
  exists.
  {
  intros.
  destruct (Z.eq_dec ([[l]]) o).
  rewrite <- e in *.
  rewrite LOCK.
  right.
  left.
  reflexivity.
  rewrite EQH.
  apply OLC.
  rewrite <- map_updl2 with (x:=(Val 0, tx, upd p1 ([[l]]) (Some Lock), O, C1, id));
  try tauto.
  unfold oof.
  simpl.
  apply in_map_iff.
  exists (g_initl l, tx, phplus p1 p2, O, C, id).
  tauto.
  assumption.
  }
  exists.
  {
  intros.
  apply LCN.
  destruct (Z.eq_dec ([[l]]) o).
  rewrite <- e in *.
  right.
  right.
  exists wt, ot, ct.
  right.
  assumption.
  rewrite <- EQH.
  assumption.
  assumption.
  }
  exists.
  {
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
  assumption.
  exists.
  {
  intros.
  inversion W4COND.
  }
  trivial.
(* ==================== x6 <> id ===========*)
  symmetry in EQ.
  inversion EQ.
  assert (tmp:=IN).
  apply VALIDT in tmp.
  destruct tmp as (WF1,(WP1,(VOBS1,TR11))).
  exists.
  assumption.
  exists.
  assumption.
  exists.
  {
  intros.
  assert (NEQlv: ([[l]]) <>([[v]])).
  {
  unfold not.
  intros.
  rewrite W4COND in WP1.
  apply sat_wait4cond in WP1.
  destruct WP1 as (pv0',(pl0',(lvl0',(prcl0',(prcv0',(Cm0',(Cmeq0',SAT0'))))))).
  assert (CO: fold_left phplus (map pof T) Pinv ([[l]]) = Some Cond).
  {
  rewrite H.
  apply fold_cond.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists x3.
  split.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }
  rewrite LOCKED in CO.
  inversion CO.
  }
  assert (EQCNT: forall c tx p C, (count_occ Z.eq_dec (concat (map oof (updl T id (c, tx, p, O, C, id)))) ([[v]]))
    = count_occ Z.eq_dec (concat (map oof T)) ([[v]])).
  {
  intros.
  symmetry.
  apply count_updl_eq.
  intros.
  assert (X': x' = (g_initl l, tx, phplus p1 p2, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold oof.
  simpl.
  reflexivity.
  }
  rewrite EQCNT.
  assert (EQFIL: forall p O C, length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some ([[v]])))) (map cmdof T)) =
    length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for h c0)
    (Some ([[v]])))) (map cmdof (updl T id (Val 0, tx, p, O, C, id))))).
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
  assert (EQX: (a1, a2, a3, a4, a5) = (g_initl l, tx, phplus p1 p2, O, C)).
  eapply unique_key_eq.
  apply IN0.
  assumption.
  assumption.
  inversion EQX.
  reflexivity.
  reflexivity.
  }
  rewrite <- EQFIL.
  apply VOBS1 with l0.
  assumption.
  }
  trivial.
  }
  trivial.
Qed.
*)

Lemma g_disch_preserves_validity:
  forall h t id v tx
         (VALIDK: validk t h)
         (CMD : t id = Some (g_disch v, tx)),
    validk (upd t id (Some (Val 0, tx))) h.
Proof.
  intros.
  unfold validk in VALIDK.
  destruct VALIDK as (T,(R,(I,(L,(M,(P,(X,(Pinv,(Ainv,(Cinv,(NODUPA,(Ainvl,(PHPDL,(PHPD,(BPE,(BPA,(BPT,(SATA,(PH2H,(AUT,(UNQ,(VLOCK,(VULOCK,(WOT,(LINV,(VALIDT,TR)))))))))))))))))))))))))).
  unfold validk.
  assert (tmp: exists p O C, In (g_disch v, tx, p, O, C, id) T).
  apply AUT.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply VALIDT in tmp.
  destruct tmp as (WF,(WP,(VOBS,TR1))).
  unfold wellformed in WF.
  simpl in WF.
  apply sat_disch in WP.
  destruct WP as (wt,(ot,(ct,(O1,(O1eq,(pl,(pv,(INO,(SAFE,SAT))))))))).
  assert (NEQvlv: ([[v]]) <> L ([[v]])).
  {
  unfold not.
  intros.
  rewrite H in pv.
  rewrite pv in pl.
  inversion pl.
  }
 
  assert (INpT: In p (map pof T)).
  {
  apply in_map_iff.
  exists (g_disch v, tx, p, O, C, id).
  auto.
  }
  assert (COND: fold_left phplus (map pof T) Pinv ([[v]]) = Some Cond).
  {
  apply fold_cond.

  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists p, INpT.
  assumption.
  } 
  assert (LOCKED: fold_left phplus (map pof T) Pinv (L ([[v]])) = Some (Locked wt ot ct)).
  {
  apply fold_locked.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists p, INpT.
  assumption.
  }
  assert (LOCK: fold_left phplus (map pof (updl T id (Val 0, tx, upd p (L ([[v]])) (Some (Locked wt (decb ot ([[v]])) ct)),
           O1, C, id))) Pinv (L ([[v]])) = Some (Locked wt (decb ot ([[v]])) ct)).
  {
  apply locked_disch with p.
  apply pofs.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (g_disch v, tx, p, O, C, id).
  auto.
  exists wt, ot, ct.
  assumption.
  reflexivity.
  }
  assert (EQH: forall l0 (NEQ: (L ([[v]])) <> l0), fold_left phplus (map pof (updl T id (Val 0, tx, upd p (L ([[v]])) (Some (Locked wt (decb ot ([[v]])) ct)),
    O1, C, id))) Pinv l0 = 
    fold_left phplus (map pof T) Pinv l0).
  {
  intros.
  apply eq_heap_disch with (p:=p) (z:=L ([[v]])).
  apply pofs.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (g_disch v, tx, p, O, C, id).
  auto.
  exists wt, ot, ct.
  assumption.
  exists wt, (decb ot ([[v]])), ct.
  reflexivity.
  assumption.
  }
  assert (tmp: L (L ([[v]])) = L ([[v]]) /\ P (L ([[v]])) = false /\
           ~ In (R (L ([[v]]))) (X (L (L ([[v]])))) /\
          (h (L ([[v]])) <> Some 1%Z -> In (L ([[v]])) (concat (map oof T)))).
  {
  apply VLOCK.
  right.
  exists wt, ot, ct.
  assumption.
  }
  destruct tmp as (lll,(plf,(ninrlxll,inlt))).
  rewrite lll in *.
  assert (p0l: forall p0 id' (NEQ: id <> id') (IN: In (p0,id') (map (fun x => (pof x, idof x)) T)), p0 (L ([[v]])) = Some Lock \/ p0 (L ([[v]])) = None).
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
  apply PHPDL with id x6.
  omega.
  apply in_map_iff.
  exists (g_disch v, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  rewrite <- H0.
  auto.
  }
  unfold phplusdef in PHPDp0.
  specialize PHPDp0 with (L ([[v]])).
  rewrite pl in PHPDp0.
  destruct (p0 (L ([[v]]))) eqn:p0l.
  destruct k;
  try contradiction.
  left.
  reflexivity.
  right.
  reflexivity.
  }
  assert (pinvl: Pinv (L ([[v]])) = Some Lock \/ Pinv (L ([[v]])) = None).
  {
  assert (PHPDppi: phplusdef p Pinv).
  {
  apply PHPD.
  assumption.
  }
  unfold phplusdef in PHPDppi.
  specialize PHPDppi with (L ([[v]])).
  rewrite pl in PHPDppi.
  destruct (Pinv (L ([[v]]))).
  destruct k;
  try contradiction.
  left.
  reflexivity.
  right.
  reflexivity.
  }
 
  exists (updl T id (Val 0, tx, upd p (L ([[v]])) (Some (Locked wt (decb ot ([[v]])) ct)),
    O1, C, id)).
  exists R, I, L, M, P, X, Pinv, Ainv, Cinv.
  assert (EQWT: forall l0 p O C, filterb L l0 (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) =
    filterb L l0 (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof
    (updl T id (Val 0, tx, p, O, C, id)))))).
  {
  intros.
  apply filterb_updl_eq.
  intros.
  split.
  unfold cmdof.
  simpl.
  apply ifboneq.
  intros.
  assert (X': x' = (g_disch v, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  apply ifboneq.
  }
  assert (EQO: forall l (NEQ: l <> (L ([[v]]))), filterb L l (count_occ Z.eq_dec (concat (map oof (updl T id
    (Val 0, tx, upd p (L ([[v]])) (Some (Locked wt (decb ot ([[v]])) ct)), O1, C, id)))))
     = filterb L l (count_occ Z.eq_dec (concat (map oof T)))).
  {
  intros.
  symmetry.
  apply filterb_updl_obs_eq.
  intros.
  assert (X': x' = (g_disch v, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold oof.
  simpl.
  rewrite O1eq.
  simpl.
  destruct (Z.eq_dec ([[v]]) v0).
  rewrite <- e in IN.
  omega.
  reflexivity.
  }
  assert (ODEC: count_occ Z.eq_dec (concat (map oof T)) ([[v]]) - 1 = count_occ Z.eq_dec (concat
    (map oof (updl T id (Val 0, tx, upd p (L ([[v]])) (Some (Locked wt (upd ot ([[v]]) (ot ([[v]]) - 1)) ct)),
    O1, C, id)))) ([[v]])).
  {
  apply count_updl_decr with O1.
  assumption.
  apply in_map_iff.
  exists (g_disch v, tx, p, O, C, id).
  rewrite <- O1eq.
  auto.
  reflexivity.
  }
  assert (EQCT: forall p O l0, 
    filterb L l0 (fold_left bagplus (map cof T) Cinv) =
    filterb L l0 (fold_left bagplus (map cof (updl T id
    (Val 0, tx, p, O, C, id))) Cinv)).
  {
  intros.
  unfold updl.
  rewrite map_map.
  rewrite map_ext_in with (g := fun x : cmd * context * pheap * list Z * bag * Z =>
         cof (if Z.eq_dec (snd x) id then (Val 0, tx, p0, O0, C, id) else x)).
  reflexivity.
  intros.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  rewrite e in *.
  assert (EQX: (a1, a2, a3, a4, a5) = (g_disch v, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  assumption.
  assumption.
  inversion EQX.
  reflexivity.
  reflexivity.
  }
  exists NODUPA.
  exists.
  {
  intros.
  apply Ainvl in IN.
  destruct IN as (EQ1,EQ2).
  destruct (Z.eq_dec l (L ([[v]]))).
  rewrite e in *.
  rewrite LOCKED in EQ1.
  inversion EQ1.
  rewrite EQH.
  auto.
  omega.
  }
  exists.
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
  unfold idof in EQ1.
  simpl in EQ1.
  inversion EQ1.
  destruct (Z.eq_dec y6 id).
  rewrite e0 in *.
  unfold pof in EQ2.
  unfold idof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  omega.
  unfold pof in EQ2.
  unfold idof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  apply phpdef_upd_locked.
  apply PHPDL with id y6.
  omega.
  apply in_map_iff.
  exists (g_disch v, tx, p, O, C, id).
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
  unfold idof in EQ1.
  simpl in EQ1.
  inversion EQ1.
  destruct (Z.eq_dec y6 id).
  rewrite e in *.
  unfold pof in EQ2.
  unfold idof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  apply phpdef_comm.
  apply phpdef_upd_locked.
  apply PHPDL with id a6.
  omega.
  apply in_map_iff.
  exists (g_disch v, tx, p, O, C, id).
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
  unfold idof in EQ2.
  simpl in EQ2.
  inversion EQ2.
  apply PHPDL with a6 y6.
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
  apply phpdef_upd_locked.
  apply PHPD.
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
  apply boundph_upd.
  apply BPE.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  simpl in EQ.
  rewrite <- EQ.
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  exists BPA.
  exists.
  {
  apply boundph_disch with (p:=p) (z:=L ([[v]])).
  apply pofs.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (g_disch v, tx, p, O, C, id).
  auto.
  exists wt, ot, ct.
  assumption.
  exists wt, (decb ot ([[v]])), ct.
  reflexivity.
  assumption.
  }
  exists SATA.
  exists.
  {
  apply functional_extensionality.
  intros.
  unfold upd.
  destruct (Z.eq_dec x (L ([[v]]))).
  rewrite e.
  rewrite PH2H.
  unfold phtoh.
  unfold upd in *.
  rewrite LOCK.
  rewrite LOCKED.
  reflexivity.
  rewrite PH2H.
  unfold phtoh.
  rewrite EQH.
  reflexivity.
  omega.
  }
  exists.
  {
  intros.
  apply upd_updl.
  exists (g_disch v, tx, p, O, C).
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
  intros.
  assert (tmp: L l = l /\ P l = false /\
    ~ In (R l) (X (L l)) /\
    (h l <> Some 1%Z -> In l (concat (map oof T)))).
  {
  apply VLOCK.
  destruct (Z.eq_dec l (L ([[v]]))).
  rewrite e.
  right.
  exists wt, ot, ct.
  assumption.
  rewrite EQH in LOCK0.
  assumption.
  omega.
  }
  destruct tmp as (ll0,(pl0,(ninl0,inl0))).
  split.
  assumption.
  split.
  assumption.
  split.
  assumption.
  intros.
  apply inl0 in H.
  rewrite <- flat_map_concat_map in H.
  apply in_flat_map in H.
  destruct H as (x,(INx,INl0)).
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  destruct (Z.eq_dec x6 id).
  rewrite e in *.
  assert (EQX: (x1, x2, x3, x4, x5) = (g_disch v, tx, p, O, C)).
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  inversion EQX.
  exists (Val 0, tx, upd p (L ([[v]])) (Some (Locked wt (decb ot ([[v]])) ct)),
                  O1, C, id).
  split.
  apply in_updl_eq.
  exists (g_disch v, tx, p, O, C).
  auto.
  unfold oof in *.
  simpl.
  simpl in INl0.
  rewrite H3 in INl0.
  rewrite O1eq in INl0.
  simpl in INl0.
  destruct INl0 as [CO|GO].
  assert (CO1: fold_left phplus
          (map pof
             (updl T id
                (Val 0, tx,
                upd p (L ([[v]])) (Some (Locked wt (decb ot ([[v]])) ct)),
                O1, C, id))) Pinv l = Some Cond).
  {
  rewrite EQH.
  rewrite <- CO.
  assumption.
  omega.
  }
  rewrite CO1 in LOCK0.
  destruct LOCK0 as [CO11|CO12].
  inversion CO11.
  destruct CO12 as (ww,(oo,(tt,CO12))).
  inversion CO12.
  assumption.
  exists (x1, x2, x3, x4, x5, x6).
  split.
  apply in_updl_neq.
  omega.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  destruct (Z.eq_dec l (L ([[v]]))) as [ll|ll].
  rewrite ll in ULOCK.
  rewrite LOCK in ULOCK.
  inversion ULOCK.
  apply VULOCK with wt0 ot0 ct0.
  rewrite <- EQH.
  assumption.
  omega.
  }
  exists.
  {
  intros.
  rewrite <- EQWT.
  rewrite <- EQCT.
  destruct (Z.eq_dec l (L ([[v]]))) as [ll|ll].
  {
  assert (wot: wt = filterb L (L ([[v]])) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) /\
    ot = filterb L (L ([[v]])) (count_occ Z.eq_dec (concat (map oof T))) /\
    ct = filterb L (L ([[v]])) (fold_left bagplus (map cof T) Cinv)).
  {
  apply WOT.
  left.
  assumption.
  }
  destruct wot as (wteq,(oteq,cteq)).
  rewrite ll in *.
  assert (U:=ULOCKED).
  rewrite LOCK in U.
  destruct U as [U1|U2].
  symmetry in U1.
  inversion U1.
  split.
  assumption.
  split.
  {
  rewrite oteq at 1.
  unfold decb.
  unfold upd at 1.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x ([[v]])).
  rewrite e.
  unfold filterb.
  destruct (Z.eq_dec ([[v]]) (L ([[v]]))).
  contradiction.
  rewrite eqz.
  rewrite eqz.
  apply ODEC.
  unfold filterb.
  destruct (Z.eq_dec x (L ([[v]]))).
  reflexivity.
  destruct (Z.eq_dec  (L x) (L ([[v]]))).
  apply count_updl_eq.
  intros.
  assert (X': x' = (g_disch v, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold oof.
  simpl.
  rewrite O1eq.
  simpl.
  destruct (Z.eq_dec ([[v]]) x).
  omega.
  reflexivity.
  reflexivity.
  }
  assumption.
  inversion U2.
  }
  rewrite EQH in ULOCKED.
  apply WOT in ULOCKED.
  rewrite EQO.
  assumption.
  omega.
  omega.
  }
  exists.
  {
  intros.
  assert (NEQllv: l <> L ([[v]])).
  {
  unfold not.
  intros.
  rewrite H in LOCK0.
  rewrite LOCK in LOCK0.
  inversion LOCK0.
  }
  rewrite <- EQWT.
  rewrite EQO.
  rewrite <- EQCT.
  apply LINV.
  rewrite <- EQH.
  assumption.
  omega.
  assumption.
  omega.
  }
  exists.
  {
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
  assumption.
  exists.
  {
  intros.
  inversion W4COND.
  }
  trivial.
(* ==================== x6 <> id ===========*)
  symmetry in EQ.
  inversion EQ.
  assert (tmp:=IN).
  apply VALIDT in tmp.
  destruct tmp as (WF1,(WP1,(VOBS1,TR11))).
  exists.
  assumption.
  exists.
  assumption.
  exists.
  {
  intros.
  assert (NEQlv: ([[l]]) <>([[v]])).
  {
  unfold not.
  intros.
  rewrite W4COND in WP1.
  apply sat_wait4cond in WP1.
  destruct WP1 as (pv0',(pl0',(lvl0',(prcl0',(prcv0',(Cm0',(Cmeq0',SAT0'))))))).
  assert (CO: fold_left phplus (map pof T) Pinv ([[l]]) = Some Cond).
  {
  rewrite H.
  apply fold_cond.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists p.
  split.
  apply in_map_iff.
  exists (g_disch v, tx, p, O, C, id).
  auto.
  assumption.
  }
  assert (CO2: fold_left phplus (map pof T) Pinv ([[l]]) = Some Lock \/
    exists wt ot ct, fold_left phplus (map pof T) Pinv ([[l]]) = Some (Locked wt ot ct)).
  {
  destruct pl0' as [pl0'|pl0'].
  apply phplus_fold_lock.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists x3.
  split.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  assumption.
  right.
  destruct pl0' as (wt',(ot',(ct',pl0'))).
  exists wt', ot', ct'.
  apply fold_locked.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists x3.
  split.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }
  rewrite CO in CO2.
  destruct CO2 as [CO2|CO2].
  inversion CO2.
  destruct CO2 as (wt2,(ot2,(ct2,CO2))).
  inversion CO2.
  }
  assert (EQW: length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for h c0) (Some ([[v0]]))))
    (map cmdof (updl T id (Val 0, tx, upd p (L ([[v]])) (Some (Locked wt (decb ot ([[v]])) ct)),
    O1, C, id)))) =
    length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for h c0) (Some ([[v0]])))) (map cmdof T ))).
  {
  rewrite <- filter_updl_eq.
  reflexivity.
  unfold cmdof.
  simpl.
  apply ifboneq.
  intros.
  assert (X': x' = (g_disch v, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  apply ifboneq.
  }
  rewrite EQW.
  destruct (Z.eq_dec ([[v]]) ([[v0]])).
  {
  rewrite <- e.
  unfold decb.
  rewrite <- ODEC.
  assert (wot: wt = filterb L (L ([[v]])) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) /\
    ot = filterb L (L ([[v]])) (count_occ Z.eq_dec (concat (map oof T))) /\
    ct = filterb L (L ([[v]])) (fold_left bagplus (map cof T) Cinv)).
  {
  apply WOT.
  left.
  assumption.
  }
  destruct wot as (eqwt,(eqot,eqct)).
  assert (S:=SAFE).
  rewrite eqwt in S.
  rewrite eqot in S.
  simpl in S.
  assert (EQFW: length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for h c0) (Some ([[v]])))) (map cmdof T)) =
    filterb L (L ([[v]])) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof T))) ([[v]])).
  {
  unfold filterb.
  destruct (Z.eq_dec ([[v]]) (L ([[v]]))).
  omega.
  rewrite eqz.
  rewrite filter_filter_eq with (f2 := fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) (Some ([[v]])))).
  reflexivity.
  intros.
  destruct (opZ_eq_dec (waiting_for_cond x) (waiting_for h x)).
  rewrite e0.
  reflexivity.
  apply waiting_for_cond_neq in n1.
  destruct n1 as (l1,eqx).
  rewrite eqx in *.
  simpl.
  destruct (opZ_eq_dec (h ([[l1]])) (Some 1%Z)).
  reflexivity.
  destruct (opZ_eq_dec (Some ([[l1]])) (Some ([[v]]))).
  inversion e0.
  apply in_map_iff in IN0.
  destruct IN0 as (a,(EQ0,IN0)).
  assert (tmp:=IN0).
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  unfold cmdof in EQ0.
  simpl in EQ0.
  rewrite EQ0 in *.
  apply VALIDT in tmp.
  destruct tmp as (WF2,(WP2,rest)).
  apply sat_wait4lock in WP2.
  destruct WP2 as (x3l1,PRCl1).
  assert (CO: fold_left phplus (map pof T) Pinv ([[v]]) = Some Lock \/
    exists wt ot ct, fold_left phplus (map pof T) Pinv ([[v]]) = Some (Locked wt ot ct)).
  {
  rewrite <- H6.
  apply fold_lock_ed.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  right.
  exists a3.
  split.
  apply in_map_iff.
  exists (Waiting4lock l1, a2, a3, a4, a5, a6).
  auto.
  assumption.
  }
  rewrite COND in CO.
  destruct CO as [CO|CO].
  inversion CO.
  destruct CO as (wt2,(ot2,(ct2,CO))).
  inversion CO.
  symmetry.
  apply ifboneq.
  }
  rewrite EQFW.
  assert (EQFO: (count_occ Z.eq_dec (concat (map oof T)) ([[v]]) - 1) =
    filterb L (L ([[v]])) (count_occ Z.eq_dec (concat (map oof T))) ([[v]]) - 1).
  {
  unfold filterb.
  destruct (Z.eq_dec ([[v]]) (L ([[v]]))).
  omega.
  rewrite eqz.
  reflexivity.
  }
  rewrite EQFO.
  assumption.
  }
  rewrite <- count_updl_eq.
  apply VOBS1 with l.
  assumption.
  intros.
  assert (X': x' = (g_disch v, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold oof.
  simpl.
  rewrite O1eq.
  simpl.
  destruct (Z.eq_dec ([[v]]) ([[v0]])).
  omega.
  reflexivity.
  }
  trivial.
  }
  trivial.
Qed.
Lemma Release_preserves_validity:
  forall h t id l tx
         (VALIDK: validk t h)
         (CMD : t id = Some (Release l, tx)),
    validk (upd t id (Some (Val 0, tx))) (upd h ([[l]]) (Some 1%Z)).
Proof.
  intros.
  unfold validk in VALIDK.
  destruct VALIDK as (T,(R,(I,(L,(M,(P,(X,(Pinv,(Ainv,(Cinv,(NODUPA,(Ainvl,(PHPDL,(PHPD,(BPE,(BPA,(BPT,(SATA,(PH2H,(AUT,(UNQ,(VLOCK,(VULOCK,(WOT,(LINV,(VALIDT,TR)))))))))))))))))))))))))).
  unfold validk.
  assert (tmp: exists p O C, In (Release l, tx, p, O, C, id) T).
  apply AUT.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply VALIDT in tmp.
  destruct tmp as (WF,(WP,(VOBS,TR1))).
  unfold wellformed in WF.
  simpl in WF.
  apply sat_release in WP.
  destruct WP as (p1,(p2,(wt,(ot,(ct,(C1,(C2,(O1,(O1eq,(bp1,(bp2,(phpdefp1p2,(p1p2,(C1C2,(p1l,(satp2,SAT)))))))))))))))).
  rewrite p1p2 in *.
  assert (INpT: In (phplus p1 p2) (map pof T)).
  {
  apply in_map_iff.
  exists (Release l, tx, phplus p1 p2, O, C, id).
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
  assert (LOCKED: fold_left phplus (map pof T) Pinv ([[l]]) = Some (Locked wt ot ct)).
  {
  apply fold_locked.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists (phplus p1 p2), INpT.
  apply phplus_locked.
  assumption.
  assumption.
  }
  assert (LOCK: fold_left phplus (map pof (updl T id (Val 0, tx, upd p1 ([[l]]) (Some Lock),
           O1, C1, id))) (phplus Pinv p2) ([[l]]) = Some Lock).
  {
  apply lock_Wait with p1.
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Release l, tx, phplus p1 p2, O, C, id).
  auto.
  exists wt, ot, ct.
  left.
  assumption.
  reflexivity.
  }
  assert (EQH: forall l0 (NEQ: ([[l]]) <> l0), fold_left phplus (map pof (updl T id (Val 0, tx, upd p1 ([[l]]) (Some Lock),
    O1, C1, id))) (phplus Pinv p2) l0 = 
    fold_left phplus (map pof T) Pinv l0).
  {
  intros.
  apply eq_heap_Wait with (z:=([[l]])) (p1:=p1).
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Release l, tx, phplus p1 p2, O, C, id).
  auto.
  exists wt, ot, ct.
  left.
  assumption.
  reflexivity.
  assumption.
  }
  assert (tmp: L ([[l]]) = ([[l]]) /\ P ([[l]]) = false /\
           ~ In (R ([[l]])) (X (L ([[l]]))) /\
          (h ([[l]]) <> Some 1%Z -> In ([[l]]) (concat (map oof T)))).
  {
  apply VLOCK.
  right.
  exists wt, ot, ct.
  assumption.
  }
  destruct tmp as (lll,(plf,(ninrlxll,inlt))).
  rewrite lll in *.
  exists (updl T id (Val 0, tx, upd p1 ([[l]]) (Some Lock), O1, C1, id)).
  exists R, I, L, M, P, X.
  exists (phplus Pinv p2), ((I ([[l]]) wt ot ct,([[l]]))::Ainv), (bagplus Cinv C2).
  assert (EQWT: forall l0 p O C, filterb L l0 (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) =
    filterb L l0 (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof
    (updl T id (Val 0, tx, p, O, C, id)))))).
  {
  intros.
  apply filterb_updl_eq.
  intros.
  split.
  unfold cmdof.
  simpl.
  apply ifboneq.
  intros.
  assert (X': x' = (Release l, tx, phplus p1 p2, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  apply ifboneq.
  }
  assert (EQOT: forall l0 c p C, filterb L l0 (count_occ Z.eq_dec (concat (map oof T))) =
    filterb L l0 (count_occ Z.eq_dec (concat (map oof (updl T id
    (c, tx, p, O1, C, id)))))).
  {
  intros.
  apply filterb_updl_obs_eq.
  intros.
  assert (X': x' = (Release l, tx, phplus p1 p2, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold oof.
  simpl.
  destruct (Z.eq_dec ([[l]]) v).
  rewrite <- e in IN.
  rewrite lll in IN.
  rewrite <- e in NEQ.
  contradiction.
  rewrite O1eq.
  simpl.
  destruct (Z.eq_dec ([[l]]) v).
  omega.
  reflexivity.
  }
  assert (EQCT: forall l0, 
    filterb L l0 (fold_left bagplus (map cof T) Cinv) =
    filterb L l0 (fold_left bagplus (map cof (updl T id
    (Val 0, tx, upd p1 ([[l]]) (Some Lock), O1, C1, id))) (bagplus Cinv C2))).
  {
  intros.
  rewrite fold_left_move_m_eq with (def:=bagdef) (x1:=C1) (x2:=C2) (id:=id)
    (x:=(Val 0, tx, upd p1 ([[l]]) (Some Lock), O1, C1)).
  rewrite <- fold_left_f with (def:=bagdef).
  rewrite bplus_comm.
  reflexivity.
  apply canbag.
  trivial.
  apply canbag.
  assumption.
  unfold defl.
  trivial.
  assumption.
  trivial.
  rewrite <- C1C2.
  apply in_map_iff.
  exists (Release l, tx, phplus p1 p2, O, C, id).
  auto.
  reflexivity.
  }
  assert (bpinvp12: boundph (phplus Pinv (phplus p2 p1))).
  {
  replace (phplus p2 p1) with (phplus p1 p2).
  {
  apply boundph_fold with (m:=pof) (l:=T).
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  apply phplus_comm.
  assumption.
  }
  assert (bppinv2: boundph (phplus Pinv p2)).
  {
  apply boundph_mon with p1.
  assumption.
  assumption.
  assumption.
  rewrite phplus_assoc.
  assumption.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  assumption.
  }
  exists.
  {
  simpl.
  apply NoDup_cons.
  unfold not.
  intros.
  apply Ainvl in H.
  destruct H as (CO1,CO2).
  rewrite LOCKED in CO1.
  inversion CO1.
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
  rewrite eqz.
  reflexivity.
  apply Ainvl in IN.
  destruct IN as (EQ1,EQ2).
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite e in EQ1.
  rewrite LOCKED in EQ1.
  inversion EQ1.
  rewrite EQH.
  split.
  assumption.
  unfold upd.
  destruct (Z.eq_dec l0 ([[l]])).
  contradiction.
  assumption.
  omega.
  }
  exists.
  {
  apply defl_Wait with (p1:=p1) (p2:=p2) (z:=([[l]])).
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Release l, tx, phplus p1 p2, O, C, id).
  auto.
  exists wt, ot, ct.
  left.
  assumption.
  reflexivity.
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
  apply phpdef_pair.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply PHPD.
  assumption.
  apply phpdef_locked_lock.
  assumption.
  exists wt, ot, ct.
  left.
  assumption.
  apply phpdef_locked_lock.
  assumption.
  exists wt, ot, ct.
  left.
  assumption.
  simpl in EQ.
  rewrite <- EQ.
  apply phpdef_pair.
  apply phpdef_comm.
  assumption.
  apply PHPD.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply PHPDL with id x6.
  omega.
  apply in_map_iff.
  exists (Release l, tx, phplus p1 p2, O, C, id).
  auto.
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
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  simpl in EQ.
  rewrite <- EQ.
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  exists bppinv2.
  exists.
  {
  apply boundph_Wait with (p1:=p1) (z:=([[l]])).
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Release l, tx, phplus p1 p2, O, C, id).
  auto.
  exists wt, ot, ct.
  left.
  assumption.
  reflexivity.
  assumption.
  }
  exists.
  {
  replace (fold_left Lastar (map fst ((I ([[l]]) wt ot ct, [[l]]) :: Ainv)) (Labool true))
     with (fold_left Lastar (map fst Ainv) (Lastar (Labool true) (I ([[l]]) wt ot ct))).
  Focus 2.
  reflexivity.
  simpl.
  apply fold_left_g_can.
  unfold cang.
  split.
  intros.
  apply lsat_comm.
  assumption.
  simpl.
  intros.
  apply lsat_perm with (l:=l0).
  assumption.
  assumption.
  assumption.
  apply lsat_comm.
  apply lsat_plus.
  apply phpdef_comm.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  exists.
  {
  apply functional_extensionality.
  intros.
  unfold upd at 1.
  destruct (Z.eq_dec x ([[l]])).
  rewrite e.
  unfold phtoh.
  rewrite LOCK.
  reflexivity.
  unfold phtoh.
  rewrite EQH.
  rewrite PH2H.
  reflexivity.
  omega.
  }
  exists.
  {
  intros.
  apply upd_updl.
  exists (Release l, tx, phplus p1 p2, O, C).
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
  intros.
  assert (tmp: L l0 = l0 /\ P l0 = false /\
    ~ In (R l0) (X (L l0)) /\
    (h l0 <> Some 1%Z -> In l0 (concat (map oof T)))).
  {
  apply VLOCK.
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite e.
  right.
  exists wt, ot, ct.
  assumption.
  rewrite EQH in LOCK0.
  assumption.
  omega.
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
  destruct (Z.eq_dec l0 ([[l]])).
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
  assert (EQX: (x1, x2, x3, x4, x5) = (Release l, tx, phplus p1 p2, O, C)).
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  inversion EQX.
  exists (Val 0, tx, upd p1 ([[l]]) (Some Lock), O1, C1, id).
  split.
  apply in_updl_eq.
  exists (Release l, tx, phplus p1 p2, O, C).
  auto.
  unfold oof.
  simpl.
  unfold oof in INl0.
  simpl in INl0.
  rewrite H3 in INl0.
  rewrite O1eq in INl0.
  destruct INl0 as [INl0|INl0].
  omega.
  assumption.
  exists (x1, x2, x3, x4, x5, x6).
  split.
  apply in_updl_neq.
  omega.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  unfold upd.
  destruct (Z.eq_dec l0 ([[l]])).
  reflexivity.
  apply VULOCK with wt0 ot0 ct0.
  rewrite <- EQH.
  assumption.
  omega.
  }
  exists.
  {
  intros.
  rewrite <- EQWT.
  rewrite <- EQOT.
  rewrite <- EQCT.
  destruct (Z.eq_dec ([[l]]) l0) as [ll0|ll0].
  rewrite <- ll0 in ULOCKED.
  rewrite LOCK in ULOCKED.
  destruct ULOCKED as [U1|U2].
  inversion U1.
  inversion U2.
  apply WOT.
  rewrite <- EQH.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  rewrite <- EQWT.
  rewrite <- EQOT.
  rewrite <- EQCT.
  unfold upd in NOTHELD.
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite e.
  left.
  assert (wot: wt = filterb L ([[l]]) (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) /\
    ot = filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))) /\
    ct = filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)).
  {
  apply WOT.
  left.
  assumption.
  }
  destruct wot as (wteq,(oteq,cteq)).
  rewrite wteq.
  rewrite oteq.
  rewrite cteq.
  reflexivity.
  right.
  apply LINV.
  rewrite <- EQH.
  assumption.
  omega.
  assumption.
  }
  exists.
  {
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
  assumption.
  exists.
  {
  intros.
  inversion W4COND.
  }
  trivial.
(* ==================== x6 <> id ===========*)
  symmetry in EQ.
  inversion EQ.
  assert (tmp:=IN).
  apply VALIDT in tmp.
  destruct tmp as (WF1,(WP1,(VOBS1,TR11))).
  exists.
  assumption.
  exists.
  assumption.
  exists.
  {
  intros.
  assert (NEQlv: ([[l]]) <>([[v]])).
  {
  unfold not.
  intros.
  rewrite W4COND in WP1.
  apply sat_wait4cond in WP1.
  destruct WP1 as (pv0',(pl0',(lvl0',(prcl0',(prcv0',(Cm0',(Cmeq0',SAT0'))))))).
  assert (CO: fold_left phplus (map pof T) Pinv ([[l]]) = Some Cond).
  {
  rewrite H.
  apply fold_cond.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists x3.
  split.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }
  rewrite LOCKED in CO.
  inversion CO.
  }
  assert (EQCNT: forall c tx p C, (count_occ Z.eq_dec (concat (map oof (updl T id (c, tx, p, O1, C, id)))) ([[v]]))
    = count_occ Z.eq_dec (concat (map oof T)) ([[v]])).
  {
  intros.
  symmetry.
  apply count_updl_eq.
  intros.
  assert (X': x' = (Release l, tx, phplus p1 p2, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold oof.
  simpl.
  rewrite O1eq.
  simpl.
  destruct (Z.eq_dec ([[l]]) ([[v]])).
  omega.
  reflexivity.
  }
  rewrite EQCNT.
  assert (EQFIL: forall p O C, length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some ([[v]])))) (map cmdof T)) =
    length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for (upd h ([[l]]) (Some 1%Z)) c0)
    (Some ([[v]])))) (map cmdof (updl T id (Val 0, tx, p, O, C, id))))).
  {
  intros.
  rewrite filter_filter_eq with (f2:=(fun c0 : cmd =>
      ifb
        (opZ_eq_dec (waiting_for (upd h ([[l]]) (Some 1%Z)) c0)
           (Some ([[v]]))))).
  unfold updl.
  rewrite map_map.
  apply filter_map_eq.
  intros.
  destruct x as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  rewrite e in *.
  assert (EQX: (a1, a2, a3, a4, a5) = (Release l, tx, phplus p1 p2, O, C)).
  eapply unique_key_eq.
  apply IN0.
  assumption.
  assumption.
  inversion EQX.
  reflexivity.
  reflexivity.
  intros.
  apply waiting_for_upd_eq.
  assumption.
  }
  rewrite <- EQFIL.
  apply VOBS1 with l0.
  assumption.
  }
  trivial.
  }
  trivial.
Qed.
Lemma Waiting4lock_preserves_validity:
  forall h t id l tx
         (VALIDK: validk t h)
         (CMD : t id = Some (Waiting4lock l, tx))
         (NON: h ([[l]]) = Some 1%Z),
    validk (upd t id (Some (Val 0, tx))) (upd h ([[l]]) (Some 0%Z)).
Proof.
  intros.
  unfold validk in VALIDK.
  destruct VALIDK as (T,(R,(I,(L,(M,(P,(X,(Pinv,(Ainv,(Cinv,(NODUPA,(Ainvl,(PHPDL,(PHPD,(BPE,(BPA,(BPT,(SATA,(PH2H,(AUT,(UNQ,(VLOCK,(VULOCK,(WOT,(LINV,(VALIDT,TR)))))))))))))))))))))))))).
  unfold validk.
  assert (tmp: exists p O C, In (Waiting4lock l, tx, p, O, C, id) T).
  apply AUT.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply VALIDT in tmp.
  destruct tmp as (WF,(WP,(VOBS,TR1))).
  unfold wellformed in WF.
  simpl in WF.
  apply sat_wait4lock in WP.
  destruct WP as (pl,prcl).
  assert (EQFOLD: fold_left phplus (map pof T) Pinv = phplus Pinv (fold_left phplus (map pof T) (emp knowledge))).
  {
  replace Pinv with (phplus Pinv (emp knowledge)) at 1.
  apply fold_left_f_m_def with (def:=phplusdef).
  apply can_phpdef.
  assumption.
  assumption.
  apply phpdef_emp.
  intros.
  split.
  apply PHPD.
  assumption.
  apply phpdef_emp.
  apply phplus_emp.
  }
  assert (INpT: In p (map pof T)).
  {
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  }
  assert (LOCKED: fold_left phplus (map pof T) Pinv ([[l]]) = Some Lock).
  {
  assert (tmp: fold_left phplus (map pof T) Pinv ([[l]]) = Some Lock \/
       (exists wt ot ct : bag,
          fold_left phplus (map pof T) Pinv ([[l]]) =
          Some (Locked wt ot ct))).
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
  destruct LKED as (wt,(ot,(ct,LKED))).
  assert (CO:=PH2H).
  apply equal_f with ([[l]]) in CO.
  unfold phtoh in CO.
  rewrite LKED in CO.
  rewrite NON in CO.
  inversion CO.
  }
  assert (tmp: L ([[l]]) = ([[l]]) /\ P ([[l]]) = false /\
           ~ In (R ([[l]])) (X (L ([[l]]))) /\
          (h ([[l]]) <> Some 1%Z -> In ([[l]]) (concat (map oof T)))).
  {
  apply VLOCK.
  left.
  assumption.
  }
  destruct tmp as (lll,(plf,(ninrlxll,inlt))).
  rewrite lll in *.
  assert (PERM: Permutation Ainv (
    (I ([[l]]) (filterb L ([[l]]) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)), ([[l]]))
     :: filter (fun x => negb (Z.eqb (snd x) ([[l]]))) Ainv)).
  {
  apply perm_filter.
  assumption.
  apply LINV.
  assumption.
  assumption.
  unfold negb.
  simpl.
  rewrite zeqb.
  reflexivity.
  intros.
  unfold negb.
  simpl.
  destruct (z' =? ([[l]]))%Z eqn:z'l.
  apply Z.eqb_eq in z'l.
  contradiction.
  reflexivity.
  }
  assert (SATA2: lsat Pinv Cinv (fold_left Lastar (map fst 
    ((I ([[l]]) (filterb L ([[l]]) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)), ([[l]]))
    :: filter (fun x => negb (Z.eqb (snd x) ([[l]]))) Ainv)
    ) (Labool true))).
  {
  apply lsat_perm with (map fst Ainv).
  apply Permutation_map.
  assumption.
  assumption.
  assumption.
  }
  simpl in SATA2.
  assert (SATA3: lsat Pinv Cinv 
    (Lastar (I ([[l]]) (filterb L ([[l]]) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)))
    (fold_left Lastar (map fst 
    (filter (fun x => negb (Z.eqb (snd x) ([[l]]))) Ainv))
    (Labool true)))).
  {
  apply fold_left_g_can2.
  unfold cang.
  split.
  intros.
  apply lsat_comm.
  assumption.
  simpl.
  intros.
  apply lsat_perm with (l:=l0).
  assumption.
  assumption.
  assumption.
  assumption.
  }
  simpl in SATA3.
  destruct SATA3 as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(C1,(C2,(SATp1,(SATp2,(p1p2,C1C2))))))))))).
  rewrite <- p1p2 in *.
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
  assert (p1l: p1 ([[l]]) = Some Lock \/ p1 ([[l]]) = None).
  {
  unfold phplusdef in PHPDpp1.
  specialize PHPDpp1 with ([[l]]).
  destruct pl as [pl|pl].
  rewrite pl in PHPDpp1.
  destruct (p1 ([[l]])) eqn:p1l.
  destruct k;
  try contradiction.
  left.
  reflexivity.
  assert (CO:=PH2H).
  apply equal_f with ([[l]]) in CO.
  rewrite EQFOLD in CO.
  rewrite NON in CO.
  unfold phtoh in CO.
  erewrite phplus_locked in CO.
  inversion CO.
  apply phpdef_comm.
  apply phpdef_fold.
  assumption.
  assumption.
  intros.
  apply phpdef_emp.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  erewrite phplus_locked.
  reflexivity.
  assumption.
  apply p1l.
  right.
  reflexivity.
  
  destruct pl as (wt0,(ot0,(ct0,pl))).
  rewrite pl in PHPDpp1.
  destruct (p1 ([[l]])) eqn:p1l.
  destruct k;
  try contradiction.
  left.
  reflexivity.
  right.
  reflexivity.
  }
  assert (p2l: p2 ([[l]]) = Some Lock \/ p2 ([[l]]) = None).
  {
  unfold phplusdef in PHPDpp2.
  specialize PHPDpp2 with ([[l]]).
  destruct pl as [pl|pl].
  rewrite pl in PHPDpp2.
  destruct (p2 ([[l]])) eqn:p2l.
  destruct k;
  try contradiction.
  left.
  reflexivity.
  assert (CO:=PH2H).
  apply equal_f with ([[l]]) in CO.
  rewrite EQFOLD in CO.
  rewrite NON in CO.
  unfold phtoh in CO.
  erewrite phplus_locked in CO.
  inversion CO.
  apply phpdef_comm.
  apply phpdef_fold.
  assumption.
  assumption.
  intros.
  apply phpdef_emp.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  rewrite phplus_comm.
  erewrite phplus_locked.
  reflexivity.
  apply phpdef_comm.
  assumption.
  apply p2l.
  assumption.
  right.
  reflexivity.
  destruct pl as (wt0,(ot0,(ct0,pl))).
  rewrite pl in PHPDpp2.
  destruct (p2 ([[l]])) eqn:p2l.
  destruct k;
  try contradiction.
  left.
  reflexivity.
  right.
  reflexivity.
  }
  assert (p0l: forall p0 (IN: In p0 (map pof T)), p0 ([[l]]) = Some Lock \/ p0 ([[l]]) = None).
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
  destruct pl as [pl|pl].
  assumption.
  destruct pl as (wt0,(ot0,(ct0,pl))).  
  assert (CO: fold_left phplus (map pof T) (phplus p1 p2) ([[l]]) = Some (Locked wt0 ot0 ct0)).
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
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  assumption.
  }
  rewrite LOCKED in CO.
  inversion CO.
  rewrite EQ in *.
  assert (PHPDp0: phplusdef p p0).
  {
  apply PHPDL with id x6.
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
  specialize PHPDp0 with ([[l]]).
  destruct pl as [pl|pl].
  rewrite pl in PHPDp0.
  destruct (p0 ([[l]])) eqn:p0l.
  destruct k;
  try contradiction.
  left.
  reflexivity.
  assert (CO:=PH2H).
  apply equal_f with ([[l]]) in CO.
  rewrite NON in CO.
  unfold phtoh in CO.
  erewrite fold_locked in CO.
  inversion CO.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists p0.
  exists.
  apply in_map_iff.
  exists (x1, x2, p0, x4, x5, x6).
  auto.
  apply p0l.
  right.
  reflexivity.
  destruct pl as (wt0,(ot0,(ct0,pl))).  
  rewrite pl in PHPDp0.
  destruct (p0 ([[l]])) eqn:p0l.
  destruct k;
  try contradiction.
  left.
  reflexivity.
  right.
  reflexivity.
  }
  assert (PHPDUp1: forall wt ot ct, phplusdef (upd p ([[l]]) (Some (Locked wt ot ct))) p1).
  {
  intros.
  apply phpdef_upd_locked.
  assumption.
  assumption.
  }
  assert (PHPDUp2: forall wt ot ct, phplusdef (upd p ([[l]]) (Some (Locked wt ot ct))) p2).
  {
  intros.
  apply phpdef_upd_locked.
  assumption.
  assumption.
  }
  assert (EQP: phplus (upd p ([[l]]) (Some (Locked 
    (filterb L ([[l]]) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv))
    ))) p1 = 
    upd (phplus p p1) ([[l]]) (Some (Locked 
    (filterb L ([[l]]) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv))
    ))).
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
  exists (updl T id (Val 0, tx, phplus (upd p ([[l]]) (Some (Locked 
    (filterb L ([[l]]) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv))
    ))) p1, ([[l]])::O, bagplus C C1, id)).
  exists R, I, L, M, P, X.
  exists p2, (filter (fun x => negb (snd x =? ([[l]]))%Z) Ainv), C2.
  assert (EQWT: forall l0 p O C, filterb L l0 (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) =
    filterb L l0 (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof
    (updl T id (Val 0, tx, p, O, C, id)))))).
  {
  intros.
  apply filterb_updl_eq.
  intros.
  split.
  unfold cmdof.
  simpl.
  apply ifboneq.
  intros.
  assert (X': x' = (Waiting4lock l, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  apply ifboneq.
  }
  assert (EQOT: forall l0 c p C, filterb L l0 (count_occ Z.eq_dec (concat (map oof T))) =
    filterb L l0 (count_occ Z.eq_dec (concat (map oof (updl T id
    (c, tx, p, ([[l]]) :: O, C, id)))))).
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
  unfold oof.
  simpl.
  destruct (Z.eq_dec ([[l]]) v).
  rewrite <- e in IN.
  rewrite lll in IN.
  rewrite <- e in NEQ.
  contradiction.
  reflexivity.
  }
  assert (EQCT: forall l0 c p O, 
    filterb L l0 (fold_left bagplus (map cof T) Cinv) =
    filterb L l0 (fold_left bagplus (map cof (updl T id
    (c, tx, p, O, bagplus C C1, id))) C2)).
  {
  intros.
  rewrite <- C1C2.
  rewrite <- fold_left_move_m_eq2 with (def:=bagdef) (x1:=C) (x2:=C1).
  rewrite fold_left_f with (def:=bagdef).
  reflexivity.
  apply canbag.
  trivial.
  apply canbag.
  assumption.
  unfold defl.
  trivial.
  assumption.
  trivial.
  trivial.
  trivial.
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  reflexivity.
  }
  assert (EQH: forall l0 (NEQ: ([[l]]) <> l0),
    fold_left phplus (map pof T) (phplus p1 p2) l0 =
    fold_left phplus (map pof (updl T id
    (Val 0, tx, phplus (upd p ([[l]]) (Some (Locked (filterb L ([[l]]) (fun v : Z => length
    (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)))))
    p1, ([[l]]) :: O, bagplus C C1, id))) p2 l0).
  {
  symmetry.
  apply eq_heap_Acquire with (z:=[[l]]) (p:=p) (p1:=p1) (h:=h).
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  assumption.
  eexists.
  eexists.
  eexists.
  reflexivity.
  assumption.
  assumption.
  omega.
  }
  assert (phpdefpp1: phplusdef (phplus p1 p2) p).
  {
  apply phpdef_comm.
  apply PHPD.
  assumption.
  }
  assert (LOCKEDU: fold_left phplus (map pof (updl T id
    (Val 0, tx, phplus (upd p ([[l]]) (Some (Locked (filterb L ([[l]]) (fun v : Z => length
    (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)))))
    p1, ([[l]]) :: O, bagplus C C1, id))) p2 ([[l]]) = Some (Locked (filterb L ([[l]]) (fun v : Z => length
    (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)))).
  {
  apply locked_Acquire with p p1 h.
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  reflexivity.
  assumption.
  assumption.
  assumption.
  }
  exists.
  {
  rewrite map_filter with (f3:=fun x => if (x =? ([[l]]))%Z then false else true).
  apply nodup_filter.
  assumption.
  intros.
  reflexivity.
  }
  exists.
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  apply filter_In in IN.
  destruct IN as (EQ1,EQ2).
  unfold negb in EQ2.
  destruct (snd x =? ([[l]]))%Z eqn:xl.
  inversion EQ2.
  apply neqb_neq in xl.
  assert (tmp: fold_left phplus (map pof T) (phplus p1 p2) l0 = Some Lock /\
        h l0 = Some 1%Z).
  {
  apply Ainvl.
  apply in_map_iff.
  exists x.
  auto.
  }
  destruct tmp as (tmp1,tmp2).
  split.
  rewrite <- EQH.
  assumption.
  omega.
  unfold upd.
  destruct (Z.eq_dec l0 ([[l]])).
  omega.
  assumption.
  }
  
  exists.
  {
  apply defl_Acquire with (p:=p) (p1:=p1) (p2:=p2) (h:=h) (z:=([[l]])).
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  assumption.
  assumption.
  assumption.
  unfold pof.
  simpl.
  exists (filterb L ([[l]])(fun v : Z => length (filter (fun c : cmd =>
    ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))(map cmdof T))))
    , (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    , (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)).
  reflexivity.
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
  apply phpdef_comm.
  apply phpdef_pair.
  apply PHPDUp1.
  apply phpdef_comm.
  apply PHPDUp2.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply phpdef_comm.
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
  rewrite EQP.
  apply boundph_upd.
  rewrite phplus_comm.
  apply bph_comm.
  assumption.
  apply boundph_mon with p2.
  apply BPE.
  assumption.
  assumption.
  assumption.
  apply bph_assoc.
  assumption.
  assumption.
  assumption.
  apply bph_comm.
  assumption.
  {
  apply boundph_fold with (m:=pof) (l:=T).
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption. 
  }
  tauto.
  intros.
  destruct H as (z',CO).
  inversion CO.
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  exists.
  {
  assumption.
  }
  exists.
  {
  apply boundph_Acquire with (p:=p) (p1:=p1) (z:=([[l]])) (h:=h).
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Waiting4lock l, tx, p, O, C, id).
  auto.
  eexists.
  eexists.
  eexists.
  reflexivity.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  exists.
  assumption.
  exists.
  {
  apply functional_extensionality.
  intros.
  unfold upd at 1.
  destruct (Z.eq_dec x ([[l]])).
  rewrite e.
  unfold phtoh.
  rewrite LOCKEDU.
  reflexivity.
  unfold phtoh.
  rewrite <- EQH.
  rewrite PH2H.
  reflexivity.
  omega.
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
  intros.
  assert (tmp: L l0 = l0 /\ P l0 = false /\
    ~ In (R l0) (X (L l0)) /\
    (h l0 <> Some 1%Z -> In l0 (concat (map oof T)))).
  {
  apply VLOCK.
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite e.
  left.
  assumption.
  rewrite EQH.
  assumption.
  omega.
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
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists (Val 0, tx, phplus (upd p ([[l]]) (Some (Locked (filterb L ([[l]]) (fun v => length (filter
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv))))) p1, ([[l]]) :: O, bagplus C C1,id).
  split.
  apply in_updl_eq.
  exists (Waiting4lock l, tx, p, O, C).
  auto.
  unfold oof.
  simpl.
  left.
  omega.
  apply inl0 in H.
  rewrite <- flat_map_concat_map in H.
  apply in_flat_map in H.
  destruct H as (x,(INx,INl0)).
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
  exists (Val 0, tx, phplus (upd p ([[l]]) (Some (Locked (filterb L ([[l]]) (fun v => length (filter
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv))))) p1, ([[l]]) :: O, bagplus C C1,id).
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
  exists.
  {
  intros.
  unfold upd.
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite e in ULOCK.
  rewrite LOCKEDU in ULOCK.
  inversion ULOCK.
  eapply VULOCK.
  rewrite <- EQH in ULOCK.
  apply ULOCK.
  omega.
  }
  exists.
  {
  intros.
  rewrite <- EQWT.
  rewrite <- EQOT.
  rewrite <- EQCT.
  destruct (Z.eq_dec ([[l]]) l0) as [ll0|ll0].
  rewrite <- ll0 in ULOCKED.
  assert (wot: wt = filterb L ([[l]]) (fun v : Z => length (filter
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) /\
    ot = filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))) /\
    ct = filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)).
  {
  rewrite LOCKEDU in ULOCKED.
  destruct ULOCKED as [U1|U2].
  inversion U1.
  auto.
  inversion U2.
  }
  rewrite <- ll0.
  auto.
  apply WOT.
  {
  rewrite <- EQH in ULOCKED.
  assumption.
  assumption.
  }
  }
  exists.
  {
  intros.
  rewrite <- EQWT.
  rewrite <- EQOT.
  rewrite <- EQCT.
  unfold upd in NOTHELD.
  destruct (Z.eq_dec l0 ([[l]])).
  inversion NOTHELD.
  apply filter_In.
  split.
  apply LINV.
  rewrite <- EQH in LOCK.
  assumption.
  omega.
  assumption.
  unfold negb.
  simpl.
  destruct (l0 =? ([[l]]))%Z eqn:l0l.
  apply Z.eqb_eq in l0l.
  contradiction.
  reflexivity.
  }
  exists.
  {
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
  {
admit.
  }
  exists.
  {
  intros.
  inversion W4COND.
  }
  trivial.
(* ==================== x6 <> id ===========*)
  symmetry in EQ.
  inversion EQ.
  assert (tmp:=IN).
  apply VALIDT in tmp.
  destruct tmp as (WF1,(WP1,(VOBS1,TR11))).
  exists.
  assumption.
  exists.
  assumption.
  exists.
  {
  intros.
  assert (NEQlv: ([[l]]) <>([[v]])).
  {
  unfold not.
  intros.
  rewrite W4COND in WP1.
  apply sat_wait4cond in WP1.
  destruct WP1 as (pv0',(pl0',(lvl0',(prcl0',(prcv0',(Cm0',(Cmeq0',SAT0'))))))).
  assert (CO: fold_left phplus (map pof T) (phplus p1 p2) ([[l]]) = Some Cond).
  {
  rewrite H.
  apply fold_cond.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists x3.
  split.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }
  rewrite LOCKED in CO.
  inversion CO.
  }
  assert (EQCNT: forall c tx p C, (count_occ Z.eq_dec (concat (map oof (updl T id (c, tx, p, ([[l]]) :: O, C, id)))) ([[v]]))
    = count_occ Z.eq_dec (concat (map oof T)) ([[v]])).
  {
  intros.
  symmetry.
  apply count_updl_eq.
  intros.
  assert (X': x' = (Waiting4lock l, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold oof.
  simpl.
  destruct (Z.eq_dec ([[l]]) ([[v]])).
  omega.
  reflexivity.
  }
  assert (EQFIL: forall p O C, length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some ([[v]])))) (map cmdof T)) =
    length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for (upd h ([[l]]) (Some 0%Z)) c0)
    (Some ([[v]])))) (map cmdof (updl T id (Val 0, tx, p, O, C, id))))).
  {
  intros.
  rewrite filter_filter_eq with (f2:=(fun c0 : cmd =>
      ifb
        (opZ_eq_dec (waiting_for (upd h ([[l]]) (Some 0%Z)) c0)
           (Some ([[v]]))))).
  unfold updl.
  rewrite map_map.
  apply filter_map_eq.
  intros.
  destruct x as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  rewrite e in *.
  assert (EQX: (a1, a2, a3, a4, a5) = (Waiting4lock l, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN0.
  assumption.
  assumption.
  inversion EQX.
  unfold cmdof.
  simpl.
  unfold upd.
  rewrite eqz.
  destruct (opZ_eq_dec (Some 0%Z) (Some 1%Z)).
  inversion e0. 
  destruct (opZ_eq_dec (Some ([[l]])) (Some ([[v]]))).
  inversion e0.
  contradiction.
  symmetry.
  apply ifboneq.
  reflexivity.
  intros.
  apply waiting_for_upd_eq.
  assumption.
  }
  rewrite <- EQFIL.
  rewrite EQCNT.
  apply VOBS1 with l0.
  assumption.
  }
  trivial.
  }
  trivial.
Admitted.

Lemma Acquire0_preserves_validity:
  forall h t id l tx
         (VALIDK: validk t h)
         (CMD : t id = Some (Acquire l, tx))
         (NON: h ([[l]]) <> Some 1%Z),
    validk (upd t id (Some (Waiting4lock l, tx))) h.
Proof.
  intros.
  unfold validk in VALIDK.
  destruct VALIDK as (T,(R,(I,(L,(M,(P,(X,(Pinv,(Ainv,(Cinv,(NODUPA,(Ainvl,(PHPDL,(PHPD,(BPE,(BPA,(BPT,(SATA,(PH2H,(AUT,(UNQ,(VLOCK,(VULOCK,(WOT,(LINV,(VALIDT,TR)))))))))))))))))))))))))).
  unfold validk.
  assert (tmp: exists p O C, In (Acquire l, tx, p, O, C, id) T).
  apply AUT.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply VALIDT in tmp.
  destruct tmp as (WF,(WP,(VOBS,Tr))).
  assert (tmp:=WP).
  apply sat_acquire0 in tmp.
  destruct tmp as (pl,(prcl,SAT1)).
  exists (updl T id (Waiting4lock l, tx, p, O, C, id)).
  exists R, I, L, M, P, X, Pinv, Ainv, Cinv.
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
  assert (EQ_2: map (fun x => (pof x, idof x)) (updl T id (Waiting4lock l, tx, p, O, C, id)) = map (fun x => (pof x, idof x)) T).
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
  assert (EQ_4: map cof (updl T id (Waiting4lock l, tx, p, O, C, id)) = map cof T).
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
  assert (EQF: forall l0, filterb L l0 (fun v => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
  (map cmdof (updl T id (Waiting4lock l, tx, p, O, C, id))))) =
  filterb L l0 (fun v => length (filter (fun c : cmd => 
  ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))).
  {
  symmetry.
  apply filterb_updl_eq.
  intros.
  split.
  apply ifboneq.
  intros.
  assert (X': x' = (Acquire l, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  apply ifboneq.
  }
  rewrite EQ_1.
  rewrite EQ_2.
  rewrite EQ_3.
  rewrite EQ_4.
  exists NODUPA, Ainvl, PHPDL,PHPD, BPE, BPA, BPT, SATA, PH2H.
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
  assumption.
  exists.
  assumption.
  exists.
  {
  intros.
  rewrite EQF.
  apply WOT.
  assumption.
  }
  exists.
  {
  intros.
  rewrite EQF.
  apply LINV.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x00,(EQ,IN)).
  destruct x00 as (((((y1,y2),y3),y4),y5),y6).
  unfold pof in EQ. unfold oof in EQ. unfold cof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec y6 id).
(* ==================== y6 = id ===========*)
  rewrite e in IN.
  symmetry in EQ.
  inversion EQ.
  exists.
  assumption.
  exists.
  apply SAT1.
  exists.
  intros.
  inversion W4COND.
  trivial.
(* ==================== z <> id ===========*)
  symmetry in EQ.
  inversion EQ.
  assert (tmp:=IN).
  apply VALIDT in tmp.
  destruct tmp as (WF1,(WP1,(VOBS1,TR11))).
  exists.
  assumption.
  exists.
  assumption.
  exists.
  {
  assert (tmp: L ([[l]]) = ([[l]]) /\
        P ([[l]]) = false /\
        ~ In (R ([[l]])) (X (L ([[l]]))) /\
        (h ([[l]]) <> Some 1%Z -> In ([[l]]) (concat (map oof T)))).
  {
  apply VLOCK.
  apply fold_lock_ed.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  apply pl.
  }
  destruct tmp as (lll,(plf,(ninrlxll,inlt))).
  intros.
  apply VOBS1 in W4COND.
  destruct (Z.eq_dec ([[v]]) ([[l]])).
  rewrite e.
  unfold safe_obs.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  unfold one_ob.
  apply Coq.Bool.Bool.orb_true_iff.
  right.
  apply Nat.ltb_lt.
  apply inlt in NON.
  apply count_occ_In.
  assumption.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  apply Coq.Bool.Bool.orb_true_iff.
  left.
  unfold negb.
  rewrite plf.
  reflexivity.
  apply Coq.Bool.Bool.orb_true_iff.
  left.
  unfold ifb.
  simpl.
  destruct (in_dec Z.eq_dec (R ([[l]])) (X (L ([[l]])))).
  contradiction.
  reflexivity.
  unfold updl.
  rewrite map_map.
  rewrite filter_map_eq with (m2:=cmdof).
  assumption.
  intros.
  destruct x as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  rewrite e in *.
  assert (EQA: (a1,a2,a3,a4,a5) = (Acquire l, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN0.
  assumption.
  assumption.
  inversion EQA.
  simpl.
  destruct (opZ_eq_dec (h ([[l]])) (Some 1%Z)).
  contradiction.
  destruct (opZ_eq_dec (Some ([[l]])) (Some ([[v]]))).
  inversion e0.
  omega.
  symmetry.
  apply ifboneq.
  reflexivity.
  }
  trivial.
  }
  trivial.
Qed.
Lemma Acquire_preserves_validity:
  forall h t id l tx
         (VALIDK: validk t h)
         (CMD : t id = Some (Acquire l, tx))
         (NON: h ([[l]]) = Some 1%Z),
    validk (upd t id (Some (Val 0, tx))) (upd h ([[l]]) (Some 0%Z)).
Proof.
  intros.
  unfold validk in VALIDK.
  destruct VALIDK as (T,(R,(I,(L,(M,(P,(X,(Pinv,(Ainv,(Cinv,(NODUPA,(Ainvl,(PHPDL,(PHPD,(BPE,(BPA,(BPT,(SATA,(PH2H,(AUT,(UNQ,(VLOCK,(VULOCK,(WOT,(LINV,(VALIDT,TR)))))))))))))))))))))))))).
  unfold validk.
  assert (tmp: exists p O C, In (Acquire l, tx, p, O, C, id) T).
  apply AUT.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply VALIDT in tmp.
  destruct tmp as (WF,(WP,(VOBS,TR1))).
  unfold wellformed in WF.
  simpl in WF.
  apply sat_acquire in WP.
  destruct WP as (pl,(prcl,SAT1)).
  assert (EQFOLD: fold_left phplus (map pof T) Pinv = phplus Pinv (fold_left phplus (map pof T) (emp knowledge))).
  {
  replace Pinv with (phplus Pinv (emp knowledge)) at 1.
  apply fold_left_f_m_def with (def:=phplusdef).
  apply can_phpdef.
  assumption.
  assumption.
  apply phpdef_emp.
  intros.
  split.
  apply PHPD.
  assumption.
  apply phpdef_emp.
  apply phplus_emp.
  }
  assert (INpT: In p (map pof T)).
  {
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  }
  assert (LOCKED: fold_left phplus (map pof T) Pinv ([[l]]) = Some Lock).
  {
  assert (tmp: fold_left phplus (map pof T) Pinv ([[l]]) = Some Lock \/
       (exists wt ot ct : bag,
          fold_left phplus (map pof T) Pinv ([[l]]) =
          Some (Locked wt ot ct))).
  {
  apply fold_lock_ed.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  right.
  exists p, INpT.
  left.
  assumption.
  }
  destruct tmp as [LK|LKED].
  assumption.
  destruct LKED as (wt,(ot,(ct,LKED))).
  assert (CO:=PH2H).
  apply equal_f with ([[l]]) in CO.
  unfold phtoh in CO.
  rewrite LKED in CO.
  rewrite NON in CO.
  inversion CO.
  }
  assert (tmp: L ([[l]]) = ([[l]]) /\ P ([[l]]) = false /\
           ~ In (R ([[l]])) (X (L ([[l]]))) /\
          (h ([[l]]) <> Some 1%Z -> In ([[l]]) (concat (map oof T)))).
  {
  apply VLOCK.
  left.
  assumption.
  }
  destruct tmp as (lll,(plf,(ninrlxll,inlt))).
  rewrite lll in *.
  assert (PERM: Permutation Ainv (
    (I ([[l]]) (filterb L ([[l]]) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)), ([[l]]))
     :: filter (fun x => negb (Z.eqb (snd x) ([[l]]))) Ainv)).
  {
  apply perm_filter.
  assumption.
  apply LINV.
  assumption.
  assumption.
  unfold negb.
  simpl.
  rewrite zeqb.
  reflexivity.
  intros.
  unfold negb.
  simpl.
  destruct (z' =? ([[l]]))%Z eqn:z'l.
  apply Z.eqb_eq in z'l.
  contradiction.
  reflexivity.
  }
  assert (SATA2: lsat Pinv Cinv (fold_left Lastar (map fst 
    ((I ([[l]]) (filterb L ([[l]]) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)), ([[l]]))
    :: filter (fun x => negb (Z.eqb (snd x) ([[l]]))) Ainv)
    ) (Labool true))).
  {
  apply lsat_perm with (map fst Ainv).
  apply Permutation_map.
  assumption.
  assumption.
  assumption.
  }
  simpl in SATA2.
  assert (SATA3: lsat Pinv Cinv 
    (Lastar (I ([[l]]) (filterb L ([[l]]) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)))
    (fold_left Lastar (map fst 
    (filter (fun x => negb (Z.eqb (snd x) ([[l]]))) Ainv))
    (Labool true)))).
  {
  apply fold_left_g_can2.
  unfold cang.
  split.
  intros.
  apply lsat_comm.
  assumption.
  simpl.
  intros.
  apply lsat_perm with (l:=l0).
  assumption.
  assumption.
  assumption.
  assumption.
  }
  simpl in SATA3.
  destruct SATA3 as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(C1,(C2,(SATp1,(SATp2,(p1p2,C1C2))))))))))).
  rewrite <- p1p2 in *.
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
  assert (p1l: p1 ([[l]]) = Some Lock \/ p1 ([[l]]) = None).
  {
  unfold phplusdef in PHPDpp1.
  specialize PHPDpp1 with ([[l]]).
  rewrite pl in PHPDpp1.
  destruct (p1 ([[l]])) eqn:p1l.
  destruct k;
  try contradiction.
  left.
  reflexivity.
  assert (CO:=PH2H).
  apply equal_f with ([[l]]) in CO.
  rewrite EQFOLD in CO.
  rewrite NON in CO.
  unfold phtoh in CO.
  erewrite phplus_locked in CO.
  inversion CO.
  apply phpdef_comm.
  apply phpdef_fold.
  assumption.
  assumption.
  intros.
  apply phpdef_emp.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  erewrite phplus_locked.
  reflexivity.
  assumption.
  apply p1l.
  right.
  reflexivity.
  }
  assert (p2l: p2 ([[l]]) = Some Lock \/ p2 ([[l]]) = None).
  {
  unfold phplusdef in PHPDpp2.
  specialize PHPDpp2 with ([[l]]).
  rewrite pl in PHPDpp2.
  destruct (p2 ([[l]])) eqn:p2l.
  destruct k;
  try contradiction.
  left.
  reflexivity.
  assert (CO:=PH2H).
  apply equal_f with ([[l]]) in CO.
  rewrite EQFOLD in CO.
  rewrite NON in CO.
  unfold phtoh in CO.
  erewrite phplus_locked in CO.
  inversion CO.
  apply phpdef_comm.
  apply phpdef_fold.
  assumption.
  assumption.
  intros.
  apply phpdef_emp.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  rewrite phplus_comm.
  erewrite phplus_locked.
  reflexivity.
  apply phpdef_comm.
  assumption.
  apply p2l.
  assumption.
  right.
  reflexivity.
  }
  assert (p0l: forall p0 (IN: In p0 (map pof T)), p0 ([[l]]) = Some Lock \/ p0 ([[l]]) = None).
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
  apply PHPDL with id x6.
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
  specialize PHPDp0 with ([[l]]).
  rewrite pl in PHPDp0.
  destruct (p0 ([[l]])) eqn:p0l.
  destruct k;
  try contradiction.
  left.
  reflexivity.
  assert (CO:=PH2H).
  apply equal_f with ([[l]]) in CO.
  rewrite NON in CO.
  unfold phtoh in CO.
  erewrite fold_locked in CO.
  inversion CO.
  apply pofs.
  assumption.
  assumption.
  assumption.
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
  assert (PHPDUp1: forall wt ot ct, phplusdef (upd p ([[l]]) (Some (Locked wt ot ct))) p1).
  {
  intros.
  apply phpdef_upd_locked.
  assumption.
  assumption.
  }
  assert (PHPDUp2: forall wt ot ct, phplusdef (upd p ([[l]]) (Some (Locked wt ot ct))) p2).
  {
  intros.
  apply phpdef_upd_locked.
  assumption.
  assumption.
  }
  assert (EQP: phplus (upd p ([[l]]) (Some (Locked 
    (filterb L ([[l]]) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv))
    ))) p1 = 
    upd (phplus p p1) ([[l]]) (Some (Locked 
    (filterb L ([[l]]) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv))
    ))).
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
  exists (updl T id (Val 0, tx, phplus (upd p ([[l]]) (Some (Locked 
    (filterb L ([[l]]) (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv))
    ))) p1, ([[l]])::O, bagplus C C1, id)).
  exists R, I, L, M, P, X.
  exists p2, (filter (fun x => negb (snd x =? ([[l]]))%Z) Ainv), C2.
  assert (EQWT: forall l0 p O C, filterb L l0 (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) =
    filterb L l0 (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof
    (updl T id (Val 0, tx, p, O, C, id)))))).
  {
  intros.
  apply filterb_updl_eq.
  intros.
  split.
  unfold cmdof.
  simpl.
  apply ifboneq.
  intros.
  assert (X': x' = (Acquire l, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold cmdof.
  simpl.
  apply ifboneq.
  }
  assert (EQOT: forall l0 c p C, filterb L l0 (count_occ Z.eq_dec (concat (map oof T))) =
    filterb L l0 (count_occ Z.eq_dec (concat (map oof (updl T id
    (c, tx, p, ([[l]]) :: O, C, id)))))).
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
  unfold oof.
  simpl.
  destruct (Z.eq_dec ([[l]]) v).
  rewrite <- e in IN.
  rewrite lll in IN.
  rewrite <- e in NEQ.
  contradiction.
  reflexivity.
  }
  assert (EQCT: forall l0 c p O, 
    filterb L l0 (fold_left bagplus (map cof T) Cinv) =
    filterb L l0 (fold_left bagplus (map cof (updl T id
    (c, tx, p, O, bagplus C C1, id))) C2)).
  {
  intros.
  rewrite <- C1C2.
  rewrite <- fold_left_move_m_eq2 with (def:=bagdef) (x1:=C) (x2:=C1).
  rewrite fold_left_f with (def:=bagdef).
  reflexivity.
  apply canbag.
  trivial.
  apply canbag.
  assumption.
  unfold defl.
  trivial.
  assumption.
  trivial.
  trivial.
  trivial.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  reflexivity.
  }
  assert (EQH: forall l0 (NEQ: ([[l]]) <> l0),
    fold_left phplus (map pof T) (phplus p1 p2) l0 =
    fold_left phplus (map pof (updl T id
    (Val 0, tx, phplus (upd p ([[l]]) (Some (Locked (filterb L ([[l]]) (fun v : Z => length
    (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)))))
    p1, ([[l]]) :: O, bagplus C C1, id))) p2 l0).
  {
  symmetry.
  apply eq_heap_Acquire with (z:=[[l]]) (p:=p) (p1:=p1) (h:=h).
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  eexists.
  eexists.
  eexists.
  reflexivity.
  assumption.
  assumption.
  omega.
  }
  assert (LOCKEDU: fold_left phplus (map pof (updl T id
    (Val 0, tx, phplus (upd p ([[l]]) (Some (Locked (filterb L ([[l]]) (fun v : Z => length
    (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)))))
    p1, ([[l]]) :: O, bagplus C C1, id))) p2 ([[l]]) = Some (Locked (filterb L ([[l]]) (fun v : Z => length
    (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)))).
  {
  apply locked_Acquire with p p1 h.
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  reflexivity.
  left.
  assumption.
  assumption.
  assumption.
  }
  exists.
  {
  rewrite map_filter with (f3:=fun x => if (x =? ([[l]]))%Z then false else true).
  apply nodup_filter.
  assumption.
  intros.
  reflexivity.
  }
  exists.
  {
  intros.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  apply filter_In in IN.
  destruct IN as (EQ1,EQ2).
  unfold negb in EQ2.
  destruct (snd x =? ([[l]]))%Z eqn:xl.
  inversion EQ2.
  apply neqb_neq in xl.
  assert (tmp: fold_left phplus (map pof T) (phplus p1 p2) l0 = Some Lock /\
        h l0 = Some 1%Z).
  {
  apply Ainvl.
  apply in_map_iff.
  exists x.
  auto.
  }
  destruct tmp as (tmp1,tmp2).
  split.
  {
  rewrite <- EQH.
  assumption.
  omega.
  }
  {
  unfold upd.
  destruct (Z.eq_dec l0 ([[l]])).
  omega.
  assumption.
  }
  }
  exists.
  {
  apply defl_Acquire with (p:=p) (p1:=p1) (p2:=p2) (z:=([[l]])) (h:=h).
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  assumption.
  assumption.
  eexists.
  eexists.
  eexists.
  reflexivity.
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
  apply phpdef_comm.
  apply phpdef_pair.
  apply PHPDUp1.
  apply phpdef_comm.
  apply PHPDUp2.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply phpdef_comm.
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
  rewrite EQP.
  apply boundph_upd.
  rewrite phplus_comm.
  rewrite phplus_comm.
  apply boundph_mon with p2.
  apply BPE.
  assumption.
  assumption.
  assumption.
  apply bph_assoc.
  assumption.
  assumption.
  assumption.
  apply bph_comm.
  apply phpdef_pair'.
  assumption.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  assumption.
  apply boundph_fold with (m:=pof) (l:=T).
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  apply phpdef_comm.
  assumption.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  apply BPE.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  }
  exists.
  {
  assumption.
  }
  exists.
  {
  apply boundph_Acquire with (p:=p) (p1:=p1) (z:=([[l]])) (h:=h).
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  eexists.
  eexists.
  eexists.
  reflexivity.
  left.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  exists.
  assumption.
  exists.
  {
  apply functional_extensionality.
  intros.
  unfold upd at 1.
  destruct (Z.eq_dec x ([[l]])).
  rewrite e.
  unfold phtoh.
  erewrite locked_Acquire with (p:=p) (p1:=p1) (z:=([[l]])) (h:=h).
  reflexivity.
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  reflexivity.
  unfold phtoh.
  left.
  assumption.
  assumption.
  assumption.
  unfold phtoh.
  rewrite eq_heap_Acquire with (h:=h) (p:=p) (p1:=p1) (z:=([[l]])).
  rewrite PH2H.
  reflexivity.
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Acquire l, tx, p, O, C, id).
  auto.
  left.
  assumption.
  eexists.
  eexists.
  eexists.
  reflexivity.
  assumption.
  assumption.
  omega.
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
  intros.
  assert (tmp: L l0 = l0 /\ P l0 = false /\
    ~ In (R l0) (X (L l0)) /\
    (h l0 <> Some 1%Z -> In l0 (concat (map oof T)))).
  {
  apply VLOCK.
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite e.
  left.
  assumption.
  rewrite EQH.
  assumption.
  omega.
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
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists (Val 0, tx, phplus (upd p ([[l]]) (Some (Locked (filterb L ([[l]]) (fun v => length (filter
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv))))) p1, ([[l]]) :: O, bagplus C C1,id).
  split.
  apply in_updl_eq.
  exists (Acquire l, tx, p, O, C).
  auto.
  unfold oof.
  simpl.
  left.
  omega.
  apply inl0 in H.
  rewrite <- flat_map_concat_map in H.
  apply in_flat_map in H.
  destruct H as (x,(INx,INl0)).
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
  exists (Val 0, tx, phplus (upd p ([[l]]) (Some (Locked (filterb L ([[l]]) (fun v => length (filter
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv))))) p1, ([[l]]) :: O, bagplus C C1,id).
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
  exists.
  {
  intros.
  unfold upd.
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite e in ULOCK.
  rewrite LOCKEDU in ULOCK.
  inversion ULOCK.
  apply VULOCK with wt ot ct.
  rewrite <- EQH in ULOCK.
  assumption.
  omega.
  }
  exists.
  {
  intros.
  rewrite <- EQWT.
  rewrite <- EQOT.
  rewrite <- EQCT.
  destruct (Z.eq_dec ([[l]]) l0) as [ll0|ll0].
  rewrite <- ll0 in ULOCKED.
  assert (wot: wt = filterb L ([[l]]) (fun v : Z => length (filter
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) /\
    ot = filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))) /\
    ct = filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)).
  {
  rewrite LOCKEDU in ULOCKED.
  destruct ULOCKED as [U1|U2].
  inversion U1.
  auto.
  inversion U2.
  }
  rewrite <- ll0.
  auto.
  apply WOT.
  {
  rewrite <- EQH in ULOCKED.
  assumption.
  assumption.
  }
  }
  exists.
  {
  intros.
  rewrite <- EQWT.
  rewrite <- EQOT.
  rewrite <- EQCT.
  unfold upd in NOTHELD.
  destruct (Z.eq_dec l0 ([[l]])).
  inversion NOTHELD.
  apply filter_In.
  split.
  apply LINV.
  rewrite <- EQH in LOCK.
  assumption.
  omega.
  assumption.
  unfold negb.
  simpl.
  destruct (l0 =? ([[l]]))%Z eqn:l0l.
  apply Z.eqb_eq in l0l.
  contradiction.
  reflexivity.
  }
  exists.
  {
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
  {
  apply SAT1.
  assumption.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  inversion W4COND.
  }
  trivial.
(* ==================== x6 <> id ===========*)
  symmetry in EQ.
  inversion EQ.
  assert (tmp:=IN).
  apply VALIDT in tmp.
  destruct tmp as (WF1,(WP1,(VOBS1,TR11))).
  exists.
  assumption.
  exists.
  assumption.
  exists.
  {
  intros.
  assert (NEQlv: ([[l]]) <>([[v]])).
  {
  unfold not.
  intros.
  rewrite W4COND in WP1.
  apply sat_wait4cond in WP1.
  destruct WP1 as (pv0',(pl0',(lvl0',(prcl0',(prcv0',(Cm0',(Cmeq0',SAT0'))))))).
  assert (CO: fold_left phplus (map pof T) (phplus p1 p2) ([[l]]) = Some Cond).
  {
  rewrite H.
  apply fold_cond.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists x3.
  split.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  assumption.
  }
  rewrite LOCKED in CO.
  inversion CO.
  }
  assert (EQCNT: forall c tx p C, (count_occ Z.eq_dec (concat (map oof (updl T id (c, tx, p, ([[l]]) :: O, C, id)))) ([[v]]))
    = count_occ Z.eq_dec (concat (map oof T)) ([[v]])).
  {
  intros.
  symmetry.
  apply count_updl_eq.
  intros.
  assert (X': x' = (Acquire l, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  rewrite X'.
  unfold oof.
  simpl.
  destruct (Z.eq_dec ([[l]]) ([[v]])).
  omega.
  reflexivity.
  }
  assert (EQFIL: forall p O C ,length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some ([[v]])))) (map cmdof T)) =
    length (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for (upd h ([[l]]) (Some 0%Z)) c0)
    (Some ([[v]])))) (map cmdof (updl T id
    (Val 0, tx, p, O, C, id))))).
  {
  intros.
  rewrite filter_filter_eq with (f2:=(fun c0 : cmd =>
      ifb
        (opZ_eq_dec (waiting_for (upd h ([[l]]) (Some 0%Z)) c0)
           (Some ([[v]]))))).
  unfold updl.
  rewrite map_map.
  apply filter_map_eq.
  intros.
  destruct x as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  rewrite e in *.
  assert (EQX: (a1, a2, a3, a4, a5) = (Acquire l, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN0.
  assumption.
  assumption.
  inversion EQX.
  unfold cmdof.
  simpl.
  reflexivity.
  reflexivity.
  intros.
  apply waiting_for_upd_eq.
  assumption.
  }
  rewrite <- EQFIL.
  rewrite EQCNT.
  apply VOBS1 with l0.
  assumption.
  }
  trivial.
  }
  trivial.
Qed.
Definition wkupmap z (athread:(cmd * context * pheap * list Z * bag * Z)) : (cmd * context * pheap * list Z * bag * Z) :=
  (wakeupcmd z (fst (fst (fst (fst (fst athread))))), snd (fst (fst (fst (fst athread)))), snd (fst (fst (fst athread))),
    snd (fst (fst athread)), snd (fst athread), snd athread).
Lemma NotifyAll_preserves_validity:
  forall h t id v tx
         (VALID: validk t h)
         (CMD : t id = Some (NotifyAll v, tx)),
    validk (upd (wakeupthrds ([[v]]) t) id (Some (Val 0, tx))) h.
Proof.
  intros.
  unfold validk in VALID.
  destruct VALID as (T,(R,(I,(L,(M,(P,(X,(Pinv,(Ainv,(Cinv,(NODUPA,(Ainvl,(PHPDL,(PHPD,(BPE,(BPA,(BPT,(SATA,(PH2H,(AUT,(UNQ,(VLOCK,(VULOCK,(WOT,(LINV,(VALIDT,TR)))))))))))))))))))))))))).
  unfold validk.
  assert (tmp: exists p O C, In (NotifyAll v, tx, p, O, C, id) T).
  {
  apply AUT.
  assumption.
  }
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply VALIDT in tmp.
  destruct tmp as (WF,(WP,(VOBS,TR1))).
  unfold wellformed in WF.
  simpl in WF.
  apply sat_notifyall in WP.
  destruct WP as (wt,(ot,(ct,(plv,(pv,(Mv,SAT1)))))).
  exists (updl (map (wkupmap ([[v]])) T) id (Val 0, tx, upd p (L ([[v]])) (Some (Locked (upd wt ([[v]]) 0%nat) ot ct)), O, C, id)).
  exists R, I, L, M, P, X, Pinv, Ainv, Cinv.
  assert (LOCKED: fold_left phplus (map pof T) Pinv (L ([[v]])) = Some (Locked wt ot ct)).
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
  exists (NotifyAll v, tx, p, O, C, id).
  auto.
  assumption.
  }
  assert (neqvl: ([[v]]) <> (L ([[v]]))).
  {
  unfold not.
  intros.
  rewrite <- H in plv.
  rewrite plv in pv.
  inversion pv.
  }
  assert (EQ_2: fold_left phplus (map pof (updl (map (wkupmap ([[v]])) T) id (Val 0, tx, upd p (L ([[v]])) (Some (Locked (upd wt ([[v]]) 0%nat) ot ct)), O, C, id))) Pinv = 
    upd (fold_left phplus (map pof T) Pinv) (L ([[v]])) (Some (Locked (upd wt ([[v]]) 0%nat) ot ct))).
  {
  apply fold_left_upd_NotifyAll with p.
  apply pofs.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (NotifyAll v, tx, p, O, C, id).
  auto.
  exists wt, ot, ct.
  assumption.
  reflexivity.
  intros.
  unfold wkupmap.
  unfold pof.
  simpl.
  tauto.
  }
  assert (EQ_3: map oof (updl (map (wkupmap ([[v]])) T) id (Val 0, tx, upd p (L ([[v]])) (Some (Locked (upd wt ([[v]]) 0%nat) ot ct)), O, C, id)) = map oof T).
  {
  unfold updl.
  rewrite map_map.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  unfold idof.
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
  assert (EQ_4: map cof (updl (map (wkupmap ([[v]])) T) id (Val 0, tx, upd p (L ([[v]])) (Some (Locked (upd wt ([[v]]) 0%nat) ot ct)), O, C, id)) =
                map cof T).
  {
  unfold updl.
  rewrite map_map.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  unfold idof.
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
  assert (FIL: forall l (NEQ:l <> L ([[v]])), filterb L l
    (fun v0 : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0)))
    (map cmdof T))) = filterb L l (fun v0 : Z => length
    (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0)))
    (map cmdof (updl (map (wkupmap ([[v]])) T) id (Val 0, tx,
    fun a : Z => if Z.eq_dec a (L ([[v]])) then Some (Locked
    (fun a0 : Z => if Z.eq_dec a0 ([[v]]) then 0 else wt a0) ot ct) else p a, O, C, id)))))).
  intros.
  rewrite <- filterb_updl_eq.
  {
  rewrite map_map.
  unfold filterb.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x l).
  reflexivity.
  destruct (Z.eq_dec (L x) l).
  Focus 2.
  reflexivity.
  apply filter_map_eq.
  intros.
  destruct x0 as (((((x1,x2),x3),x4),x5),x6).
  unfold cmdof.
  simpl.
  destruct x1;
  simpl;
  try reflexivity.
  destruct ((opZ_eq_dec (Some ([[v0]])) (Some x))).
  inversion e0.
  rewrite <- H0 in e.
  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  rewrite e1 in e.
  omega.
  simpl.
  rewrite H0.
  destruct (opZ_eq_dec (Some x) (Some x)).
  reflexivity.
  contradiction.
  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  simpl.
  symmetry.
  apply ifboneq.
  simpl.
  destruct (opZ_eq_dec (Some ([[v0]])) (Some x)).
  contradiction.
  reflexivity.
  }
  {
  intros.
  split.
  unfold cmdof.
  simpl.
  apply ifboneq.
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
  apply ifboneq.
  }
  rewrite EQ_2.
  rewrite EQ_3.
  rewrite EQ_4.
  exists NODUPA.
  exists.
  {
  intros.
  apply Ainvl in IN.
  destruct IN as (CO,hl1).
  unfold upd.
  destruct (Z.eq_dec l (L ([[v]]))).
  rewrite e in CO.
  rewrite LOCKED in CO.
  inversion CO.
  auto.
  }
  exists.
  {
  apply defl_NotifyAll with (z:=(L ([[v]]))) (p:=p) (wt:=(upd wt ([[v]]) 0)) (ot:=ot) (ct:=ct).
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (NotifyAll v, tx, p, O, C, id).
  auto.
  exists wt, ot, ct.
  assumption.
  reflexivity.
  reflexivity.
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
  apply phpdef_locked.
  apply PHPD.
  apply in_map_iff.
  exists (NotifyAll v, tx, p, O, C, id).
  auto.
  exists wt, ot, ct.
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
  apply boundph_upd.
  apply BPE.
  apply in_map_iff.
  exists (NotifyAll v, tx, p, O, C, id).
  auto.
  intros.
  destruct H as (z',CO).
  inversion CO.
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
  exists.
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }
  exists.
  assumption.
  exists.
  {
  rewrite phtoh_upd_locked.
  assumption.
  exists wt, ot, ct.
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
  apply AUT in tid1.
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
  apply AUT.
  exists x3, x4, x5.
  assumption.
  rewrite tid1.
  rewrite H1.
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
  unfold upd.
  intros.
  apply VLOCK.
  destruct (Z.eq_dec l (L ([[v]]))).
  rewrite e.
  right.
  exists wt, ot, ct.
  assumption.
  assumption.
  }
  exists.
  {
  unfold upd.
  intros.
  destruct (Z.eq_dec l (L ([[v]]))).
  inversion ULOCK.
  apply VULOCK with wt0 ot0 ct0.
  assumption.
  }
  exists.
  {
  unfold upd.
  intros.
  destruct (Z.eq_dec l (L ([[v]]))).
  {
  rewrite e.
  assert (tmp: wt0 = upd wt ([[v]]) 0 /\
               ot0 = ot /\
               ct0 = ct).
  split.
  destruct ULOCKED as [U|U].
  inversion U.
  reflexivity.
  inversion U.
  destruct ULOCKED as [U|U].
  inversion U.
  auto.
  inversion U.
  auto.
  destruct tmp as(eqwt,(eqot,eqct)).
  rewrite eqwt.
  rewrite eqot.
  rewrite eqct.
  assert (tmp: wt = filterb L (L ([[v]])) (fun v : Z => length (filter
           (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
           (map cmdof T))) /\
           ot = filterb L (L ([[v]])) (count_occ Z.eq_dec (concat (map oof T))) /\
           ct = filterb L (L ([[v]])) (fold_left bagplus (map cof T) Cinv)).
  {
  apply WOT.
  left.
  assumption.
  }
  destruct tmp as (wt1,(ot1,ct1)).
  split.
  apply functional_extensionality.
  intros.
  unfold upd.
  rewrite wt1.
  destruct (Z.eq_dec x ([[v]])).
  {
  rewrite e0.
  unfold filterb.
  simpl.
  destruct (Z.eq_dec (L ([[v]])) (L ([[v]]))).
  Focus 2.
  contradiction.
  destruct (Z.eq_dec ([[v]]) (L ([[v]]))).
  omega.
  simpl.
  rewrite <- filter_updl_eq.
  destruct (filter
     (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[v]]))))
     (map cmdof (map (wkupmap ([[v]])) T))) eqn:FIL1.
  reflexivity.
  assert (INF: In c (filter
        (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[v]]))))
        (map cmdof (map (wkupmap ([[v]])) T)))).
  rewrite FIL1.
  left.
  reflexivity.
  apply filter_In in INF.
  destruct INF as (INF,TRF).
  rewrite map_map in INF.
  apply in_map_iff in INF.
  destruct INF as (xF,(EQF,INF)).
  destruct xF as (((((x1,x2),x3),x4),x5),x6).
  unfold cmdof in EQF.
  simpl in EQF.
  rewrite <- EQF in TRF.
  unfold wkupmap in TRF.
  simpl in TRF.
  rewrite wfwk in TRF.
  inversion TRF.
  intros.
  unfold cmdof.
  simpl.
  apply ifboneq.
  intros.
  unfold elem in IN.
  apply filter_In in IN.
  destruct IN as (IN,EQ).
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ1,IN)).
  apply Z.eqb_eq in EQ.
  rewrite <- EQ1.
  apply wfwk.
  }
  {
  rewrite <- filterb_updl_eq.
  unfold filterb.
  destruct (Z.eq_dec x (L ([[v]]))).
  reflexivity.
  intros.
  destruct (Z.eq_dec (L x) (L ([[v]]))).
  Focus 2.
  reflexivity.
  rewrite map_map.
  apply filter_map_eq.
  intros.
  destruct x0 as (((((x1,x2),x3),x4),x5),x6).
  unfold wkupmap.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec (waiting_for_cond x1) (Some x)).
  destruct x1;
  simpl in e1;
  inversion e1.
  rewrite <- e1.
  unfold wakeupcmd.
  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  omega.
  simpl.
  destruct (opZ_eq_dec (Some ([[v0]])) (Some ([[v0]]))).
  reflexivity.
  contradiction.
  simpl.
  destruct x1;
  simpl;
  symmetry;
  try apply ifboneq.
  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  apply ifboneq.
  simpl.
  destruct (opZ_eq_dec (Some ([[v0]])) (Some x)).
  simpl in n1.
  contradiction.
  reflexivity.
  intros.
  unfold cmdof.
  simpl.
  split.
  apply ifboneq.
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
  apply ifboneq.
  }
  auto.
  }
  assert (tmp: wt0 =
      filterb L l
        (fun v : Z =>
         length
           (filter
              (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
              (map cmdof T))) /\
      ot0 = filterb L l (count_occ Z.eq_dec (concat (map oof T))) /\
      ct0 = filterb L l (fold_left bagplus (map cof T) Cinv)).
  apply WOT.
  assumption.
  destruct tmp as (wteq,(oteq,cteq)).
  rewrite wteq.
  split.
  apply FIL.
  assumption.
  auto.
  }
  exists.
  {
  unfold upd.
  intros.
  destruct (Z.eq_dec l (L ([[v]]))).
  inversion LOCK.
  rewrite <- FIL.
  apply LINV.
  assumption.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  unfold updl in ING.
  rewrite map_map in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
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
  assumption.
  exists.
  unfold weakest_pre_ct.
  simpl.
  assumption.
  exists.
  intros.
  inversion W4COND.
  trivial.
(* ==================== x6 <> id ===========*)
  inversion EQ.
  rewrite H1 in IN.
  rewrite H2 in IN.
  rewrite H3 in IN.
  rewrite H4 in IN.
  rewrite H5 in IN.
  assert (tmp:=IN).
  apply VALIDT in tmp.
  destruct tmp as (WF1,(WP1,(VOBS1,TR11))).
  exists.
  destruct x1;
  simpl;
  try assumption.
  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  trivial.
  trivial.
  exists.
  {
  destruct (cmd_eq_dec (wakeupcmd ([[v]]) x1) x1).
  rewrite e.
  assumption.
  destruct x1;
  try contradiction.
  simpl in n0.
  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  rewrite <- e.
  simpl.
  rewrite eqz.
  apply sat_wait4cond in WP1.
  destruct WP1 as (pv0,(pl0,(lvl0,(prcl0,(prcv0,SAT0))))).
  replace C0 with (bagplus C0 (fun x => if Z.eq_dec x ([[v0]]) then if Bool.bool_dec (M ([[v0]])) true then 1%nat else 0%nat else 0%nat)).
  assumption.
  unfold bagplus.
  rewrite e.
  rewrite Mv.
  simpl.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x ([[v]]));
  omega.
  contradiction.
  }
  exists.
  intros.
  destruct x1;
  inversion W4COND.
  destruct (Z.eq_dec ([[v1]]) ([[v]])).
  inversion H6.
  inversion H6.
  unfold updl.
  rewrite map_map.
  rewrite map_map.
  rewrite filter_map_eq with (m2:=cmdof).
  apply VOBS1 with l.
  assumption.
  intros.
  destruct x as (((((x1',x2'),x3'),x4'),x5'),x6').
  unfold cmdof.
  simpl.
  destruct (Z.eq_dec x6' id).
  simpl.
  rewrite e in IN0.
  assert (EQa: (x1',x2',x3',x4',x5') = (NotifyAll v, tx, p, O, C)).
  eapply unique_key_eq.
  apply IN0.
  assumption.
  assumption.
  inversion EQa.
  reflexivity.
  simpl.
  destruct x1';
  simpl;
  try reflexivity.
  destruct (Z.eq_dec ([[v2]]) ([[v]])).
  simpl.
  rewrite e.
  rewrite <- H7.
  destruct (opZ_eq_dec (Some ([[v]])) (Some ([[v1]]))).
  inversion e0.
  omega.
  destruct (opZ_eq_dec (h ([[l1]])) (Some 1%Z)).
  apply ifboneq.
  destruct (opZ_eq_dec (Some ([[l1]])) (Some ([[v1]]))).
  inversion e0.
  assert (tmp:=IN0).
  apply VALIDT in tmp.
  destruct tmp as (WF1',(WP1',(VOBS1',TR11'))).
  apply sat_wait4cond in WP1'.
  destruct WP1' as (x3'v3,(x3'l,rest)).
  apply sat_wait4cond in WP1.
  destruct WP1 as (p0v1,rest1).
  assert (LKD: fold_left phplus (map pof T) Pinv ([[l1]]) = Some Lock \/
       (exists wt ot ct : bag,
          fold_left phplus (map pof T) Pinv ([[l1]]) =
          Some (Locked wt ot ct))).
  {
  destruct x3'l as [x3'l|x3'l].
  apply phplus_fold_lock.
  apply pofs.
  assumption. 
  assumption.
  assumption.
  right.
  exists x3'.
  exists.
  apply in_map_iff.
  exists (Waiting4cond v2 l1, x2', x3', x4', x5', x6').
  auto.
  assumption.
  right.
  destruct x3'l as (wt',(ot',(ct',x3'l))).
  exists wt', ot', ct'.
  apply fold_locked.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists x3'.
  exists.
  apply in_map_iff.
  exists (Waiting4cond v2 l1, x2', x3', x4', x5', x6').
  auto.
  assumption.
  }
  assert (CND: fold_left phplus (map pof T) Pinv ([[l1]]) = Some Cond).
  {
  rewrite H9.
  apply fold_cond.
  apply pofs.
  assumption. 
  assumption.
  assumption.
  right.
  exists p0.
  exists.
  apply in_map_iff.
  exists (Waiting4cond v1 l0, tx0, p0, O0, C0, id0).
  auto.
  assumption.
  }
  rewrite CND in LKD.
  destruct LKD as [CO|CO].
  inversion CO.
  destruct CO as (wt0,(ot0,(ct0,CO))).
  inversion CO.
  reflexivity.
  reflexivity.
  trivial.
  }
  trivial.
Qed.

Lemma Notify_preserves_validity:
  forall h t id id' v v' l tx tx'
         (EQvv': ([[v]]) = ([[v']]))
         (CMD: t id = Some (Notify v, tx))
         (CMD': t id' = Some (Waiting4cond v' l, tx'))
         (VALID: validk t h),
    validk (upd (upd t id (Some (Val 0, tx))) id' (Some (Waiting4lock l, tx'))) h.
Proof.
  intros.
  unfold validk in VALID.
  destruct VALID as (T,(R,(I,(L,(M,(P,(X,(Pinv,(Ainv,(Cinv,(NODUPA,(Ainvl,(PHPDL,(PHPD,(BPE,(BPA,(BPT,(SATA,(PH2H,(AUT,(UNQ,(VLOCK,(VULOCK,(WOT,(LINV,(VALIDT,TR)))))))))))))))))))))))))).
  unfold validk.
  assert (NEQidid': id <>id').
  unfold not.
  intros.
  rewrite H in CMD.
  rewrite CMD in CMD'.
  inversion CMD'.
  assert (tmp: exists p O C, In (Notify v, tx, p, O, C, id) T).
  apply AUT.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply VALIDT in tmp.
  destruct tmp as (WF,(WP,(VOBS,TR1))).
  unfold wellformed in WF.
  simpl in WF.
  apply sat_notify in WP.
  destruct WP as (wt,(ot,(ct,(C1,(Cm,(C1Cm,(plv,(pv,(Cmeq,SAT1))))))))).
  assert (tmp: exists p' O' C', In (Waiting4cond v' l, tx', p', O', C', id') T).
  apply AUT.
  assumption.
  destruct tmp as (p',(O',(C',INT'))).
  assert (tmp:=INT').
  apply VALIDT in tmp.
  destruct tmp as (WF',(WP',(VOBS',TR1'))).
  unfold wellformed in WF'.
  simpl in WF'.
  apply sat_wait4cond in WP'.
  destruct WP' as (p'v',(p'l,(lv'l,(prcl,(prcv',SAT2))))).
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
  assert (lvl: ([[l]]) = L ([[v]])).
  {
  rewrite EQvv'.
  symmetry.
  assumption.
  }
  rewrite <- lvl in *.
  assert (LOCKED: fold_left phplus (map pof T) Pinv ([[l]]) = Some (Locked wt ot ct)).
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
  assert (neqvl: ([[v]]) <> ([[l]])).
  {
  unfold not.
  intros.
  rewrite <- H in plv.
  rewrite plv in pv.
  inversion pv.
  }
  assert (wtv: lt 0 (wt ([[v]]))).
  {
  assert (tmp: wt = filterb L ([[l]]) (fun v : Z => length (filter
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof T))) /\
    ot = filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))) /\
    ct = filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)).
  apply WOT.
  left.
  assumption.
  destruct tmp as (wt1,(ot1,ct1)).
  rewrite wt1.
  unfold filterb.
  destruct (Z.eq_dec ([[v]]) ([[l]])).
  contradiction.
  rewrite <- lvl.
  destruct (Z.eq_dec ([[l]]) ([[l]])).
  Focus 2.
  contradiction.
  assert (IN1: In (Waiting4cond v' l) (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[v]]))))
     (map cmdof T))).
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
  destruct (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[v]]))))
           (map cmdof T)).
  inversion IN1.
  simpl.
  omega.
  }
  assert (CmEQ: Cm = (fun x => if Z.eq_dec x ([[v']]) then if Bool.bool_dec (M ([[v']])) true then 1 else 0 else 0)).
  {
  rewrite Cmeq.
  rewrite <- EQvv'.
  apply functional_extensionality.
  intros.
  destruct (Nat.eq_dec (wt ([[v]])) 0).
  omega.
  reflexivity.
  }
  rewrite <- CmEQ in *.
  assert (tmp: L ([[l]]) = ([[l]]) /\ P ([[l]]) = false /\
           ~ In (R ([[l]])) (X (L ([[l]]))) /\
          (h ([[l]]) <> Some 1%Z -> In ([[l]]) (concat (map oof T)))).
  {
  apply VLOCK.
  destruct p'l as [p'l|p'l].
  apply phplus_fold_lock.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists p'.
  exists.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  auto.
  assumption.
  right.
  destruct p'l as (wt',(ot',(ct',p'l))).
  exists wt', ot', ct'.
  apply fold_locked.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists p'.
  exists.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  auto.
  assumption.
  }
  destruct tmp as (lll,(plf,(ninrlxll,inlt))).
  rewrite lll in *.
  exists (updl (updl T id (Val 0, tx, upd p ([[l]]) (Some (Locked (upd wt ([[v]]) ((wt ([[v]]) - 1)%nat)) ot ct)), O, C1, id))
          id' (Waiting4lock l, tx',p', O', bagplus C' Cm, id')).
  exists R, I, L, M, P, X, Pinv, Ainv, Cinv.
  assert (EQ_3: map oof (updl (updl T id (Val 0, tx, upd p ([[l]]) (Some (Locked (upd wt ([[v]]) ((wt ([[v]]) - 1)%nat)) ot ct)), O, C1, id))
          id' (Waiting4lock l, tx', p', O', bagplus C' Cm, id')) = map oof T).
  {
  unfold updl.
  rewrite map_map.
  rewrite map_map.
  apply map_ext_in.
  intros.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  unfold idof.
  simpl.
  destruct (Z.eq_dec a6 id).
  simpl.
  destruct (Z.eq_dec id id').
  contradiction.
  assert (EQa: (a1,a2,a3,a4,a5) = (Notify v, tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQa.
  reflexivity.
  simpl.
  destruct (Z.eq_dec a6 id').
  assert (EQa: (a1,a2,a3,a4,a5) = (Waiting4cond v' l, tx', p', O', C')).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQa.
  reflexivity.
  reflexivity.
  }
  assert (EQ_4: fold_left bagplus (map cof (updl (updl T id (Val 0, tx, upd p ([[l]]) (Some (Locked (upd wt ([[v]]) ((wt ([[v]]) - 1)%nat)) ot ct)), O, C1, id))
          id' (Waiting4lock l, tx', p', O', bagplus C' Cm, id'))) Cinv = fold_left bagplus (map cof T) Cinv).
  {
  replace (fold_left bagplus (map cof T) Cinv) with
    (bagplus Cm (fold_left bagplus 
     (map cof (updl T id (Val 0, tx, upd p ([[l]]) (Some (Locked (upd wt ([[v]]) ((wt ([[v]]) - 1)%nat)) ot ct)), O, C1, id))) Cinv)).
  {
  rewrite fold_left_move_m_eq with (x:=(Waiting4cond v' l, tx', p', O', C'))
    (x1:=C')(x2:=Cm)(id:=id')(def:=bagdef).
  replace (updl (updl (updl T id (Val 0, tx, upd p ([[l]]) (Some (Locked (upd wt ([[v]]) (wt ([[v]]) - 1)) ot ct)), O, C1, id))
             id' (Waiting4lock l, tx', p', O', bagplus C' Cm, id'))
             id' (Waiting4cond v' l, tx', p', O', C', id')) with 
             (updl T id (Val 0, tx, upd p ([[l]])
             (Some (Locked (upd wt ([[v]]) (wt ([[v]]) - 1)) ot ct)), O, C1, id)).
  reflexivity.
  rewrite updl_updl.
  symmetry.
  apply updl_redundant.
  unfold elem.
  unfold updl.
  intros.
  apply filter_In in IN.
  destruct IN as (IN,EQid').
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INxT)).
  apply Z.eqb_eq in EQid'.
  destruct (Z.eq_dec (snd x) id).
  rewrite <- EQx in EQid'.
  simpl in EQid'.
  contradiction.
  destruct x' as (((((a1,a2),a3),a4),a5),a6).
  simpl in EQid'.
  assert (EQa: (a1,a2,a3,a4,a5) = (Waiting4cond v' l, tx', p', O', C')).
  eapply unique_key_eq.
  rewrite EQx in INxT.
  apply INxT.
  rewrite EQid'.
  assumption.
  assumption.
  inversion EQa.
  rewrite EQid'.
  reflexivity.
  apply canbag.
  apply NoDup_updl.
  apply NoDup_updl.
  assumption.
  apply defl_bagdef.
  trivial.
  intros.
  trivial.
  apply in_map_iff.
  exists (Waiting4lock l, tx', p', O', bagplus C' Cm, id').
  split.
  reflexivity.
  apply in_updl_eq.
  exists (Waiting4cond v' l, tx', p', O', C').
  apply in_updl_neq.
  assumption.
  assumption.
  reflexivity.
  }
  symmetry.
  apply fold_left_move_m_eq with (x1:=C1)(def:=bagdef).
  apply canbag.
  assumption.
  unfold elem.
  apply defl_bagdef.
  trivial.
  trivial.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  split.
  rewrite C1Cm.
  reflexivity.
  assumption.
  simpl.
  reflexivity.
  }
assert (FILw: forall l0 (ll0: ([[l]]) <> l0),
         (filterb L l0 (fun v : Z => length (filter (fun c : cmd =>
          ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
          (map cmdof T)))) =
         (filterb L l0 (fun v0 : Z => length (filter (fun c : cmd => 
          ifb (opZ_eq_dec (waiting_for_cond c) (Some v0)))
          (map cmdof (updl (updl T id (Val 0, tx, upd p ([[l]]) (Some (Locked (upd wt ([[v]]) ((wt ([[v]]) - 1)%nat)) ot ct)), O, C1, id))
          id' (Waiting4lock l, tx', p', O', bagplus C' Cm, id'))))))).
  {
  intros.
  unfold filterb.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x l0) as [xl0|xl0].
  reflexivity.
  destruct (Z.eq_dec (L x) l0) as [lxl0|lxl0].
  Focus 2.
  reflexivity.
  destruct (Z.eq_dec x ([[l]])) as [xl|xl].
  rewrite xl in lxl0.
  rewrite lll in lxl0.
  contradiction.
  destruct (Z.eq_dec x ([[v]])) as [xv|xv].
  rewrite xv in lxl0.
  rewrite <- lvl in lxl0.
  contradiction.
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
  apply in_elem with (updl T id (Val 0, tx, upd p ([[l]])
    (Some (Locked (upd wt ([[v]]) (wt ([[v]]) - 1)) ot ct)), O, C1, id)).
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
  }
  assert (EQ_5: fold_left phplus (map pof (updl (updl T id (Val 0, tx, upd p ([[l]])
           (Some (Locked (upd wt ([[v]]) (wt ([[v]]) - 1)) ot ct)), O, C1, id))
           id' (Waiting4lock l, tx', p', O', bagplus C' Cm, id'))) Pinv = 
           upd (fold_left phplus (map pof T) Pinv) ([[l]]) (Some (Locked (upd wt ([[v]]) (wt ([[v]]) - 1)) ot ct))).
  {
  apply fold_left_upd_Notify with p p'.
  assumption.
  apply pofs.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  auto.
  exists wt, ot, ct.
  assumption.
  reflexivity.
  reflexivity.
  }
  rewrite EQ_3.
  rewrite EQ_4.
  rewrite EQ_5.
  exists NODUPA.
  exists.
  {
  intros.
  apply Ainvl in IN.
  destruct IN as (EQ1,EQ2).
  unfold upd.
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite e in EQ1.
  rewrite LOCKED in EQ1.
  inversion EQ1.
  auto.
  }
  exists.
  {
  apply defl_Notify with (z:=([[l]])) (p:=p) (p':=p') (wt:=(upd wt ([[v]]) (wt ([[v]]) - 1))) (ot:=ot) (ct:=ct).
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  auto.
  exists wt, ot, ct.
  assumption.
  reflexivity.
  reflexivity.
  }
  exists.
  {
  intros.
  eapply phpdef_updl with (m:=pof) (x:=(Waiting4lock l, tx', p', O', bagplus C' Cm, id'))
    (l:=(updl T id (Val 0, tx, upd p ([[l]]) (Some (Locked (upd wt ([[v]]) (wt ([[v]]) - 1)) ot ct)), O, C1, id))).
  intros.
  eapply phpdef_updl with (m:=pof) (x:=(Val 0, tx, upd p ([[l]])(Some (Locked (upd wt ([[v]]) (wt ([[v]]) - 1)) ot ct)), O, C1, id))
    (l:=T).
  intros.
  apply PHPD.
  assumption.
  apply IN0.
  unfold pof.
  simpl.
  apply phpdef_locked.
  apply PHPD.
  apply in_map_iff.
  exists (Notify v, tx, p, O, C, id).
  auto.
  exists wt, ot, ct.
  assumption.
  apply IN.
  unfold pof.
  simpl.
  apply PHPD.
  apply in_map_iff.
  exists (Waiting4cond v' l, tx', p', O', C', id').
  auto.
  }
  exists.
  {
  intros.
  apply boundph_updl with (m:=pof) (l:=updl T id (Val 0, tx, upd p ([[l]])
    (Some (Locked (upd wt ([[v]]) (wt ([[v]]) - 1)) ot ct)), O, C1, id)) (z:=id') (x:=(Waiting4lock l, tx', p', O', bagplus C' Cm, id')).
  intros.
  apply boundph_updl with (m:=pof) (l:=T) (z:=id) (x:=(Val 0, tx, upd p ([[l]])
    (Some (Locked (upd wt ([[v]]) (wt ([[v]]) - 1)) ot ct)), O, C1, id)).
  assumption.
  assumption.
  unfold pof.
  simpl.
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  assumption.
  unfold pof.
  simpl.
  assumption.
  }
  exists.
  assumption.
  exists.
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }
  exists.
  assumption.
  exists.
  {
  rewrite phtoh_upd_locked.
  assumption.
  exists wt, ot, ct.
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
  unfold upd.
  intros.
  apply VLOCK.
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite e.
  right.
  exists wt, ot, ct.
  assumption.
  assumption.
  }
  exists.
  {
  unfold upd.
  intros.
  destruct (Z.eq_dec l0 ([[l]])).
  inversion ULOCK.
  apply VULOCK with wt0 ot0 ct0.
  assumption.
  }
  exists.
  {
  unfold upd.
  intros.
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite e.
  assert (tmp: wt0 = upd wt ([[v]]) (wt ([[v]]) - 1) /\
               ot0 = ot /\
               ct0 = ct).
  split.
  destruct ULOCKED as [U|U].
  inversion U.
  reflexivity.
  inversion U.
  destruct ULOCKED as [U|U].
  inversion U.
  auto.
  inversion U.
  auto.
  destruct tmp as(eqwt,(eqot,eqct)).
  rewrite eqwt.
  rewrite eqot.
  rewrite eqct.
  assert (tmp: wt = filterb L (L ([[v]])) (fun v : Z => length (filter
           (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
           (map cmdof T))) /\
           ot = filterb L (L ([[v]])) (count_occ Z.eq_dec (concat (map oof T))) /\
           ct = filterb L (L ([[v]])) (fold_left bagplus (map cof T) Cinv)).
  apply WOT.
  left.
  rewrite <- lvl.
  assumption.
  destruct tmp as (wt1,(ot1,ct1)).
  split.
  apply functional_extensionality.
  intros.
  unfold upd.
  destruct (Z.eq_dec x ([[v]])).
  rewrite e0.
  unfold filterb.
  simpl.
  destruct (Z.eq_dec ([[v]]) ([[l]])).
  omega.
  rewrite <- lvl.
  destruct (Z.eq_dec ([[l]]) ([[l]])).
  Focus 2.
  contradiction.
  rewrite wt1.
  unfold filterb.
  rewrite lvl.
  destruct (Z.eq_dec ([[v]]) (L ([[v]]))).
  omega.
  destruct (Z.eq_dec (L ([[v]])) (L ([[v]]))).
  Focus 2.
  contradiction.
  rewrite updl_updl_neq.
  rewrite <- filter_updl_eq.
  simpl.
  apply filter_updl_inc.
  assumption.
  simpl.
  destruct (opZ_eq_dec None (Some ([[v]]))).
  inversion e3. 
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
  inversion e3.
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
  inversion e3.
  reflexivity.
  assumption.
  rewrite wt1.
  unfold filterb.
  rewrite <- lvl.
  destruct (Z.eq_dec x ([[l]])).
  reflexivity.
  destruct (Z.eq_dec (L x) ([[l]])).
  Focus 2.
  reflexivity.
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
  rewrite <- lvl in *.
  auto.
  apply WOT in ULOCKED.
  destruct ULOCKED as (wt1,(ot1,ct1)).
  rewrite wt1.
  split.
  apply FILw.
  omega.
  auto.
  }
  exists.
  {
  unfold upd.
  intros.
  assert (ll0: l0 <> ([[l]])).
  destruct (Z.eq_dec l0 ([[l]])).
  inversion LOCK.
  assumption.
  assert (INIL: In (I l0 (filterb L l0 (fun v : Z => length (filter
           (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
           (map cmdof T))))
           (filterb L l0 (count_occ Z.eq_dec (concat (map oof T))))
           (filterb L l0 (fold_left bagplus (map cof T) Cinv)),l0) Ainv).
  apply LINV.
  destruct (Z.eq_dec l0 ([[l]])).
  contradiction.
  assumption.
  assumption.
  rewrite <- FILw.
  assumption.
  omega.
  }
  exists.
  Focus 2.
  trivial.
  {
  intros.
  unfold updl in ING.
  rewrite map_map in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold idof in EQ.
  simpl in EQ.
  unfold ctxof in EQ.
  unfold pof in EQ.
  unfold oof in EQ.
  unfold cof in EQ.
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
  apply VALIDT in tmp.
  destruct tmp as (WF1,(WP1,(VOBS1,TR11))).
  exists.
  assumption.
  exists.
  unfold weakest_pre_ct.
  simpl.
  assumption.
  exists.
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
  apply VALIDT in tmp.
  destruct tmp as (WF1,(WP1,(VOBS1,TR11))).
  exists.
  assumption.
  exists.
  assumption.
  unfold bagplus.
  exists.
  intros.
  inversion W4COND.
  trivial.
(* ==================== x6 <> id id' ===========*)
  inversion EQ.
  rewrite H0 in IN.
  rewrite H1 in IN.
  rewrite H2 in IN.
  rewrite H3 in IN.
  rewrite H4 in IN.
  rewrite H5 in IN.
  assert (tmp:=IN).
  apply VALIDT in tmp.
  destruct tmp as (WF1,(WP1,(VOBS1,TR11))).
  exists.
  assumption.
  exists.
  assumption.
  exists.
  intros.
  assert (tmp:=IN).
  rewrite W4COND in tmp.
  apply VALIDT in tmp.
  destruct tmp as (WF'',(WP'',(VOBS'',TR1''))).
  apply sat_wait4cond in WP''.
  destruct WP'' as (pv0,(pl0,(lvl0,(prcl0,(prcv0,(Cm0,(Cmeq0,SAT0))))))).
  assert (v0l0: ([[v0]]) <> ([[l]])).
  {
  unfold not.
  intros.
  rewrite H in pv0.
  assert (CND: (fold_left phplus (map pof T) Pinv) ([[l]]) = Some Cond).
  {
  apply fold_cond.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists p0.
  exists.
  apply in_map_iff.
  exists (c, tx0, p0, O0, C0, id0).
  auto.
  assumption.
  }
  rewrite CND in LOCKED.
  inversion LOCKED.
  }
  assert (length (filter
           (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for h c0) (Some ([[v0]]))))
           (map cmdof (updl (updl T id
           (Val 0, tx, upd p ([[l]]) (Some (Locked (upd wt ([[v]]) (wt ([[v]]) - 1)) ot ct)), O, C1, id)) id'
           (Waiting4lock l, tx', p', O', bagplus C' Cm, id')))) <= 
           (length (filter (fun c : cmd =>
           ifb (opZ_eq_dec (waiting_for h c) (Some ([[v0]]))))
           (map cmdof T)))).
  {
  simpl.
  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  rewrite <- filter_updl_inc.
  rewrite <- filter_updl_eq.
  omega.
  simpl.
  destruct (opZ_eq_dec None (Some ([[v0]]))).
  inversion e0.
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
  destruct (opZ_eq_dec None (Some ([[v0]]))).
  inversion e0.
  reflexivity.
  apply NoDup_updl.
  assumption.
  simpl.
  destruct (opZ_eq_dec (h ([[l]])) (Some 1%Z)).
  destruct (opZ_eq_dec None (Some ([[v0]]))) .
  inversion e1.
  reflexivity.
  destruct (opZ_eq_dec (Some ([[l]])) (Some ([[v0]]))).
  inversion e0.
  omega.
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
  rewrite e.
  destruct (opZ_eq_dec (Some ([[v]])) (Some ([[v]]))).
  reflexivity.
  contradiction.
  rewrite <- filter_updl_eq.
  rewrite <- filter_updl_eq.
  omega.
  simpl.
  destruct (opZ_eq_dec None (Some ([[v0]]))).
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
  destruct (opZ_eq_dec None (Some ([[v0]]))).
  inversion e.
  reflexivity.
  simpl.
  destruct (opZ_eq_dec (h ([[l]])) (Some 1%Z)).
  destruct (opZ_eq_dec None (Some ([[v0]]))) .
  inversion e0.
  reflexivity.
  destruct (opZ_eq_dec (Some ([[l]])) (Some ([[v0]]))).
  inversion e.
  omega.
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
  destruct (opZ_eq_dec None (Some ([[v0]]))).
  inversion e.
  rewrite <- EQvv'.
  destruct (opZ_eq_dec (Some ([[v]])) (Some ([[v0]]))).
  inversion e.
  omega.
  reflexivity.
  }
  eapply safe_obs_obv.
  apply H.
  apply VOBS1 with l0.
  assumption.
  trivial.
  }
Qed.
Lemma Notify0_preserves_validity:
  forall h t id v tx
         (CMD: t id = Some (Notify v, tx))
         (NWT : ~ (exists (id' : Z) v' (l : exp) (tx' : context) (EQvv': eval v = eval v'),
                t id' = Some (Waiting4cond v' l, tx')))
         (VALID: validk t h),
    validk (upd t id (Some (Val 0, tx))) h.
Proof.
  intros.
  unfold validk in VALID.
  destruct VALID as (T,(R,(I,(L,(M,(P,(X,(Pinv,(Ainv,(Cinv,(NODUPA,(Ainvl,(PHPDL,(PHPD,(BPE,(BPA,(BPT,(SATA,(PH2H,(AUT,(UNQ,(VLOCK,(VULOCK,(WOT,(LINV,(VALIDT,TR)))))))))))))))))))))))))).
  unfold validk.
  assert (tmp: exists p O C, In (Notify v, tx, p, O, C, id) T).
  apply AUT.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  exists (updl T id (Val 0, tx, p, O, C, id)).
  exists R, I, L, M, P, X, Pinv, Ainv, Cinv.
  assert (tmp:=INT).
  apply VALIDT in tmp.
  destruct tmp as (WF,(WP,(VOBS,TR1))).
  unfold wellformed in WF.
  simpl in WF.
  apply sat_notify in WP.
  destruct WP as (wt,(ot,(ct,(C1,(Cm,(C1Cm,(plv,(pv,(Cmeq,SAT))))))))).
  assert (LOCKED: fold_left phplus (map pof T) Pinv (L ([[v]])) = Some (Locked wt ot ct)).
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
  assert (COND: fold_left phplus (map pof T) Pinv ([[v]]) = Some Cond).
  {
  eapply fold_cond with (m:=pof) (l:=T).
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
  assert (wtv: wt ([[v]]) = 0).
  {
  assert (tmp:wt = filterb L (L ([[v]])) (fun v : Z => length (filter
           (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
           (map cmdof T))) /\
           ot = filterb L (L ([[v]])) (count_occ Z.eq_dec (concat (map oof T))) /\
           ct = filterb L (L ([[v]])) (fold_left bagplus (map cof T) Cinv)).
  apply WOT.
  left.
  assumption.
  destruct tmp as (wteq,rest).
  rewrite wteq.
  simpl.
  unfold filterb.
  destruct (Z.eq_dec ([[v]]) (L ([[v]]))).
  reflexivity.
  destruct (Z.eq_dec (L ([[v]])) (L ([[v]]))).
  Focus 2.
  contradiction.
  destruct (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[v]]))))
     (map cmdof T)) eqn:flt.
  reflexivity.
  assert (CO: In c (filter
        (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some ([[v]]))))
        (map cmdof T))).
  rewrite flt.
  left.
  reflexivity.
  apply filter_In in CO.
  destruct CO as [INCO WC].
  exfalso.
  apply NWT.
  apply in_map_iff in INCO.
  destruct INCO as (x,(cx,INx)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  assert (tmp: t x6 = Some (x1,x2)).
  apply AUT.
  exists x3,x4,x5.
  assumption.
  unfold cmdof in cx.
  simpl in cx.
  rewrite cx in tmp.
  unfold ifb in WC.
  destruct (opZ_eq_dec (waiting_for_cond c) (Some ([[v]]))).
  Focus 2.
  inversion WC.
  rewrite cx in INx.
  assert (wflc:=e0).
  destruct c;
  simpl in wflc;
  inversion wflc.
  exists x6, v0, l0, x2.
  exists.
  reflexivity.
  assumption.
  }
  assert (EQ_1: map pof (updl T id (Val 0, tx, p, O, C, id)) = map pof T).
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
  assert (EQ_2:map (fun x => (pof x, idof x)) (updl T id (Val 0, tx, p, O, C, id)) =
               map (fun x => (pof x, idof x)) T).
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
  assert (EQ_3: map oof (updl T id (Val 0, tx, p, O, C, id)) = map oof T).
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
  assert (EQ_4: map cof (updl T id (Val 0, tx, p, O, C, id))  = map cof T).
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
  assert (EQ_5: forall v, filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T) =
          filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof (updl T id (Val 0, tx, p, O, C, id)) )).
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
           (map cmdof (updl T id (Val 0, tx, p, O, C, id)) ))) =
           (fun v0 : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0)))
           (map cmdof T)))).
  {
  apply functional_extensionality.
  intros.
  rewrite EQ_5.
  reflexivity.
  }
  assert (EQ_7: forall v, filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some v))) (map cmdof T) =
          filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some v))) (map cmdof (updl T id (Val 0, tx, p, O, C, id)) )).
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
  rewrite EQ_1.
  rewrite EQ_2.
  rewrite EQ_3.
  rewrite EQ_4.
  rewrite EQ_6.
  exists NODUPA, Ainvl, PHPDL, PHPD, BPE , BPA, BPT, SATA, PH2H.
 
  exists.
  {
  intros.
  apply upd_updl.
  exists (Notify v, tx, p, O, C).
  auto.
  assumption.
  }
  exists.
  apply NoDup_updl.
  assumption.
  exists.
  assumption.
  exists.
  assumption.
  exists.
  assumption.
  exists.
  assumption.
  exists.
  Focus 2.
  trivial.
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold idof in EQ.
  simpl in EQ.
  unfold ctxof in EQ.
  unfold pof in EQ.
  unfold oof in EQ.
  unfold cof in EQ.
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
  rewrite upd_eq in SAT.
  replace C with C1.
  assumption.
  rewrite C1Cm.
  rewrite Cmeq.
  unfold bagplus.
  apply functional_extensionality.
  intros.
  rewrite wtv.
  destruct (Z.eq_dec x ([[v]])).
  destruct (Bool.bool_dec (M ([[v]])) true).
  destruct (Nat.eq_dec 0 0).
  omega.
  contradiction.
  omega.
  omega.
  replace (upd wt ([[v]]) (wt ([[v]]) - 1)) with wt.
  assumption.
  rewrite wtv.
  simpl.
  symmetry.
  apply upd_eq.
  assumption.
  exists.
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
  apply VALIDT in tmp.
  destruct tmp as (WF1,(WP1,(VOBS1,TR11))).
  exists.
  assumption.
  exists.
  assumption.
  exists.
  intros.
  rewrite <- EQ_7.
  apply VOBS1 with l.
  assumption.
  trivial.
Qed.
Lemma Wait_preserves_validity:
  forall h t id v l tx
         (CMD: t id = Some (Wait v l, tx))
         (VALID: validk t h),
    validk (upd t id (Some (Waiting4cond v l, tx)))(upd h ([[l]]) (Some 1%Z)).
Proof.
  intros.
  unfold validk in VALID.
  destruct VALID as (T,(R,(I,(L,(M,(P,(X,(Pinv,(Ainv,(Cinv,(NODUPA,(Ainvl,(PHPDL,(PHPD,(BPE,(BPA,(BPT,(SATA,(PH2H,(AUT,(UNQ,(VLOCK,(VULOCK,(WOT,(LINV,(VALIDT,TR)))))))))))))))))))))))))).
  unfold validk.
  assert (tmp: exists p O C, In (Wait v l, tx, p, O, C, id) T).
  apply AUT.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply VALIDT in tmp.
  destruct tmp as (WF,(WP,(VOBS,TR1))).
  unfold wellformed in WF.
  simpl in WF.
  apply sat_wait in WP.
  destruct WP as (p1,(p2,(wt,(ot,(ct,(C1,(C2,(O1,(O1eq,(BP1,(BP2,(phpdp1p2,(p1p2,(C1C2,(p1l,(p1v,(p2inv,(prcv,(prcl,(NEQvl,(Lvl,(SAFE_OBS,SATp1)))))))))))))))))))))).
  exists (updl T id (Waiting4cond v l, tx, upd p1 (eval l) (Some Lock), O1, C1, id)).
  exists R, I, L, M, P, X.
  exists (phplus Pinv p2).
  exists ((I ([[l]]) (upd wt (eval v) (S (wt (eval v)))) ot ct,[[l]])::Ainv), (bagplus Cinv C2).
  assert (Pl: p ([[l]]) = Some (Locked wt ot ct)).
  {
  rewrite p1p2.
  apply phplus_locked.
  assumption.
  assumption.
  }
  assert (COND: fold_left phplus (map pof T) Pinv ([[v]]) = Some Cond).
  {
  eapply fold_cond with (m:=pof) (l:=T).
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Wait v l, tx, p, O, C, id).
  auto.
  rewrite p1p2.
  unfold pof.
  simpl.
  apply phplus_Cond.
  assumption.
  assumption.
  }
  assert (LOCKED: fold_left phplus (map pof T) Pinv ([[l]]) = Some (Locked wt ot ct)).
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
  exists (Wait v l, tx, p, O, C, id).
  auto.
  assumption.
  }
  assert (LOCK: fold_left phplus (map pof (updl T id (Waiting4cond v l, tx, upd p1 ([[l]]) (Some Lock), O1, C1, id))) (phplus Pinv p2) ([[l]]) = Some Lock).
  {
  apply lock_Wait with p1.
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Wait v l, tx, p, O, C, id).
  rewrite p1p2 at 1.
  auto.
  exists wt, ot, ct.
  left.
  assumption.
  reflexivity.
  }
  assert (tmp: L ([[l]]) = ([[l]]) /\
        P ([[l]]) = false /\
        ~ In (R ([[l]])) (X (L ([[l]]))) /\
        (h ([[l]]) <> Some 1%Z -> In ([[l]]) (concat (map oof T)))).
  {
  apply VLOCK.
  right.
  exists wt, ot, ct.
  assumption.
  }
  destruct tmp as (lll,(plf,(ninrl,linobs))).
  assert (p2Pinv: phplusdef p2 Pinv).
  {
  apply phpdef_assoc_mon with p1.
  assumption.
  apply PHPD.
  apply in_map_iff.
  exists (Wait v l, tx, p, O, C, id).
  rewrite <- p1p2.
  auto.
  }
  assert (wot: wt = filterb L ([[l]]) (fun v : Z => length (filter
           (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
           (map cmdof T))) /\
           ot = filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof T))) /\
           ct = filterb L ([[l]]) (fold_left bagplus (map cof T) Cinv)).
  {
  apply WOT.
  left.
  assumption.
  }
  destruct wot as (wteq,(oteq,cteq)).
  assert (EQW: (fun a : Z => if Z.eq_dec a ([[v]]) then S (wt ([[v]])) else wt a) = 
    (filterb L ([[l]]) (fun v0 => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0)))
    (map cmdof (updl T id (Waiting4cond v l, tx, fun a : Z => if Z.eq_dec a ([[l]]) then Some Lock else p1 a,
    O1, C1, id))))))).
  {
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x ([[v]])) as [xv|xv].
  rewrite xv.
  rewrite wteq.
  simpl.
  unfold filterb.
  destruct (Z.eq_dec ([[v]]) ([[l]])).
  contradiction.
  rewrite <- filter_updl_dec.
  rewrite Lvl.
  destruct (Z.eq_dec ([[l]]) ([[l]])).
  Focus 2.
  contradiction.
  reflexivity.
  assumption.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec (Some ([[v]])) (Some ([[v]]))).
  reflexivity.
  contradiction.
  exists (Wait v l, tx, p, O, C, id).
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
  destruct (opZ_eq_dec None (Some ([[v]]))).
  inversion e.
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
  assert (X':x' = (Wait v l, tx, p, O, C, id)).
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
  assert (EQO: ot = (filterb L ([[l]]) (count_occ Z.eq_dec (concat (map oof (updl T id
    (Waiting4cond v l, tx, fun a : Z => if Z.eq_dec a ([[l]]) then Some Lock else p1 a,
    O1, C1, id))))))).
  {
  rewrite oteq.
  apply filterb_updl_obs_eq.
  intros.
  assert (X':x' = (Wait v l, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  inversion X'.
  unfold oof.
  simpl.
  rewrite O1eq.
  simpl.
  destruct (Z.eq_dec ([[l]]) v0).
  omega.
  reflexivity.
  }
  assert (LOCKU: fold_left phplus (map pof (updl T id (Waiting4cond v l, tx,
                 upd p1 ([[l]]) (Some Lock), O1, C1, id))) (phplus Pinv p2) ([[l]]) = Some Lock).
  {
  apply lock_Wait with p1.
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Wait v l, tx, p, O, C, id).
  rewrite <- p1p2.
  auto.
  exists wt, ot, ct.
  left.
  assumption.
  reflexivity.
  }
  assert (EQH: forall l0 (NEQ: ([[l]]) <> l0), fold_left phplus (map pof (updl T id (Waiting4cond v l, tx, upd p1 ([[l]]) (Some Lock),
    O1, C1, id))) (phplus Pinv p2) l0 = 
    fold_left phplus (map pof T) Pinv l0).
  {
  intros.
  apply eq_heap_Wait with (z:=([[l]])) (p1:=p1).
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Wait v l, tx, phplus p1 p2, O, C, id).
  rewrite <- p1p2.
  auto.
  exists wt, ot, ct.
  left.
  assumption.
  reflexivity.
  assumption.
  }
  assert (bpinvp2: boundph (phplus Pinv p2)).
  {
  apply boundph_mon with p1.
  assumption.
  assumption.
  assumption.
  apply bph_assoc.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  rewrite <- p1p2.
  apply PHPD.
  apply in_map_iff.
  exists (Wait v l, tx, p, O, C, id).
  tauto.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  assumption.
  replace (phplus p2 p1) with (phplus p1 p2).
  apply boundph_fold with (m:=pof) (l:=T).
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  rewrite <- p1p2.
  apply in_map_iff.
  exists (Wait v l, tx, p, O, C, id).
  tauto.
  apply phplus_comm.
  assumption.
  }
  assert (SAFE: safe_obs ([[v]]) (length (filter (fun c0 : cmd => ifb
    (opZ_eq_dec (waiting_for (upd h ([[l]]) (Some 1%Z)) c0) (Some ([[v]]))))
    (map cmdof (updl T id (Waiting4cond v l, tx, upd p1 ([[l]]) (Some Lock),
    O1, C1, id))))) (count_occ Z.eq_dec
    (concat (map oof (updl T id (Waiting4cond v l, tx, upd p1 ([[l]]) (Some Lock),
    O1, C1, id)))) ([[v]])) R L P X = true).
  {
  unfold filterb in EQW.
  apply equal_f with (x:=([[v]])) in EQW.
  rewrite eqz in EQW.
  destruct (Z.eq_dec ([[v]]) ([[l]])).
  contradiction.
  rewrite <- Lvl in EQW.
  rewrite eqz in EQW.
  rewrite filter_filter_eq with (f2:=(fun c0 : cmd => ifb (opZ_eq_dec (waiting_for (upd h ([[l]]) (Some 1%Z)) c0)
    (Some ([[v]]))))) in EQW.
  rewrite Lvl in EQW.
  unfold upd in *.
  rewrite <- EQW.
  unfold filterb in EQO.
  apply equal_f with (x:=([[v]])) in EQO.
  destruct (Z.eq_dec ([[v]]) ([[l]])).
  contradiction.
  rewrite <- Lvl in EQO.
  rewrite eqz in EQO.
  rewrite Lvl in EQO.
  rewrite <- EQO.
  assumption.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x0,(EQ,IN)).
  destruct (opZ_eq_dec (waiting_for_cond x) (waiting_for (upd h ([[l]]) (Some 1%Z)) x)).
  rewrite e.
  reflexivity.
  apply waiting_for_upd_neq in n0.
  destruct n0 as (l1,eq1).
  rewrite eq1.
  simpl.
  destruct ((opZ_eq_dec None (Some ([[v]])))).
  inversion e.
  unfold upd.
  destruct (Z.eq_dec ([[l1]]) ([[l]])).
  destruct (opZ_eq_dec (Some 1%Z) (Some 1%Z)).
  destruct (opZ_eq_dec None (Some ([[v]]))).
  inversion e.
  inversion e1.
  reflexivity.
  contradiction.
  destruct (opZ_eq_dec (h ([[l1]])) (Some 1%Z)).
  destruct ((opZ_eq_dec None (Some ([[v]])))).
  inversion e0.
  reflexivity.
  destruct ((opZ_eq_dec (Some ([[l1]])) (Some ([[v]])))).
  inversion e.
  destruct x0 as (((((x1',x2'),x3'),x4'),x5'),x6').
  unfold cmdof in EQ.
  simpl in EQ.
  rewrite EQ in IN.
  rewrite eq1 in IN.
  unfold updl in IN.
  apply in_map_iff in IN.
  destruct IN as (x',(EQ',IN')).
  destruct x' as (((((x1'',x2''),x3''),x4''),x5''),x6'').
  simpl in EQ'.
  destruct (Z.eq_dec x6'' id).
  inversion EQ'.
  inversion EQ'.
  rewrite H1 in IN'.
  assert (tmp:=IN').
  apply VALIDT in tmp.
  destruct tmp as (WF1,(WP1,(VOBS1,TR11))).
  apply sat_wait4lock in WP1.
  destruct WP1 as (x3l1,PRCl1).
  rewrite H0 in x3l1.
  assert (LOCK_ED: fold_left phplus (map pof T) Pinv ([[v]]) = Some Lock \/
       (exists wt ot ct : bag, fold_left phplus (map pof T) Pinv ([[v]]) = Some (Locked wt ot ct))).
  {
  apply fold_lock_ed.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  right.
  exists x3''.
  exists.
  apply in_map_iff.
  exists (Waiting4lock l1, x2'', x3'', x4'', x5'', x6'').
  auto.
  assumption.
  }
  rewrite COND in LOCK_ED.
  destruct LOCK_ED as [CO|CO].
  inversion CO.
  destruct CO as (wt0,(ot0,(ct0,CO))).
  inversion CO.
  reflexivity.
  }
  exists.
  {
  simpl.
  apply NoDup_cons.
  unfold not.
  intros.
  apply Ainvl in H.
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
  rewrite eqz.
  reflexivity.
  apply Ainvl in IN.
  unfold upd.
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite e.
  auto.
  rewrite EQH.
  assumption.
  omega.
  }
  
  exists.
  {
  apply defl_Wait with ([[l]]) p1 p2.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Wait v l, tx, p, O, C, id).
  rewrite p1p2 at 1.
  auto.
  exists wt, ot, ct.
  left.
  assumption.
  reflexivity.
  }
  exists.
  {
  intros.
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
  exists (Wait v l, tx, p, O, C, id).
  rewrite <- p1p2.
  auto.
  apply phpdef_comm.
  assumption.
  exists wt, ot, ct.
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
  exists wt, ot, ct.
  left.
  assumption.
  apply phpdef_comm.
  apply phpdef_assoc_mon2 with p1.
  assumption.
  rewrite <- p1p2.
  unfold defl in PHPDL.
  apply PHPDL with id x6.
  omega.
  apply in_map_iff.
  exists (Wait v l, tx, p, O, C, id).
  auto.
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
  apply boundph_updl with (m:=pof)(l:=T)(z:=id)(x:=(Waiting4cond v l, tx, upd p1 ([[l]]) (Some Lock), O1, C1, id)).
  assumption.
  assumption.
  unfold pof.
  simpl.
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }
  exists.
  {
  apply boundph_mon with p1.
  assumption.
  assumption.
  assumption.
  apply bph_assoc.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  apply PHPD.
  rewrite phplus_comm.
  rewrite <- p1p2.
  apply in_map_iff.
  exists (Wait v l, tx, p, O, C, id).
  tauto.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  assumption.
  replace (phplus p2 p1) with (phplus p1 p2).
  apply boundph_fold with (m:=pof) (l:=T).
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  rewrite <- p1p2.
  apply in_map_iff.
  exists (Wait v l, tx, p, O, C, id).
  tauto.
  apply phplus_comm.
  assumption.
  }
  exists.
  {
  apply boundph_Wait with ([[l]]) p1.
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  rewrite <- p1p2.
  apply in_map_iff.
  exists (Wait v l, tx, p, O, C, id).
  auto.
  exists wt, ot, ct.
  left.
  assumption.
  reflexivity.
  assumption.
  }
  exists.
  {
  replace (fold_left Lastar (map fst ((I ([[l]]) (upd wt ([[v]]) (S (wt ([[v]])))) ot ct, [[l]]) :: Ainv)) (Labool true))
     with (fold_left Lastar (map fst Ainv) (Lastar (Labool true) (I ([[l]]) (upd wt ([[v]]) (S (wt ([[v]])))) ot ct))).
  Focus 2.
  reflexivity.
  simpl.
  apply fold_left_g_can.
  unfold cang.
  split.
  intros.
  apply lsat_comm.
  assumption.
  simpl.
  intros.
  apply lsat_perm with (l:=l0).
  assumption.
  assumption.
  assumption.
  apply lsat_comm.
  apply lsat_plus.
  apply phpdef_comm.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  exists.
  {
  apply phtoh_Wait with p1.
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  rewrite <- p1p2.
  apply in_map_iff.
  exists (Wait v l, tx, p, O, C, id).
  auto.
  exists wt, ot, ct.
  left.
  assumption.
  reflexivity.
  assumption.
  }
  exists.
  {
  intros.
  apply upd_updl.
  exists (Wait v l, tx, p, O, C).
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
  intros.
  assert (tmp: L l0 = l0 /\
        P l0 = false /\
        ~ In (R l0) (X (L l0)) /\
        (h l0 <> Some 1%Z -> In l0 (concat (map oof T)))).
  {
  apply VLOCK.
  destruct (Z.eq_dec l0 ([[l]])).
  rewrite e.
  right.
  exists wt, ot ,ct.
  assumption.
  rewrite EQH in LOCK0.
  assumption.
  omega.
  }
  destruct tmp as (tm1,(tm2,(tm3,tm4))).
  split.
  assumption.
  split.
  assumption.
  split.
  assumption.
  unfold upd.
  destruct (Z.eq_dec l0 ([[l]])).
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
  assert (EQA: (x1,x2,x3,x4,x5) = (Wait v l, tx, p, O, C)).
  eapply unique_key_eq.
  apply INx.
  assumption.
  assumption.
  symmetry in EQA.
  inversion EQA.
  exists (Waiting4cond v l, x2,
       fun a : Z => if Z.eq_dec a ([[l]]) then Some Lock else p1 a,
       O1, C1, id).
  split.
  apply in_updl_eq.
  exists (Wait v l, tx, p, O, C).
  assumption.
  unfold oof.
  simpl.
  unfold oof in INl.
  simpl in INl.
  rewrite <- H3 in INl.
  rewrite O1eq in INl.
  destruct INl as [INl|INl].
  omega.
  assumption.
  exists (x1, x2, x3, x4, x5, x6).
  split.
  apply in_updl_neq.
  omega.
  assumption.
  assumption.
  }
  exists.
  {
  unfold upd.
  intros.
  destruct (Z.eq_dec l0 ([[l]])).
  reflexivity.
  apply VULOCK with wt0 ot0 ct0.
  rewrite EQH in ULOCK.
  assumption.
  omega.
  }
  exists.
  {
  intros.
  destruct (Z.eq_dec l0 ([[l]])) as [ll0|ll0].
  {
  rewrite ll0 in ULOCKED.
  rewrite LOCK in ULOCKED.
  destruct ULOCKED as [CO1|CO1].
  inversion CO1.
  inversion CO1.
  }
  assert (wot: wt0 = filterb L l0 (fun v : Z => length (filter
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) /\
    ot0 = filterb L l0 (count_occ Z.eq_dec (concat (map oof T))) /\
    ct0 = filterb L l0 (fold_left bagplus (map cof T) Cinv)).
  {
  apply WOT.
  rewrite EQH in ULOCKED.
  assumption.
  omega.
  }
  destruct wot as (wt0eq,(ot0eq,ct0eq)).
  split.
  rewrite <- filterb_updl_eq.
  assumption.
  intros.
  split.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec (Some ([[v]])) (Some v0)).
  inversion e.
  rewrite <- H0 in IN.
  rewrite <- IN in ll0.
  rewrite <- Lvl in ll0.
  contradiction.
  reflexivity.
  intros.
  assert (EQx': x' = (Wait v l, tx, p, O, C, id)).
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
  split.
  rewrite <- filterb_updl_obs_eq.
  assumption.
  intros.
  assert (EQx': x' = (Wait v l, tx, p, O, C, id)).
  apply in_elem with (l:=T).
  assumption.
  assumption.
  assumption.
  inversion EQx'.
  unfold oof.
  simpl.
  rewrite O1eq.
  simpl.
  destruct (Z.eq_dec ([[l]]) v0).
  rewrite <- e in IN.
  omega.
  reflexivity.
  rewrite bplus_comm.
  rewrite fold_left_f with (def:=bagdef).
  rewrite <- fold_left_move_m_eq with (def:=bagdef) (x1:=C1).
  assumption.
  apply canbag.
  assumption.
  apply defl_bagdef.
  trivial.
  trivial.
  apply in_map_iff.
  exists (Wait v l, tx, p, O, C, id).
  split.
  rewrite <- C1C2.
  reflexivity.
  assumption.
  reflexivity.
  apply canbag.
  trivial.
  }
  exists. 
  {
  unfold upd.
  intros.
  destruct (Z.eq_dec l0 ([[l]])) as [l0l|l0l].
  rewrite l0l.
  left.
  {
  rewrite <- EQW.
  rewrite <- EQO.
  assert (EQct: (filterb L ([[l]]) (fold_left bagplus (map cof
   (updl T id (Waiting4cond v l, tx, fun a : Z => if Z.eq_dec a ([[l]]) then Some Lock else p1 a,
   O1, C1, id))) (bagplus Cinv C2))) = ct).
  {
  rewrite cteq.
  rewrite bplus_comm.
  rewrite fold_left_f with (def:=bagdef).
  rewrite <- fold_left_move_m_eq with (def:=bagdef) (x1:=C1).
  reflexivity.
  apply canbag.
  assumption.
  apply defl_bagdef.
  trivial.
  trivial.
  apply in_map_iff.
  exists (Wait v l, tx, p, O, C, id).
  split.
  rewrite C1C2.
  reflexivity.
  assumption.
  reflexivity.
  apply canbag.
  trivial.
  }
  rewrite <- EQct.
  reflexivity.
  }
  right.
  assert (INA: In (I l0 (filterb L l0 (fun v : Z => length (filter (fun c : cmd =>
    ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
    (filterb L l0 (count_occ Z.eq_dec (concat (map oof T))))
    (filterb L l0 (fold_left bagplus (map cof T) Cinv)), l0) Ainv).
  {
  apply LINV.
  rewrite EQH in LOCK0.
  assumption.
  omega.
  assumption.
  }
  assert (EQwt: (filterb L l0 (fun v0 : Z => length (filter
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v0))) (map cmdof
    (updl T id (Waiting4cond v l, tx, fun a : Z => if Z.eq_dec a ([[l]]) then Some Lock else p1 a,
    O1, C1, id)))))) =  
    (filterb L l0 (fun v : Z => length (filter 
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
  rewrite Lvl in IN.
  omega.
  reflexivity.
  intros.
  assert (X':x' = (Wait v l, tx, p, O, C, id)).
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
  assert (EQot: (filterb L l0 (count_occ Z.eq_dec (concat (map oof T)))) =
    (filterb L l0 (count_occ Z.eq_dec (concat (map oof (updl T id
    (Waiting4cond v l, tx, fun a : Z => if Z.eq_dec a ([[l]]) then Some Lock else p1 a,
    O1, C1, id))))))).
  {
  apply filterb_updl_obs_eq.
  intros.
  assert (X':x' = (Wait v l, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  inversion X'.
  unfold oof.
  simpl.
  rewrite O1eq.
  simpl.
  destruct (Z.eq_dec ([[l]]) v0).
  rewrite <- e in IN.
  omega.
  reflexivity.
  }
  rewrite <- EQot.
  assert (EQct: (filterb L l0 (fold_left bagplus (map cof (updl T id
    (Waiting4cond v l, tx, fun a : Z => if Z.eq_dec a ([[l]]) then Some Lock else p1 a,
    O1, C1, id))) (bagplus Cinv C2))) =
    (filterb L l0 (fold_left bagplus (map cof T) Cinv))).
  {
  rewrite bplus_comm.
  rewrite fold_left_f with (def:=bagdef).
  rewrite <- fold_left_move_m_eq with (def:=bagdef) (x1:=C1).
  reflexivity.
  apply canbag.
  assumption.
  apply defl_bagdef.
  trivial.
  trivial.
  apply in_map_iff.
  exists (Wait v l, tx, p, O, C, id).
  split.
  rewrite C1C2.
  reflexivity.
  assumption.
  reflexivity.
  apply canbag.
  trivial.
  }
  rewrite EQct.
  assumption.
  }
  exists.
  Focus 2.
  trivial.
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x,(EQ,IN)).
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  unfold idof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec x6 id).
(* ==================== x6 = id ===========*)
  symmetry in EQ.
  inversion EQ.
  exists.
  trivial.
  exists.
  unfold weakest_pre_ct.
  assert (S:=SATp1).
  assumption.
  exists.
  intros.
  symmetry in W4COND.
  inversion W4COND.
  assumption.
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
  apply VALIDT in tmp.
  destruct tmp as (WF1,(WP1,(VOBS1,TR11))).
  exists.
  assumption.
  exists.
  assumption.
  exists.
  intros.
  destruct (Z.eq_dec ([[v0]]) ([[v]])).
  rewrite e.
  assumption.
  rewrite W4COND in WP1.
  apply sat_wait4cond in WP1.
  destruct WP1 as (pv0,(pl0,(lvl0,(prcl0,(prcv0,(Cm0,(Cmeq0,SAT0))))))).
  assert (NEQv0l: ([[v0]]) <> ([[l]])).
  {
  unfold not.
  intros.
  rewrite W4COND in IN.
  assert (tmp:=IN).
  apply VALIDT in tmp.
  destruct tmp as (WF',(WP',(VOBS',TR'))).
  apply sat_wait4cond in WP'.
  destruct WP' as (pv0',(pl0',(lvl0',(prcl0',(prcv0',(Cm0',(Cmeq0',SAT0'))))))).
  rewrite H in pv0'.
  assert (CO: fold_left phplus (map pof T) Pinv ([[l]]) = Some Cond).
  {
  apply fold_cond.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists p0.
  exists.
  apply in_map_iff.
  exists (Waiting4cond v0 l0, tx0, p0, O0, C0, id0).
  auto.
  assumption.
  }
  rewrite LOCKED in CO.
  inversion CO.
  }
  {
  apply VOBS1 in W4COND.
  assert (EQwt: (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some ([[v0]])))) (map cmdof T)) = 
    (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for (upd h ([[l]]) (Some 1%Z)) c0)
    (Some ([[v0]])))) (map cmdof (updl T id
    (Waiting4cond v l, tx, upd p1 ([[l]]) (Some Lock),
    O1, C1, id))))).
  {
  rewrite <- filter_updl_eq.
  apply filter_filter_eq.
  intros.
  apply waiting_for_upd_eq.
  omega.
  simpl.
  destruct (opZ_eq_dec (Some ([[v]])) (Some ([[v0]]))).
  inversion e.
  omega.
  reflexivity.
  intros.
  assert (X':x' = (Wait v l, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  inversion X'.
  unfold cmdof.
  simpl.
  destruct (opZ_eq_dec None (Some ([[v0]]))).
  inversion e.
  reflexivity.
  }
  rewrite <- EQwt.
  assert (EQot: (count_occ Z.eq_dec (concat (map oof T)) ([[v0]])) =
    (count_occ Z.eq_dec (concat (map oof (updl T id
    (Waiting4cond v l, tx, upd p1 ([[l]]) (Some Lock),
    O1, C1, id)))) ([[v0]]))).
  {
  apply count_updl_eq.
  intros.
  assert (X':x' = (Wait v l, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  inversion X'.
  unfold oof.
  simpl.
  rewrite O1eq.
  simpl.
  destruct (Z.eq_dec ([[l]]) ([[v0]])).
  omega.
  reflexivity.
  }
  rewrite <- EQot.
  assumption.
  }
  trivial.  
Qed.
Lemma Let_preserves_validity:
  forall h t id x c1 c2 tx
         (CMD: t id = Some (Let x c1 c2, tx))
         (VALID: validk t h),
    validk (upd t id (Some (c1, Let' x c2 tx))) h.
Proof.
  intros.
  unfold validk in VALID.
  destruct VALID as (T,(R,(I,(L,(M,(P,(X,(Pinv,(Ainv,(Cinv,(NODUPA,(Ainvl,(PHPDL,(PHPD,(BPE,(BPA,(BPT,(SATA,(PH2H,(AUT,(UNQ,(VLOCK,(VULOCK,(WOT,(LINV,(VALIDT,TR)))))))))))))))))))))))))).
  unfold validk.
  assert (tmp: exists (p : pheap) (O : list Z) (C : bag), In (Let x c1 c2, tx, p, O, C, id) T).
  apply AUT.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  exists (updl T id (c1, Let' x c2 tx, p, O, C, id)).
  exists R, I, L, M, P, X, Pinv, Ainv, Cinv.
  assert (tmp:=INT).
  apply VALIDT in tmp.
  destruct tmp as (WF,(WP,(VOBS,TR1))).
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
  assert (EQ_2: map (fun x => (pof x, idof x)) (updl T id (c1, Let' x c2 tx, p, O, C, id)) = map (fun x => (pof x, idof x)) T).
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
  assert (EQ_4: map cof (updl T id (c1, Let' x c2 tx, p, O, C, id)) = map cof T).
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
  assert (EQ_5: forall v, filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some v)))
         (map cmdof (updl T id (c1, Let' x c2 tx, p, O, C, id))) =
         filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some v)))
         (map cmdof T)).
  {
  intros.
  symmetry.
  apply filter_updl_eq.
  unfold cmdof.
  simpl.
  rewrite not_waiting_none.
  apply ifboneq.
  assumption.
  intros.
  assert (X':x' = (Let x c1 c2, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  inversion X'.
  unfold cmdof.
  simpl.
  apply ifboneq.
  }
  assert (EQ_6: forall l, filterb L l (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
         (map cmdof (updl T id (c1, Let' x c2 tx, p, O, C, id))))) =
         filterb L l (fun v : Z => length (filter
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
  apply ifboneq.
  assumption.
  intros.
  assert (X':x' = (Let x c1 c2, tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  inversion X'.
  unfold cmdof.
  simpl.
  apply ifboneq.
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
  unfold idof in EQ.
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
  assumption.
  }
  rewrite EQ_1.
  rewrite EQ_2.
  rewrite EQ_3.
  rewrite EQ_4.
  exists NODUPA, Ainvl, PHPDL,PHPD, BPE, BPA, BPT, SATA, PH2H.
  exists.
  unfold upd.
  split.
  intros.
  destruct (Z.eq_dec id0 id).
  inversion H.
  assert (tmp: exists (p : pheap) (O : list Z) (C : bag), In (Let x c1 c2, tx, p, O, C, id) T).
  apply AUT.
  assumption.
  destruct tmp as (p0,(O0,(C0,INT0))).
  exists p0, O0, C0.
  apply in_map_iff.
  exists (Let x c1 c2, tx, p0, O0, C0, id).
  simpl.
  destruct (Z.eq_dec id id).
  Focus 2.
  contradiction.
  rewrite e.
  assert (EQ1: (Let x c1 c2, tx, p0, O0, C0) = (Let x c1 c2, tx, p, O, C)).
  eapply unique_key_eq.
  apply INT0.
  assumption.
  assumption.
  inversion EQ1.
  auto.
  assert (tmp: exists (p : pheap) (o : list Z) (d : bag), In (c, tx0, p, o, d, id0) T).
  apply AUT.
  assumption.
  destruct tmp as (p0,(o0,(d0,ING0))).
  exists p0, o0, d0.
  apply in_map_iff.
  exists (c, tx0, p0, o0, d0, id0).
  simpl.
  destruct (Z.eq_dec id0 id).
  contradiction.
  auto.
  intros.
  destruct H as (p1,(o1,(d1,IN1))).
  unfold updl in IN1.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  destruct x1. destruct p0. destruct p0. destruct p0.
  simpl in EQ1.
  destruct (Z.eq_dec id0 id).
  destruct (Z.eq_dec z id).
  inversion EQ1.
  reflexivity.
  inversion EQ1.
  rewrite <- H4 in e.
  contradiction.
  destruct (Z.eq_dec z id).
  inversion EQ1.
  rewrite H5 in n.
  contradiction.
  inversion EQ1.
  apply AUT.
  exists p1, l, b.
  rewrite H0 in IN1.
  rewrite H1 in IN1.
  rewrite H4 in IN1.
  assumption.
  exists.
  replace (map idof (updl T id (c1, Let' x c2 tx, p, O, C, id))) with
          (map idof T).
  assumption.
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
  exists.
  assumption.
  exists.
  assumption.
  exists.
  intros.
  rewrite EQ_6.
  apply WOT.
  auto.
  exists.
  intros.
  rewrite EQ_6.
  apply LINV.
  assumption.
  assumption.
  exists.
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x00,(EQ,IN)).
  destruct x00 as (((((y1,y2),y3),y4),y5),y6).
  unfold pof in EQ. unfold oof in EQ. unfold cof in EQ.
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
  destruct c1;
  simpl;
  auto.
  auto.
  exists.
  unfold weakest_pre_ct in *.
  simpl in *.
  assert (WWP:=WP).
  apply sat_weak_imp with (a:=(fun z : Z =>
            weakest_pre c2 (weakest_pre_tx tx R I L M P X)
              (fun e : exp => subse x z (Datatypes.id e)) R I L M P X)).
  apply BPE.
  apply in_map_iff.
  exists (Let x c1 c2, tx, p, O, C, id).
  auto.
  assumption.
  intros.
  apply sat_pre_subs2.
  assumption.
  assumption.
  exists.
  intros.
  rewrite W4COND in WF1.
  inversion WF1.
  exists.
(* ==================== z <> id ===========*)
  inversion EQ.
  rewrite H0 in IN.
  rewrite H1 in IN.
  rewrite H2 in IN.
  rewrite H3 in IN.
  rewrite H4 in IN.
  rewrite H5 in IN.
  apply VALIDT in IN.
  destruct IN as (WF,(WP1,(VOBS1,TR11))).
  exists.
  assumption.
  exists.
  assumption.
  exists.
  intros.
  rewrite EQ_5.
  apply VOBS1 with l.
  assumption.
  trivial.
  trivial.
Qed.
Lemma Val_preserves_validity:
  forall h t id x z c tx
         (CMD: t id = Some (Val z, Let' x c tx))
         (VALID: validk t h),
    validk (upd t id (Some (subs c (subse x z), tx))) h.
Proof.
  intros.
  unfold validk in VALID.
  destruct VALID as (T,(R,(I,(L,(M,(P,(X,(Pinv,(Ainv,(Cinv,(NODUPA,(Ainvl,(PHPDL,(PHPD,(BPE,(BPA,(BPT,(SATA,(PH2H,(AUT,(UNQ,(VLOCK,(VULOCK,(WOT,(LINV,(VALIDT,TR)))))))))))))))))))))))))).
  unfold validk.
  assert (tmp: exists (p : pheap) (O : list Z) (C : bag), In (Val z, Let' x c tx, p, O, C, id) T).
  apply AUT.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  exists (updl T id (subs c (subse x z), tx, p, O, C, id)).
  exists R, I, L, M, P, X, Pinv, Ainv, Cinv.
  assert (tmp:=INT).
  apply VALIDT in tmp.
  destruct tmp as (WF,(WP,(VOBS,TR1))).
  unfold wellformed in WF.
  simpl in WF.
  destruct WF as (WF1,(WF2,WF3)).
  assert (EQ_1: map pof (updl T id (subs c (subse x z), tx, p, O, C, id)) = map pof T).
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val z, Let' x c tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  assert (EQ_2: map (fun x => (pof x, idof x)) (updl T id (subs c (subse x z), tx, p, O, C, id)) = map (fun x => (pof x, idof x)) T).
  {
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val z, Let' x c tx, p, O, C)).
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
  assert (EQ_3: map oof (updl T id (subs c (subse x z), tx, p, O, C, id)) = map oof T).
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val z, Let' x c tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  assert (EQ_4: map cof (updl T id (subs c (subse x z), tx, p, O, C, id)) = map cof T).
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val z, Let' x c tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  reflexivity.
  reflexivity.
  assert (EQ_5: forall v, filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for h c0) (Some v)))
          (map cmdof (updl T id (subs c (subse x z), tx, p, O, C, id))) =
          filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some v)))
          (map cmdof T)).
  {
  intros.
  symmetry.
  apply filter_updl_eq.
  unfold cmdof.
  simpl.
  rewrite not_waiting_none.
  apply ifboneq.
  apply not_waiting_subs.
  assumption.
  intros.
  assert (X':x' = (Val z, Let' x c tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  inversion X'.
  unfold cmdof.
  simpl.
  apply ifboneq.
  }
  assert (EQ_6: forall l, filterb L l (fun v : Z => length
         (filter (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) (Some v)))
         (map cmdof (updl T id (subs c (subse x z), tx, p, O, C, id))))) =
         filterb L l (fun v : Z => length
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
  apply ifboneq.
  apply not_waiting_subs.
  assumption.
  intros.
  assert (X':x' = (Val z, Let' x c tx, p, O, C, id)).
  apply in_elem with T.
  assumption.
  assumption.
  assumption.
  inversion X'.
  unfold cmdof.
  simpl.
  apply ifboneq.
  }
  assert (EQ_5': map (wof h) (updl T id (subs c (subse x z), tx, p, O, C, id)) = map (wof h) T).
  {
  unfold updl.
  rewrite map_map.
  rewrite map_list_upd.
  reflexivity.
  simpl.
  intros.
  destruct x0 as (((((c01,tx01),p01),O01),C01),id01).
  unfold idof in EQ.
  simpl in EQ.
  rewrite EQ in INx.
  assert (EQ1: (c01, tx01, p01, O01, C01) = (Val z, Let' x c tx, p, O, C)).
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
  inversion WF2.
  inversion WF2.
  }
  rewrite EQ_1.
  rewrite EQ_2.
  rewrite EQ_3.
  rewrite EQ_4.
  exists NODUPA, Ainvl, PHPDL, PHPD, BPE, BPA, BPT, SATA, PH2H.
  exists.
  unfold upd.
  split.
  intros.
  destruct (Z.eq_dec id0 id).
  inversion H.
  assert (tmp: exists (p : pheap) (O : list Z) (C : bag), In (Val z, Let' x c tx, p, O, C, id) T).
  apply AUT.
  assumption.
  destruct tmp as (p0,(O0,(C0,INT0))).
  exists p0, O0, C0.
  apply in_map_iff.
  exists (Val z, Let' x c tx, p0, O0, C0, id).
  simpl.
  destruct (Z.eq_dec id id).
  Focus 2.
  contradiction.
  rewrite e.
  assert (EQA: (Val z, Let' x c tx, p0, O0, C0) = (Val z, Let' x c tx, p, O, C)).
  eapply unique_key_eq.
  apply INT0.
  assumption.
  assumption.
  inversion EQA.
  auto.
  auto.
  assert (tmp: exists (p : pheap) (o : list Z) (d : bag), In (c0, tx0, p, o, d, id0) T).
  apply AUT.
  assumption.
  destruct tmp as (p0,(o0,(d0,ING0))).
  exists p0, o0, d0.
  apply in_map_iff.
  exists (c0, tx0, p0, o0, d0, id0).
  simpl.
  destruct (Z.eq_dec id0 id).
  contradiction.
  auto.
  intros.
  destruct H as (p1,(o1,(d1,IN1))).
  unfold updl in IN1.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  destruct x1. destruct p0. destruct p0. destruct p0.
  simpl in EQ1.
  destruct (Z.eq_dec id0 id).
  destruct (Z.eq_dec z0 id).
  inversion EQ1.
  reflexivity.
  inversion EQ1.
  rewrite <- H4 in e.
  contradiction.
  destruct (Z.eq_dec z0 id).
  inversion EQ1.
  rewrite H5 in n.
  contradiction.
  inversion EQ1.
  apply AUT.
  exists p1, l, b.
  rewrite H0 in IN1.
  rewrite H1 in IN1.
  rewrite H4 in IN1.
  assumption.
  exists.
  replace (map idof (updl T id (subs c (subse x z), tx, p, O, C, id))) with
          (map idof T).
  assumption.
  unfold updl.
  rewrite map_map.
  apply map_ext_in.
  intros.
  simpl.
  destruct a as (((((a1,a2),a3),a4),a5),a6).
  simpl.
  destruct (Z.eq_dec a6 id).
  assert (EQA: (a1,a2,a3,a4,a5) = (Val z, Let' x c tx, p, O, C)).
  eapply unique_key_eq.
  apply H.
  rewrite e.
  assumption.
  assumption.
  inversion EQA.
  rewrite e.
  reflexivity.
  reflexivity.
  exists.
  assumption.
  exists.
  assumption.
  exists.
  intros.
  rewrite EQ_6.
  apply WOT.
  assumption.
  exists.
  intros.
  rewrite EQ_6.
  apply LINV.
  assumption.
  assumption.
  exists.
  intros.
  unfold updl in ING.
  apply in_map_iff in ING.
  destruct ING as (x00,(EQ,IN)).
  destruct x00 as (((((y1,y2),y3),y4),y5),y6).
  unfold pof in EQ. unfold oof in EQ. unfold cof in EQ.
  simpl in EQ.
  destruct (Z.eq_dec y6 id).
(* ==================== y6 = id ===========*)
  rewrite e in IN.
  inversion EQ.
  rewrite <- H1.
  rewrite <- H2.
  rewrite <- H3.
  rewrite <- H4.
  assert (tmp: (y1, y2, y3, y4, y5) = (Val z, Let' x c tx, p, O, C)).
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
  destruct c;
  simpl;
  auto.
  simpl in *.
  apply not_waiting_subs.
  assumption.
  simpl in *.
  destruct WF2 as (WF2,WF4).
  split.
  apply not_waiting_subs.
  assumption.
  apply not_waiting_subs.
  assumption.
  assumption.
  exists.
  unfold weakest_pre_ct in *.
  assumption.
  exists.
  intros.
  eapply not_waiting_subs with (se:= subse x z) in WF2.
  rewrite W4COND in WF2.
  inversion WF2.
  trivial.
(* ==================== z <> id ===========*)
  inversion EQ.
  rewrite H0 in IN.
  rewrite H1 in IN.
  rewrite H2 in IN.
  rewrite H3 in IN.
  rewrite H4 in IN.
  rewrite H5 in IN.
  apply VALIDT in IN.
  destruct IN as (WF,(WP1,(VOBS1,TR2))).
  exists.
  assumption.
  exists.
  assumption.
  exists.
  intros.
  rewrite EQ_5.
  apply VOBS1 with l.
  assumption.
  trivial.
  trivial.
Qed.
Lemma Val_done_preserves_validity:
  forall h t id z
         (CMD: t id = Some (Val z, done))
         (VALID: validk t h),
    validk (upd t id None) h.
Proof.
  intros.
  unfold validk in VALID.
  destruct VALID as (T,(R,(I,(L,(M,(P,(X,(Pinv,(Ainv,(Cinv,(NODUPA,(Ainvl,(PHPDL,(PHPD,(BPE,(BPA,(BPT,(SATA,(PH2H,(AUT,(UNQ,(VLOCK,(VULOCK,(WOT,(LINV,(VALIDT,TR)))))))))))))))))))))))))).
  unfold validk.
  exists (filter (fun xx => negb (Z.eqb (idof xx) id)) T).
  exists R, I, L, M, P, X, Pinv, Ainv, Cinv.
  assert (tmp: exists p O C, In (Val z, done, p, O, C, id) T).
  apply AUT.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply VALIDT in tmp.
  destruct tmp as (WF,(WP,(VOBS,Tr))).
  simpl in WP.
  destruct WP as (pN,(CN,opO1O2)).
  inversion opO1O2.
  rename H into oN.
  rename H0 into o'O.
  apply Permutation_nil in PERM.
  rewrite PERM in *.
  rewrite pN in *.
  rewrite CN in *.
  assert (EQ_1: fold_left phplus (map pof (filter (fun xx => negb (idof xx =? id)%Z) T)) Pinv = 
                fold_left phplus (map pof T) Pinv).
  {
  symmetry.
  apply fold_left_map_eq.
  unfold neutral.
  intros.
  unfold negb in H.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct ((x6 =? id)%Z) eqn:x6id.
  apply Z.eqb_eq in x6id.
  assert (EQ1: (x1, x2, x3, x4, x5) = (Val z, done, emp knowledge, nil, empb)).
  eapply unique_key_eq.
  apply IN.
  rewrite x6id.
  assumption.
  assumption.
  inversion EQ1.
  unfold pof.
  simpl.
  rewrite phplus_emp.
  rewrite phplus_comm.
  rewrite phplus_emp.
  auto.
  apply phpdef_comm.
  apply phpdef_emp.  
  inversion H.
  }
  assert (EQ_2: concat (map oof (filter (fun xx => negb (idof xx =? id)%Z) T)) = concat (map oof T)).
  {
  apply concat_map_filter.
  intros.
  unfold negb in H.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct ((x6 =? id)%Z) eqn:x6id.
  apply Z.eqb_eq in x6id.
  assert (EQ1: (x1, x2, x3, x4, x5) = (Val z, done, emp knowledge, nil, empb)).
  eapply unique_key_eq.
  apply IN.
  rewrite x6id.
  assumption.
  assumption.
  inversion EQ1.
  reflexivity.
  inversion H.
  }
  assert (EQ_3: (fold_left bagplus (map cof (filter (fun xx => negb (idof xx =? id)%Z) T)) Cinv) = (fold_left bagplus (map cof T) Cinv)).
  {
  symmetry.
  apply fold_left_map_eq.
  intros.
  unfold negb in H.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl in *.
  destruct ((x6 =? id)%Z) eqn:x6id.
  apply Z.eqb_eq in x6id.
  assert (EQ1: (x1, x2, x3, x4, x5) = (Val z, done, emp knowledge, nil, empb)).
  eapply unique_key_eq.
  apply IN.
  rewrite x6id.
  assumption.
  assumption.
  inversion EQ1.
  unfold cof.
  simpl.
  unfold neutral.
  intros.
  rewrite bplus_emp.
  rewrite bplus_comm.
  rewrite bplus_emp.
  auto.
  inversion H.
  }
  assert (FIL: forall x, length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some x)))
    (map cmdof (filter (fun xx : cmd * context * pheap * list Z * bag * Z =>
    negb (idof xx =? id)%Z) T))) =
    length(filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some x))) (map cmdof T))).
  {
  intros.
  rewrite <- map_filter with (f2:=(fun xx => ifb (opZ_eq_dec (waiting_for_cond (cmdof xx)) (Some x)))).
  rewrite <- map_filter with (f2:=(fun xx => ifb (opZ_eq_dec (waiting_for_cond (cmdof xx)) (Some x)))).
  rewrite filter_filter with (f3:=(fun xx : cmd * context * pheap * list Z * bag * Z =>
         ifb (opZ_eq_dec (waiting_for_cond (cmdof xx)) (Some x)))).
  reflexivity.
  intros.
  simpl.
  destruct (negb (idof x0 =? id)%Z) eqn:x0id.
  simpl.
  rewrite Coq.Bool.Bool.andb_true_r.
  reflexivity.
  unfold negb in x0id.
  destruct (idof x0 =? id)%Z eqn:xid.
  apply Z.eqb_eq in xid.
  destruct x0 as (((((x1,x2),x3),x4),x5),x6).
  assert (EQ1: (x1, x2, x3, x4, x5) = (Val z, done, emp knowledge, nil, empb)).
  simpl in *.
  eapply unique_key_eq.
  apply INx.
  rewrite xid.
  assumption.
  assumption.
  inversion EQ1.
  unfold cmdof.
  simpl.
  rewrite ifboneq.
  apply Coq.Bool.Bool.andb_false_iff.
  auto.
  inversion x0id.
  intros.
  reflexivity.
  intros.
  reflexivity.
  }
  assert (FILB: forall l, filterb L l (fun v : Z => length
    (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof (filter (fun xx : cmd * context * pheap * list Z * bag * Z => negb (idof xx =? id)%Z) T)))) = 
    filterb L l (fun v : Z => length (filter
    (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T)))).
  {
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x l).
  reflexivity.
  destruct (Z.eq_dec (L x) l).
  Focus 2.
  reflexivity.
  apply FIL.
  }
  rewrite EQ_1.
  rewrite EQ_2.
  rewrite EQ_3.
  exists NODUPA, Ainvl.
  exists.
  {
  unfold defl in *.
  intros.
  apply PHPDL with id1 id2.
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
  
  assert (FIL2: forall x, length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some x)))
    (map cmdof (filter (fun xx : cmd * context * pheap * list Z * bag * Z =>
    negb (idof xx =? id)%Z) T))) =
    length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some x)))
    (map cmdof T))).
  {
  intros.
  rewrite <- map_filter with (f2:=(fun xx => ifb (opZ_eq_dec (waiting_for h (cmdof xx)) (Some x)))).
  rewrite <- map_filter with (f2:=(fun xx => ifb (opZ_eq_dec (waiting_for h (cmdof xx)) (Some x)))).
  rewrite filter_filter with (f3:=(fun xx : cmd * context * pheap * list Z * bag * Z =>
         ifb (opZ_eq_dec (waiting_for h (cmdof xx)) (Some x)))).
  reflexivity.
  intros.
  simpl.
  destruct (negb (idof x0 =? id)%Z) eqn:x0id.
  simpl.
  rewrite Coq.Bool.Bool.andb_true_r.
  reflexivity.
  unfold negb in x0id.
  destruct (idof x0 =? id)%Z eqn:xid.
  apply Z.eqb_eq in xid.
  destruct x0 as (((((x1,x2),x3),x4),x5),x6).
  assert (EQ1: (x1, x2, x3, x4, x5) = (Val z, done, emp knowledge, nil, empb)).
  simpl in *.
  eapply unique_key_eq.
  apply INx.
  rewrite xid.
  assumption.
  assumption.
  inversion EQ1.
  unfold cmdof.
  simpl.
  rewrite ifboneq.
  apply Coq.Bool.Bool.andb_false_iff.
  auto.
  inversion x0id.
  reflexivity.
  reflexivity.
  }
  exists.
  {
  intros.
  apply PHPD.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  apply filter_In in IN.
  destruct IN as (IN,NEQ).
  apply in_map_iff.
  exists x.
  auto.
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
  exists BPA, BPT, SATA, PH2H.
  exists.
  {
  intros.
  unfold upd.
  split.
  intros.
  destruct (Z.eq_dec id0 id).
  inversion H.
  apply AUT in H.
  destruct H as (p',(O'',(C',IN'))).
  exists p',O'',C'.
  apply filter_In.
  split.
  assumption.
  unfold negb.
  unfold idof.
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
  unfold idof in CO.
  simpl in CO.
  destruct (id =? id)%Z eqn:idid.
  inversion CO.
  apply neqb_neq in idid.
  contradiction.
  apply AUT.
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
  assumption.
  exists.
  assumption.
  exists.
  {
  intros.
  apply WOT in ULOCKED.
  destruct ULOCKED as (wteq,(oteq,cteq)).
  rewrite wteq.
  rewrite oteq.
  rewrite cteq.
  rewrite FILB.
  auto.
  }
  exists.
  {
  intros.
  rewrite FILB.
  apply LINV.
  assumption.
  assumption.
  }
  exists.
  {
  intros.
  apply filter_In in ING.
  destruct ING as (ING, idid0).
  unfold negb in idid0.
  unfold idof in idid0.
  simpl in idid0. 
  destruct (id0 =? id)%Z eqn:id0id.
  inversion idid0.
  apply neqb_neq in id0id.
  assert (tmp:=ING).
  apply VALIDT in tmp.
  destruct tmp as (WF1,(WP1,(VOBS1,TR11))).
  exists.
  assumption.
  exists.
  assumption.
  exists.
  {
  intros.
  rewrite FIL2.
  apply VOBS1 with l.
  assumption.
  }
  trivial.
  }
  trivial.
Qed.
Lemma Fork_preserves_validity:
  forall h t id id' c tx
         (CMD: t id = Some (Fork c, tx))
         (NIN: t id' = None)
         (VALID: validk t h),
    validk (upd (upd t id (Some (Val 0, tx))) id' (Some (c, done))) h.
Proof.
  intros.
  unfold validk in VALID.
  destruct VALID as (T,(R,(I,(L,(M,(P,(X,(Pinv,(Ainv,(Cinv,(NODUPA,(Ainvl,(PHPDL,(PHPD,(BPE,(BPA,(BPT,(SATA,(PH2H,(AUT,(UNQ,(VLOCK,(VULOCK,(WOT,(LINV,(VALIDT,TR)))))))))))))))))))))))))).
  assert (tmp: exists p O C, In (Fork c, tx, p, O, C, id) T).
  apply AUT.
  assumption.
  destruct tmp as (p,(O,(C,INT))).
  assert (tmp:=INT).
  apply VALIDT in tmp.
  destruct tmp as (WF,(WP,(VOBS,TR1))).
  unfold wellformed in WF.
  simpl in WF.
  destruct WF as (WF1,WF2).
  apply sat_fork in WP.
  destruct WP as (p1,(p2,(O1,(O2,(C1,(C2,(bp1,(bp2,(PHPDp1p2,(p1p2,(O1O2,(C1C2,(SAT1,(SAT2,TR12)))))))))))))).
  exists ((c,done,p2,O2,C2,id')::updl T id (Val 0, tx, p1, O1, C1, id)).
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
  assert (EQ_1: fold_left phplus (map pof ((c,done,p2,O2,C2,id')::updl T id (Val 0, tx, p1, O1, C1, id))) Pinv = 
                fold_left phplus (map pof T) Pinv).
  {
  simpl.
  rewrite phplus_comm.
  unfold pof at 2.
  simpl.
  apply fold_phplus_Fork with p1.
  apply pofs.
  assumption.
  assumption.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Fork c, tx, p, O, C, id).
  rewrite <- p1p2.
  auto.
  reflexivity.
  apply phpdef_comm.
  assumption.
  }
  assert (EQ_2: count_occ Z.eq_dec (concat (map oof ((c,done,p2,O2,C2,id')::updl T id (Val 0, tx, p1, O1, C1, id)))) = 
                count_occ Z.eq_dec (concat (map oof T))).
  {
  unfold oof at 1.
  simpl.
  symmetry.
  apply concat_move_eq with O O1.
  assumption.
  assumption.
  apply in_map_iff.
  exists (Fork c, tx, p, O, C, id).
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
  assert (EQ_3: fold_left bagplus (map cof ((c,done,p2,O2,C2,id')::updl T id (Val 0, tx, p1, O1, C1, id))) Cinv =
                fold_left bagplus (map cof T) Cinv).
  {
  unfold cof.
  simpl.
  rewrite bplus_comm.
  rewrite fold_left_f with (def:=bagdef).
  symmetry.
  apply fold_left_move_m_eq with (def:=bagdef) (x1:= C1) .
  apply canbag.
  assumption.
  apply defl_bagdef.
  trivial.
  trivial.
  rewrite <- C1C2.
  apply in_map_iff.
  exists (Fork c, tx, p, O, C, id).
  split.
  reflexivity.
  unfold elem.
  assumption.
  reflexivity.
  apply canbag.
  trivial.
  }
  assert (FILb: forall l, filterb L l (fun v : Z => length (filter
    (fun c0 : cmd => ifb (opZ_eq_dec (waiting_for_cond c0) (Some v)))
    (map cmdof ((c, done, p2, O2, C2, id') :: updl T id (Val 0, tx, p1, O1, C1, id))))) =
    filterb L l (fun v : Z => length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for_cond c) (Some v)))
    (map cmdof T)))).
  {
  intros.
  unfold filterb.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x l).
  reflexivity.
  destruct (Z.eq_dec (L x) l).
  Focus 2.
  reflexivity.
  simpl.
  unfold cmdof.
  simpl.
  rewrite not_waiting_cond_none.
  rewrite ifboneq.
  symmetry.
  unfold updl.
  rewrite map_map.
  apply filter_map_eq.
  intros.
  destruct x0 as (((((x1,x2),x3),x4),x5),x6).
  simpl.
  destruct (Z.eq_dec x6 id).
  rewrite e0 in IN.
  assert (EQ1: (x1, x2, x3, x4, x5) = (Fork c, tx, p, O, C)).
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
  assumption.
  }
  assert (EQFIL: forall v, (length (filter (fun c1 : cmd => ifb (opZ_eq_dec (waiting_for h c1) (Some v)))
    (map cmdof ((c, done, p2, O2, C2, id') :: updl T id (Val 0, tx, p1, O1, C1, id))))) =
    (length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some v)))
    (map cmdof T)))).
  {
  intros.
  simpl.
  unfold cmdof.
  simpl.
  rewrite not_waiting_none.
  rewrite ifboneq.
  symmetry.
  unfold updl.
  rewrite map_map.
  apply filter_map_eq.
  intros.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  simpl.
  destruct (Z.eq_dec x6 id).
  rewrite e in IN.
  assert (EQ1: (x1, x2, x3, x4, x5) = (Fork c, tx, p, O, C)).
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
  assumption.
  }
exists R, I, L, M, P, X, Pinv, Ainv, Cinv, NODUPA. 
  rewrite EQ_1.
  rewrite EQ_2.
  rewrite EQ_3.
  exists Ainvl.
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
  rewrite <- p1p2.
  apply PHPDL with id x6.
  omega.
  apply in_map_iff.
  exists (Fork c, tx, p, O, C, id).
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
  rewrite <- p1p2.
  apply PHPDL with id x6.
  omega.
  apply in_map_iff.
  exists (Fork c, tx, p, O, C, id).
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
  rewrite <- p1p2.
  apply PHPDL with id y6.
  omega.
  apply in_map_iff.
  exists (Fork c, tx, p, O, C, id).
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
  rewrite <- p1p2.
  apply PHPDL with id x6.
  omega.
  apply in_map_iff.
  exists (Fork c, tx, p, O, C, id).
  auto.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  apply phpdef_comm.
  assumption.
  simpl in EQ2.
  inversion EQ2.
  rewrite <- H2.
  apply PHPDL with x6 y6.
  omega.
  apply in_map_iff.
  exists (x1, x2, x3, x4, x5, x6).
  auto.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  auto.
  }
  exists.
  {
  simpl.
  intros.
  destruct IN as [EQ|IN].
  unfold pof in EQ.
  simpl in EQ.
  inversion EQ.
  rewrite <- EQ.
  apply phpdef_assoc_mon with p1.
  assumption.
  rewrite <- p1p2.
  apply PHPD.
  apply in_map_iff.
  exists (Fork c, tx, p, O, C, id).
  auto.
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
  apply phpdef_assoc_mon2 with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  rewrite <- p1p2.
  apply PHPD.
  apply in_map_iff.
  exists (Fork c, tx, p, O, C, id).
  auto.
  apply phpdef_comm.
  assumption.
  simpl in EQ.
  rewrite <- EQ.
  apply PHPD.
  apply in_map_iff.
  exists (y1, y2, y3, y4, y5, y6).
  auto.
  }
  exists.
  {
  simpl.
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
  exists BPA, BPT, SATA, PH2H.
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
  exists (Fork c, tx, p, O, C, id).
  split.
  simpl.
  destruct (Z.eq_dec id id).
  reflexivity.
  contradiction.
  assumption.
  apply AUT in H.
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
  apply AUT.
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
  apply AUT.
  exists p', O', C'.
  rewrite EQ' in IN'.
  assumption.
  }
  exists.
  {
  unfold idof.
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
  apply AUT.
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
  intros.
  apply VLOCK in LOCK.
  destruct LOCK as (ll,(plf,(nin,inl))).
  split.
  assumption.
  split.
  assumption.
  split.
  assumption.
  intros.
  apply inl in H.
  rewrite <- flat_map_concat_map in H.
  apply in_flat_map in H.
  destruct H as (x,(INx,EQx)).
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  destruct x as (((((x1,x2),x3),x4),x5),x6).
  destruct (Z.eq_dec x6 id).
  assert (EQ1: (x1, x2, x3, x4, x5) = (Fork c, tx, p, O, C)).
  simpl in *.
  eapply unique_key_eq.
  apply INx.
  rewrite e.
  assumption.
  assumption.
  inversion EQ1.
  rewrite H3 in EQx.
  unfold oof in EQx.
  simpl in EQx.
  apply in_perm with (l':=O1 ++ O2)(l1:=O1)(l2:=O2) in EQx.
  destruct EQx as [IN1|IN2].
  exists (Val 0, tx, p1, O1, C1, id).
  split.
  right.
  apply in_updl_eq.
  exists (Fork c, tx, p, O, C).
  assumption.
  assumption.
  exists (c, done, p2, O2, C2, id').
  split.
  left.
  reflexivity.
  assumption.
  assumption.
  reflexivity.
  exists (x1, x2, x3, x4, x5, x6).
  split.
  right.
  apply in_updl_neq.
  omega.
  assumption.
  assumption.
  }
  exists.
  assumption.
  exists.
  {
  intros.
  rewrite FILb.
  apply WOT.
  assumption.
  }
  exists.
  {
  intros.
  rewrite FILb.
  apply LINV.
  assumption.
  assumption.
  }
  exists.
  {
  intros.  
  destruct ING as [EQ1|ING1].
(* ==================== id0 = id' ===========*)
  symmetry in EQ1.
  inversion EQ1.
  exists.
  unfold wellformed.
  split.
  destruct c;
  assumption.
  trivial.
  exists.
  assumption.
  exists.
  {
  intros.
  apply not_waiting_cond_none in WF1.
  rewrite W4COND in WF1.
  inversion WF1.
  }
  trivial.
(* ==================== id0 in T ===========*)
  unfold updl in ING1.
  apply in_map_iff in ING1.
  destruct ING1 as (x,(EQ,IN)).
  
  destruct (Z.eq_dec (snd x) id).
  symmetry in EQ.
  inversion EQ.
  exists.
  unfold wellformed.
  auto.
  exists.
  assumption.
  exists.
  intros.
  inversion W4COND.
  trivial.
  rewrite EQ in IN.
  assert (tmp:=IN).
  apply VALIDT in tmp.
  destruct tmp as (WF1',(WP1',(VOBS1',TR11))).
  exists.
  assumption.
  exists.
  assumption.
  exists.
  intros.
  rewrite EQFIL.
  apply VOBS1' with l.
  assumption.
  trivial.
  }
  trivial.
Qed.
Lemma Cons_preserves_validity:
  forall h t id e tx a
         (VALIDK: validk t h)
         (CMD : t id = Some (Cons e, tx))
         (NON: h a = None),
    validk (upd t id (Some (Val 0, tx))) (upd h a (Some ([[e]]))).
Proof.
Admitted.
Lemma Lookup_preserves_validity:
  forall h t id e tx
         (VALIDK: validk t h)
         (CMD : t id = Some (Lookup e, tx)),
    validk (upd t id (Some (Val (lift 0%Z (h ([[e]]))), tx))) h.
Proof.
Admitted.
Lemma Mutate_preserves_validity:
  forall h t id e1 e2 tx
         (VALIDK: validk t h)
         (CMD : t id = Some (Mutate e1 e2, tx)),
    validk (upd t id (Some (Val 0, tx))) (upd h ([[e1]]) (Some ([[e2]]))).
Proof.
Admitted.
Lemma Newlock_preserves_validity:
  forall h t id l tx
         (VALIDK: validk t h)
         (CMD : t id = Some (Newlock, tx))
         (NON: h l = None),
    validk (upd t id (Some (Val l, tx))) (upd h l (Some 1%Z)).
Proof.
Admitted.
Lemma Newcond_preserves_validity:
  forall h t id v tx
         (VALIDK: validk t h)
         (CMD : t id = Some (Newcond, tx))
         (NON: h v = None),
    validk (upd t id (Some (Val v, tx))) (upd h v (Some 0%Z)).
Proof.
Admitted.
Lemma g_dupl_preserves_validity:
  forall h t id l tx
         (VALIDK: validk t h)
         (CMD : t id = Some (g_dupl l, tx)),
    validk (upd t id (Some (Val 0, tx))) h.
Proof.
Admitted.
Lemma g_chrg_preserves_validity:
  forall h t id v tx
         (VALIDK: validk t h)
         (CMD : t id = Some (g_chrg v, tx)),
    validk (upd t id (Some (Val 0, tx))) h.
Proof.
Admitted.
Lemma g_chrgu_preserves_validity:
  forall h t id v tx
         (VALIDK: validk t h)
         (CMD : t id = Some (g_chrgu v, tx)),
    validk (upd t id (Some (Val 0, tx))) h.
Proof.
Admitted.
Lemma g_dischu_preserves_validity:
  forall h t id v tx
         (VALIDK: validk t h)
         (CMD : t id = Some (g_dischu v, tx)),
    validk (upd t id (Some (Val 0, tx))) h.
Proof.
Admitted.
Lemma g_gain_preserves_validity:
  forall h t id v tx
         (VALIDK: validk t h)
         (CMD : t id = Some (g_gain v, tx)),
    validk (upd t id (Some (Val 0, tx))) h.
Proof.
Admitted.
Lemma g_gainu_preserves_validity:
  forall h t id v tx
         (VALIDK: validk t h)
         (CMD : t id = Some (g_gainu v, tx)),
    validk (upd t id (Some (Val 0, tx))) h.
Proof.
Admitted.
Lemma g_lose_preserves_validity:
  forall h t id v tx
         (VALIDK: validk t h)
         (CMD : t id = Some (g_lose v, tx)),
    validk (upd t id (Some (Val 0, tx))) h.
Proof.
Admitted.
Lemma g_loseu_preserves_validity:
  forall h t id v tx
         (VALIDK: validk t h)
         (CMD : t id = Some (g_loseu v, tx)),
    validk (upd t id (Some (Val 0, tx))) h.
Proof.
Admitted.
Lemma g_info_preserves_validity:
  forall h t id v tx
         (VALIDK: validk t h)
         (CMD : t id = Some (g_info v, tx)),
    validk (upd t id (Some (Val 0, tx))) h.
Proof.
Admitted.
Lemma g_infou_preserves_validity:
  forall h t id v tx
         (VALIDK: validk t h)
         (CMD : t id = Some (g_infou v, tx)),
    validk (upd t id (Some (Val 0, tx))) h.
Proof.
Admitted.

