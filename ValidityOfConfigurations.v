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
