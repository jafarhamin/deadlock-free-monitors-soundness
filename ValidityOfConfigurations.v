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
  exists (T: list (cmd * context * pheap * list Z * bag * Z)) (R: Z -> option Z) (I: Z -> inv) (L: Z -> Z) (M: Z -> bool) (P: Z -> bool) (X: Z -> list Z)
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
                   L l = l /\ P l = false /\ nexc l R X L /\ (h l <> Some 1%Z -> In l (concat (map oof T))))
         (VULOCK: forall l wt ot ct (ULOCK: (fold_left phplus (map pof T) Pinv) l = Some (Ulock wt ot ct)), h l = Some 1%Z)
         (WOT: forall l wt ot ct (ULOCKED: (fold_left phplus (map pof T) Pinv) l = Some (Locked wt ot ct) \/ (fold_left phplus (map pof T) Pinv) l = Some (Ulock wt ot ct)), 
                  wt = filterb L l (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))) /\
                  ot = filterb L l (count_occ Z.eq_dec (concat (map oof T))) /\
                  ct = filterb L l (fold_left bagplus (map cof T) Cinv))
         (LINV: forall l (LOCK: (fold_left phplus (map pof T) Pinv) l = Some Lock) (NOTHELD: h l = Some (1%Z)), In ((I l) 
           (filterb L l (fun v => length (filter (fun c => ifb (opZ_eq_dec (waiting_for_cond c) (Some v))) (map cmdof T))))
           (filterb L l (count_occ Z.eq_dec (concat (map oof T))))
           (filterb L l (fold_left bagplus (map cof T) Cinv)),l) Ainv)
         (OLC: forall o (IN: In o (concat (map oof T))),
                 fold_left phplus (map pof T) Pinv o = Some Cond \/ 
                 fold_left phplus (map pof T) Pinv o = Some Lock \/
                 exists wt ot ct,
                 fold_left phplus (map pof T) Pinv o = Some (Locked wt ot ct) \/ 
                 fold_left phplus (map pof T) Pinv o = Some (Ulock wt ot ct))
         (LCN: forall o (LKCN: fold_left phplus (map pof T) Pinv o = Some Cond \/ 
                               fold_left phplus (map pof T) Pinv o = Some Lock \/
                               exists wt ot ct,
                               fold_left phplus (map pof T) Pinv o = Some (Locked wt ot ct) \/ 
                               fold_left phplus (map pof T) Pinv o = Some (Ulock wt ot ct)),
                 R o <> None)
         (VALIDT: forall id c tx p O C (ING: In (c,tx,p,O,C,id) T), exists
           (WF: wellformed (c,tx))
           (WP: sat p (Some O) C (weakest_pre_ct (c,tx) R I L M P X))
           (VOBS: forall v l (W4COND: c = Waiting4cond v l),
              safe_obs0 (eval v) (length (filter (fun c => ifb (opZ_eq_dec (waiting_for h c) (Some (eval v)))) (map cmdof T)))
                (count_occ Z.eq_dec (concat (map oof T)) (eval v)) R L P X), True), True.

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
