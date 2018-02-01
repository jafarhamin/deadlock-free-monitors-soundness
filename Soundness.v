Require Import ZArith.
Require Import Coq.Init.Nat.
Require Import List.
Require Import Coq.Sorting.Permutation.
Require Import Util_Z.
Require Import Util_list.
Require Import Programs.
Require Import Assertions.
Require Import PrecedenceRelation.
Require Import WeakestPrecondition.
Require Import ProofRules.
Require Import ValidityOfConfigurations.
Require Import Wait4Graph.

Theorem initial_configuration_is_valid:
  forall I L M P X c id
         (WELLFORMED: wellformed_cmd c)
         (VERIFIED: exists R, proof_rule (Aobs nil) c (fun _ => Aobs nil) R I L M P X),
    validk (upd (emp (cmd * context)) id (Some (c,done))) (emp Z).
Proof.
  unfold proof_rule.
  unfold validk.
  intros.
  destruct VERIFIED as (R,VERIFIED).
  assert (SAT: sat (emp knowledge) (Some nil) (fun _ => O) (weakest_pre c (fun _ : Z => Aobs nil) Datatypes.id R I L M P X)). 
  apply VERIFIED.
  apply boundph_emp.
  simpl.
  split.
  reflexivity.
  split.
  reflexivity.
  apply fs_op.
  apply perm_nil.
  exists ((c,done,emp knowledge,nil,empb,id)::nil).
  exists R, I, L, M, P, X, (emp knowledge), nil, empb.
  simpl.
  exists.
  apply NoDup_nil.
  exists.
  {
  intros.
  contradiction.
  }
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
  intros.
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
  exists.
  {
  rewrite phplus_comm.
  rewrite phplus_emp.
  apply boundph_emp.
  apply phpdef_emp.
  }
  exists.
  reflexivity.
  exists.
  rewrite phplus_comm.
  rewrite phplus_emp.
  reflexivity.
  apply phpdef_emp.
  exists.
  split.
  intros.
  exists (emp knowledge), nil, empb.
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
  exists.
  apply NoDup_cons.
  unfold not.
  intros.
  inversion H.
  apply NoDup_nil.
  exists.
  unfold phplus.
  unfold pof.
  unfold emp.
  simpl.
  intros.
  destruct LOCK as [LOCK|LOCK].
  inversion LOCK.
  destruct LOCK as (wt,(ot,(ct,CO))).
  inversion CO.
  exists.
  unfold phplus.
  unfold pof.
  unfold emp.
  simpl.
  intros.
  inversion ULOCK.
  exists.
  simpl.
  intros.
  destruct ULOCKED as [CO|CO].
  inversion CO.
  inversion CO.
  exists.
  unfold phplus.
  unfold pof.
  unfold emp.
  simpl.
  intros.
  inversion NOTHELD.
  exists.
  intros.
  contradiction.
  exists.
  intros.
  unfold phplus in LKCN.
  unfold pof in LKCN.
  simpl in LKCN.
  destruct LKCN as [LK|LK];
  inversion LK.
  destruct LK as [LK|LK];
  inversion LK.
  inversion H.
  destruct LK as [LK|LK];
  inversion LK.
  destruct LK as (wt,(ot,(ct,LK))).
  destruct LK as [LK|LK];
  inversion LK.
  exists.
  intros.
  destruct ING as [EQ|FAL].
  Focus 2.
  contradiction.
  inversion EQ.
  rewrite <- H0.
  exists.
  unfold wellformed.
  simpl.
  auto.
  exists.
  assumption.
  exists.
  intros.
  rewrite W4COND in SAT.
  rewrite W4COND in WELLFORMED.
  simpl in *.
  apply sat_wait4cond with (tx:=done) (p:=emp knowledge) (L:=L) in SAT.
  destruct SAT as (CO,rest).
  inversion CO.
  trivial.
  trivial.
Qed.

Theorem valid_configuration_is_not_deadlock:
  forall t h (VALIDK: validk t h) (HAS_THREAD: exists id, t id <> None),
    exists id c (TID: t id = Some c), waiting_for h (fst c) = None.
Proof.
  unfold validk.
  intros.
  destruct VALIDK as (T,(R,(I,(L,(M,(P,(X,(Pinv,(Ainv,(Cinv,(NODUPA,(Ainvl,(PHPDL,(PHPD,(BPE,(BPA,(BPT,(SATA,(PH2H,(AUT,(UNQ,(VLOCK,(VULOCK,(WOT,(LINV,(OLC,(LCN,(VALIDT,TR)))))))))))))))))))))))))))).
  destruct (In_dec opZ_eq_dec None (map (wof h) T)) as [IN|NIN].
  apply in_map_iff in IN.
  destruct IN as (x,(w4,INT)).
  destruct x as (((((c,ct),p),O),C),id).
  simpl in *.
  exists id, (c, ct).
  exists.
  apply AUT.
  exists p, O, C.
  assumption.
  assumption.
  assert (GOAL: (map (fun x => (lift 0%Z (wof h x), oof x, idof x)) T) = nil).

  apply valid_graph_is_deadlock_free with (length T) (lift_f 0%Z R) L P X.
  rewrite map_map.
  simpl.
  assumption.
  apply length_map.
  {
  unfold Wait4Graph.one_ob.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x1,(x2,x3)).
  destruct x1 as (((((c,ct),p),O1),C),z1).
  simpl in *.
  inversion x2.
  unfold lift in H0.
  destruct (waiting_for h c) eqn:wfc.
  Focus 2.
  exfalso.
  apply NIN.
  apply in_map_iff.
  exists (c,ct,p,O1,C,z1).
  auto.
  assert (INT:=x3).

  apply VALIDT in x3.
  destruct x3 as (WF,(WP,(VOBS,TR1))).
  assert (WFC:=wfc).
  unfold waiting_for in WFC;
  destruct c;
  inversion WFC.
  {
  rewrite map_map.
  simpl.
  apply count_occ_In.
  assert (tmp: L ([[l]]) = ([[l]]) /\
        P ([[l]]) = false /\
        nexc ([[l]]) R X L /\
        (h ([[l]]) <> Some 1%Z -> In ([[l]]) (concat (map oof T)))).
  {
  apply VLOCK.
  apply sat_wait4lock0 in WP.
  destruct WP as (WP,PRC).
  destruct WP as [pl|pl].
  apply phplus_fold_lock.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Waiting4lock l, ct, p, O1, C, z1).
  auto.
  assumption.
  destruct pl as (wt',(ot',(ct',pl))).
  right.
  exists wt', ot', ct'.
  apply fold_locked.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Waiting4lock l, ct, p, O1, C, z1).
  auto.
  assumption.
  }

  destruct tmp as (tm1,(tm2,(tm3,tm4))).
  unfold wof.
  simpl.
  destruct (opZ_eq_dec (h ([[l]])) (Some 1%Z)).
  inversion WFC.
  simpl.
  apply tm4.
  assumption.
  }

  assert (SOB': R ([[v]]) <> None).
  {
  apply LCN.
  left.
  assert (tmp:=INT).
  apply VALIDT in tmp.
  destruct tmp as (WF1,(SAT1,rest1)).
  apply sat_wait4cond in SAT1.
  destruct SAT1 as (pv,rest).
  apply fold_cond;
  try tauto.
  apply pofs.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Waiting4cond v l, ct, p, O1, C, z1).
  tauto.
  assumption.
  }

  {
  assert (SOB: safe_obs0 ([[v]]) (length (filter (fun c : cmd =>
                ifb (opZ_eq_dec (waiting_for h c) (Some ([[v]]))))
               (map cmdof T)))
         (count_occ Z.eq_dec (concat (map oof T)) ([[v]])) R L P X).
  apply VOBS with l.
  reflexivity.
  unfold safe_obs0 in SOB.
  apply SOB in SOB'.
  apply Coq.Bool.Bool.andb_true_iff in SOB'.
  destruct SOB' as (SOB1,SOB2).

  unfold one_ob in SOB1.
  apply Coq.Bool.Bool.orb_true_iff in SOB1.
  destruct SOB1 as [SOB1|SOB1].
  apply Nat.eqb_eq in SOB1.
  assert (tmp: In (Waiting4cond v l) (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some ([[v]])))) (map cmdof T))).
  apply filter_In.
  split.
  apply in_map_iff.
  exists (Waiting4cond v l, ct, p, O1, C, z1).
  auto.
  unfold ifb.
  simpl.
  destruct (opZ_eq_dec (Some ([[v]])) (Some ([[v]]))).
  reflexivity.
  contradiction.
  destruct (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some ([[v]])))) (map cmdof T)).
  inversion tmp.
  inversion SOB1.
  apply Nat.ltb_lt in SOB1.
  unfold oof in SOB1.
  rewrite map_map.
  assumption.
  }
  }
  {
  unfold Wait4Graph.spare_ob.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x1,(x2,x3)).
  destruct x1 as (((((c,ct),p),O1),C),z1).
  simpl in *.
  inversion x2.
  unfold lift in H0.
  destruct (waiting_for h c) eqn:wfc.
  Focus 2.
  exfalso.
  apply NIN.
  apply in_map_iff.
  exists (c,ct,p,O1,C,z1).
  auto.
  assert (INT:=x3).
  apply VALIDT in x3.
  destruct x3 as (WF,(WP,(VOBS,TR1))).
  assert (WFC:=wfc).
  unfold waiting_for in WFC;
  destruct c;
  inversion WFC.
  {
  apply sat_wait4lock0 in WP.
  destruct WP as (WP,PRC).
  assert (tmp: L ([[l]]) = ([[l]]) /\ P ([[l]]) = false /\ nexc ([[l]]) R X L /\
        (h ([[l]]) <> Some 1%Z -> In ([[l]]) (concat (map oof T)))).
  {
  apply VLOCK.
  destruct WP as [pl|pl].
  apply phplus_fold_lock.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Waiting4lock l, ct, p, O1, C, z1).
  auto.
  assumption.
  destruct pl as (wt',(ot',(ct',pl))).
  right.
  exists wt', ot', ct'.
  apply fold_locked.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Waiting4lock l, ct, p, O1, C, z1).
  auto.
  assumption.
  }

  destruct tmp as (Lll,(Plf,NINX)).
  unfold wof in H0.
  simpl in H0.
  destruct (opZ_eq_dec (h ([[l]])) (Some 1%Z)).
  inversion WFC.
  rewrite <- H0 in Po.
  rewrite Po in Plf.
  inversion Plf.
  }
  {
  assert (SOB: safe_obs0 ([[v]])
         (length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some ([[v]])))) (map cmdof T)))
         (count_occ Z.eq_dec (concat (map oof T)) ([[v]])) R L P X).
  apply VOBS with l.
  reflexivity.
  unfold safe_obs in SOB.
  apply Coq.Bool.Bool.andb_true_iff in SOB.
  destruct SOB as (SOB1,SOB2).
  apply Coq.Bool.Bool.andb_true_iff in SOB2.
  destruct SOB2 as (SOB2,SOB3).

  apply Coq.Bool.Bool.orb_true_iff in SOB2.
  destruct SOB2 as [SOB2|SOB2].
  simpl in H0.
  rewrite <- H0 in Po.
  rewrite Po in SOB2.
  inversion SOB2.
  unfold spare_ob in SOB2.
  apply Coq.Bool.Bool.orb_true_iff in SOB2.
  destruct SOB2 as [SOB2|SOB2].
  apply Nat.eqb_eq in SOB2.
  assert (tmp: In (Waiting4cond v l) (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some ([[v]])))) (map cmdof T))).
  apply filter_In.
  split.
  apply in_map_iff.
  exists (Waiting4cond v l, ct, p, O1, C, z1).
  auto.
  simpl.
  destruct (opZ_eq_dec (Some ([[v]])) (Some ([[v]]))).
  reflexivity.
  contradiction.
  destruct (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some ([[v]])))) (map cmdof T)).
  inversion tmp.
  inversion SOB2.
  apply Nat.ltb_lt in SOB2.
  unfold oof in *.
  unfold wof in *.
  rewrite map_map.
  rewrite map_map.
  simpl in *.
  rewrite <- length_filter_count with (C:=cmd)(f1:= fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some ([[v]]))))(f2:=cmdof).
  assumption.
  unfold cmdof.
  intros.
  destruct (opZ_eq_dec (waiting_for h (fst (fst (fst (fst (fst a))))))
             (Some ([[v]]))).
  rewrite e.
  reflexivity.
  inversion F1F2a.
  unfold cmdof.
  intros.
  destruct (opZ_eq_dec (waiting_for h (fst (fst (fst (fst (fst a))))))
             (Some ([[v]]))).
  inversion F1F2a.
  unfold not.
  intros.
  apply n.
  unfold lift in H.
  destruct (waiting_for h (fst (fst (fst (fst (fst a)))))) eqn:wfa.
  rewrite H.
  reflexivity.
  exfalso.
  apply NIN.
  apply in_map_iff.
  destruct a as (((((xx1,xx2),xx3),xx4),xx5),xx6).
  exists (xx1,xx2,xx3,xx4,xx5,xx6).
  auto.
  assert (SOB': R ([[v]]) <> None).
  {
  apply LCN.
  left.
  assert (tmp:=INT).
  apply VALIDT in tmp.
  destruct tmp as (WF1,(SAT1,rest1)).
  apply sat_wait4cond in SAT1.
  destruct SAT1 as (pv,rest).
  apply fold_cond;
  try tauto.
  apply pofs.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Waiting4cond v l, ct, p, O1, C, z1).
  tauto.
  assumption.
  }
  assumption.
  }
  }
  {
  unfold Wait4Graph.own_ob.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x1,(x2,x3)).
  destruct x1 as (((((c,ct),p),O1),C),z1).
  simpl in *.
  inversion x2.
  unfold lift in H0.
  destruct (waiting_for h c) eqn:wfc.
  Focus 2.
  exfalso.
  apply NIN.
  apply in_map_iff.
  exists (c,ct,p,O1,C,z1).
  auto.
  assert (INT:=x3).
  apply VALIDT in x3.
  destruct x3 as (WF,(WP,(VOBS,TR1))).
  assert (WFC:=wfc).

  unfold waiting_for in WFC;
  destruct c;
  inversion WFC.
  unfold wof in H0.
  simpl in H0.
  destruct (opZ_eq_dec (h ([[l]])) (Some 1%Z)).
  inversion WFC.
  {
  apply sat_wait4lock0 in WP.
  destruct WP as (WP,PRC).

  assert (tmp: L ([[l]]) = ([[l]]) /\ P ([[l]]) = false /\ nexc ([[l]]) R X L /\
        (h ([[l]]) <> Some 1%Z -> In ([[l]]) (concat (map oof T)))).
  {
  apply VLOCK.
  destruct WP as [pl|pl].
  apply phplus_fold_lock.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Waiting4lock l, ct, p, O1, C, z1).
  auto.
  assumption.
  destruct pl as (wt',(ot',(ct',pl))).
  right.
  exists wt', ot', ct'.
  apply fold_locked.
  apply pofs.
  assumption.
  assumption.
  assumption.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Waiting4lock l, ct, p, O1, C, z1).
  auto.
  assumption.
  }

  assert (LK: fold_left phplus (map pof T) Pinv ([[l]]) = Some Lock \/
    exists wt ot ct, fold_left phplus (map pof T) Pinv ([[l]]) = Some (Locked wt ot ct)).
  {
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
  exists (Waiting4lock l, ct, p, O1, C, z1).
  tauto.
  assumption.
  }

  assert (RlN: R ([[l]]) <> None).
  {
  apply LCN.
  assert (tmp1:=INT).
  apply VALIDT in tmp1.
  destruct tmp1 as (WF1,(SAT1,rest1)).
  apply sat_wait4lock0 in SAT1.
  destruct SAT1 as (pv,rest).
  right.
  destruct LK.
  left.
  assumption.
  right.
  destruct H as (wt1,(ot1,(ct1,LKD))).
  exists wt1, ot1, ct1.
  left.
  assumption.
  }
  destruct tmp as (Lll,(Plf,(NINX,LOBS))).
  simpl in H0.
  rewrite <- H0 in INX.
  unfold nexc in NINX.
  apply NINX in RlN.
  contradiction.
  }
  {
  assert (SOB: safe_obs0 ([[v]])
         (length (filter (fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some ([[v]])))) (map cmdof T)))
         (count_occ Z.eq_dec (concat (map oof T)) ([[v]])) R L P X).
  apply VOBS with l.
  reflexivity.
  unfold safe_obs in SOB.
  apply Coq.Bool.Bool.andb_true_iff in SOB.
  destruct SOB as (SOB1,SOB2).
  apply Coq.Bool.Bool.andb_true_iff in SOB2.
  destruct SOB2 as (SOB2,SOB3).

  apply Coq.Bool.Bool.orb_true_iff in SOB3.
  destruct SOB3 as [SOB3|SOB3].
  simpl in H0.
  rewrite H0 in SOB3.
  destruct (in_dec Z.eq_dec (lift_f 0%Z R o) (X (L o))).
  inversion SOB3.
  contradiction.
  unfold own_ob in SOB3.
  apply Nat.leb_le in SOB3.
  unfold oof in *.
  unfold wof in *.
  rewrite map_map.
  rewrite map_map.
  simpl in *.

  rewrite <- length_filter_count with (C:=cmd)(f1:= fun c : cmd => ifb (opZ_eq_dec (waiting_for h c) (Some ([[v]]))))(f2:=cmdof).
  assumption.
  unfold cmdof.
  intros.
  destruct (opZ_eq_dec (waiting_for h (fst (fst (fst (fst (fst a))))))
             (Some ([[v]]))).
  rewrite e.
  reflexivity.
  inversion F1F2a.
  unfold cmdof.
  intros.
  destruct (opZ_eq_dec (waiting_for h (fst (fst (fst (fst (fst a))))))
             (Some ([[v]]))).
  inversion F1F2a.
  unfold not.
  intros.
  apply n.
  unfold lift in H.
  destruct (waiting_for h (fst (fst (fst (fst (fst a)))))) eqn:wfa.
  rewrite H.
  reflexivity.
  exfalso.
  apply NIN.
  apply in_map_iff.
  destruct a as (((((xx1,xx2),xx3),xx4),xx5),xx6).
  exists (xx1,xx2,xx3,xx4,xx5,xx6).
  auto.
  assert (SOB': R ([[v]]) <> None).
  {
  apply LCN.
  left.
  assert (tmp:=INT).
  apply VALIDT in tmp.
  destruct tmp as (WF1,(SAT1,rest1)).
  apply sat_wait4cond in SAT1.
  destruct SAT1 as (pv,rest).
  apply fold_cond;
  try tauto.
  apply pofs.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Waiting4cond v l, ct, p, O1, C, z1).
  tauto.
  assumption.
  }
  assumption.
  }
  }
  {
  intros.
  apply in_map_iff in ING.
  destruct ING as (x1,(x2,x3)).
  destruct x1 as (((((c,ct),p),O1),C),z1).
  unfold oof in x2.
  unfold wof in x2.
  simpl in *.
  inversion x2.
  unfold lift in H0.
  destruct (waiting_for h c) eqn:wfc.
  Focus 2.
  exfalso.
  apply NIN.
  apply in_map_iff.
  exists (c,ct,p,O1,C,z1).
  auto.
  simpl.
  assert (INT:=x3).
  apply VALIDT in x3.
  destruct x3 as (WF,(WP,(VOBS,TR1))).
  assert (WFC:=wfc).
  unfold waiting_for in WFC;
  destruct c;
  inversion WFC.
  destruct (opZ_eq_dec (h ([[l]])) (Some 1%Z));
  inversion WFC.
  {
  apply sat_wait4lock0 in WP.
  destruct WP as (WP,PRC).
  rewrite <- H1.
  unfold prc0 in PRC.
  apply PRC.

  assert (LK: fold_left phplus (map pof T) Pinv ([[l]]) = Some Lock \/
    exists wt ot ct, fold_left phplus (map pof T) Pinv ([[l]]) = Some (Locked wt ot ct)).
  {
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
  exists (Waiting4lock l, ct, p, O1, C, z1).
  tauto.
  assumption.
  }

  assert (DOM: dom_f R (([[l]]) :: O1)).
  {
  unfold dom_f.
  simpl.
  intros.
  destruct H as [EQ|IN].
  rewrite <- EQ.
  apply LCN.
  right.
  destruct LK.
  left.
  assumption.
  right.
  destruct H as (wt1,(ot1,(ct1,LKD))).
  exists wt1, ot1, ct1.
  left.
  assumption.
  apply LCN.
  apply OLC.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists (Waiting4lock l, ct, p, O1, C, z1).
  tauto.
  }
  assumption.
  }
  {
  apply sat_wait4cond in WP.
  rewrite <- H1.
  destruct WP as (pv,(pl,(lv,(prc1,(prc2,rest))))).
  unfold prc0 in prc2.
  apply prc2.
  assert (DOM: dom_f R (([[v]]) :: O1)).
  {
  unfold dom_f.
  simpl.
  intros.
  destruct H as [EQ|IN].
  rewrite <- EQ.
  apply LCN.
  left.
  apply fold_cond;
  try tauto.
  apply pofs.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Waiting4cond v l, ct, p, O1, C, z1).
  tauto.
  assumption.
  apply LCN.
  apply OLC.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  exists (Waiting4cond v l, ct, p, O1, C, z1).
  tauto.
  }
  assumption.
  }
  }
  {
  destruct HAS_THREAD as (id,tid).
  destruct (t id) eqn:TID.
  Focus 2.
  destruct tid.
  reflexivity.
  destruct p.
  apply AUT in TID.
  destruct TID as (p,(O,(C,INT))).
  destruct T.
  inversion INT.
  inversion GOAL.
  }
Qed.


(*
Hint Resolve Let_preserves_validity.
Hint Resolve Val_preserves_validity.
Hint Resolve Val_done_preserves_validity.
Hint Resolve Fork_preserves_validity.
Hint Resolve Cons_preserves_validity.
Hint Resolve Cons_preserves_validity.
Hint Resolve Lookup_preserves_validity.
Hint Resolve Mutate_preserves_validity.
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
Hint Resolve g_dupl_preserves_validity.
Hint Resolve g_initl_preserves_validity.
Hint Resolve g_chrg_preserves_validity.
Hint Resolve g_chrgu_preserves_validity.
Hint Resolve g_disch_preserves_validity.
Hint Resolve g_dischu_preserves_validity.
Hint Resolve g_gain_preserves_validity.
Hint Resolve g_gainu_preserves_validity.
Hint Resolve g_lose_preserves_validity.
Hint Resolve g_loseu_preserves_validity.
Hint Resolve g_info_preserves_validity.
Hint Resolve g_infou_preserves_validity.

Theorem steps_preserve_validity:
  forall t h t' h' 
         (VALIDK: validk t h) (STEP: red t h t' h'),
    validk t' h'.
Proof.
  intros.
  induction STEP;
  eauto.
Qed.
*)
