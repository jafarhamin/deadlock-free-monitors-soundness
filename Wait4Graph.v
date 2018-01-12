Require Import List.
Require Import ZArith.
Require Import Coq.Init.Nat.
Require Import Util_Z.
Require Import Util_list.
Require Import PrecedenceRelation.

Set Implicit Arguments.

Definition node_dec (n1 n2: (Z * list Z * Z)) : {n1 = n2} + {n1 <> n2}.
Proof.
  decide equality.
  apply Z_eq_dec.
  decide equality.
  apply list_eq_dec.
  apply Z_eq_dec.
  apply Z_eq_dec.
Qed.

Definition one_ob (G: list (Z * list Z * Z)) o :=
  lt 0 (count_occ Z.eq_dec (concat (map (fun x => snd (fst x)) G)) o).

Definition spare_ob (G: list (Z * list Z * Z)) o :=
  lt (count_occ Z_eq_dec (map (fun x => fst (fst x)) G) o) (count_occ Z.eq_dec (concat (map (fun x => snd (fst x)) G)) o).

Definition own_ob (G: list (Z * list Z * Z)) o :=
  le (count_occ Z_eq_dec (map (fun x => fst (fst x)) G) o) (count_occ Z.eq_dec (concat (map (fun x => snd (fst x)) G)) o).

Definition list_Z_dec (lz1 lz2: (list Z * Z)) : {lz1 = lz2} + {lz1 <> lz2}.
Proof.
  decide equality.
  apply Z_eq_dec.
  apply list_eq_dec.
  apply Z_eq_dec.
Qed.

Lemma count_remove_list_Z:
  forall (G:list (list Z * Z)) r R t
         (UNQ: NoDup (map snd G))
         (IN: In (R,t) G),
    count_occ Z.eq_dec (concat (map fst G)) r =
    (count_occ Z.eq_dec R r + 
    count_occ Z.eq_dec (concat (map fst (remove list_Z_dec (R,t) G))) r)%nat.
Proof.
  induction G.
  simpl.
  intros.
  contradiction.
  simpl.
  intros.
  destruct IN as [aa|IN].
  rewrite aa.
  unfold id.
  simpl.
  destruct (list_Z_dec (R,t) (R,t)).
  Focus 2.
  contradiction.
  rewrite <- count_app.
  assert (tmp: count_occ Z.eq_dec (concat(map fst G)) r =
    count_occ Z.eq_dec (concat (map fst (remove list_Z_dec (R, t) G))) r).
  destruct (In_dec list_Z_dec (R,t) G).
  rewrite aa in UNQ.
  simpl in *.
	assert (tmp: ~In t (map snd G) /\ NoDup (map snd G)).
  apply NoDup_cons_iff.
  assumption.
  destruct tmp as (tmp1,tmp2).
  unfold not in tmp1.
  exfalso.
  apply tmp1.
  apply in_map_iff.
  exists (R,t).
  split.
  reflexivity.
  assumption.
  rewrite <- count_remove_nin with (l:=G) (a:=(R,t)) (dec:=list_Z_dec).
  reflexivity.
  assumption.
  omega.
  destruct (list_Z_dec (R, t) a).
  rewrite <- e in UNQ.
  simpl in *.
  assert (tmp: ~In t (map snd G) /\ NoDup (map snd G)).
  apply NoDup_cons_iff.
  assumption.
  destruct tmp as (tmp1,tmp2).
  unfold not in tmp1.
  exfalso.
  apply tmp1.
  apply in_map_iff.
  exists (R,t).
  split.
  reflexivity.
  assumption.
  simpl.
  rewrite <- count_app.
  rewrite <- count_app.
  assert (tmp: count_occ Z.eq_dec (concat (map fst G)) r =
    count_occ Z.eq_dec R r + count_occ Z.eq_dec (concat (map fst (remove list_Z_dec (R, t) G))) r).
  apply IHG.
  destruct a.
  apply proj2 with (~ In z (map snd G)).
  apply NoDup_cons_iff.
  assumption.
  assumption.
  omega.
Qed.

Lemma two_O:
  forall (G:list (list Z * Z)) r R t
         (UNQ: NoDup (map snd G))
         (LT1: (1 < count_occ Z.eq_dec (concat (map fst G)) r)%nat)
         (IN: In (R,t) G)
         (OCC: (count_occ Z.eq_dec R r <= 1)%nat),
    exists t' R', t <> t' /\ In r R' /\ In (R',t') G.
Proof.
  intros.
  destruct (count_occ Z.eq_dec (concat (map fst G)) r) eqn:CNT.
  inversion LT1.
  destruct n.
  inversion LT1.
  inversion H0.
  assert (tmp: S (S n) =
    (count_occ Z.eq_dec R r + 
    count_occ Z.eq_dec (concat (map fst (remove list_Z_dec (R,t) G))) r)%nat).
  rewrite <- CNT.
  apply count_remove_list_Z.
  assumption.
  assumption.
  assert (tmp2: (1 <= count_occ Z.eq_dec (concat (map fst (remove list_Z_dec (R, t) G))) r)%nat).
  omega.
  assert (tmp3: In r (concat (map fst (remove list_Z_dec (R, t) G)))).
  apply <- count_occ_In.
  assert (tmp4: count_occ Z.eq_dec (concat (map fst (remove list_Z_dec (R, t) G))) r > 0).
  omega.
  apply tmp4.
  rewrite <- flat_map_concat_map in tmp3.
  apply in_flat_map in tmp3.
  destruct tmp3 as (x, (INx, INr)).
  destruct x.
  exists z, l.
  split.
  unfold not.
  intros tk.
  rewrite <- tk in *.
  assert (tmp1:=IN).
  apply unq_nin with (dec:=list_Z_dec) in tmp1.
  unfold not in tmp1.
  exfalso.
  apply tmp1.
  exists l.
  assumption.
  assumption.
  split.
  assumption.
  apply in_remove_in with (dec:=list_Z_dec) (b:=(R,t)).
  assumption.
Qed.

Lemma two_O2:
  forall (G: list (Z * list Z * Z)) r r0 R t
         (UNQ: NoDup (map snd G))
         (LT1: (1 < count_occ Z.eq_dec (concat (map (fun x => snd (fst x)) G)) r)%nat)
         (IN: In (r0,R,t) G)
         (OCC: (count_occ Z.eq_dec R r <= 1)%nat),
    exists r' R' t' (NEQ: t <> t') (INR': In r R'), In (r',R',t') G.
Proof.
  intros.
  assert (tmp: exists t' R', t <> t' /\ In r R' /\ In (R',t') (map (fun x => (snd (fst x), snd x)) G)).
  apply two_O with R.
  rewrite map_map.
  assumption.
  rewrite map_map.
  assumption.
  apply in_map_iff.
  exists (r0,R,t).
  auto.
  assumption.
  destruct tmp as (t',(R',(tt',(INr,INR')))).
  apply in_map_iff in INR'.
  destruct INR' as (x,(s3,INx)).
  destruct x.
  destruct p.
  inversion s3.
  exists z0,l,z.
  split.
  rewrite H1.
  assumption.
  split.
  rewrite H0.
  assumption.
  assumption.
Qed.

Lemma prc_P:
  forall R o o' O L P X
         (IN: In o' O)
         (LE: Z.le (R o') (R o))
         (PRC: prc o O R L P X = true),
    P o = true.
Proof.
  unfold prc.
  intros.
  apply Coq.Bool.Bool.andb_true_iff in PRC.
  destruct PRC as (tmp1,tmp2).
  apply Coq.Bool.Bool.orb_true_iff in tmp2.
  destruct tmp2 as [tmp2|tmp2].
  apply forallb_forall with (x:=o') in tmp2.
  apply Z.ltb_lt in tmp2.
  omega.
  assumption.
  apply Coq.Bool.Bool.andb_true_iff in tmp2.
  destruct tmp2 as (tmp2,tmp3).
  assumption.
Qed.

Lemma ole_in_X:
  forall O o o' R L P X 
         (IN: In o' O)
         (LE: Z.le (R o') (R o))
         (OLE: prc o O R L P X = true),
    ifb (In_dec Z.eq_dec (R o') (X (L o))) = true.
Proof.
  unfold prc.
  intros.
  apply Coq.Bool.Bool.andb_true_iff in OLE.
  destruct OLE as (tmp1,tmp2).
  apply Coq.Bool.Bool.orb_true_iff in tmp2.
  destruct tmp2 as [tmp2|tmp2].
  apply forallb_forall with (x:=o') in tmp2.
  apply Z.ltb_lt in tmp2.
  omega.
  assumption.
  apply Coq.Bool.Bool.andb_true_iff in tmp2.
  destruct tmp2 as (tmp2,tmp3).
  apply Coq.Bool.Bool.andb_true_iff in tmp3.
  destruct tmp3 as (tmp3,tmp4).
  apply forallb_forall with (x:=o') in tmp4.
  apply Coq.Bool.Bool.orb_true_iff in tmp4.
  destruct tmp4 as [tmp4|tmp4].
  apply Z.ltb_lt in tmp4.
  omega.
  apply Coq.Bool.Bool.andb_true_iff in tmp4.
  destruct tmp4 as (tmp4,tmp5).
  apply Coq.Bool.Bool.andb_true_iff in tmp5.
  destruct tmp5 as (tmp5,tmp6).
  assumption.
  assumption.
Qed.

Lemma ole_eqL:
  forall O r r' R L P X
         (IN: In r' O)
         (LE: Z.le (R r') (R r))
         (OLE: prc r O R L P X = true),
    L r' = L r.
Proof.
  unfold prc.
  intros.
  apply Coq.Bool.Bool.andb_true_iff in OLE.
  destruct OLE as (tmp1,tmp2).
  apply Coq.Bool.Bool.orb_true_iff in tmp2.
  destruct tmp2 as [tmp2|tmp2].
  apply forallb_forall with (x:=r') in tmp2.
  apply Z.ltb_lt in tmp2.
  omega.
  assumption.
  apply Coq.Bool.Bool.andb_true_iff in tmp2.
  destruct tmp2 as (tmp2,tmp3).
  apply Coq.Bool.Bool.andb_true_iff in tmp3.
  destruct tmp3 as (tmp3,tmp4).
  apply forallb_forall with (x:=r') in tmp4.
  apply Coq.Bool.Bool.orb_true_iff in tmp4.
  destruct tmp4 as [tmp4|tmp4].
  apply Z.ltb_lt in tmp4.
  omega.
  apply Coq.Bool.Bool.andb_true_iff in tmp4.
  destruct tmp4 as (tmp4,tmp5).
  apply Coq.Bool.Bool.andb_true_iff in tmp5.
  destruct tmp5 as (tmp5,tmp6).
  apply Z.eqb_eq.
  assumption.
  assumption.
Qed.


Lemma ole_X_count:
  forall O o o' R L P X
         (Xr: ifb (In_dec Z.eq_dec (R o) (X (L o))) = true)
         (Xr: ifb (In_dec Z.eq_dec (R o') (X (L o))) = true)
         (OLE: prc o O R L P X = true),
    count_occ Z.eq_dec O o' <= 1.
Proof.
  unfold prc.
  intros.
  apply Coq.Bool.Bool.andb_true_iff in OLE.
  destruct OLE as (tmp1,tmp2).
  apply Coq.Bool.Bool.orb_true_iff in tmp1.
  destruct tmp1 as [tmp1|tmp1].
  rewrite Xr in tmp1.
  inversion tmp1.
  apply le_trans with (length (filter (fun x : Z => ifb (In_dec Z.eq_dec (R x) (X (L o)))) O)).
  apply count_filter_len.
  assumption.
  apply Nat.leb_le.
  apply Coq.Bool.Bool.andb_true_iff in tmp1.
  destruct tmp1 as (tmp3,tmp4).
  assumption.
Qed.

Lemma ole_X_count_1:
  forall O o o' R L P X
         (Xr: ifb (In_dec Z.eq_dec (R o) (X (L o))) = true)
         (Xr': ifb (In_dec Z.eq_dec (R o') (X (L o))) = true)
         (IN: In o' O)
         (OLE: prc o O R L P X = true),
    count_occ Z.eq_dec O o' = 1.
Proof.
  intros.
  destruct (count_occ Z.eq_dec O o') eqn:CNT.
  apply count_occ_In with (eq_dec := Z.eq_dec) in IN.
  rewrite CNT in IN.
  omega.
  destruct n.
  omega.
  assert (tmp: count_occ Z.eq_dec O o' <= 1).
  eapply ole_X_count.
  apply Xr.
  apply Xr'.
  apply OLE.
  omega.
Qed.

Lemma remove_concat_map:
  forall (G: list (Z * list Z * Z)) O o o0 t0
         (IN: In o (concat (map (fun x => snd (fst x)) G)))
         (NIN: ~ In o O),
    In o (concat (map (fun x => snd (fst x)) (remove node_dec (o0,O,t0) G))).
Proof.
  induction G.
  simpl.
  intros.
  assumption.
  simpl.
  intros.
  apply in_app_iff in IN.
  destruct (node_dec (o0,O,t0) a) as [Ra|Ra].
  destruct IN as [IN1|IN2].
  rewrite <- Ra in IN1.
  contradiction.
  apply IHG.
  assumption.
  assumption.
  simpl.
  apply in_app_iff.
  destruct IN as [IN1|IN2].
  left.
  assumption.
  right.
  apply IHG.
  assumption.
  assumption.
Qed. 

Lemma count_remove_w_G_seq:
  forall G r R t
         (CNT1: count_occ node_dec G (r, R, t) = S O),
    (count_occ Z.eq_dec (map (fun x => fst (fst x)) G) (r) =
    S (count_occ Z.eq_dec (map (fun x => fst (fst x)) (remove node_dec (r, R, t) G)) r))%nat.
Proof.
  induction G.
  simpl.
  intros.
  assumption.
  simpl.
  intros.
  destruct a.
  destruct p.
  destruct (node_dec (z0,l,z) (r,R,t)).
  rewrite e.
  simpl.
  destruct (Z.eq_dec r r).
  Focus 2.
  contradiction.
  destruct (node_dec (r, R, t) (r, R, t)).
  Focus 2.
  contradiction.
  inversion CNT1.
  rewrite <- remove_not_in_eq.
  reflexivity.
  apply <- count_occ_not_In.
  apply H0.
  simpl.
  destruct (Z.eq_dec z0 r).
  destruct (node_dec (r, R, t) (z0, l, z)).
  inversion e0.
  rewrite H0 in n.
  rewrite H1 in n.
  rewrite H2 in n.
  contradiction.
  rewrite e.
  simpl.
  destruct (Z.eq_dec r r).
  Focus 2.
  contradiction.
  rewrite <- IHG.
  reflexivity.
  assumption.
  destruct (node_dec (r, R, t) (z0, l, z)).
  rewrite e in n.
  contradiction.
  simpl.
  destruct (Z.eq_dec z0 r).
  contradiction.
  apply IHG.
  assumption.
Qed.

Lemma count_remove_o_G_seq:
  forall G r r0 R t
         (CNT1: count_occ node_dec G (r0, R, t) = S O)
         (CNT2: count_occ Z.eq_dec R r = S O),
    (count_occ Z_eq_dec (concat (map (fun x => snd (fst x)) G)) (r) =
    S (count_occ Z_eq_dec (concat (map (fun x => snd (fst x)) (remove node_dec (r0, R, t) G))) r))%nat.
Proof.
  induction G.
  simpl.
  intros.
  assumption.
  simpl.
  intros.
  destruct a.
  destruct p.
  destruct (node_dec (z0,l,z) (r0,R,t)).
  rewrite e.
  simpl.
  destruct (node_dec (r0, R, t) (r0, R, t)).
  Focus 2.
  contradiction.
  rewrite <- count_app.
  rewrite CNT2.
  simpl.
  inversion CNT1.
  rewrite <- remove_not_in_eq.
  reflexivity.
  apply <- count_occ_not_In.
  apply H0.
  simpl.
  destruct (node_dec (r0, R, t) (z0, l, z)).
  rewrite e in n.
  contradiction.
  simpl.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite IHG with (r0:=r0) (R:=R) (t:=t).
  rewrite plus_comm.
  rewrite -> Nat.add_succ_l.
  rewrite plus_comm.
  reflexivity.
  assumption.
  assumption.
Qed.

Lemma count_remove_w_G_eq:
  forall G r r' R t
         (NEQ: r' <> r),
    (count_occ Z_eq_dec (map (fun x => fst (fst x)) G) (r) =
    count_occ Z_eq_dec (map (fun x => fst (fst x)) (remove node_dec (r', R, t) G)) r)%nat.
Proof.
  induction G.
  simpl.
  intros.
  reflexivity.
  simpl.
  intros.
  destruct a.
  destruct p.
  simpl.
  destruct (Z_eq_dec z0 r).
  destruct (node_dec (r', R, t) (z0, l, z)).
  rewrite e in e0.
  inversion e0.
  rewrite H0 in NEQ.
  contradiction.
  simpl.
  rewrite e.
  destruct (Z_eq_dec r r).
  Focus 2.
  contradiction.
  rewrite <- IHG.
  reflexivity.
  assumption.
  destruct (node_dec (r', R, t) (z0, l, z)).
  apply IHG.
  assumption.
  simpl.
  destruct (Z_eq_dec z0 r).
  rewrite e in n.
  contradiction.
  apply IHG.
  assumption.
Qed.

Lemma count_remove_o_G_eq:
  forall G r r0 R t
         (CNT: count_occ node_dec G (r0, R, t) = S O),
    (count_occ Z_eq_dec (concat (map (fun x => snd (fst x)) G)) (r) =
    count_occ Z.eq_dec R r +
    count_occ Z_eq_dec (concat (map (fun x => snd (fst x)) (remove node_dec (r0, R, t) G))) r)%nat.
Proof.
  induction G.
  simpl.
  intros.
  inversion CNT.
  simpl.
  intros.
  destruct a.
  destruct p.
  destruct (node_dec (z0,l,z) (r0,R,t)).
  rewrite e.
  simpl.
  destruct (node_dec (r0, R, t) (r0, R, t)).
  Focus 2.
  contradiction.
  rewrite <- count_app.
  inversion CNT.
  rewrite <- remove_not_in_eq.
  reflexivity.
  apply <- count_occ_not_In.
  apply H0.
  simpl.
  destruct (node_dec (r0, R, t) (z0, l, z)).
  rewrite e in n.
  contradiction.
  simpl.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite IHG with (r0:=r0) (R:=R) (t:=t).
  omega.
  assumption.
Qed.


Definition spare_ob_inv (G: list (Z * list Z * Z)) (r:Z) :=
  eq (count_occ Z.eq_dec (map (fun x => fst (fst x)) G) r) 0 \/
  lt (count_occ Z.eq_dec (map (fun x => fst (fst x)) G) r) (count_occ Z.eq_dec (concat (map (fun x => snd (fst x)) G)) r).

Lemma spare_ob_ind1:
  forall G r0 rmin r' R' R'' t2 t3 f
         (NEQ: t2 <> t3)
         (INr': In (r', R'', t3) G)
         (O2M: spare_ob_inv G r0)
         (CNT1:count_occ Z.eq_dec R' rmin = 1)
         (CNT2:count_occ Z.eq_dec R'' rmin = 1)
         (CNT3: count_occ node_dec G (r', R'', t3) = 1)
         (CNT4: count_occ node_dec G (rmin, R', t2) = 1)
         (FIL: forall x (IN: In x (map (fun x => fst (fst x)) G)), f x = true),
      spare_ob_inv ((r', rmin :: remove Z.eq_dec rmin (filter f R' ++ R''), t2)
        :: remove node_dec (r', R'', t3)
          (remove node_dec (rmin, R', t2) G)) r0.
Proof.
  unfold spare_ob_inv.
  intros.
  assert (CNT': forall r'', count_occ node_dec (remove node_dec (r'', R', t2) G) (r', R'', t3) = 1).
  {
    intros.
    rewrite count_remove_eq.
    assumption.
    unfold not.
    intros.
    inversion H.
    rewrite H3 in NEQ.
    contradiction.
  }

  destruct O2M as [O2M|O2M].
  left.
  simpl in *.
  destruct (Z.eq_dec r' r0).
  apply count_occ_not_In in O2M.
  exfalso.
  apply O2M.
  rewrite <- e.
  apply in_map_iff.
  exists (r', R'', t3).
  auto.
  apply count_occ_not_In in O2M.
  apply count_occ_not_In.
  unfold not.
  intros.
  apply O2M.
  apply in_map_remove_in with node_dec (rmin,R',t2).
  apply in_map_remove_in with node_dec (r',R'',t3).
  assumption.

  simpl.
  destruct (Z.eq_dec (r') (r0)) as [r'r0|r'r0].
  right.
  inversion r'r0.
  destruct (Z.eq_dec rmin r0) as [rmr0|rmr0].
  rewrite rmr0.
  rewrite count_remove_w_G_seq with (R:=R') (t:=t2) in O2M.
  rewrite count_remove_w_G_seq with (R:=R'') (t:=t3) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r0) (R:=R') (t:=t2) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r0) (R:=R'') (t:=t3) in O2M.
  rewrite <- count_app.
  rewrite remove_app.
  rewrite <- count_app.
  rewrite rmr0 in CNT1.
  rewrite CNT1 in O2M.
  rewrite rmr0 in CNT2.
  rewrite CNT2 in O2M.
  omega.
  rewrite H in CNT3.
  rewrite H in CNT'.
  apply CNT'.
  rewrite rmr0 in CNT4.
  assumption.
  rewrite H in CNT'.
  apply CNT'.
  rewrite rmr0 in CNT4.
  assumption.
  rewrite count_remove_w_G_eq with (r':=rmin) (R:=R') (t:=t2) in O2M.
  rewrite count_remove_w_G_seq with (R:=R'') (t:=t3) in O2M.
  rewrite count_remove_o_G_eq with (r0:= rmin) (R:=R') (t:=t2) in O2M.
  rewrite count_remove_o_G_eq with (r0:= r0) (R:=R'') (t:=t3) in O2M.
  rewrite <- count_app.
  rewrite count_remove_eq.
  rewrite <- count_app.
  rewrite count_filter.
  omega.
  apply FIL.
  rewrite <- H.
  apply in_map_iff.
  exists (r', R'', t3).
  auto.
  assumption.
  rewrite H in CNT'.
  apply CNT'.
  assumption.
  rewrite H in CNT'.
  apply CNT'.
  unfold not in *.
  intros.
  apply rmr0.
  assumption.

  destruct (Z.eq_dec rmin r0) as [rmr0|rmr0].
  rewrite rmr0.
  rewrite count_remove_w_G_seq with (R:=R') (t:=t2) in O2M.
  rewrite count_remove_w_G_eq with (r':=r')(R:=R'') (t:=t3) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r0) (R:=R') (t:=t2) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r') (R:=R'') (t:=t3) in O2M.
  rewrite <- count_app.
  rewrite count_remove_zero.
  rewrite rmr0 in CNT1.
  rewrite CNT1 in O2M.
  rewrite rmr0 in CNT2.
  rewrite CNT2 in O2M.
  simpl in *.
  right.
  omega.
  apply CNT'.
  rewrite <- rmr0.
  assumption.
  assumption.
  rewrite <- rmr0.
  assumption.

  destruct (in_dec Z_eq_dec (r0)
     (r'
      :: map (fun node0 => fst (fst node0))
           (remove node_dec (r', R'', t3)
              (remove node_dec (rmin, R', t2) G)))).
  right.
  rewrite count_remove_w_G_eq with (r':=rmin) (R:=R') (t:=t2) in O2M.
  rewrite count_remove_w_G_eq with (r':=r') (R:=R'') (t:=t3) in O2M.
  rewrite count_remove_o_G_eq with (r0:=rmin) (R:=R') (t:=t2) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r') (R:=R'') (t:=t3) in O2M.
  rewrite <- count_app.
  rewrite remove_app.
  rewrite <- count_app.
  rewrite count_remove_eq.
  rewrite count_remove_eq.
  rewrite count_filter.
  omega.
  apply FIL.
  apply in_map_remove_in with node_dec (rmin, R', t2).
  apply in_map_remove_in with node_dec (r', R'', t3).
  simpl in i.
  destruct i as [EQ|IN].
  rewrite EQ in r'r0.
  contradiction.
  assumption.
  assumption.
  assumption.
  apply CNT'.
  assumption.
  assumption.
  unfold not in *.
  intros.
  apply rmr0.
  inversion H.
  reflexivity.
  left.
  simpl in n.
  destruct (in_dec Z_eq_dec (r0)
         (map (fun node0 => fst (fst node0))
            (remove node_dec (r', R'', t3)
               (remove node_dec (rmin, R', t2) G)))).
  exfalso.
  apply n.
  right.
  assumption.
  apply count_occ_not_In.
  assumption. 
Qed.

Lemma own_ob_ind1:
  forall G r0 rmin r' R' R'' t2 t3 f
         (NEQ: t2 <> t3)
         (INr': In (r', R'', t3) G)
         (O2M: own_ob G r0)
         (CNT1:count_occ Z.eq_dec R' rmin = 1)
         (CNT2:count_occ Z.eq_dec R'' rmin = 1)
         (CNT3: count_occ node_dec G (r', R'', t3) = 1)
         (CNT4: count_occ node_dec G (rmin, R', t2) = 1)
         (FIL: forall x (IN: In x (map (fun x => fst (fst x)) G)), f x = true),
      own_ob ((r', rmin :: remove Z.eq_dec rmin (filter f R' ++ R''), t2)
        :: remove node_dec (r', R'', t3)
          (remove node_dec (rmin, R', t2) G)) r0.
Proof.
  unfold own_ob.
  intros.
  assert (CNT': count_occ node_dec (remove node_dec (rmin, R', t2) G) (r', R'', t3) = 1).
  {
    rewrite count_remove_eq.
    assumption.
    unfold not.
    intros.
    inversion H.
    rewrite H3 in NEQ.
    contradiction.
  }

  simpl.
  destruct (Z_eq_dec r' r0) as [r'r0|r'r0].
  inversion r'r0.
  destruct (Z.eq_dec rmin r0) as [rmr0|rmr0].
  rewrite rmr0.
  rewrite count_remove_w_G_seq with (R:=R') (t:=t2) in O2M.
  rewrite count_remove_w_G_seq with (R:=R'') (t:=t3) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r0) (R:=R') (t:=t2) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r0) (R:=R'') (t:=t3) in O2M.
  rewrite <- count_app.
  rewrite remove_app.
  rewrite <- count_app.
  rewrite rmr0 in CNT1.
  rewrite CNT1 in O2M.
  rewrite rmr0 in CNT2.
  rewrite CNT2 in O2M.
  omega.
  rewrite H in CNT'.
  rewrite rmr0 in CNT'.
  assumption.
  rewrite rmr0 in CNT4.
  assumption.
  rewrite H in CNT'.
  rewrite rmr0 in CNT'.
  assumption.
  rewrite <- rmr0.
  assumption.
  rewrite count_remove_w_G_eq with (r':=rmin) (R:=R') (t:=t2) in O2M.
  rewrite count_remove_w_G_seq with (R:=R'') (t:=t3) in O2M.
  rewrite count_remove_o_G_eq with (r0:=rmin) (R:=R') (t:=t2) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r0) (R:=R'') (t:=t3) in O2M.
  rewrite <- count_app.
  rewrite count_remove_eq.
  rewrite <- count_app.
  rewrite count_filter.
  omega.
  apply FIL.
  rewrite <- H.
  apply in_map_iff.
  exists (r', R'', t3).
  auto.
  assumption.
  rewrite H in CNT'.
  assumption.
  assumption.
  rewrite <- H.
  assumption.

  unfold not in *.
  intros.
  apply rmr0.
  assumption.

  destruct (Z.eq_dec rmin r0) as [rmr0|rmr0].
  rewrite rmr0.
  rewrite count_remove_w_G_seq with (R:=R') (t:=t2) in O2M.
  rewrite count_remove_w_G_eq with (r':=r')(R:=R'') (t:=t3) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r0) (R:=R') (t:=t2) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r') (R:=R'') (t:=t3) in O2M.
  rewrite <- count_app.
  rewrite count_remove_zero.
  rewrite rmr0 in CNT1.
  rewrite CNT1 in O2M.
  rewrite rmr0 in CNT2.
  rewrite CNT2 in O2M.
  simpl in *.
  omega.
  rewrite <- rmr0.
  assumption.

  rewrite <- rmr0.
  assumption.
  assumption.
  rewrite <- rmr0.
  assumption.

  destruct (in_dec Z_eq_dec (r0)
     (r'
      :: map (fun node0 => fst (fst node0))
           (remove node_dec (r', R'', t3)
              (remove node_dec (rmin, R', t2) G)))).
  rewrite count_remove_w_G_eq with (r':=rmin) (R:=R') (t:=t2) in O2M.
  rewrite count_remove_w_G_eq with (r':=r') (R:=R'') (t:=t3) in O2M.
  rewrite count_remove_o_G_eq with (r0:=rmin) (R:=R') (t:=t2) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r') (R:=R'') (t:=t3) in O2M.
  rewrite <- count_app.
  rewrite remove_app.
  rewrite <- count_app.
  rewrite count_remove_eq.
  rewrite count_remove_eq.
  rewrite count_filter.
  omega.
  apply FIL.
  apply in_map_remove_in with node_dec (rmin, R', t2).
  apply in_map_remove_in with node_dec (r', R'', t3).
  simpl in i.
  destruct i as [EQ|IN].
  rewrite EQ in r'r0.
  contradiction.
  assumption.
  assumption.
  assumption.
  assumption.

  assumption.
  assumption.
  unfold not in *.
  intros.
  apply rmr0.
  inversion H.
  reflexivity.
  destruct (in_dec Z_eq_dec (r0)
         (map (fun node0 => fst (fst node0))
            (remove node_dec (r', R'', t3)
               (remove node_dec (rmin, R', t2) G)))).
  exfalso.
  apply n.
  right.
  assumption.
  assert (CR0: count_occ Z.eq_dec
  (map (fun x : Z * list Z * Z => fst (fst x))
     (remove node_dec (r', R'', t3) (remove node_dec (rmin, R', t2) G))) r0 = 0).
  apply count_occ_not_In.
  assumption.
  rewrite CR0.
  omega.
Qed.

Lemma ole_X_length:
  forall R r W L P X
         (Xr: ifb (In_dec Z.eq_dec (W r) (X (L r))) = true)
         (OLE: prc r R W L P X = true),
    length (filter (fun x : Z => ifb (In_dec Z.eq_dec (W x) (X (L r)))) R) <= 1.
Proof.
  unfold prc.
  intros.
  apply Coq.Bool.Bool.andb_true_iff in OLE.
  destruct OLE as (tmp1,tmp2).
  apply Coq.Bool.Bool.orb_true_iff in tmp1.
  destruct tmp1 as [tmp1|tmp1].
  rewrite Xr in tmp1.
  inversion tmp1.
  apply Coq.Bool.Bool.andb_true_iff in tmp1.
  destruct tmp1 as (tmp3,tmp4).
  apply Nat.leb_le.
  assumption.
Qed.



Lemma ole_X:
  forall R r r' W L P X
         (IN: In r' R)
         (LE: Z.le (W r') (W r))
         (OLE: prc r R W L P X = true),
    ifb (In_dec Z.eq_dec (W r) (X (L r))) = true.
Proof.
  unfold prc.
  intros.
  apply Coq.Bool.Bool.andb_true_iff in OLE.
  destruct OLE as (tmp1,tmp2).
  apply Coq.Bool.Bool.orb_true_iff in tmp2.
  destruct tmp2 as [tmp2|tmp2].
  apply forallb_forall with (x:=r') in tmp2.
  apply Z.ltb_lt in tmp2.
  omega.
  assumption.
  apply Coq.Bool.Bool.andb_true_iff in tmp2.
  destruct tmp2 as (tmp2,tmp3).
  apply Coq.Bool.Bool.andb_true_iff in tmp3.
  destruct tmp3 as (tmp3,tmp4).
  assumption.
Qed.

Lemma ole_le:
  forall R r r' W L P X
         (IN: In r' R)
         (OLE: prc r R W L P X = true),
    (W r <= W r' + 1)%Z.
Proof.
  unfold prc.
  intros.
  apply Coq.Bool.Bool.andb_true_iff in OLE.
  destruct OLE as (tmp1,tmp2).
  apply Coq.Bool.Bool.orb_true_iff in tmp2.
  destruct tmp2 as [tmp2|tmp2].
  apply forallb_forall with (x:=r') in tmp2.
  apply Z.ltb_lt in tmp2.
  omega.
  assumption.
  apply Coq.Bool.Bool.andb_true_iff in tmp2.
  destruct tmp2 as (tmp2,tmp3).
  apply Coq.Bool.Bool.andb_true_iff in tmp3.
  destruct tmp3 as (tmp3,tmp4).
  apply forallb_forall with (x:=r') in tmp4.
  apply Coq.Bool.Bool.orb_true_iff in tmp4.
  destruct tmp4 as [tmp4|tmp4].
  apply Z.ltb_lt in tmp4.
  omega.
  apply Coq.Bool.Bool.andb_true_iff in tmp4.
  destruct tmp4 as (tmp4,tmp5).
  apply Coq.Bool.Bool.andb_true_iff in tmp5.
  destruct tmp5 as (tmp5,tmp6).
  apply Z.leb_le.
  assumption.
  assumption.
Qed.

Lemma prc_ind1:
  forall rmin r' R' R'' W L X P
         (INR'': In rmin R'')
         (INR': In rmin R')
         (Rrmin: Z.le (W rmin) (W r'))
         (OLER': prc rmin R' W L P X = true)
         (OLER'': prc r' R'' W L P X = true),
    prc r' (rmin :: remove Z.eq_dec rmin ((filter (fun x => Z.leb (W rmin) (W x)) R') ++ R'')) W L P X = true.
Proof.
  intros.
  unfold prc.
  assert (Lr'Lrmin: L r' = L rmin).
  {
    symmetry.
    eapply ole_eqL.
    apply INR''.
    apply Rrmin.
    apply OLER''.
  }
  assert (Xr': ifb (In_dec Z.eq_dec (W r') (X (L rmin))) = true).
  {
    rewrite <- Lr'Lrmin.
    eapply ole_X.
    apply INR''.
    apply Rrmin.
    apply OLER''.
  }
  assert (Xrmin: ifb (In_dec Z.eq_dec (W rmin) (X (L rmin))) = true).
  {
    eapply ole_in_X.
    apply INR'.
    omega.
    apply OLER'.
    }
  assert (Wr'rmin: (W r' <= W rmin + 1)%Z).
  {
    eapply ole_le.
    apply INR''.
    apply OLER''.
  }
  assert (LEN: length(filter (fun x : Z => ifb (In_dec Z.eq_dec (W x) (X (L rmin)))) R') <= 1).
  {
    eapply ole_X_length.
    assumption.
    apply OLER'.
  }
  assert (LEN': length(filter (fun x : Z => ifb (In_dec Z.eq_dec (W x) (X (L rmin)))) R'') <= 1).
  {
    rewrite <- Lr'Lrmin.
    eapply ole_X_length.
    rewrite Lr'Lrmin.
    assumption.
    apply OLER''.
  }

  assert (CNTR': count_occ Z.eq_dec R' rmin = 1).
  {
    eapply ole_X_count_1.
    apply Xrmin.
    assumption.
    assumption.
    apply OLER'.
  }

  assert (CNTR'': count_occ Z.eq_dec R'' rmin = 1).
  {
    eapply ole_X_count_1 with (R:=W).
    rewrite Lr'Lrmin.
    apply Xr'.
    rewrite Lr'Lrmin.
    assumption.
    assumption.
    apply OLER''.
  }

  rewrite Lr'Lrmin.
  intros.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  {
    apply Coq.Bool.Bool.orb_true_iff.
    right.
    simpl.

    rewrite Xrmin.
    apply Coq.Bool.Bool.andb_true_iff.
    split.
    simpl.
    rewrite remove_app.
    rewrite filter_app.
    rewrite filter_remove.
    rewrite filter_remove.
    reflexivity.
    assumption.
    assumption.
    assumption.
    apply le_trans with (length (filter (fun x : Z => ifb (In_dec Z.eq_dec (W x) (X (L rmin)))) R')).
    apply length_filter_filter.
    assumption.
    assumption.
    apply filter_In.
    split.
    assumption.
    apply Z.leb_le.
    omega.
    apply Coq.Bool.Bool.andb_true_iff.
    split.

    apply Coq.Bool.Bool.orb_true_iff.
    right.
    apply Z.eqb_eq.
    reflexivity.
    apply forallb_forall.
    intros.
    rewrite remove_app in H.
    apply in_app_iff in H.

    destruct H as [IN1|IN2].
    unfold prc in OLER'.
    apply Coq.Bool.Bool.andb_true_iff in OLER'.
    destruct OLER' as (tmp1,tmp2).
    apply Coq.Bool.Bool.orb_true_iff in tmp1.
    destruct tmp1 as [tmp3|tmp3].
    rewrite Xrmin in tmp3.
    inversion tmp3.
    apply Coq.Bool.Bool.andb_true_iff in tmp3.
    destruct tmp3 as (tmp3,tmp4).
    apply forallb_forall with (x:=x) in tmp4.
    apply Coq.Bool.Bool.orb_true_iff in tmp4.
    apply Coq.Bool.Bool.orb_true_iff.
    destruct tmp4 as [tmp4|tmp4].
    left.
    assumption.
    right.
    assumption.
    apply in_filter_in_l with (fun x : Z => (W rmin <=? W x)%Z).
    apply in_remove_in with Z.eq_dec rmin.
    assumption.

    unfold prc in OLER''.
    apply Coq.Bool.Bool.andb_true_iff in OLER''.
    destruct OLER'' as (tmp1,tmp2).
    apply Coq.Bool.Bool.orb_true_iff in tmp1.
    destruct tmp1 as [tmp3|tmp3].
    rewrite Lr'Lrmin in tmp3.
    rewrite Xr' in tmp3.
    inversion tmp3.
    apply Coq.Bool.Bool.andb_true_iff in tmp3.
    destruct tmp3 as (tmp3,tmp4).
    apply forallb_forall with (x:=x) in tmp4.
    apply Coq.Bool.Bool.orb_true_iff in tmp4.
    apply Coq.Bool.Bool.orb_true_iff.
    destruct tmp4 as [tmp4|tmp4].
    left.
    rewrite <- Lr'Lrmin.
    assumption.
    rewrite <- Lr'Lrmin.
    right.
    assumption.
    apply in_remove_in with Z.eq_dec rmin.
    assumption.
  }
  {
    apply Coq.Bool.Bool.orb_true_iff.
    right.
    apply Coq.Bool.Bool.andb_true_iff.
    split.
    {
      eapply prc_P.
      apply INR''.
      apply Rrmin.
      apply OLER''.
    }
    {
    apply Coq.Bool.Bool.andb_true_iff.
    split.
    assumption.
    apply forallb_forall.
    simpl.
    intros.

    destruct H as [EQ|IN].
    rewrite <- EQ.
    apply Coq.Bool.Bool.orb_true_iff.
    right.
    apply Coq.Bool.Bool.andb_true_iff.
    split.
    assumption.
    apply Coq.Bool.Bool.andb_true_iff.
    split.
    apply Z.eqb_eq.
    reflexivity.
    apply Z.leb_le.
    assumption.

    rewrite remove_app in IN.
    apply in_app_iff in IN.
    destruct IN as [IN1|IN2].
    apply Coq.Bool.Bool.orb_true_iff.

    assert (tmp: (W r' = W rmin + 1)%Z \/ (W r' <= W rmin)%Z).
    omega.
    destruct tmp as [EQ1|LE1].
    destruct (Z_le_dec (W x) (W rmin + 1)) as [le1|le1].
    Focus 2.
    left.
    apply Z.ltb_lt.
    omega.
    assert (tmp: (W x = W rmin + 1)%Z \/ (W x <= W rmin)%Z).
    omega.
    destruct tmp as [EQ2|LE2].
    assert (tmp: In x (filter (fun x : Z => ifb (In_dec Z.eq_dec (W x) (X (L rmin)))) (remove Z.eq_dec rmin R'))).
    rewrite filter_remove_filter.
    apply in_in_remove.
    unfold not.
    intros.
    rewrite H in EQ2.
    omega.
    apply filter_In.
    split.
    apply in_remove_in with Z.eq_dec rmin.
    rewrite <- filter_remove_filter in IN1.
    apply in_filter_in_l with (fun x : Z => (W rmin <=? W x)%Z).
    assumption.
    rewrite EQ2.
    rewrite <- EQ1.
    assumption.
    rewrite filter_remove in tmp.
    inversion tmp.
    assumption.
    assumption.
    assumption.
    assert (tmp: (W x = W rmin)%Z \/ (W x < W rmin)%Z).
    omega.
    destruct tmp as [EQ3|LE3].

    assert (tmp: In x (filter (fun x : Z => ifb (In_dec Z.eq_dec (W x) (X (L rmin)))) (remove Z.eq_dec rmin R'))).
    rewrite filter_remove_filter.
    apply in_in_remove.
    unfold not.
    intros.
    rewrite H in IN1.
    apply remove_In in IN1.
    assumption.
    apply filter_In.
    split.
    apply in_remove_in with Z.eq_dec rmin.
    rewrite <- filter_remove_filter in IN1.
    apply in_filter_in_l with (fun x : Z => (W rmin <=? W x)%Z).
    assumption.
    rewrite EQ3.
    assumption.
    rewrite filter_remove in tmp.
    inversion tmp.
    assumption.
    assumption.
    assumption.
    rewrite <- filter_remove_filter in IN1.
    apply filter_In in IN1.
    destruct IN1 as (tmp1,tmp2).
    apply Z.leb_le in tmp2.
    omega.
    assert (tmp: (W r' = W rmin)%Z \/ (W r' < W rmin)%Z).
    omega.
    destruct tmp as [EQ2|LE2].
    Focus 2.
    assert (tmp: (W rmin <= W r')%Z).
    apply Rrmin.
    omega.
    rewrite EQ2.
    unfold prc in OLER'.
    apply Coq.Bool.Bool.andb_true_iff in OLER'.
    destruct OLER' as (tmp1,tmp2).
    apply Coq.Bool.Bool.orb_true_iff in tmp2.
    destruct tmp2 as [tmp2|tmp3].
    left.
    apply forallb_forall with (x:=x) in tmp2.
    assumption.
    apply in_filter_in_l with (fun x : Z => (W rmin <=? W x)%Z).
    apply in_remove_in with Z.eq_dec rmin.
    assumption.
    apply Coq.Bool.Bool.andb_true_iff in tmp3.
    destruct tmp3 as (tmp3,tmp4).
    apply Coq.Bool.Bool.andb_true_iff in tmp4.
    destruct tmp4 as (tmp4,tmp5).
    apply forallb_forall with (x:=x) in tmp5.
    apply Coq.Bool.Bool.orb_true_iff in tmp5.
    assumption.
    apply in_filter_in_l with (fun x : Z => (W rmin <=? W x)%Z).
    apply in_remove_in with Z.eq_dec rmin.
    assumption.

    unfold prc in OLER''.
    apply Coq.Bool.Bool.andb_true_iff in OLER''.
    destruct OLER'' as (tmp1,tmp2).
    apply Coq.Bool.Bool.orb_true_iff in tmp2.
    destruct tmp2 as [tmp2|tmp3].
    apply Coq.Bool.Bool.orb_true_iff.
    left.
    apply forallb_forall with (x:=x) in tmp2.
    assumption.
    apply in_remove_in with Z.eq_dec rmin.
    assumption.
    apply Coq.Bool.Bool.andb_true_iff in tmp3.
    destruct tmp3 as (tmp3,tmp4).
    apply Coq.Bool.Bool.andb_true_iff in tmp4.
    destruct tmp4 as (tmp4,tmp5).
    apply forallb_forall with (x:=x) in tmp5.
    rewrite <- Lr'Lrmin.
    assumption.
    apply in_remove_in with Z.eq_dec rmin.
    assumption.
  }
  }
Qed.

Lemma ole_o2o:
  forall R r r' W L X P
         (IN: In r' R)
         (OLE: prc r R W L P X = true)
         (Xr : ifb (In_dec Z.eq_dec (W r) (X (L r))) = true)
         (Xr' : ifb (In_dec Z.eq_dec (W r') (X (L r))) = true),
    In (W r') (X (L r')).
Proof.
  unfold prc.
  intros.
  apply Coq.Bool.Bool.andb_true_iff in OLE.
  destruct OLE as (tmp1,tmp2).
  apply Coq.Bool.Bool.orb_true_iff in tmp1.
  destruct tmp1 as [tmp1|tmp1].
  rewrite Xr in tmp1.
  inversion tmp1.
  apply Coq.Bool.Bool.andb_true_iff in tmp1.
  destruct tmp1 as [tmp3 tmp4].
  apply forallb_forall with (x:=r') in tmp4.
  apply Coq.Bool.Bool.orb_true_iff in tmp4.
  destruct tmp4 as [tmp4|tmp4].
  rewrite Xr' in tmp4.
  inversion tmp4.
  apply Z.eqb_eq in tmp4.
  rewrite tmp4.
  unfold ifb in Xr'.
  destruct (in_dec Z.eq_dec (W r') (X (L r))).
  assumption.
  inversion Xr'.
  assumption.
Qed.

Lemma in_in_count2 A B dec (f: A -> B):
  forall (l: list A) (a1 a2: A) fa1
         (NEQ: a1 <> a2) 
         (EQ: f a1 = f a2)
         (IN1: In a1 l)
         (IN2: In a2 l)
         (FA1: fa1 = f a1),
    2 <= count_occ dec (map f l) fa1.
Proof.
  induction l.
  simpl.
  intros.
  contradiction.
  simpl.
  intros.
  destruct IN1 as [IN1|IN1].
  destruct IN2 as [IN2|IN2].
  rewrite <- IN1 in NEQ.
  rewrite <- IN2 in NEQ.
  contradiction.
  rewrite IN1.
  destruct (dec (f a1) (f a1)).
  Focus 2.
  contradiction.
  assert (tmp: 0 <count_occ dec (map f l) (f a1)).
  rewrite EQ.
  apply count_occ_In.
  apply in_map_iff.
  exists a2.
  auto.
  rewrite FA1.
  destruct (dec (f a1) (f a1)).
  omega.
  contradiction.
  destruct IN2 as [IN2|IN2].
  rewrite IN2.
  rewrite FA1.
  rewrite EQ.
  destruct (dec (f a2) (f a2)).
  Focus 2.
  contradiction.
  assert (tmp: 0 <count_occ dec (map f l) (f a2)).
  rewrite <- EQ.
  apply count_occ_In.
  apply in_map_iff.
  exists a1.
  auto.
  omega.
  destruct (dec (f a) (f a1)).
  apply le_trans with (count_occ dec (map f l) (f a1)).
  eapply IHl.
  apply NEQ.
  assumption.
  assumption.
  assumption.
  reflexivity.
  rewrite FA1.
  rewrite e.
  destruct (dec (f a1) (f a1)).
  omega.
  contradiction.
  destruct (dec (f a) (fa1)).
  rewrite FA1 in e.
  contradiction.
  eapply IHl.
  apply NEQ.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma spare_ob_ind2:
  forall G r0 rmin r R R' t1 t2 f
         (NEQ: t1 <> t2)
         (IN: In r0 (map (fun x => fst (fst x)) G))
         (O2M: spare_ob_inv G r0)
         (CNT1: count_occ Z.eq_dec R' rmin = 1)
         (CNT3: count_occ node_dec G (r, R', t2) = 1)
         (CNT4: count_occ node_dec G (rmin, R, t1) = 1)
         (FIL: forall x (IN: In x (map (fun x => fst (fst x)) G)), f x = true),
      spare_ob_inv ((r,filter f R ++ remove Z.eq_dec rmin R', t1)
       :: remove node_dec (r, R', t2) (remove node_dec (rmin, R, t1) G)) r0.
Proof.
  unfold spare_ob_inv.
  intros.
  assert (CNT': count_occ node_dec (remove node_dec (rmin, R, t1) G) (r, R', t2) = 1).
  {
    intros.
    rewrite count_remove_eq.
    assumption.
    unfold not.
    intros.
    inversion H.
    rewrite H3 in NEQ.
    contradiction.
  }

  destruct O2M as [O2M|O2M].
  left.
  simpl in *.
  destruct (Z_eq_dec r r0).
  apply count_occ_not_In in O2M.
  contradiction.
  apply count_occ_not_In in O2M.
  contradiction.

  simpl.
  destruct (Z_eq_dec r r0) as [rr0|rr0].
  inversion rr0.
  destruct (Z.eq_dec rmin r0) as [rmr0|rmr0].
  rewrite rmr0.
  rewrite count_remove_w_G_seq with (R:=R) (t:=t1) in O2M.
  rewrite count_remove_w_G_seq with (R:=R') (t:=t2) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r0) (R:=R) (t:=t1) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r0) (R:=R') (t:=t2) in O2M.
  rewrite <- count_app.
  simpl.
  rewrite <- count_app.
  rewrite count_remove_zero.
  rewrite rmr0 in CNT1.
  rewrite CNT1 in O2M.
  rewrite count_filter.
  omega.
  apply FIL.
  assumption.
  rewrite H in CNT'.
  rewrite rmr0 in CNT'.
  assumption.
  rewrite rmr0 in CNT4.
  assumption.
  rewrite H in CNT'.
  rewrite rmr0 in CNT'.
  assumption.
  rewrite rmr0 in CNT4.
  assumption.

  rewrite count_remove_w_G_eq with (r':=rmin) (R:=R) (t:=t1) in O2M.
  rewrite count_remove_w_G_seq with (R:=R') (t:=t2) in O2M.
  rewrite count_remove_o_G_eq with (r0:=rmin) (R:=R) (t:=t1) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r0) (R:=R') (t:=t2) in O2M.
  rewrite <- count_app.
  simpl.
  rewrite <- count_app.
  rewrite count_remove_eq.
  rewrite count_filter.
  omega.
  apply FIL.
  assumption.
  assumption.
  rewrite <- H.
  assumption.
  assumption.
  rewrite <- H.
  assumption.
  unfold not in *.
  intros.
  apply rmr0.
  assumption.

  destruct (Z.eq_dec rmin r0) as [rmr0|rmr0].
  rewrite rmr0.

  rewrite count_remove_w_G_seq with (R:=R) (t:=t1) in O2M.
  rewrite count_remove_w_G_eq with (r':=r) (R:=R') (t:=t2) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r0) (R:=R) (t:=t1) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r) (R:=R') (t:=t2) in O2M.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite count_remove_zero.
  rewrite count_filter.
  rewrite rmr0 in CNT1.
  rewrite CNT1 in O2M.
  omega.
  apply FIL.
  assumption.
  rewrite <- rmr0.
  assumption.
  rewrite <- rmr0.
  assumption.
  unfold not in *.
  intros.
  apply rr0.
  inversion H.
  reflexivity.
  rewrite <- rmr0.
  assumption.

  rewrite count_remove_w_G_eq with (r':=rmin) (R:=R) (t:=t1) in O2M.
  rewrite count_remove_w_G_eq with (r':=r) (R:=R') (t:=t2) in O2M.
  rewrite count_remove_o_G_eq with (r0:=rmin) (R:=R) (t:=t1) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r) (R:=R') (t:=t2) in O2M.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite count_remove_eq.
  rewrite count_filter.
  omega.
  apply FIL.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  unfold not in *.
  intros.
  apply rmr0.
  inversion H.
  reflexivity.
Qed.

Lemma own_ob_ind2:
  forall G r0 rmin r R R' t1 t2 f
         (NEQ: t1 <> t2)
         (IN: In (r, R', t2) G)
         (O2M: own_ob G r0)
         (CNT1: count_occ Z.eq_dec R' rmin = 1)
         (CNT2: count_occ node_dec G (r, R', t2) = 1)
         (CNT3: count_occ node_dec G (rmin, R, t1) = 1)
         (FIL: forall x (IN: In (x) (map (fun x => fst (fst x)) G)), f x = true),
      own_ob ((r,filter f R ++ remove Z.eq_dec rmin R', t1)
       :: remove node_dec (r, R', t2) (remove node_dec (rmin, R, t1) G)) r0.
Proof.
  unfold own_ob.
  intros.
  assert (CNT': count_occ node_dec (remove node_dec (rmin, R, t1) G) (r, R', t2) = 1).
  {
    intros.
    rewrite count_remove_eq.
    assumption.
    unfold not.
    intros.
    inversion H.
    rewrite H3 in NEQ.
    contradiction.
  }

  simpl.
  destruct (Z_eq_dec r r0) as [rr0|rr0].
  inversion rr0.
  simpl.
  destruct (Z.eq_dec rmin r0) as [rmr0|rmr0].
  rewrite rmr0.
  rewrite count_remove_w_G_seq with (R:=R) (t:=t1) in O2M.
  rewrite count_remove_w_G_seq with (R:=R') (t:=t2) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r0) (R:=R) (t:=t1) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r0) (R:=R') (t:=t2) in O2M.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite count_remove_zero.
  rewrite rmr0 in CNT1.
  rewrite CNT1 in O2M.
  rewrite count_filter.
  omega.
  apply FIL.
  rewrite <- H.
  apply in_map_iff.
  exists (r, R', t2).
  auto.
  rewrite H in CNT'.
  rewrite rmr0 in CNT'.
  assumption.
  rewrite rmr0 in CNT3.
  assumption.
  rewrite H in CNT'.
  rewrite rmr0 in CNT'.
  assumption.
  rewrite rmr0 in CNT3.
  assumption.

  rewrite count_remove_w_G_eq with (r':=rmin) (R:=R) (t:=t1) in O2M.
  rewrite count_remove_w_G_seq with (R:=R') (t:=t2) in O2M.
  rewrite count_remove_o_G_eq with (r0:=rmin) (R:=R) (t:=t1) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r0) (R:=R') (t:=t2) in O2M.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite count_remove_eq.
  rewrite count_filter.
  omega.
  apply FIL.
  rewrite <- H.
  apply in_map_iff.
  exists (r, R', t2).
  auto.
  assumption.
  rewrite <- H.
  assumption.
  assumption.
  rewrite <- H.
  assumption.
  unfold not in *.
  intros.
  apply rmr0.
  assumption.

  destruct (Z.eq_dec rmin r0) as [rmr0|rmr0].
  rewrite rmr0.
  rewrite count_remove_w_G_seq with (R:=R) (t:=t1) in O2M.
  rewrite count_remove_w_G_eq with (r':=r) (R:=R') (t:=t2) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r0) (R:=R) (t:=t1) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r) (R:=R') (t:=t2) in O2M.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite count_remove_zero.
  rewrite count_filter.
  rewrite rmr0 in CNT1.
  rewrite CNT1 in O2M.
  simpl in *.
  omega.
  apply FIL.
  apply in_map_iff.
  exists (rmin, R, t1).
  split.
  rewrite rmr0.
  reflexivity.
  apply count_occ_In with (eq_dec := node_dec).
  omega.
  rewrite <- rmr0.
  assumption.
  rewrite <- rmr0.
  assumption.
  assumption.
  rewrite <- rmr0.
  assumption.

  destruct (in_dec Z_eq_dec r0
      (r
       :: map (fun node0 => fst (fst node0))
            (remove node_dec (r, R', t2)
               (remove node_dec (rmin, R, t1) G)))).
  rewrite count_remove_w_G_eq with (r':=rmin) (R:=R) (t:=t1) in O2M.
  rewrite count_remove_w_G_eq with (r':=r) (R:=R') (t:=t2) in O2M.
  rewrite count_remove_o_G_eq with (r0:=rmin) (R:=R) (t:=t1) in O2M.
  rewrite count_remove_o_G_eq with (r0:=r) (R:=R') (t:=t2) in O2M.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite count_remove_eq.
  rewrite count_filter.
  omega.
  apply FIL.
  destruct i as [EQ1|IN1].
  rewrite EQ1 in rr0.
  contradiction.
  apply in_map_remove_in with node_dec (rmin, R, t1).
  apply in_map_remove_in with node_dec (r, R', t2).
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  unfold not in *.
  intros.
  apply rmr0.
  inversion H.
  reflexivity.
  destruct (in_dec Z_eq_dec r0
         (map (fun node0 => fst (fst node0))
            (remove node_dec (r, R', t2)
               (remove node_dec (rmin, R, t1) G)))).
  exfalso.
  apply n.
  right.
  assumption.  
  assert (tmp: count_occ Z.eq_dec
  (map (fun x : Z * list Z * Z => fst (fst x))
     (remove node_dec (r, R', t2) (remove node_dec (rmin, R, t1) G))) r0 = 0).
  apply count_occ_not_In.
  assumption.
  rewrite tmp.
  omega.
Qed.

Lemma prc_ind2:
  forall rmin r R R' W L P X
         (INR': In rmin R')
         (CNT1: count_occ Z.eq_dec R' rmin = 1)
         (MIN: Z.le (W rmin) (W r))
         (OLER: prc rmin R W L P X = true)
         (OLER': prc r R' W L P X = true),
    prc r (filter (fun x : Z => (W rmin <=? W x)%Z) R ++ remove Z.eq_dec rmin R') W L P X = true.
Proof.
  intros.
  unfold prc.
  assert (Lr'Lrmin: L r = L rmin).
    {
      symmetry.
      eapply ole_eqL.
      apply INR'.
      apply MIN.
      apply OLER'.
    }

  assert (Xr: ifb (In_dec Z.eq_dec (W r) (X (L rmin))) = true).
    {
      rewrite <- Lr'Lrmin.
      eapply ole_X.
      apply INR'.
      apply MIN.
      apply OLER'.
    }

  assert (Xrmin: ifb (In_dec Z.eq_dec (W rmin) (X (L rmin)))= true).
    {
      rewrite <- Lr'Lrmin.
      eapply ole_in_X.
      apply INR'.
      apply MIN.
      apply OLER'.
    }

  assert (LEN: length(filter (fun x : Z => ifb (In_dec Z.eq_dec (W x) (X (L rmin)))) R) <= 1).
    {
    eapply ole_X_length.
    assumption.
    apply OLER.
    }

  assert (Wrrmin: (W r <= W rmin + 1)%Z).
    {
      eapply ole_le.
      apply INR'.
      apply OLER'.
    }

  rewrite Lr'Lrmin.
  intros.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  {
    apply Coq.Bool.Bool.orb_true_iff.
    right.
    unfold prc in OLER'.
    apply Coq.Bool.Bool.andb_true_iff in OLER'.
    destruct OLER' as (tmp1,tmp2).
    apply Coq.Bool.Bool.orb_true_iff in tmp1.
    destruct tmp1 as [tmp11|tmp12].
    rewrite Lr'Lrmin in tmp11.
    rewrite Xr in tmp11.
    inversion tmp11.
    apply Coq.Bool.Bool.andb_true_iff.
    split.
    apply Nat.leb_le.
    rewrite Lr'Lrmin in tmp12.
    apply Coq.Bool.Bool.andb_true_iff in tmp12.
    destruct tmp12 as (tmp12, tmp13).
    rewrite filter_app.
    rewrite length_app.
    assert (tmp: filter (fun x : Z => ifb (In_dec Z.eq_dec (W x) (X (L rmin))))
     (remove Z.eq_dec rmin R') = nil).
    apply filter_remove.
    apply Nat.leb_le.
    assumption.
    assumption.
    assumption.
    rewrite tmp.
    simpl.
    rewrite plus_comm.
    simpl.
    apply le_trans with (length (filter (fun x : Z => ifb (In_dec Z.eq_dec (W x) (X (L rmin)))) R)).
    apply length_filter_filter.
    assumption.

    apply forallb_forall.
    intros.
    apply Coq.Bool.Bool.orb_true_iff.
    destruct (in_dec Z.eq_dec (W x) (X (L rmin))) eqn:Xx.
    right.
    apply in_app_iff in H.
    destruct H as [INxR|INxR'].
    unfold prc in OLER.
    apply Coq.Bool.Bool.andb_true_iff in OLER.
    destruct OLER as (tmp3,tmp4).
    apply Coq.Bool.Bool.orb_true_iff in tmp3.
    destruct tmp3 as [tmp3|tmp3].
    rewrite Xrmin in tmp3.
    inversion tmp3.
    apply Coq.Bool.Bool.andb_true_iff in tmp3.
    destruct tmp3 as (tmp5,tmp6).
    apply forallb_forall with (x:=x) in tmp6.
    apply Coq.Bool.Bool.orb_true_iff in tmp6.
    destruct tmp6 as [tmp6|tmp6].
    rewrite Xx in tmp6.
    inversion tmp6.
    assumption.
    apply in_filter_in_l with (fun x : Z => (W rmin <=? W x)%Z).
    assumption.

    apply Coq.Bool.Bool.andb_true_iff in tmp12.
    destruct tmp12 as (tmp5,tmp6).
    apply forallb_forall with (x:=x) in tmp6.
    apply Coq.Bool.Bool.orb_true_iff in tmp6.
    destruct tmp6 as [tmp6|tmp6].
    rewrite Lr'Lrmin in tmp6.
    rewrite Xx in tmp6.
    inversion tmp6.
    rewrite <- Lr'Lrmin.
    assumption.
    apply in_remove_in with Z.eq_dec rmin.
    assumption.
    left.
    reflexivity.
  }
  {
    apply Coq.Bool.Bool.orb_true_iff.
    right.
    apply Coq.Bool.Bool.andb_true_iff.
    split.
    {
      eapply prc_P.
      apply INR'.
      apply MIN.
      apply OLER'.
    }
    {
    apply Coq.Bool.Bool.andb_true_iff.
    split.
    assumption.
    apply forallb_forall.
    simpl.
    intros.

    apply in_app_iff in H.

    destruct H as [IN1|IN2].
    apply Coq.Bool.Bool.orb_true_iff.


    assert (tmp: (W r = W rmin + 1)%Z \/ (W r <= W rmin)%Z).
    omega.
    destruct tmp as [EQ1|LE1].
    destruct (Z_le_dec (W x) (W rmin + 1)) as [le1|le1].
    Focus 2.
    left.
    apply Z.ltb_lt.
    omega.
    assert (tmp: (W x = W rmin + 1)%Z \/ (W x <= W rmin)%Z).
    omega.
    destruct tmp as [EQ2|LE2].
    right.
    apply Coq.Bool.Bool.andb_true_iff.
    assert (Xx: ifb (In_dec Z.eq_dec (W x) (X (L rmin))) = true).
    rewrite EQ2.
    rewrite <- EQ1.
    assumption.
    split.
    assumption.
    apply Coq.Bool.Bool.andb_true_iff.
    split.
    unfold prc in OLER.
    apply Coq.Bool.Bool.andb_true_iff in OLER.
    destruct OLER as (tmp1,tmp2).
    apply Coq.Bool.Bool.orb_true_iff in tmp1.
    destruct tmp1 as [tmp1|tmp1].
    rewrite Xrmin in tmp1.
    inversion tmp1.
    apply Coq.Bool.Bool.andb_true_iff in tmp1.
    destruct tmp1 as (tmp3, tmp4).
    apply forallb_forall with (x:=x) in tmp4.
    apply Coq.Bool.Bool.orb_true_iff in tmp4.
    destruct tmp4 as [tmp4|tmp4].
    rewrite Xx in tmp4.
    inversion tmp4.
    assumption.
    apply in_filter_in_l with (fun x : Z => (W rmin <=? W x)%Z).
    assumption.
    apply Z.leb_le.
    omega.
    assert (tmp: (W x = W rmin)%Z \/ (W x < W rmin)%Z).
    omega.
    destruct tmp as [EQ3|LT3].
    right.
    apply Coq.Bool.Bool.andb_true_iff.
    assert (Xx: ifb (In_dec Z.eq_dec (W x) (X (L rmin))) = true).
    rewrite EQ3.
    assumption.
    split.
    assumption.
    apply Coq.Bool.Bool.andb_true_iff.
    split.
    unfold prc in OLER.
    apply Coq.Bool.Bool.andb_true_iff in OLER.
    destruct OLER as (tmp1,tmp2).
    apply Coq.Bool.Bool.orb_true_iff in tmp1.
    destruct tmp1 as [tmp1|tmp1].
    rewrite Xrmin in tmp1.
    inversion tmp1.
    apply Coq.Bool.Bool.andb_true_iff in tmp1.
    destruct tmp1 as (tmp3, tmp4).
    apply forallb_forall with (x:=x) in tmp4.
    apply Coq.Bool.Bool.orb_true_iff in tmp4.
    destruct tmp4 as [tmp4|tmp4].
    rewrite Xx in tmp4.
    inversion tmp4.
    assumption.
    apply in_filter_in_l with (fun x : Z => (W rmin <=? W x)%Z).
    assumption.
    rewrite EQ1.
    rewrite EQ3.
    apply Z.leb_le.
    omega.
    apply filter_In in IN1.
    destruct IN1 as [INx Wrmin].
    apply Z.leb_le in Wrmin.
    omega.

    unfold prc in OLER.
    apply Coq.Bool.Bool.andb_true_iff in OLER.
    destruct OLER as (tmp1,tmp2).
    apply Coq.Bool.Bool.orb_true_iff in tmp2.
    destruct tmp2 as [tmp2|tmp2].
    left.
    apply forallb_forall with (x:=x) in tmp2.
    apply Z.ltb_lt in tmp2.
    apply Z.ltb_lt.
    omega.
    apply in_filter_in_l with (fun x : Z => (W rmin <=? W x)%Z).
    assumption.
    apply Coq.Bool.Bool.andb_true_iff in tmp2.
    destruct tmp2 as (tmp2,tmp3).
    apply Coq.Bool.Bool.andb_true_iff in tmp3.
    destruct tmp3 as (tmp3,tmp4).
    apply forallb_forall with (x:=x) in tmp4.
    apply Coq.Bool.Bool.orb_true_iff in tmp4.
    destruct tmp4 as [tmp4|tmp4].
    left.
    apply Z.ltb_lt in tmp4.
    apply Z.ltb_lt.
    omega.
    apply Coq.Bool.Bool.andb_true_iff in tmp4.
    destruct tmp4 as (tmp4,tmp5).
    apply Coq.Bool.Bool.andb_true_iff in tmp5.
    destruct tmp5 as (tmp5,tmp6).
    right.
    apply Coq.Bool.Bool.andb_true_iff.
    split.
    assumption.
    apply Coq.Bool.Bool.andb_true_iff.
    split.
    assumption.
    apply Z.leb_le in tmp6.
    apply Z.leb_le.
    omega.
    apply in_filter_in_l with (fun x : Z => (W rmin <=? W x)%Z).
    assumption.

    apply Coq.Bool.Bool.orb_true_iff.
    unfold prc in OLER'.
    apply Coq.Bool.Bool.andb_true_iff in OLER'.
    destruct OLER' as (tmp1,tmp2).
    apply Coq.Bool.Bool.orb_true_iff in tmp2.
    destruct tmp2 as [tmp2|tmp2].
    left.
    apply forallb_forall with (x:=x) in tmp2.
    assumption.
    apply in_remove_in with Z.eq_dec rmin.
    assumption.
    apply Coq.Bool.Bool.andb_true_iff in tmp2.
    destruct tmp2 as (tmp2,tmp3).
    apply Coq.Bool.Bool.andb_true_iff in tmp3.
    destruct tmp3 as (tmp3,tmp4).
    apply forallb_forall with (x:=x) in tmp4.
    apply Coq.Bool.Bool.orb_true_iff in tmp4.
    destruct tmp4 as [tmp4|tmp4].
    left.
    assumption.
    right.
    rewrite <- Lr'Lrmin.
    assumption.
    apply in_remove_in with Z.eq_dec rmin.
    assumption.
  }
}
Qed.

Theorem valid_graph_is_deadlock_free:
  forall n (G: list (Z * list Z * Z)) (R: Z -> Z) (L: Z -> Z) (P: Z -> bool) (X: Z -> list Z)
         (UNQ: NoDup (map snd G))
         (LEN: length G = n)
         (ONE: forall z o O (IN: In (o,O,z) G), one_ob G o)
         (SPARE: forall z o O (IN: In (o,O,z) G) (Po: P o = true), spare_ob G o)
         (OWN: forall z o O (IN: In (o,O,z) G) (INX: In (R o) (X (L o))), own_ob G o)
         (PRC: forall z o O (ING: In (o,O,z) G), prc o O R L P X = true),
    G = nil.
Proof.
  induction n.
  intros.
  destruct G.
  reflexivity.
  inversion LEN.
  (* ========================= n > 0 *)
  {
  simpl in *.
  intros.
  assert (MIN: exists om O1 t1 (INom: In (om,O1,t1) G), 
                forall o (IN: In o (map (fun x => fst (fst x)) G)), Z.le (R om) (R o)).
  {
    assert (MIN: exists min (INl: In min (map (fun x => fst (fst x)) G)), forall x (INl: In x (map (fun x => fst (fst x)) G)), Z.le (R min) (R x)).
    apply list_has_min.
    rewrite map_length.
    rewrite LEN.
    omega.
    destruct MIN as (min,(INmin,MIN)).
    apply in_map_iff in INmin.
    destruct INmin as (x,(fstx,INx)).
    destruct x as ((x1,x2),x3).
    simpl in fstx.
    exists x1, x2, x3, INx.
    rewrite fstx.
    apply MIN.
  }
  destruct MIN as (om,(O1,(t1,(T1,MIN)))).
  assert (T2: exists o2 O2 t2 (INO2: In om O2), In (o2,O2,t2) G).
  {
    apply ONE in T1.
    unfold one_ob in T1.
    apply count_occ_In in T1.
    rewrite <- flat_map_concat_map in T1.
    apply in_flat_map in T1.
    destruct T1 as (x,(INx,INo)).
    destruct x as ((x1,x2),x3).
    exists x1,x2,x3,INo.
    assumption.
  }
  destruct T2 as (o2,(O2,(t2,(INO2,T2)))).

  assert (CNTomO2t2: count_occ node_dec G (o2, O2, t2) = 1).
  {
    apply NoDup_count_occ'.
    apply nodup_map.
    assumption.
    assumption.
  }

 destruct (Z.eq_dec t1 t2) as [t1t2|t1t2].
  (* ========================= t1 = t2 *)
  {
    assert (omo2O1O2: om = o2 /\ O1 = O2).
    {
      assert (EQ: (om,O1) = (o2,O2)).
      apply unique_key_eq with G t1.
      assumption.
      rewrite t1t2.
      assumption.
      assumption.
      inversion EQ.
      auto.
    }
    destruct omo2O1O2 as (omo2,O1O2).
    rewrite <- omo2 in T2.

    assert (PRC_omO2: prc om O2 R L P X = true).
    {
      apply PRC with t2.
      assumption.
    }

    assert (SPR_om: spare_ob G om).
    {
      apply SPARE with t2 O2.
      assumption.
      eapply prc_P.
      apply INO2.
      omega.
      apply PRC_omO2.
    }

    assert (Xom: ifb (In_dec Z.eq_dec (R om) (X (L om))) = true).
    {
      eapply ole_in_X.
      apply INO2.
      omega.
      apply PRC_omO2.
    }

    assert (OCComO2: count_occ Z.eq_dec O2 om = 1).
    {
      eapply ole_X_count_1.
      apply Xom.
      apply Xom.
      apply INO2.
      apply PRC_omO2.
    }

    assert (T3: exists o3 O3 t3 (NEQt2t3: t2 <> t3) (INO3: In om O3), In (o3,O3,t3) G).
    {
      apply two_O2 with (r0:=om) (R:=O1).
      assumption.
      unfold spare_ob in SPR_om.
      assert (tmp: lt 0 (count_occ Z.eq_dec (map (fun x : Z * list Z * Z => fst (fst x)) G) om)).
      apply count_occ_In.
      apply in_map_iff.
      exists (om,O1,t2).
      rewrite O1O2.
      auto.
      omega.
      rewrite O1O2.
      assumption.
      rewrite O1O2.
      rewrite OCComO2.
      omega.
    }
    destruct T3 as (o3,(O3,(t3,(NEQt2t3,(INO3,T3))))).

    assert (OLER: prc om O1 R L P X = true).
    {
      apply PRC with t1.
      assumption.
    }

    assert (OLER': prc o3 O3 R L P X = true).
    {
      apply PRC with t3.
      assumption.
    }

    assert (LrLrmin: L o3 = L om).
    {
      symmetry.
      eapply ole_eqL.
      apply INO3.
      apply MIN.
      apply in_map_iff.
      exists (o3, O3, t3).
      auto.
      apply OLER'.
    }

    assert (Xr: ifb (In_dec Z.eq_dec (R o3) (X (L o3))) = true).
    {
      eapply ole_X.
      apply INO3.
      apply MIN.
      apply in_map_iff.
      exists (o3, O3, t3).
      auto.
      apply OLER'.
    }

    assert (Xrmin: ifb (In_dec Z.eq_dec (R om) (X (L o3))) = true).
    {
      eapply ole_in_X.
      apply INO3.
      apply MIN.
      apply in_map_iff.
      exists (o3, O3, t3).
      auto.
      apply OLER'.
    }

    assert (CNTomO3: count_occ Z.eq_dec O3 om = 1).
    {
      eapply ole_X_count_1 with (o:=o3)(R:=R).
      apply Xr.
      apply Xrmin.
      assumption.
      apply OLER'.
    }

    assert (CNTo3O3t3: count_occ node_dec G (o3, O3, t3) = 1).
    {
      apply NoDup_count_occ'.
      apply nodup_map.
      assumption.
      assumption.
    }

    assert (IND: ((o3,(om::remove Z.eq_dec om ((filter (fun x => Z.leb (R om) (R x)) O2)++O3)),t2)::
                 (remove node_dec (o3,O3,t3) (remove node_dec (om,O2,t2) G))) = nil).
    apply IHn with R L P X.
    {
    simpl.
    apply NoDup_cons.
    assert (tmp:=T2).
    apply unq_nin with (dec:=node_dec) in tmp.
    unfold not in *.
    intros.
    apply tmp.
    apply in_map_iff in H.
    destruct H as (x,(sndx,INx)).
    destruct x.
    exists p.
    apply in_remove_in with (dec:=node_dec) (b:=(o3, O3, t3)).
    simpl in sndx.
    inversion sndx.
    rewrite H in INx.
    assumption.
    assumption.
    simpl.
    apply unq_map_remove.
    apply unq_map_remove.
    assumption.
    }
    {
    simpl.
    rewrite remove_length with (G:=remove node_dec (om, O2, t2) G).
    assert (tmp: S (length (remove node_dec (om, O2, t2) G)) = S n).
    rewrite remove_length with (G:=G).
    assumption.
    assumption.
    assumption.
    omega.
    apply unq_map_remove.
    assumption.
    apply in_in_remove.
    unfold not.
    intros EQ.
    inversion EQ.
    rewrite H2 in NEQt2t3.
    contradiction.
    assumption.
    }
    {
    simpl.
    intros.
    unfold one_ob.
    apply count_occ_In.
    simpl.
    destruct (Z.eq_dec o om) as [omo|omo].
    rewrite omo.
    left.
    reflexivity.
    right.

    assert (INoG: In o (map (fun x => fst (fst x)) G)).
    {
      simpl in IN.
      destruct IN as [EQ1|IN1].
      inversion EQ1.
      rewrite <- H0.
      apply in_map_iff.
      exists (o3, O3, t3).
      auto.
      apply in_map_remove_in with node_dec (om,O2,t2).
      apply in_map_remove_in with node_dec (o3,O3,t3).
      apply in_map_iff.
      exists (o,O,z).
      auto.
    }

    destruct (In_dec Z.eq_dec o O2) as [INoO2|INoO2].
    apply in_app_iff.
    left.
    apply in_in_remove.
    assumption.
    apply in_app_iff.
    left.
    apply filter_In.
    split.
    assumption.
    apply Z.leb_le.
    apply MIN.
    assumption.
    destruct (In_dec Z.eq_dec o O3) as [INoO3|InoO3].
    apply in_app_iff.
    left.
    apply in_in_remove.
    assumption.
    apply in_app_iff.
    right.
    assumption.
    apply in_app_iff.
    right.
    apply remove_concat_map.
    apply remove_concat_map.
    apply count_occ_In with (eq_dec := Z.eq_dec).
    unfold one_ob in ONE.
    apply in_map_iff in INoG.
    destruct INoG as (x,(xo,InxG)).
    destruct x as ((x1,x2),x3).
    simpl in xo.
    rewrite <- xo.
    apply ONE with x3 x2.
    assumption.
    assumption.
    assumption.
    }
    {
    intros.
    assert (INoG: In o (map (fun x => fst (fst x)) G)).
    {
      simpl in IN.
      destruct IN as [EQ1|IN1].
      inversion EQ1.
      rewrite <- H0.
      apply in_map_iff.
      exists (o3, O3, t3).
      auto.
      apply in_map_remove_in with node_dec (om,O2,t2).
      apply in_map_remove_in with node_dec (o3,O3,t3).
      apply in_map_iff.
      exists (o,O,z).
      auto.
    }
    assert (SP: spare_ob_inv ((o3,om :: remove Z.eq_dec om (filter (fun x : Z => (R om <=? R x)%Z) O2 ++ O3),
             t2) :: remove node_dec (o3, O3, t3) (remove node_dec (om, O2, t2) G)) o).
    apply spare_ob_ind1.
    assumption.
    assumption.
    unfold spare_ob_inv.
    right.
    unfold spare_ob in SPARE.
    apply in_map_iff in INoG.
    destruct INoG as (x,(xo,InxG)).
    destruct x as ((x1,x2),x3).
    simpl in xo.
    rewrite <- xo.
    apply SPARE with x3 x2.
    assumption.
    rewrite xo.
    assumption.
    assumption.
    assumption.
    assumption.
    rewrite omo2.
    assumption.
    intros.
    rewrite Z.leb_le.
    apply MIN.
    assumption.
    unfold spare_ob_inv in SP.
    destruct SP as [SP|SP].
    apply count_occ_not_In in SP.
    exfalso.
    apply SP.
    apply in_map_iff.
    exists (o,O,z).
    auto.
    unfold spare_ob.
    assumption.
    }
    {
    intros.
    assert (INoG: In o (map (fun x => fst (fst x)) G)).
    {
      simpl in IN.
      destruct IN as [EQ1|IN1].
      inversion EQ1.
      rewrite <- H0.
      apply in_map_iff.
      exists (o3, O3, t3).
      auto.
      apply in_map_remove_in with node_dec (om,O2,t2).
      apply in_map_remove_in with node_dec (o3,O3,t3).
      apply in_map_iff.
      exists (o,O,z).
      auto.
    }
    apply own_ob_ind1.
    assumption.
    assumption.
    apply in_map_iff in INoG.
    destruct INoG as (x,(xo,InxG)).
    destruct x as ((x1,x2),x3).
    simpl in xo.
    rewrite <- xo.
    apply OWN with x3 x2.
    assumption.
    rewrite xo.
    assumption.
    assumption.
    assumption.
    assumption.
    rewrite omo2.
    assumption.
    intros.
    rewrite Z.leb_le.
    apply MIN.
    assumption.
    }
    {
    intros.
    assert (INoG':=ING).
    assert (INoG: In o (map (fun x => fst (fst x)) G)).
    {
      simpl in ING.
      destruct ING as [EQ1|IN1].
      inversion EQ1.
      rewrite <- H0.
      apply in_map_iff.
      exists (o3, O3, t3).
      auto.
      apply in_map_remove_in with node_dec (om,O2,t2).
      apply in_map_remove_in with node_dec (o3,O3,t3).
      apply in_map_iff.
      exists (o,O,z).
      auto.
    }
    simpl in ING.
    destruct ING as [EQ1|IN1].
    inversion EQ1.
    apply prc_ind1.
    assumption.
    assumption.
    apply MIN.
    assumption.
    assumption.
    rewrite <- H0.
    eapply PRC.
    apply T3.
    apply PRC with z.
    apply in_remove_in with (dec:=node_dec)(b:=(om, O2, t2)).
    apply in_remove_in with (dec:=node_dec)(b:=(o3, O3, t3)).
    assumption.
}
    inversion IND.
  }

  (* ========================= t1 <> t2 *)
  {
    assert (OLER: prc om O1 R L P X = true).
    {
      apply PRC with t1.
      assumption.
    }

    assert (OLER': prc o2 O2 R L P X = true).
    {
      apply PRC with t2.
      assumption.
    }

    assert (LrLrmin: L o2 = L om).
    {
      symmetry.
      eapply ole_eqL.
      apply INO2.
      apply MIN.
      apply in_map_iff.
      exists (o2, O2, t2).
      auto.
      apply OLER'.
    }

    assert (Xr: ifb (In_dec Z.eq_dec (R o2) (X (L o2))) = true).
    {
      eapply ole_X.
      apply INO2.
      apply MIN.
      apply in_map_iff.
      exists (o2, O2, t2).
      auto.
      apply OLER'.
    }

    assert (Xrmin: ifb (In_dec Z.eq_dec (R om) (X (L o2))) = true).
    {
      eapply ole_in_X.
      apply INO2.
      apply MIN.
      apply in_map_iff.
      exists (o2, O2, t2).
      auto.
      apply OLER'.
    }

    assert (O2Mr': spare_ob G o2).
    {
      eapply SPARE.
      apply T2.
      eapply prc_P.
      apply INO2.
      apply MIN.
      apply in_map_iff.
      exists (o2, O2, t2).
      auto.
      apply OLER'.
    }

    assert (OCCrminR': count_occ Z.eq_dec O2 om = 1).
    {
      eapply ole_X_count_1.
      unfold ifb.
      apply Xr.
      apply Xrmin.
      apply INO2.
      apply OLER'.
    }

    assert (OCCt2G: count_occ node_dec G (om, O1, t1) = 1).
    {
      apply NoDup_count_occ'.
      apply nodup_map.
      assumption.
      assumption.
    }

    assert (OCCt3G: count_occ node_dec G (o2, O2, t2) = 1).
    {
      apply NoDup_count_occ'.
      apply nodup_map.
      assumption.
      assumption.
    }

    assert (MIN': forall x0 : Z, In x0 (map (fun x => fst (fst x)) G) -> (R om <=? R x0)%Z = true).
    {
      intros.
      apply Z.leb_le.
      apply MIN.
      assumption.
    }

    assert (IND: (o2,((filter (fun x => Z.leb (R om) (R x)) O1)++(remove Z.eq_dec om O2)),t1)::
                 (remove node_dec (o2,O2,t2) (remove node_dec (om,O1,t1) G)) = nil).
    apply IHn with R L P X.
    simpl.
    {
    apply NoDup_cons.
    assert (tmp:=T1).
    apply unq_nin with (dec:=node_dec) in T1.
    unfold not in *.
    intros.
    apply T1.
    apply in_map_iff in H.
    destruct H as (x,(sndx,INx)).
    destruct x.
    exists p.
    apply in_remove_in with (dec:=node_dec) (b:=(o2, O2, t2)).
    simpl in sndx.
    inversion sndx.
    rewrite H in INx.
    assumption.
    assumption.
    simpl.
    apply unq_map_remove.
    apply unq_map_remove.
    assumption.
    }
    {
    simpl.
    rewrite remove_length with (G:=remove node_dec (om, O1, t1) G).
    assert (tmp: S (length (remove node_dec (om, O1, t1) G)) = S n).
    rewrite remove_length with (G:=G).
    assumption.
    assumption.
    assumption.
    omega.
    apply unq_map_remove.
    assumption.
    apply in_in_remove.
    unfold not.
    intros EQ.
    inversion EQ.
    rewrite H2 in t1t2.
    contradiction.
    assumption.
   }
   {
    simpl.
    intros.
    unfold one_ob.
    assert (INr1: In o (map (fun x => fst (fst x)) G)).
    {
    destruct IN as [EQ|IN].
    symmetry in EQ.
    inversion EQ.
    apply in_map_iff.
    exists (o2, O2, t2).
    auto.
    apply in_map_remove_in with node_dec (om,O1,t1).
    apply in_map_remove_in with node_dec (o2,O2,t2).
    apply in_map_iff.
    exists (o, O, z).
    auto.
    }
    simpl in *.
    apply count_occ_In.
    apply in_app_iff.
    destruct (In_dec Z.eq_dec o O1) as [INr|Inr].
    left.
    apply in_app_iff.
    left.
    apply filter_In.
    split.
    assumption.
    apply Z.leb_le.
    apply MIN.
    assumption.
    destruct (Z.eq_dec o om).
    {
    rewrite e.
    assert (O2Ormin: own_ob G om).
    {
    apply in_map_iff in INr1.
    destruct INr1 as (x,(xo,InxG)).
    destruct x as ((x1,x2),x3).
    simpl in xo.
    apply OWN with x3 x2.
    rewrite <- e.
    rewrite <- xo.
    assumption.
    rewrite <- LrLrmin.
    unfold ifb in Xrmin.
    destruct (in_dec Z.eq_dec (R om) (X (L o2))).
    assumption.
    inversion Xrmin.
    }
    assert (tmp: 1 < count_occ Z.eq_dec (concat (map (fun x => snd (fst x)) G)) om).
    {
    unfold own_ob in O2Ormin.
    assert (tmp: 2 <= count_occ Z_eq_dec (map (fun x => fst (fst x)) G) om).
    destruct IN as [i1|i2].
    inversion i1.
    rewrite H0 in T2.
    rewrite e in T2.
    apply in_in_count2 with (om,O1,t1) (om, O2, t2) .
    unfold not.
    intros.
    inversion H.
    contradiction.
    reflexivity.
    assumption.
    assumption.
    reflexivity.
    apply in_in_count2 with (om,O,z) (om,O1,t1).
    unfold not.
    intros.
    inversion H.
    rewrite <- H2 in i2.
    assert (NEX: ~ exists v', In (v',t1) (remove node_dec (om, O1, t1) G)).
    apply unq_nin.
    assumption.
    assumption.
    apply NEX.
    exists (o,O).
    apply in_remove_in with node_dec (o2, O2, t2).
    rewrite <- H2.
    assumption.
    reflexivity.
    rewrite <- e.
    apply in_remove_in with node_dec (om, O1, t1).
    apply in_remove_in with node_dec (o2, O2, t2).
    assumption.
    assumption.
    reflexivity.
    omega.
    }

    assert (tmp1: exists r'' R'' t'' (NEQ: t2 <> t'') (INR'': In om R''), In (r'',R'',t'') G).
    {
      apply two_O2 with (r0:=o2) (R:=O2).
      assumption.
      assumption.
      assumption.
      apply ole_X_count with (o:=o2) (R:=R) (L:=L) (X:=X) (P:=P).
      apply ole_X with (R:=O2) (r':= om) (P:=P).
      assumption.
      apply MIN.
      apply in_map_iff.
      exists (o2, O2, t2).
      auto.
      apply PRC with t2.
      assumption.
      assumption.
      apply PRC with t2.
      assumption.
    }

    destruct tmp1 as (t'',(R'',(r'',(NEQ,(INR'',ING))))).
    apply in_app_iff.
    apply in_app_iff.
    right.
    rewrite remove_remove.
    apply remove_concat_map.
    rewrite <- flat_map_concat_map.
    apply in_flat_map.
    exists (t'', R'', r'').
    split.
    apply in_in_remove.
    unfold not.
    intros.
    inversion H.
    rewrite <- H3 in NEQ.
    contradiction.
    assumption.
    simpl.
    assumption.
    rewrite <- e.
    assumption.
    }
    {
    destruct (In_dec Z.eq_dec o O2) as [INr'|Inr'].
    left.
    apply in_app_iff.
    right.
    apply in_in_remove.
    assumption.
    assumption.
    right.
    assert (tmp: 0 < count_occ Z.eq_dec (concat (map (fun x => snd (fst x)) G)) o).
    {
      destruct IN as [i1|i2].
      inversion i1.
      eapply ONE.
      rewrite <- H0.
      apply T2.
      eapply ONE.
      apply in_remove_in with node_dec (om, O1, t1).
      apply in_remove_in with node_dec (o2, O2, t2).
      apply i2.
    }
    apply remove_concat_map.
    apply remove_concat_map.
    apply count_occ_In with (eq_dec:=Z.eq_dec). 
    assumption.
    assumption.
    assumption.
    }
    }
    {
    intros.
    assert (INoG: In o (map (fun x => fst (fst x)) G)).
    {
      simpl in IN.
      destruct IN as [EQ1|IN1].
      inversion EQ1.
      rewrite <- H0.
      apply in_map_iff.
      exists (o2, O2, t2).
      auto.
      apply in_map_remove_in with node_dec (om,O1,t1).
      apply in_map_remove_in with node_dec (o2,O2,t2).
      apply in_map_iff.
      exists (o,O,z).
      auto.
    }
    assert (SP: spare_ob_inv ((o2,filter (fun x : Z => (R om <=? R x)%Z) O1 ++ remove Z.eq_dec om O2, t1)
     :: remove node_dec (o2, O2, t2) (remove node_dec (om, O1, t1) G)) o).
    apply spare_ob_ind2.
    assumption.
    assumption.
    unfold spare_ob_inv.
    right.
    unfold spare_ob in SPARE.
    apply in_map_iff in INoG.
    destruct INoG as (x,(xo,InxG)).
    destruct x as ((x1,x2),x3).
    simpl in xo.
    rewrite <- xo.
    apply SPARE with x3 x2.
    assumption.
    rewrite xo.
    assumption.
    assumption.
    assumption.
    assumption.
    assumption.
    unfold spare_ob_inv in SP.
    destruct SP as [SP|SP].
    apply count_occ_not_In in SP.
    exfalso.
    apply SP.
    apply in_map_iff.
    exists (o,O,z).
    auto.
    unfold spare_ob.
    assumption.
    }
    {
    intros.
    assert (INoG: In o (map (fun x => fst (fst x)) G)).
    {
      simpl in IN.
      destruct IN as [EQ1|IN1].
      inversion EQ1.
      rewrite <- H0.
      apply in_map_iff.
      exists (o2, O2, t2).
      auto.
      apply in_map_remove_in with node_dec (om,O1,t1).
      apply in_map_remove_in with node_dec (o2,O2,t2).
      apply in_map_iff.
      exists (o,O,z).
      auto.
    }
    apply own_ob_ind2.
    assumption.
    assumption.
    apply in_map_iff in INoG.
    destruct INoG as (x,(xo,InxG)).
    destruct x as ((x1,x2),x3).
    simpl in xo.
    rewrite <- xo.
    apply OWN with x3 x2.
    assumption.
    rewrite xo.
    assumption.
    assumption.
    assumption.
    assumption.
    assumption.
    }
    {
    intros.
    assert (INoG':=ING).
    assert (INoG: In o (map (fun x => fst (fst x)) G)).
    {
      simpl in ING.
      destruct ING as [EQ1|IN1].
      inversion EQ1.
      rewrite <- H0.
      apply in_map_iff.
      exists (o2, O2, t2).
      auto.
      apply in_map_remove_in with node_dec (om,O1,t1).
      apply in_map_remove_in with node_dec (o2,O2,t2).
      apply in_map_iff.
      exists (o,O,z).
      auto.
    }
    simpl in ING.
    destruct ING as [EQ1|IN1].
    inversion EQ1.
    apply prc_ind2.
    assumption.
    assumption.
    apply MIN.
    assumption.
    assumption.
    rewrite <- H0.
    eapply PRC.
    apply T2.
    apply PRC with z.
    apply in_remove_in with (dec:=node_dec)(b:=(om, O1, t1)).
    apply in_remove_in with (dec:=node_dec)(b:=(o2, O2, t2)).
    assumption.
    }
  inversion IND.
}}
Qed.

