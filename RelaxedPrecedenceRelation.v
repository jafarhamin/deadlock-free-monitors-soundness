Add LoadPath "proofs".

Require Import List.
Require Import ZArith.
Require Import Coq.Init.Nat.
Require Import Coq.Sorting.Permutation.
Require Import Util_Z.
Require Import Util_list.

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

Definition own_ob (G: list (Z * list Z * Z)) o :=
  le (count_occ Z_eq_dec (map (fun x => fst (fst x)) G) o) (count_occ Z.eq_dec (concat (map (fun x => snd (fst x)) G)) o).

Definition spare_ob (G: list (Z * list Z * Z)) o :=
  lt (count_occ Z_eq_dec (map (fun x => fst (fst x)) G) o) (count_occ Z.eq_dec (concat (map (fun x => snd (fst x)) G)) o).

Definition list_Z_dec (lz1 lz2: (list Z * Z)) : {lz1 = lz2} + {lz1 <> lz2}.
Proof.
  decide equality.
  apply Z_eq_dec.
  apply list_eq_dec.
  apply Z_eq_dec.
Qed.

Definition prc (o:Z) (O: list Z) (R: Z -> Z) (P: Z -> bool) (X: Z -> option Z) : bool :=
  match (X o) with
    | None => forallb (fun x => Z.ltb (R o) (R x)) O
    | Some xo => andb (leb (length (filter (fun x => Z.leb (R x) (Z.max (R o) xo)) O)) 1)
                (andb (forallb (fun x => orb (Z.ltb (Z.max (R o) xo) (R x)) 
                                             (leb_o (Z.max (R o) xo) (X x))) O)
                (orb (forallb (fun x => Z.ltb (R o) (R x)) O)
                (P o)))
  end.

Lemma prc_perm:
  forall O O' o R P X
         (PRC: prc o O R P X = true)
         (PERM: Permutation O' O),
    prc o O' R P X = true.
Proof.
  unfold prc.
  intros.
  destruct (X o).
  apply Coq.Bool.Bool.andb_true_iff in PRC.
  destruct PRC as (PRC1,PRC2).
  apply Coq.Bool.Bool.andb_true_iff in PRC2.
  destruct PRC2 as (PRC2,PRC3).
  apply Coq.Bool.Bool.orb_true_iff in PRC3.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  rewrite prem_length_eq with (l':=O); assumption.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  apply forallb_forall.
  intros.
  apply forallb_forall with (x:=x) in PRC2.
  assumption.
  apply Permutation_in with O'; assumption.
  apply Coq.Bool.Bool.orb_true_iff.
  destruct PRC3 as [PRC3|PRC3].
  left.
  apply forallb_forall.
  intros.
  apply forallb_forall with (x:=x) in PRC3.
  assumption.
  apply Permutation_in with O'; assumption.
  right.
  assumption.
  apply forallb_forall.
  intros.
  apply forallb_forall with (x:=x) in PRC.
  assumption.
  apply Permutation_in with O'; assumption.
Qed.


Lemma prc_P:
  forall R o o' O P X
         (PRC: prc o O R P X = true)
         (IN: In o' O)
         (LE: Z.le (R o') (R o)),
    P o = true.
Proof.
  unfold prc.
  intros.
  destruct (X o).
  apply Coq.Bool.Bool.andb_true_iff in PRC.
  destruct PRC as (PRC1,PRC2).
  apply Coq.Bool.Bool.andb_true_iff in PRC2.
  destruct PRC2 as (PRC2,PRC3).
  apply Coq.Bool.Bool.orb_true_iff in PRC3.
  destruct PRC3 as [PRC3|PRC3].
  apply forallb_forall with (x:=o') in PRC3.
  apply Z.ltb_lt in PRC3.
  omega.
  assumption.
  assumption.
  apply forallb_forall with (x:=o') in PRC.
  apply Z.ltb_lt in PRC.
  omega.
  assumption.
Qed.


Lemma prc_X:
  forall R o o' O P X
         (IN: In o O)
         (EQR: Z.le (R o) (R o'))
         (PRC: prc o' O R P X = true),
   X o <> None.
Proof.
  unfold prc.
  intros.
  destruct (X o').
  apply Coq.Bool.Bool.andb_true_iff in PRC.
  destruct PRC as (PRC1,PRC2).
  apply Coq.Bool.Bool.andb_true_iff in PRC2.
  destruct PRC2 as (PRC2,PRC3).
  apply Coq.Bool.Bool.orb_true_iff in PRC3.
  apply forallb_forall with (x:=o) in PRC2.
  apply Coq.Bool.Bool.orb_true_iff in PRC2.
  destruct PRC2 as [PRC|PRC].
  apply Z.ltb_lt in PRC.
  apply Z.max_lub_lt_iff in PRC.
  omega.
  unfold leb_o in PRC.
  destruct (X o).
  apply some_none.
  inversion PRC.
  assumption.
  apply forallb_forall with (x:=o) in PRC.
  apply Z.ltb_lt in PRC.
  omega.
  assumption.
Qed.


Lemma ole_X_count:
  forall O o o' R P X
         (EQR: Z.le (R o') (R o))
         (PRC: prc o O R P X = true),
    count_occ Z.eq_dec O o' <= 1.
Proof.
  unfold prc.
  intros.
  destruct (X o).
  apply Coq.Bool.Bool.andb_true_iff in PRC.
  destruct PRC as (PRC1,PRC2).
  apply Coq.Bool.Bool.andb_true_iff in PRC2.
  destruct PRC2 as (PRC2,PRC3).
  apply Coq.Bool.Bool.orb_true_iff in PRC3.
  apply le_trans with (length (filter (fun x : Z => (R x <=? Z.max (R o) z)%Z) O)).
  apply count_filter_len.
  apply Z.leb_le.
  apply Z.le_trans with (R o).
  assumption.
  apply Z.le_max_l.
  apply Nat.leb_le in PRC1.
  assumption.
  destruct (count_occ Z.eq_dec O o') eqn:CNT.
  omega.
  apply forallb_forall with (x:=o') in PRC.
  apply Z.ltb_lt in PRC.
  omega.
  rewrite count_occ_In with (eq_dec := Z.eq_dec).
  omega.
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
  forall G r0 rmin r' R' R'' t2 t3
         (NEQ: t2 <> t3)
         (INr': In (r', R'', t3) G)
         (O2M: spare_ob_inv G r0)
         (CNT1:count_occ Z.eq_dec R' rmin = 1)
         (CNT2:count_occ Z.eq_dec R'' rmin = 1)
         (CNT3: count_occ node_dec G (r', R'', t3) = 1)
         (CNT4: count_occ node_dec G (rmin, R', t2) = 1),
      spare_ob_inv ((r', rmin :: remove Z.eq_dec rmin (R' ++ R''), t2)
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
  omega.
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
  omega.
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


Lemma length_filter_le A f f':
  forall (l: list A)
         (FIL: forall x (IN: In x l), f x = true -> f' x = true),
    le (length (filter f l)) (length (filter f' l)).
Proof.
  induction l.
  simpl.
  intros.
  omega.
  simpl.
  intros.
  assert (G1: length (filter f l) <= length (filter f' l)).
  {
  apply IHl.
  intros.
  apply FIL.
  right.
  assumption.
  assumption.
  }
  assert (F1:=FIL).
  specialize F1 with a.
  destruct (f a).
  rewrite F1.
  simpl.
  omega.
  left.
  reflexivity.
  reflexivity.
  destruct (f' a).
  simpl.
  omega.
  assumption.
Qed.


Lemma own_ob_ind1:
  forall G r0 rmin r' R' R'' t2 t3
         (NEQ: t2 <> t3)
         (INr': In (r', R'', t3) G)
         (O2M: own_ob G r0)
         (CNT1:count_occ Z.eq_dec R' rmin = 1)
         (CNT2:count_occ Z.eq_dec R'' rmin = 1)
         (CNT3: count_occ node_dec G (r', R'', t3) = 1)
         (CNT4: count_occ node_dec G (rmin, R', t2) = 1),
      own_ob ((r', rmin :: remove Z.eq_dec rmin (R' ++ R''), t2)
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
  omega.
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
  omega.
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


Lemma prc_has_X:
  forall O o o' W P X
         (PRC: prc o' O W P X = true)
         (IN: In o O)
         (WLE: Z.le (W o) (W o')),
    exists xo, X o = Some xo.
Proof.
  unfold prc.
  intros.
  destruct (X o').
  apply Coq.Bool.Bool.andb_true_iff in PRC.
  destruct PRC as (PRC1,PRC2).
  apply Coq.Bool.Bool.andb_true_iff in PRC2.
  destruct PRC2 as (PRC2,PRC3).
  apply Coq.Bool.Bool.orb_true_iff in PRC3.
  apply forallb_forall with (x:=o) in PRC2.
  apply Coq.Bool.Bool.orb_true_iff in PRC2.
  destruct PRC2 as [PRC2|PRC2].
  apply Z.ltb_lt in PRC2.
  apply Z.max_lub_lt_iff in PRC2.
  omega.
  unfold leb_o in PRC2.
  destruct (X o) eqn:Xo.
  exists z0.
  reflexivity.
  inversion PRC2.
  assumption.
  apply forallb_forall with (x:=o) in PRC.
  apply Z.ltb_lt in PRC.
  omega.
  assumption.
Qed.


Lemma prc_le_X:
  forall O o o' xo xo' W P X
         (PRC: prc o' O W P X = true)
         (XO': X o' = Some xo')
         (XO': X o = Some xo)
         (IN: In o O)
         (WLE: Z.le (W o) (W o')),
    Z.le (Z.max (W o') xo') xo.
Proof.
  unfold prc.
  intros.
  rewrite XO' in PRC.
  apply Coq.Bool.Bool.andb_true_iff in PRC.
  destruct PRC as (PRC1,PRC2).
  apply Coq.Bool.Bool.andb_true_iff in PRC2.
  destruct PRC2 as (PRC2,PRC3).
  apply Coq.Bool.Bool.orb_true_iff in PRC3.
  apply forallb_forall with (x:=o) in PRC2.
  apply Coq.Bool.Bool.orb_true_iff in PRC2.
  destruct PRC2 as [PRC2|PRC2].
  apply Z.ltb_lt in PRC2.
  apply Z.max_lub_lt_iff in PRC2.
  omega.
  unfold leb_o in PRC2.
  rewrite XO'0 in PRC2.
  apply Z.leb_le in PRC2.
  assumption.
  assumption.
Qed.


Lemma prc_ind1:
  forall rmin r' R' R'' W P X
         (INR'': In rmin R'')
         (INR': In rmin R')
         (Rrmin: Z.le (W rmin) (W r'))
         (OLER': prc rmin R' W P X = true)
         (OLER'': prc r' R'' W P X = true),
    prc r' (rmin :: remove Z.eq_dec rmin (R' ++ R'')) W P X = true.
Proof.
  intros.
  assert (P1:=OLER'').
  assert (P5:=OLER').
  unfold prc.
  unfold prc in P1.
  unfold prc in P5.
  destruct (X r') eqn:Xr'.
  Focus 2.
  apply forallb_forall with (x:=rmin) in P1.
  apply Z.ltb_lt in P1.
  omega.
  assumption.
  apply Coq.Bool.Bool.andb_true_iff in P1.
  destruct P1 as (PRC1,PRC2).
  apply Coq.Bool.Bool.andb_true_iff in PRC2.
  destruct PRC2 as (PRC2,PRC3).
  apply Coq.Bool.Bool.orb_true_iff in PRC3.

  assert (xrmin: exists xrm, X rmin = Some xrm).
  {
  apply prc_has_X with (O:=R'') (o':=r') (W:=W) (P:=P); assumption.
  }
  destruct xrmin as (xrm, xrmin).

  rewrite xrmin in P5.
  apply Coq.Bool.Bool.andb_true_iff in P5.
  destruct P5 as (PRC5,PRC6).
  apply Coq.Bool.Bool.andb_true_iff in PRC6.
  destruct PRC6 as (PRC6,PRC7).
  apply Coq.Bool.Bool.orb_true_iff in PRC7.

  assert (CNTR': count_occ Z.eq_dec R' rmin <= 1).
  {
  eapply ole_X_count with (R:=W) (o:=rmin) (P:=P) (X:=X); try assumption.
  omega.
  }

  assert (CNTR'': count_occ Z.eq_dec R'' rmin <= 1).
  {
  eapply ole_X_count with (R:=W) (o:=r').
  omega.
  apply OLER''.
  }

  assert (LE1: (Z.max (W r') z <= xrm)%Z).
  {
  apply prc_le_X with (O:=R'') (o:=rmin) (P:=P) (X:=X); try assumption.
  }

  apply Coq.Bool.Bool.andb_true_iff.
  split.
  {
  apply Nat.leb_le.
  simpl.
  destruct ((W rmin <=? Z.max (W r') z)%Z) eqn:le1.
  Focus 2.
  apply Z_leb_falseL in le1.
  apply Z.max_lub_lt_iff in le1.
  omega.
  simpl.
  destruct (filter (fun x : Z => (W x <=? Z.max (W r') z)%Z)
      (remove Z.eq_dec rmin (R' ++ R''))) eqn:FIL.
  simpl.
  omega.
    assert (CO: In z0 (filter (fun x : Z => (W x <=? Z.max (W r') z)%Z)
      (remove Z.eq_dec rmin (R' ++ R'')))).
    {
    rewrite FIL.
    left.
    reflexivity.
    }

    apply filter_In in CO.
    destruct CO as (CO1,CO2).
    rewrite remove_app in CO1.
    apply in_app_iff in CO1.
    destruct CO1 as [CO1|CO1].
    {
    destruct (Z.eq_dec z0 rmin).
    exfalso.
    eapply remove_In.
    rewrite e in *.
    apply CO1.

    assert (IN1: In rmin (filter (fun x : Z => (W x <=? Z.max (W r') z)%Z) R')).
    {
    apply filter_In.
    split.
    assumption.
    assumption.
    }
    assert (IN2: In z0 (filter (fun x : Z => (W x <=? Z.max (W r') z)%Z) R')).
    {
    apply filter_In.
    split.
    eapply in_remove_in.
    apply CO1.
    assumption.
    }

    assert (G1: length (filter (fun x : Z => (W x <=? Z.max (W r') z)%Z) R') <= 1).
    {
    apply le_trans with (length (filter (fun x : Z => (W x <=? Z.max (W rmin) xrm)%Z) R')).
    apply length_filter_le.
    intros.
    apply Z.leb_le.
    apply Z.leb_le in H.
    apply Z.le_trans with (Z.max (W r') z).
    assumption.
    apply Z.le_trans with xrm.
    assumption.
    apply Z.max_le_iff.
    omega.
    unfold prc in OLER'.
    rewrite xrmin in OLER'.
    apply Coq.Bool.Bool.andb_true_iff in OLER'.
    destruct OLER' as (OLER',OLER'1).
    apply Nat.leb_le.
    assumption.
    }
    destruct (filter (fun x : Z => (W x <=? Z.max (W r') z)%Z) R') eqn:FIL2.
    inversion IN1.
    destruct l0.
    simpl in *.
    destruct IN1 as [IN1|F].
    destruct IN2 as [IN2|F].
    omega.
    contradiction.
    contradiction.
    simpl in G1.
    omega.
    }

    destruct (Z.eq_dec z0 rmin).
    exfalso.
    eapply remove_In.
    rewrite e in CO1.
    apply CO1.

    assert (IN1: In rmin (filter (fun x : Z => (W x <=? Z.max (W r') z)%Z) R'')).
    {
    apply filter_In.
    split.
    assumption.
    assumption.
    }
    assert (IN2: In z0 (filter (fun x : Z => (W x <=? Z.max (W r') z)%Z) R'')).
    {
    apply filter_In.
    split.
    eapply in_remove_in.
    apply CO1.
    assumption.
    }

    destruct (filter (fun x : Z => (W x <=? Z.max (W r') z)%Z) R'') eqn:FIL2.
    inversion IN1.
    destruct l0.
    simpl in *.
    destruct IN1 as [IN1|F].
    destruct IN2 as [IN2|F].
    omega.
    contradiction.
    contradiction.
    simpl in PRC1.
    inversion PRC1.
    }

    apply Coq.Bool.Bool.andb_true_iff.
    split.
    {
    apply forallb_forall.
    intros.
    destruct H as [EQ|IN].
    rewrite <- EQ.
    apply forallb_forall with (x:=rmin) in PRC2.
    assumption.
    assumption.
    rewrite remove_app in IN.
    apply in_app_iff in IN.
    destruct (Z.eq_dec x rmin).
    {
    rewrite e in IN.
    destruct IN as [IN1|IN1].
    exfalso.
    eapply remove_In.
    apply IN1.
    exfalso.
    eapply remove_In.
    apply IN1.
    }

    destruct IN as [IN1|IN1].
    {
    destruct (Z_le_dec (W x) xrm).
    {
    apply forallb_forall with (x:=x) in PRC6.
    apply Coq.Bool.Bool.orb_true_iff in PRC6.
    destruct PRC6 as [P4|P4].
    apply Z.ltb_lt in P4.
    apply Z.max_lub_lt_iff in P4.
    omega.
    unfold leb_o in *.
    destruct (X x).
    apply Coq.Bool.Bool.orb_true_iff.
    right.
    apply Z.leb_le.
    apply Z.le_trans with xrm.
    assumption.
    apply Z.leb_le in P4.
    apply Z.max_lub_iff in P4.
    omega.
    inversion P4.
    eapply in_remove_in.
    apply IN1.
    }
    apply Coq.Bool.Bool.orb_true_iff.
    left.
    apply Z.ltb_lt.
    apply Z.le_lt_trans with xrm.
    assumption.
    omega.
    }
    apply forallb_forall with (x:=x) in PRC2.
    assumption.
    eapply in_remove_in.
    apply IN1.
    }
    apply Coq.Bool.Bool.orb_true_iff.
    right.
    destruct PRC3 as [P3|P3].
    apply forallb_forall with (x:=rmin) in P3.
    apply Z.ltb_lt in P3.
    omega.
    assumption.
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
  forall G r0 rmin r R R' t1 t2
         (NEQ: t1 <> t2)
         (IN: In r0 (map (fun x => fst (fst x)) G))
         (O2M: spare_ob_inv G r0)
         (CNT1: count_occ Z.eq_dec R' rmin = 1)
         (CNT3: count_occ node_dec G (r, R', t2) = 1)
         (CNT4: count_occ node_dec G (rmin, R, t1) = 1),
      spare_ob_inv ((r,R ++ remove Z.eq_dec rmin R', t1)
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
  omega.
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
  omega.
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
  rewrite rmr0 in CNT1.
  rewrite CNT1 in O2M.
  omega.
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
  omega.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.


Lemma own_ob_ind2:
  forall G r0 rmin r R R' t1 t2
         (NEQ: t1 <> t2)
         (IN: In (r, R', t2) G)
         (O2M: own_ob G r0)
         (CNT1: count_occ Z.eq_dec R' rmin = 1)
         (CNT2: count_occ node_dec G (r, R', t2) = 1)
         (CNT3: count_occ node_dec G (rmin, R, t1) = 1),
      own_ob ((r, R ++ remove Z.eq_dec rmin R', t1)
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
  omega.
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
  omega.
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
  rewrite rmr0 in CNT1.
  rewrite CNT1 in O2M.
  simpl in *.
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
  omega.
  destruct i as [EQ1|IN1].
  rewrite EQ1 in rr0.
  contradiction.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
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
  forall rmin r R R' W P X
         (INR': In rmin R')
         (MIN: Z.le (W rmin) (W r))
         (OLER: prc rmin R W P X = true)
         (OLER': prc r R' W P X = true),
    prc r (R ++ remove Z.eq_dec rmin R') W P X = true.
Proof.
  intros.
  assert (P1:=OLER).
  assert (P5:=OLER').
  unfold prc.
  unfold prc in P1.
  unfold prc in P5.
  destruct (X r) eqn:Xr.
  Focus 2.
  apply forallb_forall with (x:=rmin) in P5.
  apply Z.ltb_lt in P5.
  omega.
  assumption.
  apply Coq.Bool.Bool.andb_true_iff in P5.
  destruct P5 as (PRC1,PRC2).
  apply Coq.Bool.Bool.andb_true_iff in PRC2.
  destruct PRC2 as (PRC2,PRC3).
  apply Coq.Bool.Bool.orb_true_iff in PRC3.

  assert (xrmin: exists xrm, X rmin = Some xrm).
  {
  apply prc_has_X with (O:=R') (o':=r) (W:=W) (P:=P); assumption.
  }
  destruct xrmin as (xrm, xrmin).

  rewrite xrmin in P1.
  apply Coq.Bool.Bool.andb_true_iff in P1.
  destruct P1 as (PRC5,PRC6).
  apply Coq.Bool.Bool.andb_true_iff in PRC6.
  destruct PRC6 as (PRC6,PRC7).
  apply Coq.Bool.Bool.orb_true_iff in PRC7.

  assert (CNTR': count_occ Z.eq_dec R rmin <= 1).
  {
  eapply ole_X_count with (R:=W) (o:=rmin) (P:=P) (X:=X); try assumption.
  omega.
  }

  assert (CNTR'': count_occ Z.eq_dec R' rmin <= 1).
  {
  eapply ole_X_count with (R:=W) (o:=r).
  omega.
  apply OLER'.
  }

  assert (LE1: (Z.max (W r) z <= xrm)%Z).
  {
  apply prc_le_X with (O:=R') (o:=rmin) (P:=P) (X:=X); try assumption.
  }

  apply Coq.Bool.Bool.andb_true_iff.
  split.
  {
    apply Nat.leb_le.
    rewrite filter_app.
    assert (G1: length (filter (fun x : Z => (W x <=? Z.max (W r) z)%Z) (remove Z.eq_dec rmin R')) = 0).
    {
    destruct (filter (fun x : Z => (W x <=? Z.max (W r) z)%Z) (remove Z.eq_dec rmin R')) eqn:FIL.
    simpl.
    reflexivity.
    assert (G1: In z0 (filter (fun x : Z => (W x <=? Z.max (W r) z)%Z) (remove Z.eq_dec rmin R'))).
    {
    rewrite FIL.
    left.
    reflexivity.
    }
    apply filter_In in G1.
    destruct G1 as (G1,G2).
    destruct (Z.eq_dec z0 rmin).
    rewrite e in G1.
    exfalso.
    eapply remove_In.
    apply G1.

    apply Nat.leb_le in PRC1.
    assert (G3: In rmin (filter (fun x : Z => (W x <=? Z.max (W r) z)%Z) R')).
    {
    apply filter_In.
    split.
    assumption.
    apply Z.leb_le.
    apply Z.max_le_iff.
    left.
    assumption.
    }
    assert (G4: In z0 (filter (fun x : Z => (W x <=? Z.max (W r) z)%Z) R')).
    {
    apply filter_In.
    split.
    eapply in_remove_in.
    apply G1.
    assumption.
    }

    destruct (filter (fun x : Z => (W x <=? Z.max (W r) z)%Z) R') eqn:FIL2.
    inversion G3.
    destruct l0.
    destruct G3 as [G3|F].
    destruct G4 as [G4|F].
    omega.
    inversion F.
    inversion F.
    simpl in PRC1.
    omega.
    }

    assert (LE1': (Z.max (W r) z <= xrm)%Z).
    {
    apply prc_le_X with (O:=R') (o:=rmin) (P:=P) (X:=X); try assumption.
    }

    assert (G2: length (filter (fun x : Z => (W x <=? Z.max (W r) z)%Z) R) <= 1).
    {
    apply le_trans with (length (filter (fun x : Z => (W x <=? Z.max (W rmin) xrm)%Z) R)).
    apply length_filter_le.
    intros.
    apply Z.leb_le in H.
    apply Z.leb_le.
    apply Z.le_trans with (Z.max (W r) z).
    assumption.
    apply Z.le_trans with xrm.
    assumption.
    apply Z.max_le_iff.
    omega.
    apply Nat.leb_le.
    assumption.
    }
    rewrite length_app.
    rewrite G1.
    omega.
    }

    apply Coq.Bool.Bool.andb_true_iff.
    split.
    {
    apply forallb_forall.
    intros.
    apply in_app_iff in H.
    destruct H as [INxR|INxR'].
    {
    apply Coq.Bool.Bool.orb_true_iff.
    apply forallb_forall with (x:=x) in PRC6.
    apply Coq.Bool.Bool.orb_true_iff in PRC6.
    destruct PRC6 as [PRC6|PRC6].
    apply Z.ltb_lt in PRC6.
    left.
    apply Z.ltb_lt.
    apply Z.le_lt_trans with xrm.
    assumption.
    apply Z.max_lub_lt_iff in PRC6.
    omega.
    right.
    unfold leb_o in *.
    destruct (X x).
    apply Z.leb_le.
    apply Z.le_trans with xrm.
    assumption.
    apply Z.leb_le in PRC6.
    apply Z.max_lub_iff in PRC6.
    omega.
    assumption.
    assumption.
    }
    apply forallb_forall with (x:=x) in PRC2.
    assumption.
    eapply in_remove_in.
    apply INxR'.
    }

    apply Coq.Bool.Bool.orb_true_iff.
    destruct PRC3 as [PRC3|PRC3].
    apply forallb_forall with (x:=rmin) in PRC3.
    apply Z.ltb_lt in PRC3.
    omega.
    assumption.
    right.
    assumption.
Qed.


Theorem valid_graph_is_deadlock_free:
  forall n (G: list (Z * list Z * Z)) (R: Z -> Z) (P: Z -> bool) (X: Z -> option Z)
         (UNQ: NoDup (map snd G))
         (LEN: length G = n)
         (ONE: forall z o O (IN: In (o,O,z) G), one_ob G o)
         (SPARE: forall z o O (IN: In (o,O,z) G) (Po: P o = true), spare_ob G o)
         (OWN: forall z o O (IN: In (o,O,z) G) (INX: X o <> None), own_ob G o)
         (PRC: forall z o O (ING: In (o,O,z) G), prc o O R P X = true),
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

    assert (PRC_omO2: prc om O2 R P X = true).
    {
      apply PRC with t2.
      assumption.
    }

    assert (SPR_om: spare_ob G om).
    {
      apply SPARE with t2 O2.
      assumption.
      eapply prc_P.
      apply PRC_omO2.
      apply INO2.
      omega.
    }

    assert (CNTomO2': count_occ Z.eq_dec O2 om = 1).
    {
    assert (OCComO2: count_occ Z.eq_dec O2 om <= 1).
    {
      eapply ole_X_count; try assumption.
      reflexivity.
      apply PRC_omO2.
    }
    apply count_occ_In with (eq_dec := Z.eq_dec) in INO2.
    destruct (count_occ Z.eq_dec O2 om).
    omega.
    destruct n0.
    omega.
    omega.
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
      omega.
    }
    destruct T3 as (o3,(O3,(t3,(NEQt2t3,(INO3,T3))))).

    assert (OLER: prc om O1 R P X = true).
    {
      apply PRC with t1.
      assumption.
    }

    assert (OLER': prc o3 O3 R P X = true).
    {
      apply PRC with t3.
      assumption.
    }

    assert (G2: Z.le (R om) (R o3)).
    {
    apply MIN.
    apply in_map_iff.
    exists (o3, O3, t3).
    auto.
    }

    assert (CNTomO3: count_occ Z.eq_dec O3 om <= 1).
    {
      eapply ole_X_count with (o:=o3)(R:=R); try assumption.
      apply OLER'.
    }

    assert (CNTomO3': count_occ Z.eq_dec O3 om = 1).
    {
    apply count_occ_In with (eq_dec := Z.eq_dec) in INO3.
    destruct (count_occ Z.eq_dec O3 om).
    omega.
    destruct n0.
    omega.
    omega.
    }

    assert (CNTo3O3t3: count_occ node_dec G (o3, O3, t3) = 1).
    {
      apply NoDup_count_occ'.
      apply nodup_map.
      assumption.
      assumption.
    }

    assert (IND: ((o3,(om::remove Z.eq_dec om (O2++O3)),t2)::
                 (remove node_dec (o3,O3,t3) (remove node_dec (om,O2,t2) G))) = nil).
    apply IHn with R P X.
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
    assert (SP: spare_ob_inv ((o3,om :: remove Z.eq_dec om (O2 ++ O3),
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
    assert (OLER: prc om O1 R P X = true).
    {
      apply PRC with t1.
      assumption.
    }

    assert (OLER': prc o2 O2 R P X = true).
    {
      apply PRC with t2.
      assumption.
    }
    assert (G1: Z.le (R om) (R o2)).
    {
    apply MIN.
    apply in_map_iff.
    exists (o2, O2, t2).
    auto.
    }

    assert (Pom: P o2 = true).
    {
    apply prc_P with (R:=R) (o':=om) (O:=O2) (X:=X); try assumption.
    }

    assert (O2Mr': own_ob G o2).
    {
    eapply SPARE in Pom.
    unfold own_ob.
    unfold spare_ob in Pom.
    omega.
    apply T2.
    }

    assert (CNTomO2': count_occ Z.eq_dec O2 om = 1).
    {
    assert (OCCrminR': count_occ Z.eq_dec O2 om <= 1).
    {
      eapply ole_X_count with (o:=o2) (R:=R).
      omega.
      apply OLER'.
    }
    apply count_occ_In with (eq_dec := Z.eq_dec) in INO2.
    destruct (count_occ Z.eq_dec O2 om).
    omega.
    destruct n0.
    omega.
    omega.
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

    assert (IND: (o2,( O1 ++ (remove Z.eq_dec om O2)),t1)::
                 (remove node_dec (o2,O2,t2) (remove node_dec (om,O1,t1) G)) = nil).
    apply IHn with R P X.
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
    assumption.
    destruct (Z.eq_dec o om).
    {
    rewrite e.


    assert (O2Ormin: own_ob G om).
    {
    eapply OWN.
    apply T1.
    apply prc_X with (R:=R) (o':=o2) (O:=O2) (P:=P); try assumption.
    }

    assert (tmp: 1 < count_occ Z.eq_dec (concat (map (fun x => snd (fst x)) G)) om).
    {

    unfold own_ob in O2Ormin.
    assert (tmp: 2 <= count_occ Z_eq_dec (map (fun x => fst (fst x)) G) om).
    destruct IN as [i1|i2].
    inversion i1.
    rewrite H0 in T2.
    rewrite e in T2.
    apply in_in_count2 with (om,O1,t1) (om, O2, t2).
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
      apply ole_X_count with (o:=o2) (R:=R) (X:=X) (P:=P).
      apply MIN.
      apply in_map_iff.
      exists (o2, O2, t2).
      auto.
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
    assert (SP: spare_ob_inv ((o2, O1 ++ remove Z.eq_dec om O2, t1)
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
