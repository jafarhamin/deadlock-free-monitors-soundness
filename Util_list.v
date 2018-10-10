Require Import List.
Require Import ZArith.
Require Import Coq.Init.Nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sorting.Permutation.
Require Import Util_Z.

Set Implicit Arguments.

Fixpoint seqof A (item: A) (len:nat) : list A :=
    match len with
      | O => nil
      | S len => item :: seqof item len
    end.

Ltac inm_ := 
  repeat match goal with 
          | _: In ?x ?l |- In (?f1 ?x, ?f2 ?x) (map (fun x1 => (?f1 x1, ?f2 x1)) ?l) => 
                 apply in_map_iff; exists x; tauto
          | _: In ?x ?l |- In ?x' (map (fun x1 => (?f1 x1, ?f2 x1)) ?l) => 
                 apply in_map_iff; exists x; tauto
          | _: _ |- In (?f ?x) (map ?f ?l) => apply in_map
         end; trivial.

Definition lift_list A (opA_eqb: option A -> option A -> bool) (default: A) (l: list (option A)) : list A :=
  map (lift default) (filter (fun x => negb (opA_eqb x None)) l).

Lemma map_app A B (f: A -> B):
  forall (l1 l2: list A),
    map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  induction l1.
  - reflexivity.
  - intros.
    simpl.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma map_list A B C (f: A -> C) (f1: B -> C) (f2: A -> B):
  forall (l: list A)
         (MAP: forall x, f x = f1 (f2 x)),
    map f l = map f1 (map f2 l).
Proof.
  induction l.
  - reflexivity.
  - simpl; intros; rewrite MAP; rewrite IHl; [reflexivity | assumption].
Qed.

Lemma length_map A B (f: A -> B):
  forall (l: list A),
    length (map f l) = length l.
Proof.
  induction l.
  - reflexivity.
  - simpl; rewrite IHl; reflexivity.
Qed.

Lemma in_in_count A B dec (f: A -> B):
  forall (l: list A) (a1 a2: A)
         (NEQ: a1 <> a2) 
         (EQ: f a1 = f a2)
         (IN1: In a1 l)
         (IN2: In a2 l),
    2 <= count_occ dec (map f l) (f a1).
Proof.
  induction l; simpl; intros.
  - contradiction.
  - destruct IN1 as [IN1|IN1].
    + destruct IN2 as [IN2|IN2].
      * rewrite <- IN1 in NEQ.
        rewrite <- IN2 in NEQ.
        contradiction.
      * rewrite IN1.
        destruct (dec (f a1) (f a1)); try contradiction.
        assert (tmp: 0 <count_occ dec (map f l) (f a1)).
        -- rewrite EQ.
           apply count_occ_In.
           apply in_map_iff.
           eexists.
           tauto.
        -- omega.
   + destruct IN2 as [IN2|IN2].
     rewrite IN2.
     rewrite EQ.
     destruct (dec (f a2) (f a2)); try contradiction.
     assert (tmp: 0 <count_occ dec (map f l) (f a2)).
     * rewrite <- EQ.
       apply count_occ_In.
       apply in_map_iff.
       eexists.
       tauto.
     * omega.
     * destruct (dec (f a) (f a1)).
       apply le_trans with (count_occ dec (map f l) (f a1)).
       apply IHl with a2; try assumption.
       omega.
       apply IHl with a2; try assumption.
Qed.

Lemma remove_remove A dec:
  forall (l: list A) a b,
    remove dec a (remove dec b l) = remove dec b (remove dec a l).
Proof.
  induction l; simpl; intros.
  - reflexivity.
  - destruct (dec b a).
    + destruct (dec a0 a).
      apply IHl.
      simpl.
      rewrite e.
      destruct (dec a a); try contradiction.
      apply IHl.
    + simpl.
      destruct (dec a0 a).
       * apply IHl.
       * simpl.
         destruct (dec b a).
         rewrite e in n.
         contradiction.
         rewrite IHl.
         reflexivity.
Qed.

Lemma length_app A:
  forall (l1 l2: list A),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
  induction l1; simpl; intros.
  - reflexivity.
  - rewrite IHl1; reflexivity.
Qed.

Lemma length_filter_app A f:
  forall (l1 l2: list A),
    length (filter f (l1 ++ l2)) = length (filter f l1) + length (filter f l2).
Proof.
  induction l1; simpl; intros.
  - reflexivity.
  - destruct (f a). simpl. rewrite IHl1; reflexivity.
    apply IHl1.
Qed.

Lemma filter_filter_eq A f1 f2:
  forall (l: list A)
    (EQF: forall x (IN: In x l), f1 x = f2 x),
    filter f1 l = filter f2 l.
Proof.
  induction l.
  simpl.
  intros.
  reflexivity.
  simpl.
  intros.
  destruct (f1 a) eqn:f1a.
  destruct (f2 a) eqn:f2a.
  rewrite IHl.
  reflexivity.
  intros.
  apply EQF.
  right.
  assumption.
  rewrite <- EQF in f2a.
  rewrite f1a in f2a.
  inversion f2a.
  left.
  reflexivity.
  destruct (f2 a) eqn:f2a.
  rewrite EQF in f1a.
  rewrite f1a in f2a.
  inversion f2a.
  left.
  reflexivity.
  apply IHl.
  intros.
  apply EQF.
  right.
  assumption.
Qed.

Lemma filter_filter_le A f1 f2:
  forall (l: list A)
    (EQF: forall x (IN: In x l) (F1: f1 x = true), f2 x = true),
    length (filter f1 l) <= length (filter f2 l).
Proof.
  induction l.
  simpl.
  intros.
  reflexivity.
  simpl.
  intros.
  assert (IH: length (filter f1 l) <= length (filter f2 l)).
  {
  apply IHl.
  intros.
  apply EQF.
  right.
  assumption.
  assumption.
  }
  destruct (f1 a) eqn:f1a.
  rewrite EQF.
  simpl.
  omega.
  left.
  reflexivity.
  assumption.
  destruct (f2 a) eqn:f2a.
  simpl.
  omega.
  assumption.
Qed.

Lemma count_filter A dec f:
  forall (l: list A) a (FIL: f a = true),
    count_occ dec (filter f l) a = count_occ dec l a.
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (dec a a0).
  rewrite e.
  rewrite FIL.
  simpl.
  destruct (dec a0 a0).
  Focus 2.
  contradiction.
  rewrite IHl.
  reflexivity.
  assumption.
  destruct (f a) eqn:fa.
  simpl.
  destruct (dec a a0).
  rewrite e in n.
  contradiction.
  apply IHl.
  assumption.
  apply IHl.
  assumption.
Qed.

Lemma count_remove_zero A dec:
  forall (l: list A) r,
    count_occ dec (remove dec r l) r = 0.
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (dec r a).
  apply IHl.
  simpl.
  destruct (dec a r).
  rewrite e in n.
  contradiction.
  apply IHl.
Qed.

Lemma count_remove_eq A dec:
  forall (l: list A) r r' (NEQ: r <> r'),
    count_occ dec (remove dec r l) r' = count_occ dec l r'.
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (dec r a).
  destruct (dec a r').
  rewrite e in NEQ.
  rewrite <- e0 in NEQ.
  contradiction.
  apply IHl.
  assumption.
  simpl.
  destruct (dec a r').
  rewrite IHl.
  reflexivity.
  assumption.
  apply IHl.
  assumption.
Qed.

Lemma length_filter_remove A dec:
  forall (l: list A) f a,
    le (length (filter f (remove dec a l))) (length (filter f l)).
Proof.
  induction l.
  simpl.
  intros.
  omega.
  simpl.
  intros.
  destruct (dec a0 a).
  destruct (f a).
  simpl.
  apply le_trans with (length (filter f l)).
  apply IHl.
  omega.
  apply IHl.
  simpl.
  destruct (f a).
  simpl.
  assert (tmp: length (filter f (remove dec a0 l)) <= length (filter f l)).
  apply IHl.
  omega.
  apply IHl.
Qed.

Lemma filter_remove A dec:
  forall (l: list A) f a
         (Len: le (length (filter f l)) 1)
         (Fil: f a = true)
         (IN: In a l),
    filter f (remove dec a l) = nil.
Proof.
  induction l.
  simpl.
  intros.
  reflexivity.
  simpl.
  intros.
  destruct IN as [EQ|IN].
  rewrite EQ.
  destruct (dec a0 a0).
  Focus 2.
  contradiction.
  rewrite EQ in Len.
  rewrite Fil in Len.
  simpl in Len.
  destruct (length (filter f l)) eqn:lenfil.
  assert (tmp: le (length (filter f (remove dec a l))) 0).
  rewrite <- lenfil.
  apply length_filter_remove.
  rewrite <- EQ.
  destruct (filter f (remove dec a l)) eqn:fil.
  reflexivity.
  simpl in tmp.
  omega.
  omega.
  destruct (dec a0 a) as [d1|d2].
  rewrite <- d1 in Len.
  rewrite Fil in Len.
  simpl in Len.
  destruct (length (filter f l)) eqn:lenfil.
  assert (tmp: le (length (filter f (remove dec a l))) 0).
  rewrite <- lenfil.
  apply length_filter_remove.
  rewrite d1.
  destruct (filter f (remove dec a l)) eqn:fil.
  reflexivity.
  simpl in tmp.
  omega.
  omega.
  simpl.
  destruct (f a) eqn:fa.
  simpl in Len.
  assert (tmp: In a0 (filter f l)).
  apply filter_In.
  auto.
  destruct (filter f l).
  inversion tmp.
  simpl in Len.
  omega.
  apply IHl.
  assumption.
  assumption.
  assumption.
Qed.

Lemma filter_app A:
  forall (l1 l2: list A) f,
    filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  induction l1.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (f a).
  simpl.
  rewrite <- IHl1.
  reflexivity.
  apply IHl1.
Qed.

Lemma filter_remove_filter A dec:
  forall (l: list A) f a,
    filter f (remove dec a l) = remove dec a (filter f l).
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (dec a0 a).
  destruct (f a) eqn:fa.
  simpl.
  rewrite e.
  destruct (dec a a).
  Focus 2.
  contradiction.
  apply IHl.
  apply IHl.
  simpl.
  destruct (f a) eqn:fa.
  simpl.
  destruct (dec a0 a).
  rewrite e in n.
  contradiction.
  rewrite IHl.
  reflexivity.
  apply IHl.
Qed.

Lemma filter_list A (f: A -> bool):
  forall (l: list A) (FX: forall x (INx: In x l), f x = true),
    filter f l = l.
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (f a) eqn:fa.
  rewrite IHl.
  reflexivity.
  intros.
  apply FX.
  right.
  assumption.
  assert (CO: f a = true).
  apply FX.
  left.
  reflexivity.
  rewrite fa in CO.
  inversion CO.
Qed.

Lemma remove_app A dec:
  forall (l l': list A) a,
    remove dec a (l ++ l') = remove dec a l ++ remove dec a l'.
Proof.
  induction l.
  simpl.
  intros.
  reflexivity.
  simpl.
  intros.
  destruct (dec a0 a).
  apply IHl.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Lemma remove_not_in_eq A dec:
  forall (G: list A) a (NIN: ~ In a G),
    G = remove dec a G.
Proof.
  induction G.
  simpl.
  intros.
  reflexivity.
  simpl.
  intros.
  destruct (dec a0 a).
  exfalso.
  apply NIN.
  left.
  symmetry.
  assumption.
  assert (tmp: G = remove dec a0 G).
  apply IHG.
  unfold not.
  intros.
  apply NIN.
  right.
  assumption.
  rewrite tmp at 1.
  reflexivity.
Qed.

Lemma in_map_remove_in A dec B:
  forall (l: list A) a b (f: A -> B) (IN: In a (map f (remove dec b l))),
    In a (map f l).
Proof.
  induction l.
  simpl.
  intros.
  assumption.
  simpl.
  intros.
  destruct (dec b a).
  right.
  apply IHl with b.
  assumption.
  simpl in IN.
  destruct IN.
  left.
  assumption.
  right.
  apply IHl with b.
  assumption.
Qed.  

Lemma in_remove_in A dec:
  forall (l: list A) a b (IN: In a (remove dec b l)),
    In a l.
Proof.
  induction l.
  simpl.
  intros.
  assumption.
  simpl.
  intros.
  destruct (dec b a).
  right.
  apply IHl with b.
  assumption.
  simpl in IN.
  destruct IN.
  left.
  assumption.
  right.
  apply IHl with b.
  assumption.
Qed.

Lemma in_in_remove A dec:
  forall (G: list A) a b 
         (NEQ: a <> b)
         (IN: In a G),
    In a (remove dec b G).
Proof.
  induction G.
  simpl.
  intros.
  assumption.
  simpl.
  intros.
  destruct IN as [aa|IN].
  destruct (dec b a).
  rewrite e in NEQ.
  rewrite aa in NEQ.
  contradiction.
  rewrite aa.
  left.
  reflexivity.
  destruct (dec b a).
  apply IHG.
  assumption.
  assumption.
  right.
  apply IHG.
  assumption.
  assumption.
Qed.

Lemma count_filter_len A dec: 
  forall (R: list A) r f
         (FIL: f r = true),
    (count_occ dec R r <= length (filter f R))%nat.
Proof.
  induction R.
  simpl.
  intros.
  omega.
  simpl.
  intros.
  destruct (dec a r).
  rewrite e.
  rewrite FIL.
  simpl.
  assert (tmp: count_occ dec R r <= length (filter f R)).
  apply IHR.
  assumption.
  omega.
  destruct (f a) eqn:fa.
  simpl.
  assert (tmp: count_occ dec R r <= length (filter f R)).
  apply IHR.
  assumption.
  omega.
  apply IHR.
  assumption.
Qed.

Lemma count_app A dec:
  forall (l1 l2: list A) r,
    count_occ dec l1 r + count_occ dec l2 r =
    count_occ dec (l1++l2) r.
Proof.
  induction l1.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (dec a r).
  simpl.
  specialize IHl1 with l2 r.
  omega.
  apply IHl1.
Qed.

Lemma count_remove_nin A dec:
  forall (l: list A) a (NIN: ~ In a l),
    l = remove dec a l.
Proof.
  induction l.
  simpl.
  intros.
  reflexivity.
  simpl.
  intros.
  unfold not in NIN.
  destruct (dec a0 a).
  exfalso.
  apply NIN.
  left.
  auto.
  rewrite <- IHl with a0.
  reflexivity.
  unfold not.
  intros.
  apply NIN.
  right.
  assumption.
Qed.

Lemma in_filter_in_l A:
  forall (l: list A) a f (IN: In a (filter f l)),
    In a l.
Proof.
  induction l.
  simpl.
  intros.
  assumption.
  simpl.
  intros.
  destruct (f a).
  simpl in IN.
  destruct IN as [EQ|IN].
  left.
  assumption.
  right.
  apply IHl with f.
  assumption.
  right.
  apply IHl with f.
  assumption.
Qed.

Lemma length_filter_filter A f1 f2:
  forall (l: list A),
    length (filter f1 (filter f2 l)) <= length (filter f1 l).
Proof.
  induction l.
  simpl.
  omega.
  simpl.
  destruct (f2 a) eqn:f2a.
  destruct (f1 a) eqn:f1a.
  simpl.
  rewrite f1a.
  simpl.
  omega.
  simpl.
  rewrite f1a.
  assumption.
  destruct (f1 a) eqn:f1a.
  simpl.
  omega.
  omega.
Qed.

Lemma list_has_min A R:
  forall (l: list A) (HAS_ELEMENT: length l > 0),
    exists min (INl: In min l), forall x (INl: In x l), Z.le (R min) (R x).
Proof.
  induction l.
  simpl.
  intros.
  inversion HAS_ELEMENT.
  simpl.
  intros.
  destruct (length l) eqn:LENL.
  exists a.
  exists.
  left.
  reflexivity.
  intros.
  destruct INl.
  rewrite H.
  omega.
  destruct l.
  inversion H.
  inversion LENL.
  assert (tmp: exists (min : A) (_ : In min l),
        forall x : A, In x l -> (R min <= R x)%Z).
  apply IHl.
  omega.
  destruct tmp as (min,(INmin,MIN)).
  destruct (Z_le_dec (R min) (R a)).
  exists min.
  exists.
  right.
  assumption.
  intros.
  destruct INl.
  rewrite <- H.
  assumption.
  apply MIN.
  assumption.
  exists a.
  exists.
  left.
  reflexivity.
  intros.
  destruct INl.
  rewrite <- H.
  omega.
  apply MIN in H.
  omega.
Qed.

Lemma min_exists:
  forall (l: list (option Z)) a (IN: In (Some a) l) W,
    exists rmin (INrmin: In (Some rmin) l), 
      forall r (IN: In (Some r) l), 
        Z.le (W rmin) (W r).
Proof.
  induction l.
  simpl.
  intros.
  contradiction.
  simpl.
  intros.
  destruct IN as [EQ|IN].
  rewrite EQ.
  destruct (filter (fun x => negb (ifb (opZ_eq_dec x None))) l) eqn:L.
  exists a0.
  exists.
  left.
  reflexivity.
  intros.
  destruct IN as [EQ1|IN].
  inversion EQ1.
  omega.
  assert (tmp: In (Some r) (filter (fun x : option Z => negb (ifb (opZ_eq_dec x None))) l)).
  apply filter_In.
  split.
  assumption.
  destruct (opZ_eq_dec (Some r) None) as [d1|d2].
  inversion d1.
  reflexivity.
  rewrite L in tmp.
  inversion tmp.
  destruct o.
  assert (tmp: exists (rmin : Z) (_ : In (Some rmin) l),
                 forall r : Z, In (Some r) l -> (W rmin <= W r)%Z).
  apply IHl with z.
  apply in_filter_in_l with (fun x : option Z => negb (ifb (opZ_eq_dec x None))).
  rewrite L.
  left.
  reflexivity.
  destruct tmp as (rmin,(INrmin,rminismin)).
  destruct (Z_le_dec (W rmin) (W a0)).
  exists rmin.
  exists.
  right.
  assumption.
  intros.
  destruct IN as [EQ1|IN].
  inversion EQ1.
  rewrite <- H0.
  assumption.
  apply rminismin.
  assumption.
  exists a0.
  exists.
  left.
  reflexivity.
  intros.
  destruct IN as [EQ1|IN].
  inversion EQ1.
  omega.
  assert (tmp: Z.le (W rmin) (W r)).
  apply rminismin.
  assumption.
  omega.
  assert (tmp: In None (filter (fun x : option Z => negb (ifb (opZ_eq_dec x None))) l)).
  rewrite L.
  left.
  reflexivity.
  apply filter_In in tmp.
  destruct tmp as [tmp1 tmp2].
  destruct (opZ_eq_dec None None).
  inversion tmp2.
  contradiction.
  assert (tmp: exists (rmin : Z) (_ : In (Some rmin) l),
                 forall r : Z, In (Some r) l -> (W rmin <= W r)%Z).
  apply IHl with a0.
  assumption.
  destruct tmp as (rmin,(INrmin,rminismin)).
  destruct a.
  destruct (Z_le_dec (W rmin) (W z)).
  exists rmin.
  exists.
  right.
  assumption.
  intros.
  destruct IN0 as [EQ1|IN1].
  inversion EQ1.
  rewrite <- H0.
  assumption.
  apply rminismin.
  assumption.
  exists z.
  exists.
  left.
  reflexivity.
  intros.
  destruct IN0 as [EQ1|IN1].
  inversion EQ1.
  omega.
  assert (tmp: Z.le (W rmin) (W r)).
  apply rminismin.
  assumption.
  omega.
  exists rmin.
  exists.
  right.
  assumption.
  intros.
  destruct IN0 as [EQ1|IN1].
  inversion EQ1.
  apply rminismin.
  assumption.
Qed.

Lemma list_has_max:
  forall (l: list Z) (HAS_ELEMENT: lt 0 (length l)),
    exists max (INl: In max l), forall x (INl: In x l), Z.le x max.
Proof.
  induction l.
  simpl.
  intros.
  inversion HAS_ELEMENT.
  simpl.
  intros.
  destruct (length l) eqn:LENL.
  exists a.
  exists.
  left.
  reflexivity.
  intros.
  destruct INl.
  rewrite H.
  omega.
  destruct l.
  inversion H.
  inversion LENL.
  assert (tmp: exists max (INM : In max l),
        forall x, In x l -> Z.le x max).
  apply IHl.
  omega.
  destruct tmp as (max,(INmax,MAX)).
  destruct (Z_le_dec a max).
  exists max.
  exists.
  right.
  assumption.
  intros.
  destruct INl.
  rewrite <- H.
  assumption.
  apply MAX.
  assumption.
  exists a.
  exists.
  left.
  reflexivity.
  intros.
  destruct INl.
  rewrite <- H.
  omega.
  apply MAX in H.
  omega.
Qed.

Lemma map_filter A B (f1: A -> B) (f2: A -> bool) (f3: B -> bool):
  forall (l: list A) (FIL: forall x (IN: In x l), f2 x = f3 (f1 x)),
    map f1 (filter f2 l) = filter f3 (map f1 l).
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (f2 a) eqn:f2a.
  destruct (f3 (f1 a)) eqn:f3f1a.
  simpl.
  rewrite IHl.
  reflexivity.
  intros.
  apply FIL.
  right.
  assumption.
  rewrite FIL in f2a.
  rewrite f2a in f3f1a.
  inversion f3f1a.
  left.
  reflexivity.
  destruct (f3 (f1 a)) eqn:f3f1a.
  rewrite FIL in f2a.
  rewrite f2a in f3f1a.
  inversion f3f1a.
  left.
  reflexivity.
  apply IHl.
  intros.
  apply FIL.
  right.
  assumption.
Qed.

Lemma count_map_filter A B dec (f1: A -> B) f2 :
  forall (l: list A) (r: B)
         (FIL: forall x (IN: In x l), f2 x = false -> f1 x <> r),
    count_occ dec (map f1 l) r = count_occ dec (map f1 (filter f2 l)) r.
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (dec (f1 a) r).
  destruct (f2 a) eqn:f2a.
  simpl.
  rewrite e.
  destruct (dec r r).
  Focus 2.
  contradiction.
  rewrite IHl.
  reflexivity.
  intros.
  apply FIL.
  right.
  assumption.
  assumption.
  apply FIL in f2a.
  contradiction.
  left.
  reflexivity.
  destruct (f2 a) eqn:f2a.
  simpl.
  destruct (dec (f1 a) r).
  contradiction.
  apply IHl.
  intros.
  apply FIL.
  right.
  assumption.
  assumption.
  apply IHl.
  intros.
  apply FIL.
  right.
  assumption.
  assumption.
Qed.

Lemma filter_filter A f1 f2 f3:
  forall (l: list A)
         (FIL: forall x (INx: In x l), andb (f1 x) (f2 x) = f3 x),
    filter f1 (filter f2 l) = filter f3 l.
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (f2 a) eqn:f2a.
  simpl.
  destruct (f1 a) eqn:f1a.
  simpl.
  destruct (f3 a) eqn:f3a.
  rewrite IHl.
  reflexivity.
  intros.
  apply FIL.
  right.
  assumption.
  rewrite <- FIL in f3a.
  rewrite f1a in f3a.
  rewrite f2a in f3a.
  inversion f3a.
  left.
  reflexivity.
  destruct (f3 a) eqn:f3a.
  rewrite <- FIL in f3a.
  rewrite f1a in f3a.
  rewrite f2a in f3a.
  inversion f3a.
  left.
  reflexivity.
  apply IHl.
  intros.
  apply FIL.
  right.
  assumption.
  destruct (f3 a) eqn:f3a.
  rewrite <- FIL in f3a.
  rewrite f2a in f3a.
  destruct (f1 a);
  inversion f3a.
  left.
  reflexivity.
  apply IHl.
  intros.
  apply FIL.
  right.
  assumption.
Qed.

Lemma nodup_filter A f:
  forall (l: list A) (UNQ: NoDup l),
    NoDup (filter f l).
Proof.
  induction l.
  simpl.
  trivial.
  simpl.
  destruct (f a) eqn:fa.
  intros.
  inversion UNQ.
  eapply NoDup_cons.
  unfold not in *.
  intros.
  apply H1.
  apply in_filter_in_l with f.
  assumption.
  apply IHl.
  assumption.
  intros.
  apply IHl.
  inversion UNQ.
  assumption.
Qed.

Lemma length_filter_count A B C (f1: C -> bool) (f2: A -> C)
(f3: A -> B) dec x:
  forall (l: list A)
   (F1a: forall a (IN: In a l) (F1F2a: f1 (f2 a) = true), f3 a = x)
   (F2a: forall a (IN: In a l) (F1F2a: f1 (f2 a) = false), f3 a <> x),
    length (filter f1 (map f2 l)) =
    count_occ dec (map f3 l) x.
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  destruct (f1 (f2 a)) eqn:f1f2a.
  simpl.
  intros.
  rewrite F1a.
  destruct (dec x x).
  assert (tmp: length (filter f1 (map f2 l)) = count_occ dec (map f3 l) x).
  apply IHl.
  intros.
  apply F1a.
  right.
  assumption.
  assumption.
  intros.
  apply F2a.
  right.
  assumption.
  assumption.
  omega.
  contradiction.
  left.
  reflexivity.
  assumption.
  simpl.
  intros.
  destruct (dec (f3 a) x).
  apply F2a in f1f2a.
  rewrite e in f1f2a.
  contradiction.
  left.
  reflexivity.
  apply IHl.
  intros.
  apply F1a.
  right.
  assumption.
  assumption.
  intros.
  apply F2a.
  right.
  assumption.
  assumption.
Qed.

Lemma filter_map_eq A B (m1 m2: A -> B) f:
  forall (l: list A)
         (F: forall x (IN: In x l), f (m1 x) = f (m2 x)),
    length (filter f (map m1 l)) = length (filter f (map m2 l)).
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (f (m1 a)) eqn:fm1a.
  rewrite F in fm1a.
  rewrite fm1a.
  simpl.
  rewrite IHl.
  reflexivity.
  intros.
  apply F.
  right.
  assumption.
  left.
  reflexivity.
  rewrite F in fm1a.
  rewrite fm1a.
  apply IHl.
  intros.
  apply F.
  right.
  assumption.
  left.
  reflexivity.
Qed.

Lemma length_filter_map_eq A B C (m1: A -> B) (m2: A -> C) f1 f2:
  forall (l: list A)
         (EQF: forall a (IN: In a l), f1 (m1 a) = f2 (m2 a)),
    length (filter f1 (map m1 l)) = length (filter f2 (map m2 l)).
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (f1 (m1 a)) eqn:f1m1a.
  rewrite EQF in f1m1a.
  rewrite f1m1a.
  simpl.
  rewrite IHl.
  reflexivity.
  intros.
  apply EQF.
  right.
  assumption.
  left.
  reflexivity.
  rewrite EQF in f1m1a.
  rewrite f1m1a.
  apply IHl.
  intros.
  apply EQF.
  right.
  assumption.
  left.
  reflexivity.
Qed.

Lemma prem_length_eq A f:
  forall (l l': list A)
         (PERM: Permutation l l'),
    length (filter f l) = length (filter f l').
Proof.
  intros.
  induction PERM.
  reflexivity.
  simpl.
  destruct (f x).
  simpl.
  omega.
  assumption.
  simpl.
  destruct (f y).
  destruct (f x).
  reflexivity.
  reflexivity.
  reflexivity.
  omega.
Qed.

Lemma count_map_perm A B dec (m: A -> B):
  forall (l1 l2: list A)
         (PERM: Permutation l1 l2) x,
    count_occ dec (map m l1) x = count_occ dec (map m l2) x.
Proof.
  intros.
  induction PERM.
  reflexivity.
  simpl.
  rewrite IHPERM.
  reflexivity.
  simpl.
  destruct (dec (m y) x).
  destruct (dec (m x0) x).
  reflexivity.
  reflexivity.
  reflexivity.
  omega.
Qed.


(** # <font size="5"><b> key-value lists </b></font> # *)

Definition keyval A := list (A*Z).

Lemma count_occ_unq A :
  forall (G: keyval A) v1 v2 k
         (IN1: In (v1,k) G)
         (IN2: In (v2,k) G)
         (OCC: (count_occ Z.eq_dec (map snd G) k <= 1)%nat),
    v1 = v2.
Proof.
  induction G.
  simpl.
  intros.
  contradiction.
  simpl.
  intros.
  destruct a.
  simpl in *.
  destruct IN1 as [aa1|IN1].
  destruct IN2 as [aa2|IN2].
  rewrite aa1 in aa2.
  inversion aa2.
  reflexivity.
  inversion aa1.
  rewrite H1 in OCC.
  destruct (Z.eq_dec k k).
  assert (tmp: lt 0 (count_occ Z.eq_dec (map snd G) k)).
  apply count_occ_In.
  apply in_map_iff.
  exists (v2,k).
  split.
  reflexivity.
  assumption.
  omega.
  contradiction.
  destruct IN2 as [aa2|IN2].
  inversion aa2.
  rewrite H1 in OCC.
  destruct (Z.eq_dec k k).
  assert (tmp: lt 0 (count_occ Z.eq_dec (map snd G) k)).
  apply count_occ_In.
  apply in_map_iff.
  exists (v1,k).
  split.
  reflexivity.
  assumption.
  omega.
  contradiction.
  apply IHG with k.
  assumption.
  assumption.
  destruct (Z.eq_dec z k).
  omega.
  assumption.
Qed.

Lemma unique_key_eq A:
  forall (G:keyval A) k v1 v2 
         (IN1: In (v1,k) G)
         (IN2: In (v2,k) G)
         (UNQ: NoDup (map snd G)),
    v1 = v2.
Proof.
  intros.
  assert (tmp: forall x, le (count_occ Z.eq_dec (map snd G) x) 1).
  apply NoDup_count_occ.
  assumption.
  specialize tmp with k.
  apply count_occ_unq with G k.
  assumption.
  assumption.
  assumption.
Qed.

Lemma unq_nin A dec:
  forall (G:keyval A) v k
         (UNQ: NoDup (map snd G))
         (IN: In (v,k) G),
    ~ exists v', In (v',k) (remove dec (v,k) G).
Proof.
  induction G.
  simpl.
  intros.
  contradiction.
  simpl.
  intros.
  destruct IN as [aa|IN].
  unfold not in *.
  intros tmp.
  destruct tmp as (v', IN).
  rewrite aa in IN.
  destruct (dec (v,k) (v,k)).
  assert (tmp: ~ In k (map snd G) /\ NoDup (map snd G)).
  apply NoDup_cons_iff.
  rewrite aa in UNQ.
  assumption.
  destruct tmp as [NIN ND].
  unfold not in NIN.
  apply NIN.
  apply in_map_iff.
  exists (v',k).
  split.
  reflexivity.
  apply in_remove_in with (dec:=dec)(b:=(v,k)).
  assumption.
  contradiction.
  unfold not in *.
  intros tmp.
  destruct tmp as [v' IN1].
  destruct (dec (v,k) a).
  rewrite <- e in UNQ.
  simpl in *.
  	assert (tmp: ~In k (map snd G) /\ NoDup (map snd G)).
  apply NoDup_cons_iff.
  assumption.
  destruct tmp as (tmp1,tmp2).
  unfold not in tmp1.
  exfalso.
  apply tmp1.
  apply in_map_iff.
  exists (v,k).
  split.
  reflexivity.
  assumption.
  destruct IN1 as [aa|IN1].
  rewrite aa in UNQ.
  simpl in *.
	assert (tmp: ~In k (map snd G) /\ NoDup (map snd G)).
  apply NoDup_cons_iff.
  assumption.
  destruct tmp as (tmp1,tmp2).
  unfold not in tmp1.
  apply tmp1.
  apply in_map_iff.
  exists (v,k).
  auto.
  apply IHG with v k.
  destruct a.
	apply proj2 with (~In z (map snd G)).
  apply NoDup_cons_iff.
  assumption.
  assumption.
  exists v'.
  assumption.
Qed.

Lemma unq_map_remove A dec:
  forall (G:keyval A) (f: (A*Z) -> Z) b (NODUP: NoDup (map f G)),
    NoDup (map f (remove dec b G)).
Proof.
  induction G.
  simpl.
  intros.
  assumption.
  simpl.
  intros.
  destruct (dec b a).
  apply IHG.
  apply proj2 with (~ In (f a) (map f G)).
  apply NoDup_cons_iff.
  assumption.
  simpl.
  apply NoDup_cons_iff.
  split.
  unfold not.
  intros.
  apply NoDup_cons_iff in NODUP.
  destruct NODUP as [NIN NODUP].
  unfold not in NIN.
  apply NIN.
  apply in_map_remove_in with (dec:=dec) (b:=b).
  assumption.
  apply IHG.
  apply proj2 with (~ In (f a) (map f G)).
  apply NoDup_cons_iff.
  assumption.
Qed.

Lemma remove_length A dec:
  forall (G: keyval A) (NODUP: NoDup (map snd G)) a
         (IN: In a G),
    S (length (remove dec a G)) = length G.
Proof.
  induction G.
  simpl.
  intros.
  contradiction.
  simpl.
  intros.
  destruct IN as [aa|IN].
  rewrite aa.
  destruct (dec a0 a0).
  Focus 2.
  contradiction.
  rewrite <- remove_not_in_eq with (G:=G) (a:=a0) (dec:=dec).
  reflexivity.
  apply NoDup_cons_iff in NODUP.
  destruct NODUP as [NIN NODUP].
  unfold not in *.
  intros.
  apply NIN.
  apply in_map.
  rewrite aa.
  assumption.
  destruct (dec a0 a).
  rewrite <- e in NODUP.
  assert (tmp: ~ In (snd a0) (map snd G) /\ NoDup (map snd G)).
  apply NoDup_cons_iff.
  assumption.
  destruct tmp as [NIN NOD].
  unfold not in *.
  exfalso.
  apply NIN.
  apply in_map.
  assumption.
  simpl.
  rewrite IHG.
  reflexivity.
  apply proj2 with (~ In (snd a) (map snd G)).
  apply NoDup_cons_iff.
  assumption.
  assumption.
Qed.

Lemma nodup_map A:
  forall (l: keyval A) (NODUP: NoDup (map snd l)),
    NoDup l.
Proof.
  induction l.
  simpl.
  intros. 
  apply NoDup_nil.
  simpl.
  intros.
  apply NoDup_cons.
  apply NoDup_cons_iff in NODUP.
  destruct NODUP as (tmp1,tmp2).
  unfold not in *.
  intros.
  apply tmp1.
  apply in_map.
  assumption.
  apply IHl.
  apply NoDup_cons_iff in NODUP.
  destruct NODUP as (tmp1,tmp2).
  assumption.
Qed.

Lemma map_list_upd A B (f1: (A * Z) -> B) f2:
  forall (T: keyval A) id
         (FX: forall x (INx: In x T) (EQ: snd x = id), f1 x = f1 (f2 x)),
    map (fun x => f1 (if Z.eq_dec (snd x) id then (f2 x) else x)) T = map f1 T.
Proof.
  induction T.
  simpl.
  reflexivity.
  simpl.
  intros.
  rewrite IHT.
  destruct (Z.eq_dec (snd a) id).
  rewrite <- FX.
  reflexivity.
  left.
  reflexivity.
  assumption.
  reflexivity.
  intros.
  apply FX.
  right.
  assumption.
  assumption.
Qed.

(*
Lemma filterb_filterb_eq A B (m: (A * Z) -> B) (f1 f2: Z -> B -> bool):
  forall (l: keyval A) L lk
    (EQF: forall x v (IN: L v = lk)(NEQ: v <> lk) (IN: In x l), (f1 v) (m x) = (f2 v) (m x)),
    filterb L lk (fun v => length (filter (f1 v) (map m l))) = filterb L lk (fun v => length (filter (f2 v) (map m l))).
Proof.
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x lk).
  reflexivity.
  destruct (Z.eq_dec (L x) lk).
  Focus 2.
  reflexivity.

  rewrite filter_filter_eq with (f2:=f2 x).
  reflexivity.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ,IN)).
  specialize EQF with (x:=x1).
  rewrite EQ in EQF.
  apply EQF.
  assumption.
  assumption.
  assumption.
Qed.
*)

Lemma in_perm A:
  forall (l l': list A)
         (PERM: Permutation l' l) l1 l2
         (EQL': l' = l1 ++ l2) x
         (INPERM: In x l),
    In x l1 \/ In x l2.
Proof.
  intros l l' PERM.
  induction PERM.
  intros.
  inversion INPERM.
  simpl.
  intros.
  destruct l1.
  destruct l2.
  inversion EQL'.
  simpl in EQL'.
  inversion EQL'.
  destruct INPERM as [EQ|IN].
  rewrite <- EQ.
  rewrite H0.
  right.
  left.
  reflexivity.
  specialize IHPERM with (l1:=nil).
  simpl in IHPERM.
  right.
  right.
  assert (G: False \/ In x0 l2).
  apply IHPERM.
  assumption.
  assumption.
  destruct G as [CO|G].
  contradiction.
  assumption.
  inversion EQL'.
  destruct INPERM as [EQ|IN].
  rewrite <- EQ.
  rewrite H0.
  left.
  left.
  reflexivity.
  apply IHPERM with (x:=x0) in H1.
  destruct H1 as [I1|I2].
  left.
  right.
  assumption.
  right.
  assumption.
  assumption.
  intros.
  apply in_app_or.
  rewrite <- EQL'.
  destruct INPERM as [EQ|IN].
  rewrite EQ.
  right.
  left.
  reflexivity.
  destruct IN as [EQ|IN].
  rewrite EQ.
  left.
  reflexivity.
  right.
  right.
  assumption.
  simpl.
  intros.
  apply IHPERM1.
  assumption.
  apply Permutation_in with l''.
  apply Permutation_sym.
  assumption.
  assumption.
Qed.

Lemma perm_filter' A f:
  forall (l: keyval A) x z
         (NODUP: NoDup (map snd l))
         (IN: In (x,z) l)
         (Fx: f (x,z) = false)
         (Fx': forall x' z' (IN: In (x',z') l) (NEQ: z' <> z), f (x',z') = true),
    Permutation l ((x,z) :: filter f l).
Proof.
  induction l.
  simpl.
  intros.
  contradiction.
  simpl.
  intros.
  destruct IN as [EQ|IN].
  rewrite EQ.
  rewrite Fx.
  apply perm_skip.
  rewrite filter_list.
  apply Permutation_refl.
  intros.
  destruct x0.
  apply Fx'.
  right.
  assumption.
  unfold not.
  intros.
  rewrite EQ in NODUP.
  simpl in NODUP.
  rewrite H in INx.
  inversion NODUP.
  apply H2.
  apply in_map_iff.
  exists (a0,z).
  auto.
  destruct (f a) eqn:fa.
  apply Permutation_trans with (a :: (x,z) :: filter f l).
  apply perm_skip.
  apply IHl.
  inversion NODUP.
  assumption.
  assumption.
  assumption.
  intros.
  apply Fx'.
  right.
  assumption.
  assumption.
  apply perm_swap.
  destruct a.
  rewrite Fx' in fa.
  inversion fa.
  left.
  reflexivity.
  unfold not.
  intros.
  rewrite H in NODUP.
  simpl in NODUP.
  inversion NODUP.
  apply H2.
  apply in_map_iff.
  exists (x,z).
  auto.
Qed.

Lemma perm_filter A B f:
  forall (l: list (A * B)) x z
         (NODUP: NoDup (map snd l))
         (IN: In (x,z) l)
         (Fx: f (x,z) = false)
         (Fx': forall x' z' (IN: In (x',z') l) (NEQ: z' <> z), f (x',z') = true),
    Permutation l ((x,z) :: filter f l).
Proof.
  induction l.
  simpl.
  intros.
  contradiction.
  simpl.
  intros.
  destruct IN as [EQ|IN].
  rewrite EQ.
  rewrite Fx.
  apply perm_skip.
  rewrite filter_list.
  apply Permutation_refl.
  intros.
  destruct x0.
  apply Fx'.
  right.
  assumption.
  unfold not.
  intros.
  rewrite EQ in NODUP.
  simpl in NODUP.
  rewrite H in INx.
  inversion NODUP.
  apply H2.
  apply in_map_iff.
  exists (a0,z).
  auto.
  destruct (f a) eqn:fa.
  apply Permutation_trans with (a :: (x,z) :: filter f l).
  apply perm_skip.
  apply IHl.
  inversion NODUP.
  assumption.
  assumption.
  assumption.
  intros.
  apply Fx'.
  right.
  assumption.
  assumption.
  apply perm_swap.
  destruct a.
  rewrite Fx' in fa.
  inversion fa.
  left.
  reflexivity.
  unfold not.
  intros.
  rewrite H in NODUP.
  simpl in NODUP.
  inversion NODUP.
  apply H2.
  apply in_map_iff.
  exists (x,z).
  auto.
Qed.

(** # <font size="5"><b> updl-elem </b></font> # *)

Definition updl A (l: list (A*Z)) id a :=
  map (fun x => if (Z.eq_dec (snd x) id) then a else x) l.  

Definition elem A (id:Z) (l: list (A * Z))  :=
  filter (fun x => Z.eqb (snd x) id) l.

Lemma in_elem_in A:
  forall (l: list (A *Z)) x z
         (IN: In (x,z) (elem z l)),
    In (x,z) l.
Proof.
  unfold elem.
  intros.
  apply filter_In in IN.
  tauto.
Qed.

Lemma updl_eq_l A:
  forall (l: list (A * Z)) z x
         (NODUP: NoDup (z::map snd l)),
    updl l z x = l.
  unfold updl.
  intros.
  replace l with (map (fun x => x) l) at 2.
  apply map_ext_in.
  intros.
  destruct (Z.eq_dec (snd a) z).
  exfalso.
  inversion NODUP.
  apply H2.
  apply in_map_iff.
  exists a.
  auto.
  reflexivity.
  apply map_id.
Qed.

Lemma updl_updl A:
  forall (l:list (A * Z)) z x x',
    updl (updl l z (x,z)) z x' = updl l z x'.
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (Z.eq_dec (snd a) z).
  simpl.
  destruct (Z.eq_dec z z).
  intros.
  rewrite IHl.
  reflexivity.
  contradiction.
  destruct (Z.eq_dec (snd a) z).
  contradiction.
  rewrite IHl.
  reflexivity.
Qed.

Lemma updl_redundant A:
  forall (l:list (A * Z)) z x 
         (RED: forall x' (IN: In x' (elem z l)), x' = x),
    updl l z x = l.
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (Z.eq_dec (snd a) z).
  rewrite e in RED.
  destruct ((z =? z)%Z) eqn:zz.
  Focus 2.
  apply neqb_neq in zz.
  contradiction.
  rewrite IHl.
  rewrite RED with a.
  reflexivity.
  left.
  reflexivity.
  intros.
  apply RED.
  right.
  assumption.
  destruct ((snd a =? z)%Z) eqn:az.
  apply Z.eqb_eq in az.
  contradiction.
  rewrite IHl.
  reflexivity.
  intros.
  apply RED.
  assumption.
Qed.

Lemma NoDup_updl A:
  forall (l: list (A * Z)) x id
         (NODUP: NoDup (map snd l)),
    NoDup (map snd (updl l id (x,id))).
Proof.
  induction l.
  simpl.
  intros.
  assumption.
  simpl.
  intros.
  destruct (Z.eq_dec (snd a) id).
  simpl.
  apply NoDup_cons.
  rewrite e in NODUP.
  inversion NODUP.
  unfold not in *.
  intros.
  apply H1.
  unfold updl in H3.
  rewrite map_map in H3.
  apply in_map_iff in H3.
  destruct H3 as (y,(EQy,INy)).
  destruct (Z.eq_dec (snd y) id).
  apply in_map_iff.
  exists y.
  auto.
  contradiction.
  apply IHl.
  inversion NODUP.
  assumption.
  apply NoDup_cons.
  inversion NODUP.
  unfold not.
  intros.
  apply H1.
  unfold updl in H3.
  rewrite map_map in H3.
  apply in_map_iff in H3.
  destruct H3 as (y,(EQy,INy)).
  destruct (Z.eq_dec (snd y) id).
  apply in_map_iff.
  exists y.
  rewrite e.
  auto.
  apply in_map_iff.
  exists y.
  auto.
  apply IHl.
  inversion NODUP.
  assumption.
Qed.

Lemma elem_updl A:
  forall (l: list (A * Z)) x z (INz: exists x', In (x',z) l),
    In (x,z) (elem z (updl l z (x,z))).
Proof.
  induction l.
  simpl.
  intros.
  destruct INz as (F1,F2).
  assumption.
  simpl.
  intros.
  destruct INz as (x',EQIN).
  destruct EQIN as [EQ|IN].
  rewrite EQ.
  simpl.
  destruct (Z.eq_dec z z).
  Focus 2.
  contradiction.
  simpl.
  destruct ((z =? z)%Z) eqn:xz.
  Focus 2.
  apply neqb_neq in xz.
  contradiction.
  left.
  reflexivity.
  destruct (Z.eq_dec (snd a) z).
  simpl.
  destruct ((z =? z)%Z) eqn:xz.
  Focus 2.
  apply neqb_neq in xz.
  contradiction.
  left.
  reflexivity.
  destruct ((snd a =? z)%Z) eqn:az.
  apply Z.eqb_eq in az.
  contradiction.
  apply IHl.
  exists x'.
  assumption.
Qed.

Lemma in_updl_neq A:
  forall (l: list (A * Z)) z z' x x'
         (NEQ: z' <> z)
         (IN: In (x,z) l),
    In (x,z) (updl l z' x').
Proof.
  induction l.
  simpl.
  intros.
  assumption.
  simpl.
  intros.
  destruct (Z.eq_dec (snd a) z').
  destruct IN as [IN|EQ].
  rewrite IN in e.
  simpl in e.
  symmetry in e.
  contradiction.
  right.
  apply IHl.
  assumption.
  assumption.
  destruct IN as [IN|EQ].
  left.
  assumption.
  right.
  apply IHl.
  assumption.
  assumption.
Qed.

Lemma in_updl_eq A:
  forall (l: list (A * Z)) z x
         (INz: exists x', In (x',z) l),
    In x (updl l z x).
Proof.
  induction l.
  simpl.
  intros.
  destruct INz.
  contradiction.
  simpl.
  intros.
  destruct INz as (x',EI).
  destruct EI as [EQ|IN].
  rewrite EQ.
  simpl.
  destruct (Z.eq_dec z z).
  left.
  reflexivity.
  contradiction.
  destruct (Z.eq_dec (snd a) z).
  left.
  reflexivity.
  right.
  apply IHl.
  exists x'.
  assumption.
Qed.

Lemma eq_map A B (m: (A * Z) -> B) (m': (A * Z) -> (A * Z)):
  forall (l: list (A * Z)) id x
         (M': forall x, m x = m (m' x) /\ snd (m' x) = snd x),
    map m (updl (map m' l) id x) = map m (updl l id x).
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (m' a) eqn:m'a.
  destruct a.
  simpl.
  destruct (Z.eq_dec z id).
  destruct (Z.eq_dec z0 id).
  rewrite IHl.
  reflexivity.
  assumption.
  assert (M2:=M').
  specialize M2 with (a,z0).
  destruct M2 as (M2,M3).
  rewrite m'a in M3.
  simpl in *.
  omega.
  destruct (Z.eq_dec z0 id).
  assert (M2:=M').
  specialize M2 with (a,z0).
  destruct M2 as (M2,M3).
  rewrite m'a in M3.
  simpl in *.
  omega.
  assert (M2:=M').
  specialize M2 with (a,z0).
  destruct M2 as (M2,M3).
  rewrite m'a in M2.
  rewrite M2.
  rewrite IHl.
  reflexivity.
  assumption.
Qed.

Lemma filter_updl_eq A B (f: B -> bool) (m: (A * Z) -> B):
  forall (l: list (A * Z)) x z
         (F1: f (m x) = false)
         (F2: forall x' (IN: In x' (elem z l)), f (m x') = false),
    filter f (map m l) = filter f (map m (updl l z x)).
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (f (m a)) eqn:fma.
  destruct (Z.eq_dec (snd a) z).
  rewrite e in F2.
  rewrite F2 in fma.
  inversion fma.
  destruct ((z =? z)%Z) eqn:zz.
  left.
  reflexivity.
  apply neqb_neq in zz.
  contradiction.
  rewrite fma.
  rewrite IHl with x z.
  reflexivity.
  assumption.
  intros.
  apply F2.
  destruct (snd a =? z)%Z eqn:az.
  rewrite Z.eqb_eq in az.
  contradiction.
  assumption.
  destruct (Z.eq_dec (snd a) z).
  rewrite F1.
  apply IHl.
  assumption.
  intros.
  apply F2.
  rewrite e.
  destruct (z =? z)%Z eqn:zz.
  right.
  assumption.
  apply neqb_neq in zz.
  contradiction.
  rewrite fma.
  apply IHl.
  assumption.
  intros.
  apply F2.
  destruct ((snd a =? z)%Z) eqn:az.
  apply Z.eqb_eq in az.
  contradiction.
  assumption.
Qed.

Lemma in_elem A:
  forall (l: list (A * Z)) x x' z
         (NODUP: NoDup (map snd l))
         (IN1: In (x',z) l)
         (IN2: In x (elem z l)),
    x = (x',z).
Proof.
  induction l.
  simpl.
  intros.
  contradiction.
  simpl.
  intros.
  destruct (snd a =? z)%Z eqn:az.
  apply Z.eqb_eq in az.
  destruct IN1 as [EQ1|IN1].
  destruct IN2 as [EQ2|IN2].
  rewrite <- EQ2.
  assumption.
  inversion NODUP.
  exfalso.
  apply H1.
  rewrite az.
  apply in_map_iff.
  exists x.
  unfold elem in IN2.
  apply filter_In in IN2.
  destruct IN2 as [IN2 EQ2].
  apply Z.eqb_eq in EQ2.
  auto.
  destruct IN2 as [IN2|EQ2].
  inversion NODUP.
  exfalso.
  apply H1.
  rewrite az.
  apply in_map_iff.
  exists (x',z).
  auto.
  apply IHl.
  inversion NODUP.
  assumption.
  assumption.
  assumption.
  apply neqb_neq in az.
  destruct IN1 as [EQ1|IN1].
  rewrite EQ1 in az.
  contradiction.
  apply IHl.
  inversion NODUP.
  assumption.
  assumption.
  assumption.
Qed.

Lemma NoDup_elem A:
  forall (l: list (A * Z)) z x
         (NODUP: NoDup (z::map snd l))
         (IN: In x (elem z l)),
    False.
Proof.
  unfold elem.
  intros.
  destruct (filter (fun x : A * Z => (snd x =? z)%Z) l) eqn:fil.
  inversion IN.
  inversion NODUP.
  apply H1.
  apply in_map_iff.
  exists p.
  assert (IN1: In p (filter (fun x : A * Z => (snd x =? z)%Z) l)).
  rewrite fil.
  left.
  reflexivity.
  apply filter_In in IN1.
  destruct IN1 as (IN1,EQ1).
  apply Z.eqb_eq in EQ1.
  auto.
Qed.

Lemma map_updl A B (m: A * Z -> B):
  forall (l: list (A * Z)) x 
          (NODUP: NoDup (map snd l)) 
         (IN: In (m x,snd x) (map (fun x => (m x, snd x)) l)),
    map (fun x => (m x, snd x)) (updl l (snd x) x) = map (fun x => (m x, snd x)) l.
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct x.
  destruct a.
  simpl in *.
  destruct IN as [EQ|IN].
  inversion EQ.
  repeat dstr_.
  rewrite updl_eq_l.
  reflexivity.
  assumption.
  repeat dstr_.
  exfalso.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  eapply NoDup_elem.
  apply NODUP.
  unfold elem.
  apply filter_In.
  split.
  apply IN.
  inversion EQ.
  apply Z.eqb_eq.
  reflexivity.
  simpl.
  erewrite <- IHl with (a0,z).
  reflexivity.
  inversion NODUP.
  assumption.
  assumption.
Qed.

Lemma map_updl2 A B (m: A * Z -> B):
  forall (l: list (A * Z)) x 
         (NODUP: NoDup (map snd l)) 
         (IN: In (m x,snd x) (map (fun x => (m x, snd x)) l)),
    map m (updl l (snd x) x) = map m l.
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct x.
  destruct a.
  simpl in *.
  destruct IN as [EQ|IN].
  inversion EQ.
  repeat dstr_.
  rewrite updl_eq_l.
  reflexivity.
  assumption.
  repeat dstr_.
  exfalso.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  eapply NoDup_elem.
  apply NODUP.
  unfold elem.
  apply filter_In.
  split.
  apply IN.
  inversion EQ.
  apply Z.eqb_eq.
  reflexivity.
  simpl.
  erewrite <- IHl with (a0,z).
  reflexivity.
  inversion NODUP.
  assumption.
  assumption.
Qed.

Lemma in_map_updl A B (m: A * Z -> B):
  forall (l: list (A * Z)) p i i' x'
         (NEQ: i <> i')
         (IN: In (p,i) (map (fun x => (m x, snd x)) l)),
    In (p,i) (map (fun x => (m x, snd x)) (updl l i' x')).
Proof.
  induction l.
  simpl.
  intros.
  assumption.
  simpl.
  intros.
  destruct IN as [EQ|IN].
  inversion EQ.
  rewrite H1.
  destruct (Z.eq_dec i i').
  contradiction.
  left.
  rewrite H1.
  reflexivity.
  destruct (Z.eq_dec (snd a) i').
  right.
  apply IHl.
  assumption.
  assumption.
  right.
  apply IHl.
  assumption.
  assumption.
Qed.

Lemma updl_updl_neq A:
  forall (l: list (A * Z)) z1 x1 z2 x2
         (NEQ: z1 <> z2),
    updl (updl l z1 (x1,z1)) z2 (x2,z2) = updl (updl l z2 (x2,z2)) z1 (x1,z1).
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (Z.eq_dec (snd a) z1).
  simpl.
  destruct (Z.eq_dec z1 z2).
  contradiction.
  destruct (Z.eq_dec (snd a) z2).
  rewrite e in e0.
  contradiction.
  rewrite e.
  destruct (Z.eq_dec z1 z1).
  Focus 2.
  contradiction.
  rewrite IHl.
  reflexivity.
  assumption.
  destruct (Z.eq_dec (snd a) z2).
  simpl. 
  destruct (Z.eq_dec z2 z1). 
  omega.
  rewrite IHl.
  reflexivity.
  assumption.
  destruct (Z.eq_dec (snd a) z1).
  contradiction.
  rewrite IHl.
  reflexivity.
  assumption.
Qed.

Lemma filter_updl_inc A B (f: B -> bool) (m: (A * Z) -> B):
  forall (l: keyval A) x z
         (NODUP: NoDup (map snd l))
         (F1: f (m x) = false)
         (F2: exists x' (IN: In x' (elem z l)), f (m x') = true),
    length (filter f (map m l)) - 1 = length (filter f (map m (updl l z x))).
Proof.
  induction l.
  simpl.
  intros.
  reflexivity.
  simpl.
  intros.
  destruct F2 as (x',(IN',EQ')).
  destruct (snd a =? z)%Z eqn:az.
  apply Z.eqb_eq in az.
  rewrite az.
  destruct (Z.eq_dec z z).
  Focus 2.
  contradiction.
  destruct IN' as [EQ''|IN'].
  rewrite EQ''.
  rewrite EQ'.
  rewrite F1.
  simpl.
  rewrite <- filter_updl_eq.
  omega.
  assumption.
  intros.
  exfalso.
  eapply NoDup_elem.
  rewrite az in NODUP.
  apply NODUP.
  apply IN.
  exfalso.
  eapply NoDup_elem.
  rewrite az in NODUP.
  apply NODUP.
  apply IN'.
  apply neqb_neq in az.
  destruct (Z.eq_dec (snd a) z).
  contradiction.
  destruct (f (m a)) eqn:fma.
  simpl.
  rewrite <- IHl.
  assert (tmp: length (filter f (map m l)) > 0).
  destruct (filter f (map m l)) eqn:fil.
  assert (tmp: In (m x') (filter f (map m l))).
  apply filter_In.
  split.
  apply in_map.
  unfold elem in IN'.
  apply filter_In in IN'.
  tauto.
  assumption.
  rewrite fil in tmp.
  inversion tmp.
  simpl.
  omega.
  omega.
  inversion NODUP.
  assumption.
  assumption.
  exists x', IN'.
  assumption.
  apply IHl.
  inversion NODUP.
  assumption.
  assumption.
  exists x', IN'.
  assumption.
Qed.

Lemma eq_in_updl_eq A:
  forall (l: list (A * Z)) z x x'
         (IN: In (x,z) (updl l z (x',z))),
    x = x'.
Proof.
  induction l.
  simpl.
  intros.
  contradiction.
  simpl.
  intros.
  destruct (Z.eq_dec (snd a) z).
  destruct IN as [EQ|IN].
  inversion EQ.
  reflexivity.
  apply IHl with z.
  assumption.
  destruct IN as [EQ|IN].
  rewrite EQ in n.
  contradiction.
  apply IHl with z.
  assumption.
Qed.

Lemma in_in_updl_neq A:
  forall (l: list (A * Z)) z z' x x'
         (NEQ: z <> z')
         (IN: In (x,z) (updl l z' (x',z'))),
    In (x,z) l.
Proof.
  induction l.
  simpl.
  intros.
  assumption.
  simpl.
  intros.
  destruct (Z.eq_dec (snd a) z').
  destruct IN as [EQ|IN].
  inversion EQ.
  omega.
  right.
  apply IHl with z' x'.
  assumption.
  assumption.
  destruct IN as [EQ|IN].
  left.
  assumption.
  right.
  apply IHl with z' x'.
  assumption.
  assumption.
Qed.

(*
Lemma filterb_updl_eq222 A B (m: (A * Z) -> B) (f: Z -> B -> bool):
  forall (l: list (A * Z)) L lk x z
         (F: forall v (IN: L v = lk) (NEQ: v <> lk), (f v) (m x) = false /\ (forall x' (IN: In x' (elem z l)), (f v) (m x') = false)),
    filterb L lk (fun v => length (filter (f v) (map m l))) = filterb L lk (fun v => length (filter (f v) (map m (updl l z x)))).
Proof.
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x0 lk).
  reflexivity.
  destruct (Z.eq_dec (L x0) lk).
  Focus 2.
  reflexivity.
  destruct F with (v:=x0) as [F1 F2].
  assumption.
  assumption.
  rewrite <- filter_updl_eq.
  reflexivity.
  apply F1.
  intros.
  apply F2.
  assumption.
Qed.
*)

Lemma filter_updl_dec A B (f: B -> bool) (m: (A * Z) -> B):
  forall (l: list (A * Z)) x z
         (NODUP: NoDup (map snd l))
         (F1: f (m x) = true)
         (F2: exists x' (IN: In x' (elem z l)), f (m x') = false),
    S (length (filter f (map m l))) = length (filter f (map m (updl l z x))).
Proof.
  induction l.
  simpl.
  intros.
  destruct F2 as (x',(CO,rest)).
  contradiction.
  simpl.
  intros.
  destruct F2 as (x',(IN',EQ')).
  destruct (Z.eq_dec (snd a) z).
  rewrite e in IN'.
  destruct ((z =? z)%Z) eqn:zz.
  destruct IN' as [EQ|IN].
  rewrite EQ.
  rewrite EQ'.
  rewrite F1.
  simpl.
  rewrite updl_eq_l.
  reflexivity.
  rewrite <- e.
  assumption.
  destruct (f (m a)) eqn:fma.
  rewrite F1.
  simpl.
  rewrite IHl with x z.
  reflexivity.
  inversion NODUP.
  assumption.
  assumption.
  exists x', IN.
  assumption.
  rewrite F1.
  simpl.
  rewrite updl_eq_l.
  reflexivity.
  rewrite <- e.
  assumption.
  apply neqb_neq in zz.
  contradiction.
  destruct (snd a =? z)%Z eqn:az.
  rewrite Z.eqb_eq in az.
  contradiction.
  simpl.
  destruct (f (m a)) eqn:fma.
  simpl.
  rewrite IHl with x z.
  reflexivity.
  inversion NODUP.
  assumption.
  assumption.
  exists x', IN'.
  assumption.
  apply IHl.
  inversion NODUP.
  assumption.
  assumption.
  exists x', IN'.
  assumption.
Qed.

Lemma count_updl_eq A (m: (A * Z) -> list Z):
  forall (l: list (A * Z)) x z z'
         (F: forall x' (IN: In x' (elem z l)), count_occ Z.eq_dec (m x') z' = count_occ Z.eq_dec (m x) z'),
    count_occ Z.eq_dec (concat (map m l)) z' = count_occ Z.eq_dec (concat (map m (updl l z x))) z'.
Proof.
  induction l.
  simpl.
  intros.
  reflexivity.
  simpl.
  intros.
  destruct (snd a =? z)%Z eqn:az.
  apply Z.eqb_eq in az.
  rewrite az.
  repeat dstr_.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite F.
  rewrite IHl with (x:=x)(z:=z).
  reflexivity.
  intros.
  apply F.
  destruct (z =? z)%Z eqn:zz.
  right.
  assumption.
  apply neqb_neq in zz.
  contradiction.
  destruct (z =? z)%Z eqn:zz.
  left.
  reflexivity.
  apply neqb_neq in zz.
  contradiction.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite IHl with (x:=x)(z:=z).
  apply neqb_neq in az.
  destruct (Z.eq_dec (snd a) z).
  contradiction.
  reflexivity.
  intros.
  apply F.
  assumption.
Qed.

Lemma filterb_updl_obs_eq A (m: (A*Z) -> list Z):
  forall (l: list (A * Z)) (lk: Z) x z L
         (F: forall v (IN: L v = Some lk) (NEQ: v <> lk) x' (IN: In x' (elem z l)), 
               count_occ Z.eq_dec (m x') v = count_occ Z.eq_dec (m x) v),
     filterb L lk (count_occ Z.eq_dec (concat (map m l))) = filterb L lk (count_occ Z.eq_dec (concat (map m (updl l z x)))).
Proof.
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.
  destruct (L x0) eqn:Lx0.
  destruct (Z.eq_dec x0 lk).
  reflexivity.
  destruct (Z.eq_dec z0 lk) eqn:EQ.
  apply count_updl_eq.
  intros.
  apply F;
  try tauto.
  rewrite <- e.
  assumption.
  reflexivity.
  reflexivity.
Qed.

Lemma filterb_updl_eq A B (m: (A * Z) -> B) (f: Z -> B -> bool):
  forall (l: list (A * Z)) (lk: Z) x z L
         (F: forall v (IN: L v = Some lk) (NEQ: v <> lk), (f v) (m x) = false /\ (forall x' (IN: In x' (elem z l)), (f v) (m x') = false)),
    filterb L lk (fun v => length (filter (f v) (map m l))) = filterb L lk (fun v => length (filter (f v) (map m (updl l z x)))).
Proof.
  unfold filterb.
  intros.
  apply functional_extensionality.
  intros.
  destruct (L x0) eqn:Lx0.
  destruct (Z.eq_dec x0 lk).
  reflexivity.
  destruct (Z.eq_dec z0 lk) eqn:EQ.
  destruct F with (v:=x0) as [F1 F2].
  rewrite <- e.
  assumption.
  assumption.
  rewrite <- filter_updl_eq;
  try tauto.
  reflexivity.
  reflexivity.
Qed.


Lemma filterbv_updl_eq A B (m: (A * Z) -> B) (f: Z -> B -> bool):
  forall (l: list (A * Z)) L lk x z v
         (F: (f v) (m x) = false /\ (forall x' (IN: In x' (elem z l)), (f v) (m x') = false)),
    filterb L lk (fun v => length (filter (f v) (map m l))) v = filterb L lk (fun v => length (filter (f v) (map m (updl l z x)))) v.
Proof.
  unfold filterb.
  intros.
  destruct (L v) eqn:LV.
  destruct (Z.eq_dec v lk).
  reflexivity.
  destruct (Z.eq_dec z0 lk).
  Focus 2.
  reflexivity.
  destruct F as [F1 F2].
  rewrite <- filter_updl_eq.
  reflexivity.
  apply F1.
  intros.
  apply F2.
  assumption.
  reflexivity.
Qed.

Lemma count_updl_decr A m:
  forall (l: keyval A) O x z id
         (NODUP: NoDup (map snd l))
         (IN: In (z::O,id) (map (fun x => (m x, snd x)) l))
         (X: m (x,id) = O),
    count_occ Z.eq_dec (concat (map m l)) z - 1 =
    count_occ Z.eq_dec (concat (map m (updl l id (x,id)))) z.
Proof.
  induction l.
  simpl.
  intros.
  reflexivity.
  simpl.
  intros.
  destruct IN as [EQ|IN].
  inversion EQ.
  repeat dstr_.
  rewrite updl_eq_l.
  omega.
  assumption.
  repeat dstr_.
  inversion NODUP.
  exfalso.
  apply H1.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ,IN)).
  inversion EQ.
  apply in_map_iff.
  exists x1.
  auto.
  rewrite <- count_app.
  rewrite <- count_app.
  erewrite <- IHl.
  assert (tmp: count_occ Z.eq_dec (concat (map m l)) z > 0).
  {
  apply count_occ_In.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ,IN)).
  inversion EQ.
  exists x1.
  rewrite H0.
  split.
  assumption.
  left.
  reflexivity.
  }
  omega.
  inversion NODUP.
  assumption.
  apply IN.
  assumption.
Qed.

Lemma count_perm1 A dec:
  forall (l1 l2: list A)
         (PERM: Permutation l1 l2) x,
    count_occ dec l1 x = count_occ dec l2 x.
Proof.
  intros.
  induction PERM.
  reflexivity.
  simpl.
  rewrite IHPERM.
  reflexivity.
  simpl.
  destruct (dec y x).
  destruct (dec x0 x).
  reflexivity.
  reflexivity.
  reflexivity.
  omega.
Qed.

Lemma count_perm A dec:
  forall (l l': list A)
         (PERM: Permutation l' l) l1 l2 x
         (EQ: l' = l1 ++ l2),
    count_occ dec l1 x + count_occ dec l2 x = count_occ dec l x.
Proof.
  intros l l' PERM.
  induction PERM.
  simpl.
  intros.
  {
  destruct l1.
  destruct l2.
  simpl.
  omega.
  inversion EQ.
  inversion EQ.
  }
  {
  simpl.
  intros.
  destruct (dec x x0).
  {
  destruct l1.
  destruct l2.
  inversion EQ.
  simpl in EQ.
  inversion EQ.
  rewrite <- H0.
  rewrite e.
  simpl.
  destruct (dec x0 x0).
  Focus 2.
  contradiction.
  specialize IHPERM with (l1:=nil).
  simpl in IHPERM.
  rewrite IHPERM.
  reflexivity.
  assumption.
  inversion EQ.
  rewrite <- e.
  rewrite H0.
  simpl.
  destruct (dec a a).
  Focus 2.
  contradiction.
  simpl.
  rewrite IHPERM.
  reflexivity.
  assumption.
  }
  destruct l1.
  destruct l2.
  inversion EQ.
  simpl in EQ.
  inversion EQ.
  rewrite <- H0.
  simpl.
  destruct (dec x x0).
  contradiction.
  specialize IHPERM with (l1:=nil).
  simpl in IHPERM.
  rewrite IHPERM.
  reflexivity.
  assumption.
  inversion EQ.
  rewrite <- H0.
  simpl.
  destruct (dec x x0).
  contradiction.
  rewrite IHPERM.
  reflexivity.
  assumption.
  }
  simpl.
  intros.
  rewrite count_app.
  rewrite <- EQ.
  simpl.
  destruct (dec y x0).
  destruct (dec x x0).
  reflexivity.
  reflexivity.
  reflexivity.
  simpl.
  intros.
  apply IHPERM1 with (x:=x) in EQ.
  rewrite EQ.
  apply count_perm1.
  assumption.
Qed.

Lemma count_updl_decr' A m:
  forall (l: keyval A) O O' x z id
         (NODUP: NoDup (map snd l))
         (PERM: Permutation O' (z::O))
         (IN: In (O',id) (map (fun x => (m x, snd x)) l))
         (X: m (x,id) = O),
    count_occ Z.eq_dec (concat (map m l)) z - 1 =
    count_occ Z.eq_dec (concat (map m (updl l id (x,id)))) z.
Proof.
  induction l.
  simpl.
  intros.
  reflexivity.
  simpl.
  intros.
  destruct IN as [EQ|IN].
  inversion EQ.
  rewrite eqz.
  rewrite H1.
  rewrite X.
  rewrite H0.
  rewrite updl_eq_l.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite count_perm1 with (l2:=z::O).
  simpl.
  rewrite eqz.
  omega.
  assumption.
  repeat dstr_.
  inversion NODUP.
  rewrite <- count_app.
  rewrite <- count_app.
  erewrite <- IHl.
  assert (tmp: count_occ Z.eq_dec (concat (map m l)) z > 0).
  {
  apply count_occ_In.
  rewrite <- flat_map_concat_map.
  apply in_flat_map.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ,IN)).
  inversion EQ.
  exists x1.
  split.
  assumption.
  rewrite H4.
  apply Permutation_in with (z :: O).
  apply Permutation_sym.
  assumption.
  left.
  reflexivity.
  }
  destruct (Z.eq_dec (snd a) id).
  {
  inversion NODUP.
  exfalso.
  apply H5.
  apply in_map_iff in IN.
  destruct IN as (x2,(EQx,INx)).
  apply in_map_iff.
  exists x2.
  inversion EQx.
  rewrite e.
  auto.
  }
  omega.
  inversion NODUP.
  assumption.
  apply PERM.
  apply IN.
  assumption.
Qed.

Lemma count_updl_incr' A m:
  forall (l: keyval A) O x z id
         (NODUP: NoDup (map snd l))
         (IN: In (O,id) (map (fun x => (m x, snd x)) l))
         (X: m (x,id) = z::O),
    count_occ Z.eq_dec (concat (map m l)) z + 1 =
    count_occ Z.eq_dec (concat (map m (updl l id (x,id)))) z.
Proof.
  induction l.
  simpl.
  intros.
  contradiction.
  simpl.
  intros.
  destruct IN as [EQ|IN].
  inversion EQ.
  rewrite eqz.
  rewrite H1.
  rewrite X.
  rewrite H0.
  simpl.
  rewrite eqz.
  rewrite updl_eq_l.
  omega.
  rewrite <- H1.
  assumption.
  rewrite <- count_app.
  rewrite <- count_app.
  destruct (Z.eq_dec (snd a) id).
  {
  inversion NODUP.
  exfalso.
  apply H1.
  apply in_map_iff in IN.
  destruct IN as (x2,(EQx,INx)).
  apply in_map_iff.
  exists x2.
  inversion EQx.
  rewrite e.
  auto.
  }
  rewrite <- plus_assoc.
  erewrite IHl.
  reflexivity.
  inversion NODUP.
  assumption.
  apply IN.
  assumption.
Qed.

(** # <font size="5"><b> fold_left </b></font> # *)

Lemma fold_left_eq A (f1: A -> A -> A) f2:
  forall (l: list A) b
         (FIL: forall x, f2 x = false -> neutral f1 x),
    fold_left f1 l b = fold_left f1 (filter f2 l) b.
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (f2 a) eqn:f2a.
  simpl.
  apply IHl.
  assumption.
  apply FIL in f2a.
  unfold neutral in f2a.
  assert (tmp:=f2a).
  specialize tmp with b.
  destruct tmp as [f1ba f1ab].
  rewrite f1ba.
  apply IHl.
  assumption.
Qed.

Lemma fold_left_map_eq A B (f1: B -> B -> B) (f2: A -> B) f3:
  forall (l: list A) b
         (FIL: forall x (IN: In x l), f3 x = false -> neutral f1 (f2 x)),
    fold_left f1 (map f2 l) b = fold_left f1 (map f2 (filter f3 l)) b.
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (f3 a) eqn:f2a.
  simpl.
  apply IHl.
  intros.
  apply FIL.
  right.
  assumption.
  assumption.
  apply FIL in f2a.
  unfold neutral in f2a.
  assert (tmp:=f2a).
  specialize tmp with b.
  destruct tmp as [f1ba f1ab].
  rewrite IHl.
  rewrite f1ba.
  reflexivity.
  intros.
  apply FIL.
  right.
  assumption.
  assumption.
  left.
  reflexivity.
Qed.

Definition defl A (def: A -> A -> Prop) (P: list (A * Z)) :=
  forall p1 p2 id1 id2 (NEQ: id1 <> id2)
         (IN1: In (p1,id1) P)
         (IN2: In (p2,id2) P),
    def p1 p2. 

(*
Lemma fold_left_f A f def (CAN: can def f):
  forall (l: list A) a b 
         (DEFab: def a b)
         (DEFLab: forall x (IN: In x l), def x a /\ def x b),
    fold_left f l (f a b) = f a (fold_left f l b).
Proof.
  induction l.
  simpl.
  intros.
  reflexivity.
  simpl.
  intros.
  assert (CAN1:=CAN).
  unfold can in CAN1.
  destruct CAN1 as (COMM,(ASSOC,(DASSOC,(DDIST,(DCOMM,NUT))))).
  replace (f (f a0 b) a) with (f a0 (f b a)).
  apply IHl.
  assert (G: def a a0 /\ def a b).
  {
  apply DEFLab.
  left.
  reflexivity.
  }
  apply DASSOC;
  try tauto.
  apply DCOMM.
  tauto.
  apply DCOMM.
  tauto.
  intros.
  split.
  apply DEFLab.
  right.
  assumption.
  apply DASSOC.
  apply DEFLab.
  right.
  assumption.
  apply DEFLab.
  assumpt
  rewrite ASSOC.
  reflexivity.
  apply DEF.
  apply DEF.
  apply DEF.
Qed.
*)

Lemma fold_left_f_def A f def (CAN: can def f):
  forall (l: list (A * Z)) a b
         (NODUP: NoDup (map snd l))
         (DEFL: defl def l)
         (DEFab: def a b)
         (DEFLab: forall x (IN: In x (map fst l)), def x a /\ def x b),
    fold_left f (map fst l) (f a b) = f a (fold_left f (map fst l) b).
Proof.
  induction l.
  simpl.
  intros.
  reflexivity.
  simpl.
  intros.
  assert (CAN1:=CAN).
  unfold can in CAN1.
  destruct CAN1 as (COMM,(ASSOC,(DASSOC,(DASSOCF,(DCOMM,(DREF,NUT)))))).
  replace (f (f a0 b) (fst a)) with (f a0 (f b (fst a))).
  apply IHl.
  inversion NODUP.
  assumption.
  unfold defl in *.
  intros.
  apply DEFL with id1 id2.
  assumption.
  right.
  assumption.
  right.
  assumption.
  apply DASSOC.
  assumption.
  apply DCOMM.
  apply DEFLab.
  left.
  reflexivity.
  apply DCOMM.
  apply DEFLab.
  left.
  reflexivity.
  intros.
  split.
  apply DEFLab.
  right.
  assumption.
  apply DASSOC.
  apply DEFLab.
  right.
  assumption.
  apply in_map_iff in IN.
  destruct IN as (x0,(EQ,IN)).
  destruct x0 as (x1,x2).
  destruct a as (a1,a2).
  rewrite <- EQ.
  unfold defl in DEFL.
  apply DEFL with x2 a2.
  unfold not.
  intros.
  inversion NODUP.
  apply H2.
  rewrite <- H.
  apply in_map_iff.
  exists (x1,x2).
  auto.
  right.
  assumption.
  left.
  reflexivity.
  apply DCOMM.
  apply DEFLab.
  left.
  reflexivity.
  symmetry.
  apply ASSOC.
  assumption.
  apply DCOMM.
  apply DEFLab.
  left.
  reflexivity.
  apply DCOMM.
  apply DEFLab.
  left.
  reflexivity.
Qed.

Lemma fold_left_f_m_def A B (m: (A * Z) -> B) (f: B -> B -> B) def (CAN: can def f):
  forall (l: list (A * Z)) a b
         (NODUP: NoDup (map snd l))
         (DEFL: defl def (map (fun x => (m x, snd x)) l))
         (DEFab: def a b)
         (DEFLab: forall x (IN: In x (map m l)), def x a /\ def x b),
    fold_left f (map m l) (f a b) = f a (fold_left f (map m l) b).
Proof.
  induction l.
  simpl.
  intros.
  reflexivity.
  simpl.
  intros.
  assert (CAN1:=CAN).
  unfold can in CAN1.
  destruct CAN1 as (COMM,(ASSOC,(DASSOC,(DASSOCF,(DCOMM,(DREF,NUT)))))).
  replace (f (f a0 b) (m a)) with (f a0 (f b (m a))).
  apply IHl.
  inversion NODUP.
  assumption.
  unfold defl in *.
  intros.
  apply DEFL with id1 id2.
  assumption.
  right.
  assumption.
  right.
  assumption.
  apply DASSOC.
  assumption.
  apply DCOMM.
  apply DEFLab.
  left.
  reflexivity.
  apply DCOMM.
  apply DEFLab.
  left.
  reflexivity.
  intros.
  split.
  apply DEFLab.
  right.
  assumption.
  apply DASSOC.
  apply DEFLab.
  right.
  assumption.
  apply in_map_iff in IN.
  destruct IN as (x0,(EQ,IN)).
  destruct x0 as (x1,x2).
  destruct a as (a1,a2).
  rewrite <- EQ.
  unfold defl in DEFL.
  apply DEFL with x2 a2.
  unfold not.
  intros.
  inversion NODUP.
  apply H2.
  rewrite <- H.
  apply in_map_iff.
  exists (x1,x2).
  auto.
  right.
  simpl.
  apply in_map_iff.
  exists (x1, x2).
  auto.
  left.
  reflexivity.
  apply DCOMM.
  apply DEFLab.
  left.
  reflexivity.
  symmetry.
  apply ASSOC.
  assumption.
  apply DCOMM.
  apply DEFLab.
  left.
  reflexivity.
  apply DCOMM.
  apply DEFLab.
  left.
  reflexivity.
Qed.

Lemma fold_left_move_eq A def (f: A -> A -> A) (CAN: can def f) x1 x2 id:
  forall (l: list (A * Z)) 
         (NODUP: NoDup (map snd l)) b
         (DEFL: defl def l)
         (DEFx1x2: def x1 x2)
         (DEFLb: forall x (IN: In x (map fst l)), def x b)
         (ELM: In (f x1 x2,id) l),
    fold_left f (map fst l) b = f x2 (fold_left f (map fst (updl l id (x1,id))) b).
Proof.
  induction l.
  simpl.
  intros.
  contradiction.
  assert (CAN1:=CAN).
  unfold can in CAN1.
  destruct CAN1 as (COMM,(ASSOC,(DASSOC,(DASSOCF,(DCOMM,(DREF,NUT)))))).
  simpl.
  intros.
  assert (DEFx1x2b: def (f x1 x2) b).
  {
  apply DEFLb.
  destruct ELM as [EQ|IN].
  rewrite EQ.
  left.
  reflexivity.
  right.
  apply in_map_iff.
  exists (f x1 x2, id).
  auto.
  }
  assert (tmp: def x1 b /\ def x2 b).
  {
  apply DASSOCF.
  assumption.
  assumption.
  }
  destruct tmp as (defx1,defx2).
  destruct ELM as [EQ|IN].
  destruct (Z.eq_dec (snd a) id).
  rewrite EQ.
  simpl.
  rewrite updl_eq_l.
  replace (f b (f x1 x2)) with (f x2 (f b x1)).
  {
  apply fold_left_f_def with (def:=def).
  assumption.
  inversion NODUP.
  assumption.
  unfold defl in *.
  intros.
  apply DEFL with id1 id2.
  assumption.
  right.
  assumption.
  right.
  assumption.
  apply DASSOC.
  assumption.
  apply DCOMM.
  assumption.
  apply DCOMM.
  assumption.
  intros.
  apply in_map_iff in IN.
  destruct IN as (x0,(EQ0,IN)).
  destruct x0 as (x0',x1').
  simpl in EQ0.
  rewrite <- EQ0.
  rewrite EQ in DEFL.
  split.
  apply DCOMM.
  apply DASSOCF with x1.
  apply DEFL with id x1'.
  unfold not.
  intros.
  rewrite e in NODUP.
  inversion NODUP.
  apply H2.
  rewrite H.
  apply in_map_iff.
  exists (x0', x1').
  auto.
  left.
  reflexivity.
  right.
  assumption.
  assumption.
  apply DASSOC.
  apply DEFLb.
  right.
  apply in_map_iff.
  exists (x0', x1').
  auto.
  apply DCOMM.
  apply DASSOCF with x2.
  rewrite COMM.
  apply DEFL with id x1'.
  unfold not.
  intros.
  rewrite e in NODUP.
  inversion NODUP.
  apply H2.
  rewrite H.
  apply in_map_iff.
  exists (x0', x1').
  auto.
  left.
  reflexivity.
  right.
  assumption.
  apply DCOMM.
  assumption.
  apply DCOMM.
  assumption.
  apply DCOMM.
  assumption.
  }
  symmetry.
  replace (f b x1) with (f x1 b).
  replace (f x2 (f x1 b)) with (f (f x2 x1) b).
  rewrite COMM.
  replace (f x2 x1) with (f x1 x2).
  reflexivity.
  apply COMM.
  assumption.
  apply DCOMM.
  assumption.
  apply ASSOC.
  apply DCOMM.
  assumption.
  assumption.
  assumption.
  apply COMM.
  assumption.
  rewrite <- e.
  assumption.

  simpl.
  rewrite EQ in n.
  contradiction.
  {
  simpl.
  destruct (Z.eq_dec (snd a) id ).
  rewrite e in NODUP.
  inversion NODUP.
  exfalso.
  apply H1.
  apply in_map_iff.
  exists (f x1 x2, id).
  auto.
  apply IHl.
  inversion NODUP.
  assumption.
  unfold defl in *.
  intros.
  apply DEFL with id1 id2.
  assumption.
  right.
  assumption.
  right.
  assumption.
  assumption.
  intros.
  apply DASSOC.
  apply DEFLb.
  right.
  assumption.
  destruct a as (a0,a1).
  apply in_map_iff in IN0.
  destruct IN0 as (c,(EQc,INc)).
  destruct c as (c0,c1).
  simpl in EQc.
  simpl.
  rewrite <- EQc.
  apply DEFL with c1 a1.
  unfold not.
  intros.
  inversion NODUP.
  apply H2.
  rewrite <- H.
  apply in_map_iff.
  exists (c0, c1).
  auto.
  right.
  assumption.
  left.
  reflexivity.
  apply DCOMM.
  apply DEFLb.
  left.
  reflexivity.
  assumption.
  }
Qed.

Lemma fold_left_move_m_eq A B def (f: B -> B -> B) (m: (A * Z) -> B) (CAN: can def f) x1 x2 id:
  forall (l: list (A * Z)) b x
         (NODUP: NoDup (map snd l))
         (DEFL: defl def (map (fun x => (m x, snd x)) l))
         (DEFx1x2: def x1 x2)
         (DEFLb: forall x (IN: In x (map m l)), def x b)
         (ELM: In (f x1 x2,id) (map (fun x => (m x, snd x)) l))
         (X: m (x,id) = x1),
    fold_left f (map m l) b = f x2 (fold_left f (map m (updl l id (x,id))) b).
Proof.
  induction l.
  simpl.
  intros.
  contradiction.
  assert (CAN1:=CAN).
  unfold can in CAN1.
  destruct CAN1 as (COMM,(ASSOC,(DASSOC,(DASSOCF,(DCOMM,(DREF,NUT)))))).
  simpl.
  intros.
  assert (DEFx1x2b: def (f x1 x2) b).
  {
  apply DEFLb.
  destruct ELM as [EQ|IN].
  inversion EQ.
  left.
  reflexivity.
  right.
  apply in_map_iff.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  inversion EQy.
  exists y.
  auto.
  }
  assert (tmp: def x1 b /\ def x2 b).
  {
  apply DASSOCF.
  assumption.
  assumption.
  }
  destruct tmp as (defx1,defx2).
  destruct ELM as [EQ|IN].
  destruct (Z.eq_dec (snd a) id).
  inversion EQ.
  simpl.
  rewrite updl_eq_l.
  rewrite H0.
  rewrite H1.
  replace (f b (f x1 x2)) with (f x2 (f b x1)).
  {
  rewrite X.
  apply fold_left_f_m_def with (def:=def).
  assumption.
  inversion NODUP.
  assumption.
  unfold defl in *.
  intros.
  apply DEFL with id1 id2.
  assumption.
  right.
  assumption.
  right.
  assumption.
  apply DASSOC.
  assumption.
  apply DCOMM.
  assumption.
  apply DCOMM.
  assumption.
  intros.
  apply in_map_iff in IN.
  destruct IN as (y0,(EQ0,IN)).
  destruct y0 as (x0',x1').
  simpl in EQ0.
  rewrite <- EQ0.
  rewrite EQ in DEFL.
  split.
  apply DCOMM.
  apply DASSOCF with x1.
  apply DEFL with id x1'.
  unfold not.
  intros.
  rewrite e in NODUP.
  inversion NODUP.
  apply H4.
  rewrite H.
  apply in_map_iff.
  exists (x0', x1').
  auto.
  left.
  reflexivity.
  right.
  apply in_map_iff.
  exists (x0', x1').
  auto.
  assumption.
  apply DASSOC.
  apply DEFLb.
  right.
  apply in_map_iff.
  exists (x0', x1').
  auto.
  apply DCOMM.
  apply DASSOCF with x2.
  rewrite COMM.
  apply DEFL with id x1'.
  unfold not.
  intros.
  rewrite e in NODUP.
  inversion NODUP.
  apply H4.
  rewrite H.
  apply in_map_iff.
  exists (x0', x1').
  auto.
  left.
  reflexivity.
  right.
  apply in_map_iff.
  exists (x0', x1').
  auto.
  apply DCOMM.
  assumption.
  apply DCOMM.
  assumption.
  apply DCOMM.
  assumption.
  }
  symmetry.
  replace (f b x1) with (f x1 b).
  replace (f x2 (f x1 b)) with (f (f x2 x1) b).
  rewrite COMM.
  replace (f x2 x1) with (f x1 x2).
  reflexivity.
  apply COMM.
  assumption.
  apply DCOMM.
  assumption.
  apply ASSOC.
  apply DCOMM.
  assumption.
  assumption.
  assumption.
  apply COMM.
  assumption.
  assumption.

  simpl.
  inversion EQ.
  contradiction.
  {
  simpl.
  destruct (Z.eq_dec (snd a) id ).
  rewrite e in NODUP.
  inversion NODUP.
  exfalso.
  apply H1.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  inversion EQy.
  apply in_map_iff.
  exists y.
  auto.
  apply IHl.
  inversion NODUP.
  assumption.
  unfold defl in *.
  intros.
  apply DEFL with id1 id2.
  assumption.
  right.
  assumption.
  right.
  assumption.
  assumption.
  intros.
  apply DASSOC.
  apply DEFLb.
  right.
  assumption.
  destruct a as (a0,a1).
  apply in_map_iff in IN0.
  destruct IN0 as (c,(EQc,INc)).
  destruct c as (c0,c1).
  simpl in EQc.
  simpl.
  rewrite <- EQc.
  apply DEFL with c1 a1.
  unfold not.
  intros.
  inversion NODUP.
  apply H2.
  rewrite <- H.
  apply in_map_iff.
  exists (c0, c1).
  auto.
  right.
  apply in_map_iff.
  exists (c0, c1).
  auto.
  left.
  reflexivity.
  apply DCOMM.
  apply DEFLb.
  left.
  reflexivity.
  assumption.
  assumption.
  }
Qed.

Lemma fold_left_move_m_eq2 A B def (f: B -> B -> B) (m: (A * Z) -> B) (CAN: can def f) x1 x2 id:
  forall (l: list (A * Z)) b x
         (NODUP: NoDup (map snd l))
         (DEFL: defl def (map (fun x => (m x, snd x)) l))
         (DEFx2b: def x2 b)
         (DEFLb: forall x (IN: In x (map m l)), def x b)
         (DEFLx2: forall x (IN: In x (map m l)), def x x2)
         (ELM: In (x1,id) (map (fun x => (m x, snd x)) l))
         (X: m (x,id) = f x1 x2),
    f x2 (fold_left f (map m l) b) = fold_left f (map m (updl l id (x,id))) b.
Proof.
  induction l.
  simpl.
  intros.
  contradiction.
  assert (CAN1:=CAN).
  unfold can in CAN1.
  destruct CAN1 as (COMM,(ASSOC,(DASSOC,(DASSOCF,(DCOMM,(DREF,NUT)))))).
  simpl.
  intros.


  assert (tmp: def x1 x2).
  {
  apply DEFLx2.
  destruct ELM as [EQ|IN].
  inversion EQ.
  auto.
  right.
  apply in_map_iff.
  apply in_map_iff in IN.
  destruct IN as (y,(EQy,INy)).
  inversion EQy.
  exists y.
  auto.
  }

  destruct ELM as [EQ|IN].
  inversion EQ.
  repeat dstr_.
  rewrite updl_eq_l.
  replace (f b (f x1 x2)) with (f x2 (f b x1)).
  {
  symmetry.
  apply fold_left_f_m_def with (def:=def).
  assumption.
  inversion NODUP.
  assumption.
  unfold defl in *.
  intros.
  apply DEFL with id1 id2.
  assumption.
  right.
  assumption.
  right.
  assumption.
  apply DASSOC.
  assumption.
  apply DCOMM.
  assumption.
  apply DCOMM.
  apply DEFLb.
  tauto.
  intros.
  apply in_map_iff in IN.
  destruct IN as (y0,(EQ0,IN)).
  destruct y0 as (x0',x1').
  simpl in EQ0.
  rewrite <- EQ0.
  split.
  apply DEFLx2.
  right.
  apply in_map.
  assumption.
  apply DASSOC.
  apply DEFLb.
  right.
  apply in_map.
  assumption.
  apply DEFL with x1' id.
  unfold not.
  intros.
  rewrite H in IN.
  inversion NODUP.
  apply H2.
  apply in_map_iff.
  exists (x0', id).
  auto.
  right.
  apply in_map_iff.
  exists (x0', x1').
  auto.
  left.
  reflexivity.
  apply DCOMM.
  apply DEFLb.
  tauto.
  }
  rewrite COMM.
  apply ASSOC.
  apply DCOMM.
  apply DEFLb.
  tauto.
  apply DCOMM. 
  assumption.
  assumption.
  apply DASSOC.
  assumption.
  apply DCOMM.
  apply DEFLx2.
  tauto.
  apply DCOMM.
  apply DEFLb.
  tauto.
  assumption.
  apply in_map_iff in IN.
  destruct IN as (y0,(EQ0,IN)).
  destruct y0 as (x0',x1').
  simpl in EQ0.
  inversion EQ0.
  destruct (Z.eq_dec (snd a) id).
  rewrite e in NODUP.
  rewrite H1 in IN.
  inversion NODUP.
  exfalso.
  apply H3.
  apply in_map_iff.
  exists (x0',id).
  auto.
  apply IHl.
  inversion NODUP.
  assumption.
  unfold defl.
  intros.
  apply DEFL with id1 id2.
  assumption.
  right.
  assumption.
  right.
  assumption.
  apply DASSOC.
  assumption.
  apply DCOMM.
  apply DEFLx2.
  left.
  reflexivity.
  apply DCOMM.
  apply DEFLb.
  left.
  reflexivity.
  intros.
  apply DASSOC.
  apply DEFLb.
  right.
  assumption.
  apply in_map_iff in IN0.
  destruct IN0 as (y0,(EQ1,IN1)).
  destruct y0 as (y0,y1).
  apply DEFL with y1 (snd a).
  unfold not.
  intros.
  rewrite <- H in NODUP.
  inversion NODUP.
  apply H4.
  apply in_map_iff.
  exists (y0, y1).
  auto.
  rewrite <- EQ1.
  right.
  apply in_map_iff.
  exists (y0, y1).
  auto.
  left.
  reflexivity.
  apply DCOMM.
  apply DEFLb.
  left.
  reflexivity.
  intros.
  apply DEFLx2.
  right.
  assumption.
  apply in_map_iff.
  exists (x0', x1').
  auto.
  assumption.
Qed.

(*
Lemma fold_left_g A B def (f: A -> A -> A) (g: A -> B) (CAN: can def f) (DEF: forall a b, def a b):
  forall (l: list A) a b,
    g (fold_left f l (f a b)) = g (f b (fold_left f l a)).
Proof.
  induction l.
  simpl.
  intros.
  assert (CAN1:=CAN).
  unfold can in CAN1.
  destruct CAN1 as (COMM,(ASSOC,(DASSOC,(DASSOCF,(DCOMM,(DREF,NUT)))))).
  rewrite COMM.
  reflexivity.
  apply DEF.
  simpl.
  intros.
  replace (f (f a0 b) a) with (f b (f a0 a)).
  rewrite fold_left_f with (def:=def).
  reflexivity.
  assumption.
  assumption.
  assert (CAN1:=CAN).
  unfold can in CAN1.
  destruct CAN1 as (COMM,(ASSOC,(DASSOC,(DASSOCF,(DCOMM,(DREF,NUT)))))).
  replace (f a0 a) with (f a a0).
  rewrite ASSOC.
  rewrite <- ASSOC.
  apply COMM.
  apply DEF.
  apply DEF.
  apply DEF.
  apply DEF.
  apply DEF.
  apply DEF.
  apply DEF.
  apply COMM.
  apply DEF.
Qed.
*)

(*Class cang A B (f: A -> A -> A) (g: A -> B) :=
{
  fg_comm : forall x y, g (f x y) = g (f y x);
  fg_perm: forall l l' b (Perm: Permutation l l'), g (fold_left f l b) = g (fold_left f l' b)
}.*)

Definition cang A (f: A -> A -> A) (g: A -> Prop) :=
  (forall x y, g (f x y) -> g (f y x)) /\
  forall l l' b (Perm: Coq.Sorting.Permutation.Permutation l l'), g (fold_left f l b) -> g (fold_left f l' b).

Lemma fold_left_g_back A (f: A -> A -> A) (g: A -> Prop) (CAN: cang f g):
  forall (l: list A) a b,
    g (fold_left f l (f a b)) -> g (fold_left f (b::l) a).
Proof.
  simpl.
  intros.
  assumption.
Qed.

Lemma fold_left_g_back2 A (f: A -> A -> A) (g: A -> Prop) (CAN: cang f g):
  forall (l: list A) a b,
    g (fold_left f (b::l) a) -> g (fold_left f l (f a b)).
Proof.
  simpl.
  intros.
  assumption.
Qed.

Lemma fold_left_g_can A (f: A -> A -> A) (g: A -> Prop) (CAN: cang f g):
  forall (l: list A) a b,
    g (f b (fold_left f l a)) -> g (fold_left f l (f a b)).
Proof.
  induction l.
  simpl.
  unfold cang in CAN.
  destruct CAN as (COMM,PERM).
  intros.
  apply COMM.
  assumption.
  simpl.
  intros.
  apply IHl in H.
  apply fold_left_g_back in H.
  apply fold_left_g_back in H.
  apply fold_left_g_back2.
  trivial.
  apply fold_left_g_back2.
  trivial.
  destruct CAN as (COMM,PERM).
  apply PERM with (a :: b :: l).
  apply perm_swap.
  assumption.
  trivial.
  trivial.
Qed.

Lemma fold_left_g_can2 A (f: A -> A -> A) (g: A -> Prop) (CAN: cang f g):
  forall (l: list A) a b,
    g (fold_left f l (f a b)) -> g (f b (fold_left f l a)).
Proof.
  induction l.
  simpl.
  unfold cang in CAN.
  destruct CAN as (COMM,PERM).
  intros.
  apply COMM.
  assumption.
  simpl.
  intros.
  apply IHl.
  apply fold_left_g_back in H.
  apply fold_left_g_back in H.
  apply fold_left_g_back2.
  trivial.
  apply fold_left_g_back2.
  trivial.
  destruct CAN as (COMM,PERM).
  apply PERM with (b :: a :: l).
  apply perm_swap.
  assumption.
  trivial.
  trivial.
Qed.


(** # <font size="5"><b> concat </b></font> # *)

Lemma concat_map_filter A B (f1: A -> list B) (f2: A -> bool):
  forall (l: list A)
         (FIL: forall x (IN: In x l), f2 x = false -> f1 x = nil),
    concat (map f1 (filter f2 l)) = concat (map f1 l).
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct (f2 a) eqn:f2a.
  simpl.
  rewrite IHl.
  reflexivity.
  intros.
  apply FIL.
  right.
  assumption.
  assumption.
  apply FIL in f2a.
  rewrite f2a.
  simpl.
  apply IHl.
  intros.
  apply FIL.
  right.
  assumption.
  assumption.
  left.
  reflexivity.
Qed.

Lemma concat_move_eq A (m: (A * Z) -> list Z) :
  forall (l: list (A * Z)) x O O1 O2 id
         (UNQ: NoDup (map snd l))
         (PERM: Permutation.Permutation (O1 ++ O2) O)
         (ELM: In O (map m (elem id l)))
         (Mx: m x = O1),
    count_occ Z.eq_dec (concat (map m l)) = count_occ Z.eq_dec (O2 ++ concat (map m (updl l id x))).
Proof.
  induction l.
  simpl.
  intros.
  contradiction.
  simpl.
  intros.
  destruct (Z.eq_dec (snd a) id).
  rewrite e in ELM.
  destruct (id =? id)%Z eqn:idid.
  simpl in ELM.
  destruct ELM as [EQ|IN].
  rewrite EQ.
  rewrite Mx.
  rewrite updl_eq_l.
  apply functional_extensionality.
  intros.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite plus_assoc.
  replace (count_occ Z.eq_dec O2 x0 + count_occ Z.eq_dec O1 x0) with
    (count_occ Z.eq_dec O1 x0 + count_occ Z.eq_dec O2 x0). 
  erewrite <- count_perm.
  reflexivity.
  apply PERM.
  reflexivity.
  apply plus_comm.
  rewrite <- e.
  assumption.
  apply in_map_iff in IN.
  destruct IN as (y,(EQ,IN)).
  unfold elem in IN.
  apply filter_In in IN.
  destruct IN as (IN, EQ1).
  apply Z.eqb_eq in EQ1.
  rewrite e in UNQ.
  exfalso.
  inversion UNQ.
  apply H1.
  apply in_map_iff.
  exists y.
  auto.
  apply neqb_neq in idid.
  contradiction.
  apply functional_extensionality.
  intros.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite plus_assoc.
  rewrite IHl with (x:=x) (O:=O) (O1:=O1) (O2:=O2) (id:=id).
  rewrite <- count_app.
  omega.
  inversion UNQ.
  assumption.
  assumption.
  destruct (snd a =? id)%Z eqn:az.
  apply Z.eqb_eq in az.
  contradiction.
  assumption.
  assumption.
Qed.

Lemma map_updl_eq A m:
  forall (l:list (A * Z)) z x 
         (UNQ: NoDup (map snd l))
         (RED: forall x' (IN: In (x',z) l), m (x',z) = m (x,z)),
    count_occ Z.eq_dec (concat (map m l)) = count_occ Z.eq_dec (concat (map m (updl l z (x,z)))).
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct a.
  simpl in *.
  destruct (Z.eq_dec z0 z).
  apply functional_extensionality.
  intros.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite <- IHl.
  rewrite <- RED with a.
  rewrite <- e.
  reflexivity.
  rewrite <- e.
  left.
  reflexivity.
  inversion UNQ.
  assumption.
  intros.
  apply RED.
  right.
  assumption.
  apply functional_extensionality.
  intros.
  rewrite <- count_app.
  rewrite <- count_app.
  rewrite <- IHl.
  reflexivity.
  inversion UNQ.
  assumption.
  intros.
  apply RED.
  right.
  assumption.
Qed.

