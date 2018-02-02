Require Import Coq.Bool.Bool.
Require Import ZArith.
Require Import Coq.Init.Nat.
Require Import Qcanon.
Require Import List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sorting.Permutation.
Require Import Util_Z.
Require Import Util_list.
Require Import Programs.
Require Import Assertions.
Require Import PrecedenceRelation.

Set Implicit Arguments.

Open Local Scope nat.

Definition one_ob (o:Z) (Wt Ot: nat) : bool:=
  orb (eqb Wt 0) (ltb 0 Ot).

Definition spare_ob (o:Z) (Wt Ot: nat) : bool :=
  orb (eqb Wt 0) (ltb Wt Ot).

Definition own_ob (o:Z) (Wt Ot: nat) : bool :=
  leb Wt Ot.

Definition safe_obs (o:Z) (Wt Ot: nat) (R: Z -> Z) (L: Z -> Z) (P: Z -> bool) (X: Z -> list Z) := 
  andb (one_ob o Wt Ot)
       (andb (orb (negb (P o))(spare_ob o Wt Ot))
             (orb (negb (ifb (In_dec Z.eq_dec (R o) (X (L o))))) (own_ob o Wt Ot))).

(** # <font size="5"><b> Weakest Precondition </b></font> # *)

Definition inv := bag -> bag -> bag -> lassn.

Open Local Scope Z.

Definition M_to_crd M v : lassn :=
  match M with 
    | true => Lacredit v
    | _ => Labool true
  end.

Definition prc0 (o:Z) (O: list Z) (R: Z -> option Z) (L: Z -> Z) (P: Z -> bool) (X: Z -> list Z) := 
  dom_f R (o::O) ->
  prc o O (lift_f 0 R) L P X = true.

Definition nexc x (R: Z -> option Z) X (L: Z -> Z) :=
  R x <> None ->
  ~ In ((lift_f 0 R) x) (X (L x)).

Definition safe_obs0 (o:Z) (Wt Ot: nat) (R: Z -> option Z) (L: Z -> Z) (P: Z -> bool) (X: Z -> list Z) := 
  R o <> None ->
  safe_obs o Wt Ot (lift_f 0 R) L P X = true.


Fixpoint weakest_pre (c:cmd) (Q: Z -> assn) (se: exp -> exp) (R: Z -> option Z) (I: Z -> inv) (L: Z -> Z) (M: Z -> bool) (P: Z -> bool) (X: Z -> list Z) : assn :=
  match c with
    | Val z => Q z
    | Cons e => FA r, (r |-> ([[se e]]) --* (Q r))
    | Lookup e => EX z, (EX f, (Apointsto f ([[se e]]) z ** ((Apointsto f ([[se e]]) z) --* (Q z))))
    | Mutate e1 e2 => EX z, (([[se e1]]) |-> z) ** ((Apointsto 1 ([[se e1]]) ([[se e2]])) --* (Q 0))
    | Let x c1 c2 => weakest_pre c1 (fun z => weakest_pre c2 Q (fun e => subse x z (se e)) R I L M P X) se R I L M P X
    | Fork c => EX O, (EX O', ((Aobs(O ++ O') ** (Aobs(O) --* Q 0)) ** (Aobs(O') --* weakest_pre c (fun _ => Aobs(nil)) se R I L M P X)))
    | Newlock => FA l, (Aulock l empb empb empb --* Q l)
    | Acquire l => EX O, ((Aprop (prc0 ([[se l]]) O R L P X) &* (Alock ([[se l]]) ** Aobs O)) **
        (FA wt, (FA ot, (FA ct, ((Aobs ([[se l]]::O) ** Alocked ([[se l]]) wt ot ct ** (Alasn (I ([[se l]]) wt ot ct))) --* Q 0)))))
    | Release l => EX O, (EX wt, (EX ot, (EX ct,
        ((Aobs (([[se l]])::O) ** Alocked ([[se l]]) wt ot ct ** (Alasn (I ([[se l]]) wt ot ct))) **
        ((Aobs O ** Alock ([[se l]])) --* Q 0)))))
    | Newcond => FA v, (Acond v --* Q v)
    | Waiting4lock l => EX O, (Aprop (prc0 ([[se l]]) O R L P X) &* (Alock ([[se l]]) ** Aobs O) **
        (FA wt, (FA ot, (FA ct, (Aobs ([[se l]]::O) ** Alocked ([[se l]]) wt ot ct ** (Alasn (I ([[se l]]) wt ot ct))) --* Q 0))))
    | Wait v l => EX O, (EX wt, (EX ot, (EX ct,
        ((Abool (Z.eqb (L ([[se v]])) ([[se l]])) &*
        (Aprop (safe_obs0 ([[se v]]) (S (wt ([[se v]]))) (ot ([[se v]])) R L P X) &*
        Aprop (prc0 ([[se v]]) O R L P X) &*
        Aprop (prc0 ([[se l]]) O R L P X))) &* 
        (Aobs (([[se l]])::O) ** Acond ([[se v]]) ** Alocked ([[se l]]) wt ot ct ** (Alasn (I ([[se l]]) (incb wt ([[se v]])) ot ct))))))) **
        (FA wt', (FA ot', (FA ct', ((Aobs (([[se l]])::O) ** Alocked ([[se l]]) wt' ot' ct' ** (Alasn (I ([[se l]]) wt' ot' ct')) ** 
        (Alasn (M_to_crd (M ([[se v]])) ([[se v]])))) --* Q 0))))
    | Waiting4cond v l => EX O, ((Abool (Z.eqb (L ([[se v]])) ([[se l]])) &* ((Aprop (prc0 ([[se v]]) O R L P X)) &*
        (Aprop (prc0 ([[se l]]) O R L P X)))) &* (Acond ([[se v]]) ** Alock ([[se l]]) ** Aobs O)) **
        (FA wt, (FA ot, (FA ct, ((Aobs ([[se l]]::O) ** Alocked ([[se l]]) wt ot ct ** (Alasn (I ([[se l]]) wt ot ct)) **
        Alasn (M_to_crd (M ([[se v]])) ([[se v]]))) --* Q 0))))
    | Notify v => EX wt, (EX ot, (EX ct, (Acond ([[se v]]) ** Alocked (L ([[se v]])) wt ot ct ** (Alasn (M_to_crd (M ([[se v]])) ([[se v]]))) **
       ((Alocked (L ([[se v]])) (decb wt ([[se v]])) ot ct ** 
       ((Alasn (M_to_crd (M ([[se v]])) ([[se v]]))) |* Abool (ltb 0 (wt ([[se v]]))))) --* Q 0))))
    | NotifyAll v => EX wt, (EX ot, (EX ct ,(Abool (negb (M ([[se v]]))) &* (Acond ([[se v]]) ** Alocked (L ([[se v]])) wt ot ct **
       ((Alocked (L ([[se v]])) (rstb wt ([[se v]])) ot ct) ** 
       ((Alasn (M_to_crd (M ([[se v]])) ([[se v]]))) |* Abool (ltb 0 (wt ([[se v]])))) --* Q 0)))))
    | g_initl l => EX O, (EX wt, (EX ot, (EX ct, ((Abool (andb (negb (P ([[se l]])))(Z.eqb (L ([[se l]])) ([[se l]]))) &*
        (Aprop (nexc ([[se l]]) R X L)))
        &* Aulock ([[se l]]) wt ot ct ** (Alasn (I ([[se l]]) wt ot ct) ** Aobs O) **
        ((Alock ([[se l]]) ** Aobs O) --* Q 0)))))
    | g_dupl l => Alock ([[se l]]) ** ((Alock ([[se l]]) ** Alock ([[se l]])) --* (Q 0))
    | g_chrg v => EX O, (EX wt, (EX ot, (EX ct, (Acond ([[se v]]) ** Aobs O ** Alocked (L ([[se v]])) wt ot ct
        ** ((Aobs (([[se v]])::O) ** Alocked (L ([[se v]])) wt (incb ot ([[se v]])) ct) --* (Q 0))))))
    | g_chrgu v => EX O, (EX wt, (EX ot, (EX ct, (Acond ([[se v]]) ** Aobs O ** Aulock (L ([[se v]])) wt ot ct
        ** ((Aobs (([[se v]])::O) ** Aulock (L ([[se v]])) wt (incb ot ([[se v]])) ct) --* (Q 0))))))
    | g_disch v => EX O, (EX wt, (EX ot, (EX ct, ((Abool (ltb 0 (ot ([[se v]]))) &* Aprop (safe_obs0 ([[se v]]) (wt ([[se v]])) ((ot ([[se v]]) - 1)) R L P X))
        &* Acond ([[se v]]) ** Aobs (([[se v]])::O) ** Alocked (L ([[se v]])) wt ot ct
        ** ((Aobs O ** Alocked (L ([[se v]])) wt (decb ot ([[se v]])) ct) --* (Q 0))))))
    | g_dischu v => EX O, (EX wt, (EX ot, (EX ct, ((Abool (ltb 0 (ot ([[se v]]))) &* Aprop (safe_obs0 ([[se v]]) (wt ([[se v]])) ((ot ([[se v]]) - 1)) R L P X))
        &* Acond ([[se v]]) ** Aobs (([[se v]])::O) ** Aulock (L ([[se v]])) wt ot ct
        ** ((Aobs O ** Aulock (L ([[se v]])) wt (decb ot ([[se v]])) ct) --* (Q 0))))))
    | g_gain v => EX wt, (EX ot, (EX ct, (Acond ([[se v]]) ** Alocked (L ([[se v]])) wt ot ct
        ** ((Alocked (L ([[se v]])) wt ot (incb ct ([[se v]])) ** Acredit ([[se v]])) --* (Q 0)))))
    | g_gainu v => EX wt, (EX ot, (EX ct, (Acond ([[se v]]) ** Aulock (L ([[se v]])) wt ot ct
        ** ((Aulock (L ([[se v]])) wt ot (incb ct ([[se v]])) ** Acredit ([[se v]])) --* (Q 0)))))
    | g_lose v => EX wt, (EX ot, (EX ct, (Abool (ltb 0 (ct ([[se v]]))) &* Acond ([[se v]]) ** Alocked (L ([[se v]])) wt ot ct ** Acredit ([[se v]])
        ** ((Alocked (L ([[se v]])) wt ot (decb ct ([[se v]]))) --* (Q 0)))))
    | g_loseu v => EX wt, (EX ot, (EX ct, (Abool (ltb 0 (ct ([[se v]]))) &* Acond ([[se v]]) ** Aulock (L ([[se v]])) wt ot ct ** Acredit ([[se v]])
        ** ((Aulock (L ([[se v]])) wt ot (decb ct ([[se v]]))) --* (Q 0)))))
    | g_info v => EX wt, (EX ot, (EX ct, (Acond ([[se v]]) ** Alocked (L ([[se v]])) wt ot ct ** Acredit ([[se v]])
        ** ((Abool (ltb 0 (ct ([[se v]]))) &* Alocked (L ([[se v]])) wt ot ct) --* (Q 0)))))
    | g_infou v => EX wt, (EX ot, (EX ct, (Acond ([[se v]]) ** Aulock (L ([[se v]])) wt ot ct ** Acredit ([[se v]])
        ** ((Abool (ltb 0 (ct ([[se v]]))) &* Aulock (L ([[se v]])) wt ot ct) --* (Q 0)))))
  end.

Fixpoint weakest_pre_tx (tx:context) (R: Z -> option Z) (I: Z -> inv) (L: Z -> Z) (M: Z -> bool) (P: Z -> bool) (X: Z -> list Z) : (Z -> assn) :=
  match tx with
    | done => fun _ => Aobs nil
    | Let' x c tx => fun z => weakest_pre (subs c (subse x z)) (weakest_pre_tx tx R I L M P X) id R I L M P X
  end.

Definition weakest_pre_ct (ct: (cmd * context)) (R: Z -> option Z) (I: Z -> inv) (L: Z -> Z) (M: Z -> bool) (P: Z -> bool) (X: Z -> list Z) : assn :=
  weakest_pre (fst ct) (weakest_pre_tx (snd ct) R I L M P X) id R I L M P X.

Lemma dom_f_perm A (f: Z -> option A):
  forall l l' 
         (PERM: Permutation l l')
         (DOM: dom_f f l),
    (dom_f f l').
Proof.
  intros l l' PERM.
  induction PERM;
  unfold dom_f in *;
  simpl;
  try tauto.
  intros.
  destruct H as [EQ|IN].
  apply DOM.
  left.
  assumption.
  apply IHPERM.
  intros.
  apply DOM.
  right.
  assumption.
  assumption.
  intros.
  apply DOM.
  tauto.
Qed.

Lemma sat_wait4cond:
  forall p O C v l tx R I L M P X
        (SAT: sat p (Some O) C (weakest_pre_ct (Waiting4cond v l, tx) R I L M P X)),
  exists (Pv: p ([[v]]) = Some Cond)
         (Pl: p ([[l]]) = Some Lock \/ exists wt ot ct, p ([[l]]) = Some (Locked wt ot ct))
         (lvl: L ([[v]]) = ([[l]]))
         (PRCl: prc0 ([[l]]) O R L P X)
         (PRCv: prc0 ([[v]]) O R L P X),
    sat p (Some O) (bagplus C (fun x => if Z.eq_dec x ([[v]]) then if bool_dec (M ([[v]])) true then 1%nat else 0%nat else 0%nat))
     (weakest_pre_ct (Waiting4lock l, tx) R I L M P X).
Proof.
  intros.
  simpl in SAT.
  destruct SAT as (v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,
    (opo1o2,(tmp1,(tmp2,(p1p2,C1C2))))))))))))))).
  destruct tmp1 as ((lvl,(prcv,prcl)),(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(o3,(o4,(C3,(C4,(opo3o4,(tmp1,(tmp3,(p3p4,C3C4))))))))))))))).
  destruct tmp3 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(o5,(o6,(C5,(C6,(opo5o6,(tmp5,((p6N,(C6N,opo6)),(p5p6,C5C6)))))))))))))).

  assert (phpdefp2p34: phplusdef p2 (phplus p3 p4)).
  {
  rewrite p3p4.
  apply phpdef_comm.
  assumption.
  }

  assert (PERMOv0: Permutation v0 O).
  {
  inversion opo6.
  rewrite <- H1 in opo5o6.
  inversion opo5o6.
  rewrite <- H2 in opo3o4.
  inversion opo3o4.
  rewrite <- H5 in opo1o2.
  inversion opo1o2.
  apply Permutation_trans with o'.
  assumption.
  apply Permutation_trans with o'0.
  assumption.
  apply Permutation_trans with o'1.
  assumption.
  assumption.
  }

  assert (p1l: p1 ([[l]]) = Some Lock \/
    exists wt ot ct : bag, p1 ([[l]]) = Some (Locked wt ot ct)).
  {
  rewrite <- p3p4.
  rewrite phplus_comm.
  apply phplus_lock.
  rewrite <- p5p6.
  apply phplus_lock.
  assumption.
  assumption.
  }

  assert (o2N: o2 = None).
  {
  destruct o2.
  inversion opo6.
  rewrite <- H1 in opo5o6.
  inversion opo5o6.
  rewrite <- H2 in opo3o4.
  inversion opo3o4.
  rewrite <- H5 in opo1o2.
  inversion opo1o2.
  reflexivity.
  }
  rewrite o2N in *.



  unfold id in *.
  exists.
  rewrite <- p1p2.
  rewrite <- p3p4.
  apply phplus_Cond.
  apply phpdef_comm.
  assumption.
  apply phplus_Cond;
  try assumption.
  exists.
  rewrite <- p1p2.
  apply phplus_lock.
  assumption.
  exists.
  apply Z.eqb_eq.
  tauto.
  exists.
  unfold prc0 in *.
  intros.
  apply prc_perm with v0.
  apply prcl.
  apply dom_f_perm with (([[l]]) :: O).
  apply perm_skip.
  apply Permutation_sym.
  assumption.
  assumption.
  apply Permutation_sym.
  assumption.
  exists.
  unfold prc0 in *.
  intros.
  apply prc_perm with v0.
  apply prcv.
  apply dom_f_perm with (([[v]]) :: O).
  apply perm_skip.
  apply Permutation_sym.
  assumption.
  assumption.
  apply Permutation_sym.
  assumption.

  simpl.
  exists v0.
  split.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12.
  exists (Some O), None, empb.

  exists (bagplus C (fun x => if Z.eq_dec x ([[v]]) then if bool_dec (M ([[v]])) true then 1%nat else 0%nat else 0%nat)).
  exists.
  apply fs_op.
  apply Permutation_refl.
  exists.
  exists p1, (emp knowledge).
  exists.
  apply phpdef_emp.
  exists bp1, boundph_emp.
  exists.
  rewrite phplus_emp.
  assumption.
  exists None, (Some O), empb, empb.
  exists.
  apply sn_op.
  apply Permutation_refl.
  split.
  assumption.
  split.
  split.
  reflexivity.
  split.
  reflexivity.
  apply fs_op.
  assumption.
  rewrite phplus_emp.
  tauto.
  split.
  intros.
  destruct SAT as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(o7,(o8,(C7,(C8,(opo7o8,((p7N,(C7N,op7)),(tmp9,tmp10))))))))))))).
  destruct tmp9 as (p9,(p0,(phpdefp9p0,(bp9,(bp0,(bp90,(o9,(o0,(C9,(C0,(opo9o0,(tmp12,(tmp13,tmp14))))))))))))).
  rewrite <- C1C2.
  replace (bagplus C1 C2) with (bagplus C2 C1).
  rewrite bplus_assoc.
  rewrite bplus_assoc.
  apply tmp2 with v1 v2 v3 O'.
  assumption.
  assumption.
  assumption.
  assumption.
  exists (emp knowledge), p'.
  exists.
  apply phpdef_comm.
  apply phpdef_emp.
  exists boundph_emp.
  exists BP'.
  exists.
  rewrite phplus_comm.
  rewrite phplus_emp.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  exists (Some (([[l]]) :: v0)), None.

  exists empb, (bagplus C1 (bagplus (fun x => if Z.eq_dec x ([[v]]) then if bool_dec (M ([[v]])) true then 1%nat else 0%nat else 0%nat) C')).
  exists.
  inversion op7.
  rewrite <- H1 in opo7o8.
  inversion opo7o8.
  apply fs_op.
  apply Permutation_trans with o'.
  assumption.
  assumption.
  split.
  split.
  reflexivity.
  split.
  reflexivity.
  apply fs_op.
  apply Permutation_refl.
  exists.
  exists p9,p0.
  exists phpdefp9p0, bp9, bp0, bp90.
  exists None, None.

  exists (bagplus C1 C9), (bagplus (fun x => if Z.eq_dec x ([[v]]) then if bool_dec (M ([[v]])) true then 1%nat else 0%nat else 0%nat) C0).
  exists.
  apply None_op.
  split.
  assumption.
  split.
  exists p0, (emp knowledge).
  exists.
  apply phpdef_emp.
  exists bp0, boundph_emp.
  exists.
  rewrite phplus_emp.
  assumption.
  exists None, None.
  exists C0, (fun x => if Z.eq_dec x ([[v]]) then if bool_dec (M ([[v]])) true then 1%nat else 0%nat else 0%nat).
  exists.
  apply None_op.
  split.
  assumption.
  split.
  unfold M_to_crd.
  unfold id.
  destruct (M ([[v]])).
  simpl.
  rewrite eqz.
  exists 0%nat.
  omega.
  simpl.
  reflexivity.
  split.
  apply phplus_emp.
  apply bplus_comm.
  split.
  destruct tmp10 as (p7p8,C7C8).
  rewrite <- p7p8.
  rewrite p7N.
  replace (phplus (emp knowledge) p8) with (phplus p8 (emp knowledge)).
  rewrite phplus_emp.
  tauto.
  apply phplus_comm.
  apply phpdef_emp.
  destruct tmp10 as (p7p8,C7C8).
  rewrite <- C7C8.
  rewrite C7N.
  replace (bagplus empb C8) with (bagplus C8 empb).
  rewrite bplus_emp.
  destruct tmp14 as (p9p0,C9C0).
  rewrite bplus_assoc.
  rewrite bplus_comm.
  rewrite bplus_assoc.
  rewrite bplus_comm.
  rewrite bplus_assoc.
  rewrite bplus_assoc.
  replace (bagplus C0 (bagplus C1 C9)) with (bagplus C1 (bagplus C9 C0)).
  rewrite C9C0.
  rewrite bplus_comm.
  rewrite bplus_assoc.
  replace (bagplus C8 (fun x : Z => if Z.eq_dec x ([[v]]) then if bool_dec (M ([[v]])) true then 1%nat else 0%nat
      else 0%nat)) with (bagplus (fun x : Z => if Z.eq_dec x ([[v]])
      then if bool_dec (M ([[v]])) true then 1%nat else 0%nat else 0%nat) C8).
  reflexivity.
  apply bplus_comm.
  rewrite <- bplus_assoc.
  apply bplus_comm.
  apply bplus_comm.
  rewrite phplus_comm.
  rewrite phplus_emp.
  rewrite bplus_comm.
  rewrite bplus_emp.
  tauto.
  apply phpdef_comm.
  apply phpdef_emp.
  apply bplus_comm.
  rewrite bplus_comm.
  rewrite bplus_emp.
  auto.
Qed.


Lemma sat_wait4lock0:
  forall p O C l tx R I L M P X
      (SAT: sat p (Some O) C (weakest_pre_ct (Waiting4lock l, tx) R I L M P X)),
    (p ([[l]]) = Some Lock \/ exists wt ot ct, p ([[l]]) = Some (Locked wt ot ct)) /\
    prc0 ([[l]]) O R L P X.
Proof.
  intros.
  destruct SAT as (v,(sat4,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(opO1O2,(sat1,(sat2,(p1p2,C1C2)))))))))))))))).
  simpl in sat4.
  destruct sat1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,tmp1))))))))))).
  destruct tmp1 as (sat1, ((p4N,(C4N,op4)),(p3p4,C3C4))).

  assert (PERM: Permutation O v).
  {
  inversion op4.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  rewrite <- H2 in opO1O2.
  inversion opO1O2.
  apply Permutation_sym.
  apply Permutation_trans with o'.
  assumption.
  apply Permutation_trans with o'0.
  assumption.
  assumption.
  }

  simpl in sat1.
  rewrite <- p1p2.
  split.
  apply phplus_lock.
  rewrite <- p3p4.
  apply phplus_lock.
  assumption.
  unfold prc0 in *.
  intros.
  apply prc_perm with v.
  apply sat4.
  apply dom_f_perm with (([[l]]) :: O).
  apply perm_skip.
  assumption.
  assumption.
  assumption.
Qed.
