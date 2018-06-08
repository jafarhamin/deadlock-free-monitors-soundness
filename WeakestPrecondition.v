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

Set Implicit Arguments.

(** # <font size="5"><b> Weakest Precondition </b></font> # *)

Open Local Scope nat.

Definition safe_obs (o:location) (Wt Ot: nat) := 
  andb (orb (eqb Wt 0) (ltb 0 Ot))
       (andb (orb (negb (Pof o))(orb (eqb Wt 0) (ltb Wt Ot)))
             (orb (negb (ifb (In_dec Z.eq_dec (Rof o) (Xof o)))) (leb Wt Ot))).

Open Local Scope Z.

Definition inv := bag -> bag -> assn.

Definition prcl (o:location) (O: list location) : bool :=
  andb (orb (negb (ifb (In_dec Z.eq_dec (Rof o) (Xof o))))
            (andb (leb (length (filter (fun x => ifb (In_dec Z.eq_dec (Rof x) (Xof o))) O)) 1)
                  (forallb (fun x => orb (negb (ifb (In_dec Z.eq_dec (Rof x) (Xof o))))
                                         (Z.eqb (Lof x) (Lof o))) O)))
       (orb (forallb (fun x => Z.ltb (Rof o) (Rof x)) O)
            (andb (Pof o)
                  (andb (ifb (In_dec Z.eq_dec (Rof o) (Xof o)))
                        (forallb (fun x => orb (Z.ltb (Rof o) (Rof x)) 
                                               (andb (ifb (In_dec Z.eq_dec (Rof x) (Xof o)))
                                                     (andb (Z.eqb (Lof x) (Lof o))
                                                           (Z.leb (Rof o) (Rof x + 1))))) O)))).

Lemma prcl_perm:
  forall O O' o
         (PRC: prcl o O = true)
         (PERM: Permutation O' O),
    prcl o O' = true.
Proof.
  unfold prcl.
  intros.
  apply Coq.Bool.Bool.andb_true_iff in PRC.
  destruct PRC as (PRC1,PRC2).
  apply Coq.Bool.Bool.orb_true_iff in PRC1.
  apply Coq.Bool.Bool.orb_true_iff in PRC2.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  apply Coq.Bool.Bool.orb_true_iff.
  destruct PRC1 as [PRC1|PRC1].
  left.
  assumption.
  right.
  apply Coq.Bool.Bool.andb_true_iff in PRC1.
  destruct PRC1 as (PRC1,PRC1').
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  apply Nat.leb_le.
  apply Nat.leb_le in PRC1.
  rewrite prem_length_eq with (l':=O).
  assumption.
  assumption. 
  apply forallb_forall.
  intros.
  apply forallb_forall with (x:=x) in PRC1'.
  apply PRC1'.
  apply Permutation_in with O'.
  assumption.
  assumption.
  apply Coq.Bool.Bool.orb_true_iff.
  destruct PRC2 as [PRC2|PRC2].
  left.
  apply forallb_forall.
  intros.
  apply forallb_forall with (x:=x) in PRC2.
  apply PRC2.
  apply Permutation_in with O'.
  assumption.
  assumption.
  right.
  apply Coq.Bool.Bool.andb_true_iff in PRC2.
  destruct PRC2 as (PRC2, PRC2').
  apply Coq.Bool.Bool.andb_true_iff in PRC2'.
  destruct PRC2' as (PRC2', PRC2'').
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  assumption.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  assumption.
  apply forallb_forall.
  intros.
  apply forallb_forall with (x:=x) in PRC2''.
  apply PRC2''.
  apply Permutation_in with O'.
  assumption.
  assumption.
Qed.

(*
Fixpoint list_eqb (l1 l2: list Z) :=
  match l1,l2 with
    | nil, nil => true
    | (h1::t1), (h2::t2) => andb (Z.eqb h1 h2) (list_eqb t1 t2)
    | _, _ => false
  end.

Definition Zlist_eqb (l1 l2: (Z * list Z)) : bool :=
  andb (Z.eqb (fst l1) (fst l2)) (list_eqb (snd l1) (snd l2)).

Definition inv_table : Z -> inv :=
  fun _ => fun _ _ => Abool (Z.eqb 0 0).
*)

Definition array (l: locatione) (index: nat) : locatione :=
  (Eplus (Aof l) (Enum (Z.of_nat index)), Rof l, Iof l, Lof l, Xof l, Mof l, Pof l).

Definition points_tos (ns: list nat) (l: locatione) : list assn := map (fun index => array l index |-> (Enum 0)) ns.

Fixpoint weakest_pre (c:cmd) (Q: Z -> assn) (se: exp -> exp) (invs: Z -> inv) : assn :=
  match c with
    | Val e => Q ([[se e]])
    | Cons n => FA l, (fold_left Astar (points_tos (seq O n) l) (Abool true) --* (Q ([[Aof l]])))
    | Lookup e => EX l, (EX z, (EX f, (Abool (Z.eqb ([[se e]]) ([[Aof l]])) &* Apointsto f l (Enum z) ** (Apointsto f l (Enum z) --* Q z))))
    | Mutate e1 e2 => EX l, (EX z, (Abool (Z.eqb ([[se e1]]) ([[Aof l]])) &* l |-> z) ** (l |-> (se e2) --* Q 0))
    | Let x c1 c2 => weakest_pre c1 (fun z => weakest_pre c2 Q (fun e => subse x z (se e)) invs) se invs
    | Fork c => EX O, (EX O', ((Aobs(O ++ O') ** (Aobs(O) --* Q 0)) ** (Aobs(O') --* weakest_pre c (fun _ => Aobs(nil)) se invs)))

    | Newlock => FA l, (EX r, (EX x, 
        Abool (negb (ifb (In_dec Z.eq_dec r x))) &* (Aulock (Enum l,r,(0,nil),Enum l,x,(0,nil),false) empb empb --* Q l)))

    | g_initl e => EX l, (EX O, (EX wt, (EX ot, (EX i, (EX params, ((Abool (Z.eqb ([[se e]]) ([[Aof l]]))
        &* Aulock l wt ot ** subsas params (invs i wt ot) ** Aobs O ** ((Alock (Aof l, Rof l, (i,params), Lof l, Xof l, Mof l, Pof l) ** Aobs O) --* Q 0))))))))
    | Acquire e => EX O, (EX l, ((Abool (andb (Z.eqb ([[se e]]) ([[Aof l]])) (prcl (evall l) (map evall O))) &* Alock l ** Aobs O) **
        (FA wt, (FA ot, ((Aobs (l::O) ** Alocked l wt ot ** 
        (subsas (snd (Iof l)) (invs (fst (Iof l)) wt ot)))) --* Q 0))))
    | Release e => EX O, (EX l, (EX wt, (EX ot,
        ((Abool (Z.eqb ([[se e]]) ([[Aof l]])) &* Aobs (l::O) ** Alocked l wt ot ** 
        (subsas (snd (Iof l)) (invs (fst (Iof l)) wt ot)))) ** ((Aobs O ** Alock l --* Q 0)))))
    | Newcond => FA v, (EX R, (EX l, (EX M, (EX P, (EX wt, (EX ot,
        (Aulock l wt ot ** (Aulock l wt ot ** Acond (Enum v,R,(0,nil),Aof l,Xof l,M,P) --* Q v))))))))

    | Waiting4lock e => EX O, (EX l, ((Abool (andb (Z.eqb ([[se e]]) ([[Aof l]])) (prcl (evall l) (map evall O))) &* Alock l ** Aobs O) **
        (FA wt, (FA ot, ((Aobs (l::O) ** Alocked l wt ot ** 
        (subsas (snd (Iof l)) (invs (fst (Iof l)) wt ot)))) --* Q 0))))
    | Wait ev el => EX O, (EX l, (EX v, (EX wt, (EX ot,
        (Abool (andb (Z.eqb ([[se ev]]) ([[Aof v]]))
        (andb (Z.eqb ([[se el]]) ([[Aof l]]))
        (andb (Z.eqb ([[Lof v]]) ([[Aof l]]))
        (andb (safe_obs (evall v) (S (wt ([[Aof v]]))) (ot ([[Aof v]])))
        (andb (prcl (evall v) (map evall O))
        (prcl (evall l) (map evall O))))))) &* 
        ((subsas (snd (Iof l)) (invs (fst (Iof l)) (upd Z.eq_dec wt ([[Aof v]]) (S (wt ([[Aof v]])))) ot)) ** Aobs (l::O) ** Acond v ** Alocked l wt ot)))) **
        (FA wt', (FA ot', ((Aobs (l::O) ** Alocked l wt' ot' ** (subsas (snd (Iof l)) (invs (fst (Iof l)) wt' ot')) ** 
        (subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb))) --* Q 0)))))
    | Waiting4cond ev el => EX O, (EX l, (EX v, 
        (Abool (andb (Z.eqb ([[se ev]]) ([[Aof v]]))
        (andb (Z.eqb ([[se el]]) ([[Aof l]]))
        (andb (Z.eqb ([[Lof v]]) ([[Aof l]]))
        (andb (prcl (evall v) (map evall O))
        (prcl (evall l) (map evall O))))))) &* (Acond v ** Alock l ** Aobs O) **
        (FA wt, (FA ot, ((Aobs (l::O) ** Alocked l wt ot ** (subsas (snd (Iof l)) (invs (fst (Iof l)) wt ot)) **
        (subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb)) --* Q 0))))))
    | Notify ev => EX O, (EX wt, (EX ot, (EX l, (EX v, (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (Z.eqb ([[se ev]]) ([[Aof v]]))) &* 
       (subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb)) ** Acond v ** Alocked l wt ot ** Aobs (O) **
       ((Acond v ** Alocked l (upd Z.eq_dec wt ([[Aof v]]) (wt ([[Aof v]]) - 1)%nat) ot **
       (subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb) |* Abool (ltb 0 (wt ([[Aof v]])))) ** Aobs (O)) --* Q 0))))))
    | NotifyAll ev => EX wt, (EX ot, (EX l, (EX v, ((Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (Z.eqb ([[se ev]]) ([[Aof v]])))
       &* Aprop (subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb) = Aemp)) ** Acond v ** Alocked l wt ot ** 
       ((Acond v ** Alocked l (upd Z.eq_dec wt ([[Aof v]]) 0%nat) ot) --* Q 0)))))
    | g_newctr => FA gc, Actr (Enum gc) 0 --* Q 0
    | g_ctrdec ev => EX n, (Actr (se ev) n ** Atic (se ev) ** (Actr (se ev) (n-1)%nat --* Q 0))
    | g_ctrinc ev => EX n, (Actr (se ev) n ** (Actr (se ev) (S n)%nat ** Atic (se ev) --* Q 0))
    | g_disch ev => EX O, (EX wt, (EX ot, (EX l, (EX v, (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (andb (Z.eqb ([[se ev]]) ([[Aof v]]))
        (andb (safe_obs (evall v) (wt ([[se ev]])) ((ot ([[se ev]]) - 1))) (ltb 0 (ot ([[se ev]]))))))
        &* Acond v ** Aobs (v::O) ** Alocked l wt ot 
        ** ((Acond v ** Aobs O ** Alocked l wt (upd Z.eq_dec ot ([[se ev]]) (ot ([[se ev]]) - 1)%nat)) --* Q 0))))))
    | g_dischu ev => EX O, (EX wt, (EX ot, (EX l, (EX v, (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (andb (Z.eqb ([[se ev]]) ([[Aof v]]))
        (andb (safe_obs (evall v) (wt ([[se ev]])) ((ot ([[se ev]]) - 1))) (ltb 0 (ot ([[se ev]]))))))
        &* Acond v ** Aobs (v::O) ** Aulock l wt ot 
        ** ((Acond v ** Aobs O ** Aulock l wt (upd Z.eq_dec ot ([[se ev]]) (ot ([[se ev]]) - 1)%nat)) --* Q 0))))))
    | g_chrg ev => EX O, (EX wt, (EX ot, (EX l, (EX v, (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (Z.eqb ([[se ev]]) ([[Aof v]])))
        &* Acond v ** Aobs O ** Alocked l wt ot 
        ** ((Acond v ** Aobs (v::O) ** Alocked l wt (upd Z.eq_dec ot ([[se ev]]) (ot ([[se ev]]) + 1)%nat)) --* Q 0))))))
    | g_chrgu ev => EX O, (EX wt, (EX ot, (EX l, (EX v, (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (Z.eqb ([[se ev]]) ([[Aof v]])))
        &* Acond v ** Aobs O ** Aulock l wt ot 
        ** ((Acond v ** Aobs (v::O) ** Aulock l wt (upd Z.eq_dec ot ([[se ev]]) (ot ([[se ev]]) + 1)%nat)) --* Q 0))))))
    | _ => Abool true
  end.

Fixpoint weakest_pre_tx (tx:context) invs : (Z -> assn) :=
  match tx with
    | done => fun _ => Aobs nil
    | Let' x c tx => fun z => weakest_pre (subs c (subse x z)) (weakest_pre_tx tx invs) id invs
    | If' c1 c2 tx => fun z => if Z.ltb 0 z then 
        weakest_pre c1 (weakest_pre_tx tx invs) id invs else
        weakest_pre c2 (weakest_pre_tx tx invs) id invs
  end.

Definition weakest_pre_ct (ct: (cmd * context)) invs : assn :=
  weakest_pre (fst ct) (weakest_pre_tx (snd ct) invs) id invs.


Lemma sat_weak_imp:
  forall c p o d se a a' invs (BP: boundph p) (BG: boundgh d)
         (SAT: sat p o d (weakest_pre c a se invs))
         (IMP: forall z, a z |= a' z),
    sat p o d (weakest_pre c a' se invs).
Proof.
  induction c;
  try reflexivity.
  simpl.
  intros.
  apply IMP.
  assumption.
  assumption.
  assumption.
  simpl.
  intros.
  apply IMP.
  assumption.
  assumption.
  apply SAT with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opO1O2,(tmp1,tmp2)))))))))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v, v0, v1.
  split.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2, C1, C2, ghpdefC1C2, BC1, BC2, BC1C2, opO1O2.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  assumption.
  apply tmp2 with O';
  try tauto.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC12,(opO1O2,(tmp1,tmp2)))))))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v, v0, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2, C1, C2, ghpdefC1C2, BC1, BC2, BC12, opO1O2.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  assumption.
  apply tmp2 with O';
  try tauto.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(BC1,(BC2,(ghpdefC1C2,(bc12,(opO1O2,(tmp1,tmp2)))))))))))))))))).
  destruct tmp1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,tmp1))))))))))))))).
  destruct tmp1 as (tmp1, tmp3).
  destruct tmp3 as (tmp3, tmp5).
  destruct tmp2 as (tmp2,tmp4).
  exists v, v0, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2, C1, C2, BC1, BC2, ghpdefC1C2, bc12, opO1O2.
  split.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, BC3, BC4, ghpdefC3C4, bc34, opO3O4.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  assumption.
  apply tmp3 with (O':=O');
  try tauto.
  assumption.
  tauto.
  }
  {
  simpl.
  intros.
  eapply IHc1.
  assumption.
  assumption.
  apply SAT.
  intros.
  eapply IHc2.
  assumption.
  assumption.
  simpl in *.
  apply SAT0.
  intros.
  apply IMP.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  specialize SAT with v.

  destruct SAT as (v0,(v1,(NIN,SAT))).
  exists v0, v1.
  split.
  assumption.
  intros.
  apply IMP.
  assumption.
  assumption.
  apply SAT with O';
  try tauto.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(BC1,(BC2,(ghpdefC1C2,(bc12,(opO1O2,(tmp1,tmp2)))))))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v, v0, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2, C1, C2, BC1, BC2, ghpdefC1C2, bc12, opO1O2.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  assumption.
  apply tmp2 with v1 v2 O';
  try tauto.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(v2,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(BC1,(BC2,(ghpdefC1C2,(bc12,(opO1O2,(tmp1,tmp2)))))))))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v, v0, v1, v2, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2, C1, C2, BC1, BC2, ghpdefC1C2, bc12, opO1O2.
  split.
  destruct tmp1 as (EQ,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp4,tmp5))))))))))))))))).
  split.
  assumption.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, BC3, BC4, ghpdefC3C4, bc34, opO3O4.
  split.
  assumption.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  assumption.
  apply tmp2 with O';
  try tauto.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(BC1,(BC2,(ghpdefC1C2,(bc12,(opO1O2,(tmp1,tmp2)))))))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  destruct tmp1 as (EQ,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp4,tmp5))))))))))))))))).
  exists v,v0.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, BC1, BC2, ghpdefC1C2, bc12, opO1O2.
  split.
  split.
  assumption.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, BC3, BC4, ghpdefC3C4, bc34, opO3O4.
  split.
  assumption.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  assumption.
  apply tmp2 with v1 v2 O';
  try tauto.
  assumption.
  }
  {
  simpl.
  intros.
  specialize SAT with v.


  destruct SAT as (v0,(v1,(v2,(v3,(v4,(v5,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(BC1,(BC2,(ghpdefC1C2,(bc12,(opO1O2,(tmp1,tmp2)))))))))))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v0,v1,v2, v3, v4, v5, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, BC1, BC2, ghpdefC1C2, bc12, opO1O2.
  split.
  assumption.
  split.
  intros.
  apply IMP; repeat php_.
  apply tmp2 with O'; repeat php_.
  tauto.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(BC1,(BC2,(ghpdefC1C2,(bc12,(opO1O2,(tmp1,tmp2))))))))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v,v0,v1,p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, BC1, BC2, ghpdefC1C2, bc12, opO1O2.
  split.
  destruct tmp1 as (v3,(v4,(Lx,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp4,tmp5))))))))))))))))))).
  exists v3,v4.
  split.
  assumption.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, BC3, BC4, ghpdefC3C4, bc34, opO3O4.
  split.
  assumption.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  assumption.
  apply tmp2 with v2 v3 O';
  tauto.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(v2,(v3,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc1c2,(opO1O2,(tmp1,tmp2)))))))))))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v, v0, v1, v2, v3.
  split.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc1c2, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, p3p4))))))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  exists.
  assumption.
  exists.
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp5,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56, opO5O6.
  split.
  assumption.
  split.
  destruct tmp6 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(tmp7,(tmp8,p7p8))))))))))))))))).
  exists p7, p8, phpdefp7p8, bp7, bp8, bp78, O7, O8, C7, C8, ghpdefC7C8, BC7, BC8, bc78, opO7O8.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  assumption.
  apply tmp8 with O';
  try tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(v2,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc1c2,(opO1O2,(tmp1,(tmp2,tmp3))))))))))))))))))))).
  exists v, v0, v1, v2, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc1c2, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, p3p4))))))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  split.
  assumption.
  split.
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp5,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56, opO5O6.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  assumption.
  apply tmp6 with O'; try assumption.
  tauto.
  tauto.
  tauto.
  }
  {
  simpl.
  intros.
  destruct SAT as (v0,(v1,(v2,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,tmp2)))))))))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v0, v1, v2.
  split.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  assumption.
  apply tmp2 with v3 v4 O';
  try tauto.
  tauto.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(v2,(v3,(v4,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,tmp3)))))))))))))))))))))))).
  exists v, v0, v1, v2, v3, v4.
  exists.
  tauto.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, p3p4))))))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  split.
  assumption.
  split.
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp6,(tmp7, p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56, opO5O6.
  split.
  assumption.
  split.
  intros.
  apply IMP;
  try tauto.
  apply tmp7 with O';
  try tauto.
  tauto.
  tauto.
  tauto.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(v2,(v3,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,tmp2)))))))))))))))))))))).
  exists v, v0, v1, v2, v3.
  exists.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (tmp2, tmp3).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, p3p4))))))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  exists.
  assumption.
  split.
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp5,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56, opO5O6.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  assumption.
  apply tmp6 with O'; repeat php_.
  tauto.
  tauto.
  tauto.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(v2,(v3,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,tmp2)))))))))))))))))))))).
  exists v, v0, v1, v2, v3.
  exists.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (tmp2, tmp3).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, p3p4))))))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  exists.
  assumption.
  split.
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp5,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56, opO5O6.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  assumption.
  apply tmp6 with O'; repeat php_.
  tauto.
  tauto.
  tauto.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(v2,(v3,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,tmp2)))))))))))))))))))))).
  exists v, v0, v1, v2, v3.
  exists.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (tmp2, tmp3).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, p3p4))))))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  exists.
  assumption.
  split.
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp5,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56, opO5O6.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  assumption.
  apply tmp6 with O'; repeat php_.
  tauto.
  tauto.
  tauto.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(v2,(v3,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,tmp2)))))))))))))))))))))).
  exists v, v0, v1, v2, v3.
  exists.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (tmp2, tmp3).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, p3p4))))))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  exists.
  assumption.
  split.
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp5,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56, opO5O6.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  assumption.
  apply tmp6 with O'; repeat php_.
  tauto.
  tauto.
  tauto.
  }
  {
  simpl.
  intros.
  apply IMP; try assumption.
  apply SAT with v O'; try assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,tmp3)))))))))))))))))).
  exists v, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split.
  assumption.
  split.
  intros.
  apply IMP; try assumption.
  apply tmp2 with O'; try assumption.
  auto.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,tmp3)))))))))))))))))).
  exists v, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, p3p4))))))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  split.
  assumption.
  split.
  intros.
  apply IMP; try assumption.
  apply tmp5 with O'; try assumption.
  auto.
  auto.
  }
Qed.

(** # <font size="5"><b> Substitution </b></font> # *)

Lemma sat_pre_subs1:
  forall c se a p o d x z invs (BP: boundph p) (BG: boundgh d)
        (SAT: sat p o d (weakest_pre (subs c (subse x z)) a se invs)),
    sat p o d (weakest_pre c a (fun e : exp => se (subse x z e)) invs).
Proof.
  induction c;
  intros;
  try assumption.
  {
  simpl in *.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,tmp2)))))))))))))))))).
  destruct tmp1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,tmp1))))))))))))))).
  destruct tmp1 as (tmp1, tmp3).
  destruct tmp2 as (tmp2,tmp4).
  exists v, v0, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2, C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  split.
  assumption.
  assumption.
  split.
  intros.
  apply IHc.
  assumption.
  assumption.
  apply tmp2 with (O':=O');
  try tauto.
  assumption.
  }
  {
  simpl in *.
  apply IHc1.
  assumption.
  assumption.
  apply sat_weak_imp with (a := fun z0 : Z => 
    weakest_pre (subs c2 (subse x0 z)) a (fun e : exp => subse x z0 (se e)) invs).
  assumption.
  assumption.
  assumption.
  intros.
  apply IHc2 in SAT0.
  assumption.
  assumption.
  assumption.
  }
Qed.

Lemma sat_pre_subs2:
  forall c se a p o d x z invs (BP: boundph p) (BG: boundgh d)
        (SAT: sat p o d (weakest_pre c a (fun e : exp => se (subse x z e)) invs)),
    sat p o d (weakest_pre (subs c (subse x z)) a se invs).
Proof.
  induction c;
  intros;
  try assumption.
  {
  simpl in *.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,tmp2)))))))))))))))))).
  destruct tmp1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,tmp1))))))))))))))).
  destruct tmp1 as (tmp1, tmp3).
  destruct tmp2 as (tmp2,tmp4).
  exists v, v0, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2, C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  split.
  assumption.
  assumption.
  split.
  intros.
  apply IHc.
  assumption.
  assumption.
  apply tmp2 with (O':=O');
  try tauto.
  assumption.
  }
  {
  simpl in *.
  apply IHc1.
  assumption.
  assumption.
  apply sat_weak_imp with (a:= fun z0 : Z => weakest_pre c2 a
    (fun e : exp => subse x z0 (se (subse x0 z e))) invs).
  assumption.
  assumption.
  simpl.
  assumption.
  intros.
  apply IHc2.
  assumption.
  assumption.
  assumption.
  }
Qed.

Lemma sat_pre_subs3:
  forall c p o C a se1 se2 invs (bp: boundph p) (bg: boundgh C)
         (SAT: sat p o C (weakest_pre (subs c se1) a se2 invs)),
    sat p o C (weakest_pre c a (fun e => se2 (se1 e)) invs).
Proof.
  induction c;
  intros;
  try assumption;
  try apply SAT.
  {
  simpl in *.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(sat1,(sat2,(p1p2,C1C2)))))))))))))))))))).
  exists v, v0, p1, p2, phpdefp1p2, bp1, bp2, bp12, o1, o2, C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  exists.
  assumption.
  exists.
  intros.
  apply IHc.
  assumption.
  assumption.
  apply sat2 with O';
  try tauto.
  tauto.
  }
  {
  apply IHc1.
  assumption.
  assumption.
  eapply sat_weak_imp.
  assumption.
  assumption.
  apply SAT.
  simpl.
  intros.
  apply IHc2 in SAT0.
  assumption.
  assumption.
  assumption.
  }
Qed.

Lemma sat_pre_subs:
  forall c se a p o d x z invs (BP: boundph p) (BG: boundgh d),
    sat p o d (weakest_pre (subs c (subse x z)) a se invs) <->
    sat p o d (weakest_pre c a (fun e : exp => se (subse x z e)) invs).
Proof.
  split.
  apply sat_pre_subs1.
  assumption.
  assumption.
  apply sat_pre_subs2.
  assumption.
  assumption.
Qed.

(** # <font size="5"><b> Weakening Safe Obligations </b></font> # *)

Lemma safe_obs_wt_weak:
  forall v wt ot wt'
         (LE: le wt' wt)
         (SAFE_OBS: safe_obs v wt ot = true),
  safe_obs v wt' ot = true.
Proof.
  unfold safe_obs.
  intros.
  apply Coq.Bool.Bool.andb_true_iff in SAFE_OBS.
  destruct SAFE_OBS as (ONE,SAFE_OBS).
  apply Coq.Bool.Bool.andb_true_iff in SAFE_OBS.
  destruct SAFE_OBS as (SPR,OWN).
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  apply Coq.Bool.Bool.orb_true_iff in ONE.
  apply Coq.Bool.Bool.orb_true_iff.
  destruct ONE as [ONE|ONE].
  left.
  apply Nat.eqb_eq in ONE.
  apply Nat.eqb_eq.
  omega.
  right.
  assumption.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  apply Coq.Bool.Bool.orb_true_iff in SPR.
  apply Coq.Bool.Bool.orb_true_iff.
  destruct SPR as [SPR|SPR].
  left.
  assumption.
  right.
  apply Coq.Bool.Bool.orb_true_iff in SPR.
  apply Coq.Bool.Bool.orb_true_iff.
  destruct SPR as [SPR|SPR].
  left.
  apply Nat.eqb_eq in SPR.
  apply Nat.eqb_eq.
  omega.
  right.
  apply Nat.ltb_lt in SPR.
  apply Nat.ltb_lt.
  omega.
  apply Coq.Bool.Bool.orb_true_iff in OWN.
  apply Coq.Bool.Bool.orb_true_iff.
  destruct OWN as [OWN|OWN].
  left.
  assumption.
  right.
  apply Nat.leb_le in OWN.
  apply Nat.leb_le.
  omega.
Qed.

Lemma safe_obs_ot_weak:
  forall v wt ot ot'
         (LE: le ot ot')
         (SAFE_OBS: safe_obs v wt ot = true),
  safe_obs v wt ot' = true.
Proof.
  unfold safe_obs.
  intros.
  apply Coq.Bool.Bool.andb_true_iff in SAFE_OBS.
  destruct SAFE_OBS as (ONE,SAFE_OBS).
  apply Coq.Bool.Bool.andb_true_iff in SAFE_OBS.
  destruct SAFE_OBS as (SPR,OWN).
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  apply Coq.Bool.Bool.orb_true_iff in ONE.
  apply Coq.Bool.Bool.orb_true_iff.
  destruct ONE as [ONE|ONE].
  left.
  assumption.
  apply Nat.ltb_lt in ONE.
  right.
  apply Nat.ltb_lt.
  omega.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  apply Coq.Bool.Bool.orb_true_iff in SPR.
  apply Coq.Bool.Bool.orb_true_iff.
  destruct SPR as [SPR|SPR].
  left.
  assumption.
  right.
  apply Coq.Bool.Bool.orb_true_iff in SPR.
  apply Coq.Bool.Bool.orb_true_iff.
  destruct SPR as [SPR|SPR].
  left.
  apply Nat.eqb_eq in SPR.
  apply Nat.eqb_eq.
  omega.
  right.
  apply Nat.ltb_lt in SPR.
  apply Nat.ltb_lt.
  omega.
  apply Coq.Bool.Bool.orb_true_iff in OWN.
  apply Coq.Bool.Bool.orb_true_iff.
  destruct OWN as [OWN|OWN].
  left.
  assumption.
  right.
  apply Nat.leb_le in OWN.
  apply Nat.leb_le.
  omega.
Qed.

(** # <font size="5"><b> sat_wp </b></font> # *)

Lemma sat_notify:
forall p O C v tx invs
      (SAT: sat p (Some O) C (weakest_pre_ct (Notify v, tx) invs)),
  exists p1 pm C1 Cm wt ot lv ll
         (bp1: boundph p1)
         (bpm: boundph pm)
         (bp1pm: boundph (phplus p1 pm))
         (phpdefp1pm: phplusdef p1 pm)
         (p1pm: p = phplus p1 pm)
         (ghpdefC1Cm: ghplusdef C1 Cm)
         (C1Cm: C = ghplus C1 Cm)
         (EQv: Aof lv = ([[v]]))
         (EQl: Aof ll = Lof lv)
         (P1l: p1 ll = Some (Locked wt ot)) 
         (P1l: p1 lv = Some Cond)
         (SATv: sat pm None Cm (subsas (snd (Mof lv)) (invs (fst (Mof lv)) empb empb))),
    (lt 0 (wt ([[v]])) -> sat (upd location_eq_dec p1 ll (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) (Some O) C1 (weakest_pre_tx tx invs 0)) /\
    (le (wt ([[v]])) 0 -> sat (upd location_eq_dec p ll (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) (Some O) C (weakest_pre_tx tx invs 0)).
Proof.
  simpl.
  intros.
  destruct SAT as (v0,(v1,(v2,(v3,(v4,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(satp1v3,(sat1,(p1p2,C1C2)))))))))))))))))))))))).
  destruct sat1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(p3v2,(tmp1,(p3p4,C3C4)))))))))))))))))).
  destruct tmp1 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp6,(tmp7, (p5p6,C5C6)))))))))))))))))).
  destruct tmp7 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(tmp7,(tmp8, (p7p8,C7C8)))))))))))))))))).

  subst.

  assert (o1n: Permutation (map evall v0) O /\ o1 = None /\ O8 = None).
  {
  inversion tmp7.
  rewrite <- H1 in opO7O8.
  inversion opO7O8.
  rewrite <- H4 in opO5O6.
  inversion opO5O6.
  rewrite <- H5 in opO3O4.
  inversion opO3O4.
  rewrite <- H8 in opO1O2.
  inversion opO1O2.
  split.
  apply Permutation_trans with o'.
  assumption.
  apply Permutation_trans with o'0.
  assumption.
  apply Permutation_trans with o'1.
  assumption.
  apply Permutation_trans with o'2.
  assumption.
  assumption.
  split;
  reflexivity.
  }
  destruct o1n as (PERM,(o1n,o8n)).
  rewrite o1n, o8n in *.

  assert (phpdefp13p156: phplusdef p1 p3 /\ phplusdef p1 (phplus p5 (phplus p7 p8))). repeat php_.
  assert (phpdefp15p16: phplusdef p1 p5 /\ phplusdef p1 (phplus p7 p8)). repeat php_.
  assert (phpdefp17p18: phplusdef p1 p7 /\ phplusdef p1 p8). repeat php_.
  assert (phpdefp35p36: phplusdef p3 p5 /\ phplusdef p3 (phplus p7 p8)). repeat php_.
  assert (phpdefp37p38: phplusdef p3 p7 /\ phplusdef p3 p8). repeat php_.
  assert (phpdefp57p58: phplusdef p5 p7 /\ phplusdef p5 p8). repeat php_.

  assert (ghpdefp13p156: ghplusdef C1 C3 /\ ghplusdef C1 (ghplus C5 (ghplus C7 C8))). repeat php_.
  assert (ghpdefp15p16: ghplusdef C1 C5 /\ ghplusdef C1 (ghplus C7 C8)). repeat php_.
  assert (ghpdefp17p18: ghplusdef C1 C7 /\ ghplusdef C1 C8). repeat php_.
  assert (ghpdefp35p36: ghplusdef C3 C5 /\ ghplusdef C3 (ghplus C7 C8)). repeat php_.
  assert (ghpdefp37p38: ghplusdef C3 C7 /\ ghplusdef C3 C8). repeat php_.
  assert (ghpdefp57p58: ghplusdef C5 C7 /\ ghplusdef C5 C8). repeat php_.

  apply Coq.Bool.Bool.andb_true_iff in EQ.
  destruct EQ as (EQ1,EQ2).
  apply Z.eqb_eq in EQ1.
  apply Z.eqb_eq in EQ2.
  unfold id in *.

  exists (phplus p3 (phplus p5 (phplus p7 p8))), p1.
  exists (ghplus C3 (ghplus C5 (ghplus C7 C8))), C1.
  exists v1, v2.
  exists (evall v4), (evall v3).
  exists. assumption.
  exists. assumption.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply phplus_comm; repeat php_.
  exists. repeat php_.
  exists. apply ghplus_comm; repeat php_.
  exists. symmetry. assumption.
  exists. symmetry. assumption.
  exists.
  apply phplus_locked'; repeat php_.
  apply phplus_locked; repeat php_.
  exists.
  apply phplus_Cond; repeat php_.
  exists. assumption.

  assert (eqh: phplus p3 (phplus p5 (phplus p7 p8)) = phplus p5 (phplus p7 (phplus p8 p3))).
  {
  rewrite phplus_comm; repeat php_.
  }

  assert (phpdefup5p6: phplusdef
    (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p7).
  {
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  assumption.
  }

  assert (phpdefup7p8: phplusdef
    (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p8).
  {
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  assumption.
  }

  assert (phpdefup5p3: phplusdef
    (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p3).
  {
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  assumption.
  }

  assert (phpdefp8up5: phplusdef p8
    (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2)))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  assumption.
  }

  assert (phpdefp3up5: phplusdef p3
    (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2)))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  assumption.
  }

  assert (phpdefp8up57: phplusdef p8
    (phplus (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p7)).
  {
  apply phpdef_pair; repeat php_.
  }

  assert (phpdefp3up5p7: phplusdef p3 (phplus
    (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p7)).
  {
  apply phpdef_pair; repeat php_.
  }

  assert (EQH: upd location_eq_dec (phplus p3 (phplus p5 (phplus p7 p8))) (evall v3)
   (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2)) =
   phplus p8 (phplus p3 (phplus (upd location_eq_dec p5 (evall v3)
   (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p7))).
  {
  rewrite eqh.
  rewrite <- phplus_upd.
  symmetry.
  rewrite <- phplus_assoc.
  rewrite phplus_comm; repeat php_.
  php_.
  assumption.
  assumption.
  unfold not.
  intros.

  destruct H as (v0',(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
  }

  assert (EQC: ghplus C3 (ghplus C5 (ghplus C7 C8)) = ghplus C8 (ghplus C3 (ghplus C5 C7))).
  {
  symmetry.
  rewrite ghplus_comm; repeat php_.
  }

  assert (bp3p78: boundph (phplus p3 (phplus p7 p8))).
  {
  apply boundph_mon with p5; repeat php_.
  rewrite phplus_assoc; repeat php_.
  replace (phplus (phplus p7 p8) p5) with (phplus p5 (phplus p7 p8)); repeat php_.
  }

  assert (bp73: boundph (phplus p7 p3)).
  {
  apply boundph_mon with p8; repeat php_.
  replace (phplus (phplus p7 p3) p8) with (phplus p3 (phplus p7 p8)); repeat php_.
  rewrite phplus_comm; repeat php_.
  }

  assert (b5p73: boundph (phplus p5 (phplus p7 p3))).
  {
  apply boundph_mon with p8; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  replace (phplus (phplus p5 p7) p3) with (phplus p3 (phplus p5 p7)); repeat php_.
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_assoc; repeat php_.
  }

  assert (bp3up57: boundph (phplus p3 (phplus (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p7))).
  {
  rewrite phplus_comm; repeat php_.
  rewrite phplus_assoc; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v4',(v5,(CO,rest))).
  inversion CO.
  }

  assert (bp7p83: boundph (phplus p7 (phplus p8 p3))).
  {
  rewrite <- phplus_assoc; repeat php_.
  }

  assert (bp5p7p83: boundph (phplus p5 (phplus p7 (phplus p8 p3)))).
  {
  rewrite <- phplus_assoc; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  rewrite phplus_comm; repeat php_.
  rewrite phplus_assoc; repeat php_.
  }

  assert (bp8p3up57: boundph (phplus p8 (phplus p3 (phplus
    (upd location_eq_dec p5 (evall v3) (Some
    (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p7)))).
  {
  rewrite phplus_comm; repeat php_.
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_comm; repeat php_.
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_assoc; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v4',(v5,(CO,rest))).
  inversion CO.
  }

  assert (bup52: boundph (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2)))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bup57: boundph (phplus (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p7)).
  {
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v5,(v6,(CO,rest))).
  inversion CO.
  }

  assert (bc3c57: boundgh (ghplus C3 (ghplus C5 C7))).
  {
  apply boundgh_mon with C8; repeat php_.
  rewrite ghplus_assoc; repeat php_.
  rewrite ghplus_assoc; repeat php_.
  }

  assert (bc8c3c57: boundgh (ghplus C8 (ghplus C3 (ghplus C5 C7)))).
  {
  rewrite ghplus_comm; repeat php_.
  rewrite ghplus_assoc; repeat php_.
  rewrite ghplus_assoc; repeat php_.
  }

  assert (op1: oplus None (Some O) (Some O)).
  {
  apply sn_op.
  apply Permutation_refl.
  }

  split.
  {
  intros.
  rewrite EQH.
  rewrite EQC.
  apply tmp8 with (Some O); repeat php_.

  exists p3, (phplus (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p7).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, (Some O).
  exists C3, (ghplus C5 C7).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split.
  {
  exists (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))), p7.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, (Some O).
  exists C5, C7.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  unfold upd.
  destruct (location_eq_dec (evall v3) (evall v3)).
  rewrite EQ2.
  reflexivity.
  contradiction.
  split.
  {
  exists p7, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, (Some O).
  exists C7, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split.
  right.
  apply Nat.ltb_lt.
  rewrite <- EQ2.
  assumption.
  split.
  apply fs_op.
  assumption.
  split; repeat php_.
  }
  split; reflexivity.
  }
  split; reflexivity.
  }

  intros.

  assert (eqh2: phplus p1 (phplus p3 (phplus p5 (phplus p7 p8))) =
    phplus p5 (phplus p1 (phplus p7 (phplus p8 p3)))).
  {
  symmetry.
  rewrite phplus_comm; repeat php_.
  rewrite phplus_assoc; repeat php_.
  symmetry.
  rewrite <- phplus_assoc. 
  rewrite phplus_comm; repeat php_.
  repeat php_.
  repeat php_.
  repeat php_.
  }

  assert (phpdefup5p1: phplusdef (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p1).
  {
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  assumption.
  }

  assert (phpdefp8up5p17: phplusdef p8 (phplus (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) (phplus p1 p7))).
  {
  rewrite phplus_comm; repeat php_.
  }

  assert (phpdefp3up5p17: phplusdef p3 (phplus (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2)))(phplus p1 p7))).
  {
  rewrite phplus_comm; repeat php_.
  }

  assert (EQH1: upd location_eq_dec (phplus p1 (phplus p3 (phplus p5 (phplus p7 p8))))
    (evall v3) (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2)) =
    phplus p8 (phplus p3 (phplus (upd location_eq_dec p5
    (evall v3) (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) (phplus p1 p7)))).
  {
  rewrite eqh2.
  rewrite <- phplus_upd.
  symmetry.
  rewrite <- phplus_assoc.
  rewrite phplus_comm; repeat php_.
  php_.
  assumption.
  assumption.
  unfold not.
  intros.
  destruct H0 as (v0',(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H0.
  intros.
  inversion H0.
  }

  assert (EQC1: ghplus C1 (ghplus C3 (ghplus C5 (ghplus C7 C8))) =
    ghplus C8 (ghplus C3 (ghplus C5 (ghplus C1 C7)))).
  {
  rewrite ghplus_comm; repeat php_.
  symmetry.
  rewrite ghplus_comm; repeat php_.
  }

  rewrite EQH1.
  rewrite EQC1.

  assert (bp17p3: boundph (phplus (phplus p1 p7) p3)).
  {
  rewrite phplus_assoc; repeat php_.
  apply boundph_mon with p5; repeat php_.
  rewrite phplus_assoc; repeat php_.
  apply boundph_mon with p8; repeat php_.
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_assoc; repeat php_.
  replace (phplus (phplus p7 p3) (phplus p5 p8)) with 
    (phplus p3 (phplus p5 (phplus p7 p8))); repeat php_.
  symmetry.
  rewrite phplus_comm; repeat php_.
  }

  assert (bp5p17p3: boundph (phplus p5 (phplus (phplus p1 p7) p3))).
  {
  apply boundph_mon with p8; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  replace (phplus p5 p1) with (phplus p1 p5).
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_assoc; repeat php_.
  replace (phplus p5 (phplus p7 (phplus p3 p8))) with 
    (phplus p3 (phplus p5 (phplus p7 p8))); repeat php_.
  rewrite phplus_comm; repeat php_.
  php_.
  }

  assert (bp3up5p17: boundph (phplus p3 (phplus (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) (phplus p1 p7)))).
  {
  rewrite phplus_comm; repeat php_.
  rewrite phplus_assoc; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v5,(v6,(CO,rest))).
  inversion CO.
  }

  assert (bp17p83: boundph (phplus (phplus p1 p7) (phplus p8 p3))).
  {
  apply boundph_mon with p5; repeat php_.
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_assoc; repeat php_.
  replace (phplus p7 (phplus (phplus p8 p3) p5)) with
    (phplus p3 (phplus p5 (phplus p7 p8))); repeat php_.
  rewrite phplus_comm; repeat php_.
  symmetry.
  rewrite <- phplus_assoc; repeat php_.
  }

  assert (bp5p17p83: boundph (phplus p5 (phplus (phplus p1 p7) (phplus p8 p3)))).
  {
  rewrite phplus_comm; repeat php_.
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_assoc; repeat php_.
  replace (phplus p7 (phplus p8 (phplus p3 p5))) with
    (phplus p3 (phplus p5 (phplus p7 p8))); repeat php_.
  rewrite <- phplus_assoc. 
  symmetry.
  rewrite <- phplus_assoc. 
  apply phplus_comm; repeat php_.
  repeat php_.
  repeat php_.
  repeat php_.
  repeat php_.
  repeat php_.
  repeat php_.
  }

  assert (bp8p3up5p17: boundph (phplus p8 (phplus p3 (phplus (upd location_eq_dec p5 (evall v3)
   (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) (phplus p1 p7))))).
  {
  rewrite phplus_comm; repeat php_.
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_comm; repeat php_.
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_assoc; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v5,(v6,(CO,rest))).
  inversion CO.
  }

  assert (bc3c5c17: boundgh (ghplus C3 (ghplus C5 (ghplus C1 C7)))).
  {
  apply boundgh_mon with C8; repeat php_.
  rewrite ghplus_comm; repeat php_.
  rewrite <- EQC1.
  assumption.
  }

  assert (bc8c3c5c17: boundgh (ghplus C8 (ghplus C3 (ghplus C5 (ghplus C1 C7))))).
  {
  rewrite <- EQC1.
  assumption.
  }

  assert (bp17: boundph (phplus p1 p7)).
  {
  apply boundph_mon with p3; repeat php_.
  }

  assert (bup517: boundph (phplus (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2)))(phplus p1 p7))).
  {
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v5',(v6,(CO,rest))).
  inversion CO.
  }

  assert (bc17: boundgh (ghplus C1 C7)).
  {
  apply boundgh_mon with (ghplus C5 (ghplus C3 C8)).
  rewrite ghplus_assoc; repeat php_.
  replace (ghplus C7 (ghplus C5 (ghplus C3 C8))) with
    (ghplus C3 (ghplus C5 (ghplus C7 C8))); repeat php_.
  rewrite ghplus_comm; repeat php_.
  symmetry.
  rewrite ghplus_comm; repeat php_.
  }

  apply tmp8 with (Some O); repeat php_.

  exists p3, (phplus (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) (phplus p1 p7)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, (Some O).
  exists C3, (ghplus C5 (ghplus C1 C7)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split.
  {
  exists (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))).
  exists (phplus p1 p7).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, (Some O).
  exists C5, (ghplus C1 C7).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  apply sn_op.
  apply Permutation_refl.
  split.
  unfold upd.
  destruct (location_eq_dec (evall v3) (evall v3)).
  rewrite EQ2.
  reflexivity.
  contradiction.
  split.
  {
  exists p1, p7.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, (Some O).
  exists C1, C7.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  left.
  assumption.
  split.
  apply fs_op.
  assumption.
  split; reflexivity.
  }
  split; reflexivity.
  }
  split; reflexivity.
Qed.

Lemma sat_notifyAll:
forall p O C v tx invs
      (SAT: sat p (Some O) C (weakest_pre_ct (NotifyAll v, tx) invs)),
  exists wt ot lv ll
         (EQv: Aof lv = ([[v]]))
         (EQl: Aof ll = Lof lv)
         (P1l: p ll = Some (Locked wt ot)) 
         (P1l: p lv = Some Cond)
         (EMP: subsas (snd (Mof lv)) (invs (fst (Mof lv)) empb empb) = Aemp),
    sat (upd location_eq_dec p ll (Some (Locked (upd Z.eq_dec wt ([[v]]) 0%nat) ot))) (Some O) C (weakest_pre_tx tx invs 0).
Proof.
  simpl.
  intros.
  destruct SAT as (v1,(v2,(v3,(v4,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4)))))))))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp6,(tmp7, (p5p6,C5C6)))))))))))))))))).

  destruct tmp1 as (eqls,EQ1).
  apply Coq.Bool.Bool.andb_true_iff in eqls.
  destruct eqls as (EQ2,EQ3).
  apply Z.eqb_eq in EQ2.
  apply Z.eqb_eq in EQ3.
  unfold id in *.
  subst.
  exists v1, v2, (evall v4), (evall v3).
  exists. symmetry. assumption.
  exists. symmetry. assumption.
  exists.
  apply phplus_locked'; repeat php_.
  apply phplus_locked'; repeat php_.
  apply phplus_locked; repeat php_.
  exists.
  apply phplus_Cond'; repeat php_.
  apply phplus_Cond; repeat php_.
  exists EQ1.

  assert (phpdefp13p1578: phplusdef p1 p3 /\ phplusdef p1 (phplus p5 p6)). repeat php_.
  assert (phpdefp17p18: phplusdef p1 p5 /\ phplusdef p1 p6). repeat php_.
  assert (phpdefp35p378: phplusdef p3 p5 /\ phplusdef p3 p6). repeat php_.

  assert (ghpdefp15p178: ghplusdef c1 C3 /\ ghplusdef c1 (ghplus C5 C6)). repeat php_.
  assert (ghpdefp17p18: ghplusdef c1 C5 /\ ghplusdef c1 C6). repeat php_.
  assert (ghpdefp35p378: ghplusdef C3 C5 /\ ghplusdef C3 C6). repeat php_.

  assert (eqh: phplus p1 (phplus p3 (phplus p5 p6)) =
    phplus (phplus p1 (phplus p3 p5)) p6). rewrite phplus_assoc; repeat php_.

  assert (phpdefp8r: phplusdef p6
    (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2)))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  apply phplus_locked'; repeat php_.
  apply phplus_locked'; repeat php_.
  }

  assert (EQH: upd location_eq_dec (phplus p1 (phplus p3 (phplus p5 p6)))
    (evall v3) (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2)) =
    phplus p6 (upd location_eq_dec (phplus p1 (phplus p3 p5))
    (evall v3) (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2)))).
  {
  rewrite eqh.
  symmetry.
  rewrite phplus_comm; repeat php_.
  apply phplus_upd; repeat php_.
  unfold not.
  intros.
  inversion H as (v0',(f',(v'',(f'',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
  }

  assert (EQC: ghplus c1 (ghplus C3 (ghplus C5 C6)) =
    ghplus C6 (ghplus C3 (ghplus C5 c1))).
  {
  rewrite ghplus_comm; repeat php_.
  symmetry.
  rewrite ghplus_comm; repeat php_.
  }

  rewrite EQH.
  rewrite EQC.

  assert (bp1234: boundph (phplus p1 (phplus p3 p5))).
  {
  apply boundph_mon with p6; repeat php_.
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_assoc; repeat php_.
  }

  assert (bupss: boundph (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
   (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2)))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert(bp8u: boundph (phplus p6
   (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
   (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2))))).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_assoc; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v40',(v5',(CO,rest))).
  inversion CO.
  }

  assert (ghc3571: boundgh (ghplus C3 (ghplus C5 c1))).
  {
  apply boundgh_mon with C6; repeat php_.
  rewrite ghplus_comm; repeat php_.
  rewrite <- EQC.
  assumption.
  }

  assert (ghc83571: boundgh (ghplus C6 (ghplus C3 (ghplus C5 c1)))).
  {
  rewrite <- EQC.
  assumption.
  }

  assert (exo: exists O', oplus O6 O' (Some O)).
  {
  destruct O6.
  inversion opO5O6.
  rewrite <- H0 in opO3O4.
  inversion opO3O4.
  rewrite <- H3 in opo1o2.
  inversion opo1o2.
  exists None.
  apply fs_op.
  apply Permutation_trans with o'.
  assumption.
  apply Permutation_trans with o'0.
  assumption.
  assumption.
  exists (Some O).
  apply sn_op.
  apply Permutation_refl.
  }
  destruct exo as (O',op').

  apply tmp7 with O'; repeat php_.

  assert (phpdefp1up5: phplusdef p1
    (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2)))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  assumption.
  }

  assert (phpdefp3up5: phplusdef p3
    (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2)))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  assumption.
  }

  assert (phpdefp13up5: phplusdef (phplus p1 p3)
    (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2)))).
  {
  apply phpdef_pair'; repeat php_.
  }

  assert (bup5: boundph (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2)))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bp513: boundph (phplus p5 (phplus p1 p3))).
  {
  apply boundph_mon with p6; repeat php_.
  replace (phplus p5 (phplus p1 p3)) with (phplus p1 (phplus p3 p5)); repeat php_.
  rewrite phplus_assoc; repeat php_.
  rewrite phplus_assoc; repeat php_.
  symmetry.
  rewrite phplus_comm; repeat php_.
  }

  assert (bp13up5: boundph (phplus (phplus p1 p3)
    (upd location_eq_dec p5 (evall v3) (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2))))).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v5,(v6,(CO,rest))).
  inversion CO.
  }

  exists (phplus p1 p3), (upd location_eq_dec p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, O'.
  exists C3, (ghplus C5 c1).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  destruct O'.
  apply sn_op.
  apply Permutation_refl.
  apply None_op.
  split.
  apply phplus_Cond'; repeat php_.
  split.
  unfold upd.
  destruct (location_eq_dec (evall v3) (evall v3)).
  rewrite EQ3.
  reflexivity.
  contradiction.
  split.
  symmetry.
  replace (phplus p1 (phplus p3 p5)) with
    (phplus p5 (phplus p1 p3)).
  rewrite <- phplus_upd; repeat php_.
  unfold not.
  intros.
  destruct H as (v',(f',(v'',(f'',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
  rewrite phplus_comm; repeat php_.
  reflexivity.
Qed.

Lemma sat_acquire0:
  forall p O C l tx invs
        (SAT: sat p (Some O) C (weakest_pre_ct (Acquire l, tx) invs)),
  exists ll
         (EQL: Aof ll = ([[l]]))
         (Pl: p ll = Some Lock \/ exists Wt Ot, p ll = Some (Locked Wt Ot))
         (PRCl: prcl ll O = true),
    sat p (Some O) C (weakest_pre_ct (Waiting4lock l, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v0,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))).
  destruct tmp1 as (eqls,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4))))))))))))))))))).
  subst.
  assert (phpdefp32p42: phplusdef p3 p2 /\ phplusdef p4 p2). repeat php_.
  assert (ghpdefp32p42: ghplusdef C3 c2 /\ ghplusdef C4 c2). repeat php_.
  apply Coq.Bool.Bool.andb_true_iff in eqls.
  destruct eqls as (EQ1,EQ2).
  apply Z.eqb_eq in EQ1.
  unfold id in *.

  assert (PERM: Permutation O (map evall v0) /\ o2 = None).
  {
  inversion tmp5.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  rewrite <- H2 in opo1o2.
  inversion opo1o2.
  split.
  apply Permutation_trans with o'0.
  apply Permutation_sym.
  assumption.
  apply Permutation_trans with o'.
  apply Permutation_sym.
  assumption.
  apply Permutation_sym.
  assumption.
  reflexivity.
  }
  destruct PERM as (PERM,o2n).
  rewrite o2n in *.
  exists (evall v1).
  exists. symmetry. assumption.
  exists.
  apply phplus_lock.
  apply phplus_lock.
  assumption.
  exists.
  apply prcl_perm with (map evall v0).
  assumption.
  assumption.
  exists v0, v1.
  exists (phplus p3 p4), p2.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some O), None.
  exists (ghplus C3 C4), c2.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists.
  apply fs_op.
  apply Permutation_refl.
  split.
  split.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  apply Z.eqb_eq.
  assumption.
  assumption.
  exists p3, p4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists None, (Some (map evall v0)), C3, C4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. apply sn_op. apply Permutation_sym. assumption.
  exists. assumption.
  exists. apply fs_op. apply Permutation_refl.
  exists; reflexivity.
  split.
  intros.
  apply tmp2 with v v2 O'; repeat php_.
  split; reflexivity.
Qed.

Lemma sat_acquire:
  forall p O C l tx invs
        (SAT: sat p (Some O) C (weakest_pre_ct (Acquire l, tx) invs)),
  exists ll
         (EQL: Aof ll = ([[l]]))
         (Pl: p ll = Some Lock \/ exists Wt Ot, p ll = Some (Locked Wt Ot))
         (PRCl: prcl ll O = true),
    forall p1 C1 wt ot 
          (bp: boundph p1)
          (bp1p: boundph (phplus p1 p))
          (bc: boundgh C1)
          (bc1c: boundgh (ghplus C1 C))
          (phpdefp1p: phplusdef p1 p)
          (ghpdefc1p: ghplusdef C1 C)
          (p1l : p1 ll = Some Lock \/ p1 ll = None)
          (pl : p ll = Some Lock \/ p ll = None)
          (SAT1: sat p1 None C1 (subsas (snd (Iof ll)) (invs (fst (Iof ll)) wt ot))),
      sat (phplus (upd location_eq_dec p ll (Some (Locked wt ot))) p1) (Some (ll :: O)) (ghplus C C1) (weakest_pre_ct (tt, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))).
  destruct tmp1 as (eqls,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4))))))))))))))))))).
  subst.

  assert (phpdefp32p42: phplusdef p3 p2 /\ phplusdef p4 p2). repeat php_.
  assert (ghpdefp32p42: ghplusdef C3 c2 /\ ghplusdef C4 c2). repeat php_.

  apply Coq.Bool.Bool.andb_true_iff in eqls.
  destruct eqls as (EQ1,EQ2).
  apply Z.eqb_eq in EQ1.
  unfold id in *.

  assert (PERM: Permutation O (map evall v) /\ o2 = None).
  {
  inversion tmp5.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  rewrite <- H2 in opo1o2.
  inversion opo1o2.
  split.
  apply Permutation_trans with o'0.
  apply Permutation_sym.
  assumption.
  apply Permutation_trans with o'.
  apply Permutation_sym.
  assumption.
  apply Permutation_sym.
  assumption.
  reflexivity.
  }
  destruct PERM as (PERM,o2n).
  rewrite o2n in *.

  exists (evall v0).
  exists. rewrite EQ1. reflexivity.
  exists.
  apply phplus_lock.
  apply phplus_lock.
  assumption.
  exists.
  apply prcl_perm with (map evall v).
  assumption.
  assumption.
  intros.

  assert (p2v0: p2 (evall v0) = Some Lock \/ p2 (evall v0) = None).
  {
  apply phplus_lock_none with (phplus p3 p4).
  rewrite phplus_comm; repeat php_.
  }

  assert (phpdefp2up34: phplusdef p2 (upd location_eq_dec (phplus p3 p4) (evall v0) (Some (Locked wt ot)))).
  {
  apply phpdef_comm.
  apply phpdef_locked'; repeat php_.
  }

  assert (phpdefp1p34p1p2: phplusdef p1 (phplus p3 p4) /\ phplusdef p1 p2). repeat php_.
  assert (phpdefp13p14: phplusdef p1 p3 /\ phplusdef p1 p4). repeat php_.

  assert (phpdefup34p1: phplusdef (upd location_eq_dec (phplus p3 p4) (evall v0) (Some (Locked wt ot))) p1).
  {
  apply phpdef_locked'; repeat php_.
  }

  assert (eqh: phplus (phplus (phplus p3 p4) p1) p2 = phplus p1 (phplus (phplus p3 p4) p2)).
  {
  symmetry.
  rewrite phplus_comm; repeat php_.
  }

  assert (bp34p1: boundph (phplus (phplus p3 p4) p1)).
  {
  apply boundph_mon with p2; repeat php_.
  rewrite eqh.
  assumption.
  }

  assert (bup34p1: boundph (phplus (upd location_eq_dec (phplus p3 p4) (evall v0) (Some (Locked wt ot))) p1)).
  {
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1',(v2',(CO,rest))).
  inversion CO.
  }

  assert (EQH: phplus (upd location_eq_dec (phplus (phplus p3 p4) p2) (evall v0)
    (Some (Locked wt ot))) p1 = 
    phplus p2 (phplus (upd location_eq_dec (phplus p3 p4) (evall v0)
    (Some (Locked wt ot))) p1)).
  {
  symmetry.
  rewrite <- phplus_assoc; repeat php_.
  rewrite phplus_comm; repeat php_.
  rewrite phplus_upd; repeat php_.
  unfold not.
  intros.
  destruct H as (v3,(f3,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
  }

  assert (bp2up34: boundph (phplus p2 (phplus
    (upd location_eq_dec (phplus p3 p4) (evall v0) (Some (Locked wt ot))) p1))).
  {
  rewrite <- EQH.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1',(v2',(CO,rest))).
  inversion CO.
  }

  assert (ghpdefp1p34p1p2: ghplusdef C1 (ghplus C3 C4) /\ ghplusdef C1 c2). repeat php_.
  assert (ghpdefp13p14: ghplusdef C1 C3 /\ ghplusdef C1 C4). repeat php_.

  assert (EQC: ghplus (ghplus (ghplus C3 C4) c2) C1 =
    ghplus c2 (ghplus (ghplus C3 C4) C1)).
  {
  symmetry.
  rewrite ghplus_comm; repeat php_.
  }

  assert (eqc: ghplus (ghplus (ghplus C3 C4) C1) c2 = ghplus C1 (ghplus (ghplus C3 C4) c2)).
  {
  symmetry.
  rewrite ghplus_comm; repeat php_.
  }

  assert (gbC34C1: boundgh (ghplus (ghplus C3 C4) C1)).
  {
  apply boundgh_mon with c2; repeat php_.
  rewrite eqc.
  assumption.
  }

  assert (bc2c34c1: boundgh (ghplus c2 (ghplus (ghplus C3 C4) C1))).
  {
  rewrite <- EQC.
  rewrite ghplus_comm; repeat php_.
  }

  assert (bu34: boundph (upd location_eq_dec (phplus p3 p4) (evall v0) (Some (Locked wt ot)))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  rewrite EQH.
  rewrite EQC.
  apply tmp2 with wt ot (Some (evall v0 :: O)); repeat php_.
  apply sn_op.
  apply Permutation_refl.
  exists (emp knowledge), (phplus (upd location_eq_dec (phplus p3 p4) (evall v0) (Some (Locked wt ot))) p1).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (evall v0 :: map evall v)), None.
  exists (emp (option nat*nat)), (ghplus (ghplus C3 C4) C1).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  apply fs_op.
  apply perm_skip.
  apply Permutation_sym.
  assumption.
  split.
  apply fs_op.
  apply Permutation_refl.
  split.
  exists (upd location_eq_dec (phplus p3 p4) (evall v0) (Some (Locked wt ot))), p1.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists None, None, (ghplus C3 C4), C1.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  apply None_op.
  split.
  unfold upd.
  destruct (location_eq_dec (evall v0) (evall v0)).
  reflexivity.
  contradiction.
  split. assumption.
  split; reflexivity.
  split; repeat php_.
Qed.

Lemma sat_wait4lock:
  forall p O C l tx invs
        (SAT: sat p (Some O) C (weakest_pre_ct (Waiting4lock l, tx) invs)),
  exists ll
         (EQL: Aof ll = ([[l]]))
         (Pl: p ll = Some Lock \/ exists Wt Ot, p ll = Some (Locked Wt Ot))
         (PRCl: prcl ll O = true),
    forall p1 C1 wt ot 
          (bp: boundph p1)
          (bp1p: boundph (phplus p1 p))
          (bc: boundgh C1)
          (bc1c: boundgh (ghplus C1 C))
          (phpdefp1p: phplusdef p1 p)
          (ghpdefc1p: ghplusdef C1 C)
          (p1l : p1 ll = Some Lock \/ p1 ll = None)
          (pl : p ll = Some Lock \/ p ll = None)
          (SAT1: sat p1 None C1 (subsas (snd (Iof ll)) (invs (fst (Iof ll)) wt ot))),
      sat (phplus (upd location_eq_dec p ll (Some (Locked wt ot))) p1) (Some (ll :: O)) (ghplus C C1) (weakest_pre_ct (tt, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))).
  destruct tmp1 as (eqls,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4))))))))))))))))))).
  subst.

  assert (phpdefp32p42: phplusdef p3 p2 /\ phplusdef p4 p2). repeat php_.
  assert (ghpdefp32p42: ghplusdef C3 c2 /\ ghplusdef C4 c2). repeat php_.

  apply Coq.Bool.Bool.andb_true_iff in eqls.
  destruct eqls as (EQ1,EQ2).
  apply Z.eqb_eq in EQ1.
  unfold id in *.

  assert (PERM: Permutation O (map evall v) /\ o2 = None).
  {
  inversion tmp5.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  rewrite <- H2 in opo1o2.
  inversion opo1o2.
  split.
  apply Permutation_trans with o'0.
  apply Permutation_sym.
  assumption.
  apply Permutation_trans with o'.
  apply Permutation_sym.
  assumption.
  apply Permutation_sym.
  assumption.
  reflexivity.
  }
  destruct PERM as (PERM,o2n).
  rewrite o2n in *.

  exists (evall v0).
  exists. rewrite EQ1. reflexivity.
  exists.
  apply phplus_lock.
  apply phplus_lock.
  assumption.
  exists.
  apply prcl_perm with (map evall v).
  assumption.
  assumption.
  intros.

  assert (p2v0: p2 (evall v0) = Some Lock \/ p2 (evall v0) = None).
  {
  apply phplus_lock_none with (phplus p3 p4).
  rewrite phplus_comm; repeat php_.
  }

  assert (phpdefp2up34: phplusdef p2 (upd location_eq_dec (phplus p3 p4) (evall v0) (Some (Locked wt ot)))).
  {
  apply phpdef_comm.
  apply phpdef_locked'; repeat php_.
  }

  assert (phpdefp1p34p1p2: phplusdef p1 (phplus p3 p4) /\ phplusdef p1 p2). repeat php_.
  assert (phpdefp13p14: phplusdef p1 p3 /\ phplusdef p1 p4). repeat php_.

  assert (phpdefup34p1: phplusdef (upd location_eq_dec (phplus p3 p4) (evall v0) (Some (Locked wt ot))) p1).
  {
  apply phpdef_locked'; repeat php_.
  }

  assert (eqh: phplus (phplus (phplus p3 p4) p1) p2 = phplus p1 (phplus (phplus p3 p4) p2)).
  {
  symmetry.
  rewrite phplus_comm; repeat php_.
  }

  assert (bp34p1: boundph (phplus (phplus p3 p4) p1)).
  {
  apply boundph_mon with p2; repeat php_.
  rewrite eqh.
  assumption.
  }

  assert (bup34p1: boundph (phplus (upd location_eq_dec (phplus p3 p4) (evall v0) (Some (Locked wt ot))) p1)).
  {
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1',(v2',(CO,rest))).
  inversion CO.
  }

  assert (EQH: phplus (upd location_eq_dec (phplus (phplus p3 p4) p2) (evall v0)
    (Some (Locked wt ot))) p1 = 
    phplus p2 (phplus (upd location_eq_dec (phplus p3 p4) (evall v0)
    (Some (Locked wt ot))) p1)).
  {
  symmetry.
  rewrite <- phplus_assoc; repeat php_.
  rewrite phplus_comm; repeat php_.
  rewrite phplus_upd; repeat php_.
  unfold not.
  intros.
  destruct H as (v3,(f3,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
  }

  assert (bp2up34: boundph (phplus p2 (phplus
    (upd location_eq_dec (phplus p3 p4) (evall v0) (Some (Locked wt ot))) p1))).
  {
  rewrite <- EQH.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1',(v2',(CO,rest))).
  inversion CO.
  }

  assert (ghpdefp1p34p1p2: ghplusdef C1 (ghplus C3 C4) /\ ghplusdef C1 c2). repeat php_.
  assert (ghpdefp13p14: ghplusdef C1 C3 /\ ghplusdef C1 C4). repeat php_.

  assert (EQC: ghplus (ghplus (ghplus C3 C4) c2) C1 =
    ghplus c2 (ghplus (ghplus C3 C4) C1)).
  {
  symmetry.
  rewrite ghplus_comm; repeat php_.
  }

  assert (eqc: ghplus (ghplus (ghplus C3 C4) C1) c2 = ghplus C1 (ghplus (ghplus C3 C4) c2)).
  {
  symmetry.
  rewrite ghplus_comm; repeat php_.
  }

  assert (gbC34C1: boundgh (ghplus (ghplus C3 C4) C1)).
  {
  apply boundgh_mon with c2; repeat php_.
  rewrite eqc.
  assumption.
  }

  assert (bc2c34c1: boundgh (ghplus c2 (ghplus (ghplus C3 C4) C1))).
  {
  rewrite <- EQC.
  rewrite ghplus_comm; repeat php_.
  }

  assert (bu34: boundph (upd location_eq_dec (phplus p3 p4) (evall v0) (Some (Locked wt ot)))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  rewrite EQH.
  rewrite EQC.
  apply tmp2 with wt ot (Some (evall v0 :: O)); repeat php_.
  apply sn_op.
  apply Permutation_refl.
  exists (emp knowledge), (phplus (upd location_eq_dec (phplus p3 p4) (evall v0) (Some (Locked wt ot))) p1).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (evall v0 :: map evall v)), None.
  exists (emp (option nat*nat)), (ghplus (ghplus C3 C4) C1).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  apply fs_op.
  apply perm_skip.
  apply Permutation_sym.
  assumption.
  split.
  apply fs_op.
  apply Permutation_refl.
  split.
  exists (upd location_eq_dec (phplus p3 p4) (evall v0) (Some (Locked wt ot))), p1.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists None, None, (ghplus C3 C4), C1.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  apply None_op.
  split.
  unfold upd.
  destruct (location_eq_dec (evall v0) (evall v0)).
  reflexivity.
  contradiction.
  split. assumption.
  split; reflexivity.
  split; repeat php_.
Qed.

Lemma sat_chrg:
  forall p O C v tx invs
        (SAT: sat p (Some O) C (weakest_pre_ct (g_chrg v, tx) invs)),
    exists wt ot lv ll
           (EQv: Aof lv = ([[v]]))
           (EQl: Aof ll = Lof lv)
           (Pl: p ll = Some (Locked wt ot))
           (Pv: p lv = Some Cond),
      sat (upd location_eq_dec p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)%nat))))
       (Some (lv::O)) C (weakest_pre_ct (tt, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v0,(v1,(v2,(v3,(v4,(eqls,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4)))))))))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp6,(tmp7, (p5p6,C5C6)))))))))))))))))).

subst.

  assert (phpdefp13p156: phplusdef p1 p3 /\ phplusdef p1 (phplus p5 p6)).
  {
  repeat php_.
  }
  assert (phpdefp15p16: phplusdef p1 p5 /\ phplusdef p1 p6).
  {
  repeat php_.
  }
  assert (phpdefp35p36: phplusdef p3 p5 /\ phplusdef p3 p6).
  {
  repeat php_.
  }

  assert (ghpdefp13p156: ghplusdef c1 C3 /\ ghplusdef c1 (ghplus C5 C6)).
  {
  repeat php_.
  }
  assert (ghpdefp15p16: ghplusdef c1 C5 /\ ghplusdef c1 C6).
  {
  repeat php_.
  }
  assert (ghpdefp35p36: ghplusdef C3 C5 /\ ghplusdef C3 C6).
  {
  repeat php_.
  }

  assert (o6N: Permutation O (map evall v0) /\ O6 = None).
  {
  inversion tmp4.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  rewrite <- H4 in opo1o2.
  inversion opo1o2.
  rewrite <- H3 in opO5O6.
  inversion opO5O6.
  split.
  apply Permutation_trans with o'0.
  apply Permutation_sym.
  assumption.
  apply Permutation_trans with o'.
  apply Permutation_sym.
  assumption.
  apply Permutation_sym.
  assumption.
  reflexivity.
  }
  destruct o6N as (PERM,o6N).
  rewrite o6N in *.

  assert (p1p3p45v3: phplus p1 (phplus p3 (phplus p5 p6)) (evall v3) = Some (Locked v1 v2)).
  {
  apply phplus_locked'; repeat php_.
  apply phplus_locked'; repeat php_.
  apply phplus_locked; repeat php_.
  }

  assert (p1p3p56v4: phplus p1 (phplus p3 (phplus p5 p6)) (evall v4) = Some Cond).
  {
  apply phplus_Cond; repeat php_.
  }

  assert (eqh: phplus (phplus p1 (phplus p3 p5)) p6 = phplus p1 (phplus p3 (phplus p5 p6))).
  {
  rewrite phplus_assoc; repeat php_.
  }

  assert (bp135: boundph (phplus p1 (phplus p3 p5))).
  {
  apply boundph_mon with p6; repeat php_.
  rewrite eqh.
  assumption.
  }

  assert (bp1p35: boundph (phplus p1 (phplus p3 p5))).
  {
  apply boundph_mon with p6; repeat php_.
  rewrite eqh.
  assumption.
  }

  assert (bup135: boundph (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
   (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))))).
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (p35v3: exists wt1 ot1 : bag, phplus p3 p5 (evall v3) = Some (Locked wt1 ot1)).
  {
  exists v1, v2.
  apply phplus_locked'; repeat php_.
  }

  assert (p11p35v3: exists wt1 ot1 : bag,
    phplus p1 (phplus p3 p5) (evall v3) = Some (Locked wt1 ot1)).
  {
  exists v1, v2.
  apply phplus_locked'; repeat php_.
  apply phplus_locked'; repeat php_.
  }

  assert (phpdefp6up1p35: phplusdef p6
    (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  }

  assert (bp6up1p35: boundph (phplus p6
    (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat)))))).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  rewrite eqh.
  assumption.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v4',(v5',(CO,rest))).
  inversion CO.
  }

  assert (eqc': ghplus (ghplus C3 (ghplus C5 c1)) C6 = 
    ghplus c1 (ghplus C3 (ghplus C5 C6))).
  {
  replace (ghplus c1 (ghplus C3 (ghplus C5 C6))) with 
    (ghplus (ghplus C3 (ghplus C5 C6)) c1).
  rewrite ghplus_assoc; repeat php_.
  apply ghplus_comm.
  repeat php_.
  }

  assert (bgC3C51: boundgh (ghplus C3 (ghplus C5 c1))).
  {
  apply boundgh_mon with C6.
  rewrite eqc'.
  assumption.
  }

  assert (bgc6c3c51: boundgh (ghplus C6 (ghplus C3 (ghplus C5 c1)))).
  {
  rewrite ghplus_comm; repeat php_.
  rewrite eqc'.
  assumption.
  }

  assert (phpdefp1up35: phplusdef p1 (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  }

  assert (bu35: boundph (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bp1up35: boundph (phplus p1 (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat)))))).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v4',(v5',(CON,rest))).
  inversion CON.
  }

  apply Coq.Bool.Bool.andb_true_iff in eqls.
  destruct eqls as (EQ1,EQ2).
  apply Z.eqb_eq in EQ1.
  apply Z.eqb_eq in EQ2.
  unfold id in *.

  exists v1, v2, (evall v4), (evall v3).
  exists. symmetry. assumption.
  exists. symmetry. assumption.
  exists. assumption.
  exists. assumption.

  assert (EQH: upd location_eq_dec (phplus p1 (phplus p3 (phplus p5 p6))) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))) =
    phplus p6 (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))))).
  {
  replace (phplus p1 (phplus p3 (phplus p5 p6))) with 
    (phplus (phplus p1 (phplus p3 p5)) p6).
  rewrite <- phplus_upd.
  apply phplus_comm.
  apply phpdef_locked; repeat php_.
  unfold not.
  intros.
  destruct H as (v0',(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
  }

  assert (EQC: ghplus c1 (ghplus C3 (ghplus C5 C6)) =
    ghplus C6 (ghplus C3 (ghplus C5 c1))).
  {
  rewrite ghplus_comm.
  replace (ghplus C6 (ghplus C3 (ghplus C5 c1))) with
    (ghplus (ghplus C3 (ghplus C5 c1)) C6).
  rewrite ghplus_assoc; repeat php_.
  apply ghplus_comm; repeat php_.
  assumption.
  } 

  rewrite EQH.
  rewrite EQC.

  apply tmp7 with (Some (evall v4 :: O)); repeat php_.
  apply sn_op.
  apply Permutation_refl.
  exists p1, (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat)))).
  exists. repeat php_.
  exists. repeat php_.
  exists. assumption.
  exists. assumption.
  exists None, (Some (evall v4 :: O)), (emp (option nat*nat)), (ghplus C3 (ghplus C5 c1)).
  exists. repeat php_. 
  exists. repeat php_. 
  exists. assumption.
  exists. assumption.
  exists.
  apply sn_op.
  apply Permutation_refl.
  split.
  assumption.
  split.
  exists (emp knowledge), (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat)))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (evall v4 :: O)), None.
  exists (emp (option nat*nat)), (ghplus C3 (ghplus C5 c1)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  apply fs_op.
  apply Permutation_refl.
  split.
  apply fs_op.
  apply perm_skip.
  apply Permutation_sym.
  assumption.
  split.
  unfold upd.
  destruct (location_eq_dec (evall v3) (evall v3)).
  reflexivity.
  contradiction.
  split.
  repeat php_.
  repeat php_.
  split.
  rewrite phplus_comm; repeat php_.
  rewrite phplus_upd; repeat php_.
  rewrite phplus_comm; repeat php_.
  unfold not.
  intros.
  destruct H as (v0',(f',(v',(f'',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
  repeat php_.
Qed.


Lemma sat_disch:
  forall p O C v tx invs
        (SAT: sat p (Some O) C (weakest_pre_ct (g_disch v, tx) invs)),
    exists wt ot O1 lv ll
           (O1eq: Permutation O (lv::O1))
           (EQv: Aof lv = ([[v]]))
           (EQl: Aof ll = Lof lv)
           (Pl: p ll = Some (Locked wt ot))
           (Pv: p lv = Some Cond)
           (INO: In lv O)
           (SAFE_OBS: safe_obs lv (wt ([[v]])) ((ot ([[v]])) - 1) = true),
      sat (upd location_eq_dec p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)%nat))))
       (Some O1) C (weakest_pre_ct (tt, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v0,(v1,(v2,(v3,(v4,(eqls,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4)))))))))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp6,(tmp7, (p5p6,C5C6)))))))))))))))))).

subst.

  assert (phpdefp13p156: phplusdef p1 p3 /\ phplusdef p1 (phplus p5 p6)).
  {
  repeat php_.
  }
  assert (phpdefp15p16: phplusdef p1 p5 /\ phplusdef p1 p6).
  {
  repeat php_.
  }
  assert (phpdefp35p36: phplusdef p3 p5 /\ phplusdef p3 p6).
  {
  repeat php_.
  }

  assert (ghpdefp13p156: ghplusdef c1 C3 /\ ghplusdef c1 (ghplus C5 C6)).
  {
  repeat php_.
  }
  assert (ghpdefp15p16: ghplusdef c1 C5 /\ ghplusdef c1 C6).
  {
  repeat php_.
  }
  assert (ghpdefp35p36: ghplusdef C3 C5 /\ ghplusdef C3 C6).
  {
  repeat php_.
  }

  assert (PERM: Permutation O (evall v4 :: map evall v0) /\ O6 = None).
  {
  inversion tmp4.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  rewrite <- H4 in opo1o2.
  inversion opo1o2.
  split.
  apply Permutation_trans with o'0.
  apply Permutation_sym.
  assumption.
  apply Permutation_trans with o'.
  apply Permutation_sym.
  assumption.
  apply Permutation_sym.
  assumption.
  rewrite <- H3 in opO5O6.
  inversion opO5O6.
  reflexivity.
  }
  destruct PERM as (PERM,o6N).
  rewrite o6N in *.

  assert (p1p3p45v3: phplus p1 (phplus p3 (phplus p5 p6)) (evall v3) = Some (Locked v1 v2)).
  {
  apply phplus_locked'; repeat php_.
  apply phplus_locked'; repeat php_.
  apply phplus_locked; repeat php_.
  }

  assert (p1p3p56v4: phplus p1 (phplus p3 (phplus p5 p6)) (evall v4) = Some Cond).
  {
  apply phplus_Cond; repeat php_.
  }

  assert (eqh: phplus (phplus p1 (phplus p3 p5)) p6 = phplus p1 (phplus p3 (phplus p5 p6))).
  {
  rewrite phplus_assoc; repeat php_.
  }

  assert (bp135: boundph (phplus p1 (phplus p3 p5))).
  {
  apply boundph_mon with p6; repeat php_.
  rewrite eqh.
  assumption.
  }

  assert (bp1p35: boundph (phplus p1 (phplus p3 p5))).
  {
  apply boundph_mon with p6; repeat php_.
  rewrite eqh.
  assumption.
  }

  assert (bup135: boundph (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
   (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))))).
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (p35v3: exists wt1 ot1 : bag, phplus p3 p5 (evall v3) = Some (Locked wt1 ot1)).
  {
  exists v1, v2.
  apply phplus_locked'; repeat php_.
  }

  assert (p11p35v3: exists wt1 ot1 : bag,
    phplus p1 (phplus p3 p5) (evall v3) = Some (Locked wt1 ot1)).
  {
  exists v1, v2.
  apply phplus_locked'; repeat php_.
  apply phplus_locked'; repeat php_.
  }

  assert (phpdefp6up1p35: phplusdef p6
    (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  }

  assert (bp6up1p35: boundph (phplus p6
    (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat)))))).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  rewrite eqh.
  assumption.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v4',(v5',(CO,rest))).
  inversion CO.
  }

  assert (eqc': ghplus (ghplus C3 (ghplus C5 c1)) C6 = 
    ghplus c1 (ghplus C3 (ghplus C5 C6))).
  {
  replace (ghplus c1 (ghplus C3 (ghplus C5 C6))) with 
    (ghplus (ghplus C3 (ghplus C5 C6)) c1).
  rewrite ghplus_assoc; repeat php_.
  apply ghplus_comm.
  repeat php_.
  }

  assert (bgC3C51: boundgh (ghplus C3 (ghplus C5 c1))).
  {
  apply boundgh_mon with C6.
  rewrite eqc'.
  assumption.
  }

  assert (bgc6c3c51: boundgh (ghplus C6 (ghplus C3 (ghplus C5 c1)))).
  {
  rewrite ghplus_comm; repeat php_.
  rewrite eqc'.
  assumption.
  }

  assert (phpdefp1up35: phplusdef p1 (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  }

  assert (bu35: boundph (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bp1up35: boundph (phplus p1 (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat)))))).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v4',(v5',(CON,rest))).
  inversion CON.
  }

  apply Coq.Bool.Bool.andb_true_iff in eqls.
  destruct eqls as (EQ1,EQ2).
  apply Coq.Bool.Bool.andb_true_iff in EQ2.
  destruct EQ2 as (EQ2,EQ3).
  apply Coq.Bool.Bool.andb_true_iff in EQ3.
  destruct EQ3 as (EQ3,EQ4).
  apply Z.eqb_eq in EQ1.
  apply Z.eqb_eq in EQ2.
  unfold id in *.

  exists v1, v2, (map evall v0), (evall v4), (evall v3).
  exists PERM.
  exists. symmetry. assumption.
  exists. symmetry. assumption.
  exists. assumption.
  exists. assumption.
  exists. apply Permutation_in with (evall v4 :: map evall v0).
  apply Permutation_sym.
  assumption.
  left. reflexivity.
  exists. assumption.

  assert (EQH: upd location_eq_dec (phplus p1 (phplus p3 (phplus p5 p6))) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))) =
    phplus p6 (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))))).
  {
  replace (phplus p1 (phplus p3 (phplus p5 p6))) with 
    (phplus (phplus p1 (phplus p3 p5)) p6).
  rewrite <- phplus_upd.
  apply phplus_comm.
  apply phpdef_locked; repeat php_.
  unfold not.
  intros.
  destruct H as (v0',(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
  }

  assert (EQC: ghplus c1 (ghplus C3 (ghplus C5 C6)) =
    ghplus C6 (ghplus C3 (ghplus C5 c1))).
  {
  rewrite ghplus_comm.
  replace (ghplus C6 (ghplus C3 (ghplus C5 c1))) with
    (ghplus (ghplus C3 (ghplus C5 c1)) C6).
  rewrite ghplus_assoc; repeat php_.
  apply ghplus_comm; repeat php_.
  assumption.
  } 

  rewrite EQH.
  rewrite EQC.

  apply tmp7 with (Some (map evall v0)); repeat php_.
  apply sn_op.
  apply Permutation_refl.

  exists p1, (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat)))).
  exists. repeat php_.
  exists. repeat php_.
  exists. assumption.
  exists. assumption.
  exists None, (Some (map evall v0)), (emp (option nat*nat)), (ghplus C3 (ghplus C5 c1)).
  exists. repeat php_. 
  exists. repeat php_. 
  exists. assumption.
  exists. assumption.
  exists.
  apply sn_op.
  apply Permutation_refl.
  split.
  assumption.
  split.
  exists (emp knowledge), (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat)))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (map evall v0)), None.
  exists (emp (option nat*nat)), (ghplus C3 (ghplus C5 c1)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  apply fs_op.
  apply Permutation_refl.
  split.
  apply fs_op.
  apply Permutation_refl.
  split.
  unfold upd.
  destruct (location_eq_dec (evall v3) (evall v3)).
  reflexivity.
  contradiction.
  split.
  repeat php_.
  repeat php_.
  split.
  rewrite phplus_comm; repeat php_.
  rewrite phplus_upd; repeat php_.
  rewrite phplus_comm; repeat php_.
  unfold not.
  intros.
  destruct H as (v0',(f',(v',(f'',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
  repeat php_.
Qed.


Lemma sat_dischu:
  forall p O C v tx invs
        (SAT: sat p (Some O) C (weakest_pre_ct (g_dischu v, tx) invs)),
    exists wt ot O1 lv ll
           (O1eq: Permutation O (lv::O1))
           (EQv: Aof lv = ([[v]]))
           (EQl: Aof ll = Lof lv)
           (Pl: p ll = Some (Ulock wt ot))
           (Pv: p lv = Some Cond)
           (INO: In lv O)
           (SAFE_OBS: safe_obs lv (wt ([[v]])) ((ot ([[v]])) - 1) = true),
      sat (upd location_eq_dec p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)%nat))))
       (Some O1) C (weakest_pre_ct (tt, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v0,(v1,(v2,(v3,(v4,(eqls,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4)))))))))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp6,(tmp7, (p5p6,C5C6)))))))))))))))))).

subst.

  assert (phpdefp13p156: phplusdef p1 p3 /\ phplusdef p1 (phplus p5 p6)).
  {
  repeat php_.
  }
  assert (phpdefp15p16: phplusdef p1 p5 /\ phplusdef p1 p6).
  {
  repeat php_.
  }
  assert (phpdefp35p36: phplusdef p3 p5 /\ phplusdef p3 p6).
  {
  repeat php_.
  }

  assert (ghpdefp13p156: ghplusdef c1 C3 /\ ghplusdef c1 (ghplus C5 C6)).
  {
  repeat php_.
  }
  assert (ghpdefp15p16: ghplusdef c1 C5 /\ ghplusdef c1 C6).
  {
  repeat php_.
  }
  assert (ghpdefp35p36: ghplusdef C3 C5 /\ ghplusdef C3 C6).
  {
  repeat php_.
  }

  assert (PERM: Permutation O (evall v4 :: map evall v0) /\ O6 = None).
  {
  inversion tmp4.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  rewrite <- H4 in opo1o2.
  inversion opo1o2.
  split.
  apply Permutation_trans with o'0.
  apply Permutation_sym.
  assumption.
  apply Permutation_trans with o'.
  apply Permutation_sym.
  assumption.
  apply Permutation_sym.
  assumption.
  rewrite <- H3 in opO5O6.
  inversion opO5O6.
  reflexivity.
  }
  destruct PERM as (PERM,o6N).
  rewrite o6N in *.

  assert (p1p3p45v3: phplus p1 (phplus p3 (phplus p5 p6)) (evall v3) = Some (Ulock v1 v2)).
  {
  apply phplus_ulock'; repeat php_.
  apply phplus_ulock'; repeat php_.
  apply phplus_ulock; repeat php_.
  }

  assert (p1p3p56v4: phplus p1 (phplus p3 (phplus p5 p6)) (evall v4) = Some Cond).
  {
  apply phplus_Cond; repeat php_.
  }

  assert (eqh: phplus (phplus p1 (phplus p3 p5)) p6 = phplus p1 (phplus p3 (phplus p5 p6))).
  {
  rewrite phplus_assoc; repeat php_.
  }

  assert (bp135: boundph (phplus p1 (phplus p3 p5))).
  {
  apply boundph_mon with p6; repeat php_.
  rewrite eqh.
  assumption.
  }

  assert (bp1p35: boundph (phplus p1 (phplus p3 p5))).
  {
  apply boundph_mon with p6; repeat php_.
  rewrite eqh.
  assumption.
  }

  assert (bup135: boundph (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
   (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))))).
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (p35v3: exists wt1 ot1 : bag, phplus p3 p5 (evall v3) = Some (Ulock wt1 ot1)).
  {
  exists v1, v2.
  apply phplus_ulock'; repeat php_.
  }

  assert (p11p35v3: exists wt1 ot1 : bag,
    phplus p1 (phplus p3 p5) (evall v3) = Some (Ulock wt1 ot1)).
  {
  exists v1, v2.
  apply phplus_ulock'; repeat php_.
  apply phplus_ulock'; repeat php_.
  }

  assert (p6v3: p6 (evall v3) = None).
  {
  unfold phplusdef in phpdefp5p6.
  specialize phpdefp5p6 with (evall v3).
  rewrite tmp6 in phpdefp5p6.
  destruct (p6 (evall v3)).
  contradiction.
  reflexivity.
  }

  assert (p1v3: p1 (evall v3) = None).
  {
  destruct phpdefp15p16 as (pd,pd2).
  unfold phplusdef in pd.
  specialize pd with (evall v3).
  rewrite tmp6 in pd.
  destruct (p1 (evall v3)).
  destruct k;
  contradiction.
  reflexivity.
  }

  assert (phpdefp6up1p35: phplusdef p6
    (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))))).
  {
  apply phpdef_comm.
  apply phpdef_ulock; repeat php_.
  }

  assert (bp6up1p35: boundph (phplus p6
    (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat)))))).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  rewrite eqh.
  assumption.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v4',(v5',(CO,rest))).
  inversion CO.
  }

  assert (eqc': ghplus (ghplus C3 (ghplus C5 c1)) C6 = 
    ghplus c1 (ghplus C3 (ghplus C5 C6))).
  {
  replace (ghplus c1 (ghplus C3 (ghplus C5 C6))) with 
    (ghplus (ghplus C3 (ghplus C5 C6)) c1).
  rewrite ghplus_assoc; repeat php_.
  apply ghplus_comm.
  repeat php_.
  }

  assert (bgC3C51: boundgh (ghplus C3 (ghplus C5 c1))).
  {
  apply boundgh_mon with C6.
  rewrite eqc'.
  assumption.
  }

  assert (bgc6c3c51: boundgh (ghplus C6 (ghplus C3 (ghplus C5 c1)))).
  {
  rewrite ghplus_comm; repeat php_.
  rewrite eqc'.
  assumption.
  }

  assert (phpdefp1up35: phplusdef p1 (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))))).
  {
  apply phpdef_comm.
  apply phpdef_ulock; repeat php_.
  }

  assert (bu35: boundph (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bp1up35: boundph (phplus p1 (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat)))))).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v4',(v5',(CON,rest))).
  inversion CON.
  }

  apply Coq.Bool.Bool.andb_true_iff in eqls.
  destruct eqls as (EQ1,EQ2).
  apply Coq.Bool.Bool.andb_true_iff in EQ2.
  destruct EQ2 as (EQ2,EQ3).
  apply Coq.Bool.Bool.andb_true_iff in EQ3.
  destruct EQ3 as (EQ3,EQ4).
  apply Z.eqb_eq in EQ1.
  apply Z.eqb_eq in EQ2.
  unfold id in *.

  exists v1, v2, (map evall v0), (evall v4), (evall v3).
  exists PERM.
  exists. symmetry. assumption.
  exists. symmetry. assumption.
  exists. assumption.
  exists. assumption.
  exists. apply Permutation_in with (evall v4 :: map evall v0).
  apply Permutation_sym.
  assumption.
  left. reflexivity.
  exists. assumption.

  assert (EQH: upd location_eq_dec (phplus p1 (phplus p3 (phplus p5 p6))) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))) =
    phplus p6 (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))))).
  {
  replace (phplus p1 (phplus p3 (phplus p5 p6))) with 
    (phplus (phplus p1 (phplus p3 p5)) p6).
  rewrite <- phplus_upd.
  apply phplus_comm.
  apply phpdef_ulock; repeat php_.
  unfold not.
  intros.
  destruct H as (v0',(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
  }

  assert (EQC: ghplus c1 (ghplus C3 (ghplus C5 C6)) =
    ghplus C6 (ghplus C3 (ghplus C5 c1))).
  {
  rewrite ghplus_comm.
  replace (ghplus C6 (ghplus C3 (ghplus C5 c1))) with
    (ghplus (ghplus C3 (ghplus C5 c1)) C6).
  rewrite ghplus_assoc; repeat php_.
  apply ghplus_comm; repeat php_.
  assumption.
  } 

  rewrite EQH.
  rewrite EQC.

  apply tmp7 with (Some (map evall v0)); repeat php_.
  apply sn_op.
  apply Permutation_refl.

  exists p1, (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat)))).
  exists. repeat php_.
  exists. repeat php_.
  exists. assumption.
  exists. assumption.
  exists None, (Some (map evall v0)), (emp (option nat*nat)), (ghplus C3 (ghplus C5 c1)).
  exists. repeat php_. 
  exists. repeat php_. 
  exists. assumption.
  exists. assumption.
  exists.
  apply sn_op.
  apply Permutation_refl.
  split.
  assumption.
  split.
  exists (emp knowledge), (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat)))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (map evall v0)), None.
  exists (emp (option nat*nat)), (ghplus C3 (ghplus C5 c1)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  apply fs_op.
  apply Permutation_refl.
  split.
  apply fs_op.
  apply Permutation_refl.
  split.
  unfold upd.
  destruct (location_eq_dec (evall v3) (evall v3)).
  reflexivity.
  contradiction.
  split.
  repeat php_.
  repeat php_.
  split.
  rewrite phplus_comm; repeat php_.
  rewrite phplus_upd; repeat php_.
  rewrite phplus_comm; repeat php_.
  unfold not.
  intros.
  destruct H as (v0',(f',(v',(f'',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  repeat php_.
Qed.

Lemma sat_chrgu:
  forall p O C v tx invs
        (SAT: sat p (Some O) C (weakest_pre_ct (g_chrgu v, tx) invs)),
    exists wt ot lv ll
           (EQv: Aof lv = ([[v]]))
           (EQl: Aof ll = Lof lv)
           (Pl: p ll = Some (Ulock wt ot))
           (Pv: p lv = Some Cond),
      sat (upd location_eq_dec p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)%nat))))
       (Some (lv::O)) C (weakest_pre_ct (tt, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v0,(v1,(v2,(v3,(v4,(eqls,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4)))))))))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp6,(tmp7, (p5p6,C5C6)))))))))))))))))).

subst.

  assert (phpdefp13p156: phplusdef p1 p3 /\ phplusdef p1 (phplus p5 p6)).
  {
  repeat php_.
  }
  assert (phpdefp15p16: phplusdef p1 p5 /\ phplusdef p1 p6).
  {
  repeat php_.
  }
  assert (phpdefp35p36: phplusdef p3 p5 /\ phplusdef p3 p6).
  {
  repeat php_.
  }

  assert (ghpdefp13p156: ghplusdef c1 C3 /\ ghplusdef c1 (ghplus C5 C6)).
  {
  repeat php_.
  }
  assert (ghpdefp15p16: ghplusdef c1 C5 /\ ghplusdef c1 C6).
  {
  repeat php_.
  }
  assert (ghpdefp35p36: ghplusdef C3 C5 /\ ghplusdef C3 C6).
  {
  repeat php_.
  }

  assert (o6N: Permutation O (map evall v0) /\ O6 = None).
  {
  inversion tmp4.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  rewrite <- H4 in opo1o2.
  inversion opo1o2.
  rewrite <- H3 in opO5O6.
  inversion opO5O6.
  split.
  apply Permutation_trans with o'0.
  apply Permutation_sym.
  assumption.
  apply Permutation_trans with o'.
  apply Permutation_sym.
  assumption.
  apply Permutation_sym.
  assumption.
  reflexivity.
  }
  destruct o6N as (PERM,o6N).
  rewrite o6N in *.

  assert (p1p3p45v3: phplus p1 (phplus p3 (phplus p5 p6)) (evall v3) = Some (Ulock v1 v2)).
  {
  apply phplus_ulock'; repeat php_.
  apply phplus_ulock'; repeat php_.
  apply phplus_ulock; repeat php_.
  }

  assert (p1p3p56v4: phplus p1 (phplus p3 (phplus p5 p6)) (evall v4) = Some Cond).
  {
  apply phplus_Cond; repeat php_.
  }

  assert (eqh: phplus (phplus p1 (phplus p3 p5)) p6 = phplus p1 (phplus p3 (phplus p5 p6))).
  {
  rewrite phplus_assoc; repeat php_.
  }

  assert (bp135: boundph (phplus p1 (phplus p3 p5))).
  {
  apply boundph_mon with p6; repeat php_.
  rewrite eqh.
  assumption.
  }

  assert (bp1p35: boundph (phplus p1 (phplus p3 p5))).
  {
  apply boundph_mon with p6; repeat php_.
  rewrite eqh.
  assumption.
  }

  assert (bup135: boundph (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
   (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))))).
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (p35v3: exists wt1 ot1 : bag, phplus p3 p5 (evall v3) = Some (Ulock wt1 ot1)).
  {
  exists v1, v2.
  apply phplus_ulock'; repeat php_.
  }

  assert (p11p35v3: exists wt1 ot1 : bag,
    phplus p1 (phplus p3 p5) (evall v3) = Some (Ulock wt1 ot1)).
  {
  exists v1, v2.
  apply phplus_ulock'; repeat php_.
  apply phplus_ulock'; repeat php_.
  }

  assert (p6v3: p6 (evall v3) = None).
  {
  unfold phplusdef in phpdefp5p6.
  specialize phpdefp5p6 with (evall v3).
  rewrite tmp6 in phpdefp5p6.
  destruct (p6 (evall v3)).
  contradiction.
  reflexivity.
  }

  assert (p1v3: p1 (evall v3) = None).
  {
  destruct phpdefp15p16 as (pd,pd2).
  unfold phplusdef in pd.
  specialize pd with (evall v3).
  rewrite tmp6 in pd.
  destruct (p1 (evall v3)).
  destruct k;
  contradiction.
  reflexivity.
  }

  assert (phpdefp6up1p35: phplusdef p6
    (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))))).
  {
  apply phpdef_comm.
  apply phpdef_ulock; repeat php_.
  }

  assert (bp6up1p35: boundph (phplus p6
    (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat)))))).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  rewrite eqh.
  assumption.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v4',(v5',(CO,rest))).
  inversion CO.
  }

  assert (eqc': ghplus (ghplus C3 (ghplus C5 c1)) C6 = 
    ghplus c1 (ghplus C3 (ghplus C5 C6))).
  {
  replace (ghplus c1 (ghplus C3 (ghplus C5 C6))) with 
    (ghplus (ghplus C3 (ghplus C5 C6)) c1).
  rewrite ghplus_assoc; repeat php_.
  apply ghplus_comm.
  repeat php_.
  }

  assert (bgC3C51: boundgh (ghplus C3 (ghplus C5 c1))).
  {
  apply boundgh_mon with C6.
  rewrite eqc'.
  assumption.
  }

  assert (bgc6c3c51: boundgh (ghplus C6 (ghplus C3 (ghplus C5 c1)))).
  {
  rewrite ghplus_comm; repeat php_.
  rewrite eqc'.
  assumption.
  }

  assert (phpdefp1up35: phplusdef p1 (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))))).
  {
  apply phpdef_comm.
  apply phpdef_ulock; repeat php_.
  }

  assert (bu35: boundph (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bp1up35: boundph (phplus p1 (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat)))))).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v4',(v5',(CON,rest))).
  inversion CON.
  }

  apply Coq.Bool.Bool.andb_true_iff in eqls.
  destruct eqls as (EQ1,EQ2).
  apply Z.eqb_eq in EQ1.
  apply Z.eqb_eq in EQ2.
  unfold id in *.

  exists v1, v2, (evall v4), (evall v3).
  exists. symmetry. assumption.
  exists. symmetry. assumption.
  exists. assumption.
  exists. assumption.

  assert (EQH: upd location_eq_dec (phplus p1 (phplus p3 (phplus p5 p6))) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))) =
    phplus p6 (upd location_eq_dec (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))))).
  {
  replace (phplus p1 (phplus p3 (phplus p5 p6))) with 
    (phplus (phplus p1 (phplus p3 p5)) p6).
  rewrite <- phplus_upd.
  apply phplus_comm.
  apply phpdef_ulock; repeat php_.
  unfold not.
  intros.
  destruct H as (v0',(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
  }

  assert (EQC: ghplus c1 (ghplus C3 (ghplus C5 C6)) =
    ghplus C6 (ghplus C3 (ghplus C5 c1))).
  {
  rewrite ghplus_comm.
  replace (ghplus C6 (ghplus C3 (ghplus C5 c1))) with
    (ghplus (ghplus C3 (ghplus C5 c1)) C6).
  rewrite ghplus_assoc; repeat php_.
  apply ghplus_comm; repeat php_.
  assumption.
  } 

  rewrite EQH.
  rewrite EQC.

  apply tmp7 with (Some (evall v4 :: O)); repeat php_.
  apply sn_op.
  apply Permutation_refl.
  exists p1, (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat)))).
  exists. repeat php_.
  exists. repeat php_.
  exists. assumption.
  exists. assumption.
  exists None, (Some (evall v4 :: O)), (emp (option nat*nat)), (ghplus C3 (ghplus C5 c1)).
  exists. repeat php_. 
  exists. repeat php_. 
  exists. assumption.
  exists. assumption.
  exists.
  apply sn_op.
  apply Permutation_refl.
  split.
  assumption.
  split.
  exists (emp knowledge), (upd location_eq_dec (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat)))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (evall v4 :: O)), None.
  exists (emp (option nat*nat)), (ghplus C3 (ghplus C5 c1)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  apply fs_op.
  apply Permutation_refl.
  split.
  apply fs_op.
  apply perm_skip.
  apply Permutation_sym.
  assumption.
  split.
  unfold upd.
  destruct (location_eq_dec (evall v3) (evall v3)).
  reflexivity.
  contradiction.
  split.
  repeat php_.
  repeat php_.
  split.
  rewrite phplus_comm; repeat php_.
  rewrite phplus_upd; repeat php_.
  rewrite phplus_comm; repeat php_.
  unfold not.
  intros.
  destruct H as (v0',(f',(v',(f'',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  repeat php_.
Qed.

Lemma sat_fork:
  forall p O C c tx invs
         (SAT: sat p (Some O) C (weakest_pre_ct (Fork c, tx) invs)),
    exists p1 p2 O1 O2 C1 C2 (GHPD: ghplusdef C1 C2) (BP1: boundph p1) (BP2: boundph p2) (PHPD: phplusdef p1 p2) (BP12: boundph (phplus p1 p2))
          (p1p2: p = phplus p1 p2) (O1O2: Permutation.Permutation (O1++O2) O) (C1C2: C = ghplus C1 C2)
     (SAT1: sat p1 (Some O1) C1 (weakest_pre_tx tx invs 0))
     (SAT2: sat p2 (Some O2) C2 (weakest_pre c (fun _ : Z => Aobs nil) id invs)), True.
Proof.
  intros.
  simpl in SAT.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))).
  destruct tmp1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4)))))))))))))))))).
  subst.

  assert (tmp: Permutation (map evall v ++ map evall v0) O /\ O4 = None /\ o2 = None).
  {
  inversion tmp4.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  rewrite <- H4 in opo1o2.
  inversion opo1o2.
  split.
  apply Permutation_trans with o'.
  rewrite <- map_app.
  assumption.
  apply Permutation_trans with o'0.
  assumption.
  assumption.
  split.
  reflexivity.
  reflexivity.
  }
  destruct tmp as (PERM,(o4n,o2n)).
  rewrite o4n,o2n in *.

  exists (phplus p3 p4), p2, (map evall v), (map evall v0), (ghplus C3 C4), c2, ghpdefc1c2, bp1, bp2.
  exists phpdefp1p2, bp1p2.
  exists. reflexivity.
  exists. assumption.
  exists. reflexivity.
  exists.
  rewrite ghplus_comm; repeat php_.
  rewrite phplus_comm; repeat php_.
  apply tmp5 with (Some (map evall v)); repeat php_.
  apply sn_op.
  apply Permutation_refl.
  apply fs_op.
  apply Permutation_refl.
  exists.
  replace p2 with (phplus p2 (emp knowledge)).
  replace c2 with (ghplus c2 (emp (option nat*nat))).
  apply tmp2 with (Some (map evall v0)); repeat php_.
  apply sn_op.
  apply Permutation_refl.
  apply fs_op.
  apply Permutation_refl.
  apply ghplus_emp.
  apply phplus_emp.
  trivial.
Qed.

Lemma sat_wait4cond:
  forall p O C ev el tx invs
        (SAT: sat p (Some O) C (weakest_pre_ct (Waiting4cond ev el, tx) invs)),
  exists l v
         (EQl: Aof l = ([[el]]))
         (EQv: Aof v = ([[ev]]))
         (Pv: p v = Some Cond)
         (Pl: p l = Some Lock \/ exists wt ot, p l = Some (Locked wt ot))
         (lvl: Lof v = ([[el]]))
         (PRCl: prcl l O = true)
         (PRCv: prcl v O = true),
    forall pm Cm (PHPDEF: phplusdef p pm) (BPm: boundph pm) (BPmp: boundph (phplus pm p)) (GHPDEF: ghplusdef C Cm) (BCm: boundgh Cm) (BCmC: boundgh (ghplus Cm C))
           (SATM: sat pm None Cm (subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb))),
      sat (phplus p pm) (Some O) (ghplus C Cm) (weakest_pre_ct (Waiting4lock el, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(sat1,(sat2,(p1p2,C1C2)))))))))))))))))))))).
  destruct sat1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(p3v1,(tmp1,(p3p4,C3C4)))))))))))))))))).
  destruct tmp1 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp6,(tmp7, (p5p6,C5C6)))))))))))))))))).

  assert (PERM: Permutation O (map evall v) /\ o2 = None).
  {
  inversion tmp7.
  rewrite <- H1 in opO5O6.
  inversion opO5O6.
  rewrite <- H2 in opO3O4.
  inversion opO3O4.
  rewrite <- H5 in opO1O2.
  inversion opO1O2.
  split.
  apply Permutation_trans with o'1.
  apply Permutation_sym.
  assumption.
  apply Permutation_trans with o'0.
  apply Permutation_sym.
  assumption.
  apply Permutation_trans with o'.
  apply Permutation_sym.
  assumption.
  apply Permutation_sym.
  assumption.
  reflexivity.
  }
  destruct PERM as (PERM, o2N).
  rewrite o2N in *.

  apply Coq.Bool.Bool.andb_true_iff in EQ.
  destruct EQ as (EQ1,EQ2).
  apply Coq.Bool.Bool.andb_true_iff in EQ2.
  destruct EQ2 as (EQ2,EQ3).
  apply Coq.Bool.Bool.andb_true_iff in EQ3.
  destruct EQ3 as (EQ3,EQ4).
  apply Coq.Bool.Bool.andb_true_iff in EQ4.
  destruct EQ4 as (EQ4,EQ5).
  apply Z.eqb_eq in EQ1.
  apply Z.eqb_eq in EQ2.
  apply Z.eqb_eq in EQ3.
  unfold id in *.

  assert (p1v0: p1 (evall v0) = Some Lock \/ (exists wt ot : bag, p1 (evall v0) = Some (Locked wt ot))).
  {
  rewrite <- p3p4.
  rewrite phplus_comm;
  try tauto.
  apply phplus_lock.
  rewrite <- p5p6.
  apply phplus_lock.
  tauto.
  }

  exists (evall v0), (evall v1).
  exists.
  rewrite EQ2.
  reflexivity.
  exists.
  rewrite EQ1.
  reflexivity.
  exists.
  rewrite <- p1p2.
  rewrite <- p3p4.
  unfold phplus.
  rewrite p3v1.
  reflexivity.
  exists.
  rewrite <- p1p2.
  apply phplus_lock;
  try tauto.
  exists.
  rewrite EQ2.
  rewrite <- EQ3.
  reflexivity.
  exists.
  apply prcl_perm with (map evall v).
  assumption.
  assumption.
  exists.
  apply prcl_perm with (map evall v).
  assumption.
  assumption.

  intros.
  assert (phpdefp1mp2m: phplusdef p1 pm /\ phplusdef p2 pm).
  {
  apply phpdef_dist;
  try tauto.
  rewrite p1p2.
  tauto.
  }

  assert (phpdefp1p2m: phplusdef p1 (phplus p2 pm)).
  {
  apply phpdef_pair;
  try tauto.
  }

  assert (bp2m: boundph (phplus p2 pm)).
  {
  rewrite phplus_comm;
  try tauto.
  apply boundph_mon with p1;
  try tauto.
  rewrite phplus_assoc;
  try tauto.
  replace (phplus p2 p1) with (phplus p1 p2).
  rewrite p1p2.
  tauto.
  apply phplus_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  }

  assert (bp1p2m: boundph (phplus p1 (phplus p2 pm))).
  {
  rewrite <- phplus_assoc;
  try tauto.
  rewrite p1p2.
  rewrite phplus_comm;
  try tauto.
  }

  assert (ghpdefp1mp2m: ghplusdef C1 Cm /\ ghplusdef C2 Cm).
  {
  apply ghpdef_dist;
  try tauto.
  rewrite C1C2.
  tauto.
  }

  assert (ghpdefp1p2m: ghplusdef C1 (ghplus C2 Cm)).
  {
  apply ghpdef_pair;
  try tauto.
  }

  assert (bgp2m: boundgh (ghplus C2 Cm)).
  {
  rewrite ghplus_comm;
  try tauto.
  apply boundgh_mon with C1;
  try tauto.
  rewrite ghplus_assoc;
  try tauto.
  replace (ghplus C2 C1) with (ghplus C1 C2).
  rewrite C1C2.
  tauto.
  apply ghplus_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  }

  assert (bgp1p2m: boundgh (ghplus C1 (ghplus C2 Cm))).
  {
  rewrite <- ghplus_assoc;
  try tauto.
  rewrite C1C2.
  rewrite ghplus_comm;
  try tauto.
  }

  exists v, v0.
  exists p1, (phplus p2 pm), phpdefp1p2m, bp1, bp2m, bp1p2m.
  exists (Some O), None, C1, (ghplus C2 Cm).
  exists ghpdefp1p2m, BC1, bgp2m, bgp1p2m.
  exists.
  apply fs_op.
  apply Permutation_refl.
  split.
  split.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  apply Z.eqb_eq.
  tauto.
  tauto.
  exists p1, (emp knowledge).
  exists.
  apply phpdef_emp.
  exists bp1, boundph_emp.
  exists.
  rewrite phplus_emp.
  assumption.
  exists None, (Some O), C1, (emp (option nat*nat)).
  exists.
  apply ghpdef_emp.
  exists BC1, boundgh_emp.
  exists.
  rewrite ghplus_emp.
  assumption.
  exists.
  apply sn_op.
  apply Permutation_refl.
  split.
  tauto.
  split.
  apply fs_op.
  apply Permutation_sym;
  tauto.
  rewrite phplus_emp.
  rewrite ghplus_emp.
  tauto.
  split.

  intros.
  assert (bp2mp': phplusdef p2 p' /\ phplusdef pm p').
  {
  apply phpdef_dist;
  try tauto.
  }

  assert (phpdefpmp'p2: phplusdef (phplus pm p') p2).
  {
  apply phpdef_pair';
  try tauto.
  apply phpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  }

  assert (bpmp': boundph (phplus pm p')).
  {
  apply boundph_mon with p2;
  try tauto.
  rewrite phplus_comm;
  try tauto.
  rewrite <- phplus_assoc;
  try tauto.
  }

  assert (bp2pm': boundph (phplus p2 (phplus pm p'))).
  {
  rewrite <- phplus_assoc;
  try tauto.
  }

  assert (gp2mp': ghplusdef C2 g' /\ ghplusdef Cm g').
  {
  apply ghpdef_dist;
  try tauto.
  }

  assert (ghpdefpmp'p2: ghplusdef (ghplus Cm g') C2).
  {
  apply ghpdef_pair';
  try tauto.
  apply ghpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  }

  assert (bgpmp': boundgh (ghplus Cm g')).
  {
  apply boundgh_mon with C2;
  try tauto.
  rewrite ghplus_comm;
  try tauto.
  rewrite <- ghplus_assoc;
  try tauto.
  }

  assert (bgp2pm': boundgh (ghplus C2 (ghplus Cm g'))).
  {
  rewrite <- ghplus_assoc;
  try tauto.
  }

  rewrite phplus_assoc;
  try tauto.
  rewrite ghplus_assoc;
  try tauto.
  apply sat2 with v2 v3 O';
  try tauto.
  apply phpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.

  destruct SAT as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(o7,(o8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(BC7C8,(opo7o8,(tmp10,(tmp8,(p7p8,C7C8)))))))))))))))))).


  assert (phpdefpm7pm8: phplusdef pm p7 /\ phplusdef pm p8).
  {
  apply phpdef_dist';
  try tauto.
  rewrite p7p8.
  tauto.
  }

  assert (phpdefp7p8m: phplusdef p7 (phplus p8 pm)).
  {
  apply phpdef_pair;
  try tauto.
  apply phpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  }

  assert (bp7p8m : boundph (phplus p7 (phplus p8 pm))).
  {
  rewrite <- phplus_assoc;
  try tauto.
  rewrite p7p8.
  rewrite phplus_comm;
  try tauto.
  apply phpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  }

  assert (bp8m: boundph (phplus p8 pm)).
  {
  apply boundph_mon with p7;
  try tauto.
  rewrite phplus_comm;
  try tauto.
  apply phpdef_comm;
  try tauto.
  }

  assert (ghpdefpm7pm8: ghplusdef Cm C7 /\ ghplusdef Cm C8).
  {
  apply ghpdef_dist';
  try tauto.
  rewrite C7C8.
  tauto.
  }

  assert (ghpdefp7p8m: ghplusdef C7 (ghplus C8 Cm)).
  {
  apply ghpdef_pair;
  try tauto.
  apply ghpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  }

  assert (bgp7p8m : boundgh (ghplus C7 (ghplus C8 Cm))).
  {
  rewrite <- ghplus_assoc;
  try tauto.
  rewrite C7C8.
  rewrite ghplus_comm;
  try tauto.
  apply ghpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  }

  assert (bgp8m: boundgh (ghplus C8 Cm)).
  {
  apply boundgh_mon with C7;
  try tauto.
  rewrite ghplus_comm;
  try tauto.
  apply ghpdef_comm;
  try tauto.
  }


  exists p7, (phplus p8 pm).
  exists phpdefp7p8m, bp7, bp8m, bp7p8m.
  exists o7, o8, C7, (ghplus C8 Cm).
  exists ghpdefp7p8m, BC7, bgp8m, bgp7p8m, opo7o8.
  split.
  assumption.
  split.
  destruct tmp8 as (p9,(p0,(phpdefp9p0,(bp9,(bp0,(bp90,(o9,(o0,(C9,(C0,(ghpdefC9C0,(BC9,(BC0,(BC9C0,(opo9o0,(tmp110,(tmp18,(p9p0,C9C0)))))))))))))))))).

  assert (phpdefpm9pm0: phplusdef pm p9 /\ phplusdef pm p0).
  {
  apply phpdef_dist';
  try tauto.
  rewrite p9p0.
  tauto.
  }

  assert (phpdefp90m: phplusdef p9 (phplus p0 pm)).
  {
  apply phpdef_pair;
  try tauto.
  apply phpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  }

  assert (bpmp8: boundph (phplus pm p8)).
  {
  apply boundph_mon with p7;
  try tauto.
  rewrite phplus_assoc;
  try tauto.
  replace (phplus p8 p7) with (phplus p7 p8).
  rewrite p7p8.
  tauto.
  apply phplus_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  }

  assert (bp9p0m : boundph (phplus p9 (phplus p0 pm))).
  {
  rewrite <- phplus_assoc;
  try tauto.
  rewrite p9p0.
  rewrite phplus_comm;
  try tauto.
  apply phpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  }

  assert (bp0m: boundph (phplus p0 pm)).
  {
  apply boundph_mon with p9;
  try tauto.
  rewrite phplus_comm;
  try tauto.
  apply phpdef_comm;
  try tauto.
  }

  assert (ghpdefpm9pm0: ghplusdef Cm C9 /\ ghplusdef Cm C0).
  {
  apply ghpdef_dist';
  try tauto.
  rewrite C9C0.
  tauto.
  }

  assert (ghpdefp90m: ghplusdef C9 (ghplus C0 Cm)).
  {
  apply ghpdef_pair;
  try tauto.
  apply ghpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  }

  assert (bgpmp8: boundgh (ghplus Cm C8)).
  {
  apply boundgh_mon with C7;
  try tauto.
  rewrite ghplus_assoc;
  try tauto.
  replace (ghplus C8 C7) with (ghplus C7 C8).
  rewrite C7C8.
  tauto.
  apply ghplus_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  }

  assert (bgp9p0m : boundgh (ghplus C9 (ghplus C0 Cm))).
  {
  rewrite <- ghplus_assoc;
  try tauto.
  rewrite C9C0.
  rewrite ghplus_comm;
  try tauto.
  apply ghpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  }

  assert (bgp0m: boundgh (ghplus C0 Cm)).
  {
  apply boundgh_mon with C9;
  try tauto.
  rewrite ghplus_comm;
  try tauto.
  apply ghpdef_comm;
  try tauto.
  }

  assert (bp0pm: boundph (phplus p0 pm)).
  {
  rewrite phplus_comm;
  try tauto.
  apply boundph_mon with p9;
  try tauto.
  rewrite phplus_assoc;
  try tauto.
  replace (phplus p0 p9) with (phplus p9 p0).
  rewrite p9p0.
  tauto.
  apply phplus_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  }

  assert (bgp0pm: boundgh (ghplus C0 Cm)).
  {
  rewrite ghplus_comm;
  try tauto.
  apply boundgh_mon with C9;
  try tauto.
  rewrite ghplus_assoc;
  try tauto.
  replace (ghplus C0 C9) with (ghplus C9 C0).
  rewrite C9C0.
  tauto.
  apply ghplus_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  }


  exists p9, (phplus p0 pm), phpdefp90m, bp9, bp0m, bp9p0m.
  exists o9, o0, C9, (ghplus C0 Cm).
  exists ghpdefp90m, BC9, bgp0m, bgp9p0m, opo9o0.
  split.
  tauto.
  split.
  exists p0, pm.
  exists.
  apply phpdef_comm; tauto.
  exists bp0, BPm, bp0pm.
  exists o0, None, C0, Cm.
  exists.
  apply ghpdef_comm; tauto.
  exists BC0, BCm, bgp0pm.
  exists.
  destruct o0.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  tauto.
  rewrite <- phplus_assoc;
  try tauto.
  rewrite p9p0.
  rewrite <- ghplus_assoc;
  try tauto.
  rewrite C9C0.
  tauto.
  apply ghpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  rewrite <- phplus_assoc;
  try tauto.
  rewrite p7p8.
  rewrite <- ghplus_assoc;
  try tauto.
  rewrite C7C8.
  rewrite phplus_comm;
  try tauto.
  rewrite ghplus_comm;
  try tauto.
  apply ghpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  rewrite <- phplus_assoc;
  try tauto.
  rewrite p1p2.
  rewrite <- ghplus_assoc;
  try tauto.
  rewrite C1C2.
  tauto.
Qed.

Lemma sat_g_ctrinc:
  forall p O C gc tx invs (BP: boundph p) (BC: boundgh C)
        (SAT: sat p O C (weakest_pre_ct (g_ctrinc gc, tx) invs)),
    exists t m
      (Cgc: C ([[gc]]) = Some (Some t, m)),
      sat p O (upd Z.eq_dec C ([[gc]]) (Some (Some (S t), S m))) (weakest_pre_ct (tt, tx) invs).
Proof.
  unfold weakest_pre_ct.
  simpl.
  intros.
  destruct SAT as (v,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,((n,C1gc),(tmp2,(p1p2,C1C2))))))))))))))))))).
  subst.
  unfold id in *.

  assert (le: le n v).
  {
  apply BC1 with ([[gc]]).
  assumption.
  }

  assert (buc1: boundgh (upd Z.eq_dec C1 ([[gc]]) (Some (Some (S v), S n)))).
  {
  unfold boundgh.
  unfold upd.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  inversion H.
  omega.
  apply BC1 with x.
  assumption.
  }

  assert (ghpdefC2C1: ghplusdef C2 C1).
  {
  repeat php_.
  }

  assert (ghpdefc2uc1: ghplusdef C2 (upd Z.eq_dec C1 ([[gc]]) (Some (Some (S v), S n)))).
  {
  unfold ghplusdef.
  unfold upd.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e in *.
  destruct (C2 ([[gc]])) eqn:C2gc.
  destruct p.
  destruct o.
  unfold ghplusdef in ghpdefC1C2.
  specialize ghpdefC1C2 with ([[gc]]).
  rewrite C1gc in ghpdefC1C2.
  rewrite C2gc in ghpdefC1C2.
  contradiction.
  trivial.
  trivial.
  apply ghpdefC2C1.
  }

  assert (bc2c1: boundgh (ghplus C2 C1)).
  {
  rewrite ghplus_comm; repeat php_.
  }

  assert (bC2uC1: boundgh (ghplus C2 (upd Z.eq_dec C1 ([[gc]]) (Some (Some (S v), S n))))).
  {
  unfold boundgh.
  unfold upd.
  unfold ghplus.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e in *.
  destruct (C2 ([[gc]])) eqn:C2gc.
  destruct p.
  destruct o.
  unfold ghplusdef in ghpdefC1C2.
  specialize ghpdefC1C2 with ([[gc]]).
  rewrite C1gc in ghpdefC1C2.
  rewrite C2gc in ghpdefC1C2.
  contradiction.
  inversion H.
  assert (G: ((n + n1)%nat <= v)%nat).
  {
  apply bc12 with ([[gc]]).
  unfold ghplus.
  rewrite C1gc, C2gc.
  reflexivity.
  }
  omega.
  inversion H.
  omega.
  apply bc2c1 with x.
  assumption.
  }

  assert (ghpdefuc1: ghplusdef (upd Z.eq_dec C1 ([[gc]]) (Some (Some (S v), 0%nat)))
    (upd Z.eq_dec (emp (option nat * nat)) ([[gc]]) (Some (None, S n)))).
  {
  unfold ghplusdef.
  unfold upd.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  trivial.
  unfold emp.
  destruct (C1 x); trivial.
  destruct p.
  destruct o; trivial.
  }

  assert (buc1': boundgh (upd Z.eq_dec C1 ([[gc]]) (Some (Some (S v), 0%nat)))).
  {
  unfold boundgh.
  unfold upd.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  inversion H.
  omega.
  apply BC1 with x.
  assumption.
  }

  assert (bue: boundgh(upd Z.eq_dec (emp (option nat * nat)) ([[gc]]) (Some (None, S n)))).
  {
  unfold boundgh.
  unfold upd.
  unfold emp.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  inversion H.
  inversion H.
  }

  assert (buc1ue: boundgh (ghplus (upd Z.eq_dec C1 ([[gc]]) (Some (Some (S v), 0%nat)))
    (upd Z.eq_dec (emp (option nat * nat)) ([[gc]]) (Some (None, S n))))).
  {
  unfold boundgh.
  unfold upd.
  unfold emp.
  unfold ghplus.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  inversion H.
  omega.
  destruct (C1 x) eqn:C1x.
  destruct p.
  apply BC1 with x.
  symmetry in H.
  inversion H.
  rewrite H1.
  assumption.
  inversion H.
  }


  destruct (C2 ([[gc]])) eqn:C2gc.
  {
  destruct p.
  destruct o.
  {
  unfold ghplusdef in ghpdefC1C2.
  specialize ghpdefC1C2 with ([[gc]]).
  rewrite C1gc in ghpdefC1C2.
  rewrite C2gc in ghpdefC1C2.
  contradiction.
  }

  exists v, (n+n0)%nat.
  exists.
  unfold ghplus.
  rewrite C1gc, C2gc.
  reflexivity.
  rewrite phplus_comm; repeat php_.
  assert (EQC: upd Z.eq_dec (ghplus C1 C2) ([[gc]]) (Some (Some (S v), S (n + n0))) = 
    ghplus C2 (upd Z.eq_dec C1 ([[gc]]) (Some (Some (S v), S n)))).
  {
  unfold upd.
  unfold ghplus.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e.
  rewrite C2gc.
  replace (S (n + n0)) with (n0 + S n)%nat.
  reflexivity.
  omega.

  destruct (C1 x) eqn:C1x.
  destruct p.

  destruct (C2 x) eqn:C2x.
  destruct p.

  assert (exco0o3: exc_op o o0).
  {
  eapply exc_ghpdef.
  apply ghpdefC1C2.
  apply C1x.
  apply C2x.
  }

  rewrite lift_comm.
  replace (n2 + n3)%nat with (n3 + n2)%nat.
  reflexivity.
  omega.
  assumption.
  reflexivity.

  destruct (C2 x) eqn:C2x.
  destruct p.
  reflexivity.
  reflexivity.
  }

  rewrite EQC.
  apply tmp2 with o1; repeat php_.
  apply oplus_comm.
  assumption.
  exists p1, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o1, None.
  exists (upd Z.eq_dec C1 ([[gc]]) (Some (Some (S v), 0%nat))).
  exists (upd Z.eq_dec (emp (option nat*nat)) ([[gc]]) (Some (None, S n))).
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists.
  destruct o1.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  exists.
  exists 0%nat.
  unfold upd.
  rewrite eqz.
  reflexivity.
  exists.
  exists n.
  unfold upd.
  rewrite eqz.
  reflexivity.
  split.
  php_.
  unfold ghplus.
  unfold upd.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  reflexivity.
  unfold emp.
  destruct (C1 x) eqn:C1x.
  destruct p.
  reflexivity.
  reflexivity.
  }

  exists v, n.
  exists.
  unfold ghplus.
  rewrite C1gc, C2gc.
  reflexivity.
  rewrite phplus_comm; repeat php_.

  assert (EQC: upd Z.eq_dec (ghplus C1 C2) ([[gc]]) (Some (Some (S v), S n)) = 
    ghplus C2 (upd Z.eq_dec C1 ([[gc]]) (Some (Some (S v), S n)))).
  {
  unfold upd.
  unfold ghplus.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e.
  rewrite C2gc.
  reflexivity.

  destruct (C1 x) eqn:C1x.
  destruct p.

  destruct (C2 x) eqn:C2x.
  destruct p.

  assert (exco0o3: exc_op o o0).
  {
  eapply exc_ghpdef.
  apply ghpdefC1C2.
  apply C1x.
  apply C2x.
  }

  rewrite lift_comm.
  replace (n1 + n2)%nat with (n2 + n1)%nat.
  reflexivity.
  omega.
  assumption.
  reflexivity.

  destruct (C2 x) eqn:C2x.
  destruct p.
  reflexivity.
  reflexivity.
  }

  rewrite EQC.
  apply tmp2 with o1; repeat php_.
  apply oplus_comm.
  assumption.
  exists p1, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o1, None.
  exists (upd Z.eq_dec C1 ([[gc]]) (Some (Some (S v), 0%nat))).
  exists (upd Z.eq_dec (emp (option nat*nat)) ([[gc]]) (Some (None, S n))).
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists.
  destruct o1.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  exists.
  exists 0%nat.
  unfold upd.
  rewrite eqz.
  reflexivity.
  exists.
  exists n.
  unfold upd.
  rewrite eqz.
  reflexivity.
  split.
  php_.
  unfold ghplus.
  unfold upd.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  reflexivity.
  unfold emp.
  destruct (C1 x) eqn:C1x.
  destruct p.
  reflexivity.
  reflexivity.
Qed.

Lemma sat_g_ctrdec:
  forall p O C gc tx invs (BP: boundph p) (BC: boundgh C)
        (SAT: sat p O C (weakest_pre_ct (g_ctrdec gc, tx) invs)),
    exists t m
      (Cgc: C ([[gc]]) = Some (Some (S t),S m)),
      sat p O (upd Z.eq_dec C ([[gc]]) (Some (Some t,m))) (weakest_pre_ct (tt, tx) invs).
Proof.
  unfold weakest_pre_ct.
  simpl.
  intros.
  destruct SAT as (v,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,((n,C1gc),(tmp2,(p1p2,C1C2))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4)))))))))))))))))).

  rewrite <- C1C2.
  rewrite <- C3C4.
  unfold id in *.
  destruct tmp4 as (n',C3gc).
  unfold ghplus at 1 2 3 4.
  rewrite C1gc.
  rewrite C3gc.

  subst.

  assert (ghpdefc13c14: ghplusdef C1 C3 /\ ghplusdef C1 C4).
  {
  apply ghpdef_dist'; repeat php_.
  }
  destruct ghpdefc13c14 as (ghpdefc13,ghpdefc14).

  assert (bc1c3: boundgh (ghplus C1 C3)).
  {
  apply boundgh_mon with C4; repeat php_.
  }

  assert (bc1c4: boundgh (ghplus C1 C4)).
  {
  apply boundgh_mon with C3; repeat php_.
  rewrite ghplus_assoc; repeat php_.
  replace (ghplus C4 C3) with (ghplus C3 C4); repeat php_.
  }

  assert (vv': exists v', v = S v').
  {
  assert (G: le (n + S n')%nat v%nat).
  {
  unfold boundgh in bc1c3.
  apply bc1c3 with ([[gc]]).
  unfold ghplus.
  rewrite C3gc.
  rewrite C1gc.
  reflexivity.
  }
  exists (v-1)%nat.
  omega.
  }

  destruct vv' as (v',eqv).
  rewrite eqv.
  unfold lift'.

  assert (phpdefp13p14: phplusdef p1 p3 /\ phplusdef p1 p4).
  {
  repeat php_.
  }

  assert (eqh1: phplus p4 (phplus p1 p3) = phplus p1 (phplus p3 p4)).
  {
  rewrite phplus_comm; repeat php_.
  }

  assert (bp4p13: boundph (phplus p4 (phplus p1 p3))).
  {
  rewrite eqh1.
  assumption.
  }

  assert (le1: le (n + n') v').
  {
  assert (G: le (n + S n') (S v')).
  {
  unfold boundgh in bc1c3.
  apply bc1c3 with ([[gc]]).
  unfold ghplus.
  rewrite C1gc.
  rewrite C3gc.
  rewrite eqv.
  reflexivity.
  }
  omega.
  }

  assert (buc13: boundgh (upd Z.eq_dec (ghplus C1 C3) ([[gc]]) (Some (Some v', (n + n')%nat)))).
  {
  unfold boundgh.
  unfold upd.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  inversion H.
  rewrite <- H1.
  assumption.
  unfold boundgh in bc1c3.
  apply bc1c3 with x.
  assumption.
  }

  assert (ghpdefC4C13: ghplusdef C4 (ghplus C1 C3)).
  {
  repeat php_.
  }

  assert (ghpdefc4uc13: ghplusdef C4 (upd Z.eq_dec (ghplus C1 C3) ([[gc]]) (Some (Some v', (n + n')%nat)))).
  {
  unfold ghplusdef.
  unfold upd.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e in *.
  destruct (C4 ([[gc]])) eqn:C4gc.
  destruct p.
  destruct o.
  unfold ghplusdef in ghpdefc14.
  specialize ghpdefc14 with ([[gc]]).
  rewrite C4gc in ghpdefc14.
  rewrite C1gc in ghpdefc14.
  contradiction.
  trivial.
  trivial.
  apply ghpdefC4C13.
  }

  assert (bc4c13: boundgh (ghplus C4 (ghplus C1 C3))).
  {
  rewrite ghplus_comm; repeat php_.
  }

  assert (bgc4uc13: boundgh (ghplus C4 (upd Z.eq_dec (ghplus C1 C3) ([[gc]]) (Some (Some v', (n + n')%nat))))).
  {
  unfold boundgh.
  unfold ghplus.
  unfold upd.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e in *.
  destruct (C4 ([[gc]])) eqn:C4gc.
  destruct p.
  destruct o.
  unfold ghplusdef in ghpdefc14.
  specialize ghpdefc14 with ([[gc]]).
  rewrite C4gc in ghpdefc14.
  rewrite C1gc in ghpdefc14.
  contradiction.
  inversion H.
  rewrite <- H1.
  assert (G: le (n + (S n' + n1)) v).
  {
  unfold boundgh in bc12.
  apply bc12 with ([[gc]]).
  unfold ghplus.
  rewrite C1gc, C3gc, C4gc.
  reflexivity.
  }
  omega.
  inversion H.
  omega.
  unfold boundgh in bc4c13.
  apply bc4c13 with x.
  assumption.
  }

  assert (exo'': exists o'', oplus O4 o'' O).
  {
  destruct o2.
  exists O3.
  apply oplus_comm.
  inversion opO1O2.
  apply oplus_trans with l; assumption.
  exists o1.
  inversion opO3O4.
  inversion opO1O2.
  apply None_op.
  apply sn_op.
  assumption.
  }
  destruct exo'' as (o'',opo'').

  destruct (C4 ([[gc]])) eqn:C4gc.
  destruct p.
  {
  destruct o.
  {
  unfold ghplusdef in ghpdefc14.
  specialize ghpdefc14 with ([[gc]]).
  rewrite C1gc in ghpdefc14.
  rewrite C4gc in ghpdefc14.
  contradiction.
  }

  exists v', (n + n' + n0)%nat.
  exists.
  assert (eq1: (n + (S n' + n0))%nat = S (n + n' + n0)).
  omega.
  rewrite eq1.
  reflexivity.

  assert (EQC: upd Z.eq_dec (ghplus C1 (ghplus C3 C4)) ([[gc]])
    (Some (Some v', (n + n' + n0)%nat)) =
    ghplus C4 (upd Z.eq_dec (ghplus C1 C3) ([[gc]]) (Some (Some v',(n+n')%nat)))).
  {
  unfold upd.
  unfold ghplus.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e.
  rewrite C4gc.
  replace (n + n' + n0)%nat with (n0 + (n + n'))%nat.
  reflexivity.
  omega.
  destruct (C1 x) eqn:C1x.
  destruct p.
  destruct (C3 x) eqn:C3x.
  destruct p.

  assert (excoo0: exc_op o o0).
  {
  eapply exc_ghpdef.
  apply ghpdefc13.
  apply C1x.
  apply C3x.
  }

  destruct (C4 x) eqn:C4x.
  destruct p.

  assert (excoo3: exc_op o o3).
  {
  eapply exc_ghpdef.
  apply ghpdefc14.
  apply C1x.
  apply C4x.
  }

  assert (exco0o3: exc_op o0 o3).
  {
  eapply exc_ghpdef.
  apply ghpdefC3C4.
  apply C3x.
  apply C4x.
  }

  rewrite <- lift_assoc.
  rewrite lift_comm.
  replace (n2 + (n3 + n4))%nat with (n4 + (n2 + n3))%nat.
  reflexivity.
  omega.
  apply exc_dist; assumption.
  reflexivity.
  destruct (C4 x) eqn:C4x.
  destruct p.

  assert (exco0o3: exc_op o o0).
  {
  eapply exc_ghpdef.
  apply ghpdefc14.
  apply C1x.
  apply C4x.
  }

  rewrite lift_comm.
  replace (n2 + n3)%nat with (n3 + n2)%nat.
  reflexivity.
  omega.
  assumption.
  reflexivity.

  destruct (C3 x) eqn:C3x.
  destruct p.
  destruct (C4 x) eqn:C4x.
  destruct p.

  assert (exco0o3: exc_op o o0).
  {
  eapply exc_ghpdef.
  apply ghpdefC3C4.
  apply C3x.
  apply C4x.
  }
  rewrite lift_comm.
  replace (n2 + n3)%nat with (n3 + n2)%nat.
  reflexivity.
  omega.
  assumption.
  reflexivity.
  destruct (C4 x) eqn:C4x.
  destruct p.
  reflexivity.
  reflexivity.
  }

  rewrite EQC.

  replace (phplus p1 (phplus p3 p4)) with (phplus p4 (phplus p1 p3)); repeat php_.

  apply tmp5 with o''; repeat php_.
  exists (n+n')%nat.
  unfold upd.
  rewrite eqz.
  rewrite eqv.
  replace (S v' - 1)%nat with v'.
  reflexivity.
  omega.
  }


  exists v', (n + n')%nat.
  exists.
  replace (n + S n')%nat with (S (n + n')).
  reflexivity.
  omega.

  assert (EQC: upd Z.eq_dec (ghplus C1 (ghplus C3 C4)) ([[gc]])
    (Some (Some v', (n + n')%nat)) =
    ghplus C4 (upd Z.eq_dec (ghplus C1 C3) ([[gc]]) (Some (Some v',(n+n')%nat)))).
  {
  unfold upd.
  unfold ghplus.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x ([[gc]])).
  rewrite e.
  rewrite C4gc.
  reflexivity.
  destruct (C1 x) eqn:C1x.
  destruct p.
  destruct (C3 x) eqn:C3x.
  destruct p.

  assert (excoo0: exc_op o o0).
  {
  eapply exc_ghpdef.
  apply ghpdefc13.
  apply C1x.
  apply C3x.
  }

  destruct (C4 x) eqn:C4x.
  destruct p.

  assert (excoo3: exc_op o o3).
  {
  eapply exc_ghpdef.
  apply ghpdefc14.
  apply C1x.
  apply C4x.
  }

  assert (exco0o3: exc_op o0 o3).
  {
  eapply exc_ghpdef.
  apply ghpdefC3C4.
  apply C3x.
  apply C4x.
  }

  rewrite <- lift_assoc.
  rewrite lift_comm.
  replace (n1 + (n2 + n3))%nat with (n3 + (n1 + n2))%nat.
  reflexivity.
  omega.
  apply exc_dist; assumption.
  reflexivity.
  destruct (C4 x) eqn:C4x.
  destruct p.

  assert (exco0o3: exc_op o o0).
  {
  eapply exc_ghpdef.
  apply ghpdefc14.
  apply C1x.
  apply C4x.
  }

  rewrite lift_comm.
  replace (n1 + n2)%nat with (n2 + n1)%nat.
  reflexivity.
  omega.
  assumption.
  reflexivity.

  destruct (C3 x) eqn:C3x.
  destruct p.
  destruct (C4 x) eqn:C4x.
  destruct p.

  assert (exco0o3: exc_op o o0).
  {
  eapply exc_ghpdef.
  apply ghpdefC3C4.
  apply C3x.
  apply C4x.
  }
  rewrite lift_comm.
  replace (n1 + n2)%nat with (n2 + n1)%nat.
  reflexivity.
  omega.
  assumption.
  reflexivity.
  destruct (C4 x) eqn:C4x.
  destruct p.
  reflexivity.
  reflexivity.
  }

  rewrite EQC.

  replace (phplus p1 (phplus p3 p4)) with (phplus p4 (phplus p1 p3)); repeat php_.

  apply tmp5 with o''; repeat php_.
  exists (n+n')%nat.
  unfold upd.
  rewrite eqz.
  rewrite eqv.
  replace (S v' - 1)%nat with v'.
  reflexivity.
  omega.
Qed.

Lemma sat_g_newctr:
  forall p O C gc tx invs (BP: boundph p) (BC: boundgh C)
        (Cgc: C gc = None)
        (SAT: sat p O C (weakest_pre_ct (g_newctr, tx) invs)),
      sat p O (upd Z.eq_dec C gc (Some (Some 0%nat,0%nat))) (weakest_pre_ct (tt, tx) invs).
Proof.
  unfold weakest_pre_ct.
  unfold boundgh.
  simpl.
  intros.
  replace p with (phplus p (emp knowledge)).
  replace (upd Z.eq_dec C gc (Some (Some 0%nat, 0%nat))) with
    (ghplus C (upd Z.eq_dec (emp (option nat*nat)) gc (Some (Some 0%nat, 0%nat)))).
  apply SAT with gc None; repeat php_.
  apply boundgh_upd; repeat php_.
  intros.
  inversion H.
  omega.
  apply ghpdef_comm.
  apply ghpdef_v; repeat php_.
  {
  unfold ghplus.
  unfold boundgh.
  unfold upd.
  unfold emp.
  intros.
  destruct (C x) eqn:Cx.
  destruct p0.
  destruct (Z.eq_dec x gc).
  rewrite e in Cx.
  rewrite Cgc in Cx.
  inversion Cx.
  eapply BC with x.
  symmetry in H.
  inversion H.
  rewrite H1.
  assumption.
  destruct (Z.eq_dec x gc).
  inversion H.
  omega.
  inversion H.
  }
  destruct O.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  exists 0%nat.
  repeat dstr_.
  apply functional_extensionality.
  intros.
  unfold upd.
  unfold ghplus.
  destruct (Z.eq_dec x gc).
  rewrite e.
  rewrite Cgc.
  reflexivity.
  unfold emp.
  destruct (C x) eqn:Cx;
  try destruct p0;
  try reflexivity.
  php_.
Qed.

Lemma sat_release:
  forall p O C l tx invs
        (SAT: sat p (Some O) C (weakest_pre_ct (Release l, tx) invs)),
    exists ll p1 p2 wt ot C1 C2 O1
           (EQl: Aof ll = ([[l]]))
           (OO1: Permutation O (ll :: O1))
           (BP1: boundph p1)
           (BP2: boundph p2)
           (BC1: boundgh C1)
           (BC2: boundgh C2)
           (phpdp1p2: phplusdef p1 p2)
           (ghpdc1c2: ghplusdef C1 C2)
           (p1p2: p = phplus p1 p2)
           (C1C2: C = ghplus C1 C2) 
           (P1l: p1 ll = Some (Locked wt ot))
           (p2inv: sat p2 None C2 (subsas (snd (Iof ll)) (invs (fst (Iof ll)) wt ot))),
    sat (upd location_eq_dec p1 ll (Some Lock)) (Some O1) C1 (weakest_pre_ct (tt, tx) invs).
Proof.
  intros.
  simpl in SAT.
  destruct SAT as (v,(v0,(v1,(v2,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,((eq1,tmp1),(tmp2,(p1p2,C1C2)))))))))))))))))))))).
  destruct tmp1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, p3p4))))))))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp6,(tmp7, p5p6))))))))))))))))).
  cnj_.
  subst.

  unfold id in *.
  apply Z.eqb_eq in eq1.
  symmetry in eq1.
  assert (tmp: Permutation O (evall v0 :: map evall v) /\ O6 = None /\ o2 = None).
  {
  inversion tmp4.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  rewrite <- H4 in opO1O2.
  inversion opO1O2.
  split.
  apply Permutation_sym.
  apply Permutation_trans with o'.
  assumption.
  apply Permutation_trans with o'0.
  assumption.
  assumption.
  rewrite <- H3 in opO5O6.
  inversion opO5O6.
  tauto.
  }
  destruct tmp as (PERM,(o6n,o2n)).
  rewrite o6n, o2n in *.


  assert (phpdp3p52: phplusdef p3 (phplus p5 p6)). repeat php_.
  assert (phpdp35p36: phplusdef p3 p5 /\ phplusdef p3 p6). repeat php_.
  assert (ghpdp3p52: ghplusdef C3 (ghplus C5 C6)). repeat php_.
  assert (ghpdp35p36: ghplusdef C3 C5 /\ ghplusdef C3 C6). repeat php_.
  assert (phpdp32p562: phplusdef p3 p2 /\ phplusdef (phplus p5 p6) p2). apply phpdef_dist; try tauto.
  assert (ghpdp32p562: ghplusdef C3 C2 /\ ghplusdef (ghplus C5 C6) C2). apply ghpdef_dist; try tauto.
  assert (phpdp52p62: phplusdef p5 p2 /\ phplusdef p6 p2). apply phpdef_dist; try tauto.
  assert (ghpdp52p62: ghplusdef C5 C2 /\ ghplusdef C6 C2). apply ghpdef_dist; try tauto.
  assert (phpdefp53: phplusdef p3 p5 /\ phplusdef p3 p6). repeat php_. cnj_.
  assert (phpd23: phplusdef p2 p3). repeat php_.
  assert (phpd55p2: phplusdef p3 p2 /\ phplusdef (phplus p5 p6) p2). repeat php_.
  assert (phpd25: phplusdef p2 p5). repeat php_.

  assert (eqh1: phplus (phplus p3 (phplus p5 p6)) p2 = phplus (phplus p2 (phplus p3 p5)) p6). rewrite phplus_comm; repeat php_.
  assert (eqg1: ghplus (ghplus C3 (ghplus C5 C6)) C2 = ghplus (ghplus C2 (ghplus C3 C5)) C6). rewrite ghplus_comm; repeat php_.
  assert (bp35: boundph (phplus p3 p5)). apply boundph_mon with p6; try tauto. rewrite phplus_assoc; repeat php_.
  assert (bp2p35: boundph (phplus p2 (phplus p3 p5))). 
  apply boundph_mon with p6; try tauto.
  rewrite <- eqh1. assumption.
  assert (ghpd23: ghplusdef C2 C3). repeat php_.
  assert (ghpd55p2: ghplusdef C3 C2 /\ ghplusdef (ghplus C5 C6) C2). repeat php_. cnj_.
  assert (ghpd25: ghplusdef C2 C5). repeat php_.
  assert (bp53: boundph (phplus p5 p3)). rewrite phplus_comm; repeat php_.


  assert (bp43p2p5: boundph (phplus (phplus (phplus p5 p3) p2) p6)).
  {
  replace (phplus (phplus p5 p3) p2) with (phplus p2 (phplus p3 p5)).
  rewrite <- eqh1.
  assumption.
  repeat php_.
  }

  assert (bp3p2: boundph (phplus (phplus p5 p3) p2)).
  {
  apply boundph_mon with p6; try tauto.
  }

  assert (bpu: boundph (upd location_eq_dec p5 (evall v0) (Some Lock))).
  {
  apply boundph_upd.
  assumption.
  intros f CO.
  destruct CO as (z',CO).
  inversion CO.
  }

  assert (phpdp3p5u: phplusdef p3 (upd location_eq_dec p5 (evall v0) (Some Lock))).
  {
  apply phpdef_comm.
  apply phpdef_locked_lock.
  repeat php_.
  exists v1, v2.
  tauto.
  }

  assert (phpdp2p5u: phplusdef p2 (upd location_eq_dec p5 (evall v0) (Some Lock))).
  {
  apply phpdef_comm.
  apply phpdef_locked_lock.
  repeat php_.
  exists v1, v2.
  tauto.
  }

  assert (bp35u: boundph (phplus p3 (upd location_eq_dec p5 (evall v0) (Some Lock)))).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1',(v2',(CO,rest))).
  inversion CO.
  }

  assert (eqh2: phplus p3 (upd location_eq_dec p5 (evall v0) (Some Lock)) = 
                upd location_eq_dec (phplus p5 p3) (evall v0) (Some Lock)).
  {
  rewrite phplus_comm.
  apply phplus_upd.
  unfold not.
  intros CO.
  destruct CO as (v',(f',(v'',(f'',(CO,rest))))).
  inversion CO.
  intros.
  unfold not.
  intros CO.
  destruct CO as (wt,(ot,p3v0)).
  unfold phplusdef in phpdp35p36_1.
  specialize phpdp35p36_1 with (evall v0).
  rewrite p3v0 in phpdp35p36_1.
  rewrite tmp6 in phpdp35p36_1.
  contradiction.
  intros.
  inversion H.
  repeat php_.
  }

  assert (p43locked: phplus p5 p3 (evall v0) = Some (Locked v1 v2)).
  {
  apply phplus_locked.
  repeat php_.
  assumption.
  }

  assert (phpdefp2p43u: phplusdef p2 (upd location_eq_dec (phplus p5 p3) (evall v0) (Some Lock))).
  {
  apply phpdef_comm.
  apply phpdef_locked_lock.
  apply phpdef_pair'; repeat php_.
  exists v1, v2.
  tauto.
  }

  assert (bp2p35u: boundph (phplus p2 (phplus p3 (upd location_eq_dec p5 (evall v0) (Some Lock))))).
  {
  rewrite eqh2.
  rewrite phplus_comm.
  apply boundph_phplus_upd; try tauto.
  apply phpdef_pair'; repeat php_.
  repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1',(v2',(CO,rest))).
  inversion CO.
  tauto.
  }

  exists (evall v0), (phplus p2 (phplus p3 p5)), p6, v1, v2, (ghplus C2 (ghplus C3 C5)), C6, (map evall v).
  exists eq1, PERM, bp2p35, bp6.
  exists. apply boundgh_mon with C6. rewrite <- eqg1. assumption.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  rewrite phplus_comm; repeat php_.
  apply phplus_locked; repeat php_.
  rewrite phplus_comm; repeat php_.
  exists. assumption.
  unfold weakest_pre_ct.
  simpl.
  assert (G: sat (phplus p2 (phplus p3 (upd location_eq_dec p5 (evall v0) (Some Lock)))) (Some (map evall v)) (ghplus C2 (ghplus C3 C5))
    (weakest_pre_tx tx invs 0)).
  {
  apply tmp2 with (Some (map evall v)); repeat php_.
  apply boundgh_mon with C6.
  rewrite <- eqg1. assumption.
  apply sn_op.
  apply Permutation_refl.
  exists p3, (upd location_eq_dec p5 (evall v0) (Some Lock)).
  exists. repeat php_.
  exists. repeat php_.
  exists. assumption.
  exists. repeat php_.
  exists (Some (map evall v)), None, C3, C5.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply boundgh_mon with C6.
  rewrite ghplus_assoc; repeat php_.
  exists. apply fs_op. apply Permutation_refl.
  exists. apply fs_op. apply Permutation_refl.
  exists. left. repeat dstr_.
  tauto.
  }
  replace (upd location_eq_dec (phplus p2 (phplus p3 p5)) (evall v0) (Some Lock)) with
    (phplus p2 (phplus p3 (upd location_eq_dec p5 (evall v0) (Some Lock)))).
  assumption.
  rewrite <- phplus_assoc; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  rewrite phplus_comm; repeat php_.
  rewrite phplus_upd; repeat php_.
  rewrite phplus_comm; repeat php_.
  unfold not.
  intros.
  destruct H as (v',(f',(v'',(f'',(CO,rest))))).
  inversion CO.
  unfold not.
  intros.
  destruct H0 as (wt,(ot,p23v)).
  assert (phpdefp23p5: phplusdef (phplus p2 p3) p5). repeat php_.
  unfold phplusdef in phpdefp23p5.
  specialize phpdefp23p5 with (evall v0).
  rewrite p23v in phpdefp23p5.
  rewrite tmp6 in phpdefp23p5.
  contradiction.
  intros.
  inversion H.
Qed.

Lemma sat_initl:
  forall p O C e tx invs
        (INJ: injph p)
        (SAT: sat p (Some O) C (weakest_pre_ct (g_initl e, tx) invs)),
    exists (l: location) p1 p2 wt ot C1 C2 i
           (GHPD: ghplusdef C1 C2)
           (EQl: Aof l = ([[e]]))
           (BP1: boundph p1)
           (BP2: boundph p2)
           (phpdp1p2: phplusdef p1 p2)
           (p1p2: p = phplus p1 p2)
           (C1C2: C = ghplus C1 C2) 
           (P1l: p1 l = Some (Ulock wt ot))
           (p2inv: sat p2 None C2 (subsas (snd i) (invs (fst i) wt ot))),
    sat (upd location_eq_dec (upd location_eq_dec p1 l None) (Aof l, Rof l, i, Lof l, Xof l, Mof l, Pof l) (Some Lock)) (Some O) C1 (weakest_pre_ct (tt, tx) invs).
Proof.
  intros.
  simpl in SAT.
  destruct SAT as (v,(v0,(v1,(v2,(v3,(v4,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(sat1,(sat2,(p1p2,C1C2))))))))))))))))))))))))).
  destruct sat2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(SAT,(tmp1,(p3p4,C3C4)))))))))))))))))).
  destruct tmp1 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(ops,(tmp1,(p56,C56)))))))))))))))))).
  unfold id in *.
  exists (evall v).

  assert (phpdefp14: phplusdef p1 p4).
  {
  apply phpdef_comm.
  apply phpdef_assoc_mon with p3.
  tauto.
  rewrite p3p4.
  apply phpdef_comm.
  assumption.
  }

  assert (phpdefp13: phplusdef p1 p3).
  {
  apply phpdef_comm.
  apply phpdef_assoc_mon with p4.
  apply phpdef_comm.
  tauto.
  rewrite phplus_comm.
  rewrite p3p4.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  assumption.
  }

  assert (bpp14: boundph (phplus p1 p4)).
  {
  apply boundph_mon with p3;
  try assumption.
  rewrite phplus_assoc.
  replace (phplus p4 p3) with (phplus p3 p4).
  rewrite p3p4.
  assumption.
  apply phplus_comm.
  tauto.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  }

  assert (phpdefp15: phplusdef p1 p5).
  {
  apply phpdef_comm.
  apply phpdef_assoc_mon with p6.
  apply phpdef_comm.
  assumption.
  apply phpdef_assoc_mon with p3.
  rewrite phplus_comm.
  rewrite p56.
  assumption.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  replace (phplus p6 p5) with (phplus p5 p6).
  rewrite p56.
  replace (phplus p4 p3) with (phplus p3 p4).
  rewrite p3p4.
  assumption.
  apply phplus_comm.
  assumption.
  apply phplus_comm.
  assumption.
  }

  assert (o36N: O3 = None /\ O6 = None /\ Permutation (map evall v0) O).
  {
  inversion ops.
  rewrite <- H1 in opO5O6.
  inversion opO5O6.
  rewrite <- H4 in opO3O4.
  inversion opO3O4.
  split.
  tauto.
  split.
  tauto.
  rewrite <- H5 in opO1O2.
  inversion opO1O2.
  apply Permutation_trans with o'.
  assumption.
  apply Permutation_trans with o'0.
  assumption.
  apply Permutation_trans with o'1.
  assumption.
  assumption.
  }
  destruct o36N as (o3N,(o6N,per)).
  rewrite o3N,o6N in *.

  assert (phpdefp13p14: phplusdef p1 p3 /\ phplusdef p1 p4).
  {
  apply phpdef_dist';
  try tauto.
  rewrite p3p4.
  tauto.
  }

  assert (phpdefp14p3: phplusdef (phplus p1 p4) p3).
  {
  rewrite phpdef_assoc;
  try tauto.
  replace (phplus p4 p3) with (phplus p3 p4);
  try tauto.
  rewrite p3p4.
  tauto.
  apply phplus_comm;
  try tauto.
  apply phpdef_comm.
  tauto.
  }

  assert (ghpdefc13c14: ghplusdef C1 C3 /\ ghplusdef C1 C4).
  {
  apply ghpdef_dist';
  try tauto.
  rewrite C3C4.
  tauto.
  }

  assert (ghpdefc14c3: ghplusdef (ghplus C1 C4) C3).
  {
  rewrite ghpdef_assoc;
  try tauto.
  replace (ghplus C4 C3) with (ghplus C3 C4);
  try tauto.
  rewrite C3C4.
  tauto.
  apply ghplus_comm;
  try tauto.
  apply ghpdef_comm.
  tauto.
  }

  assert (phpdefp15p16: phplusdef p1 p5 /\ phplusdef p1 p6).
  {
  apply phpdef_dist';
  try tauto.
  rewrite p56.
  tauto.
  }

  assert (phpdefp35p36: phplusdef p3 p5 /\ phplusdef p3 p6).
  {
  apply phpdef_dist'.
  rewrite p56.
  assumption.
  assumption.
  }

  assert (ghpdefC15C16: ghplusdef C1 C5 /\ ghplusdef C1 C6).
  {
  apply ghpdef_dist';
  try tauto.
  rewrite C56.
  tauto.
  }

  assert (phpdefp515u: phplusdef p6 (upd location_eq_dec (phplus p1 p5) (evall v) (Some Lock))).
  {
  apply phpdef_comm.
  apply phpdef_locked_lock.
  apply phpdef_pair';
  try tauto.
  unfold phplus.
  rewrite sat1.
  exists v1,v2.
  tauto.
  }

  assert (EQH: upd location_eq_dec (phplus p1 p4) (evall v) (Some Lock) = phplus p6 (upd location_eq_dec (phplus p1 p5) (evall v) (Some Lock))).
  {
  replace (phplus p6 (upd location_eq_dec (phplus p1 p5) (evall v) (Some Lock))) with
    (phplus (upd location_eq_dec (phplus p1 p5) (evall v) (Some Lock)) p6).
  rewrite phplus_upd;
  try tauto.
  rewrite <- p56.
  rewrite phplus_assoc;
  try tauto.
  unfold not.
  intros.
  destruct H as (v4',(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  unfold not.
  intros.
  destruct H0 as (wt,(ot,p6v)).
  destruct phpdefp15p16 as (phpdefp1p5,phpdefp16).
  unfold phplusdef in phpdefp16.
  specialize phpdefp16 with (evall v).
  rewrite p6v in phpdefp16.
  rewrite sat1 in phpdefp16.
  contradiction.
  intros.
  inversion H.
  apply phplus_comm.
  apply phpdef_comm.
  tauto.
  }

  assert (EQC: ghplus C1 C4 = ghplus C6 (ghplus C1 C5)).
  {
  rewrite <- C56.
  rewrite <- ghplus_assoc;
  try tauto.
  rewrite ghplus_comm;
  try tauto.
  apply ghpdef_pair';
  try tauto.
  }

  assert (bp14: boundph (phplus p1 p4)).
  {
  apply boundph_mon with p3;
  try tauto.
  rewrite phplus_assoc;
  try tauto.
  replace (phplus p4 p3) with (phplus p3 p4).
  rewrite p3p4.
  tauto.
  apply phplus_comm;
  try tauto.
  apply phpdef_comm.
  tauto.
  }

  assert (bp15: boundph (phplus p1 p5)).
  {
  apply boundph_mon with p6;
  try tauto.
  rewrite phplus_assoc;
  try tauto.
  rewrite p56.
  tauto.
  }

  assert (bp15u: boundph (upd location_eq_dec (phplus p1 p5) (evall v) (Some Lock))).
  {
  apply boundph_upd.
  tauto.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bp515: boundph (phplus p6 (upd location_eq_dec (phplus p1 p5) (evall v) (Some Lock)))).
  {
  rewrite phplus_comm.
  apply boundph_phplus_upd;
  try tauto.
  apply phpdef_pair';
  tauto.
  rewrite phplus_assoc;
  try tauto.
  rewrite p56.
  tauto.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v3',(v4',(CO,rest))).
  inversion CO.
  assumption.
  }

  assert (bg14: boundgh (ghplus C1 C4)).
  {
  apply boundgh_mon with C3;
  try tauto.
  rewrite ghplus_assoc;
  try tauto.
  replace (ghplus C4 C3) with (ghplus C3 C4).
  rewrite C3C4.
  tauto.
  apply ghplus_comm;
  try tauto.
  apply ghpdef_comm.
  tauto.
  }

  assert (bg15: boundgh (ghplus C1 C5)).
  {
  apply boundgh_mon with C6;
  try tauto.
  rewrite ghplus_assoc;
  try tauto.
  rewrite C56.
  tauto.
  }

  assert (phpdefp1u5: phplusdef (upd location_eq_dec p1 (evall v) (Some Lock)) p5).
  {
  apply phpdef_locked_lock.
  tauto.
  exists v1, v2.
  tauto.
  }

  assert (bp1u: boundph (upd location_eq_dec p1 (evall v) (Some Lock))).
  {
  apply boundph_upd;
  try tauto.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bp1up5: boundph (phplus (upd location_eq_dec p1 (evall v) (Some Lock)) p5)).
  {
  apply boundph_phplus_upd;
  try tauto.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v3',(v4',(CO,rest))).
  inversion CO.
  }

  exists (phplus p1 p4), p3, v1, v2.
  exists (ghplus C1 C4) ,C3.
  exists (v3,v4).
  exists ghpdefc14c3.
  exists.
  apply Z.eqb_eq in EQ.
  symmetry.
  assumption.
  exists bpp14, bp3.
  exists phpdefp14p3.
  exists.
  rewrite phplus_assoc;
  try tauto.
  replace (phplus p4 p3) with (phplus p3 p4);
  try tauto.
  rewrite p3p4.
  symmetry.
  tauto.
  apply phplus_comm;
  try tauto.
  apply phpdef_comm.
  tauto.
  exists.
  rewrite ghplus_assoc;
  try tauto.
  replace (ghplus C4 C3) with (ghplus C3 C4);
  try tauto.
  rewrite C3C4.
  symmetry.
  tauto.
  apply ghplus_comm;
  try tauto.
  apply ghpdef_comm.
  tauto.
  exists.
  unfold phplus.
  rewrite sat1.
  reflexivity.
  exists SAT.
  assert (p6v: p6 (evall v) = None).
  {
  destruct phpdefp15p16 as (phpdefp1p5,phpdefp16).
  unfold phplusdef in phpdefp16.
  specialize phpdefp16 with (evall v).
  rewrite sat1 in phpdefp16.
  destruct (p6 (evall v)).
  contradiction.
  reflexivity.
  }

  assert (p5v: p5 (evall v) = None).
  {
  destruct phpdefp15p16 as (phpdefp1p5,phpdefp16).
  unfold phplusdef in phpdefp15.
  specialize phpdefp15 with (evall v).
  rewrite sat1 in phpdefp15.
  destruct (p5 (evall v)).
  contradiction.
  reflexivity.
  }

  assert (pv: phplus p1 (phplus p3 (phplus p5 p6)) (evall v) = Some (Ulock v1 v2)).
  {
  apply phplus_ulock; repeat php_.
  }

  assert (p6en: p6 (evall (Aof v, Rof v, (v3, v4), Lof v, Xof v, Mof v, Pof v)) = None).
  {
  destruct (p6 (evall (Aof v, Rof v, (v3, v4), Lof v, Xof v, Mof v, Pof v))) eqn:p6e.

  assert (p1356v: phplus p1 (phplus p3 (phplus p5 p6)) (evall (Aof v, Rof v, (v3, v4), Lof v, Xof v, Mof v, Pof v)) <> None).
  {
  apply phplus_some'; repeat php_.
  apply phplus_some'; repeat php_.
  apply phplus_some'; repeat php_.
  rewrite p6e.
  apply some_none.
  }

  assert (CO: evall (Aof v, Rof v, (v3, v4), Lof v, Xof v, Mof v, Pof v) = evall v).
  {
  subst.
  apply INJ.
  assumption.
  rewrite pv.
  apply some_none.
  reflexivity.
  }
  rewrite CO in p6e.
  rewrite p6v in p6e.
  inversion p6e.
  reflexivity.
  }

  assert (p5en: p5 (evall (Aof v, Rof v, (v3, v4), Lof v, Xof v, Mof v, Pof v)) = None).
  {
  destruct (p5 (evall (Aof v, Rof v, (v3, v4), Lof v, Xof v, Mof v, Pof v))) eqn:p5e.
  assert (p1356v: phplus p1 (phplus p3 (phplus p5 p6)) (evall (Aof v, Rof v, (v3, v4), Lof v, Xof v, Mof v, Pof v)) <> None).
  {
  apply phplus_some'; repeat php_.
  apply phplus_some'; repeat php_.
  apply phplus_some; repeat php_.
  rewrite p5e.
  apply some_none.
  }
  assert (CO: evall (Aof v, Rof v, (v3, v4), Lof v, Xof v, Mof v, Pof v) = evall v).
  {
  subst.
  apply INJ.
  assumption.
  rewrite pv.
  apply some_none.
  reflexivity.
  }
  rewrite CO in p5e.
  rewrite p5v in p5e.
  inversion p5e.
  reflexivity.
  }


  assert (phpdefp6u: phplusdef p6 (upd location_eq_dec (upd location_eq_dec (phplus p1 p5) (evall v) None)
    (evall (Aof v, Rof v, (v3, v4), Lof v, Xof v, Mof v, Pof v)) (Some Lock))).
  {
  apply phpdef_comm.
  apply phpdef_v; repeat php_.
  apply phpdef_v; repeat php_.
  }

  assert (bp15u': boundph (upd location_eq_dec (upd location_eq_dec (phplus p1 p5) (evall v) None)
    (Aof (evall v), Rof (evall v), (v3, v4), Lof (evall v), Xof (evall v),
    Mof (evall v), Pof (evall v)) (Some Lock))).
  {
  apply boundph_upd.
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bC6C15: boundgh (ghplus C6 (ghplus C1 C5))).
  {
  rewrite ghplus_comm; repeat php_.
  rewrite ghplus_assoc; repeat php_.
  subst.
  assumption.
  }

  assert (EQH': upd location_eq_dec (upd location_eq_dec (phplus p1 p4) (evall v) None)
    (Aof (evall v), Rof (evall v), (v3, v4), Lof (evall v), Xof (evall v),
    Mof (evall v), Pof (evall v)) (Some Lock) =
    phplus p6 (upd location_eq_dec (upd location_eq_dec (phplus p1 p5) (evall v) None)
    (Aof (evall v), Rof (evall v), (v3, v4), Lof (evall v), Xof (evall v),
    Mof (evall v), Pof (evall v)) (Some Lock))).
  {
  subst.
  symmetry.
  rewrite phplus_comm; repeat php_.
  rewrite phplus_upd; repeat php_.
  replace (phplus (upd location_eq_dec (phplus p1 p5) (evall v) None) p6) with
    (upd location_eq_dec (phplus p1 (phplus p5 p6)) (evall v) None).
  reflexivity.
  rewrite phplus_upd; repeat php_.
  rewrite phplus_assoc; repeat php_.
  unfold not.
  intros.
  destruct H as (v0',(f',(v',(f'',(CO,rest))))).
  inversion CO.
  unfold not.
  intros.
  inversion H.
  unfold not.
  intros.
  destruct H as (v0',(f',(v',(f'',(CO,rest))))).
  inversion CO.
  unfold not.
  intros.
  destruct H0 as (wt1,(ot1,CO)).
  assert (CO1: (Aof (evall v), Rof (evall v), (v3, v4), Lof (evall v), Xof (evall v),
       Mof (evall v), Pof (evall v)) = (evall v)).
  {
  apply INJ.
  rewrite phplus_locked' with (wt:=wt1) (ot:=ot1); repeat php_.
  apply some_none.
  rewrite phplus_locked' with (wt:=wt1) (ot:=ot1); repeat php_.
  rewrite phplus_locked' with (wt:=wt1) (ot:=ot1); repeat php_.
  rewrite phplus_ulock with (wt:=v1) (ot:=v2); repeat php_.
  apply some_none.
  reflexivity.
  }

  rewrite CO1 in CO.
  rewrite p6v in CO.
  inversion CO.
  }

  assert (bp6u: boundph (phplus p6
     (upd location_eq_dec (upd location_eq_dec (phplus p1 p5) (evall v) None)
        (Aof (evall v), Rof (evall v), (v3, v4), Lof (evall v),
        Xof (evall v), Mof (evall v), Pof (evall v)) (Some Lock)))).
  {
  rewrite <- EQH'.
  apply boundph_upd.
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (phpdefu5: phplusdef (upd location_eq_dec (upd location_eq_dec p1 (evall v) None)
    (evall (Aof v, Rof v, (v3, v4), Lof v, Xof v, Mof v, Pof v)) (Some Lock)) p5).
  {
  apply phpdef_v; repeat php_.
  apply phpdef_none; repeat php_.
  }

  assert (bu1: boundph (upd location_eq_dec p1 (evall v) None)).
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (buu1: boundph (upd location_eq_dec (upd location_eq_dec p1 (evall v) None)
    (evall (Aof v, Rof v, (v3, v4), Lof v, Xof v, Mof v, Pof v)) (Some Lock))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (phpdefp1up5: phplusdef (upd location_eq_dec p1 (evall v) None) p5).
  {
  apply phpdef_v; repeat php_.
  }

  assert (bp1u5': boundph (phplus (upd location_eq_dec p1 (evall v) None) p5)).
  {
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1',(v2',(CO,rest))).
  inversion CO.
  }

  assert (bu15: boundph (phplus (upd location_eq_dec (upd location_eq_dec p1 (evall v) None)
    (evall (Aof v, Rof v, (v3, v4), Lof v, Xof v, Mof v, Pof v)) (Some Lock)) p5)).
  {
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1',(v2',(CO,rest))).
  inversion CO.
  }

  rewrite EQH'.
  rewrite EQC.
  apply tmp1 with (Some O); repeat php_.
  apply sn_op.
  apply Permutation_refl.

  exists (upd location_eq_dec (upd location_eq_dec p1 (evall v) None) (evall (Aof v, Rof v, (v3, v4), Lof v, Xof v, Mof v, Pof v)) (Some Lock)), p5.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists None, (Some O), C1, C5.
  exists.
  tauto.
  exists.
  tauto.
  exists.
  tauto.
  exists.
  tauto.
  exists.
  apply sn_op.
  apply Permutation_refl.
  split.
  left.
  unfold upd.
  destruct (location_eq_dec (evall (Aof v, Rof v, (v3, v4), Lof v, Xof v, Mof v, Pof v))
    (evall (Aof v, Rof v, (v3, v4), Lof v, Xof v, Mof v, Pof v))).
  reflexivity.
  contradiction.
  split.
  apply fs_op.
  tauto.
  split.
  rewrite phplus_upd; repeat php_.
  rewrite phplus_upd; repeat php_.
  unfold not.
  intros.
  destruct H as (v0',(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  unfold not.
  intros.
  destruct H as (v0',(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  unfold not.
  intros.
  destruct H0 as (wt,(ot,p5vn)).
  rewrite p5en in p5vn.
  inversion p5vn.
  reflexivity.
Qed.

Lemma sat_newcond:
  forall p O C tx invs v (BP: boundph p) (BC: boundgh C)
        (Pv: forall r I L X M P, p (v, r, I, L, X, M, P) = None)
        (SAT: sat p O C (weakest_pre_ct (Newcond, tx) invs)),
    exists R M params P l wt ot
           (Pl: p l = Some (Ulock wt ot)),
      sat (upd location_eq_dec p (v, R, (0%Z,nil),Aof l, Xof l, (M,params), P) (Some Cond)) O C (weakest_pre_ct (Val (Enum v), tx) invs).
Proof.
  simpl.
  intros.
  specialize SAT with v.

  destruct SAT as (R,(L,((M,params),(P,(wt,(ot,sat1)))))).
  destruct sat1 as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opO1O2,(tmp1,(tmp2,(tmp3,tmp4)))))))))))))))))).

  assert (bp1u: boundph (upd location_eq_dec p1
    (v, R, (0, nil), Aof (evall L), Xof (evall L), (M, params), P) (Some Cond))).
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (p2v: p2 (v, R, (0, nil), Aof (evall L), Xof (evall L), (M, params), P) = None).
  {
  apply phplus_none_mon with p1.
  rewrite tmp3.
  apply Pv.
  }

  assert (phpdefp2p1u: phplusdef p2 (upd location_eq_dec p1
    (v, R, (0, nil), Aof (evall L), Xof (evall L), (M, params), P) (Some Cond))).
  {
  apply phpdef_comm.
  apply phpdef_v.
  assumption.
  assumption.
  }
  assert (EQH: phplus p2 (upd location_eq_dec p1 (v, R, (0, nil), Aof (evall L), Xof (evall L), (M, params), P)
     (Some Cond)) = upd location_eq_dec (phplus p1 p2) (v, R, (0, nil), Aof (evall L), Xof (evall L), (M, params), P) (Some Cond)).
  {
  rewrite <- phplus_upd; repeat php_.
  unfold not.
  intros.
  destruct H as (v0,(f,(v',(f',(CO,rest))))).
  inversion CO.
  unfold not.
  intros.
  destruct H0 as (wt',(ot',CO)).
  rewrite p2v in CO.
  inversion CO.
  }

  assert (bp2p1u: boundph (phplus p2 (upd location_eq_dec p1
    (v, R, (0, nil), Aof (evall L), Xof (evall L), (M, params), P)(Some Cond)))).
  {
  rewrite EQH.
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  exists R, M, params, P.
  exists (evall L), wt, ot.
  subst.
  exists.
  unfold phplus.
  rewrite tmp1.
  reflexivity.
  replace (upd location_eq_dec (phplus p1 p2)
     (v, R, (0, nil), Aof (evall L), Xof (evall L), (M, params), P)
     (Some Cond)) with 
    (phplus p2 (upd location_eq_dec p1
     (v, R, (0, nil), Aof (evall L), Xof (evall L), (M, params), P)
     (Some Cond))).
  rewrite ghplus_comm; repeat php_.
  apply tmp2 with O1; repeat php_.
  apply oplus_comm.
  assumption.
  repeat dstr_.

  assert (p1nl: p1 (evall (Enum v, R, (0, nil), Aof L, Xof L, (M, params), P)) = None).
  {
  apply phplus_none_mon with p2.
  rewrite phplus_comm.
  apply Pv.
  php_.
  }

  assert (NEQ: evall L <> evall (Enum v, R, (0, nil), Aof L, Xof L, (M, params), P)).
  {
  unfold not.
  intros.
  rewrite <- H in p1nl.
  rewrite tmp1 in p1nl.
  inversion p1nl.
  }

  assert (bpu: boundph (upd location_eq_dec (emp knowledge)
    (evall (Enum v, R, (0, nil), Aof L, Xof L, (M, params), P)) (Some Cond))).
  {
  apply boundph_upd.
  php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (phpdefp1u: phplusdef p1 (upd location_eq_dec (emp knowledge)
    (evall (Enum v, R, (0, nil), Aof L, Xof L, (M, params), P)) (Some Cond))).
  {
  apply phpdef_comm.
  apply phpdef_v; repeat php_.
  }

  assert (EQH: phplus p1 (upd location_eq_dec (emp knowledge)
    (evall (Enum v, R, (0, nil), Aof L, Xof L, (M, params), P)) (Some Cond)) =
   upd location_eq_dec p1 (v, R, (0, nil), Aof (evall L), Xof (evall L), (M, params), P) (Some Cond)).
  {
  rewrite phplus_comm; repeat php_.
  rewrite phplus_upd; repeat php_.
  unfold not.
  intros.
  destruct H as (v0,(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  }

  exists p1.
  exists (upd location_eq_dec (emp knowledge) (evall (Enum v, R, (0, nil), Aof L, Xof L, (M, params), P)) (Some Cond)).
  exists phpdefp1u, bp1, bpu.
  exists. rewrite EQH. assumption.
  exists O1, None, C1, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. 
  destruct O1.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  split.
  repeat dstr_.
  split.
  repeat dstr_.
  split.
  repeat dstr_.
  repeat php_.
Qed.

Lemma sat_newlock:
  forall p O C tx invs l (BP: boundph p) (BC: boundgh C)
        (Pl: forall r I X M P, p (l, r, I, l, X, M, P) = None)
        (SAT: sat p O C (weakest_pre_ct (Newlock, tx) invs)),
    exists r x (NIN: ~ In r x),
      sat (upd location_eq_dec p (l, r, (0%Z,nil),l, x, (0%Z,nil), false) (Some (Ulock empb empb))) O C (weakest_pre_ct (Val (Enum l), tx) invs).
Proof.
  simpl.
  intros.
  specialize SAT with l.
  destruct SAT as (r,(x,(nin,sat1))).
  exists r, x.

  assert (phpdefu: phplusdef (upd location_eq_dec (emp knowledge)
    (l, r, (0%Z, nil), l, x, (0, nil), false) (Some (Ulock empb empb))) p).
  {
  apply phpdef_ulock.
  repeat php_.
  apply Pl.
  }

  replace (upd location_eq_dec p (l, r, (0%Z, nil), l, x, (0%Z, nil), false)
    (Some (Ulock empb empb))) with
    (phplus p (upd location_eq_dec (emp knowledge) (l, r, (0%Z, nil), l, x, (0%Z, nil), false)
    (Some (Ulock empb empb)))).
  replace C with (ghplus C (emp (option nat*nat))).
  specialize Pl with r (0%Z, nil) x (0%Z,nil) false.
  exists.
  unfold ifb in nin.
  destruct (in_dec Z.eq_dec r x).
  inversion nin.
  assumption.
  apply sat1 with None; repeat php_.
  apply boundph_upd.
  repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1,(v2,(CO,rest))).
  inversion CO.
  destruct O.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  unfold upd.
  repeat dstr_.
  repeat php_.
  rewrite phplus_comm; repeat php_.
  apply phplus_upd; repeat php_.
  unfold not.
  intros.
  destruct H as (v,(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
Qed.

Lemma sat_mutate:
  forall p o g e1 e2 tx invs
         (SAT: sat p o g (weakest_pre_ct (Mutate e1 e2, tx) invs)),
    exists l1 v (EQ: Aof l1 = ([[e1]])), p l1 = Some (Cell 1 v).
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,((sat0,sat1),(sat2,(p1p2,C1C2)))))))))))))))))))).
  exists (evall v), ([[v0]]).
  apply Z.eqb_eq in sat0.
  unfold id in *.
  exists.
  unfold evall.
  unfold Aof in *.
  simpl.
  rewrite sat0.
  reflexivity.
  destruct sat1 as (f',(lef',p1v)).
  rewrite <- p1p2.
  unfold phplus.
  unfold phplusdef in phpdefp1p2.
  specialize phpdefp1p2 with (evall v).
  unfold boundph in bp12.
  unfold phplus in bp12.
  specialize bp12 with (x:=evall v).
  unfold boundph in bp2.
  specialize bp2 with (x:=evall v).
  rewrite p1v in *.
  destruct (p2 (evall v)) eqn:pv2.
  destruct k;
  try contradiction.
  assert (G: (0 < f)%Qc /\ (f <= 1)%Qc).
  {
  apply bp2 with z.
  reflexivity.
  }
  assert (CO: (0 < 1 + f' + f)%Qc /\ (1 + f' + f <= 1)%Qc).
  {
  eapply bp12.
  reflexivity.
  }
  destruct CO as (CO1,CO2).
  exfalso.
  apply qcpluslelt with (f' + f)%Qc.
  rewrite Qcplus_assoc.
  assumption.
  eapply Qclt_le_trans with f.
  tauto.
  rewrite Qcle_minus_iff.
  rewrite <- Qcplus_assoc.
  rewrite Qcplus_opp_r.
  rewrite Qcplus_0_r.
  assumption.
  unfold boundph in bp1.
  assert (G: (0 < 1 + f')%Qc /\ (1+f' <= 1)%Qc).
  {
  eapply bp1.
  apply p1v.
  }
  assert (G1: (f' <= 0)%Qc).
  {
  apply qcplusle.
  tauto.
  }
  assert (G2: (f' = 0)%Qc).
  {
  apply Qcle_antisym;
  assumption.
  }
  rewrite G2.
  rewrite Qcplus_0_r.
  reflexivity.
Qed.

Lemma sat_lookup:
  forall p o g e tx invs
         (SAT: sat p o g (weakest_pre_ct (Lookup e, tx) invs)),
    exists l1 v f (LT: (0 < f)%Qc) (EQ: Aof l1 = ([[e]])), p l1 = Some (Cell f v).
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(sat1,(sat2,(p1p2,C1C2)))))))))))))))))))))).
  exists (evall v), v0.
  destruct sat1 as (f',(ltf',p1v)).
  unfold phplusdef in phpdefp1p2.
  specialize phpdefp1p2 with (evall v).
  rewrite <- p1p2.
  unfold phplus.
  rewrite p1v in *.
  apply Z.eqb_eq in EQ.
  unfold id in EQ.
  rewrite EQ.
  unfold boundph in bp1.
  assert (G: (0 < v1 + f')%Qc /\ (v1 + f' <= 1)%Qc).
  {
  eapply bp1.
  apply p1v.
  }
  destruct (p2 (evall v)) eqn:p2v.
  destruct k;
  try contradiction.
  exists (v1 + f' + f)%Qc.
  exists.
  unfold boundph in bp2.
  assert (G1: (0 < f)%Qc /\ (f <= 1)%Qc).
  {
  eapply bp2.
  apply p2v.
  }
  apply Qc_Lt_plus.
  tauto.
  tauto.
  exists.
  reflexivity.
  reflexivity.
  exists (v1 + f')%Qc.
  exists.
  tauto.
  exists.
  reflexivity.
  reflexivity.
Qed.

Lemma sat_wait:
  forall p O C ev el tx invs
         (SAT: sat p (Some O) C (weakest_pre_ct (Wait ev el, tx) invs)),
    exists v l p1 p2 wt ot C1 C2 O1
           (EQl: Aof l = ([[el]]))
           (EQv: Aof v = ([[ev]]))
           (OO1: Permutation O (l :: O1))
           (BP1: boundph p1)
           (BP2: boundph p2)
           (phpdp1p2: phplusdef p1 p2)
           (p1p2: p = phplus p1 p2)
           (ghpdefc1c2: ghplusdef C1 C2)
           (C1C2: C = ghplus C1 C2) 
           (p1l: p1 l = Some (Locked wt ot))
           (p1v: p1 v = Some Cond)
           (p2inv: sat p2 None C2 (subsas (snd (Iof l)) (invs (fst (Iof l)) (upd Z.eq_dec wt (Aof v) (S (wt (Aof v)))) ot)))
           (PRCv: prcl v O1 = true)
           (PRCl: prcl l O1 = true)
           (NEQlv: v <> l)
           (Lvl: Lof v = Aof l)
           (SAFE_OBS: safe_obs v (S (wt (Aof v))) (ot (Aof v)) = true),
      sat (upd location_eq_dec p1 l (Some Lock)) (Some O1) C1
        (weakest_pre_ct (Waiting4cond ev el, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(sat1,(sat2,(p1p2,C1C2))))))))))))))))))))).
  destruct sat1 as (v2,(v3,(EQ,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(SAT,(tmp1,(p3p4,C3C4))))))))))))))))))))).
  destruct tmp1 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(ops56,(tmp1,(p56,C56)))))))))))))))))).
  destruct tmp1 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(ops78,(tmp1,(p78,C78)))))))))))))))))).
  assert (EQ1:=EQ).
  apply Coq.Bool.Bool.andb_true_iff in EQ.
  destruct EQ as (eqev,EQ).
  apply Coq.Bool.Bool.andb_true_iff in EQ.
  destruct EQ as (eqel,EQ).
  apply Coq.Bool.Bool.andb_true_iff in EQ.
  destruct EQ as (lov1,EQ).
  apply Coq.Bool.Bool.andb_true_iff in EQ.
  destruct EQ as (safe1,EQ).
  apply Coq.Bool.Bool.andb_true_iff in EQ.
  destruct EQ as (prcv1,prcv0).
  unfold id in *.

  assert (eqO: Permutation O (evall v0 :: map evall v) /\ O3 = None /\ o2 = None).
  {
  inversion ops56.
  rewrite <- H1 in opO5O6.
  inversion opO5O6.
  rewrite <- H4 in opO3O4.
  inversion opO3O4.
  rewrite <- H5 in opO1O2.
  inversion opO1O2.
  split.
  apply Permutation_trans with o'1.
  apply Permutation_sym.
  assumption.
  apply Permutation_trans with o'0.
  apply Permutation_sym.
  assumption.
  apply Permutation_trans with o'.
  apply Permutation_sym.
  assumption.
  apply Permutation_sym.
  assumption.
  split.
  reflexivity.
  reflexivity.
  }
  destruct eqO as (eqO,(O3N,O2N)).
  rewrite O3N,O2N in *. 

  assert (phpdefp32p42: phplusdef p3 p2 /\ phplusdef p4 p2).
  {
  apply phpdef_dist;
  try tauto.
  rewrite p3p4.
  tauto.
  }

  assert (phpdefp57p58: phplusdef p5 p7 /\ phplusdef p5 p8).
  {
  apply phpdef_dist';
  try tauto.
  rewrite p78.
  tauto.
  }

  assert (bp2p4: boundph (phplus p2 p4)).
  {
  apply boundph_mon with p3;
  try tauto.
  rewrite phplus_assoc;
  try tauto.
  replace (phplus p4 p3) with (phplus p3 p4);
  try tauto.
  rewrite p3p4.
  rewrite phplus_comm;
  try tauto.
  apply phpdef_comm.
  tauto.
  apply phplus_comm;
  try tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  }

  assert (ghpdefp32p42: ghplusdef C3 C2 /\ ghplusdef C4 C2).
  {
  apply ghpdef_dist;
  try tauto.
  rewrite C3C4.
  tauto.
  }

  assert (bgp2p4: boundgh (ghplus C2 C4)).
  {
  apply boundgh_mon with C3;
  try tauto.
  rewrite ghplus_assoc;
  try tauto.
  replace (ghplus C4 C3) with (ghplus C3 C4);
  try tauto.
  rewrite C3C4.
  rewrite ghplus_comm;
  try tauto.
  apply ghpdef_comm.
  tauto.
  apply ghplus_comm;
  try tauto.
  apply ghpdef_comm.
  tauto.
  apply ghpdef_comm.
  tauto.
  apply ghpdef_comm.
  tauto.
  }

  assert (p4v0: p4 (evall v0) = Some (Locked v2 v3)).
  {
  rewrite <- p56.
  apply phplus_locked';
  try tauto.
  rewrite <- p78.
  apply phplus_locked';
  try tauto.
  }

  assert (bp57: boundph (phplus p5 p7)).
  {
  apply boundph_mon with p8;
  try tauto.
  rewrite phplus_assoc;
  try tauto.
  rewrite p78.
  tauto.
  }
  assert (phpdefp8p57: phplusdef p8 (phplus p5 p7)).
  {
  apply phpdef_comm.
  apply phpdef_pair';
  try tauto.
  }

  assert (bp8u: boundph (upd location_eq_dec p8 (evall v0) (Some Lock))).
  {
  apply boundph_upd;
  try tauto.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }



  exists (evall v1), (evall v0).
  exists (phplus p2 p4), p3, v2, v3, (ghplus C2 C4), C3, (map evall v).
  exists.
  apply Z.eqb_eq in eqel.
  rewrite eqel.
  reflexivity.
  exists.
  apply Z.eqb_eq in eqev.
  rewrite eqev.
  reflexivity.
  exists eqO, bp2p4, bp3.
  exists.
  apply phpdef_pair';
  try tauto.
  apply phpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  exists.
  rewrite phplus_assoc;
  try tauto.
  replace (phplus p4 p3) with (phplus p3 p4).
  rewrite p3p4.
  rewrite phplus_comm;
  try tauto.
  symmetry.
  tauto.
  apply phpdef_comm;
  tauto.
  apply phplus_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  apply phpdef_comm;
  tauto.
  exists.
  apply ghpdef_pair';
  try tauto.
  apply ghpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  exists.
  rewrite ghplus_assoc;
  try tauto.
  replace (ghplus C4 C3) with (ghplus C3 C4).
  rewrite C3C4.
  rewrite ghplus_comm;
  try tauto.
  symmetry.
  tauto.
  apply ghpdef_comm;
  tauto.
  apply ghplus_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  apply ghpdef_comm;
  tauto.
  exists.
  apply phplus_locked';
  try tauto.
  apply phpdef_comm.
  tauto.  
  exists.
  apply phplus_Cond';
  try tauto.
  apply phpdef_comm;
  tauto.
  rewrite <- p56.
  apply phplus_Cond';
  try tauto.
  rewrite <- p78.
  apply phplus_Cond;
  try tauto.
  exists SAT.
  exists prcv1, prcv0.
  exists.
  unfold not.
  intros.
  rewrite H in ops78.
  unfold phplusdef in phpdefp7p8.
  specialize phpdefp7p8 with (evall v0).
  rewrite ops78 in phpdefp7p8.
  rewrite tmp1 in phpdefp7p8.
  contradiction.
  exists.
  unfold evall.
  apply Z.eqb_eq in lov1.
  rewrite <- lov1.
  reflexivity.
  exists safe1.
  exists v, v0, v1.
  exists.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  assumption.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  assumption.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  assumption.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  assumption.
  assumption.
  exists (upd location_eq_dec p4 (evall v0) (Some Lock)), p2.
  exists.
  apply phpdef_locked_lock.
  try tauto.
  exists v2, v3.
  left.
  assumption.
  exists.
  apply boundph_upd;
  try tauto.
  intros.
  destruct H as (f',CO).
  inversion CO.
  exists bp2.
  exists.
  apply boundph_phplus_upd;
  try tauto.
  rewrite phplus_comm;
  try tauto.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v4,(v5,(CO,rest))).
  inversion CO.
  exists (Some (map evall v)), None.
  exists C4, C2.
  exists.
  tauto.
  exists BC4, BC2.
  exists.
  rewrite ghplus_comm;
  try tauto.
  exists.
  apply fs_op.
  apply Permutation_refl.
  split.
  exists (phplus p5 p7), (upd location_eq_dec p8 (evall v0) (Some Lock)).
  exists.
  apply phpdef_comm.
  apply phpdef_locked_lock;
  try tauto.
  exists v2, v3.
  left.
  assumption.
  exists bp57.
  exists.
  apply boundph_upd;
  try tauto.
  intros.
  destruct H as (z',CO).
  inversion CO.
  exists.
  rewrite phplus_comm;
  try tauto.
  apply boundph_phplus_upd;
  try tauto.
  rewrite phplus_comm;
  try tauto.
  rewrite phplus_assoc;
  try tauto.
  rewrite p78.
  tauto.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v4,(v5,(CO,rest))).
  inversion CO.
  apply phpdef_comm.
  apply phpdef_locked_lock;
  try tauto.
  exists v2, v3.
  tauto.
  exists None, (Some (map evall v)).
  exists C4, (emp (option nat*nat)).
  exists.
  apply ghpdef_emp.
  exists BC4, boundgh_emp.
  exists.
  rewrite ghplus_emp.
  assumption.
  exists.
  apply sn_op.
  apply Permutation_refl.
  split.
  rewrite phplus_comm;
  try tauto.
  unfold phplus.
  rewrite ops78.
  reflexivity.
  split.
  exists (upd location_eq_dec p8 (evall v0) (Some Lock)), (emp knowledge).
  exists.
  apply phpdef_emp.
  exists bp8u.
  exists boundph_emp.
  exists.
  rewrite phplus_emp.
  tauto.
  exists None, (Some (map evall v)).
  exists (emp (option nat * nat)), (emp (option nat * nat)).
  rewrite ghplus_emp.
  exists.
  apply ghpdef_emp.
  exists boundgh_emp, boundgh_emp, boundgh_emp.
  exists.
  apply sn_op.
  apply Permutation_refl.
  split.
  left.
  unfold upd.
  destruct (location_eq_dec (evall v0) (evall v0)).
  reflexivity.
  contradiction.
  split.
  apply fs_op.
  apply Permutation_refl.
  rewrite phplus_emp.
  tauto.
  split.
  rewrite phplus_comm;
  try tauto.
  rewrite phplus_upd;
  try tauto.
  rewrite phplus_comm;
  try tauto.
  rewrite phplus_assoc;
  try tauto.
  rewrite p78.
  rewrite p56.
  reflexivity.
  unfold not.
  intros.
  destruct H as (v',(f',(v'',(f'',(CO,rest))))).
  inversion CO.
  intros.
  unfold not.
  intros.
  destruct H0 as (wt,(ot,p57v)).
  apply phplus_locked_mon in p57v.
  destruct p57v as [LK|LK].
  destruct phpdefp57p58 as (phpdefp57,phpdefp58).
  unfold phplusdef in phpdefp58.
  specialize phpdefp58 with (evall v0).
  rewrite LK in phpdefp58.
  rewrite tmp1 in phpdefp58.
  contradiction.
  unfold phplusdef in phpdefp7p8.
  specialize phpdefp7p8 with (evall v0).
  rewrite LK in phpdefp7p8.
  rewrite tmp1 in phpdefp7p8.
  contradiction.
  intros.
  inversion H.
  apply phpdef_comm.
  apply phpdef_locked_lock;
  try tauto.
  exists v2, v3.
  tauto.
  apply ghplus_emp.
  split.
  intros.
  apply sat2 with v4 v5 O';
  try tauto.
  split.
  replace (phplus p2 p4) with (phplus p4 p2).
  apply phplus_upd;
  try tauto.
  unfold not.
  intros.
  destruct H as (v',(f',(v'',(f'',(CO, rest))))).
  inversion CO.
  unfold not.
  intros.
  destruct H0 as (wt,(ot,p2v0)).
  destruct phpdefp32p42 as (phpdefp32,phpdefp42).
  unfold phplusdef in phpdefp42.
  specialize phpdefp42 with (evall v0).
  rewrite p2v0 in phpdefp42.
  rewrite p4v0 in phpdefp42.
  contradiction.
  intros.
  inversion H.
  apply phplus_comm;
  try tauto.
  apply ghplus_comm;
  try tauto.
Qed.