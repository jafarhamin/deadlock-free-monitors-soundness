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

Fixpoint weakest_pre (c:cmd) (Q: Z -> assn) (se: exp -> exp) (R: Z -> Z) (I: Z -> inv) (L: Z -> Z) (M: Z -> bool) (P: Z -> bool) (X: Z -> list Z) : assn :=
  match c with
    | Val z => Q z
    | Cons e => FA r, (r |-> ([[se e]]) --* (Q r))
    | Lookup e => EX z, (EX f, (Apointsto f ([[se e]]) z ** ((Apointsto f ([[se e]]) z) --* (Q z))))
    | Mutate e1 e2 => EX z, (([[se e1]]) |-> z) ** ((Apointsto 1 ([[se e1]]) ([[se e2]])) --* (Q 0))
    | Let x c1 c2 => weakest_pre c1 (fun z => weakest_pre c2 Q (fun e => subse x z (se e)) R I L M P X) se R I L M P X
    | Fork c => EX O, (EX O', ((Aobs(O ++ O') ** (Aobs(O) --* Q 0)) ** (Aobs(O') --* weakest_pre c (fun _ => Aobs(nil)) se R I L M P X)))
    | Newlock => FA l, (EX r, (EX x, (Abool (andb (Z.eqb (R l) r) (ifb (list_eq_dec Z.eq_dec (X l) x))) ** (Aulock l empb empb empb)) --* (Q l)))
    | Acquire l => EX O, ((Abool (prc ([[se l]]) O R L P X) &* (Alock ([[se l]]) ** Aobs O)) **
        (FA wt, (FA ot, (FA ct, ((Aobs ([[se l]]::O) ** Alocked ([[se l]]) wt ot ct ** (Alasn (I ([[se l]]) wt ot ct))) --* Q 0)))))
    | Release l => EX O, (EX wt, (EX ot, (EX ct,
        ((Aobs (([[se l]])::O) ** Alocked ([[se l]]) wt ot ct ** (Alasn (I ([[se l]]) wt ot ct))) **
        ((Aobs O ** Alock ([[se l]])) --* Q 0)))))
    | Newcond => FA v, (EX r, (EX l, (EX m, (EX b,
        ((Abool (andb (Z.eqb (R l) r)(andb (Z.eqb (L (v)) l)(andb (Coq.Bool.Bool.eqb (M (v)) m)(Coq.Bool.Bool.eqb (P (v)) b)))) &* Acond v) --* (Q v))))))
    | Waiting4lock l => EX O, (Abool (prc ([[se l]]) O R L P X) &* (Alock ([[se l]]) ** Aobs O) **
        (FA wt, (FA ot, (FA ct, (Aobs ([[se l]]::O) ** Alocked ([[se l]]) wt ot ct ** (Alasn (I ([[se l]]) wt ot ct))) --* Q 0))))
    | Wait v l => EX O, (EX wt, (EX ot, (EX ct,
        (Abool (andb (Z.eqb (L ([[se v]])) ([[se l]]))
        (andb (safe_obs ([[se v]]) (S (wt ([[se v]]))) (ot ([[se v]])) R L P X)
        (andb (prc ([[se v]]) O R L P X)
        (prc ([[se l]]) O R L P X)))) &* 
        (Aobs (([[se l]])::O) ** Acond ([[se v]]) ** Alocked ([[se l]]) wt ot ct ** (Alasn (I ([[se l]]) (incb wt ([[se v]])) ot ct))))))) **
        (FA wt', (FA ot', (FA ct', ((Aobs (([[se l]])::O) ** Alocked ([[se l]]) wt' ot' ct' ** (Alasn (I ([[se l]]) wt' ot' ct')) ** 
        (Alasn (M_to_crd (M ([[se v]])) ([[se v]])))) --* Q 0))))
    | Waiting4cond v l => EX O, (Abool (andb (Z.eqb (L ([[se v]])) ([[se l]])) (andb (prc ([[se v]]) O R L P X)
        (prc ([[se l]]) O R L P X))) &* (Acond ([[se v]]) ** Alock ([[se l]]) ** Aobs O)) **
        (FA wt, (FA ot, (FA ct, ((Aobs ([[se l]]::O) ** Alocked ([[se l]]) wt ot ct ** (Alasn (I ([[se l]]) wt ot ct)) **
        Alasn (M_to_crd (M ([[se v]])) ([[se v]]))) --* Q 0))))
    | Notify v => EX wt, (EX ot, (EX ct, (Acond ([[se v]]) ** Alocked (L ([[se v]])) wt ot ct ** (Alasn (M_to_crd (M ([[se v]])) ([[se v]]))) **
       ((Alocked (L ([[se v]])) (decb wt ([[se v]])) ot ct ** 
       ((Alasn (M_to_crd (M ([[se v]])) ([[se v]]))) |* Abool (ltb 0 (wt ([[se v]]))))) --* Q 0))))
    | NotifyAll v => EX wt, (EX ot, (EX ct ,(Abool (negb (M ([[se v]]))) &* Acond ([[se v]]) ** Alocked (L ([[se v]])) wt ot ct **
       ((Alocked (L ([[se v]])) (rstb wt ([[se v]])) ot ct ** 
       ((Alasn (M_to_crd (M ([[se v]])) ([[se v]]))) |* Abool (ltb 0 (wt ([[se v]])))) --* Q 0)))))
    | g_initl l => EX O, (EXi i, (EX wt, (EX ot, (EX ct, (Abool (andb (negb (P ([[se l]])))(andb (Z.eqb (L ([[se l]])) ([[se l]]))
        (negb (ifb (In_dec Z.eq_dec (R ([[se l]])) (X (L ([[se l]]))))))))
        &* Aulock ([[se l]]) wt ot ct ** (Alasn (I ([[se l]]) wt ot ct)) ** Aobs O ** ((Aprop (I ([[se l]]) = i) &* Alock ([[se l]]) ** Aobs O) --* (Q 0)))))))
    | g_dupl l => Alock ([[se l]]) ** ((Alock ([[se l]]) ** Alock ([[se l]])) --* (Q 0))
    | g_chrg v => EX O, (EX wt, (EX ot, (EX ct, (Acond ([[se v]]) ** Aobs O ** Alocked (L ([[se v]])) wt ot ct
        ** ((Aobs (([[se v]])::O) ** Alocked (L ([[se v]])) wt (incb ot ([[se v]])) ct) --* (Q 0))))))
    | g_chrgu v => EX O, (EX wt, (EX ot, (EX ct, (Acond ([[se v]]) ** Aobs O ** Aulock (L ([[se v]])) wt ot ct
        ** ((Aobs (([[se v]])::O) ** Aulock (L ([[se v]])) wt (incb ot ([[se v]])) ct) --* (Q 0))))))
    | g_disch v => EX O, (EX wt, (EX ot, (EX ct, (Abool (andb (safe_obs ([[se v]]) (wt ([[se v]])) ((ot ([[se v]]) - 1)) R L P X) (ltb 0 (ot ([[se v]])))) 
        &* Acond ([[se v]]) ** Aobs (([[se v]])::O) ** Alocked (L ([[se v]])) wt ot ct
        ** ((Aobs O ** Alocked (L ([[se v]])) wt (decb ot ([[se v]])) ct) --* (Q 0))))))
    | g_dischu v => EX O, (EX wt, (EX ot, (EX ct, (Abool (andb (safe_obs ([[se v]]) (wt ([[se v]])) ((ot ([[se v]]) - 1)) R L P X) (ltb 0 (ot ([[se v]]))))
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


Fixpoint weakest_pre_tx (tx:context) (R: Z -> Z) (I: Z -> inv) (L: Z -> Z) (M: Z -> bool) (P: Z -> bool) (X: Z -> list Z) : (Z -> assn) :=
  match tx with
    | done => fun _ => Aobs nil
    | Let' x c tx => fun z => weakest_pre (subs c (subse x z)) (weakest_pre_tx tx R I L M P X) id R I L M P X
  end.

Definition weakest_pre_ct (ct: (cmd * context)) (R: Z -> Z) (I: Z -> inv) (L: Z -> Z) (M: Z -> bool) (P: Z -> bool) (X: Z -> list Z) : assn :=
  weakest_pre (fst ct) (weakest_pre_tx (snd ct) R I L M P X) id R I L M P X.



Lemma sat_weak_imp:
  forall c p o d se a a' R I L M P X (BP: boundph p)
         (SAT: sat p o d (weakest_pre c a se R I L M P X))
         (IMP: forall z, a z |= a' z),
    sat p o d (weakest_pre c a' se R I L M P X).
Proof.
  induction c;
  try reflexivity.
  simpl.
  intros.
  apply IMP.
  assumption.
  assumption.
  simpl.
  intros.
  apply IMP.
  assumption.
  apply SAT with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,tmp2)))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v, v0, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp2 with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,tmp2))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp2 with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,tmp2)))))))))))))).
  destruct tmp1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,tmp1))))))))))).
  destruct tmp1 as (tmp1, tmp3).
  destruct tmp3 as (tmp3, tmp5).
  destruct tmp2 as (tmp2,tmp4).
  exists v, v0, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2, C1, C2, opO1O2.
  split.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp3 with (O':=O').
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  split.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  eapply IHc1.
  assumption.
  apply SAT.
  intros.
  eapply IHc2.
  assumption.
  simpl in *.
  apply SAT0.
  intros.
  apply IMP.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  specialize SAT with v.
  destruct SAT as (v0,(v1,SAT)).
  exists v0, v1.
  intros.
  apply IMP.
  assumption.
  apply SAT with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,tmp2))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp2 with v0 v1 v2 O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(v2,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,tmp2)))))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v, v0, v1, v2, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  destruct tmp1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,(tmp4,tmp5)))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp2 with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(PRC,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,tmp2)))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v.
  split.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  destruct tmp1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,(tmp4,tmp5)))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp2 with v0 v1 v2 O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  specialize SAT with v.
  destruct SAT as (v0,(v1,(v2,(v3,SAT)))).
  exists v0, v1, v2, v3.
  intros.
  apply IMP.
  assumption.
  apply SAT with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,tmp2))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  destruct tmp1 as (v0,(v1,(v2,(Lx,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,(tmp4,tmp5)))))))))))))))).
  exists v0,v1,v2.
  split.
  assumption.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp2 with v0 v1 v2 O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,tmp2))))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v, v0, v1, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,(tmp4,tmp5)))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  split.
  destruct tmp5 as (tmp5,tmp6).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(opO5O6,(tmp5,(tmp7,tmp8))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, opO5O6.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp7 with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  destruct tmp5 as (tmp5,tmp8).
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(NEG,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,tmp2)))))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v, v0, v1.
  split.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,(tmp4,(tmp5,tmp6))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp5 with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,tmp2))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v0, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp2 with v1 v2 v3 O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(v2,(v3,(NEG,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,tmp2)))))))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v, v0, v1, v2, v3.
  split.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,(tmp4,(tmp5,tmp6))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  split.
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(opO5O6,(tmp9,(tmp7,tmp8))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, opO5O6.
  split.
  tauto.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp7 with O';
  try tauto.
  assumption.
  assumption.
  assumption.
  }

  {
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,(tmp2,tmp3))))))))))))).
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp2 with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(v2,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,(tmp2,tmp3))))))))))))))))).
  exists v, v0, v1, v2, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,(tmp4,(tmp5,tmp6))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  split.
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(opO5O6,(tmp5,(tmp7,tmp8))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, opO5O6.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp7 with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(v2,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,(tmp2,tmp3))))))))))))))))).
  exists v, v0, v1, v2, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,(tmp4,(tmp5,tmp6))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  split.
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(opO5O6,(tmp5,(tmp7,tmp8))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, opO5O6.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp7 with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(v2,(SAFE,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,(tmp2,tmp3)))))))))))))))))).
  exists v, v0, v1, v2.
  split.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,(tmp4,(tmp5,tmp6))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  split.
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(opO5O6,(tmp5,(tmp7,tmp8))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, opO5O6.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp7 with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(v2,(SAFE,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,(tmp2,tmp3)))))))))))))))))).
  exists v, v0, v1, v2.
  split.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,(tmp4,(tmp5,tmp6))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  split.
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(opO5O6,(tmp5,(tmp7,tmp8))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, opO5O6.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp7 with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,(tmp2,tmp3)))))))))))))))).
  exists v, v0, v1, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,(tmp4,(tmp5,tmp6))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp5 with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,(tmp2,tmp3)))))))))))))))).
  exists v, v0, v1, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,(tmp4,(tmp5,tmp6))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp5 with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(LT,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,(tmp2,tmp3))))))))))))))))).
  exists v, v0, v1.
  split.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,(tmp4,(tmp5,tmp6))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  split.
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(opO5O6,(tmp5,(tmp7,tmp8))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, opO5O6.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp7 with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(LT,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,(tmp2,tmp3))))))))))))))))).
  exists v, v0, v1.
  split.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,(tmp4,(tmp5,tmp6))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  split.
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(opO5O6,(tmp5,(tmp7,tmp8))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, opO5O6.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp7 with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,(tmp2,tmp3)))))))))))))))).
  exists v, v0, v1, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,(tmp4,(tmp5,tmp6))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  split.
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(opO5O6,(tmp5,(tmp7,tmp8))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, opO5O6.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp7 with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,(tmp2,tmp3)))))))))))))))).
  exists v, v0, v1, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, opO1O2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,(tmp4,(tmp5,tmp6))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  split.
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(opO5O6,(tmp5,(tmp7,tmp8))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, opO5O6.
  split.
  assumption.
  split.
  intros.
  apply IMP.
  assumption.
  apply tmp7 with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
Qed.

Lemma sat_pre_subs1:
  forall c se a p o d x z R I L M P X (BP: boundph p)
        (SAT: sat p o d (weakest_pre (subs c (subse x z)) a se R I L M P X)),
    sat p o d (weakest_pre c a (fun e : exp => se (subse x z e)) R I L M P X).
Proof.
  induction c;
  intros;
  try assumption.
  {
  simpl in *.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,tmp2)))))))))))))).
  destruct tmp1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,tmp1))))))))))).
  destruct tmp1 as (tmp1, tmp3).
  destruct tmp2 as (tmp2,tmp4).
  exists v, v0, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2, C1, C2, opO1O2.
  split.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  assumption.
  split.
  intros.
  apply IHc.
  assumption.
  apply tmp2 with (O':=O').
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  simpl in *.
  apply IHc1.
  assumption.
  apply sat_weak_imp with (a := fun z0 : Z => 
    weakest_pre (subs c2 (subse x0 z)) a (fun e : exp => subse x z0 (se e)) R I L M P X).
  assumption.
  assumption.
  intros.
  apply IHc2 in SAT0.
  assumption.
  assumption.
  }
Qed.

Lemma sat_pre_subs2:
  forall c se a p o d x z R I L M P X (BP: boundph p)
        (SAT: sat p o d (weakest_pre c a (fun e : exp => se (subse x z e)) R I L M P X)),
    sat p o d (weakest_pre (subs c (subse x z)) a se R I L M P X).
Proof.
  induction c;
  intros;
  try assumption.
  {
  simpl in *.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(tmp1,tmp2)))))))))))))).
  destruct tmp1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opO3O4,tmp1))))))))))).
  destruct tmp1 as (tmp1, tmp3).
  destruct tmp2 as (tmp2,tmp4).
  exists v, v0, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2, C1, C2, opO1O2.
  split.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, opO3O4.
  split.
  assumption.
  assumption.
  split.
  intros.
  apply IHc.
  assumption.
  apply tmp2 with (O':=O').
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  simpl in *.
  apply IHc1.
  assumption.
  apply sat_weak_imp with (a:= fun z0 : Z => weakest_pre c2 a
    (fun e : exp => subse x z0 (se (subse x0 z e))) R I L M P X).
  assumption.
  assumption.
  simpl.
  intros.
  apply IHc2.
  assumption.
  assumption.
Qed.

Lemma sat_pre_subs3:
  forall c p o C a se1 se2 R I L M P X (bp: boundph p)
         (SAT: sat p o C (weakest_pre (subs c se1) a se2 R I L M P X)),
    sat p o C (weakest_pre c a (fun e => se2 (se1 e)) R I L M P X).
Proof.
  induction c;
  intros;
  try assumption;
  try apply SAT.
  {
  simpl in *.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(opO1O2,(sat1,(sat2,(p1p2,C1C2)))))))))))))))).
  exists v, v0, p1, p2, phpdefp1p2, bp1, bp2, bp12, o1, o2, C1, C2, opO1O2.
  exists.
  assumption.
  exists.
  intros.
  apply IHc.
  assumption.
  apply sat2 with O'.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  tauto.
  }
  {
  apply IHc1.
  assumption.
  eapply sat_weak_imp.
  assumption.
  apply SAT.
  simpl.
  intros.
  apply IHc2 in SAT0.
  assumption.
  assumption.
  }
Qed.

Lemma sat_pre_subs:
  forall c se a p o d x z R I L M P X (BP: boundph p),
    sat p o d (weakest_pre (subs c (subse x z)) a se R I L M P X) <->
    sat p o d (weakest_pre c a (fun e : exp => se (subse x z e)) R I L M P X).
Proof.
  split.
  apply sat_pre_subs1.
  assumption.
  apply sat_pre_subs2.
  assumption.
Qed.


Lemma safe_obs_obv:
  forall v wt ot wt' R L P X
         (LE: le wt' wt)
         (SAFE_OBS: safe_obs v wt ot R L P X = true),
  safe_obs v wt' ot R L P X= true.
Proof.
  unfold safe_obs.
  intros.
  apply Coq.Bool.Bool.andb_true_iff in SAFE_OBS.
  destruct SAFE_OBS as (ONE,SAFE_OBS).
  apply Coq.Bool.Bool.andb_true_iff in SAFE_OBS.
  destruct SAFE_OBS as (SPR,OWN).
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  unfold one_ob in *.
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
  unfold spare_ob in *.
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
  unfold own_ob in *.
  apply Nat.leb_le in OWN.
  apply Nat.leb_le.
  omega.
Qed.

Lemma sat_wait4cond:
  forall p O C v l tx R I L M P X
        (SAT: sat p (Some O) C (weakest_pre_ct (Waiting4cond v l, tx) R I L M P X)),
  exists (Pv: p ([[v]]) = Some Cond)
         (Pl: p ([[l]]) = Some Lock \/ exists wt ot ct, p ([[l]]) = Some (Locked wt ot ct))
         (lvl: L ([[v]]) = ([[l]]))
         (PRCl: prc ([[l]]) O R L P X = true)
         (PRCv: prc ([[v]]) O R L P X = true),
    sat p (Some O) (bagplus C (fun x => if Z.eq_dec x ([[v]]) then if bool_dec (M ([[v]])) true then 1%nat else 0%nat else 0%nat))
     (weakest_pre_ct (Waiting4lock l, tx) R I L M P X).
Proof.
  intros.
  simpl in SAT.
  destruct SAT as (v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,
    (opo1o2,(tmp1,(tmp2,(p1p2,C1C2))))))))))))))).
  destruct tmp1 as (tmp6,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(o3,(o4,(C3,(C4,(opo3o4,(tmp1,(tmp3,(p3p4,C3C4))))))))))))))).
  destruct tmp3 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(o5,(o6,(C5,(C6,(opo5o6,(tmp5,((p6N,(C6N,opo6)),(p5p6,C5C6)))))))))))))).
  apply Coq.Bool.Bool.andb_true_iff in tmp6.
  destruct tmp6 as (lvl,tmp6).
  apply Coq.Bool.Bool.andb_true_iff in tmp6.
  destruct tmp6 as (prcv,prcl).

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
  apply prc_perm with v0.
  apply prcl.
  apply Permutation_sym.
  assumption.
  exists.
  apply prc_perm with v0.
  apply prcv.
  apply Permutation_sym.
  assumption.
  simpl.
  exists v0.
  split.
  tauto.
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

Lemma sat_notifyall:
forall p O C v tx R I L M P X
      (SAT: sat p (Some O) C (weakest_pre_ct (NotifyAll v, tx) R I L M P X)),
  exists wt ot ct
         (P1l: p (L ([[v]])) = Some (Locked wt ot ct)) 
         (P1l: p ([[v]]) = Some Cond)
         (Mv: M ([[v]]) = false),
    sat (upd p (L ([[v]])) (Some (Locked (upd wt ([[v]]) 0%nat) ot ct))) (Some O) C
      (weakest_pre_tx tx R I L M P X 0).
Proof.
  intros.
  simpl in SAT.
  destruct SAT as (v0,(v1,(v2,(NEG,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,
    (opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(o3,(o4,(C3,(C4,(opo3o4,(tmp3,(tmp4,tmp5))))))))))))).

  assert (phpdefp134: phplusdef p1 p3 /\ phplusdef p1 p4).
  {
  apply phpdef_dist'.
  intuition.
  rewrite H.
  assumption.
  assumption.
  }

  assert (bp13: boundph (phplus p1 p3)).
  {
  apply boundph_mon with p4;
  try tauto.
  apply bph_assoc;
  try tauto.
  intuition.
  rewrite H.
  assumption.
  }

  assert (bp14: boundph (phplus p1 p4)).
  {
  apply boundph_mon with p3;
  try tauto.
  apply bph_assoc;
  try tauto.
  apply phpdef_comm.
  assumption.
  replace (phplus p4 p3) with (phplus p3 p4).
  intuition.
  rewrite H.
  assumption.
  apply phplus_comm.
  assumption.
  }

  assert (bp1u3: boundph (phplus p1 (upd p3 (L ([[v]])) (Some (Locked (upd v0 ([[v]]) 0%nat) v1 v2))))).
  {
  rewrite phplus_comm.
  apply boundph_phplus_upd;
  try tauto.
  apply phpdef_comm.
  tauto.
  rewrite phplus_comm;
  try tauto.
  apply phpdef_comm.
  tauto.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v3,(v4,(CO,rest))).
  inversion CO.
  apply phpdef_comm.
  apply phpdef_locked;
  try tauto.
  apply phpdef_comm.
  tauto.
  exists v0, v1, v2.
  assumption.
  }

  assert (phpdefp1u3: phplusdef p1 (upd p3 (L ([[v]])) (Some (Locked (upd v0 ([[v]]) 0%nat) v1 v2)))).
  {
  apply phpdef_comm.
  apply phpdef_locked;
  try tauto.
  apply phpdef_comm.
  tauto.
  exists v0, v1, v2.
  assumption.
  }

  assert (phpdefp4u3: phplusdef p4(upd p3 (L ([[v]])) (Some (Locked (upd v0 ([[v]]) 0%nat) v1 v2)))).
  {
  apply phpdef_comm.
  apply phpdef_locked;
  try tauto.
  exists v0, v1, v2.
  assumption.
  }

  assert (phpdp41u3: phplusdef p4 (phplus p1 (upd p3 (L ([[v]])) (Some (Locked (upd v0 ([[v]]) 0%nat) v1 v2))))).
  {
  apply phpdef_pair.
  assumption.
  apply phpdef_comm.
  tauto.
  assumption.
  }

  assert (phpdefp3p41: phplusdef p3 (phplus p4 p1)).
  {
  apply phpdef_pair;
  try tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  }

  assert (bp34p1: boundph (phplus (phplus p3 p4) p1)).
  {
  intuition.
  rewrite H.
  rewrite phplus_comm.
  assumption.
  apply phpdef_comm.
  assumption.
  }

  assert (bpu3p41: boundph (phplus (upd p3 (L ([[v]])) (Some (Locked (upd v0 ([[v]]) 0%nat) v1 v2))) (phplus p4 p1))).
  {
  apply boundph_phplus_upd;
  try tauto.
  apply bph_comm.
  tauto.
  assumption.
  rewrite <- phplus_assoc.
  assumption.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v3,(v4,(CO,rest))).
  inversion CO.
  }

  assert (phpdefp41p3u: phplusdef (phplus p4 p1) (upd p3 (L ([[v]])) (Some (Locked (upd v0 ([[v]]) 0%nat) v1 v2)))).
  {
  apply phpdef_pair'.
  apply phpdef_comm.
  tauto.
  assumption.
  assumption.
  }

  assert (bp41pu3: boundph (phplus (phplus p4 p1) (upd p3 (L ([[v]])) (Some (Locked (upd v0 ([[v]]) 0%nat) v1 v2))))).
  {
  rewrite phplus_comm.
  assumption.
  assumption.
  }

  assert (bp41u3: boundph (phplus p4 (phplus p1 (upd p3 (L ([[v]])) (Some (Locked (upd v0 ([[v]]) 0%nat) v1 v2)))))).
  {
  rewrite <- phplus_assoc.
  assumption.
  apply phpdef_comm.
  tauto.
  assumption.
  assumption.
  }

  assert (bp3u: boundph (upd p3 (L ([[v]])) (Some (Locked (upd v0 ([[v]]) 0%nat) v1 v2)))).
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z1,CO).
  inversion CO.
  }

  assert (bp3up1: boundph (phplus (upd p3 (L ([[v]])) (Some (Locked (upd v0 ([[v]]) 0%nat) v1 v2))) p1)).
  {
  apply boundph_phplus_upd;
  try tauto.
  apply phpdef_comm.
  tauto.
  rewrite phplus_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v3,(v4,(CO,rest))).
  inversion CO.
  }




  exists v0, v1, v2.
  exists.
  rewrite <- p1p2.
  rewrite phplus_comm.
  apply phplus_locked.
  apply phpdef_comm.
  assumption.
  intuition.
  rewrite <- H.
  apply phplus_locked;
  assumption.
  assumption.
  exists.
  rewrite <- p1p2.
  apply phplus_Cond;
  assumption.
  unfold id in *.
  exists.
  destruct (M ([[v]])).
  inversion NEG.
  tauto.
  assert (O4N: o4 = None \/ exists o4' (EQO: o4 = Some o4'),
    Permutation o4' O).
  {
  destruct o4.
  right.
  exists l.
  exists.
  reflexivity.
  inversion opo3o4.
  rewrite <- H0 in opo1o2.
  inversion opo1o2.
  apply Permutation_trans with o';
  assumption.
  left.
  reflexivity.
  }


  assert (G: sat (phplus p4 (phplus p1 (upd p3 (L ([[v]])) (Some (Locked (upd v0 ([[v]]) 0%nat) v1 v2)))))
     (Some O) (bagplus C4 (bagplus C1 C3)) (weakest_pre_tx tx R I L M P X 0)).
  {

  destruct O4N as [O4N|O4N].
  {
  rewrite O4N in *.
  apply tmp4 with (Some O).
  assumption.
  assumption.
  assumption.
  apply sn_op.
  apply Permutation_refl.
  exists (upd p3 (L ([[v]])) (Some (Locked (upd v0 ([[v]]) 0%nat) v1 v2))), p1.
  exists.
  apply phpdef_comm.
  assumption.
  exists bp3u, bp1, bp3up1.
  exists None, (Some O).
  exists C1, C3.
  exists.
  apply sn_op.
  apply Permutation_refl.
  split.
  unfold upd.
  rewrite eqz.
  reflexivity.
  split.
  simpl.
  unfold M_to_crd.
  simpl.
  destruct (M ([[v]])).
  inversion NEG.
  simpl.
  left.
  reflexivity.
  rewrite phplus_comm.
  tauto.
  apply phpdef_comm.
  assumption.
  }

  {
  destruct O4N as (o4',(o4'eq,Perm)).
  rewrite o4'eq in *.
  apply tmp4 with None.
  assumption.
  assumption.
  assumption.
  apply fs_op.
  assumption.
  exists (upd p3 (L ([[v]])) (Some (Locked (upd v0 ([[v]]) 0%nat) v1 v2))), p1.
  exists.
  apply phpdef_comm.
  assumption.
  exists bp3u, bp1, bp3up1.
  exists None, None.
  exists C1, C3.
  exists.
  apply None_op.
  split.
  unfold upd.
  rewrite eqz.
  reflexivity.
  split.
  simpl.
  unfold M_to_crd.
  simpl.
  destruct (M ([[v]])).
  inversion NEG.
  simpl.
  left.
  reflexivity.
  rewrite phplus_comm.
  tauto.
  apply phpdef_comm.
  assumption.
  }
  }

  assert (EQH: upd p (L ([[v]])) (Some (Locked (upd v0 ([[v]]) 0%nat) v1 v2)) =
    phplus p4 (phplus p1 (upd p3 (L ([[v]])) (Some (Locked (upd v0 ([[v]]) 0%nat) v1 v2))))).
  {
  rewrite <- p1p2.
  destruct tmp5 as (p3p4,tmp5).
  rewrite <- p3p4.
  rewrite phplus_comm.
  rewrite <- phplus_upd.
  rewrite <- phplus_upd.
  rewrite phplus_assoc.
  rewrite phplus_comm.
  rewrite phplus_assoc.
  reflexivity.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  unfold not.
  intros.
  destruct H as (v3,(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
  unfold not.
  intros.
  destruct H as (v3,(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
  rewrite p3p4.
  assumption.
  }

  assert (EQC: C = bagplus C4 (bagplus C1 C3)).
  {
  rewrite <- C1C2.
  destruct tmp5 as (p3p4,tmp5).
  rewrite <- tmp5.
  rewrite <- bplus_assoc.
  apply bplus_comm.
  }
  rewrite EQH.
  rewrite EQC.
  assumption.
Qed.

Lemma sat_wait4lock:
forall p O C l tx R I L M P X
      (SAT: sat p (Some O) C (weakest_pre_ct (Waiting4lock l, tx) R I L M P X)),
  (p ([[l]]) = Some Lock \/ exists wt ot ct, p ([[l]]) = Some (Locked wt ot ct))
  /\ prc ([[l]]) O R L P X = true.
(* /\
    forall p1 C1 wt ot ct (SAT1: sat p1 None C1 (Alasn (I ([[l]]) wt ot ct))),
      sat (phplus (upd p ([[l]]) (Some (Locked wt ot ct))) p1) (Some (([[l]]) :: O)) (bagplus C C1) (weakest_pre_ct (Val 0, tx) R I L M P X).*)
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
  apply prc_perm with v.
  apply sat4.
  assumption.
Qed.
