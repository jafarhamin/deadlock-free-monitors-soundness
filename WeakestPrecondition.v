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

(*
  simpl.
  intros.
  unfold weakest_pre_ct.
  simpl in *.
  replace (phplus (upd p ([[l]]) (Some (Locked wt ot ct))) p0) with 
    (phplus p2 (upd (phplus p1 p0) ([[l]]) (Some (Locked wt ot ct)))).
  replace (bagplus C C0) with (bagplus C2 (bagplus C1 C0)).
  apply sat2 with (O':=Some (([[l]]) :: O)) (v0:=wt) (v1:=ot) (v2:=ct).
admit.
admit.
admit.
  exists (emp knowledge), (upd (phplus p1 p0) ([[l]]) (Some (Locked wt ot ct))).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists (Some (([[l]]) :: O)), None.
  exists empb, (bagplus C1 C0).
  exists.
admit.
  exists.
admit.
  exists.
  exists (upd p1 ([[l]]) (Some (Locked wt ot ct))),p0.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists None, None.
  exists C1,C0.
  exists.
admit.
  exists.
admit.
  exists.
  assumption.
(* HERE STILL NEEDS *)
Admitted.
*)

Lemma sat_initl:
  forall p O C l tx R I L M P X
        (SAT: sat p (Some O) C (weakest_pre_ct (g_initl l, tx) R I L M P X)),
    exists p1 p2 wt ot ct C1 C2
           (BP1: boundph p1)
           (BP2: boundph p2)
           (phpdp1p2: phplusdef p1 p2)
           (p1p2: p = phplus p1 p2)
           (C1C2: C = bagplus C1 C2) 
           (P1l: p1 ([[l]]) = Some (Ulock wt ot ct))
           (p2inv: sat p2 None C2 (Alasn (I ([[l]]) wt ot ct)))
           (lll: L ([[l]]) = ([[l]]))
           (plf: P ([[l]]) = false)
           (NINxl: ~ In (R ([[l]])) (X (L ([[l]])))),
    sat (upd p1 ([[l]]) (Some Lock)) (Some O) C1
    (weakest_pre_ct (Val 0, tx) R I L M P X).
Proof.
  intros.
  simpl in SAT.
  destruct SAT as (v,(v0,(v1,(v2,(v3,(NEGB,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,
    (opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(o3,(o4,(C3,(C4,(opo3o4,(tmp5,(tmp3,tmp4))))))))))))).
Admitted.

(*
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(o5,(o6,(C5,(C6,(opo5o6,(tmp8,(tmp6,tmp7))))))))))))).

  assert (phpdefp14: phplusdef p1 p4).
  {
  apply phpdef_comm.
  apply phpdef_assoc_mon with p3.
  tauto.
  destruct tmp4 as (p3p4,C3C4).
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
  destruct tmp4 as (p3p4,C3C4).
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
  destruct tmp4 as (p3p4,C3C4).
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
  apply phpdef_assoc_mon with p4.
  rewrite phplus_comm.
  destruct tmp7 as (p56,C56).
  rewrite p56.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  replace (phplus p6 p5) with (phplus p5 p6).
  destruct tmp7 as (p56,C56).
  rewrite p56.
  replace (phplus p4 p3) with (phplus p3 p4).
  destruct tmp4 as (p34,C34).
  rewrite p34.
  assumption.
  apply phplus_comm.
  assumption.
  apply phplus_comm.
  assumption.
  }

  assert (phpdefp45: phplusdef p4 p5).
  {
  apply phpdef_comm.
  apply phpdef_assoc_mon with p6.
  apply phpdef_comm.
  tauto.
  rewrite phplus_comm.
  destruct tmp7 as (p56,C56).
  rewrite p56.
  assumption.
  apply phpdef_comm.
  assumption.
  }

  assert (phpdefp14p5: phplusdef (phplus p1 p4) p5).
  {
  apply phpdef_pair';
  tauto.
  }

  assert (eqp: p = phplus (phplus p1 p4) p5).
  {
  replace p5 with (phplus p5 p6).
  destruct tmp7 as (p56,C56).
  rewrite p56.
  rewrite phplus_assoc.
  replace (phplus p4 p3) with (phplus p3 p4).
  destruct tmp4 as (p34,C34).
  rewrite p34.
  symmetry.
  tauto.
  apply phplus_comm.
  tauto.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  destruct tmp6 as (p6N,rest).
  rewrite p6N.
  apply phplus_emp.
  }

  assert (eqc : C = bagplus (bagplus C1 C4) C5).
  {
  replace C5 with (bagplus C5 C6).
  destruct tmp7 as (p56,C56).
  rewrite C56.
  rewrite bplus_assoc.
  replace (bagplus C4 C3) with (bagplus C3 C4).
  destruct tmp4 as (p34,C34).
  rewrite C34.
  symmetry.
  tauto.
  apply bplus_comm.
  destruct tmp6 as (p6N,(C6N,rest)).
  rewrite C6N.
  apply bplus_emp.
  }

  exists (phplus p1 p4), p5, v1, v2, v3.
  exists (bagplus C1 C4) ,C5.
  exists bpp14, bp5, phpdefp14p5.
  exists eqp, eqc.
  exists.
admit.
  exists.
  assumption.
  exists.
admit.
  exists.
admit.
  exists.
admit.
admit.
*)

Lemma sat_wait:
  forall p O C v l tx R I L M P X
         (SAT: sat p (Some O) C (weakest_pre_ct (Wait v l, tx) R I L M P X)),
    exists p1 p2 wt ot ct C1 C2 O1
           (OO1: O = ([[l]]) :: O1)
           (BP1: boundph p1)
           (BP2: boundph p2)
           (phpdp1p2: phplusdef p1 p2)
           (p1p2: p = phplus p1 p2)
           (C1C2: C = bagplus C1 C2) 
           (p1l: p1 ([[l]]) = Some (Locked wt ot ct))
           (p1v: p1 ([[v]]) = Some Cond)
           (p2inv: sat p2 None C2 (Alasn (I ([[l]]) (upd wt ([[v]]) (S (wt ([[v]])))) ot ct)))
           (prcv: prc ([[v]]) O1 R L P X = true)
           (prcl: prc ([[l]]) O1 R L P X = true)
           (NEQlv: [[v]] <> [[l]])
           (Lvl: L ([[v]]) = [[l]])
           (SAFE_OBS: safe_obs ([[v]]) (S (wt ([[v]]))) (ot ([[v]])) R L P X = true),
      sat (upd p1 ([[l]]) (Some Lock)) (Some O1) C1
        (weakest_pre_ct (Waiting4cond v l, tx) R I L M P X).
Proof.
  simpl.
  intros.
  destruct SAT as (v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,
    (opo1o2,(tmp1,(tmp2,(p1p2,C1C2))))))))))))))).
  destruct tmp1 as (v1,(v2,(v3,(bl,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(o3,(o4,(C3,(C4,(opo3o4,(tmp1,(tmp3,tmp4))))))))))))))))).
  destruct tmp3 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(o5,(o6,(C5,(C6,(opo5o6,(tmp5,(tmp6,tmp7))))))))))))).
  destruct tmp6 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(o7,(o8,(C7,(C8,(opo7o8,(tmp8,(tmp9,tmp0))))))))))))).
  exists (phplus (phplus p5 p7) p2), p8, v1, v2, v3, (bagplus (bagplus C5 C7) C2), C8, v0.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
  assumption.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists v0.
  exists (phplus p5 (upd p7 ([[l]]) (Some Lock))), p2.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists (Some v0), None.
  exists (bagplus C5 C7), C2.
  exists.
admit.
  exists.
  split.
admit.
  exists p5, (upd p7 ([[l]]) (Some Lock)).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists None, (Some v0).
  exists C5, C7.
  exists.
admit.
  split.
  assumption.
  split.
  exists (upd p7 ([[l]]) (Some Lock)), (emp knowledge).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists None, (Some v0).
  exists C7, empb.
  exists.
admit.
  exists.
  left.
admit.
admit.
admit.
  split.
  intros.
  destruct SAT as (p9,(p0,(phpdefp9p0,(bp9,(bp0,(bp90,(o9,(o0,(C9,(C0,(opo9o0,(tmp01,(tmp00,tmp000))))))))))))).
  destruct tmp00 as (p19,(p10,(phpdefp19p10,(bp19,(bp10,(bp1910,(o19,(o10,(C19,(C10,(opo19o10,(tmp101,(tmp100,tmp1000))))))))))))).
  destruct tmp100 as (p29,(p20,(phpdefp29p20,(bp29,(bp20,(bp2920,(o29,(o20,(C29,(C20,(opo29o20,(tmp201,(tmp200,tmp2000))))))))))))).
  apply tmp2 with v4 v5 v6 O'.
  assumption.
  assumption.
  assumption.
admit.
  exists p9, p0, phpdefp9p0, bp9, bp0, bp90.
  exists (Some (([[l]]) :: v0)), None.
  exists empb, C'.
  exists.
admit.
  exists.
admit.
  exists.
  exists p19, p10, phpdefp19p10, bp19, bp10, bp1910.
  exists None, None.
  exists C19, C10.
  exists.
admit.
  exists.
  assumption.
  split.
  exists p29, p20, phpdefp29p20, bp29, bp20, bp2920.
  exists None, None.
  exists C29, C20.
  exists.
admit.
  auto.
admit.
admit.
admit.
Admitted.

Lemma sat_acquire:
  forall p O C l tx R I L M P X
        (SAT: sat p (Some O) C (weakest_pre_ct (Acquire l, tx) R I L M P X)),
  exists (Pl: p ([[l]]) = Some Lock)
         (PRCl: prc ([[l]]) O R L P X = true),
    forall p1 C1 wt ot ct (bp: boundph p1) (p1l : p1 ([[l]]) = Some Lock \/ p1 ([[l]]) = None)
          (SAT1: sat p1 None C1 (Alasn (I ([[l]]) wt ot ct))),
      sat (phplus (upd p ([[l]]) (Some (Locked wt ot ct))) p1) (Some (([[l]]) :: O)) (bagplus C C1) (weakest_pre_ct (Val 0, tx) R I L M P X).
Proof.
  intros.
  simpl in SAT.
  destruct SAT as (v,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,
    (opo1o2,(tmp1,(tmp2,(p1p2,C1C2))))))))))))))).
  destruct tmp1 as (PRC,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(o3,(o4,(C3,(C4,(opo3o4,(tmp1,(tmp3,tmp4)))))))))))))).
  split.
admit.
  split.
admit.
  intros.
  unfold weakest_pre_ct.
  simpl.
  assert (G: sat (phplus p2 (phplus (upd p1 ([[l]]) (Some (Locked wt ot ct))) p0))
    (Some (([[l]]) :: O)) (bagplus C2 (bagplus C1 C0))
    (weakest_pre_tx tx R I L M P X 0)).
  {
  apply tmp2 with wt ot ct (Some (([[l]]) :: O)).
admit.
admit.
admit.
admit.
  exists (emp knowledge), (phplus (upd p1 ([[l]]) (Some (Locked wt ot ct))) p0).
exists.
  apply phpdef_comm.
  apply phpdef_emp.
  exists boundph_emp.
  exists.
admit.
  exists.
admit.
  exists (Some (([[id l]]) :: v)), None, empb, (bagplus C1 C0).
  exists.
admit.
  split.
admit.
  split.
  exists (upd p1 ([[l]]) (Some (Locked wt ot ct))), p0.
  exists.
admit.
  exists.
admit.
  exists bp.
  exists.
admit.
  exists None, None, C1, C0.
  exists.
admit.
  split.
admit.
  split.
  simpl in SAT1.
  assumption.
admit.
admit.
  }
  assert (EQP: phplus (upd p ([[l]]) (Some (Locked wt ot ct))) p0 =
    phplus p2 (phplus (upd p1 ([[l]]) (Some (Locked wt ot ct))) p0)).
  {
admit.
  }
  assert (EQC: bagplus C C0 = bagplus C2 (bagplus C1 C0)).
  {
admit.
  }
  rewrite EQP.
  rewrite EQC.
  assumption.
Admitted.

Lemma sat_acquire0:
  forall p O C l tx R I L M P X
        (SAT: sat p (Some O) C (weakest_pre_ct (Acquire l, tx) R I L M P X)),
  exists (Pl: p ([[l]]) = Some Lock \/ 
              exists Wt Ot Ct : bag, p ([[id l]]) = Some (Locked Wt Ot Ct))
         (PRCl: prc ([[l]]) O R L P X = true),
    sat p (Some O) C (weakest_pre_ct (Waiting4lock l, tx) R I L M P X).
Proof.
  intros.
  simpl in SAT.
  destruct SAT as (v,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,
    (opo1o2,(tmp1,(tmp2,(p1p2,C1C2))))))))))))))).
  destruct tmp1 as (PRC,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(o3,(o4,(C3,(C4,(opo3o4,(tmp1,(tmp3,tmp4)))))))))))))).
  split.
admit.
  split.
admit.
  intros.
  simpl.
  exists v.
  split.
  assumption.
  exists p3, p2.
  exists.
admit.
  exists bp3, bp2.
  exists.
admit.
  exists (Some O), None.
  exists C3, C2.
  exists.
admit.
  split.
  exists p3, (emp knowledge).
  exists.
admit.
  exists bp3, boundph_emp.
admit.
  exists.
  intros.
  apply tmp2 with v0 v1 v2 O'.
  assumption.
  assumption.
  assumption.
admit.
  assumption.
admit.
Admitted.

Lemma sat_release:
  forall p O C l tx R I L M P X
        (SAT: sat p (Some O) C (weakest_pre_ct (Release l, tx) R I L M P X)),
    exists p1 p2 wt ot ct C1 C2 O1
           (O1eq: O = ([[l]])::O1)
           (BP1: boundph p1)
           (BP2: boundph p2)
           (phpdp1p2: phplusdef p1 p2)
           (p1p2: p = phplus p1 p2)
           (C1C2: C = bagplus C1 C2) 
           (P1l: p1 ([[l]]) = Some (Locked wt ot ct))
           (p2inv: sat p2 None C2 (Alasn (I ([[l]]) wt ot ct))),
    sat (upd p1 ([[l]]) (Some Lock)) (Some O1) C1
    (weakest_pre_ct (Val 0, tx) R I L M P X).
Proof.
  intros.
  simpl in SAT.
  destruct SAT as (v,(v0,(v1,(v2,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,
    (opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))).
  destruct tmp1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(o3,(o4,(C3,(C4,(opo3o4,(tmp1,(tmp3,tmp4))))))))))))).
  destruct tmp3 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(o5,(o6,(C5,(C6,(opo5o6,(tmp5,(tmp6,tmp7))))))))))))).
  exists (phplus p5 p2), p6, v0, v1, v2, (bagplus C2 C5), C6, v.
  exists.
admit.
  exists.
admit.
  exists bp6.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  unfold weakest_pre_ct.
  simpl.
  assert (G: sat (phplus p2 (upd p5 ([[l]]) (Some Lock))) (Some v) (bagplus C2 C5)
    (weakest_pre_tx tx R I L M P X 0)).
  {
  apply tmp2 with (Some v).
admit.
admit.
admit.
admit.
  exists (emp knowledge), (upd p5 ([[l]]) (Some Lock)).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists (Some v), None, empb, C5.
  exists.
admit.
  split.
admit.
  split.
admit.
admit.
Admitted.

Lemma sat_disch:
  forall p O C v tx R I L M P X
        (SAT: sat p (Some O) C (weakest_pre_ct (g_disch v, tx) R I L M P X)),
    exists wt ot ct O1
           (O1eq: O = ([[v]])::O1)
           (Pl: p (L ([[v]])) = Some (Locked wt ot ct))
           (Pv: p ([[v]]) = Some Cond)
           (INO: In ([[v]]) O)
           (SAFE_OBS: safe_obs ([[v]]) (wt ([[v]])) ((ot ([[v]])) - 1) R L P X = true),
      sat (upd p (L ([[v]])) (Some (Locked wt (decb ot ([[v]])) ct)))
       (Some O1) C
       (weakest_pre_ct (Val 0, tx) R I L M P X).
Proof.
  intros.
  simpl in SAT.
  destruct SAT as (v0,(v1,(v2,(v3,(SAFE,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,
    (opo1o2,(tmp1,(tmp2,(p1p2,C1C2))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(o3,(o4,(C3,(C4,(opo3o4,(tmp3,(tmp4,tmp5))))))))))))).
  destruct tmp4 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(o5,(o6,(C5,(C6,(opo5o6,(tmp6,(tmp7,tmp8))))))))))))).
  exists v1, v2, v3, v0.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  assert (G: sat (phplus p6 (upd (phplus p1 p5) (L ([[v]])) (Some (Locked v1 (decb v2 ([[v]])) v3))))
    (Some v0) (bagplus C6 (bagplus C1 C5)) (weakest_pre_tx tx R I L M P X 0)).
  {
  apply tmp7 with (Some v0).
admit.
admit.
admit.
admit.
  exists (emp knowledge), (upd (phplus p1 p5) (L ([[v]])) (Some (Locked v1 (decb v2 ([[v]])) v3))).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists (Some v0), None, empb, (bagplus C1 C5).
  exists.
admit.
  split.
admit.
  split.
admit.
admit.
Admitted.

Lemma sat_notify:
forall p O C v tx R I L M P X
      (SAT: sat p (Some O) C (weakest_pre_ct (Notify v, tx) R I L M P X)),
  exists wt ot ct C1 Cm (C1Cm: C = bagplus C1 Cm)
         (P1l: p (L ([[v]])) = Some (Locked wt ot ct)) 
         (P1l: p ([[v]]) = Some Cond)
         (MOVE: Cm = (fun x => if Z.eq_dec x ([[v]]) then if bool_dec (M ([[v]])) true then (if eq_nat_dec (wt ([[v]])) 0%nat then 0%nat else 1%nat) else 0%nat else 0%nat)),
    sat (upd p (L ([[v]])) (Some (Locked (upd wt ([[v]]) (wt ([[v]]) - 1)%nat) ot ct)))
    (Some O) C1 (weakest_pre_tx tx R I L M P X 0).
Proof.
  intros.
  simpl in SAT.
  destruct SAT as (v0,(v1,(v2,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,
    (opo1o2,(tmp1,(tmp2,(p1p2,C1C2))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(o3,(o4,(C3,(C4,(opo3o4,(tmp3,(tmp4,tmp5))))))))))))).
  destruct tmp4 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(o5,(o6,(C5,(C6,(opo5o6,(tmp6,(tmp7,tmp8))))))))))))).
  unfold M_to_crd in tmp6.
  exists v0, v1, v2.

  exists (fun x => if Z.eq_dec x ([[v]]) then if bool_dec (M ([[v]])) true then
    if Nat.eq_dec (v0 ([[v]])) 0 then (C x) else ((C x) - 1)%nat else (C x) else (C x)).
  exists (fun x => if Z.eq_dec x ([[v]]) then if bool_dec (M ([[v]])) true then
    if Nat.eq_dec (v0 ([[v]])) 0 then 0%nat else 1%nat else 0%nat else 0%nat).
  exists.
  {
  unfold id in tmp6.
  unfold bagplus.
  apply functional_extensionality.
  intros.
  destruct (M ([[v]])).
  simpl.
  simpl in tmp6.
  destruct (Z.eq_dec x ([[v]])).
  destruct (Nat.eq_dec (v0 ([[v]])) 0).
  omega.
  assert (CX: lt 0 (C x)).
admit.
  omega.
  omega.
  destruct (Z.eq_dec x ([[v]]));
  simpl;
  omega.
  }
  exists.
admit.
  exists.
admit.
  exists.
  reflexivity.
  assert (G: sat (phplus p6 (phplus (upd (phplus p1 p3) (L ([[v]]))
     (Some (Locked (upd v0 ([[v]]) (v0 ([[v]]) - 1)%nat) v1 v2))) p5)) (Some O)
     (bagplus C6 (bagplus (bagplus C1 C3) (fun x => if Z.eq_dec x ([[v]]) then if bool_dec (M ([[v]])) true then
    if Nat.eq_dec (v0 ([[v]])) 0 then (C5 x) else ((C5 x) - 1)%nat else (C5 x) else (C5 x))))
    (weakest_pre_tx tx R I L M P X 0)).
  {
  apply tmp7 with None.
admit.
admit.
admit.
admit.
  exists ((upd (phplus p1 p3) (L ([[v]]))
       (Some (Locked (upd v0 ([[v]]) (v0 ([[v]]) - 1)%nat) v1 v2)))), p5.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists None, None.
  exists (bagplus C1 C3), (fun x : Z => if Z.eq_dec x ([[v]]) then
    if bool_dec (M ([[v]])) true then if Nat.eq_dec (v0 ([[v]])) 0 then C5 x 
    else (C5 x - 1)%nat else C5 x else C5 x).
  exists.
admit.
  split.
admit.
  split.
  {
  simpl.
  assert (SAT:=tmp6).
  unfold id in *.
  destruct (M ([[v]])).
  simpl in *.
  destruct (Nat.eq_dec (v0 ([[v]])) 0).
  rewrite eqz.
  left.
  assumption.
  rewrite eqz.
  right.
  apply Nat.ltb_lt.
  omega.
  simpl.
  left.
  reflexivity.
  }
  split.
  reflexivity.
  reflexivity.
  }
  assert (EQH: upd p (L ([[v]])) (Some (Locked (upd v0 ([[v]]) (v0 ([[v]]) - 1)%nat) v1 v2)) =
    phplus p6 (phplus (upd (phplus p1 p3) (L ([[v]])) (Some (Locked (upd v0 ([[v]]) (v0 ([[v]]) - 1)%nat) v1 v2))) p5)).
  {
admit.
  }
  assert (EQC: (fun x : Z => if Z.eq_dec x ([[v]]) then if bool_dec (M ([[v]])) true 
    then if Nat.eq_dec (v0 ([[v]])) 0 then C x else (C x - 1)%nat else C x else C x) =
    bagplus C6 (bagplus (bagplus C1 C3) (fun x : Z => if Z.eq_dec x ([[v]])
    then if bool_dec (M ([[v]])) true then if Nat.eq_dec (v0 ([[v]])) 0 then C5 x else (C5 x - 1)%nat
    else C5 x else C5 x))).
  {
admit.
  }
  rewrite EQH.
  rewrite EQC.
  assumption.
Admitted.

Lemma sat_fork:
  forall p O C c tx R I L M P X
         (SAT: sat p (Some O) C (weakest_pre_ct (Fork c, tx) R I L M P X)),
    exists p1 p2 O1 O2 C1 C2 (BP1: boundph p1) (BP2: boundph p2) (PHPD: phplusdef p1 p2) (p1p2: p = phplus p1 p2) (O1O2: Permutation.Permutation (O1++O2) O) (C1C2: C = bagplus C1 C2)
     (SAT1: sat p1 (Some O1) C1 (weakest_pre_tx tx R I L M P X 0))
     (SAT2: sat p2 (Some O2) C2 (weakest_pre c (fun _ : Z => Aobs nil) id R I L M P X)), True.
Proof.
  intros.
  simpl in SAT.
  destruct SAT as (v,(v0,(p1,(p2,(phpp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opo1o2,(tmp1,(tmp2,tmp3))))))))))))))).
  destruct tmp1 as (p3,(p4,(phpp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(opo3o4,(tmp4,(tmp5,tmp6))))))))))))).
  exists p4, p2, v, v0, C4, C2, bp4, bp2.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  exists.
  replace p4 with (phplus p4 (emp knowledge)).
  replace C4 with (bagplus C4 empb).
  {
  apply tmp5 with (Some v).
admit.
admit.
admit.
admit.
admit.
  }
  apply bplus_emp.
  apply phplus_emp.
  exists.
  replace p2 with (phplus p2 (emp knowledge)).
  replace C2 with (bagplus C2 empb).
  {
  apply tmp2 with (Some v0).
admit.
admit.
admit.
admit.
admit.
  }
  apply bplus_emp.
  apply phplus_emp.
  trivial.
Admitted.

(*
Lemma sat_frame:
  forall c f Q p1 p2 o1 o2 C1 C2 R I L M P X se
         (phpdefp1p2: phplusdef p1 p2) o1o2 (opo1o2: oplus o1 o2 o1o2) (bp1 : boundph p1) (bp2 : boundph p2) (bp12 : boundph (phplus p1 p2))
         (SATF: sat p2 o2 C2 f)
         (SATQ: sat p1 o1 C1 (weakest_pre c Q se R I L M P X)),
    sat (phplus p1 p2) o1o2 (bagplus C1 C2) (weakest_pre c (fun x : Z => (Q x) ** f) se R I L M P X).
Proof.
  induction c;
  simpl;
  intros;
  try auto.
  {
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, o1, o2, C1, C2, opo1o2.
  auto.
  }
  {
  assert (tmp: phplusdef p1 p' /\ phplusdef p2 p').
  apply phpdef_dist.
  assumption.
  assumption.
  exists (phplus p1 p'), p2.
  exists.
  apply phpdef_assoc'.
  tauto.
  assumption.
  apply phpdef_comm.
  tauto.
  exists.
  apply phplus_boundph.
  tauto.
  exists.
  assumption.
  inversion OPLUS.
  rewrite <- H in *.
  inversion opo1o2.
  rewrite <- H0, <- H1, <- H2, <- H3 in *.
  exists None, None.
  exists (bagplus C1 C'), C2.
  exists.
  apply None_op.
  split.
  apply SATQ with O'.
  assumption.
  tauto.
  rewrite <- H0.
  apply None_op.
  assumption.
  split.
  assumption.
  split.
  rewrite phplus_assoc.
  replace (phplus p' p2) with (phplus p2 p').
  rewrite phplus_assoc.
  reflexivity.
  assumption.
  tauto.
  tauto.
  apply phplus_comm.
  tauto.
  tauto.
  assumption.
  apply phpdef_comm.
  tauto.
  rewrite bplus_assoc.
  replace (bagplus C' C2) with (bagplus C2 C').
  rewrite bplus_assoc.
  reflexivity.
  apply bplus_comm.
  exists o1, o2.
  exists (bagplus C1 C'), C2.
  exists.
  rewrite <- H in *.
  inversion opo1o2.
  apply fs_op.
  apply Permutation_trans with o.
  assumption.
  assumption.
  apply sn_op.
  apply Permutation_trans with o.
  assumption.
  assumption.
  split.
  apply SATQ with O'.
  assumption.
  tauto.
  rewrite <- H0.
  destruct o1.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  assumption.
  split.
  assumption.
  split.
  rewrite phplus_assoc.
  replace (phplus p' p2) with (phplus p2 p').
  rewrite phplus_assoc.
  reflexivity.
  assumption.
  tauto.
  tauto.
  apply phplus_comm.
  tauto.
  tauto.
  assumption.
  apply phpdef_comm.
  tauto.
  rewrite bplus_assoc.
  replace (bagplus C' C2) with (bagplus C2 C').
  rewrite bplus_assoc.
  reflexivity.
  apply bplus_comm.
  rewrite <- H in *.
  inversion opo1o2.
  exists O', None.
  exists (bagplus C1 C'), C2.
  exists.
  rewrite <- H0.
  apply fs_op.
  assumption.
  split.
  apply SATQ with O'.
  assumption.
  tauto.
  rewrite <- H2, <- H0.
  apply sn_op.
  apply Permutation_refl.
  assumption.
  split.
  rewrite H3.
  assumption.
  split.
  rewrite phplus_assoc.
  replace (phplus p' p2) with (phplus p2 p').
  rewrite phplus_assoc.
  reflexivity.
  assumption.
  tauto.
  tauto.
  apply phplus_comm.
  tauto.
  tauto.
  assumption.
  apply phpdef_comm.
  tauto.
  rewrite bplus_assoc.
  replace (bagplus C' C2) with (bagplus C2 C').
  rewrite bplus_assoc.
  reflexivity.
  apply bplus_comm.
  }
  {
  destruct SATQ as (v,(v0,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opO3O4,(sat1,(sat2,(p3p4,C3C4))))))))))))))).
  assert (phpdef234: phplusdef p3 p2 /\ phplusdef p4 p2).
  {
  apply phpdef_dist.
  rewrite p3p4.
  assumption.
  assumption.
  }
  exists v, v0, p3, (phplus p2 p4).
  exists.
  apply phpdef_assoc.
  apply phpdef_comm.
  tauto.
  tauto.
  assumption.
  exists bp3.
  exists.
  apply phplus_boundph.
  apply phpdef_comm.
  tauto.
  assert (tmp: exists o2o4, oplus o2 o4 o2o4).
  {
  apply oplus_exists.
  destruct o2.
  inversion opo1o2.
  rewrite <- H in opO3O4.
  inversion opO3O4.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct tmp as (o2o4,opo2o4).
  exists o3, o2o4, C3, (bagplus C2 C4).
  exists.
  apply oplus_assoc with o1 o2 o4.
  assumption.
  assumption.
  assumption.
  split.
  assumption.
  split.
  intros.
  assert (phpdef24p': phplusdef p2 p' /\ phplusdef p4 p').
  {
  apply phpdef_dist.
  assumption.
  apply phpdef_comm.
  tauto.
  }
  exists (phplus p4 p'), p2.
  exists.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  exists.
  apply phplus_boundph.
  tauto.
  exists bp2.
  assert (tmp: exists o4o', oplus o4 O' o4o').
  {
  apply oplus_exists.
  destruct o4.
  inversion opO3O4.
  inversion opo2o4.
  rewrite <- H3 in OPLUS.
  inversion OPLUS.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct tmp as (o4o',opo4o').
  exists o4o', o2, (bagplus C4 C'), C2.
  exists.
  apply oplus_comm.
  apply oplus_assoc with o2o4 O' o4.
  assumption.
  assumption.
  apply oplus_comm.
  assumption.
  split.
  eapply sat2 with O'.
  assumption.
  tauto.
  assumption.
  assumption.
  split.
  assumption.
  rewrite phplus_comm.
  rewrite phplus_assoc.
  rewrite bplus_comm.
  rewrite bplus_assoc.
  auto.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  rewrite phplus_comm.
  rewrite phplus_assoc.
  rewrite phplus_comm in p3p4.
  rewrite p3p4.
  rewrite phplus_comm.
  rewrite bplus_comm.
  rewrite bplus_assoc.
  rewrite bplus_comm in C3C4.
  rewrite C3C4.
  rewrite bplus_comm.
  auto.
  apply phpdef_comm.
  assumption.
  assumption.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  assumption.
  apply phpdef_assoc.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  }
  {
  destruct SATQ as (v,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opO3O4,(SAT1,(SAT3,(p3p4,C3C4)))))))))))))).
  assert (phpdefp342: phplusdef p3 p2 /\ phplusdef p4 p2).
  {
  apply phpdef_dist.
  rewrite p3p4.
  assumption.
  assumption.
  }
  exists v, p3, (phplus p2 p4).
  exists.
  apply phpdef_assoc.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  exists bp3.
  exists.
  apply phplus_boundph.
  apply phpdef_comm.
  tauto.
  assert (o2o4: exists o2o4, oplus o2 o4 o2o4).
  {
  apply oplus_exists.
  destruct o2.
  inversion opo1o2.
  rewrite <- H in *.
  inversion opO3O4.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o2o4 as (o2o4, opo2o4).
  exists o3, o2o4.
  exists C3, (bagplus C2 C4).
  exists.
  apply oplus_assoc with o1 o2 o4.
  assumption.
  assumption.
  assumption.
  split.
  assumption.
  split.
  intros.
  assert (phpdefp24p': phplusdef p2 p' /\ phplusdef p4 p').
  {
  apply phpdef_dist.
  assumption.
  apply phpdef_comm.
  tauto.
  }
  exists (phplus p4 p'),p2.
  exists.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  exists.
  apply phplus_boundph.
  tauto.
  exists bp2.
  assert (o4o': exists o4o', oplus o4 O' o4o').
  {
  apply oplus_exists.
  destruct o4.
  inversion opO3O4.
  rewrite <- H0 in *.
  inversion opo2o4.
  rewrite <- H3 in *.
  inversion OPLUS.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o4o' as (o4o', opo4o').
  exists o4o', o2.
  exists (bagplus C4 C'), C2.
  exists.
  apply oplus_comm.
  apply oplus_assoc with o2o4 O' o4.
  assumption.
  assumption.
  apply oplus_comm.
  assumption.
  split.
  apply SAT3 with O'.
  assumption.
  tauto.
  assumption.
  assumption.
  split.
  assumption.
  rewrite phplus_comm.
  rewrite phplus_assoc.
  rewrite phplus_comm in p3p4.
  rewrite bplus_comm.
  rewrite bplus_assoc.
  rewrite bplus_comm in C3C4.
  auto.
  assumption.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  rewrite phplus_comm.
  rewrite phplus_assoc.
  rewrite phplus_comm in p3p4.
  rewrite phplus_comm.
  rewrite bplus_comm.
  rewrite p3p4.
  rewrite bplus_assoc.
  rewrite bplus_comm in C3C4.
  rewrite C3C4.
  rewrite bplus_comm.
  auto.
  apply phpdef_assoc.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_assoc.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  }

  {
  destruct SATQ as (v,(v0,(p1',(p2',(phpdefp1p2',(bp1',(bp2',(o1',(o2',(C1',(C2',(opo1'o2',tmp)))))))))))).
  destruct tmp as (tmp1,(tmp2,(p1p2,C1C2))).
  assert (phpdefp122: phplusdef p1' p2 /\ phplusdef p2' p2).
  {
  apply phpdef_dist.
  rewrite p1p2.
  assumption.
  assumption.
  }
  exists v, v0, (phplus p1' p2), p2'.
  exists.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  exists.
  apply phplus_boundph.
  tauto.
  exists bp2'.
  exists o1'.
  assert (o2'o2: exists o2'o2, oplus o2' o2 o2'o2).
  {
  apply oplus_exists.
  destruct o2'.
  inversion opo1'o2'.
  rewrite <- H0 in *.
  inversion opo1o2.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o2'o2 as (o2'o2, eqo2'o2).
  exists o2'o2.
  exists (bagplus C1' C2), C2'.
  exists.
  inversion opo1o2.
  rewrite <- H, <- H0, <- H1 in *.  
  inversion opo1'o2'.
  rewrite <- H2, <- H3 in *.
  inversion eqo2'o2.
  apply None_op.
  rewrite <- H, <- H0, <- H1 in *.
  inversion opo1'o2'.
  rewrite <- H2, <- H3, <- H5 in *.
  inversion eqo2'o2.
  apply fs_op.
  apply Permutation_trans with o'0.
  assumption.
  assumption.
  rewrite <- H2, <- H3, <- H5 in *.
  inversion eqo2'o2.
  apply sn_op.
  apply Permutation_trans with o0.
  apply Permutation_sym.
  assumption.
  apply Permutation_trans with o'0.
  assumption.
  assumption.
  rewrite <- H, <- H0, <- H1 in *.
  inversion opo1'o2'.
  rewrite <- H2, <- H3 in *.
  inversion eqo2'o2.
  apply sn_op.
  apply Permutation_trans with o.
  apply Permutation_sym.
  assumption.
  assumption.
  split.
  destruct tmp1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opo3o4,(tmp1,(tmp4,(p3p4,C3C4))))))))))))).
  assert (phpdefp342: phplusdef p3 p2 /\ phplusdef p4 p2).
  {
  apply phpdef_dist.
  rewrite p3p4.
  tauto.
  assumption.
  }
  exists p3, (phplus p4 p2).
  exists.
  apply phpdef_assoc.
  tauto.
  tauto.
  tauto.
  exists bp3.
  exists.
  apply phplus_boundph.
  tauto.
  exists o3,o4.
  exists empb, (bagplus C1' C2).
  exists.
  assumption.
  split.
  tauto.
  split.
  intros.
  exists p4, p2.
  exists.
  tauto.
  exists bp4, bp2.
  exists O'', None.
  exists C4, C2.
  exists.
  destruct O''.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  split.
  replace C4 with (bagplus C4 empb).
  replace p4 with (phplus p4 (emp knowledge)).
  apply tmp4 with O'.
  apply boundph_emp.
  apply phpdef_emp.
  assumption.
  tauto.
  apply phplus_emp.
  apply bplus_emp.
  destruct SAT as (p'N,(C'N,OP)).
  rewrite p'N, C'N.
  split.
  destruct o2.
  inversion opo1o2.
  destruct tmp1 as (p3N, (C3N, opo3)).
  inversion opo3.
  rewrite <- H4 in opo3o4.
  inversion opo3o4.
  rewrite <- H6 in opo1'o2'.
  rewrite <- H in opo1'o2'.
  inversion opo1'o2'.
  assumption.
  rewrite phplus_emp.
  rewrite bplus_emp.
  rewrite <- C3C4.
  destruct tmp1 as (p3N, (C3N, opo3)).
  rewrite C3N.
  replace (bagplus empb C4) with C4.
  auto.
  rewrite bplus_comm.
  symmetry.
  apply bplus_emp.
  rewrite <- phplus_assoc.
  rewrite p3p4.
  rewrite bplus_comm.
  rewrite bplus_emp.
  auto.
  tauto.
  tauto.
  tauto.
  split.
  intros.
  apply tmp2 with O'.
  assumption.
  tauto.
  destruct o2.
  inversion opo1o2.
  inversion eqo2'o2.
  destruct SAT as (p'N,(C'N,OP)).
  inversion OP.
  rewrite <- H7 in OPLUS.
  inversion OPLUS.
  apply sn_op.
  assumption.
  inversion eqo2'o2.
  rewrite H1.
  assumption.
  rewrite <- H1 in OPLUS.
  inversion OPLUS.
  apply fs_op.
  apply Permutation_trans with o'.
  assumption.
  assumption.
  assumption.
  rewrite phplus_comm.
  rewrite <- phplus_assoc.
  replace (phplus p2' p1') with (phplus p1' p2').
  rewrite p1p2.
  rewrite bplus_comm.
  rewrite <- bplus_assoc.
  replace (bagplus C2' C1') with (bagplus C1' C2').
  rewrite C1C2.
  auto.
  apply bplus_comm.
  apply phplus_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  }

  {
  eapply sat_weak_imp.
  apply phplus_boundph.
  assumption.
  apply IHc1 with o1 o2.
  assumption.
  assumption.
  assumption.
  assumption.
  apply SATF.
  apply SATQ.
  simpl.
  intros.
  destruct SAT as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opO3O4,(SAT1,(SAT3,(p3p4,C3C4))))))))))))).
  rewrite <- p3p4.
  rewrite <- C3C4.
  apply IHc2 with o3 o4.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  {
  specialize SATQ with v.
  destruct SATQ as (v0,(v1,SATQ)).
  exists v0, v1.
  intros.
  destruct SAT as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opO3O4,(SAT1,(SAT3,(p3p4,C3C4))))))))))))).
  assert (phpdefp12': phplusdef p1 p' /\ phplusdef p2 p').
  {
  apply phpdef_dist.
  assumption.
  assumption.
  }
  exists (phplus p1 p'), p2.
  exists.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  exists.
  apply phplus_boundph.
  tauto.
  exists bp2.
  assert (o1o': exists o1o', oplus o1 O' o1o').
  {
  apply oplus_exists.
  destruct o1.
  inversion opo1o2.
  rewrite <- H2 in *.
  inversion OPLUS.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o1o' as (o1o', opo1o').
  exists o1o',o2.
  exists (bagplus C1 C'), C2.
  exists.
  apply oplus_comm.
  apply oplus_assoc with o1o2 O' o1.
  assumption.
  apply oplus_comm.
  assumption.
  apply oplus_comm.
  assumption.
  split.
  apply SATQ with O'.
  assumption.
  tauto.
  assumption.
  exists p3, p4, phpdefp3p4, bp3, bp4, o3, o4, C3, C4, opO3O4.
  auto.
  split.
  assumption.
  rewrite phplus_comm.
  rewrite <- phplus_assoc.
  replace (phplus p2 p1) with (phplus p1 p2).
  rewrite bplus_comm.
  rewrite <- bplus_assoc.
  replace (bagplus C2 C1) with (bagplus C1 C2).
  auto.
  apply bplus_comm.
  apply phplus_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  }
  {
  destruct SATQ as (v,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opO3O4,(SAT1,(SAT3,(p3p4,C3C4)))))))))))))).
  assert (phpdefp342: phplusdef p3 p2 /\ phplusdef p4 p2).
  {
  apply phpdef_dist.
  rewrite p3p4.
  assumption.
  assumption.
  }
  exists v, p3, (phplus p2 p4).
  exists.
  apply phpdef_assoc.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  exists bp3.
  exists.
  apply phplus_boundph.
  apply phpdef_comm.
  tauto.
  assert (o2o4: exists o2o4, oplus o2 o4 o2o4).
  {
  apply oplus_exists.
  destruct o2.
  inversion opo1o2.
  rewrite <- H in *.
  inversion opO3O4.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o2o4 as (o2o4, opo2o4).
  exists o3, o2o4.
  exists C3, (bagplus C2 C4).
  exists.
  apply oplus_assoc with o1 o2 o4.
  assumption.
  assumption.
  assumption.
  split.
  assumption.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(o5,(o6,(C5,(C6,(opO5O6,(SAT5,(SAT6,(p5p6,C5C6))))))))))))).
  assert (phpdefp24': phplusdef p2 p' /\ phplusdef p4 p').
  {
  apply phpdef_dist.
  assumption.
  apply phpdef_comm.
  tauto.
  }

  exists (phplus p4 p'),p2.
  exists.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  exists.
  apply phplus_boundph.
  tauto.
  exists bp2.
  assert (o4o': exists o4o', oplus o4 O' o4o').
  {
  apply oplus_exists.
  destruct o4.
  inversion opO3O4.
  rewrite <- H0 in *.
  inversion opo2o4.
  rewrite <- H3 in *.
  inversion OPLUS.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o4o' as (o4o', opo4o').
  exists o4o', o2.
  exists (bagplus C4 C'), C2.
  exists.
  apply oplus_comm.
  apply oplus_assoc with o2o4 O' o4.
  assumption.
  assumption.
  apply oplus_comm.
  assumption.
  split.
  apply SAT3 with v0 v1 v2 O'.
  assumption.
  tauto.
  assumption.
  exists p5, p6, phpdefp5p6, bp5, bp6, o5, o6, C5, C6, opO5O6.
  split.
  assumption.
  split.
  assumption.
  auto.
  split.
  assumption.
  rewrite phplus_comm.
  rewrite phplus_assoc.
  rewrite bplus_comm.
  rewrite bplus_assoc.
  auto.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  rewrite phplus_comm.
  rewrite phplus_assoc.
  replace (phplus p4 p3) with (phplus p3 p4).
  rewrite p3p4.
  rewrite phplus_comm.
  rewrite bplus_comm.
  rewrite bplus_assoc.
  replace (bagplus C4 C3) with (bagplus C3 C4).
  rewrite C3C4.
  rewrite bplus_comm.
  auto.
  apply bplus_comm.
  apply phpdef_comm.
  tauto.
  apply phplus_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_assoc.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  }
  {
  destruct SATQ as (v,(v0,(v1,(v2,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opO3O4,(SAT1,(SAT3,(p3p4,C3C4))))))))))))))))).
  assert (phpdefp342: phplusdef p3 p2 /\ phplusdef p4 p2).
  {
  apply phpdef_dist.
  rewrite p3p4.
  assumption.
  assumption.
  }
  exists v, v0, v1, v2.
  exists p3, (phplus p2 p4).
  exists.
  apply phpdef_assoc.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  exists bp3.
  exists.
  apply phplus_boundph.
  apply phpdef_comm.
  tauto.
  assert (o2o4: exists o2o4, oplus o2 o4 o2o4).
  {
  apply oplus_exists.
  destruct o2.
  inversion opo1o2.
  rewrite <- H in *.
  inversion opO3O4.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o2o4 as (o2o4, opo2o4).
  exists o3, o2o4.
  exists C3, (bagplus C2 C4).
  exists.
  apply oplus_assoc with o1 o2 o4.
  assumption.
  assumption.
  assumption.
  split.
  assumption.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(o5,(o6,(C5,(C6,(opO5O6,(SAT5,(SAT6,(p5p6,C5C6))))))))))))).
  assert (phpdefp24': phplusdef p2 p' /\ phplusdef p4 p').
  {
  apply phpdef_dist.
  assumption.
  apply phpdef_comm.
  tauto.
  }
  exists (phplus p4 p'),p2.
  exists.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  exists.
  apply phplus_boundph.
  tauto.
  exists bp2.
  assert (o4o': exists o4o', oplus o4 O' o4o').
  {
  apply oplus_exists.
  destruct o4.
  inversion opO3O4.
  rewrite <- H0 in *.
  inversion opo2o4.
  rewrite <- H3 in *.
  inversion OPLUS.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o4o' as (o4o', opo4o').
  exists o4o', o2.
  exists (bagplus C4 C'), C2.
  exists.
  apply oplus_comm.
  apply oplus_assoc with o2o4 O' o4.
  assumption.
  assumption.
  apply oplus_comm.
  assumption.
  split.
  apply SAT3 with O'.
  assumption.
  tauto.
  assumption.
  exists p5, p6, phpdefp5p6, bp5, bp6, o5, o6, C5, C6, opO5O6.
  split.
  assumption.
  split.
  assumption.
  auto.
  split.
  assumption.
  rewrite phplus_comm.
  rewrite phplus_assoc.
  rewrite bplus_comm.
  rewrite bplus_assoc.
  auto.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  rewrite phplus_comm.
  rewrite phplus_assoc.
  replace (phplus p4 p3) with (phplus p3 p4).
  rewrite p3p4.
  rewrite phplus_comm.
  rewrite bplus_comm.
  rewrite bplus_assoc.
  replace (bagplus C4 C3) with (bagplus C3 C4).
  rewrite C3C4.
  rewrite bplus_comm.
  auto.
  apply bplus_comm.
  apply phpdef_comm.
  tauto.
  apply phplus_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_assoc.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  }
  {
  destruct SATQ as (v,(PRC,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opO3O4,(SAT1,(SAT3,(p3p4,C3C4))))))))))))))).
  assert (phpdefp342: phplusdef p3 p2 /\ phplusdef p4 p2).
  {
  apply phpdef_dist.
  rewrite p3p4.
  assumption.
  assumption.
  }
  exists v.
  split.
  assumption.
  exists p3, (phplus p2 p4).
  exists.
  apply phpdef_assoc.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  exists bp3.
  exists.
  apply phplus_boundph.
  apply phpdef_comm.
  tauto.
  assert (o2o4: exists o2o4, oplus o2 o4 o2o4).
  {
  apply oplus_exists.
  destruct o2.
  inversion opo1o2.
  rewrite <- H in *.
  inversion opO3O4.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o2o4 as (o2o4, opo2o4).
  exists o3, o2o4.
  exists C3, (bagplus C2 C4).
  exists.
  apply oplus_assoc with o1 o2 o4.
  assumption.
  assumption.
  assumption.
  split.
  assumption.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(o5,(o6,(C5,(C6,(opO5O6,(SAT5,(SAT6,(p5p6,C5C6))))))))))))).
  assert (phpdefp24': phplusdef p2 p' /\ phplusdef p4 p').
  {
  apply phpdef_dist.
  assumption.
  apply phpdef_comm.
  tauto.
  }
  exists (phplus p4 p'),p2.
  exists.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  exists.
  apply phplus_boundph.
  tauto.
  exists bp2.
  assert (o4o': exists o4o', oplus o4 O' o4o').
  {
  apply oplus_exists.
  destruct o4.
  inversion opO3O4.
  rewrite <- H0 in *.
  inversion opo2o4.
  rewrite <- H3 in *.
  inversion OPLUS.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o4o' as (o4o', opo4o').
  exists o4o', o2.
  exists (bagplus C4 C'), C2.
  exists.
  apply oplus_comm.
  apply oplus_assoc with o2o4 O' o4.
  assumption.
  assumption.
  apply oplus_comm.
  assumption.
  split.
  apply SAT3 with v0 v1 v2 O'.
  assumption.
  tauto.
  assumption.
  exists p5, p6, phpdefp5p6, bp5, bp6, o5, o6, C5, C6, opO5O6.
  split.
  assumption.
  split.
  assumption.
  auto.
  split.
  assumption.
  rewrite phplus_comm.
  rewrite phplus_assoc.
  rewrite bplus_comm.
  rewrite bplus_assoc.
  auto.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  rewrite phplus_comm.
  rewrite phplus_assoc.
  replace (phplus p4 p3) with (phplus p3 p4).
  rewrite p3p4.
  rewrite phplus_comm.
  rewrite bplus_comm.
  rewrite bplus_assoc.
  replace (bagplus C4 C3) with (bagplus C3 C4).
  rewrite C3C4.
  rewrite bplus_comm.
  auto.
  apply bplus_comm.
  apply phpdef_comm.
  tauto.
  apply phplus_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_assoc.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  }
  {
  specialize SATQ with v.
  destruct SATQ as (v0,(v1,(v2,(v3,SATQ)))).
  exists v0, v1, v2, v3.
  intros.
  assert (phpdefp12': phplusdef p1 p' /\ phplusdef p2 p').
  {
  apply phpdef_dist.
  assumption.
  assumption.
  }
  exists (phplus p1 p'), p2.
  exists.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  exists.
  apply phplus_boundph.
  tauto.
  exists bp2.
  assert (o1o': exists o1o', oplus o1 O' o1o').
  {
  apply oplus_exists.
  destruct o1.
  inversion opo1o2.
  rewrite <- H2 in *.
  inversion OPLUS.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o1o' as (o1o', opo1o').
  exists o1o', o2.
  exists (bagplus C1 C'), C2.
  exists.
  apply oplus_comm.
  apply oplus_assoc with o1o2 O' o1.
  assumption.
  apply oplus_comm.
  assumption.
  apply oplus_comm.
  assumption.
  split.
  apply SATQ with O'.
  assumption.
  tauto.
  assumption.
  assumption.
  split.
  assumption.
  rewrite phplus_comm.
  rewrite <- phplus_assoc.
  replace (phplus p2 p1) with (phplus p1 p2).
  rewrite bplus_comm.
  rewrite <- bplus_assoc.
  replace (bagplus C2 C1) with (bagplus C1 C2).
  auto.
  apply bplus_comm.
  apply phplus_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  }

  {
  destruct SATQ as (v,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opO3O4,(SAT1,(SAT3,(p3p4,C3C4)))))))))))))).
  assert (phpdefp342: phplusdef p3 p2 /\ phplusdef p4 p2).
  {
  apply phpdef_dist.
  rewrite p3p4.
  assumption.
  assumption.
  }
  exists v.
  exists p3, (phplus p2 p4).
  exists.
  apply phpdef_assoc.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  exists bp3.
  exists.
  apply phplus_boundph.
  apply phpdef_comm.
  tauto.
  assert (o2o4: exists o2o4, oplus o2 o4 o2o4).
  {
  apply oplus_exists.
  destruct o2.
  inversion opo1o2.
  rewrite <- H in *.
  inversion opO3O4.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o2o4 as (o2o4, opo2o4).
  exists o3, o2o4.
  exists C3, (bagplus C2 C4).
  exists.
  apply oplus_assoc with o1 o2 o4.
  assumption.
  assumption.
  assumption.
  split.
  assumption.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(o5,(o6,(C5,(C6,(opO5O6,(SAT5,(SAT6,(p5p6,C5C6))))))))))))).
  assert (phpdefp24': phplusdef p2 p' /\ phplusdef p4 p').
  {
  apply phpdef_dist.
  assumption.
  apply phpdef_comm.
  tauto.
  }
  exists (phplus p4 p'),p2.
  exists.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  exists.
  apply phplus_boundph.
  tauto.
  exists bp2.
  assert (o4o': exists o4o', oplus o4 O' o4o').
  {
  apply oplus_exists.
  destruct o4.
  inversion opO3O4.
  rewrite <- H0 in *.
  inversion opo2o4.
  rewrite <- H3 in *.
  inversion OPLUS.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o4o' as (o4o', opo4o').
  exists o4o', o2.
  exists (bagplus C4 C'), C2.
  exists.
  apply oplus_comm.
  apply oplus_assoc with o2o4 O' o4.
  assumption.
  assumption.
  apply oplus_comm.
  assumption.
  split.
  apply SAT3 with v0 v1 v2 O'.
  assumption.
  tauto.
  assumption.
  exists p5, p6, phpdefp5p6, bp5, bp6, o5, o6, C5, C6, opO5O6.
  split.
  assumption.
  split.
  assumption.
  auto.
  split.
  assumption.
  rewrite phplus_comm.
  rewrite phplus_assoc.
  rewrite bplus_comm.
  rewrite bplus_assoc.
  auto.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  rewrite phplus_comm.
  rewrite phplus_assoc.
  replace (phplus p4 p3) with (phplus p3 p4).
  rewrite p3p4.
  rewrite phplus_comm.
  rewrite bplus_comm.
  rewrite bplus_assoc.
  replace (bagplus C4 C3) with (bagplus C3 C4).
  rewrite C3C4.
  rewrite bplus_comm.
  auto.
  apply bplus_comm.
  apply phpdef_comm.
  tauto.
  apply phplus_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_assoc.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  }

  {
  destruct SATQ as (v,(v0,(v1,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opO3O4,(SAT1,(SAT3,(p3p4,C3C4)))))))))))))))).
  assert (phpdefp342: phplusdef p3 p2 /\ phplusdef p4 p2).
  {
  apply phpdef_dist.
  rewrite p3p4.
  assumption.
  assumption.
  }
  exists v,v0,v1.
  exists p3, (phplus p2 p4).
  exists.
  apply phpdef_assoc.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  exists bp3.
  exists.
  apply phplus_boundph.
  apply phpdef_comm.
  tauto.
  assert (o2o4: exists o2o4, oplus o2 o4 o2o4).
  {
  apply oplus_exists.
  destruct o2.
  inversion opo1o2.
  rewrite <- H in *.
  inversion opO3O4.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o2o4 as (o2o4, opo2o4).
  exists o3, o2o4.
  exists C3, (bagplus C2 C4).
  exists.
  apply oplus_assoc with o1 o2 o4.
  assumption.
  assumption.
  assumption.
  split.
  assumption.
  split.
  destruct SAT3 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(o5,(o6,(C5,(C6,(opO5O6,(SAT5,(SAT6,(p5p6,C5C6))))))))))))).
  assert (phpdefp562: phplusdef p5 p2 /\ phplusdef p6 p2).
  {
  apply phpdef_dist.
  rewrite p5p6.
  tauto.
  tauto.
  }
  exists p5, (phplus p2 p6).
  exists.
  apply phpdef_assoc.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  exists bp5.
  exists.
  apply phplus_boundph.
  apply phpdef_comm.
  tauto.
  assert (o2o6: exists o2o6, oplus o2 o6 o2o6).
  {
  apply oplus_exists.
  destruct o2.
  inversion opo2o4.
  rewrite <- H1 in *.
  inversion opO5O6.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o2o6 as (o2o6, opo2o6).
  exists o5, o2o6, C2, (bagplus C2 C6).
  exists.
  apply oplus_assoc with o4 o2 o6.
  apply oplus_comm.
  assumption.
  assumption.
  assumption.
  split.
  assumption.
  split.
  destruct SAT6 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(o7,(o8,(C7,(C8,(opO7O8,(SAT7,(SAT8,(p7p8,C7C8))))))))))))).
  assert (phpdefp782: phplusdef p7 p2 /\ phplusdef p8 p2).
  {
  apply phpdef_dist.
  rewrite p7p8.
  tauto.
  tauto.
  }
  exists p7, (phplus p2 p8).
  exists.
  apply phpdef_assoc.
  apply phpdef_comm.
  tauto.
  tauto.
  tauto.
  exists bp7.
  exists.
  apply phplus_boundph.
  apply phpdef_comm.
  tauto.
  assert (o2o8: exists o2o8, oplus o2 o8 o2o8).
  {
  apply oplus_exists.
  destruct o2.
  inversion opo2o6.
  rewrite <- H1 in *.
  inversion opO7O8.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o2o8 as (o2o8, opo2o8).
  exists o7, o2o8, C7, (bagplus C2 C8).
  exists.
  apply oplus_assoc with o6 o2 o8.
  apply oplus_comm.
  assumption.
  assumption.
  assumption.
  split.
  assumption.
  split.
  intros.
  assert (phpdefp28': phplusdef p2 p' /\ phplusdef p8 p').
  {
  apply phpdef_dist.
  assumption.
  apply phpdef_comm.
  tauto.
  }
  exists (phplus p8 p'),p2.
  exists.
  apply phpdef_assoc'.
  tauto.
  tauto.
  apply phpdef_comm.
  tauto.
  exists.
  apply phplus_boundph.
  tauto.
  exists bp2.
  assert (tmp: exists o8o', oplus o8 O' o8o').
  {
  apply oplus_exists.
  destruct o8.
  inversion opo2o8.
  rewrite <- H0 in OPLUS.
  inversion OPLUS.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct tmp as (o8o', opo8o').
  exists o8o', o2, (bagplus C8 C'), C2.
  exists.
admit.
  split.
  apply SAT8 with O'.
  assumption.
admit.
  assumption.
  assumption.
  split.
  assumption.
admit.
admit.
admit.
admit.
  }
  {
  destruct SATQ as (v,(v0,(v1,(NEGB,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opO3O4,(SAT1,(SAT3,(p3p4,C3C4))))))))))))))))).
  exists v,v0,v1.
  exists.
  assumption.
  exists p3, (phplus p2 p4).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  assert (o2o4: exists o2o4, oplus o2 o4 o2o4).
  {
  apply oplus_exists.
  destruct o2.
  inversion opo1o2.
  rewrite <- H in *.
  inversion opO3O4.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o2o4 as (o2o4, opo2o4).
  exists o3, o2o4.
  exists C3, (bagplus C2 C4).
  exists.
  apply oplus_assoc with o1 o2 o4.
  assumption.
  assumption.
  assumption.
  split.
  assumption.
  split.
  destruct SAT3 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(o5,(o6,(C5,(C6,(opO5O6,(SAT5,(SAT6,(p5p6,C5C6))))))))))))).
  exists p5, (phplus p2 p6).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  assert (o2o6: exists o2o6, oplus o2 o6 o2o6).
  {
admit.
  }
  destruct o2o6 as (o2o6, opo2o6).
  exists o5, o2o6, C2, (bagplus C2 C6).
  exists.
admit.
  split.
  assumption.
  split.
  intros.
  exists (phplus p6 p'),p2.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  assert (tmp: exists o6o', oplus o6 O' o6o').
  {
admit.
  }
  destruct tmp as (o6o', opo6o').
  exists o6o', o2, (bagplus C6 C'), C2.
  exists.
admit.
  split.
  apply SAT6 with O'.
  assumption.
admit.
  assumption.
  assumption.
  split.
  assumption.
admit.
admit.
admit.
  }

  {
  destruct SATQ as (v0,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opO3O4,(SAT1,(SAT3,(p3p4,C3C4)))))))))))))).
  exists v0.
  exists p3, (phplus p2 p4).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  assert (o2o4: exists o2o4, oplus o2 o4 o2o4).
  {
  apply oplus_exists.
  destruct o2.
  inversion opo1o2.
  rewrite <- H in *.
  inversion opO3O4.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o2o4 as (o2o4, opo2o4).
  exists o3, o2o4.
  exists C3, (bagplus C2 C4).
  exists.
  apply oplus_assoc with o1 o2 o4.
  assumption.
  assumption.
  assumption.
  split.
  assumption.
  split.
  intros.
  exists (phplus p4 p'),p2.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  assert (tmp: exists o4o', oplus o4 O' o4o').
  {
admit.
  }
  destruct tmp as (o4o', opo4o').
  exists o4o', o2, (bagplus C4 C'), C2.
  exists.
admit.
  split.
  apply SAT3 with v1 v2 v3 O'.
  assumption.
admit.
  assumption.
  assumption.
  split.
  assumption.
admit.
admit.
  }

  {
  destruct SATQ as (v,(v0,(v1,(v2,(v3,(NEGB,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opO3O4,(SAT1,(SAT3,(p3p4,C3C4))))))))))))))))))).
  exists v,v0,v1,v2,v3.
  exists.
  assumption.
  exists p3, (phplus p2 p4).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  assert (o2o4: exists o2o4, oplus o2 o4 o2o4).
  {
  apply oplus_exists.
  destruct o2.
  inversion opo1o2.
  rewrite <- H in *.
  inversion opO3O4.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o2o4 as (o2o4, opo2o4).
  exists o3, o2o4.
  exists C3, (bagplus C2 C4).
  exists.
  apply oplus_assoc with o1 o2 o4.
  assumption.
  assumption.
  assumption.
  split.
  assumption.
  split.
  destruct SAT3 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(o5,(o6,(C5,(C6,(opO5O6,(SAT5,(SAT6,(p5p6,C5C6))))))))))))).
  exists p5, (phplus p2 p6).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  assert (o2o6: exists o2o6, oplus o2 o6 o2o6).
  {
admit.
  }
  destruct o2o6 as (o2o6, opo2o6).
  exists o5, o2o6, C5, (bagplus C2 C6).
  exists.
admit.
  split.
  assumption.
  split.
  intros.

  destruct SAT6 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(o7,(o8,(C7,(C8,(opO7O8,(SAT7,(SAT8,(p7p8,C7C8))))))))))))).
  exists p7, (phplus p2 p8).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  assert (o2o8: exists o2o8, oplus o2 o8 o2o8).
  {
admit.
  }
  destruct o2o8 as (o2o8, opo2o8).
  exists o7, o2o8, C7, (bagplus C2 C8).
  exists.
admit.
  split.
  assumption.
  split.
  intros.
  exists (phplus p8 p'),p2.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  assert (tmp: exists o8o', oplus o8 O' o8o').
  {
admit.
  }
  destruct tmp as (o8o', opo8o').
  exists o8o', o2, (bagplus C8 C'), C2.
  exists.
admit.
  split.
  apply SAT8 with O'.
  assumption.
admit.
  assumption.
  assumption.
  split.
  assumption.
admit.
admit.
admit.
admit.
  }
  {
  destruct SATQ as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opO3O4,(SAT1,(SAT3,(p3p4,C3C4))))))))))))).
  exists p3, (phplus p2 p4).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  assert (o2o4: exists o2o4, oplus o2 o4 o2o4).
  {
  apply oplus_exists.
  destruct o2.
  inversion opo1o2.
  rewrite <- H in *.
  inversion opO3O4.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o2o4 as (o2o4, opo2o4).
  exists o3, o2o4.
  exists C3, (bagplus C2 C4).
  exists.
  apply oplus_assoc with o1 o2 o4.
  assumption.
  assumption.
  assumption.
  split.
  assumption.
  split.
  intros.
  exists (phplus p4 p'),p2.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  assert (tmp: exists o4o', oplus o4 O' o4o').
  {
  apply oplus_exists.
  destruct o4.
  inversion opo2o4.
  rewrite <- H0 in OPLUS.
  inversion OPLUS.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct tmp as (o4o', opo4o').
  exists o4o', o2, (bagplus C4 C'), C2.
  exists.
admit.
  split.
  apply SAT3 with O'.
  assumption.
admit.
  assumption.
  assumption.
  split.
  assumption.
admit.
admit.
  }
  {
  destruct SATQ as (v,(v0,(v1,(v2,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(o3,(o4,(C3,(C4,(opO3O4,(SAT1,(SAT3,(p3p4,C3C4))))))))))))))))).
  exists v,v0,v1,v2.
  exists p3, (phplus p2 p4).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  assert (o2o4: exists o2o4, oplus o2 o4 o2o4).
  {
  apply oplus_exists.
  destruct o2.
  inversion opo1o2.
  rewrite <- H in *.
  inversion opO3O4.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct o2o4 as (o2o4, opo2o4).
  exists o3, o2o4.
  exists C3, (bagplus C2 C4).
  exists.
  apply oplus_assoc with o1 o2 o4.
  assumption.
  assumption.
  assumption.
  split.
  assumption.
  split.
  destruct SAT3 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(o5,(o6,(C5,(C6,(opO5O6,(SAT5,(SAT6,(p5p6,C5C6))))))))))))).
  exists p5, (phplus p2 p6).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  assert (o2o6: exists o2o6, oplus o2 o6 o2o6).
  {
admit.
  }
  destruct o2o6 as (o2o6, opo2o6).
  exists o5, o2o6, C5, (bagplus C2 C6).
  exists.
admit.
  split.
  assumption.
  split.
  destruct SAT6 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(o7,(o8,(C7,(C8,(opO7O8,(SAT7,(SAT8,(p7p8,C7C8))))))))))))).
  exists p7, (phplus p2 p8).
  exists.
admit.
  exists.
admit.
  exists.
admit.
  assert (o2o8: exists o2o8, oplus o2 o8 o2o8).
  {
admit.
  }
  destruct o2o8 as (o2o8, opo2o8).
  exists o7, o2o8, C7, (bagplus C2 C8).
  exists.
admit.
  split.
  assumption.
  split.
  intros.
  exists (phplus p8 p'),p2.
  exists.
admit.
  exists.
admit.
  exists.
admit.
  assert (tmp: exists o8o', oplus o8 O' o8o').
  {
admit.
  }
  destruct tmp as (o8o', opo8o').
  exists o8o', o2, (bagplus C8 C'), C2.
  exists.
admit.
  split.
  apply SAT8 with O'.
  assumption.
admit.
  assumption.
  assumption.
  split.
  assumption.
admit.
admit.
admit.
admit.
  }
*)


