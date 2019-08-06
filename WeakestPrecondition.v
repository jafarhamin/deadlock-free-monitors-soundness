Add LoadPath "proofs".

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

Local Open Scope Z.


(** # <font size="5"><b> Weakest Precondition </b></font> # *)

Fixpoint weakest_pre (n': nat) (sp: bool) (c:cmd) (Q: Z -> assn) (se: exp -> exp) (invs: Z -> inv) {struct n'} : assn :=
  match n' with
    | O => Abool true
    | S n =>
  match c with
    | Val e => Q ([[se e]])
    | Cons n => FA l, (fold_left Astar (points_tos (seq O n) ((Enum l, 0%Qc, Enum l, None, false), (0,nil), (0,nil), nil)) (Abool true) --* (Q l))
    | Lookup e => EX l, (EX z, (EX f, (Abool (Z.eqb ([[se e]]) ([[Aof l]])) &* Apointsto f l (Enum z) ** (Apointsto f l (Enum z) --* Q z))))
    | Mutate e1 e2 => EX l, (EX z, (Abool (Z.eqb ([[se e1]]) ([[Aof l]])) &* l |-> z) ** (l |-> (se e2) --* Q 0))
    | Let x c1 c2 => weakest_pre n sp c1 (fun z => weakest_pre n sp c2 Q (fun e => subse x z (se e)) invs) se invs
    | Fork c => EX O, (EX O', ((Aobs(O ++ O') ** (Aobs(O) --* Q 0)) ** (Aobs(O') --* weakest_pre n sp c (fun _ => Aobs(nil)) se invs)))
    | Newlock => FA l, (EX r, 
        (Aulock ((Enum l,r,Enum l, None, false), (0,nil), (0,nil), nil) empb empb --* Q l))
    | Acquire e => EX O, (EX l, (((Abool (Z.eqb ([[se e]]) ([[Aof l]])) &* Aprop (prcl (evalol (Oof l)) (map evalol O))) &* Alock l ** Aobs O) **
        (FA wt, (FA ot, ((Aobs ((Oof l)::O) ** Alocked l wt ot ** 
        (subsas (snd (Iof l)) (invs (fst (Iof l)) wt ot)))) --* Q 0))))
    | Release e => EX O, (EX l, (EX wt, (EX ot,
        ((Abool (Z.eqb ([[se e]]) ([[Aof l]])) &* Aobs ((Oof l)::O) ** Alocked l wt ot ** 
        (subsas (snd (Iof l)) (invs (fst (Iof l)) wt ot)))) ** ((Aobs O ** Alock l --* Q 0)))))
    | Newcond => FA v, (EX R, (EX P, (EX X,
        (Aucond ((Enum v,R,Enum v,X,P),(0,nil),(0,nil),nil) --* Q v))))
    | Waiting4lock e => EX O, (EX l, (((Abool (Z.eqb ([[se e]]) ([[Aof l]])) &* Aprop (prcl (evalol (Oof l)) (map evalol O))) &* Alock l ** Aobs O) **
        (FA wt, (FA ot, ((Aobs ((Oof l)::O) ** Alocked l wt ot ** 
        (subsas (snd (Iof l)) (invs (fst (Iof l)) wt ot)))) --* Q 0))))
    | Wait ev el => EX O, (EX l, (EX v, (EX wt, (EX ot,
        ((Abool (andb (Z.eqb ([[se ev]]) ([[Aof v]]))
        (andb (Z.eqb ([[se el]]) ([[Aof l]]))
        (andb (Z.eqb ([[Lof v]]) ([[Aof l]]))
        (safe_obs (evall v) (S (wt ([[Aof v]]))) (ot ([[Aof v]])))))) &*
        (Aprop (prcl (evalol (Oof v)) (map evalol O)) &*
        Aprop (prcl (evalol (Oof l)) (map evalol (M'of v ++ O))))) &*
        ((subsas (snd (Iof l)) (invs (fst (Iof l)) (upd Z.eq_dec wt ([[Aof v]]) (S (wt ([[Aof v]])))) ot)) ** Aobs (Oof l::O) ** Acond v ** Alocked l wt ot)))) **
        (FA wt', (FA ot', ((Aobs (Oof l:: M'of v ++ O) ** Acond v ** Alocked l wt' ot' ** (subsas (snd (Iof l)) (invs (fst (Iof l)) wt' ot')) ** 
        (subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb))) --* Q 0)))))
    | Waiting4cond ev el => EX O, (EX l, (EX v, 
        (Abool (andb (Z.eqb ([[se ev]]) ([[Aof v]]))
        (andb (Z.eqb ([[se el]]) ([[Aof l]]))
        (Z.eqb ([[Lof v]]) ([[Aof l]])))) &*
        (Aprop (prcl (evalol (Oof v)) (map evalol O)) &*
        Aprop (prcl (evalol (Oof l)) (map evalol (M'of v ++ O))))) &* 
        (Acond v ** Alock l ** Aobs O) **
        (FA wt, (FA ot, ((Aobs (Oof l:: M'of v ++ O) ** Acond v ** Alocked l wt ot ** (subsas (snd (Iof l)) (invs (fst (Iof l)) wt ot)) **
        (subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb)) --* Q 0))))))
    | WasWaiting4cond ev el => EX O, (EX l, (EX v, 
        (Abool (andb sp
        (andb (Z.eqb ([[se ev]]) ([[Aof v]]))
        (andb (Z.eqb ([[se el]]) ([[Aof l]]))
        (Z.eqb ([[Lof v]]) ([[Aof l]]))))) &*
        (Aprop (prcl (evalol (Oof v)) (map evalol O)) &*
        Aprop (prcl (evalol (Oof l)) (map evalol (M'of v ++ O))))) &* 
        (Acond v ** Alock l ** Aobs O) **
        (FA wt, (FA ot, ((Aobs (Oof l:: M'of v ++ O) ** Acond v ** Alocked l wt ot ** (subsas (snd (Iof l)) (invs (fst (Iof l)) wt ot)) **
        (subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb)) --* Q 0))))))
    | Notify ev => EX O, (EX wt, (EX ot, (EX l, (EX v, (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (Z.eqb ([[se ev]]) ([[Aof v]]))) &*
       ((subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb)) |* Abool (leb (wt ([[Aof v]])) 0)) ** Acond v ** Alocked l wt ot ** 
       Aobs ((if ltb 0 (wt ([[Aof v]])) then (M'of v) else nil) ++ O) **
       ((Acond v ** Alocked l (upd Z.eq_dec wt ([[Aof v]]) (wt ([[Aof v]]) - 1)%nat) ot ** Aobs (O)) --* Q 0))))))
    | NotifyAll ev => EX wt, (EX ot, (EX l, (EX v, ((Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (andb (Z.eqb ([[se ev]]) ([[Aof v]])) 
      (ifb ((list_eq_dec (olocation_eq_dec exp_eq_dec) (M'of v) nil)))))
       &* Aprop (subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb) = Abool true)) ** Acond v ** Alocked l wt ot ** 
       ((Acond v ** Alocked l (upd Z.eq_dec wt ([[Aof v]]) 0%nat) ot) --* Q 0)))))
    | If c c1 c2 => weakest_pre n sp c (fun z => if Z.ltb 0%Z z then (weakest_pre n sp c1 Q se invs) else (weakest_pre n sp c2 Q se invs)) se invs
    | While c1 c2 => weakest_pre n sp c1 (fun z => if Z.ltb 0%Z z then
       (weakest_pre n sp c2 (fun _ => weakest_pre n sp (While c1 c2) Q se invs) se invs) else Q 0) se invs
    | nop => 
        (* nop *)
        (FA z, Q z) |*
        (* g_initl *)
        (EX l, (EX O, (EX wt, (EX ot, (EX i, (EX params, (EX e, ((Abool (Z.eqb ([[e]]) ([[Aof l]]))
        &* Aulock l wt ot ** subsas params (invs i wt ot) ** Aobs O ** 
        ((Alock ((Aof l, Rof l, Lof l, Xof l, Pof l), (i,params), Mof l, M'of l) ** Aobs O) --* Q 0)))))))))) |*
        (* g_initc *)
        (EX v, (EX l, (EX M, (EX M', (EX wt, (EX ot, (EX e, (Abool (Z.eqb ([[e]]) ([[Aof v]])) &*
        Aulock l wt ot ** Aucond v ** (Aulock l wt ot ** Aicond ((Aof v, Rof v, Aof l, Xof v, Pof v), Iof v, M, M') --* Q 0))))))))) |*
        (* g_finlc *)
        (EX v, (EX l, (EX e, ((Abool (andb (Z.eqb ([[e]]) ([[Aof v]])) (Z.eqb ([[Lof v]]) ([[Aof l]]))) &*
        Aprop (spurious_ok sp (evall l) (evall v) invs)) &* Alock l ** Aicond v ** (Alock l ** Acond v --* Q 0))))) |*
        (* g_newctr *)
        (FA gc, Actr (Enum gc) 0 --* Q 0) |*
        (* g_ctrdec *)
        (EX n, (EX ev, (Actr ev n ** Atic ev ** (Actr ev (n-1)%nat --* Q 0)))) |*
        (* g_ctrinc *)
        (EX n, (EX gv, (Actr gv n ** (Actr gv (S n)%nat ** Atic gv --* Q 0)))) |*
        (* g_disch *)
        (EX O, (EX wt, (EX ot, (EX l, (EX v, (EX ev, (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (andb (Z.eqb ([[ev]]) ([[Aof v]]))
        (safe_obs (evall v) (wt ([[ev]])) ((ot ([[ev]]) - 1))))) &* Acond v ** Aobs (Oof v::O) ** Alocked l wt ot 
        ** ((Acond v ** Aobs O ** Alocked l wt (upd Z.eq_dec ot ([[ev]]) (ot ([[ev]]) - 1)%nat)) --* Q 0)))))))) |*
        (* g_dischu *)
        (EX O, (EX wt, (EX ot, (EX l, (EX v, (EX ev, (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (andb (Z.eqb ([[ev]]) ([[Aof v]]))
        (safe_obs (evall v) (wt ([[ev]])) ((ot ([[ev]]) - 1))))) &* Aicond v ** Aobs (Oof v::O) ** Aulock l wt ot **
        ((Aicond v ** Aobs O ** Aulock l wt (upd Z.eq_dec ot ([[ev]]) (ot ([[ev]]) - 1)%nat)) --* Q 0)))))))) |*
        (* g_chrg *)
        (EX O, (EX wt, (EX ot, (EX l, (EX v, (EX ev, (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (Z.eqb ([[ev]]) ([[Aof v]]))) &* Acond v **
        Aobs O ** Alocked l wt ot ** ((Acond v ** Aobs (Oof v::O) ** Alocked l wt (upd Z.eq_dec ot ([[ev]]) (ot ([[ev]]) + 1)%nat)) --* Q 0)))))))) |*
        (* g_chrgu *)
        (EX O, (EX wt, (EX ot, (EX l, (EX v, (EX ev, (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (Z.eqb ([[ev]]) ([[Aof v]]))) &* Aicond v **
        Aobs O ** Aulock l wt ot ** ((Aicond v ** Aobs (Oof v::O) ** Aulock l wt (upd Z.eq_dec ot ([[ev]]) (ot ([[ev]]) + 1)%nat)) --* Q 0))))))))
  end
  end.


Fixpoint weakest_pre_tx (n: nat) (sp: bool) (tx:context) invs : (Z -> assn) :=
  match tx with
    | done => fun _ => Aobs nil
    | Let' x c tx => fun z => weakest_pre n sp (subs c (subse x z)) (weakest_pre_tx n sp tx invs) id invs
    | If' c1 c2 tx => fun z => if Z.ltb 0 z then 
        weakest_pre n sp c1 (weakest_pre_tx n sp tx invs) id invs else
        weakest_pre n sp c2 (weakest_pre_tx n sp tx invs) id invs
  end.

Definition weakest_pre_ct (n: nat) (sp: bool) (ct: (cmd * context)) invs : assn :=
  weakest_pre n sp (fst ct) (weakest_pre_tx n sp (snd ct) invs) id invs.


Lemma sat_weak_imp:
  forall n c p o d se a a' invs sp (BP: boundph p) (BG: boundgh d)
         (SAT: sat p o d (weakest_pre n sp c a se invs))
         (IMP: forall z, a z |= a' z),
    forall n' (LE: le n' n), sat p o d (weakest_pre n' sp c a' se invs).
Proof.
  induction n.
  intros.
  destruct n'.
  reflexivity.
  inversion LE.
  destruct c.
  simpl.
  intros.
  destruct n'; try reflexivity.
  apply IMP; try assumption.
  simpl.
  intros.
  destruct n'; try reflexivity.
  simpl.
  intros.
  apply IMP; try assumption.
  apply SAT with O'; try assumption.
  simpl.
  intros.
  destruct n'; try reflexivity.
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
  destruct n'; try reflexivity.
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
  destruct n'; try reflexivity.
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
  split.
  intros.
  eapply IHn; try assumption.
  apply tmp2 with O'; try assumption.
  intros.
  assumption.
  omega.
  assumption.
  }
  {
  destruct n'; try reflexivity.
  simpl.
  intros.
  simpl in SAT.
  eapply IHn; try assumption.
  apply SAT.
  intros.
  eapply IHn; try assumption.
  apply SAT0.
  intros.
  apply IMP; try assumption.
  omega.
  omega.
  }
  {
  simpl.
  intros.
  destruct n'; try reflexivity.
  simpl.
  eapply IHn; try assumption.
  apply SAT.
  intros.
  simpl in SAT0.
  destruct (0 <? z) eqn:z0.
  {
  eapply IHn; try assumption.
  apply SAT0.
  intros.
  apply IMP; try assumption.
  omega.
  }
  {
  eapply IHn; try assumption.
  apply SAT0.
  intros.
  apply IMP; try assumption.
  omega.
  }
  omega.
  }
  {
  intros.
  destruct n'; try reflexivity.
  simpl.
  simpl in SAT.
  eapply IHn; try assumption.
  apply SAT.
  intros.
  simpl in SAT0.
  destruct (0 <? z) eqn:z0.
  {
  eapply IHn; try assumption.
  apply SAT0.
  inversion z0.
  intros.
  eapply IHn; try assumption.
  apply SAT1.
  intros.
  apply IMP; assumption.
  omega.
  omega.
  }
  apply IMP; try assumption.
  omega.
  }
  {
  destruct n'; try reflexivity.
  simpl.
  intros.
  simpl in SAT.
  specialize SAT with v.
  destruct SAT as (v0,SAT).
  exists v0.
  intros.
  apply IMP.
  assumption.
  assumption.
  apply SAT with O';
  try tauto.
  }
  {
  destruct n'; try reflexivity.
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
  destruct n'; try reflexivity.
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
  destruct n'; try reflexivity.
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
  destruct n'; try reflexivity.
  simpl.
  intros.
  simpl in SAT.
  specialize SAT with v.
  destruct SAT as (v0,(v1,(v2,tmp1))).
  exists v0,v1,v2.
  intros.
  apply IMP; repeat php_.
  apply tmp1 with O'; repeat php_.
  }
  {
  destruct n'; try reflexivity.
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(BC1,(BC2,(ghpdefC1C2,(bc12,(opO1O2,(tmp1,tmp2))))))))))))))))))).
  destruct tmp2 as (tmp2,tmp3).
  exists v,v0,v1, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, BC1, BC2, ghpdefC1C2, bc12, opO1O2.
  split.
  assumption.
  split.
  intros.
  apply IMP; repeat php_.
  eapply tmp2 with v2 v3 O'; repeat php_.
  tauto.
  }
  {
  destruct n'; try reflexivity.
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
  destruct n'; try reflexivity.
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
  destruct n'; try reflexivity.
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
  destruct n'; try reflexivity.
  simpl.
  intros.
  destruct SAT as (v0,(v1,(v2,((EQ1,EQ2),(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,tmp3))))))))))))))))))))).
  exists v0, v1, v2.
  exists.
  split; assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split.
  assumption.
  split.
  intros.
  apply IMP; repeat php_.
  apply tmp2 with v3 v4 O'; repeat php_.
  tauto.
  }
  {
  destruct n'; try reflexivity.
  destruct SAT as [SAT|g_chrgu].
  destruct SAT as [SAT|g_chrg].
  destruct SAT as [SAT|g_dischu].
  destruct SAT as [SAT|g_disch].
  destruct SAT as [SAT|g_ctrinc].
  destruct SAT as [SAT|g_ctrdec].
  destruct SAT as [SAT|g_newctr].
  destruct SAT as [SAT|g_finlc].
  destruct SAT as [SAT|g_initc].
  destruct SAT as [nop|g_initl].
  {
  intros.
  left. left. left. left. left. left. left. left. left. left.
  simpl.
  intros.
  apply IMP; try assumption.
  apply nop.
  }
  {
  intros.
  left. left. left. left. left. left. left. left. left. right.
  simpl.
  intros.
  destruct g_initl as (v,(v0,(v1,(v2,(v3,(v4,(v5,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,tmp3))))))))))))))))))))))))).
  exists v, v0, v1, v2, v3, v4, v5.
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
  intros.
  left. left. left. left. left. left. left. left. right.
  simpl.
  intros.
  destruct g_initc as (v,(v0,(v1,(v2,(v3,(v4,(v5,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(tmp3,tmp4)))))))))))))))))))))))))).
  exists v, v0, v1, v2, v3, v4, v5.
  split.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split.
  assumption.
  split.
  intros.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp6,(tmp5, p3p4))))))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  split.
  assumption.
  split.
  intros.
  apply IMP;
  try tauto.
  apply tmp5 with O'; try tauto.
  tauto.
  tauto.
  }
  {
  intros.
  left. left. left. left. left. left. left. right.
  simpl.
  intros.
  destruct g_finlc as (v,(v0,(v1,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,tmp2)))))))))))))))))))).
  exists v, v0, v1.
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
  intros.
  apply IMP.
  assumption.
  assumption.
  apply tmp5 with O'; repeat php_.
  tauto.
  tauto.
  }
  {
  intros.
  left. left. left. left. left. left. right.
  simpl.
  intros.
  simpl in g_newctr.
  apply IMP; try assumption.
  apply g_newctr with v O'; try assumption.
  }
  {
  intros.
  left. left. left. left. left. right.
  simpl.
  intros.
  destruct g_ctrdec as (v,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,tmp3))))))))))))))))))).
  exists v, v1, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
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
  {
  intros.
  left. left. left. left. right.
  simpl.
  intros.
  destruct g_ctrinc as (v,(gv,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,tmp3))))))))))))))))))).
  exists v, gv, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split.
  assumption.
  split.
  intros.
  apply IMP; try assumption.
  apply tmp2 with O'; try assumption.
  auto.
  }
  {
  intros.
  left. left. left. right.
  simpl.
  intros.
  destruct g_disch as (v,(v0,(v1,(v2,(v3,(v4,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,tmp2))))))))))))))))))))))).
  exists v, v0, v1, v2, v3, v4.
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
  intros.
  left. left. right.
  simpl.
  intros.
  destruct g_dischu as (v,(v0,(v1,(v2,(v3,(v4,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,tmp2))))))))))))))))))))))).
  exists v, v0, v1, v2, v3, v4.
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
  intros.
  left. right.
  destruct g_chrg as (v,(v0,(v1,(v2,(v3,(v4,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,tmp2))))))))))))))))))))))).
  exists v, v0, v1, v2, v3, v4.
  simpl.
  split. assumption.
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
  intros.
  right.
  simpl.
  intros.
  destruct g_chrgu as (v,(v0,(v1,(v2,(v3,(v4,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,tmp2))))))))))))))))))))))).
  exists v, v0, v1, v2, v3, v4.
  simpl.
  split. assumption.
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
  }
Qed.


Lemma sat_tx_weak_imp:
  forall n tx p o d z invs sp (BP: boundph p) (BG: boundgh d)
         (SAT: sat p o d (weakest_pre_tx n sp tx invs z)),
    forall n' (LE: le n' n), sat p o d (weakest_pre_tx n' sp tx invs z).
Proof.
  induction tx.
  simpl.
  intros.
  assumption.
  {
  intros.
  unfold weakest_pre_tx in *.
  destruct ((0 <? z)%Z) eqn:zz.
  eapply sat_weak_imp; try assumption.
  apply SAT.
  simpl.
  intros.
  apply IHtx; try assumption.
  omega.
  eapply sat_weak_imp; try assumption.
  apply SAT.
  intros.
  apply IHtx; try assumption.
  omega.
  }
  {
  intros.
  unfold weakest_pre_tx in *.
  eapply sat_weak_imp; try assumption.
  apply SAT.
  simpl.
  intros.
  apply IHtx; try assumption.
  omega.
  }
Qed.


Lemma sat_ct_weak_imp:
  forall n ct p o d invs sp (BP: boundph p) (BG: boundgh d)
         (SAT: sat p o d (weakest_pre_ct n sp ct invs)),
    forall n' (LE: le n' n), sat p o d (weakest_pre_ct n' sp ct invs).
Proof.
  intros.
  eapply sat_weak_imp; try assumption.
  apply SAT.
  intros.
  eapply sat_tx_weak_imp; try assumption.
  apply SAT0; assumption.
  assumption.
  omega.
Qed.


Lemma sat_weak_imp1:
  forall n c p o d se a a' invs sp (BP: boundph p) (BG: boundgh d)
         (SAT: sat p o d (weakest_pre (S n) sp c a se invs))
         (IMP: forall z, a z |= a' z),
    sat p o d (weakest_pre n sp c a' se invs).
Proof.
  intros.
  eapply sat_weak_imp with (S n) a; try assumption.
  omega.
Qed.


Lemma sat_tx_weak_imp1:
  forall n tx p o d z invs sp (BP: boundph p) (BG: boundgh d)
         (SAT: sat p o d (weakest_pre_tx (S n) sp tx invs z)),
    sat p o d (weakest_pre_tx n sp tx invs z).
Proof.
  intros.
  apply sat_tx_weak_imp with (S n); try assumption.
  omega.
Qed.


(** # <font size="5"><b> Substitution </b></font> # *)

Lemma wp_subst_free:
  forall n c se sp a x z invs
    (NOTFREE: is_free (subs c se) x = false),
    (weakest_pre n sp c a se invs |=
    weakest_pre n sp c a (fun e => subse x z (se e)) invs) /\
    (weakest_pre n sp c a (fun e => subse x z (se e)) invs |=
    weakest_pre n sp c a se invs).
Proof.
  induction n.
  split; reflexivity.
  destruct c.
  {
  split. simpl. intros. rewrite subse_free; try assumption.
  simpl. intros. rewrite subse_free in SAT; try assumption.
  }
  {
  simpl. split; intros. apply SAT with O'; try assumption.
  apply SAT with O'; try assumption.
  }
  {
  split; simpl; intros. rewrite subse_free.
  destruct SAT as (v,(v0,(v1,(eq,rest)))).
  exists v, v0, v1. split. assumption. assumption. assumption.
  rewrite subse_free in SAT; assumption.
  }
  {
  simpl. split. intros.
  apply Coq.Bool.Bool.orb_false_iff in NOTFREE.
  destruct NOTFREE.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,tmp3))))))))))))))))))).
  exists v, v0, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2, C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split. rewrite subse_free; try assumption.
  split; intros. apply tmp2 with O'; try assumption.
  rewrite subse_free in SAT; try assumption. assumption.
  apply Coq.Bool.Bool.orb_false_iff in NOTFREE.
  destruct NOTFREE.
  simpl. intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,tmp3))))))))))))))))))).
  exists v, v0, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2, C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split. rewrite subse_free in tmp1; try assumption.
  split. intros. apply tmp2 with O'; try assumption.
  rewrite subse_free; try assumption. assumption.
  }
  {
  split; simpl.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,tmp3))))))))))))))))))).
  exists v, v0, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2, C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  destruct tmp1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,tmp1))))))))))))))).
  split.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  assumption.
  split.
  intros.
  destruct IHn with c se sp (fun _ : Z => Aobs nil) x z invs as (IHc1,IHc2); try assumption.
  apply IHc1; try assumption.
  apply tmp2 with O'; try assumption.
  assumption.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,tmp3))))))))))))))))))).
  exists v, v0, p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2, C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  destruct tmp1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,tmp1))))))))))))))).
  split.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  assumption.
  split.
  intros.
  destruct IHn with c se sp (fun _ : Z => Aobs nil) x z invs as (IHc1,IHc2); try assumption.
  apply IHc2; try assumption.
  apply tmp2 with O'; try assumption.
  assumption.
  }
  {
  simpl. split; intros.
  apply Coq.Bool.Bool.orb_false_iff in NOTFREE.
  destruct NOTFREE.

  destruct IHn with c1 se sp (fun z0 : Z =>
    weakest_pre n sp c2 a (fun e : exp => subse x z0 (subse x0 z (se e))) invs)
    x0 z invs as (IHc11,IHc12); try assumption.
  apply IHc11; try assumption.
  eapply sat_weak_imp; repeat php_.
  apply SAT.
  simpl. intros.
  destruct (Z.eq_dec x x0).
  rewrite e in *.
  replace (fun e0 => subse x0 z0 (subse x0 z (se e0))) with
    (fun e0 => subse x0 z (se e0)).
  destruct IHn with c2 se sp a x0 z invs as (IHc21,IHc22); try assumption.
  apply IHc21; try assumption.
  destruct IHn with c2 se sp a x0 z0 invs as (IHc21',IHc22'); try assumption.
  apply IHc22'; try assumption.
  apply functional_extensionality.
  intros.
  apply subse_subse; try assumption.
  replace (fun e : exp => subse x z0 (subse x0 z (se e))) with
    (fun e : exp => subse x0 z (subse x z0 (se e))).
  destruct IHn with c2 (fun e => subse x z0 (se e)) sp a x0 z invs as (IHc21,IHc22); try assumption.
  simpl.
  apply is_free_subs; assumption.
  apply IHc21; try assumption.
  apply functional_extensionality.
  intros.
  apply subse_subse_neq; try assumption.
  apply Coq.Bool.Bool.orb_false_iff in NOTFREE.
  destruct NOTFREE.
  destruct IHn with c1 se sp (fun z0 : Z => weakest_pre n sp c2 a
   (fun e : exp => subse x z0 (subse x0 z (se e))) invs)
    x0 z invs as (IHc11,IHc12); try assumption.
  apply IHc12 in SAT; try assumption.
  eapply sat_weak_imp; try assumption.
  apply SAT.
  simpl. intros.
  destruct (Z.eq_dec x x0).
  rewrite e in *.
  replace (fun e0 => subse x0 z0 (subse x0 z (se e0))) with
    (fun e0 => subse x0 z (se e0)) in SAT0.
  destruct IHn with c2 se sp a x0 z0 invs as (IHc21,IHc22); try assumption.
  apply IHc21; try assumption.
  destruct IHn with c2 se sp a x0 z invs as (IHc21',IHc22'); try assumption.
  apply IHc22' in SAT0; try assumption.
  apply functional_extensionality.
  intros.
  apply subse_subse; try assumption.
  replace (fun e : exp => subse x z0 (subse x0 z (se e))) with
    (fun e : exp => subse x0 z (subse x z0 (se e))) in SAT0.
  destruct IHn with c2 (fun e => subse x z0 (se e)) sp a x0 z invs as (IHc21,IHc22); try assumption.
  apply is_free_subs; assumption.
  apply IHc22 in SAT0; try assumption.
  apply functional_extensionality.
  intros.
  apply subse_subse_neq; try assumption.
  omega.
  }
  {
  simpl. split; intros.
  apply Coq.Bool.Bool.orb_false_iff in NOTFREE.
  destruct NOTFREE as (NF1,NF2).
  apply Coq.Bool.Bool.orb_false_iff in NF1.
  destruct NF1 as (NF0,NF1).
  eapply sat_weak_imp; repeat php_.
  apply IHn; try assumption.
  apply SAT.
  simpl. intros.
  destruct (0 <? z0).
  apply IHn; try assumption.
  apply IHn; try assumption.
  apply Coq.Bool.Bool.orb_false_iff in NOTFREE.
  destruct NOTFREE as (NF1,NF2).
  apply Coq.Bool.Bool.orb_false_iff in NF1.
  destruct NF1 as (NF0,NF1).
  eapply sat_weak_imp; repeat php_.
  apply IHn in SAT; try assumption.
  apply SAT.
  simpl. intros.
  destruct (0 <? z0).
  apply IHn in SAT0; try assumption.
  apply IHn in SAT0; try assumption.
  }
  {
  simpl. split; intros.
  apply Coq.Bool.Bool.orb_false_iff in NOTFREE.
  destruct NOTFREE as (NF1,NF2).
  eapply sat_weak_imp; repeat php_.
  apply IHn; try assumption.
  apply SAT.
  simpl. intros.
  destruct (0 <? z0).
  apply IHn; try assumption.
  eapply sat_weak_imp; repeat php_.
  apply SAT0; try assumption.
  simpl. intros.
  apply IHn; try assumption.
  apply Coq.Bool.Bool.orb_false_iff; split; assumption.
  assumption.
  apply Coq.Bool.Bool.orb_false_iff in NOTFREE.
  destruct NOTFREE as (NF1,NF2).
  eapply sat_weak_imp; repeat php_.
  destruct IHn with c1 se sp (fun z0 : Z => if 0 <? z0
    then weakest_pre n sp c2 (fun _ : Z =>
    weakest_pre n sp (While c1 c2) a
    (fun e : exp => subse x z (se e)) invs)
    (fun e : exp => subse x z (se e)) invs
     else a 0) x z invs as (IHn1,IHn2); try assumption.
  apply IHn2; try assumption.
  simpl. intros.
  destruct (0 <? z0).
  destruct IHn with c2 se sp (fun _:Z => weakest_pre n sp (While c1 c2) a
    (fun e : exp => subse x z (se e)) invs) x z invs as (IHn1,IHn2); try assumption.
  apply IHn2 in SAT0; try assumption.
  eapply sat_weak_imp; repeat php_.
  apply SAT0.
  simpl. intros.
  destruct IHn with (While c1 c2) se sp a x z invs as (IHn1',IHn2'); try assumption.
  apply Coq.Bool.Bool.orb_false_iff; split; assumption.
  apply IHn2' in SAT1; try assumption. assumption.
  }
  {
  split; simpl; intros. specialize SAT with v. assumption.
  specialize SAT with v. assumption.
  }
  {
  simpl. split; intros. rewrite subse_free; assumption.
  rewrite subse_free in SAT; assumption.
  }
  {
  simpl. split; intros. rewrite subse_free; assumption.
  rewrite subse_free in SAT; assumption.
  }
  {
  simpl. split; intros. rewrite subse_free; assumption.
  rewrite subse_free in SAT; assumption.
  }
  {
  simpl. split; intros. specialize SAT with v. assumption.
  specialize SAT with v. assumption.
  }
  {
  simpl. split; intros.
  apply Coq.Bool.Bool.orb_false_iff in NOTFREE. destruct NOTFREE as (NF1,NF2).
  rewrite subse_free; try assumption. rewrite subse_free; try assumption.
  apply Coq.Bool.Bool.orb_false_iff in NOTFREE. destruct NOTFREE as (NF1,NF2).
  rewrite subse_free in SAT; try assumption. rewrite subse_free in SAT; try assumption.
  }
  {
  simpl. split; intros. rewrite subse_free; assumption.
  rewrite subse_free in SAT; assumption.
  }
  {
  simpl. split; intros. rewrite subse_free; assumption.
  rewrite subse_free in SAT; assumption.
  }
  {
  simpl. split; intros.
  apply Coq.Bool.Bool.orb_false_iff in NOTFREE. destruct NOTFREE as (NF1,NF2).
  rewrite subse_free; try assumption. rewrite subse_free; try assumption.
  apply Coq.Bool.Bool.orb_false_iff in NOTFREE. destruct NOTFREE as (NF1,NF2).
  rewrite subse_free in SAT; try assumption. rewrite subse_free in SAT; try assumption.
  }
  {
  simpl. split; intros.
  apply Coq.Bool.Bool.orb_false_iff in NOTFREE. destruct NOTFREE as (NF1,NF2).
  rewrite subse_free; try assumption. rewrite subse_free; try assumption.
  apply Coq.Bool.Bool.orb_false_iff in NOTFREE. destruct NOTFREE as (NF1,NF2).
  rewrite subse_free in SAT; try assumption. rewrite subse_free in SAT; try assumption.
  }
  simpl. split; intros. assumption. assumption.
Qed.


Lemma sat_pre_subs1:
  forall n c se a p o d x z invs sp (BP: boundph p) (BG: boundgh d)
        (SAT: sat p o d (weakest_pre n sp (subs c (subse x z)) a se invs)),
    forall n' (LE: le n' n), sat p o d (weakest_pre n' sp c a (fun e : exp => se (subse x z e)) invs).
Proof.
  induction n.
  simpl.
  intros.
  destruct n'.
  reflexivity.
  inversion LE.
  destruct c; intros;
  try destruct n';
  try reflexivity;
  try assumption.
  {
  simpl.
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
  apply IHn; try assumption.
  apply tmp2 with (O':=O'); try assumption.
  omega. assumption.
  }
  {
  simpl.
  simpl in SAT.
  eapply sat_weak_imp; try assumption.
  apply IHn with (n':=n); try assumption.
  apply SAT.
  omega.
  intros.
  simpl in SAT0.
  simpl.
  eapply IHn in SAT0; try assumption.
  apply SAT0.
  omega.
  omega.
  }
  {
  simpl.
  simpl in SAT.
  eapply sat_weak_imp; try assumption.
  apply IHn with (n':=n); try assumption.
  apply SAT.
  omega.
  intros.
  simpl in SAT0.
  destruct (0 <? z0).
  apply IHn; try assumption.
  omega.
  apply IHn; try assumption.
  omega.
  omega.
  }
  {
  simpl.
  simpl in SAT.
  eapply sat_weak_imp; try assumption.
  apply IHn with (n':=n); try assumption.
  apply SAT.
  omega.
  intros.
  simpl in SAT0.
  destruct (0 <? z0).
  simpl.
  apply IHn; try assumption.
  eapply sat_weak_imp; try assumption.
  apply SAT0.
  intros.
  simpl in SAT1.
  apply IHn; try assumption.
  omega.
  omega.
  omega.
  assumption.
  omega.
  }
Qed.


Lemma sat_pre_subs2:
  forall n c se a p o d x z invs sp (BP: boundph p) (BG: boundgh d)
        (SAT: sat p o d (weakest_pre n sp c a (fun e : exp => se (subse x z e)) invs)),
    forall n' (LE: le n' n), sat p o d (weakest_pre n' sp (subs c (subse x z)) a se invs).
Proof.
  induction n.
  simpl.
  intros.
  destruct n'.
  reflexivity.
  inversion LE.
  destruct c; intros;
  try destruct n';
  try reflexivity;
  try assumption.
  {
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
  simpl.
  intros.
  apply IHn; try assumption.
  apply tmp2 with (O':=O'); try assumption.
  omega.
  assumption.
  }
  {
  simpl.
  eapply sat_weak_imp; try assumption.
  apply IHn with (n':=n); try assumption.
  simpl in SAT.
  apply SAT.
  omega.
  simpl.
  intros.
  eapply IHn; try assumption.
  omega.
  omega.
  }
  {
  simpl.
  eapply sat_weak_imp; try assumption.
  eapply IHn with (n':=n); try assumption.
  apply SAT.
  omega.
  simpl.
  intros.
  destruct (0 <? z0).
  simpl.
  apply IHn; try assumption.
  omega.
  apply IHn; try assumption.
  omega.
  omega.
  }
  {
  simpl.
  eapply sat_weak_imp; try assumption.
  eapply IHn with (n':=n); try assumption. 
  simpl in SAT.
  apply SAT.
  omega.
  simpl.
  intros.
  destruct (0 <? z0).
  simpl.
  apply IHn; try assumption.
  eapply sat_weak_imp; try assumption.
  apply SAT0.
  intros.
  simpl in SAT1.
  simpl.
  eapply sat_weak_imp; try assumption.
  simpl.
  simpl in SAT1.
  eapply IHn with (n':=n) in SAT1; try assumption.
  apply SAT1.
  omega.
  intros.
  assumption.
  omega.
  omega.
  omega.
  assumption.
  omega.
  }
Qed.


Lemma sat_pre_subs3:
  forall n c p o C a se1 se2 invs sp (bp: boundph p) (bg: boundgh C)
         (SAT: sat p o C (weakest_pre n sp (subs c se1) a se2 invs)),
    forall n' (LE: le n' n), sat p o C (weakest_pre n' sp c a (fun e => se2 (se1 e)) invs).
Proof.
  induction n.
  simpl.
  intros.
  destruct n'.
  reflexivity.
  inversion LE.
  destruct c; intros;
  try destruct n';
  try reflexivity;
  try assumption.
  {
  simpl.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(sat1,(sat2,(p1p2,C1C2)))))))))))))))))))).
  exists v, v0, p1, p2, phpdefp1p2, bp1, bp2, bp12, o1, o2, C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  exists.
  assumption.
  exists.
  intros.
  apply IHn; try assumption.
  apply sat2 with O'; try assumption.
  omega.
  split; assumption.
  }
  {
  simpl.
  eapply IHn; try assumption.
  eapply sat_weak_imp; try assumption.
  simpl in SAT.
  simpl.
  apply SAT.
  simpl.
  intros.
  eapply IHn in SAT0; try assumption.
  apply SAT0.
  omega.
  omega.
  omega.
  }
  {
  simpl.
  simpl in SAT.
  eapply IHn; try assumption.
  eapply sat_weak_imp; try assumption.
  apply SAT.
  simpl.
  intros.
  destruct (0 <? z).
  simpl.
  eapply IHn; try assumption.
  omega.
  eapply IHn; try assumption.
  omega.
  omega.
  omega.
  }
  {
  simpl.
  eapply sat_weak_imp; try assumption.
  eapply IHn with (n':=n); try assumption. 
  simpl in SAT.
  apply SAT.
  omega.
  simpl.
  intros.
  destruct (0 <? z).
  simpl.
  apply IHn; try assumption.
  eapply sat_weak_imp; try assumption.
  apply SAT0.
  intros.
  simpl in SAT1.
  simpl.
  eapply sat_weak_imp; try assumption.
  simpl.
  simpl in SAT1.
  eapply IHn with (n':=n); try assumption.
  apply SAT1.
  omega.
  intros.
  assumption.
  omega.
  omega.
  omega.
  assumption.
  omega.
  }
Qed.


Lemma sat_pre_subs:
  forall n c se a p o d x z invs sp (BP: boundph p) (BG: boundgh d),
    sat p o d (weakest_pre n sp (subs c (subse x z)) a se invs) <->
    sat p o d (weakest_pre n sp c a (fun e : exp => se (subse x z e)) invs).
Proof.
  split.
  intros. apply sat_pre_subs1 with n; try assumption. omega.
  intros. apply sat_pre_subs2 with n; try assumption. omega.
Qed.


(** # <font size="5"><b> Weakest Precondition - Satisfaction Relation </b></font> # *)

Lemma sat_Cons:
  forall m p O C sp n tx invs a
         (BP: boundph p)
         (BG: boundgh C)
         (NONE: forall z (IN: In z (map (fun x0 => ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
                  (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))), p z = None)
         (SAT: sat p O C (weakest_pre_ct (S m) sp (Cons n, tx) invs)),
    sat (dstr_cells' p (map (fun x0 : nat =>
      ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
      (0%Z, nil), (0%Z, nil), nil)) (seq 0 n)) (Some (Cell full 0)))
      O C (weakest_pre_ct (S m) sp (Val (Enum a), tx) invs).
Proof.
  intros.
  unfold weakest_pre_ct.
  assert (EQH: dstr_cells' p (map (fun x0 : nat => ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n)) (Some (Cell full 0)) = 
    phplus p (dstr_cells' (emp knowledge) (map (fun x0 : nat => ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n)) (Some (Cell full 0)))).
  {
  apply functional_extensionality.
  unfold dstr_cells'.
  unfold phplus.
  intros.
  destruct (in_dec (location_eq_dec Z.eq_dec) x
    (map (fun x0 : nat => ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  rewrite NONE.
  reflexivity.
  assumption.
  unfold emp.
  destruct (p x).
  destruct k; reflexivity.
  reflexivity.
  }
  rewrite EQH.

  assert (EQC: C = ghplus C (emp (option nat*nat))). repeat php_.
  rewrite EQC.
  simpl in SAT.
  apply SAT with None; repeat php_.
  {
  unfold boundph.
  unfold dstr_cells'.
  intros.
  destruct (in_dec (location_eq_dec Z.eq_dec) x
    (map (fun x0 : nat => ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  inversion H.
  apply full_bound.
  inversion H.
  }
  {
  unfold phplusdef.
  unfold dstr_cells'.
  intros.
  destruct (in_dec (location_eq_dec Z.eq_dec) x
    (map (fun x0 : nat => ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  rewrite NONE; try assumption. trivial.
  unfold emp.
  destruct (p x). destruct k; trivial. trivial.
  }
  {
  unfold boundph.
  unfold dstr_cells'.
  unfold phplus.
  intros.
  destruct (in_dec (location_eq_dec Z.eq_dec) x
    (map (fun x0 : nat => ((a + Z.of_nat x0)%Z, 0%Qc, (a + Z.of_nat x0)%Z, None, false,
    (0%Z, nil), (0%Z, nil), nil)) (seq 0 n))).
  rewrite NONE in H; try assumption.
  inversion H.
  apply full_bound.
  symmetry in H.
  unfold emp in H.
  eapply BP with x z.
  rewrite H.
  destruct (p x).
  destruct k; reflexivity.
  reflexivity.
  }
  {
  destruct O.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  }
  apply sat_dstr.
Qed.


Lemma sat_lookup:
  forall m p O C sp tx invs e
         (SAT: sat p O C (weakest_pre_ct (S m) sp (Lookup e, tx) invs)),
    exists v0 ll
           (EQ: ([[e]]) = ([[Aof ll]]))
           (pv: exists f' (f'le : Qclt 0 f'), p (evall ll) = Some (Cell f' v0)),
      sat p O C (weakest_pre_ct (S m) sp (Val (Enum v0), tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(eql,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))))).
  subst.
  rewrite phplus_comm; repeat php_.
  rewrite ghplus_comm; repeat php_.
  unfold weakest_pre_ct.
  simpl.
  apply Z.eqb_eq in eql.
  exists v0, v, eql.
  split.
  {
  destruct tmp1 as (f',(lef',pv)).
  assert (G2: Qclt 0 (v1 + f') /\ Qcle (v1 + f') 1).
  {
  eapply bp1.
  apply pv.
  }
  destruct G2 as (G3,G4).
  assert (G2: Qcle 0 (v1 + f')).
  {
  apply Qclt_le_weak; assumption.
  }  
  unfold phplusdef in phpdefp1p2.
  specialize phpdefp1p2 with (evall v).
  unfold phplus.
  rewrite pv in *.
  destruct (p2 (evall v)) eqn:p2v.
  destruct k; try contradiction.
  exists (f + (v1 + f'))%Qc.
  rewrite phpdefp1p2.
  exists.
  assert (G1: Qcle 0 f).
  {
  assert (G1: Qclt 0 f /\ Qcle f 1).
  {
  eapply bp2.
  apply p2v.
  }
  destruct G1 as (G1,G5).
  apply Qclt_le_weak; assumption.
  }
  replace 0 with (0+0).
  apply Qc_Ltet_plus; try assumption.
  omega.
  reflexivity.
  exists (v1 + f')%Qc, G3.
  reflexivity.
  }
  apply tmp2 with o1; repeat php_.
  apply oplus_comm; assumption.
Qed.


Lemma sat_mutate:
  forall m p O C sp e1 e2 tx invs
         (SAT: sat p O C (weakest_pre_ct (S m) sp (Mutate e1 e2, tx) invs)),
    exists l
         (EQl: Aof l = ([[e1]]))
         (pl: exists v, p l = Some (Cell full v)),
      sat (upd (location_eq_dec Z.eq_dec) p l (Some (Cell full ([[e2]])))) O C (weakest_pre_ct (S m) sp (tt, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,((tmp1,tmp2),(tmp3,(p1p2,C1C2)))))))))))))))))))).
  subst.
  apply Z.eqb_eq in tmp1.
  unfold id in *.
  symmetry in tmp1.
  destruct tmp2 as (v',(lef',p1v)).
  assert (v'0: v' = 0%Qc).
  {
  assert (G: Qclt 0 (1 + v') /\ Qcle (1 + v') 1).
  {
  eapply bp1.
  apply p1v.
  }
  destruct G as (G1,G2).
  apply qcplusle in G2.
  apply Qcle_antisym; assumption.
  }
  rewrite v'0 in *.
  rewrite Qcplus_0_r in p1v.
  exists (evall v), tmp1.
  exists.
  unfold phplus.
  unfold phplusdef in phpdefp1p2.
  specialize phpdefp1p2 with (evall v).
  unfold boundph in bp1p2.
  specialize bp1p2 with (x:=evall v).
  unfold phplus in bp1p2.
  rewrite p1v in *.  
  destruct (p2 (evall v)) eqn:p2v.
  destruct k; inversion phpdefp1p2.
  assert (G: f = 0%Qc).
  {
  assert (G: Qclt 0 (1 + f) /\ Qcle (1 + f) 1).
  {
  eapply bp1p2.
  reflexivity.
  }
  destruct G as (G1,G2).
  assert (G: Qclt 0 f /\ Qcle f 1).
  {
  eapply bp2.
  apply p2v.
  }
  destruct G as (G3,G4).
  apply qcplusle in G2.
  apply Qcle_antisym; try assumption.
  apply Qclt_le_weak. assumption.
  }
  rewrite G in *.
  rewrite Qcplus_0_r.
  exists ([[v0]]).
  reflexivity.
  exists ([[v0]]).
  reflexivity.

  assert (p2v: p2 (evall v) = None).
  {
  unfold boundph in bp1p2.
  specialize bp1p2 with (x:=(evall v)).
  unfold phplus in bp1p2.
  unfold phplusdef in phpdefp1p2.
  specialize phpdefp1p2 with (evall v).
  rewrite p1v in *.
  destruct (p2 (evall v)) eqn:p2v.
  destruct k; try contradiction.
  assert (CO: Qclt 0 (1 + f) /\ Qcle (1 + f) 1).
  {
  apply bp1p2 with ([[v0]]).
  reflexivity.
  }
  destruct CO as (CO1,CO2).
  assert (CO: Qclt 0 f /\ Qcle f 1).
  {
  eapply bp2.
  apply p2v.
  }
  destruct CO as (CO3,CO4).
  exfalso.
  apply qcpluslelt with f; assumption.
  reflexivity.
  }

  assert (phpp1up2: phplusdef (upd (location_eq_dec Z.eq_dec) p1 (evall v) (Some (Cell full ([[e2]])))) p2).
  {
  apply phpdef_v; try assumption.
  }

  assert (EQH: upd (location_eq_dec Z.eq_dec) (phplus p1 p2) (evall v)
    (Some (Cell full ([[e2]]))) =
    phplus p2 (upd (location_eq_dec Z.eq_dec) p1 (evall v)
    (Some (Cell full ([[e2]]))))).
  {
  rewrite <- phplus_upd; repeat php_.
  unfold not.
  intros.
  destruct H as (v0',(f,(v1',(f',(eq,p22v))))).
  rewrite p22v in p2v.
  inversion p2v.
  intros.
  inversion H.
  }
  rewrite EQH.
  rewrite ghplus_comm; repeat php_.
  apply tmp3 with o1; repeat php_.
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',eq).
  inversion eq.
  apply full_bound.
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  apply full_bound.
  intros.
  destruct CELL as (v1,(v2,(eq,p22v))).
  rewrite p22v in p2v.
  inversion p2v.
  apply oplus_comm; assumption.
  exists 0%Qc.
  exists.
  unfold Qcle.
  unfold QArith_base.Qle.
  omega.
  unfold upd.
  destruct (location_eq_dec Z.eq_dec (evall v) (evall v)).
  reflexivity.
  contradiction.
Qed.


Lemma sat_fork:
  forall m p O C c tx invs sp
         (SAT: sat p (Some O) C (weakest_pre_ct (S m) sp (Fork c, tx) invs)),
    exists p1 p2 O1 O2 C1 C2 (GHPD: ghplusdef C1 C2) (BP1: boundph p1) (BP2: boundph p2) (PHPD: phplusdef p1 p2) (BP12: boundph (phplus p1 p2))
          (p1p2: p = phplus p1 p2) (O1O2: Permutation.Permutation (O1++O2) O) (C1C2: C = ghplus C1 C2)
     (SAT1: sat p1 (Some O1) C1 (weakest_pre_tx (S m) sp tx invs 0))
     (SAT2: sat p2 (Some O2) C2 (weakest_pre m sp c (fun _ : Z => Aobs nil) id invs)), True.
Proof.
  intros.
  simpl in SAT.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))).
  destruct tmp1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4)))))))))))))))))).
  subst.

  assert (tmp: Permutation (map evalol v ++ map evalol v0) O /\ O4 = None /\ o2 = None).
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

  exists (phplus p3 p4), p2, (map evalol v), (map evalol v0), (ghplus C3 C4), c2, ghpdefc1c2, bp1, bp2.
  exists phpdefp1p2, bp1p2.
  exists. reflexivity.
  exists. assumption.
  exists. reflexivity.
  exists.
  rewrite ghplus_comm; repeat php_.
  rewrite phplus_comm; repeat php_.
  apply tmp5 with (Some (map evalol v)); repeat php_.
  apply sn_op.
  apply Permutation_refl.
  apply fs_op.
  apply Permutation_refl.
  exists.
  replace p2 with (phplus p2 (emp knowledge)).
  replace c2 with (ghplus c2 (emp (option nat*nat))).
  apply tmp2 with (Some (map evalol v0)); repeat php_.
  apply sn_op.
  apply Permutation_refl.
  apply fs_op.
  apply Permutation_refl.
  apply ghplus_emp.
  apply phplus_emp.
  trivial.
Qed.


Lemma sat_newlock:
  forall m p O C tx invs sp l (BP: boundph p) (BC: boundgh C)
        (Pl: forall ll (EQA: Aof ll = l), p ll = None)
        (SAT: sat p O C (weakest_pre_ct (S m) sp (Newlock, tx) invs)),
    exists r,
      sat (upd (location_eq_dec Z.eq_dec) p ((l, r, l, None, false), (0%Z,nil), (0%Z,nil), nil) (Some (Ulock empb empb))) O C (weakest_pre_ct (S m) sp (Val (Enum l), tx) invs).
Proof.
  simpl.
  intros.
  specialize SAT with l.
  destruct SAT as (r,sat1).
  exists r.

  assert (phpdefu: phplusdef (upd (location_eq_dec Z.eq_dec) (emp knowledge)
    ((l, r, l, None, false), (0%Z,nil), (0%Z,nil), nil) (Some (Ulock empb empb))) p).
  {
  apply phpdef_ulock.
  repeat php_.
  apply Pl.
  reflexivity.
  }

  replace (upd (location_eq_dec Z.eq_dec) p ((l, r, l, None, false), (0%Z,nil), (0%Z,nil), nil)
    (Some (Ulock empb empb))) with
    (phplus p (upd (location_eq_dec Z.eq_dec) (emp knowledge) ((l, r, l, None, false), (0%Z,nil), (0%Z,nil), nil)
    (Some (Ulock empb empb)))).
  replace C with (ghplus C (emp (option nat*nat))).
  specialize Pl with ((l, r, l, None, false), (0%Z,nil), (0%Z,nil), nil).
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
  intros.
  inversion H.
Qed.


Lemma sat_initl:
  forall m p O C tx invs sp
        (INJ: injph p)
        (SAT: sat p (Some O) C (EX l, (EX O, (EX wt, (EX ot, (EX i, (EX params, (EX e, ((Abool (Z.eqb ([[e]]) ([[Aof l]]))
        &* Aulock l wt ot ** subsas params (invs i wt ot) ** Aobs O ** 
        ((Alock ((Aof l, Rof l, Lof l, Xof l, Pof l), (i,params), Mof l, M'of l) ** Aobs O) --*
        (weakest_pre_tx (S m) sp tx invs 0)))))))))))),
    exists (l: location Z) p1 p2 wt ot C1 C2 i e
           (GHPD: ghplusdef C1 C2)
           (EQl: Aof l = ([[e]]))
           (BP1: boundph p1)
           (BP2: boundph p2)
           (phpdp1p2: phplusdef p1 p2)
           (p1p2: p = phplus p1 p2)
           (C1C2: C = ghplus C1 C2) 
           (P1l: p1 l = Some (Ulock wt ot))
           (p2inv: sat p2 None C2 (subsas (snd i) (invs (fst i) wt ot))),
    sat (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p1 l None) 
(Oof l, i, Mof l, M'of l) (Some Lock)) (Some O) C1 (weakest_pre_ct (S m) sp (tt, tx) invs).
Proof.
  intros.
  simpl in SAT.
  destruct SAT as (v,(v0,(v1,(v2,(v3,(v4,(v5,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(sat1,(sat2,(p1p2,C1C2)))))))))))))))))))))))))).
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

  assert (o36N: O3 = None /\ O6 = None /\ Permutation (map evalol v0) O).
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

  assert (phpdefp515u: phplusdef p6 (upd (location_eq_dec Z.eq_dec) (phplus p1 p5) (evall v) (Some Lock))).
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

  assert (EQH: upd (location_eq_dec Z.eq_dec) (phplus p1 p4) (evall v) (Some Lock) = phplus p6 (upd (location_eq_dec Z.eq_dec) (phplus p1 p5) (evall v) (Some Lock))).
  {
  replace (phplus p6 (upd (location_eq_dec Z.eq_dec) (phplus p1 p5) (evall v) (Some Lock))) with
    (phplus (upd (location_eq_dec Z.eq_dec) (phplus p1 p5) (evall v) (Some Lock)) p6).
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

  assert (bp15u: boundph (upd (location_eq_dec Z.eq_dec) (phplus p1 p5) (evall v) (Some Lock))).
  {
  apply boundph_upd.
  tauto.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bp515: boundph (phplus p6 (upd (location_eq_dec Z.eq_dec) (phplus p1 p5) (evall v) (Some Lock)))).
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

  assert (phpdefp1u5: phplusdef (upd (location_eq_dec Z.eq_dec) p1 (evall v) (Some Lock)) p5).
  {
  apply phpdef_locked_lock.
  tauto.
  exists v1, v2.
  tauto.
  }

  assert (bp1u: boundph (upd (location_eq_dec Z.eq_dec) p1 (evall v) (Some Lock))).
  {
  apply boundph_upd;
  try tauto.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bp1up5: boundph (phplus (upd (location_eq_dec Z.eq_dec) p1 (evall v) (Some Lock)) p5)).
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
  exists (v3,v4), v5.
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

  assert (p6en: p6 (evall (Oof v, (v3, v4), Mof v, M'of v)) = None).
  {
  destruct (p6 (evall (Oof v, (v3, v4), Mof v, M'of v))) eqn:p6e.

  assert (p1356v: phplus p1 (phplus p3 (phplus p5 p6)) (evall (Oof v, (v3, v4), Mof v, M'of v)) <> None).
  {
  apply phplus_some'; repeat php_.
  apply phplus_some'; repeat php_.
  apply phplus_some'; repeat php_.
  rewrite p6e.
  apply some_none.
  }

  assert (CO: evall (Oof v, (v3, v4), Mof v, M'of v) = evall v).
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

  assert (p5en: p5 (evall (Oof v, (v3, v4), Mof v, M'of v)) = None).
  {
  destruct (p5 (evall (Oof v, (v3, v4), Mof v, M'of v))) eqn:p5e.
  assert (p1356v: phplus p1 (phplus p3 (phplus p5 p6)) (evall (Oof v, (v3, v4), Mof v, M'of v)) <> None).
  {
  apply phplus_some'; repeat php_.
  apply phplus_some'; repeat php_.
  apply phplus_some; repeat php_.
  rewrite p5e.
  apply some_none.
  }
  assert (CO: evall (Oof v, (v3, v4), Mof v, M'of v) = evall v).
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


  assert (phpdefp6u: phplusdef p6 (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) (phplus p1 p5) (evall v) None)
    (evall (Oof v, (v3, v4), Mof v, M'of v)) (Some Lock))).
  {
  apply phpdef_comm.
  apply phpdef_v; repeat php_.
  apply phpdef_v; repeat php_.
  }

  assert (bp15u': boundph (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) (phplus p1 p5) (evall v) None)
    ((Aof (evall v), Rof (evall v), Lof (evall v), Xof (evall v), Pof (evall v)), (v3, v4),
    Mof (evall v), M'of (evall v)) (Some Lock))).
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

  assert (EQH': upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) (phplus p1 p4) (evall v) None)
    (Oof (evall v), (v3, v4),
    Mof (evall v), M'of (evall v)) (Some Lock) =
    phplus p6 (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) (phplus p1 p5) (evall v) None)
    (Oof (evall v), (v3, v4),
    Mof (evall v), M'of (evall v)) (Some Lock))).
  {
  subst.
  symmetry.
  rewrite phplus_comm; repeat php_.
  rewrite phplus_upd; repeat php_.
  replace (phplus (upd (location_eq_dec Z.eq_dec) (phplus p1 p5) (evall v) None) p6) with
    (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p5 p6)) (evall v) None).
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
  assert (CO1: (Oof (evall v), (v3, v4),
    Mof (evall v), M'of (evall v)) = (evall v)).
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
     (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) (phplus p1 p5) (evall v) None)
        (Oof (evall v), (v3, v4),
    Mof (evall v), M'of (evall v)) (Some Lock)))).
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

  assert (phpdefu5: phplusdef (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p1 (evall v) None)
    (evall (Oof v, (v3, v4), Mof v, M'of v)) (Some Lock)) p5).
  {
  apply phpdef_v; repeat php_.
  apply phpdef_none; repeat php_.
  }

  assert (bu1: boundph (upd (location_eq_dec Z.eq_dec) p1 (evall v) None)).
  {
  apply boundph_upd.
  assumption.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (buu1: boundph (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p1 (evall v) None)
    (evall (Oof v, (v3, v4), Mof v, M'of v)) (Some Lock))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (phpdefp1up5: phplusdef (upd (location_eq_dec Z.eq_dec) p1 (evall v) None) p5).
  {
  apply phpdef_v; repeat php_.
  }

  assert (bp1u5': boundph (phplus (upd (location_eq_dec Z.eq_dec) p1 (evall v) None) p5)).
  {
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1',(v2',(CO,rest))).
  inversion CO.
  }

  assert (bu15: boundph (phplus (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p1 (evall v) None)
    (evall (Oof v, (v3, v4), Mof v, M'of v)) (Some Lock)) p5)).
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

  exists (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p1 (evall v) None) (evall (Oof v, (v3, v4), Mof v, M'of v)) (Some Lock)), p5.
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
  destruct ((location_eq_dec Z.eq_dec) (evall (Aof v, Rof v, Lof v, Xof v, Pof v, (v3, v4), Mof v, M'of v))
    (evall (Oof v, (v3, v4), Mof v, M'of v))).
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


Lemma sat_acquire0:
  forall m p O C l tx invs sp
        (SAT: sat p (Some O) C (weakest_pre_ct (S m) sp (Acquire l, tx) invs)),
  exists ll
         (EQL: Aof ll = ([[l]]))
         (Pl: p ll = Some Lock \/ exists Wt Ot, p ll = Some (Locked Wt Ot))
         (PRCl: prcl (Oof ll) O),
    sat p (Some O) C (weakest_pre_ct (S m) sp (Waiting4lock l, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v0,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))).
  destruct tmp1 as (eqls,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4))))))))))))))))))).
  subst.
  assert (phpdefp32p42: phplusdef p3 p2 /\ phplusdef p4 p2). repeat php_.
  assert (ghpdefp32p42: ghplusdef C3 c2 /\ ghplusdef C4 c2). repeat php_.
  destruct eqls as (EQ1,EQ2).
  apply Z.eqb_eq in EQ1.
  unfold id in *.

  assert (PERM: Permutation O (map evalol v0) /\ o2 = None).
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
  apply prcl_perm with (map evalol v0).
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
  split.
  apply Z.eqb_eq.
  assumption.
  assumption.
  exists p3, p4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists None, (Some (map evalol v0)), C3, C4.
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
  forall m p O C l tx invs sp
        (SAT: sat p (Some O) C (weakest_pre_ct (S m) sp (Acquire l, tx) invs)),
  exists ll
         (EQL: Aof ll = ([[l]]))
         (Pl: p ll = Some Lock \/ exists Wt Ot, p ll = Some (Locked Wt Ot))
         (PRCl: prcl (Oof ll) O),
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
      sat (phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt ot))) p1) (Some (Oof ll :: O)) (ghplus C C1) (weakest_pre_ct (S m) sp (tt, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))).
  destruct tmp1 as (eqls,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4))))))))))))))))))).
  subst.

  assert (phpdefp32p42: phplusdef p3 p2 /\ phplusdef p4 p2). repeat php_.
  assert (ghpdefp32p42: ghplusdef C3 c2 /\ ghplusdef C4 c2). repeat php_.

  destruct eqls as (EQ1,EQ2).
  apply Z.eqb_eq in EQ1.
  unfold id in *.

  assert (PERM: Permutation O (map evalol v) /\ o2 = None).
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
  apply prcl_perm with (map evalol v).
  assumption.
  assumption.
  intros.

  assert (p2v0: p2 (evall v0) = Some Lock \/ p2 (evall v0) = None).
  {
  apply phplus_lock_none with (phplus p3 p4).
  rewrite phplus_comm; repeat php_.
  }

  assert (phpdefp2up34: phplusdef p2 (upd (location_eq_dec Z.eq_dec) (phplus p3 p4) (evall v0) (Some (Locked wt ot)))).
  {
  apply phpdef_comm.
  apply phpdef_locked'; repeat php_.
  }

  assert (phpdefp1p34p1p2: phplusdef p1 (phplus p3 p4) /\ phplusdef p1 p2). repeat php_.
  assert (phpdefp13p14: phplusdef p1 p3 /\ phplusdef p1 p4). repeat php_.

  assert (phpdefup34p1: phplusdef (upd (location_eq_dec Z.eq_dec) (phplus p3 p4) (evall v0) (Some (Locked wt ot))) p1).
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

  assert (bup34p1: boundph (phplus (upd (location_eq_dec Z.eq_dec) (phplus p3 p4) (evall v0) (Some (Locked wt ot))) p1)).
  {
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1',(v2',(CO,rest))).
  inversion CO.
  }

  assert (EQH: phplus (upd (location_eq_dec Z.eq_dec) (phplus (phplus p3 p4) p2) (evall v0)
    (Some (Locked wt ot))) p1 = 
    phplus p2 (phplus (upd (location_eq_dec Z.eq_dec) (phplus p3 p4) (evall v0)
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
    (upd (location_eq_dec Z.eq_dec) (phplus p3 p4) (evall v0) (Some (Locked wt ot))) p1))).
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

  assert (bu34: boundph (upd (location_eq_dec Z.eq_dec) (phplus p3 p4) (evall v0) (Some (Locked wt ot)))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  rewrite EQH.
  rewrite EQC.
  apply tmp2 with wt ot (Some (evalol (Oof v0) :: O)); repeat php_.
  apply sn_op.
  apply Permutation_refl.
  exists (emp knowledge), (phplus (upd (location_eq_dec Z.eq_dec) (phplus p3 p4) (evall v0) (Some (Locked wt ot))) p1).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (evalol (Oof v0) :: map evalol v)), None.
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
  exists (upd (location_eq_dec Z.eq_dec) (phplus p3 p4) (evall v0) (Some (Locked wt ot))), p1.
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
  destruct ((location_eq_dec Z.eq_dec) (evall v0) (evall v0)).
  reflexivity.
  contradiction.
  split. assumption.
  split; reflexivity.
  split; repeat php_.
Qed.


Lemma sat_wait4lock:
  forall m p O C l tx invs sp
        (SAT: sat p (Some O) C (weakest_pre_ct (S m) sp (Waiting4lock l, tx) invs)),
  exists ll
         (EQL: Aof ll = ([[l]]))
         (Pl: p ll = Some Lock \/ exists Wt Ot, p ll = Some (Locked Wt Ot))
         (PRCl: prcl (Oof ll) O),
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
      sat (phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt ot))) p1) (Some (Oof ll :: O)) (ghplus C C1) (weakest_pre_ct (S m) sp (tt, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))).
  destruct tmp1 as (eqls,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4))))))))))))))))))).
  subst.

  assert (phpdefp32p42: phplusdef p3 p2 /\ phplusdef p4 p2). repeat php_.
  assert (ghpdefp32p42: ghplusdef C3 c2 /\ ghplusdef C4 c2). repeat php_.

  destruct eqls as (EQ1,EQ2).
  apply Z.eqb_eq in EQ1.
  unfold id in *.

  assert (PERM: Permutation O (map evalol v) /\ o2 = None).
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
  apply prcl_perm with (map evalol v).
  assumption.
  assumption.
  intros.

  assert (p2v0: p2 (evall v0) = Some Lock \/ p2 (evall v0) = None).
  {
  apply phplus_lock_none with (phplus p3 p4).
  rewrite phplus_comm; repeat php_.
  }

  assert (phpdefp2up34: phplusdef p2 (upd (location_eq_dec Z.eq_dec) (phplus p3 p4) (evall v0) (Some (Locked wt ot)))).
  {
  apply phpdef_comm.
  apply phpdef_locked'; repeat php_.
  }

  assert (phpdefp1p34p1p2: phplusdef p1 (phplus p3 p4) /\ phplusdef p1 p2). repeat php_.
  assert (phpdefp13p14: phplusdef p1 p3 /\ phplusdef p1 p4). repeat php_.

  assert (phpdefup34p1: phplusdef (upd (location_eq_dec Z.eq_dec) (phplus p3 p4) (evall v0) (Some (Locked wt ot))) p1).
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

  assert (bup34p1: boundph (phplus (upd (location_eq_dec Z.eq_dec) (phplus p3 p4) (evall v0) (Some (Locked wt ot))) p1)).
  {
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1',(v2',(CO,rest))).
  inversion CO.
  }

  assert (EQH: phplus (upd (location_eq_dec Z.eq_dec) (phplus (phplus p3 p4) p2) (evall v0)
    (Some (Locked wt ot))) p1 = 
    phplus p2 (phplus (upd (location_eq_dec Z.eq_dec) (phplus p3 p4) (evall v0)
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
    (upd (location_eq_dec Z.eq_dec) (phplus p3 p4) (evall v0) (Some (Locked wt ot))) p1))).
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

  assert (bu34: boundph (upd (location_eq_dec Z.eq_dec) (phplus p3 p4) (evall v0) (Some (Locked wt ot)))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  rewrite EQH.
  rewrite EQC.
  apply tmp2 with wt ot (Some (evalol (Oof v0) :: O)); repeat php_.
  apply sn_op.
  apply Permutation_refl.
  exists (emp knowledge), (phplus (upd (location_eq_dec Z.eq_dec) (phplus p3 p4) (evall v0) (Some (Locked wt ot))) p1).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (evalol (Oof v0) :: map evalol v)), None.
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
  exists (upd (location_eq_dec Z.eq_dec) (phplus p3 p4) (evall v0) (Some (Locked wt ot))), p1.
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
  destruct ((location_eq_dec Z.eq_dec) (evall v0) (evall v0)).
  reflexivity.
  contradiction.
  split. assumption.
  split; reflexivity.
  split; repeat php_.
Qed.


Lemma sat_release:
  forall m p O C l tx invs sp
        (SAT: sat p (Some O) C (weakest_pre_ct (S m) sp (Release l, tx) invs)),
    exists ll p1 p2 wt ot C1 C2 O1
           (EQl: Aof ll = ([[l]]))
           (OO1: Permutation O (Oof ll :: O1))
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
    sat (upd (location_eq_dec Z.eq_dec) p1 ll (Some Lock)) (Some O1) C1 (weakest_pre_ct (S m) sp (tt, tx) invs).
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
  assert (tmp: Permutation O (evalol (Oof v0) :: map evalol v) /\ O6 = None /\ o2 = None).
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

  assert (bpu: boundph (upd (location_eq_dec Z.eq_dec) p5 (evall v0) (Some Lock))).
  {
  apply boundph_upd.
  assumption.
  intros f CO.
  destruct CO as (z',CO).
  inversion CO.
  }

  assert (phpdp3p5u: phplusdef p3 (upd (location_eq_dec Z.eq_dec) p5 (evall v0) (Some Lock))).
  {
  apply phpdef_comm.
  apply phpdef_locked_lock.
  repeat php_.
  exists v1, v2.
  tauto.
  }

  assert (phpdp2p5u: phplusdef p2 (upd (location_eq_dec Z.eq_dec) p5 (evall v0) (Some Lock))).
  {
  apply phpdef_comm.
  apply phpdef_locked_lock.
  repeat php_.
  exists v1, v2.
  tauto.
  }

  assert (bp35u: boundph (phplus p3 (upd (location_eq_dec Z.eq_dec) p5 (evall v0) (Some Lock)))).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1',(v2',(CO,rest))).
  inversion CO.
  }

  assert (eqh2: phplus p3 (upd (location_eq_dec Z.eq_dec) p5 (evall v0) (Some Lock)) = 
                upd (location_eq_dec Z.eq_dec) (phplus p5 p3) (evall v0) (Some Lock)).
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

  assert (phpdefp2p43u: phplusdef p2 (upd (location_eq_dec Z.eq_dec) (phplus p5 p3) (evall v0) (Some Lock))).
  {
  apply phpdef_comm.
  apply phpdef_locked_lock.
  apply phpdef_pair'; repeat php_.
  exists v1, v2.
  tauto.
  }

  assert (bp2p35u: boundph (phplus p2 (phplus p3 (upd (location_eq_dec Z.eq_dec) p5 (evall v0) (Some Lock))))).
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

  exists (evall v0), (phplus p2 (phplus p3 p5)), p6, v1, v2, (ghplus C2 (ghplus C3 C5)), C6, (map evalol v).
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
  assert (G: sat (phplus p2 (phplus p3 (upd (location_eq_dec Z.eq_dec) p5 (evall v0) (Some Lock)))) (Some (map evalol v)) (ghplus C2 (ghplus C3 C5))
    (weakest_pre_tx (S m) sp tx invs 0)).
  {
  apply tmp2 with (Some (map evalol v)); repeat php_.
  apply boundgh_mon with C6.
  rewrite <- eqg1. assumption.
  apply sn_op.
  apply Permutation_refl.
  exists p3, (upd (location_eq_dec Z.eq_dec) p5 (evall v0) (Some Lock)).
  exists. repeat php_.
  exists. repeat php_.
  exists. assumption.
  exists. repeat php_.
  exists (Some (map evalol v)), None, C3, C5.
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
  replace (upd (location_eq_dec Z.eq_dec) (phplus p2 (phplus p3 p5)) (evall v0) (Some Lock)) with
    (phplus p2 (phplus p3 (upd (location_eq_dec Z.eq_dec) p5 (evall v0) (Some Lock)))).
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


Lemma sat_newcond:
  forall m p O C tx invs sp v (BP: boundph p) (BC: boundgh C)
        (Pv: forall r I L X M M' P, p (v, r, I, L, X, M, M', P) = None)
        (SAT: sat p O C (weakest_pre_ct (S m) sp (Newcond, tx) invs)),
    exists R X P,
      sat (upd (location_eq_dec Z.eq_dec) p ((v, R, v, X, P), (0%Z,nil), (0,nil), nil) (Some Ucond)) O C (weakest_pre_ct (S m) sp (Val (Enum v), tx) invs).
Proof.
  simpl.
  intros.
  specialize SAT with v.

  destruct SAT as (R,(P,(X, sat1))).
  exists R, X, P.

  replace C with (ghplus C (emp (option nat*nat))).
  assert (bue: boundph (upd (location_eq_dec Z.eq_dec) (emp knowledge)
    (v, R, v, X, P, (0, nil), (0, nil), nil) (Some Ucond))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (phpdefpu: phplusdef p (upd (location_eq_dec Z.eq_dec) (emp knowledge)
    (v, R, v, X, P, (0, nil), (0, nil), nil) (Some Ucond))).
  {
  apply phpdef_comm; repeat php_.
  apply phpdef_v; repeat php_.
  }

  assert (bpue: boundph (phplus p (upd (location_eq_dec Z.eq_dec) (emp knowledge)
    (v, R, v, X, P, (0, nil), (0, nil), nil) (Some Ucond)))).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1',(v2',(CO,rest))).
  inversion CO.
  }

  assert (EQH: upd (location_eq_dec Z.eq_dec) p ((v, R, v, X, P), (0%Z,nil), (0,nil), nil)
    (Some Ucond) = phplus p (upd (location_eq_dec Z.eq_dec) (emp knowledge) ((v, R, v, X, P), (0%Z,nil), (0,nil), nil) (Some Ucond))).
  {
  rewrite phplus_comm; repeat php_.
  rewrite phplus_upd.
  reflexivity.
  unfold not.
  intros.
  destruct H as (v',(f',(v'',(f'',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
  }

  rewrite EQH.
  apply sat1 with None; repeat php_.
  destruct O.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  unfold upd.
  simpl.
  destruct (location_eq_dec Z.eq_dec
    (evall (Enum v, R, Enum v, X, P, (0, nil), (0, nil), nil))
    (v, R, v, X, P, (0, nil), (0, nil), nil)).
  reflexivity.
  contradiction.
  repeat php_.
Qed.


Lemma sat_initc:
  forall m p O C tx invs sp
        (INJ: injph p)
        (SAT: sat p (Some O) C ((EX v, (EX l, (EX M, (EX M', (EX wt, (EX ot, (EX e, (Abool (Z.eqb ([[e]]) ([[Aof v]])) &*
        Aulock l wt ot ** Aucond v ** (Aulock l wt ot ** Aicond ((Aof v, Rof v, Aof l, Xof v, Pof v), Iof v, M, M') --*
        (weakest_pre_tx (S m) sp tx invs 0)))))))))))),
    exists (l: location Z) ml m'l lk wt ot e
           (EQl: Aof l = ([[e]]))
           (Pl: p l = Some Ucond)
           (Plk: p lk = Some (Ulock wt ot)),
    sat (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p l None) ((Aof l, Rof l, Aof lk, Xof l, Pof l), Iof l, ml, m'l) (Some Icond)) (Some O) C (weakest_pre_ct (S m) sp (tt, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(v2,(v3,(v4,(v5,(eqls,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4)))))))))))))))))).
  subst.
  exists (evall v), v1, (map evalol v2), (evall v0), v3, v4, v5.
  apply Z.eqb_eq in eqls.
  unfold id in *.
  exists.
  symmetry.
  assumption.
  exists.
  apply phplus_Ucond'; repeat php_.
  apply phplus_Ucond; repeat php_.
  exists.
  apply phplus_ulock; repeat php_.
  assert (phpdefp13p14: phplusdef p1 p3 /\ phplusdef p1 p4).
  repeat php_.

  assert (ghpdefp13p14: ghplusdef c1 C3 /\ ghplusdef c1 C4).
  repeat php_.

  assert (p4n: p4 (evall v) = None).
  {
  unfold phplusdef in phpdefp3p4.
  specialize phpdefp3p4 with (evall v).
  rewrite tmp4 in *.
  unfold phplus.
  destruct (p4 (evall v)).
  contradiction.
  reflexivity.
  }

  assert (p1n: p1 (evall v) = None).
  {
  destruct phpdefp13p14 as (pp1,pp2).
  unfold phplusdef in pp1.
  specialize pp1 with (evall v).
  rewrite tmp4 in *.
  unfold phplus.
  destruct (p1 (evall v)).
  destruct k; contradiction.
  reflexivity.
  }

  assert (p14v: phplus p4 p1 (evall v) = None).
  {
  unfold phplus.
  rewrite p1n, p4n.
  reflexivity.
  }

  assert (p4n': p4 (Aof (evall v), Rof (evall v), Aof (evall v0), Xof (evall v),
    Pof (evall v), Iof (evall v), v1, map evalol v2) = None).
  {
  destruct (p4 (Aof (evall v), Rof (evall v), Aof (evall v0), Xof (evall v),
  Pof (evall v), Iof (evall v), v1, map evalol v2)) eqn:p4n'.
  assert (CO: (Aof (evall v), Rof (evall v), Aof (evall v0), Xof (evall v),
        Pof (evall v), Iof (evall v), v1, map evalol v2) = evall v).
  {
  apply INJ.
  apply phplus_some'; repeat php_.
  apply phplus_some'; repeat php_.
  rewrite p4n'.
  apply some_none.
  apply phplus_some'; repeat php_.
  apply phplus_some; repeat php_.
  rewrite tmp4.
  apply some_none.
  reflexivity.
  }
  rewrite CO in p4n'.
  rewrite p4n in p4n'.
  inversion p4n'.
  reflexivity.
  }

  assert (phpdefp3up4: phplusdef (upd (location_eq_dec Z.eq_dec)
    (upd (location_eq_dec Z.eq_dec) p3 (evall v) None)
    (Aof (evall v), Rof (evall v), Aof (evall v0), Xof (evall v),
    Pof (evall v), Iof (evall v), v1, map evalol v2) (Some Icond)) p4).
  {
  apply phpdef_v.
  apply phpdef_none.
  assumption.
  assumption.
  }

  assert (p1n': p1 (Aof (evall v), Rof (evall v), Aof (evall v0), Xof (evall v),
    Pof (evall v), Iof (evall v), v1, map evalol v2) = None).
  {
  destruct (p1 (Aof (evall v), Rof (evall v), Aof (evall v0), Xof (evall v),
  Pof (evall v), Iof (evall v), v1, map evalol v2)) eqn:p1n'.
  assert (CO: (Aof (evall v), Rof (evall v), Aof (evall v0), Xof (evall v),
        Pof (evall v), Iof (evall v), v1, map evalol v2) = evall v).
  {
  apply INJ.
  apply phplus_some; repeat php_.
  rewrite p1n'.
  apply some_none.
  apply phplus_some'; repeat php_.
  apply phplus_some; repeat php_.
  rewrite tmp4.
  apply some_none.
  reflexivity.
  }
  rewrite CO in p1n'.
  rewrite p1n in p1n'.
  inversion p1n'.
  reflexivity.
  }

  assert (phpdefp3up1: phplusdef (upd (location_eq_dec Z.eq_dec)
     (upd (location_eq_dec Z.eq_dec) p3 (evall v) None)
     (Aof (evall v), Rof (evall v), Aof (evall v0), Xof (evall v),
     Pof (evall v), Iof (evall v), v1, map evalol v2) (Some Icond)) p1).
  {
  apply phpdef_v.
  apply phpdef_none.
  repeat php_.
  assumption.
  }

  assert (EQH: upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p4)) (evall v) None)
   (Aof (evall v), Rof (evall v), Aof (evall v0), Xof (evall v), Pof (evall v), Iof (evall v), v1, map evalol v2) (Some Icond) =
    phplus p4 (phplus p1 (upd (location_eq_dec Z.eq_dec) (upd (location_eq_dec Z.eq_dec) p3 (evall v) None)
   (Aof (evall v), Rof (evall v), Aof (evall v0), Xof (evall v), Pof (evall v), Iof (evall v), v1, map evalol v2) (Some Icond)))).
  {
  replace (phplus p1 (phplus p3 p4)) with (phplus (phplus p4 p1) p3).
  rewrite <- phplus_assoc.
  replace (phplus (phplus p4 p1)
  (upd (location_eq_dec Z.eq_dec)
     (upd (location_eq_dec Z.eq_dec) p3 (evall v) None)
     (Aof (evall v), Rof (evall v), Aof (evall v0), Xof (evall v),
     Pof (evall v), Iof (evall v), v1, map evalol v2) (Some Icond)))
  with (phplus (upd (location_eq_dec Z.eq_dec)
     (upd (location_eq_dec Z.eq_dec) p3 (evall v) None)
     (Aof (evall v), Rof (evall v), Aof (evall v0), Xof (evall v),
     Pof (evall v), Iof (evall v), v1, map evalol v2) (Some Icond)) (phplus p4 p1)).
  rewrite phplus_upd.
  rewrite phplus_upd.
  replace (phplus (phplus p4 p1) p3) with (phplus p3 (phplus p4 p1)).
  reflexivity.
  repeat php_.
  unfold not.
  intros.
  destruct H as (v0',(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros CO.
  inversion CO.
  intros.
  assumption.
  unfold not.
  intros.
  destruct H as (v0',(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros CO.
  inversion CO.
  intros CO.
  inversion CO.
  apply phplus_comm.
  repeat php_.
  repeat php_.
  repeat php_.
  repeat php_.
  rewrite phplus_comm; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  }
  rewrite EQH.
  assert (EQC: ghplus c1 (ghplus C3 C4) = ghplus C4 (ghplus c1 C3)).
  {
  rewrite <- ghplus_assoc; repeat php_.
  }
  rewrite EQC.
  assert (exo: exists O', oplus O4 O' (Some O)).
  {
  inversion opo1o2.
  rewrite <- H0 in opO3O4.
  inversion opO3O4.
  exists (Some O).
  apply sn_op.
  apply Permutation_refl.
  rewrite <- H0 in opO3O4.
  inversion opO3O4.
  exists (Some O).
  apply sn_op.
  apply Permutation_refl.
  exists None.
  apply fs_op.
  apply Permutation_trans with o; assumption.
  }
  destruct exo as (O',OPO').

  assert (bp3u: boundph (upd (location_eq_dec Z.eq_dec) p3 (evall v) None)).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (phpdefp3up1': phplusdef (upd (location_eq_dec Z.eq_dec) p3 (evall v) None) p1).
  {
  apply phpdef_none; repeat php_.
  }

  assert (bp3p1: boundph (phplus p3 p1)).
  {
  apply boundph_mon with p4; repeat php_.
  replace (phplus (phplus p3 p1) p4) with (phplus p1 (phplus p3 p4)); repeat php_.
  rewrite phplus_comm; repeat php_.
  }

  assert (bp3up1: boundph (phplus (upd (location_eq_dec Z.eq_dec) p3 (evall v) None) p1)).
  {
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1',(v2',(CO,rest))).
  inversion CO.
  }

  assert (bp1p3u: boundph (phplus p1 (upd (location_eq_dec Z.eq_dec)
    (upd (location_eq_dec Z.eq_dec) p3 (evall v) None)
    (Aof (evall v), Rof (evall v), Aof (evall v0), Xof (evall v),
    Pof (evall v), Iof (evall v), v1, map evalol v2) (Some Icond)))).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1',(v2',(CO,rest))).
  inversion CO.
  }

  assert (bup1p3p4: boundph (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p4)) (evall v) None)).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bp4p1p3u: boundph (phplus p4 (phplus p1 (upd (location_eq_dec Z.eq_dec)
    (upd (location_eq_dec Z.eq_dec) p3 (evall v) None)
    (Aof (evall v), Rof (evall v), Aof (evall v0), Xof (evall v),
    Pof (evall v), Iof (evall v), v1, map evalol v2) (Some Icond))))).
  {
  rewrite <- EQH.
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (buup3: boundph (upd (location_eq_dec Z.eq_dec)
    (upd (location_eq_dec Z.eq_dec) p3 (evall v) None)
    (Aof (evall v), Rof (evall v), Aof (evall v0), Xof (evall v),
    Pof (evall v), Iof (evall v), v1, map evalol v2) (Some Icond))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  apply tmp5 with O'; repeat php_.
  replace (ghplus C4 (ghplus c1 C3)) with (ghplus c1 (ghplus C3 C4)); repeat php_.
  exists p1, (upd (location_eq_dec Z.eq_dec)
       (upd (location_eq_dec Z.eq_dec) p3 (evall v) None)
       (Aof (evall v), Rof (evall v), Aof (evall v0), Xof (evall v),
       Pof (evall v), Iof (evall v), v1, map evalol v2) (Some Icond)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, O'.
  exists c1, C3.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  destruct O'.
  apply sn_op.
  apply Permutation_refl.
  apply None_op.
  split. repeat php_.
  split.
  unfold upd.
  simpl.
  destruct (location_eq_dec Z.eq_dec
    (evall (Aof v, Rof v, Aof v0, Xof v, Pof v, Iof v, v1, v2))
    (Aof (evall v), Rof (evall v), Aof (evall v0), Xof (evall v),
    Pof (evall v), Iof (evall v), v1, map evalol v2)).
  reflexivity.
  contradiction.
  split; reflexivity.
Qed.


Lemma sat_g_finlc:
  forall m p O C tx invs sp
        (SAT: sat p O C (EX v, (EX l, (EX e, ((Abool (andb (Z.eqb ([[e]]) ([[Aof v]])) (Z.eqb ([[Lof v]]) ([[Aof l]]))) &*
        Aprop (spurious_ok sp (evall l) (evall v) invs)) &* Alock l ** Aicond v ** (Alock l ** Acond v --*
       (weakest_pre_tx (S m) sp tx invs 0))))))),
    exists lv lk e
           (EQl: Aof lv = ([[e]]))
           (EQl: Lof lv = Aof lk)
           (Pl: p lv = Some Icond)
           (Plk: p lk = Some Lock \/ exists wt ot, p lk = Some (Locked wt ot))
           (SPUR: spurious_ok sp lk lv invs),
    sat (upd (location_eq_dec Z.eq_dec) p lv (Some Cond)) O C (weakest_pre_ct (S m) sp (tt, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(v5,((eql,SPUR),(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4)))))))))))))))))).
  apply Coq.Bool.Bool.andb_true_iff in eql.
  destruct eql as (EQ1,EQ2).
  unfold id in *.
  apply Z.eqb_eq in EQ1.
  apply Z.eqb_eq in EQ2.
  subst.  
  exists (evall v), (evall v0), v5.
  exists.
  rewrite EQ1.
  reflexivity.
  exists.
  unfold evall.
  unfold evalol.
  unfold Lof in *.
  unfold Lofo in *.
  unfold Oof in *.
  rewrite EQ2.
  reflexivity.
  exists.
  apply phplus_Icond'; repeat php_.
  apply phplus_Icond; repeat php_.
  exists.
  apply phplus_lock; repeat php_.
  exists SPUR.

  assert (phpp13p14: phplusdef p1 p3 /\ phplusdef p1 p4).
  {
  repeat php_.
  }

  assert (gphpp13p14: ghplusdef c1 C3 /\ ghplusdef c1 C4).
  {
  repeat php_.
  }


  assert (eqh: phplus p1 (phplus p3 p4) = phplus p3 (phplus p4 p1)).
  {
  rewrite phplus_comm; repeat php_.
  }

  assert (p4v: p4 (evall v) = None).
  {
  unfold phplusdef in phpdefp3p4.
  specialize phpdefp3p4 with (evall v).
  rewrite tmp4 in phpdefp3p4.
  destruct (p4 (evall v)).
  contradiction.
  reflexivity.
  }

  assert (p1v: p1 (evall v) = None).
  {
  destruct phpp13p14 as (phpp13,phpp14).
  unfold phplusdef in phpp13.
  specialize phpp13 with (evall v).
  rewrite tmp4 in phpp13.
  destruct (p1 (evall v)).
  destruct k;
  contradiction.
  reflexivity.
  }

  assert (phpp4up3: phplusdef p4 (upd (location_eq_dec Z.eq_dec) p3 (evall v) (Some Cond))).
  {
  apply phpdef_comm; repeat php_.
  apply phpdef_v; repeat php_.
  }

  assert (phpdefp1up3: phplusdef p1 (upd (location_eq_dec Z.eq_dec) p3 (evall v) (Some Cond))).
  {
  apply phpdef_comm; repeat php_.
  apply phpdef_v; repeat php_.
  }

  assert (EQH: upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p4)) (evall v)
     (Some Cond) = phplus p4 (phplus p1 (upd (location_eq_dec Z.eq_dec) p3 (evall v) (Some Cond)))).
  {
  rewrite eqh.
  rewrite <- phplus_upd; repeat php_.
  rewrite phplus_comm; repeat php_.
  unfold not.
  intros.
  destruct H as (v',(f',(v'',(f'',(CO,rest))))).
  inversion CO.
  intros CO.
  inversion CO.
  intros CO.
  inversion CO.
}

  rewrite EQH.
  assert (EQC: ghplus c1 (ghplus C3 C4) = ghplus C4 (ghplus c1 C3)).
  {
  rewrite <- ghplus_assoc; repeat php_.
  }
  rewrite EQC.
  assert (exo': exists O', oplus O4 O' O).
  {
  inversion opo1o2.
  rewrite <- H0 in opO3O4.
  inversion opO3O4.
  exists None.
  apply None_op.
  rewrite <- H0 in opO3O4.
  inversion opO3O4.
  exists (Some o').
  apply sn_op.
  apply Permutation_refl.
  rewrite <- H0 in opO3O4.
  inversion opO3O4.
  exists (Some o').
  apply sn_op.
  apply Permutation_refl.
  exists None.
  apply fs_op.
  apply Permutation_trans with o; assumption.
  }
  destruct exo' as (O',op').

  assert (eqh': phplus p1 (phplus p3 p4) = phplus (phplus p3 p1) p4).
  {
  rewrite phplus_comm; repeat php_.
  }

  assert (bp31: boundph (phplus p3 p1)).
  {
  apply boundph_mon with p4; repeat php_.
  rewrite <- eqh'.
  assumption.
  }

  assert (bp1p3: boundph (phplus p1 (upd (location_eq_dec Z.eq_dec) p3 (evall v) (Some Cond)))).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1,(v2,(CO,rest))).
  inversion CO.
  }

  assert (bp41: boundph (phplus p4 p1)).
  {
  apply boundph_mon with p3; repeat php_.
  rewrite phplus_comm; repeat php_.
  rewrite <- eqh.
  assumption.
  }

  assert (bp4p1p3: boundph (phplus p4 (phplus p1 (upd (location_eq_dec Z.eq_dec) p3 (evall v) (Some Cond))))).
  {
  rewrite <- phplus_assoc; repeat php_.
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  rewrite <- eqh.
  assumption.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v1,(v2,(CO,rest))).
  inversion CO.
  }

  assert (bg4g13: boundgh (ghplus C4 (ghplus c1 C3))).
  {
  rewrite <- EQC.
  assumption.
  }

  apply tmp5 with O'; repeat php_.
  exists p1, (upd (location_eq_dec Z.eq_dec) p3 (evall v) (Some Cond)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  exists. repeat php_.
  exists O', None, c1, C3.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  destruct O'.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  exists. repeat php_.
  exists.
  unfold upd.
  destruct (location_eq_dec Z.eq_dec (evall v) (evall v)).
  reflexivity.
  contradiction.
  split; reflexivity.
Qed.

Lemma sat_wait:
  forall m p O C ev el tx invs sp
         (SAT: sat p (Some O) C (weakest_pre_ct (S m) sp (Wait ev el, tx) invs)),
    exists v l p1 p2 wt ot C1 C2 O1
           (EQl: Aof l = ([[el]]))
           (EQv: Aof v = ([[ev]]))
           (OO1: Permutation O (Oof l :: O1))
           (BP1: boundph p1)
           (BP2: boundph p2)
           (phpdp1p2: phplusdef p1 p2)
           (p1p2: p = phplus p1 p2)
           (ghpdefc1c2: ghplusdef C1 C2)
           (C1C2: C = ghplus C1 C2) 
           (p1l: p1 l = Some (Locked wt ot))
           (p1v: p1 v = Some Cond)
           (p2inv: sat p2 None C2 (subsas (snd (Iof l)) (invs (fst (Iof l)) (upd Z.eq_dec wt (Aof v) (S (wt (Aof v)))) ot)))
           (PRCv: prcl (Oof v) O1)
           (PRCl: prcl (Oof l) (M'of v ++ O1))
           (NEQlv: v <> l)
           (Lvl: Lof v = Aof l)
           (SAFE_OBS: safe_obs v (S (wt (Aof v))) (ot (Aof v)) = true),
      sat (upd (location_eq_dec Z.eq_dec) p1 l (Some Lock)) (Some O1) C1
        (weakest_pre_ct (S m) sp (Waiting4cond ev el, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(sat1,(sat2,(p1p2,C1C2))))))))))))))))))))).
  destruct sat1 as (v2,(v3,(EQ,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(SAT,(tmp1,(p3p4,C3C4))))))))))))))))))))).
  destruct tmp1 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(ops56,(tmp1,(p56,C56)))))))))))))))))).
  destruct tmp1 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(ops78,(tmp1,(p78,C78)))))))))))))))))).
  assert (EQ1:=EQ).
  destruct EQ as (EQ,(prcv1,prcv0)).
  apply Coq.Bool.Bool.andb_true_iff in EQ.
  destruct EQ as (eqev,EQ).
  apply Coq.Bool.Bool.andb_true_iff in EQ.
  destruct EQ as (eqel,EQ).
  apply Coq.Bool.Bool.andb_true_iff in EQ.
  destruct EQ as (lov1,safe1).
  unfold id in *.

  assert (eqO: Permutation O (evalol (Oof v0) :: map evalol v) /\ O3 = None /\ o2 = None).
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

  assert (bp8u: boundph (upd (location_eq_dec Z.eq_dec) p8 (evall v0) (Some Lock))).
  {
  apply boundph_upd;
  try tauto.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  exists (evall v1), (evall v0).
  exists (phplus p2 p4), p3, v2, v3, (ghplus C2 C4), C3, (map evalol v).
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
  exists prcv1.
  exists.
  rewrite map_app in prcv0.
  replace (Oof (evall v0)) with (evalol (Oof v0)).
  assumption.
  reflexivity.
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
  unfold Lof in *.
  unfold Aof in *.
  unfold Oof in *.
  simpl in *.
  unfold Lofo in *.
  unfold Aofo in *.
  simpl.
  unfold Lofo in *.
  unfold Aofo in *.
  simpl in *.
  rewrite <- lov1.
  reflexivity.
  exists safe1.
  exists v, v0, v1.
  exists.
  split.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  assumption.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  assumption.
  assumption.
  split; assumption.
  exists (upd (location_eq_dec Z.eq_dec) p4 (evall v0) (Some Lock)), p2.
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
  exists (Some (map evalol v)), None.
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
  {
  exists (phplus p5 p7), (upd (location_eq_dec Z.eq_dec) p8 (evall v0) (Some Lock)).
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
  exists None, (Some (map evalol v)).
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
  exists (upd (location_eq_dec Z.eq_dec) p8 (evall v0) (Some Lock)), (emp knowledge).
  exists.
  apply phpdef_emp.
  exists bp8u.
  exists boundph_emp.
  exists.
  rewrite phplus_emp.
  tauto.
  exists None, (Some (map evalol v)).
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
  destruct ((location_eq_dec Z.eq_dec) (evall v0) (evall v0)).
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
  }
  split.
  {
  intros.
  apply sat2 with v4 v5 O'; repeat php_.
  }
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

Lemma sat_wait4cond:
  forall m p O C ev el tx invs sp
        (SAT: sat p (Some O) C (weakest_pre_ct (S m) sp (Waiting4cond ev el, tx) invs)),
  exists l v
         (EQl: Aof l = ([[el]]))
         (EQv: Aof v = ([[ev]]))
         (Pv: p v = Some Cond)
         (Pl: p l = Some Lock \/ exists wt ot, p l = Some (Locked wt ot))
         (lvl: Lof v = ([[el]]))
         (PRCl: prcl (Oof l) (M'of v ++ O))
         (PRCv: prcl (Oof v) O),
    forall pm Cm (PHPDEF: phplusdef p pm) (BPm: boundph pm) (BPmp: boundph (phplus pm p)) (GHPDEF: ghplusdef C Cm) (BCm: boundgh Cm) (BCmC: boundgh (ghplus Cm C))
           (SATM: sat pm None Cm (subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb))),
      sat (phplus p pm) (Some (M'of v ++ O)) (ghplus C Cm) (weakest_pre_ct (S m) sp (Waiting4lock el, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(sat1,(sat2,(p1p2,C1C2)))))))))))))))))))))).
  destruct sat1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(p3v1,(tmp1,(p3p4,C3C4)))))))))))))))))).
  destruct tmp1 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp6,(tmp7, (p5p6,C5C6)))))))))))))))))).

  assert (PERM: Permutation O (map evalol v) /\ o2 = None).
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

  destruct EQ as (EQ1,EQ4).
  apply Coq.Bool.Bool.andb_true_iff in EQ1.
  destruct EQ1 as (EQ1,EQ2).
  apply Coq.Bool.Bool.andb_true_iff in EQ2.
  destruct EQ2 as (EQ2,EQ3).
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
  apply prcl_perm with (map evalol (M'of v1 ++ v)).
  assumption.
  rewrite map_app.
  simpl.
  apply Permutation_app_head.
  assumption.
  exists.
  apply prcl_perm with (map evalol v).
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
  subst.

  assert (phpd1: phplusdef (phplus p3 (phplus p5 p6)) p2 /\ phplusdef (phplus p3 (phplus p5 p6)) pm). apply phpdef_dist'; repeat php_.
  destruct phpd1 as (phpd3562,phpd356m).
  assert (phpd1: phplusdef p3 pm /\ phplusdef (phplus p5 p6) pm). apply phpdef_dist; repeat php_.
  destruct phpd1 as (phpd3m,phpd56m).
  assert (phpd1: phplusdef p5 pm /\ phplusdef p6 pm). apply phpdef_dist; repeat php_.
  destruct phpd1 as (phpd5m,phpd6m).
  assert (phpd1: phplusdef p3 p2 /\ phplusdef (phplus p5 p6) p2). apply phpdef_dist; repeat php_.
  destruct phpd1 as (phpd32,phpd562).
  assert (phpd1: phplusdef p5 p2 /\ phplusdef p6 p2). apply phpdef_dist; repeat php_.
  destruct phpd1 as (phpd52,phpd62).

  assert (phpd1: ghplusdef (ghplus C3 (ghplus C5 C6)) C2 /\ ghplusdef (ghplus C3 (ghplus C5 C6)) Cm). apply ghpdef_dist'; repeat php_.
  destruct phpd1 as (ghpd3562,ghpd356m).
  assert (phpd1: ghplusdef C3 Cm /\ ghplusdef (ghplus C5 C6) Cm). apply ghpdef_dist; repeat php_.
  destruct phpd1 as (ghpd3m,ghpd56m).
  assert (phpd1: ghplusdef C5 Cm /\ ghplusdef C6 Cm). apply ghpdef_dist; repeat php_.
  destruct phpd1 as (ghpd5m,ghpd6m).
  assert (phpd1: ghplusdef C3 C2 /\ ghplusdef (ghplus C5 C6) C2). apply ghpdef_dist; repeat php_.
  destruct phpd1 as (ghpd32,ghpd562).
  assert (phpd1: ghplusdef C5 C2 /\ ghplusdef C6 C2). apply ghpdef_dist; repeat php_.
  destruct phpd1 as (ghpd52,ghpd62).

  assert (eqh1: phplus (phplus p3 (phplus p2 pm)) (phplus p5 p6) = 
    phplus (phplus p3 (phplus p5 p6)) (phplus p2 pm)).
  {
  repeat php_. rewrite <- phplus_assoc.
  symmetry.
  rewrite <- phplus_assoc. repeat php_.
  repeat php_. repeat php_. repeat php_. repeat php_. repeat php_. repeat php_.
  }

  assert (eqg1: ghplus (ghplus C3 (ghplus C2 Cm)) (ghplus C5 C6) = 
    ghplus (ghplus C3 (ghplus C5 C6)) (ghplus C2 Cm)).
  {
  repeat php_. rewrite <- ghplus_assoc.
  symmetry.
  rewrite <- ghplus_assoc. repeat php_.
  repeat php_. repeat php_. repeat php_. repeat php_. repeat php_. repeat php_.
  }

  assert (bp32m : boundph (phplus p3 (phplus p2 pm))).
  {
  apply boundph_mon with (phplus p5 p6); repeat php_. rewrite eqh1. assumption.
  }

  assert (b5632m: boundph (phplus (phplus p5 p6) (phplus p3 (phplus p2 pm)))).
  {
  rewrite phplus_comm; repeat php_. rewrite eqh1. assumption.
  }

  assert (bg32m : boundgh (ghplus C3 (ghplus C2 Cm))).
  {
  apply boundgh_mon with (ghplus C5 C6); repeat php_. rewrite eqg1. assumption.
  }

  assert (bg5632m: boundgh (ghplus (ghplus C5 C6) (ghplus C3 (ghplus C2 Cm)))).
  {
  rewrite ghplus_comm; repeat php_. rewrite eqg1. assumption.
  }

  exists (M'of v1 ++ v), v0.
  exists (phplus p5 p6), (phplus p3 (phplus p2 pm)).
  exists. repeat php_.
  exists. repeat php_.
  exists. assumption.
  exists. assumption.
  exists (Some (M'of (evall v1) ++ O)), None.
  exists (ghplus C5 C6), (ghplus C3 (ghplus C2 Cm)).
  exists. repeat php_.
  exists. repeat php_.
  exists. assumption.
  exists. assumption.
  exists. apply fs_op. apply Permutation_refl.
  exists.
  split. split.
  apply Z.eqb_eq. assumption. assumption.
  exists p5, p6.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists None, (Some (map evalol (M'of v1 ++ v))).
  exists C5, C6.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. apply sn_op.
  apply perm_trans with (M'of (evall v1) ++ (map evalol v)).
  rewrite map_app. apply Permutation_refl.
  apply Permutation_app_head. apply Permutation_sym. assumption.
  split. assumption. split. apply fs_op. apply Permutation_refl. split; reflexivity.
  split.
  intros.

  assert (phpd1: phplusdef p3 p' /\ phplusdef (phplus p2 pm) p'). apply phpdef_dist; repeat php_.
  destruct phpd1 as (phpd3p',phpd2mp').
  assert (phpd1: phplusdef p2 p' /\ phplusdef pm p'). apply phpdef_dist; repeat php_.
  destruct phpd1 as (phpd2p',phpdmp').

  assert (phpd1: ghplusdef C3 g' /\ ghplusdef (ghplus C2 Cm) g'). apply ghpdef_dist; repeat php_.
  destruct phpd1 as (ghpd3p',ghpd2mp').
  assert (phpd1: ghplusdef C2 g' /\ ghplusdef Cm g'). apply ghpdef_dist; repeat php_.
  destruct phpd1 as (ghpd2p',ghpdmp').

  assert (EQH1: phplus (phplus p3 (phplus p2 pm)) p' = phplus p2 (phplus p3 (phplus pm p'))).
  {
  symmetry. rewrite phplus_comm; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  }

  assert (EQG1: ghplus (ghplus C3 (ghplus C2 Cm)) g' = ghplus C2 (ghplus C3 (ghplus Cm g'))).
  {
  symmetry. rewrite ghplus_comm; repeat php_.
  rewrite <- ghplus_assoc; repeat php_.
  }

  rewrite EQH1.
  rewrite EQG1.

  assert (eqh2: phplus (phplus p2 p3) pm = phplus p3 (phplus p2 pm)).
  {
  rewrite phplus_comm; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  }

  assert (eqh3: phplus (phplus pm p') (phplus p2 p3) = 
    phplus p2 (phplus p3 (phplus pm p'))).
  {
  symmetry.
  rewrite <- phplus_assoc; repeat php_.
  }

  assert (eqg2: ghplus (ghplus C2 C3) Cm = ghplus C3 (ghplus C2 Cm)).
  {
  rewrite ghplus_comm; repeat php_.
  rewrite <- ghplus_assoc; repeat php_.
  }

  assert (eqg3: ghplus (ghplus Cm g') (ghplus C2 C3) = 
    ghplus C2 (ghplus C3 (ghplus Cm g'))).
  {
  symmetry.
  rewrite <- ghplus_assoc; repeat php_.
  }

  assert (bp23m': boundph (phplus p2 (phplus p3 (phplus pm p')))).
  rewrite <- EQH1. assumption.

  assert (bp23m: boundph (phplus p3 (phplus p2 pm))).
  apply boundph_mon with p'; try assumption.

  assert (bp23: boundph (phplus p2 p3)).
  {
  apply boundph_mon with pm; try assumption.
  rewrite eqh2. assumption.
  }

  assert (bpm': boundph (phplus pm p')).
  {
  apply boundph_mon with (phplus p2 p3); try assumption.
  rewrite eqh3. assumption.
  }

  assert (bp3m': boundph (phplus p3 (phplus pm p'))).
  apply boundph_mon with p2; repeat php_.

  assert (bg23m': boundgh (ghplus C2 (ghplus C3 (ghplus Cm g')))).
  rewrite <- EQG1. assumption.

  assert (bg23m: boundgh (ghplus C3 (ghplus C2 Cm))).
  apply boundgh_mon with g'; try assumption.

  assert (bg23: boundgh (ghplus C2 C3)).
  {
  apply boundgh_mon with Cm; try assumption.
  rewrite eqg2. assumption.
  }

  assert (bgm': boundgh (ghplus Cm g')).
  {
  apply boundgh_mon with (ghplus C2 C3); try assumption.
  rewrite eqg3. assumption.
  }

  assert (bg3m': boundgh (ghplus C3 (ghplus Cm g'))).
  {
  apply boundgh_mon with C2; repeat php_.
  }

  apply sat2 with v2 v3 O'; repeat php_.

  assert (eqh4: phplus p' (phplus p3 pm) = phplus p3 (phplus pm p')).
  {
  rewrite phplus_comm; try assumption.
  symmetry.
  rewrite phplus_assoc; try assumption. reflexivity.
  repeat php_.
  }

  assert (eqg4: ghplus g' (ghplus C3 Cm) = ghplus C3 (ghplus Cm g')).
  {
  rewrite ghplus_comm; try assumption.
  symmetry.
  rewrite ghplus_assoc; try assumption. reflexivity.
  repeat php_.
  }

  destruct SAT as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(o7,(o8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(BC7C8,(opo7o8,(tmp10,(tmp8,(p7p8,C7C8)))))))))))))))))).
  destruct tmp8 as (p9,(p0,(phpdefp9p0,(bp9,(bp0,(bp90,(o9,(o0,(C9,(C0,(ghpdefC9C0,(BC9,(BC0,(BC9C0,(opo9o0,(tmp110,(tmp18,(p9p0,C9C0)))))))))))))))))).

  exists (emp knowledge), (phplus p' (phplus p3 pm)).
  exists. repeat php_.
  exists. repeat php_.
  exists. rewrite eqh4. assumption.
  exists. repeat php_. rewrite eqh4. assumption.
  exists (Some (evalol (Oof v0) :: map evalol (M'of v1 ++ v))), None.
  exists (emp (option nat * nat)), (ghplus g' (ghplus C3 Cm)).
  exists. repeat php_.
  exists. repeat php_.
  exists. rewrite eqg4. assumption.
  exists. repeat php_. rewrite eqg4. assumption.
  exists.
  inversion tmp10.
  rewrite <- H1 in opo7o8.
  inversion opo7o8.
  apply fs_op.
  apply Permutation_trans with o'; try assumption.
  split. apply fs_op. apply Permutation_refl.
  split.
  exists p3, (phplus p' pm) .
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. replace (phplus p' pm) with (phplus pm p'). assumption. repeat php_.
  exists None, None.
  exists C3, (ghplus g' Cm) .
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. replace (ghplus g' Cm) with (ghplus Cm g'). assumption. repeat php_.
  exists. apply None_op.
  split. assumption.
  split.
  subst.
  assert (phpd1: phplusdef p2 (phplus p7 (phplus p9 p0)) /\ phplusdef pm ((phplus p7 (phplus p9 p0)))). apply phpdef_dist; repeat php_.
  destruct phpd1 as (phpd2790,phpdm790).
  assert (phpd1: phplusdef p2 p7 /\ phplusdef p2 (phplus p9 p0)). apply phpdef_dist'; repeat php_.
  destruct phpd1 as (phpd27,phpdm290).
  assert (phpd1: phplusdef p2 p9 /\ phplusdef p2 p0). apply phpdef_dist'; repeat php_.
  destruct phpd1 as (phpd29,phpdm20).
  assert (phpd1: phplusdef pm p7 /\ phplusdef pm (phplus p9 p0)). apply phpdef_dist'; repeat php_.
  destruct phpd1 as (phpdm7,phpdm90).
  assert (phpd1: phplusdef pm p9 /\ phplusdef pm p0). apply phpdef_dist'; repeat php_.
  destruct phpd1 as (phpdm9,phpdm0).
  assert (phpd1: phplusdef p7 p9 /\ phplusdef p7 p0). apply phpdef_dist'; repeat php_.
  destruct phpd1 as (phpd79,phpd70).

  assert (phpd1: ghplusdef C2 (ghplus C7 (ghplus C9 C0)) /\ ghplusdef Cm ((ghplus C7 (ghplus C9 C0)))). apply ghpdef_dist; repeat php_.
  destruct phpd1 as (ghpd2790,ghpdm790).
  assert (phpd1: ghplusdef C2 C7 /\ ghplusdef C2 (ghplus C9 C0)). apply ghpdef_dist'; repeat php_.
  destruct phpd1 as (ghpd27,ghpdm290).
  assert (phpd1: ghplusdef C2 C9 /\ ghplusdef C2 C0). apply ghpdef_dist'; repeat php_.
  destruct phpd1 as (ghpd29,ghpdm20).
  assert (phpd1: ghplusdef Cm C7 /\ ghplusdef Cm (ghplus C9 C0)). apply ghpdef_dist'; repeat php_.
  destruct phpd1 as (ghpdm7,ghpdm90).
  assert (phpd1: ghplusdef Cm C9 /\ ghplusdef Cm C0). apply ghpdef_dist'; repeat php_.
  destruct phpd1 as (ghpdm9,ghpdm0).
  assert (phpd1: ghplusdef C7 C9 /\ ghplusdef C7 C0). apply ghpdef_dist'; repeat php_.
  destruct phpd1 as (ghpd79,ghpd70).

  assert (bp790: boundph (phplus p7 (phplus p9 p0))).
  {
  apply boundph_mon with pm; repeat php_.
  }

  assert (bp79: boundph (phplus p7 p9)).
  {
  apply boundph_mon with p0; repeat php_.
  }

  assert (bp90m: boundph (phplus (phplus p9 p0) pm)).
  {
  rewrite phplus_comm in bpm'; repeat php_.
  rewrite phplus_assoc in bpm'; repeat php_.
  }
  assert (bp0m: boundph (phplus p0 pm)).
  {
  repeat php_. rewrite phplus_comm; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  }

  assert (bg790: boundgh (ghplus C7 (ghplus C9 C0))).
  {
  apply boundgh_mon with Cm; repeat php_.
  }

  assert (bg79: boundgh (ghplus C7 C9)).
  {
  apply boundgh_mon with C0; repeat php_.
  }

  assert (bg90m: boundgh (ghplus (ghplus C9 C0) Cm)).
  {
  rewrite ghplus_comm in bgm'; repeat php_.
  rewrite ghplus_assoc in bgm'; repeat php_.
  }
  assert (bg0m: boundgh (ghplus C0 Cm)).
  {
  repeat php_. rewrite ghplus_comm; repeat php_.
  rewrite <- ghplus_assoc; repeat php_.
  }

  assert (eqh5: phplus (phplus p9 p7) (phplus p0 pm) =
    phplus pm (phplus p7 (phplus p9 p0))).
  {
  rewrite phplus_comm; try assumption.
  replace (phplus p0 pm) with (phplus pm p0).
  repeat php_. rewrite <- phplus_assoc; repeat php_. repeat php_. repeat php_.
  }

  assert (eqg5: ghplus (ghplus C9 C7) (ghplus C0 Cm) =
    ghplus Cm (ghplus C7 (ghplus C9 C0))).
  {
  rewrite ghplus_comm; try assumption.
  replace (ghplus C0 Cm) with (ghplus Cm C0).
  repeat php_. rewrite <- ghplus_assoc; repeat php_. repeat php_. repeat php_.
  }

  exists (phplus p9 p7), (phplus p0 pm).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. rewrite eqh5. assumption.
  exists None, None.
  exists (ghplus C9 C7), (ghplus C0 Cm).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. rewrite eqg5. assumption.
  exists. apply None_op.
  split.
  apply phplus_locked; repeat php_.
  split.
  exists p0, pm.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, None.
  exists C0, Cm.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply None_op.
  split.
  inversion tmp10.
  rewrite <- H1 in opo7o8.
  inversion opo7o8.
  rewrite <- H3 in opo9o0.
  inversion opo9o0. rewrite H5. assumption.
  split. assumption. split; reflexivity.
  split. rewrite eqh5. repeat php_. rewrite eqg5. repeat php_.
  split. rewrite phplus_comm; repeat php_.
  rewrite ghplus_comm; repeat php_.
  split; repeat php_. 
  split. rewrite phplus_comm; try assumption. rewrite eqh1. repeat php_. repeat php_.
  rewrite ghplus_comm; try assumption. rewrite eqg1. repeat php_. repeat php_.
Qed.

Lemma sat_notify:
forall m p O C v tx invs sp
      (SAT: sat p (Some O) C (weakest_pre_ct (S m) sp (Notify v, tx) invs)),
  exists p1 pm C1 Cm wt ot lv ll O'
         (PERM: Permutation ((if ltb 0 (wt (Aof lv)) then (M'of lv) else nil) ++ O') O)
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
         (SATm: lt 0 (wt ([[v]])) -> sat pm None Cm (subsas (snd (Mof lv)) (invs (fst (Mof lv)) empb empb)))
         (SATn: le (wt ([[v]])) 0 -> pm = emp knowledge /\ Cm = emp (option nat * nat)),
    sat (upd (location_eq_dec Z.eq_dec) p1 ll (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) (Some O') C1 (weakest_pre_tx (S m) sp tx invs 0).
Proof.
  simpl.
  intros.
  destruct SAT as (v0,(v1,(v2,(v3,(v4,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(satp1v3,(sat1,(p1p2,C1C2)))))))))))))))))))))))).
  destruct sat1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(p3v2,(tmp1,(p3p4,C3C4)))))))))))))))))).
  destruct tmp1 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp6,(tmp7, (p5p6,C5C6)))))))))))))))))).
  destruct tmp7 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(tmp7,(tmp8, (p7p8,C7C8)))))))))))))))))).

  subst.


  assert (o1n: Permutation
  ((if (0 <? v1 (Aof (evall v4)))%nat then M'of (evall v4) else nil) ++  map evalol v0) O
   /\ o1 = None /\ O8 = None).
  {
  replace (Aof (evall v4)) with ([[Aof v4]]).
  destruct (0 <? v1 ([[Aof v4]]))%nat.
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
  rewrite map_app in PERM.
  replace (M'of (evall v4)) with (map evalol (M'of v4)).
  assumption.
  reflexivity.
  apply Permutation_trans with o'0.
  assumption.
  apply Permutation_trans with o'1.
  assumption.
  apply Permutation_trans with o'2.
  assumption.
  assumption.
  split;
  reflexivity.
  rewrite app_nil_l in *.
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

  assert (eqh: phplus p3 (phplus p5 (phplus p7 p8)) = phplus p5 (phplus p7 (phplus p8 p3))).
  {
  rewrite phplus_comm; repeat php_.
  }

  assert (phpdefup5p6: phplusdef
    (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p7).
  {
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  assumption.
  }

  assert (phpdefup7p8: phplusdef
    (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p8).
  {
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  assumption.
  }

  assert (phpdefup5p3: phplusdef
    (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p3).
  {
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  assumption.
  }

  assert (phpdefp8up5: phplusdef p8
    (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2)))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  assumption.
  }

  assert (phpdefp3up5: phplusdef p3
    (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2)))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  assumption.
  }

  assert (phpdefp8up57: phplusdef p8
    (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p7)).
  {
  apply phpdef_pair; repeat php_.
  }

  assert (phpdefp3up5p7: phplusdef p3 (phplus
    (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p7)).
  {
  apply phpdef_pair; repeat php_.
  }

  assert (EQH: upd (location_eq_dec Z.eq_dec) (phplus p3 (phplus p5 (phplus p7 p8))) (evall v3)
   (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2)) =
   phplus p8 (phplus p3 (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
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

  assert (bp3up57: boundph (phplus p3 (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
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
    (upd (location_eq_dec Z.eq_dec) p5 (evall v3) (Some
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

  assert (bup52: boundph (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2)))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bup57: boundph (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
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

  destruct (leb (v1 ([[Aof v4]])) 0) eqn:M1.
  {
  exists (phplus p1 (phplus p3 (phplus p5 (phplus p7 p8)))), (emp knowledge).
  exists (ghplus C1 (ghplus C3 (ghplus C5 (ghplus C7 C8)))), (emp (option nat * nat)).
  exists v1, v2.
  exists (evall v4), (evall v3).
  exists (map evalol v0).
  exists. assumption.
  exists. assumption.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. symmetry. assumption.
  exists. symmetry. assumption.
  exists.
  apply phplus_locked'; repeat php_.
  apply phplus_locked'; repeat php_.
  apply phplus_locked; repeat php_.
  exists.
  apply phplus_Cond'; repeat php_.
  apply phplus_Cond; repeat php_.
  exists. intros.
  apply Nat.leb_le in M1.
  rewrite EQ2 in *.
  omega.
  exists.
  intros.
  split; reflexivity.


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

  assert (phpdefup5p1: phplusdef (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p1).
  {
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  assumption.
  }

  assert (phpdefp8up5p17: phplusdef p8 (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) (phplus p1 p7))).
  {
  rewrite phplus_comm; repeat php_.
  }

  assert (phpdefp3up5p17: phplusdef p3 (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2)))(phplus p1 p7))).
  {
  rewrite phplus_comm; repeat php_.
  }

  assert (EQH1: upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 (phplus p5 (phplus p7 p8))))
    (evall v3) (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2)) =
    phplus p8 (phplus p3 (phplus (upd (location_eq_dec Z.eq_dec) p5
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
  destruct H as (v0',(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros.
  inversion H.
  intros.
  inversion H.
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

  assert (bp3up5p17: boundph (phplus p3 (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
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

  assert (bp8p3up5p17: boundph (phplus p8 (phplus p3 (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
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

  assert (bup517: boundph (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
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

  apply tmp8 with (Some (map evalol v0)); repeat php_.
  apply sn_op.
  apply Permutation_refl.
  exists p3, (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) (phplus p1 p7)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, (Some (map evalol v0)).
  exists C3, (ghplus C5 (ghplus C1 C7)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  apply sn_op.
  apply Permutation_refl.
  exists. repeat php_.
  split.
  {
  exists (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))).
  exists (phplus p1 p7).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, (Some (map evalol v0)).
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
  destruct ((location_eq_dec Z.eq_dec) (evall v3) (evall v3)).
  rewrite EQ2.
  reflexivity.
  contradiction.
  split.
  apply fs_op.
  apply Permutation_refl.
  split; reflexivity.
  }
  split; reflexivity.
  }

  destruct satp1v3 as [SATM|SATM].
  {
  exists (phplus p3 (phplus p5 (phplus p7 p8))), p1.
  exists (ghplus C3 (ghplus C5 (ghplus C7 C8))), C1.
  exists v1, v2.
  exists (evall v4), (evall v3).
  exists (map evalol v0).
  exists. assumption.
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
  exists. intros. assumption.

  split.
  {
  intros.
  apply nat_leb_falseL in M1.
  rewrite EQ2 in *.
  omega.
  }

  rewrite EQH.
  rewrite EQC.

  apply tmp8 with (Some (map evalol v0)); repeat php_.
  apply sn_op.
  apply Permutation_refl.
  exists p3, (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))) p7).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, (Some (map evalol v0)).
  exists C3, (ghplus C5 C7).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  apply sn_op.
  apply Permutation_refl.
  exists. repeat php_.
  split.
  {
  exists (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) (v1 ([[v]]) - 1)%nat) v2))), p7.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, (Some (map evalol v0)).
  exists C5, C7.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  apply sn_op.
  apply Permutation_refl.
  exists. repeat php_.
  unfold upd.
  destruct ((location_eq_dec Z.eq_dec) (evall v3) (evall v3)).
  rewrite EQ2.
  reflexivity.
  contradiction.
  split.
  apply fs_op.
  apply Permutation_refl.
  split; reflexivity.
  }
  split; reflexivity.
  }
  inversion SATM.
Qed.


Lemma sat_notifyAll:
forall m p O C v tx invs sp
      (SAT: sat p (Some O) C (weakest_pre_ct (S m) sp (NotifyAll v, tx) invs)),
  exists wt ot lv ll
         (M'nil: M'of lv = nil)
         (EQv: Aof lv = ([[v]]))
         (EQl: Aof ll = Lof lv)
         (P1l: p ll = Some (Locked wt ot)) 
         (P1l: p lv = Some Cond)
         (EMP: subsas (snd (Mof lv)) (invs (fst (Mof lv)) empb empb) = Abool true),
    sat (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked (upd Z.eq_dec wt ([[v]]) 0%nat) ot))) (Some O) C (weakest_pre_tx (S m) sp tx invs 0).
Proof.
  simpl.
  intros.
  destruct SAT as (v1,(v2,(v3,(v4,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2)))))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4)))))))))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp6,(tmp7, (p5p6,C5C6)))))))))))))))))).

  destruct tmp1 as (eqls,EQ1).
  apply Coq.Bool.Bool.andb_true_iff in eqls.
  destruct eqls as (EQ2,EQ3).
  apply Coq.Bool.Bool.andb_true_iff in EQ3.
  destruct EQ3 as (EQ3,EQ4).
  apply Z.eqb_eq in EQ2.
  apply Z.eqb_eq in EQ3.
  unfold id in *.
  subst.
  exists v1, v2, (evall v4), (evall v3).
  exists.
  unfold ifb in EQ4.
  destruct (list_eq_dec (olocation_eq_dec exp_eq_dec) (M'of v4) nil).
  replace (M'of (evall v4)) with (map evalol (M'of v4)).
  rewrite e.
  reflexivity.
  reflexivity.
  inversion EQ4.
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
    (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2)))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  apply phplus_locked'; repeat php_.
  apply phplus_locked'; repeat php_.
  }

  assert (EQH: upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 (phplus p5 p6)))
    (evall v3) (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2)) =
    phplus p6 (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5))
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

  assert (bupss: boundph (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
   (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2)))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert(bp8u: boundph (phplus p6
   (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
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
    (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2)))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  assumption.
  }

  assert (phpdefp3up5: phplusdef p3
    (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2)))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  exists v1, v2.
  assumption.
  }

  assert (phpdefp13up5: phplusdef (phplus p1 p3)
    (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
    (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2)))).
  {
  apply phpdef_pair'; repeat php_.
  }

  assert (bup5: boundph (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
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
    (upd (location_eq_dec Z.eq_dec) p5 (evall v3) (Some (Locked (upd Z.eq_dec v1 ([[v]]) 0%nat) v2))))).
  {
  rewrite phplus_comm; repeat php_.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v5,(v6,(CO,rest))).
  inversion CO.
  }

  exists (phplus p1 p3), (upd (location_eq_dec Z.eq_dec) p5 (evall v3)
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
  destruct ((location_eq_dec Z.eq_dec) (evall v3) (evall v3)).
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

Lemma sat_WasWaiting4cond:
  forall m sp p O C v l tx invs
        (SAT: sat p (Some O) C (weakest_pre_ct (S m) sp (WasWaiting4cond v l, tx) invs)),
  exists ll lv
         (EQL: Aof ll = ([[l]]))
         (EQV: Aof lv = ([[v]]))
         (Lofv: Lof lv = ([[l]]))
         (Pl: p ll = Some Lock \/ exists Wt Ot, p ll = Some (Locked Wt Ot))
         (Pv: p lv = Some Cond)
         (PRCl: prcl (Oof ll) O),
    forall p1 C1 wt ot 
          (SPUR: spurious_ok true ll lv invs)
          (bp: boundph p1)
          (bp1p: boundph (phplus p1 p))
          (bc: boundgh C1)
          (bc1c: boundgh (ghplus C1 C))
          (phpdefp1p: phplusdef p1 p)
          (ghpdefc1p: ghplusdef C1 C)
          (p1l: p1 ll = Some Lock \/ p1 ll = None)
          (pl: p ll = Some Lock \/ p ll = None)
          (LTWT: lt 0 (wt ([[v]])))
          (M'NIL: M'of lv = nil)
          (SAT1: sat p1 None C1 (subsas (snd (Iof ll)) (invs (fst (Iof ll)) wt ot))),
      sat (phplus (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) p1) (Some (Oof ll :: O)) (ghplus C C1) (weakest_pre_ct (S m) sp (tt, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v0,(v1,(v2,(EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opO1O2,(tmp1,tmp2)))))))))))))))))))).
  destruct tmp2 as (tmp2,(p1p2,c1c2)).
  destruct EQ as (EQ,EQ4).
  apply Coq.Bool.Bool.andb_true_iff in EQ.
  destruct EQ as (EQ0,EQ1).
  apply Coq.Bool.Bool.andb_true_iff in EQ1.
  destruct EQ1 as (EQ1,EQ2).
  apply Coq.Bool.Bool.andb_true_iff in EQ2.
  destruct EQ2 as (EQ2,EQ3).
  destruct EQ4 as (EQ4,EQ5).
  unfold id in *.

  apply Z.eqb_eq in EQ1.
  apply Z.eqb_eq in EQ2.
  apply Z.eqb_eq in EQ3.

  destruct tmp1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(p3v2,(tmp1,(p3p4,C3C4)))))))))))))))))).
  destruct tmp1 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp6,(tmp7, (p5p6,C5C6)))))))))))))))))).


  assert (PERM: Permutation O (map evalol v0) /\ O2 = None).
  {
  inversion tmp7.
  rewrite <- H1 in opO5O6.
  inversion opO5O6.
  rewrite <- H2 in opO3O4.
  inversion opO3O4.
  rewrite <- H5 in opO1O2.
  inversion opO1O2.
  split.
  apply Permutation_sym.
  apply Permutation_trans with o'; try assumption.
  apply Permutation_trans with o'0; try assumption.
  apply Permutation_trans with o'1; try assumption.
  reflexivity.
  }
  destruct PERM as (PERM,o2n).
  rewrite o2n in *.

  exists (evall v1), (evall v2).
  exists.
  rewrite EQ2.
  reflexivity.
  exists.
  rewrite EQ1.
  reflexivity.
  exists.
  rewrite EQ2.
  rewrite <- EQ3.
  reflexivity.
  exists.
  subst.
  apply phplus_lock.
  apply phplus_lock'; repeat php_.
  apply phplus_lock.
  assumption.
  exists.
  subst.
  apply phplus_Cond; repeat php_.
  apply phplus_Cond; repeat php_.
  exists.
  apply prcl_perm with (map evalol v0).
  apply prcl_mono with (map evalol (M'of v2)).
  rewrite <- map_app.
  assumption.
  assumption.
  intros.
  unfold weakest_pre_ct.
  simpl.
  subst.

  assert (phpd32p532: phplusdef p3 p2 /\ phplusdef (phplus p5 p6) p2). repeat php_.
  assert (phpd35p36: phplusdef p3 p5 /\ phplusdef p3 p6). repeat php_.
  assert (phpdp0p356p02: phplusdef p0 (phplus p3 (phplus p5 p6)) /\ phplusdef p0 p2). repeat php_.
  assert (phpdp52p62: phplusdef p5 p2 /\ phplusdef p6 p2). repeat php_.
  assert (phpdp03p056: phplusdef p0 p3 /\ phplusdef p0 (phplus p5 p6)). repeat php_.
  assert (phpdefp05p06: phplusdef p0 p5 /\ phplusdef p0 p6). repeat php_.

  assert (ghpd32p532: ghplusdef C3 C2 /\ ghplusdef (ghplus C5 C6) C2). repeat php_.
  assert (ghpd35p36: ghplusdef C3 C5 /\ ghplusdef C3 C6). repeat php_.
  assert (ghpdp0p356p02: ghplusdef C0 (ghplus C3 (ghplus C5 C6)) /\ ghplusdef C0 C2). repeat php_.
  assert (ghpdp52p62: ghplusdef C5 C2 /\ ghplusdef C6 C2). repeat php_.
  assert (ghpdp03p056: ghplusdef C0 C3 /\ ghplusdef C0 (ghplus C5 C6)). repeat php_.
  assert (ghpdefp05p06: ghplusdef C0 C5 /\ ghplusdef C0 C6). repeat php_.

  assert (EQH1: phplus (phplus p3 (phplus p5 p6)) p2 = phplus p5 (phplus p2 (phplus p3 p6))).
  {
  symmetry.
  rewrite phplus_comm; repeat php_.
  }

  assert (p2ln: p2 (evall v1) = Some Lock \/ p2 (evall v1) = None).
  apply phplus_lock_none' with (phplus p3 (phplus p5 p6)); repeat php_.

  assert (p356ln: phplus p3 (phplus p5 p6) (evall v1) = Some Lock \/ phplus p3 (phplus p5 p6) (evall v1) = None).
  apply phplus_lock_none with p2; repeat php_.

  assert (p3ln: p3 (evall v1) = Some Lock \/ p3 (evall v1) = None).
  apply phplus_lock_none with (phplus p5 p6); repeat php_.

  assert (p56ln: phplus p5 p6 (evall v1) = Some Lock \/ phplus p5 p6 (evall v1) = None).
  apply phplus_lock_none' with p3; repeat php_.

  assert (p5ln: p5 (evall v1) = Some Lock \/ p5 (evall v1) = None).
  apply phplus_lock_none with p6; repeat php_.

  assert (p6ln: p6 (evall v1) = Some Lock \/ p6 (evall v1) = None).
  apply phplus_lock_none' with p5; repeat php_.

  assert (phpdu0: phplusdef (upd (location_eq_dec Z.eq_dec) p5 (evall v1)
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) p0).
  apply phpdef_locked'; repeat php_.

  assert (phpdu2: phplusdef (upd (location_eq_dec Z.eq_dec) p5 (evall v1)
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) p2).
  apply phpdef_locked'; repeat php_.

  assert (phpdu3: phplusdef (upd (location_eq_dec Z.eq_dec) p5 (evall v1)
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) p3).
  apply phpdef_locked'; repeat php_.

  assert (phpdu4: phplusdef (upd (location_eq_dec Z.eq_dec) p5 (evall v1)
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) p6).
  apply phpdef_locked'; repeat php_.

  assert (EQH: phplus (upd (location_eq_dec Z.eq_dec) (phplus (phplus p3 (phplus p5 p6)) p2)
   (evall v1) (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) p0 =
   phplus p2 (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v1) (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot)))
   (phplus p0 (phplus p3 p6)))).
  {
  rewrite EQH1.
  rewrite <- phplus_upd.
  rewrite phplus_assoc; repeat php_.
  symmetry.
  rewrite phplus_comm; repeat php_.
  unfold not.
  intros.
  destruct H as (v',(f',(v'',(f'',(CO,rest))))).
  inversion CO.
  intros CO.
  inversion CO.
  intros CO.
  inversion CO.
  }
  rewrite EQH.

  assert (EQC: ghplus (ghplus (ghplus C3 (ghplus C5 C6)) C2) C0 = ghplus C2 (ghplus C5 (ghplus C0 (ghplus C3 C6)))).
  {
  rewrite ghplus_comm; repeat php_.
  rewrite <- ghplus_assoc; repeat php_.
  symmetry.
  rewrite ghplus_comm; repeat php_.
  }
  rewrite EQC.

  assert (bp0356: boundph (phplus p0 (phplus p3 (phplus p5 p6)))).
  {
  apply boundph_mon with p2; repeat php_.
  }

  assert (EQH2: phplus p5 (phplus p0 (phplus p3 p6)) = phplus p0 (phplus p3 (phplus p5 p6))).
  rewrite phplus_comm; repeat php_.

  assert (bp5p0p36: boundph (phplus p5 (phplus p0 (phplus p3 p6)))).
  rewrite EQH2. assumption.

  assert (b36: boundph (phplus p3 p6)).
  apply boundph_mon with p5; try assumption.
  rewrite phplus_assoc; repeat php_.
  replace (phplus p6 p5) with (phplus p5 p6); repeat php_.

  assert (bp0p36: boundph (phplus p0 (phplus p3 p6))).
  apply boundph_mon with p5; try assumption.
  rewrite phplus_comm; repeat php_.

  assert (bu5p036: boundph (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v1)
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) (phplus p0 (phplus p3 p6)))).
  {
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v2',(v3',(CO,rest))).
  inversion CO.
  }

  assert (bp2p5p036: boundph (phplus p2 (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v1)
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) (phplus p0 (phplus p3 p6))))).
  {
  rewrite <- EQH.
  apply boundph_phplus_upd; repeat php_.
  intros.
  inversion VCELL.
  intros.
  destruct CELL as (v2',(v3',(CO,rest))).
  inversion CO.
  }

  assert (bgc0c356: boundgh (ghplus C0 (ghplus C3 (ghplus C5 C6)))).
  apply boundgh_mon with C2; repeat php_.

  assert (EQC1: ghplus C5 (ghplus C0 (ghplus C3 C6)) = ghplus C0 (ghplus C3 (ghplus C5 C6))).
  rewrite ghplus_comm; repeat php_.

  assert (bg5036: boundgh (ghplus C5 (ghplus C0 (ghplus C3 C6)))).
  rewrite EQC1. assumption.

  assert (bc2c5c036: boundgh (ghplus C2 (ghplus C5 (ghplus C0 (ghplus C3 C6))))).
  rewrite <- EQC. rewrite ghplus_comm; repeat php_.
  apply tmp2 with (v:=upd Z.eq_dec wt (Aof (evall v2)) (wt (Aof (evall v2)) - 1)%nat)(v3:=ot)(O':= (Some (Oof (evall v1) :: O))); repeat php_.
  apply sn_op.
  apply Permutation_refl.
  unfold spurious_ok in SPUR.
  destruct SPUR as [SPUR|SPUR].
  inversion SPUR.

  assert (G: sat p0 None C0 (subsas (snd (Iof (evall v1)))
    (invs (fst (Iof (evall v1))) (upd Z.eq_dec wt (Aof (evall v2)) (wt (Aof (evall v2)) - 1)%nat) ot) **
    subsas (snd (Mof (evall v2))) (invs (fst (Mof (evall v2))) empb empb))).
  {
  apply SPUR; try assumption.
  simpl.
  split.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  apply Nat.ltb_lt.
  rewrite EQ1 in LTWT.
  assumption.
  unfold ifb.
  destruct (list_eq_dec (olocation_eq_dec Z.eq_dec) (map evalol (M'of v2)) nil).
  reflexivity.
  contradiction.
  assumption.
  }
  simpl in G.
  destruct G as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(tmp0,(tmp8, (p7p8,C7C8)))))))))))))))))).
  subst.

  assert (phpdp7p3562: phplusdef p7 (phplus (phplus p3 (phplus p5 p6)) p2) /\ phplusdef p8 (phplus (phplus p3 (phplus p5 p6)) p2)).
  repeat php_.

  assert (phpdp7p356p72: phplusdef p7 (phplus p3 (phplus p5 p6)) /\ phplusdef p7 p2).
  repeat php_.

  assert (phpdp73p756: phplusdef p7 p3 /\ phplusdef p7 (phplus p5 p6)).
  repeat php_.

  assert (phpdp75p76: phplusdef p7 p5 /\ phplusdef p7 p6).
  repeat php_.

  assert (phpdp8356p82: phplusdef p8 (phplus p3 (phplus p5 p6)) /\ phplusdef p8 p2).
  repeat php_.

  assert (phpdp83p856: phplusdef p8 p3 /\ phplusdef p8 (phplus p5 p6)).
  repeat php_.

  assert (phpdp85p86: phplusdef p8 p5 /\ phplusdef p8 p6).
  repeat php_.

  assert (ghpdp7p3562: ghplusdef C7 (ghplus (ghplus C3 (ghplus C5 C6)) C2) /\ ghplusdef C8 (ghplus (ghplus C3 (ghplus C5 C6)) C2)).
  repeat php_.

  assert (ghpdp7p356p72: ghplusdef C7 (ghplus C3 (ghplus C5 C6)) /\ ghplusdef C7 C2).
  repeat php_.

  assert (ghpdp73p756: ghplusdef C7 C3 /\ ghplusdef C7 (ghplus C5 C6)).
  repeat php_.

  assert (ghpdp75p76: ghplusdef C7 C5 /\ ghplusdef C7 C6).
  repeat php_.

  assert (ghpdp8356p82: ghplusdef C8 (ghplus C3 (ghplus C5 C6)) /\ ghplusdef C8 C2).
  repeat php_.

  assert (ghpdp83p856: ghplusdef C8 C3 /\ ghplusdef C8 (ghplus C5 C6)).
  repeat php_.

  assert (ghpdp85p86: ghplusdef C8 C5 /\ ghplusdef C8 C6).
  repeat php_.


  assert (bp36u578: boundph(phplus (phplus p3 p6) (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v1)
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) (phplus p7 p8)))).
  rewrite phplus_comm; repeat php_.

  assert (bu5: boundph (upd (location_eq_dec Z.eq_dec) p5 (evall v1)
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot)))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bu5p78: boundph (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v1)
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) (phplus p7 p8))).
  {
  apply boundph_mon with (phplus p3 p6); try assumption.
  rewrite phplus_comm; repeat php_.
  }

  assert (EQC2: ghplus (ghplus C7 C8) (ghplus C3 (ghplus C5 C6)) =
    ghplus (ghplus C3 C6) (ghplus C5 (ghplus C7 C8))).
  {
  rewrite ghplus_comm; repeat php_.
  rewrite ghplus_comm; repeat php_.
  }

  assert (bgc36c578: boundgh (ghplus (ghplus C3 C6) (ghplus C5 (ghplus C7 C8)))).
  rewrite <- EQC2. assumption.

  assert (bg365: boundgh (ghplus (ghplus C3 C6) C5)).
  rewrite ghplus_assoc; repeat php_.
  replace (ghplus C6 C5) with (ghplus C5 C6); repeat php_.

  assert (bg578: boundgh (ghplus C5 (ghplus C7 C8))).
  apply boundgh_mon with (ghplus C3 C6).
  rewrite ghplus_comm; repeat php_.

  assert (EQH3: phplus (phplus p3 p6) (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v1)
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot)))
    (phplus p7 p8)) = phplus  (upd (location_eq_dec Z.eq_dec) p5 (evall v1)
    (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot)))
    (phplus (phplus p7 p8) (phplus p3 p6))).
  rewrite phplus_comm; repeat php_.
  rewrite <- EQH3.

  assert (EQC3: ghplus (ghplus C3 C6) (ghplus C5 (ghplus C7 C8)) =
    ghplus C5 (ghplus (ghplus C7 C8) (ghplus C3 C6))).
  rewrite ghplus_comm; repeat php_.
  rewrite <- EQC3.

  assert (eqh4: phplus p6 (phplus p3 (phplus (upd (location_eq_dec Z.eq_dec) p5 
   (evall v1) (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) (phplus p7 p8))) =
   phplus (phplus p3 p6) (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v1)
   (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) (phplus p7 p8))).
  {
  replace (phplus p3 p6) with (phplus p6 p3).
  rewrite phplus_assoc; repeat php_. repeat php_.
  }

  assert (eqg4: ghplus C6 (ghplus C3 (ghplus C5 (ghplus C7 C8))) = ghplus (ghplus C3 C6) (ghplus C5 (ghplus C7 C8))).
  {
  replace (ghplus C3 C6) with (ghplus C6 C3).
  rewrite ghplus_assoc; repeat php_. repeat php_.
  }

  assert (b3578: boundph (phplus p3 (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v1)
   (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) (phplus p7 p8)))).
  rewrite <- eqh4 in bp36u578. repeat php_.

  assert (bg3578: boundgh (ghplus C3 (ghplus C5 (ghplus C7 C8)))).
  rewrite <- eqg4 in bgc36c578. repeat php_.

  exists p6, (phplus p3 (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v1)
       (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) (phplus p7 p8))).
  exists. repeat php_.
  exists. repeat php_.
  exists. assumption.
  exists. rewrite eqh4. assumption.
  exists (Some (Oof(evall v1)::O)), None.
  exists C6, (ghplus C3 (ghplus C5 (ghplus C7 C8))).
  exists. repeat php_.
  exists. repeat php_.
  exists. assumption.
  exists. rewrite eqg4. assumption.
  exists. apply fs_op. apply Permutation_refl. split.
  {
  destruct SPUR as (SPUR1,SPUR2).
  assert (M'n: M'of v2 = nil).
  {
  destruct v2.
  simpl in *.
  destruct l0.
  reflexivity.
  inversion SPUR1.
  }
  rewrite M'n.
  simpl.
  apply fs_op.
  apply perm_skip.
  apply Permutation_sym.
  assumption.
  }
  split.
  {
  subst.
  exists p3, (phplus (upd (location_eq_dec Z.eq_dec) p5 (evall v1)
   (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) (phplus p7 p8)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, None.
  exists C3, (ghplus C5 (ghplus C7 C8)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply None_op.
  split. assumption. split.

  exists (upd (location_eq_dec Z.eq_dec) p5 (evall v1)
   (Some (Locked (upd Z.eq_dec wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))), (phplus p7 p8).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, None.
  exists C5, (ghplus C7 C8).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply None_op.
  split.
  unfold upd at 1.
  destruct (location_eq_dec Z.eq_dec (evall v1) (evall v1)).
  rewrite EQ1. reflexivity.
  contradiction.
  split.
  {
  exists p7, p8.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists O7, O8, C7, C8.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  split; reflexivity.
  }
  rewrite EQ1.
  split; reflexivity.
  split; reflexivity.
  }
  split.
  rewrite <- phplus_assoc; try assumption.
  replace (phplus p6 p3) with (phplus p3 p6). reflexivity.
  repeat php_. repeat php_. repeat php_. repeat php_.
  rewrite <- ghplus_assoc; try assumption.
  replace (ghplus C6 C3) with (ghplus C3 C6). reflexivity.
  repeat php_. repeat php_. repeat php_. repeat php_.
Qed.


Lemma sat_chrg:
  forall m p O C tx invs sp
        (SAT: sat p (Some O) C (EX O, (EX wt, (EX ot, (EX l, (EX v, (EX ev, (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (Z.eqb ([[ev]]) ([[Aof v]])))
        &* Acond v ** Aobs O ** Alocked l wt ot 
        ** ((Acond v ** Aobs (Oof v::O) ** Alocked l wt (upd Z.eq_dec ot ([[ev]]) (ot ([[ev]]) + 1)%nat)) --*
        (weakest_pre_tx (S m) sp tx invs 0)))))))))),
    exists wt ot lv ll v
           (EQv: Aof lv = ([[v]]))
           (EQl: Aof ll = Lof lv)
           (Pl: p ll = Some (Locked wt ot))
           (Pv: p lv = Some Cond),
      sat (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)%nat))))
       (Some (Oof lv::O)) C (weakest_pre_ct (S m) sp (tt, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v0,(v1,(v2,(v3,(v4,(v,(eqls,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2))))))))))))))))))))))))).
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

  assert (o6N: Permutation O (map evalol v0) /\ O6 = None).
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

  assert (bup135: boundph (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
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
    (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  }

  assert (bp6up1p35: boundph (phplus p6
    (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
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

  assert (phpdefp1up35: phplusdef p1 (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  }

  assert (bu35: boundph (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bp1up35: boundph (phplus p1 (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
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

  exists v1, v2, (evall v4), (evall v3), v.
  exists. symmetry. assumption.
  exists. symmetry. assumption.
  exists. assumption.
  exists. assumption.

  assert (EQH: upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 (phplus p5 p6))) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))) =
    phplus p6 (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
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

  apply tmp7 with (Some (evalol (Oof v4) :: O)); repeat php_.
  apply sn_op.
  apply Permutation_refl.
  exists p1, (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat)))).
  exists. repeat php_.
  exists. repeat php_.
  exists. assumption.
  exists. assumption.
  exists None, (Some (evalol (Oof v4) :: O)), (emp (option nat*nat)), (ghplus C3 (ghplus C5 c1)).
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
  exists (emp knowledge), (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat)))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (evalol (Oof v4) :: O)), None.
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
  destruct ((location_eq_dec Z.eq_dec) (evall v3) (evall v3)).
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


Lemma sat_chrgu:
  forall m p O C tx invs sp
        (SAT: sat p (Some O) C (EX O, (EX wt, (EX ot, (EX l, (EX v, (EX ev, (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (Z.eqb ([[ev]]) ([[Aof v]])))
        &* Aicond v ** Aobs O ** Aulock l wt ot 
        ** ((Aicond v ** Aobs (Oof v::O) ** Aulock l wt (upd Z.eq_dec ot ([[ev]]) (ot ([[ev]]) + 1)%nat)) --*
        (weakest_pre_tx (S m) sp tx invs 0)))))))))),
    exists wt ot lv ll v
           (EQv: Aof lv = ([[v]]))
           (EQl: Aof ll = Lof lv)
           (Pl: p ll = Some (Ulock wt ot))
           (Pv: p lv = Some Icond),
      sat (upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) + 1)%nat))))
       (Some (Oof lv::O)) C (weakest_pre_ct (S m) sp (tt, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v0,(v1,(v2,(v3,(v4,(v,(eqls,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2))))))))))))))))))))))))).
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

  assert (o6N: Permutation O (map evalol v0) /\ O6 = None).
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

  assert (p1p3p56v4: phplus p1 (phplus p3 (phplus p5 p6)) (evall v4) = Some Icond).
  {
  apply phplus_Icond; repeat php_.
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

  assert (bup135: boundph (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
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
    (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))))).
  {
  apply phpdef_comm.
  apply phpdef_ulock; repeat php_.
  }

  assert (bp6up1p35: boundph (phplus p6
    (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
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

  assert (phpdefp1up35: phplusdef p1 (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))))).
  {
  apply phpdef_comm.
  apply phpdef_ulock; repeat php_.
  }

  assert (bu35: boundph (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bp1up35: boundph (phplus p1 (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
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

  exists v1, v2, (evall v4), (evall v3), v.
  exists. symmetry. assumption.
  exists. symmetry. assumption.
  exists. assumption.
  exists. assumption.

  assert (EQH: upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 (phplus p5 p6))) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat))) =
    phplus p6 (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
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

  apply tmp7 with (Some (evalol (Oof v4) :: O)); repeat php_.
  apply sn_op.
  apply Permutation_refl.
  exists p1, (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat)))).
  exists. repeat php_.
  exists. repeat php_.
  exists. assumption.
  exists. assumption.
  exists None, (Some (evalol (Oof v4) :: O)), (emp (option nat*nat)), (ghplus C3 (ghplus C5 c1)).
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
  exists (emp knowledge), (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) + 1)%nat)))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (evalol (Oof v4) :: O)), None.
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
  destruct ((location_eq_dec Z.eq_dec) (evall v3) (evall v3)).
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


Lemma sat_disch:
  forall m p O C tx invs sp
        (SAT: sat p (Some O) C (EX O, (EX wt, (EX ot, (EX l, (EX v, (EX ev, (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (andb (Z.eqb ([[ev]]) ([[Aof v]]))
        (safe_obs (evall v) (wt ([[ev]])) ((ot ([[ev]]) - 1)))))
        &* Acond v ** Aobs (Oof v::O) ** Alocked l wt ot 
        ** ((Acond v ** Aobs O ** Alocked l wt (upd Z.eq_dec ot ([[ev]]) (ot ([[ev]]) - 1)%nat)) --*
        (weakest_pre_tx (S m) sp tx invs 0)))))))))),
    exists wt ot O1 lv ll v
           (O1eq: Permutation O (Oof lv::O1))
           (EQv: Aof lv = ([[v]]))
           (EQl: Aof ll = Lof lv)
           (Pl: p ll = Some (Locked wt ot))
           (Pv: p lv = Some Cond)
           (INO: In (Oof lv) O)
           (SAFE_OBS: safe_obs lv (wt ([[v]])) ((ot ([[v]])) - 1) = true),
      sat (upd (location_eq_dec Z.eq_dec) p ll (Some (Locked wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)%nat))))
       (Some O1) C (weakest_pre_ct (S m) sp (tt, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v0,(v1,(v2,(v3,(v4,(v,(eqls,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2))))))))))))))))))))))))).
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

  assert (PERM: Permutation O (evalol (Oof v4) :: map evalol v0) /\ O6 = None).
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

  assert (bup135: boundph (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
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
    (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  }

  assert (bp6up1p35: boundph (phplus p6
    (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
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

  assert (phpdefp1up35: phplusdef p1 (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))))).
  {
  apply phpdef_comm.
  apply phpdef_locked; repeat php_.
  }

  assert (bu35: boundph (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bp1up35: boundph (phplus p1 (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
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
  apply Z.eqb_eq in EQ1.
  apply Z.eqb_eq in EQ2.
  unfold id in *.

  exists v1, v2, (map evalol v0), (evall v4), (evall v3), v.
  exists PERM.
  exists. symmetry. assumption.
  exists. symmetry. assumption.
  exists. assumption.
  exists. assumption.
  exists. apply Permutation_in with (evalol (Oof v4) :: map evalol v0).
  apply Permutation_sym.
  assumption.
  left. reflexivity.
  exists. assumption.

  assert (EQH: upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 (phplus p5 p6))) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))) =
    phplus p6 (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
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

  apply tmp7 with (Some (map evalol v0)); repeat php_.
  apply sn_op.
  apply Permutation_refl.

  exists p1, (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat)))).
  exists. repeat php_.
  exists. repeat php_.
  exists. assumption.
  exists. assumption.
  exists None, (Some (map evalol v0)), (emp (option nat*nat)), (ghplus C3 (ghplus C5 c1)).
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
  exists (emp knowledge), (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
    (Some (Locked v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat)))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (map evalol v0)), None.
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
  destruct ((location_eq_dec Z.eq_dec) (evall v3) (evall v3)).
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
  forall m p O C tx invs sp
        (SAT: sat p (Some O) C (EX O, (EX wt, (EX ot, (EX l, (EX v, (EX ev, (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (andb (Z.eqb ([[ev]]) ([[Aof v]]))
        (safe_obs (evall v) (wt ([[ev]])) ((ot ([[ev]]) - 1)))))
        &* Aicond v ** Aobs (Oof v::O) ** Aulock l wt ot 
        ** ((Aicond v ** Aobs O ** Aulock l wt (upd Z.eq_dec ot ([[ev]]) (ot ([[ev]]) - 1)%nat)) --*
        (weakest_pre_tx (S m) sp tx invs 0)))))))))),
    exists wt ot O1 lv ll v
           (O1eq: Permutation O (Oof lv::O1))
           (EQv: Aof lv = ([[v]]))
           (EQl: Aof ll = Lof lv)
           (Pl: p ll = Some (Ulock wt ot))
           (Pv: p lv = Some Icond)
           (INO: In (Oof lv) O)
           (SAFE_OBS: safe_obs lv (wt ([[v]])) ((ot ([[v]])) - 1) = true),
      sat (upd (location_eq_dec Z.eq_dec) p ll (Some (Ulock wt (upd Z.eq_dec ot ([[v]]) (ot ([[v]]) - 1)%nat))))
       (Some O1) C (weakest_pre_ct (S m) sp (tt, tx) invs).
Proof.
  simpl.
  intros.
  destruct SAT as (v0,(v1,(v2,(v3,(v4,(v,(eqls,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(tmp1,(tmp2,(p1p2,C1C2))))))))))))))))))))))))).
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

  assert (PERM: Permutation O (evalol (Oof v4) :: map evalol v0) /\ O6 = None).
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

  assert (p1p3p56v4: phplus p1 (phplus p3 (phplus p5 p6)) (evall v4) = Some Icond).
  {
  apply phplus_Icond; repeat php_.
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

  assert (bup135: boundph (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
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
    (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))))).
  {
  apply phpdef_comm.
  apply phpdef_ulock; repeat php_.
  }

  assert (bp6up1p35: boundph (phplus p6
    (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
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

  assert (phpdefp1up35: phplusdef p1 (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))))).
  {
  apply phpdef_comm.
  apply phpdef_ulock; repeat php_.
  }

  assert (bu35: boundph (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))))).
  {
  apply boundph_upd; repeat php_.
  intros.
  destruct H as (z',CO).
  inversion CO.
  }

  assert (bp1up35: boundph (phplus p1 (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
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
  apply Z.eqb_eq in EQ1.
  apply Z.eqb_eq in EQ2.
  unfold id in *.

  exists v1, v2, (map evalol v0), (evall v4), (evall v3), v.
  exists PERM.
  exists. symmetry. assumption.
  exists. symmetry. assumption.
  exists. assumption.
  exists.
 assumption.
  exists. apply Permutation_in with (evalol (Oof v4) :: map evalol v0).
  apply Permutation_sym.
  assumption.
  left. reflexivity.
  exists. assumption.

  assert (EQH: upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 (phplus p5 p6))) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat))) =
    phplus p6 (upd (location_eq_dec Z.eq_dec) (phplus p1 (phplus p3 p5)) (evall v3)
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

  apply tmp7 with (Some (map evalol v0)); repeat php_.
  apply sn_op.
  apply Permutation_refl.

  exists p1, (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat)))).
  exists. repeat php_.
  exists. repeat php_.
  exists. assumption.
  exists. assumption.
  exists None, (Some (map evalol v0)), (emp (option nat*nat)), (ghplus C3 (ghplus C5 c1)).
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
  exists (emp knowledge), (upd (location_eq_dec Z.eq_dec) (phplus p3 p5) (evall v3)
    (Some (Ulock v1 (upd Z.eq_dec v2 ([[v]]) (v2 ([[v]]) - 1)%nat)))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (map evalol v0)), None.
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
  destruct ((location_eq_dec Z.eq_dec) (evall v3) (evall v3)).
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


Lemma sat_g_newctr:
  forall m p O C gc tx invs sp (BP: boundph p) (BC: boundgh C)
        (Cgc: C gc = None)
        (SAT: sat p O C (FA gc, Actr (Enum gc) 0 --* (weakest_pre_tx (S m) sp tx invs 0))),
      sat p O (upd Z.eq_dec C gc (Some (Some 0%nat,0%nat))) (weakest_pre_ct (S m) sp (tt, tx) invs).
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


Lemma sat_g_ctrinc:
  forall m' p O C tx invs sp (BP: boundph p) (BC: boundgh C)
        (SAT: sat p O C (EX n, (EX gv, (Actr gv n ** (Actr gv (S n)%nat ** Atic gv --* (weakest_pre_tx (S m') sp tx invs 0)))))),
    exists t m gc
      (Cgc: C ([[gc]]) = Some (Some t, m)),
      sat p O (upd Z.eq_dec C ([[gc]]) (Some (Some (S t), S m))) (weakest_pre_ct (S m') sp (tt, tx) invs).
Proof.
  unfold weakest_pre_ct.
  simpl.
  intros.
  destruct SAT as (v,(gc,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,((n,C1gc),(tmp2,(p1p2,C1C2)))))))))))))))))))).
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
  exists gc.
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
  exists None. 
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

  exists v, n, gc.
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
  exists None.
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
  forall m' p O C tx invs sp (BP: boundph p) (BC: boundgh C)
        (SAT: sat p O C (EX n, (EX ev, (Actr ev n ** Atic ev ** (Actr ev (n-1)%nat --* (weakest_pre_tx (S m') sp tx invs 0)))))),
    exists gc t m
      (Cgc: C ([[gc]]) = Some (Some (S t),S m)),
      sat p O (upd Z.eq_dec C ([[gc]]) (Some (Some t,m))) (weakest_pre_ct (S m') sp (tt, tx) invs).
Proof.
  unfold weakest_pre_ct.
  simpl.
  intros.
  destruct SAT as (v,(gc,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,((n,C1gc),(tmp2,(p1p2,C1C2)))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,C3C4)))))))))))))))))).

  rewrite <- C1C2.
  rewrite <- C3C4.
  unfold id in *.
  destruct tmp4 as (n',C3gc).
  unfold ghplus at 1 2 3 4.
  exists gc.
  rewrite C1gc.
  destruct C3gc as (oc3,C3gc).
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


Lemma sat_frame:
  forall m f c p O C Q se invs sp
         (SAT: sat p O C ((weakest_pre m sp c (fun x : Z => Q x) se invs) ** f)),
    forall m' (LE: le m' m), sat p O C (weakest_pre m' sp c (fun x : Z => Q x ** f) se invs).
Proof.
  induction m.
  intros.
  destruct m'.
  reflexivity.
  inversion LE.

  destruct c; intros; try assumption.
  {
  destruct m'; try reflexivity.
  simpl in *.
  assumption.
  }
  {
  destruct m'; try reflexivity.
  simpl in *.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  subst.
  assert (phpdefp1p'p2p': phplusdef p1 p' /\ phplusdef p2 p'). repeat php_.
  assert (ghpdefp1p'p2p': ghplusdef C1 g' /\ ghplusdef C2 g'). repeat php_.
  assert (eqh: phplus (phplus p1 p') p2 = phplus (phplus p1 p2) p').
  {
  rewrite phplus_comm; try assumption. rewrite <- phplus_assoc; try assumption.
  replace (phplus p2 p1) with (phplus p1 p2); repeat php_.
  repeat php_. repeat php_. repeat php_. repeat php_.
  }
  assert (eqg: ghplus (ghplus C1 g') C2 = ghplus (ghplus C1 C2) g').
  {
  rewrite ghplus_comm; try assumption. rewrite <- ghplus_assoc; try assumption.
  replace (ghplus C2 C1) with (ghplus C1 C2); repeat php_.
  repeat php_. repeat php_. repeat php_. repeat php_.
  }

  assert (exo: exists O1', oplus O1' O2 O'' /\ oplus O1 O' O1').
  {
  inversion opO1O2.
  rewrite <- H1 in OPLUS.
  inversion OPLUS.
  exists None.
  split; apply None_op.
  exists (Some o').
  split. apply fs_op. apply Permutation_refl.
  apply sn_op. assumption.
  rewrite <- H1 in OPLUS.
  inversion OPLUS.
  exists (Some o'0).
  split. apply fs_op. apply Permutation_refl.
  apply fs_op. apply Permutation_trans with o'; try assumption.
  rewrite <- H1 in OPLUS.
  inversion OPLUS.
  exists None.
  split. apply sn_op. apply Permutation_trans with o'; try assumption.
  apply None_op.
  }
  destruct exo as (O1',(op1,op2)).

  exists (phplus p1 p'), p2.
  exists. repeat php_.
  exists. apply boundph_mon with p2; repeat php_.
  rewrite eqh. assumption.
  exists. assumption.
  exists. rewrite eqh. assumption.
  exists O1', O2, (ghplus C1 g'), C2. 
  exists. repeat php_.
  exists. apply boundgh_mon with C2; repeat php_.
  rewrite eqg. assumption.
  exists. assumption.
  exists. rewrite eqg. assumption.
  exists op1.
  split.
  apply tmp1 with O'; repeat php_.
  rewrite eqh. assumption.
  rewrite eqg. assumption.
  split. assumption.
  split; repeat php_.
  }
  {
  destruct m'; try reflexivity.
  simpl in *.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  destruct tmp1 as (v,(v0,(v1,(eq,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4)))))))))))))))))))))).
  subst.
  exists v, v0, v1.
  split. assumption.

  assert (phpdef1: phplusdef p3 p2 /\ phplusdef p4 p2). repeat php_.
  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef C4 C2). repeat php_.
  assert (eqh: phplus (phplus p4 p2) p3 = phplus (phplus p3 p4) p2).
  rewrite phplus_comm; repeat php_.
  assert (eqg: ghplus (ghplus C4 C2) C3 = ghplus (ghplus C3 C4) C2).
  rewrite ghplus_comm; repeat php_.
  exists p3, (phplus p4 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh. assumption.
  exists. rewrite <- phplus_assoc; repeat php_.
  assert (exo: exists O42, oplus O4 O2 O42 /\ oplus O3 O42 O).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  inversion OP1.
  rewrite <- H in OP2.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in OP2.
  inversion OP2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply fs_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in OP2.
  inversion OP2.
  exists (Some o).
  split. apply sn_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O42,(op42,op342)).
  exists O3, O42, C3, (ghplus C4 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg. assumption.
  exists. repeat php_. rewrite <- ghplus_assoc; repeat php_.
  exists op342.
  split. assumption.
  split.
  intros.
  assert (phpdef2: phplusdef p4 p' /\ phplusdef p2 p'). repeat php_.
  assert (ghpdef2: ghplusdef C4 g' /\ ghplusdef C2 g'). repeat php_.
  assert (eqh1: phplus (phplus p4 p') p2 = phplus (phplus p4 p2) p').
  rewrite phplus_comm; try assumption. rewrite <- phplus_assoc; repeat php_. repeat php_.
  assert (eqg1: ghplus (ghplus C4 g') C2 = ghplus (ghplus C4 C2) g').
  rewrite ghplus_comm; try assumption. rewrite <- ghplus_assoc; repeat php_. repeat php_.
  exists (phplus p4 p'), p2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh1. assumption.
  exists. repeat php_.
  exists. rewrite eqh1. assumption.
  assert (exo: exists O4', oplus O4' O2 O'' /\ oplus O4 O' O4').
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=OPLUS).
  assert (OP4:=op42).
  inversion OP3.
  rewrite <- H in *.
  inversion OP4.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP4.
  exists (Some o').
  split. apply fs_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists None.
  split. apply sn_op. apply Permutation_trans with o; assumption.
  apply None_op.
  rewrite <- H in *.
  inversion OP4.
  exists (Some o').
  split. apply fs_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O4',(op4'2,op4')).
  exists O4', O2, (ghplus C4 g'), C2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists op4'2.
  split.
  apply tmp5 with O'; repeat php_.
  rewrite eqh1. assumption.
  rewrite eqg1. assumption.
  split. assumption.
  split; repeat php_.
  split; repeat php_.
  }

  {
  destruct m'; try reflexivity.
  simpl in *.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  destruct tmp1 as (v,(v0,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4)))))))))))))))))))).
  subst.
  exists v, v0.

  assert (phpdef1: phplusdef p3 p2 /\ phplusdef p4 p2). repeat php_.
  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef C4 C2). repeat php_.
  assert (eqh: phplus (phplus p4 p2) p3 = phplus (phplus p3 p4) p2).
  rewrite phplus_comm; repeat php_.
  assert (eqg: ghplus (ghplus C4 C2) C3 = ghplus (ghplus C3 C4) C2).
  rewrite ghplus_comm; repeat php_.
  exists p3, (phplus p4 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh. assumption.
  exists. rewrite <- phplus_assoc; repeat php_.
  assert (exo: exists O42, oplus O4 O2 O42 /\ oplus O3 O42 O).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  inversion OP1.
  rewrite <- H in OP2.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in OP2.
  inversion OP2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply fs_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in OP2.
  inversion OP2.
  exists (Some o).
  split. apply sn_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O42,(op42,op342)).
  exists O3, O42, C3, (ghplus C4 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg. assumption.
  exists. repeat php_. rewrite <- ghplus_assoc; repeat php_.
  exists op342.
  split. assumption.
  split.
  intros.
  assert (phpdef2: phplusdef p4 p' /\ phplusdef p2 p'). repeat php_.
  assert (ghpdef2: ghplusdef C4 g' /\ ghplusdef C2 g'). repeat php_.
  assert (eqh1: phplus (phplus p4 p') p2 = phplus (phplus p4 p2) p').
  rewrite phplus_comm; try assumption. rewrite <- phplus_assoc; repeat php_. repeat php_.
  assert (eqg1: ghplus (ghplus C4 g') C2 = ghplus (ghplus C4 C2) g').
  rewrite ghplus_comm; try assumption. rewrite <- ghplus_assoc; repeat php_. repeat php_.
  exists (phplus p4 p'), p2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh1. assumption.
  exists. repeat php_.
  exists. rewrite eqh1. assumption.
  assert (exo: exists O4', oplus O4' O2 O'' /\ oplus O4 O' O4').
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=OPLUS).
  assert (OP4:=op42).
  inversion OP3.
  rewrite <- H in *.
  inversion OP4.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP4.
  exists (Some o').
  split. apply fs_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists None.
  split. apply sn_op. apply Permutation_trans with o; assumption.
  apply None_op.
  rewrite <- H in *.
  inversion OP4.
  exists (Some o').
  split. apply fs_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O4',(op4'2,op4')).
  exists O4', O2, (ghplus C4 g'), C2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists op4'2.
  split.
  apply tmp5 with O'; repeat php_.
  rewrite eqh1. assumption.
  rewrite eqg1. assumption.
  split. assumption.
  split; repeat php_.
  split; repeat php_.
  }

  {
  destruct m'; try reflexivity.
  simpl in *.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  destruct tmp1 as (v,(v0,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4)))))))))))))))))))).
  destruct tmp4 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp8,(tmp6,(p5p6,c56)))))))))))))))))).
  subst.
  exists v, v0.

  assert (phpdef1: phplusdef (phplus p5 p6) p2 /\ phplusdef p4 p2). repeat php_.
  assert (phpdef2: phplusdef p5 p2 /\ phplusdef p6 p2). repeat php_.
  assert (phpdef3: phplusdef p5 p4 /\ phplusdef p6 p4). repeat php_.
  assert (ghpdef1: ghplusdef (ghplus C5 C6) C2 /\ ghplusdef C4 C2). repeat php_.
  assert (ghpdef2: ghplusdef C5 C2 /\ ghplusdef C6 C2). repeat php_.
  assert (ghpdef3: ghplusdef C5 C4 /\ ghplusdef C6 C4). repeat php_.
  assert (eqh: phplus (phplus (phplus p5 p6) p2) p4 = phplus (phplus (phplus p5 p6) p4) p2).
  rewrite phplus_assoc; repeat php_.
  assert (eqg: ghplus (ghplus (ghplus C5 C6) C2) C4 = ghplus (ghplus (ghplus C5 C6) C4) C2).
  rewrite ghplus_assoc; repeat php_.
  assert (bp562: boundph (phplus p5 (phplus p6 p2))).
  repeat php_. rewrite <- phplus_assoc; repeat php_. rewrite eqh. assumption.
  assert (bp62: boundph (phplus p6 p2)).
  repeat php_.
  assert (bg562: boundgh (ghplus C5 (ghplus C6 C2))).
  repeat php_. rewrite <- ghplus_assoc; repeat php_. rewrite eqg. assumption.
  assert (bg62: boundgh (ghplus C6 C2)).
  repeat php_.

  exists (phplus (phplus p5 p6) p2), p4.
  exists. repeat php_.
  exists. rewrite phplus_assoc; repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh. assumption.
  assert (exo: exists O32, oplus O3 O2 O32 /\ oplus O32 O4 O).
  {
  assert (op1:=opO1O2).
  assert (op2:=opO3O4).
  assert (op3:=opO5O6).
  inversion op1.
  rewrite <- H in *.
  inversion op2.
  exists None. split; apply None_op.
  rewrite <- H in *.
  inversion op2.
  exists (Some o0).
  split. apply fs_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists None.
  split. apply None_op.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion op2.
  exists (Some o).
  split. apply sn_oplus.
  apply fs_op. assumption.
  }
  destruct exo as (O32,(op32,op324)).
  exists O32, O4, (ghplus (ghplus C5 C6) C2), C4.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg. assumption.
  exists op324.
  split.
  exists p5, (phplus p6 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O62, oplus O6 O2 O62 /\ oplus O5 O62 O32).
  {
  assert (op1:=opO1O2).
  assert (op2:=opO3O4).
  assert (op3:=opO5O6).
  inversion op32.
  rewrite <- H in *.
  inversion op3.
  exists None. split; apply None_op.
  rewrite <- H in *.
  inversion op3.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply fs_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion op3.
  exists (Some o).
  split. apply sn_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O62,(op62,op562)).
  exists O5, O62, C5, (ghplus C6 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  intros.
  assert (phpdef4: phplusdef p6 p' /\ phplusdef p2 p'). repeat php_.
  assert (ghpdef4: ghplusdef C6 g' /\ ghplusdef C2 g'). repeat php_.
  assert (eqh1: phplus (phplus p6 p') p2 = phplus (phplus p6 p2) p').
  rewrite phplus_comm; try assumption.
  rewrite <- phplus_assoc; try assumption.
  replace (phplus p2 p6) with (phplus p6 p2); repeat php_.
  repeat php_.  repeat php_.  repeat php_.  repeat php_.

  assert (eqg1: ghplus (ghplus C6 g') C2 = ghplus (ghplus C6 C2) g').
  rewrite ghplus_comm; try assumption.
  rewrite <- ghplus_assoc; try assumption.
  replace (ghplus C2 C6) with (ghplus C6 C2); repeat php_.
  repeat php_.  repeat php_.  repeat php_.  repeat php_.

  exists (phplus p6 p'), p2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh1. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh1. assumption.
  assert (exo: exists O6', oplus O6 O' O6' /\ oplus O6' O2 O'').
  {
  assert (op1:=opO1O2).
  assert (op2:=op62).
  inversion OPLUS.
  rewrite <- H in *.
  inversion op2.
  exists None. split; apply None_op.
  rewrite <- H in *.
  inversion op2.
  exists (Some o0).
  split. apply fs_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists None.
  split. apply None_op.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion op2.
  exists (Some o).
  split. apply sn_oplus.
  apply fs_op. assumption.
  }
  destruct exo as (O6',(op6',op6'2)).
  exists O6', O2, (ghplus C6 g'), C2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists op6'2.
  split.
  apply tmp6 with O'; repeat php_.
  rewrite eqh1. assumption.
  rewrite eqg1. assumption.
  split. assumption.
  rewrite eqh1, eqg1.
  split; reflexivity.
  split; repeat php_.
  split.
  intros.
  eapply sat_weak_imp; try assumption.
  apply tmp5 with O'; repeat php_.
  intros.
  apply SAT0.
  omega.
  split; repeat php_.
  }
  {
  destruct m'; try reflexivity.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  subst.
  simpl.
  eapply sat_weak_imp; repeat php_.
  apply IHm.
  simpl in tmp1.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split.
  apply tmp1.
  split.
  apply tmp2.
  split; reflexivity.
  omega.
  simpl.
  intros.
  destruct SAT as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, p3p4))))))))))))))))).
  destruct p3p4.
  subst.
  apply IHm.
  simpl.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  split. assumption.
  split; try assumption.
  split; reflexivity.
  omega.
  }

  {
  destruct m'; try reflexivity.
  simpl in *.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  subst.
  eapply sat_weak_imp; repeat php_.
  apply IHm.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split.
  apply tmp1.
  split.
  apply tmp2.
  split; reflexivity.
  omega.
  simpl.
  intros.
  destruct SAT as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, p3p4))))))))))))))))).
  subst.
  destruct ((0 <? z)%Z).
  eapply IHm.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  split. assumption.
  split; assumption.
  omega.
  eapply IHm.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  split. assumption.
  split; assumption.
  omega.
  }
  {
  destruct m'; try reflexivity.
  simpl in *.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  subst.
  eapply sat_weak_imp with (n:=m'); try assumption.
  apply IHm; try assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc12, opO1O2.
  split.
  apply tmp1.
  split.
  apply tmp2.
  split; reflexivity.
  omega.
  simpl.
  intros.
  destruct SAT as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, p3p4))))))))))))))))).
  subst.
  destruct ((0 <? z)%Z).
  eapply sat_weak_imp with (n:=m); try assumption.
  eapply IHm.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  split.
  apply tmp4.
  split.
  apply tmp5.
  assumption.
  omega.
  simpl.
  intros.
  simpl.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp8,(tmp6,(p5p6,c56)))))))))))))))))).
  subst.
  eapply sat_weak_imp with (n:=m); try assumption.
  apply IHm.
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56, opO5O6.
  split.
  apply tmp8.
  split.
  apply tmp6.
  split; reflexivity.
  omega.
  simpl.
  intros.
  assumption.
  omega.
  omega.
  destruct p3p4.
  subst.
  simpl.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, ghpdefC3C4, BC3, BC4, bc34, opO3O4.
  split. assumption.
  split. assumption.
  split; reflexivity.
  omega.
  }

  {
  destruct m'; try reflexivity.
  simpl in *.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  subst.
  specialize tmp1 with v.
  destruct tmp1 as (v0,tmp1).
  exists v0.
  intros.
  assert (phpdefp1p'p2p': phplusdef p1 p' /\ phplusdef p2 p'). repeat php_.
  assert (ghpdefp1p'p2p': ghplusdef C1 g' /\ ghplusdef C2 g'). repeat php_.
  assert (eqh: phplus (phplus p1 p') p2 = phplus (phplus p1 p2) p').
  {
  rewrite phplus_comm; try assumption. rewrite <- phplus_assoc; try assumption.
  replace (phplus p2 p1) with (phplus p1 p2); repeat php_.
  repeat php_. repeat php_. repeat php_. repeat php_.
  }
  assert (eqg: ghplus (ghplus C1 g') C2 = ghplus (ghplus C1 C2) g').
  {
  rewrite ghplus_comm; try assumption. rewrite <- ghplus_assoc; try assumption.
  replace (ghplus C2 C1) with (ghplus C1 C2); repeat php_.
  repeat php_. repeat php_. repeat php_. repeat php_.
  }

  assert (exo: exists O1', oplus O1' O2 O'' /\ oplus O1 O' O1').
  {
  inversion opO1O2.
  rewrite <- H1 in OPLUS.
  inversion OPLUS.
  exists None.
  split; apply None_op.
  exists (Some o').
  split. apply fs_op. apply Permutation_refl.
  apply sn_op. assumption.
  rewrite <- H1 in OPLUS.
  inversion OPLUS.
  exists (Some o'0).
  split. apply fs_op. apply Permutation_refl.
  apply fs_op. apply Permutation_trans with o'; try assumption.
  rewrite <- H1 in OPLUS.
  inversion OPLUS.
  exists None.
  split. apply sn_op. apply Permutation_trans with o'; try assumption.
  apply None_op.
  }
  destruct exo as (O1',(op1,op2)).

  exists (phplus p1 p'), p2.
  exists. repeat php_.
  exists. apply boundph_mon with p2; repeat php_.
  rewrite eqh. assumption.
  exists. assumption.
  exists. rewrite eqh. assumption.
  exists O1', O2, (ghplus C1 g'), C2. 
  exists. repeat php_.
  exists. apply boundgh_mon with C2; repeat php_.
  rewrite eqg. assumption.
  exists. assumption.
  exists. rewrite eqg. assumption.
  exists op1.
  split.
  eapply tmp1 with O'; repeat php_.
  rewrite eqh. assumption.
  rewrite eqg. assumption.
  split. assumption.
  split; repeat php_.
  }

  {
  destruct m'; try reflexivity.
  simpl in *.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  destruct tmp1 as (v,(v0,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4)))))))))))))))))))).
  destruct tmp4 as (eq,(p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp8,(tmp6,(p5p6,c56))))))))))))))))))).
  subst.
  exists v, v0.

  assert (phpdef1: phplusdef (phplus p5 p6) p2 /\ phplusdef p4 p2). repeat php_.
  assert (phpdef2: phplusdef p5 p2 /\ phplusdef p6 p2). repeat php_.
  assert (phpdef3: phplusdef p5 p4 /\ phplusdef p6 p4). repeat php_.
  assert (ghpdef1: ghplusdef (ghplus C5 C6) C2 /\ ghplusdef C4 C2). repeat php_.
  assert (ghpdef2: ghplusdef C5 C2 /\ ghplusdef C6 C2). repeat php_.
  assert (ghpdef3: ghplusdef C5 C4 /\ ghplusdef C6 C4). repeat php_.
  assert (eqh: phplus (phplus p4 p2) (phplus p5 p6) = phplus (phplus (phplus p5 p6) p4) p2).
  symmetry. rewrite phplus_assoc; repeat php_.
  assert (eqg: ghplus (ghplus C4 C2) (ghplus C5 C6) = ghplus (ghplus (ghplus C5 C6) C4) C2).
  symmetry. rewrite ghplus_assoc; repeat php_.

  exists (phplus p5 p6), (phplus p4 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh. assumption.
  exists. repeat php_. rewrite phplus_comm; repeat php_. rewrite eqh. assumption.
  assert (exo: exists O42, oplus O4 O2 O42 /\ oplus O3 O42 O).
  {
  assert (op1:=opO1O2).
  assert (op2:=opO3O4).
  assert (op3:=opO5O6).
  inversion op1.
  rewrite <- H in *.
  inversion op2.
  exists None. split; apply None_op.
  rewrite <- H in *.
  inversion op2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply fs_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion op2.
  exists (Some o).
  split. apply sn_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O42,(op42,op342)).
  exists O3, O42, (ghplus C5 C6), (ghplus C4 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg. assumption.
  exists. repeat php_. rewrite ghplus_comm; repeat php_. rewrite eqg. assumption.
  exists op342.
  split. split. assumption.
  exists p5, p6.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists O5, O6, C5, C6.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split; reflexivity.
  split.
  intros.
  assert (phpdef4: phplusdef p4 p' /\ phplusdef p2 p'). repeat php_.
  assert (ghpdef4: ghplusdef C4 g' /\ ghplusdef C2 g'). repeat php_.
  assert (eqh2: phplus (phplus p4 p') p2 = phplus (phplus p4 p2) p'). repeat php_.
  assert (eqg2: ghplus (ghplus C4 g') C2 = ghplus (ghplus C4 C2) g'). repeat php_.
  exists (phplus p4 p'), p2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh2. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh2. assumption.
  assert (exo: exists O4', oplus O4 O' O4' /\ oplus O4' O2 O'').
  {
  assert (op1:=opO1O2).
  assert (op2:=opO3O4).
  assert (op3:=opO5O6).
  assert (op4:=OPLUS).
  assert (op5:=op42).
  inversion op4.
  rewrite <- H in *.
  inversion op5.
  exists None. split; apply None_op.
  rewrite <- H in *.
  inversion op5.
  exists (Some o0).
  split. apply fs_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists None.
  split. apply None_op.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion op5.
  exists (Some o).
  split. apply sn_oplus.
  apply fs_op. assumption.
  }
  destruct exo as (O4',(op4',op4'2)).
  exists O4', O2, (ghplus C4 g'), C2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg2. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg2. assumption.
  exists. repeat php_.
  split.
  apply tmp5 with v1 v2 O'; repeat php_.
  rewrite eqh2. assumption.
  rewrite eqg2. assumption.
  split. assumption.
  split; repeat php_.
  split; repeat php_.
  }

  {
  destruct m'; try reflexivity.
  simpl in *.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  destruct tmp1 as (v,(v0,(v1,(v2,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4)))))))))))))))))))))).
  subst.
  exists v, v0, v1, v2.

  assert (phpdef1: phplusdef p3 p2 /\ phplusdef p4 p2). repeat php_.
  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef C4 C2). repeat php_.
  assert (eqh: phplus (phplus p4 p2) p3 = phplus (phplus p3 p4) p2).
  rewrite phplus_comm; repeat php_.
  assert (eqg: ghplus (ghplus C4 C2) C3 = ghplus (ghplus C3 C4) C2).
  rewrite ghplus_comm; repeat php_.
  exists p3, (phplus p4 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh. assumption.
  exists. rewrite <- phplus_assoc; repeat php_.
  assert (exo: exists O42, oplus O4 O2 O42 /\ oplus O3 O42 O).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  inversion OP1.
  rewrite <- H in OP2.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in OP2.
  inversion OP2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply fs_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in OP2.
  inversion OP2.
  exists (Some o).
  split. apply sn_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O42,(op42,op342)).
  exists O3, O42, C3, (ghplus C4 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg. assumption.
  exists. repeat php_. rewrite <- ghplus_assoc; repeat php_.
  exists op342.
  split. assumption.
  split.
  intros.
  assert (phpdef2: phplusdef p4 p' /\ phplusdef p2 p'). repeat php_.
  assert (ghpdef2: ghplusdef C4 g' /\ ghplusdef C2 g'). repeat php_.
  assert (eqh1: phplus (phplus p4 p') p2 = phplus (phplus p4 p2) p').
  rewrite phplus_comm; try assumption. rewrite <- phplus_assoc; repeat php_. repeat php_.
  assert (eqg1: ghplus (ghplus C4 g') C2 = ghplus (ghplus C4 C2) g').
  rewrite ghplus_comm; try assumption. rewrite <- ghplus_assoc; repeat php_. repeat php_.
  exists (phplus p4 p'), p2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh1. assumption.
  exists. repeat php_.
  exists. rewrite eqh1. assumption.
  assert (exo: exists O4', oplus O4' O2 O'' /\ oplus O4 O' O4').
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=OPLUS).
  assert (OP4:=op42).
  inversion OP3.
  rewrite <- H in *.
  inversion OP4.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP4.
  exists (Some o').
  split. apply fs_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists None.
  split. apply sn_op. apply Permutation_trans with o; assumption.
  apply None_op.
  rewrite <- H in *.
  inversion OP4.
  exists (Some o').
  split. apply fs_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O4',(op4'2,op4')).
  exists O4', O2, (ghplus C4 g'), C2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists op4'2.
  split.
  apply tmp5 with O'; repeat php_.
  rewrite eqh1. assumption.
  rewrite eqg1. assumption.
  split. assumption.
  split; repeat php_.
  split; repeat php_.
  }

  {
  destruct m'; try reflexivity.
  simpl in *.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  destruct tmp1 as (v,(v0,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4)))))))))))))))))))).
  subst.
  exists v, v0.

  assert (phpdef1: phplusdef p3 p2 /\ phplusdef p4 p2). repeat php_.
  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef C4 C2). repeat php_.
  assert (eqh: phplus (phplus p4 p2) p3 = phplus (phplus p3 p4) p2).
  rewrite phplus_comm; repeat php_.
  assert (eqg: ghplus (ghplus C4 C2) C3 = ghplus (ghplus C3 C4) C2).
  rewrite ghplus_comm; repeat php_.
  exists p3, (phplus p4 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh. assumption.
  exists. rewrite <- phplus_assoc; repeat php_.
  assert (exo: exists O42, oplus O4 O2 O42 /\ oplus O3 O42 O).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  inversion OP1.
  rewrite <- H in OP2.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in OP2.
  inversion OP2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply fs_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in OP2.
  inversion OP2.
  exists (Some o).
  split. apply sn_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O42,(op42,op342)).
  exists O3, O42, C3, (ghplus C4 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg. assumption.
  exists. repeat php_. rewrite <- ghplus_assoc; repeat php_.
  exists op342.
  split. assumption.
  split.
  intros.
  assert (phpdef2: phplusdef p4 p' /\ phplusdef p2 p'). repeat php_.
  assert (ghpdef2: ghplusdef C4 g' /\ ghplusdef C2 g'). repeat php_.
  assert (eqh1: phplus (phplus p4 p') p2 = phplus (phplus p4 p2) p').
  rewrite phplus_comm; try assumption. rewrite <- phplus_assoc; repeat php_. repeat php_.
  assert (eqg1: ghplus (ghplus C4 g') C2 = ghplus (ghplus C4 C2) g').
  rewrite ghplus_comm; try assumption. rewrite <- ghplus_assoc; repeat php_. repeat php_.
  exists (phplus p4 p'), p2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh1. assumption.
  exists. repeat php_.
  exists. rewrite eqh1. assumption.
  assert (exo: exists O4', oplus O4' O2 O'' /\ oplus O4 O' O4').
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=OPLUS).
  assert (OP4:=op42).
  inversion OP3.
  rewrite <- H in *.
  inversion OP4.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP4.
  exists (Some o').
  split. apply fs_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists None.
  split. apply sn_op. apply Permutation_trans with o; assumption.
  apply None_op.
  rewrite <- H in *.
  inversion OP4.
  exists (Some o').
  split. apply fs_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O4',(op4'2,op4')).
  exists O4', O2, (ghplus C4 g'), C2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists op4'2.
  split.
  apply tmp5 with v1 v2 O'; repeat php_.
  rewrite eqh1. assumption.
  rewrite eqg1. assumption.
  split. assumption.
  split; repeat php_.
  split; repeat php_.
  }

  {
  destruct m'; try reflexivity.
  simpl in *.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  subst.
  specialize tmp1 with v.
  destruct tmp1 as (v0,(v1,(v2,tmp1))).
  exists v0, v1, v2.
  intros.
  assert (phpdef1: phplusdef p1 p' /\ phplusdef p2 p'). repeat php_.
  assert (ghpdef1: ghplusdef C1 g' /\ ghplusdef C2 g'). repeat php_.
  assert (eqp: phplus (phplus p1 p') p2 = phplus (phplus p1 p2) p'). repeat php_.
  assert (eqg: ghplus (ghplus C1 g') C2 = ghplus (ghplus C1 C2) g'). repeat php_.
  exists (phplus p1 p'), p2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqp. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqp. assumption.
  assert (exo: exists O1', oplus O1 O' O1' /\ oplus O1' O2 O'').
  {
  assert (OP1:=opO1O2).
  assert (OP2:=OPLUS).
  inversion OP2.
  rewrite <- H in *.
  inversion OP1.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP1.
  exists (Some o0).
  split. apply fs_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists None.
  split. apply None_op.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP1.
  exists (Some o).
  split. apply sn_oplus.
  apply fs_op. assumption.
  }
  destruct exo as (O1',(opo1',op1'2)).

  exists O1', O2, (ghplus C1 g'), C2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg. assumption.
  exists. repeat php_.
  split.
  apply tmp1 with O'; repeat php_.
  rewrite eqp. assumption.
  rewrite eqg. assumption.
  split. assumption.
  split; repeat php_.
  }

  {
  destruct m'; try reflexivity.
  simpl in *.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  destruct tmp1 as (v,(v0,(v1,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4))))))))))))))))))))).
  subst.
  exists v, v0, v1.

  assert (phpdef1: phplusdef p3 p2 /\ phplusdef p4 p2). repeat php_.
  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef C4 C2). repeat php_.
  assert (eqh: phplus (phplus p4 p2) p3 = phplus (phplus p3 p4) p2).
  rewrite phplus_comm; repeat php_.
  assert (eqg: ghplus (ghplus C4 C2) C3 = ghplus (ghplus C3 C4) C2).
  rewrite ghplus_comm; repeat php_.
  exists p3, (phplus p4 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh. assumption.
  exists. rewrite <- phplus_assoc; repeat php_.
  assert (exo: exists O42, oplus O4 O2 O42 /\ oplus O3 O42 O).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  inversion OP1.
  rewrite <- H in OP2.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in OP2.
  inversion OP2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply fs_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in OP2.
  inversion OP2.
  exists (Some o).
  split. apply sn_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O42,(op42,op342)).
  exists O3, O42, C3, (ghplus C4 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg. assumption.
  exists. repeat php_. rewrite <- ghplus_assoc; repeat php_.
  exists op342.
  split. assumption.
  split.
  intros.
  assert (phpdef2: phplusdef p4 p' /\ phplusdef p2 p'). repeat php_.
  assert (ghpdef2: ghplusdef C4 g' /\ ghplusdef C2 g'). repeat php_.
  assert (eqh1: phplus (phplus p4 p') p2 = phplus (phplus p4 p2) p').
  rewrite phplus_comm; try assumption. rewrite <- phplus_assoc; repeat php_. repeat php_.
  assert (eqg1: ghplus (ghplus C4 g') C2 = ghplus (ghplus C4 C2) g').
  rewrite ghplus_comm; try assumption. rewrite <- ghplus_assoc; repeat php_. repeat php_.
  exists (phplus p4 p'), p2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh1. assumption.
  exists. repeat php_.
  exists. rewrite eqh1. assumption.
  assert (exo: exists O4', oplus O4' O2 O'' /\ oplus O4 O' O4').
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=OPLUS).
  assert (OP4:=op42).
  inversion OP3.
  rewrite <- H in *.
  inversion OP4.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP4.
  exists (Some o').
  split. apply fs_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists None.
  split. apply sn_op. apply Permutation_trans with o; assumption.
  apply None_op.
  rewrite <- H in *.
  inversion OP4.
  exists (Some o').
  split. apply fs_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O4',(op4'2,op4')).
  exists O4', O2, (ghplus C4 g'), C2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists op4'2.
  split.
  apply tmp5 with v2 v3 O'; repeat php_.
  rewrite eqh1. assumption.
  rewrite eqg1. assumption.
  split. assumption.
  split; repeat php_.
  split; repeat php_.
  }

  {
  destruct m'; try reflexivity.
  simpl in *.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  destruct tmp1 as (v,(v0,(v1,(v2,(v3,(eql,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4)))))))))))))))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp8,(tmp6,(p5p6,c56)))))))))))))))))).
  destruct tmp6 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(tmp7,(tmp9, (p7p8,C7C8)))))))))))))))))).
  destruct tmp9 as (p9,(p0,(phpdefp9p0,(bp9,(bp0,(bp90,(o9,(o0,(C9,(C0,(ghpdefC9C0,(BC9,(BC0,(BC9C0,(opo9o0,(tmp110,(tmp18,(p9p0,C9C0)))))))))))))))))).
  subst.
  exists v, v0, v1, v2, v3.
  split. assumption.

  assert (os: o0 = None /\ O7 = None /\ O5 = None /\ O3 = None /\ O2 = None /\ 
    (exists o (P: Permutation (map evalol ((if ltb 0 (v0 ([[Aof v3]])) then (M'of v3) else nil) ++ v)) o), o9 = Some o) /\
    (exists o (P: Permutation (map evalol ((if ltb 0 (v0 ([[Aof v3]])) then (M'of v3) else nil) ++ v)) o), O8 = Some o) /\
    (exists o (P: Permutation (map evalol ((if ltb 0 (v0 ([[Aof v3]])) then (M'of v3) else nil) ++ v)) o), O6 = Some o) /\
    (exists o (P: Permutation (map evalol ((if ltb 0 (v0 ([[Aof v3]])) then (M'of v3) else nil) ++ v)) o), O4 = Some o) /\
    (exists o (P: Permutation (map evalol ((if ltb 0 (v0 ([[Aof v3]])) then (M'of v3) else nil) ++ v)) o), O1 = Some o) /\
    (exists o (P: Permutation (map evalol ((if ltb 0 (v0 ([[Aof v3]])) then (M'of v3) else nil) ++ v)) o), O = Some o)).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  assert (OP5:=opo9o0).
  assert (OP6:=tmp110).
  inversion OP6.
  rewrite <- H1 in *.
  inversion OP5.
  rewrite <- H4 in *.
  inversion OP4.
  rewrite <- H5 in *.
  inversion OP3.
  rewrite <- H8 in *.
  inversion OP2.
  rewrite <- H11 in *.
  inversion OP1.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  split. exists o'. exists PERM. reflexivity.
  split. exists o'0. exists. apply Permutation_trans with o'; assumption. reflexivity.
  split. exists o'1. exists. apply Permutation_trans with o'; try assumption.
    apply Permutation_trans with o'0; try assumption. reflexivity.
  split. exists o'2. exists. apply Permutation_trans with o'; try assumption.
    apply Permutation_trans with o'0; try assumption.
    apply Permutation_trans with o'1; try assumption. reflexivity.
  split. exists o'3. exists. apply Permutation_trans with o'; try assumption.
    apply Permutation_trans with o'0; try assumption.
    apply Permutation_trans with o'1; try assumption.
    apply Permutation_trans with o'2; try assumption. reflexivity.
  exists o'4. exists. apply Permutation_trans with o'; try assumption.
    apply Permutation_trans with o'0; try assumption.
    apply Permutation_trans with o'1; try assumption.
    apply Permutation_trans with o'2; try assumption.
    apply Permutation_trans with o'3; try assumption. reflexivity.
  }
  destruct os as (o0n,(o7n,(o5n,(o3n,(o2n,((i1,(r1,e1)),((i2,(r2,e2)),((i3,(r3,e3)),((i4,(r4,e4)),((i5,(r5,e5)),(i6,(r6,e6)))))))))))).
  subst.

  assert (phpdef1: phplusdef p3 p2 /\ phplusdef (phplus p5 (phplus p7 (phplus p9 p0))) p2). repeat php_.
  assert (phpdef2: phplusdef p5 p2 /\ phplusdef (phplus p7 (phplus p9 p0)) p2). repeat php_.
  assert (phpdef3: phplusdef p7 p2 /\ phplusdef (phplus p9 p0) p2). repeat php_.
  assert (phpdef4: phplusdef p9 p2 /\ phplusdef p0 p2). repeat php_.
  assert (phpdef5: phplusdef p3 p5 /\ phplusdef p3 (phplus p7 (phplus p9 p0))). repeat php_.
  assert (phpdef6: phplusdef p3 p7 /\ phplusdef p3 (phplus p9 p0)). repeat php_.
  assert (phpdef7: phplusdef p3 p9 /\ phplusdef p3 p0). repeat php_.
  assert (phpdef8: phplusdef p7 p9 /\ phplusdef p7 p0). repeat php_.
  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef (ghplus C5 (ghplus C7 (ghplus C9 C0))) C2). repeat php_.
  assert (ghpdef2: ghplusdef C5 C2 /\ ghplusdef (ghplus C7 (ghplus C9 C0)) C2). repeat php_.
  assert (ghpdef3: ghplusdef C7 C2 /\ ghplusdef (ghplus C9 C0) C2). repeat php_.
  assert (ghpdef4: ghplusdef C9 C2 /\ ghplusdef C0 C2). repeat php_.
  assert (ghpdef5: ghplusdef C3 C5 /\ ghplusdef C3 (ghplus C7 (ghplus C9 C0))). repeat php_.
  assert (ghpdef6: ghplusdef C3 C7 /\ ghplusdef C3 (ghplus C9 C0)). repeat php_.
  assert (ghpdef7: ghplusdef C3 C9 /\ ghplusdef C3 C0). repeat php_.
  assert (ghpdef8: ghplusdef C7 C9 /\ ghplusdef C7 C0). repeat php_.
  assert (eqp: phplus (phplus p2 (phplus p5 (phplus p7 (phplus p9 p0)))) p3 =
    phplus (phplus p3 (phplus p5 (phplus p7 (phplus p9 p0)))) p2). repeat php_.
  assert (eqg: ghplus (ghplus C2 (ghplus C5 (ghplus C7 (ghplus C9 C0)))) C3 =
    ghplus (ghplus C3 (ghplus C5 (ghplus C7 (ghplus C9 C0)))) C2). repeat php_.

  exists p3, (phplus p2 (phplus p5 (phplus p7 (phplus p9 p0)))).
  exists. repeat php_. 
  exists. repeat php_. 
  exists. repeat php_.
  apply boundph_mon with p3; repeat php_. rewrite eqp. assumption.
  exists. repeat php_. rewrite phplus_comm; repeat php_. rewrite eqp. assumption.
  exists None, (Some i6), C3, (ghplus C2 (ghplus C5 (ghplus C7 (ghplus C9 C0)))).
  exists. repeat php_. 
  exists. repeat php_. 
  exists. repeat php_.
  apply boundgh_mon with C3; repeat php_. rewrite eqg. assumption.
  exists. repeat php_. rewrite ghplus_comm; repeat php_. rewrite eqg. assumption.
  exists. apply sn_oplus.
  split. assumption.
  split.
  assert (eqp2: phplus p5 (phplus p2 (phplus p7 (phplus p9 p0))) =
    phplus (phplus p5 (phplus p7 (phplus p9 p0))) p2). repeat php_.
  assert (eqp3: phplus (phplus (phplus p5 (phplus p7 (phplus p9 p0))) p2) p3 =
    phplus (phplus p3 (phplus p5 (phplus p7 (phplus p9 p0)))) p2).
  rewrite <- eqp2.
  rewrite phplus_comm; repeat php_.
  assert (eqg2: ghplus C5 (ghplus C2 (ghplus C7 (ghplus C9 C0))) =
    ghplus (ghplus C5 (ghplus C7 (ghplus C9 C0))) C2). repeat php_.
  assert (eqg3: ghplus (ghplus (ghplus C5 (ghplus C7 (ghplus C9 C0))) C2) C3 =
    ghplus (ghplus C3 (ghplus C5 (ghplus C7 (ghplus C9 C0)))) C2).
  rewrite <- eqg2.
  rewrite ghplus_comm; repeat php_.

  assert (bp52790: boundph (phplus p5 (phplus p2 (phplus p7 (phplus p9 p0))))).
  {
  rewrite eqp2.
  apply boundph_mon with p3; repeat php_.
  rewrite eqp3. assumption.
  }

  assert (bg52790: boundgh (ghplus C5 (ghplus C2 (ghplus C7 (ghplus C9 C0))))).
  {
  rewrite eqg2.
  apply boundgh_mon with C3; repeat php_.
  rewrite eqg3. assumption.
  }

  exists p5, (phplus p2 (phplus p7 (phplus p9 p0))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, (Some i6), C5, (ghplus C2 (ghplus C7 (ghplus C9 C0))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply sn_oplus.
  split. assumption.
  split.

  assert (eqp4: phplus p7 (phplus p2 (phplus p9 p0)) = phplus p2 (phplus p7 (phplus p9 p0))).
  {
  rewrite <- phplus_assoc; try assumption. symmetry.
  rewrite <- phplus_assoc; repeat php_.  repeat php_. repeat php_.
  }
  assert (eqg4: ghplus C7 (ghplus C2 (ghplus C9 C0)) = ghplus C2 (ghplus C7 (ghplus C9 C0))).
  {
  rewrite <- ghplus_assoc; try assumption. symmetry.
  rewrite <- ghplus_assoc; repeat php_.  repeat php_. repeat php_.
  }
  assert (bp7290: boundph (phplus p7 (phplus p2 (phplus p9 p0)))).
  rewrite eqp4.
  apply boundph_mon with p5; repeat php_.
  assert (bgp7290: boundgh (ghplus C7 (ghplus C2 (ghplus C9 C0)))).
  rewrite eqg4.
  apply boundgh_mon with C5; repeat php_.

  exists p7, (phplus p2 (phplus p9 p0)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.

  exists None, (Some i6), C7, (ghplus C2 (ghplus C9 C0)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply sn_oplus.
  split. assumption.
  split.

  assert (eqp5: phplus p9 (phplus p2 p0) = phplus p2 (phplus p9 p0)).
  symmetry. rewrite phplus_comm; repeat php_.
  assert (eqg5: ghplus C9 (ghplus C2 C0) = ghplus C2 (ghplus C9 C0)).
  symmetry. rewrite ghplus_comm; repeat php_.
  assert (bp920: boundph (phplus p9 (phplus p2 p0))).
  rewrite eqp5.
  apply boundph_mon with p7; repeat php_.
  assert (bg920: boundgh (ghplus C9 (ghplus C2 C0))).
  rewrite eqg5.
  apply boundgh_mon with C7; repeat php_.

  exists p9, (phplus p2 p0).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.

  exists (Some i6), None, C9, (ghplus C2 C0).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply fs_oplus.
  split.
  apply fs_op. assumption.
  split.
  intros.
  assert (phpdef9: phplusdef p2 p' /\ phplusdef p0 p'). repeat php_.
  assert (ghpdef9: ghplusdef C2 g' /\ ghplusdef C0 g'). repeat php_.
  assert (eqp7: phplus (phplus p0 p') p2 = phplus (phplus p2 p0) p').
  rewrite phplus_comm; repeat php_.
  assert (eqg7: ghplus (ghplus C0 g') C2 = ghplus (ghplus C2 C0) g').
  rewrite ghplus_comm; repeat php_.

  exists (phplus p0 p'), p2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqp7. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqp7. assumption.

  exists O', None, (ghplus C0 g'), C2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg7. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg7. assumption.
  exists. apply oplus_comm; assumption.
  split.
  apply tmp18 with O'; repeat php_.
  rewrite eqp7. assumption.
  rewrite eqg7. assumption.
  apply sn_oplus.
  split. assumption.
  split; repeat php_.
  split; repeat php_.
  split; repeat php_.
  split. rewrite eqp2. repeat php_.
  rewrite eqg2. repeat php_.
  split; repeat php_.
  }

  {
  destruct m'; try reflexivity.
  simpl in *.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  destruct tmp1 as (v,(v0,(v1,(v2,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4)))))))))))))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp8,(tmp6,(p5p6,c56)))))))))))))))))).
  destruct tmp6 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(tmp7,(tmp9, (p7p8,C7C8)))))))))))))))))).
  subst.
  exists v, v0, v1, v2.

  assert (phpdef1: phplusdef p3 p2 /\ phplusdef (phplus p5 (phplus p7 p8)) p2). repeat php_.
  assert (phpdef2: phplusdef p5 p2 /\ phplusdef (phplus p7 p8) p2). repeat php_.
  assert (phpdef3: phplusdef p7 p2 /\ phplusdef p8 p2). repeat php_.
  assert (phpdef4: phplusdef p3 p5 /\ phplusdef p3 (phplus p7 p8)). repeat php_.
  assert (phpdef5: phplusdef p3 p7 /\ phplusdef p3 p8). repeat php_.
  assert (phpdef6: phplusdef p5 p7 /\ phplusdef p5 p8). repeat php_.

  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef (ghplus C5 (ghplus C7 C8)) C2). repeat php_.
  assert (ghpdef2: ghplusdef C5 C2 /\ ghplusdef (ghplus C7 C8) C2). repeat php_.
  assert (ghpdef3: ghplusdef C7 C2 /\ ghplusdef C8 C2). repeat php_.
  assert (ghpdef4: ghplusdef C3 C5 /\ ghplusdef C3 (ghplus C7 C8)). repeat php_.
  assert (ghpdef5: ghplusdef C3 C7 /\ ghplusdef C3 C8). repeat php_.
  assert (ghpdef6: ghplusdef C5 C7 /\ ghplusdef C5 C8). repeat php_.

  assert (eqh1: phplus p3 (phplus p5 (phplus p7 (phplus p8 p2))) =
    phplus (phplus p3 (phplus p5 (phplus p7 p8))) p2). repeat php_.
  assert (eqh2: phplus p5 (phplus p7 (phplus p8 p2)) = phplus p2 (phplus p5 (phplus p7 p8))).
    symmetry. rewrite phplus_comm; repeat php_.
  assert (eqh3: phplus (phplus p2 (phplus p5 (phplus p7 p8))) p3 =
    phplus (phplus p3 (phplus p5 (phplus p7 p8))) p2).
    rewrite phplus_assoc; repeat php_.
  assert (eqg1: ghplus C3 (ghplus C5 (ghplus C7 (ghplus C8 C2))) =
    ghplus (ghplus C3 (ghplus C5 (ghplus C7 C8))) C2). repeat php_.
  assert (eqg2: ghplus C5 (ghplus C7 (ghplus C8 C2)) = ghplus C2 (ghplus C5 (ghplus C7 C8))).
    symmetry. rewrite ghplus_comm; repeat php_.
  assert (eqg3: ghplus (ghplus C2 (ghplus C5 (ghplus C7 C8))) C3 =
    ghplus (ghplus C3 (ghplus C5 (ghplus C7 C8))) C2).
    rewrite ghplus_assoc; repeat php_.

  assert (b35782: boundph (phplus p3 (phplus p5 (phplus p7 (phplus p8 p2))))).
    rewrite eqh1. assumption.
  assert (b5782: boundph (phplus p5 (phplus p7 (phplus p8 p2)))).
    rewrite eqh2.
    apply boundph_mon with p3; repeat php_.
    rewrite eqh3. assumption.

  assert (bg35782: boundgh (ghplus C3 (ghplus C5 (ghplus C7 (ghplus C8 C2))))).
    rewrite eqg1. assumption.
  assert (bg5782: boundgh (ghplus C5 (ghplus C7 (ghplus C8 C2)))).
    rewrite eqg2.
    apply boundgh_mon with C3; repeat php_.
    rewrite eqg3. assumption.
  exists p3, (phplus p5 (phplus p7 (phplus p8 p2))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O24, oplus O2 O4 O24 /\ oplus O3 O24 O).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  inversion OP1.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP2.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O24,(op24,op324)).
  exists O3, O24, C3, (ghplus C5 (ghplus C7 (ghplus C8 C2))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split. assumption.
  split.

  assert (eqh4: phplus (phplus (phplus p7 p8) p2) p5 = phplus p5 (phplus p7 (phplus p8 p2))). repeat php_.
  assert (eqg4: ghplus (ghplus (ghplus C7 C8) C2) C5 = ghplus C5 (ghplus C7 (ghplus C8 C2))). repeat php_.

  assert (bp5782: boundph (phplus p5 (phplus p7 (phplus p8 p2)))). repeat php_.
  assert (bgp5782: boundgh (ghplus C5 (ghplus C7 (ghplus C8 C2)))). repeat php_.
  assert (bp782: boundph (phplus p7 (phplus p8 p2))).
  rewrite <- phplus_assoc; repeat php_. apply boundph_mon with p5; repeat php_.
  rewrite eqh4. assumption.
  assert (bgp782: boundgh (ghplus C7 (ghplus C8 C2))).
  rewrite <- ghplus_assoc; repeat php_. apply boundgh_mon with C5; repeat php_.
  rewrite eqg4. assumption.

  exists p5, (phplus p7 (phplus p8 p2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O26, oplus O2 O6 O26 /\ oplus O5 O26 O24).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  assert (OP5:=op24).
  inversion OP5.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split; apply None_op.
  rewrite <- H0 in *.
  inversion OP3.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  }
  destruct exo as (O26,(op26,op526)).

  exists O5, O26, C5, (ghplus C7 (ghplus C8 C2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.

  exists p7, (phplus p8 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O28, oplus O2 O8 O28 /\ oplus O7 O28 O26).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  assert (OP5:=op24).
  inversion op26.
  rewrite <- H0 in *.
  inversion OP4.
  exists None.
  split; apply None_op.
  rewrite <- H0 in *.
  inversion OP4.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  rewrite <- H0 in *.
  inversion OP4.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  }
  destruct exo as (O28,(op28,op728)).
  exists O7, O28, C7, (ghplus C8 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split.
  intros.
  destruct SAT as (p9,(p0,(phpdefp9p0,(bp9,(bp0,(bp90,(o9,(o0,(C9,(C0,(ghpdefC9C0,(BC9,(BC0,(BC9C0,(opo9o0,(tmp110,(tmp18,(p9p0,C9C0)))))))))))))))))).
  subst.
  assert (phpdef7: phplusdef p8 (phplus p9 p0) /\ phplusdef p2 (phplus p9 p0)). repeat php_.
  assert (phpdef9: phplusdef p8 p9 /\ phplusdef p8 p0). repeat php_.
  assert (phpdef10: phplusdef p2 p9 /\ phplusdef p2 p0). repeat php_.
  assert (ghpdef7: ghplusdef C8 (ghplus C9 C0) /\ ghplusdef C2 (ghplus C9 C0)). repeat php_.
  assert (ghpdef9: ghplusdef C8 C9 /\ ghplusdef C8 C0). repeat php_.
  assert (ghpdef10: ghplusdef C2 C9 /\ ghplusdef C2 C0). repeat php_.

  assert (eqh7: phplus (phplus p8 (phplus p9 p0)) p2 = 
    phplus (phplus p8 p2) (phplus p9 p0)).
    rewrite phplus_comm; repeat php_.
    rewrite <- phplus_assoc; try assumption. symmetry.
    rewrite <- phplus_assoc; try assumption.
    replace (phplus p8 p2) with (phplus p2 p8); repeat php_.
    repeat php_.
  assert (eqg7: ghplus (ghplus C8 (ghplus C9 C0)) C2 = 
    ghplus (ghplus C8 C2) (ghplus C9 C0)).
    rewrite ghplus_comm; repeat php_.
    rewrite <- ghplus_assoc; try assumption. symmetry.
    rewrite <- ghplus_assoc; try assumption.
    replace (ghplus C8 C2) with (ghplus C2 C8); repeat php_.
    repeat php_.

  exists (phplus p8 (phplus p9 p0)), p2.
  exists. repeat php_.
  exists. apply boundph_mon with p2; repeat php_. rewrite eqh7. assumption.
  exists. repeat php_.
  exists. rewrite eqh7. assumption.
  assert (exo: exists O'8, oplus O' O8 O'8 /\ oplus O'8 O2 O'').
  {
  assert (OP1:=op28).
  assert (OP2:=OPLUS).
  inversion OPLUS.
  rewrite <- H in *.
  inversion OP1.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP1.
  exists None.
  split. apply None_op.
  apply sn_op. apply Permutation_trans with o; assumption.
  exists (Some o1).
  split. apply sn_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP1.
  exists (Some o).
  split. apply fs_oplus.
  apply fs_op. assumption.
  }
  destruct exo as (O'8,(op'8,opd28)).
  exists O'8, O2, (ghplus C8 (ghplus C9 C0)), C2.
  exists. repeat php_.
  exists. apply boundgh_mon with C2; repeat php_. rewrite eqg7. assumption.
  exists. repeat php_.
  exists. rewrite eqg7. assumption.
  exists. repeat php_.
  split.
  apply tmp9 with O'; repeat php_.
  rewrite eqh7. assumption.
  rewrite eqg7. assumption.
  apply oplus_comm; assumption.
  exists p9, p0.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists o9, o0, C9, C0.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  split. assumption.
  split. assumption.
  split; reflexivity.
  split. assumption.
  split; repeat php_.
  split; reflexivity.
  split; reflexivity.
  split; repeat php_.
  }

  {
  destruct m'; try reflexivity.
  simpl in *.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  destruct tmp1 as (v0,(v1,(v2,(eql,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4)))))))))))))))))))))).
  subst.
  exists v0, v1, v2.
  split. assumption.

  assert (phpdef1: phplusdef p3 p2 /\ phplusdef p4 p2). repeat php_.
  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef C4 C2). repeat php_.
  assert (eqh: phplus (phplus p4 p2) p3 = phplus (phplus p3 p4) p2).
  rewrite phplus_comm; repeat php_.
  assert (eqg: ghplus (ghplus C4 C2) C3 = ghplus (ghplus C3 C4) C2).
  rewrite ghplus_comm; repeat php_.
  exists p3, (phplus p4 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh. assumption.
  exists. rewrite <- phplus_assoc; repeat php_.
  assert (exo: exists O42, oplus O4 O2 O42 /\ oplus O3 O42 O).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  inversion OP1.
  rewrite <- H in OP2.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in OP2.
  inversion OP2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply fs_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in OP2.
  inversion OP2.
  exists (Some o).
  split. apply sn_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O42,(op42,op342)).
  exists O3, O42, C3, (ghplus C4 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg. assumption.
  exists. repeat php_. rewrite <- ghplus_assoc; repeat php_.
  exists op342.
  split. assumption.
  split.
  intros.
  assert (phpdef2: phplusdef p4 p' /\ phplusdef p2 p'). repeat php_.
  assert (ghpdef2: ghplusdef C4 g' /\ ghplusdef C2 g'). repeat php_.
  assert (eqh1: phplus (phplus p4 p') p2 = phplus (phplus p4 p2) p').
  rewrite phplus_comm; try assumption. rewrite <- phplus_assoc; repeat php_. repeat php_.
  assert (eqg1: ghplus (ghplus C4 g') C2 = ghplus (ghplus C4 C2) g').
  rewrite ghplus_comm; try assumption. rewrite <- ghplus_assoc; repeat php_. repeat php_.
  exists (phplus p4 p'), p2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh1. assumption.
  exists. repeat php_.
  exists. rewrite eqh1. assumption.
  assert (exo: exists O4', oplus O4' O2 O'' /\ oplus O4 O' O4').
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=OPLUS).
  assert (OP4:=op42).
  inversion OP3.
  rewrite <- H in *.
  inversion OP4.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP4.
  exists (Some o').
  split. apply fs_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists None.
  split. apply sn_op. apply Permutation_trans with o; assumption.
  apply None_op.
  rewrite <- H in *.
  inversion OP4.
  exists (Some o').
  split. apply fs_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O4',(op4'2,op4')).
  exists O4', O2, (ghplus C4 g'), C2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists op4'2.
  split.
  apply tmp5 with v3 v4 O'; repeat php_.
  rewrite eqh1. assumption.
  rewrite eqg1. assumption.
  split. assumption.
  split; repeat php_.
  split; repeat php_.
  }

  {
  destruct m'; try reflexivity.
  simpl in *.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  destruct tmp1 as (v0,(v1,(v2,(eql,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4)))))))))))))))))))))).
  subst.
  exists v0, v1, v2.
  split. assumption.

  assert (phpdef1: phplusdef p3 p2 /\ phplusdef p4 p2). repeat php_.
  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef C4 C2). repeat php_.
  assert (eqh: phplus (phplus p4 p2) p3 = phplus (phplus p3 p4) p2).
  rewrite phplus_comm; repeat php_.
  assert (eqg: ghplus (ghplus C4 C2) C3 = ghplus (ghplus C3 C4) C2).
  rewrite ghplus_comm; repeat php_.
  exists p3, (phplus p4 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh. assumption.
  exists. rewrite <- phplus_assoc; repeat php_.
  assert (exo: exists O42, oplus O4 O2 O42 /\ oplus O3 O42 O).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  inversion OP1.
  rewrite <- H in OP2.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in OP2.
  inversion OP2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply fs_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in OP2.
  inversion OP2.
  exists (Some o).
  split. apply sn_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O42,(op42,op342)).
  exists O3, O42, C3, (ghplus C4 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg. assumption.
  exists. repeat php_. rewrite <- ghplus_assoc; repeat php_.
  exists op342.
  split. assumption.
  split.
  intros.
  assert (phpdef2: phplusdef p4 p' /\ phplusdef p2 p'). repeat php_.
  assert (ghpdef2: ghplusdef C4 g' /\ ghplusdef C2 g'). repeat php_.
  assert (eqh1: phplus (phplus p4 p') p2 = phplus (phplus p4 p2) p').
  rewrite phplus_comm; try assumption. rewrite <- phplus_assoc; repeat php_. repeat php_.
  assert (eqg1: ghplus (ghplus C4 g') C2 = ghplus (ghplus C4 C2) g').
  rewrite ghplus_comm; try assumption. rewrite <- ghplus_assoc; repeat php_. repeat php_.
  exists (phplus p4 p'), p2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh1. assumption.
  exists. repeat php_.
  exists. rewrite eqh1. assumption.
  assert (exo: exists O4', oplus O4' O2 O'' /\ oplus O4 O' O4').
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=OPLUS).
  assert (OP4:=op42).
  inversion OP3.
  rewrite <- H in *.
  inversion OP4.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP4.
  exists (Some o').
  split. apply fs_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists None.
  split. apply sn_op. apply Permutation_trans with o; assumption.
  apply None_op.
  rewrite <- H in *.
  inversion OP4.
  exists (Some o').
  split. apply fs_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O4',(op4'2,op4')).
  exists O4', O2, (ghplus C4 g'), C2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists op4'2.
  split.
  apply tmp5 with v3 v4 O'; repeat php_.
  rewrite eqh1. assumption.
  rewrite eqg1. assumption.
  split. assumption.
  split; repeat php_.
  split; repeat php_.
  }

  {
  destruct m'; try reflexivity.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  destruct tmp1 as [SAT|g_chrgu].
  destruct SAT as [SAT|g_chrg].
  destruct SAT as [SAT|g_dischu].
  destruct SAT as [SAT|g_disch].
  destruct SAT as [SAT|g_ctrinc].
  destruct SAT as [SAT|g_ctrdec].
  destruct SAT as [SAT|g_newctr].
  destruct SAT as [SAT|g_finlc].
  destruct SAT as [SAT|g_initc].
  destruct SAT as [nop|g_initl].
  {
  left. left. left. left. left. left. left. left. left. left.
  simpl in *.
  intros.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2, C1, C2, ghpdefC1C2, BC1, BC2, bc12,opO1O2.
  split. apply nop.
  split; try assumption.
  split; try assumption.
  }

  {
  left. left. left. left. left. left. left. left. left. right.
  simpl in *.
  intros.
  destruct g_initl as (v,(v0,(v1,(v2,(v3,(v4,(v5,(eql,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4)))))))))))))))))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp8,(tmp6,(p5p6,c56)))))))))))))))))).
  destruct tmp6 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(tmp7,(tmp9, (p7p8,C7C8)))))))))))))))))).
  subst.
  exists v, v0, v1, v2, v3, v4, v5.
  split. assumption.

  assert (phpdef1: phplusdef p3 p2 /\ phplusdef (phplus p5 (phplus p7 p8)) p2). repeat php_.
  assert (phpdef2: phplusdef p5 p2 /\ phplusdef (phplus p7 p8) p2). repeat php_.
  assert (phpdef3: phplusdef p7 p2 /\ phplusdef p8 p2). repeat php_.
  assert (phpdef4: phplusdef p3 p5 /\ phplusdef p3 (phplus p7 p8)). repeat php_.
  assert (phpdef5: phplusdef p3 p7 /\ phplusdef p3 p8). repeat php_.
  assert (phpdef6: phplusdef p5 p7 /\ phplusdef p5 p8). repeat php_.

  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef (ghplus C5 (ghplus C7 C8)) C2). repeat php_.
  assert (ghpdef2: ghplusdef C5 C2 /\ ghplusdef (ghplus C7 C8) C2). repeat php_.
  assert (ghpdef3: ghplusdef C7 C2 /\ ghplusdef C8 C2). repeat php_.
  assert (ghpdef4: ghplusdef C3 C5 /\ ghplusdef C3 (ghplus C7 C8)). repeat php_.
  assert (ghpdef5: ghplusdef C3 C7 /\ ghplusdef C3 C8). repeat php_.
  assert (ghpdef6: ghplusdef C5 C7 /\ ghplusdef C5 C8). repeat php_.

  assert (eqh1: phplus p3 (phplus p5 (phplus p7 (phplus p8 p2))) =
    phplus (phplus p3 (phplus p5 (phplus p7 p8))) p2). repeat php_.
  assert (eqh2: phplus p5 (phplus p7 (phplus p8 p2)) = phplus p2 (phplus p5 (phplus p7 p8))).
    symmetry. rewrite phplus_comm; repeat php_.
  assert (eqh3: phplus (phplus p2 (phplus p5 (phplus p7 p8))) p3 =
    phplus (phplus p3 (phplus p5 (phplus p7 p8))) p2).
    rewrite phplus_assoc; repeat php_.
  assert (eqg1: ghplus C3 (ghplus C5 (ghplus C7 (ghplus C8 C2))) =
    ghplus (ghplus C3 (ghplus C5 (ghplus C7 C8))) C2). repeat php_.
  assert (eqg2: ghplus C5 (ghplus C7 (ghplus C8 C2)) = ghplus C2 (ghplus C5 (ghplus C7 C8))).
    symmetry. rewrite ghplus_comm; repeat php_.
  assert (eqg3: ghplus (ghplus C2 (ghplus C5 (ghplus C7 C8))) C3 =
    ghplus (ghplus C3 (ghplus C5 (ghplus C7 C8))) C2).
    rewrite ghplus_assoc; repeat php_.

  assert (b35782: boundph (phplus p3 (phplus p5 (phplus p7 (phplus p8 p2))))).
    rewrite eqh1. assumption.
  assert (b5782: boundph (phplus p5 (phplus p7 (phplus p8 p2)))).
    rewrite eqh2.
    apply boundph_mon with p3; repeat php_.
    rewrite eqh3. assumption.

  assert (bg35782: boundgh (ghplus C3 (ghplus C5 (ghplus C7 (ghplus C8 C2))))).
    rewrite eqg1. assumption.
  assert (bg5782: boundgh (ghplus C5 (ghplus C7 (ghplus C8 C2)))).
    rewrite eqg2.
    apply boundgh_mon with C3; repeat php_.
    rewrite eqg3. assumption.
  exists p3, (phplus p5 (phplus p7 (phplus p8 p2))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O24, oplus O2 O4 O24 /\ oplus O3 O24 O).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  inversion OP1.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP2.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O24,(op24,op324)).
  exists O3, O24, C3, (ghplus C5 (ghplus C7 (ghplus C8 C2))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split. assumption.
  split.

  assert (eqh4: phplus (phplus (phplus p7 p8) p2) p5 = phplus p5 (phplus p7 (phplus p8 p2))). repeat php_.
  assert (eqg4: ghplus (ghplus (ghplus C7 C8) C2) C5 = ghplus C5 (ghplus C7 (ghplus C8 C2))). repeat php_.

  assert (bp5782: boundph (phplus p5 (phplus p7 (phplus p8 p2)))). repeat php_.
  assert (bgp5782: boundgh (ghplus C5 (ghplus C7 (ghplus C8 C2)))). repeat php_.
  assert (bp782: boundph (phplus p7 (phplus p8 p2))).
  rewrite <- phplus_assoc; repeat php_. apply boundph_mon with p5; repeat php_.
  rewrite eqh4. assumption.
  assert (bgp782: boundgh (ghplus C7 (ghplus C8 C2))).
  rewrite <- ghplus_assoc; repeat php_. apply boundgh_mon with C5; repeat php_.
  rewrite eqg4. assumption.

  exists p5, (phplus p7 (phplus p8 p2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O26, oplus O2 O6 O26 /\ oplus O5 O26 O24).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  assert (OP5:=op24).
  inversion OP5.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split; apply None_op.
  rewrite <- H0 in *.
  inversion OP3.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  }
  destruct exo as (O26,(op26,op526)).

  exists O5, O26, C5, (ghplus C7 (ghplus C8 C2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.

  exists p7, (phplus p8 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O28, oplus O2 O8 O28 /\ oplus O7 O28 O26).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  assert (OP5:=op24).
  inversion op26.
  rewrite <- H0 in *.
  inversion OP4.
  exists None.
  split; apply None_op.
  rewrite <- H0 in *.
  inversion OP4.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  rewrite <- H0 in *.
  inversion OP4.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  }
  destruct exo as (O28,(op28,op728)).
  exists O7, O28, C7, (ghplus C8 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split.
  intros.
  destruct SAT as (p9,(p0,(phpdefp9p0,(bp9,(bp0,(bp90,(o9,(o0,(C9,(C0,(ghpdefC9C0,(BC9,(BC0,(BC9C0,(opo9o0,(tmp110,(tmp18,(p9p0,C9C0)))))))))))))))))).
  subst.
  assert (phpdef7: phplusdef p8 (phplus p9 p0) /\ phplusdef p2 (phplus p9 p0)). repeat php_.
  assert (phpdef9: phplusdef p8 p9 /\ phplusdef p8 p0). repeat php_.
  assert (phpdef10: phplusdef p2 p9 /\ phplusdef p2 p0). repeat php_.
  assert (ghpdef7: ghplusdef C8 (ghplus C9 C0) /\ ghplusdef C2 (ghplus C9 C0)). repeat php_.
  assert (ghpdef9: ghplusdef C8 C9 /\ ghplusdef C8 C0). repeat php_.
  assert (ghpdef10: ghplusdef C2 C9 /\ ghplusdef C2 C0). repeat php_.

  assert (eqh7: phplus (phplus p8 (phplus p9 p0)) p2 = 
    phplus (phplus p8 p2) (phplus p9 p0)).
    rewrite phplus_comm; repeat php_.
    rewrite <- phplus_assoc; try assumption. symmetry.
    rewrite <- phplus_assoc; try assumption.
    replace (phplus p8 p2) with (phplus p2 p8); repeat php_.
    repeat php_.
  assert (eqg7: ghplus (ghplus C8 (ghplus C9 C0)) C2 = 
    ghplus (ghplus C8 C2) (ghplus C9 C0)).
    rewrite ghplus_comm; repeat php_.
    rewrite <- ghplus_assoc; try assumption. symmetry.
    rewrite <- ghplus_assoc; try assumption.
    replace (ghplus C8 C2) with (ghplus C2 C8); repeat php_.
    repeat php_.

  exists (phplus p8 (phplus p9 p0)), p2.
  exists. repeat php_.
  exists. apply boundph_mon with p2; repeat php_. rewrite eqh7. assumption.
  exists. repeat php_.
  exists. rewrite eqh7. assumption.
  assert (exo: exists O'8, oplus O' O8 O'8 /\ oplus O'8 O2 O'').
  {
  assert (OP1:=op28).
  assert (OP2:=OPLUS).
  inversion OPLUS.
  rewrite <- H in *.
  inversion OP1.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP1.
  exists None.
  split. apply None_op.
  apply sn_op. apply Permutation_trans with o; assumption.
  exists (Some o1).
  split. apply sn_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP1.
  exists (Some o).
  split. apply fs_oplus.
  apply fs_op. assumption.
  }
  destruct exo as (O'8,(op'8,opd28)).
  exists O'8, O2, (ghplus C8 (ghplus C9 C0)), C2.
  exists. repeat php_.
  exists. apply boundgh_mon with C2; repeat php_. rewrite eqg7. assumption.
  exists. repeat php_.
  exists. rewrite eqg7. assumption.
  exists. repeat php_.
  split.
  apply tmp9 with O'; repeat php_.
  rewrite eqh7. assumption.
  rewrite eqg7. assumption.
  apply oplus_comm; assumption.
  exists p9, p0.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists o9, o0, C9, C0.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  split. assumption.
  split. assumption.
  split; reflexivity.
  split. assumption.
  split; repeat php_.
  split; reflexivity.
  split; reflexivity.
  split; repeat php_.
  }

  {
  left. left. left. left. left. left. left. left. right.
  simpl in *.
  intros.
  destruct g_initc as (v,(v0,(v1,(v2,(v3,(v4,(v5,(eql,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4)))))))))))))))))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp8,(tmp6,(p5p6,c56)))))))))))))))))).
  subst.
  exists v, v0, v1, v2, v3, v4, v5.
  split. assumption.


  assert (phpdef1: phplusdef p3 p2 /\ phplusdef (phplus p5 p6) p2). repeat php_.
  assert (phpdef2: phplusdef p5 p2 /\ phplusdef p6 p2). repeat php_.
  assert (phpdef3: phplusdef p3 p5 /\ phplusdef p3 p6). repeat php_.
  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef (ghplus C5 C6) C2). repeat php_.
  assert (ghpdef2: ghplusdef C5 C2 /\ ghplusdef C6 C2). repeat php_.
  assert (ghpdef3: ghplusdef C3 C5 /\ ghplusdef C3 C6). repeat php_.

  assert (bp3562: boundph (phplus p3 (phplus p5 (phplus p6 p2)))).
  rewrite phplus_assoc in bp12; repeat php_.
  rewrite phplus_assoc in bp12; repeat php_.
  assert (bp562: boundph (phplus p5 (phplus p6 p2))).
  rewrite <- phplus_assoc; repeat php_.
  rewrite <- phplus_comm; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  assert (bgp3562: boundgh (ghplus C3 (ghplus C5 (ghplus C6 C2)))).
  rewrite ghplus_assoc in bc12; repeat php_.
  rewrite ghplus_assoc in bc12; repeat php_.
  assert (bgp562: boundgh (ghplus C5 (ghplus C6 C2))).
  rewrite <- ghplus_assoc; repeat php_.
  rewrite <- ghplus_comm; repeat php_.
  rewrite <- ghplus_assoc; repeat php_.

  exists p3, (phplus p5 (phplus p6 p2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O42, oplus O2 O4 O42 /\ oplus O3 O42 O).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  inversion OP1.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP2.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O42,(op42,opd228)).
  exists O3, O42, C3, (ghplus C5 (ghplus C6 C2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split.
  exists p5, (phplus p6 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O62, oplus O6 O2 O62 /\ oplus O5 O62 O42).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  inversion op42.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split; apply None_op.
  rewrite <- H0 in *.
  inversion OP3.
  exists (Some o).
  split. apply sn_oplus.
  apply sn_op. assumption.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply fs_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  }
  destruct exo as (O62,(op62,op562)).
  exists O5, O62, C5, (ghplus C6 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split.
  intros.
  destruct SAT as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(tmp7,(tmp9, (p7p8,C7C8)))))))))))))))))).
  subst.
  assert (phpdef4: phplusdef (phplus p6 p2) p7 /\ phplusdef (phplus p6 p2) p8). repeat php_.
  assert (phpdef5: phplusdef p6 p7 /\ phplusdef p2 p7). repeat php_.
  assert (phpdef6: phplusdef p6 p8 /\ phplusdef p2 p8). repeat php_.
  assert (ghpdef4: ghplusdef (ghplus C6 C2) C7 /\ ghplusdef (ghplus C6 C2) C8). repeat php_.
  assert (ghpdef5: ghplusdef C6 C7 /\ ghplusdef C2 C7). repeat php_.
  assert (ghpdef6: ghplusdef C6 C8 /\ ghplusdef C2 C8). repeat php_.
  assert (eqh1: phplus (phplus p6 (phplus p7 p8)) p2 =
    phplus (phplus p6 p2) (phplus p7 p8)).
    rewrite phplus_comm; try assumption.
    rewrite <- phplus_assoc; repeat php_. repeat php_.
  assert (eqg1: ghplus (ghplus C6 (ghplus C7 C8)) C2 =
    ghplus (ghplus C6 C2) (ghplus C7 C8)).
    rewrite ghplus_comm; try assumption.
    rewrite <- ghplus_assoc; repeat php_. repeat php_.

  exists (phplus p6 (phplus p7 p8)), p2.
  exists. repeat php_.
  exists. apply boundph_mon with p2; repeat php_. rewrite eqh1. assumption.
  exists. repeat php_.
  exists. rewrite eqh1. assumption.
  assert (exo: exists O6', oplus O6 O' O6' /\ oplus O6' O2 O'').
  {
  assert (OP1:=op62).
  assert (OP2:=OPLUS).
  inversion OP2.
  rewrite <- H in *.
  inversion OP1.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP1.
  exists (Some o0).
  split. apply fs_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists None.
  split. apply None_op.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP1.
  exists (Some o).
  split. apply sn_oplus.
  apply fs_op. assumption.
  }
  destruct exo as (O6',(op6',op6'2)).

  exists O6', O2, (ghplus C6 (ghplus C7 C8)), C2.
  exists. repeat php_.
  exists. apply boundgh_mon with C2; repeat php_. rewrite eqg1. assumption.
  exists. repeat php_.
  exists. rewrite eqg1. assumption.
  exists. repeat php_.
  split.
  apply tmp6 with O'; repeat php_.
  rewrite eqh1. assumption.
  rewrite eqg1. assumption.
  exists p7, p8.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists O7, O8, C7, C8.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  split. assumption.
  split. assumption.
  split; reflexivity.
  split. assumption.
  split; repeat php_.
  split; reflexivity.
  split; repeat php_.
  }

  {
  left. left. left. left. left. left. left. right.
  simpl in *.
  intros.
  destruct g_finlc as (v,(v0,(v1,(eql,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4)))))))))))))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp8,(tmp6,(p5p6,c56)))))))))))))))))).
  subst.
  exists v, v0, v1.
  split. assumption.

  assert (phpdef1: phplusdef p3 p2 /\ phplusdef (phplus p5 p6) p2). repeat php_.
  assert (phpdef2: phplusdef p5 p2 /\ phplusdef p6 p2). repeat php_.
  assert (phpdef3: phplusdef p3 p5 /\ phplusdef p3 p6). repeat php_.
  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef (ghplus C5 C6) C2). repeat php_.
  assert (ghpdef2: ghplusdef C5 C2 /\ ghplusdef C6 C2). repeat php_.
  assert (ghpdef3: ghplusdef C3 C5 /\ ghplusdef C3 C6). repeat php_.

  assert (bp3562: boundph (phplus p3 (phplus p5 (phplus p6 p2)))).
  rewrite phplus_assoc in bp12; repeat php_.
  rewrite phplus_assoc in bp12; repeat php_.
  assert (bp562: boundph (phplus p5 (phplus p6 p2))).
  rewrite <- phplus_assoc; repeat php_.
  rewrite <- phplus_comm; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  assert (bgp3562: boundgh (ghplus C3 (ghplus C5 (ghplus C6 C2)))).
  rewrite ghplus_assoc in bc12; repeat php_.
  rewrite ghplus_assoc in bc12; repeat php_.
  assert (bgp562: boundgh (ghplus C5 (ghplus C6 C2))).
  rewrite <- ghplus_assoc; repeat php_.
  rewrite <- ghplus_comm; repeat php_.
  rewrite <- ghplus_assoc; repeat php_.

  exists p3, (phplus p5 (phplus p6 p2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O42, oplus O2 O4 O42 /\ oplus O3 O42 O).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  inversion OP1.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP2.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O42,(op42,opd228)).
  exists O3, O42, C3, (ghplus C5 (ghplus C6 C2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split.
  exists p5, (phplus p6 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O62, oplus O6 O2 O62 /\ oplus O5 O62 O42).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  inversion op42.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split; apply None_op.
  rewrite <- H0 in *.
  inversion OP3.
  exists (Some o).
  split. apply sn_oplus.
  apply sn_op. assumption.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply fs_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  }
  destruct exo as (O62,(op62,op562)).
  exists O5, O62, C5, (ghplus C6 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split.
  intros.
  destruct SAT as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(tmp7,(tmp9, (p7p8,C7C8)))))))))))))))))).
  subst.
  assert (phpdef4: phplusdef (phplus p6 p2) p7 /\ phplusdef (phplus p6 p2) p8). repeat php_.
  assert (phpdef5: phplusdef p6 p7 /\ phplusdef p2 p7). repeat php_.
  assert (phpdef6: phplusdef p6 p8 /\ phplusdef p2 p8). repeat php_.
  assert (ghpdef4: ghplusdef (ghplus C6 C2) C7 /\ ghplusdef (ghplus C6 C2) C8). repeat php_.
  assert (ghpdef5: ghplusdef C6 C7 /\ ghplusdef C2 C7). repeat php_.
  assert (ghpdef6: ghplusdef C6 C8 /\ ghplusdef C2 C8). repeat php_.
  assert (eqh1: phplus (phplus p6 (phplus p7 p8)) p2 =
    phplus (phplus p6 p2) (phplus p7 p8)).
    rewrite phplus_comm; try assumption.
    rewrite <- phplus_assoc; repeat php_. repeat php_.
  assert (eqg1: ghplus (ghplus C6 (ghplus C7 C8)) C2 =
    ghplus (ghplus C6 C2) (ghplus C7 C8)).
    rewrite ghplus_comm; try assumption.
    rewrite <- ghplus_assoc; repeat php_. repeat php_.

  exists (phplus p6 (phplus p7 p8)), p2.
  exists. repeat php_.
  exists. apply boundph_mon with p2; repeat php_. rewrite eqh1. assumption.
  exists. repeat php_.
  exists. rewrite eqh1. assumption.
  assert (exo: exists O6', oplus O6 O' O6' /\ oplus O6' O2 O'').
  {
  assert (OP1:=op62).
  assert (OP2:=OPLUS).
  inversion OP2.
  rewrite <- H in *.
  inversion OP1.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP1.
  exists (Some o0).
  split. apply fs_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists None.
  split. apply None_op.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP1.
  exists (Some o).
  split. apply sn_oplus.
  apply fs_op. assumption.
  }
  destruct exo as (O6',(op6',op6'2)).

  exists O6', O2, (ghplus C6 (ghplus C7 C8)), C2.
  exists. repeat php_.
  exists. apply boundgh_mon with C2; repeat php_. rewrite eqg1. assumption.
  exists. repeat php_.
  exists. rewrite eqg1. assumption.
  exists. repeat php_.
  split.
  apply tmp6 with O'; repeat php_.
  rewrite eqh1. assumption.
  rewrite eqg1. assumption.
  exists p7, p8.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists O7, O8, C7, C8.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  split. assumption.
  split. assumption.
  split; reflexivity.
  split. assumption.
  split; repeat php_.
  split; reflexivity.
  split; repeat php_.
  }

  {
  left. left. left. left. left. left. right.
  simpl in *.
  intros.
  subst.
  assert (phpdef1: phplusdef p1 p' /\ phplusdef p2 p'). repeat php_.
  assert (ghpdef1: ghplusdef C1 g' /\ ghplusdef C2 g'). repeat php_.
  assert (eqp: phplus (phplus p1 p') p2 = phplus (phplus p1 p2) p'). repeat php_.
  assert (eqg: ghplus (ghplus C1 g') C2 = ghplus (ghplus C1 C2) g'). repeat php_.
  exists (phplus p1 p'), p2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqp. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqp. assumption.
  assert (exo: exists O1', oplus O1 O' O1' /\ oplus O1' O2 O'').
  {
  assert (OP1:=opO1O2).
  assert (OP2:=OPLUS).
  inversion OP2.
  rewrite <- H in *.
  inversion OP1.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP1.
  exists (Some o0).
  split. apply fs_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists None.
  split. apply None_op.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP1.
  exists (Some o).
  split. apply sn_oplus.
  apply fs_op. assumption.
  }
  destruct exo as (O1',(opo1',op1'2)).

  exists O1', O2, (ghplus C1 g'), C2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg. assumption.
  exists. repeat php_.
  split.
  apply g_newctr with v O'; repeat php_.
  rewrite eqp. assumption.
  rewrite eqg. assumption.
  split. assumption.
  split; repeat php_.
  }

  {
  left. left. left. left. left. right.
  simpl in *.
  intros.
  destruct g_ctrdec as (v,(v1,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4)))))))))))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp8,(tmp6,(p5p6,c56)))))))))))))))))).
  subst.
  exists v, v1.

  assert (phpdef1: phplusdef p3 p2 /\ phplusdef (phplus p5 p6) p2). repeat php_.
  assert (phpdef2: phplusdef p5 p2 /\ phplusdef p6 p2). repeat php_.
  assert (phpdef3: phplusdef p3 p5 /\ phplusdef p3 p6). repeat php_.
  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef (ghplus C5 C6) C2). repeat php_.
  assert (ghpdef2: ghplusdef C5 C2 /\ ghplusdef C6 C2). repeat php_.
  assert (ghpdef3: ghplusdef C3 C5 /\ ghplusdef C3 C6). repeat php_.

  assert (bp3562: boundph (phplus p3 (phplus p5 (phplus p6 p2)))).
  rewrite phplus_assoc in bp12; repeat php_.
  rewrite phplus_assoc in bp12; repeat php_.
  assert (bp562: boundph (phplus p5 (phplus p6 p2))).
  rewrite <- phplus_assoc; repeat php_.
  rewrite <- phplus_comm; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  assert (bgp3562: boundgh (ghplus C3 (ghplus C5 (ghplus C6 C2)))).
  rewrite ghplus_assoc in bc12; repeat php_.
  rewrite ghplus_assoc in bc12; repeat php_.
  assert (bgp562: boundgh (ghplus C5 (ghplus C6 C2))).
  rewrite <- ghplus_assoc; repeat php_.
  rewrite <- ghplus_comm; repeat php_.
  rewrite <- ghplus_assoc; repeat php_.

  exists p3, (phplus p5 (phplus p6 p2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O42, oplus O2 O4 O42 /\ oplus O3 O42 O).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  inversion OP1.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP2.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O42,(op42,opd228)).
  exists O3, O42, C3, (ghplus C5 (ghplus C6 C2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split.
  exists p5, (phplus p6 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O62, oplus O6 O2 O62 /\ oplus O5 O62 O42).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  inversion op42.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split; apply None_op.
  rewrite <- H0 in *.
  inversion OP3.
  exists (Some o).
  split. apply sn_oplus.
  apply sn_op. assumption.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply fs_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  }
  destruct exo as (O62,(op62,op562)).
  exists O5, O62, C5, (ghplus C6 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split.
  intros.

  assert (phpdef4: phplusdef p6 p' /\ phplusdef p2 p'). repeat php_.
  assert (ghpdef4: ghplusdef C6 g' /\ ghplusdef C2 g'). repeat php_.

  assert (eqh2: phplus (phplus p6 p') p2 = phplus (phplus p6 p2) p'). repeat php_.
  assert (eqg2: ghplus (ghplus C6 g') C2 = ghplus (ghplus C6 C2) g'). repeat php_.

  exists (phplus p6 p'), p2.
  exists. repeat php_.
  exists. apply boundph_mon with p2; repeat php_. rewrite eqh2. assumption.
  exists. repeat php_.
  exists. rewrite eqh2. assumption.
  assert (exo: exists O6', oplus O6 O' O6' /\ oplus O6' O2 O'').
  {
  assert (OP1:=OPLUS).
  assert (OP2:=op62).
  inversion OP1.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP2.
  exists (Some o0).
  split. apply fs_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists None.
  split. apply None_op.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP2.
  exists (Some o).
  split. apply sn_oplus.
  apply fs_op. assumption.
  }
  destruct exo as (O6',(op6',opp)).
  exists O6', O2, (ghplus C6 g'), C2.
  exists. repeat php_.
  exists. apply boundgh_mon with C2; repeat php_. rewrite eqg2. assumption.
  exists. repeat php_.
  exists. rewrite eqg2. assumption.
  exists. repeat php_.
  split.
  apply tmp6 with O'; repeat php_.
  rewrite eqh2. assumption.
  rewrite eqg2. assumption.
  split. assumption.
  split; repeat php_.
  split; reflexivity.
  split; repeat php_.
  }

  {
  left. left. left. left. right.
  simpl in *.
  intros.
  destruct g_ctrinc as (v,(v1,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4)))))))))))))))))))).
  subst.
  exists v, v1.

  assert (phpdef1: phplusdef p3 p2 /\ phplusdef p4 p2). repeat php_.
  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef C4 C2). repeat php_.
  assert (eqh: phplus (phplus p4 p2) p3 = phplus (phplus p3 p4) p2).
  rewrite phplus_comm; repeat php_.
  assert (eqg: ghplus (ghplus C4 C2) C3 = ghplus (ghplus C3 C4) C2).
  rewrite ghplus_comm; repeat php_.
  exists p3, (phplus p4 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh. assumption.
  exists. rewrite <- phplus_assoc; repeat php_.
  assert (exo: exists O42, oplus O4 O2 O42 /\ oplus O3 O42 O).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  inversion OP1.
  rewrite <- H in OP2.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in OP2.
  inversion OP2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply fs_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in OP2.
  inversion OP2.
  exists (Some o).
  split. apply sn_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O42,(op42,op342)).
  exists O3, O42, C3, (ghplus C4 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg. assumption.
  exists. repeat php_. rewrite <- ghplus_assoc; repeat php_.
  exists op342.
  split. assumption.
  split.
  intros.
  assert (phpdef2: phplusdef p4 p' /\ phplusdef p2 p'). repeat php_.
  assert (ghpdef2: ghplusdef C4 g' /\ ghplusdef C2 g'). repeat php_.
  assert (eqh1: phplus (phplus p4 p') p2 = phplus (phplus p4 p2) p').
  rewrite phplus_comm; try assumption. rewrite <- phplus_assoc; repeat php_. repeat php_.
  assert (eqg1: ghplus (ghplus C4 g') C2 = ghplus (ghplus C4 C2) g').
  rewrite ghplus_comm; try assumption. rewrite <- ghplus_assoc; repeat php_. repeat php_.
  exists (phplus p4 p'), p2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqh1. assumption.
  exists. repeat php_.
  exists. rewrite eqh1. assumption.
  assert (exo: exists O4', oplus O4' O2 O'' /\ oplus O4 O' O4').
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=OPLUS).
  assert (OP4:=op42).
  inversion OP3.
  rewrite <- H in *.
  inversion OP4.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP4.
  exists (Some o').
  split. apply fs_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists None.
  split. apply sn_op. apply Permutation_trans with o; assumption.
  apply None_op.
  rewrite <- H in *.
  inversion OP4.
  exists (Some o').
  split. apply fs_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O4',(op4'2,op4')).
  exists O4', O2, (ghplus C4 g'), C2.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists. repeat php_.
  exists. repeat php_. rewrite eqg1. assumption.
  exists op4'2.
  split.
  apply tmp5 with O'; repeat php_.
  rewrite eqh1. assumption.
  rewrite eqg1. assumption.
  split. assumption.
  split; repeat php_.
  split; repeat php_.
  }

  {
  left. left. left. right.
  simpl in *.
  intros.
  destruct g_disch as (v,(v0,(v1,(v2,(v3,(v4,(eql,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4))))))))))))))))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp8,(tmp6,(p5p6,c56)))))))))))))))))).
  destruct tmp6 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(tmp7,(tmp9, (p7p8,C7C8)))))))))))))))))).
  subst.
  exists v, v0, v1, v2, v3, v4.
  split. assumption.

  assert (phpdef1: phplusdef p3 p2 /\ phplusdef (phplus p5 (phplus p7 p8)) p2). repeat php_.
  assert (phpdef2: phplusdef p5 p2 /\ phplusdef (phplus p7 p8) p2). repeat php_.
  assert (phpdef3: phplusdef p7 p2 /\ phplusdef p8 p2). repeat php_.
  assert (phpdef4: phplusdef p3 p5 /\ phplusdef p3 (phplus p7 p8)). repeat php_.
  assert (phpdef5: phplusdef p3 p7 /\ phplusdef p3 p8). repeat php_.
  assert (phpdef6: phplusdef p5 p7 /\ phplusdef p5 p8). repeat php_.

  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef (ghplus C5 (ghplus C7 C8)) C2). repeat php_.
  assert (ghpdef2: ghplusdef C5 C2 /\ ghplusdef (ghplus C7 C8) C2). repeat php_.
  assert (ghpdef3: ghplusdef C7 C2 /\ ghplusdef C8 C2). repeat php_.
  assert (ghpdef4: ghplusdef C3 C5 /\ ghplusdef C3 (ghplus C7 C8)). repeat php_.
  assert (ghpdef5: ghplusdef C3 C7 /\ ghplusdef C3 C8). repeat php_.
  assert (ghpdef6: ghplusdef C5 C7 /\ ghplusdef C5 C8). repeat php_.

  assert (eqh1: phplus p3 (phplus p5 (phplus p7 (phplus p8 p2))) =
    phplus (phplus p3 (phplus p5 (phplus p7 p8))) p2). repeat php_.
  assert (eqh2: phplus p5 (phplus p7 (phplus p8 p2)) = phplus p2 (phplus p5 (phplus p7 p8))).
    symmetry. rewrite phplus_comm; repeat php_.
  assert (eqh3: phplus (phplus p2 (phplus p5 (phplus p7 p8))) p3 =
    phplus (phplus p3 (phplus p5 (phplus p7 p8))) p2).
    rewrite phplus_assoc; repeat php_.
  assert (eqg1: ghplus C3 (ghplus C5 (ghplus C7 (ghplus C8 C2))) =
    ghplus (ghplus C3 (ghplus C5 (ghplus C7 C8))) C2). repeat php_.
  assert (eqg2: ghplus C5 (ghplus C7 (ghplus C8 C2)) = ghplus C2 (ghplus C5 (ghplus C7 C8))).
    symmetry. rewrite ghplus_comm; repeat php_.
  assert (eqg3: ghplus (ghplus C2 (ghplus C5 (ghplus C7 C8))) C3 =
    ghplus (ghplus C3 (ghplus C5 (ghplus C7 C8))) C2).
    rewrite ghplus_assoc; repeat php_.

  assert (b35782: boundph (phplus p3 (phplus p5 (phplus p7 (phplus p8 p2))))).
    rewrite eqh1. assumption.
  assert (b5782: boundph (phplus p5 (phplus p7 (phplus p8 p2)))).
    rewrite eqh2.
    apply boundph_mon with p3; repeat php_.
    rewrite eqh3. assumption.

  assert (bg35782: boundgh (ghplus C3 (ghplus C5 (ghplus C7 (ghplus C8 C2))))).
    rewrite eqg1. assumption.
  assert (bg5782: boundgh (ghplus C5 (ghplus C7 (ghplus C8 C2)))).
    rewrite eqg2.
    apply boundgh_mon with C3; repeat php_.
    rewrite eqg3. assumption.
  exists p3, (phplus p5 (phplus p7 (phplus p8 p2))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O24, oplus O2 O4 O24 /\ oplus O3 O24 O).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  inversion OP1.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP2.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O24,(op24,op324)).
  exists O3, O24, C3, (ghplus C5 (ghplus C7 (ghplus C8 C2))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split. assumption.
  split.

  assert (eqh4: phplus (phplus (phplus p7 p8) p2) p5 = phplus p5 (phplus p7 (phplus p8 p2))). repeat php_.
  assert (eqg4: ghplus (ghplus (ghplus C7 C8) C2) C5 = ghplus C5 (ghplus C7 (ghplus C8 C2))). repeat php_.

  assert (bp5782: boundph (phplus p5 (phplus p7 (phplus p8 p2)))). repeat php_.
  assert (bgp5782: boundgh (ghplus C5 (ghplus C7 (ghplus C8 C2)))). repeat php_.
  assert (bp782: boundph (phplus p7 (phplus p8 p2))).
  rewrite <- phplus_assoc; repeat php_. apply boundph_mon with p5; repeat php_.
  rewrite eqh4. assumption.
  assert (bgp782: boundgh (ghplus C7 (ghplus C8 C2))).
  rewrite <- ghplus_assoc; repeat php_. apply boundgh_mon with C5; repeat php_.
  rewrite eqg4. assumption.

  exists p5, (phplus p7 (phplus p8 p2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O26, oplus O2 O6 O26 /\ oplus O5 O26 O24).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  assert (OP5:=op24).
  inversion OP5.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split; apply None_op.
  rewrite <- H0 in *.
  inversion OP3.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  }
  destruct exo as (O26,(op26,op526)).

  exists O5, O26, C5, (ghplus C7 (ghplus C8 C2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.

  exists p7, (phplus p8 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O28, oplus O2 O8 O28 /\ oplus O7 O28 O26).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  assert (OP5:=op24).
  inversion op26.
  rewrite <- H0 in *.
  inversion OP4.
  exists None.
  split; apply None_op.
  rewrite <- H0 in *.
  inversion OP4.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  rewrite <- H0 in *.
  inversion OP4.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  }
  destruct exo as (O28,(op28,op728)).
  exists O7, O28, C7, (ghplus C8 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split.
  intros.
  destruct SAT as (p9,(p0,(phpdefp9p0,(bp9,(bp0,(bp90,(o9,(o0,(C9,(C0,(ghpdefC9C0,(BC9,(BC0,(BC9C0,(opo9o0,(tmp110,(tmp18,(p9p0,C9C0)))))))))))))))))).
  subst.
  assert (phpdef7: phplusdef p8 (phplus p9 p0) /\ phplusdef p2 (phplus p9 p0)). repeat php_.
  assert (phpdef9: phplusdef p8 p9 /\ phplusdef p8 p0). repeat php_.
  assert (phpdef10: phplusdef p2 p9 /\ phplusdef p2 p0). repeat php_.
  assert (ghpdef7: ghplusdef C8 (ghplus C9 C0) /\ ghplusdef C2 (ghplus C9 C0)). repeat php_.
  assert (ghpdef9: ghplusdef C8 C9 /\ ghplusdef C8 C0). repeat php_.
  assert (ghpdef10: ghplusdef C2 C9 /\ ghplusdef C2 C0). repeat php_.

  assert (eqh7: phplus (phplus p8 (phplus p9 p0)) p2 = 
    phplus (phplus p8 p2) (phplus p9 p0)).
    rewrite phplus_comm; repeat php_.
    rewrite <- phplus_assoc; try assumption. symmetry.
    rewrite <- phplus_assoc; try assumption.
    replace (phplus p8 p2) with (phplus p2 p8); repeat php_.
    repeat php_.
  assert (eqg7: ghplus (ghplus C8 (ghplus C9 C0)) C2 = 
    ghplus (ghplus C8 C2) (ghplus C9 C0)).
    rewrite ghplus_comm; repeat php_.
    rewrite <- ghplus_assoc; try assumption. symmetry.
    rewrite <- ghplus_assoc; try assumption.
    replace (ghplus C8 C2) with (ghplus C2 C8); repeat php_.
    repeat php_.

  exists (phplus p8 (phplus p9 p0)), p2.
  exists. repeat php_.
  exists. apply boundph_mon with p2; repeat php_. rewrite eqh7. assumption.
  exists. repeat php_.
  exists. rewrite eqh7. assumption.
  assert (exo: exists O'8, oplus O' O8 O'8 /\ oplus O'8 O2 O'').
  {
  assert (OP1:=op28).
  assert (OP2:=OPLUS).
  inversion OPLUS.
  rewrite <- H in *.
  inversion OP1.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP1.
  exists None.
  split. apply None_op.
  apply sn_op. apply Permutation_trans with o; assumption.
  exists (Some o1).
  split. apply sn_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP1.
  exists (Some o).
  split. apply fs_oplus.
  apply fs_op. assumption.
  }
  destruct exo as (O'8,(op'8,opd28)).
  exists O'8, O2, (ghplus C8 (ghplus C9 C0)), C2.
  exists. repeat php_.
  exists. apply boundgh_mon with C2; repeat php_. rewrite eqg7. assumption.
  exists. repeat php_.
  exists. rewrite eqg7. assumption.
  exists. repeat php_.
  split.
  apply tmp9 with O'; repeat php_.
  rewrite eqh7. assumption.
  rewrite eqg7. assumption.
  apply oplus_comm; assumption.
  exists p9, p0.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists o9, o0, C9, C0.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  split. assumption.
  split. assumption.
  split; reflexivity.
  split. assumption.
  split; repeat php_.
  split; reflexivity.
  split; reflexivity.
  split; repeat php_.
  }

  {
  left. left. right.
  simpl in *.
  intros.
  destruct g_dischu as (v,(v0,(v1,(v2,(v3,(v4,(eql,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4))))))))))))))))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp8,(tmp6,(p5p6,c56)))))))))))))))))).
  destruct tmp6 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(tmp7,(tmp9, (p7p8,C7C8)))))))))))))))))).
  subst.
  exists v, v0, v1, v2, v3, v4.
  split. assumption.

  assert (phpdef1: phplusdef p3 p2 /\ phplusdef (phplus p5 (phplus p7 p8)) p2). repeat php_.
  assert (phpdef2: phplusdef p5 p2 /\ phplusdef (phplus p7 p8) p2). repeat php_.
  assert (phpdef3: phplusdef p7 p2 /\ phplusdef p8 p2). repeat php_.
  assert (phpdef4: phplusdef p3 p5 /\ phplusdef p3 (phplus p7 p8)). repeat php_.
  assert (phpdef5: phplusdef p3 p7 /\ phplusdef p3 p8). repeat php_.
  assert (phpdef6: phplusdef p5 p7 /\ phplusdef p5 p8). repeat php_.

  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef (ghplus C5 (ghplus C7 C8)) C2). repeat php_.
  assert (ghpdef2: ghplusdef C5 C2 /\ ghplusdef (ghplus C7 C8) C2). repeat php_.
  assert (ghpdef3: ghplusdef C7 C2 /\ ghplusdef C8 C2). repeat php_.
  assert (ghpdef4: ghplusdef C3 C5 /\ ghplusdef C3 (ghplus C7 C8)). repeat php_.
  assert (ghpdef5: ghplusdef C3 C7 /\ ghplusdef C3 C8). repeat php_.
  assert (ghpdef6: ghplusdef C5 C7 /\ ghplusdef C5 C8). repeat php_.

  assert (eqh1: phplus p3 (phplus p5 (phplus p7 (phplus p8 p2))) =
    phplus (phplus p3 (phplus p5 (phplus p7 p8))) p2). repeat php_.
  assert (eqh2: phplus p5 (phplus p7 (phplus p8 p2)) = phplus p2 (phplus p5 (phplus p7 p8))).
    symmetry. rewrite phplus_comm; repeat php_.
  assert (eqh3: phplus (phplus p2 (phplus p5 (phplus p7 p8))) p3 =
    phplus (phplus p3 (phplus p5 (phplus p7 p8))) p2).
    rewrite phplus_assoc; repeat php_.
  assert (eqg1: ghplus C3 (ghplus C5 (ghplus C7 (ghplus C8 C2))) =
    ghplus (ghplus C3 (ghplus C5 (ghplus C7 C8))) C2). repeat php_.
  assert (eqg2: ghplus C5 (ghplus C7 (ghplus C8 C2)) = ghplus C2 (ghplus C5 (ghplus C7 C8))).
    symmetry. rewrite ghplus_comm; repeat php_.
  assert (eqg3: ghplus (ghplus C2 (ghplus C5 (ghplus C7 C8))) C3 =
    ghplus (ghplus C3 (ghplus C5 (ghplus C7 C8))) C2).
    rewrite ghplus_assoc; repeat php_.

  assert (b35782: boundph (phplus p3 (phplus p5 (phplus p7 (phplus p8 p2))))).
    rewrite eqh1. assumption.
  assert (b5782: boundph (phplus p5 (phplus p7 (phplus p8 p2)))).
    rewrite eqh2.
    apply boundph_mon with p3; repeat php_.
    rewrite eqh3. assumption.

  assert (bg35782: boundgh (ghplus C3 (ghplus C5 (ghplus C7 (ghplus C8 C2))))).
    rewrite eqg1. assumption.
  assert (bg5782: boundgh (ghplus C5 (ghplus C7 (ghplus C8 C2)))).
    rewrite eqg2.
    apply boundgh_mon with C3; repeat php_.
    rewrite eqg3. assumption.
  exists p3, (phplus p5 (phplus p7 (phplus p8 p2))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O24, oplus O2 O4 O24 /\ oplus O3 O24 O).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  inversion OP1.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP2.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O24,(op24,op324)).
  exists O3, O24, C3, (ghplus C5 (ghplus C7 (ghplus C8 C2))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split. assumption.
  split.

  assert (eqh4: phplus (phplus (phplus p7 p8) p2) p5 = phplus p5 (phplus p7 (phplus p8 p2))). repeat php_.
  assert (eqg4: ghplus (ghplus (ghplus C7 C8) C2) C5 = ghplus C5 (ghplus C7 (ghplus C8 C2))). repeat php_.

  assert (bp5782: boundph (phplus p5 (phplus p7 (phplus p8 p2)))). repeat php_.
  assert (bgp5782: boundgh (ghplus C5 (ghplus C7 (ghplus C8 C2)))). repeat php_.
  assert (bp782: boundph (phplus p7 (phplus p8 p2))).
  rewrite <- phplus_assoc; repeat php_. apply boundph_mon with p5; repeat php_.
  rewrite eqh4. assumption.
  assert (bgp782: boundgh (ghplus C7 (ghplus C8 C2))).
  rewrite <- ghplus_assoc; repeat php_. apply boundgh_mon with C5; repeat php_.
  rewrite eqg4. assumption.

  exists p5, (phplus p7 (phplus p8 p2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O26, oplus O2 O6 O26 /\ oplus O5 O26 O24).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  assert (OP5:=op24).
  inversion OP5.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split; apply None_op.
  rewrite <- H0 in *.
  inversion OP3.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  }
  destruct exo as (O26,(op26,op526)).

  exists O5, O26, C5, (ghplus C7 (ghplus C8 C2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.

  exists p7, (phplus p8 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O28, oplus O2 O8 O28 /\ oplus O7 O28 O26).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  assert (OP5:=op24).
  inversion op26.
  rewrite <- H0 in *.
  inversion OP4.
  exists None.
  split; apply None_op.
  rewrite <- H0 in *.
  inversion OP4.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  rewrite <- H0 in *.
  inversion OP4.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  }
  destruct exo as (O28,(op28,op728)).
  exists O7, O28, C7, (ghplus C8 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split.
  intros.
  destruct SAT as (p9,(p0,(phpdefp9p0,(bp9,(bp0,(bp90,(o9,(o0,(C9,(C0,(ghpdefC9C0,(BC9,(BC0,(BC9C0,(opo9o0,(tmp110,(tmp18,(p9p0,C9C0)))))))))))))))))).
  subst.
  assert (phpdef7: phplusdef p8 (phplus p9 p0) /\ phplusdef p2 (phplus p9 p0)). repeat php_.
  assert (phpdef9: phplusdef p8 p9 /\ phplusdef p8 p0). repeat php_.
  assert (phpdef10: phplusdef p2 p9 /\ phplusdef p2 p0). repeat php_.
  assert (ghpdef7: ghplusdef C8 (ghplus C9 C0) /\ ghplusdef C2 (ghplus C9 C0)). repeat php_.
  assert (ghpdef9: ghplusdef C8 C9 /\ ghplusdef C8 C0). repeat php_.
  assert (ghpdef10: ghplusdef C2 C9 /\ ghplusdef C2 C0). repeat php_.

  assert (eqh7: phplus (phplus p8 (phplus p9 p0)) p2 = 
    phplus (phplus p8 p2) (phplus p9 p0)).
    rewrite phplus_comm; repeat php_.
    rewrite <- phplus_assoc; try assumption. symmetry.
    rewrite <- phplus_assoc; try assumption.
    replace (phplus p8 p2) with (phplus p2 p8); repeat php_.
    repeat php_.
  assert (eqg7: ghplus (ghplus C8 (ghplus C9 C0)) C2 = 
    ghplus (ghplus C8 C2) (ghplus C9 C0)).
    rewrite ghplus_comm; repeat php_.
    rewrite <- ghplus_assoc; try assumption. symmetry.
    rewrite <- ghplus_assoc; try assumption.
    replace (ghplus C8 C2) with (ghplus C2 C8); repeat php_.
    repeat php_.

  exists (phplus p8 (phplus p9 p0)), p2.
  exists. repeat php_.
  exists. apply boundph_mon with p2; repeat php_. rewrite eqh7. assumption.
  exists. repeat php_.
  exists. rewrite eqh7. assumption.
  assert (exo: exists O'8, oplus O' O8 O'8 /\ oplus O'8 O2 O'').
  {
  assert (OP1:=op28).
  assert (OP2:=OPLUS).
  inversion OPLUS.
  rewrite <- H in *.
  inversion OP1.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP1.
  exists None.
  split. apply None_op.
  apply sn_op. apply Permutation_trans with o; assumption.
  exists (Some o1).
  split. apply sn_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP1.
  exists (Some o).
  split. apply fs_oplus.
  apply fs_op. assumption.
  }
  destruct exo as (O'8,(op'8,opd28)).
  exists O'8, O2, (ghplus C8 (ghplus C9 C0)), C2.
  exists. repeat php_.
  exists. apply boundgh_mon with C2; repeat php_. rewrite eqg7. assumption.
  exists. repeat php_.
  exists. rewrite eqg7. assumption.
  exists. repeat php_.
  split.
  apply tmp9 with O'; repeat php_.
  rewrite eqh7. assumption.
  rewrite eqg7. assumption.
  apply oplus_comm; assumption.
  exists p9, p0.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists o9, o0, C9, C0.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  split. assumption.
  split. assumption.
  split; reflexivity.
  split. assumption.
  split; repeat php_.
  split; reflexivity.
  split; reflexivity.
  split; repeat php_.
  }

  {
  left. right.
  simpl in *.
  intros.
  destruct g_chrg as (v,(v0,(v1,(v2,(v3,(v4,(eql,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4))))))))))))))))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp8,(tmp6,(p5p6,c56)))))))))))))))))).
  destruct tmp6 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(tmp7,(tmp9, (p7p8,C7C8)))))))))))))))))).
  subst.
  exists v, v0, v1, v2, v3, v4.
  split. assumption.

  assert (phpdef1: phplusdef p3 p2 /\ phplusdef (phplus p5 (phplus p7 p8)) p2). repeat php_.
  assert (phpdef2: phplusdef p5 p2 /\ phplusdef (phplus p7 p8) p2). repeat php_.
  assert (phpdef3: phplusdef p7 p2 /\ phplusdef p8 p2). repeat php_.
  assert (phpdef4: phplusdef p3 p5 /\ phplusdef p3 (phplus p7 p8)). repeat php_.
  assert (phpdef5: phplusdef p3 p7 /\ phplusdef p3 p8). repeat php_.
  assert (phpdef6: phplusdef p5 p7 /\ phplusdef p5 p8). repeat php_.

  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef (ghplus C5 (ghplus C7 C8)) C2). repeat php_.
  assert (ghpdef2: ghplusdef C5 C2 /\ ghplusdef (ghplus C7 C8) C2). repeat php_.
  assert (ghpdef3: ghplusdef C7 C2 /\ ghplusdef C8 C2). repeat php_.
  assert (ghpdef4: ghplusdef C3 C5 /\ ghplusdef C3 (ghplus C7 C8)). repeat php_.
  assert (ghpdef5: ghplusdef C3 C7 /\ ghplusdef C3 C8). repeat php_.
  assert (ghpdef6: ghplusdef C5 C7 /\ ghplusdef C5 C8). repeat php_.

  assert (eqh1: phplus p3 (phplus p5 (phplus p7 (phplus p8 p2))) =
    phplus (phplus p3 (phplus p5 (phplus p7 p8))) p2). repeat php_.
  assert (eqh2: phplus p5 (phplus p7 (phplus p8 p2)) = phplus p2 (phplus p5 (phplus p7 p8))).
    symmetry. rewrite phplus_comm; repeat php_.
  assert (eqh3: phplus (phplus p2 (phplus p5 (phplus p7 p8))) p3 =
    phplus (phplus p3 (phplus p5 (phplus p7 p8))) p2).
    rewrite phplus_assoc; repeat php_.
  assert (eqg1: ghplus C3 (ghplus C5 (ghplus C7 (ghplus C8 C2))) =
    ghplus (ghplus C3 (ghplus C5 (ghplus C7 C8))) C2). repeat php_.
  assert (eqg2: ghplus C5 (ghplus C7 (ghplus C8 C2)) = ghplus C2 (ghplus C5 (ghplus C7 C8))).
    symmetry. rewrite ghplus_comm; repeat php_.
  assert (eqg3: ghplus (ghplus C2 (ghplus C5 (ghplus C7 C8))) C3 =
    ghplus (ghplus C3 (ghplus C5 (ghplus C7 C8))) C2).
    rewrite ghplus_assoc; repeat php_.

  assert (b35782: boundph (phplus p3 (phplus p5 (phplus p7 (phplus p8 p2))))).
    rewrite eqh1. assumption.
  assert (b5782: boundph (phplus p5 (phplus p7 (phplus p8 p2)))).
    rewrite eqh2.
    apply boundph_mon with p3; repeat php_.
    rewrite eqh3. assumption.

  assert (bg35782: boundgh (ghplus C3 (ghplus C5 (ghplus C7 (ghplus C8 C2))))).
    rewrite eqg1. assumption.
  assert (bg5782: boundgh (ghplus C5 (ghplus C7 (ghplus C8 C2)))).
    rewrite eqg2.
    apply boundgh_mon with C3; repeat php_.
    rewrite eqg3. assumption.
  exists p3, (phplus p5 (phplus p7 (phplus p8 p2))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O24, oplus O2 O4 O24 /\ oplus O3 O24 O).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  inversion OP1.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP2.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O24,(op24,op324)).
  exists O3, O24, C3, (ghplus C5 (ghplus C7 (ghplus C8 C2))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split. assumption.
  split.

  assert (eqh4: phplus (phplus (phplus p7 p8) p2) p5 = phplus p5 (phplus p7 (phplus p8 p2))). repeat php_.
  assert (eqg4: ghplus (ghplus (ghplus C7 C8) C2) C5 = ghplus C5 (ghplus C7 (ghplus C8 C2))). repeat php_.

  assert (bp5782: boundph (phplus p5 (phplus p7 (phplus p8 p2)))). repeat php_.
  assert (bgp5782: boundgh (ghplus C5 (ghplus C7 (ghplus C8 C2)))). repeat php_.
  assert (bp782: boundph (phplus p7 (phplus p8 p2))).
  rewrite <- phplus_assoc; repeat php_. apply boundph_mon with p5; repeat php_.
  rewrite eqh4. assumption.
  assert (bgp782: boundgh (ghplus C7 (ghplus C8 C2))).
  rewrite <- ghplus_assoc; repeat php_. apply boundgh_mon with C5; repeat php_.
  rewrite eqg4. assumption.

  exists p5, (phplus p7 (phplus p8 p2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O26, oplus O2 O6 O26 /\ oplus O5 O26 O24).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  assert (OP5:=op24).
  inversion OP5.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split; apply None_op.
  rewrite <- H0 in *.
  inversion OP3.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  }
  destruct exo as (O26,(op26,op526)).

  exists O5, O26, C5, (ghplus C7 (ghplus C8 C2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.

  exists p7, (phplus p8 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O28, oplus O2 O8 O28 /\ oplus O7 O28 O26).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  assert (OP5:=op24).
  inversion op26.
  rewrite <- H0 in *.
  inversion OP4.
  exists None.
  split; apply None_op.
  rewrite <- H0 in *.
  inversion OP4.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  rewrite <- H0 in *.
  inversion OP4.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  }
  destruct exo as (O28,(op28,op728)).
  exists O7, O28, C7, (ghplus C8 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split.
  intros.
  destruct SAT as (p9,(p0,(phpdefp9p0,(bp9,(bp0,(bp90,(o9,(o0,(C9,(C0,(ghpdefC9C0,(BC9,(BC0,(BC9C0,(opo9o0,(tmp110,(tmp18,(p9p0,C9C0)))))))))))))))))).
  subst.
  assert (phpdef7: phplusdef p8 (phplus p9 p0) /\ phplusdef p2 (phplus p9 p0)). repeat php_.
  assert (phpdef9: phplusdef p8 p9 /\ phplusdef p8 p0). repeat php_.
  assert (phpdef10: phplusdef p2 p9 /\ phplusdef p2 p0). repeat php_.
  assert (ghpdef7: ghplusdef C8 (ghplus C9 C0) /\ ghplusdef C2 (ghplus C9 C0)). repeat php_.
  assert (ghpdef9: ghplusdef C8 C9 /\ ghplusdef C8 C0). repeat php_.
  assert (ghpdef10: ghplusdef C2 C9 /\ ghplusdef C2 C0). repeat php_.

  assert (eqh7: phplus (phplus p8 (phplus p9 p0)) p2 = 
    phplus (phplus p8 p2) (phplus p9 p0)).
    rewrite phplus_comm; repeat php_.
    rewrite <- phplus_assoc; try assumption. symmetry.
    rewrite <- phplus_assoc; try assumption.
    replace (phplus p8 p2) with (phplus p2 p8); repeat php_.
    repeat php_.
  assert (eqg7: ghplus (ghplus C8 (ghplus C9 C0)) C2 = 
    ghplus (ghplus C8 C2) (ghplus C9 C0)).
    rewrite ghplus_comm; repeat php_.
    rewrite <- ghplus_assoc; try assumption. symmetry.
    rewrite <- ghplus_assoc; try assumption.
    replace (ghplus C8 C2) with (ghplus C2 C8); repeat php_.
    repeat php_.

  exists (phplus p8 (phplus p9 p0)), p2.
  exists. repeat php_.
  exists. apply boundph_mon with p2; repeat php_. rewrite eqh7. assumption.
  exists. repeat php_.
  exists. rewrite eqh7. assumption.
  assert (exo: exists O'8, oplus O' O8 O'8 /\ oplus O'8 O2 O'').
  {
  assert (OP1:=op28).
  assert (OP2:=OPLUS).
  inversion OPLUS.
  rewrite <- H in *.
  inversion OP1.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP1.
  exists None.
  split. apply None_op.
  apply sn_op. apply Permutation_trans with o; assumption.
  exists (Some o1).
  split. apply sn_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP1.
  exists (Some o).
  split. apply fs_oplus.
  apply fs_op. assumption.
  }
  destruct exo as (O'8,(op'8,opd28)).
  exists O'8, O2, (ghplus C8 (ghplus C9 C0)), C2.
  exists. repeat php_.
  exists. apply boundgh_mon with C2; repeat php_. rewrite eqg7. assumption.
  exists. repeat php_.
  exists. rewrite eqg7. assumption.
  exists. repeat php_.
  split.
  apply tmp9 with O'; repeat php_.
  rewrite eqh7. assumption.
  rewrite eqg7. assumption.
  apply oplus_comm; assumption.
  exists p9, p0.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists o9, o0, C9, C0.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  split. assumption.
  split. assumption.
  split; reflexivity.
  split. assumption.
  split; repeat php_.
  split; reflexivity.
  split; reflexivity.
  split; repeat php_.
  }

  {
  right.
  simpl in *.
  intros.
  destruct g_chrgu as (v,(v0,(v1,(v2,(v3,(v4,(eql,(p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(ghpdefC3C4,(BC3,(BC4,(bc34,(opO3O4,(tmp4,(tmp5, (p3p4,c3c4))))))))))))))))))))))))).
  destruct tmp5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp8,(tmp6,(p5p6,c56)))))))))))))))))).
  destruct tmp6 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(tmp7,(tmp9, (p7p8,C7C8)))))))))))))))))).
  subst.
  exists v, v0, v1, v2, v3, v4.
  split. assumption.

  assert (phpdef1: phplusdef p3 p2 /\ phplusdef (phplus p5 (phplus p7 p8)) p2). repeat php_.
  assert (phpdef2: phplusdef p5 p2 /\ phplusdef (phplus p7 p8) p2). repeat php_.
  assert (phpdef3: phplusdef p7 p2 /\ phplusdef p8 p2). repeat php_.
  assert (phpdef4: phplusdef p3 p5 /\ phplusdef p3 (phplus p7 p8)). repeat php_.
  assert (phpdef5: phplusdef p3 p7 /\ phplusdef p3 p8). repeat php_.
  assert (phpdef6: phplusdef p5 p7 /\ phplusdef p5 p8). repeat php_.

  assert (ghpdef1: ghplusdef C3 C2 /\ ghplusdef (ghplus C5 (ghplus C7 C8)) C2). repeat php_.
  assert (ghpdef2: ghplusdef C5 C2 /\ ghplusdef (ghplus C7 C8) C2). repeat php_.
  assert (ghpdef3: ghplusdef C7 C2 /\ ghplusdef C8 C2). repeat php_.
  assert (ghpdef4: ghplusdef C3 C5 /\ ghplusdef C3 (ghplus C7 C8)). repeat php_.
  assert (ghpdef5: ghplusdef C3 C7 /\ ghplusdef C3 C8). repeat php_.
  assert (ghpdef6: ghplusdef C5 C7 /\ ghplusdef C5 C8). repeat php_.

  assert (eqh1: phplus p3 (phplus p5 (phplus p7 (phplus p8 p2))) =
    phplus (phplus p3 (phplus p5 (phplus p7 p8))) p2). repeat php_.
  assert (eqh2: phplus p5 (phplus p7 (phplus p8 p2)) = phplus p2 (phplus p5 (phplus p7 p8))).
    symmetry. rewrite phplus_comm; repeat php_.
  assert (eqh3: phplus (phplus p2 (phplus p5 (phplus p7 p8))) p3 =
    phplus (phplus p3 (phplus p5 (phplus p7 p8))) p2).
    rewrite phplus_assoc; repeat php_.
  assert (eqg1: ghplus C3 (ghplus C5 (ghplus C7 (ghplus C8 C2))) =
    ghplus (ghplus C3 (ghplus C5 (ghplus C7 C8))) C2). repeat php_.
  assert (eqg2: ghplus C5 (ghplus C7 (ghplus C8 C2)) = ghplus C2 (ghplus C5 (ghplus C7 C8))).
    symmetry. rewrite ghplus_comm; repeat php_.
  assert (eqg3: ghplus (ghplus C2 (ghplus C5 (ghplus C7 C8))) C3 =
    ghplus (ghplus C3 (ghplus C5 (ghplus C7 C8))) C2).
    rewrite ghplus_assoc; repeat php_.

  assert (b35782: boundph (phplus p3 (phplus p5 (phplus p7 (phplus p8 p2))))).
    rewrite eqh1. assumption.
  assert (b5782: boundph (phplus p5 (phplus p7 (phplus p8 p2)))).
    rewrite eqh2.
    apply boundph_mon with p3; repeat php_.
    rewrite eqh3. assumption.

  assert (bg35782: boundgh (ghplus C3 (ghplus C5 (ghplus C7 (ghplus C8 C2))))).
    rewrite eqg1. assumption.
  assert (bg5782: boundgh (ghplus C5 (ghplus C7 (ghplus C8 C2)))).
    rewrite eqg2.
    apply boundgh_mon with C3; repeat php_.
    rewrite eqg3. assumption.
  exists p3, (phplus p5 (phplus p7 (phplus p8 p2))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O24, oplus O2 O4 O24 /\ oplus O3 O24 O).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  inversion OP1.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP2.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP2.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  }
  destruct exo as (O24,(op24,op324)).
  exists O3, O24, C3, (ghplus C5 (ghplus C7 (ghplus C8 C2))).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split. assumption.
  split.

  assert (eqh4: phplus (phplus (phplus p7 p8) p2) p5 = phplus p5 (phplus p7 (phplus p8 p2))). repeat php_.
  assert (eqg4: ghplus (ghplus (ghplus C7 C8) C2) C5 = ghplus C5 (ghplus C7 (ghplus C8 C2))). repeat php_.

  assert (bp5782: boundph (phplus p5 (phplus p7 (phplus p8 p2)))). repeat php_.
  assert (bgp5782: boundgh (ghplus C5 (ghplus C7 (ghplus C8 C2)))). repeat php_.
  assert (bp782: boundph (phplus p7 (phplus p8 p2))).
  rewrite <- phplus_assoc; repeat php_. apply boundph_mon with p5; repeat php_.
  rewrite eqh4. assumption.
  assert (bgp782: boundgh (ghplus C7 (ghplus C8 C2))).
  rewrite <- ghplus_assoc; repeat php_. apply boundgh_mon with C5; repeat php_.
  rewrite eqg4. assumption.

  exists p5, (phplus p7 (phplus p8 p2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O26, oplus O2 O6 O26 /\ oplus O5 O26 O24).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  assert (OP5:=op24).
  inversion OP5.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split; apply None_op.
  rewrite <- H0 in *.
  inversion OP3.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  rewrite <- H0 in *.
  inversion OP3.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  }
  destruct exo as (O26,(op26,op526)).

  exists O5, O26, C5, (ghplus C7 (ghplus C8 C2)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.

  exists p7, (phplus p8 p2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  assert (exo: exists O28, oplus O2 O8 O28 /\ oplus O7 O28 O26).
  {
  assert (OP1:=opO1O2).
  assert (OP2:=opO3O4).
  assert (OP3:=opO5O6).
  assert (OP4:=opO7O8).
  assert (OP5:=op24).
  inversion op26.
  rewrite <- H0 in *.
  inversion OP4.
  exists None.
  split; apply None_op.
  rewrite <- H0 in *.
  inversion OP4.
  exists (Some o).
  split. apply fs_oplus.
  apply sn_op. assumption.
  rewrite <- H0 in *.
  inversion OP4.
  exists None.
  split. apply None_op.
  apply fs_op. apply Permutation_trans with o; assumption.
  exists (Some o0).
  split. apply sn_oplus.
  apply sn_op. apply Permutation_trans with o; assumption.
  }
  destruct exo as (O28,(op28,op728)).
  exists O7, O28, C7, (ghplus C8 C2).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  split.
  intros.
  destruct SAT as (p9,(p0,(phpdefp9p0,(bp9,(bp0,(bp90,(o9,(o0,(C9,(C0,(ghpdefC9C0,(BC9,(BC0,(BC9C0,(opo9o0,(tmp110,(tmp18,(p9p0,C9C0)))))))))))))))))).
  subst.
  assert (phpdef7: phplusdef p8 (phplus p9 p0) /\ phplusdef p2 (phplus p9 p0)). repeat php_.
  assert (phpdef9: phplusdef p8 p9 /\ phplusdef p8 p0). repeat php_.
  assert (phpdef10: phplusdef p2 p9 /\ phplusdef p2 p0). repeat php_.
  assert (ghpdef7: ghplusdef C8 (ghplus C9 C0) /\ ghplusdef C2 (ghplus C9 C0)). repeat php_.
  assert (ghpdef9: ghplusdef C8 C9 /\ ghplusdef C8 C0). repeat php_.
  assert (ghpdef10: ghplusdef C2 C9 /\ ghplusdef C2 C0). repeat php_.

  assert (eqh7: phplus (phplus p8 (phplus p9 p0)) p2 = 
    phplus (phplus p8 p2) (phplus p9 p0)).
    rewrite phplus_comm; repeat php_.
    rewrite <- phplus_assoc; try assumption. symmetry.
    rewrite <- phplus_assoc; try assumption.
    replace (phplus p8 p2) with (phplus p2 p8); repeat php_.
    repeat php_.
  assert (eqg7: ghplus (ghplus C8 (ghplus C9 C0)) C2 = 
    ghplus (ghplus C8 C2) (ghplus C9 C0)).
    rewrite ghplus_comm; repeat php_.
    rewrite <- ghplus_assoc; try assumption. symmetry.
    rewrite <- ghplus_assoc; try assumption.
    replace (ghplus C8 C2) with (ghplus C2 C8); repeat php_.
    repeat php_.

  exists (phplus p8 (phplus p9 p0)), p2.
  exists. repeat php_.
  exists. apply boundph_mon with p2; repeat php_. rewrite eqh7. assumption.
  exists. repeat php_.
  exists. rewrite eqh7. assumption.
  assert (exo: exists O'8, oplus O' O8 O'8 /\ oplus O'8 O2 O'').
  {
  assert (OP1:=op28).
  assert (OP2:=OPLUS).
  inversion OPLUS.
  rewrite <- H in *.
  inversion OP1.
  exists None.
  split; apply None_op.
  rewrite <- H in *.
  inversion OP1.
  exists None.
  split. apply None_op.
  apply sn_op. apply Permutation_trans with o; assumption.
  exists (Some o1).
  split. apply sn_oplus.
  apply fs_op. apply Permutation_trans with o; assumption.
  rewrite <- H in *.
  inversion OP1.
  exists (Some o).
  split. apply fs_oplus.
  apply fs_op. assumption.
  }
  destruct exo as (O'8,(op'8,opd28)).
  exists O'8, O2, (ghplus C8 (ghplus C9 C0)), C2.
  exists. repeat php_.
  exists. apply boundgh_mon with C2; repeat php_. rewrite eqg7. assumption.
  exists. repeat php_.
  exists. rewrite eqg7. assumption.
  exists. repeat php_.
  split.
  apply tmp9 with O'; repeat php_.
  rewrite eqh7. assumption.
  rewrite eqg7. assumption.
  apply oplus_comm; assumption.
  exists p9, p0.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists o9, o0, C9, C0.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  split. assumption.
  split. assumption.
  split; reflexivity.
  split. assumption.
  split; repeat php_.
  split; reflexivity.
  split; reflexivity.
  split; repeat php_.
  }
  }
Qed.
