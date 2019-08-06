Add LoadPath "proofs".

Require Import Qcanon.
Require Import ZArith.
Require Import List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sorting.Permutation.
Require Import Util_Z.
Require Import Util_list.
Require Import Programs.
Require Import Assertions.
Require Import WeakestPrecondition.

Set Implicit Arguments.

Local Open Scope Z.

Definition zero : Z := 0.
Definition ND := (zero, nil:list (Z*Z)).


Definition correct a c a' invs sp :=
  forall n, a |= weakest_pre n sp c a' id invs.


(** # <font size="5"><b> NOP </b></font> # *)

Theorem rule_nop invs sp P: correct
  P nop (fun _ => P) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  left. left. left. left. left. left. left. left. left. left.
  simpl in *.
  intros.
  assumption.
Qed.

(** # <font size="5"><b> Value </b></font> # *)

Theorem rule_Val invs sp e: correct
  (Abool true)
  (Val e)
  (fun z => Abool (Z.eqb z ([[e]]))) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  simpl.
  apply Z.eqb_eq.
  reflexivity.
Qed.


(** # <font size="5"><b> Allocate Memory </b></font> # *)

Theorem rule_Cons invs sp n: correct
  (Abool true)
  (Cons n)
  (fun l => fold_left Astar (points_tos (seq 0 n)(Enum l, 0%Qc, Enum l, None, false, ND, ND ,nil)) (Abool true)) invs sp.
Proof.
  unfold correct.
  intros. destruct n0. reflexivity.
  simpl.
  intros.
  rewrite phplus_comm; repeat php_.
  rewrite ghplus_comm; repeat php_.
  apply sat_mon with O' o; repeat php_.
  apply oplus_comm; assumption.
Qed.


(** # <font size="5"><b> Lookup Memory </b></font> # *)

Definition cell_loc (adrs: exp) : location exp := (adrs, 0%Qc, adrs, None, false, ND, ND,nil).

Theorem rule_Lookup invs sp f e e': correct
  (Apointsto f (cell_loc e) e')
  (Lookup e)
  (fun r => Abool (Z.eqb r ([[e']])) &* Apointsto f (cell_loc e) e') invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  simpl.
  intros.
  destruct SAT as (f',(lef',pl)).
  exists (cell_loc e), ([[e']]), f.
  split. apply Z.eqb_eq. reflexivity.
  exists p, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o, None, g, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  destruct o.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  split.
  exists f', lef'. assumption.
  split.
  intros.
  split.
  apply Z.eqb_eq. reflexivity.
  assumption.
  split; repeat php_.
Qed.


(** # <font size="5"><b> Mutate Memory </b></font> # *)

Theorem rule_Mutate invs sp (e1 e2 e': exp): correct
  (cell_loc e1 |-> e')
  (Mutate e1 e2)
  (fun r => cell_loc e1 |-> e2) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  simpl.
  intros.
  exists (cell_loc e1), e'.
  exists p, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o, None, g, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  destruct o.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  split.
  split.
  apply Z.eqb_eq. reflexivity.
  simpl in SAT.
  assumption.
  split.
  intros.
  rewrite phplus_comm; repeat php_.
  split; repeat php_.
Qed.


(** # <font size="5"><b> Paralle Composition </b></font> # *)

Theorem rule_fork c o o' a invs sp:
  forall (C: correct (Aobs o' ** a) c (fun _ => Aobs nil) invs sp),
    correct (Aobs (o ++ o') ** a ) (Fork c) (fun _ => Aobs o) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest))))))))))))))).
  destruct rest as (op,(satp2,(p1p2,c1c2))).
  exists o, o'.
  exists (emp knowledge), p.
  exists.
  apply phpdef_comm.
  apply phpdef_emp.
  exists.
  apply boundph_emp.
  exists.
  assumption.
  exists.
  rewrite phplus_comm.
  rewrite phplus_emp.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  exists (Some (map evalol o ++ map evalol o')), None.
  exists (emp (option nat * nat)), g.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  inversion op.
  rewrite <- H1 in opo1o2.
  inversion opo1o2.
  apply fs_op.
  apply Permutation_trans with o'0.
  rewrite <- map_app.
  assumption.
  assumption.
  split.
  exists (emp knowledge), (emp knowledge).
  exists.
  apply phpdef_emp.
  exists.
  apply boundph_emp.
  exists.
  apply boundph_emp.
  exists.
  apply boundph_emp.
  exists (Some (map evalol o ++ map evalol o')), None.
  exists (emp (option nat * nat)), (emp (option nat * nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  apply fs_op.
  apply Permutation_refl.
  split.
  apply fs_op.
  rewrite map_app.
  apply Permutation_refl.
  split.
  intros.
  inversion SAT.
  rewrite <- H1 in OPLUS.
  inversion OPLUS.
  apply fs_op.
  apply Permutation_trans with o'0.
  assumption.
  assumption.
  split.
  apply phplus_emp.
  repeat php_.
  assert (o2N: o2 = None).
  {
  inversion op.
  rewrite <- H1 in opo1o2.
  inversion opo1o2.
  reflexivity.
  }
  rewrite o2N in *.
  assert (G: sat p (Some (map evalol o')) g (weakest_pre n sp c (fun _ => Aobs nil) id invs)).
  apply C.
  assumption.
  assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp1p2.
  exists (Some (map evalol o')), None.
  exists c1, c2, ghpdefc1c2, bc1, bc2, bc12.
  exists.
  apply fs_op.
  apply Permutation_refl.
  split.
  apply fs_op.
  apply Permutation_refl.
  tauto.
  split.
  intros.
  rewrite <- p1p2 in *.
  rewrite <- c1c2 in *.
  assert (phpdefp1p'p2p': phplusdef p1 p' /\ phplusdef p2 p'). repeat php_.
  assert (ghpdefp1p'p2p': ghplusdef c1 g' /\ ghplusdef c2 g'). repeat php_.
  apply C; repeat php_.

  assert (bp1p'p2: boundph (phplus (phplus p1 p') p2)).
  {
  rewrite phplus_comm; repeat php_.
  rewrite <- phplus_assoc; repeat php_.
  replace (phplus p2 p1) with (phplus p1 p2); repeat php_.
  }

  assert (bgp1p'p2: boundgh (ghplus (ghplus c1 g') c2)).
  {
  rewrite ghplus_comm; repeat php_.
  rewrite <- ghplus_assoc; repeat php_.
  replace (ghplus c2 c1) with (ghplus c1 c2); repeat php_.
  }

  exists (phplus p1 p'), p2.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists O'', None.
  exists (ghplus c1 g'), c2.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  destruct O''.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  inversion SAT.
  rewrite <- H1 in OPLUS.
  inversion OPLUS.
  exists.
  apply fs_op.
  apply Permutation_trans with o'0.
  assumption.
  assumption.
  split. assumption.
  split; repeat php_.
  split; repeat php_.
Qed.


(** # <font size="5"><b> Sequential Composition </b></font> # *)

Theorem rule_Let a a' a'' c1 c2 x invs sp:
  forall (C1: correct a c1 a' invs sp)
         (C2: forall z, correct (a' z) (subs c2 (subse x z)) a'' invs sp),
    correct a (Let x c1 c2) a'' invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  simpl.
  intros.
  eapply sat_weak_imp with (n:=n).
  assumption.
  assumption.
  apply C1.
  assumption.
  assumption.
  assumption.
  intros.
  unfold id.
  simpl.
  specialize C2 with (z:=z).
  eapply C2 in SAT0.
  eapply sat_pre_subs3 with (n:=n) in SAT0;
  try tauto.
  apply SAT0.
  omega.
  assumption.
  assumption.
  omega.
Qed.


(** # <font size="5"><b> Conditional Commands </b></font> # *)

Theorem rule_If c c1 c2 a a' a'' invs sp:
  forall (C: correct a c a' invs sp)
         (C1: forall z (TRUE: Z.lt 0 z), correct (a' z) c1 a'' invs sp)
         (C2: forall z (TRUE: Z.le z 0), correct (a' z) c2 a'' invs sp),
    correct a (If c c1 c2) a'' invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  simpl.
  intros.
  eapply sat_weak_imp with (n:=n); try assumption.
  apply C; try assumption.
  intros.
  destruct (0 <? z)%Z eqn:z0.
  apply Z.ltb_lt in z0.
  apply C1 with z; try assumption.
  apply Z_ltb_falseL in z0.
  apply C2 with z; try assumption.
  omega.
Qed.


(** # <font size="5"><b> Loop Commands </b></font> # *)

Theorem rule_While c1 c2 a a' invs sp:
  forall (C: correct a c1 a' invs sp)
         (C1: forall z (TRUE: Z.lt 0 z), correct (a' z) c2 (fun _ => a) invs sp)
         (C2: forall z (TRUE: Z.le z 0), (a' z) |= a),
    correct a (While c1 c2) (fun _ => EX z, a' z &* Abool (Z.leb z 0)) invs sp.
(*
while (1 - size(l))
  wait(v,l);
a' = fun z => 1 <= size(l) + z <= 1
a = fun _ => 0 <= size(l)
*)
Proof.
  unfold correct.
  simpl.
  induction n.
  reflexivity.
  simpl.
  intros.
  eapply sat_weak_imp with (n:=n); try assumption.
  apply C; try assumption.
  intros.
  destruct (0 <? z)%Z eqn:z0.
  apply Z.ltb_lt in z0.
  eapply sat_weak_imp with (n:=n); try assumption.
  eapply C1 with z; try assumption.
  intros.
  apply IHn; try assumption.
  omega.
  apply Z_ltb_falseL in z0.
  simpl.
  exists z.
  split. assumption.
  apply Z.leb_le.
  assumption.
  omega.
Qed.


(** # <font size="5"><b> Create Lock </b></font> # *)

Theorem rule_Newlock invs sp r: correct 
  (Abool true)
  Newlock 
  (fun l => Aulock ((Enum l,r,Enum l,None,false),(0,nil),(0,nil),nil) empb empb) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  intros.
  simpl.
  intros.
  exists r.
  simpl in SAT.
  intros.
  rewrite phplus_comm.
  unfold phplus.
  rewrite SAT0.
  reflexivity.
  assumption.
Qed.


(** # <font size="5"><b> Initialize Lock </b></font> # *)

Theorem rule_g_initl invs sp l wt ot O i params: correct 
  (Aulock l wt ot ** subsas params (invs i wt ot) ** Aobs O)
  nop
  (fun _ => Alock ((Aof l, Rof l, Lof l, Xof l, Pof l), (i,params), Mof l, M'of l) ** Aobs O) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  left. left. left. left. left. left. left. left. left. right.
  simpl in *.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest))))))))))))))).
  destruct rest as (tmp1,(tmp2,tmp3)).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp3p4,(o3,(o4,(c3,(c4,(ghpdefc3c4,(bc3,(bc4,(bc34,(opo3o4,rest1))))))))))))))).
  exists l, O, wt, ot, i, params, (Aof l).
  split.
  apply Z.eqb_eq. reflexivity.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split.
  tauto.
  split.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp3p4, o3, o4, c3, c4, ghpdefc3c4, bc3, bc4, bc34, opo3o4.
  split.
  tauto.
  split.
  exists p4, (emp knowledge).
  exists.
  apply phpdef_emp.
  exists bp4, boundph_emp.
  exists.
  rewrite phplus_emp.
  tauto.
  exists (Some (map evalol O)), None.
  exists c4, (emp (option nat*nat)).
  exists.
  apply ghpdef_emp.
  exists bc4, boundgh_emp.
  exists.
  rewrite ghplus_emp.
  tauto.
  exists.
  tauto.
  split.
  apply fs_op.
  apply Permutation_refl.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp5p6,(o5,(o6,(c5,(c6,(ghpdefc5c6,(bc5,(bc6,(bc56,(opo5o6,rest2))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp5p6, o5, o6, c5, c6.
  exists ghpdefc5c6, bc5, bc6, bc56.
  exists.
  inversion OPLUS.
  rewrite <- H0 in opo5o6.
  tauto.
  rewrite <- H0 in opo5o6.
  inversion opo5o6.
  apply fs_op.
  apply Permutation_trans with o0.
  assumption.
  assumption.
  apply sn_op.
  apply Permutation_trans with o0.
  assumption.
  assumption.
  tauto.
  rewrite phplus_emp.
  rewrite ghplus_emp.
  tauto.
  tauto.
  tauto.
Qed.


(** # <font size="5"><b> Acquire Lock </b></font> # *)

Theorem rule_Acquire invs sp el l (O: list (olocation exp)): correct
  (Abool (Z.eqb ([[el]]) ([[Aof l]])) &* Aprop (prcl (evalol (Oof l)) (map evalol O)) &* Alock l ** Aobs O)
  (Acquire el) 
  (fun _ => EX wt, (EX ot, (Aobs (Oof l::O) ** Alocked l wt ot ** (subsas (snd (Iof l)) (invs (fst (Iof l)) wt ot))))) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  simpl.
  intros.
  destruct SAT as (EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,(p12,c12))))))))))))))))))).
  subst.
  unfold id in *.

  assert (o1n: o1 = None).
  {
  inversion tmp2.
  rewrite <- H1 in opo1o2.
  inversion opo1o2.
  reflexivity.
  }
  rewrite o1n in *.

  exists O, l.
  exists p1, p2.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists o2, None, C1, C2.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. apply oplus_comm. assumption.
  exists.
  split. assumption.
  exists p1, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, (Some (map evalol O)), C1, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply oplus_comm. assumption.
  split.
  assumption.
  split.
  apply fs_op.
  apply Permutation_refl.
  repeat php_.
  split; reflexivity.
  split.
  intros.
  exists v, v0.
  destruct SAT as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp3,(tmp4,(p34,c34)))))))))))))))))).
  subst.

  assert (phpdefp23p24: phplusdef p2 p3 /\ phplusdef p2 p4). repeat php_.
  assert (ghpdefp23p24: ghplusdef C2 C3 /\ ghplusdef C2 C4). repeat php_.

  assert (o4n: O4 = None).
  {
  inversion tmp3.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  reflexivity.
  }
  rewrite o4n in *.

  exists (phplus p2 p3), p4.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (evalol (Oof l) :: map evalol O)), None, (ghplus C2 C3), C4.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  inversion OPLUS.
  rewrite <- H0 in opO3O4.
  inversion opO3O4.
  rewrite <- H in tmp3.
  inversion tmp3.
  rewrite <- H0 in *.
  rewrite <- H1 in *.
  inversion OPLUS.
  inversion tmp3.
  rewrite <- H5 in opO3O4.
  inversion opO3O4.
  apply fs_op.
  apply Permutation_trans with o'1.
  assumption.
  apply Permutation_trans with o0.
  assumption.
  assumption.
  split.
  apply fs_op.
  apply Permutation_refl.
  split.
  assumption.
  split.
  rewrite phplus_assoc; repeat php_.
  repeat php_.
  split; reflexivity.
Qed.


(** # <font size="5"><b> Release Lock </b></font> # *)

Theorem rule_Release invs sp e l O wt ot: correct
   (Abool (Z.eqb ([[e]]) ([[Aof l]])) &* Aobs (Oof l::O) ** Alocked l wt ot ** (subsas (snd (Iof l)) (invs (fst (Iof l)) wt ot)))
   (Release e)
   (fun _ => Aobs O ** Alock l) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  simpl.
  intros.
  destruct SAT as (EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,tmp3)))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp2,(tmp4,tmp5))))))))))))))))).
  subst.
  assert (tmp: oplus (Some (evalol (Oof l) :: map evalol O)) None o /\ O4 = None).
  {
  inversion tmp1.
  rewrite <- H1 in opo1o2.
  inversion opo1o2.
  split.
  apply fs_op.
  apply Permutation_trans with o'; assumption.
  rewrite <- H3 in opO3O4.
  inversion opO3O4.
  reflexivity.
  }
  destruct tmp as (opo,o4n).
  rewrite o4n in *.

  exists O, l, wt, ot.
  exists p2, p1.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. rewrite phplus_comm; repeat php_.
  exists (Some (evalol (Oof l) :: map evalol O)), None, C2, C1.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. rewrite ghplus_comm; repeat php_.
  exists opo.
  split.
  split.
  assumption.
  exists (emp knowledge), p2.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (evalol (Oof l) :: map evalol O)), None.
  exists (emp (option nat*nat)), C2.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply fs_op. apply Permutation_refl.
  split. apply fs_op. apply Permutation_refl.
  split.
  exists p3, p4.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, None, C3, C4.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply None_op.
  tauto.
  repeat php_. tauto.
  exists.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp7,(tmp6,p5p6))))))))))))))))).
  cnj_.
  subst.
  assert (phpdefp15p16: phplusdef p1 p5 /\ phplusdef p1 p6). repeat php_.
  assert (ghpdefp15p16: ghplusdef C1 C5 /\ ghplusdef C1 C6). repeat php_.
  exists (phplus p1 p5), p6.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists (Some (map evalol O)), None.
  exists (ghplus C1 C5), C6.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. inversion tmp7.
  rewrite <- H1 in opO5O6.
  inversion opO5O6.
  rewrite <- H4 in OPLUS.
  inversion OPLUS.
  apply fs_op.
  apply Permutation_trans with o'.
  assumption.
  apply Permutation_trans with o'0.
  assumption.
  assumption.
  exists.
  apply fs_op. apply Permutation_refl.
  exists. assumption.
  rewrite phplus_assoc; repeat php_.
  rewrite ghplus_assoc; repeat php_.
  tauto.
  rewrite phplus_comm; repeat php_.
  rewrite ghplus_comm; repeat php_.
Qed.


(** # <font size="5"><b> Create CV </b></font> # *)

Theorem rule_Newcond invs sp r X P: correct
  (Abool true)
  Newcond
  (fun v => Aucond ((Enum v,r,Enum v,X,P),(0,nil),(0,nil),nil)) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  simpl.
  intros.
  exists r, P, X.
  intros.
  unfold phplusdef in PHPDEF.
  specialize PHPDEF with (evall ((Enum v,r,Enum v,X,P),(0,nil),(0,nil),nil)).
  unfold phplus.
  rewrite SAT0 in *.
  destruct (p (evall ((Enum v,r,Enum v,X,P),(0,nil),(0,nil),nil))).
  destruct k; contradiction.
  reflexivity.
Qed.


(** # <font size="5"><b> Initialize CV </b></font> # *)

Theorem rule_g_initc invs sp m m' v l wt ot: correct 
  (Aulock l wt ot ** Aucond v)
  nop
  (fun _ => Aulock l wt ot ** Aicond ((Aof v, Rof v, Aof l, Xof v, Pof v), Iof v, m, m')) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  left. left. left. left. left. left. left. left. right.
  simpl in *.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest))))))))))))))).
  exists v, l, m, m', wt, ot, (Aof v).
  split.
  apply Z.eqb_eq. reflexivity.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split.
  tauto.
  split.
  exists p2, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o2, None.
  exists c2, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  destruct o2.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  split.
  tauto.
  split.
  intros.
  destruct SAT as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp3p4,(o3,(o4,(c3,(c4,(ghpdefc3c4,(bc3,(bc4,(bc34,(opo3o4,rest1))))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp3p4, o3, o4, c3, c4, ghpdefc3c4, bc3, bc4, bc34.
  exists.
  inversion OPLUS.
  rewrite H0.
  assumption.
  apply oplus_trans with o0.
  rewrite H0.
  assumption.
  assumption.
  tauto.
  repeat php_.
  tauto.
  tauto.
Qed.


(** # <font size="5"><b> Finalize CV </b></font> # *)

Theorem rule_g_finlc invs sp v l: correct 
  ((Abool (Z.eqb ([[Lof v]]) ([[Aof l]])) &* Aprop (spurious_ok sp (evall l) (evall v) invs)) &* Alock l ** Aicond v)
  nop
  (fun _ => Alock l ** Acond v) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  left. left. left. left. left. left. left. right.
  simpl in *.
  destruct SAT as (EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest)))))))))))))))).
  exists v, l, (Aof v).
  split. split.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  apply Z.eqb_eq. reflexivity.
  destruct EQ. assumption.
  destruct EQ. assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split. tauto.
  split.
  exists p2, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o2, None.
  exists c2, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  destruct o2.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  split.
  tauto.
  split.
  intros.
  destruct SAT as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp3p4,(o3,(o4,(c3,(c4,(ghpdefc3c4,(bc3,(bc4,(bc34,(opo3o4,rest1))))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp3p4, o3, o4, c3, c4, ghpdefc3c4, bc3, bc4, bc34.
  exists.
  inversion OPLUS.
  rewrite H0.
  assumption.
  apply oplus_trans with o0.
  rewrite H0.
  assumption.
  assumption.
  tauto.
  repeat php_.
  tauto.
  tauto.
Qed.


(** # <font size="5"><b> Wait on CV </b></font> # *)

Theorem rule_Wait invs sp l v el ev O wt ot: correct
  ((Abool (andb (Z.eqb ([[ev]]) ([[Aof v]]))
    (andb (Z.eqb ([[el]]) ([[Aof l]]))
    (andb (Z.eqb ([[Lof v]]) ([[Aof l]]))
    (safe_obs (evall v) (S (wt ([[Aof v]]))) (ot ([[Aof v]])))))) &*
    (Aprop (prcl (evalol (Oof v)) (map evalol O)) &*
    Aprop (prcl (evalol (Oof l)) (map evalol (M'of v ++ O)))) &* 
    ((subsas (snd (Iof l)) (invs (fst (Iof l)) (upd Z.eq_dec wt ([[Aof v]]) (S (wt ([[Aof v]])))) ot)) ** 
    Aobs (Oof l::O) ** Acond v ** Alocked l wt ot)))
  (Wait ev el) 
  (fun _ => EX wt', (EX ot', (Aobs (Oof l :: M'of v ++ O) ** Acond v ** Alocked l wt' ot' **
    (subsas (snd (Iof l)) (invs (fst (Iof l)) wt' ot')) ** 
    (subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb))))) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  simpl.
  intros.
  destruct SAT as ((EQ1,EQ2),(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,tmp3)))))))))))))))))).
  exists O, l, v.
  exists p, (emp knowledge).
  exists.
  apply phpdef_emp.
  exists bp, boundph_emp.
  exists.
  rewrite phplus_emp.
  assumption.
  exists o, None, g, (emp (option nat*nat)).
  exists.
  apply ghpdef_emp.
  exists bg, boundgh_emp.
  exists.
  rewrite ghplus_emp.
  assumption.
  exists.
  destruct o.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  split.
  exists wt, ot.
  split.
  split; assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, o1, o2, C1, C2, ghpdefC1C2, BC1, BC2, BC1C2, opo1o2.
  split.
  assumption.
  tauto.
  split.
  intros.
  exists v0, v1.
  replace (phplus (emp knowledge) p') with p'.
  replace (ghplus (emp (option nat * nat)) g') with g'.
  destruct SAT as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(ops78,(tmp5,(p78,C78)))))))))))))))))).
  exists p7, p8, phpdefp7p8, bp7, bp8, bp78, O7, O8, C7, C8, ghpdefC7C8, BC7, BC8, bc78.
  exists.
  inversion OPLUS.
  rewrite <- H0 in opO7O8.
  inversion opO7O8.
  apply None_op.
  apply oplus_trans with o0.
  rewrite H0. 
  assumption.
  assumption.
  tauto.
  rewrite ghplus_comm.
  symmetry.
  apply ghplus_emp.
  apply ghpdef_comm.
  apply ghpdef_emp.
  rewrite phplus_comm.
  symmetry.
  apply phplus_emp.
  apply phpdef_comm.
  apply phpdef_emp.
  rewrite phplus_emp.
  rewrite ghplus_emp.
  tauto.
Qed.

(** # <font size="5"><b> Notify CV </b></font> # *)

Theorem rule_Notify invs sp ev v l O wt ot: correct
  (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (Z.eqb ([[ev]]) ([[Aof v]]))) &* 
    ((subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb)) |* Abool (Nat.leb (wt ([[Aof v]])) 0)) **
    Acond v ** Alocked l wt ot ** Aobs ((if Nat.ltb 0 (wt ([[Aof v]])) then (M'of v) else nil) ++ O))
  (Notify ev)
  (fun _ => Acond v ** Alocked l (upd Z.eq_dec wt ([[Aof v]]) (wt ([[Aof v]]) - 1)%nat) ot ** Aobs (O)) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  simpl.
  intros.
  destruct SAT as (EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,tmp3)))))))))))))))))).
  exists O, wt, ot, l, v.
  split.
  tauto.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, o1, o2, C1, C2, ghpdefC1C2, BC1, BC2, BC1C2, opo1o2.
  split.
  tauto.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp2,(tmp4,tmp5))))))))))))))))).
  exists p3, p4, phpdefp3p4, bp3, bp4, bp34, O3, O4, C3, C4, BC3, BC4, ghpdefC3C4, bc34, opO3O4.
  split.
  tauto.
  split.
  destruct tmp4 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp7,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56, opO5O6.
  split.
  tauto.
  split.
  exists p6, (emp knowledge).
  exists.
  apply phpdef_emp.
  exists bp6, boundph_emp.
  exists.
  rewrite phplus_emp.
  assumption.
  exists (Some (map evalol ((if Nat.ltb 0 (wt ([[Aof v]])) then (M'of v) else nil) ++ O))), None.
  exists C6, (emp (option nat*nat)).
  exists.
  apply ghpdef_emp.
  exists BC6, boundgh_emp.
  exists.
  rewrite ghplus_emp.
  assumption.
  exists. assumption.
  split.
  apply fs_op.
  apply Permutation_refl.
  split.
  intros.
  destruct SAT as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(tmp9,(tmp8,p7p8))))))))))))))))).
  exists p7, p8, phpdefp7p8, bp7, bp8, bp78, O7, O8, C7, C8, ghpdefC7C8, BC7, BC8, bc78.
  exists.
  inversion OPLUS.
  rewrite <- H0 in opO7O8.
  inversion opO7O8.
  apply None_op.
  apply oplus_trans with o0.
  rewrite H0.
  assumption.
  assumption.
  split.
  assumption.
  split.
  assumption.
  tauto.
  rewrite phplus_emp.
  rewrite ghplus_emp.
  tauto.
  tauto.
  tauto.
  tauto.
Qed.


(** # <font size="5"><b> NotifyAll CV </b></font> # *)

Theorem rule_NotifyAll invs sp ev v l wt ot: correct 
  ((Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (andb (Z.eqb ([[ev]]) ([[Aof v]])) (ifb ((list_eq_dec (olocation_eq_dec exp_eq_dec) (M'of v) nil))))) &* 
    Aprop (subsas (snd (Mof v)) (invs (fst (Mof v)) empb empb) = Abool true)) ** Acond v ** Alocked l wt ot)
  (NotifyAll ev)
  (fun _ => Acond v ** Alocked l (upd Z.eq_dec wt ([[Aof v]]) 0%nat) ot) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,(p12,c12)))))))))))))))))).
  exists wt, ot, l, v.
  exists p1,p2,phpdefp1p2,bp1,bp2,bp12,o1,o2,C1,C2,ghpdefC1C2,BC1,BC2,BC1C2,opo1o2.
  split.
  assumption.
  split.
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp3,(tmp4,(p34,c34)))))))))))))))))).
  exists p3,p4,phpdefp3p4,bp3,bp4,bp34,O3,O4,C3,C4,BC3,BC4,ghpdefC3C4,bc34,opO3O4.
  split.
  assumption.
  split.
  exists p4, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, O4, C4, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  destruct O4.
  apply sn_op.
  apply Permutation_refl.
  apply None_op.
  split. assumption.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp7,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, None, O'', C5, C6, ghpdefC5C6, BC5, BC6, bc56.
  exists.
  destruct O''.
  apply sn_op.
  apply Permutation_refl.
  apply None_op.
  tauto.
  split; repeat php_.
  split; assumption. 
  split; assumption.
Qed.


(** # <font size="5"><b> Charge Obligation </b></font> # *)

Theorem rule_g_chrg invs sp v l wt ot O: correct
  (Abool (Z.eqb ([[Lof v]]) ([[Aof l]])) &* Acond v ** Aobs O ** Alocked l wt ot) 
  nop
  (fun _ => Acond v ** Aobs (Oof v::O) ** Alocked l wt (upd Z.eq_dec ot ([[Aof v]]) (ot ([[Aof v]]) + 1)%nat)) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  left. right.
  simpl in *.
  destruct SAT as (EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,(p12,c12))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp2,(tmp4,(p34,c34)))))))))))))))))).
  subst.

  assert (o4n: O4 = None).
  {
  inversion tmp2.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  reflexivity.
  }
  rewrite o4n in *.

  exists O, wt, ot, l, v, (Aof v).
  split.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  assumption.
  apply Z.eqb_eq.
  reflexivity.
  exists p1, (phplus p3 p4).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o1, o2, C1, (ghplus C3 C4).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists p3, p4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists O3, None.
  exists C3, C4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists.
  exists p4, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, None.
  exists C4, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  apply None_op.
  split. assumption.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp7,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56.
  split.
  inversion OPLUS.
  rewrite <- H0 in opO5O6.
  inversion opO5O6.
  apply None_op.
  eapply oplus_trans with o0.
  rewrite H0.
  assumption.
  assumption.
  split. assumption.
  split. assumption.
  repeat php_.
  split.
  repeat php_.
  repeat php_.
  split; reflexivity.
  split; reflexivity.
Qed.

Theorem rule_g_chrgu invs sp v l wt ot O:
  correct (Abool (Z.eqb ([[Lof v]]) ([[Aof l]])) &* Aicond v ** Aobs O ** Aulock l wt ot)
  nop
  (fun _ => Aicond v ** Aobs (Oof v::O) ** Aulock l wt (upd Z.eq_dec ot ([[Aof v]]) (ot ([[Aof v]]) + 1)%nat)) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  right.
  simpl in *.
  destruct SAT as (EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,(p12,c12))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp2,(tmp4,(p34,c34)))))))))))))))))).
  subst.

  assert (o4n: O4 = None).
  {
  inversion tmp2.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  reflexivity.
  }
  rewrite o4n in *.

  exists O, wt, ot, l, v, (Aof v).
  split.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  assumption.
  apply Z.eqb_eq.
  reflexivity.
  exists p1, (phplus p3 p4).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o1, o2, C1, (ghplus C3 C4).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists p3, p4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists O3, None.
  exists C3, C4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists.
  exists p4, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, None.
  exists C4, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  apply None_op.
  split. assumption.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp7,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56.
  split.
  inversion OPLUS.
  rewrite <- H0 in opO5O6.
  inversion opO5O6.
  apply None_op.
  eapply oplus_trans with o0.
  rewrite H0.
  assumption.
  assumption.
  split. assumption.
  split. assumption.
  repeat php_.
  split.
  repeat php_.
  repeat php_.
  split; reflexivity.
  split; reflexivity.
Qed.


(** # <font size="5"><b> Discharge Obligation </b></font> # *)

Theorem rule_g_disch invs sp v l wt ot O: correct
  (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (safe_obs (evall v) (wt ([[Aof v]])) ((ot ([[Aof v]]) - 1)))) &*
    Acond v ** Aobs (Oof v::O) ** Alocked l wt ot)
  nop
  (fun _ => Acond v ** Aobs O ** Alocked l wt (upd Z.eq_dec ot ([[Aof v]]) (ot ([[Aof v]]) - 1)%nat)) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  left. left. left. right.
  simpl in *.
  destruct SAT as (EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,(p12,c12))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp2,(tmp4,(p34,c34)))))))))))))))))).
  subst.

  assert (o4n: O4 = None).
  {
  inversion tmp2.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  reflexivity.
  }
  rewrite o4n in *.

  exists O, wt, ot, l, v, (Aof v).
  split.
  apply Coq.Bool.Bool.andb_true_iff in EQ.
  destruct EQ as (EQ1,EQ2).
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  assumption.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  apply Z.eqb_eq.
  reflexivity.
  assumption.
  exists p1, (phplus p3 p4).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o1, o2, C1, (ghplus C3 C4).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists p3, p4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists O3, None.
  exists C3, C4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists.
  exists p4, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, None.
  exists C4, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  apply None_op.
  split. assumption.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp7,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56.
  split.
  inversion OPLUS.
  rewrite <- H0 in opO5O6.
  inversion opO5O6.
  apply None_op.
  eapply oplus_trans with o0.
  rewrite H0.
  assumption.
  assumption.
  split. assumption.
  split. assumption.
  repeat php_.
  split.
  repeat php_.
  repeat php_.
  split; reflexivity.
  split; reflexivity.
Qed.

Theorem rule_g_dischu invs sp v l wt ot O: correct
  (Abool (andb (Z.eqb ([[Lof v]]) ([[Aof l]])) (safe_obs (evall v) (wt ([[Aof v]])) ((ot ([[Aof v]]) - 1)))) &*
    Aicond v ** Aobs (Oof v::O) ** Aulock l wt ot)
  nop
  (fun _ => Aicond v ** Aobs O ** Aulock l wt (upd Z.eq_dec ot ([[Aof v]]) (ot ([[Aof v]]) - 1)%nat)) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  left. left. right.
  simpl in *.
  destruct SAT as (EQ,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,(p12,c12))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(O3,(O4,(C3,(C4,(BC3,(BC4,(ghpdefC3C4,(bc34,(opO3O4,(tmp2,(tmp4,(p34,c34)))))))))))))))))).
  subst.

  assert (o4n: O4 = None).
  {
  inversion tmp2.
  rewrite <- H1 in opO3O4.
  inversion opO3O4.
  reflexivity.
  }
  rewrite o4n in *.

  exists O, wt, ot, l, v, (Aof v).
  split.
  apply Coq.Bool.Bool.andb_true_iff in EQ.
  destruct EQ as (EQ1,EQ2).
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  assumption.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  apply Z.eqb_eq.
  reflexivity.
  assumption.  exists p1, (phplus p3 p4).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o1, o2, C1, (ghplus C3 C4).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists p3, p4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists O3, None.
  exists C3, C4.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists. assumption.
  exists.
  exists p4, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, None.
  exists C4, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  apply None_op.
  split. assumption.
  split.
  intros.
  destruct SAT as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp56,(O5,(O6,(C5,(C6,(ghpdefC5C6,(BC5,(BC6,(bc56,(opO5O6,(tmp7,(tmp6,p5p6))))))))))))))))).
  exists p5, p6, phpdefp5p6, bp5, bp6, bp56, O5, O6, C5, C6, ghpdefC5C6, BC5, BC6, bc56.
  split.
  inversion OPLUS.
  rewrite <- H0 in opO5O6.
  inversion opO5O6.
  apply None_op.
  eapply oplus_trans with o0.
  rewrite H0.
  assumption.
  assumption.
  split. assumption.
  split. assumption.
  repeat php_.
  split.
  repeat php_.
  repeat php_.
  split; reflexivity.
  split; reflexivity.
Qed.


(** # <font size="5"><b> Create Goust Counter </b></font> # *)

Theorem rule_g_newctr invs sp: correct 
  (Abool true) 
  nop
  (fun _ => EX gc, Actr (Enum gc) 0) sp invs.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  left. left. left. left. left. left. right.
  simpl in *.
  intros.
  destruct SAT0 as (n0,EQ).
  exists v.
  unfold ghplus.
  unfold ghplusdef in GHPDEF.
  specialize GHPDEF with v.
  rewrite EQ in *.
  destruct (g v) eqn:CV.
  destruct p0.
  destruct o0.
  contradiction.
  exists (plus n1 n0).
  unfold lift'.
  reflexivity.
  exists n0.
  exists.
Qed.


(** # <font size="5"><b> Increment Goust Counter </b></font> # *)

Theorem rule_g_ctrinc invs sp gc n: correct
  (Actr gc n) 
  nop
  (fun _ => Actr gc (S n)%nat ** Atic gc) invs sp.
Proof.
  unfold correct.
  intros. destruct n0. reflexivity.
  left. left. left. left. right.
  simpl in SAT.
  destruct SAT as (m,ggc).
  simpl.
  exists n,gc.
  exists p, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o, None.
  exists g, (emp (option nat * nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply fs_oplus.
  split.
  exists m. assumption.
  split.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,tmp3))))))))))))))))).
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2,C1, C2, ghpdefC1C2, BC1, BC2, bc12.
  exists. inversion OPLUS. rewrite H0. assumption. apply oplus_trans with o0; try assumption. rewrite H0. assumption.
  split; try assumption.
  split; try assumption.
  split; repeat php_.
Qed.


(** # <font size="5"><b> Decrement Goust Counter </b></font> # *)

Theorem rule_g_ctrdec invs sp c n: correct
  (Actr c n ** Atic c) 
  nop
  (fun _ => Actr c (n-1)%nat &* Abool (Nat.ltb 0 n)) invs sp.
Proof.
  unfold correct.
  intros. destruct n0. reflexivity.
  left. left. left. left. left. right.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest))))))))))))))).
  destruct rest as (tmp1,(tmp2,tmp3)).
  exists n, c, p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split.
  tauto.
  split.
  exists (emp knowledge), p2.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, o2.
  exists c2, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  destruct o2.
  apply sn_op.
  apply Permutation_refl.
  apply None_op.
  split.
  assumption.
  split.
  intros.
  split.
  rewrite ghplus_comm.
  rewrite ghplus_emp.
  unfold id in *.
  destruct SAT as (n1,rest).
  exists n1.
  assumption.
  repeat php_.
  destruct tmp1 as (n1,c1c).
  destruct tmp2 as (n2,c2c).
  unfold boundgh in bc12.
  unfold ghplus in bc12.
  specialize bc12 with (x:=([[c]])).
  rewrite c1c in bc12.
  destruct c2c as (o',c2c).
  rewrite c2c in bc12.
  apply Nat.ltb_lt.
  apply le_trans with (n1 + S n2)%nat.
  omega.
  apply bc12.
  reflexivity.
  rewrite phplus_comm.
  rewrite phplus_emp.
  rewrite ghplus_emp.
  auto.
  repeat php_.
  auto.
Qed.


(** # <font size="5"><b> Frame Rule </b></font> # *)

Theorem rule_frame a a' c invs sp:
  forall f (RULE: correct a c a' invs sp),
    correct (a ** f) c (fun z => a' z ** f) invs sp.
Proof.
  unfold correct.
  intros. destruct n. reflexivity.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  assert (sata:=tmp1).
  eapply RULE in sata.
  rewrite <- p1p2.
  rewrite <- c1c2.
  eapply sat_frame with (S n).
  apply sat_plus with o1 o2; try assumption.
  apply sata.
  omega.
  assumption.
  assumption.
Qed.

(** # <font size="5"><b> Duplicate Lock Permission </b></font> # *)

Theorem rule_dupl l:
  Alock l |= Alock l ** Alock l.
Proof.
  simpl.
  intros.
  exists p, (fun x => if location_eq_dec Z.eq_dec x (evall l) then Some Lock else None).
  exists.
  unfold phplusdef.
  intros.
  destruct (location_eq_dec Z.eq_dec x (evall l)).
  rewrite e.
  destruct SAT as [S|S].
  rewrite S. trivial.
  destruct S as (wt,(ot,S)). rewrite S. trivial.
  destruct (p x).
  destruct k; trivial.
  trivial.
  exists bp.
  exists.
  unfold boundph.
  intros.
  destruct (location_eq_dec Z.eq_dec x (evall l)); inversion H.
  exists.
  unfold boundph.
  intros.
  unfold phplus in H.
  destruct (location_eq_dec Z.eq_dec x (evall l)); inversion H.
  rewrite e in *.
  destruct SAT as [S|S].
  rewrite S in *. inversion H.
  destruct S as (wt,(ot,S)). rewrite S in *. inversion H.
  destruct (p x) eqn:px.
  destruct k; inversion H.
  eapply bp. rewrite <- H2. apply px.
  inversion H.
  exists o, None, g, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  destruct o.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  split. assumption.
  split.
  destruct (location_eq_dec Z.eq_dec (evall l) (evall l)).
  left. reflexivity. contradiction.
  split.
  unfold phplus.
  apply functional_extensionality.
  intros.
  destruct (location_eq_dec Z.eq_dec x (evall l)).
  rewrite e.
  destruct SAT as [S|S].
  rewrite S. reflexivity.
  destruct S as (wt,(ot,S)). rewrite S. reflexivity.
  destruct (p x).
  destruct k; reflexivity.
  reflexivity.
  repeat php_.
Qed.


(** # <font size="5"><b> Duplicate CV Permission </b></font> # *)

Theorem rule_dupc l:
  Acond l |= Acond l ** Acond l.
Proof.
  simpl.
  intros.
  exists p, (fun x => if location_eq_dec Z.eq_dec x (evall l) then Some Cond else None).
  exists.
  unfold phplusdef.
  intros.
  destruct (location_eq_dec Z.eq_dec x (evall l)).
  rewrite e.
  rewrite SAT. trivial.
  destruct (p x).
  destruct k; trivial.
  trivial.
  exists bp.
  exists.
  unfold boundph.
  intros.
  destruct (location_eq_dec Z.eq_dec x (evall l)); inversion H.
  exists.
  unfold boundph.
  intros.
  unfold phplus in H.
  destruct (location_eq_dec Z.eq_dec x (evall l)); inversion H.
  rewrite e in *.
  rewrite SAT in *. inversion H.
  destruct (p x) eqn:px.
  destruct k; inversion H.
  eapply bp. rewrite <- H2. apply px.
  inversion H.
  exists o, None, g, (emp (option nat*nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  destruct o.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
  split. assumption.
  split.
  destruct (location_eq_dec Z.eq_dec (evall l) (evall l)).
  reflexivity. contradiction.
  split.
  unfold phplus.
  apply functional_extensionality.
  intros.
  destruct (location_eq_dec Z.eq_dec x (evall l)).
  rewrite e.
  rewrite SAT. reflexivity.
  destruct (p x).
  destruct k; reflexivity.
  reflexivity.
  repeat php_.
Qed.


(** # <font size="5"><b> Rule Exists </b></font> # *)

Theorem rule_exists1 invs sp A c P Q :
  (forall (x:A), correct (P x) c Q invs sp) ->
  correct (EX x, P x) c Q invs sp.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT as (v,SAT).
  eapply sat_weak_imp with (n:=n); try assumption.
  eapply H; try assumption.
  apply SAT.
  simpl.
  intros.
  assumption.
  omega.
Qed.

Theorem rule_exists invs sp A c P Q :
  (forall (x:A), correct (P x) c (fun z => (Q z) x) invs sp) ->
  correct (EX x, P x) c (fun z => EX x, (Q z) x) invs sp.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT as (v,SAT).
  eapply sat_weak_imp with (n:=n); try assumption.
  apply H; try assumption.
  apply SAT.
  simpl.
  intros.
  exists v.
  assumption.
  omega.
Qed.

Theorem rule_exists2 invs sp A c P Q :
  (exists (x:A), correct P c (fun z => (Q z) x) invs sp) ->
  correct P c (fun z => EX x, (Q z) x) invs sp.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct H as (x,SAT1).
  eapply sat_weak_imp with (n:=n); try assumption.
  apply SAT1; try assumption.
  simpl.
  intros.
  exists x.
  assumption.
  omega.
Qed.


(** # <font size="5"><b> Rule Consequence </b></font> # *)

Theorem rule_conseq a1 a2 a1' a2' c invs sp:
  forall (C: correct a1 c a2 invs sp)
         (IMP1: a1' |= a1)
         (IMP2: forall z, a2 z |= a2' z),
    correct a1' c a2' invs sp.
Proof.
  unfold correct.
  intros.
  eapply sat_weak_imp with (n:=n)(a:=a2). 
  assumption.
  assumption.
  apply C.
  assumption.
  assumption.
  apply IMP1.
  assumption.
  assumption.
  assumption.
  intros.
  apply IMP2.
  assumption.
  assumption.
  assumption.
  omega.
Qed.

Theorem rule_conseq1 a1 a2 a1' c invs sp:
  forall (C: correct a1 c a2 invs sp)
         (IMP1: a1' |= a1),
    correct a1' c a2 invs sp.
Proof.
  unfold correct.
  intros.
  eapply sat_weak_imp with (n:=n)(a:=a2). 
  assumption.
  assumption.
  apply C.
  assumption.
  assumption.
  apply IMP1.
  assumption.
  assumption.
  assumption.
  intros.
  assumption.
  omega.
Qed.

Theorem rule_conseq2 a1 a2 a2' c invs sp:
  forall (C: correct a1 c a2 invs sp)
         (IMP2: forall z, a2 z |= a2' z),
    correct a1 c a2' invs sp.
Proof.
  unfold correct.
  intros.
  eapply sat_weak_imp with (n:=n)(a:=a2). 
  assumption.
  assumption.
  apply C.
  assumption.
  assumption.
  assumption.
  assumption.
  omega.
Qed.

Theorem rule_comm a a':
  a ** a' |= a' ** a.
Proof.
  intros. apply sat_comm. assumption.
Qed.

Theorem rule_assoc a a' a'':
  (a ** a') ** a'' |= a ** (a' ** a'').
Proof.
  intros. apply sat_assoc; try assumption.
Qed.


Theorem rule_assoc_pure b a a':
  (Abool b &* a) ** a' |= (Abool b) &* (a ** a').
Proof.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest))))))))))))))).
  destruct rest as ((tmp0,tmp1),(tmp2,tmp3)).
  split. assumption.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split. assumption. split; assumption.
Qed.

Theorem rule_assoc_pure' b a a':
  (Abool b) &* (a ** a') |= (Abool b &* a) ** a'.
Proof.
  simpl.
  intros.
  destruct SAT as (bt,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest)))))))))))))))).
  destruct rest.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split. split; assumption. assumption.
Qed.

Theorem rule_assoc_pureP' b a a':
  (Aprop b) &* (a ** a') |= (Aprop b &* a) ** a'.
Proof.
  simpl.
  intros.
  destruct SAT as (bt,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest)))))))))))))))).
  destruct rest.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split. split; assumption. assumption.
Qed.

Theorem rule_assoc' a a' a'':
  a ** (a' ** a'') |= (a ** a') ** a''.
Proof.
  intros. apply sat_assoc; try assumption.
Qed.

Theorem rule_trans a a' a'':
  (a |= a') /\ (a' |= a'') -> a |= a''.
Proof.
  intros. apply H; try assumption. apply H; try assumption.
Qed.

Theorem rule_exists_dist A (a: A -> assn) a':
  (EX x, a x) ** a' |=  EX x, (a x ** a').
Proof.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest))))))))))))))).
  destruct rest as (tmp1,(tmp2,tmp3)).
  destruct tmp1 as (v,satv).
  exists v, p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split; try assumption.
  split; try assumption.
Qed.

Theorem rule_exists_dist1 A a (a': A -> assn):
  a ** (EX x, a' x) |=  EX x, (a ** (a' x)).
Proof.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest))))))))))))))).
  destruct rest as (tmp1,(tmp2,tmp3)).
  destruct tmp2 as (v,satv).
  exists v, p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split; try assumption.
  split; try assumption.
Qed.

Theorem rule_exists_dist2 A a (a': A -> assn):
  EX x, (a ** (a' x)) |= a ** (EX x, a' x).
Proof.
  simpl.
  intros.
  destruct SAT as (v,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest)))))))))))))))).
  destruct rest as (tmp1,(tmp2,tmp3)).
  exists p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split; try assumption.
  split; try assumption.
  exists v. assumption.
Qed.

Theorem rule_exists_dist' A (a: A -> assn) a':
  EX x, (a x ** a') |= (EX x, a x) ** a'.
Proof.
  simpl.
  intros.
  destruct SAT as (v,SAT).
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest))))))))))))))).
  destruct rest as (tmp1,tmp2).
  exists p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split.
  exists v. assumption.
  assumption.
Qed.

Theorem sat_exists_imps A (a a': A -> assn):
  forall (IMP1: forall x, a x |= a' x),
    (EX x, a x) |= (EX x, a' x).
Proof.
  simpl.
  intros.
  destruct SAT as (v,SAT).
  exists v.
  apply IMP1; try assumption.
Qed.

Theorem rule_star_pure a a':
  a ** a' |= a &* a'.
Proof.
  simpl. intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest))))))))))))))).
  destruct rest as (tmp1,(tmp2,(p1p2,c1c2))).
  subst.
  split.
  {
  inversion opo1o2.
  {
  rewrite <- H in *.
  apply sat_mon with None None; try assumption.
  apply None_op.
  }
  {
  rewrite <- H in *.
  apply sat_mon with (Some o0) None; try assumption.
  apply fs_op; assumption.
  }
  {
  rewrite <- H in *.
  apply sat_mon with None (Some o0); try assumption.
  apply sn_op; assumption.
  }
  }
  {
  rewrite phplus_comm; repeat php_.
  rewrite ghplus_comm; repeat php_.
  inversion opo1o2.
  {
  rewrite <- H0 in *.
  apply sat_mon with None None; repeat php_.
  apply None_op.
  }
  {
  rewrite <- H0 in *.
  apply sat_mon with None (Some o0); repeat php_.
  apply sn_op; assumption.
  }
  {
  rewrite <- H0 in *.
  apply sat_mon with (Some o0) None; repeat php_.
  apply fs_op; assumption.
  }
  }
Qed.

Theorem rule_pure_star a b:
  a &* (Abool b) |= a ** (Abool b).
Proof.
  simpl. intros.
  destruct SAT as (SAT,btrue).
  exists p, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o, None.
  exists g, (emp (option nat * nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply fs_oplus.
  split. assumption.
  split. assumption.
  split; repeat php_.
Qed.

Theorem rule_pure_star' a b:
  (Abool b) &* a |= (Abool b) ** a.
Proof.
  simpl. intros.
  destruct SAT as (SAT,btrue).
  exists (emp knowledge), p.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, o.
  exists (emp (option nat * nat)), g.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply sn_oplus.
  split. assumption.
  split. assumption.
  split; repeat php_.
Qed.

Theorem rule_prop_star a b:
  a &* (Aprop b) |= a ** (Aprop b).
Proof.
  simpl. intros.
  destruct SAT as (SAT,btrue).
  exists p, (emp knowledge).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists o, None.
  exists g, (emp (option nat * nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply fs_oplus.
  split. assumption.
  split. assumption.
  split; repeat php_.
Qed.

Theorem rule_prop_star' a b:
  (Aprop b) &* a |= (Aprop b) ** a.
Proof.
  simpl. intros.
  destruct SAT as (SAT,btrue).
  exists (emp knowledge), p.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, o.
  exists (emp (option nat * nat)), g.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply sn_oplus.
  split. assumption.
  split. assumption.
  split; repeat php_.
Qed.

Theorem rule_pure_prop_star a b1 b2:
  Abool b1 &* Aprop b2 &* a |= Abool b1 ** Aprop b2 ** a.
Proof.
  simpl. intros.
  destruct SAT as ((SAT,btrue),b2true).
  exists (emp knowledge), p.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, o.
  exists (emp (option nat * nat)), g.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply sn_oplus.
  split. assumption.
  split.
  exists (emp knowledge), p.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists None, o.
  exists (emp (option nat * nat)), g.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. apply sn_oplus.
  split. assumption.
  split.
  assumption.
  split; repeat php_.
  split; repeat php_.
Qed.

Theorem rule_pure_prop_star' a b1 b2:
  Abool b1 ** Aprop b2 ** a |= Abool b1 &* Aprop b2 &* a.
Proof.
  simpl. intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(b1true,(rest1,(p1p2,c1c2)))))))))))))))))).
  destruct rest1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp3p4,(o3,(o4,(c3,(c4,(ghpdefc3c4,(bc3,(bc4,(bc34,(opo3o4,(rest4,(rest5,(p3p4,c3c4)))))))))))))))))).
  split.
  split; assumption.
  subst.
  rewrite phplus_comm; try assumption.
  rewrite ghplus_comm; try assumption.
  assert (phpdefp13: phplusdef p1 p3 /\ phplusdef p1 p4). repeat php_.
  destruct phpdefp13 as (phpdefp13,phpdefp14).
  assert (ghpdefp13: ghplusdef c1 c3 /\ ghplusdef c1 c4). repeat php_.
  destruct ghpdefp13 as (ghpdefp13,ghpdefp14).
  destruct o4.
  apply sat_mon with (Some l) None; repeat php_.
  inversion opo3o4.
  rewrite <- H0 in opo1o2.
  inversion opo1o2.
  apply fs_op.
  apply Coq.Sorting.Permutation.Permutation_trans with o'; try assumption.
  rewrite phplus_comm; repeat php_.
  rewrite ghplus_comm; repeat php_.
  apply sat_mon with (Some l) None; repeat php_.
  apply fs_op.
  apply Coq.Sorting.Permutation.Permutation_refl.
  apply sat_mon with None o; repeat php_.
  destruct o. apply sn_op.
  apply Coq.Sorting.Permutation.Permutation_refl.
  apply None_op.
  rewrite phplus_comm; repeat php_.
  rewrite ghplus_comm; repeat php_.
  apply sat_mon with None None; repeat php_.
  apply None_op.
Qed.

Theorem rule_comm_pure a a':
  a &* a' |= a' &* a.
Proof.
  simpl. intros.
  destruct SAT as (SAT1, SAT2).
  split; assumption.
Qed.

Theorem rule_sat_mon_pure a a':
  a &* a' |= a.
Proof.
  simpl. intros. destruct SAT. assumption.
Qed.

Theorem rule_sat_mon a a':
  a ** a' |= a.
Proof.
  simpl. intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest))))))))))))))).
  destruct rest as (tmp1,(tmp2,(p1p2,c1c2))).
  subst.
  inversion opo1o2.
  {
  rewrite <- H in *.
  apply sat_mon with None None; repeat php_.
  apply None_op.
  }
  {
  rewrite <- H in *.
  apply sat_mon with (Some o0) None; repeat php_.
  apply fs_op; assumption.
  }
  {
  rewrite <- H in *.
  apply sat_mon with None (Some o0); repeat php_.
  apply sn_op; assumption.
  }
Qed.

Theorem sat_star_imps:
  forall a a' b b' p o C
         (SAT: sat p o C (a ** b))
         (IMP1: a |= a')
         (IMP2: b |= b'),
    sat p o C (a' ** b').
Proof.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest))))))))))))))).
  destruct rest as (tmp1,(tmp2,(p1p2,c1c2))).
  exists p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split. apply IMP1; assumption.
  split. apply IMP2; assumption.
  split; assumption.
Qed.


Theorem rule_perm_obs:
  forall O O' (Perm: Permutation.Permutation (map evalol O) (map evalol O')),
    Aobs O |= Aobs O'.
Proof.
  simpl. intros. inversion SAT.
  apply fs_op.
  apply Coq.Sorting.Permutation.perm_trans with (map evalol O).
  apply Coq.Sorting.Permutation.Permutation_sym. assumption. assumption.
Qed.

Theorem sat_array:
  forall v1 v2,
    (array (cell_loc v1) 0 |-> v2) |= (cell_loc v1 |-> v2).
Proof.
  unfold array. unfold cell_loc.
  simpl.
  unfold evall, evalol.
  simpl.
  unfold Aofo, Rofo, Lofo, Xofo, Pofo, Iof, Mof, Aof, Rof, Lof, Xof, Pof, Aofo, Rofo, Lofo, Xofo, Pofo.
  simpl.
  intros.
  destruct SAT as (v',(lev,pv)).
  exists v', lev.
  replace (([[v1]]) + 0) with ([[v1]]) in pv; try omega.
  assumption.
Qed.

Definition next_loc (l: location exp) : location exp := cell_loc (Eplus (Aof l) (Enum 1)).

Theorem sat_array1:
  forall v1 v2,
    (array (cell_loc v1) 1 |-> v2) |= (next_loc (cell_loc v1) |-> v2).
Proof.
  intros.
  destruct SAT as (v',(lev,pv)).
  exists v', lev. assumption.
Qed.

Theorem cell_loc_eval:
  forall v v' value (EQ: ([[v]]) = ([[v']])),
  (cell_loc v) |-> Enum value |=
  (cell_loc v') |-> Enum value.
Proof.
  simpl.
  unfold evall, evalol.
  simpl.
  unfold Aofo, Rofo, Lofo, Xofo, Pofo, Iof, Mof, Aof, Rof, Lof, Xof, Pof, Aofo, Rofo, Lofo, Xofo, Pofo.
  simpl.
  intros.
  rewrite EQ in *.
  assumption.
Qed.

Theorem cell_loc_eval1:
  forall v v' value (EQ: ([[v]]) = ([[v']])),
  (next_loc (cell_loc v) |-> Enum value) |=
(next_loc (cell_loc v') |-> Enum value).
Proof.
  simpl.
  unfold evall, evalol.
  simpl.
  unfold Aofo, Rofo, Lofo, Xofo, Pofo, Iof, Mof, Aof, Rof, Lof, Xof, Pof, Aofo, Rofo, Lofo, Xofo, Pofo.
  simpl.
  intros.
  rewrite EQ in *.
  assumption.
Qed.

Theorem rule_plus_evall:
  forall l z z',
    (cell_loc l |-> Eplus (Enum z) (Enum z')) |=  (cell_loc l |-> Enum (z + z')).
Proof.
  simpl.
  unfold evall, evalol.
  simpl.
  unfold Aofo, Rofo, Lofo, Xofo, Pofo, Iof, Mof, Aof, Rof, Lof, Xof, Pof, Aofo, Rofo, Lofo, Xofo, Pofo.
  simpl.
  intros.
  destruct SAT as (v',(lev,pv)).
  exists v', lev. assumption.
Qed.

Theorem rule_points_to_leak f1 f2 l v (LE: Qcle f2 f1):
  Apointsto f1 (cell_loc l) v |= Apointsto f2 (cell_loc l) v.
Proof.
  simpl. intros.
  destruct SAT as (f',(lez,pll)).
  exists (-f2 + f1 + f')%Qc.
  exists.
  replace 0%Qc with (0+0)%Qc.
  apply Qcplus_le_compat.
  rewrite Qcplus_comm.
  apply Qcle_minus_iff in LE. assumption. assumption.
  apply Qcplus_0_r.
  rewrite Qcplus_assoc.
  rewrite Qcplus_assoc.
  rewrite Qcplus_opp_r.
  rewrite Qcplus_0_l.
  assumption.
Qed.

Theorem rule_points_to_fraction f1 f2 l v:
  Apointsto f1 l v ** Apointsto f2 l v |= Apointsto (f1+f2) l v.
Proof.
  simpl. intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,rest))))))))))))))).
  destruct rest as (f1',(f2',(p1p2,c1c2))).
  destruct f1' as (f',(le',p1')).
  destruct f2' as (f'',(le'',p1'')).
  subst.
  unfold phplus.
  rewrite p1', p1''.
  exists (f'+f'')%Qc.
  exists.
  replace 0%Qc with (0+0)%Qc.
  apply Qcplus_le_compat; assumption. reflexivity.
  rewrite <- Qcplus_assoc.
  rewrite <- Qcplus_assoc.
  replace (f' + (f2 + f''))%Qc with (f2 + (f' + f''))%Qc. reflexivity.
  rewrite Qcplus_comm.
  rewrite <- Qcplus_assoc.
  replace (f'' + f2)%Qc with (f2 + f'')%Qc. reflexivity.
  apply Qcplus_comm.
Qed.

Theorem rule_points_to_fraction' f1 f2 l v (F1: Qclt 0 f1) (F2: Qclt 0 f2):
  Apointsto (f1+f2)%Qc l v |= Apointsto f1 l v ** Apointsto f2 l v.
Proof.
  simpl. intros.
  destruct SAT as (f',(le',pl)).

  assert (bu: boundph (upd (location_eq_dec Z.eq_dec) (emp knowledge) (evall l)
    (Some (Cell (f2 + f') ([[v]]))))).
  {
  apply boundph_upd; try assumption. repeat php_.
  intros.
  destruct H as (z',eq).
  inversion eq.
  unfold boundph in bp. apply bp in pl.
  destruct pl as (pl1,pl2).
  split.
  apply Qclt_le_trans with f2. assumption.
  rewrite <- Qcplus_0_r at 1.
  apply Qcplus_le_compat.
  apply Qcle_refl. assumption.
  apply Qcle_trans with (f1 + f2 + f')%Qc.
  replace (f2 + f')%Qc with (0 + f2 + f')%Qc.
  rewrite <- Qcplus_assoc.
  rewrite <- Qcplus_assoc.
  apply Qcplus_le_compat.
  apply Qclt_le_weak. assumption.
  apply Qcle_refl.
  rewrite <- Qcplus_assoc.
  apply Qcplus_0_l.
  assumption.
  }

  assert (bu1: boundph (upd (location_eq_dec Z.eq_dec) p (evall l) (Some (Cell f1 ([[v]]))))).
  {
  apply boundph_upd; try assumption.
  intros.
  destruct H as (z',eq).
  inversion eq.
  rewrite <- H0.
  unfold boundph in bp.
  apply bp in pl.
  split. assumption.
  destruct pl as (pl1,pl2).
  apply Qcle_trans with (f1 + f2 + f')%Qc.
  apply Qcle_minus_iff.
  rewrite Qcplus_comm.
  rewrite Qcplus_assoc.
  rewrite Qcplus_assoc.
  replace (- f1 + f1)%Qc with (f1 + (-f1))%Qc.
  rewrite Qcplus_opp_r.
  rewrite Qcplus_0_l.
  replace 0%Qc with (0+0)%Qc.
  apply Qcplus_le_compat; try assumption.
  apply Qclt_le_weak. assumption. reflexivity.
  apply Qcplus_comm. assumption.
  }


  exists (upd (location_eq_dec Z.eq_dec) p (evall l) (Some (Cell f1 ([[v]])))).
  exists (upd (location_eq_dec Z.eq_dec) (emp knowledge) (evall l) (Some (Cell (f2+f') ([[v]])))).
  exists.
  apply phpdef_comm.
  unfold phplusdef.
  intros.
  unfold upd.
  destruct (location_eq_dec Z.eq_dec x (evall l)). reflexivity.
  simpl. trivial.
  exists. assumption.
  exists. assumption.
  exists.
  unfold boundph. unfold phplus. unfold upd. simpl. intros.
  destruct (location_eq_dec Z.eq_dec x (evall l)).
  inversion H.
  unfold boundph in bp.
  apply bp in pl.
  rewrite Qcplus_assoc. assumption.
  destruct (p x) eqn:px. destruct k; simpl in H; try inversion H. rewrite <- H1.
  unfold boundph in bp.
  apply bp in px. assumption. inversion H.
  exists o, None.
  exists g, (emp (option nat * nat)).
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists. repeat php_.
  exists.
  destruct o. apply fs_op. apply Coq.Sorting.Permutation.Permutation_refl. apply None_op.
  split.
  exists 0%Qc.
  exists.
  apply Qcle_refl.
  unfold upd.
  destruct (location_eq_dec Z.eq_dec (evall l) (evall l)).
  rewrite Qcplus_0_r. reflexivity. contradiction.
  split.
  exists f', le'.
  unfold upd.
  destruct (location_eq_dec Z.eq_dec (evall l) (evall l)). reflexivity. contradiction.
  split.
  unfold phplus, upd.
  apply functional_extensionality.
  intros.
  destruct (location_eq_dec Z.eq_dec x (evall l)).
  rewrite e.
  rewrite Qcplus_assoc.
  symmetry. assumption.
  simpl.
  destruct (p x).
  destruct k; reflexivity. reflexivity.
  repeat php_.
Qed.

Theorem rule_points_to_value f1 f2 l v v':
  Apointsto f1 l v ** Apointsto f2 l v' |= Apointsto f1 l v ** Apointsto f2 l v' &* Aprop (([[v]]) = ([[v']])).
Proof.
  simpl. intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(rest1,(rest2,rest3))))))))))))))))).
  split.
  exists p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split; try assumption.
  split; try assumption.
  destruct rest1 as (f1',(le1,p1l)).
  destruct rest2 as (f2',(le2,p2l)).
  unfold phplusdef in phpdefp1p2.
  specialize phpdefp1p2 with (evall l).
  rewrite p1l in phpdefp1p2.
  rewrite p2l in phpdefp1p2.
  assumption.
Qed.  

Theorem next_plus2:
  forall f z v,
    Apointsto f (cell_loc (Eplus (Enum z) (Enum 2))) v |=
    Apointsto f (next_loc (next_loc (cell_loc (Enum z)))) v.
Proof.
  simpl.
  intros.
  unfold next_loc in *.
  unfold Aof,Aofo,Oof in *. simpl.
  unfold evall, evalol in *.
  simpl in *.
  unfold Aofo, Rofo, Lofo, Xofo, Pofo, Iof, Mof, Aof, Rof, Lof, Xof, Pof, Aofo, Rofo, Lofo, Xofo, Pofo in *.
  simpl in *.
  replace (z + 1 + 1)%Z with (z+2)%Z.
  assumption.
  omega.
Qed.

Theorem next_plus2':
  forall f z v,
    Apointsto f (next_loc (next_loc (cell_loc (Enum z)))) v |=
    Apointsto f (cell_loc (Eplus (Enum z) (Enum 2))) v .
Proof.
  simpl.
  intros.
  unfold next_loc in *.
  unfold Aof,Aofo,Oof in *. simpl.
  unfold evall, evalol in *.
  simpl in *.
  unfold Aofo, Rofo, Lofo, Xofo, Pofo, Iof, Mof, Aof, Rof, Lof, Xof, Pof, Aofo, Rofo, Lofo, Xofo, Pofo in *.
  simpl in *.
  replace (z + 1 + 1)%Z with (z+2)%Z in SAT.
  assumption.
  omega.
Qed.

Theorem rule_disjont:
  forall l l' v v' (EQ: ([[l]]) = ([[l']])),
    cell_loc l |-> v ** cell_loc l' |-> v' |= Abool false.
Proof.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(bc12,(opO1O2,(tmp1,(tmp2,tmp3))))))))))))))))).
  destruct tmp1 as (f1,(le1,p1l)).
  destruct tmp2 as (f2,(le2,p2l)).
  replace (evall (cell_loc l')) with (evall (cell_loc l)) in p2l.
  unfold boundph in bp12.
  assert (CO: (0<(1 + f1 + (1 + f2)))%Qc /\ ((1 + f1 + (1 + f2))<=1)%Qc).
  {
  apply bp12 with (evall (cell_loc l)) ([[v]]).
  unfold phplus.
  rewrite p1l, p2l. reflexivity.
  }
  destruct CO as (C,CO).
  rewrite Qcplus_assoc in CO.
  apply Qc_Le_le_mon1 in CO; try assumption.
  rewrite Qcplus_comm in CO.
  rewrite Qcplus_assoc in CO.
  apply Qc_Le_le_mon1 in CO; try assumption.
  exfalso.
  apply qcpluslelt with 1%Qc; try assumption.
  unfold Qclt. simpl. unfold QArith_base.Qlt. simpl. omega.
  unfold evall, evalol. simpl.
  unfold Aofo, Rofo, Lofo, Xofo, Pofo, Iof, Mof, Aof, Rof, Lof, Xof, Pof, Aofo, Rofo, Lofo, Xofo, Pofo.
  simpl. rewrite EQ. reflexivity.
Qed.

Theorem pointsto_loc_eval:
  forall l l' f v (EQ: (evall l) = (evall l')),
  Apointsto f l v |= Apointsto f l' v.
Proof.
  simpl.
  unfold evall, evalol.
  simpl.
  unfold Aofo, Rofo, Lofo, Xofo, Pofo, Iof, Mof, Aof, Rof, Lof, Xof, Pof, Aofo, Rofo, Lofo, Xofo, Pofo.
  simpl.
  intros.
  rewrite EQ in *.
  assumption.
Qed.
