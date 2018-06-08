Require Import ZArith.
Require Import Coq.Init.Nat.
Require Import List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sorting.Permutation.
Require Import Util_Z.
Require Import Util_list.
Require Import Programs.
Require Import Assertions.
Require Import WeakestPrecondition.
Require Import Wait4Graph.
Require Import ValidityOfConfigurations.
Require Import ProofRules.

Set Implicit Arguments.

(** # <font size="5"><b> Proof Rules </b></font> # *)

Lemma sat_frame:
  forall c f Q p1 p2 o1 o2 C1 C2 invs se
         (phpdefp1p2: phplusdef p1 p2) o1o2 (opo1o2: oplus o1 o2 o1o2) (bp1 : boundph p1) (bp2 : boundph p2) (bp12 : boundph (phplus p1 p2))
         (SATF: sat p2 o2 C2 f)
         (SATQ: sat p1 o1 C1 (weakest_pre c Q se invs)),
    sat (phplus p1 p2) o1o2 (ghplus C1 C2) (weakest_pre c (fun x : Z => (Q x) ** f) se invs).
Admitted.

Theorem rule_frame a a' c invs:
  forall f (RULE: correct a c a' invs),
    correct (a ** f) c (fun z => a' z ** f) invs.
Proof.
  unfold correct.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(ghpdefC1C2,(BC1,(BC2,(BC1C2,(opo1o2,(tmp1,(tmp2,(p1p2,c1c2)))))))))))))))))).
  assert (sata:=tmp1).
  apply RULE in sata.
  rewrite <- p1p2.
  rewrite <- c1c2.
  apply sat_frame with o1 o2; assumption.
  assumption.
  assumption.
Qed.

Theorem rule_Lookup invs f l e e': correct
  (Abool (Z.eqb ([[e]]) ([[Aof l]])) &* Apointsto f l e')
  (Lookup e)
  (fun r => Abool (Z.eqb r ([[e']])) &* Apointsto f l e') invs.
Proof.
Admitted.

Theorem rule_Mutate invs l e1 e2 e': correct
  (Abool (Z.eqb ([[e1]]) ([[Aof l]])) &* l |-> e')
  (Mutate e1 e2)
  (fun r => l |-> e2) invs.
Proof.
Admitted.

Theorem rule_Cons invs n: correct
  (Abool true)
  (Cons n)
  (fun r => fold_left Astar (map (fun x => (Enum (r + (Z.of_nat x)),0%Z,(0%Z,nil),Enum 0%Z,nil,(0%Z,nil),false) |-> Enum 0) (seq O n)) (Abool true)) invs.
Admitted.

Theorem rule_If c c1 c2 a a' a'' invs:
  forall (C: correct a c a' invs)
         (C1: forall z (TRUE: Z.lt 0 z), correct (a' z) c1 a'' invs)
         (C2: forall z (TRUE: Z.le z 0), correct (a' z) c2 a'' invs),
    correct a (If c c1 c2) a'' invs.
Admitted.

Theorem rule_While c c1 a a' invs:
  forall (C: correct a c a' invs)
         (C1: forall z (TRUE: Z.lt 0 z), correct (a' z) c1 a' invs),
    correct a (While c c1) (fun z => Abool (Z.ltb z 0) &* a' z) invs.
Admitted.

Theorem rule_comm a a':
  a ** a' |= a' ** a.
Admitted.

Theorem rule_assoc a a' a'':
  (a ** a') ** a'' |= a ** (a' ** a'').
Admitted.

Theorem rule_assoc' a a' a'':
  a ** (a' ** a'') |= (a ** a') ** a''.
Admitted.

(** # <font size="5"><b> Steps Preserve Validity of Configurations </b></font> # *)

Lemma Cons_preserves_validity:
  forall h t id a n tx
         (VALIDK: validk t h)
         (CMD: t id = Some (Cons n, tx))
         (NIN: forall z' : Z, In z' (map Z.of_nat (seq 0 n)) -> h (a + z')%Z = None),
    validk (upd Z.eq_dec t id (Some (tt, tx)))
      (dstr_cells h (map (fun x : nat => (a + Z.of_nat x)%Z) (seq 0 n)) (Some 0%Z)).
Admitted.

Lemma Lookup_preserves_validity:
  forall h t id tx e v
         (VALIDK: validk t h)
         (CMD: t id = Some (Lookup e, tx))
         (ALC: h ([[e]]) = Some v),
    validk (upd Z.eq_dec t id (Some (Val (Enum v), tx))) h.
Admitted.

Lemma Mutate_preserves_validity:
  forall h t id tx e1 e2 v
         (VALIDK: validk t h)
         (CMD: t id = Some (Mutate e1 e2, tx))
         (ALC: h ([[e1]]) = Some v),
    validk (upd Z.eq_dec t id (Some (tt, tx))) (upd Z.eq_dec h ([[e1]]) (Some ([[e2]]))).
Admitted.

Lemma If_preserves_validity:
  forall h t id tx c c1 c2
         (VALIDK: validk t h)
         (CMD: t id = Some (If c c1 c2, tx)),
    validk (upd Z.eq_dec t id (Some (c, If' c1 c2 tx))) h.
Admitted.

Lemma If1_preserves_validity:
  forall h t id tx e c1 c2
         (VALIDK: validk t h)
         (CMD: t id = Some (Val e, If' c1 c2 tx))
         (TRUE: (0 < ([[e]]))%Z),
    validk (upd Z.eq_dec t id (Some (c1, tx))) h.
Admitted.

Lemma If2_preserves_validity:
  forall h t id tx e c1 c2
         (VALIDK: validk t h)
         (CMD: t id = Some (Val e, If' c1 c2 tx))
         (False: (([[e]]) <= 0)%Z),
    validk (upd Z.eq_dec t id (Some (c2, tx))) h.
Admitted.

Lemma While_preserves_validity:
  forall h t id tx c c1 x
         (VALIDK: validk t h)
         (CMD: t id = Some (While c c1, tx))
         (NOTFREE: is_free (While c c1) x = false),
    validk (upd Z.eq_dec t id (Some (If c (Let x c1 (While c c1)) tt, tx))) h.
Admitted.

Lemma g_dupl_preserves_validity:
  forall h t id tx l
         (VALIDK: validk t h)
         (CMD: t id = Some (g_dupl l, tx)),
    validk (upd Z.eq_dec t id (Some (tt, tx))) h.
Admitted.

(** # <font size="5"><b> Valid Configuration Does Not Abort </b></font> # *)

Require Import Qcanon.

Theorem valid_configuration_does_not_abort:
  forall t h (VALIDK: validk t h),
    ~ aborts t h.
Proof.
  intros.
  unfold not.
  intros ABORT.
  destruct VALIDK as (T,(invs,(locs,(Pinv,(Pleak,(Ainv,(Cinv,(Cleak,(INF,(PHsOK,(GHsOK,(TOK,(NDPT,(INVsOK,(LOCsOK,(LOCKsOK,(WTsOTsOK,SOBS))))))))))))))))).
  unfold pheaps_heap in *.
  destruct PHsOK as (DEFL,(PHPDIL,(PHPD,(BPE,(BPI,(BPL,(BPIL,(BPT,PH2H)))))))).
  unfold gheaps_ok in *.
  destruct GHsOK as (DEFLg,(GHPD,(GHPDIL,BGT))).
  unfold locations_ok in *.
  destruct LOCsOK as (INJ,(XCOM,(LCOM,(LOCs,OBsOK)))).
  unfold invs_ok in *.
  destruct INVsOK as (NDPA,(AinvOK,(INAOK,SATAOK))).
  unfold locks_ok.
  destruct LOCKsOK as (LOCKOK,ULOCKOK).
  rewrite map_map in *.
  simpl in *.
  change (fun x : cmd * context * pheap * list location * gheap * Z => pof x) with pof in *.

  inversion ABORT.  
  {
  unfold data_race in *.
  destruct RACE as (id,(id',(c,(c',(tx,(tx',(NEQ,(tid,(tid',(NEQW,EQW)))))))))).
  destruct (write c) eqn:wrc.
  Focus 2.
  contradiction.
  destruct c;
  inversion wrc.
  apply TOK in tid.
  destruct tid as (p,(O,(C,IN))).
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF,(SAT,rest)).
  assert (G1: exists l1 v (EQ: Aof l1 = z), p l1 = Some (Cell 1%Qc v)).
  {
  rewrite <- H2.
  eapply sat_mutate.
  apply SAT.
  }
  apply TOK in tid'.
  destruct tid' as (p',(O',(C',IN'))).
  assert (tmp':=IN').
  apply SOBS in tmp'.
  destruct tmp' as (WF',(SAT',rest')).
  assert (G': exists l' v f (LT: 0 < f) (EQ: Aof l' = z), p' l' = Some (Cell f v)).
  {
  destruct c';
  inversion EQW.
  eapply sat_lookup.
  apply SAT'.
  eapply sat_mutate in SAT'.
  destruct SAT' as (l1,(v,(EQ,p'l1))).
  exists l1, v, 1.
  exists.
  unfold Qclt.
  unfold QArith_base.Qlt.
  simpl.
  omega.
  exists EQ.
  assumption.
  }
  destruct G1 as (l1,(v1,(EQ1,pl1))).
  destruct G' as (l2,(v2,(f2,(lef2,(EQ2,pl2))))).
  assert (EQL: l1 = l2).
  {
  apply INJ.
  apply LOCs.
  apply LOCs.
  assert (G: exists f, (fold_left phplus (map pof T) (phplus Pinv Pleak)) l1 = Some (Cell f v1)).
  {
  apply fold_cell;
  try tauto.
  apply pofs.
  intros.
  apply PHPD in IN0.
  apply phpdef_pair;
  tauto.
  exists 1.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Mutate e1 e2, tx, p, O, C, id).
  tauto.
  assumption.
  }
  destruct G as (f',foldl1).
  rewrite foldl1.
  apply some_none.
  assert (G: exists f, (fold_left phplus (map pof T) (phplus Pinv Pleak)) l2 = Some (Cell f v2)).
  {
  apply fold_cell;
  try tauto.
  apply pofs.
  intros.
  apply PHPD in IN0.
  apply phpdef_pair;
  tauto.
  exists f2.
  right.
  exists p'.
  exists.
  apply in_map_iff.
  exists (c', tx', p', O', C', id').
  tauto.
  assumption.
  }
  destruct G as (f',foldl1).
  rewrite foldl1.
  apply some_none.
  rewrite EQ1.
  rewrite EQ2.
  reflexivity.
  }
  rewrite <- EQL in *.
  assert (bp': boundph p').
  {
  apply BPE.
  apply in_map_iff.
  exists (c', tx', p', O', C', id').
  tauto.
  }
  assert (co: boundph (phplus p p')).
  {
admit.
(*boundph_fold with (m:=pof)(l:=T);*)
  }
  unfold boundph in co.
  unfold phplus in co.
  specialize co with (x:=l1) (f:=1+f2)(z:=v1).
  rewrite pl1 in co.
  rewrite pl2 in co.
  pose proof co as [co1 co2].
  reflexivity.
  apply qcpluslelt with f2.
  assumption.
  unfold boundph in bp'.
  pose proof bp' as [bp''].
  apply pl2.
  tauto.
  }
  {
  apply TOK in CMD.
  destruct CMD as (p,(O,(C,IN))).
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF,(SAT,rest)).
  assert (G: exists l' v f (LT: 0 < f) (EQ: Aof l' = ([[e]])), p l' = Some (Cell f v)).
  {
  eapply sat_lookup.
  apply SAT.
  }
  destruct G as (l2,(v2,(f2,(lef2,(EQ2,pl2))))).
  assert (G': exists f, (fold_left phplus (map pof T) (phplus Pinv Pleak)) l2 = Some (Cell f v2)).
  {
  apply fold_cell;
  try tauto.
  apply pofs.
  intros.
  apply PHPD in IN0.
  apply phpdef_pair;
  tauto.
  exists f2.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Lookup e, tx, p, O, C, tid).
  tauto.
  assumption.
  }
  destruct G' as (f',foldl2).
  unfold phtoh in PH2H.
  destruct PH2H as (PH2H,PH2H1).
  specialize PH2H with l2.
  rewrite foldl2 in PH2H.
  rewrite EQ2 in *.
  rewrite PH2H in NUL.
  inversion NUL.
  }

  {
  apply TOK in CMD.
  destruct CMD as (p,(O,(C,IN))).
  assert (tmp:=IN).
  apply SOBS in tmp.
  destruct tmp as (WF,(SAT,rest)).
  assert (G: exists l' v (EQ: Aof l' = ([[e1]])), p l' = Some (Cell 1 v)).
  {
  eapply sat_mutate.
  apply SAT.
  }
  destruct G as (l2,(v2,(EQ2,pl2))).
  assert (G': exists f, (fold_left phplus (map pof T) (phplus Pinv Pleak)) l2 = Some (Cell f v2)).
  {
  apply fold_cell;
  try tauto.
  apply pofs.
  intros.
  apply PHPD in IN0.
  apply phpdef_pair;
  tauto.
  exists 1.
  right.
  exists p.
  exists.
  apply in_map_iff.
  exists (Mutate e1 e2, tx, p, O, C, tid).
  tauto.
  assumption.
  }
  destruct G' as (f',foldl2).
  unfold phtoh in PH2H.
  destruct PH2H as (PH2H,PH2H1).
  specialize PH2H with l2.
  rewrite foldl2 in PH2H.
  rewrite EQ2 in *.
  rewrite PH2H in NUL.
  inversion NUL.
  }
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


Lemma sat_notifyall:
forall p O C v tx invs
      (SAT: sat p (Some O) C (weakest_pre_ct (NotifyAll v, tx) invs)),
  exists lv ll wt ot
         (EQv: Aof lv = ([[v]]))
         (EQl: Aof ll = Lof lv)
         (P1v: p lv = Some Cond)
         (P1l: p ll = Some (Locked wt ot)) 
         (Mv: Mof lv = Mof lv),
    sat (upd location_eq_dec p ll (Some (Locked (upd wt ([[v]]) 0%nat) ot))) (Some O) C
      (weakest_pre_tx tx invs 0).
Check Mof.
intros.
Check invs.
Print inv.
Check inv.

forall p O C v tx invs
      (SAT: sat p (Some O) C (weakest_pre_ct (Notify v, tx) invs)),
  exists p1 pm C1 Cm wt ot lv ll
         (bp1: boundph p1)
         (bpm: boundph pm)
         (phpdefp1pm: phplusdef p1 pm)
         (p1pm: p = phplus p1 pm)
         (ghpdefC1Cm: ghplusdef C1 Cm)
         (C1Cm: C = ghplus C1 Cm)
         (EQv: Aof lv = ([[v]]))
         (EQl: Aof ll = Lof lv)
         (P1l: p1 ll = Some (Locked wt ot)) 
         (P1l: p1 lv = Some Cond)
         (SATv: sat pm None Cm (subsas (snd (Mof lv)) (invs (fst (Mof lv)) empb empb))),
    (lt 0 (wt ([[v]])) -> sat (upd location_eq_dec p1 ll (Some (Locked (upd wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) (Some O) C1 (weakest_pre_tx tx invs 0)) /\
    (le (wt ([[v]])) 0 -> sat (upd location_eq_dec p ll (Some (Locked (upd wt ([[v]]) (wt ([[v]]) - 1)%nat) ot))) (Some O) C (weakest_pre_tx tx invs 0)).
Proof.
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
*)
