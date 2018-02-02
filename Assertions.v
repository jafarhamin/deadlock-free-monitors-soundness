Require Import ZArith.
Require Import Qcanon.
Require Import List.
Require Import Util_Z.
Require Import Util_list.
Require Import Programs.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.

(** # <font size="5"><b> Assertions </b></font> # *)

Inductive lassn :=
  | Labool (b: bool)
  | Laprop (p: Prop)
  | Laconj (P: lassn) (Q: lassn)
  | Ladisj (P: lassn) (Q: lassn)
  | Lastar (P: lassn) (Q: lassn)
  | Lasepimp (P: lassn) (Q: lassn)
  | Lapointsto (fr:Qc) (a z: Z)
  | Laulock (l: Z) (Wt Ot Ct: bag)
  | Lalock (l: Z)
  | Lalocked (l: Z) (Wt Ot Ct: bag)
  | Lacond (v: Z)
  | Lacredit (cvar: Z)
  | Laex A (pp: A -> lassn)
  | Lafa A (pp: A -> lassn).

Inductive assn :=
  | Abool (b: bool)
  | Aprop (p: Prop)
  | Aconj (P: assn) (Q: assn)
  | Adisj (P: assn) (Q: assn)
  | Astar (P: assn) (Q: assn)
  | Asepimp (P: assn) (Q: assn)
  | Apointsto (fr:Qc) (a z: Z)
  | Aulock (l: Z) (Wt Ot Ct: bag)
  | Alock (l: Z)
  | Alocked (l: Z) (Wt Ot Ct: bag)
  | Acond (v: Z)
  | Aobs (obs: (list Z))
  | Acredit (cvar: Z)
  | Aex A (pp: A -> assn)
  | Afa A (pp: A -> assn)
  | Aexi (pp: (bag -> bag -> bag -> lassn) -> assn)
  | Alasn (la: lassn).


(** # <font size="5"><b> Permission Heaps to Heaps </b></font> # *)

Inductive knowledge :=
  | Cell (f:Qc) (z:Z)
  | Ulock (Wt Ot Ct: bag)
  | Lock
  | Locked (Wt Ot Ct: bag)
  | Cond.

Definition pheap := Z -> option knowledge.

Open Local Scope Qc.

Definition phplusdef (p1 p2 : pheap) :=
  forall x,
    match p1 x with
      | None => True
      | Some (Cell f1 z1) => match p2 x with
                               | None => True
                               | Some (Cell f2 z2) => z1 = z2
                               | _ => False
                             end
      | Some (Ulock _ _ _) => match p2 x with
                                | None => True
                                | _ => False
                              end
      | Some (Lock) => match p2 x with
                         | None => True
                         | Some Lock => True
                         | Some (Locked _ _ _) => True
                         | _ => False
                       end
      | Some (Locked _ _ _) => match p2 x with
                                 | None => True
                                 | Some Lock => True
                                 | _ => False
                               end
      | Some Cond => match p2 x with
                       | None => True
                       | Some Cond => True
                       | _ => False
                     end
    end.

Definition phplus (p1 p2: pheap) : pheap :=
  fun x =>
     match p1 x with
       | None => p2 x
       | Some (Cell f1 z1) => match p2 x with
                                | Some (Cell f2 z2) => Some (Cell (f1+f2) z1)
                                | _ => p1 x
                              end
       | Some Lock => match p2 x with
                        | Some (Locked _ _ _) => p2 x
                        | _ => p1 x
                      end
       | _ => p1 x
     end.

Definition boundph (p: pheap) :=
  forall x f z, p x = Some (Cell f z) -> 0 < f /\ f <= 1.

Definition emp A : (Z -> option A) :=
  fun _ => None.

Definition phtoh (p: pheap) : heap := 
  fun x => match p x with
             | None => None
             | Some (Cell _ z) => Some z
             | Some (Ulock _ _ _) => Some 1%Z
             | Some Lock => Some 1%Z
             | Some (Locked _ _ _) => Some 0%Z
             | Some cond => Some 0%Z
           end.

(** # <font size="5"><b> Satisfaction Relation </b></font> # *)

Inductive oplus A: (option (list A)) -> (option (list A)) -> (option (list A)) -> Prop :=
  | None_op: oplus None None None
  | fs_op o o' (PERM: Permutation o o'): oplus (Some o) None (Some o')
  | sn_op o o' (PERM: Permutation o o'): oplus None (Some o) (Some o').

Fixpoint lsat (p:pheap) (C: bag) (a:lassn) :=
  match a with
    | Labool b => b = true
    | Laprop b => b
    | Laconj P Q => lsat p C P /\ lsat p C Q
    | Ladisj P Q => lsat p C P \/ lsat p C Q
    | Lastar P Q => exists (p1 p2: pheap) (phpdef: phplusdef p1 p2) (BP1: boundph p1) (BP2: boundph p2) (BP12: boundph (phplus p1 p2)) C1 C2,
                    lsat p1 C1 P /\ lsat p2 C2 Q /\ phplus p1 p2 = p /\ bagplus C1 C2 = C
    | Lasepimp P Q => forall p' (BP': boundph p') (PHPDEF: phplusdef p p') (BPP': boundph (phplus p p')) C'
                            (SAT: lsat p' C' P),
                       lsat (phplus p p') (bagplus C C') Q
    | Lapointsto f a z => exists f', p a = Some (Cell (f+f') z)
    | Laulock l Wt Ot Ct => p l = Some (Ulock Wt Ot Ct)
    | Lalock l => p l = Some Lock \/ exists Wt Ot Ct, p l = Some (Locked Wt Ot Ct)
    | Lalocked l Wt Ot Ct => p l = Some (Locked Wt Ot Ct)
    | Lacond v => p v = Some Cond
    | Lacredit v => exists n, C v = S n
    | Laex pp => exists v, lsat p C (pp v)
    | Lafa pp => forall v, lsat p C (pp v)
  end.

Fixpoint sat (p:pheap) (O: option (list Z)) (C: bag) (a:assn) :=
  match a with
    | Abool b => b = true
    | Aprop b => b
    | Aconj P Q => sat p O C P /\ sat p O C Q
    | Adisj P Q => sat p O C P \/ sat p O C Q
    | Astar P Q => exists (p1 p2: pheap) (phpdef: phplusdef p1 p2) (BP1: boundph p1) (BP2: boundph p2) (BP12: boundph (phplus p1 p2)) 
                           O1 O2 C1 C2 (OPLUS: oplus O1 O2 O),
                    sat p1 O1 C1 P /\ sat p2 O2 C2 Q /\ phplus p1 p2 = p /\ bagplus C1 C2 = C
    | Asepimp P Q => forall p' (BP': boundph p') (PHPDEF: phplusdef p p') (BPP': boundph (phplus p p')) O' C' O'' (OPLUS: oplus O O' O'')
                            (SAT: sat p' O' C' P),
                       sat (phplus p p') O'' (bagplus C C') Q
    | Apointsto f a z => exists f', p a = Some (Cell (f+f') z)
    | Aulock l Wt Ot Ct => p l = Some (Ulock Wt Ot Ct)
    | Alock l => p l = Some Lock \/ exists Wt Ot Ct, p l = Some (Locked Wt Ot Ct)
    | Alocked l Wt Ot Ct => p l = Some (Locked Wt Ot Ct)
    | Acond v => p v = Some Cond
    | Aobs O1 => p = emp knowledge /\ C = empb /\ oplus (Some O1) None O
    | Acredit v => exists n, C v = S n
    | Aex pp => exists v, sat p O C (pp v)
    | Afa pp => forall v, sat p O C (pp v)
    | Aexi pp => exists v, sat p O C (pp v)
    | Alasn la => lsat p C la
  end.

Notation "P '|=' Q" := 
  (forall p o C (bp: boundph p)
          (SAT: sat p o C P),
    sat p o C Q)
(at level 120).

Notation "'FA' z ',' P" := 
  (Afa (fun z => P))(at level 115).

Notation "'EX' z ',' P" := 
  (Aex (fun z => P))(at level 115).

Notation "'EXi' z ',' P" := 
  (Aexi (fun z => P))(at level 115).

Notation "P '--*' Q" := 
  (Asepimp P Q)(at level 110).

Notation "P '|*' Q" := 
  (Adisj P Q)(at level 105).

Notation "P '&*' Q" := 
  (Aconj P Q)(at level 100).

Notation "P '**' Q" := 
  (Astar P Q)(at level 95, right associativity).

Notation "P '|->' Q" := 
  (Apointsto 1 P Q)(at level 90).


(** # <font size="5"><b> oplus </b></font> # *)

Lemma oplus_assoc A:
  forall (o1 o2 o3 o4 o1o2 o2o4: option (list A))
         (OP1: oplus o1 o2 o1o2)
         (OP2: oplus o3 o4 o1)
         (OP3: oplus o2 o4 o2o4),
    oplus o3 o2o4 o1o2.
Proof.
  intros.
  inversion OP1.
  rewrite <- H in *.
  rewrite <- H0 in *.
  rewrite <- H1 in *.
  inversion OP2.
  rewrite <- H3 in *.
  inversion OP3.
  apply None_op.
  rewrite <- H in *.
  rewrite <- H0 in *.
  rewrite <- H1 in *.
  inversion OP2.
  rewrite <- H3 in *.
  inversion OP3.
  apply fs_op.
  apply Permutation_trans with o.
  assumption.
  assumption.
  rewrite <- H3 in *.
  inversion OP3.
  apply sn_op.
  apply Permutation_trans with o0.
  apply Permutation_sym.
  assumption.
  apply Permutation_trans with o.
  assumption.
  assumption.
  rewrite <- H in *.
  rewrite <- H0 in *.
  rewrite <- H1 in *.
  inversion OP2.
  rewrite <- H3 in *.
  inversion OP3.
  apply sn_op.
  apply Permutation_trans with o.
  apply Permutation_sym.
  assumption.
  assumption.
Qed.

Lemma oplus_comm A:
  forall (o1 o2 o1o2: option (list A))
         (OP: oplus o1 o2 o1o2),
    oplus o2 o1 o1o2.
Proof.
  intros.
  inversion OP.
  apply None_op.
  apply sn_op.
  assumption.
  apply fs_op.
  assumption.
Qed.

Lemma oplus_exists A:
  forall (o1 o2: option (list A)) (DEF: o1 = None \/ o2 = None),
    exists o1o2, oplus o1 o2 o1o2.
Proof.
  intros.
  destruct DEF as [DEF|DEF].
  rewrite DEF.
  exists o2.
  destruct o2.
  apply sn_op.
  apply Permutation_refl.
  apply None_op.
  rewrite DEF.
  exists o1.
  destruct o1.
  apply fs_op.
  apply Permutation_refl.
  apply None_op.
Qed.

(** # <font size="5"><b> phplusdef </b></font> # *)

Lemma phpdef_comm: 
  forall p1 p2 (PHPDEF: phplusdef p1 p2),
    phplusdef p2 p1.
Proof.
  unfold phplusdef.
  intros.
  specialize PHPDEF with x.
  destruct (p1 x) eqn:p1x.
  destruct k.
  destruct (p2 x) eqn:p2x.
  destruct k;
  try symmetry;
  try assumption.
  assumption.
  destruct (p2 x).
  contradiction.
  assumption.
  assumption.
  assumption.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
Qed.

Lemma phpdef_emp p: 
  phplusdef p (emp knowledge).
Proof.
  unfold phplusdef.
  unfold emp.
  intros.
  destruct (p x).
  destruct k;
  trivial.
  trivial.
Qed.

Lemma phpdef_pair:
  forall p1 p2 p3
         (PHPD1: phplusdef p2 p3)
         (PHPD2: phplusdef p1 p2)
         (PHPD3: phplusdef p1 p3),
    phplusdef p1 (phplus p2 p3).
Proof.
  unfold boundph.
  unfold phplusdef.
  unfold phplus.
  intros.
  specialize PHPD1 with x.
  specialize PHPD2 with x.
  specialize PHPD3 with x.
  destruct (p1 x).
  destruct k;
  try tauto.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p3 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  assumption.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  assumption.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  assumption.
Qed.

Lemma phpdef_pair':
  forall p1 p2 p3
         (PHPD1: phplusdef p1 p2)
         (PHPD2: phplusdef p1 p3)
         (PHPD3: phplusdef p2 p3),
    phplusdef (phplus p1 p2) p3.
Proof.
  unfold boundph.
  unfold phplusdef.
  unfold phplus.
  intros.
  specialize PHPD1 with x.
  specialize PHPD2 with x.
  specialize PHPD3 with x.
  destruct (p1 x).
  destruct k;
  try tauto.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  assumption.
Qed.

Lemma phpdef_assoc:
  forall p1 p2 p3
         (PHPD1: phplusdef p1 p2)
         (PHPD2: phplusdef p1 p3)
         (PHPD3: phplusdef p2 p3),
    phplusdef (phplus p1 p2) p3 <->
    phplusdef p1 (phplus p2 p3).
Proof.
  unfold phplusdef.
  unfold phplus.
  split.
  {
  intros.
  specialize PHPD1 with x.
  specialize PHPD2 with x.
  specialize PHPD3 with x.
  specialize H with x.
  destruct (p1 x).
  destruct k;
  try tauto.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  assumption.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  trivial.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  trivial.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  assumption.
  }
  {
  intros.
  specialize PHPD1 with x.
  specialize PHPD2 with x.
  specialize PHPD3 with x.
  specialize H with x.
  destruct (p1 x).
  destruct k;
  try tauto.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  assumption.
  }
Qed.

Lemma phpdef_dist:
  forall p1 p2 p3
         (PHPD1: phplusdef (phplus p1 p2) p3)
         (PHPD2: phplusdef p1 p2),
    phplusdef p1 p3 /\ phplusdef p2 p3.
Proof.
  unfold boundph.
  unfold phplusdef.
  unfold phplus.
  split.
  {
  intros.
  specialize PHPD1 with x.
  specialize PHPD2 with x.
  destruct (p1 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  trivial.
  assumption.
  assumption.
  }
  {
  intros.
  specialize PHPD1 with x.
  specialize PHPD2 with x.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  intuition.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  intuition.
  trivial.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  trivial.
  }
Qed.

Lemma phpdef_dist':
  forall p1 p2 p3
         (PHPD1: phplusdef p1 (phplus p2 p3))
         (PHPD2: phplusdef p2 p3),
    phplusdef p1 p2 /\ phplusdef p1 p3.
Proof.
  unfold phplus.
  unfold phplusdef.
  unfold boundph.
  split.
  {
  intros.
  specialize PHPD1 with x.
  specialize PHPD2 with x.
  destruct (p1 x).
  destruct k;
  try tauto.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  intuition.
  intuition.
  destruct (p3 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p3 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p3 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  trivial.
  }
  {
  intros.
  specialize PHPD1 with x.
  specialize PHPD2 with x.
  destruct (p1 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p2 x).
  destruct k;
  try tauto.
  intuition.
  intuition.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  destruct (p3 x).
  destruct k;
  try tauto.
  trivial.
  destruct (p2 x).
  destruct k;
  try tauto.
  trivial.
  destruct (p2 x).
  destruct k;
  try tauto.
  trivial.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p2 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  trivial.
  }
Qed.

Lemma phpdef_locked:
  forall p1 p2 wt ot ct z
         (PHPDL: phplusdef p1 p2)
         (P1z: exists wt1 ot1 ct1, p1 z = (Some (Locked wt1 ot1 ct1))),
    phplusdef (upd p1 z (Some (Locked wt ot ct))) p2.
Proof.
  unfold phplusdef.
  unfold upd.
  intros.
  specialize PHPDL with x.
  destruct P1z as (wt1,(ot1,(ct1,p1z))).
  destruct (Z.eq_dec x z).
  rewrite <- e in p1z.
  rewrite p1z in PHPDL.
  destruct (p2 x).
  destruct k;
  try tauto.
  tauto.
  destruct (p1 x) eqn:p1x.
  destruct k;
  try tauto.
  tauto.
Qed.

Lemma phpdef_updl A m:
  forall (l: list (A * Z)) p1 p2 z x
         (PHPDL: forall p (IN: In p (map m l)), phplusdef p p2)
         (IN: In p1 (map m (updl l z x)))
         (PHPD: phplusdef (m x) p2),
    phplusdef p1 p2.
Proof.
  induction l.
  simpl.
  intros.
  contradiction.
  simpl.
  intros.
  destruct (Z.eq_dec (snd a) z).
  destruct IN as [EQ|IN].
  rewrite <- EQ.
  assumption.
  apply IHl with z x.
  intros.
  apply PHPDL.
  right.
  assumption.
  assumption.
  assumption.
  destruct IN as [EQ|IN].
  rewrite <- EQ.
  apply PHPDL.
  left.
  reflexivity.
  apply IHl with z x.
  intros.
  apply PHPDL.
  right.
  assumption.
  assumption.
  assumption.
Qed.

Lemma phpdef_assoc_mon:
  forall p1 p2 p3
         (PHPDEF1: phplusdef p1 p2)
         (PHPDEF2: phplusdef (phplus p1 p2) p3),
    phplusdef p2 p3.
Proof.
  unfold phplus.
  unfold phplusdef.
  unfold boundph.
  intros.
  specialize PHPDEF1 with x.
  specialize PHPDEF2 with x.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  intuition.
  intuition.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  intuition.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  destruct (p1 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  assumption.
  assumption.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  destruct (p1 x).
  destruct k;
  try tauto.
  assumption.
  trivial.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  intuition.
Qed.

Lemma phpdef_locked_lock:
  forall p1 p2 z
        (PHPD: phplusdef p1 p2)
        (P1z: exists wt ot ct, p1 z = Some (Locked wt ot ct) \/ p1 z = Some (Ulock wt ot ct)),
    phplusdef (upd p1 z (Some Lock)) p2.
Proof.
  unfold phplusdef.
  unfold upd.
  intros.
  specialize PHPD with x.
  destruct P1z as (wt,(ot,(ct,p1z))).
  destruct (Z.eq_dec x z).
  rewrite <- e in p1z.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct p1z as [p1z|p1z].
  rewrite p1z in PHPD.
  tauto.
  rewrite p1z in PHPD.
  tauto.
  destruct p1z as [p1z|p1z].
  rewrite p1z in PHPD.
  tauto.
  rewrite p1z in PHPD.
  tauto.
  destruct p1z as [p1z|p1z].
  rewrite p1z in PHPD.
  tauto.
  rewrite p1z in PHPD.
  tauto.
  tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
Qed.

Lemma phpdef_assoc_mon2:
  forall p1 p2 p3
         (PHPDEF1: phplusdef p1 p2)
         (PHPDEF2: phplusdef (phplus p1 p2) p3),
    phplusdef p2 p3.
Proof.
  unfold phplusdef.
  unfold phplus.
  unfold boundph.
  intros.
  specialize PHPDEF1 with x.
  specialize PHPDEF2 with x.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  intuition.
  intuition.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  intuition.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
  tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
  tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
  tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  destruct (p1 x).
  destruct k;
  try tauto.
  intuition.
Qed.

Lemma phpdef_upd_locked:
  forall p1 p2 z wt ot ct
         (PHPD: phplusdef p1 p2)
         (p2z: p2 z = Some Lock \/ p2 z = None),
    phplusdef (upd p1 z (Some (Locked wt ot ct))) p2.
Proof.
  unfold phplusdef.
  unfold upd.
  intros.
  specialize PHPD with x.
  destruct (Z.eq_dec x z).
  rewrite <- e in p2z.
  destruct p2z as [p2z|p2z].
  rewrite p2z.
  tauto.
  rewrite p2z.
  tauto.
  assumption.
Qed.

(** # <font size="5"><b> phplus </b></font> # *)

Lemma phplus_emp:
  forall p,
    phplus p (emp knowledge) = p.
Proof.
  unfold emp.
  unfold phplus.
  intros.
  apply functional_extensionality.
  intros.
  destruct (p x);
  try destruct k;
  reflexivity.
Qed.

Lemma phplus_comm:
  forall p1 p2 (PHPD: phplusdef p1 p2),
    phplus p1 p2 = phplus p2 p1.
Proof.
  unfold phplusdef.
  unfold phplus.
  intros.
  apply functional_extensionality.
  intros.
  specialize PHPD with x.
  destruct (p1 x).
  destruct k.
  destruct (p2 x).
  destruct k;
  try contradiction.
  rewrite Qcplus_comm.
  rewrite PHPD.
  reflexivity.
  reflexivity.
  destruct (p2 x).
  contradiction.
  reflexivity.
  destruct (p2 x).
  destruct k;
  try contradiction;
  try reflexivity.
  reflexivity.
  destruct (p2 x).
  destruct k;
  try contradiction;
  try reflexivity.
  reflexivity.
  destruct (p2 x).
  destruct k;
  try contradiction;
  try reflexivity.
  reflexivity.
  destruct (p2 x).
  destruct k;
  try reflexivity.
  reflexivity.
Qed.

Lemma phplus_assoc:
  forall p1 p2 p3 
         (PHPD1: phplusdef p1 p2)
         (PHPD2: phplusdef p1 p3)
         (PHPD3: phplusdef p2 p3),
    phplus (phplus p1 p2) p3 = phplus p1 (phplus p2 p3).
Proof.
  unfold phplusdef.
  unfold phplus.
  intros.
  apply functional_extensionality.
  intros.
  specialize PHPD1 with x.
  specialize PHPD2 with x.
  specialize PHPD3 with x.
  destruct (p1 x).
  destruct k;
  try tauto.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  rewrite Qcplus_assoc.
  reflexivity.
  reflexivity.
  tauto.
  destruct (p2 x).
  destruct k;
  try tauto.
  destruct (p3 x).
  destruct k;
  try tauto.
  tauto.
  tauto.
  tauto.
Qed.

Lemma phplus_lock:
  forall p1 p2 l
         (P1l: p1 l = Some Lock \/ exists wt ot ct, p1 l = Some (Locked wt ot ct)),
    (phplus p1 p2) l = Some Lock \/ exists wt ot ct, (phplus p1 p2) l = Some (Locked wt ot ct).
Proof.
  unfold phplusdef.
  unfold phplus.
  intros.
  destruct P1l as [p1l|p1l].
  rewrite p1l in *.
  destruct (p2 l).
  destruct k;
  try tauto.
  right.
  exists Wt, Ot, Ct.
  reflexivity.
  left.
  reflexivity.
  destruct p1l as (wt,(ot,(ct,p1l))).
  rewrite p1l in *.
  right.
  exists wt, ot, ct.
  reflexivity.
Qed.

Lemma phplus_locked:
  forall p1 p2 l wt ot ct
         (PHPD: phplusdef p1 p2)
         (P1l: p1 l = Some (Locked wt ot ct)),
    (phplus p1 p2) l = Some (Locked wt ot ct).
Proof.
  unfold phplus.
  unfold phplusdef.
  intros.
  specialize PHPD with l.
  rewrite P1l in *.
  reflexivity.
Qed.

Lemma phplus_ulock:
  forall p1 p2 l wt ot ct
         (PHPD: phplusdef p1 p2)
         (P1l: p1 l = Some (Ulock wt ot ct)),
    (phplus p1 p2) l = Some (Ulock wt ot ct).
Proof.
  unfold phplus.
  unfold phplusdef.
  intros.
  specialize PHPD with l.
  rewrite P1l in *.
  reflexivity.
Qed.

Lemma phplus_upd:
  forall p1 p2 z z'
         (CELL: ~ exists v f v' f' (Z': z' = Some (Cell f v)), p2 z = Some (Cell f' v'))
         (LOCKED: z' = Some Lock -> ~ exists wt ot ct, p2 z = Some (Locked wt ot ct))
         (NONE: z' = None -> p2 z = None),
    phplus (upd p1 z z') p2 = upd (phplus p1 p2) z z'.
Proof.
  intros.
  unfold phplus.
  unfold upd.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x z).
  destruct z' eqn:z'_.
  destruct k eqn:k_.
  destruct (p2 x) eqn:p2x.
  destruct k0 eqn:k0_.
  exfalso.
  apply CELL.
  exists z0, f, z1, f0.
  exists.
  reflexivity.
  rewrite <- e.
  assumption.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  destruct (p2 x) eqn:p2x.
  destruct k0 eqn:k0_.
  reflexivity.
  reflexivity.
  reflexivity.
  exfalso.
  apply LOCKED.
  reflexivity.
  exists Wt, Ot, Ct.
  rewrite <- e.
  assumption.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  rewrite e.
  apply NONE.
  reflexivity.
  destruct (p1 x) eqn:p1x.
  destruct k eqn:k_.
  destruct (p2 x) eqn:p2x.
  destruct k0 eqn:k0_.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

Lemma phplus_Cond:
  forall p1 p2 z
         (PHPD: phplusdef p1 p2)
         (P1v: p1 z = Some Cond),
    phplus p1 p2 z = Some Cond.
Proof.
  unfold phplus.
  unfold phplusdef.
  intros.
  specialize PHPD with z.
  rewrite P1v in *.
  reflexivity.
Qed.

Lemma phplus_locked_mono:
  forall p1 p2 z
         (p1p2z: phplus p1 p2 z = None \/ phplus p1 p2 z = Some Lock),
    p1 z = None \/ p1 z = Some Lock.
Proof.
  unfold phplus.
  intros.
  destruct (p1 z).
  destruct k;
  try tauto.
  destruct (p2 z).
  destruct k;
  inversion p1p2z;
  try inversion H.
  destruct p1p2z;
  inversion H.
  left.
  reflexivity.
Qed.

Lemma phplus_lock_mon:
  forall p1 p2 z wt ot ct
         (PHPDEF: phplusdef p1 p2)
         (P1: p1 z = Some (Locked wt ot ct)),
    p2 z = Some Lock \/ p2 z = None.
Proof.
  unfold phplus.
  unfold phplusdef.
  intros.
  specialize PHPDEF with z.
  rewrite P1 in *.
  destruct (p2 z).
  destruct k;
  try tauto.
  right.
  reflexivity.
Qed.

Lemma phplus_ulock_mon:
  forall p1 p2 z wt ot ct
         (PHPDEF: phplusdef p1 p2)
         (P1: p1 z = Some (Ulock wt ot ct)),
    p2 z = None.
Proof.
  unfold phplus.
  unfold phplusdef.
  intros.
  specialize PHPDEF with z.
  rewrite P1 in *.
  destruct (p2 z).
  destruct k;
  try tauto.
  reflexivity.
Qed.

Lemma phplus_upd_lock:
  forall p1 p2 z (P2: p2 z = Some Lock \/ p2 z = None),
    phplus (upd p1 z (Some Lock)) p2 z = Some Lock.
Proof.
  unfold upd.
  unfold phplus.
  intros.
  rewrite eqz.
  destruct P2 as [p2z|p2z];
  rewrite p2z;
  reflexivity.
Qed.

Lemma phplus_mon:
  forall p1 p1' p2 x
         (EQ: p1 x = p1' x),
    phplus p1 p2 x = phplus p1' p2 x.
Proof.
  unfold phplus.
  intros.
  rewrite EQ.
  reflexivity.
Qed.

(** # <font size="5"><b> boundph </b></font> # *)

Lemma bph_comm:
  forall p1 p2 
        (PHPDEF: phplusdef p1 p2)
        (BP: boundph (phplus p1 p2)),
    boundph (phplus p2 p1).
Proof.
  unfold boundph.
  intros.
  apply BP with x z.
  rewrite phplus_comm.
  assumption.
  assumption.
Qed.

Lemma bph_assoc: 
  forall p1 p2 p3
        (PHPDEF1: phplusdef p1 p2)
        (PHPDEF2: phplusdef p1 p3)
        (PHPDEF3: phplusdef p2 p3),
    boundph (phplus p1 (phplus p2 p3)) <->
    boundph (phplus (phplus p1 p2) p3).
Proof.
  unfold boundph.
  split.
  intros.
  apply H with x z.
  rewrite <- phplus_assoc.
  assumption.
  assumption.
  assumption.
  assumption.
  intros.
  apply H with x z.
  rewrite phplus_assoc.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma boundph_emp: 
  boundph (emp knowledge).
Proof.
  unfold boundph.
  unfold emp.
  intros.
  inversion H.
Qed.

Lemma boundph_phplus_upd:
  forall p1 p2 z v
         (BP1: boundph p1)
         (BP2: boundph p2)
         (PHPD: phplusdef p1 p2)
         (BP: boundph (phplus p1 p2))
         (V1: forall f1 v1 (VCELL: v = Some (Cell f1 v1)), 0 < f1 /\ f1 <= 1 )
         (V2: forall f1 f2 (CELL: exists v1 v2 (V1: v = Some (Cell f1 v1)), p2 z = Some (Cell f2 v2)), f1 + f2 <= 1 ),
    boundph (phplus (upd p1 z v) p2).
Proof.
  unfold boundph.
  unfold phplusdef.
  unfold upd.
  unfold phplus.
  intros.
  specialize BP1 with (x:=x).
  specialize BP2 with (x:=x).
  specialize PHPD with (x:=x).
  specialize BP with (x:=x).
  destruct (Z.eq_dec x z).
  rewrite e in *.
  destruct v;
  try tauto.
  symmetry in H.
  destruct k;
  inversion H;
  try tauto.
  assert (G1: 0 < f0 /\ f0 <= 1).
  {
  apply V1 with z1.
  reflexivity.
  }
  destruct (p2 z) eqn:p2z.
  destruct k;
  inversion H;
  try tauto.
  assert (G: f0 + f1 <= 1).
  {
  apply V2.
  exists z1, z2.
  exists.
  reflexivity.
  reflexivity.
  }
  assert (G2: 0 < f1 /\ f1 <= 1).
  {
  apply BP2 with z2.
  reflexivity.
  }
  split.
  apply Qc_Lt_plus.
  tauto.
  tauto.
  tauto.
  inversion H.
  tauto.
  destruct (p2 z) eqn:p2z.
  destruct k;
  inversion H;
  try tauto.
  inversion H.
  apply BP2 with z0.
  tauto.
  destruct (p1 x) eqn:p1x.
  destruct k;
  try tauto.
  assert (G: 0 < f0 /\ f0 <= 1).
  {
  apply BP1 with z1.
  reflexivity.
  }
  destruct (p2 x) eqn:p2x.
  destruct k;
  inversion H;
  try tauto.
  assert (G1: 0 < f1 /\ f1 <= 1).
  {
  apply BP2 with z2.
  reflexivity.
  }
  split.
  apply Qc_Lt_plus.
  tauto.
  tauto.
  assert (G2: 0 < f0 + f1 /\ f0 + f1 <= 1).
  {
  apply BP with z1.
  reflexivity.
  }  
  tauto.
  symmetry in H.
  inversion H.
  tauto.
  inversion H.
  destruct (p2 x) eqn:p2x.
  destruct k;
  inversion H;
  try tauto.
  inversion H.
  inversion H.
  inversion H.
  apply BP2 with z0.
  assumption.
Qed.

Lemma boundph_upd:
  forall p z v
         (BP: boundph p)
         (BV: forall f, (exists z', v = Some (Cell f z')) -> 0 < f /\ f <= 1),
    boundph (upd p z v).
Proof.
  unfold boundph.
  unfold upd.
  intros.
  specialize BP with (x:=x).
  destruct (Z.eq_dec x z).
  rewrite e in *.
  apply BV.
  exists z0.
  assumption.
  apply BP with z0.
  assumption.
Qed.

Lemma boundph_updl A m:
  forall (l: list (A * Z)) p z x
         (PHPDL: forall p (IN: In p (map m l)), boundph p)
         (IN: In p (map m (updl l z x)))
         (BP: boundph (m x)),
    boundph p.
Proof.
  unfold updl.
  intros.
  rewrite map_map in IN.
  apply in_map_iff in IN.
  destruct IN as ((x1,x2),(EQ,IN)).
  simpl in *.
  rewrite <- EQ.
  destruct (Z.eq_dec x2 z).
  assumption.
  apply PHPDL.
  apply in_map.
  assumption.
Qed.

Lemma boundph_mon:
  forall p1 p2 p3
         (BP1: boundph p1)
         (BP2: boundph p2)
         (BP3: boundph p3)
         (BP134: boundph (phplus (phplus p1 p2) p3)),
    boundph (phplus p1 p2).
Proof.
  unfold boundph.
  unfold phplus.
  intros.
  specialize BP1 with (x:=x).
  specialize BP2 with (x:=x).
  specialize BP3 with (x:=x).
  specialize BP134 with (x:=x).

  destruct (p1 x).
  destruct k;
  try tauto.
  assert (G1: 0 < f0 /\ f0 <= 1).
  {
  apply BP1 with z0.
  reflexivity.
  }
  destruct (p2 x).
  destruct k;
  try tauto.
  assert (G2: 0 < f1 /\ f1 <= 1).
  {
  apply BP2 with z1.
  reflexivity.
  }
  destruct (p3 x).
  destruct k;
  try tauto.
  inversion H.
  assert (G3: 0 < f2 /\ f2 <= 1).
  {
  apply BP3 with z2.
  reflexivity.
  }
  assert (G: 0 < f0 + f1 + f2 /\ f0 + f1 + f2 <= 1).
  {
  apply BP134 with z0.
  reflexivity.
  }
  split.
  apply Qc_Lt_plus.
  tauto.
  tauto.
  apply Qc_Le_mon12 with f2.
  rewrite Qcplus_assoc.
  tauto.
  tauto.
  inversion H.
  split.
  apply Qc_Lt_plus.
  tauto.
  tauto.
  assert (G: 0 < f0 + f1 /\ f0 + f1 <= 1).
  {
  apply BP134 with z0.
  reflexivity.
  }
  tauto.
  inversion H.
  assert (G: 0 < f0 + f1 /\ f0 + f1 <= 1).
  {
  apply BP134 with z0.
  reflexivity.
  }
  tauto.
  inversion H.
  assert (G: 0 < f0 + f1 /\ f0 + f1 <= 1).
  {
  apply BP134 with z0.
  reflexivity.
  }
  tauto.
  inversion H.  
  assert (G: 0 < f0 + f1 /\ f0 + f1 <= 1).
  {
  apply BP134 with z0.
  reflexivity.
  }
  tauto.
  inversion H.
  assert (G: 0 < f0 + f1 /\ f0 + f1 <= 1).
  {
  apply BP134 with z0.
  reflexivity.
  }
  tauto.
  inversion H.
  rewrite <- H1.
  assumption.
  inversion H.
  rewrite <- H1.
  assumption.
  inversion H.
  rewrite <- H1.
  assumption.
  inversion H.
  rewrite <- H1.
  assumption.
  inversion H.
  rewrite <- H1.
  assumption.
  inversion H.

  destruct (p2 x).
  destruct k;
  inversion H;
  try tauto.
  inversion H.
  inversion H.
  inversion H.
  destruct (p2 x).
  destruct k;
  inversion H;
  try tauto.
  rewrite <- H1.
  apply BP2 with z0.
  reflexivity.
  inversion H.
Qed.

(** # <font size="5"><b> phtoheap </b></font> # *)

Lemma phtoh_upd_locked:
  forall p1 z wt ot ct
         (P1z: exists wt1 ot1 ct1, p1 z = Some (Locked wt1 ot1 ct1)),
  phtoh (upd p1 z (Some (Locked wt ot ct))) = phtoh p1.
Proof.
  unfold phtoh.
  unfold upd.
  intros.
  apply functional_extensionality.
  intros.
  destruct P1z as (wt1,(ot1,(ct1,p1z))).
  destruct (Z.eq_dec x z).
  rewrite <- e in *.
  rewrite p1z.
  reflexivity.
  reflexivity.
Qed. 

(** # <font size="5"><b> can phplus </b></font> # *)

Lemma can_phpdef: can phplusdef phplus.
Proof.
  unfold can.
  split.
  apply phplus_comm.
  split.
  apply phplus_assoc.
  split.
  {
  intros.
  apply phpdef_pair.
  assumption.
  assumption.
  assumption.
  }
  split.
  {
  intros.
  apply phpdef_dist.
  assumption.
  assumption.
  }
  split.
  {
  apply phpdef_comm.
  }
  exists (emp knowledge).
  unfold neutral.
  intros.
  split.
  apply phplus_emp.
  rewrite phplus_comm.
  apply phplus_emp.
  apply phpdef_comm.
  apply phpdef_emp.
Qed.

(** # <font size="5"><b> sat </b></font> # *)

Lemma sat_comm:
  forall a a' p O C
         (SAT: sat p O C (a ** a')),
    sat p O C (a' ** a).
Proof.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(C1,(C2,(opo1o2,(bt,(sat2,(p1p2,C1C2)))))))))))))).
  exists p2, p1.
  exists.
  apply phpdef_comm.
  assumption.
  exists bp2, bp1.
  exists.
  apply bph_comm.
  assumption.
  assumption.
  exists o2, o1, C2, C1.
  exists.
  apply oplus_comm.
  assumption.
  rewrite phplus_comm.
  rewrite bplus_comm.
  tauto.
  apply phpdef_comm.
  assumption.
Qed.

Lemma lsat_comm:
  forall a a' p C
         (SAT: lsat p C (Lastar a a')),
    lsat p C (Lastar a' a).
Proof.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(C1,(C2,(lsat1,(lsat2,(p1p2,C1C2))))))))))).
  exists p2, p1.
  exists.
  apply phpdef_comm.
  assumption.
  exists bp2, bp1.
  exists.
  apply bph_comm.
  assumption.
  assumption.
  exists C2, C1.
  rewrite phplus_comm.
  rewrite bplus_comm.
  tauto.
  apply phpdef_comm.
  assumption.
Qed.

Lemma sat_assoc:
  forall a1 a2 a3 p O C (BP: boundph p),
    sat p O C (a1 ** (a2 ** a3)) <->
    sat p O C ((a1 ** a2) ** a3).
Proof.
  simpl.
  split.
  {
  intros.
  destruct H as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(C1,(C2,(opo1o2,(sat1,(sat2,(p1p2,C1C2)))))))))))))).
  destruct sat2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(o3,(o4,(C3,(C4,(opo3o4,(sat3,(sat4,(p3p4,C3C4)))))))))))))).
  rewrite <- p3p4 in phpdefp1p2.
  rewrite <- p1p2 in BP.
  rewrite <- p3p4 in BP.
  assert (phpdefp134: phplusdef p1 p3 /\ phplusdef p1 p4).
  {
  apply phpdef_dist'.
  assumption.
  assumption.
  }
  assert (bp134: boundph (phplus (phplus p1 p3) p4)).
  {
  apply bph_assoc.
  tauto.
  tauto.
  tauto.
  tauto.
  }
  assert (phpdef134: phplusdef (phplus p1 p3) p4).
  {
  apply phpdef_pair'.
  tauto.
  tauto.
  tauto.
  }
  exists (phplus p1 p3), p4, phpdef134.
  exists.
  apply boundph_mon with p4.
  assumption.
  assumption.
  assumption.
  assumption.
  exists bp4.
  exists bp134.
  assert (opo1o3: exists o1o3, oplus o1 o3 o1o3).
  {
  apply oplus_exists.
  destruct o1.
  inversion opo1o2.
  rewrite <- H1 in opo3o4.
  inversion opo3o4.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct opo1o3 as (o1o3,opo1o3).
  exists o1o3, o4.
  exists (bagplus C1 C3), C4.
  exists.
  apply oplus_comm.
  apply oplus_assoc with o2 o1 o3.
  apply oplus_comm.
  assumption.
  apply oplus_comm.
  assumption.
  assumption.
  exists.
  exists p1, p3.
  exists.
  tauto.
  exists bp1, bp3.
  exists.
  apply boundph_mon with p4.
  assumption.
  assumption.
  assumption.
  assumption.
  exists o1, o3, C1, C3, opo1o3.
  tauto.
  rewrite phplus_assoc.
  rewrite p3p4.
  rewrite bplus_assoc.
  rewrite C3C4.
  tauto.
  tauto.
  tauto.
  tauto.
  }
  {
  intros.
  destruct H as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(C1,(C2,(opo1o2,(sat1,(sat2,(p1p2,C1C2)))))))))))))).
  destruct sat1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(o3,(o4,(C3,(C4,(opo3o4,(sat3,(sat4,(p3p4,C3C4)))))))))))))).
  rewrite <- p3p4 in phpdefp1p2.
  rewrite <- p1p2 in BP.
  rewrite <- p3p4 in BP.
  assert (phpdefp134: phplusdef p3 p2 /\ phplusdef p4 p2).
  {
  apply phpdef_dist.
  assumption.
  assumption.
  }
  assert (bp134: boundph (phplus p3 (phplus p4 p2))).
  {
  apply bph_assoc.
  tauto.
  tauto.
  tauto.
  tauto.
  }
  assert (phpdef134: phplusdef p3 (phplus p4 p2)).
  {
  apply phpdef_assoc.
  tauto.
  tauto.
  tauto.
  assumption.
  }
  exists p3, (phplus p4 p2), phpdef134, bp3.
  exists.
  apply boundph_mon with p3.
  assumption.
  assumption.
  assumption.
  apply bph_comm.
  assumption.
  assumption.
  exists bp134.
  assert (opo1o3: exists o4o2, oplus o4 o2 o4o2).
  {
  apply oplus_exists.
  destruct o4.
  inversion opo3o4.
  rewrite <- H0 in opo1o2.
  inversion opo1o2.
  right.
  reflexivity.
  left.
  reflexivity.
  }
  destruct opo1o3 as (o4o2,opo4o2).
  exists o3, o4o2.
  exists C3, (bagplus C4 C2).
  exists.
  apply oplus_assoc with o1 o2 o4.
  assumption.
  assumption.
  apply oplus_comm.
  assumption.
  split.
  assumption.
  exists.
  exists p4, p2.
  exists.
  tauto.
  exists bp4, bp2.
  exists.
  apply boundph_mon with p3.
  assumption.
  assumption.
  assumption.
  apply bph_comm.
  assumption.
  assumption.
  exists o4, o2, C4, C2, opo4o2.
  tauto.
  rewrite <- phplus_assoc.
  rewrite p3p4.
  rewrite <- bplus_assoc.
  rewrite C3C4.
  tauto.
  tauto.
  tauto.
  tauto.
  }
Qed.

Lemma lsat_assoc:
  forall a1 a2 a3 p C (BP: boundph p),
    lsat p C (Lastar a1 (Lastar a2 a3)) <->
    lsat p C (Lastar (Lastar a1 a2) a3).
Proof.
  simpl.
  split.
  {
  intros.
  destruct H as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(C1,(C2,(sat1,(sat2,(p1p2,C1C2))))))))))).
  destruct sat2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(C3,(C4,(sat3,(sat4,(p3p4,C3C4))))))))))).
  rewrite <- p3p4 in phpdefp1p2.
  rewrite <- p1p2 in BP.
  rewrite <- p3p4 in BP.
  assert (phpdefp134: phplusdef p1 p3 /\ phplusdef p1 p4).
  {
  apply phpdef_dist'.
  assumption.
  assumption.
  }
  assert (bp134: boundph (phplus (phplus p1 p3) p4)).
  {
  apply bph_assoc.
  tauto.
  tauto.
  tauto.
  tauto.
  }
  assert (phpdef134: phplusdef (phplus p1 p3) p4).
  {
  apply phpdef_pair'.
  tauto.
  tauto.
  tauto.
  }
  exists (phplus p1 p3), p4, phpdef134.
  exists.
  apply boundph_mon with p4.
  assumption.
  assumption.
  assumption.
  assumption.
  exists bp4.
  exists bp134, (bagplus C1 C3), C4.
  exists.
  exists p1, p3.
  exists.
  tauto.
  exists bp1, bp3.
  exists.
  apply boundph_mon with p4.
  assumption.
  assumption.
  assumption.
  assumption.
  exists C1, C3.
  tauto.
  rewrite phplus_assoc.
  rewrite p3p4.
  rewrite bplus_assoc.
  rewrite C3C4.
  tauto.
  tauto.
  tauto.
  tauto.
  }
  {
  intros.
  destruct H as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(C1,(C2,(sat1,(sat2,(p1p2,C1C2))))))))))).
  destruct sat1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(C3,(C4,(sat3,(sat4,(p3p4,C3C4))))))))))).
  rewrite <- p3p4 in phpdefp1p2.
  rewrite <- p1p2 in BP.
  rewrite <- p3p4 in BP.
  assert (phpdefp134: phplusdef p3 p2 /\ phplusdef p4 p2).
  {
  apply phpdef_dist.
  assumption.
  assumption.
  }
  assert (bp134: boundph (phplus p3 (phplus p4 p2))).
  {
  apply bph_assoc.
  tauto.
  tauto.
  tauto.
  tauto.
  }
  assert (phpdef134: phplusdef p3 (phplus p4 p2)).
  {
  apply phpdef_assoc.
  tauto.
  tauto.
  tauto.
  assumption.
  }
  exists p3, (phplus p4 p2), phpdef134, bp3.
  exists.
  apply boundph_mon with p3.
  assumption.
  assumption.
  assumption.
  apply bph_comm.
  assumption.
  assumption.
  exists bp134, C3, (bagplus C4 C2).
  split.
  assumption.
  exists.
  exists p4, p2.
  exists.
  tauto.
  exists bp4, bp2.
  exists.
  apply boundph_mon with p3.
  assumption.
  assumption.
  assumption.
  apply bph_comm.
  assumption.
  assumption.
  exists C4, C2.
  tauto.
  rewrite <- phplus_assoc.
  rewrite p3p4.
  rewrite <- bplus_assoc.
  rewrite C3C4.
  tauto.
  tauto.
  tauto.
  tauto.
  }
Qed.

Lemma sat_assoc_comm:
  forall a1 a2 a3 p O C (BP: boundph p)
         (SAT:sat p O C ((a1 ** a2) ** a3)),
    sat p O C ((a2 ** a1) ** a3).
Proof.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(opo1o2,(sat1,(sat2,(p1p2,C1C2)))))))))))))).
  destruct sat1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(o3,(o4,(C3,(C4,(opo3o4,(sat3,(sat4,(p3p4,C3C4)))))))))))))).
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, o1, o2, C1, C2, opo1o2.
  exists.
  exists p4, p3.
  exists.
  apply phpdef_comm.
  assumption.
  exists bp4, bp3.
  exists.
  apply bph_comm.
  assumption.
  assumption.
  exists o4, o3, C4, C3.
  exists.
  apply oplus_comm.
  assumption.
  rewrite phplus_comm.
  rewrite bplus_comm.
  tauto.
  apply phpdef_comm.
  assumption.
  tauto.
Qed.

Lemma lsat_assoc_comm:
  forall a1 a2 a3 p C (BP: boundph p)
         (SAT:lsat p C (Lastar (Lastar a1 a2) a3)),
    lsat p C (Lastar (Lastar a2 a1) a3).
Proof.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(C1,(C2,(sat1,(sat2,(p1p2,C1C2))))))))))).
  destruct sat1 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp34,(C3,(C4,(sat3,(sat4,(p3p4,C3C4))))))))))).
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, C1, C2.
  exists.
  exists p4, p3.
  exists.
  apply phpdef_comm.
  assumption.
  exists bp4, bp3.
  exists.
  apply bph_comm.
  assumption.
  assumption.
  exists C4, C3.
  exists.
  assumption.
  rewrite phplus_comm.
  rewrite bplus_comm.
  tauto.
  apply phpdef_comm.
  assumption.
  tauto.
Qed.

Lemma sat_plus:
  forall a1 a2 p1 p2 C1 C2 o1 o2 o (PHPD: phplusdef p1 p2) (BP1: boundph p1) (BP2: boundph p2) (BP12: boundph (phplus p1 p2)) (opo1o2: oplus o1 o2 o)
         (SAT1: sat p1 o1 C1 a1)
         (SAT2: sat p2 o2 C2 a2),
    sat (phplus p1 p2) o (bagplus C1 C2) (a1 ** a2).
Proof.
  simpl.
  intros.
  exists p1, p2, PHPD, BP1, BP2, BP12, o1, o2, C1, C2, opo1o2.
  auto.
Qed.

Lemma lsat_plus:
  forall a1 a2 p1 p2 C1 C2 (PHPD: phplusdef p1 p2) (BP1: boundph p1) (BP2: boundph p2) (BP12: boundph (phplus p1 p2))
         (SAT1: lsat p1 C1 a1)
         (SAT2: lsat p2 C2 a2),
    lsat (phplus p1 p2) (bagplus C1 C2) (Lastar a1 a2).
Proof.
  simpl.
  intros.
  exists p1, p2, PHPD, BP1, BP2, BP12, C1, C2.
  auto.
Qed.

Lemma sat_star_imp:
  forall b b' a p o C
         (SAT: sat p o C (b ** a))
         (IMP: b |= b'),
    sat p o C (b' ** a).
Proof.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(o1,(o2,(C1,(C2,(opo1o2,(bt,(sat2,(p1p2,C1C2)))))))))))))).
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, o1, o2, C1, C2, opo1o2.
  split.
  apply IMP.
  assumption.
  assumption.
  tauto.
Qed.

Lemma lsat_star_imp:
  forall b b' a p C
         (SAT: lsat p C (Lastar b a))
         (IMP: forall p C (bp: boundph p) (SAT: lsat p C b), lsat p C b'),
    lsat p C (Lastar b' a).
Proof.
  simpl.
  intros.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(C1,(C2,(sat1,(sat2,(p1p2,C1C2))))))))))).
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, C1, C2.
  split.
  apply IMP.
  assumption.
  assumption.
  tauto.
Qed.

Lemma sat_fold_imp:
  forall l p C b b' (BP: boundph p)
         (SAT: sat p None C (fold_left Astar l b))
         (IMP: b |= b'),
    sat p None C (fold_left Astar l b').
Proof.
  induction l.
  simpl.
  intros.
  apply IMP.
  assumption.
  assumption.
  simpl.
  intros.
  eapply IHl.
  assumption.
  apply SAT.
  intros.
  apply sat_star_imp with b.
  assumption.
  assumption.
Qed.

Lemma lsat_fold_imp:
  forall l p C b b' (BP: boundph p)
         (SAT: lsat p C (fold_left Lastar l b))
         (IMP: forall p C (bp: boundph p) (SAT: lsat p C b), lsat p C b'),
    lsat p C (fold_left Lastar l b').
Proof.
  induction l.
  simpl.
  intros.
  apply IMP.
  assumption.
  assumption.
  simpl.
  intros.
  eapply IHl.
  assumption.
  apply SAT.
  intros.
  apply lsat_star_imp with b.
  assumption.
  assumption.
Qed.

Lemma sat_perm:
  forall l l' 
         (Perm: Permutation.Permutation l l') p C b 
         (BP: boundph p)
         (SAT: sat p None C (fold_left Astar l b)),
    sat p None C (fold_left Astar l' b).
Proof.
  intros l l' Perm.
  induction Perm.
  simpl.
  trivial.
  simpl.
  intros.
  apply IHPerm.
  assumption.
  assumption.
  simpl.
  intros.
  apply sat_fold_imp with ((b ** y) ** x).
  assumption.
  assumption.
  intros.
  apply sat_comm.
  apply sat_assoc.
  assumption.
  apply sat_assoc_comm.
  assumption.
  assumption.
  intros.
  apply IHPerm2.
  assumption.
  apply IHPerm1.
  assumption.
  assumption.
Qed.

Lemma lsat_perm:
  forall l l'
         (Perm: Permutation.Permutation l l')  p C b
         (BP: boundph p)
         (SAT: lsat p C (fold_left Lastar l b)),
    lsat p C (fold_left Lastar l' b).
Proof.
  intros l l' Perm.
  induction Perm.
  simpl.
  trivial.
  simpl.
  intros.
  apply IHPerm.
  assumption.
  assumption.
  simpl.
  intros.
  apply lsat_fold_imp with (Lastar (Lastar b y) x).
  assumption.
  assumption.
  intros.
  apply lsat_comm.
  apply lsat_assoc.
  assumption.
  apply lsat_assoc_comm.
  assumption.
  assumption.
  intros.
  apply IHPerm2.
  assumption.
  apply IHPerm1.
  assumption.
  assumption.
Qed.

Lemma sat_O_perm:
  forall a O O' p C
         (Perm: Permutation.Permutation O O')
         (SAT: sat p (Some O) C a),
    sat p (Some O') C a.
Proof.
  induction a;
  simpl;
  intros;
  try assumption.
  split.
  apply IHa1 with O.
  assumption.
  tauto.
  apply IHa2 with O.
  assumption.
  tauto.
  destruct SAT as [S|S].
  left.
  apply IHa1 with O.
  assumption.
  assumption.
  right.
  apply IHa2 with O.
  assumption.
  assumption.
  destruct SAT as (p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp12,(O1,(O2,(C1,(C2,(opO1O2,(SAT1,(SAT2,(p1p2,C1C2)))))))))))))).
  exists p1, p2, phpdefp1p2, bp1, bp2, bp12, O1, O2, C1, C2.
  exists.
  inversion opO1O2.
  apply fs_op.
  apply Permutation_trans with O.
  assumption.
  assumption.
  apply sn_op.
  apply Permutation_trans with O.
  assumption.
  assumption.
  auto.
  apply SAT with O'0.
  assumption.
  assumption.
  assumption.
  inversion OPLUS.
  apply fs_op.
  apply Permutation_trans with O'.
  assumption.
  assumption.
  assumption.
  destruct SAT as (pN,(CN,op)).
  split.
  assumption.
  split.
  assumption.
  apply fs_op.
  inversion op.
  apply Permutation_trans with O.
  assumption.
  assumption.
  destruct SAT as (v,sat).
  exists v.
  apply H with O.
  assumption.
  assumption.
  apply H with O.
  assumption.
  apply SAT.
  destruct SAT as (v,sat1).
  exists v.
  apply H with O.
  assumption.
  assumption.
Qed.

(** # <font size="5"><b> defl </b></font> # *)

Lemma defl_Notify A m:
   forall (l: list (A * Z)) id id' z p p' wt ot ct x1 x2
          (NEQ: id <> id')
          (NODUP: NoDup (map snd l))
          (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
          (IN: In (p,id) (map (fun x => (m x, snd x)) l))
          (IN': In (p',id') (map (fun x => (m x, snd x)) l))
          (P1z: exists wt1 ot1 ct1, p z = Some (Locked wt1 ot1 ct1))
          (X1: (m x1, snd x1) = (upd p z (Some (Locked wt ot ct)), id))
          (X2: (m x2, snd x2) = (p', id')),
     defl phplusdef (map (fun x => (m x, snd x)) (updl (updl l id x1) id' x2)).
Proof.
  intros.
  inversion X1.
  inversion X2.
  rewrite map_updl.
  {
  unfold defl in *.
  unfold updl in *.
  rewrite map_map.
  intros.
  apply in_map_iff in IN1.
  destruct IN1 as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) (snd x1)).
  inversion EQx.
  apply in_map_iff in IN2.
  destruct IN2 as (x3,(EQx3,INx3)).
  destruct (Z.eq_dec (snd x3) (snd x1)).
  inversion EQx3.
  omega.
  rewrite H0.
  apply phpdef_locked.
  apply DEFL with id id2.
  omega.
  assumption.
  apply in_map_iff.
  exists x3.
  tauto.
  assumption.
  apply in_map_iff in IN2.
  destruct IN2 as (x3,(EQx3,INx3)).
  destruct (Z.eq_dec (snd x3) (snd x1)).
  inversion EQx3.
  rewrite H0.
  apply phpdef_comm.
  apply phpdef_locked.
  apply DEFL with id id1.
  omega.
  assumption.
  apply in_map_iff.
  exists x.
  tauto.
  assumption.
  apply DEFL with id1 id2.
  omega.
  apply in_map_iff.
  exists x.
  tauto.
  apply in_map_iff.
  exists x3.
  tauto.
  }
  destruct x1.
  apply NoDup_updl.
  assumption.
  rewrite H2.
  rewrite H3.
  apply in_map_updl.
  omega.
  assumption.
Qed.

Lemma defl_NotifyAll A m (m': (A * Z) -> (A * Z)):
   forall (l l': list (A * Z)) id z p wt ot ct x1
          (NODUP: NoDup (map snd l))
          (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
          (IN: In (p,id) (map (fun x => (m x, snd x)) l))
          (P1z: exists wt1 ot1 ct1, p z = Some (Locked wt1 ot1 ct1))
          (X1: (m x1, snd x1) = (upd p z (Some (Locked wt ot ct)), id))
          (M': forall x, (m x, snd x) = (m (m' x), snd (m' x))),
     defl phplusdef (map (fun x => (m x, snd x)) (updl (map m' l) id x1)).
Proof.
  unfold defl in *.
  unfold updl in *.
  intros.
  inversion X1.
  rewrite map_map in *.
  apply in_map_iff in IN1.
  destruct IN1 as (x,(EQx,INx)).
  destruct (Z.eq_dec (snd x) id).
  inversion EQx.
  apply in_map_iff in IN2.
  destruct IN2 as (x3,(EQx3,INx3)).
  destruct (Z.eq_dec (snd x3) id).
  inversion EQx3.
  omega.
  rewrite H0.
  apply phpdef_locked.
  apply DEFL with id id2.
  omega.
  assumption.
  apply in_map_iff in INx3.
  destruct INx3 as (x4,(EQx4,INx4)).
  apply in_map_iff.
  exists x4.
  rewrite <- EQx4 in EQx3.
  rewrite <- M' in EQx3.
  tauto.
  assumption.
  apply in_map_iff in IN2.
  destruct IN2 as (x3,(EQx3,INx3)).
  destruct (Z.eq_dec (snd x3) id).
  inversion EQx3.
  rewrite H0.
  apply phpdef_comm.
  apply phpdef_locked.
  apply DEFL with id id1.
  omega.
  assumption.
  apply in_map_iff in INx.
  destruct INx as (x4,(EQx4,INx4)).
  apply in_map_iff.
  exists x4.
  rewrite <- EQx4 in EQx.
  rewrite <- M' in EQx.
  tauto.
  assumption.
  apply DEFL with id1 id2.
  omega.
  apply in_map_iff in INx.
  destruct INx as (x4,(EQx4,INx4)).
  apply in_map_iff.
  exists x4.
  rewrite <- EQx4 in EQx.
  rewrite <- M' in EQx.
  tauto.
  apply in_map_iff in INx3.
  destruct INx3 as (x4,(EQx4,INx4)).
  apply in_map_iff.
  exists x4.
  rewrite <- EQx4 in EQx3.
  rewrite <- M' in EQx3.
  tauto.
Qed.

Lemma defl_Wait A m:
   forall (l: list (A * Z)) id z p1 p2 x
          (NODUP: NoDup (map snd l))
          (BP2: boundph p2)
          (PHPD: phplusdef p1 p2)
          (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
          (IN: In (phplus p1 p2,id) (map (fun x => (m x, snd x)) l))
          (P1z: exists wt1 ot1 ct1, p1 z = Some (Locked wt1 ot1 ct1) \/ p1 z = Some (Ulock wt1 ot1 ct1))
          (X: (m x, snd x) = (upd p1 z (Some Lock), id)),
     defl phplusdef (map (fun x => (m x, snd x)) (updl l id x)).
Proof.
  unfold defl in *.
  unfold updl in *.
  intros.
  inversion X.
  rewrite map_map in *.
  apply in_map_iff in IN1.
  destruct IN1 as (x0,(EQx,INx)).
  destruct (Z.eq_dec (snd x0) id).
  inversion EQx.
  apply in_map_iff in IN2.
  destruct IN2 as (x3,(EQx3,INx3)).
  destruct (Z.eq_dec (snd x3) id).
  inversion EQx3.
  omega.
  rewrite H0.
  apply phpdef_locked_lock.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply DEFL with id id2.
  omega.
  assumption.
  apply in_map_iff.
  exists x3.
  tauto.
  apply phpdef_comm.
  assumption.
  assumption.
  apply in_map_iff in IN2.
  destruct IN2 as (x3,(EQx3,INx3)).
  destruct (Z.eq_dec (snd x3) id).
  inversion EQx3.
  rewrite H0.
  apply phpdef_comm.
  apply phpdef_locked_lock.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply DEFL with id id1.
  omega.
  assumption.
  apply in_map_iff.
  exists x0.
  tauto.
  apply phpdef_comm.
  assumption.
  assumption.
  apply DEFL with id1 id2.
  omega.
  apply in_map_iff.
  exists x0.
  tauto.
  apply in_map_iff.
  exists x3.
  tauto.
Qed.

Lemma defl_updl A m:
  forall (l: list (A * Z)) a z
         (PHPD: forall p id (NEQ: z <> id)
                       (IN: In (p, id) (map (fun x => (m x, snd x)) l)),
                  phplusdef p (m (a,z)))
         (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l)),
    defl phplusdef (map (fun x => (m x, snd x)) (updl l z (a, z))).
Proof.
  intros.
  unfold defl in *.
  intros.
  unfold updl in *.
  rewrite map_map in *.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  apply in_map_iff in IN2.
  destruct IN2 as (x2,(EQ2,IN2)).
  destruct (Z.eq_dec (snd x1) z).
  inversion EQ1.
  destruct (Z.eq_dec (snd x2) z).
  inversion EQ2.
  omega.
  inversion EQ2.
  rewrite <- H1.
  apply phpdef_comm.
  apply PHPD with id2.
  omega.
  apply in_map_iff.
  exists x2.
  inversion EQ2.
  tauto.
  destruct (Z.eq_dec (snd x2) z).
  inversion EQ2.
  rewrite <- H1.
  apply PHPD with id1.
  omega.
  apply in_map_iff.
  exists x1.
  tauto.
  apply DEFL with id1 id2.
  omega.
  apply in_map_iff.
  exists x1.
  tauto.
  apply in_map_iff.
  exists x2.
  tauto.
Qed.

Lemma phpdef_fold A m:
  forall (l: list (A * Z)) p b
         (NODUP: NoDup (map snd l))
         (PHPDL: defl phplusdef (map (fun x => (m x, snd x)) l))
         (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
         (PHPLp: forall p0 (IN: In p0 (map m l)), phplusdef p0 p)
         (PHPDbp: phplusdef b p),
    phplusdef (fold_left phplus (map m l) b) p.
Proof.
  induction l.
  simpl.
  intros.
  assumption.
  simpl.
  intros.
  apply IHl.
  inversion NODUP.
  assumption.
  unfold defl in *.
  intros.
  apply PHPDL with id1 id2.
  omega.
  right.
  assumption.
  right.
  assumption.
  intros.
  apply phpdef_pair.
  apply phpdef_comm.
  apply DEFLb.
  left.
  reflexivity.
  apply DEFLb.
  right.
  assumption.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct x.
  unfold defl in PHPDL.
  apply PHPDL with z (snd a).
  unfold not.
  intros.
  inversion NODUP.
  apply H2.
  rewrite <- H.
  apply in_map_iff.
  exists (a0,z).
  tauto.
  right.
  apply in_map_iff.
  exists (a0,z).
  rewrite EQx.
  tauto.
  left.
  reflexivity.
  intros.
  apply PHPLp.
  right.
  assumption.
  apply phpdef_pair'.
  apply phpdef_comm.
  apply DEFLb.
  tauto.
  tauto.
  apply PHPLp.
  tauto.
Qed.

Lemma locked_fold_phtoheap A m:
  forall (l: list (A * Z)) id p b h z
         (EXT: forall z p, exists x2, m (x2, z) = p)
         (NODUP: NoDup (map snd l))
         (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
         (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
         (IN: In (p,id) (map (fun x => (m x, snd x)) l))
         (Pl : p z = Some Lock \/ (exists wt ot ct : bag, p z = Some (Locked wt ot ct)))
         (hz': h z = Some 1%Z)
         (PH2H: h = phtoh (fold_left phplus (map m l) b)),
    forall p' (IN: In p' (map m l) \/ p' = b), p' z = None \/ p' z = Some Lock.
Proof.
  intros.
  assert (EXT1:=EXT).
  specialize EXT with id (emp knowledge).
  destruct EXT as (empx,memp).

  assert (phpdefpb: phplusdef p b).
  {
  apply DEFLb.
  apply in_map_iff.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ1,IN1)).
  exists x1.
  inversion EQ1.
  tauto.
  }

  assert (G: h = phtoh (phplus p (fold_left phplus (map m (updl l id (empx, id))) b))).
  {
  erewrite <- fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge)
    (x2:=p)(id:=id)(x:=empx).
  assumption.
  apply can_phpdef.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  rewrite phplus_comm.
  rewrite phplus_emp.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  }

  assert (pz: p z = Some Lock).
  {
  destruct Pl as [pz|pz].
  assumption.
  apply equal_f with z in G.
  unfold phtoh in G.
  unfold phplus in G.
  destruct pz as (wt,(ot,(ct,pz))).
  rewrite pz in G.
  rewrite hz' in G.
  inversion G.
  }

  assert (deflu: defl phplusdef (map (fun x : A * Z => (m x, snd x)) (updl l id (empx, id)))).
  {
  apply defl_updl.
  intros.
  rewrite memp.
  apply phpdef_emp.
  assumption.
  }

  destruct IN0 as [INp'|EQp'].
  {
  apply in_map_iff in INp'.
  destruct INp' as (x0,(EQ0,IN0)).
  inversion EQ0.
  destruct x0.
  destruct (Z.eq_dec z0 id).
  {
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ1,IN1)).
  destruct x1.
  inversion EQ1.
  simpl in H2.
  rewrite e in *.
  rewrite H2 in *.
 
  assert (EQa: a0 = a).
  {
  eapply unique_key_eq.
  apply IN1.
  apply IN0.
  assumption.
  }
  rewrite <- EQa in EQ0.
  rewrite EQ0 in H1.
  rewrite H.
  rewrite H1.
  right.
  assumption.
  }

  assert (phpdefpp': phplusdef p p').
  {
  unfold defl in DEFL.
  apply DEFL with id z0.
  omega.
  assumption.
  apply in_map_iff.
  exists (a,z0).
  rewrite EQ0.
  tauto.
  }

  assert (phpdefpp'1:=phpdefpp').
  unfold phplusdef in phpdefpp'.
  specialize phpdefpp' with z.
  rewrite pz in phpdefpp'.
  rewrite H.
  destruct (p' z) eqn:p'z.
  destruct k;
  try tauto.
  Focus 2.
  left.
  reflexivity.

  specialize EXT1 with z0 (emp knowledge).
  destruct EXT1 as (empx1,memp1).

  assert (deflu1: defl phplusdef (map (fun x : A * Z => (m x, snd x)) (updl (updl l id (empx, id)) z0 (empx1, z0)))).
  {
  apply defl_updl.
  intros.
  rewrite memp1.
  apply phpdef_emp.
  assumption.
  }

  assert (G1: h = phtoh (phplus p (phplus p' (fold_left phplus (map m (updl (updl l id (empx, id)) z0 (empx1,z0))) b)))).
  {
  erewrite <- fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge)
    (x2:=p')(id:=z0)(x:=empx1).
  assumption.
  apply can_phpdef.
  apply NoDup_updl.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  intros.
  unfold updl in IN1.
  rewrite map_map in IN1.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ1.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  apply DEFLb.
  apply in_map_iff.
  exists x1.
  inversion EQ1.
  tauto.
  rewrite phplus_comm.
  rewrite phplus_emp.
  apply in_map_iff.
  exists (a, z0).
  rewrite H.
  split.
  tauto.
  apply in_updl_neq.
  omega.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  }

  assert (phpdefbp': phplusdef b p').
  {
  apply phpdef_comm.
  apply DEFLb.
  apply in_map_iff.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ1,IN1)).
  exists (a, z0).
  inversion EQ0.
  tauto.
  }

  assert (phpdefpfold: phplusdef p (fold_left phplus (map m (updl (updl l id (empx, id)) z0 (empx1, z0))) b)).
  {
  apply phpdef_comm.
  apply phpdef_fold.
  apply NoDup_updl.
  apply NoDup_updl.
  assumption.
  assumption.
  intros.
  unfold updl in IN1.
  rewrite map_map in IN1.
  rewrite map_map in IN1.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  simpl in EQ1.
  destruct (Z.eq_dec id z0).
  rewrite <- EQ1.
  rewrite memp1.
  apply phpdef_comm.
  apply phpdef_emp.
  rewrite <- EQ1.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  destruct (Z.eq_dec (snd x1) z0).
  rewrite <- EQ1.
  rewrite memp1.
  apply phpdef_comm.
  apply phpdef_emp.
  apply DEFLb.
  apply in_map_iff.
  exists x1.
  inversion EQ1.
  tauto.
  intros.
  unfold updl in IN1.
  rewrite map_map in IN1.
  rewrite map_map in IN1.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  simpl in EQ1.
  destruct (Z.eq_dec id z0).
  rewrite <- EQ1.
  rewrite memp1.
  apply phpdef_comm.
  apply phpdef_emp.
  rewrite <- EQ1.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  destruct (Z.eq_dec (snd x1) z0).
  rewrite <- EQ1.
  rewrite memp1.
  apply phpdef_comm.
  apply phpdef_emp.
  unfold defl in DEFL.
  apply DEFL with (snd x1) id.
  omega.
  apply in_map_iff.
  exists x1.
  inversion EQ1.
  tauto.
  assumption.
  apply phpdef_comm.
  assumption.
  }

  assert (phpdefp'fold: phplusdef p' (fold_left phplus (map m (updl (updl l id (empx, id)) z0 (empx1, z0))) b)).
  {
  apply phpdef_comm.

  apply phpdef_fold.
  apply NoDup_updl.
  apply NoDup_updl.
  assumption.
  assumption.
  intros.
  unfold updl in IN1.
  rewrite map_map in IN1.
  rewrite map_map in IN1.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  simpl in EQ1.
  destruct (Z.eq_dec id z0).
  rewrite <- EQ1.
  rewrite memp1.
  apply phpdef_comm.
  apply phpdef_emp.
  rewrite <- EQ1.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  destruct (Z.eq_dec (snd x1) z0).
  rewrite <- EQ1.
  rewrite memp1.
  apply phpdef_comm.
  apply phpdef_emp.
  apply DEFLb.
  apply in_map_iff.
  exists x1.
  inversion EQ1.
  tauto.
  intros.
  unfold updl in IN1.
  rewrite map_map in IN1.
  rewrite map_map in IN1.
  apply in_map_iff in IN1.
  destruct IN1 as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  simpl in EQ1.
  destruct (Z.eq_dec id z0).
  rewrite <- EQ1.
  rewrite memp1.
  apply phpdef_comm.
  apply phpdef_emp.
  rewrite <- EQ1.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  destruct (Z.eq_dec (snd x1) z0).
  rewrite <- EQ1.
  rewrite memp1.
  apply phpdef_comm.
  apply phpdef_emp.
  unfold defl in DEFL.
  apply DEFL with (snd x1) z0.
  omega.
  apply in_map_iff.
  exists x1.
  inversion EQ1.
  tauto.
  apply in_map_iff.
  exists (a, z0).
  rewrite EQ0.
  tauto.
  assumption.
  }

  assert (G2: h = phtoh (phplus (phplus p p') (fold_left phplus (map m (updl (updl l id (empx, id)) z0 (empx1, z0))) b))).
  {
  rewrite phplus_assoc.
  assumption.
  assumption.
  assumption.
  assumption.
  }

  apply equal_f with z in G2.
  unfold phtoh in G2.
  unfold phplus in G2.
  rewrite pz in G2.
  rewrite p'z in G2.
  rewrite hz' in G2.
  inversion G2.
  }
  rewrite EQp'.
  assert (G1: h = phtoh (phplus p (phplus b (fold_left phplus (map m (updl l id (empx, id))) (emp knowledge))))).
  {
  rewrite <- fold_left_f_m_def with (def:=phplusdef).
  rewrite phplus_emp.
  assumption.
  apply can_phpdef.
  apply NoDup_updl.
  assumption.
  assumption.
  apply phpdef_emp.
  intros.
  split.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ1.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  apply DEFLb.
  apply in_map_iff.
  exists x1.
  rewrite <- EQ1.
  tauto.
  apply phpdef_emp.
  }

  assert (G2: h = phtoh (phplus (phplus p b) (fold_left phplus (map m (updl l id (empx, id))) (emp knowledge)))).
  {
  rewrite phplus_assoc.
  assumption.
  assumption.
  {
  apply phpdef_comm.
  apply phpdef_fold.
  apply NoDup_updl.
  assumption.
  assumption.
  intros.
  apply phpdef_emp.
  intros.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ1.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  unfold defl in DEFL.
  apply DEFL with (snd x1) id.
  omega.
  apply in_map_iff.
  exists x1.
  rewrite <- EQ1.
  tauto.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  }
  apply phpdef_comm.
  apply phpdef_fold.
  apply NoDup_updl.
  assumption.
  assumption.
  intros.
  apply phpdef_emp.
  intros.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ1.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  apply DEFLb.
  apply in_map_iff.
  exists x1.
  rewrite <- EQ1.
  tauto.
  apply phpdef_comm.
  apply phpdef_emp.
  }

  assert (phpdefpb2:=phpdefpb).
  unfold phplusdef in phpdefpb.
  specialize phpdefpb with z.
  rewrite pz in phpdefpb.
  destruct (b z) eqn:bz.
  destruct k;
  try tauto.
  Focus 2.
  left.
  reflexivity.
  apply equal_f with z in G2.
  unfold phtoh in G2.
  unfold phplus in G2.
  rewrite pz in G2.
  rewrite bz in G2.
  rewrite hz' in G2.
  inversion G2.
Qed.

Lemma defl_Acquire A m:
   forall (l: list (A * Z)) id p p1 p2 x z h
          (EXT: forall z p, exists x2, m (x2, z) = p)
          (NODUP: NoDup (map snd l))
          (PHPDEF: phplusdef p1 p2)
          (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 (phplus p1 p2))
          (NODUP: NoDup (map snd l))
          (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
          (IN: In (p,id) (map (fun x => (m x, snd x)) l))
          (Pl : p z = Some Lock \/ (exists wt ot ct : bag, p z = Some (Locked wt ot ct)))
          (hz': h z = Some 1%Z)
          (PH2H: h = phtoh (fold_left phplus (map m l) (phplus p1 p2)))
          (X: exists wt ot ct, m (x,id) = phplus (upd p z (Some (Locked wt ot ct))) p1),
     defl phplusdef (map (fun x => (m x, snd x)) (updl l id (x,id))).
Proof.
  intros.
  assert (p'z: forall p' (IN: In p' (map m l) \/ p' = phplus p1 p2), p' z = None \/ p' z = Some Lock).
  {
  apply locked_fold_phtoheap with id p h.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }

  assert (p1z: p1 z = None \/ p1 z = Some Lock).
  {
  apply phplus_locked_mono with p2.
  apply p'z.
  right.
  reflexivity.
  }

  assert (p2z: p2 z = None \/ p2 z = Some Lock).
  {
  apply phplus_locked_mono with p1.
  apply p'z.
  right.
  apply phplus_comm.
  apply phpdef_comm.
  assumption.
  }

  assert (phpdefpp12: phplusdef p (phplus p1 p2)).
  {
  apply DEFLb.
  apply in_map_iff.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ1,IN1)).
  exists x1.
  inversion EQ1.
  tauto.
  }

  assert (phpdefpp1pp2: phplusdef p p1 /\ phplusdef p p2).
  {
  apply phpdef_dist'.
  assumption.
  assumption.
  }

  unfold defl in *.
  unfold updl in *.
  intros.
  rewrite map_map in *.
  destruct X as (wt,(ot,(ct,EQm))).
  apply in_map_iff in IN1.
  destruct IN1 as (x0,(EQx,INx)).
  destruct (Z.eq_dec (snd x0) id).
  inversion EQx.
  apply in_map_iff in IN2.
  destruct IN2 as (x3,(EQx3,INx3)).
  destruct (Z.eq_dec (snd x3) id).
  inversion EQx3.
  omega.
  rewrite <- H1.
  rewrite EQm.
  apply phpdef_pair'.
  apply phpdef_upd_locked.
  tauto.
  tauto.
  apply phpdef_upd_locked.
  apply DEFL with id id2.
  omega.
  assumption.
  apply in_map_iff.
  exists x3.
  tauto.
  inversion EQx3.
  assert (G:  m x3 z = None \/ m x3 z = Some Lock).
  {
  apply p'z.
  left.
  apply in_map.
  assumption.
  }
  tauto.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply phpdef_comm.
  apply DEFLb.
  apply in_map_iff.
  exists x3.
  inversion EQx3.
  tauto.
  apply phpdef_comm.
  assumption.
  apply in_map_iff in IN2.
  destruct IN2 as (x3,(EQx3,INx3)).
  destruct (Z.eq_dec (snd x3) id).
  inversion EQx3.
  rewrite <- H1.
  rewrite EQm.
  apply phpdef_pair.
  apply phpdef_upd_locked.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply phpdef_comm.
  apply DEFLb.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ,IN)).
  apply in_map_iff.
  exists x1.
  inversion EQ.
  tauto.
  apply phpdef_comm.
  assumption.
  tauto.
  apply phpdef_comm.
  apply phpdef_upd_locked.
  apply DEFL with id id1.
  omega.
  assumption.
  apply in_map_iff.
  exists x0.
  tauto.
  inversion EQx.
  assert (G: m x0 z = None \/ m x0 z = Some Lock).
  {
  apply p'z.
  left.
  apply in_map.
  assumption.
  }
  tauto.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply phpdef_comm.
  apply DEFLb.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ,IN)).
  apply in_map_iff.
  exists x0.
  inversion EQx.
  tauto.
  apply phpdef_comm.
  assumption.
  apply DEFL with id1 id2.
  omega.
  apply in_map_iff.
  exists x0.
  inversion EQx.
  tauto.
  apply in_map_iff.
  exists x3.
  tauto.
Qed.


(** # <font size="5"><b> fold_left </b></font> # *)

Lemma fold_left_upd_Notify_1 A m:
   forall (l: list (A * Z)) id z p b wt ot ct x1
          (EXT: forall z p, exists x, m (x, z) = p)
          (NODUP: NoDup (map snd l))
          (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
          (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
          (IN: In (p,id) (map (fun x => (m x, snd x)) l))
          (P1z: exists wt1 ot1 ct1, p z = Some (Locked wt1 ot1 ct1))
          (X1: (m x1, snd x1) = (upd p z (Some (Locked wt ot ct)), id)),
      fold_left phplus (map m (updl l id x1)) b = 
        upd (fold_left phplus (map m l) b) z (Some (Locked wt ot ct)).
Proof.
  intros.
  inversion X1.
  destruct x1.
  specialize EXT with z0 (emp knowledge).
  destruct EXT as (empx, memp).
  erewrite fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge)
    (x2:=upd p z (Some (Locked wt ot ct)))(id:=z0)(x:=empx).
  {
  rewrite updl_updl.
  replace (fold_left phplus (map m l) b) with
    (phplus p (fold_left phplus (map m (updl l z0 (empx,z0))) b)).
  {
  apply phplus_upd.
  unfold not.
  intros CO.
  destruct CO as (v,(f,(v',(f',(CO,rest))))).
  inversion CO.
  intros CO.
  inversion CO.
  intros CO.
  inversion CO.
  }
  symmetry.
  apply fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge).
  apply can_phpdef.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  rewrite phplus_comm.
  rewrite phplus_emp.
  simpl in H1.
  rewrite H1.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  }
  apply can_phpdef.
  apply NoDup_updl.
  assumption.
  apply defl_updl.
  intros.
  rewrite H0.
  apply phpdef_comm.
  apply phpdef_locked.
  unfold defl in DEFL.
  apply DEFL with id id0.
  simpl in H1.
  omega.
  assumption.
  assumption.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  intros.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  simpl in IN0.
  destruct IN0 as (x0,(EQ0,IN0)).
  destruct (Z.eq_dec (snd x0) z0).
  rewrite <- EQ0.
  rewrite H0.
  apply phpdef_locked.
  apply DEFLb.
  apply in_map_iff in IN.
  destruct IN as (x1,(EXx,INx)).
  apply in_map_iff.
  exists x1.
  inversion EXx.
  tauto.
  assumption.
  rewrite <- EQ0.
  apply DEFLb.
  apply in_map.
  assumption.
  rewrite phplus_comm.
  rewrite phplus_emp.
  apply in_map_iff.
  exists (a,z0).
  split.
  inversion X1.
  tauto.
  apply in_updl_eq.
  apply in_map_iff in IN.
  destruct IN as (x1,(EXx,INx)).
  destruct x1.
  exists a0.
  rewrite H1.
  inversion EXx.
  rewrite <- H3.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
Qed.

Lemma fold_left_upd_Notify A m:
   forall (l: list (A * Z)) id id' z p p' b wt ot ct x1 x2
          (NEQ: id <> id')
          (EXT: forall z p, exists x, m (x, z) = p)
          (NODUP: NoDup (map snd l))
          (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
          (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
          (IN: In (p,id) (map (fun x => (m x, snd x)) l))
          (IN': In (p',id') (map (fun x => (m x, snd x)) l))
          (P1z: exists wt1 ot1 ct1, p z = Some (Locked wt1 ot1 ct1))
          (X1: (m x1, snd x1) = (upd p z (Some (Locked wt ot ct)), id))
          (X2: (m x2, snd x2) = (p', id')),
      fold_left phplus (map m (updl (updl l id x1) id' x2)) b = 
        upd (fold_left phplus (map m l) b) z (Some (Locked wt ot ct)).
Proof.
  intros.
  inversion X1.
  inversion X2.
  rewrite map_updl2.
  {
  apply fold_left_upd_Notify_1 with (p:=p).
  assumption.
  assumption.
  assumption.
  assumption.
  rewrite H1.
  assumption.
  assumption.
  rewrite H0.
  reflexivity.
  }
  destruct x1.
  apply NoDup_updl.
  assumption.
  destruct x2.
  simpl in H3.
  rewrite H3 in *.
  apply in_map_iff in IN'.
  destruct IN' as (x',(EX',IN')).
  apply in_map_iff.
  exists x'.
  split.
  inversion EX'.
  rewrite H5 in *.
  rewrite H2.
  rewrite H4.
  tauto.
  destruct x'.
  apply in_updl_neq.
  inversion EX'.
  rewrite H1.
  omega.
  assumption.
Qed.

Lemma fold_locked A m:
  forall (l: list (A * Z)) wt ot ct z b
         (EXT: forall z p, exists x, m (x, z) = p)
         (NODUP: NoDup (map snd l))
         (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
         (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
         (P1z: b z = Some (Locked wt ot ct) \/ exists p (IN: In p (map m l)), p z = Some (Locked wt ot ct)),
    (fold_left phplus (map m l) b) z = Some (Locked wt ot ct).
Proof.
  intros.
  destruct P1z as [p1z|p1z].
  {
  replace b with (phplus b (emp knowledge)).
  rewrite fold_left_f_m_def with (def:=phplusdef).
  unfold phplus.
  rewrite p1z.
  reflexivity.
  apply can_phpdef.
  assumption.
  assumption.
  apply phpdef_emp.
  intros.
  split.
  apply DEFLb.
  assumption.
  apply phpdef_emp.
  apply phplus_emp.
  }
  {
  destruct p1z as (p, (INp, EQp)).
  assert (INp2:=INp).
  apply in_map_iff in INp2.
  destruct INp2 as (x, (EXx, INx)).
  destruct x.
  specialize EXT with z0 (emp knowledge).
  destruct EXT as (empx, memp).
  erewrite fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge)
    (x2:=p)(id:=z0)(x:=empx).
  unfold phplus.
  rewrite EQp.
  reflexivity.
  apply can_phpdef.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  rewrite phplus_comm.
  rewrite phplus_emp.
  apply in_map_iff.
  exists (a,z0).
  simpl.
  rewrite EXx.
  tauto.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  }
Qed.

Lemma fold_ulock A m:
  forall (l: list (A * Z)) wt ot ct z b
         (EXT: forall z p, exists x, m (x, z) = p)
         (NODUP: NoDup (map snd l))
         (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
         (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
         (P1z: b z = Some (Ulock wt ot ct) \/ exists p (IN: In p (map m l)), p z = Some (Ulock wt ot ct)),
    (fold_left phplus (map m l) b) z = Some (Ulock wt ot ct).
Proof.
  intros.
  destruct P1z as [p1z|p1z].
  {
  replace b with (phplus b (emp knowledge)).
  rewrite fold_left_f_m_def with (def:=phplusdef).
  unfold phplus.
  rewrite p1z.
  reflexivity.
  apply can_phpdef.
  assumption.
  assumption.
  apply phpdef_emp.
  intros.
  split.
  apply DEFLb.
  assumption.
  apply phpdef_emp.
  apply phplus_emp.
  }
  {
  destruct p1z as (p, (INp, EQp)).
  assert (INp2:=INp).
  apply in_map_iff in INp2.
  destruct INp2 as (x, (EXx, INx)).
  destruct x.
  specialize EXT with z0 (emp knowledge).
  destruct EXT as (empx, memp).
  erewrite fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge)
    (x2:=p)(id:=z0)(x:=empx).
  unfold phplus.
  rewrite EQp.
  reflexivity.
  apply can_phpdef.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  rewrite phplus_comm.
  rewrite phplus_emp.
  apply in_map_iff.
  exists (a,z0).
  simpl.
  rewrite EXx.
  tauto.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  }
Qed.

Lemma fold_cond A m:
  forall (l: list (A * Z)) z b 
         (EXT: forall z p, exists x, m (x, z) = p)
         (NODUP: NoDup (map snd l))
         (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
         (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
         (P1z: b z = Some Cond \/ exists p (IN: In p (map m l)), p z = Some Cond),
    (fold_left phplus (map m l) b) z = Some Cond.
Proof.
  intros.
  destruct P1z as [p1z|p1z].
  {
  replace b with (phplus b (emp knowledge)).
  rewrite fold_left_f_m_def with (def:=phplusdef).
  unfold phplus.
  rewrite p1z.
  reflexivity.
  apply can_phpdef.
  assumption.
  assumption.
  apply phpdef_emp.
  intros.
  split.
  apply DEFLb.
  assumption.
  apply phpdef_emp.
  apply phplus_emp.
  }
  {
  destruct p1z as (p, (INp, EQp)).
  assert (INp2:=INp).
  apply in_map_iff in INp2.
  destruct INp2 as (x, (EXx, INx)).
  destruct x.
  specialize EXT with z0 (emp knowledge).
  destruct EXT as (empx, memp).
  erewrite fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge)
    (x2:=p)(id:=z0)(x:=empx).
  unfold phplus.
  rewrite EQp.
  reflexivity.
  apply can_phpdef.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  rewrite phplus_comm.
  rewrite phplus_emp.
  apply in_map_iff.
  exists (a,z0).
  simpl.
  rewrite EXx.
  tauto.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  }
Qed.

Lemma phplus_fold_lock A m:
  forall (l:list (A * Z)) z b
         (EXT: forall z p, exists x, m (x, z) = p)
         (NODUP: NoDup (map snd l))
         (PHPDL: defl phplusdef (map (fun x => (m x,snd x)) l))
         (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
         (P1z: b z = Some Lock \/ exists p (IN: In p (map m l)), p z = Some Lock),
    (fold_left phplus (map m l) b) z = Some Lock \/
    exists wt ot ct, (fold_left phplus (map m l) b) z = Some (Locked wt ot ct).
Proof.
  intros.
  destruct P1z as [p1z|p1z].
  {
  replace b with (phplus b (emp knowledge)).
  rewrite fold_left_f_m_def with (def:=phplusdef).
  apply phplus_lock.
  left.
  assumption.
  apply can_phpdef.
  assumption.
  assumption.
  apply phpdef_emp.
  intros.
  split.
  apply DEFLb.
  assumption.
  apply phpdef_emp.
  apply phplus_emp.
  }
  {
  destruct p1z as (p, (INp, EQp)).
  assert (INp2:=INp).
  apply in_map_iff in INp2.
  destruct INp2 as (x, (EXx, INx)).
  destruct x.
  specialize EXT with z0 (emp knowledge).
  destruct EXT as (empx, memp).
  erewrite fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge)
    (x2:=p)(id:=z0)(x:=empx).
  apply phplus_lock.
  left.
  assumption.
  apply can_phpdef.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  rewrite phplus_comm.
  rewrite phplus_emp.
  apply in_map_iff.
  exists (a,z0).
  simpl.
  rewrite EXx.
  tauto.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  }
Qed.

Lemma fold_lock_ed A m:
  forall (l: list (A * Z)) z b
         (EXT: forall z p, exists x, m (x, z) = p)
         (NODUP: NoDup (map snd l))
         (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
         (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
         (P1z: b z = Some Lock \/ (exists wt ot ct, b z = Some (Locked wt ot ct))
           \/ exists p (IN: In p (map m l)), p z = Some Lock \/ exists wt ot ct, p z = Some (Locked wt ot ct)),
    (fold_left phplus (map m l) b) z = Some Lock \/
    exists wt ot ct, (fold_left phplus (map m l) b) z = Some (Locked wt ot ct).
Proof.
  intros.
  destruct P1z as [p1z|p1z].
  apply phplus_fold_lock.
  assumption.
  assumption.
  assumption.
  assumption.
  left.
  assumption.
  destruct p1z as [p1z|p1z].
  right.
  destruct p1z as (wt, (ot, (ct, bz))).
  exists wt, ot, ct.
  apply fold_locked.
  assumption.
  assumption.
  assumption.
  assumption.
  left.
  assumption.
  destruct p1z as (p,(INp,p1z)).
  destruct p1z as [p1z|p1z].
  apply phplus_fold_lock.
  assumption.
  assumption.
  assumption.
  assumption.
  right.
  exists p, INp.
  assumption.
  right.
  destruct p1z as (wt, (ot, (ct, bz))).
  exists wt, ot, ct.
  apply fold_locked.
  assumption.
  assumption.
  assumption.
  assumption.
  right.
  exists p, INp.
  assumption.
Qed.

Lemma lock_Wait A m:
  forall (l: list (A * Z)) id z p1 p2 x b
         (EXT: forall z p, exists x, m (x, z) = p)
         (NODUP: NoDup (map snd l))
         (PHPD: phplusdef p1 p2)
         (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
         (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
         (IN: In (phplus p1 p2,id) (map (fun x => (m x, snd x)) l))
         (P1z: exists wt1 ot1 ct1, p1 z = Some (Locked wt1 ot1 ct1) \/ p1 z = Some (Ulock wt1 ot1 ct1))
         (X: (m x, snd x) = (upd p1 z (Some Lock), id)),
     fold_left phplus (map m (updl l id x)) (phplus b p2) z = Some Lock.
Proof.
  intros.
  assert (IN1:=IN).
  apply in_map_iff in IN1.
  destruct IN1 as (x12,(EQx,INx)).
  assert (EXTE:=EXT).
  specialize EXT with id p2.
  destruct EXT as (x2, mx2).
  destruct P1z as (wt, (ot, (ct, p1z))).

  assert (G1:
    phplus p1 (fold_left phplus (map m (updl l id (x2, id))) b) z = Some (Locked wt ot ct) \/
    phplus p1 (fold_left phplus (map m (updl l id (x2, id))) b) z = Some (Ulock wt ot ct)).
  {
  destruct p1z as [p1z|p1z];
  unfold phplus;
  rewrite p1z;
  tauto;
  reflexivity.
  }
  assert (PHPDF: phplusdef p1 (fold_left phplus (map m (updl l id (x2, id))) b)).
  {
  apply phpdef_comm.
  apply phpdef_fold.
  apply NoDup_updl.
  assumption.
  apply defl_updl.
  intros.
  rewrite mx2.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  unfold defl in DEFL.
  apply DEFL with id id0.
  omega.
  assumption.
  assumption.
  assumption.
  {
  intros.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x0,(EQ0,IN0)).
  destruct (Z.eq_dec (snd x0) id).
  rewrite <- EQ0.
  rewrite mx2.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply DEFLb.
  apply in_map_iff.
  exists x12.
  inversion EQx.
  tauto.
  apply DEFLb.
  apply in_map_iff.
  exists x0.
  tauto.
  }
  {
  intros.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x0,(EQ0,IN0)).
  destruct (Z.eq_dec (snd x0) id).
  rewrite <- EQ0.
  rewrite mx2.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  unfold defl in DEFL.
  destruct x0.
  simpl in n.
  apply DEFL with id z0.
  omega.
  assumption.
  apply in_map_iff.
  exists (a,z0).
  inversion EQ0.
  tauto.
  apply phpdef_comm.
  assumption.
  }
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply DEFLb.
  apply in_map_iff.
  exists x12.
  inversion EQx.
  tauto.
  apply phpdef_comm.
  assumption.
  }
  assert (G2:
    (fold_left phplus (map m (updl l id (x2, id))) b) z = Some Lock \/
    (fold_left phplus (map m (updl l id (x2, id))) b) z = None).
  {
  destruct G1 as [G1z|G1z].
  {
  destruct p1z as [p1z|p1z].
  unfold phplus in G1z.
  rewrite p1z in G1z.
  Focus 2.
  unfold phplus in G1z.
  rewrite p1z in G1z.
  inversion G1z.
  apply phplus_lock_mon with p1 wt ot ct.
  assumption.
  assumption.
  }
  destruct p1z as [p1z|p1z].
  unfold phplus in G1z.
  rewrite p1z in G1z.
  inversion G1z.
  right.
  apply phplus_ulock_mon with p1 wt ot ct.
  assumption.
  assumption.
  }

  specialize EXTE with id (emp knowledge).
  destruct EXTE as (empx, memp).

  assert (G3:
    phplus p2 (fold_left phplus (map m (updl (updl l id (x2, id)) id (empx, id))) b) z = Some Lock \/
    phplus p2 (fold_left phplus (map m (updl (updl l id (x2, id)) id (empx, id))) b) z = None).
  {
  rewrite <- fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge)
    (x2:=p2)(id:=id)(x:=empx).
  assumption.
  apply can_phpdef.
  apply NoDup_updl.
  assumption.
  apply defl_updl.
  intros.
  rewrite mx2.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  unfold defl in DEFL.
  apply DEFL with id id0.
  omega.
  assumption.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  intros.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ0,IN0)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ0.
  rewrite mx2.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply DEFLb.
  apply in_map_iff.
  exists x12.
  inversion EQx.
  tauto.
  apply DEFLb.
  apply in_map_iff.
  exists x1.
  inversion EQ0.
  tauto.
  rewrite phplus_comm.
  rewrite phplus_emp.
  apply in_map_iff.
  exists (x2, id).
  split.
  rewrite mx2.
  tauto.
  unfold updl.
  apply in_map_iff.
  exists x12.
  inversion EQx.
  rewrite eqz.
  tauto.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  }  

  assert (G4:
    fold_left phplus (map m (updl l id (empx, id))) (phplus b p2) z = Some Lock \/
    fold_left phplus (map m (updl l id (empx, id))) (phplus b p2) z = None).
  {
  rewrite updl_updl in G3.
  rewrite <- fold_left_f_m_def with (def:=phplusdef) in G3.
  rewrite phplus_comm in G3.
  assumption.
  apply can_phpdef.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply DEFLb.
  apply in_map_iff.
  exists x12.
  inversion EQx.
  tauto.
  apply can_phpdef.
  apply NoDup_updl.
  assumption.
  apply defl_updl.
  intros.
  rewrite memp.
  apply phpdef_emp.
  assumption.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply DEFLb.
  apply in_map_iff.
  exists x12.
  inversion EQx.
  tauto.
  intros.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ0,IN0)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ0.
  rewrite memp.
  split.
  apply phpdef_comm.
  apply phpdef_emp.
  apply phpdef_comm.
  apply phpdef_emp.
  split.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  destruct x1.
  unfold defl in DEFL.
  apply DEFL with id z0.
  simpl in n.
  omega.
  assumption.
  apply in_map_iff.
  exists (a, z0).
  inversion EQ0.
  tauto.
  apply DEFLb.
  apply in_map_iff.
  exists x1.
  inversion EQ0.
  tauto.
  }

  erewrite fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge)
    (x2:=upd p1 z (Some Lock))(id:=id)(x:=empx).
  {
  destruct x.
  inversion X.
  rewrite updl_updl.
  rewrite <- H1.
  rewrite H0.
  apply phplus_upd_lock.
  rewrite H1.
  assumption.
  }
  apply can_phpdef.
  destruct x.
  inversion X.
  apply NoDup_updl.
  assumption.
  destruct x.
  inversion X.
  apply defl_updl.
  intros.
  rewrite <- H1.
  rewrite H0.
  apply phpdef_comm.
  apply phpdef_locked_lock.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  unfold defl in DEFL.
  apply DEFL with id id0.
  omega.
  assumption.
  assumption.
  apply phpdef_comm.
  assumption.
  exists wt, ot, ct.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  intros.
  apply phpdef_pair.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply DEFLb.
  apply in_map_iff.
  exists x12.
  inversion EQx.
  tauto.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ0,IN0)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ0.
  inversion X.
  rewrite H0.
  apply phpdef_locked_lock.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply DEFLb.
  apply in_map_iff.
  exists x12.
  inversion EQx.
  tauto.
  apply phpdef_comm.
  assumption.
  exists wt, ot, ct.
  assumption.
  rewrite <- EQ0.
  apply DEFLb.
  apply in_map.
  assumption.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ0,IN0)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ0.
  inversion X.
  rewrite H0.
  apply phpdef_locked_lock.
  assumption.
  exists wt, ot, ct.
  assumption.
  rewrite <- EQ0.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  unfold defl in DEFL.
  apply DEFL with id (snd x1).
  omega.
  assumption.
  apply in_map_iff.
  exists x1.
  inversion EQ0.
  tauto.
  rewrite phplus_comm.
  rewrite phplus_emp.
  apply in_map_iff.
  exists x.
  split.
  tauto.
  apply in_updl_eq.
  exists (fst x12).
  inversion EQx.
  destruct x12.
  simpl.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
Qed.

Lemma eq_heap_Wait A m:
  forall (l: list (A * Z)) id z p1 p2 x z' b
          (EXT: forall z p, exists x2, m (x2, z) = p)
          (NODUP: NoDup (map snd l))
          (PHPD: phplusdef p1 p2)
          (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
          (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
          (IN: In (phplus p1 p2,id) (map (fun x => (m x, snd x)) l))
          (P1z: exists wt1 ot1 ct1, p1 z = Some (Locked wt1 ot1 ct1) \/ p1 z = Some (Ulock wt1 ot1 ct1))
          (X: m (x,id) = upd p1 z (Some Lock))
          (NEQ: z <> z'),
    fold_left phplus (map m (updl l id (x,id))) (phplus b p2) z' = fold_left phplus (map m l) b z'.
Proof.
  intros.
  specialize EXT with id (emp knowledge).
  destruct EXT as (empx, memp).

  assert (phpdefp2up1: phplusdef p2 (upd p1 z (Some Lock))).
  {
  apply phpdef_comm.
  apply phpdef_locked_lock.
  assumption.
  assumption.
  }

  assert (INp1p2: In (phplus p1 p2) (map m l)).
  {
  apply in_map_iff.
  apply in_map_iff in IN.
  destruct IN as (x0,(EQx0,INx0)).
  exists x0.
  inversion EQx0.
  tauto.
  }

  assert (phpdefp1b: phplusdef p1 b).
  {
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply DEFLb.
  assumption.
  apply phpdef_comm.
  assumption.
  }

  assert (phpdefp2b: phplusdef p2 b).
  {
  apply phpdef_assoc_mon with p1.
  assumption.
  apply DEFLb.
  assumption.
  }

  assert (phpdefup1fold: phplusdef (upd p1 z (Some Lock)) (fold_left phplus (map m (updl l id (empx, id))) b)).
  {
  apply phpdef_comm.
  apply phpdef_fold.
  apply NoDup_updl.
  assumption.
  apply defl_updl.
  intros.
  rewrite memp.
  apply phpdef_emp.
  assumption.
  intros.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x0,(EQ0,IN0)).
  destruct (Z.eq_dec (snd x0) id).
  rewrite <- EQ0.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  apply DEFLb.
  apply in_map_iff.
  exists x0.
  tauto.
  intros.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x0,(EQ0,IN0)).
  destruct (Z.eq_dec (snd x0) id).
  rewrite <- EQ0.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  apply phpdef_comm.
  apply phpdef_locked_lock.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  unfold defl in DEFL.
  destruct x0.
  simpl in n.
  apply DEFL with id z0.
  omega.
  assumption.
  apply in_map_iff.
  exists (a,z0).
  inversion EQ0.
  tauto.
  apply phpdef_comm.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_locked_lock.
  assumption.
  assumption.
  }

  assert (phpdefp0b: forall p0 : pheap, In p0 (map m (updl l id (empx, id))) -> phplusdef p0 b).
  {
  intros.
  unfold updl in H.
  rewrite map_map in H.
  apply in_map_iff in H.
  destruct H as (x0,(EQ0,IN0)).
  destruct (Z.eq_dec (snd x0) id).
  rewrite <- EQ0.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  apply DEFLb.
  apply in_map_iff.
  exists x0.
  tauto.
  }

  assert (phpdefp0p2: forall p0 : pheap, In p0 (map m (updl l id (empx, id))) -> phplusdef p0 p2).
  {
  intros.
  unfold updl in H.
  rewrite map_map in H.
  apply in_map_iff in H.
  destruct H as (x0,(EQ0,IN0)).
  destruct (Z.eq_dec (snd x0) id).
  rewrite <- EQ0.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  unfold defl in DEFL.
  destruct x0.
  simpl in n.
  apply DEFL with id z0.
  omega.
  assumption.
  apply in_map_iff.
  exists (a,z0).
  inversion EQ0.
  tauto.
  }

  assert (phpdefp2fold: phplusdef p2 (fold_left phplus (map m (updl l id (empx, id))) b)).
  {
  apply phpdef_comm.
  apply phpdef_fold.
  apply NoDup_updl.
  assumption.
  apply defl_updl.
  intros.
  rewrite memp.
  apply phpdef_emp.
  assumption.
  assumption.
  assumption.
  apply phpdef_comm.
  assumption.
  }

  assert (deflu: defl phplusdef (map (fun x0 : A * Z => (m x0, snd x0)) (updl l id (x, id)))).
  {
  apply defl_updl.
  intros.
  rewrite X.
  apply phpdef_comm.
  apply phpdef_locked_lock.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  unfold defl in DEFL.
  apply DEFL with id id0.
  omega.
  assumption.
  assumption.
  apply phpdef_comm.
  assumption.
  assumption.
  assumption.
  }

  rewrite phplus_comm.
  rewrite fold_left_f_m_def with (def:=phplusdef).
  {
  erewrite fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge)
    (x2:=upd p1 z (Some Lock))(id:=id)(x:=empx).
  {
  rewrite updl_updl.
  replace (fold_left phplus (map m l) b) with 
    (phplus (phplus p1 p2) (fold_left phplus (map m (updl l id (empx,id))) b)).
  {
  rewrite <- phplus_assoc.
  apply phplus_mon.
  rewrite phplus_comm.
  unfold upd.
  unfold phplus.
  destruct (Z.eq_dec z' z).
  omega.
  reflexivity.
  apply phpdef_comm.
  apply phpdef_locked_lock.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  symmetry.
  {
  apply fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge).
  apply can_phpdef.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  rewrite phplus_comm.
  rewrite phplus_emp.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  }
  }
  apply can_phpdef.
  apply NoDup_updl.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  intros.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ1.
  rewrite X.
  apply phpdef_locked_lock.
  assumption.
  assumption.
  apply DEFLb.
  apply in_map_iff.
  exists x1.
  tauto.
  rewrite phplus_comm.
  rewrite phplus_emp.
  apply in_map_iff.
  exists (x,id).
  rewrite X.
  split.
  tauto.
  apply in_updl_eq.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQx1,INx1)).
  destruct x1.
  exists a.
  inversion EQx1.
  rewrite <- H1.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  }
  apply can_phpdef.
  apply NoDup_updl.
  assumption.
  assumption.
  assumption.
  intros.
  split.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ0,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ0.
  rewrite X.
  apply phpdef_locked_lock.
  assumption.
  assumption.
  destruct x1.
  simpl in n.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  unfold defl in DEFL.
  apply DEFL with id z0.
  omega.
  assumption.
  apply in_map_iff.
  exists (a,z0).
  inversion EQ0.
  tauto.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ0,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ0.
  rewrite X.
  apply phpdef_locked_lock.
  assumption.
  assumption.
  destruct x1.
  simpl in n.
  apply DEFLb.
  apply in_map_iff.
  exists (a, z0).
  inversion EQ0.
  tauto.
  apply phpdef_comm.
  assumption.
Qed.

Lemma boundph_Wait A m:
   forall (l: list (A * Z)) id z p1 p2 x b
          (EXT: forall z p, exists x2, m (x2, z) = p)
          (NODUP: NoDup (map snd l))
          (PHPD: phplusdef p1 p2)
          (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
          (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
          (IN: In (phplus p1 p2,id) (map (fun x => (m x, snd x)) l))
          (P1z: exists wt ot ct, p1 z = Some (Locked wt ot ct) \/ p1 z = Some (Ulock wt ot ct))
          (X: (m x, snd x) = (upd p1 z (Some Lock), id))
          (BP: boundph (fold_left phplus (map m l) b)),
     boundph (fold_left phplus (map m (updl l id x)) (phplus b p2)).
Proof.
  intros.
  assert (INp1p2: In (phplus p1 p2) (map m l)).
  {
  apply in_map_iff.
  apply in_map_iff in IN.
  destruct IN as (x0,(EQx0,INx0)).
  exists x0.
  inversion EQx0.
  tauto.
  }

  unfold boundph.
  intros.
  destruct x.
  inversion X.
  rewrite H2 in *.
  destruct (Z.eq_dec z x0).
  rewrite <- e in *.

  assert (CO: fold_left phplus (map m (updl l id (a, id))) (phplus b p2) z = Some Lock \/
    exists wt ot ct, fold_left phplus (map m (updl l id (a, id))) (phplus b p2) z = Some (Locked wt ot ct)).
  {
  apply phplus_fold_lock.
  assumption.
  apply NoDup_updl.
  assumption.
  apply defl_updl.
  intros.
  rewrite H1.
  apply phpdef_comm.
  apply phpdef_locked_lock.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  unfold defl in DEFL.
  apply DEFL with id id0.
  omega.
  assumption.
  assumption.
  apply phpdef_comm.
  assumption.
  assumption.
  assumption.
  intros.
  apply phpdef_pair.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply DEFLb.
  assumption.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ1.
  rewrite H1.
  apply phpdef_locked_lock.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply DEFLb.
  assumption.
  apply phpdef_comm.
  assumption.
  assumption.
  apply DEFLb.
  apply in_map_iff.
  exists x1.
  tauto.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ1.
  rewrite H1.
  apply phpdef_locked_lock.
  assumption.
  assumption.
  destruct x1.
  simpl in n.
  unfold defl in DEFL.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply DEFL with id z2.
  omega.
  assumption.
  apply in_map_iff.
  exists (a0,z2).
  inversion EQ1.
  tauto.
  right.
  exists (upd p1 z (Some Lock)).
  exists.
  apply in_map_iff.
  exists (a,id).
  split.
  assumption.
  apply in_updl_eq.
  apply in_map_iff in IN.
  destruct IN as (x,(EQ,IN)).
  destruct x.
  exists a0.
  inversion EQ.
  rewrite <- H4.
  tauto.
  unfold upd.
  rewrite eqz.
  reflexivity.
  }

  destruct CO as [CO|CO].
  rewrite H in CO.
  inversion CO.
  destruct CO as (wt,(ot,(ct,CO))).
  rewrite H in CO.
  inversion CO.

  rewrite eq_heap_Wait with (z:=z) (p1:=p1) in H.
  unfold boundph in BP.
  apply BP with x0 z0.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma phtoh_Wait A m:
   forall (l: list (A * Z)) id z p1 p2 x b (h: heap)
          (EXT: forall z p, exists x2, m (x2, z) = p)
          (NODUP: NoDup (map snd l))
          (PHPD: phplusdef p1 p2)
          (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
          (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
          (IN: In (phplus p1 p2,id) (map (fun x => (m x, snd x)) l))
          (P1z: exists wt ot ct, p1 z = Some (Locked wt ot ct) \/ p1 z = Some (Ulock wt ot ct))
          (X: (m x, snd x) = (upd p1 z (Some Lock), id))
          (PHTOH: h = phtoh (fold_left phplus (map m l) b)),
     upd h z (Some 1%Z) = phtoh (fold_left phplus (map m (updl l id x)) (phplus b p2)).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold upd.
  unfold phtoh.
  destruct (Z.eq_dec x0 z).
  rewrite e in *.
  rewrite lock_Wait with (p1:=p1).
  reflexivity.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  destruct x.
  inversion X.
  rewrite H1 in *.
  rewrite eq_heap_Wait with (z:=z) (p1:=p1).
  rewrite PHTOH.
  reflexivity.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  omega.
Qed.

Lemma fold_phplus_Fork A m:
  forall (l: list (A * Z)) id p1 p2 x b
         (EXT: forall z p, exists x2, m (x2, z) = p)
         (PHPD: phplusdef p1 p2)
         (NODUP: NoDup (map snd l))
         (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
         (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
         (IN: In (phplus p1 p2,id) (map (fun x => (m x, snd x)) l))
         (X1: (m x, snd x) = (p1, id)),
  fold_left phplus (map m (updl l id x)) (phplus p2 b) =
  fold_left phplus (map m l) b.
Proof.
  intros.
  specialize EXT with id (emp knowledge).
  destruct EXT as (empx,memp).
  destruct x.
  inversion X1.
  rewrite H1 in *.

  assert (deflu: defl phplusdef (map (fun x : A * Z => (m x, snd x)) (updl l id (empx, id)))).
  {
  apply defl_updl.
  intros.
  rewrite memp.
  apply phpdef_emp.
  assumption.
  }

  assert (phpdefp0b: forall p0 : pheap, In p0 (map m (updl l id (empx, id))) -> phplusdef p0 b).
  {
  intros.
  unfold updl in H.
  rewrite map_map in H.
  apply in_map_iff in H.
  destruct H as (x1,(EQ0,IN0)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ0.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  apply DEFLb.
  apply in_map_iff.
  exists x1.
  tauto.
  }

  assert (phpdefp0p2: forall p0 : pheap, In p0 (map m (updl l id (empx, id))) -> phplusdef p0 p2).
  {
  intros.
  unfold updl in H.
  rewrite map_map in H.
  apply in_map_iff in H.
  destruct H as (x1,(EQ0,IN0)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ0.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply DEFL with id (snd x1).
  omega.
  assumption.
  apply in_map_iff.
  exists x1.
  inversion EQ0.
  tauto.
  }

  assert (phpdefp0p1: forall p0 : pheap, In p0 (map m (updl l id (empx, id))) -> phplusdef p0 p1).
  {
  intros.
  unfold updl in H.
  rewrite map_map in H.
  apply in_map_iff in H.
  destruct H as (x1,(EQ0,IN0)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ0.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply DEFL with id (snd x1).
  omega.
  assumption.
  apply in_map_iff.
  exists x1.
  inversion EQ0.
  tauto.
  apply phpdef_comm.
  assumption.
  }

  assert (INp1p2: In (phplus p1 p2) (map m l)).
  {
  apply in_map_iff.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  exists x.
  inversion EQx.
  tauto.
  }

  assert (phpdefbp2: phplusdef b p2).
  {
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply DEFLb.
  assumption.
  }

  assert (phpdefbp1: phplusdef b p1).
  {
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply DEFLb.
  assumption.
  apply phpdef_comm.
  assumption.
  }

  assert (updlua: defl phplusdef (map (fun x : A * Z => (m x, snd x)) (updl l id (a, id)))).
  {
  apply defl_updl.
  intros.
  rewrite H0.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  unfold defl in DEFL.
  apply DEFL with id id0.
  omega.
  assumption.
  assumption.
  apply phpdef_comm.
  assumption.
  assumption.
  }

  assert (phpdefxb: forall x : pheap, In x (map m (updl l id (a, id))) -> phplusdef x b).
  {
  intros.
  unfold updl in H.
  rewrite map_map in H.
  apply in_map_iff in H.
  destruct H as (x1,(EQ0,IN0)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ0.
  rewrite H0.
  apply phpdef_comm.
  assumption.
  apply DEFLb.
  apply in_map_iff.
  exists x1.
  inversion EQ0.
  tauto.
  }

  assert (phpdefxp2: forall x : pheap, In x (map m (updl l id (a, id))) -> phplusdef x p2).
  {
  intros.
  unfold updl in H.
  rewrite map_map in H.
  apply in_map_iff in H.
  destruct H as (x1,(EQ0,IN0)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ0.
  rewrite H0.
  assumption.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  unfold defl in DEFL.
  apply DEFL with id (snd x1).
  omega.
  assumption.
  apply in_map_iff.
  exists x1.
  inversion EQ0.
  tauto.
  }

  rewrite fold_left_f_m_def with (def:=phplusdef).
  {
  erewrite fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge)
    (x2:=p1)(id:=id)(x:=empx).
  {
  rewrite updl_updl.
  replace (fold_left phplus (map m l) b) with 
    (phplus (phplus p1 p2) (fold_left phplus (map m (updl l id (empx,id))) b)).
  {
  rewrite <- phplus_assoc.
  replace (phplus p1 p2) with (phplus p2 p1).
  reflexivity.
  apply phplus_comm.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  assumption.
  apply phpdef_comm.
  {
  apply phpdef_fold.
  apply NoDup_updl.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }
  apply phpdef_comm.
  apply phpdef_fold.
  apply NoDup_updl.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }

  symmetry.
  apply fold_left_move_m_eq with (def:=phplusdef)(x1:=emp knowledge).
  apply can_phpdef.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  assumption.
  assumption.
  }
  apply can_phpdef.
  apply NoDup_updl.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  rewrite phplus_comm.
  rewrite phplus_emp.
  apply in_map_iff.
  exists (a, id).
  inversion H0.
  split.
  tauto.
  apply in_updl_eq.
  apply in_map_iff in IN.
  destruct IN as (x,(EQx,INx)).
  destruct x.
  exists a0.
  inversion EQx.
  rewrite <- H4.
  tauto.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  }

  apply can_phpdef.
  apply NoDup_updl.
  assumption.
  assumption.
  apply phpdef_comm.
  assumption.
  intros.
  split.
  apply phpdefxp2.
  assumption.
  apply phpdefxb.
  assumption.
Qed.

Lemma fold_left_upd_NotifyAll A m (m': (A * Z) -> (A * Z)):
  forall (l: list (A * Z)) id z p wt ot ct x b
         (EXT: forall z p, exists x2, m (x2, z) = p)
         (NODUP: NoDup (map snd l))
         (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
         (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
         (IN: In (p,id) (map (fun x => (m x, snd x)) l))
         (P1z: exists wt1 ot1 ct1, p z = Some (Locked wt1 ot1 ct1))
         (X1: (m x, snd x) = (upd p z (Some (Locked wt ot ct)), id))
         (M': forall x, m x = m (m' x) /\ snd (m' x) = snd x),
     fold_left phplus (map m (updl (map m' l) id x)) b = 
       upd (fold_left phplus (map m l) b) z (Some (Locked wt ot ct)).
Proof.
  intros.
  rewrite eq_map.
  apply fold_left_upd_Notify_1 with (p:=p).
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.


Lemma eq_heap_Acquire A m:
  forall (l: list (A * Z)) id z z' p p1 p2 x h
         (EXT: forall z p, exists x2, m (x2, z) = p)
         (NODUP: NoDup (map snd l))
         (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
         (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 (phplus p1 p2))
         (PHPD: phplusdef p1 p2)
         (IN: In (p,id) (map (fun x => (m x, snd x)) l))
         (Pl : p z = Some Lock \/ (exists wt ot ct : bag, p z = Some (Locked wt ot ct)))
         (X: exists wt ot ct, m (x,id) = phplus (upd p z (Some (Locked wt ot ct))) p1)
         (hz': h z = Some 1%Z)
         (PH2H: h = phtoh (fold_left phplus (map m l) (phplus p1 p2)))
         (NEQ: z <> z'),
    fold_left phplus (map m (updl l id (x, id))) p2 z' = fold_left phplus (map m l) (phplus p1 p2) z'.
Proof.
  intros.
  destruct X as (wt,(ot,(ct,mxid))).
  assert (EXT2:=EXT).
  specialize EXT with id (emp knowledge).
  destruct EXT as (empx,memp).

  assert (Inp: In p (map m l)).
  {
  apply in_map_iff.
  apply in_map_iff in IN.
  destruct IN as (x0,(EQx0,INx0)).
  exists x0.
  inversion EQx0.
  tauto.
  }

  assert (phpdefpp12: phplusdef p (phplus p1 p2)).
  {
  apply DEFLb.
  assumption.
  }  

  assert (phpdefpp1pp2: phplusdef p p1 /\ phplusdef p p2).
  {
  apply phpdef_dist'.
  assumption.
  assumption.
  }

  assert (deflu: defl phplusdef (map (fun x0 : A * Z => (m x0, snd x0)) (updl l id (empx, id)))).
  {
  apply defl_updl.
  intros.
  rewrite memp.
  apply phpdef_emp.
  assumption.
  }

  assert (phpdefp0p2: forall x1, In x1 l -> phplusdef (m x1) p2).
  {
  intros.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply phpdef_comm.
  apply DEFLb.
  apply in_map.
  assumption.
  }

  assert (phpdefup0p2: forall p0 : pheap, In p0 (map m (updl l id (empx, id))) -> phplusdef p0 p2).
  {
  intros.
  unfold updl in H.
  rewrite map_map in H.
  apply in_map_iff in H.
  destruct H as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ1.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  rewrite <- EQ1.
  apply phpdefp0p2.
  assumption.
  }

  assert (phpdefp0p1: forall x1, In x1 l -> phplusdef (m x1) p1).
  {
  intros.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply phpdef_comm.
  apply DEFLb.
  apply in_map.
  assumption.
  apply phpdef_comm.
  assumption.
  }

  assert (phpdefup0p1: forall p0 : pheap, In p0 (map m (updl l id (empx, id))) -> phplusdef p0 p1).
  {
  intros.
  unfold updl in H.
  rewrite map_map in H.
  apply in_map_iff in H.
  destruct H as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ1.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  rewrite <- EQ1.
  apply phpdefp0p1.
  assumption.
  }

  assert (phpdefp1fold: phplusdef p1 (fold_left phplus (map m (updl l id (empx, id))) p2)).
  {
  apply phpdef_comm.
  apply phpdef_fold.
  apply NoDup_updl.
  assumption.
  assumption.
  assumption.
  assumption.
  apply phpdef_comm.
  assumption.
  }

  assert (phpdefup0p: forall p0 : pheap, In p0 (map m (updl l id (empx, id))) -> phplusdef p0 p).
  {
  intros.
  unfold updl in H.
  rewrite map_map in H.
  apply in_map_iff in H.
  destruct H as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ1.
  rewrite memp.
  apply phpdef_comm.
  apply phpdef_emp.
  rewrite <- EQ1.
  unfold defl in DEFL.
  apply DEFL with (snd x1) id.
  omega.
  apply in_map_iff.
  exists x1.
  inversion EQ1.
  tauto.
  assumption.
  }

  assert (phpdefpfold: phplusdef p (fold_left phplus (map m (updl l id (empx, id))) p2)).
  {
  apply phpdef_comm.
  apply phpdef_fold.
  apply NoDup_updl.
  assumption.
  assumption.
  assumption.
  assumption.
  apply phpdef_comm.
  tauto.
  }

  assert (p1p2N: phplus p1 p2 z = None \/ phplus p1 p2 z = Some Lock).
  {
  apply locked_fold_phtoheap with (m:=m) (l:=l) (id:=id) (p:=p) (b:=phplus p1 p2) (h:=h).
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  right.
  reflexivity.
  }

  assert (phpdefupp1: phplusdef (upd p z (Some (Locked wt ot ct))) p1).
  {
  apply phpdef_upd_locked.
  tauto.
  apply phplus_locked_mono in p1p2N.
  tauto.
  }

  assert (phpdefupp2: phplusdef (upd p z (Some (Locked wt ot ct))) p2).
  {
  apply phpdef_upd_locked.
  tauto.
  rewrite phplus_comm in p1p2N.
  apply phplus_locked_mono in p1p2N.
  tauto.
  assumption.
  }

  rewrite fold_left_f_m_def with (def:=phplusdef).
  erewrite fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge)
    (x2:=phplus (upd p z (Some (Locked wt ot ct))) p1)(id:=id)(x:=empx).
  rewrite updl_updl.
  replace (fold_left phplus (map m l) p2) with
    (phplus p (fold_left phplus (map m (updl l id (empx,id))) p2)).
  rewrite <- phplus_assoc.
  apply phplus_mon.
  replace (phplus p1 p) with (phplus p p1).
  unfold phplus.
  unfold upd.
  destruct (Z.eq_dec z' z).
  omega.
  reflexivity.
  apply phplus_comm.
  tauto.
  apply phpdef_comm.
  tauto.
  assumption.
  assumption.
  symmetry.
  apply fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge).
  apply can_phpdef.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  intros.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ1,IN1)).
  inversion EQ1.
  apply phpdefp0p2.
  assumption.
  rewrite phplus_comm.
  rewrite phplus_emp.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  apply can_phpdef.
  apply NoDup_updl.
  assumption.

  assert (deflux: defl phplusdef (map (fun x0 : A * Z => (m x0, snd x0)) (updl l id (x, id)))).
  {
  apply defl_updl.
  intros.

  assert (p0N: p0 z = None \/ p0 z = Some Lock).
  {
  apply locked_fold_phtoheap with (m:=m) (l:=l) (id:=id) (p:=p) (b:=phplus p1 p2) (h:=h).
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  left.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ1,IN1)).
  apply in_map_iff.
  exists x1.
  inversion EQ1.
  tauto.
  }

  rewrite mxid.
  apply phpdef_pair.
  assumption.
  apply phpdef_comm.
  apply phpdef_upd_locked.
  unfold defl in DEFL.
  apply DEFL with id id0.
  assumption.
  assumption.
  assumption.
  tauto.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply phpdef_comm.
  apply DEFLb.
  apply in_map_iff in IN0.
  destruct IN0 as (x1, (EQ1,IN1)).
  apply in_map_iff.
  exists x1.
  inversion EQ1.
  tauto.
  apply phpdef_comm.
  tauto.
  assumption.
  }

  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  intros.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ1.
  rewrite mxid.
  apply phpdef_pair'.
  assumption.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply phpdef_comm.
  apply DEFLb.
  apply in_map_iff.
  exists x1.
  inversion EQ1.
  tauto.

  rewrite phplus_comm.
  rewrite phplus_emp.
  apply in_map_iff.
  exists (x, id).
  split.
  rewrite mxid.
  reflexivity.
  apply in_updl_eq.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ1,IN1)).
  destruct x1.
  exists a.
  simpl in EQ1.
  inversion EQ1.
  rewrite <- H1.
  tauto.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  apply can_phpdef.
  assumption.
  assumption.
  assumption.
  intros.
  split.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply phpdef_comm.
  apply DEFLb.
  apply in_map_iff in IN0.
  destruct IN0 as (x1, (EQ1,IN1)).
  apply in_map_iff.
  exists x1.
  inversion EQ1.
  tauto.
  apply phpdef_comm.
  tauto.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply phpdef_comm.
  apply DEFLb.
  assumption.
Qed.

Lemma locked_Acquire A m:
   forall (l: list (A * Z)) x p p1 p2 z id wt ot ct h
          (EXT: forall z p, exists x2, m (x2, z) = p)
          (NODUP: NoDup (map snd l))
          (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
          (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 (phplus p1 p2))
          (PHPD: phplusdef p1 p2)
          (IN: In (p,id) (map (fun x => (m x, snd x)) l))
          (X: m (x,id) = phplus (upd p z (Some (Locked wt ot ct))) p1)
          (Pl : p z = Some Lock \/ (exists wt ot ct : bag, p z = Some (Locked wt ot ct)))
          (hz': h z = Some 1%Z)
          (PH2H: h = phtoh (fold_left phplus (map m l) (phplus p1 p2))),
    fold_left phplus (map m (updl l id (x,id))) p2 z = Some (Locked wt ot ct).
Proof.
  intros.
  assert (p'z: forall p' (IN: In p' (map m l) \/ p' = phplus p1 p2), p' z = None \/ p' z = Some Lock).
  {
  apply locked_fold_phtoheap with id p h.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  }

  assert (p1z: p1 z = None \/ p1 z = Some Lock).
  {
  apply phplus_locked_mono with p2.
  apply p'z.
  right.
  reflexivity.
  }

  assert (p2z: p2 z = None \/ p2 z = Some Lock).
  {
  apply phplus_locked_mono with p1.
  apply p'z.
  right.
  apply phplus_comm.
  apply phpdef_comm.
  assumption.
  }

  assert (INp: In p (map m l)).
  {
  apply in_map_iff.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQx,INx)).
  exists x1.
  inversion EQx.
  tauto.
  }

  assert (phpdefpp12: phplusdef p (phplus p1 p2)).
  {
  apply DEFLb.
  assumption.
  }

  assert (phpdefpp1pp2: phplusdef p p1 /\ phplusdef p p2).
  {
  apply phpdef_dist';
  assumption.
  }

  specialize EXT with id (emp knowledge).
  destruct EXT as (empx,memp).

  erewrite fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge)
    (x2:=phplus (upd p z (Some (Locked wt ot ct))) p1)(id:=id)(x:=empx).
  unfold phplus.
  unfold upd.
  rewrite eqz.
  reflexivity.
  apply can_phpdef.
  apply NoDup_updl.
  assumption.
  apply defl_updl.
  intros.
  rewrite X.
  apply phpdef_pair.
  apply phpdef_upd_locked;
  tauto.
  apply phpdef_comm.
  apply phpdef_upd_locked.
  unfold defl in DEFL.
  apply DEFL with id id0;
  assumption.
  assert (G: p0 z = None \/  p0 z = Some Lock).
  apply p'z.
  left.
  apply in_map_iff.
  apply in_map_iff in IN0.
  destruct IN0 as (x0,(EQ0,IN0)).
  exists x0.
  inversion EQ0.
  tauto.
  tauto.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p2.
  apply phpdef_comm.
  assumption.
  rewrite phplus_comm.
  apply phpdef_comm.
  apply DEFLb.
  apply in_map_iff.
  apply in_map_iff in IN0.
  destruct IN0 as (x0,(EQ0,IN0)).
  exists x0.
  inversion EQ0.
  tauto.
  apply phpdef_comm.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  intros.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ1.
  rewrite X.
  apply phpdef_pair'.
  apply phpdef_upd_locked;
  tauto.
  apply phpdef_upd_locked;
  tauto.
  assumption.
  apply phpdef_comm.
  apply phpdef_assoc_mon with p1.
  assumption.
  apply phpdef_comm.
  apply DEFLb.
  apply in_map_iff.
  exists x1.
  tauto.
  rewrite phplus_comm.
  rewrite phplus_emp.
  apply in_map_iff.
  exists (x,id).
  rewrite X.
  split.
  reflexivity.
  apply in_updl_eq.
  apply in_map_iff in IN.
  destruct IN as (x1,(EQ1,IN1)).
  destruct x1.
  exists a.
  simpl in EQ1.
  inversion EQ1.
  rewrite <- H1.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
Qed.

Lemma boundph_Acquire A m:
   forall (l: list (A * Z)) x p p1 p2 z id h
          (EXT: forall z p, exists x2, m (x2, z) = p)
          (NODUP: NoDup (map snd l))
          (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
          (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 (phplus p1 p2))
          (PHPD: phplusdef p1 p2)
          (IN: In (p,id) (map (fun x => (m x, snd x)) l))
          (X: exists wt ot ct, m (x,id) = phplus (upd p z (Some (Locked wt ot ct))) p1)
          (Pl : p z = Some Lock \/ (exists wt ot ct : bag, p z = Some (Locked wt ot ct)))
          (hz': h z = Some 1%Z)
          (PH2H: h = phtoh (fold_left phplus (map m l) (phplus p1 p2)))
          (BPT: boundph (fold_left phplus (map m l) (phplus p1 p2))),
    boundph (fold_left phplus (map m (updl l id (x,id))) p2).
Proof.
  intros.
  unfold boundph.
  intros.
  destruct X as (wt,(ot,(ct,X))).
  destruct (Z.eq_dec x0 z).
  rewrite e in *.
  rewrite locked_Acquire with (p:=p) (p1:=p1) (wt:=wt) (ot:=ot) (ct:=ct) (h:=h) in H.
  inversion H.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  rewrite eq_heap_Acquire with (z:=z) (p:=p) (p1:=p1) (h:=h) in H.
  unfold boundph in BPT.
  apply BPT with x0 z0.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  exists wt, ot, ct.
  assumption.
  assumption.
  assumption.
  omega.
Qed.

Lemma locked_disch A m:
   forall (l: list (A * Z)) x p b z id wt ot ct
          (EXT: forall z p, exists x2, m (x2, z) = p)
          (NODUP: NoDup (map snd l))
          (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
          (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
          (IN: In (p,id) (map (fun x => (m x, snd x)) l))
          (pz: exists wt ot ct, p z = Some (Locked wt ot ct))
          (X: m (x,id) = upd p z (Some (Locked wt ot ct))),
    fold_left phplus (map m (updl l id (x,id))) b z = Some (Locked wt ot ct).
Proof.
  intros.
  specialize EXT with id (emp knowledge).
  destruct EXT as (empx,memp).
  erewrite fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge)
    (x2:=upd p z (Some (Locked wt ot ct)))(id:=id)(x:=empx).
  unfold phplus.
  unfold upd.
  rewrite eqz.
  reflexivity.
  apply can_phpdef.
  apply NoDup_updl.
  assumption.
  apply defl_updl.
  intros.
  rewrite X.
  apply phpdef_comm.
  apply phpdef_locked.
  unfold defl in DEFL.
  apply DEFL with id id0;
  tauto.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  intros.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ1.
  rewrite X.
  apply phpdef_locked.
  apply DEFLb.
  apply in_map_iff.
  apply in_map_iff in IN.
  destruct IN as (x2,(EQ2,IN2)).
  exists x2.
  inversion EQ2.
  tauto.
  assumption.
  apply DEFLb.
  apply in_map_iff.
  exists x1.
  inversion EQ1.
  tauto.
  rewrite phplus_comm.
  rewrite phplus_emp.
  apply in_map_iff.
  exists (x,id).
  rewrite X.
  split.
  reflexivity.
  apply in_updl_eq.
  apply in_map_iff in IN.
  destruct IN as (x2,(EQ2,IN2)).
  destruct x2.
  exists a.
  simpl in EQ2.
  inversion EQ2.
  rewrite <- H1.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
Qed.

Lemma eq_heap_disch A m:
   forall (l: list (A * Z)) x p b z z' id
          (EXT: forall z p, exists x2, m (x2, z) = p)
          (NODUP: NoDup (map snd l))
          (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
          (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
          (IN: In (p,id) (map (fun x => (m x, snd x)) l))
          (pz: exists wt ot ct, p z = Some (Locked wt ot ct))
          (X: exists wt ot ct, m (x,id) = upd p z (Some (Locked wt ot ct)))
          (NEQ: z <> z'),
    fold_left phplus (map m (updl l id (x,id))) b z' = fold_left phplus (map m l) b z'.
Proof.
  intros.
  destruct X as (wt,(ot,(ct,X))).
  destruct pz as (wt1,(ot1,(ct1,pz))).
  specialize EXT with id (emp knowledge).
  destruct EXT as (empx,memp).
  erewrite fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge)
    (x2:=upd p z (Some (Locked wt ot ct)))(id:=id)(x:=empx).
  rewrite updl_updl.
  replace (fold_left phplus (map m l) b) with 
    (phplus p (fold_left phplus (map m (updl l id (empx,id))) b)).
  unfold phplus.
  unfold upd.
  destruct (Z.eq_dec z' z).
  omega.
  reflexivity.
  symmetry.
  apply fold_left_move_m_eq with (def:=phplusdef) (x1:=emp knowledge).
  apply can_phpdef.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
  assumption.
  assumption.
  apply can_phpdef.
  apply NoDup_updl.
  assumption.
  apply defl_updl.
  intros.
  rewrite X.
  apply phpdef_comm.
  apply phpdef_locked.
  unfold defl in DEFL.
  apply DEFL with id id0;
  tauto.
  exists wt1, ot1, ct1.
  assumption.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  intros.
  unfold updl in IN0.
  rewrite map_map in IN0.
  apply in_map_iff in IN0.
  destruct IN0 as (x1,(EQ1,IN1)).
  destruct (Z.eq_dec (snd x1) id).
  rewrite <- EQ1.
  rewrite X.
  apply phpdef_locked.
  apply DEFLb.
  apply in_map_iff.
  apply in_map_iff in IN.
  destruct IN as (x2,(EQ2,IN2)).
  exists x2.
  inversion EQ2.
  tauto.
  exists wt1, ot1, ct1.
  assumption.
  apply DEFLb.
  apply in_map_iff.
  exists x1.
  inversion EQ1.
  tauto.
  rewrite phplus_comm.
  rewrite phplus_emp.
  apply in_map_iff.
  exists (x,id).
  rewrite X.
  split.
  tauto.
  apply in_updl_eq.
  apply in_map_iff in IN.
  destruct IN as (x2,(EQ2,IN2)).
  destruct x2.
  exists a.
  simpl in EQ2.
  inversion EQ2.
  rewrite <- H1.
  assumption.
  apply phpdef_comm.
  apply phpdef_emp.
  assumption.
Qed.

Lemma boundph_disch A m:
   forall (l: list (A * Z)) x p b z id
          (EXT: forall z p, exists x2, m (x2, z) = p)
          (NODUP: NoDup (map snd l))
          (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
          (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
          (IN: In (p,id) (map (fun x => (m x, snd x)) l))
          (pz: exists wt ot ct, p z = Some (Locked wt ot ct))
          (X: exists wt ot ct, m (x,id) = upd p z (Some (Locked wt ot ct)))
          (BPT: boundph (fold_left phplus (map m l) b)),
    boundph (fold_left phplus (map m (updl l id (x,id))) b).
Proof.
  intros.
  unfold boundph.
  intros.
  destruct (Z.eq_dec x0 z).
  rewrite e in *.
  destruct X as (wt,(ot,(ct,X))).
  rewrite locked_disch with (p:=p)(wt:=wt)(ot:=ot)(ct:=ct) in H.
  inversion H.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  rewrite eq_heap_disch with (p:=p) (z:=z) in H.
  unfold boundph in BPT.
  apply BPT with x0 z0.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  omega.
Qed.

Definition uboundph (p: pheap) :=
  forall x f z, p x = Some (Cell f z) -> f <= 1.

Lemma uboundph_fold:
  forall l b 
         (BPE: forall p (IN: In p l), boundph p)
         (BPT: boundph (fold_left phplus l b)),
    uboundph b.
Proof.
  induction l.
  simpl.
  intros.
  unfold boundph in *.
  unfold uboundph.
  intros.
  apply BPT in H.
  tauto.
  simpl.
  intros.
  assert (UB: uboundph (phplus b a)).
  {
  apply IHl.
  intros.
  apply BPE.
  right.
  assumption.
  assumption.
  }
  assert (Ba: boundph a).
  {
  apply BPE.
  left.
  reflexivity.
  }
  unfold uboundph in *.
  unfold boundph in *.
  intros.
  specialize UB with (x:=x).
  specialize Ba with (x:=x).
  unfold phplus in UB.
  rewrite H in UB.
  destruct (a x).
  destruct k;
  try tauto.
  assert (G1: f + f0 <= 1).
  apply UB with z.
  reflexivity.
  assert (G2: 0 < f0 /\ f0 <= 1).
  apply Ba with z0.
  reflexivity.
  apply Qc_Le_mon1 with f0.
  tauto.
  tauto.
  apply UB with z.
  reflexivity.
  apply UB with z.
  reflexivity.
  apply UB with z.
  reflexivity.
  apply UB with z.
  reflexivity.
  apply UB with z.
  reflexivity.
Qed.

Definition lboundph (p: pheap) :=
  forall x f z, p x = Some (Cell f z) -> 0 < f.

Lemma lboundph_phplus:
  forall p1 p2
         (BP1: boundph p1)
         (BP2: boundph p2),
    lboundph (phplus p1 p2).
Proof.
  unfold lboundph.
  unfold boundph.
  unfold phplus.
  intros.
  specialize BP1 with (x:=x).
  specialize BP2 with (x:=x).
  destruct (p1 x).
  destruct k;
  try tauto.
  assert (G: 0 < f0 /\ f0 <= 1).
  {
  apply BP1 with z0.
  reflexivity.
  }
  destruct (p2 x).
  destruct k;
  inversion H;
  try tauto.
  assert (G2: 0 < f1 /\ f1 <= 1).
  {
  apply BP2 with z1.
  reflexivity.
  }
  apply Qc_Lt_plus.
  tauto.
  tauto.
  inversion H.
  rewrite <- H1.
  tauto.
  rewrite <- H1.
  tauto.
  rewrite <- H1.
  tauto.
  rewrite <- H1.
  tauto.
  inversion H.
  rewrite <- H1.
  tauto.
  inversion H.
  destruct (p2 x).
  destruct k;
  inversion H;
  try tauto.
  inversion H.
  inversion H.
  inversion H.
  apply BP2 in H.
  tauto.
Qed.

Lemma luboundph:
  forall p
         (LB: lboundph p)
         (UB: uboundph p),
    boundph p.
Proof.
  unfold lboundph.
  unfold uboundph.
  unfold boundph.
  intros.
  split.
  apply LB with x z.
  assumption.
  apply UB with x z.
  assumption.
Qed.

Lemma boundph_fold A m:
  forall (l: list (A * Z)) b p
         (NODUP: NoDup (map snd l))
         (DEFL: defl phplusdef (map (fun x => (m x, snd x)) l))
         (DEFLb: forall p0 (IN: In p0 (map m l)), phplusdef p0 b)
         (BPb: boundph b)
         (BPE: forall p (IN: In p (map m l)), boundph p)
         (BPT: boundph (fold_left phplus (map m l) b))
         (IN: In p (map m l)),
    boundph (phplus b p).
Proof.
  induction l.
  simpl.
  intros.
  contradiction.
  simpl.
  intros.
  assert (BP: boundph p).
  apply BPE.
  assumption.
  assert (LB: lboundph (phplus b p)).
  {
  apply lboundph_phplus.
  assumption.
  assumption.
  }
  destruct IN as [EQ|IN].
  rewrite EQ in *.

  assert (UB: uboundph (phplus b p)).
  {
  apply uboundph_fold with (map m l).
  intros.
  apply BPE.
  right.
  assumption.
  assumption.
  }

  apply luboundph.
  assumption.
  assumption.

  assert (UBba: uboundph (phplus b (m a))).
  {
  apply uboundph_fold with (map m l).
  intros.
  apply BPE.
  right.
  assumption.
  assumption.
  }

  assert (LBba: lboundph (phplus b (m a))).
  {
  apply lboundph_phplus.
  assumption.
  apply BPE.
  left.
  reflexivity.
  }

  assert (boundph (phplus (phplus b (m a)) p)).
  {
  apply IHl.
  inversion NODUP.
  assumption.
  {
  unfold defl in *.
  intros.
  apply DEFL with id1 id2.
  omega.
  right.
  assumption.
  right.
  assumption.
  }
  {
  intros.
  apply phpdef_pair.
  apply phpdef_comm.
  apply DEFLb.
  left.
  reflexivity.
  apply DEFLb.
  right.
  assumption.
  unfold defl in DEFL.
  apply in_map_iff in IN0.
  destruct IN0 as (x0,(EQ0,IN0)).
  destruct x0.
  inversion EQ0.
  apply DEFL with z (snd a).
  unfold not.
  intros.
  rewrite <- H0 in NODUP.
  inversion NODUP.
  apply H3.
  apply in_map_iff.
  exists (a0, z).
  tauto.
  right.
  apply in_map_iff. 
  exists (a0, z).
  tauto.
  left.
  reflexivity.
  }
  apply luboundph.
  assumption.
  assumption.
  intros.
  apply BPE.
  right.
  assumption.
  assumption.
  assumption.
  }

  assert (phpdefab: phplusdef (m a) b).
  {
  apply DEFLb.
  left.
  reflexivity.
  }
  
  assert (phpdefap: phplusdef (m a) p).
  {
  unfold defl in DEFL.
  apply in_map_iff in IN.
  destruct IN as (x0,(EQ0,IN0)).
  destruct x0.
  inversion EQ0.
  apply DEFL with (snd a) z.
  unfold not.
  intros.
  rewrite H1 in NODUP.
  inversion NODUP.
  apply H4.
  apply in_map_iff.
  exists (a0, z).
  tauto.
  left.
  reflexivity.
  right.
  apply in_map_iff.
  exists (a0, z).
  tauto.
  }

  assert (phpdefba: phplusdef b p).
  {
  apply phpdef_comm.
  apply DEFLb.
  right.
  assumption.
  }

  apply boundph_mon with (m a).
  assumption.
  assumption.
  apply BPE.
  left.
  reflexivity.
  apply bph_comm.
  {
  apply phpdef_pair.
  assumption.
  assumption.
  assumption.
  }
  apply bph_assoc.
  assumption.
  assumption.
  assumption.
  replace (phplus (m a) b) with (phplus b (m a)).
  assumption.
  apply phplus_comm.
  apply phpdef_comm.
  assumption.
Qed.
