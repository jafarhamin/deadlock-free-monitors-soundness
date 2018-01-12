Require Import ZArith.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.

Definition lift A (default: A) (a: option A): A :=
  match a with
    | None => default
    | Some a => a
  end.

Definition opZ_eq_dec (o1 o2: option Z) : {o1 = o2} + {o1 <> o2}.
Proof.
  decide equality.
  apply Z_eq_dec.
Qed.

Definition ifb A (cond: {A} + {~A}) : bool :=
  if cond then true else false.

Lemma neqb_neq:
  forall x y (NEQ: (x =? y)%Z = false),
    x <> y.
Proof.
  intros.
  unfold not.
  intros.
  rewrite H in NEQ.
  assert (CO: (y =? y)%Z = true).
  apply Z.eqb_eq.
  reflexivity.
  rewrite NEQ in CO.
  inversion CO.
Qed.

Lemma eqz A (a a': A) z:
  (if Z.eq_dec z z then a else a') = a.
Proof.
  destruct (Z.eq_dec z z).
  reflexivity.
  contradiction.
Qed.

Lemma zeqb A (a a': A) z:
  (if (z =? z)%Z then a else a') = a.
Proof.
  destruct (z =? z)%Z eqn:zz.
  reflexivity.
  apply neqb_neq in zz.
  contradiction.
Qed.

Lemma Z_leb_falseL:
  forall a b (LEB: (b <=? a)%Z = false),
    Z.lt a b.
Proof.
  intros.
  unfold Z.leb in LEB.
  destruct (b ?= a)%Z eqn:ba.
  inversion LEB.
  inversion LEB.
  apply Zcompare_Gt_Lt_antisym in ba.
  rewrite Z.compare_lt_iff in ba.
  assumption.
Qed.

Lemma ifboneq:
  forall z,
    ifb (opZ_eq_dec None (Some z)) = false.
Proof.
  intros.
  destruct (opZ_eq_dec None (Some z)).
  inversion e.
  reflexivity.
Qed.

(** # <font size="5"><b> upd </b></font> # *)

Definition upd {A} (f: Z -> A) x y a := if Z.eq_dec a x then y else f a.

Lemma upd_eq A:
  forall (p: Z -> A) z v
         (Pz: p z = v),
    upd p z v = p.
Proof.
  unfold upd.
  intros.
  apply functional_extensionality.
  intros.
  destruct (Z.eq_dec x z).
  rewrite e.
  symmetry.
  assumption.
  reflexivity.
Qed.

(** # <font size="5"><b> filterb </b></font> # *)

Definition filterb (L: Z -> Z) (l: Z) (b: Z -> nat) :=
  fun x => if Z.eq_dec x l then 0 else if Z.eq_dec (L x) l then b x else 0.


(** # <font size="5"><b> COMM_ASSOC_NEUTRAL </b></font> # *)

Definition can A (def: A -> A -> Prop) (f: A -> A -> A) :=
  (forall x y (DEF: def x y), f x y = f y x) /\
  (forall x y z (DEF1: def x y)(DEF2: def x z)(DEF3: def y z), f (f x y) z = f x (f y z)) /\
  (forall x y z (DEF1: def x y)(DEF2: def x z)(DEF3: def y z), def x (f y z)) /\
  (forall x y z (DEF1: def (f x y) z)(DEF2: def x y), def x z /\ def y z) /\
  (forall x y (DEF1: def x y), def y x) /\
  exists n, forall x, f x n = x.


Definition neutral A (f: A -> A -> A) (n: A) :=
  forall x, f x n = x /\ f n x = x.

(** # <font size="5"><b> bag </b></font> # *)

Definition bag := Z -> nat.

Definition empb : (Z -> nat) :=
  fun _ => O.

Definition bagplus (d1 d2: bag) : bag :=
  fun v => (d1 v + d2 v)%nat.

Definition incb (b: bag) (z:Z) : bag :=
  upd b z (S (b z)).

Definition decb (b: bag) (z:Z) : bag :=
  upd b z ((b z) - 1)%nat.

Definition rstb (b: bag) (z:Z) : bag :=
  upd b z O.

(** # <font size="5"><b> bplus </b></font> # *)

Lemma bplus_comm:
  forall d1 d2,
    bagplus d1 d2 = bagplus d2 d1.
Proof.
  unfold bagplus.
  intros.
  apply functional_extensionality.
  intros.
  omega.
Qed.

Lemma bplus_assoc:
  forall (b1 b2 b3: bag),
    bagplus (bagplus b1 b2) b3 = bagplus b1 (bagplus b2 b3).
Proof.
  unfold bagplus.
  intros.
  apply functional_extensionality.
  intros.
  omega.
Qed.

Lemma bplus_emp:
  forall b,
    bagplus b empb = b.
Proof.
  unfold bagplus.
  intros.
  apply functional_extensionality.
  intros.
  unfold empb.
  omega.
Qed.

Definition bagdef (b1 b2: bag) := True.

Lemma canbag: can bagdef bagplus.
Proof.
  unfold can.
  split.
  intros.
  apply bplus_comm.
  split.
  intros.
  unfold bagplus.
  apply functional_extensionality.
  intros.
  omega.
  split.
  intros.
  trivial.
  split.
  intros.
  auto.
  split.
  intros.
  trivial.
  intros.
  exists empb.
  intros.
  unfold bagplus.
  unfold empb.
  apply functional_extensionality.
  intros.
  omega.
Qed.

(** # <font size="5"><b> Qc </b></font> # *)

Require Import Coq.QArith.Qcanon.
Require Import Coq.QArith.QArith_base.

Open Local Scope Qc.

Lemma qcplus_mono:
  forall q1 q2 q3, 
    q1 + q3 = q2 + q3 -> q1 = q2.
Proof.
  intros.
  assert (q1+q3+ -q3=q2+q3+ -q3).
  rewrite H.
  reflexivity.
  rewrite <- Qcplus_assoc in H0.
  rewrite Qcplus_opp_r in H0.
  rewrite <- Qcplus_assoc in H0.
  rewrite Qcplus_opp_r in H0.
  rewrite Qcplus_0_r in H0.
  rewrite Qcplus_0_r in H0.
  assumption.
Qed.



Lemma qcplusgtzero 
  (q1 q2 : Qc) (q1gtzero: 0<q1)(q2gtzero: 0<q2) :
    0 < q1 + q2.
Proof.
  assert ((0 < Qnum q1)%Z).
  unfold "<" in q1gtzero.
  unfold Qlt in q1gtzero.
  simpl in q1gtzero.
  omega.
  assert ((0<Qnum q2)%Z).
  unfold "<" in q2gtzero.
  unfold Qlt in q2gtzero.
  simpl in q2gtzero.
  omega.
  unfold "+".
  simpl.
  unfold "<".
  simpl.
  unfold Qlt.
  simpl.
  assert ((0<(Qnum q1 * ' Qden q2 + Qnum q2 * ' Qden q1))%Z).
  unfold Z.lt.
  replace 0%Z with ((0%Z+0%Z)%Z).
  rewrite Zplus_compare_compat with (n:=0%Z) (m:=(Qnum q1 * ' Qden q2)%Z) (p:=0%Z) (q:=(Qnum q2 * ' Qden q1)%Z) (r:=Lt).
  reflexivity.
  replace 0%Z with ((Qnum q1*0%Z)%Z).
  rewrite <- Zmult_compare_compat_l with (p:=Qnum q1).
  simpl.
  reflexivity.
  omega.
  omega.
  replace 0%Z with ((Qnum q2*0%Z)%Z).
  rewrite <- Zmult_compare_compat_l with (p:=Qnum q2).
  simpl.
  reflexivity.
  omega.
  omega.
  simpl.
  reflexivity.
  unfold Z.ggcd.
  destruct ((Qnum q1 * ' Qden q2 + Qnum q2 * ' Qden q1)%Z) eqn:QQ.
  inversion H1.
  destruct (Pos.ggcd p (Qden q1 * Qden q2)) eqn:AA.
  destruct p1.
  unfold snd.
  simpl.
  unfold Zlt.
  destruct (Zpos (p1 * 1)) eqn:P1.
  inversion P1.
  inversion P1.
  simpl.
  reflexivity.
  inversion P1.
  inversion H1.
Qed.

Lemma qcpluslt:
  forall q1 q2, 
    0 < q2 -> q1 < q1 + q2.
Proof.
intros.
rewrite Qcplus_comm.
rewrite Qclt_minus_iff.
rewrite <- Qcplus_assoc.
rewrite Qcplus_opp_r.
rewrite Qcplus_0_r.
assumption.
Qed.

Lemma qcplusle :
  forall q,
    1 + q <= 1 -> q <= 0.
Proof.
  intros.
  apply Qcle_not_lt in H.
  apply Qcnot_lt_le.
  unfold not in *.
  intros.
  apply H.
  rewrite Qcplus_comm.
  rewrite Qclt_minus_iff.
  rewrite <- Qcplus_assoc.
  rewrite Qcplus_opp_r.
  rewrite Qcplus_0_r.
  assumption.
Qed.

Lemma qcpluslelt:
  forall q,
    1 + q <= 1 -> 0 < q -> False.
Proof.
  intros.
  assert (Cont: 0<0).
  eapply Qclt_le_trans with q.
  assumption.
  apply qcplusle in H.
  assumption.
  inversion Cont.
Qed.

