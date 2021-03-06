Require Import ZArith.
Require Import Qcanon.
Require Import QArith_base.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.

(** # <font size="5"><b> Injectivity </b></font> # *)

Definition inj A B (f: A -> B) (a b: A) :=
  f a = f b -> a = b.

(** # <font size="5"><b> upd </b></font> # *)

Definition upd A B (eq_dec: forall (x y: A), {x = y} + {x <> y}) (f: A -> B) x y a := if (eq_dec a x) then y else f a.

Definition ifb A (cond: {A} + {~A}) : bool :=
  if cond then true else false.

Ltac inn_match_ trm :=
  match trm with
   | match ?a with _ => _ end => inn_match_ a
   | if ?a then ?b else ?c => inn_match_ a
   | ifb ?a => inn_match_ a
   | _ => trm
  end.

Ltac dstr_ := simpl; intros;
  match goal with
    | _: ?a <> ?a |- _ => contradiction
    | H: None = Some _ |- _ => inversion H
    | H: Some _ = Some _ |- _ => inversion H; clear H
    | H: ?a = ?b |- _ => rewrite H in *; clear H
    | |- Some _ <> None => unfold not; intros CO_SN; inversion CO_SN
    | [ |- context[upd ?x ?y ?z] ] => unfold upd
    | [ |- context[if ?x then _ else _] ] => let x' := inn_match_ x in destruct x'
    | [ |- context[ifb ?x] ] => destruct x
    | [H: context[if ?x then _ else _] |- _ ] => let x' := inn_match_ x in destruct x'
    | [H: context[ifb ?x] |- _ ] => let x' := inn_match_ x in destruct x'
    | [ |- context[match ?x with _ => _ end] ] => let x' := inn_match_ x in destruct x'
    | [_: context[match ?x with _ => _ end] |- _ ] => let x' := inn_match_ x in destruct x'
  end; trivial; try omega; try contradiction.

Lemma upd_eq A:
  forall (p: Z -> A) z v
         (Pz: p z = v),
    upd Z.eq_dec p z v = p.
Proof.
  intros; apply functional_extensionality; repeat dstr_.
Qed.

Lemma upd_upd A B (eq_dec: forall (x y: A), {x = y} + {x <> y}) (p: A -> B):
  forall x v v',
    upd eq_dec (upd eq_dec p x v) x v' = upd eq_dec p x v'.
Proof.
  intros.
  apply functional_extensionality.
  repeat dstr_.
Qed.


(** # <font size="5"><b> lift </b></font> # *)

Definition lift A (default: A) (a: option A): A :=
  match a with
    | None => default
    | Some a => a
  end.

Definition lift' A (a1 a2: option A): option A :=
  match a1 with
    | None => a2
    | Some a => Some a
  end.

Definition opZ_eq_dec (o1 o2: option Z) : {o1 = o2} + {o1 <> o2}.
Proof.
  repeat decide equality.
Qed.

Definition opQc_eq_dec (o1 o2: option Qc) : {o1 = o2} + {o1 <> o2}.
Proof.
  repeat decide equality.
  apply Qc_eq_dec.
Qed.

Definition exc_op A (o1 o2: option A) :=
  o1 = None \/ o2 = None.

Definition leb_o (x: Z) (y: option Z) :=
  match y with
    | None => false
    | Some y' => Z.leb x y'
  end.

Lemma lift_comm A:
  forall (o1 o2: option A)
         (EXC: exc_op o1 o2),
    lift' o1 o2 = lift' o2 o1.
Proof.
  unfold lift'.
  unfold exc_op.
  intros.
  repeat dstr_.
  destruct EXC as [E|E];
  inversion E.
Qed.

Lemma lift_assoc A:
  forall (o1 o2 o3: option A),
    lift' (lift' o1 o2) o3 = lift' o1 (lift' o2 o3).
Proof.
  unfold lift'.
  unfold exc_op.
  intros.
  repeat dstr_.
Qed.

Lemma exc_dist A:
  forall (o1 o2 o3: option A)
         (EX13: exc_op o1 o3)
         (EX23: exc_op o2 o3),
  exc_op (lift' o1 o2) o3.
Proof.
  unfold exc_op.
  unfold lift'.
  intros.
  repeat dstr_.
Qed.

Lemma neqb_neq:
  forall x y (NEQ: (x =? y)%Z = false),
    x <> y.
Proof.
  intros.
  unfold not.
  intros EQ.
  rewrite EQ in NEQ.
  assert (CO: (y =? y)%Z = true).
  - apply Z.eqb_eq; reflexivity.
  - rewrite NEQ in CO; inversion CO.
Qed.

Lemma eqz A (a a': A) z:
  (if Z.eq_dec z z then a else a') = a.
Proof.
  destruct (Z.eq_dec z z).
  reflexivity.
  contradiction.
Qed.

Lemma neqz A (a a': A) z z':
  z <> z' -> (if Z.eq_dec z z' then a else a') = a'.
Proof.
  destruct (Z.eq_dec z z').
  intros.
  omega.
  reflexivity.
Qed.

Lemma neq_symm A:
  forall (x y:A), x <> y -> y <> x.
Proof.
  intros. auto.
Qed.

Lemma Z_leb_falseL:
  forall a b (LEB: (b <=? a)%Z = false),
    Z.lt a b.
Proof.
  intros; unfold Z.leb in LEB.
  destruct (b ?= a)%Z eqn:ba; inversion LEB.
  apply Zcompare_Gt_Lt_antisym in ba; rewrite Z.compare_lt_iff in ba; assumption.
Qed.

Lemma nat_leb_falseL:
  forall b a (LEB: (b <=? a)%nat = false),
    lt a b.
Proof.
  induction b; intros; inversion LEB.
  destruct a; try omega.
  assert (a<b)%nat.
  - apply IHb; assumption.
  - omega.
Qed.

Lemma Z_ltb_falseL:
  forall a b (LEB: (b <? a)%Z = false),
    Z.le a b.
Proof.
  intros; unfold Z.ltb in LEB.
  destruct (b ?= a)%Z eqn:ba; inversion LEB.
  apply Z.compare_eq_iff in ba.
  rewrite ba.
  omega.
  simpl in *.
  assert (b>a)%Z.
  assumption.
  omega.
Qed.

Lemma some_none A:
  forall (a: A), Some a <> None.
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

(** # <font size="5"><b> filterb </b></font> # *)

Definition filterb (L: Z -> option Z) (l: Z) (b: Z -> nat) :=
  fun x => match (L x) with
            | None => O
            | Some lx => if Z.eq_dec x l then O else if Z.eq_dec lx l then b x else O
           end.

(** # <font size="5"><b> comm_assoc_neutral </b></font> # *)

Definition neutral A (f: A -> A -> A) (n: A) :=
  forall x, f x n = x /\ f n x = x.

Definition can A (def: A -> A -> Prop) (f: A -> A -> A) :=
  (forall x y (DEF: def x y), f x y = f y x) /\
  (forall x y z (DEF1: def x y)(DEF2: def x z)(DEF3: def y z), f (f x y) z = f x (f y z)) /\
  (forall x y z (DEF1: def x y)(DEF2: def x z)(DEF3: def y z), def x (f y z)) /\
  (forall x y z (DEF1: def (f x y) z)(DEF2: def x y), def x z /\ def y z) /\
  (forall x y (DEF1: def x y), def y x) /\
  exists n, neutral f n.

(** # <font size="5"><b> Qc </b></font> # *)

Local Open Scope Qc.

Definition frac: Qc := 1/(1+1).

Lemma frac_bound:
  (0 < frac < 1)%Qc.
Proof.
  unfold Qclt. simpl. unfold Qlt. simpl. omega.
Qed.

Lemma qcplus_mono:
  forall q1 q2 q3, 
    q1 + q3 = q2 + q3 -> q1 = q2.
Proof.
  intros.
  assert (q1 + q3 + -q3 = q2 + q3 + -q3).
  - rewrite H; reflexivity.
  - rewrite <- Qcplus_assoc in H0.
    rewrite Qcplus_opp_r in H0.
    rewrite <- Qcplus_assoc in H0.
    rewrite Qcplus_opp_r in H0.
    rewrite Qcplus_0_r in H0.
    rewrite Qcplus_0_r in H0.
    assumption.
Qed.

Lemma qcplusgtzero 
  (q1 q2 : Qc) (q1gtzero: 0 < q1)(q2gtzero: 0 < q2):
    0 < q1 + q2.
Proof.
  assert ((0 < Qnum q1)%Z).
  - unfold "<" in q1gtzero.
    unfold Qlt in q1gtzero.
    simpl in q1gtzero.
    omega.
  - assert ((0<Qnum q2)%Z).
    + unfold "<" in q2gtzero.
      unfold Qlt in q2gtzero.
      simpl in q2gtzero.
      omega.
    + unfold "+".
      simpl.
      unfold "<".
      simpl.
      unfold Qlt.
      simpl.
      assert ((0<(Qnum q1 * QDen q2 + Qnum q2 * QDen q1))%Z).
      * unfold Z.lt.
        replace 0%Z with ((0%Z+0%Z)%Z).
        erewrite Zplus_compare_compat.
        reflexivity.
        replace 0%Z with ((Qnum q1*0%Z)%Z).
        erewrite <- Zmult_compare_compat_l.
        reflexivity.
        omega.
        omega.
        replace 0%Z with ((Qnum q2*0%Z)%Z).
        erewrite <- Zmult_compare_compat_l.
        reflexivity.
        omega.
        omega.
        reflexivity.
      * unfold Z.ggcd.
        destruct ((Qnum q1 * QDen q2 + Qnum q2 * QDen q1)%Z) eqn:QQ.
        -- inversion H1.
        -- destruct (Pos.ggcd p (Qden q1 * Qden q2)) eqn:AA.
           destruct p1.
           unfold snd.
           simpl.
           unfold Z.lt.
           destruct (Zpos (p1 * 1)) eqn:P1; inversion P1.
           reflexivity.
        -- inversion H1.
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

Lemma Qc_Lt_plus:
  forall (q1 q2: Qc)
         (LT1: 0 < q1)
         (LT2: 0 < q2),
    0 < q1 + q2.
Proof.
  intros.
  apply Qclt_trans with q2.
  tauto.
  rewrite Qclt_minus_iff.
  rewrite <- Qcplus_assoc.
  rewrite Qcplus_opp_r.
  rewrite Qcplus_0_r.
  tauto.
Qed.

Lemma Qc_Le_mon1:
  forall (q1 q2: Qc)
         (LE: q1 + q2 <= 1)
         (LT: 0 < q2),
    q1 <= 1.
Proof.
  intros.
  apply Qcle_trans with (q2 + q1).
  rewrite Qcle_minus_iff.
  rewrite <- Qcplus_assoc.
  rewrite Qcplus_opp_r.
  rewrite Qcplus_0_r.
  apply Qclt_le_weak.
  tauto.
  rewrite Qcplus_comm.
  tauto.
Qed.

Lemma Qc_Le_le_mon1:
  forall (q1 q2: Qc)
         (LE: q1 + q2 <= 1)
         (LT: 0 <= q2),
    q1 <= 1.
Proof.
  intros.
  apply Qcle_trans with (q2 + q1).
  rewrite Qcle_minus_iff.
  rewrite <- Qcplus_assoc.
  rewrite Qcplus_opp_r.
  rewrite Qcplus_0_r.
  assumption.
  rewrite Qcplus_comm.
  tauto.
Qed.


Lemma Qc_Le_mon2:
  forall (q1 q2: Qc)
         (LE: q1 + q2 <= 1)
         (LT: 0 < q1),
    q2 <= 1.
Proof.
  intros.
  apply Qcle_trans with (q1 + q2).
  rewrite Qcle_minus_iff.
  rewrite <- Qcplus_assoc.
  rewrite Qcplus_opp_r.
  rewrite Qcplus_0_r.
  apply Qclt_le_weak.
  tauto.
  tauto.
Qed.

Lemma Qc_Le_mon13:
  forall (q1 q2 q3: Qc)
         (LE: q1 + q2 + q3 <= 1)
         (LT: 0 < q2),
    q1 + q3 <= 1.
Proof.
  intros.
  apply Qcle_trans with (q2 + (q1 + q3)).
  rewrite Qcle_minus_iff.
  rewrite <- Qcplus_assoc.
  rewrite Qcplus_opp_r.
  rewrite Qcplus_0_r.
  apply Qclt_le_weak.
  tauto.
  rewrite Qcplus_assoc.
  replace (q2 + q1) with (q1 + q2).
  tauto.
  apply Qcplus_comm.
Qed.

Lemma Qc_Le_mon23:
  forall (q1 q2 q3: Qc)
         (LE: q1 + q2 + q3 <= 1)
         (LT: 0 < q1),
    q2 + q3 <= 1.
Proof.
  intros.
  apply Qcle_trans with (q1 + (q2 + q3)).
  rewrite Qcle_minus_iff.
  rewrite <- Qcplus_assoc.
  rewrite Qcplus_opp_r.
  rewrite Qcplus_0_r.
  apply Qclt_le_weak.
  tauto.
  rewrite Qcplus_assoc.
  replace (q2 + q1) with (q1 + q2).
  tauto.
  apply Qcplus_comm.
Qed.

Lemma Qc_Le_mon12:
  forall (q1 q2 q3: Qc)
         (LE: q1 + (q2 + q3) <= 1)
         (LT: 0 < q3),
    q1 + q2 <= 1.
Proof.
  intros.
  apply Qcle_trans with (q3 + (q1 + q2)).
  rewrite Qcle_minus_iff.
  rewrite <- Qcplus_assoc.
  rewrite Qcplus_opp_r.
  rewrite Qcplus_0_r.
  apply Qclt_le_weak.
  tauto.
  rewrite Qcplus_comm.
  rewrite <- Qcplus_assoc.
  tauto.
Qed.

Lemma Qc_Ltet_plus:
  forall (q1 q2: Qc)
         (LT1: 0 <= q1)
         (LT2: 0 < q2),
    0 < q1 + q2.
Proof.
  intros.
  rewrite Qcplus_comm.
  apply Qcle_lt_trans with q1.
  assumption.
  rewrite Qcplus_comm.
  apply qcpluslt.
  assumption.
Qed.

Lemma Qc_Lte_plus:
  forall (q1 q2: Qc)
         (LT1: 0 <= q1)
         (LT2: 0 < q2),
    0 <= q1 + q2.
Proof.
  intros.
  rewrite Qcplus_comm.
  apply Qcle_trans with q1.
  assumption.
  rewrite Qcle_minus_iff.
  rewrite <- Qcplus_assoc.
  rewrite Qcplus_opp_r.
  rewrite Qcplus_0_r.
  apply Qclt_le_weak.
  assumption.
Qed.

Definition full := 1%Qc.

Lemma full_bound: Qclt 0 full /\ Qcle full 1.
Proof.
  split.
  unfold Qclt.
  unfold QArith_base.Qlt.
  simpl.
  omega.
  unfold Qcle.
  unfold QArith_base.Qle.
  simpl.
  omega.
Qed.

Lemma frac2_bound:
  forall (f:Qc) (POS: 0 < f < 1), f/(1+1) < 1.
Proof.
  intros.
  apply Qclt_trans with f.
  replace (f / (1 + 1)) with (f * (1/(1 + 1))).
  replace f with (1*f) at 2.
  rewrite Qcmult_comm.
  apply Qcmult_lt_compat_r. destruct POS. assumption.
  unfold Qclt, Qlt. simpl. omega.
  apply Qcmult_1_l.
  reflexivity.
  destruct POS. assumption.
Qed.

Lemma frac2_pos:
  forall (f:Qc) (POS: 0 < f), 0 < f/(1+1).
Proof.
  intros.
  replace 0 with (0*1/(1+1)).
  replace (f / (1 + 1)) with (f * 1/(1 + 1)).
  apply Qcmult_lt_compat_r.
  unfold Qclt, Qlt. simpl. omega.
  rewrite Qcmult_0_l.
  rewrite Qcmult_1_r.
  assumption.
  replace (f * 1) with f.
  reflexivity.
  symmetry. apply Qcmult_1_r.
  apply Qcmult_0_l.
Qed.

Lemma frac2_plus:
  forall (f: Qc), f = f/(1+1) + f/(1+1).
Proof.
  intros.
  rewrite <- (Qcmult_1_l (f / (1 + 1))).
  rewrite <- Qcmult_plus_distr_l.
  rewrite Qcmult_div_r; trivial.
  unfold not.
  intros.
  unfold Qcplus in H.
  unfold Qplus in H.
  inversion H.
Qed.


(** # <font size="5"><b> Partially ordered sets </b></font> # *)

Definition transitive A R: Prop := forall x y z:A, R x y = true -> R y z = true -> R x z = true.
Definition asymmetric A R : Prop := forall x y:A, R x y = true -> R y x = true -> False.

Record order A (ltl: A -> A -> bool) : Prop :={
  ltl_trans : transitive ltl;
  ltl_asym : asymmetric ltl;
}.

Definition Qlt_bool x y :=
  andb (Qle_bool x y) (negb (Qeq_bool x y)).

Lemma order_Qc': order (fun x y : Qc => Qlt_bool x y).
Proof.
  unfold Qlt_bool.
  split.
  {
  unfold transitive.
  intros.
  apply andb_true_iff.
  apply andb_true_iff in H.
  apply andb_true_iff in H0.
  destruct H as (EQ1,EQ2).
  destruct H0 as (EQ3,EQ4).
  apply negb_true_iff in EQ2.
  apply negb_true_iff in EQ4.
  apply Qle_bool_iff in EQ1.
  apply Qle_bool_iff in EQ3.
  split.
  apply Qle_bool_iff.
  apply Qle_trans with y; assumption.
  apply negb_true_iff.
  apply Qeq_bool_neq in EQ4.
  destruct (Qeq_bool x z) eqn:QEQ.
  apply Qeq_bool_eq in QEQ.
  rewrite QEQ in *.
  exfalso. apply EQ4.
  apply Qle_antisym; assumption. reflexivity.
  }
  unfold asymmetric.
  intros.
  apply andb_true_iff in H.
  apply andb_true_iff in H0.
  destruct H as (EQ1,EQ2).
  destruct H0 as (EQ3,EQ4).
  apply negb_true_iff in EQ2.
  apply negb_true_iff in EQ4.
  apply Qle_bool_iff in EQ1.
  apply Qle_bool_iff in EQ3.
  apply Qeq_bool_neq in EQ4.
  apply EQ4.
  apply Qle_antisym; assumption.
Qed.

Lemma ltl_asym_false A ltl (ASYM: asymmetric (ltl: A -> A -> bool)):
  forall x y, ltl x y = true -> ltl y x = false.
Proof.
  intros.
  destruct (ltl y x) eqn:LTL.
  eapply ASYM in H. exfalso. apply H; assumption.
  reflexivity.
Qed.

Lemma ltl_asym_false' A ltl (ASYM: asymmetric (ltl: A -> A -> bool)):
  forall x, ltl x x = false.
Proof.
  intros.
  destruct (ltl x x) eqn:LTL.
  assert (tmp:=LTL).
  apply ASYM in tmp.
  apply tmp in LTL. contradiction.
  reflexivity.
Qed.

Lemma ltl_le A ltl (ASYM: asymmetric (ltl: A -> A -> bool)):
  forall x y (LEL: ltl x y = true \/ x = y),
    ltl y x = false.
Proof.
  intros.
  destruct LEL as [EQ1|EQ2].
  apply ltl_asym_false; try assumption.
  rewrite EQ2.
  apply ltl_asym_false'; try assumption.
Qed.

Lemma Qlt_bool_trans:
  forall x y z 
         (LT1: Qle_bool x y = true)
         (LT2: Qlt_bool y z = true),
    Qlt_bool x z = true.
Proof.
  unfold Qlt_bool.
  intros.
  apply andb_true_iff in LT2.
  destruct LT2 as (LT2,LT3).
  apply andb_true_iff.
  apply Qle_bool_iff in LT1.
  apply Qle_bool_iff in LT2.
  split.
  apply Qle_bool_iff.
  apply Qle_trans with y; try assumption.
  apply negb_true_iff.
  apply negb_true_iff in LT3.
  apply Qeq_bool_neq in LT3.
  destruct (Qeq_bool x z) eqn:EQ.
  apply Qeq_bool_eq in EQ.
  rewrite EQ in *.
  apply Qle_antisym in LT1. contradiction. assumption.
  reflexivity.
Qed.

