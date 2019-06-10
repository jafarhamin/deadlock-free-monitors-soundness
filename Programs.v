Add LoadPath "proofs".

Require Import Coq.Bool.Bool.
Require Import ZArith.
Require Import List.
Require Import Util_Z.
Require Import Util_list.

Set Implicit Arguments.

(** # <font size="5"><b> Expressions </b></font> # *)

Inductive exp := 
  | Evar (x: Z)
  | Enum (num: Z)
  | Eneg (e: exp)
  | Eplus (e1: exp) (e2: exp).


(** # <font size="5"><b> Commands </b></font> # *)

Inductive cmd :=
  | Val (e: exp)
  | Cons (n: nat)
  | Lookup (e: exp)
  | Mutate (e1 e2: exp)
  | Fork (c: cmd)
  | Let (x: Z) (c1 c2: cmd)
  | If (c c1 c2: cmd)
  | While (c1 c2: cmd)
  | Newlock
  | Acquire (e: exp)
  | Release (e: exp)
  | Waiting4lock (l: exp)
  | Newcond
  | Wait (x l: exp)
  | Notify (x: exp)
  | NotifyAll (x: exp)
  | Waiting4cond (v l: exp)
  | WasWaiting4cond (v l: exp)
  | nop.

Definition exp_eq_dec (e1 e2: exp) : {e1 = e2} + {e1 <> e2}.
Proof.
  repeat decide equality.
Qed.

Definition cmd_eq_dec (c1 c2: cmd) : {c1 = c2} + {c1 <> c2}.
Proof.
  repeat decide equality.
Qed.

Inductive context :=
  | done
  | If' (c1: cmd) (c2: cmd) (tx: context)
  | Let' (x: Z) (c: cmd) (tx: context).


(** # <font size="5"><b> Semantics of Expressions </b></font> # *)

Definition heap := Z -> option Z.
Definition thrds := Z -> option (cmd * context).

Local Open Scope Z.

Fixpoint eval (e:exp) : Z :=
  match e with
    | Evar x => 0
    | Enum n => n
    | Eneg e => - (eval e)
    | Eplus e1 e2 => (eval e1) + (eval e2)
  end.

Notation "'[[' e ']]'" := 
  (eval e)(at level 100).


Fixpoint subse (x:Z) (z:Z) (e:exp): exp :=
  match e with 
    | Evar v => if Z.eq_dec x v then Enum z else Evar v
    | Enum n => Enum n
    | Eneg e => Eneg (subse x z e)
    | Eplus e1 e2 => Eplus (subse x z e1) (subse x z e2)
  end.

Fixpoint subs (c:cmd) (se: exp -> exp) : cmd :=
  match c with
    | Val e => Val (se e)
    | Cons n => Cons n
    | Lookup e => Lookup (se e)
    | Mutate e1 e2 => Mutate (se e1) (se e2)
    | Fork c => Fork (subs c se)
    | Let x' c1 c2 => Let x' (subs c1 se) (subs c2 se)
    | If c c1 c2 => If (subs c se) (subs c1 se) (subs c2 se)
    | While c c1 => While (subs c se) (subs c1 se)
    | Newlock => Newlock
    | Acquire e => Acquire (se e)
    | Release e => Release (se e)
    | Waiting4lock l => Waiting4lock (se l)
    | Newcond => Newcond
    | Wait v l => Wait (se v) (se l)
    | Notify v => Notify (se v)
    | NotifyAll v => NotifyAll (se v)
    | Waiting4cond v l => Waiting4cond (se v) (se l)
    | WasWaiting4cond v l => WasWaiting4cond (se v) (se l)
    | g => g
  end.

Fixpoint is_free_e (e: exp) (x: Z): bool :=
  match e with
    | Evar y => Z.eqb x y
    | Enum n => false
    | Eneg e => is_free_e e x
    | Eplus e1 e2 => orb (is_free_e e1 x) (is_free_e e2 x)
  end.

Fixpoint is_free (c: cmd) (x: Z): bool :=
  match c with
    | Val e => is_free_e e x
    | Cons n => false
    | Lookup e => is_free_e e x
    | Mutate e1 e2 => orb (is_free_e e1 x) (is_free_e e2 x)
    | Fork c => is_free c x
    | Let x' c1 c2 => orb (is_free c1 x) (is_free c2 x)
    | If c c1 c2 => orb (orb (is_free c x) (is_free c1 x)) (is_free c2 x)
    | While c c1 => orb (is_free c x) (is_free c1 x)
    | Newlock => false
    | Acquire e => is_free_e e x
    | Release e => is_free_e e x
    | Waiting4lock l => is_free_e l x
    | Newcond => false
    | Wait v l => orb (is_free_e v x) (is_free_e l x)
    | Notify v => is_free_e v x
    | NotifyAll v => is_free_e v x
    | Waiting4cond v l => orb (is_free_e v x) (is_free_e l x)
    | WasWaiting4cond v l => orb (is_free_e v x) (is_free_e l x)
    | g => false
  end.

Lemma subsc_id:
  forall c,
    subs c (fun e: exp => e) = c.
Proof.
  induction c; simpl; try reflexivity; try rewrite IHc; try reflexivity.
  rewrite IHc1. rewrite IHc2; reflexivity.
  rewrite IHc1. rewrite IHc2. rewrite IHc3; reflexivity.
  rewrite IHc1. rewrite IHc2; reflexivity.
Qed.

Lemma subse_subse:
  forall (e: exp) x z z',
    subse x z e = subse x z' (subse x z e).
Proof.
  induction e; simpl; intros.
  destruct (Z.eq_dec x0 x); try reflexivity. simpl.
  destruct (Z.eq_dec x0 x); try reflexivity. contradiction.
  reflexivity.
  rewrite <- IHe. reflexivity.
  rewrite <- IHe1.
  rewrite <- IHe2.
  reflexivity.
Qed.

Lemma is_free_subse:
  forall e x x' z
         (IS_FREE : is_free_e e x = false),
    is_free_e (subse x' z e) x = false.
Proof.
  induction e; simpl; intros.
  destruct (Z.eq_dec x' x); try reflexivity. simpl. assumption. assumption.
  apply IHe; assumption.
  apply Coq.Bool.Bool.orb_false_iff in IS_FREE.
  destruct IS_FREE.
  apply Coq.Bool.Bool.orb_false_iff. split.
  apply IHe1. assumption.
  apply IHe2. assumption.
Qed.

Lemma is_free_subs:
  forall c se x x' z
         (IS_FREE: is_free (subs c se) x = false),
    is_free (subs c (fun e => subse x' z (se e))) x = false.
Proof.
  induction c; simpl; intros; try apply is_free_subse; try assumption.
  apply Coq.Bool.Bool.orb_false_iff in IS_FREE. destruct IS_FREE.
  apply Coq.Bool.Bool.orb_false_iff. split;
  apply is_free_subse; try assumption.
  apply IHc; assumption.
  apply Coq.Bool.Bool.orb_false_iff in IS_FREE. destruct IS_FREE.
  apply Coq.Bool.Bool.orb_false_iff. split.
  apply IHc1; assumption.
  apply IHc2; assumption.
  apply Coq.Bool.Bool.orb_false_iff in IS_FREE. destruct IS_FREE.
  apply Coq.Bool.Bool.orb_false_iff in H. destruct H.
  apply Coq.Bool.Bool.orb_false_iff. split.
  apply Coq.Bool.Bool.orb_false_iff. split.
  apply IHc1; assumption.
  apply IHc2; assumption.
  apply IHc3; assumption.
  apply Coq.Bool.Bool.orb_false_iff in IS_FREE. destruct IS_FREE.
  apply Coq.Bool.Bool.orb_false_iff. split.
  apply IHc1; assumption.
  apply IHc2; assumption.
  apply Coq.Bool.Bool.orb_false_iff in IS_FREE. destruct IS_FREE.
  apply Coq.Bool.Bool.orb_false_iff. split; apply is_free_subse; try assumption.
  apply Coq.Bool.Bool.orb_false_iff in IS_FREE. destruct IS_FREE.
  apply Coq.Bool.Bool.orb_false_iff. split; apply is_free_subse; try assumption.
  apply Coq.Bool.Bool.orb_false_iff in IS_FREE. destruct IS_FREE.
  apply Coq.Bool.Bool.orb_false_iff. split; apply is_free_subse; try assumption.
Qed.

Lemma subse_subse_neq:
  forall (e: exp) x x0 z z0 (NEQ: x <> x0),
    subse x0 z (subse x z0 e) = subse x z0 (subse x0 z e).
Proof.
  induction e; simpl; intros.
  destruct (Z.eq_dec x0 x); try reflexivity. simpl.
  destruct (Z.eq_dec x1 x); try reflexivity. rewrite <- e0 in e. contradiction.
  simpl.
  destruct (Z.eq_dec x0 x); try reflexivity. contradiction.
  destruct (Z.eq_dec x1 x); try reflexivity. simpl.
  destruct (Z.eq_dec x1 x); try reflexivity. contradiction. simpl.
  destruct (Z.eq_dec x1 x); try reflexivity. contradiction.
  destruct (Z.eq_dec x0 x); try reflexivity. contradiction. reflexivity.
  rewrite IHe. reflexivity. assumption.
  rewrite IHe1; try assumption.
  rewrite IHe2; try assumption. reflexivity.
Qed.


(** # <font size="5"><b> Semantics of Commands </b></font> # *)

Definition wakeupcmd (z:Z) (c:cmd) :=
  match c with
    | Waiting4cond v l => if Z.eq_dec ([[v]]) z then (Waiting4lock l) else c
    | WasWaiting4cond v l => if Z.eq_dec ([[v]]) z then (Waiting4lock l) else c
    | c => c
  end.

Definition wakeupthrd (z:Z) (ctx: option (cmd * context)) :=
  match ctx with
    | Some (c,tx) => Some (wakeupcmd z c,tx)
    | c => c
  end.

Definition wakeupthrds (z:Z) (thrds1:thrds): thrds :=
  fun id => wakeupthrd z (thrds1 id).

Definition tt := Val (Enum 0).

Definition dstr_cells A (f: Z -> A) (l: list Z) (default: A) a := if in_dec Z.eq_dec a l then default else f a.

Inductive red: bool -> thrds -> heap -> thrds -> heap -> Prop := 
  | red_Cons: forall sp n a h id t tx (CMD: t id = Some (Cons n,tx)) 
              (NIN: forall z' (IN: In z' (map Z.of_nat (seq O n))), h (a+z') = None),
      red sp t h (upd Z.eq_dec t id (Some (Val (Enum a),tx))) (dstr_cells h (map (fun x => a + (Z.of_nat x)) (seq O n)) (Some 0))
  | red_Lookup: forall sp e h v id t tx (CMD: t id = Some (Lookup e,tx)) (ALC: h ([[e]]) = Some v),
      red sp t h (upd Z.eq_dec t id (Some (Val (Enum v),tx))) h
  | red_Mutate: forall sp e1 e2 h id t tx (CMD: t id = Some (Mutate e1 e2,tx)),
      red sp t h (upd Z.eq_dec t id (Some (tt,tx))) (upd Z.eq_dec h ([[e1]]) (Some ([[e2]])))
  | red_Fork: forall sp c h id t id' tx (CMD: t id = Some (Fork c,tx))(NIN: t id' = None),
      red sp t h (upd Z.eq_dec (upd Z.eq_dec t id (Some (tt,tx))) id' (Some (c,done))) h
  | red_Val: forall sp e x c h id t tx (CMD: t id = Some (Val e, Let' x c tx)),
      red sp t h (upd Z.eq_dec t id (Some (subs c (subse x ([[e]])),tx))) h
  | red_Terminate: forall sp e h id t (CMD: t id = Some (Val e,done)),
      red sp t h (upd Z.eq_dec t id None) h
  | red_Let: forall sp c1 c2 x h id t tx (CMD: t id = Some (Let x c1 c2,tx)),
      red sp t h (upd Z.eq_dec t id (Some (c1,Let' x c2 tx))) h
  | red_If: forall sp c c1 c2 h id t tx (CMD: t id = Some (If c c1 c2,tx)),
      red sp t h (upd Z.eq_dec t id (Some (c,If' c1 c2 tx))) h
  | red_If_true: forall sp e c1 c2 h id t tx (CMD: t id = Some (Val e, If' c1 c2 tx)) (TRUE: 0 < ([[e]])),
      red sp t h (upd Z.eq_dec t id (Some (c1,tx))) h
  | red_If_false: forall sp e c1 c2 h id t tx (CMD: t id = Some (Val e, If' c1 c2 tx)) (TRUE: ([[e]]) <= 0),
      red sp t h (upd Z.eq_dec t id (Some (c2,tx))) h
  | red_While: forall sp c c1 x h id t tx (CMD: t id = Some (While c c1,tx)) (NOTFREE: is_free (While c c1) x = false),
      red sp t h (upd Z.eq_dec t id (Some (If c (Let x c1 (While c c1)) tt, tx))) h
  | red_Newlock: forall sp h l id t tx (CMD: t id = Some (Newlock,tx)) (NIN: h l = None),
      red sp t h (upd Z.eq_dec t id (Some (Val (Enum l),tx))) (upd Z.eq_dec h l (Some 1))
  | red_Acquire: forall sp l h id t tx (CMD: t id = Some (Acquire l,tx)) (OPEN: h ([[l]]) = Some 1),
      red sp t h (upd Z.eq_dec t id (Some (tt,tx))) (upd Z.eq_dec h ([[l]]) (Some 0))
  | red_Acquire0: forall sp l h id t tx (CMD: t id = Some (Acquire l,tx)) (HELD: h ([[l]]) <> Some 1),
      red sp t h (upd Z.eq_dec t id (Some (Waiting4lock l,tx))) h
  | red_Acquire1: forall sp l h id t tx (CMD: t id = Some (Waiting4lock l,tx)) (OPEN: h ([[l]]) = Some 1),
      red sp t h (upd Z.eq_dec t id (Some (tt,tx))) (upd Z.eq_dec h ([[l]]) (Some 0))
  | red_Release: forall sp l h id t tx (CMD: t id = Some (Release l,tx)),
      red sp t h (upd Z.eq_dec t id (Some (tt,tx))) (upd Z.eq_dec h ([[l]]) (Some 1))
  | red_Newcond: forall sp h v id t tx (CMD: t id = Some (Newcond,tx)) (NIN: h v = None),
      red sp t h (upd Z.eq_dec t id (Some (Val (Enum v),tx))) (upd Z.eq_dec h v (Some 0))
  | red_Wait: forall sp h id t v l tx (CMD: t id = Some (Wait v l,tx)),
      red sp t h (upd Z.eq_dec t id (Some (Waiting4cond v l,tx))) (upd Z.eq_dec h ([[l]]) (Some 1))
  | red_Notify0: forall sp h id t v tx (CMD: t id = Some (Notify v,tx))
                        (NWT: ~ exists id' v' l tx' (EQvv': ([[v]]) = ([[v']])) , t id' = Some (Waiting4cond v' l,tx'))
                        (NWWT: ~ exists id' v' l tx' (EQvv': ([[v]]) = ([[v']])) , t id' = Some (WasWaiting4cond v' l,tx')),
      red sp t h (upd Z.eq_dec t id (Some (tt,tx))) h
  | red_Notify01: forall sp h id t v tx id' tx' l (CMD: t id = Some (Notify v,tx))
                        (NWT: ~ exists id' v' l tx' (EQvv': ([[v]]) = ([[v']])) , t id' = Some (Waiting4cond v' l,tx'))
                        (WWT: exists v' (EQvv': ([[v]]) = ([[v']])) , t id' = Some (WasWaiting4cond v' l,tx')),
      red sp t h (upd Z.eq_dec (upd Z.eq_dec t id (Some (tt,tx))) id' (Some (Waiting4lock l,tx'))) h
  | red_Notify: forall sp h id t v v' tx id' tx' l
                       (EQvv': ([[v]]) = ([[v']])) (CMD: t id = Some (Notify v,tx)) (CMD': t id' = Some (Waiting4cond v' l,tx')),
      red sp t h (upd Z.eq_dec (upd Z.eq_dec t id (Some (tt,tx))) id' (Some (Waiting4lock l,tx'))) h
  | red_SpuriousWakeup: forall h id t v tx l (CMD: t id = Some (Waiting4cond v l,tx)),
      red true t h (upd Z.eq_dec t id (Some (WasWaiting4cond v l,tx))) h
  | red_WasWait: forall sp h id t v l tx (CMD: t id = Some (WasWaiting4cond v l,tx)) (OPEN: h ([[l]]) = Some 1),
      red sp t h (upd Z.eq_dec t id (Some (tt,tx))) (upd Z.eq_dec h ([[l]]) (Some 0))
  | red_NotifyAll: forall sp h id t v tx (CMD: t id = Some (NotifyAll v,tx)),
      red sp t h (upd Z.eq_dec (wakeupthrds ([[v]]) t) id (Some (tt,tx))) h
  | red_nop: forall sp h id t tx (CMD: t id = Some (nop,tx)), red sp t h (upd Z.eq_dec t id (Some (tt,tx))) h.


(** # <font size="5"><b> Semantics of Abort </b></font> # *)

Definition access c : option Z := 
  match c with
    | Lookup e => Some ([[e]])
    | Mutate e _ => Some ([[e]])
    | _ => None
  end.

Definition write c : option Z :=
  match c with
    | Mutate e _ => Some ([[e]])
    | other => None
  end.

Definition data_race (t: thrds) :=
  exists id id' c c' tx tx' (NEQ: id <> id') 
         (CMD: t id = Some (c,tx)) (CMD': t id' = Some (c',tx')) (WR:write c <> None),
    write c = access c'.

Inductive aborts : thrds -> heap -> Prop := 
  | aborts_Race: forall h thrds (RACE: data_race thrds), aborts thrds h
  | aborts_Lookup: forall e h tid thrds tx (NUL: h ([[e]]) = None)(CMD: thrds tid = Some (Lookup e,tx)),
      aborts thrds h
  | aborts_Mutate: forall e1 e2 h tid thrds tx (NUL: h ([[e1]]) = None)(CMD: thrds tid = Some (Mutate e1 e2,tx)),
      aborts thrds h
  | aborts_Acquire: forall h l tid thrds tx (NUL: h ([[l]]) = None)(CMD: thrds tid = Some (Acquire l,tx)),
      aborts thrds h
  | aborts_Waiting4lock: forall h l tid thrds tx (NUL: h ([[l]]) = None)(CMD: thrds tid = Some (Waiting4lock l,tx)),
      aborts thrds h
  | aborts_WasWaiting4cond: forall h v l tid thrds tx (NUL: h ([[l]]) = None \/ h ([[v]]) = None)(CMD: thrds tid = Some (WasWaiting4cond v l,tx)),
      aborts thrds h
  | aborts_Release: forall h l tid thrds tx (NUL: h ([[l]]) = None \/ h ([[l]]) = Some 1)(CMD: thrds tid = Some (Release l,tx)),
      aborts thrds h
  | aborts_Wait: forall v h l tid thrds tx (NUL: h ([[l]]) = None \/ h ([[l]]) = Some 1 \/ h ([[v]]) = None) (CMD: thrds tid = Some (Wait v l,tx)),
      aborts thrds h
  | aborts_Waiting4cond: forall v h l tid thrds tx (NUL: h ([[l]]) = None \/ h ([[v]]) = None) (CMD: thrds tid = Some (Waiting4cond v l,tx)),
      aborts thrds h
  | aborts_Notify: forall v h tid thrds tx (NIN: h ([[v]]) = None) (CMD: thrds tid = Some (Notify v,tx)),
      aborts thrds h
  | aborts_NotifyAll: forall v h tid thrds tx (NIN: h ([[v]]) = None) (CMD: thrds tid = Some (NotifyAll v,tx)),
      aborts thrds h.


(** # <font size="5"><b> Suspension </b></font> # *)

Definition waiting_for (h:heap) (c:cmd) : option Z :=
  match c with
    | Waiting4cond v l => Some ([[v]])
    | WasWaiting4cond v l => if opZ_eq_dec (h ([[l]])) (Some 1%Z) then None else Some ([[l]])
    | Waiting4lock l => if opZ_eq_dec (h ([[l]])) (Some 1%Z) then None else Some ([[l]])
    | rest => None
  end.

Definition waiting_for_cond (c:cmd) : option Z :=
  match c with
    | Waiting4cond v l => Some ([[v]])
    | WasWaiting4cond v l => Some ([[v]])
    | rest => None
  end.

Fixpoint not_waiting_in (c:cmd) :=
  match c with
    | Waiting4cond v l => False
    | WasWaiting4cond v l => False
    | Waiting4lock l => False
    | Let x c1 c2 => not_waiting_in c1 /\ not_waiting_in c2
    | Fork c => not_waiting_in c
    | _ => True
  end.

Lemma not_waiting_none:
  forall c h (NOTW: not_waiting_in c),
    waiting_for h c = None.
Proof.
  intros.
  unfold not_waiting_in in NOTW.
  unfold waiting_for.
  induction c; try assumption; try reflexivity; try contradiction.
Qed.

Lemma not_waiting_cond_none:
  forall c (NOTW: not_waiting_in c),
    waiting_for_cond c = None.
Proof.
  intros.
  unfold not_waiting_in in NOTW.
  unfold waiting_for_cond.
  induction c; try assumption; try reflexivity; try contradiction.
Qed.

Lemma not_waiting_subs:
  forall c se,
    not_waiting_in c <-> not_waiting_in (subs c se).
Proof.
  induction c; simpl; intros; try reflexivity.
  - apply IHc.
  - split; intros.
    + destruct H as (NC1,NC2).
      * split.
        apply IHc1; assumption.
        apply IHc2; assumption.
    + destruct H as (NC1,NC2).
      * split.
        apply <- IHc1; apply NC1.
        apply <- IHc2; apply NC2.
Qed.

Lemma waiting_for_lock_cond:
  forall c h o
         (W4lc: waiting_for h c = Some o),
    exists e (EQ: o = ([[e]])), c = Waiting4lock e \/ exists l, c = Waiting4cond e l \/ c = WasWaiting4cond l e.
Proof.
  induction c; simpl; intros;
  inversion W4lc.
  - destruct (opZ_eq_dec (h ([[l]])) (Some 1%Z)); inversion W4lc.
    exists l. exists. reflexivity. tauto.
  - exists v. exists. reflexivity. right. exists l. left. reflexivity.
  - exists l. exists. destruct (opZ_eq_dec (h ([[l]])) (Some 1%Z)); inversion W4lc.
    reflexivity. right. exists v. right. reflexivity.
Qed.

Lemma wfwk:
  forall c z,
    ifb (opZ_eq_dec (waiting_for_cond (wakeupcmd z c)) (Some z)) = false.
Proof.
  induction c; repeat dstr_.
Qed.

Lemma waiting_for_dstr_eq:
  forall c h z z' v
         (NEQ: z <> z'),
    ifb (opZ_eq_dec (waiting_for h c) (Some z')) =
    ifb (opZ_eq_dec (waiting_for (upd Z.eq_dec h z v) c) (Some z')).
Proof.
  induction c; repeat dstr_.
Qed.

Lemma waiting_for_upd_eq:
  forall c h z z' v
         (NEQ: z <> z'),
    ifb (opZ_eq_dec (waiting_for h c) (Some z')) =
    ifb (opZ_eq_dec (waiting_for (upd Z.eq_dec h z v) c) (Some z')).
Proof.
  induction c;
  simpl;
  intros;
  try reflexivity;
  repeat dstr_.
Qed.


(** # <font size="5"><b> Wellformed Commands </b></font> # *)

Fixpoint wellformed_cmd (c:cmd) :=
  match c with
    | Let x c1 c2 => wellformed_cmd c1 /\ wellformed_cmd c2 /\ not_waiting_in c1 /\ not_waiting_in c2
    | Fork c => not_waiting_in c /\ wellformed_cmd c
    | If c c1 c2 => wellformed_cmd c /\ wellformed_cmd c1 /\ wellformed_cmd c2 /\ not_waiting_in c /\ not_waiting_in c1 /\ not_waiting_in c2
    | While c c1 => wellformed_cmd c /\ wellformed_cmd c1 /\ not_waiting_in c /\ not_waiting_in c1
    | _ => True
  end.

Fixpoint wellformed_ctx (ct:context) :=
  match ct with
    | Let' x c tx => wellformed_cmd c /\ not_waiting_in c /\ wellformed_ctx tx
    | If' c1 c2 tx => wellformed_cmd c1 /\ wellformed_cmd c2 /\ not_waiting_in c1 /\ not_waiting_in c2 /\ wellformed_ctx tx
    | done => True
  end.

Definition wellformed (ct: cmd * context) :=
  wellformed_cmd (fst ct) /\ wellformed_ctx (snd ct).

Lemma wellformed_cmd_subs:
  forall c se,
    wellformed_cmd c <-> wellformed_cmd (subs c se).
Proof.
  induction c; simpl; intros; try reflexivity.
  split.
  intros.
  destruct H as (N,W).
  split.
  apply not_waiting_subs; assumption.
  apply IHc; assumption.
  intros.
  destruct H as (N,W).
  split.
  apply not_waiting_subs in N; assumption.
  apply IHc in W; assumption.
  split.
  intros.
  destruct H as (W1,(W2,(N1,N2))).
  split. apply IHc1; assumption.
  split. apply IHc2; assumption.
  split. apply not_waiting_subs; assumption.
  apply not_waiting_subs; assumption.
  intros.
  destruct H as (W1,(W2,(N1,N2))).
  split. apply IHc1 in W1; assumption.
  split. apply IHc2 in W2; assumption.
  split. apply not_waiting_subs in N1; assumption.
  apply not_waiting_subs in N2; assumption.
  split.
  intros.
  destruct H as (W1,(W2,(W3,(N1,(N2,N3))))).
  split. apply IHc1; assumption.
  split. apply IHc2; assumption.
  split. apply IHc3; assumption.
  split. apply not_waiting_subs; assumption.
  split. apply not_waiting_subs; assumption.
  apply not_waiting_subs; assumption.
  intros.
  destruct H as (W1,(W2,(W3,(N1,(N2,N3))))).
  split. apply IHc1 in W1; assumption.
  split. apply IHc2 in W2; assumption.
  split. apply IHc3 in W3; assumption.
  split. apply not_waiting_subs in N1; assumption.
  split. apply not_waiting_subs in N2; assumption.
  apply not_waiting_subs in N3; assumption.
  split.
  intros.
  destruct H as (W1,(W2,(N1,N2))).
  split. apply IHc1; assumption.
  split. apply IHc2; assumption.
  split. apply not_waiting_subs; assumption.
  apply not_waiting_subs; assumption.
  intros.
  destruct H as (W1,(W2,(N1,N2))).
  split. apply IHc1 in W1; assumption.
  split. apply IHc2 in W2; assumption.
  split. apply not_waiting_subs in N1; assumption.
  apply not_waiting_subs in N2; assumption.
Qed.


(** # <font size="5"><b> Free Variables </b></font> # *)

Fixpoint free_var_e (e: exp) : list Z :=
  match e with
    | Evar y => y::nil
    | Enum n => nil
    | Eneg e => free_var_e e
    | Eplus e1 e2 => (free_var_e e1) ++ (free_var_e e2)
  end.

Lemma is_free_var_e:
  forall e x (NFREE: is_free_e e x = true),
    In x (free_var_e e).
Proof.
  induction e; simpl; intros.
  left.
  apply Z.eqb_eq in NFREE.
  omega.
  inversion NFREE.
  apply IHe; assumption.
  apply Coq.Bool.Bool.orb_true_iff in NFREE.
  apply in_app_iff.
  destruct NFREE.
  left.
  apply IHe1.
  assumption.
  right.
  apply IHe2.
  assumption.
Qed.

Fixpoint free_var (c: cmd) : list Z :=
  match c with
    | Val e => free_var_e e
    | Cons n => nil
    | Lookup e => free_var_e e
    | Mutate e1 e2 => free_var_e e1 ++ free_var_e e2
    | Fork c => free_var c
    | Let x' c1 c2 => free_var c1 ++ free_var c2
    | If c c1 c2 => free_var c ++ free_var c1 ++ free_var c2
    | While c c1 => free_var c ++ free_var c1
    | Newlock => nil
    | Acquire e => free_var_e e
    | Release e => free_var_e e
    | Waiting4lock l => free_var_e l
    | Newcond => nil
    | Wait v l => free_var_e v ++ free_var_e l
    | Notify v => free_var_e v
    | NotifyAll v => free_var_e v
    | Waiting4cond v l => free_var_e v ++ free_var_e l
    | WasWaiting4cond v l => free_var_e v ++ free_var_e l
    | g => nil
  end.

Lemma is_free_var:
  forall c x (NFREE: is_free c x = true),
    In x (free_var c).
Proof.
  induction c;
  try apply is_free_var_e;
  intros;
  inversion NFREE.
  simpl in *.
  apply Coq.Bool.Bool.orb_true_iff in H0.
  apply in_app_iff.
  destruct H0.
  left.
  apply is_free_var_e.
  assumption.
  right.
  apply is_free_var_e.
  assumption.
  simpl.
  apply IHc.
  assumption.
  simpl.
  apply Coq.Bool.Bool.orb_true_iff in H0.
  apply in_app_iff.
  destruct H0.
  left.
  apply IHc1.
  assumption.
  right.
  apply IHc2.
  assumption.
  simpl.
  apply in_app_iff.
  apply Coq.Bool.Bool.orb_true_iff in H0.
  destruct H0.
  apply Coq.Bool.Bool.orb_true_iff in H.
  destruct H.
  left.
  apply IHc1.
  assumption.
  right.
  apply in_app_iff.
  left.
  apply IHc2.
  assumption.
  right.
  apply in_app_iff.
  right.
  apply IHc3.
  assumption.

  simpl.
  apply in_app_iff.
  apply Coq.Bool.Bool.orb_true_iff in H0.
  destruct H0.
  left. apply IHc1. assumption.
  right. apply IHc2. assumption.
  simpl.
  apply in_app_iff.
  apply Coq.Bool.Bool.orb_true_iff in H0.
  destruct H0.
  left.
  apply is_free_var_e.
  assumption.
  right.
  apply is_free_var_e.
  assumption.
  simpl.
  apply in_app_iff.
  apply Coq.Bool.Bool.orb_true_iff in H0.
  destruct H0.
  left.
  apply is_free_var_e.
  assumption.
  right.
  apply is_free_var_e.
  assumption.
  simpl.
  apply in_app_iff.
  apply Coq.Bool.Bool.orb_true_iff in H0.
  destruct H0.
  left.
  apply is_free_var_e.
  assumption.
  right.
  apply is_free_var_e.
  assumption.
Qed.

Lemma is_free_var':
  forall c x (NIN: ~ In x (free_var c)),
    is_free c x = false.
Proof.
  intros.
  destruct (is_free c x) eqn:ISF.
  apply is_free_var in ISF.
  contradiction.
  reflexivity.
Qed.

Lemma inf_var:
  forall c, exists x, is_free c x = false.
Proof.
  intros.
  destruct (free_var c) eqn:FV.
  exists 0.
  apply is_free_var'.
  rewrite FV.
  unfold not.
  intros.
  inversion H.
  assert (G: exists max (INl: In max (z::l)), forall x (INl: In x (z::l)), Z.le x max).
  {
  apply list_has_max.
  simpl.
  omega.
  }
  destruct G as (max, (INmax, MAX)).
  exists (max+1).
  apply is_free_var'.
  unfold not.
  intros.
  assert (CO: max+1 <= max).
  {
  apply MAX.
  rewrite <- FV.
  assumption.
  }
  omega.
Qed.

Lemma subse_free:
  forall e x z
    (NOTFREE: is_free_e e x = false),
  subse x z e = e.
Proof.
  induction e.
  simpl.
  intros.
  apply neqb_neq in NOTFREE.
  destruct (Z.eq_dec x0 x).
  contradiction.
  reflexivity.
  simpl.
  intros.
  reflexivity.
  simpl.
  intros.
  rewrite IHe.
  reflexivity.
  assumption.
  simpl.
  intros.
  apply Coq.Bool.Bool.orb_false_iff in NOTFREE.
  destruct NOTFREE.
  rewrite IHe1; try assumption.
  rewrite IHe2; try assumption.
  reflexivity.
Qed.

(** # <font size="5"><b> Infinite Capacity </b></font> # *)

Definition inf_capacity A (f: Z -> option A) :=
  exists x, forall y (LE: x <= y), f y = None.

Lemma dstr_preserves_inf_capacity A (f: Z -> option A):
  forall x y (INF: inf_capacity f),
    inf_capacity (upd Z.eq_dec f x y).
Proof.
  unfold inf_capacity.
  intros.
  destruct INF as (x1,INF).
  exists ((Z.max x1 x) + 1)%Z.
  intros.
  unfold upd.
  destruct (Z.eq_dec y0 x).
  rewrite e in *.
  unfold Z.max in *.
  destruct (x1 ?= x)%Z eqn:EQ.
  apply Z.compare_eq_iff in EQ.
  omega.
  omega.
  apply Z.compare_le_iff in EQ.
  omega.
  omega.
  apply INF.
  unfold Z.max in *.
  destruct (x1 ?= x)%Z eqn:EQ.
  omega.
  rewrite Z.compare_lt_iff in EQ.
  omega.
  omega.
Qed.

Lemma steps_preserve_inf_capacity1:
  forall sp t h t' h'
         (INF_CAP: inf_capacity t)
         (RED: red sp t h t' h'),
    inf_capacity t'.
Proof.
  intros.
  induction RED;
  try apply dstr_preserves_inf_capacity;
  try tauto;
  try apply dstr_preserves_inf_capacity;
  try tauto.
  unfold inf_capacity in *.
  destruct INF_CAP.
  unfold wakeupthrds.
  unfold wakeupthrd.
  exists x.
  intros.
  rewrite H.
  reflexivity.
  assumption.
Qed.

Lemma steps_preserve_inf_capacity2:
  forall sp t h t' h'
         (INF_CAP: inf_capacity h)
         (RED: red sp t h t' h'),
    inf_capacity h'.
Proof.
  intros.
  induction RED;
  try apply dstr_preserves_inf_capacity;
  try tauto;
  try apply dstr_preserves_inf_capacity;
  try tauto.
  unfold dstr_cells.
  unfold inf_capacity in *.
  destruct INF_CAP.
  exists ((Z.max x (a+Z.of_nat n)%Z)+1)%Z.
  intros.
  destruct (in_dec Z.eq_dec y (map (fun x0 : nat => (a + Z.of_nat x0)%Z) (seq 0 n))) eqn:IN.
  destruct IN.
  apply in_map_iff in i.
  destruct i as (x1,(EQx,INx)).
  rewrite <- EQx in LE.
  assert (LE1: le x1 n).
  {
  apply in_seq in INx.
  omega.
  }
  assert (G: (Z.max x (a + Z.of_nat n) + 1 <= a + Z.of_nat n)%Z).
  {
  omega.
  }
  unfold Z.max in G.
  destruct (x ?= a + Z.of_nat n)%Z eqn:EQ.
  apply Z.compare_eq_iff in EQ.
  rewrite EQ in *.
  simpl in *.
  omega.
  omega.
  apply Z.compare_le_iff in EQ.
  omega.
  omega.
  apply H.
  unfold Z.max in LE.
  destruct (x ?= a + Z.of_nat n)%Z eqn:EQ.
  apply Z.compare_eq_iff in EQ.
  omega.
  rewrite Z.compare_lt_iff in EQ.
  omega.
  omega.
Qed.

Lemma steps_preserve_inf_capacity:
  forall sp t h t' h'
         (INF_CAP: inf_capacity t /\ inf_capacity h)
         (RED: red sp t h t' h'),
    inf_capacity t' /\ inf_capacity h'.
Proof.
  intros.
  destruct INF_CAP as (INF1,INF2).
  split.
  apply steps_preserve_inf_capacity1 with sp t h h'; assumption.
  apply steps_preserve_inf_capacity2 with sp t h t'; assumption.
Qed.
