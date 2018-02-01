Add LoadPath "/Users/jafarhamin/Desktop/deadlock-free-monitors-soundness".
Require Import ZArith.
Require Import Util_Z.
Require Import Util_list.

Set Implicit Arguments.

(** # <font size="5"><b> Expressions </b></font> # *)

Inductive exp := 
  | Evar (x: Z)
  | Enum (num: Z)
  | Eplus (e1: exp) (e2: exp).

Inductive bexp :=
  | Blt (e1: exp) (e2: exp)
  | Bneg (b: bexp).

(** # <font size="5"><b> Commands </b></font> # *)

Inductive cmd :=
  | Val (z: Z)
  | Cons (e: exp)
  | Lookup (e: exp)
  | Mutate (e1: exp) (e2: exp)
  | Fork (c: cmd)
  | Let (x: Z) (c1: cmd) (c2: cmd)
  | Newlock
  | Acquire (e: exp)
  | Release (e: exp)
  | Waiting4lock (l: exp)
  | Newcond
  | Wait (x: exp)(l: exp)
  | Notify (x: exp)
  | NotifyAll (x: exp)
  | Waiting4cond (v: exp)(l: exp)
  | g_initl (x: exp)
  | g_dupl (x:exp)
  | g_chrg (x:exp)
  | g_chrgu (x:exp)
  | g_disch (x:exp)
  | g_dischu (x:exp)
  | g_gain (x:exp)
  | g_gainu (x:exp)
  | g_lose (x:exp)
  | g_loseu (x:exp)
  | g_info (x:exp)
  | g_infou (x:exp).

Definition exp_eq_dec (e1 e2: exp) : {e1 = e2} + {e1 <> e2}.
Proof.
  decide equality;
  apply Z_eq_dec.
Qed.

Definition cmd_eq_dec (c1 c2: cmd) : {c1 = c2} + {c1 <> c2}.
Proof.
  decide equality;
  try apply Z_eq_dec;
  try apply exp_eq_dec.
Qed.

Inductive context :=
  | done
  | Let' (x: Z) (c: cmd) (tx: context).


(** # <font size="5"><b> Semantics of Expressions </b></font> # *)

Definition heap := Z -> option Z.
Definition thrds := Z -> option (cmd * context).

Open Local Scope Z.

Fixpoint eval (e:exp) : Z :=
  match e with
    | Evar x => 0
    | Enum n => n
    | Eplus e1 e2 => (eval e1) + (eval e2)
  end.

Notation "'[[' e ']]'" := 
  (eval e)(at level 100).

Fixpoint beval (b:bexp) : bool :=
  match b with
    | Blt e1 e2 => if Z_lt_dec ([[e1]]) ([[e2]]) then true else false
    | Bneg b => negb (beval b)
  end.

Fixpoint subse (x:Z) (z:Z) (e:exp): exp :=
  match e with 
    | Evar v => if Z.eq_dec x v then Enum z else Evar v
    | Enum n => Enum n
    | Eplus e1 e2 => Eplus (subse x z e1) (subse x z e2)
  end.

Fixpoint subsb (x:Z) (z:Z) (b:bexp): bexp :=
  match b with 
    | Blt e1 e2 => Blt (subse x z e1) (subse x z e2)
    | Bneg b => Bneg (subsb x z b)
  end.

Fixpoint subs (c:cmd) (se: exp -> exp) : cmd :=
  match c with
    | Val z => Val z
    | Cons e => Cons (se e)
    | Lookup e => Lookup (se e)
    | Mutate e1 e2 => Mutate (se e1) (se e2)
    | Fork c => Fork (subs c se)
    | Let x' c1 c2 => Let x' (subs c1 se) (subs c2 se)
    | Newlock => Newlock
    | Acquire e => Acquire (se e)
    | Release e => Release (se e)
    | Waiting4lock l => Waiting4lock (se l)
    | Newcond => Newcond
    | Wait v l => Wait (se v) (se l)
    | Notify v => Notify (se v)
    | NotifyAll v => NotifyAll (se v)
    | Waiting4cond v l => Waiting4cond (se v) (se l)
    | g_dupl e => g_dupl (se e)
    | g_initl e => g_initl (se e)
    | g_chrg e => g_chrg (se e)
    | g_chrgu e => g_chrgu (se e)
    | g_disch e => g_disch (se e)
    | g_dischu e => g_dischu (se e)
    | g_gain e => g_gain (se e)
    | g_gainu e => g_gainu (se e)
    | g_lose e => g_lose (se e)
    | g_loseu e => g_loseu (se e)
    | g_info e => g_info (se e)
    | g_infou e => g_infou (se e)
  end.

(** # <font size="5"><b> Semantics of Commands </b></font> # *)

Definition wakeupcmd (z:Z) (c:cmd) :=
  match c with
    | Waiting4cond v l => if Z.eq_dec ([[v]]) z then (Waiting4lock l) else (Waiting4cond v l)
    | c => c
  end.

Definition wakeupthrd (z:Z) (ctx: option (cmd * context)) :=
  match ctx with
    | Some (c,tx) => Some (wakeupcmd z c,tx)
    | c => c
  end.

Definition wakeupthrds (z:Z) (thrds1:thrds): thrds :=
  fun id => wakeupthrd z (thrds1 id).

Inductive red: thrds -> heap -> thrds -> heap -> Prop := 
  | red_Cons: forall e a h id t tx (NIN: h a = None) (CMD: t id = Some (Cons e,tx)),
      red t h (upd t id (Some (Val 0,tx))) (upd h a (Some ([[e]])))
  | red_Lookup: forall e h id t tx (CMD: t id = Some (Lookup e,tx)),
      red t h (upd t id (Some (Val (lift 0 (h ([[e]]))),tx))) h
  | red_Mutate: forall e1 e2 h id t tx (CMD: t id = Some (Mutate e1 e2,tx)),
      red t h (upd t id (Some (Val 0,tx))) (upd h ([[e1]]) (Some ([[e2]])))
  | red_Fork: forall c h id t id' tx (CMD: t id = Some (Fork c,tx))(NIN: t id' = None),
      red t h (upd (upd t id (Some (Val 0,tx))) id' (Some (c,done))) h
  | red_Val: forall z x c h id t tx (CMD: t id = Some (Val z, Let' x c tx)),
      red t h (upd t id (Some (subs c (subse x z),tx))) h
  | red_Terminate: forall z h id t (CMD: t id = Some (Val z,done)),
      red t h (upd t id None) h
  | red_Let: forall c1 c2 x h id t tx (CMD: t id = Some (Let x c1 c2,tx)),
      red t h (upd t id (Some (c1,Let' x c2 tx))) h
  | red_Newlock: forall h l id t tx (CMD: t id = Some (Newlock,tx)) (NIN: h l = None),
      red t h (upd t id (Some (Val l,tx))) (upd h l (Some 1))
  | red_Acquire: forall l h id t tx (CMD: t id = Some (Acquire l,tx)) (OPEN: h ([[l]]) = Some 1),
      red t h (upd t id (Some (Val 0,tx))) (upd h ([[l]]) (Some 0))
  | red_Acquire0: forall l h id t tx (CMD: t id = Some (Acquire l,tx)) (HELD: h ([[l]]) <> Some 1),
      red t h (upd t id (Some (Waiting4lock l,tx))) h
  | red_Acquire1: forall l h id t tx (CMD: t id = Some (Waiting4lock l,tx)) (HELD: h ([[l]]) = Some 1),
      red t h (upd t id (Some (Val 0,tx))) (upd h ([[l]]) (Some 0))
  | red_Release: forall l h id t tx (CMD: t id = Some (Release l,tx)),
      red t h (upd t id (Some (Val 0,tx))) (upd h ([[l]]) (Some 1))
  | red_Newcond: forall h v id t tx (CMD: t id = Some (Newcond,tx)) (NIN: h v = None),
      red t h (upd t id (Some (Val v,tx))) (upd h v (Some 0))
  | red_Wait: forall h id t v l tx (CMD: t id = Some (Wait v l,tx)),
      red t h (upd t id (Some (Waiting4cond v l,tx))) (upd h ([[l]]) (Some 1))
  | red_Notify0: forall h id t v tx (CMD: t id = Some (Notify v,tx))
                        (NWT: ~ exists id' v' l tx' (EQvv': ([[v]]) = ([[v']])) , t id' = Some (Waiting4cond v' l,tx')),
      red t h (upd t id (Some (Val 0,tx))) h
  | red_Notify: forall h id t v v' tx id' tx' l (EQvv': ([[v]]) = ([[v']])) (CMD: t id = Some (Notify v,tx)) (CMD':t id' = Some (Waiting4cond v' l,tx')),
      red t h (upd (upd t id (Some (Val 0,tx))) id' (Some (Waiting4lock l,tx'))) h
  | red_NotifyAll: forall h id t v tx (CMD: t id = Some (NotifyAll v,tx)),
      red t h (upd (wakeupthrds ([[v]]) t) id (Some (Val 0,tx))) h
  | red_g_dupl: forall h id t l tx (CMD: t id = Some (g_dupl l,tx)), red t h (upd t id (Some (Val 0,tx))) h
  | red_g_initl: forall h id t l tx (CMD: t id = Some (g_initl l,tx)), red t h (upd t id (Some (Val 0,tx))) h
  | red_g_chrg: forall h id t v tx (CMD: t id = Some (g_chrg v,tx)), red t h (upd t id (Some (Val 0,tx))) h
  | red_g_chrgu: forall h id t v tx (CMD: t id = Some (g_chrgu v,tx)), red t h (upd t id (Some (Val 0,tx))) h
  | red_g_disch: forall h id t v tx (CMD: t id = Some (g_disch v,tx)), red t h (upd t id (Some (Val 0,tx))) h
  | red_g_dischu: forall h id t v tx (CMD: t id = Some (g_dischu v,tx)), red t h (upd t id (Some (Val 0,tx))) h
  | red_g_gain: forall h id t v tx (CMD: t id = Some (g_gain v,tx)), red t h (upd t id (Some (Val 0,tx))) h
  | red_g_gainu: forall h id t v tx (CMD: t id = Some (g_gainu v,tx)), red t h (upd t id (Some (Val 0,tx))) h
  | red_g_lose: forall h id t v tx (CMD: t id = Some (g_lose v,tx)), red t h (upd t id (Some (Val 0,tx))) h
  | red_g_loseu: forall h id t v tx (CMD: t id = Some (g_loseu v,tx)), red t h (upd t id (Some (Val 0,tx))) h
  | red_g_info: forall h id t v tx (CMD: t id = Some (g_info v,tx)), red t h (upd t id (Some (Val 0,tx))) h
  | red_g_infou: forall h id t v tx (CMD: t id = Some (g_infou v,tx)), red t h (upd t id (Some (Val 0,tx))) h.


(** # <font size="5"><b> Semantics of Abort </b></font> # *)

Fixpoint access c : option Z := 
  match c with
    | Lookup e => Some ([[e]])
    | Mutate e _ => Some ([[e]])
    | Let _ c _ => access c
    | _ => None
  end.

Fixpoint write c : option Z :=
  match c with
    | Mutate e _ => Some ([[e]])
    | Let _ c _ => write c
    | other => None
  end.

Inductive aborts : thrds -> heap -> Prop := 
  | aborts_Let : forall x c1 c2 h tid thrds tx tx1 (CMD: thrds tid = Some (Let x c1 c2,tx)) (A: aborts (upd thrds tid (Some (c1,tx1))) h),
      aborts thrds h
  | aborts_Race: forall c c' h tid tid' thrds tx tx' (NEQ: tid <> tid')(WR: write c <> None)(RC: write c = access c')
                        (CMD: thrds tid = Some (c,tx))(CMD': thrds tid' = Some (c',tx')),
      aborts thrds h
  | aborts_Lookup: forall e h tid thrds tx (NIN: h ([[e]]) = None)(CMD: thrds tid = Some (Lookup e,tx)),
      aborts thrds h
  | aborts_Mutate: forall e1 e2 h tid thrds tx (NIN: h ([[e1]]) = None)(CMD: thrds tid = Some (Mutate e1 e2,tx)),
      aborts thrds h
  | aborts_Acquire: forall h l tid thrds tx (NIN: h ([[l]]) = None)(CMD: thrds tid = Some (Acquire l,tx)),
      aborts thrds h
  | aborts_Release: forall h l tid thrds tx (NIN: h ([[l]]) <> Some 0)(CMD: thrds tid = Some (Release l,tx)),
      aborts thrds h.

(** # <font size="5"><b> Suspension </b></font> # *)

Definition waiting_for (h:heap) (c:cmd) : option Z :=
  match c with
    | Waiting4cond v l => Some ([[v]])
    | Waiting4lock l => if opZ_eq_dec (h ([[l]])) (Some 1%Z) then None else Some ([[l]])
    | rest => None
  end.

Definition waiting_for_cond (c:cmd) : option Z :=
  match c with
    | Waiting4cond v l => Some ([[v]])
    | rest => None
  end.

Fixpoint not_waiting_in (c:cmd) :=
  match c with
    | Waiting4cond v l => False
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
  induction c;
  try assumption;
  try reflexivity.
  contradiction.
  contradiction.
Qed.

Lemma not_waiting_cond_none:
  forall c (NOTW: not_waiting_in c),
    waiting_for_cond c = None.
Proof.
  intros.
  unfold not_waiting_in in NOTW.
  unfold waiting_for_cond.
  induction c;
  try assumption;
  try reflexivity.
  contradiction.
Qed.

Lemma not_waiting_subs:
  forall c se,
    not_waiting_in c <-> not_waiting_in (subs c se).
Proof.
  induction c;
  try reflexivity.
  simpl.
  apply IHc.
  simpl.
  split.
  intros.
  destruct H as (NC1,NC2).
  split.
  apply IHc1.
  assumption.
  apply IHc2.
  assumption.
  intros.
  destruct H as (NC1,NC2).
  split.
  apply <- IHc1.
  apply NC1.
  apply <- IHc2.
  apply NC2.
Qed.

Lemma waiting_for_lock_cond:
  forall c h o
         (W4lc: waiting_for h c = Some o),
    exists e (EQ: o = ([[e]])), c = Waiting4lock e \/ exists l, c = Waiting4cond e l.
Proof.
  induction c;
  simpl;
  intros;
  inversion W4lc.
  destruct (opZ_eq_dec (h ([[l]])) (Some 1%Z));
  inversion W4lc.
  exists l.
  exists.
  reflexivity.
  left.
  reflexivity.
  exists v.
  exists.
  reflexivity.
  right.
  exists l.
  reflexivity.
Qed.

Lemma wfwk:
  forall c z,
    ifb (opZ_eq_dec (waiting_for_cond (wakeupcmd z c)) (Some z)) = false.
Proof.
  induction c;
  simpl;
  try apply ifboneq.
  intros.
  destruct (Z.eq_dec ([[v]]) z).
  simpl.
  apply ifboneq.
  simpl.
  destruct (opZ_eq_dec (Some ([[v]])) (Some z)).
  inversion e.
  contradiction.
  reflexivity.
Qed.

Lemma waiting_for_upd_neq:
  forall c h z v
         (NEQ: waiting_for_cond c <> waiting_for (upd h z v) c),
    exists l, c = Waiting4lock l.
Proof.
  induction c;
  simpl;
  intros;
  try contradiction.
  exists l.
  reflexivity.
Qed.

Lemma waiting_for_upd_neq2a:
  forall c h z v
         (NEQ: waiting_for h c <> waiting_for (upd h z v) c),
    exists l, c = Waiting4lock l.
Proof.
  induction c;
  simpl;
  intros;
  try contradiction.
  exists l.
  reflexivity.
Qed.

Lemma waiting_for_upd_eq:
  forall c h z z' v
         (NEQ: z <> z'),
    ifb (opZ_eq_dec (waiting_for h c) (Some z')) =
    ifb (opZ_eq_dec (waiting_for (upd h z v) c) (Some z')).
Proof.
  induction c;
  simpl;
  intros;
  try reflexivity.
  unfold upd.
  destruct (Z.eq_dec ([[l]]) z).
  rewrite e.
  destruct (opZ_eq_dec (h z) (Some 1%Z)).
  destruct (opZ_eq_dec v (Some 1%Z)).
  reflexivity.
  destruct (opZ_eq_dec (Some z) (Some z')).
  inversion e1.
  omega.
  apply ifboneq.
  destruct (opZ_eq_dec v (Some 1%Z)).
  destruct (opZ_eq_dec (Some z) (Some z')).
  inversion e1.
  omega.
  symmetry.
  apply ifboneq.
  reflexivity.
  reflexivity.
Qed.

Lemma waiting_for_cond_neq:
  forall c h 
         (NEQ: waiting_for_cond c <> waiting_for h c),
    exists l, c = Waiting4lock l.
Proof.
  induction c;
  simpl;
  intros;
  try contradiction.
  exists l.
  reflexivity.
Qed.

(** # <font size="5"><b> Wellformed Commands </b></font> # *)

Definition wellformed_cmd (c:cmd) :=
  match c with
    | Let x c1 c2 => not_waiting_in c1 /\ not_waiting_in c2
    | Fork c => not_waiting_in c
    | _ => True
  end.

Fixpoint wellformed_ctx (ct:context) :=
  match ct with
    | Let' x c tx => not_waiting_in c /\ wellformed_ctx tx
    | done => True
  end.

Definition wellformed (ct: cmd * context) :=
  wellformed_cmd (fst ct) /\ wellformed_ctx (snd ct).


