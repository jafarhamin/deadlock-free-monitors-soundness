Add LoadPath "proofs".

Require Import ZArith.
Require Import Qcanon.
Require Import List.
Require Import Util_Z.
Require Import Util_list.
Require Import Coq.QArith.QArith_base.
Require Import Programs.
Require Import Assertions.
Require Import ProofRules.
Require Import Soundness.

Set Implicit Arguments.

Local Open Scope Z.

(** # <font size="5"><b> Increment </b></font> # *)

Definition inc (e: exp) (x: Z) :=
  Let x (Lookup e) 
  (Mutate e (Eplus (Evar x) (Enum 1))).

Theorem rule_inc invs sp e v x (FRESH: is_free_e e x = false): correct
  (cell_loc e |-> v)
  (inc e x)
  (fun r => cell_loc e |-> (Eplus v (Enum 1))) invs sp.
Proof.
  apply rule_Let with (fun z => Abool (Z.eqb z ([[v]])) &* cell_loc e |-> v).
  apply rule_Lookup.
  intros.
  simpl.
  rewrite eqz.
  unfold subs.
  rewrite subse_free; try assumption.
  apply rule_conseq with
  (cell_loc e |-> v ** Abool (z =? ([[v]])))
  (fun _ : Z => cell_loc e |-> Eplus (Enum z) (Enum 1) ** Abool (z =? ([[v]]))); intros; try assumption.
  apply rule_frame.
  apply rule_Mutate.
  apply rule_comm_pure in SAT; try assumption.
  apply rule_pure_star; assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,EQ).
  apply Z.eqb_eq in EQ.
  rewrite EQ in *.
  assumption.
Qed.

Lemma subs_inc:
  forall e se x
         (EQ: se (Eplus (Evar x) (Enum 1)) = Eplus (Evar x) (Enum 1)),
    subs (inc e x) se = inc (se e) x.
Proof.
  unfold inc.
  simpl.
  intros.
  rewrite EQ.
  reflexivity.
Qed.

Opaque inc.


(** # <font size="5"><b> Not Equal </b></font> # *)

Definition not_equal (e1 e2: exp) :=
  If (Val (Eplus e1 (Eneg e2)))
     (Val (Enum 1))
     (If (Val (Eplus e2 (Eneg e1)))
         (Val (Enum 1))
         (Val (Enum 0))).

Theorem rule_not_equal invs sp e1 e2: correct
  (Abool true)
  (not_equal e1 e2)
  (fun z => Abool (Z.eqb z (if Z.eq_dec ([[e1]]) ([[e2]]) then 0 else 1))) invs sp.
Proof.
  apply rule_If with (fun z' => Abool (Z.eqb z' ([[Eplus e1 (Eneg e2)]]))).
  apply rule_Val.
  simpl.
  intros.
  apply rule_conseq with (Abool true ** Abool (Z.ltb ([[e2]]) ([[e1]])))
    (fun z0 => Abool (Z.eqb z0 ([[Enum 1]])) ** Abool (Z.ltb ([[e2]]) ([[e1]]))).
  apply rule_frame.
  apply rule_Val.
  {
  intros.
  apply rule_pure_star'; try assumption.
  split. simpl. trivial.
  simpl in *.
  apply Z.ltb_lt.
  apply Z.eqb_eq in SAT.
  omega.
  }
  {
  intros.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,NEQ).
  apply Z.ltb_lt in NEQ.
  simpl.
  rewrite neqz.
  assumption.
  omega.
  }
  simpl.
  intros.
  apply rule_If with (fun z' => Abool (Z.eqb z' ([[Eplus e2 (Eneg e1)]])) **
    Abool (Z.leb ([[e1]]) ([[e2]]))).
  apply rule_conseq1 with (Abool true ** Abool (Z.leb ([[e1]]) ([[e2]]))).
  apply rule_frame.
  apply rule_Val.
  {
  intros.
  apply rule_pure_star'; try assumption.
  split. simpl. trivial.
  simpl in *.
  apply Z.leb_le.
  apply Z.eqb_eq in SAT.
  omega.
  }
  simpl.
  intros.
  apply rule_conseq with (Abool true ** Abool (Z.ltb ([[e1]]) ([[e2]])))
    (fun z0 => Abool (Z.eqb z0 ([[Enum 1]])) ** Abool (Z.ltb ([[e1]]) ([[e2]]))).
  apply rule_frame.
  apply rule_Val.
  {
  intros.
  apply rule_pure_star'; try assumption.
  split. simpl. trivial.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ,LE).
  simpl in *.
  apply Z.ltb_lt.
  apply Z.leb_le in LE.
  apply Z.eqb_eq in EQ.
  omega.
  }
  {
  intros.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ,LE).
  simpl in *.
  apply Z.ltb_lt in LE.
  rewrite neqz; try assumption.
  omega.
  }
 simpl.
  intros.
  apply rule_conseq with (Abool true ** Abool (Z.eqb ([[e1]]) ([[e2]])))
    (fun z0 => Abool (Z.eqb z0 ([[Enum 0]])) ** Abool (Z.eqb ([[e1]]) ([[e2]]))).
  apply rule_frame.
  apply rule_Val.
  {
  intros.
  apply rule_pure_star'; try assumption.
  split. simpl. trivial.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ,LE).
  simpl in *.
  apply Z.eqb_eq.
  apply Z.eqb_eq in EQ.
  apply Z.leb_le in LE.
  omega.
  }
  {
  intros.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ,LE).
  simpl in *.
  rewrite Z.eqb_eq in LE.
  rewrite LE.
  rewrite eqz. assumption.
  }
Qed.

Lemma subs_not_equal:
  forall se e1 e2 
         (EQ1: se (Eplus e1 (Eneg e2)) = Eplus (se e1) (Eneg (se e2)))
         (EQ2: se (Eplus e2 (Eneg e1)) = Eplus (se e2) (Eneg (se e1)))
         (EQ3: se (Enum 0) = Enum 0)
         (EQ4: se (Enum 1) = Enum 1),
    subs (not_equal e1 e2) se = not_equal (se e1) (se e2).
Proof.
  unfold not_equal.
  simpl.
  intros.
  rewrite EQ1, EQ2, EQ3, EQ4.
  reflexivity.
Qed.

Opaque not_equal.


(** # <font size="5"><b> Queues </b></font> # *)

Definition new_queue (q nd tmp: Z) :=
  Let q (Cons 2)
  (Let nd (Cons 2)
  (Let tmp (Mutate (Evar q) (Evar nd))
  (Let tmp (Mutate (Eplus (Evar q) (Enum 1)) (Evar nd))
  (Val (Evar q))))).

Definition enqueue (q: exp) (value: Z) (nd rear tmp: Z) :=
  Let nd (Cons 2)
  (Let rear (Lookup (Eplus q (Enum 1)))
  (Let tmp (Mutate (Evar rear) (Evar nd))
  (Let tmp (Mutate (Eplus (Evar rear) (Enum 1)) (Enum value))
  (Mutate (Eplus q (Enum 1)) (Evar nd))))).

Definition dequeue (q: exp) (front next_front tmp: Z) :=
  Let front (Lookup q)
  (Let next_front (Lookup (Evar front)) 
  (Let tmp (Mutate q (Evar next_front))
  (Lookup (Eplus (Evar front) (Enum 1))))).

Definition size_of (q: exp) (size last front rear lastval nextnode incv tmp: Z) :=
  Let size (Cons 1)
  (Let last (Cons 1)
  (Let front (Lookup q)
  (Let tmp (Mutate (Evar last) (Evar front))
  (Let rear (Lookup (Eplus q (Enum 1)))
  (Let tmp (While (Let lastval (Lookup (Evar last)) (not_equal (Evar lastval) (Evar rear)))
              (Let lastval (Lookup (Evar last))
              (Let nextnode (Lookup (Evar lastval))
              (Let tmp (Mutate (Evar last) (Evar nextnode))
              (inc (Evar size) incv)))))
  (Lookup (Evar size))))))).

Fixpoint nodes (front: exp) (rear: exp) (size: nat) :=
  match size with
    | O => Abool (Z.eqb ([[front]]) ([[rear]]))
    | S n => EX next, (EX value,
             cell_loc front |-> (Enum next) ** 
             next_loc (cell_loc front) |-> (Enum value) ** 
             (nodes (Enum next) rear n))
  end.

Lemma nodes_move:
  forall size size' front rear,
    (EX mid, nodes front (Enum mid) size ** nodes (Enum mid) rear (S size')) |=
    (EX mid, nodes front (Enum mid) (S size) ** nodes (Enum mid) rear size').
Proof.
  induction size.
  {
  unfold nodes.
  intros.
  destruct SAT as (mid,SAT).
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ,SAT).
  apply Z.eqb_eq in EQ.
  simpl in EQ.
  rewrite <- EQ in *.
  destruct SAT as (next,SAT).
  exists next.
  apply rule_exists_dist'; try assumption.
  exists next.
  apply rule_exists_dist'; try assumption.
  destruct SAT as (value,SAT).
  exists value.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (cell_loc (Enum ([[front]])) |-> Enum next)
         (next_loc (cell_loc (Enum ([[front]]))) |-> Enum value **
         nodes (Enum next) rear size'); try assumption.
  intros. assumption.
  intros.
  apply sat_star_imps with (next_loc (cell_loc (Enum ([[front]]))) |-> Enum value)
          (nodes (Enum next) rear size'); try assumption.
  intros.
  apply rule_pure_star; try assumption.
  split; try assumption.
  apply Z.eqb_eq. reflexivity.
  intros. assumption.
  }
  intros.
  destruct SAT as (mid,SAT).
  unfold nodes at 1 in SAT.
  fold nodes in SAT.
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (next,SAT).

  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (value,SAT).
  unfold nodes at 1. fold nodes.
  assert (G: sat p o g
        (cell_loc front |-> Enum next **
          next_loc (cell_loc front) |-> Enum value ** 
(EX mid, nodes (Enum next) (Enum mid) (S size) ** nodes (Enum mid) rear size'))).
{
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (cell_loc front |-> Enum next)
         ((next_loc (cell_loc front) |-> Enum value **
          nodes (Enum next) (Enum mid) size) **
         nodes (Enum mid) rear (S size')); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc in SAT0; try assumption.

  apply sat_star_imps with (next_loc (cell_loc front) |-> Enum value)
          (nodes (Enum next) (Enum mid) size ** nodes (Enum mid) rear (S size')); try assumption.
  intros. assumption.
  intros.
  apply IHsize; try assumption.
  exists mid; assumption.
  }
  apply rule_assoc' in G; try assumption.
  apply rule_exists_dist1 in G; try assumption.
  destruct G as (mid0,G).
  exists mid0.
  apply rule_exists_dist'; try assumption.
  exists next.
  apply rule_exists_dist'; try assumption.
  exists value.
  apply rule_assoc'; try assumption.
  apply rule_assoc in G; try assumption.
  apply sat_star_imps with (cell_loc front |-> Enum next)
       (next_loc (cell_loc front) |-> Enum value **
       nodes (Enum next) (Enum mid0) (S size) ** nodes (Enum mid0) rear size'); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc'; try assumption.
Qed.

Lemma nodes_open:
  forall size front rear (NEQ: ([[front]]) <> ([[rear]])),
    nodes front rear size |= EX next, (EX value,
             cell_loc front |-> (Enum next) **
             next_loc (cell_loc front) |-> (Enum value) ** 
             (nodes (Enum next) rear (size-1))).
Proof.
  destruct size.
  intros.
  simpl in SAT.
  apply Z.eqb_eq in SAT.
  contradiction.
  intros.
  replace (S size - 1)%nat with size.
  assumption.
  omega.
Qed.

Lemma nodes_next:
 forall size front mid mid_next mid_val,
   (nodes front mid size ** cell_loc mid |-> mid_next **
   next_loc (cell_loc mid) |-> mid_val) |=
   (nodes front mid_next (S size)).
Proof.
  induction size.
  {
  unfold nodes. fold nodes.
  intros.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ, SAT).
  apply Z.eqb_eq in EQ. simpl in EQ.
  exists ([[mid_next]]).
  exists ([[mid_val]]).
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_pure_star'; try assumption.
  split.
  apply Z.eqb_eq; reflexivity.
  apply sat_star_imps with (cell_loc mid |-> mid_next) (next_loc (cell_loc mid) |-> mid_val); try assumption.
  intros. apply cell_loc_eval with mid; try assumption. symmetry. assumption.
  intros. apply cell_loc_eval1 with mid; try assumption. symmetry. assumption.
  }
  {
  intros.
  unfold nodes in SAT. fold nodes in SAT.
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (next,SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (value,SAT).
  unfold nodes. fold nodes.
  exists next. exists value.
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (cell_loc front |-> Enum next)
         ((next_loc (cell_loc front) |-> Enum value ** nodes (Enum next) mid size) **
         cell_loc mid |-> mid_next ** next_loc (cell_loc mid) |-> mid_val); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc in SAT0; try assumption.
  apply sat_star_imps with (next_loc (cell_loc front) |-> Enum value)
          (nodes (Enum next) mid size **
          cell_loc mid |-> mid_next ** next_loc (cell_loc mid) |-> mid_val); try assumption.
  intros. assumption.
  apply IHsize.
  }
Qed.

Lemma nodes_eval:
  forall size front front' rear (EQ: ([[front]]) = ([[front']])),
    nodes front rear size |= nodes front' rear size.
Proof.
  induction size.
  unfold nodes. fold nodes.
  intros.
  rewrite EQ in *. assumption.
  unfold nodes. fold nodes.
  intros.
  destruct SAT as (next, SAT).
  destruct SAT as (value, SAT).
  exists next.
  exists value.
  apply rule_assoc; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply sat_star_imps with (cell_loc front |-> Enum next **
          next_loc (cell_loc front) |-> Enum value)
         (nodes (Enum next) rear size); try assumption.
  intros.
  apply sat_star_imps with (cell_loc front |-> Enum next)
   (next_loc (cell_loc front) |-> Enum value); try assumption.
  intros.
  apply cell_loc_eval with front; try assumption.
  intros.
  apply cell_loc_eval1 with front; try assumption.
  intros.
  apply IHsize with (Enum next); try assumption. reflexivity.
Qed.

Lemma nodes_eval':
  forall size front rear rear' (EQ: ([[rear]]) = ([[rear']])),
    nodes front rear size |= nodes front rear' size.
Proof.
  induction size.
  unfold nodes. fold nodes.
  intros.
  rewrite EQ in *. assumption.
  unfold nodes. fold nodes.
  intros.
  destruct SAT as (next, SAT).
  destruct SAT as (value, SAT).
  exists next.
  exists value.
  apply rule_assoc; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply sat_star_imps with (cell_loc front |-> Enum next **
          next_loc (cell_loc front) |-> Enum value)
         (nodes (Enum next) rear size); try assumption.
  intros.
  apply sat_star_imps with (cell_loc front |-> Enum next)
   (next_loc (cell_loc front) |-> Enum value); try assumption.
  intros. assumption.
  intros. assumption.
  intros.  
  apply IHsize with rear; try assumption.
Qed.

Lemma nodes_move':
  forall size size' front rear mid,
    nodes front mid (S size) ** nodes mid rear size' |=
    (EX mid, nodes front mid size ** nodes mid rear (S size')).
Proof.
  induction size.
  {
  unfold nodes. fold nodes.
  intros.
  exists front.
  apply rule_pure_star'; try assumption.
  split.
  apply Z.eqb_eq; try reflexivity.
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (next,SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (value,SAT).
  exists next.
  exists value.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ,SAT).
  apply Z.eqb_eq in EQ. simpl in EQ.
  rewrite EQ in *.
  apply rule_assoc in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (cell_loc front |-> Enum ([[mid]]) **
          next_loc (cell_loc front) |-> Enum value)
         (nodes mid rear size'); try assumption.
  intros. assumption.
  intros.
  apply nodes_eval with mid; try assumption; try reflexivity.
  }
  {
  intros.
  unfold nodes at 1 in SAT. fold nodes in SAT.
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (next,SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (value,SAT).

  assert (G: sat p o g
        (cell_loc front |-> Enum next **
          next_loc (cell_loc front) |-> Enum value **
          nodes (Enum next) mid (S size) ** nodes mid rear size')).
  {
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (cell_loc front |-> Enum next)
         ((next_loc (cell_loc front) |-> Enum value **
          (EX next0,
           (EX value,
            cell_loc (Enum next) |-> Enum next0 **
            next_loc (cell_loc (Enum next)) |-> Enum value **
            nodes (Enum next0) mid size))) ** nodes mid rear size'); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc in SAT0; try assumption.
  }

  assert (G': sat p o g (cell_loc front |-> Enum next **
       next_loc (cell_loc front) |-> Enum value **
    (EX mid0, nodes (Enum next) mid0 size ** nodes mid0 rear (S size')))).
  {
  apply rule_assoc; try assumption.
  apply rule_assoc' in G; try assumption.
  apply sat_star_imps with (cell_loc front |-> Enum next ** next_loc (cell_loc front) |-> Enum value)
       (nodes (Enum next) mid (S size) ** nodes mid rear size'); try assumption.
  intros. assumption. eapply IHsize; try assumption.
  }
  apply rule_assoc' in G'; try assumption.
  apply rule_comm in G'; try assumption.
  apply rule_exists_dist in G'; try assumption.
  destruct G' as (mid',G').
  exists mid'.
  apply rule_comm in G'; try assumption.
  apply rule_assoc' in G'; try assumption.
  apply sat_star_imps with ((cell_loc front |-> Enum next ** next_loc (cell_loc front) |-> Enum value) **
         nodes (Enum next) mid' size) (nodes mid' rear (S size')); try assumption.
  intros. unfold nodes. fold nodes.
  exists next.
  exists value.
  apply rule_assoc; try assumption.
  intros. assumption.
  }
Qed.

Lemma nodes_merge:
  forall n size front mid rear (LE: le n size),
    nodes front mid n ** nodes mid rear (size - n) |=
    nodes front rear size.
Proof.
  induction n.
  {
  unfold nodes. fold nodes.
  intros.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ,SAT).
  apply Z.eqb_eq in EQ. simpl in EQ.
  apply nodes_eval with mid; try assumption.
  symmetry. assumption. replace size with (size - 0)%nat. assumption. omega.
  }
  intros.
  apply nodes_move' in SAT; try assumption.
  destruct SAT as (mid1,SAT).
  destruct (Nat.leb n size) eqn:LEN.
  apply Nat.leb_le in LEN.
  {
  apply IHn with mid1; try assumption.
  replace (size - n)%nat with (S (size - S n))%nat.
  assumption.
  omega.
  }
  apply nat_leb_falseL in LEN.
  omega.
Qed.

Lemma node_in:
  forall n front rear value z,
    nodes (Enum front) (Enum rear) n **
    cell_loc (Eplus (Enum rear) (Enum 1)) |-> Enum value **
    cell_loc (Enum rear) |-> Enum z |=
    nodes (Enum front) (Enum z) (S n).
Proof.
  induction n.
  intros.
  unfold nodes in *.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ,SAT).
  apply Z.eqb_eq in EQ.
  exists z, value.
  {
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_pure_star'; try assumption.
  split.
  apply Z.eqb_eq. reflexivity.
  apply rule_comm; try assumption.

  apply sat_star_imps with (cell_loc (Eplus (Enum rear) (Enum 1)) |-> Enum value)
         (cell_loc (Enum rear) |-> Enum z); try assumption.
  intros.
  apply rule_trans with (cell_loc (Eplus (Enum rear) (Enum 1)) |-> Enum value)
    (next_loc (cell_loc (Enum rear)) |-> Enum value); try assumption.
  split; intros. assumption.
  apply cell_loc_eval1 with (Enum rear); try assumption. symmetry. assumption.
  intros.
  apply cell_loc_eval with (Enum rear); try assumption. symmetry. assumption.
  }
  intros.
  unfold nodes in SAT.
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (next1,SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (value1,SAT).
  exists next1, value1.
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (cell_loc (Enum front) |-> Enum next1)
         ((next_loc (cell_loc (Enum front)) |-> Enum value1 **
          nodes (Enum next1) (Enum rear) n) **
         cell_loc (Eplus (Enum rear) (Enum 1)) |-> Enum value ** cell_loc (Enum rear) |-> Enum z); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc in SAT0; try assumption.
  apply sat_star_imps with (next_loc (cell_loc (Enum front)) |-> Enum value1)
          (nodes (Enum next1) (Enum rear) n **
          cell_loc (Eplus (Enum rear) (Enum 1)) |-> Enum value **
          cell_loc (Enum rear) |-> Enum z); try assumption.
  intros. assumption.
  intros.
  eapply IHn; try assumption.
  apply SAT1.
Qed.

Definition queue (q: Z) (size: nat) :=
  EX front, (EX rear, (EX last_value, (
  cell_loc (Enum q) |-> (Enum front) **
  next_loc (cell_loc (Enum q)) |-> (Enum rear) **
  cell_loc (Enum rear) |-> Enum 0 ** 
  next_loc (cell_loc (Enum rear)) |-> (Enum last_value) **
  nodes (Enum front) (Enum rear) size))).

Theorem rule_new_queue invs sp q nd tmp (NODUP: NoDup (q::nd::tmp::nil)): correct
  (Abool true)
  (new_queue q nd tmp)
  (fun q => queue q O) invs sp.
Proof.
  unfold queue.
  apply rule_Let with (fun l => fold_left Astar (points_tos (seq 0 2)(cell_loc (Enum l))) (Abool true)).
  apply rule_Cons.
  simpl.
  intros.
  apply rule_Let with (fun l => fold_left Astar (points_tos (seq 0 2)(cell_loc (Enum l))) (Abool true) **
    array (cell_loc (Enum z)) 0 |-> Enum 0 ** array (cell_loc (Enum z)) 1 |-> Enum 0).
  simpl.
  apply rule_conseq1 with ((Abool true ** (array (cell_loc (Enum z)) 0 |-> Enum 0) **
   array (cell_loc (Enum z)) 1 |-> Enum 0)).
  apply rule_frame.
  apply rule_Cons.
  intros.
  apply rule_assoc; try assumption.
  intros.
  simpl.
  apply rule_Let with (fun _ => cell_loc (Enum z) |-> Enum z0 ** 
  (next_loc (cell_loc (Enum z)) |-> Enum 0 **
  cell_loc (Enum z0) |-> Enum 0 **
  next_loc (cell_loc (Enum z0)) |-> Enum 0)).
  apply rule_conseq1 with (cell_loc (Enum z) |-> Enum 0 ** 
  (next_loc (cell_loc (Enum z)) |-> Enum 0 **
  cell_loc (Enum z0) |-> Enum 0 **
  next_loc (cell_loc (Enum z0)) |-> Enum 0)).
  rewrite eqz.
  rewrite neqz; try assumption.
  simpl.
  rewrite eqz.
  apply rule_frame.
  apply rule_Mutate.
  eapply nodup_neq. apply NODUP. simpl. tauto.
  intros.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT1,SAT).
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  {
  apply sat_star_imps with (array (cell_loc (Enum z0)) 0 |-> Enum 0)
    (array (cell_loc (Enum z0)) 1 |-> Enum 0 **
         array (cell_loc (Enum z)) 0 |-> Enum 0 **
         array (cell_loc (Enum z)) 1 |-> Enum 0); try assumption.
  intros.
  apply sat_array; assumption.
  intros.
  apply sat_star_imps with (array (cell_loc (Enum z0)) 1 |-> Enum 0)
         (array (cell_loc (Enum z)) 0 |-> Enum 0 **
         array (cell_loc (Enum z)) 1 |-> Enum 0); try assumption.
  intros.
  apply sat_array1; assumption.
  intros.
  apply sat_star_imps with (array (cell_loc (Enum z)) 0 |-> Enum 0)
         (array (cell_loc (Enum z)) 1 |-> Enum 0); try assumption.
  intros.
  apply sat_array; assumption.
  intros.
  apply sat_array1; assumption.
  }
  simpl.
  intros.
  apply rule_Let with (fun _ => next_loc (cell_loc (Enum z)) |-> Enum z0 **
  (cell_loc (Enum z) |-> Enum z0 **
  cell_loc (Enum z0) |-> Enum 0 **
  next_loc (cell_loc (Enum z0)) |-> Enum 0)).
  apply rule_conseq1 with (next_loc (cell_loc (Enum z)) |-> Enum 0 **
  (cell_loc (Enum z) |-> Enum z0 **
  cell_loc (Enum z0) |-> Enum 0 **
  next_loc (cell_loc (Enum z0)) |-> Enum 0)).
  rewrite eqz.
  rewrite neqz; try assumption.
  simpl.
  rewrite eqz.
  simpl.
  apply rule_frame.
  apply rule_Mutate.
  eapply nodup_neq. apply NODUP. simpl. tauto.
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply sat_star_imps with (cell_loc (Enum z) |-> Enum z0 **
    next_loc (cell_loc (Enum z)) |-> Enum 0)
    (cell_loc (Enum z0) |-> Enum 0 **
         next_loc (cell_loc (Enum z0)) |-> Enum 0); try assumption.
  intros. apply rule_comm; assumption.
  intros. assumption.
  simpl.
  intros.
  apply rule_exists2.
  exists z0.
  apply rule_exists2.
  exists z0.
  apply rule_exists2.
  exists 0.
  rewrite eqz.
  simpl.
  apply rule_conseq with (Abool true ** (cell_loc (Enum z) |-> Enum z0 **
  next_loc (cell_loc (Enum z)) |-> Enum z0 **
  cell_loc (Enum z0) |-> Enum 0 **
  next_loc (cell_loc (Enum z0)) |-> Enum 0))
  (fun z' => Abool (Z.eqb z' ([[Enum z]])) **
  (cell_loc (Enum z) |-> Enum z0 **
  next_loc (cell_loc (Enum z)) |-> Enum z0 **
  cell_loc (Enum z0) |-> Enum 0 **
  next_loc (cell_loc (Enum z0)) |-> Enum 0)).
  simpl.
  apply rule_frame.
  apply rule_Val.
  intros.
  apply rule_comm; try assumption.
  apply rule_pure_star; try assumption.
  split.
  apply rule_assoc; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply sat_star_imps with (next_loc (cell_loc (Enum z)) |-> Enum z0 **
    cell_loc (Enum z) |-> Enum z0)
    (cell_loc (Enum z0) |-> Enum 0 ** next_loc (cell_loc (Enum z0)) |-> Enum 0); try assumption.
  intros. apply rule_comm; try assumption.
  intros. assumption. simpl. trivial.
  intros.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ,SAT).
  apply Z.eqb_eq in EQ.
  rewrite EQ in *.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_pure_star; try assumption.
  split.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply Z.eqb_eq.
  reflexivity.
Qed.

Theorem rule_enqueue invs sp q value n ndv rearv tmpv (NODUP: NoDup(ndv::rearv::tmpv::nil))
                     (NOTFREE: is_free_e q rearv = false /\ is_free_e q tmpv = false /\ is_free_e q ndv = false): correct
  (queue ([[q]]) n)
  (enqueue q value ndv rearv tmpv)
  (fun _ => queue ([[q]]) (S n)) invs sp.
Proof.
  destruct NOTFREE as (NF1,(NF2,NF3)).
  unfold queue.
  simpl.
  apply rule_exists1.
  intros front.
  apply rule_exists1.
  intros rear.
  apply rule_exists1.
  intros last_value.
  apply rule_Let with (fun r' => fold_left Astar (points_tos (seq 0 2)(cell_loc (Enum r'))) (Abool true) **
   cell_loc q |-> Enum front **
   next_loc (cell_loc q) |-> Enum rear **
   cell_loc (Enum rear) |-> Enum 0 **
   next_loc (cell_loc (Enum rear)) |-> Enum last_value ** nodes (Enum front) (Enum rear) n).
  apply rule_conseq1 with (Abool true ** cell_loc q |-> Enum front **
   next_loc (cell_loc q) |-> Enum rear **
   cell_loc (Enum rear) |-> Enum 0 **
   next_loc (cell_loc (Enum rear)) |-> Enum last_value ** nodes (Enum front) (Enum rear) n).
  apply rule_frame.
  apply rule_Cons.
  intros.
  apply rule_pure_star'; try assumption.
  split.
  simpl. trivial. assumption.
  simpl.
  intros.
  rewrite subse_free; try assumption.
  rewrite eqz.
  rewrite neqz; try assumption.
  apply rule_Let with (fun z' => (Abool (z' =? ([[Enum rear]])) &*
    cell_loc (Eplus q (Enum 1)) |-> Enum rear) **
    cell_loc (Enum z) |-> Enum 0 **
    next_loc (cell_loc (Enum z)) |-> Enum 0 **
    cell_loc q |-> Enum front **
    cell_loc (Enum rear) |-> Enum 0 **
    next_loc (cell_loc (Enum rear)) |-> Enum last_value ** nodes (Enum front) (Enum rear) n).
  apply rule_conseq1 with (cell_loc (Eplus q (Enum 1)) |-> Enum rear **
    cell_loc (Enum z) |-> Enum 0 **
    next_loc (cell_loc (Enum z)) |-> Enum 0 **
    cell_loc q |-> Enum front **
    cell_loc (Enum rear) |-> Enum 0 **
    next_loc (cell_loc (Enum rear)) |-> Enum last_value ** nodes (Enum front) (Enum rear) n).
  apply rule_frame.
  apply rule_Lookup.
  {
  intros.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ,SAT).
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply sat_star_imps with (((array (cell_loc (Enum z)) 0 |-> Enum 0 **
            array (cell_loc (Enum z)) 1 |-> Enum 0) **
           cell_loc q |-> Enum front) **
          next_loc (cell_loc q) |-> Enum rear)
         (cell_loc (Enum rear) |-> Enum 0 **
         next_loc (cell_loc (Enum rear)) |-> Enum last_value **
         nodes (Enum front) (Enum rear) n); try assumption.
  intros.
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply sat_star_imps with (next_loc (cell_loc q) |-> Enum rear **
           array (cell_loc (Enum z)) 0 |-> Enum 0 **
           array (cell_loc (Enum z)) 1 |-> Enum 0)
          (cell_loc q |-> Enum front); try assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (next_loc (cell_loc q) |-> Enum rear)
          (array (cell_loc (Enum z)) 0 |-> Enum 0 **
          array (cell_loc (Enum z)) 1 |-> Enum 0); try assumption.
  intros. assumption.
  intros.
  apply sat_star_imps with (array (cell_loc (Enum z)) 0 |-> Enum 0)
          (array (cell_loc (Enum z)) 1 |-> Enum 0); try assumption.
  intros.
  apply sat_array; try assumption.
  intros.
  apply sat_array1; try assumption.
  intros. assumption.
  intros. assumption.
  }
  simpl.
  intros.
  rewrite eqz.
  apply rule_Let with (fun _ => cell_loc (Enum z0) |-> Enum z **
   (Abool (z0 =? ([[Enum rear]])) ** cell_loc (Eplus q (Enum 1)) |-> Enum rear **
   cell_loc (Enum z) |-> Enum 0 **
   next_loc (cell_loc (Enum z)) |-> Enum 0 **
   cell_loc q |-> Enum front **
   next_loc (cell_loc (Enum rear)) |-> Enum last_value ** nodes (Enum front) (Enum rear) n)).
  apply rule_conseq1 with (cell_loc (Enum z0) |-> Enum 0 ** 
   (Abool (z0 =? ([[Enum rear]])) ** cell_loc (Eplus q (Enum 1)) |-> Enum rear **
   cell_loc (Enum z) |-> Enum 0 **
   next_loc (cell_loc (Enum z)) |-> Enum 0 **
   cell_loc q |-> Enum front **
   next_loc (cell_loc (Enum rear)) |-> Enum last_value ** nodes (Enum front) (Enum rear) n)).
  apply rule_frame.
  apply rule_Mutate.
  {
  intros.
  apply rule_assoc_pure in SAT; try assumption.
  destruct SAT as (EQ,SAT).
  apply Z.eqb_eq in EQ.
  rewrite EQ in *.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_pure_star'; try assumption.
  split.
  apply Z.eqb_eq; reflexivity.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (cell_loc (Eplus q (Enum 1)) |-> Enum rear)
         (cell_loc (Enum z) |-> Enum 0 **
         next_loc (cell_loc (Enum z)) |-> Enum 0 **
         cell_loc q |-> Enum front **
         cell_loc (Enum rear) |-> Enum 0 **
         next_loc (cell_loc (Enum rear)) |-> Enum last_value **
         nodes (Enum front) (Enum rear) n); try assumption.
  intros. assumption.
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (((cell_loc (Enum z) |-> Enum 0 **
             next_loc (cell_loc (Enum z)) |-> Enum 0) **
            cell_loc q |-> Enum front) **
           cell_loc (Enum rear) |-> Enum 0)
          (next_loc (cell_loc (Enum rear)) |-> Enum last_value **
          nodes (Enum front) (Enum rear) n); try assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_comm; try assumption.
  apply sat_star_imps with ((cell_loc (Enum z) |-> Enum 0 **
            next_loc (cell_loc (Enum z)) |-> Enum 0) **
           cell_loc q |-> Enum front) (cell_loc (Enum rear) |-> Enum 0); try assumption.
  intros.
  apply rule_assoc in SAT2; try assumption.
  intros. assumption.
  intros. assumption.
  }
  intros.
  simpl.
  rewrite subse_free; try assumption.
  apply rule_Let with (fun _ => cell_loc (Eplus (Enum z0) (Enum 1)) |-> (Enum value) **
    (cell_loc (Enum z0) |-> Enum z **
    Abool (z0 =? ([[Enum rear]])) **
    cell_loc (Eplus q (Enum 1)) |-> Enum rear **
    cell_loc (Enum z) |-> Enum 0 **
    next_loc (cell_loc (Enum z)) |-> Enum 0 **
    cell_loc q |-> Enum front **
    nodes (Enum front) (Enum rear) n)).
  apply rule_conseq1 with (cell_loc (Eplus (Enum z0) (Enum 1)) |-> Enum last_value **
   (cell_loc (Enum z0) |-> Enum z **
   Abool (z0 =? ([[Enum rear]])) **
    cell_loc (Eplus q (Enum 1)) |-> Enum rear **
    cell_loc (Enum z) |-> Enum 0 **
    next_loc (cell_loc (Enum z)) |-> Enum 0 **
    cell_loc q |-> Enum front **
    nodes (Enum front) (Enum rear) n)).
  apply rule_frame.
  apply rule_Mutate.
  {
  intros.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ,SAT).
  apply Z.eqb_eq in EQ.
  rewrite EQ in *.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_pure_star'; try assumption.
  split.
  apply Z.eqb_eq. reflexivity.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (cell_loc (Eplus q (Enum 1)) |-> Enum rear **
          cell_loc (Enum z) |-> Enum 0 **
          next_loc (cell_loc (Enum z)) |-> Enum 0 **
          cell_loc q |-> Enum front **
          next_loc (cell_loc (Enum rear)) |-> Enum last_value **
          nodes (Enum front) (Enum rear) n)
         (cell_loc (Enum rear) |-> Enum z); try assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (cell_loc (Eplus q (Enum 1)) |-> Enum rear)
          (cell_loc (Enum z) |-> Enum 0 **
          next_loc (cell_loc (Enum z)) |-> Enum 0 **
          cell_loc q |-> Enum front **
          next_loc (cell_loc (Enum rear)) |-> Enum last_value **
          nodes (Enum front) (Enum rear) n); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (cell_loc (Enum z) |-> Enum 0)
          (next_loc (cell_loc (Enum z)) |-> Enum 0 **
          cell_loc q |-> Enum front **
          next_loc (cell_loc (Enum rear)) |-> Enum last_value **
          nodes (Enum front) (Enum rear) n); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (next_loc (cell_loc (Enum z)) |-> Enum 0)
          (cell_loc q |-> Enum front **
          next_loc (cell_loc (Enum rear)) |-> Enum last_value **
          nodes (Enum front) (Enum rear) n); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (cell_loc q |-> Enum front)
          (next_loc (cell_loc (Enum rear)) |-> Enum last_value **
          nodes (Enum front) (Enum rear) n); try assumption.
  intros. assumption.
  intros. apply rule_comm; try assumption.
  intros. assumption.
  }
  intros.
  simpl.
  rewrite subse_free; try assumption.
  rewrite subse_free; try assumption.
  apply rule_exists2.
  exists front.
  apply rule_exists2.
  exists z.
  apply rule_exists2.
  exists 0.
  apply rule_conseq1 with (cell_loc (Eplus q (Enum 1)) |-> Enum rear **
    cell_loc q |-> Enum front ** 
    cell_loc (Enum z) |-> Enum 0 **
    next_loc (cell_loc (Enum z)) |-> Enum 0 **
    nodes (Enum front) (Enum z) (S n)).
  simpl.
  apply rule_conseq2 with (fun _ => next_loc (cell_loc q) |-> Enum z **
   cell_loc q |-> Enum front **
   cell_loc (Enum z) |-> Enum 0 **
   next_loc (cell_loc (Enum z)) |-> Enum 0 **
   (EX next,
    (EX value0,
     cell_loc (Enum front) |-> (Enum next) **
     next_loc (cell_loc (Enum front)) |-> Enum value0 ** nodes (Enum next) (Enum z) n))).
  apply rule_frame.
  apply rule_Mutate.
  {
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply sat_star_imps with (next_loc (cell_loc q) |-> Enum z ** cell_loc q |-> Enum front)
         (cell_loc (Enum z) |-> Enum 0 **
         next_loc (cell_loc (Enum z)) |-> Enum 0 **
         (EX next,
          (EX value0,
           cell_loc (Enum front) |-> Enum next **
           next_loc (cell_loc (Enum front)) |-> Enum value0 **
           nodes (Enum next) (Enum z) n))); try assumption.
  intros.
  apply rule_comm; try assumption.
  intros. assumption.
  }
  {
  intros.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (cell_loc (Eplus q (Enum 1)) |-> Enum rear)
         ((cell_loc (Enum z) |-> Enum 0 **
          next_loc (cell_loc (Enum z)) |-> Enum 0 **
          cell_loc q |-> Enum front ** nodes (Enum front) (Enum rear) n) **
         (cell_loc (Eplus (Enum z0) (Enum 1)) |-> Enum value **
          cell_loc (Enum z0) |-> Enum z) ** Abool (z0 =? rear)); try assumption.
  intros. assumption.
  intros.
  assert (G': sat p0 o0 g0 ((cell_loc q |-> Enum front ** 
           cell_loc (Enum z) |-> Enum 0 **
           next_loc (cell_loc (Enum z)) |-> Enum 0 **
           nodes (Enum front) (Enum rear) n) **
          ((cell_loc (Eplus (Enum z0) (Enum 1)) |-> Enum value **
           cell_loc (Enum z0) |-> Enum z) ** Abool (z0 =? rear)))).
  {
  apply sat_star_imps with (cell_loc (Enum z) |-> Enum 0 **
           next_loc (cell_loc (Enum z)) |-> Enum 0 **
           cell_loc q |-> Enum front **
           nodes (Enum front) (Enum rear) n)
          ((cell_loc (Eplus (Enum z0) (Enum 1)) |-> Enum value **
           cell_loc (Enum z0) |-> Enum z) ** 
          Abool (z0 =? rear)); try assumption.
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply sat_star_imps with ((cell_loc (Enum z) |-> Enum 0 ** next_loc (cell_loc (Enum z)) |-> Enum 0) **
           cell_loc q |-> Enum front) (nodes (Enum front) (Enum rear) n); try assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply rule_comm; try assumption.
  intros. assumption.
  intros. assumption.
  }
  apply rule_assoc in G'; try assumption.
  apply sat_star_imps with (cell_loc q |-> Enum front)
   ((cell_loc (Enum z) |-> Enum 0 **
   next_loc (cell_loc (Enum z)) |-> Enum 0 **
   nodes (Enum front) (Enum rear) n) **
        (cell_loc (Eplus (Enum z0) (Enum 1)) |-> Enum value **
         cell_loc (Enum z0) |-> Enum z) ** Abool (z0 =? rear)); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc in SAT1; try assumption.
  apply sat_star_imps with (cell_loc (Enum z) |-> Enum 0)
          ((next_loc (cell_loc (Enum z)) |-> Enum 0 **
           nodes (Enum front) (Enum rear) n) **
          (cell_loc (Eplus (Enum z0) (Enum 1)) |-> Enum value **
           cell_loc (Enum z0) |-> Enum z) ** 
          Abool (z0 =? rear)); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc in SAT2; try assumption.
  apply sat_star_imps with (next_loc (cell_loc (Enum z)) |-> Enum 0)
          (nodes (Enum front) (Enum rear) n **
          (cell_loc (Eplus (Enum z0) (Enum 1)) |-> Enum value **
           cell_loc (Enum z0) |-> Enum z) ** 
          Abool (z0 =? rear)); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_comm in SAT3; try assumption.
  apply rule_star_pure in SAT3; try assumption.
  destruct SAT3 as (EQ3,SAT3).
  apply Z.eqb_eq in EQ3.
  rewrite EQ3 in *.
  eapply node_in; try assumption. apply SAT3.
  }
  apply is_free_subse; assumption.
  apply is_free_subse; assumption.
  eapply nodup_neq. apply NODUP. simpl. tauto.
Qed.

Theorem rule_dequeue invs sp q n frontv next_frontv tmpv (NODUP: NoDup(frontv::next_frontv::tmpv::nil))
                     (NOTFREE: is_free_e q frontv = false /\ is_free_e q next_frontv = false): correct
  (queue ([[q]]) (S n))
  (dequeue q frontv next_frontv tmpv)
  (fun _ => queue ([[q]]) n) invs sp.
Proof.
  destruct NOTFREE as (NF1,NF2).
  unfold queue.
  simpl.
  apply rule_exists1.
  intros front.
  apply rule_exists1.
  intros rear.
  apply rule_exists1.
  intros last_value.
  apply rule_Let with (fun z' => (Abool (Z.eqb z' ([[Enum front]])) &* 
  cell_loc q |-> Enum front) ** 
  next_loc (cell_loc q) |-> Enum rear **
  cell_loc (Enum rear) |-> Enum 0 ** 
  next_loc (cell_loc (Enum rear)) |-> Enum last_value **
  (EX next, (EX value, cell_loc (Enum front) |-> Enum next **
  next_loc (cell_loc (Enum front)) |-> Enum value ** nodes (Enum next) (Enum rear) n))).
  apply rule_conseq1 with (cell_loc q |-> Enum front ** 
  next_loc (cell_loc q) |-> Enum rear **
  cell_loc (Enum rear) |-> Enum 0 ** 
  next_loc (cell_loc (Enum rear)) |-> Enum last_value **
  (EX next, (EX value, cell_loc (Enum front) |-> Enum next **
  next_loc (cell_loc (Enum front)) |-> Enum value ** nodes (Enum next) (Enum rear) n))).
  apply rule_frame.
  apply rule_Lookup.
  intros. assumption.
  simpl.
  intros.
  rewrite eqz.
  simpl.
  rewrite neqz; try omega.
  apply rule_conseq1 with (EX next,
  (EX value, ((Abool (z =? ([[Enum front]])) &* cell_loc q |-> Enum front) **
  next_loc (cell_loc q) |-> Enum rear **
  cell_loc (Enum rear) |-> Enum 0 **
  next_loc (cell_loc (Enum rear)) |-> Enum last_value **
  cell_loc (Enum front) |-> Enum next **
  next_loc (cell_loc (Enum front)) |-> Enum value ** nodes (Enum next) (Enum rear) n))).
  apply rule_exists1.
  intros next.
  apply rule_exists1.
  intros value.
  apply rule_Let with (fun z' => (Abool (z' =? ([[Enum next]])) &* 
  cell_loc (Enum z) |-> Enum next) **
  ((Abool (z =? ([[Enum front]])) &* cell_loc q |-> Enum front) **
  next_loc (cell_loc q) |-> Enum rear **
  cell_loc (Enum rear) |-> Enum 0 **
  next_loc (cell_loc (Enum rear)) |-> Enum last_value **  
  next_loc (cell_loc (Enum front)) |-> Enum value ** nodes (Enum next) (Enum rear) n)).
  apply rule_conseq1 with (cell_loc (Enum z) |-> Enum next **
  (Abool (z =? ([[Enum front]])) &* cell_loc q |-> Enum front) **
   next_loc (cell_loc q) |-> Enum rear **
   cell_loc (Enum rear) |-> Enum 0 **
   next_loc (cell_loc (Enum rear)) |-> Enum last_value **
   next_loc (cell_loc (Enum front)) |-> Enum value ** nodes (Enum next) (Enum rear) n).
  apply rule_frame.
  apply rule_Lookup.
  {
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply sat_star_imps with ((Abool (z =? ([[Enum front]])) &* cell_loc q |-> Enum front) **
         next_loc (cell_loc q) |-> Enum rear **
         cell_loc (Enum rear) |-> Enum 0 **
         next_loc (cell_loc (Enum rear)) |-> Enum last_value **
         cell_loc (Enum front) |-> Enum next)
         (next_loc (cell_loc (Enum front)) |-> Enum value **
         nodes (Enum next) (Enum rear) n); try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply sat_star_imps with (((((Abool (z =? ([[Enum front]])) &* cell_loc q |-> Enum front) **
             next_loc (cell_loc q) |-> Enum rear) **
            cell_loc (Enum rear) |-> Enum 0) **
           next_loc (cell_loc (Enum rear)) |-> Enum last_value) **
          cell_loc (Enum front) |-> Enum next)
  (next_loc (cell_loc (Enum front)) |-> Enum value **
         nodes (Enum next) (Enum rear) n); try assumption.
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  intros. assumption.
  intros.
  assert (SAT': sat p0 o0 g0
         ((Abool (z =? ([[Enum front]])) ** cell_loc q |-> Enum front) **
          next_loc (cell_loc q) |-> Enum rear **
          cell_loc (Enum rear) |-> Enum 0 **
          next_loc (cell_loc (Enum rear)) |-> Enum last_value **
          cell_loc (Enum front) |-> Enum next)).
  {
  apply sat_star_imps with (Abool (z =? ([[Enum front]])) &* cell_loc q |-> Enum front)
          (next_loc (cell_loc q) |-> Enum rear **
          cell_loc (Enum rear) |-> Enum 0 **
          next_loc (cell_loc (Enum rear)) |-> Enum last_value **
          cell_loc (Enum front) |-> Enum next); try assumption.
  intros.
  apply rule_comm; try assumption.
  apply rule_pure_star; try assumption.
  apply rule_comm_pure; try assumption.
  intros. assumption.
  }
  apply rule_assoc in SAT'; try assumption.
  apply rule_star_pure in SAT'; try assumption.
  destruct SAT' as (EQ,SAT').
  apply Z.eqb_eq in EQ.
  rewrite EQ.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc' in SAT'; try assumption.
  apply rule_assoc' in SAT'; try assumption.
  apply rule_assoc' in SAT'; try assumption.
  apply rule_comm in SAT'; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (cell_loc (Enum front) |-> Enum next **
          ((cell_loc q |-> Enum front ** next_loc (cell_loc q) |-> Enum rear) **
           cell_loc (Enum rear) |-> Enum 0))
          (next_loc (cell_loc (Enum rear)) |-> Enum last_value); try assumption.
  apply rule_assoc'; try assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (cell_loc (Enum front) |-> Enum next)
          ((cell_loc q |-> Enum front ** next_loc (cell_loc q) |-> Enum rear) **
          cell_loc (Enum rear) |-> Enum 0); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc in SAT2; try assumption.
  apply sat_star_imps with (cell_loc q |-> Enum front)
          (next_loc (cell_loc q) |-> Enum rear ** cell_loc (Enum rear) |-> Enum 0); try assumption.
  intros.
  split.
  apply Z.eqb_eq. reflexivity. assumption.
  intros. assumption.
  intros. assumption.
  intros. assumption.
  }
  simpl.
  intros.
  simpl.
  rewrite eqz.
  rewrite subse_free; try assumption.
  rewrite subse_free; try assumption.
  apply rule_Let with (fun _=> cell_loc q |-> Enum z0 ** 
    ((Abool (z0 =? ([[Enum next]])) &* cell_loc (Enum z) |-> Enum next) **
    Abool (z =? ([[Enum front]])) **
    next_loc (cell_loc q) |-> Enum rear **
    cell_loc (Enum rear) |-> Enum 0 **
    next_loc (cell_loc (Enum rear)) |-> Enum last_value **
    next_loc (cell_loc (Enum front)) |-> Enum value ** nodes (Enum next) (Enum rear) n)).
  apply rule_conseq1 with (cell_loc q |-> Enum front **
    ((Abool (z0 =? ([[Enum next]])) &* cell_loc (Enum z) |-> Enum next) **
    Abool (z =? ([[Enum front]])) ** next_loc (cell_loc q) |-> Enum rear **
    cell_loc (Enum rear) |-> Enum 0 ** next_loc (cell_loc (Enum rear)) |-> Enum last_value **
    next_loc (cell_loc (Enum front)) |-> Enum value ** nodes (Enum next) (Enum rear) n)).
  apply rule_frame.
  apply rule_Mutate.
  {
  intros.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with ((Abool (z0 =? next) &* cell_loc (Enum z) |-> Enum next) **
          (Abool (z =? front) &* cell_loc q |-> Enum front))
         (next_loc (cell_loc q) |-> Enum rear **
         cell_loc (Enum rear) |-> Enum 0 **
         next_loc (cell_loc (Enum rear)) |-> Enum last_value **
         next_loc (cell_loc (Enum front)) |-> Enum value **
         nodes (Enum next) (Enum rear) n); try assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Abool (z0 =? next) &* cell_loc (Enum z) |-> Enum next)
          (Abool (z =? front) &* cell_loc q |-> Enum front); try assumption.
  intros. assumption.
  intros. apply rule_pure_star'; try assumption.
  intros. assumption.
  }
  simpl.
  intros.
  apply rule_exists2.
  exists next.
  apply rule_exists2.
  exists rear.
  apply rule_exists2.
  exists last_value.
  apply rule_conseq with
    (cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum value ** 
    cell_loc q |-> Enum next **
    next_loc (cell_loc q) |-> Enum rear **
    cell_loc (Enum rear) |-> Enum 0 **
    next_loc (cell_loc (Enum rear)) |-> Enum last_value **
    nodes (Enum next) (Enum rear) n)
   (fun z' => (Abool (z' =? ([[Enum value]])) &* cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum value) ** 
   cell_loc q |-> Enum next **
   next_loc (cell_loc q) |-> Enum rear **
   cell_loc (Enum rear) |-> Enum 0 **
   next_loc (cell_loc (Enum rear)) |-> Enum last_value ** nodes (Enum next) (Enum rear) n).
  apply rule_frame.
  apply rule_Lookup.
  {
  intros.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  assert (SAT': sat p o g
        ((cell_loc (Enum z) |-> Enum next ** Abool (z0 =? next)) **
         (Abool (z =? front) **
          next_loc (cell_loc q) |-> Enum rear **
          cell_loc (Enum rear) |-> Enum 0 **
          next_loc (cell_loc (Enum rear)) |-> Enum last_value **
          next_loc (cell_loc (Enum front)) |-> Enum value ** nodes (Enum next) (Enum rear) n) **
         cell_loc q |-> Enum z0)).
  {
  apply sat_star_imps with (Abool (z0 =? next) &* cell_loc (Enum z) |-> Enum next)
         ((Abool (z =? front) **
          next_loc (cell_loc q) |-> Enum rear **
          cell_loc (Enum rear) |-> Enum 0 **
          next_loc (cell_loc (Enum rear)) |-> Enum last_value **
          next_loc (cell_loc (Enum front)) |-> Enum value **
          nodes (Enum next) (Enum rear) n) ** cell_loc q |-> Enum z0); try assumption.
  intros.
  apply rule_pure_star; try assumption.
  apply rule_comm_pure; try assumption.
  intros. assumption.
  }
  apply rule_assoc in SAT'; try assumption.
  apply rule_comm in SAT'; try assumption.
  apply rule_assoc in SAT'; try assumption.
  apply rule_star_pure in SAT'; try assumption.
  destruct SAT' as (EQ,SAT').
  apply rule_assoc in SAT'; try assumption.
  apply rule_assoc in SAT'; try assumption.  
  apply rule_star_pure in SAT'; try assumption.
  destruct SAT' as (EQ',SAT').
  apply Z.eqb_eq in EQ.
  rewrite EQ in *.
  apply Z.eqb_eq in EQ'.
  rewrite EQ' in *.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (cell_loc q |-> Enum next ** cell_loc (Eplus (Enum front) (Enum 1)) |-> Enum value)
   (next_loc (cell_loc q) |-> Enum rear **
   cell_loc (Enum rear) |-> Enum 0 **
   next_loc (cell_loc (Enum rear)) |-> Enum last_value ** nodes (Enum next) (Enum rear) n); try assumption.
  apply rule_assoc'; try assumption.
  apply rule_comm; try assumption.
  apply sat_star_imps with (next_loc (cell_loc q) |-> Enum rear **
           cell_loc (Enum rear) |-> Enum 0 **
           next_loc (cell_loc (Enum rear)) |-> Enum last_value **
           next_loc (cell_loc (Enum front)) |-> Enum value **
           nodes (Enum next) (Enum rear) n)
          (cell_loc q |-> Enum next ** cell_loc (Enum front) |-> Enum next); try assumption.
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (next_loc (cell_loc q) |-> Enum rear)
          (cell_loc (Enum rear) |-> Enum 0 **
          next_loc (cell_loc (Enum rear)) |-> Enum last_value **
          next_loc (cell_loc (Enum front)) |-> Enum value **
          nodes (Enum next) (Enum rear) n); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (cell_loc (Enum rear) |-> Enum 0)
          (next_loc (cell_loc (Enum rear)) |-> Enum last_value **
          next_loc (cell_loc (Enum front)) |-> Enum value **
          nodes (Enum next) (Enum rear) n); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (next_loc (cell_loc (Enum rear)) |-> Enum last_value)
          (next_loc (cell_loc (Enum front)) |-> Enum value **
          nodes (Enum next) (Enum rear) n); try assumption.
  intros. assumption.
  intros.
  apply rule_comm; try assumption.
  intros.
  eapply rule_sat_mon; try assumption.
  apply SAT0.
  intros. apply rule_comm; try assumption.
  intros. assumption.
  }
  {
  intros.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ,SAT).
  assumption.
  }
  apply is_free_subse. assumption.
  {
  intros.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (x,SAT).
  exists x.
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (y,SAT).
  exists y.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  }
  eapply nodup_neq. apply NODUP. simpl. auto.
Qed.

Theorem rule_size_of invs sp q n sizev lastv frontv rearv lastvalv nextnodev incv tmpv
                     (NODUP: NoDup (sizev::lastv::frontv::rearv::lastvalv::nextnodev::incv::tmpv::nil))
                     (NOTFREE: is_free_e q sizev = false /\ is_free_e q frontv = false /\
                               is_free_e q lastv = false /\
                               is_free_e q tmpv = false): correct
  (queue ([[q]]) n)
  (size_of q sizev lastv frontv rearv lastvalv nextnodev incv tmpv)
  (fun size => queue ([[q]]) n &* Abool (Z.eqb size (Z.of_nat n))) invs sp.
Proof.
  destruct NOTFREE as (nf1,(nf2,(nf3,nf4))).
  apply rule_Let with (fun r' => fold_left Astar (points_tos (seq 0 1)(cell_loc (Enum r'))) (Abool true) ** (queue ([[q]]) n)).
  apply rule_conseq1 with (Abool true ** (queue ([[q]]) n)).
  apply rule_frame.
  apply rule_Cons.
  {
  intros.
  apply rule_pure_star'; try assumption.
  split. simpl. trivial. assumption.
  }
  simpl.
  intros.
  apply rule_Let with (fun r' => (fold_left Astar (points_tos (seq 0 1)(cell_loc (Enum r'))) (Abool true)) **
    (cell_loc (Enum z) |-> Enum 0 ** queue ([[q]]) n)).
  apply rule_conseq1 with (Abool true ** cell_loc (Enum z) |-> Enum 0 ** queue ([[q]]) n).
  apply rule_frame.
  apply rule_Cons.
  {
  intros.
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (Abool true) (array (cell_loc (Enum z)) 0 |-> Enum 0 ** queue ([[q]]) n); try assumption.
  intros. assumption.
  intros.
  apply sat_star_imps with (array (cell_loc (Enum z)) 0 |-> Enum 0) (queue ([[q]]) n); try assumption.
  intros. apply sat_array; try assumption.
  intros. assumption.
  }
  simpl.
  intros.
  rewrite neqz; try assumption.
  rewrite neqz; try assumption.
  rewrite neqz; try assumption.
  rewrite eqz.
  rewrite subse_free; try assumption.
  rewrite subse_free; try assumption.
  simpl.
  rewrite eqz.
  rewrite neqz; try assumption.
  rewrite neqz; try assumption.
  rewrite subs_inc.
  simpl.
  rewrite eqz.
  rewrite subs_inc.
  simpl.
  rewrite subs_not_equal; try reflexivity.
  simpl.
  rewrite neqz; try assumption.
  rewrite neqz; try assumption.
  rewrite subs_not_equal; try reflexivity.
  simpl.
  rewrite neqz; try assumption.
  rewrite neqz; try assumption.
  apply rule_conseq1 with (EX front, (EX rear, (EX last_value,
    cell_loc q |-> front **
    next_loc (cell_loc q) |-> rear **
    cell_loc rear |-> Enum 0 **
    next_loc (cell_loc rear) |-> last_value ** nodes front rear n ** 
    cell_loc (Enum z0) |-> Enum 0 **
    cell_loc (Enum z) |-> Enum 0))).
  apply rule_exists1.
  intros front.
  apply rule_exists1.
  intros rear.
  apply rule_exists1.
  intros last_value.
  apply rule_Let with (fun z' => (Abool (Z.eqb z' ([[front]])) &*
   cell_loc q |-> front) **
   next_loc (cell_loc q) |-> rear **
   cell_loc rear |-> Enum 0 **
   next_loc (cell_loc rear) |-> last_value **
   nodes front rear n **
   cell_loc (Enum z0) |-> Enum 0 ** cell_loc (Enum z) |-> Enum 0).
  apply rule_frame.
  apply rule_Lookup.
  simpl.
  intros.
  rewrite eqz.
  apply rule_Let with (fun _ => cell_loc (Enum z0) |-> Enum z1 **
   (Abool (z1 =? ([[front]])) ** cell_loc q |-> front **
   next_loc (cell_loc q) |-> rear **
   cell_loc rear |-> Enum 0 **
   next_loc (cell_loc rear) |-> last_value **
   nodes front rear n **
   cell_loc (Enum z) |-> Enum 0)).
  apply rule_conseq1 with (cell_loc (Enum z0) |-> Enum 0 **
   (Abool (z1 =? ([[front]])) ** cell_loc q |-> front **
   next_loc (cell_loc q) |-> rear **
   cell_loc rear |-> Enum 0 **
   next_loc (cell_loc rear) |-> last_value **
   nodes front rear n **
   cell_loc (Enum z) |-> Enum 0)).
  apply rule_frame.
  apply rule_Mutate.
  {
  intros.
  apply rule_assoc_pure in SAT; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  destruct SAT as (EQ,SAT).
  apply rule_pure_star'; try assumption.
  split. assumption.
  apply rule_comm; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (((((cell_loc q |-> front ** next_loc (cell_loc q) |-> rear) **
             cell_loc rear |-> Enum 0) ** next_loc (cell_loc rear) |-> last_value) **
           nodes front rear n) ** cell_loc (Enum z0) |-> Enum 0)
         (cell_loc (Enum z) |-> Enum 0); try assumption.
  intros.
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (cell_loc (Enum z0) |-> Enum 0)
          ((((cell_loc q |-> front ** next_loc (cell_loc q) |-> rear) **
            cell_loc rear |-> Enum 0) **
           next_loc (cell_loc rear) |-> last_value) ** 
          nodes front rear n); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  intros. assumption.
  }
  simpl.
  intros.
  rewrite subse_free; try assumption.
  rewrite subs_inc.
  rewrite subs_inc.
  simpl.
  rewrite neqz; try assumption.
  simpl.
  rewrite neqz; try assumption.
  rewrite subs_not_equal; try reflexivity.
  simpl.
  rewrite neqz; try assumption.
  rewrite neqz; try assumption.
  rewrite subs_not_equal; try reflexivity.
  simpl.
  rewrite neqz; try assumption.
  rewrite neqz; try assumption.
  rewrite subse_free; try assumption.
  apply rule_Let with (fun z' => (Abool (Z.eqb z' ([[rear]])) &*
    cell_loc (Eplus q (Enum 1)) |-> rear) **
    cell_loc (Enum z0) |-> Enum z1 **
    (Abool (z1 =? ([[front]])) **
    cell_loc q |-> front **
    cell_loc rear |-> Enum 0 **
    next_loc (cell_loc rear) |-> last_value **
    nodes front rear n ** cell_loc (Enum z) |-> Enum 0)).
  apply rule_conseq1 with (cell_loc (Eplus q (Enum 1)) |-> rear **
    cell_loc (Enum z0) |-> Enum z1 **
    (Abool (z1 =? ([[front]])) **
    cell_loc q |-> front **
    cell_loc rear |-> Enum 0 **
    next_loc (cell_loc rear) |-> last_value **
    nodes front rear n ** cell_loc (Enum z) |-> Enum 0)).
  apply rule_frame.
  apply rule_Lookup.
  {
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply sat_star_imps with (((cell_loc (Enum z0) |-> Enum z1 ** Abool (z1 =? ([[front]]))) **
           cell_loc q |-> front) ** next_loc (cell_loc q) |-> rear)
         (cell_loc rear |-> Enum 0 **
         next_loc (cell_loc rear) |-> last_value **
         nodes front rear n ** cell_loc (Enum z) |-> Enum 0); try assumption.
  intros.
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (next_loc (cell_loc q) |-> rear)
          ((cell_loc (Enum z0) |-> Enum z1 ** Abool (z1 =? ([[front]]))) **
          cell_loc q |-> front); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc in SAT1; try assumption.
  intros. assumption.
  }
  simpl.
  intros.
  rewrite subs_inc.
  simpl.
  rewrite subs_not_equal; try reflexivity.
  simpl.
  rewrite neqz; try assumption.
  rewrite eqz.

  apply rule_Let with (fun _ => Abool ((z3 =? ([[rear]])) && (z1 =? ([[front]]))) &*
    cell_loc (Eplus q (Enum 1)) |-> rear **
    (EX zmid, cell_loc (Enum z0) |-> Enum zmid) **
    cell_loc q |-> front **
    cell_loc rear |-> Enum 0 **
    next_loc (cell_loc rear) |-> last_value **
    nodes front rear n ** cell_loc (Enum z) |-> Enum (Z.of_nat n)).
  {

  apply rule_conseq1 with (EX n1, (EX mid, Abool ((z3 =? ([[rear]])) && (z1 =? ([[front]])) && (n1 <=? n)%nat) &*
    cell_loc (Eplus q (Enum 1)) |-> rear **
    cell_loc (Enum z0) |-> Enum mid **
    cell_loc q |-> front **
    cell_loc rear |-> Enum 0 **
    next_loc (cell_loc rear) |-> last_value **
    nodes front (Enum mid) n1 **
    nodes (Enum mid) rear (n-n1) **
    cell_loc (Enum z) |-> Enum (Z.of_nat n1))).

  apply rule_conseq2 with (fun _ => EX z', (EX n1, (EX mid,
    (Abool ((z3 =? ([[rear]])) && (z1 =? ([[front]])) && (n1 <=? n)%nat &&
    (if Z.leb z' 0 then (Z.eqb mid z3) else (negb (Z.eqb mid z3)))) &*
    cell_loc (Eplus q (Enum 1)) |-> rear **
    cell_loc (Enum z0) |-> Enum mid **
    cell_loc q |-> front **
    cell_loc rear |-> Enum 0 **
    next_loc (cell_loc rear) |-> last_value **
    nodes front (Enum mid) n1 **
    nodes (Enum mid) rear (n-n1) **
    cell_loc (Enum z) |-> Enum (Z.of_nat n1)))) &* Abool (Z.leb z' 0)).

  apply rule_While.

  {
  apply rule_exists1.
  intros size.
  apply rule_exists1.
  intros mid.
  apply rule_Let with (fun z' => (Abool (Z.eqb z' mid) &*
    cell_loc (Enum z0) |-> Enum mid) **
   (Abool ((z3 =? ([[rear]])) && (z1 =? ([[front]])) && (size <=? n)%nat) **
   cell_loc (Eplus q (Enum 1)) |-> rear **
   cell_loc q |-> front **
   cell_loc rear |-> Enum 0 **
   next_loc (cell_loc rear) |-> last_value **
   nodes front (Enum mid) size **
   nodes (Enum mid) rear (n - size) ** cell_loc (Enum z) |-> Enum (Z.of_nat size))).
  apply rule_conseq1 with (cell_loc (Enum z0) |-> Enum mid **
   (Abool ((z3 =? ([[rear]])) && (z1 =? ([[front]])) && (size <=? n)%nat) **
   cell_loc (Eplus q (Enum 1)) |-> rear **
   cell_loc q |-> front **
   cell_loc rear |-> Enum 0 **
   next_loc (cell_loc rear) |-> last_value **
   nodes front (Enum mid) size **
   nodes (Enum mid) rear (n - size) ** cell_loc (Enum z) |-> Enum (Z.of_nat size))).
  apply rule_frame.
  apply rule_Lookup.
  {
  intros.
  destruct SAT as (n1,SAT).
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_pure_star'; try assumption.
  split. assumption.
  apply rule_comm; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply sat_star_imps with (cell_loc (Eplus q (Enum 1)) |-> rear **
          cell_loc (Enum z0) |-> Enum mid)
         (cell_loc q |-> front **
         cell_loc rear |-> Enum 0 **
         next_loc (cell_loc rear) |-> last_value **
         nodes front (Enum mid) size **
         nodes (Enum mid) rear (n - size) **
         cell_loc (Enum z) |-> Enum (Z.of_nat size)); try assumption.
  intros.
  apply rule_comm; try assumption.
  intros. assumption.
  }
  {
  simpl. intros.
  rewrite subs_not_equal; try reflexivity.
  simpl. rewrite eqz.
  apply rule_conseq1 with (Abool true **
   Abool ((z4 =? mid) && (z3 =? ([[rear]])) && (z1 =? ([[front]])) && (size <=? n)%nat) **
   cell_loc (Eplus q (Enum 1)) |-> rear **
   cell_loc (Enum z0) |-> Enum mid **
   cell_loc q |-> front **
   cell_loc rear |-> Enum 0 **
   next_loc (cell_loc rear) |-> last_value **
   nodes front (Enum mid) size **
   nodes (Enum mid) rear (n - size) ** cell_loc (Enum z) |-> Enum (Z.of_nat size)).
  apply rule_exists2.
  exists size.
  apply rule_exists2.
  exists mid.
  apply rule_conseq2 with (fun z' =>
   Abool (Z.eqb z' (if Z.eq_dec ([[Enum z4]]) ([[Enum z3]]) then 0 else 1)) **
   Abool ((z4 =? mid) && (z3 =? ([[rear]])) && (z1 =? ([[front]])) && (size <=? n)%nat) **
   cell_loc (Eplus q (Enum 1)) |-> rear **
   cell_loc (Enum z0) |-> Enum mid **
   cell_loc q |-> front **
   cell_loc rear |-> Enum 0 **
   next_loc (cell_loc rear) |-> last_value **
   nodes front (Enum mid) size **
   nodes (Enum mid) rear (n - size) ** cell_loc (Enum z) |-> Enum (Z.of_nat size)).
  apply rule_frame.
  apply rule_not_equal.
  intros.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ,SAT).
  apply Z.eqb_eq in EQ.
  destruct (Z.eq_dec ([[Enum z4]]) ([[Enum z3]])).
  {
  rewrite EQ in *.
  simpl in e. rewrite e in *.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ1,SAT).
  apply Coq.Bool.Bool.andb_true_iff in EQ1.
  destruct EQ1 as (EQ1,EQ2).
  apply Coq.Bool.Bool.andb_true_iff in EQ1.
  destruct EQ1 as (EQ1,EQ3).
  apply Coq.Bool.Bool.andb_true_iff in EQ1.
  destruct EQ1 as (EQ1,EQ4).
  split. simpl.
  apply Coq.Bool.Bool.andb_true_iff. split; try assumption.
  apply Coq.Bool.Bool.andb_true_iff. split; try assumption.
  apply Coq.Bool.Bool.andb_true_iff. split; try assumption.
  apply Z.eqb_eq in EQ1.
  apply Z.eqb_eq. symmetry. assumption. assumption.
  }
  {
  simpl in n0.
  rewrite EQ in *.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ1,SAT).
  apply Coq.Bool.Bool.andb_true_iff in EQ1.
  destruct EQ1 as (EQ1,EQ2).
  apply Coq.Bool.Bool.andb_true_iff in EQ1.
  destruct EQ1 as (EQ1,EQ3).
  apply Coq.Bool.Bool.andb_true_iff in EQ1.
  destruct EQ1 as (EQ1,EQ4).
  apply Z.eqb_eq in EQ1.
  rewrite EQ1 in *.
  split.
  apply Coq.Bool.Bool.andb_true_iff. split; try assumption.
  apply Coq.Bool.Bool.andb_true_iff. split; try assumption.
  apply Coq.Bool.Bool.andb_true_iff. split; try assumption.
  apply Coq.Bool.Bool.negb_true_iff.
  destruct (mid =? z3) eqn:z1z3.
  apply Z.eqb_eq in z1z3.
  omega.
  reflexivity.
  assumption.
  }
  intros.
  apply rule_pure_star'; try assumption.
  split. simpl. trivial.
  apply rule_assoc_pure in SAT; try assumption.
  destruct SAT as (EQ,SAT).
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ2,SAT).
  apply rule_comm in SAT; try assumption.
  apply rule_pure_star'; try assumption.
  split.
  apply Coq.Bool.Bool.andb_true_iff in EQ2.
  destruct EQ2 as (EQ2,EQ3).
  apply Coq.Bool.Bool.andb_true_iff in EQ2.
  destruct EQ2 as (EQ2,EQ4).
  apply Coq.Bool.Bool.andb_true_iff. split; try assumption.
  apply Coq.Bool.Bool.andb_true_iff. split; try assumption.
  apply Coq.Bool.Bool.andb_true_iff. split; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply sat_star_imps with (cell_loc (Enum z0) |-> Enum mid **
          cell_loc (Eplus q (Enum 1)) |-> rear)
         (cell_loc q |-> front **
         cell_loc rear |-> Enum 0 **
         next_loc (cell_loc rear) |-> last_value **
         nodes front (Enum mid) size **
         nodes (Enum mid) rear (n - size) **
         cell_loc (Enum z) |-> Enum (Z.of_nat size)); try assumption.
  intros.
  apply rule_comm; try assumption.
  intros. assumption.
  }
  }
  {
  simpl.
  intros.
  apply rule_exists1.
  intros size.
  apply rule_exists1.
  intros mid.
  apply rule_Let with (fun z' => (Abool (Z.eqb z' ([[Enum mid]])) &*
   cell_loc (Enum z0) |-> Enum mid) **
   Abool ((z3 =? ([[rear]])) && (z1 =? ([[front]])) && (size <? n)%nat &&
    (if z4 <=? 0 then mid =? z3 else negb (mid =? z3))) **
   cell_loc (Eplus q (Enum 1)) |-> rear **
   cell_loc q |-> front **
   cell_loc rear |-> Enum 0 **
   next_loc (cell_loc rear) |-> last_value **
   nodes front (Enum mid) size **
   nodes (Enum mid) rear (n - size) **
   cell_loc (Enum z) |-> Enum (Z.of_nat size)).
  apply rule_conseq1 with (cell_loc (Enum z0) |-> Enum mid **
   Abool ((z3 =? ([[rear]])) && (z1 =? ([[front]])) && (size <? n)%nat &&
    (if z4 <=? 0 then mid =? z3 else negb (mid =? z3))) **
   cell_loc (Eplus q (Enum 1)) |-> rear **
   cell_loc q |-> front **
   cell_loc rear |-> Enum 0 **
   next_loc (cell_loc rear) |-> last_value **
   nodes front (Enum mid) size **
   nodes (Enum mid) rear (n - size) **
   cell_loc (Enum z) |-> Enum (Z.of_nat size)).
  apply rule_frame.
  apply rule_Lookup.
  {
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_pure_star' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  assert (LTS: lt size n).
  {
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ,SAT).
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ',SAT).
  apply Coq.Bool.Bool.andb_true_iff in EQ.
  destruct EQ as (EQ2,EQ3).
  apply Coq.Bool.Bool.andb_true_iff in EQ2.
  destruct EQ2 as (EQ2,EQ4).
  apply Coq.Bool.Bool.andb_true_iff in EQ2.
  destruct EQ2 as (EQ2,EQ5).
  apply Z.eqb_eq in EQ2.
  rewrite EQ2 in *.
  destruct (z4 <=? 0) eqn:z4le.
  apply Z.leb_le in z4le.
  omega.
  apply Coq.Bool.Bool.negb_true_iff in EQ3.
  apply neqb_neq in EQ3.
  destruct (n - size)%nat eqn:nsize.
  {
  simpl in EQ'.
  apply Z.eqb_eq in EQ'.
  contradiction.
  }
  omega.
  }
  apply sat_star_imps with ((Abool
             ((z3 =? ([[rear]])) && (z1 =? ([[front]])) && (size <=? n)%nat &&
              (if z4 <=? 0 then mid =? z3 else negb (mid =? z3))) **
           cell_loc (Eplus q (Enum 1)) |-> rear) **
          cell_loc (Enum z0) |-> Enum mid)
         (cell_loc q |-> front **
         cell_loc rear |-> Enum 0 **
         next_loc (cell_loc rear) |-> last_value **
         nodes front (Enum mid) size **
         nodes (Enum mid) rear (n - size) **
         cell_loc (Enum z) |-> Enum (Z.of_nat size)); try assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply rule_comm; try assumption.
  intros.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_star_pure in SAT0; try assumption.
  destruct SAT0 as (EQ,SAT0).
  apply rule_pure_star'; try assumption.
  split.
  apply Coq.Bool.Bool.andb_true_iff in EQ.
  destruct EQ as (EQ2,EQ3).
  apply Coq.Bool.Bool.andb_true_iff in EQ2.
  destruct EQ2 as (EQ2,EQ4).
  apply Coq.Bool.Bool.andb_true_iff. split; try assumption.
  apply Coq.Bool.Bool.andb_true_iff. split; try assumption.
  apply Nat.ltb_lt. assumption.
  intros. assumption.
  intros. assumption.
  }
  simpl.
  intros.
  rewrite eqz.
  apply rule_conseq1 with (
   (EX next, (EX value,
     cell_loc (Enum z5) |-> (Enum next) **
     next_loc (cell_loc (Enum mid)) |-> (Enum value) ** 
     nodes (Enum next) rear (n - S size) **
   Abool (z5 =? mid) **
   cell_loc (Enum z0) |-> Enum mid **
   Abool ((z3 =? ([[rear]])) && (z1 =? ([[front]])) && (size <? n)%nat &&
      (if z4 <=? 0 then mid =? z3 else negb (mid =? z3))) **
   cell_loc (Eplus q (Enum 1)) |-> rear **
   cell_loc q |-> front **
   cell_loc rear |-> Enum 0 **
   next_loc (cell_loc rear) |-> last_value **
   nodes front (Enum mid) size **
   cell_loc (Enum z) |-> Enum (Z.of_nat size)))).
  apply rule_exists1.
  intros mid_next.
  apply rule_exists1.
  intros mid_val.
  apply rule_Let with (fun z' =>(Abool (Z.eqb z' ([[Enum mid_next]])) &*
   cell_loc (Enum z5) |-> Enum mid_next) **
   next_loc (cell_loc (Enum mid)) |-> Enum mid_val **
   nodes (Enum mid_next) rear (n - S size) **
   Abool (z5 =? mid) **
   cell_loc (Enum z0) |-> Enum mid **
   Abool
     ((z3 =? ([[rear]])) && (z1 =? ([[front]])) && (size <? n)%nat &&
      (if z4 <=? 0 then mid =? z3 else negb (mid =? z3))) **
   cell_loc (Eplus q (Enum 1)) |-> rear **
   cell_loc q |-> front **
   cell_loc rear |-> Enum 0 **
   next_loc (cell_loc rear) |-> last_value **
   nodes front (Enum mid) size **
   cell_loc (Enum z) |-> Enum (Z.of_nat size)).
  apply rule_frame.
  apply rule_Lookup.
  simpl. intros.
  rewrite neqz; try assumption. simpl.
  rewrite neqz; try assumption. simpl.
  rewrite neqz; try assumption. simpl.
  rewrite neqz; try assumption. simpl.
  rewrite neqz; try assumption. simpl.
  rewrite neqz; try assumption. simpl.
  rewrite eqz. simpl.
  apply rule_Let with (fun _ => cell_loc (Enum z0) |-> Enum z6 **
   (Abool (Z.eqb z6 ([[Enum mid_next]])) **
   cell_loc (Enum z5) |-> Enum mid_next **
   next_loc (cell_loc (Enum mid)) |-> Enum mid_val **
   nodes (Enum mid_next) rear (n - S size) **
   Abool (z5 =? mid) **
   Abool ((z3 =? ([[rear]])) && (z1 =? ([[front]])) && (size <? n)%nat &&
      (if z4 <=? 0 then mid =? z3 else negb (mid =? z3))) **
   cell_loc (Eplus q (Enum 1)) |-> rear **
   cell_loc q |-> front **
   cell_loc rear |-> Enum 0 **
   next_loc (cell_loc rear) |-> last_value **
   nodes front (Enum mid) size **
   cell_loc (Enum z) |-> Enum (Z.of_nat size))).
  apply rule_conseq1 with (cell_loc (Enum z0) |-> Enum mid **
   (Abool (Z.eqb z6 ([[Enum mid_next]])) **
   cell_loc (Enum z5) |-> Enum mid_next **
   next_loc (cell_loc (Enum mid)) |-> Enum mid_val **
   nodes (Enum mid_next) rear (n - S size) **
   Abool (z5 =? mid) **
   Abool ((z3 =? ([[rear]])) && (z1 =? ([[front]])) && (size <? n)%nat &&
      (if z4 <=? 0 then mid =? z3 else negb (mid =? z3))) **
   cell_loc (Eplus q (Enum 1)) |-> rear **
   cell_loc q |-> front **
   cell_loc rear |-> Enum 0 **
   next_loc (cell_loc rear) |-> last_value **
   nodes front (Enum mid) size **
   cell_loc (Enum z) |-> Enum (Z.of_nat size))).
  apply rule_frame.
  apply rule_Mutate.
{
  intros.
  apply rule_assoc_pure in SAT; try assumption.
  destruct SAT as (EQ,SAT).
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (cell_loc (Enum z0) |-> Enum mid)
         ((Abool
            ((z3 =? ([[rear]])) && (z1 =? ([[front]])) && (size <? n)%nat &&
             (if z4 <=? 0 then mid =? z3 else negb (mid =? z3))) **
          cell_loc (Eplus q (Enum 1)) |-> rear **
          cell_loc q |-> front **
          cell_loc rear |-> Enum 0 **
          next_loc (cell_loc rear) |-> last_value **
          nodes front (Enum mid) size **
          cell_loc (Enum z) |-> Enum (Z.of_nat size)) **
         ((cell_loc (Enum z5) |-> Enum mid_next **
           next_loc (cell_loc (Enum mid)) |-> Enum mid_val) **
          nodes (Enum mid_next) rear (n - S size)) ** 
         Abool (z5 =? mid)); try assumption.
  intros. assumption.
  intros.
  apply rule_pure_star'; try assumption.
  split. assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_star_pure in SAT0; try assumption.
  destruct SAT0 as (EQ0,SAT0).
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (((cell_loc (Enum z5) |-> Enum mid_next **
             next_loc (cell_loc (Enum mid)) |-> Enum mid_val) **
            nodes (Enum mid_next) rear (n - S size)) ** 
           Abool (z5 =? mid))
          (cell_loc (Eplus q (Enum 1)) |-> rear **
          cell_loc q |-> front **
          cell_loc rear |-> Enum 0 **
          next_loc (cell_loc rear) |-> last_value **
          nodes front (Enum mid) size **
          cell_loc (Enum z) |-> Enum (Z.of_nat size)); try assumption.
  intros. assumption.
  intros.
  apply rule_pure_star'; try assumption.
  split; try assumption.
  }

  simpl. intros.
  rewrite subs_inc; simpl.
  rewrite subs_inc; simpl.
  rewrite subs_inc; simpl.

  apply rule_conseq1 with (cell_loc (Enum z) |-> Enum (Z.of_nat size) **
   (cell_loc (Enum z0) |-> Enum z6 **
   Abool (Z.eqb z6 ([[Enum mid_next]])) **
   cell_loc (Enum z5) |-> Enum mid_next **
   next_loc (cell_loc (Enum mid)) |-> Enum mid_val **
   nodes (Enum mid_next) rear (n - S size) **
   Abool (z5 =? mid) **
   Abool ((z3 =? ([[rear]])) && (z1 =? ([[front]])) && (size <? n)%nat &&
      (if z4 <=? 0 then mid =? z3 else negb (mid =? z3))) **
   cell_loc (Eplus q (Enum 1)) |-> rear **
   cell_loc q |-> front **
   cell_loc rear |-> Enum 0 **
   next_loc (cell_loc rear) |-> last_value **
   nodes front (Enum mid) size)).

  apply rule_conseq2 with (fun _ => cell_loc (Enum z) |-> (Eplus (Enum (Z.of_nat size)) (Enum 1)) **
   (cell_loc (Enum z0) |-> Enum z6 **
   Abool (Z.eqb z6 ([[Enum mid_next]])) **
   cell_loc (Enum z5) |-> Enum mid_next **
   next_loc (cell_loc (Enum mid)) |-> Enum mid_val **
   nodes (Enum mid_next) rear (n - S size) **
   Abool (z5 =? mid) **
   Abool ((z3 =? ([[rear]])) && (z1 =? ([[front]])) && (size <? n)%nat &&
      (if z4 <=? 0 then mid =? z3 else negb (mid =? z3))) **
   cell_loc (Eplus q (Enum 1)) |-> rear **
   cell_loc q |-> front **
   cell_loc rear |-> Enum 0 **
   next_loc (cell_loc rear) |-> last_value **
   nodes front (Enum mid) size)).
  apply rule_frame.
  apply rule_inc; reflexivity.
  {
  intros.
  exists (S size).
  exists mid_next.

  apply rule_comm in SAT; try assumption.

  apply rule_star_pure; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (cell_loc (Enum z0) |-> Enum z6 **
          Abool (z6 =? ([[Enum mid_next]])) **
          cell_loc (Enum z5) |-> Enum mid_next **
          next_loc (cell_loc (Enum mid)) |-> Enum mid_val **
          nodes (Enum mid_next) rear (n - S size) ** Abool (z5 =? mid) **
          Abool
            ((z3 =? ([[rear]])) && (z1 =? ([[front]])) && (size <? n)%nat &&
             (if z4 <=? 0 then mid =? z3 else negb (mid =? z3))) **
          cell_loc (Eplus q (Enum 1)) |-> rear **
          cell_loc q |-> front **
          cell_loc rear |-> Enum 0 **
          next_loc (cell_loc rear) |-> last_value ** nodes front (Enum mid) size)
         (cell_loc (Enum z) |-> Eplus (Enum (Z.of_nat size)) (Enum 1)); try assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_star_pure in SAT0; try assumption.
  destruct SAT0 as (EQ,SAT0).
  apply rule_assoc in SAT0; try assumption.
  apply rule_star_pure in SAT0; try assumption.
  destruct SAT0 as (EQ0,SAT0).
  apply rule_pure_star'; try assumption.
  apply Coq.Bool.Bool.andb_true_iff in EQ0.
  destruct EQ0 as (EQ0,EQ2).
  split. assumption.


  apply rule_comm in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_star_pure in SAT0; try assumption.
  destruct SAT0 as (EQ3,SAT0).
  apply Z.eqb_eq in EQ3.
  rewrite EQ3 in *.
  apply rule_comm in SAT0; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (cell_loc (Enum z0) |-> Enum ([[Enum mid_next]]))
          (cell_loc (Enum z5) |-> Enum mid_next **
          next_loc (cell_loc (Enum mid)) |-> Enum mid_val **
          nodes (Enum mid_next) rear (n - S size) **
          cell_loc (Eplus q (Enum 1)) |-> rear **
          cell_loc q |-> front **
          cell_loc rear |-> Enum 0 **
          next_loc (cell_loc rear) |-> last_value ** nodes front (Enum mid) size); try assumption.
  intros. assumption.
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_comm in SAT1; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply sat_star_imps with (cell_loc (Eplus q (Enum 1)) |-> rear)
          ((cell_loc q |-> front **
           cell_loc rear |-> Enum 0 **
           next_loc (cell_loc rear) |-> last_value **
           nodes front (Enum mid) size) **
          (cell_loc (Enum z5) |-> Enum mid_next **
           next_loc (cell_loc (Enum mid)) |-> Enum mid_val) **
          nodes (Enum mid_next) rear (n - S size)); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc in SAT2; try assumption.
  apply sat_star_imps with (cell_loc q |-> front)
          ((cell_loc rear |-> Enum 0 **
           next_loc (cell_loc rear) |-> last_value **
           nodes front (Enum mid) size) **
          (cell_loc (Enum z5) |-> Enum mid_next **
           next_loc (cell_loc (Enum mid)) |-> Enum mid_val) **
          nodes (Enum mid_next) rear (n - S size)); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc in SAT3; try assumption.
  apply sat_star_imps with (cell_loc rear |-> Enum 0)
          ((next_loc (cell_loc rear) |-> last_value **
           nodes front (Enum mid) size) **
          (cell_loc (Enum z5) |-> Enum mid_next **
           next_loc (cell_loc (Enum mid)) |-> Enum mid_val) **
          nodes (Enum mid_next) rear (n - S size)); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc in SAT4; try assumption.
  apply sat_star_imps with (next_loc (cell_loc rear) |-> last_value)
          (nodes front (Enum mid) size **
          (cell_loc (Enum z5) |-> Enum mid_next **
           next_loc (cell_loc (Enum mid)) |-> Enum mid_val) **
          nodes (Enum mid_next) rear (n - S size)); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc' in SAT5; try assumption.
  apply sat_star_imps with (nodes front (Enum mid) size **
           cell_loc (Enum z5) |-> Enum mid_next **
           next_loc (cell_loc (Enum mid)) |-> Enum mid_val)
          (nodes (Enum mid_next) rear (n - S size)); try assumption.
  apply Z.eqb_eq in EQ.
  rewrite EQ in *.
  intros.
  eapply nodes_next; try assumption. apply SAT6.
  intros. assumption.
  intros.
  replace (Z.of_nat (S size)) with (Z.of_nat size + 1).
  apply rule_plus_evall; try assumption.
  symmetry. rewrite Nat2Z.inj_succ. simpl. omega.
  }
  {
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (cell_loc (Enum z0) |-> Enum z6)
         ((Abool (z6 =? mid_next) **
          cell_loc (Enum z5) |-> Enum mid_next **
          next_loc (cell_loc (Enum mid)) |-> Enum mid_val **
          nodes (Enum mid_next) rear (n - S size) ** Abool (z5 =? mid) **
          Abool
            ((z3 =? ([[rear]])) && (z1 =? ([[front]])) && (size <? n)%nat &&
             (if z4 <=? 0 then mid =? z3 else negb (mid =? z3))) **
          cell_loc (Eplus q (Enum 1)) |-> rear **
          cell_loc q |-> front **
          cell_loc rear |-> Enum 0 **
          next_loc (cell_loc rear) |-> last_value **
          nodes front (Enum mid) size **
          cell_loc (Enum z) |-> Enum (Z.of_nat size))); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.

  apply sat_star_imps with ((((((((((Abool (z6 =? mid_next) **
                    cell_loc (Enum z5) |-> Enum mid_next) **
                   next_loc (cell_loc (Enum mid)) |-> Enum mid_val) **
                  nodes (Enum mid_next) rear (n - S size)) ** 
                 Abool (z5 =? mid)) **
                Abool
                  ((z3 =? ([[rear]])) && (z1 =? ([[front]])) && (size <? n)%nat &&
                   (if z4 <=? 0 then mid =? z3 else negb (mid =? z3)))) **
               cell_loc (Eplus q (Enum 1)) |-> rear) ** 
              cell_loc q |-> front) ** cell_loc rear |-> Enum 0) **
            next_loc (cell_loc rear) |-> last_value) **
           nodes front (Enum mid) size)
          (cell_loc (Enum z) |-> Enum (Z.of_nat size)); try assumption.
  intros.
  apply rule_assoc in SAT1; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply rule_assoc in SAT1; try assumption.
  intros. assumption.
  }
  {
  rewrite neqz. reflexivity.
  inversion NODUP. inversion H2. inversion H6. inversion H10. inversion H14. inversion H18.
  apply neq_symm. eapply nodup_neq. apply H22. simpl. auto.
  }
  {
  rewrite neqz. reflexivity.
  inversion NODUP. inversion H2. inversion H6. inversion H10. inversion H14.
  eapply nodup_neq. apply H18. simpl. auto.
  }
  {
  rewrite neqz. reflexivity.
  inversion NODUP. inversion H2. inversion H6. inversion H10.
  eapply nodup_neq. apply H14. simpl. auto.
  }
  {
  inversion NODUP. inversion H2. inversion H6. inversion H10.
  eapply nodup_neq. apply H14. simpl. auto.
  }
  {
  inversion NODUP. inversion H2. inversion H6.
  eapply nodup_neq. apply H10. simpl. auto.
  }
  {
  inversion NODUP. inversion H2. inversion H6. inversion H10. inversion H14.
  apply neq_symm. eapply nodup_neq. apply H18. simpl. auto.
  }
  {
  inversion NODUP. inversion H2.
  eapply nodup_neq. apply H6. simpl. auto.
  }
  {
  inversion NODUP.
  eapply nodup_neq. apply H2. simpl. auto.
  }
  {
  eapply nodup_neq. apply NODUP. simpl. auto 10.
  }
  {
  intros.
  apply rule_assoc_pure in SAT; try assumption.
  destruct SAT as (EQ,SAT).
  apply Z.eqb_eq in EQ.
  rewrite EQ in *.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ1,SAT).
  apply Coq.Bool.Bool.andb_true_iff in EQ1.
  destruct EQ1 as (EQ2,EQ3).
  destruct (z4 <=? 0) eqn:z4le.
  apply Z.leb_le in z4le.
  omega.
  assert (EQ3':=EQ3).
  apply Coq.Bool.Bool.negb_true_iff in EQ3.
  apply neqb_neq in EQ3.
  apply Coq.Bool.Bool.andb_true_iff in EQ2.
  destruct EQ2 as (EQ2,EQ4).
  apply Coq.Bool.Bool.andb_true_iff in EQ2.
  destruct EQ2 as (EQ2,EQ5).
  apply Z.eqb_eq in EQ2.
  rewrite EQ2 in *.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  assert (G: sat p o g (
  (EX next, (EX value,
    cell_loc (Enum mid) |-> Enum next **
    next_loc (cell_loc (Enum mid)) |-> Enum value **
    nodes (Enum next) rear (n - S size))) **
         cell_loc (Enum z) |-> Enum (Z.of_nat size) **
         ((((cell_loc (Enum z0) |-> Enum mid ** cell_loc (Eplus q (Enum 1)) |-> rear) **
         cell_loc q |-> front) ** cell_loc rear |-> Enum 0) **
         next_loc (cell_loc rear) |-> last_value) ** nodes front (Enum mid) size)).
  {
  apply sat_star_imps with (nodes (Enum mid) rear (n - size))
         (cell_loc (Enum z) |-> Enum (Z.of_nat size) **
         ((((cell_loc (Enum z0) |-> Enum mid ** cell_loc (Eplus q (Enum 1)) |-> rear) **
            cell_loc q |-> front) ** cell_loc rear |-> Enum 0) **
          next_loc (cell_loc rear) |-> last_value) ** nodes front (Enum mid) size); try assumption.
  intros.
  replace (n - S size)%nat with ((n - size) - 1)%nat.
  apply nodes_open; try assumption.
  omega.
  intros. assumption.
  }
  apply rule_exists_dist in G; try assumption.
  destruct G as (next,G).
  apply rule_exists_dist in G; try assumption.
  destruct G as (value,G).
  exists next.
  exists value.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (cell_loc (Enum mid) |-> Enum next **
        next_loc (cell_loc (Enum mid)) |-> Enum value **
        nodes (Enum next) rear (n - S size))
       (cell_loc (Enum z) |-> Enum (Z.of_nat size) **
       ((((cell_loc (Enum z0) |-> Enum mid ** cell_loc (Eplus q (Enum 1)) |-> rear) **
          cell_loc q |-> front) ** cell_loc rear |-> Enum 0) **
        next_loc (cell_loc rear) |-> last_value) ** nodes front (Enum mid) size); try assumption.
  intros.
  apply rule_assoc'; try assumption.
  intros.
  apply rule_pure_star'; try assumption.
  split.
  apply Z.eqb_eq. reflexivity.
  apply rule_comm in SAT0; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_pure_star'; try assumption.
  split.
  apply Coq.Bool.Bool.andb_true_iff. split.
  apply Coq.Bool.Bool.andb_true_iff. split.
  apply Coq.Bool.Bool.andb_true_iff. split.
  apply Z.eqb_eq. reflexivity. assumption. assumption. assumption.
  apply rule_comm; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  }
  }
  {
  intros.
  destruct SAT as (n1,SAT).
  destruct SAT as (mid,SAT).
  exists n1.
  exists mid.
  destruct SAT as (EQ,SAT).
  apply Coq.Bool.Bool.andb_true_iff in EQ.
  destruct EQ as (EQ1,EQ2).
  split. assumption. assumption.
  }
  {
  intros.

  destruct SAT as (z',SAT).
  destruct SAT as (SAT,EQ).
  destruct SAT as (n1,SAT).
  destruct SAT as (mid,SAT).
  destruct SAT as (EQ1,SAT).
  apply Coq.Bool.Bool.andb_true_iff in EQ1.
  destruct EQ1 as (EQ1,EQ2).
  apply Z.leb_le in EQ.
  destruct (z' <=? 0) eqn:CO.
  2: { apply Z_leb_falseL in CO. omega. }
  apply Z.eqb_eq in EQ2.
  rewrite <- EQ2 in *.
  apply Coq.Bool.Bool.andb_true_iff in EQ1.
  destruct EQ1 as (EQ1,EQ3).
  split. assumption.
  apply sat_star_imps with (cell_loc (Eplus q (Enum 1)) |-> rear)
         (cell_loc (Enum z0) |-> Enum mid **
         cell_loc q |-> front **
         cell_loc rear |-> Enum 0 **
         next_loc (cell_loc rear) |-> last_value **
         nodes front (Enum mid) n1 **
         nodes (Enum mid) rear (n - n1) **
         cell_loc (Enum z) |-> Enum (Z.of_nat n1)); try assumption.
  intros. assumption.
  intros.
  apply rule_exists_dist'; try assumption.
  exists mid.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply sat_star_imps with (((cell_loc (Enum z0) |-> Enum mid ** cell_loc q |-> front) **
            cell_loc rear |-> Enum 0) **
           next_loc (cell_loc rear) |-> last_value)
          (nodes front (Enum mid) n1 **
          nodes (Enum mid) rear (n - n1) **
          cell_loc (Enum z) |-> Enum (Z.of_nat n1)); try assumption.
  intros. assumption.
  intros.
  apply Nat.leb_le in EQ3.
  apply rule_assoc' in SAT1; try assumption.
  apply sat_star_imps with (nodes front (Enum mid) n1 ** nodes (Enum mid) rear (n - n1))
          (cell_loc (Enum z) |-> Enum (Z.of_nat n1)); try assumption.
  intros. eapply nodes_merge with n1 (Enum mid); try assumption.


  assert (EQN: n = n1).
  {
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT2,SAT3).
  apply rule_assoc' in SAT3; try assumption.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_star_pure in SAT3; try assumption.
  destruct SAT3 as (SAT3,SAT4).
  apply rule_comm in SAT3; try assumption.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_star_pure in SAT3; try assumption.
  destruct SAT3 as (SAT3,SAT5).
  apply rule_assoc' in SAT3; try assumption.
  apply rule_star_pure in SAT3; try assumption.
  destruct SAT3 as (SAT3,SAT6).
  apply Coq.Bool.Bool.andb_true_iff in EQ1.
  destruct EQ1 as (EQ1,EQ5).
  apply Z.eqb_eq in EQ1.
  rewrite EQ1 in *.
  destruct (n - n1)%nat eqn:nn1. omega.
  unfold nodes in SAT3. fold nodes in SAT3.
  apply rule_exists_dist in SAT3; try assumption.
  destruct SAT3 as (next,SAT3).
  apply rule_exists_dist in SAT3; try assumption.
  destruct SAT3 as (value,SAT3).
  apply rule_comm in SAT3; try assumption.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_star_pure in SAT3; try assumption.
  destruct SAT3 as (SAT3,SAT7).
  apply rule_disjont in SAT3; try assumption.
  inversion SAT3.
  reflexivity.
  }
  rewrite EQN.
  intros. assumption.
  }
  {
  intros.
  exists O.
  exists z1.
  apply rule_assoc_pure in SAT; try assumption.
  apply rule_pure_star' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ,SAT).
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ1,SAT).
  split.
  apply Coq.Bool.Bool.andb_true_iff.
  split.
  apply Coq.Bool.Bool.andb_true_iff.
  split; assumption.
  apply Nat.leb_le. omega.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with ((((cell_loc (Eplus q (Enum 1)) |-> rear **
             cell_loc (Enum z0) |-> Enum z1) ** cell_loc q |-> front) **
           cell_loc rear |-> Enum 0) ** next_loc (cell_loc rear) |-> last_value)
         (nodes front rear n ** cell_loc (Enum z) |-> Enum 0); try assumption.
  intros. assumption.
  intros.
  apply Z.eqb_eq in EQ1. rewrite EQ1 in *.
  apply rule_pure_star'; try assumption.
  split. apply Z.eqb_eq. reflexivity.
  apply sat_star_imps with (nodes front rear n) (cell_loc (Enum z) |-> Enum 0); try assumption.
  intros.
  apply nodes_eval with front; try assumption. reflexivity.
  intros. replace (n - 0)%nat with n. assumption. omega.
  intros. assumption.
  }
  }
  {
  simpl.
  intros.
  apply rule_conseq1 with (cell_loc (Enum z) |-> Enum (Z.of_nat n) **
   (Abool ((z3 =? ([[rear]])) && (z1 =? ([[front]]))) **
   cell_loc (Eplus q (Enum 1)) |-> rear **
  (EX zmid, cell_loc (Enum z0) |-> Enum zmid) **
   cell_loc q |-> front **
   cell_loc rear |-> Enum 0 **
   next_loc (cell_loc rear) |-> last_value **
   nodes front rear n)).
  apply rule_conseq2 with (fun z' => (Abool (z' =? (Z.of_nat n)) &*
   cell_loc (Enum z) |-> Enum (Z.of_nat n)) **
   (Abool ((z3 =? ([[rear]])) && (z1 =? ([[front]]))) **
   cell_loc (Eplus q (Enum 1)) |-> rear **
   (EX zmid, cell_loc (Enum z0) |-> Enum zmid) **
   cell_loc q |-> front **
   cell_loc rear |-> Enum 0 **
   next_loc (cell_loc rear) |-> last_value **
   nodes front rear n)).
  apply rule_frame.
  apply rule_Lookup.
  {
  intros.
  unfold queue.
  apply rule_assoc_pure in SAT; try assumption.
  destruct SAT as (EQ,SAT).
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ1,SAT).
  apply rule_comm in SAT; try assumption.
  split.
  exists ([[front]]).
  exists ([[rear]]).
  exists ([[last_value]]).
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ2,SAT).
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ3,SAT).
  apply rule_comm in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (cell_loc (Eplus q (Enum 1)) |-> rear ** cell_loc q |-> front)
         (cell_loc rear |-> Enum 0 **
         next_loc (cell_loc rear) |-> last_value ** nodes front rear n); try assumption.
  intros.
  apply rule_comm; try assumption.
  intros.
  apply sat_star_imps with (cell_loc rear |-> Enum 0)
          (next_loc (cell_loc rear) |-> last_value ** nodes front rear n); try assumption.
  intros. assumption.
  intros.
  apply sat_star_imps with (next_loc (cell_loc rear) |-> last_value) (nodes front rear n); try assumption.
  intros. assumption.
  intros.
  apply nodes_eval with front; try assumption. reflexivity.
  apply nodes_eval' with rear; try assumption. reflexivity.
  assumption.
  }
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_pure_star'; try assumption.
  destruct SAT as (EQ,SAT).
  split; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply sat_star_imps with (((((cell_loc (Eplus q (Enum 1)) |-> rear **
              (EX zmid, cell_loc (Enum z0) |-> Enum zmid)) **
             cell_loc q |-> front) ** cell_loc rear |-> Enum 0) **
           next_loc (cell_loc rear) |-> last_value) ** 
          nodes front rear n) (cell_loc (Enum z) |-> Enum (Z.of_nat n)); try assumption.
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  intros. assumption.
  }
  {
  inversion NODUP. inversion H2. inversion H6.
  eapply nodup_neq. apply H10. simpl. auto 10.
  }
  {
  simpl. rewrite neqz. reflexivity.
  inversion NODUP. inversion H2. inversion H6.
  eapply nodup_neq. apply H10. simpl. auto 10.
  }
  {
  inversion NODUP. inversion H2. inversion H6.
  apply neq_symm. eapply nodup_neq. apply H10. simpl. auto 10.
  }
  {
  inversion NODUP. inversion H2. inversion H6. inversion H10.
  apply neq_symm. eapply nodup_neq. apply H14. simpl. auto 10.
  }
  {
  inversion NODUP. inversion H2.
  eapply nodup_neq. apply H6. simpl. auto 10.
  }
  {
  inversion NODUP. inversion H2.
  eapply nodup_neq. apply H6. simpl. auto 10.
  }
  {
  inversion NODUP. inversion H2. inversion H6. inversion H10.
  apply neq_symm. eapply nodup_neq. apply H14. simpl. auto 10.
  }
  {
  inversion NODUP. inversion H2.
  eapply nodup_neq. apply H6. simpl. auto 10.
  }
  {
  simpl. rewrite neqz. reflexivity.
  inversion NODUP. inversion H2. inversion H6. inversion H10. inversion H14. inversion H18.
  apply neq_symm. eapply nodup_neq. apply H22. simpl. auto.
  }
  {
  simpl. rewrite neqz. reflexivity.
  inversion NODUP. inversion H2.
  eapply nodup_neq. apply H6. simpl. auto.
  }
  {
  apply is_free_subse. assumption.
  }
  {
  intros.
  apply rule_assoc in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (EQ,SAT).
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  unfold queue in SAT.
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (front,SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (rear,SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (lastval,SAT).
  exists (Enum front).
  exists (Enum rear).
  exists (Enum lastval).
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (cell_loc (Enum ([[q]])) |-> Enum front **
          next_loc (cell_loc (Enum ([[q]]))) |-> Enum rear **
          cell_loc (Enum rear) |-> Enum 0 **
          next_loc (cell_loc (Enum rear)) |-> Enum lastval **
          nodes (Enum front) (Enum rear) n)
          (array (cell_loc (Enum z0)) 0 |-> Enum 0 ** cell_loc (Enum z) |-> Enum 0); try assumption.
  intros.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  intros.
  apply sat_star_imps with (array (cell_loc (Enum z0)) 0 |-> Enum 0) (cell_loc (Enum z) |-> Enum 0); try assumption.
  intros.
  apply sat_array; try assumption.
  intros. assumption.
  }
  {
  inversion NODUP.
  eapply nodup_neq. apply H2. simpl. auto.
  }
  {
  inversion NODUP.
  eapply nodup_neq. apply H2. simpl. auto.
  }
  {
  eapply nodup_neq. apply NODUP. simpl. auto.
  }
  {
  eapply nodup_neq. apply NODUP. simpl. auto.
  }
  {
  simpl. rewrite neqz. reflexivity.
  inversion NODUP.
  eapply nodup_neq. apply H2. simpl. auto 10.
  }
  {
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 10.
  }
  {
  inversion NODUP.
  eapply nodup_neq. apply H2. simpl. auto.
  }
  {
  inversion NODUP.
  eapply nodup_neq. apply H2. simpl. auto.
  }
  apply is_free_subse. assumption.
  {
  eapply nodup_neq. apply NODUP. simpl. auto.
  }
  {
  eapply nodup_neq. apply NODUP. simpl. auto.
  }
  {
  eapply nodup_neq. apply NODUP. simpl. auto.
  }
Qed.

Lemma subsa_nodes:
  forall size x z front rear,
    subsa (nodes (Enum front) (Enum rear) size) (subse x z) |= nodes (Enum front) (Enum rear) size.
Proof.
  induction size.
  simpl.
  intros.
  assumption.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(g1,(g2,(ghpg1g2,(bg1,(bg2,(bg1g2,(opo1o2,(tmp1,(tmp2,tmp3))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdp3p4,(bp3,(bp4,(bp3p4,(o3,(o4,(g3,(g4,(ghpg3g4,(bg3,(bg4,(bg3g4,(opo3o4,(tmp2,(tmp4,tmp5))))))))))))))))).
  apply IHsize in tmp4; try assumption.
  simpl.
  exists v, v0, p1, p2, phpdp1p2, bp1, bp2, bp1p2, o1, o2, g1, g2, ghpg1g2, bg1, bg2, bg1g2, opo1o2.
  split; try assumption.
  split; try assumption.
  exists p3, p4, phpdp3p4, bp3, bp4, bp3p4, o3, o4, g3, g4, ghpg3g4, bg3, bg4, bg3g4, opo3o4.
  split; try assumption.
  split; try assumption.
Qed.

Lemma subsa_nodes2:
  forall size x z x' z' front rear,
    subsa (subsa (nodes (Enum front) (Enum rear) size) (subse x z)) (subse x' z') |= nodes (Enum front) (Enum rear) size.
Proof.
  induction size.
  simpl.
  intros.
  assumption.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(g1,(g2,(ghpg1g2,(bg1,(bg2,(bg1g2,(opo1o2,(tmp1,(tmp2,tmp3))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdp3p4,(bp3,(bp4,(bp3p4,(o3,(o4,(g3,(g4,(ghpg3g4,(bg3,(bg4,(bg3g4,(opo3o4,(tmp2,(tmp4,tmp5))))))))))))))))).
  apply IHsize in tmp4; try assumption.
  simpl.
  exists v, v0, p1, p2, phpdp1p2, bp1, bp2, bp1p2, o1, o2, g1, g2, ghpg1g2, bg1, bg2, bg1g2, opo1o2.
  split; try assumption.
  split; try assumption.
  exists p3, p4, phpdp3p4, bp3, bp4, bp3p4, o3, o4, g3, g4, ghpg3g4, bg3, bg4, bg3g4, opo3o4.
  split; try assumption.
  split; try assumption.
Qed.

Lemma subsa_nodes3:
  forall size x z x' z' x'' z'' front rear,
    subsa (subsa (subsa (nodes (Enum front) (Enum rear) size) (subse x z)) (subse x' z')) (subse x'' z'') |= nodes (Enum front) (Enum rear) size.
Proof.
  induction size.
  simpl.
  intros.
  assumption.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(g1,(g2,(ghpg1g2,(bg1,(bg2,(bg1g2,(opo1o2,(tmp1,(tmp2,tmp3))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdp3p4,(bp3,(bp4,(bp3p4,(o3,(o4,(g3,(g4,(ghpg3g4,(bg3,(bg4,(bg3g4,(opo3o4,(tmp2,(tmp4,tmp5))))))))))))))))).
  apply IHsize in tmp4; try assumption.
  simpl.
  exists v, v0, p1, p2, phpdp1p2, bp1, bp2, bp1p2, o1, o2, g1, g2, ghpg1g2, bg1, bg2, bg1g2, opo1o2.
  split; try assumption.
  split; try assumption.
  exists p3, p4, phpdp3p4, bp3, bp4, bp3p4, o3, o4, g3, g4, ghpg3g4, bg3, bg4, bg3g4, opo3o4.
  split; try assumption.
  split; try assumption.
Qed.

Lemma subsa_nodes2':
  forall size x z x' z' front rear,
    nodes (Enum front) (Enum rear) size |= subsa (subsa (nodes (Enum front) (Enum rear) size) (subse x z)) (subse x' z').
Proof.
  induction size.
  simpl.
  intros.
  assumption.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(g1,(g2,(ghpg1g2,(bg1,(bg2,(bg1g2,(opo1o2,(tmp1,(tmp2,tmp3))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdp3p4,(bp3,(bp4,(bp3p4,(o3,(o4,(g3,(g4,(ghpg3g4,(bg3,(bg4,(bg3g4,(opo3o4,(tmp2,(tmp4,tmp5))))))))))))))))).
  eapply IHsize in tmp4; try assumption.
  simpl.
  exists v, v0, p1, p2, phpdp1p2, bp1, bp2, bp1p2, o1, o2, g1, g2, ghpg1g2, bg1, bg2, bg1g2, opo1o2.
  split; try assumption.
  split; try assumption.
  exists p3, p4, phpdp3p4, bp3, bp4, bp3p4, o3, o4, g3, g4, ghpg3g4, bg3, bg4, bg3g4, opo3o4.
  split; try assumption.
  split; try assumption.
  apply tmp4.
Qed.

Lemma subsa_nodes3':
  forall size x z x' z' x'' z'' front rear,
    nodes (Enum front) (Enum rear) size |= subsa (subsa (subsa (nodes (Enum front) (Enum rear) size) (subse x z)) (subse x' z')) (subse x'' z'').
Proof.
  induction size.
  simpl.
  intros.
  assumption.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(g1,(g2,(ghpg1g2,(bg1,(bg2,(bg1g2,(opo1o2,(tmp1,(tmp2,tmp3))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdp3p4,(bp3,(bp4,(bp3p4,(o3,(o4,(g3,(g4,(ghpg3g4,(bg3,(bg4,(bg3g4,(opo3o4,(tmp2,(tmp4,tmp5))))))))))))))))).
  eapply IHsize in tmp4; try assumption.
  simpl.
  exists v, v0, p1, p2, phpdp1p2, bp1, bp2, bp1p2, o1, o2, g1, g2, ghpg1g2, bg1, bg2, bg1g2, opo1o2.
  split; try assumption.
  split; try assumption.
  exists p3, p4, phpdp3p4, bp3, bp4, bp3p4, o3, o4, g3, g4, ghpg3g4, bg3, bg4, bg3g4, opo3o4.
  split; try assumption.
  split; try assumption.
  apply tmp4.
Qed.

Lemma subsa_nodes':
  forall size x z front rear,
    nodes (Enum front) (Enum rear) size |= subsa (nodes (Enum front) (Enum rear) size) (subse x z).
Proof.
  induction size.
  simpl.
  intros.
  assumption.
  intros.
  destruct SAT as (v,(v0,(p1,(p2,(phpdp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(g1,(g2,(ghpg1g2,(bg1,(bg2,(bg1g2,(opo1o2,(tmp1,(tmp2,tmp3))))))))))))))))))).
  destruct tmp2 as (p3,(p4,(phpdp3p4,(bp3,(bp4,(bp3p4,(o3,(o4,(g3,(g4,(ghpg3g4,(bg3,(bg4,(bg3g4,(opo3o4,(tmp2,(tmp4,tmp5))))))))))))))))).
  apply IHsize with (x:=x) (z:=z) in tmp4; try assumption.
  simpl.
  exists v, v0, p1, p2, phpdp1p2, bp1, bp2, bp1p2, o1, o2, g1, g2, ghpg1g2, bg1, bg2, bg1g2, opo1o2.
  split; try assumption.
  split; try assumption.
  exists p3, p4, phpdp3p4, bp3, bp4, bp3p4, o3, o4, g3, g4, ghpg3g4, bg3, bg4, bg3g4, opo3o4.
  split; try assumption.
  split; try assumption.
Qed.

Lemma subsa_queue:
  forall q sinv x z,
    subsa (queue q sinv) (subse x z) |= queue q sinv.
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(rest1,(rest2,rest3)))))))))))))))))))).
  destruct rest2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp3p4,(o3,(o4,(c3,(c4,(ghpdefc3c4,(bc3,(bc4,(bc34,(opo3o4,(rest4,(rest5,rest6))))))))))))))))).
  destruct rest5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp5p6,(o5,(o6,(c5,(c6,(ghpdefc5c6,(bc5,(bc6,(bc56,(opo5o6,(rest7,(rest8,rest9))))))))))))))))).
  destruct rest8 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(ops78,(tmp5,(p78,C78)))))))))))))))))).
  apply subsa_nodes in tmp5; try assumption.
  exists v, v0, v1, p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split. assumption.
  split.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp3p4, o3, o4, c3, c4, ghpdefc3c4, bc3, bc4, bc34, opo3o4.
  split. assumption.
  split.
  exists p5, p6, phpdefp5p6, bp5, bp6, bp5p6, o5, o6, c5, c6, ghpdefc5c6, bc5, bc6, bc56, opo5o6.
  split. assumption.
  split.
  exists p7, p8, phpdefp7p8, bp7, bp8, bp78, O7, O8, C7, C8, ghpdefC7C8, BC7, BC8, bc78, opO7O8.
  split. assumption.
  split. assumption.
  split; assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma subsa_queue2:
  forall q sinv x z x' z',
    subsa (subsa (queue q sinv) (subse x z)) (subse x' z') |= queue q sinv.
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(rest1,(rest2,rest3)))))))))))))))))))).
  destruct rest2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp3p4,(o3,(o4,(c3,(c4,(ghpdefc3c4,(bc3,(bc4,(bc34,(opo3o4,(rest4,(rest5,rest6))))))))))))))))).
  destruct rest5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp5p6,(o5,(o6,(c5,(c6,(ghpdefc5c6,(bc5,(bc6,(bc56,(opo5o6,(rest7,(rest8,rest9))))))))))))))))).
  destruct rest8 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(ops78,(tmp5,(p78,C78)))))))))))))))))).
  apply subsa_nodes2 in tmp5; try assumption.
  exists v, v0, v1, p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split. assumption.
  split.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp3p4, o3, o4, c3, c4, ghpdefc3c4, bc3, bc4, bc34, opo3o4.
  split. assumption.
  split.
  exists p5, p6, phpdefp5p6, bp5, bp6, bp5p6, o5, o6, c5, c6, ghpdefc5c6, bc5, bc6, bc56, opo5o6.
  split. assumption.
  split.
  exists p7, p8, phpdefp7p8, bp7, bp8, bp78, O7, O8, C7, C8, ghpdefC7C8, BC7, BC8, bc78, opO7O8.
  split. assumption.
  split. assumption.
  split; assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma subsa_queue3:
  forall q sinv x z x' z' x'' z'',
    subsa (subsa (subsa (queue q sinv) (subse x z)) (subse x' z')) (subse x'' z'') |= queue q sinv.
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(rest1,(rest2,rest3)))))))))))))))))))).
  destruct rest2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp3p4,(o3,(o4,(c3,(c4,(ghpdefc3c4,(bc3,(bc4,(bc34,(opo3o4,(rest4,(rest5,rest6))))))))))))))))).
  destruct rest5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp5p6,(o5,(o6,(c5,(c6,(ghpdefc5c6,(bc5,(bc6,(bc56,(opo5o6,(rest7,(rest8,rest9))))))))))))))))).
  destruct rest8 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(ops78,(tmp5,(p78,C78)))))))))))))))))).
  apply subsa_nodes3 in tmp5; try assumption.
  exists v, v0, v1, p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split. assumption.
  split.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp3p4, o3, o4, c3, c4, ghpdefc3c4, bc3, bc4, bc34, opo3o4.
  split. assumption.
  split.
  exists p5, p6, phpdefp5p6, bp5, bp6, bp5p6, o5, o6, c5, c6, ghpdefc5c6, bc5, bc6, bc56, opo5o6.
  split. assumption.
  split.
  exists p7, p8, phpdefp7p8, bp7, bp8, bp78, O7, O8, C7, C8, ghpdefC7C8, BC7, BC8, bc78, opO7O8.
  split. assumption.
  split. assumption.
  split; assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma subsa_queue2':
  forall q sinv x z x' z',
    queue q sinv |= subsa (subsa (queue q sinv) (subse x z)) (subse x' z').
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(rest1,(rest2,rest3)))))))))))))))))))).
  destruct rest2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp3p4,(o3,(o4,(c3,(c4,(ghpdefc3c4,(bc3,(bc4,(bc34,(opo3o4,(rest4,(rest5,rest6))))))))))))))))).
  destruct rest5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp5p6,(o5,(o6,(c5,(c6,(ghpdefc5c6,(bc5,(bc6,(bc56,(opo5o6,(rest7,(rest8,rest9))))))))))))))))).
  destruct rest8 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(ops78,(tmp5,(p78,C78)))))))))))))))))).
  eapply subsa_nodes2' in tmp5; try assumption.
  exists v, v0, v1, p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split. assumption.
  split.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp3p4, o3, o4, c3, c4, ghpdefc3c4, bc3, bc4, bc34, opo3o4.
  split. assumption.
  split.
  exists p5, p6, phpdefp5p6, bp5, bp6, bp5p6, o5, o6, c5, c6, ghpdefc5c6, bc5, bc6, bc56, opo5o6.
  split. assumption.
  split.
  exists p7, p8, phpdefp7p8, bp7, bp8, bp78, O7, O8, C7, C8, ghpdefC7C8, BC7, BC8, bc78, opO7O8.
  split. assumption.
  split. apply tmp5.
  split; assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma subsa_queue3':
  forall q sinv x z x' z' x'' z'',
    queue q sinv |= subsa (subsa (subsa (queue q sinv) (subse x z)) (subse x' z')) (subse x'' z'').
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(rest1,(rest2,rest3)))))))))))))))))))).
  destruct rest2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp3p4,(o3,(o4,(c3,(c4,(ghpdefc3c4,(bc3,(bc4,(bc34,(opo3o4,(rest4,(rest5,rest6))))))))))))))))).
  destruct rest5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp5p6,(o5,(o6,(c5,(c6,(ghpdefc5c6,(bc5,(bc6,(bc56,(opo5o6,(rest7,(rest8,rest9))))))))))))))))).
  destruct rest8 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(ops78,(tmp5,(p78,C78)))))))))))))))))).

  eapply subsa_nodes3' in tmp5; try assumption.
  exists v, v0, v1, p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split. assumption.
  split.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp3p4, o3, o4, c3, c4, ghpdefc3c4, bc3, bc4, bc34, opo3o4.
  split. assumption.
  split.
  exists p5, p6, phpdefp5p6, bp5, bp6, bp5p6, o5, o6, c5, c6, ghpdefc5c6, bc5, bc6, bc56, opo5o6.
  split. assumption.
  split.
  exists p7, p8, phpdefp7p8, bp7, bp8, bp78, O7, O8, C7, C8, ghpdefC7C8, BC7, BC8, bc78, opO7O8.
  split. assumption.
  split. apply tmp5.
  split; assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma subsa_queue':
  forall q sinv x z,
    queue q sinv |= subsa (queue q sinv) (subse x z).
Proof.
  simpl.
  intros.
  destruct SAT as (v,(v0,(v1,(p1,(p2,(phpdefp1p2,(bp1,(bp2,(bp1p2,(o1,(o2,(c1,(c2,(ghpdefc1c2,(bc1,(bc2,(bc12,(opo1o2,(rest1,(rest2,rest3)))))))))))))))))))).
  destruct rest2 as (p3,(p4,(phpdefp3p4,(bp3,(bp4,(bp3p4,(o3,(o4,(c3,(c4,(ghpdefc3c4,(bc3,(bc4,(bc34,(opo3o4,(rest4,(rest5,rest6))))))))))))))))).
  destruct rest5 as (p5,(p6,(phpdefp5p6,(bp5,(bp6,(bp5p6,(o5,(o6,(c5,(c6,(ghpdefc5c6,(bc5,(bc6,(bc56,(opo5o6,(rest7,(rest8,rest9))))))))))))))))).
  destruct rest8 as (p7,(p8,(phpdefp7p8,(bp7,(bp8,(bp78,(O7,(O8,(C7,(C8,(ghpdefC7C8,(BC7,(BC8,(bc78,(opO7O8,(ops78,(tmp5,(p78,C78)))))))))))))))))).
  apply subsa_nodes' with (x:=x) (z:=z) in tmp5; try assumption.
  exists v, v0, v1, p1, p2, phpdefp1p2, bp1, bp2, bp1p2, o1, o2, c1, c2, ghpdefc1c2, bc1, bc2, bc12, opo1o2.
  split. assumption.
  split.
  exists p3, p4, phpdefp3p4, bp3, bp4, bp3p4, o3, o4, c3, c4, ghpdefc3c4, bc3, bc4, bc34, opo3o4.
  split. assumption.
  split.
  exists p5, p6, phpdefp5p6, bp5, bp6, bp5p6, o5, o6, c5, c6, ghpdefc5c6, bc5, bc6, bc56, opo5o6.
  split. assumption.
  split.
  exists p7, p8, phpdefp7p8, bp7, bp8, bp78, O7, O8, C7, C8, ghpdefC7C8, BC7, BC8, bc78, opO7O8.
  split. assumption.
  split. assumption.
  split; assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma subs_enqueue:
  forall se e value nd rear tmp
    (EQ1: se (Eplus e (Enum 1)) = Eplus (se e) (Enum 1))
    (EQ2: se (Evar rear) = Evar rear)
    (EQ3: se (Evar nd) = Evar nd)
    (EQ4: se (Eplus (Evar rear) (Enum 1)) = Eplus (Evar rear) (Enum 1))
    (EQ5: se (Enum value) = Enum value),
    subs (enqueue e value nd rear tmp) se = enqueue (se e) value nd rear tmp.
Proof.
  unfold enqueue.
  simpl.
  intros.
  rewrite EQ1, EQ2, EQ3, EQ4, EQ5.
  reflexivity.
Qed.

Lemma subs_dequeue:
  forall se e front next_front tmp
    (EQ1: se (Evar front) = Evar front)
    (EQ2: se (Evar next_front) = Evar next_front)
    (EQ3: se (Eplus (Evar front) (Enum 1)) = Eplus (Evar front) (Enum 1)),
    subs (dequeue e front next_front tmp) se = dequeue (se e) front next_front tmp.
Proof.
  unfold dequeue.
  simpl.
  intros.
  rewrite EQ1, EQ2, EQ3.
  reflexivity.
Qed.

Lemma subs_size_of:
  forall se e size last front rear lastval nextnode incv tmp
    (EQ2: se (Evar last) = Evar last)
    (EQ3: se (Evar front) = Evar front)
    (EQ4: se (Evar size) = Evar size)
    (EQ5: se (Eplus e (Enum 1)) = Eplus (se e) (Enum 1))
    (EQ6: se (Evar lastval) = Evar lastval)
    (EQ7: se (Evar rear) = Evar rear)
    (EQ8: se (Evar nextnode) = Evar nextnode)
    (EQ9: se (Eplus (Evar incv) (Enum 1)) = Eplus (Evar incv) (Enum 1))
    (EQ10: se (Eplus (Evar lastval) (Eneg (Evar rear))) = Eplus (se (Evar lastval)) (Eneg (se (Evar rear))))
    (EQ11: se (Eplus (Evar rear) (Eneg (Evar lastval))) = Eplus (se (Evar rear)) (Eneg (se (Evar lastval))))
    (EQ12: se (Enum 0) = Enum 0)
    (EQ13: se (Enum 1) = Enum 1),
    subs (size_of e size last front rear lastval nextnode incv tmp) se = size_of (se e) size last front rear lastval nextnode incv tmp.
Proof.
  unfold size_of.
  simpl.
  intros.
  rewrite subs_not_equal; try assumption.
  rewrite subs_inc; try assumption.
  rewrite EQ2, EQ3, EQ4, EQ5, EQ6, EQ7, EQ8.
  reflexivity.
Qed.

Opaque enqueue.
Opaque dequeue.
Opaque size_of.
Opaque nodes.
Opaque queue.


(** # <font size="5"><b> Channels </b></font> # *)

Definition new_channel (ch q nd m v tmp tmp1: Z) :=
  Let ch (Cons 3)
  (Let q (new_queue q nd tmp1)
  (Let tmp (Mutate (Evar ch) (Evar q))
  (Let m Newlock
  (Let tmp (Mutate (Eplus (Evar ch) (Enum 1)) (Evar m))
  (Let tmp nop (* g_newctr *)
  (Let v Newcond
  (Let tmp nop (* g_initc *)
  (Let tmp (Mutate (Eplus (Evar ch) (Enum 2)) (Evar v))
  (Let tmp nop (* g_ctrinc *)
  (Let tmp nop (* g_chrgu *)
  (Let tmp nop (* g_initl *)
  (Let tmp nop (* g_finlc *)
  (Val (Evar ch)))))))))))))).

Definition send (ch: exp) (value m1 v1 q1 nd1 rear1 tmp1 tmp2: Z) := 
  Let m1 (Lookup (Eplus ch (Enum 1)))
  (Let v1 (Lookup (Eplus ch (Enum 2)))
  (Let tmp1 (Acquire (Evar m1))
  (Let tmp1 (Let tmp1 nop (* g_ctrinc or nop *)
            (Notify (Evar v1)))
  (Let q1 (Lookup ch)
  (Let tmp1 (enqueue (Evar q1) value nd1 rear1 tmp2)
  (Let tmp1 nop (* g_disch *)
  (Release (Evar m1)))))))).

Definition receive (ch: exp) (q m v s size last front1 front2 next_front rear lastval nextnode incv tmp tmp1 tmp2: Z) := 
  Let m (Lookup (Eplus ch (Enum 1)))
  (Let v (Lookup (Eplus ch (Enum 2)))
  (Let tmp (Acquire (Evar m))
  (Let q (Lookup ch)
  (Let tmp (While (Let s (size_of (Evar q) size last front1 rear lastval nextnode incv tmp1) (Val (Eplus (Enum 1) (Eneg (Evar s)))))
             (Let tmp nop (* g_ctrdec *)
             (Wait (Evar v) (Evar m))))
  (Let tmp (dequeue (Evar q) front2 next_front tmp2)
  (Let tmp nop (* g_ctrdec *)
  (Release (Evar m)))))))).


Definition gcM: Z := 500.
Definition chInv: Z := 501.
Definition gcInv: Z := 502.
Definition vInv: Z := 503.

Definition new_channel_level := 0%Qc.
Definition receive_level := 1%Q.
Definition send_level := 1%Q.

Definition LinvIndex : Z := 0.
Definition MIndex : Z := 1.

Definition Linv (ch gv: Z) := (LinvIndex, (chInv,ch)::(gcInv,gv)::nil).
Definition Mv (gv: Z) := (MIndex, (gcM,gv)::nil).

Definition channel_inv : inv := let ch := chInv in let gc := gcInv in 
  fun Wt => fun Ot =>
  EX q, (EX size, (EX Ct, (EX v, (EX fq, (EX fv, (
  Aprop (Qclt 0 fq /\ Qclt fq 1 /\ Qclt 0 fv /\ Qclt fv 1) **
  Apointsto fq (cell_loc (Evar ch)) (Enum q) **
  Apointsto fv (next_loc (next_loc (cell_loc (Evar ch)))) (Enum v) **
  queue q size **
  Actr (Evar gc) Ct **
  Abool (andb (Nat.leb (Wt v)%nat (Ot v)%nat)
        (Nat.leb (Wt v + Ct) (Ot v + size))))))))).

Definition M_transfer : inv := let gc := gcM in 
  fun Wt => fun Ot => Atic (Evar gc).

Definition channels_invs : Z -> inv :=
  fun z => if (Z.eq_dec z LinvIndex) then channel_inv
           else if (Z.eq_dec z MIndex) then M_transfer
           else fun _ => fun _ => Abool (true).

Definition channel (ch gv : Z) (v: location Z) :=
  EX m, (EX fm, (EX fv, (
  Aprop ((Qclt 0 fm /\ Qclt fm 1 /\ Qclt 0 fv /\ Qclt fv 1) /\
  v = (Aof v, Rof v, ([[m]]), None, false, ND, Mv gv, nil)) **
  Apointsto fm (next_loc (cell_loc (Enum ch))) m **
  Apointsto fv (next_loc (next_loc (cell_loc (Enum ch)))) (Enum (Aof v)) **
  Alock (m, new_channel_level, m, None, false, Linv ch gv, ND, nil) **
  Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)))).

Local Open Scope Qc.

Theorem rule_new_channel (r:Qc) O ch q nd m v tmp tmp1 (NODUP: NoDup(ch::q::nd::m::v::tmp::tmp1::nil)): correct
  (Aobs O)
  (new_channel ch q nd m v tmp tmp1)
  (fun ch => EX v, (EX gv, (Aobs (Oof v::O) ** channel ch gv (evall v) ** Atic (Enum gv) &* (Abool (Qeq_bool (Rof v) r))))) channels_invs false.
Proof.
  assert (fracb: 0 < frac /\ frac < 1). apply frac_bound. destruct fracb as (frb1,frb2).
  apply rule_Let with (fun r' => fold_left Astar (points_tos (seq 0 3)(cell_loc (Enum r'))) (Abool true) ** Aobs O).
  apply rule_conseq1 with (Abool true ** Aobs O).
  apply rule_frame.
  apply rule_Cons.
  {
  intros.
  apply rule_pure_star'; try assumption.
  split. simpl. trivial. assumption.
  }
  simpl.
  intros.
  rewrite eqz.
  rewrite neqz; try omega.
  rewrite neqz; try omega.
  rewrite neqz; try omega.
  rewrite neqz; try omega.
  apply rule_Let with (fun q => queue q 0 ** (fold_left Astar (points_tos (seq 0 3)(cell_loc (Enum z))) (Abool true)) ** Aobs O).
  simpl.
  apply rule_conseq with (Abool true ** 
    array (cell_loc (Enum z)) 0 |-> Enum 0 **
    array (cell_loc (Enum z)) 1 |-> Enum 0 **
    array (cell_loc (Enum z)) 2 |-> Enum 0 ** Aobs O)
    (fun q => queue q 0 **
    array (cell_loc (Enum z)) 0 |-> Enum 0 **
    array (cell_loc (Enum z)) 1 |-> Enum 0 **
    array (cell_loc (Enum z)) 2 |-> Enum 0 ** Aobs O).
   apply rule_frame.
  apply rule_new_queue.
  {
  inversion NODUP.
  replace (q :: nd :: tmp1 :: nil) with ((q::nd::nil) ++ (tmp1::nil)).
  apply NoDup_remove_1 with m. simpl.
  replace (q :: nd :: m :: tmp1 :: nil) with ((q :: nd :: m :: nil) ++ (tmp1 :: nil)).
  apply NoDup_remove_1 with v. simpl.
  replace (q :: nd :: m :: v :: tmp1 :: nil) with ((q :: nd :: m :: v :: nil) ++ (tmp1 :: nil)).
  apply NoDup_remove_1 with tmp. simpl. assumption.
  reflexivity. reflexivity. reflexivity.
  }
  {
  intros.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  }
  {
  intros.
  apply sat_star_imps with (queue z0 0)
         (array (cell_loc (Enum z)) 0 |-> Enum 0 **
         array (cell_loc (Enum z)) 1 |-> Enum 0 **
         array (cell_loc (Enum z)) 2 |-> Enum 0 ** Aobs O); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_pure_star'; try assumption.
  split. simpl. trivial. assumption.
  }
  simpl.
  intros.
  rewrite eqz.
  rewrite neqz; try omega.
  rewrite neqz; try omega.
  apply rule_Let with (fun _ => cell_loc (Enum z) |-> Enum z0 **
    queue z0 0 **
    cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum 0 **
    cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 ** Aobs O).
  apply rule_conseq1 with (cell_loc (Enum z) |-> Enum 0 **
    queue z0 0 **
    cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum 0 **
    cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 ** Aobs O).
  apply rule_frame.
  apply rule_Mutate.
  {
  intros.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT1,SAT).
  apply sat_star_imps with (array (cell_loc (Enum z)) 0 |-> Enum 0)
         (array (cell_loc (Enum z)) 1 |-> Enum 0 **
         array (cell_loc (Enum z)) 2 |-> Enum 0 ** Aobs O ** queue z0 0); try assumption.
  intros.
  apply sat_array; assumption.
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply sat_star_imps with (((array (cell_loc (Enum z)) 1 |-> Enum 0 **
            array (cell_loc (Enum z)) 2 |-> Enum 0) ** 
           Aobs O)) (queue z0 0); try assumption.
  intros.
  apply rule_assoc in SAT2; try assumption.
  intros. assumption.
  }
  simpl.
  intros.
  rewrite neqz; try omega.
  rewrite neqz; try omega.
  apply rule_Let with (fun z' => Aulock ((Enum z',new_channel_level,Enum z',None,false),ND,ND,nil) empb empb **
   cell_loc (Enum z) |-> Enum z0 **
   queue z0 0 **
   cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum 0 **
   cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 ** Aobs O).
  apply rule_conseq1 with (Abool true **
    cell_loc (Enum z) |-> Enum z0 **
    queue z0 0 **
    cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum 0 **
    cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 ** Aobs O).
  apply rule_frame.
  apply rule_Newlock.
  {
  intros.
  apply rule_pure_star'; try assumption.
  split. simpl. trivial. assumption.
  }
  simpl.
  intros.
  rewrite eqz.
  rewrite neqz; try omega.
  apply rule_Let with (fun _ => cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
    Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil) empb empb **
    cell_loc (Enum z) |-> Enum z0 **
    queue z0 0 **
    cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 ** Aobs O).
  apply rule_conseq1 with (cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum 0 **
    Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil) empb empb **
    cell_loc (Enum z) |-> Enum z0 **
    queue z0 0 **
    cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 ** Aobs O).
  apply rule_frame.
  apply rule_Mutate.
  {
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Aulock
           (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil)
           empb empb)
         (cell_loc (Enum z) |-> Enum z0 **
         queue z0 0 **
         cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum 0 **
         cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 ** Aobs O); try assumption.
  intros. assumption.
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply sat_star_imps with (((cell_loc (Enum z) |-> Enum z0 ** queue z0 0) **
           cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum 0))
          (cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 ** Aobs O); try assumption.
  intros.
  apply rule_comm in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  intros. assumption.
  }
  simpl.
  intros.
  rewrite neqz; try omega.
  apply rule_Let with (fun _ => (EX gc, Actr (Enum gc) 0) **
    cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
    Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil) empb empb **
    cell_loc (Enum z) |-> Enum z0 **
    queue z0 0 ** cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 ** Aobs O).
  apply rule_conseq1 with (Abool true **
    cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
    Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil) empb empb **
    cell_loc (Enum z) |-> Enum z0 **
    queue z0 0 ** cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 ** Aobs O).
  apply rule_frame.
  apply rule_g_newctr.
  {
  intros.
  apply rule_pure_star'; try assumption.
  split. simpl. reflexivity. assumption.
  }
  simpl.
  intros.
  rewrite neqz; try omega.
  apply rule_Let with (fun z' => Aucond ((Enum z',r,Enum z',None,false),ND, ND,nil) **
   (EX gc, Actr (Enum gc) 0) **
   cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
   Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil) empb empb **
   cell_loc (Enum z) |-> Enum z0 **
   queue z0 0 ** cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 ** Aobs O).
  apply rule_conseq1 with (Abool true **
    (EX gc, Actr (Enum gc) 0) **
    cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
    Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil) empb empb **
    cell_loc (Enum z) |-> Enum z0 **
    queue z0 0 ** cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 ** Aobs O).
  apply rule_frame.
  apply rule_Newcond.
  {
  intros.
  apply rule_pure_star'; try assumption.
  split. simpl. reflexivity. assumption.
  }
  simpl.
  intros.
  rewrite eqz.
  apply rule_conseq1 with (EX gc, (Aucond (Enum z5, r, Enum z5, None, false, ND, ND, nil) **
    Actr (Enum gc) 0 **
    cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
    Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil) empb empb **
    cell_loc (Enum z) |-> Enum z0 **
    queue z0 0 **
    cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 ** Aobs O)).
  apply rule_exists1.
  intros gc.
  apply rule_Let with (fun _ => (Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil) empb empb **
    Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)) **
    Actr (Enum gc) 0 **
    cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
    cell_loc (Enum z) |-> Enum z0 **
    queue z0 0 ** cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 ** Aobs O).
  apply rule_conseq1 with ((Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil) empb empb **
    Aucond (Enum z5, r, Enum z5, None, false, ND, ND, nil)) **
    Actr (Enum gc) 0 **
    cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
    cell_loc (Enum z) |-> Enum z0 **
    queue z0 0 ** cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 ** Aobs O).
  apply rule_frame.
  apply rule_g_initc.
  {
  intros.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with ((((Aucond (Enum z5, r, Enum z5, None, false, ND, ND, nil) **
            Actr (Enum gc) 0) **
           cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2) **
          Aulock
            (Enum z2, new_channel_level, Enum z2, None, false, ND,
            ND, nil) empb empb))
         (cell_loc (Enum z) |-> Enum z0 **
         queue z0 0 **
         cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 ** Aobs O); try assumption.
  intros.
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Aulock
            (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil)
            empb empb)
          ((Aucond (Enum z5, r, Enum z5, None, false, ND, ND, nil) **
           Actr (Enum gc) 0) **
          cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc in SAT1; try assumption.
  intros. assumption.
  }
  simpl.
  intros.
  apply rule_Let with (fun _ => cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum z5 **
    (Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil) empb empb **
    Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)) **
    Actr (Enum gc) 0 **
    cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
    cell_loc (Enum z) |-> Enum z0 **
    queue z0 0 ** Aobs O).
  apply rule_conseq1 with (cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 **
    (Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil) empb empb **
    Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)) **
    Actr (Enum gc) 0 **
    cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
    cell_loc (Enum z) |-> Enum z0 **
    queue z0 0 ** Aobs O).
  apply rule_frame.
  apply rule_Mutate.
  {
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with ((Aulock
            (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil)
            empb empb **
          Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)))
         (Actr (Enum gc) 0 **
         cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
         cell_loc (Enum z) |-> Enum z0 **
         queue z0 0 **
         cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0 ** Aobs O); try assumption.
  intros. assumption.
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (((((Actr (Enum gc) 0 **
              cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2) **
             cell_loc (Enum z) |-> Enum z0) ** queue z0 0) **
           cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0))
          (Aobs O); try assumption.
  intros.
  apply rule_comm in SAT1; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum 0)
          (((Actr (Enum gc) 0 **
            cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2) **
           cell_loc (Enum z) |-> Enum z0) ** queue z0 0); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc in SAT2; try assumption.
  apply rule_assoc in SAT2; try assumption.
  intros. assumption.
  }
  simpl.
  intros.
  apply rule_Let with (fun _ => (Actr (Enum gc) (S 0) ** Atic (Enum gc)) **
    cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum z5 **
    Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil)
    empb empb ** Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
    cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
    cell_loc (Enum z) |-> Enum z0 ** queue z0 0 ** Aobs O).
  apply rule_conseq1 with  (Actr (Enum gc) 0 **
    cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum z5 **
    Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil)
    empb empb ** Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
    cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
    cell_loc (Enum z) |-> Enum z0 ** queue z0 0 ** Aobs O).
  apply rule_frame.
  apply rule_g_ctrinc.
  {
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum z5)
         ((Aulock
            (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil)
            empb empb **
          Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)) **
         Actr (Enum gc) 0 **
         cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
         cell_loc (Enum z) |-> Enum z0 ** queue z0 0 ** Aobs O); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Aulock
            (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil)
            empb empb)
          (Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
          Actr (Enum gc) 0 **
          cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
          cell_loc (Enum z) |-> Enum z0 ** queue z0 0 ** Aobs O); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil))
          (Actr (Enum gc) 0 **
          cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
          cell_loc (Enum z) |-> Enum z0 ** queue z0 0 ** Aobs O); try assumption.
  intros. assumption.
  intros.
  apply rule_comm; try assumption.
  }
  simpl. intros.
  apply rule_Let with (fun _ =>
    (Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
    Aobs (Oof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) :: O) **
    Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil) empb
    (upd Z.eq_dec empb ([[Aof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)]])
    (empb ([[Aof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)]]) + 1)%nat)) **
    Actr (Enum gc) (S 0) ** Atic (Enum gc) **
    cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum z5 **
    cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
    cell_loc (Enum z) |-> Enum z0 ** queue z0 0).
  apply rule_conseq1 with (
    (Abool (Z.eqb ([[Lof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)]])
    ([[Aof (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil)]])) &*
    Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
    Aobs O **
    Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil) empb empb) **
    Actr (Enum gc) (S 0) ** Atic (Enum gc) **
    cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum z5 **
    cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
    cell_loc (Enum z) |-> Enum z0 ** queue z0 0).
  apply rule_frame.
  apply rule_g_chrgu.
  {
  intros.
  apply rule_assoc_pure'; try assumption.
  split. simpl. apply Z.eqb_eq. reflexivity.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (Actr (Enum gc) 1)
         (Atic (Enum gc) **
         cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum z5 **
         Aulock
           (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil)
           empb empb **
         Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
         cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
         cell_loc (Enum z) |-> Enum z0 ** queue z0 0 ** Aobs O); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Atic (Enum gc))
          (cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum z5 **
          Aulock
            (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil)
            empb empb **
          Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
          cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
          cell_loc (Enum z) |-> Enum z0 ** queue z0 0 ** Aobs O); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum z5)
          (Aulock
            (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil)
            empb empb **
          Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
          cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
          cell_loc (Enum z) |-> Enum z0 ** queue z0 0 ** Aobs O); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply sat_star_imps with (Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil) empb empb)
          (Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
          cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
          cell_loc (Enum z) |-> Enum z0 ** queue z0 0 ** Aobs O); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_assoc' in SAT3; try assumption.
  apply sat_star_imps with ((((Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
             cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2) ** cell_loc (Enum z) |-> Enum z0) **
           queue z0 0)) (Aobs O); try assumption.
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc in SAT4; try assumption.
  apply rule_assoc in SAT4; try assumption.
  intros. assumption.
  }
  simpl. intros.
  apply rule_Let with (fun _ => (Alock (Enum z2, new_channel_level, Enum z2, None, false, Linv z gc, ND, nil) **
    Aobs (Oof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) :: O)) ** 
    Atic (Enum gc) **
    EX fq, (EX fm, (EX fv, (Aprop (Qclt 0 fq /\ Qclt fq 1 /\ Qclt 0 fm /\ Qclt fm 1 /\ Qclt 0 fv /\ Qclt fv 1)) **
    Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5) **
    Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
    Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
    Apointsto fq (cell_loc (Enum z)) (Enum z0)))).
  apply rule_conseq1 with ((Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil) empb (upd Z.eq_dec empb z5 1%nat) **
    subsas (snd (Linv z gc)) (channels_invs (fst (Linv z gc)) empb (upd Z.eq_dec empb z5 1%nat)) ** 
    Aobs (Oof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) :: O)) **
    Atic (Enum gc) **
    EX fq, (EX fm, (EX fv, (Aprop (Qclt 0 fq /\ Qclt fq 1 /\ Qclt 0 fm /\ Qclt fm 1 /\ Qclt 0 fv /\ Qclt fv 1)) **
    Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5) **
    Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
    Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
    Apointsto fq (cell_loc (Enum z)) (Enum z0)))).
  apply rule_frame.
  apply rule_g_initl.
  {
  intros.
  apply rule_assoc; try assumption.
  apply rule_exists_dist2; try assumption.
  exists frac.
  apply rule_exists_dist2; try assumption.
  exists frac.
  apply rule_exists_dist2; try assumption.
  exists frac.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_prop_star'; try assumption.
  split.
  repeat split; try apply frac_bound.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil))
         ((Aobs (Oof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) :: O) **
          Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil)
            empb (upd Z.eq_dec empb z5 1%nat)) **
         Actr (Enum gc) 1 **
         Atic (Enum gc) **
         cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum z5 **
         cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2 **
         cell_loc (Enum z) |-> Enum z0 ** queue z0 0); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply sat_star_imps with (cell_loc (Eplus (Enum z) (Enum 1)) |-> Enum z2)
          ((cell_loc (Enum z) |-> Enum z0 ** queue z0 0) **
          (((Aobs (Oof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) :: O) **
             Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil)
               empb (upd Z.eq_dec empb z5 1%nat)) ** Actr (Enum gc) 1) **
           Atic (Enum gc)) ** cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum z5); try assumption.
  intros.
  apply rule_points_to_leak with 1; try assumption.
  apply Qclt_le_weak. apply frac_bound.
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_comm in SAT1; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply rule_comm in SAT1; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply sat_star_imps with (Aulock (Enum z2, new_channel_level, Enum z2, None, false, ND, ND, nil) empb
            (upd Z.eq_dec empb z5 1%nat))
          ((Actr (Enum gc) 1 **
           Atic (Enum gc) **
           cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum z5 **
           cell_loc (Enum z) |-> Enum z0 ** queue z0 0) **
          Aobs (Oof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) :: O)); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_comm in SAT2; try assumption.
  apply sat_star_imps with (Aobs (Oof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) :: O))
          (Actr (Enum gc) 1 **
          Atic (Enum gc) **
          cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum z5 **
          cell_loc (Enum z) |-> Enum z0 ** queue z0 0); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply rule_comm in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply sat_star_imps with (Atic (Enum gc))
          ((cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum z5 **
           cell_loc (Enum z) |-> Enum z0 ** queue z0 0) ** Actr (Enum gc) 1); try assumption.
  intros. assumption.
  intros.


  apply sat_star_imps with (Apointsto frac (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5) **
    Apointsto frac (cell_loc (Enum z)) (Enum z0))
   (
EX q, (EX size, (EX Ct, (EX v, (EX fq, (EX fv, (
  Aprop (Qclt 0 fq /\ Qclt fq 1 /\ Qclt 0 fv /\ Qclt fv 1) **
  Apointsto fq (cell_loc (Enum z)) (Enum q) **
  Apointsto fv (next_loc (next_loc (cell_loc (Enum z)))) (Enum v) **
  (subsa (subsa (queue q size) (subse chInv z)) (subse gcInv gc)) **
  Actr (Enum gc) Ct **
  Abool (andb (Nat.leb (empb v) ((upd Z.eq_dec empb z5 1%nat) v))
        (Nat.leb (empb v + Ct) ((upd Z.eq_dec empb z5 1%nat) v + size)))))))))
   ); try assumption.
  {
  apply rule_exists_dist2; try assumption.
  exists z0.
  apply rule_exists_dist2; try assumption.
  exists 0%nat.
  apply rule_exists_dist2; try assumption.
  exists 1%nat.
  apply rule_exists_dist2; try assumption.
  exists z5.
  apply rule_exists_dist2; try assumption.
  exists frac.
  apply rule_exists_dist2; try assumption.
  exists frac.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_prop_star'; try assumption.
  split. simpl.
  repeat split; try apply frac_bound.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (Apointsto 1%Qc (cell_loc (Enum z)) (Enum z0) **
    Apointsto frac (next_loc (next_loc (cell_loc (Enum z)))) (Enum z5) **
    subsa (subsa (queue z0 0) (subse chInv z)) (subse gcInv gc) **
    Actr (Enum gc) 1 **
    Abool
      ((empb z5 <=? upd Z.eq_dec empb z5 1 z5)%nat &&
       (empb z5 + 1 <=? upd Z.eq_dec empb z5 1 z5 + 0)%nat))
   (Apointsto frac (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5)); try assumption.
  apply rule_assoc in SAT4; try assumption.
  apply rule_comm in SAT4; try assumption.
  apply rule_assoc in SAT4; try assumption.
  apply rule_assoc in SAT4; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (cell_loc (Enum z) |-> Enum z0)
          (queue z0 0 **
          Actr (Enum gc) 1 ** cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum z5); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (queue z0 0)
          (Actr (Enum gc) 1 ** cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum z5); try assumption.
  intros.

  apply subsa_queue' with (x:=gcInv) (z:=gc) in SAT6; assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Actr (Enum gc) 1) (cell_loc (Eplus (Enum z) (Enum 2)) |-> Enum z5); try assumption.
  intros. assumption.
  intros.
  apply rule_pure_star'; try assumption.
  split. simpl.
  unfold upd. rewrite eqz. reflexivity.
  apply sat_star_imps with (Apointsto frac (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5))
    (Apointsto frac (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5)); try assumption.
  apply rule_points_to_fraction'; try assumption.
  intros. assumption.
  intros.
  apply next_plus2; try assumption.
  intros.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (cell_loc (Enum z) |-> Enum z0)
          (Apointsto frac (next_loc (next_loc (cell_loc (Enum z)))) (Enum z5) **
          subsa (subsa (queue z0 0) (subse chInv z)) (subse gcInv gc) **
          Actr (Enum gc) 1 **
          Abool
            ((empb z5 <=? upd Z.eq_dec empb z5 1 z5)%nat &&
             (empb z5 + 1 <=? upd Z.eq_dec empb z5 1 z5 + 0)%nat)); try assumption.
  intros.
  apply rule_points_to_fraction'; try assumption.
  intros. assumption.
  intros. assumption.
  }
  intros. assumption.
  intros. assumption.
  }
  simpl.
  intros.
  apply rule_Let with (fun _ =>
    (Alock (Enum z2, new_channel_level, Enum z2, None, false, Linv z gc, ND, nil) **
    Acond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)) **
    (EX fq, (EX fm, (EX fv, (Aprop (Qclt 0 fq /\ Qclt fq 1 /\ Qclt 0 fm /\ Qclt fm 1 /\ Qclt 0 fv /\ Qclt fv 1)) &*
    Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5) **
    Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
    Apointsto fq (cell_loc (Enum z)) (Enum z0)))) **
    Aobs (Oof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) :: O) **
    Atic (Enum gc)).
  apply rule_conseq1 with (
    ((Abool (Z.eqb ([[Lof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)]])
    ([[Aof (Enum z2, new_channel_level, Enum z2, None, false, Linv z gc, ND, nil)]])) &*
    Aprop (spurious_ok false (evall (Enum z2, new_channel_level, Enum z2, None, false, Linv z gc, ND, nil))
     (evall (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)) channels_invs)) &*
    Alock (Enum z2, new_channel_level, Enum z2, None, false, Linv z gc, ND, nil) **
    Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)) **
    (EX fq, (EX fm, (EX fv, (Aprop (Qclt 0 fq /\ Qclt fq 1 /\ Qclt 0 fm /\ Qclt fm 1 /\ Qclt 0 fv /\ Qclt fv 1)) &*
    Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5) **
    Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
    Apointsto fq (cell_loc (Enum z)) (Enum z0)))) **
    Aobs (Oof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) :: O) **
    Atic (Enum gc)).
  apply rule_frame.
  apply rule_g_finlc.
  {
  intros.
  apply sat_star_imps with ((Abool
       (([[Lof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)]]) =?
        ([[Aof (Enum z2, new_channel_level, Enum z2, None, false, Linv z gc, ND, nil)]])) **
     Aprop
       (spurious_ok false
          (evall (Enum z2, new_channel_level, Enum z2, None, false, Linv z gc, ND, nil))
          (evall (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)) channels_invs)) **
    Alock (Enum z2, new_channel_level, Enum z2, None, false, Linv z gc, ND, nil) **
    Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil))
   ((EX fq,
    (EX fm,
     (EX fv,
      Aprop (0 < fq /\ fq < 1 /\ 0 < fm /\ fm < 1 /\ 0 < fv < 1) &*
      Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5) **
      Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
      Apointsto fq (cell_loc (Enum z)) (Enum z0)))) **
   Aobs (Oof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) :: O) ** Atic (Enum gc)); try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_pure_star'; try assumption.
  split. simpl. apply Z.eqb_eq. reflexivity.
  apply rule_prop_star'; try assumption.
  split. simpl. unfold spurious_ok. left. reflexivity.
  apply rule_assoc'; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (Alock (Enum z2, new_channel_level, Enum z2, None, false, Linv z gc, ND, nil))
         (Aobs (Oof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) :: O) **
         Atic (Enum gc) **
         (EX fq,
          (EX fm,
           (EX fv,
            Aprop (0 < fq /\ fq < 1 /\ 0 < fm /\ fm < 1 /\ 0 < fv < 1) **
            Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5) **
            Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
            Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
            Apointsto fq (cell_loc (Enum z)) (Enum z0))))); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Aobs (Oof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) :: O))
        (Atic (Enum gc) **
          (EX fq,
           (EX fm,
            (EX fv,
             Aprop (0 < fq /\ fq < 1 /\ 0 < fm /\ fm < 1 /\ 0 < fv < 1) **
             Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5) **
             Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
             Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
             Apointsto fq (cell_loc (Enum z)) (Enum z0))))); try assumption.
  intros. assumption.
  intros.
  apply sat_star_imps with (Atic (Enum gc))
          ((EX fq,
           (EX fm,
            (EX fv,
             Aprop (0 < fq /\ fq < 1 /\ 0 < fm /\ fm < 1 /\ 0 < fv < 1) **
             Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5) **
             Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
             Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
             Apointsto fq (cell_loc (Enum z)) (Enum z0))))); try assumption.
  intros. assumption.
  intros.
  destruct SAT2 as (fq,(fm,(fv,SAT2))).
  apply rule_exists_dist2; try assumption.
  exists fq.
  apply rule_exists_dist2; try assumption.
  exists fm.
  apply rule_exists_dist2; try assumption.
  exists fv.
  apply rule_comm; try assumption.
  apply rule_assoc_pureP'; try assumption.
  apply rule_star_pure in SAT2; try assumption.
  destruct SAT2 as (SAT2,SAT3).
  split. assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5))
          (Aicond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
          Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
          Apointsto fq (cell_loc (Enum z)) (Enum z0)); try assumption.
  intros. assumption.
  intros.
  apply rule_comm; try assumption.
  intros.
  apply rule_pure_prop_star'; try assumption.
  apply rule_assoc; try assumption.
  intros. assumption.
  }
  simpl.
  intros.
  apply rule_exists2 .
  exists (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil). 
  apply rule_exists2 .
  exists gc.
  apply rule_conseq2 with (fun z10 => channel z10 gc (evall (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)) **
    Aobs (Oof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) :: O) **
    Atic (Enum gc)).
  apply rule_conseq1 with ((Alock
      (Enum z2, new_channel_level, Enum z2, None, false, Linv z gc, ND, nil) ** Acond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
   (EX fq,
    (EX fm,
     (EX fv,
      Aprop (0 < fq /\ fq < 1 /\ 0 < fm /\ fm < 1 /\ 0 < fv < 1) &*
      Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5) **
      Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
      Apointsto fq (cell_loc (Enum z)) (Enum z0))))) **
   Aobs (Oof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) :: O) **
   Atic (Enum gc)).
  apply rule_frame.
  unfold channel.
  apply rule_exists2 .
  exists (Enum z2).
  apply rule_conseq1 with (EX fq, (EX fm, (EX fv, (
    Alock (Enum z2, new_channel_level, Enum z2, None, false, Linv z gc, ND, nil) **
    Acond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
    Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5) **
    Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
    Apointsto fq (cell_loc (Enum z)) (Enum z0) **
    Aprop (0 < fq /\ fq < 1 /\ 0 < fm /\ fm < 1 /\ 0 < fv < 1))))).
  apply rule_exists1.
  intros fq.
  apply rule_exists1.
  intros fm.
  apply rule_exists1.
  intros fv.
  apply rule_exists2.
  exists fm.
  apply rule_exists2.
  exists fv.
  apply rule_conseq1 with (Abool true **
    (Alock (Enum z2, new_channel_level, Enum z2, None, false, Linv z gc, ND, nil) **
    Acond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
    Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5) **
    Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
    Apointsto fq (cell_loc (Enum z)) (Enum z0) **
    Aprop (0 < fq /\ fq < 1 /\ 0 < fm /\ fm < 1 /\ 0 < fv < 1))).
simpl.
  apply rule_conseq2 with (fun z' => Abool (Z.eqb z' ([[Enum z]])) **
    (Alock (Enum z2, new_channel_level, Enum z2, None, false, Linv z gc, ND, nil) **
    Acond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
    Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5) **
    Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
    Apointsto fq (cell_loc (Enum z)) (Enum z0) **
    Aprop (0 < fq /\ fq < 1 /\ 0 < fm /\ fm < 1 /\ 0 < fv < 1))).
  apply rule_frame.
  apply rule_Val.
  {
  intros.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT1).
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_comm in SAT1; try assumption.
  apply rule_star_pure in SAT1; try assumption.
  destruct SAT1 as (SAT1,SAT2).
  apply rule_prop_star'; try assumption.
  split.
  simpl.
  split.
  destruct SAT1 as (s1,(s2,(s3,(s4,s5)))).
  split. assumption. split. assumption. assumption.
  reflexivity.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply Z.eqb_eq in SAT.
  rewrite SAT in *.
  apply sat_star_imps with (Alock
            (Enum z2, new_channel_level, Enum z2, None, false, Linv z gc, ND, nil))
          (Acond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) **
          Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5) **
          Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
          Apointsto fq (cell_loc (Enum z)) (Enum z0)); try assumption.
  intros. assumption.
  intros.
  apply sat_star_imps with (Acond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil))
          (Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5) **
          Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
          Apointsto fq (cell_loc (Enum z)) (Enum z0)); try assumption.
  intros. assumption.
  intros.
  apply rule_comm; try assumption.
  apply sat_star_imps with (Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5))
          (Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
          Apointsto fq (cell_loc (Enum z)) (Enum z0)); try assumption.
  intros. apply next_plus2; try assumption.
  intros.
  apply rule_star_pure in SAT4; try assumption.
  destruct SAT4. assumption.
  }
  {
  intros.
  apply rule_pure_star'; try assumption.
  split. simpl. trivial. assumption.
  }
  {
  intros.
  apply rule_assoc' in SAT; try assumption.
  apply rule_exists_dist1 in SAT; try assumption.
  destruct SAT as (fq,SAT).
  apply rule_exists_dist1 in SAT; try assumption.
  destruct SAT as (fm,SAT).
  apply rule_exists_dist1 in SAT; try assumption.
  destruct SAT as (fv,SAT).
  exists fq, fm, fv.
  apply rule_assoc; try assumption.
  apply sat_star_imps with ((Alock (Enum z2, new_channel_level, Enum z2, None, false, Linv z gc, ND, nil) **
          Acond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)))
         ((Aprop (0 < fq /\ fq < 1 /\ 0 < fm /\ fm < 1 /\ 0 < fv < 1) &*
          Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5) **
          Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
          Apointsto fq (cell_loc (Enum z)) (Enum z0))); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_prop_star'; try assumption.
  destruct SAT0 as (SAT0,SAT1).
  split. assumption.
  apply rule_assoc'; try assumption.
  }
  {
  intros.
  apply rule_assoc' in SAT; try assumption.
  apply sat_star_imps with (((Alock
             (Enum z2, new_channel_level, Enum z2, None, false, Linv z gc, ND, nil) **
           Acond (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)) **
          (EX fq,
           (EX fm,
            (EX fv,
             Aprop (0 < fq /\ fq < 1 /\ 0 < fm /\ fm < 1 /\ 0 < fv < 1) &*
             Apointsto fv (cell_loc (Eplus (Enum z) (Enum 2))) (Enum z5) **
             Apointsto fm (cell_loc (Eplus (Enum z) (Enum 1))) (Enum z2) **
             Apointsto fq (cell_loc (Enum z)) (Enum z0))))))
         (Aobs (Oof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) :: O) **
         Atic (Enum gc)); try assumption.
  intros.
  apply rule_assoc; try assumption.
  intros. assumption.
  }
  {
  intros. split.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.

  apply sat_star_imps with (channel z12 gc (evall (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil)) )
         (Aobs (Oof (Enum z5, r, Enum z2, None, false, ND, Mv gc, nil) :: O) **
         Atic (Enum gc)); try assumption.
  intros. assumption.
  intros.
  apply rule_comm; try assumption.
  simpl. apply Coq.QArith.QArith_base.Qeq_eq_bool.
  reflexivity.
  }
  {
  intros.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (gc,SAT).
  exists gc.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  }
  apply neq_symm. eapply nodup_neq.
  inversion NODUP. inversion H2. inversion H6. inversion H10. apply H14. simpl. auto.
  apply neq_symm. eapply nodup_neq.
  inversion NODUP. inversion H2. inversion H6. inversion H10. apply H14. simpl. auto.
  eapply nodup_neq.
  inversion NODUP. inversion H2. inversion H6. apply H10. simpl. auto 10.
  apply neq_symm. eapply nodup_neq.
  inversion NODUP. inversion H2. inversion H6. inversion H10. apply H14. simpl. auto 10.
  apply neq_symm. eapply nodup_neq.
  inversion NODUP. inversion H2. inversion H6. apply H10. simpl. auto 10.
  eapply nodup_neq.
  inversion NODUP. apply H2. simpl. auto.
  eapply nodup_neq.
  inversion NODUP. apply H2. simpl. auto.
  eapply nodup_neq. apply NODUP. simpl. auto.
  eapply nodup_neq. apply NODUP. simpl. auto.
  eapply nodup_neq. apply NODUP. simpl. auto.
  eapply nodup_neq. apply NODUP. simpl. auto.
Qed.

Theorem rule_send sp O ch gv (v: location exp) value m1 v1 q1 nd1 rear1 tmp1 tmp2
  (ISF1: is_free_e ch tmp1 = false)
  (ISF2: is_free_e ch v1 = false)
  (ISF3: is_free_e ch m1 = false)
  (NODUP: NoDup (q1::tmp1::v1::m1::nd1::rear1::tmp2::nil))
  : correct
  (Aobs (Oof v :: O) ** channel ([[ch]]) gv (evall v) &* Abool (forallb (fun x => Qlt_bool send_level (Rofo x)) (Oof v :: O)))
  (send ch value m1 v1 q1 nd1 rear1 tmp1 tmp2)
  (fun _ => Aobs O ** channel ([[ch]]) gv (evall v)) channels_invs sp.
Proof.
  assert (NDtmp1: NoDup(tmp1::v1::m1::nd1::rear1::tmp2::nil)).
  {
  eapply NoDup_concat'.
  replace (q1::tmp1::v1::m1::nd1::rear1::tmp2::nil)
    with ((q1::nil)++tmp1::v1::m1::nd1::rear1::tmp2::nil)
    in NODUP.
  apply NODUP. reflexivity.
  }

  assert (NDv1: NoDup(v1::m1::nd1::rear1::tmp2::nil)).
  {
  eapply NoDup_concat'.
  replace (q1::tmp1::v1::m1::nd1::rear1::tmp2::nil)
    with ((q1::tmp1::nil)++v1::m1::nd1::rear1::tmp2::nil)
    in NODUP.
  apply NODUP. reflexivity.
  }

  assert (NDm1: NoDup(m1::nd1::rear1::tmp2::nil)).
  {
  eapply NoDup_concat'.
  replace (q1::tmp1::v1::m1::nd1::rear1::tmp2::nil)
    with ((q1::tmp1::v1::nil)++m1::nd1::rear1::tmp2::nil)
    in NODUP.
  apply NODUP. reflexivity.
  }

  unfold channel.
  apply rule_conseq1 with (EX m, (EX fm, (EX fv, (
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
    Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aobs (Oof v :: O) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\
    evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))))).
  apply rule_exists1.
  intros m.
  apply rule_exists1.
  intros fm.
  apply rule_exists1.
  intros fv.
  apply rule_Let with (fun z' => (Abool (Z.eqb z' ([[m]])) &*
    Apointsto fm (cell_loc (Eplus ch (Enum 1))) m) **
    (Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
    Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aobs (Oof v :: O) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))).
  apply rule_conseq1 with (Apointsto fm (cell_loc (Eplus ch (Enum 1))) m **
    (Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
    Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aobs (Oof v :: O) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))).
  apply rule_frame.
  apply rule_Lookup.
  {
  intros. assumption.
  }
  simpl.
  intros.
  rewrite subse_free.
  apply rule_conseq1 with (Apointsto fv (cell_loc (Eplus ch (Enum 2))) (Enum (Aof (evall v))) **
    (Abool (z =? ([[m]])) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aobs (Oof v :: O) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))).
  apply rule_Let with (fun z' => (Abool (Z.eqb z' ([[Enum (Aof (evall v))]])) &*
    Apointsto fv (cell_loc (Eplus ch (Enum 2))) (Enum (Aof (evall v)))) **
    (Abool (z =? ([[m]])) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aobs (Oof v :: O) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))).
  apply rule_frame.
  apply rule_Lookup.
  simpl.
  intros.
  rewrite eqz.
  rewrite subse_free.
  apply rule_Let with (fun _ => (EX wt, (EX ot, (
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)::Oof v::O) ** 
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) wt ot **
    (subsas (snd (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)))
    (channels_invs (fst (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil))) wt ot))))) **
    (Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))).
  apply rule_conseq1 with ((Abool (Z.eqb ([[Enum z]]) ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]])) &*
    Aprop (prcl (evalol (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil))) (map evalol (Oof v :: O))) &* 
    Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) ** 
    Aobs (Oof v :: O)) **
    (Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))).
  apply rule_frame.
  apply rule_Acquire.
  {
  intros.
  apply rule_assoc_pure in SAT; try assumption.
  destruct SAT as (SAT1,SAT2).
  apply rule_comm in SAT2; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply rule_star_pure in SAT2; try assumption.
  destruct SAT2 as (SAT2,SAT3).
  apply Z.eqb_eq in SAT2.
  rewrite SAT2 in *.
  apply sat_star_imps with (((Abool
       (([[Enum ([[m]])]]) =?
        ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]])) **
     Aprop
       (prcl (evalol (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)))
          (map evalol (Oof v :: O)))) **
    Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) ** Aobs (Oof v :: O)))
   (Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
   Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
   Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
   Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
   Abool ((([[m]]) =? ([[m]])) && (z0 =? Aof (evall v))) **
   Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O))); try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_pure_star'; try assumption.
  split. apply Z.eqb_eq. reflexivity.
  apply rule_comm in SAT3; try assumption.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_star_pure in SAT3; try assumption.
  destruct SAT3 as (SAT3,SAT4).
  apply rule_prop_star'; try assumption.
  split.
  {
  simpl.
  apply rule_star_pure in SAT4; try assumption.
  destruct SAT4 as (SAT5,SAT4).
  apply andb_true_iff in SAT4.
  destruct SAT4 as (SAT6,SAT4).
  replace (evalol (Oof v) :: map evalol O) with (map evalol (Oof v::O)).
  apply precedence_relaxed.
  apply forallb_forall. intros.
  destruct H as [eq1|in1].
  rewrite <- eq1 in *.
  apply Qlt_bool_trans with send_level.
  apply Qle_bool_iff. unfold Qle. simpl. omega. assumption. 
  eapply forallb_forall with (x:=x) in SAT4.
  apply Qlt_bool_trans with send_level. apply Qle_bool_iff.
  unfold Qle. simpl. omega. assumption. assumption. reflexivity. reflexivity.
  }
  apply rule_assoc'; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_comm in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply sat_star_imps with (Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil))
          ((Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
           Aobs (Oof v :: O)) **
          Apointsto fv (cell_loc (Eplus ch (Enum 2))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m); try assumption.
  intros. assumption. intros.
  apply rule_assoc in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (Aobs (Oof v :: O))
         ((Apointsto fv (cell_loc (Eplus ch (Enum 2))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m) **
         Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)); try assumption.
  intros. assumption. intros.
  apply rule_assoc in SAT0; try assumption.
  apply sat_star_imps with (Apointsto fv (cell_loc (Eplus ch (Enum 2))) (Enum (Aof (evall v))))
          (Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)); try assumption.
  intros. apply next_plus2; try assumption. intros.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (
     Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)) (Abool true); try assumption.
  apply rule_pure_star;try assumption. split. assumption. reflexivity. intros. assumption.
  intros.
  apply rule_prop_star'; try assumption.
  apply rule_star_pure in SAT4; try assumption.
  destruct SAT4 as (SAT4,SAT41).
  split. assumption.
  apply rule_pure_star'; try assumption.
  split. apply andb_true_iff. split.
  apply Z.eqb_eq. reflexivity. assumption. assumption.
  intros.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT0).
  split; try assumption.
  apply rule_star_pure in SAT; try assumption.
  intros. assumption.
  }
  simpl.
  intros.
  rewrite neqz; try omega.
  simpl.
  rewrite eqz. simpl.
  apply rule_conseq1 with (EX wt, (EX ot, (EX y, (EX y0, (EX y1, (EX y2, (EX y3, (EX y4,
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) wt ot **
    (Aprop (0 < y3 /\ y3 < 1 /\ 0 < y4 < 1) **
    Apointsto y3 (Enum ([[ch]]), 0%Qc, Enum ([[ch]]), None, false, ND, ND, nil) (Enum y) **
    Apointsto y4 (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0%Qc, Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) (Enum y2) **
    subsa (subsa (subsa (queue y y0) (subse chInv ([[ch]]))) (subse gcInv gv)) (subse vInv (Aof (evall v))) ** Actr (Enum gv) y1) **
    Abool ((wt y2 <=? ot y2)%nat && (wt y2 + y1 <=? ot y2 + y0)%nat) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))))))))).
  apply rule_exists1.
  intros Wt.
  apply rule_exists1.
  intros Ot.
  apply rule_exists1.
  intros qi.
  apply rule_exists1.
  intros sizei.
  apply rule_exists1.
  intros Ct.
  apply rule_exists1.
  intros vi.
  apply rule_exists1.
  intros fqi.
  apply rule_exists1.
  intros fvi.
  simpl.
  apply rule_conseq1 with 
    (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot **
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    Apointsto fqi (Enum ([[ch]]), 0%Qc, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
    Apointsto fvi (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0%Qc, 
      Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) (Enum vi) **
    queue qi sizei **
    Actr (Enum gv) Ct ** Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m ** Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) ** Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O))).

  apply rule_Let with (fun _ => EX Ct, (
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) 
     (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot **
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    Apointsto fqi (Enum ([[ch]]), 0%Qc, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
    Apointsto fvi (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0%Qc, 
      Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) (Enum vi) **
    queue qi sizei **
    Actr (Enum gv) Ct ** Abool ((Wt vi <=? Ot vi)%nat && ((Wt vi - 1) + Ct <=? Ot vi + sizei)%nat) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m ** Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) ** Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))).
  {
  destruct (Nat.eqb (Wt vi) 0) eqn:wt0.
  {
  apply Nat.eqb_eq in wt0.
  rewrite wt0 in *.

  apply rule_Let with (fun _ => 
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot **
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    Apointsto fqi (Enum ([[ch]]), 0%Qc, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
    Apointsto fvi (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0%Qc, 
      Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) (Enum vi) **
    queue qi sizei **
    Actr (Enum gv) Ct ** Abool ((0 <=? Ot vi)%nat && (0 + Ct <=? Ot vi + sizei)%nat) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m ** Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) ** Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O))).

  apply rule_nop.
  simpl.
  intros.
  apply rule_exists2.
  exists Ct.

  apply rule_conseq1 with ((Abool (andb (Z.eqb ([[Lof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]])
      ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]]))
      (Z.eqb ([[(Enum z0)]]) ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]))) &*
    ((subsas (snd (Mof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)))
      (channels_invs (fst (Mof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil))) empb empb))
      |* Abool (Nat.leb (Wt ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]])) 0)) **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot **
    Aobs ((if Nat.ltb 0 (Wt ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]))
    then (M'of (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)) else nil) ++
    (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O))) **
    ((Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    Apointsto fqi (Enum ([[ch]]), 0%Qc, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
    Apointsto fvi (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0%Qc, 
      Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) (Enum vi) **
    queue qi sizei **
    Actr (Enum gv) Ct ** Abool ((0 <=? Ot vi)%nat && (0 + Ct <=? Ot vi + sizei)%nat) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) ** Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O))))).


  apply rule_conseq2 with (fun _ =>
    (Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
      (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot **
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O)) **
    (Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    Apointsto fqi (Enum ([[ch]]), 0%Qc, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
    Apointsto fvi (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0%Qc, Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) (Enum vi) **
    queue qi sizei ** Actr (Enum gv) Ct **
    Abool (Ct <=? Ot vi + sizei)%nat **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))).

  apply rule_frame.
  apply rule_Notify.
  {
  intros.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil))
         ((Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
            (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot **
          Aobs
            (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
             :: Oof v :: O)) **
         Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
         Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
         Apointsto fvi
           (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
           Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil)
           (Enum vi) **
         queue qi sizei **
         Actr (Enum gv) Ct **
         Abool (Ct <=? Ot vi + sizei)%nat **
         Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
         Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
         Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
         Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
         Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O))); try assumption.
  intros. assumption. intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with ((Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
             (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot **
           Aobs
             (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
              :: Oof v :: O)))
          (Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
          Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
          Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
            Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil)
            (Enum vi) **
          queue qi sizei **
          Actr (Enum gv) Ct **
          Abool (Ct <=? Ot vi + sizei)%nat **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
          Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O))); try assumption.
  intros.
  apply rule_comm; try assumption. intros. assumption.
  }
  intros.
  assert (EQ1: Aof (evall v) = vi).
  {
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT0,SAT).
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT01).
  apply rule_comm in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT02).
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT03).
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT04).
  apply rule_points_to_value in SAT; try assumption.
  destruct SAT as (SAT05,SAT).
  assumption.
  }

  apply sat_star_imps with ((Abool
      ((([[Lof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]) =?
        ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]])) &&
       (([[Enum z0]]) =?
        ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]))) **
    (subsas (snd (Mof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)))
       (channels_invs
          (fst (Mof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil))) empb empb)
     |* Abool
          (Wt ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]) <=? 0)%nat) **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot **
    Aobs
      ((if
         (0 <? Wt ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]))%nat
        then M'of (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)
        else nil) ++
       Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O)))
   (Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
   Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
   Apointsto fvi
     (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
     Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
     (Enum vi) **
   queue qi sizei **
   Actr (Enum gv) Ct **
   Abool ((0 <=? Ot vi)%nat && (0 + Ct <=? Ot vi + sizei)%nat) **
   Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
   Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
   Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
   Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
   Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O))); try assumption.
  apply rule_assoc'; try assumption.
  apply rule_pure_star'; try assumption.
  split.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT1).
  apply rule_star_pure in SAT1; try assumption.
  destruct SAT1 as (SAT1,SAT2).
  apply andb_true_iff in SAT1.
  destruct SAT1 as (SAT1,SAT11).
  apply Z.eqb_eq in SAT11.
  rewrite SAT11 in *.
  apply andb_true_iff. split.
  apply Z.eqb_eq. reflexivity.
  apply Z.eqb_eq. reflexivity.
  intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Abool true)
   ((Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot **
    Aobs
      ((if
         (0 <? Wt ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]))%nat
        then M'of (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)
        else nil) ++
       Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O)) **
   Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
   Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
   Apointsto fvi
     (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
     Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
     (Enum vi) **
   queue qi sizei **
   Actr (Enum gv) Ct **
   Abool ((0 <=? Ot vi)%nat && (0 + Ct <=? Ot vi + sizei)%nat) **
   Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
   Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
   Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
   Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
   Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O))); try assumption.
  apply rule_pure_star'; try assumption. split. reflexivity.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil))
         ((Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
          Abool
            (Qlt_bool send_level (Rofo (Oof v)) &&
             forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)) **
         ((((((((Aobs
                   (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
                    :: Oof v :: O) **
                 Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot) **
                Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1)) **
               Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi)) **
              Apointsto fvi
                (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
                Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil)
                (Enum vi)) ** queue qi sizei) ** Actr (Enum gv) Ct) **
           Abool (Ct <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v)))) **
         Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m); try assumption.
  intros. assumption. intros.
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply sat_star_imps with ((Aobs
             (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
           Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot))
          (Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
          Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
          Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
            Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
            (Enum vi) **
          queue qi sizei **
          Actr (Enum gv) Ct **
          Abool (Ct <=? Ot vi + sizei)%nat **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
          Abool
            (Qlt_bool send_level (Rofo (Oof v)) &&
             forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)); try assumption.
  intros. apply rule_comm; try assumption.
  destruct (0 <? Wt ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]))%nat.
  rewrite app_nil_l. assumption.
  rewrite app_nil_l. assumption.
  intros. assumption. intros. right. simpl.
  rewrite EQ1 in *. apply Nat.leb_le. omega.
  intros. assumption. intros.
  apply rule_star_pure in SAT0; try assumption.
  intros. assumption.
  }
  {
    assert (wtlt: (0 < Wt vi)%nat).
    {
    assert (wtnz: Wt vi <> 0%nat).
    {
    assert (zr: (0 =? 0)%nat = true). apply Nat.eqb_eq. reflexivity.
    unfold not. intros. rewrite H in wt0. rewrite zr in wt0. inversion wt0.
    }
    omega.
    }
  apply rule_exists2.
  exists (S Ct).
  apply rule_Let with (fun _ => (Actr (Enum gv) (S Ct) ** Atic (Enum gv)) **
    (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot **
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    Apointsto fqi (Enum ([[ch]]), 0%Qc, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
    Apointsto fvi (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0%Qc, Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) (Enum vi) ** queue qi sizei **
    Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))).

  apply rule_conseq1 with (Actr (Enum gv) Ct **
    (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot **
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    Apointsto fqi (Enum ([[ch]]), 0%Qc, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
    Apointsto fvi (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0%Qc, Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) (Enum vi) ** queue qi sizei **
    Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))).

  apply rule_frame.
  apply rule_g_ctrinc.
  {
  intros.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (Actr (Enum gv) Ct)
         ((Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
          Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O))) **
         ((((Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
             Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot) **
            Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1)) **
           Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi)) **
          Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0, Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1),
            None, false, ND, ND, nil) (Enum vi)) ** queue qi sizei); try assumption.
  intros. assumption. intros.
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  }
  simpl. intros.
  apply rule_conseq1 with ((Abool (andb (Z.eqb ([[Lof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]])
      ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]]))
      (Z.eqb ([[(Enum z0)]]) ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]))) &*
    ((subsas (snd (Mof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)))
      (channels_invs (fst (Mof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil))) empb empb))
      |* Abool (Nat.leb (Wt ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]])) 0)) **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot **
    Aobs ((if Nat.ltb 0 (Wt ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]))
    then (M'of (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)) else nil) ++
    (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O))) **
    (Actr (Enum gv) (S Ct) **
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    Apointsto fqi (Enum ([[ch]]), 0%Qc, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
    Apointsto fvi (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0%Qc, Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) (Enum vi) ** queue qi sizei **
    Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))).

  apply rule_conseq2 with (fun _ => (Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) 
    (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot **
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O)) **
    (Actr (Enum gv) (S Ct) **
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    Apointsto fqi (Enum ([[ch]]), 0%Qc, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
    Apointsto fvi (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0%Qc, Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) (Enum vi) ** queue qi sizei **
    Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))).
  apply rule_frame.
  apply rule_Notify.
  {
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil))
         ((Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
            (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot **
          Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O)) **
         Actr (Enum gv) (S Ct) **
         Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
         Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
         Apointsto fvi
           (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0, Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1),
           None, false, ND, ND, nil) (Enum vi) **
         queue qi sizei **
         Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
         Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
         Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
         Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
         Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
         Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O))); try assumption.
  intros. assumption. intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with ((Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
             (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot **
           Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O)))
          (Actr (Enum gv) (S Ct) **
          Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
          Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
          Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0, Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1),
            None, false, ND, ND, nil) (Enum vi) **
          queue qi sizei **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
          Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O))); try assumption.
  intros.
  apply rule_comm; try assumption. intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Actr (Enum gv) (S Ct))
          (Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
          Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
          Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0, Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1),
            None, false, ND, ND, nil) (Enum vi) **
          queue qi sizei **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
          Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O))); try assumption.
  intros. assumption. intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  replace (Wt vi - 1 + S Ct)%nat with (Wt vi + Ct)%nat. assumption. omega.
  }
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (Actr (Enum gv) (S Ct))
         (Atic (Enum gv) **
         Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
         Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot **
         Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
         Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
         Apointsto fvi
           (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0, Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1),
           None, false, ND, ND, nil) (Enum vi) **
         queue qi sizei **
         Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
         Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
         Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
         Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
         Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
         Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
         Abool
           (Qlt_bool send_level (Rofo (Oof v)) && forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)); try assumption.
  intros. assumption. intros.
  apply rule_comm; try assumption.
  apply sat_star_imps with ((Abool
      ((([[Lof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]) =?
        ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]])) &&
       (([[Enum z0]]) =? ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]))) **
    (subsas (snd (Mof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)))
       (channels_invs (fst (Mof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil))) empb empb)
     |* Abool (Wt ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]) <=? 0)%nat) **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot **
    Aobs
      ((if (0 <? Wt ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]))%nat
        then M'of (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)
        else nil) ++ Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O)))
   (Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
   Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
   Apointsto fvi
     (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0, Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None,
     false, ND, ND, nil) (Enum vi) **
   queue qi sizei **
   Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
   Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
   Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
   Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
   Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
   Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O))); try assumption.
  apply rule_assoc'; try assumption.
  apply rule_pure_star'; try assumption. split.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_star_pure in SAT0; try assumption.
  destruct SAT0 as (SAT01,SAT0).
  apply rule_star_pure in SAT0; try assumption.
  destruct SAT0 as (SAT0,SAT02).
  apply andb_true_iff in SAT0.
  destruct SAT0 as (SAT03,SAT0).
  apply Z.eqb_eq in SAT0. rewrite SAT0 in *.
  apply andb_true_iff.
  split. apply Z.eqb_eq. reflexivity.
  apply Z.eqb_eq. reflexivity.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Atic (Enum gv))
          (Aobs
            (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
             :: Oof v :: O) **
          Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot **
          Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
          Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil)
            (Enum qi) **
          Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
            Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil)
            (Enum vi) **
          queue qi sizei **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
            (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
          Abool
            (Qlt_bool send_level (Rofo (Oof v)) &&
             forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)); try assumption.
  intros. left. assumption. intros.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_comm in SAT1; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil))
          ((Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
           Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
           Abool
             (Qlt_bool send_level (Rofo (Oof v)) &&
              forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)) **
          (((((((Aobs
                   (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
                    :: Oof v :: O) **
                 Alocked
                   (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt
                   Ot) ** Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1)) **
               Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil)
                 (Enum qi)) **
              Apointsto fvi
                (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
                Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND,
                nil) (Enum vi)) ** queue qi sizei) **
            Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat)) **
           Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
             (Enum (Aof (evall v)))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m); try assumption.
  intros. assumption. intros.
  apply rule_comm in SAT2; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply sat_star_imps with ((Aobs
             (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
              :: Oof v :: O) **
           Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt
             Ot))
          (Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
          Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil)
            (Enum qi) **
          Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
            Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil)
            (Enum vi) **
          queue qi sizei **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
            (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
          Abool
            (Qlt_bool send_level (Rofo (Oof v)) &&
             forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)); try assumption.
  intros. apply rule_comm; try assumption.
  destruct (0 <? Wt ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]))%nat.
  rewrite app_nil_l. assumption.
  rewrite app_nil_l. assumption.
  intros. assumption. intros.
  apply rule_star_pure in SAT1; try assumption.
  intros. assumption.
  }
  }
  simpl. intros.
  apply rule_exists1.
  intros CT.
  apply rule_Let with (fun z' => (Abool (Z.eqb z' ([[Enum qi]])) &*
    Apointsto fqi (cell_loc ch) (Enum qi)) **
    (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
      (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot **
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    Apointsto fvi (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0%Qc,
        Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) (Enum vi) ** queue qi sizei **
    Actr (Enum gv) CT **
    Abool ((Wt vi <=? Ot vi)%nat && ((Wt vi - 1) + CT <=? Ot vi + sizei)%nat) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]])))))(Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))).

  apply rule_conseq1 with (Apointsto fqi (cell_loc ch) (Enum qi) **
    (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
      (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot **
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    Apointsto fvi (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0%Qc,
        Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) (Enum vi) ** queue qi sizei **
    Actr (Enum gv) CT **
    Abool ((Wt vi <=? Ot vi)%nat && ((Wt vi - 1) + CT <=? Ot vi + sizei)%nat) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]])))))(Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))).

  apply rule_frame.
  repeat rewrite subse_free; try reflexivity.
  apply rule_Lookup.
  assumption. assumption. assumption. assumption. assumption. assumption. assumption.
  {
  intros.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi))
         ((Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
            Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
            (Enum vi) **
          queue qi sizei **
          Actr (Enum gv) CT **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi - 1 + CT <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
          Abool
            (Qlt_bool send_level (Rofo (Oof v)) &&
             forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)) **
         (Aobs
            (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
          Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
            (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot) **
         Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1)); try assumption.
  intros. assumption. intros.
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  }
  simpl. intros.
  apply rule_conseq1 with (queue z3 sizei **
    (Abool (z3 =? qi) **
    Apointsto fqi (cell_loc ch) (Enum z3) **
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
      (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot **
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    Apointsto fvi (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0%Qc,
        Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) (Enum vi) **
    Actr (Enum gv) CT **
    Abool ((Wt vi <=? Ot vi)%nat && ((Wt vi - 1) + CT <=? Ot vi + sizei)%nat) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]])))))(Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))).
  apply rule_Let with (fun z' => queue z3 (S sizei) **
    (Abool (z3 =? qi) **
    Apointsto fqi (cell_loc ch) (Enum z3) **
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
      (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot **
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    Apointsto fvi (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0%Qc,
        Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) (Enum vi) **
    Actr (Enum gv) CT **
    Abool ((Wt vi  <=? Ot vi)%nat && ((Wt vi - 1) + CT <=? Ot vi + sizei)%nat) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]])))))(Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))).

  apply rule_frame.
  rewrite subs_enqueue. simpl. rewrite neqz; try omega. simpl.
  rewrite subs_enqueue. simpl. rewrite neqz; try omega. simpl.
  rewrite subs_enqueue. simpl. rewrite neqz; try omega. simpl.
  rewrite subs_enqueue. simpl. rewrite neqz; try omega. simpl.
  rewrite subs_enqueue. simpl. rewrite eqz.
  apply rule_enqueue.
  inversion NDm1. assumption.
  simpl. split. reflexivity. split; reflexivity.
  simpl. rewrite eqz. reflexivity.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 10.
  simpl. reflexivity.
  apply neq_symm. eapply nodup_neq. apply NODUP. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  apply neq_symm. eapply nodup_neq. apply NODUP. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp1. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp1. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp1. simpl. auto 10.
  simpl. reflexivity.
  apply neq_symm. eapply nodup_neq. apply NODUP. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  apply neq_symm. eapply nodup_neq. apply NODUP. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp1. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp1. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp1. simpl. auto 10.
  simpl. reflexivity.
  apply neq_symm. eapply nodup_neq. apply NODUP. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  apply neq_symm. eapply nodup_neq. apply NODUP. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDv1. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDv1. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDv1. simpl. auto 10.
  simpl. reflexivity.
  apply neq_symm. eapply nodup_neq. apply NODUP. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  apply neq_symm. eapply nodup_neq. apply NODUP. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDm1. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDm1. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDm1. simpl. auto 10.
  simpl. reflexivity.

  simpl. intros.
  apply rule_conseq1 with (
    (Abool (andb (Z.eqb ([[Lof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]])
      ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]]))
    (safe_obs (evall (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil))
     ((upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]))
     ((Ot ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]) - 1)))) &*
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aobs (Oof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) 
      :: Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
      (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot) **
    (queue z3 (S sizei) **
    (Abool (z3 =? qi) **
    Apointsto fqi (cell_loc ch) (Enum z3) **
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    Apointsto fvi (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0%Qc,
        Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) (Enum vi) **
    Actr (Enum gv) CT **
    Abool ((Wt vi <=? Ot vi)%nat && (Wt vi - 1 + CT <=? Ot vi + sizei)%nat) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]])))))(Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O))))).

  apply rule_Let with (fun _ =>
    (Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
      (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) 
      (upd Z.eq_dec Ot (Aof (evall v)) (Ot (Aof (evall v)) - 1)%nat)) **
    queue z3 (S sizei) **
    (Abool (z3 =? qi) **
    Apointsto fqi (cell_loc ch) (Enum z3) **
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    Apointsto fvi (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0%Qc,
        Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) (Enum vi) **
    Actr (Enum gv) CT **
    Abool ((Wt vi <=? Ot vi)%nat && (Wt vi - 1 + CT <=? Ot vi + sizei)%nat) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]])))))(Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O)))).

  apply rule_frame.
  apply rule_g_disch.
  simpl.
  intros.
  apply rule_conseq1 with (
    (Abool (Z.eqb ([[Enum z]]) ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]])) &*
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
    (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat)
    (upd Z.eq_dec Ot (Aof (evall v)) (Ot (Aof (evall v)) - 1)%nat) **
    (subsas (snd (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)))
    (channels_invs (fst (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil))) 
    (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat)
    (upd Z.eq_dec Ot (Aof (evall v)) (Ot (Aof (evall v)) - 1)%nat))))
    **
    (Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) ** Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))))).

  apply rule_conseq2 with (fun _ => 
    (Aobs (O) **
    Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil))
    **
    (Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) ** Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))))).
  apply rule_frame.
  apply rule_Release.
  {
  intros.
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (Aobs O)
         (Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
         Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
         Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
           (Enum (Aof (evall v))) **
         Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
         Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
         Abool ((z =? ([[m]])) && (z0 =? Aof (evall v)))); try assumption.
  intros. assumption. intros.
  exists m, fm, fv.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_star_pure in SAT0; try assumption.
  destruct SAT0 as (SAT0, SAT00).
  apply rule_comm in SAT0; try assumption.
  apply sat_star_imps with (Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\
    evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)))
          (((Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
            Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)) **
           Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
             (Enum (Aof (evall v)))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m); try assumption.
  intros. assumption. intros.
  apply rule_comm in SAT1; try assumption.
  apply sat_star_imps with (Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m)
          ((Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
           Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
            (Enum (Aof (evall v)))); try assumption.
  intros. assumption. intros.
  apply rule_comm in SAT2; try assumption.
  }
  {
  intros.

  assert (EQ1: Aof (evall v) = vi).
  {
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT0,SAT).
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT01,SAT).
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT02).
  apply rule_comm in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT03).
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT04).
  apply rule_points_to_value in SAT; try assumption.
  destruct SAT as (SAT05,SAT).
  assumption.
  }

  apply sat_star_imps with ((Abool
      (([[Enum z]]) =?
       ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]])) **
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
      (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat)
      (upd Z.eq_dec Ot (Aof (evall v)) (Ot (Aof (evall v)) - 1)%nat) **
    subsas (snd (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)))
      (channels_invs
         (fst (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)))
         (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat)
         (upd Z.eq_dec Ot (Aof (evall v)) (Ot (Aof (evall v)) - 1)%nat))))
   (Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
   Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
   Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
   Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
   Abool ((z =? ([[m]])) && (z0 =? Aof (evall v)))); try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT1).
  apply andb_true_iff in SAT.
  destruct SAT as (SAT,SAT2).
  apply Z.eqb_eq in SAT. rewrite SAT in *.
  apply rule_pure_star'; try assumption.
  split. apply Z.eqb_eq. reflexivity.
  apply rule_star_pure in SAT1; try assumption.
  destruct SAT1 as (SAT1,SAT3).
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil))
          ((Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
           Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
             (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat)
             (upd Z.eq_dec Ot (Aof (evall v)) (Ot (Aof (evall v)) - 1)%nat)) **
          queue z3 (S sizei) **
          Abool (z3 =? qi) **
          Apointsto fqi (cell_loc ch) (Enum z3) **
          Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
          Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
            Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
            (Enum vi) **
          Actr (Enum gv) CT **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi - 1 + CT <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil))); try assumption.
  intros. assumption. intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply sat_star_imps with (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O))
          (Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
            (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat)
            (upd Z.eq_dec Ot (Aof (evall v)) (Ot (Aof (evall v)) - 1)%nat) **
          queue z3 (S sizei) **
          Abool (z3 =? qi) **
          Apointsto fqi (cell_loc ch) (Enum z3) **
          Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
          Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
            Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
            (Enum vi) **
          Actr (Enum gv) CT **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi - 1 + CT <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil))); try assumption.
  intros. assumption. intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
            (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat)
            (upd Z.eq_dec Ot (Aof (evall v)) (Ot (Aof (evall v)) - 1)%nat))
          (queue z3 (S sizei) **
          Abool (z3 =? qi) **
          Apointsto fqi (cell_loc ch) (Enum z3) **
          Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
          Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
            Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
            (Enum vi) **
          Actr (Enum gv) CT **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi - 1 + CT <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil))); try assumption.
  intros. assumption. intros.
  apply rule_assoc' in SAT5; try assumption.
  apply rule_assoc' in SAT5; try assumption.
  apply rule_assoc' in SAT5; try assumption.
  apply rule_assoc' in SAT5; try assumption.
  apply rule_assoc' in SAT5; try assumption.
  apply rule_assoc' in SAT5; try assumption.

  apply sat_star_imps with (EX q, (EX size, (EX Ct, (EX v', (EX fq, (EX fv, (
  Aprop (Qclt 0 fq /\ Qclt fq 1 /\ Qclt 0 fv /\ Qclt fv 1) **
  Apointsto fq (cell_loc ch) (Enum q) **
  Apointsto fv (next_loc (next_loc (cell_loc ch))) (Enum v') **
  subsa (subsa (queue q size) (subse chInv ([[ch]]))) (subse gcInv gv) ** 
  Actr (Enum gv) Ct **
  Abool (andb (Nat.leb ((upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) v')%nat
  ((upd Z.eq_dec Ot (Aof (evall v)) (Ot (Aof (evall v)) - 1)%nat) v')%nat)
  (Nat.leb ((upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) v' + Ct)
  ((upd Z.eq_dec Ot (Aof (evall v)) (Ot (Aof (evall v)) - 1)%nat) v' + size))))))))))
          (Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil))); try assumption.
  apply rule_exists_dist'; try assumption.
  exists z3.
  apply rule_exists_dist'; try assumption.
  exists (S sizei).
  apply rule_exists_dist'; try assumption.
  exists CT.
  apply rule_exists_dist'; try assumption.
  exists vi.
  apply rule_exists_dist'; try assumption.
  exists fqi.
  apply rule_exists_dist'; try assumption.
  exists fvi.
  apply rule_comm; try assumption.
  apply rule_comm in SAT5; try assumption.
  apply sat_star_imps with ((Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
           Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
           Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil))))
          ((((((queue z3 (S sizei) ** Abool (z3 =? qi)) ** Apointsto fqi (cell_loc ch) (Enum z3)) **
             Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1)) **
            Apointsto fvi
              (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
              Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil)
              (Enum vi)) ** Actr (Enum gv) CT) **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi - 1 + CT <=? Ot vi + sizei)%nat)); try assumption.
  intros. assumption. intros.
  apply rule_assoc in SAT6; try assumption.
  apply rule_assoc in SAT6; try assumption.
  apply rule_assoc in SAT6; try assumption.
  apply rule_assoc in SAT6; try assumption.
  apply rule_assoc in SAT6; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (queue z3 (S sizei))
          (Abool (z3 =? qi) **
          Apointsto fqi (cell_loc ch) (Enum z3) **
          Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
          Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
            Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
            (Enum vi) **
          Actr (Enum gv) CT **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi - 1 + CT <=? Ot vi + sizei)%nat)); try assumption.
  intros. apply subsa_queue2';try assumption.
  intros.
  apply rule_comm; try assumption.
  apply rule_star_pure in SAT7; try assumption.
  destruct SAT7 as (SAT7,SAT8).
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Apointsto fqi (cell_loc ch) (Enum z3))
          (Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
          Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
            Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
            (Enum vi) **
          Actr (Enum gv) CT **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi - 1 + CT <=? Ot vi + sizei)%nat)); try assumption.
  intros. assumption. intros.
  apply rule_comm; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc' in SAT9; try assumption.
  apply rule_assoc' in SAT9; try assumption.
  apply sat_star_imps with (((Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
            Apointsto fvi
              (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
              Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil)
              (Enum vi)) ** Actr (Enum gv) CT))
          (Abool ((Wt vi <=? Ot vi)%nat && (Wt vi - 1 + CT <=? Ot vi + sizei)%nat)); try assumption.
  intros. assumption. intros.
  apply andb_true_iff in SAT10.
  destruct SAT10 as (SAT10,SAT11).
  apply Nat.leb_le in SAT10.
  apply Nat.leb_le in SAT11.
  rewrite EQ1 in *.
  apply andb_true_iff. split.
  apply Nat.leb_le. unfold upd. rewrite eqz. rewrite eqz. omega.
  apply Nat.leb_le. unfold upd. rewrite eqz. rewrite eqz. omega.
  intros. assumption.
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_pure_star; try assumption.
  split.
  apply rule_assoc'; try assumption.
  apply andb_true_iff. split.
  apply Z.eqb_eq. reflexivity. assumption.
  intros.
  apply rule_star_pure in SAT0; try assumption.
  intros. assumption.
  }
  {
  intros.
  assert (EQ1: Aof (evall v) = vi).
  {
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT0,SAT).
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT01).
  apply rule_comm in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT03).
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT04).
  apply rule_points_to_value in SAT; try assumption.
  destruct SAT as (SAT05,SAT).
  assumption.
  }
  apply sat_star_imps with ((Abool
      ((([[Lof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]) =?
        ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]])) &&
       safe_obs (evall (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil))
         (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat
            ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]))
         (Ot ([[Aof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)]]) - 1)) **
    Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
    Aobs
      (Oof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil)
       :: Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
      (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot))
   (queue z3 (S sizei) **
   Abool (z3 =? qi) **
   Apointsto fqi (cell_loc ch) (Enum z3) **
   Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
   Apointsto fvi
     (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
     Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
     (Enum vi) **
   Actr (Enum gv) CT **
   Abool ((Wt vi <=? Ot vi)%nat && (Wt vi - 1 + CT <=? Ot vi + sizei)%nat) **
   Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
   Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
   Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
   Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
   Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: O))); try assumption.
  apply rule_assoc'; try assumption.
  apply rule_pure_star'; try assumption. split.
  apply andb_true_iff. split.
  apply Z.eqb_eq. reflexivity.
  unfold safe_obs.
  apply andb_true_iff. split.
  apply orb_true_iff. unfold upd.
  rewrite eqz.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT0,SAT).
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT1).
  apply andb_true_iff in SAT.
  destruct SAT as (SAT,SAT2).
  apply Nat.leb_le in SAT.
  rewrite EQ1 in *.

  destruct (Nat.leb (Wt vi) 1) eqn:eq1.
  apply Nat.leb_le in eq1. left. apply Nat.eqb_eq. omega.
  right. apply nat_leb_falseL in eq1. apply Nat.ltb_lt. simpl. omega.
  apply andb_true_iff. split.
  apply orb_true_iff. left. simpl. reflexivity.
  apply orb_true_iff. left. unfold Util_Z.ifb. simpl.
  destruct (opQc_eq_dec (Xof (evall (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil))) None) eqn:CO. reflexivity. contradiction.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (queue z3 (S sizei))
         (Abool (z3 =? qi) **
         Apointsto fqi (cell_loc ch) (Enum z3) **
         Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
         Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
           (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot **
         Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
         Apointsto fvi
           (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
           Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
           (Enum vi) **
         Actr (Enum gv) CT **
         Abool ((Wt vi <=? Ot vi)%nat && (Wt vi - 1 + CT <=? Ot vi + sizei)%nat) **
         Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
         Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
         Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
         Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
         Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
         Abool
           (Qlt_bool send_level (Rofo (Oof v)) &&
            forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)); try assumption.
  intros. assumption. intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Abool (z3 =? qi))
          (Apointsto fqi (cell_loc ch) (Enum z3) **
          Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
          Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
            (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot **
          Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
          Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
            Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
            (Enum vi) **
          Actr (Enum gv) CT **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi - 1 + CT <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
          Abool
            (Qlt_bool send_level (Rofo (Oof v)) &&
             forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)); try assumption.
  intros. assumption. intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Apointsto fqi (cell_loc ch) (Enum z3))
          (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
          Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
            (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot **
          Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
          Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
            Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
            (Enum vi) **
          Actr (Enum gv) CT **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi - 1 + CT <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
          Abool
            (Qlt_bool send_level (Rofo (Oof v)) &&
             forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)); try assumption.
  intros. assumption. intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_comm in SAT2; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply sat_star_imps with (Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil))
          ((Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
           Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
           Abool
             (Qlt_bool send_level (Rofo (Oof v)) &&
              forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)) **
          ((((((Aobs
                  (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
                   :: Oof v :: O) **
                Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
                  (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot) **
               Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1)) **
              Apointsto fvi
                (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
                Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
                (Enum vi)) ** Actr (Enum gv) CT) **
            Abool ((Wt vi <=? Ot vi)%nat && (Wt vi - 1 + CT <=? Ot vi + sizei)%nat)) **
           Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v)))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m); try assumption.
  intros. assumption. intros.
  apply rule_comm in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O))
          (Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
            (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot **
          Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
          Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
            Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
            (Enum vi) **
          Actr (Enum gv) CT **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi - 1 + CT <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\ evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
          Abool
            (Qlt_bool send_level (Rofo (Oof v)) &&
             forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)); try assumption.
  intros.
  eapply rule_perm_obs with (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O); try assumption.
  simpl.
  replace (evalol (Oof (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil))) with
    (evalol (Oof v)).
  apply Coq.Sorting.Permutation.perm_swap.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_star_pure in SAT3; try assumption.
  destruct SAT3 as (SAT5,SAT3).
  apply rule_star_pure in SAT3; try assumption.
  destruct SAT3 as (SAT3,SAT6).
  destruct SAT3 as (SAT3,SAT7).
  unfold evall in SAT7.
  assert (EQ2: evalol (Oof v) = (Aof (evalol (Oof v), Iof v, Mof v, map evalol (M'of v)),
       Rof (evalol (Oof v), Iof v, Mof v, map evalol (M'of v)), [[m]], None, false)).
  {
  inversion SAT7. reflexivity.
  }
  rewrite EQ2. reflexivity.
  intros. assumption. intros.
  apply rule_star_pure in SAT0; try assumption. intros. assumption.
  }
  {
  intros.
  assert (EQ1: z3 = qi).
  {
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as ((SAT,SAT01),SAT00).
  apply Z.eqb_eq in SAT. rewrite SAT in *. reflexivity.
  }
  rewrite EQ1 in *.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (queue qi sizei)
         ((Actr (Enum gv) CT **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi - 1 + CT <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
          Aprop
            ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\
             evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
          Abool
            (Qlt_bool send_level (Rofo (Oof v)) &&
             forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)) **
         ((((Abool (qi =? qi) &* Apointsto fqi (cell_loc ch) (Enum qi)) **
            Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O)) **
           Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
             (upd Z.eq_dec Wt (Aof (evall v)) (Wt (Aof (evall v)) - 1)%nat) Ot) **
          Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1)) **
         Apointsto fvi
           (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
           Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
           (Enum vi)); try assumption.
  intros. assumption.
  intros.
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc_pure in SAT0; try assumption.
  apply rule_pure_star'; try assumption.
  }
  {
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply sat_star_imps with ((Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
          Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot))
         ((Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
          Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
          Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
            Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
            (Enum vi) **
          subsa (subsa (subsa (queue qi sizei) (subse chInv ([[ch]]))) (subse gcInv gv))
            (subse vInv (Aof (evall v))) ** Actr (Enum gv) Ct) **
         Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
         Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
         Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
         Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
         Aprop
           ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\
            evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
         Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
         Abool
           (Qlt_bool send_level (Rofo (Oof v)) &&
            forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)); try assumption.
  intros. assumption. intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with ((Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
           Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi) **
           Apointsto fvi
             (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
             Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
             (Enum vi) **
           subsa (subsa (subsa (queue qi sizei) (subse chInv ([[ch]]))) (subse gcInv gv))
             (subse vInv (Aof (evall v))) ** Actr (Enum gv) Ct))
          (Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
          Aprop
            ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\
             evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
          Abool
            (Qlt_bool send_level (Rofo (Oof v)) &&
             forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)); try assumption.
  intros.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (((Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
            Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi)) **
           Apointsto fvi
             (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
             Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
             (Enum vi)))
          (subsa (subsa (subsa (queue qi sizei) (subse chInv ([[ch]]))) (subse gcInv gv))
            (subse vInv (Aof (evall v))) ** Actr (Enum gv) Ct); try assumption.
  intros. assumption. intros.
  apply sat_star_imps with (subsa (subsa (subsa (queue qi sizei) (subse chInv ([[ch]]))) (subse gcInv gv))
            (subse vInv (Aof (evall v)))) (Actr (Enum gv) Ct); try assumption.
  intros. apply subsa_queue3 in SAT3; try assumption. intros. assumption.
  intros. assumption.
  }
  {
  intros.
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (wt,SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (ot,SAT).
  apply sat_star_imps with (a':=
          (EX y,
           (EX y0,
            (EX y1,
             (EX y2,
              (EX y3,
               (EX y4,
                Aprop (0 < y3 /\ y3 < 1 /\ 0 < y4 < 1) **
                Apointsto y3 (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum y) **
                Apointsto y4
                  (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
                  Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
                  (Enum y2) **
                subsa (subsa (queue y y0) (subse chInv ([[ch]]))) (subse gcInv gv) **
                Actr (Enum gv) y1 ** Abool ((wt y2 <=? ot y2)%nat && (wt y2 + y1 <=? ot y2 + y0)%nat))))))) **
Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
          Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) wt ot)
         (b':=Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
         Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
         Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
         Aprop
           ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\
            evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
         Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
         Abool
           (Qlt_bool send_level (Rofo (Oof v)) &&
            forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)) in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (y',SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (y0',SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (y1',SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (y2',SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (y3',SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (y4',SAT).
  exists wt, ot, y', y0', y1', y2', y3', y4'.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with ((Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: Oof v :: O) **
          Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) wt ot))
         ((Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
          Aprop
            ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\
             evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
          Abool
            (Qlt_bool send_level (Rofo (Oof v)) &&
             forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)) **
         Aprop (0 < y3' /\ y3' < 1 /\ 0 < y4' < 1) **
         Apointsto y3' (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum y') **
         Apointsto y4'
           (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
           Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
           (Enum y2') **
         subsa (subsa (queue y' y0') (subse chInv ([[ch]]))) (subse gcInv gv) **
         Actr (Enum gv) y1' ** Abool ((wt y2' <=? ot y2')%nat && (wt y2' + y1' <=? ot y2' + y0')%nat)); try assumption.
  intros. assumption. intros.
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with ((Aprop (0 < y3' /\ y3' < 1 /\ 0 < y4' < 1) **
           Apointsto y3' (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum y') **
           Apointsto y4'
             (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
             Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
             (Enum y2') **
           subsa (subsa (queue y' y0') (subse chInv ([[ch]]))) (subse gcInv gv) **
           Actr (Enum gv) y1' ** Abool ((wt y2' <=? ot y2')%nat && (wt y2' + y1' <=? ot y2' + y0')%nat)))
          (Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
          Aprop
            ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\
             evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof (evall v))) **
          Abool
            (Qlt_bool send_level (Rofo (Oof v)) &&
             forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)); try assumption.

  intros.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply sat_star_imps with (((((Aprop (0 < y3' /\ y3' < 1 /\ 0 < y4' < 1) **
              Apointsto y3' (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum y')) **
             Apointsto y4'
               (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
               Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
               (Enum y2')) ** subsa (subsa (queue y' y0') (subse chInv ([[ch]]))) (subse gcInv gv)) **
           Actr (Enum gv) y1')) (Abool ((wt y2' <=? ot y2')%nat && (wt y2' + y1' <=? ot y2' + y0')%nat)); try assumption.
  intros.
  apply rule_assoc in SAT2; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (((Aprop (0 < y3' /\ y3' < 1 /\ 0 < y4' < 1) **
            Apointsto y3' (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum y')) **
           Apointsto y4'
             (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
             Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
             (Enum y2')))
          (subsa (subsa (queue y' y0') (subse chInv ([[ch]]))) (subse gcInv gv) ** Actr (Enum gv) y1'); try assumption.
  intros. assumption. intros.
  apply sat_star_imps with (subsa (subsa (queue y' y0') (subse chInv ([[ch]]))) (subse gcInv gv)) (Actr (Enum gv) y1'); try assumption.
  intros.
  apply subsa_queue2 in SAT4; try assumption.
  apply subsa_queue3'; try assumption.
  intros. assumption. intros. assumption. intros. assumption. intros.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_comm in SAT0; try assumption.
  intros. assumption.
  }
  apply neq_symm. eapply nodup_neq. apply NDv1. simpl. auto 10.
  simpl. reflexivity.
  {
  intros.
  apply rule_assoc_pure in SAT; try assumption.
  destruct SAT as (SAT0,SAT).
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_pure_star'; try assumption. split. assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Apointsto fm (cell_loc (Eplus ch (Enum 1))) m)
         (Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
         Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
         Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
         Aobs (Oof v :: O) **
         Aprop
           ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\
            evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
         Abool
           (Qlt_bool send_level (Rofo (Oof v)) &&
            forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)); try assumption.
  intros. assumption. intros.
  apply rule_comm; try assumption.
  apply sat_star_imps with (Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))))
          (Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
          Acond (Enum (Aof (evall v)), Rof v, m, None, false, ND, Mv gv, nil) **
          Aobs (Oof v :: O) **
          Aprop
            ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\
             evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
          Abool
            (Qlt_bool send_level (Rofo (Oof v)) &&
             forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) O)); try assumption.
  intros. apply next_plus2' with o1 g1; try assumption.
  intros. assumption.
  }
  assumption.
  {
  intros.
  destruct SAT as (SAT,SAT0).
  apply rule_comm in SAT; try assumption.
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (m,SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (fm,SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (fv,SAT).
  exists m, fm, fv.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Aobs (Oof v :: O))
         (Aprop
           ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\
            evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)) **
         Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
         Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
         Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
         Acond (Enum (Aof (evall v)), Rof (evall v), m, None, false, ND, Mv gv, nil)); try assumption.
  intros. assumption. intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Aprop
            ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\
             evall v = (Aof (evall v), Rof (evall v), [[m]], None, false, ND, Mv gv, nil)))
          (Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof (evall v))) **
          Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
          Acond (Enum (Aof (evall v)), Rof (evall v), m, None, false, ND, Mv gv, nil)); try assumption.
  intros. assumption. intros.
  apply rule_pure_star'; try assumption. split. assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  }
Qed.

Theorem rule_receive sp O ch gv v q mv s v1 size last front1 front2 next_front rear lastval nextnode incv tmp tmp1 tmp2
  (ISF1: is_free_e ch tmp = false)
  (ISF2: is_free_e ch v1 = false)
  (ISF3: is_free_e ch mv = false)
  (NODUP: NoDup(q::mv::s::v1::tmp::front2::next_front::tmp2::size::last::front1::rear::lastval::nextnode::incv::tmp1::nil)): correct
  (Aobs O ** channel ([[ch]]) gv v ** Atic (Enum gv) &* Abool ((forallb (fun x => Qlt_bool (Rof v) (Rofo x)) O) && (forallb (fun x => Qlt_bool receive_level (Rofo x)) O)))
  (receive ch q mv v1 s size last front1 front2 next_front rear lastval nextnode incv tmp tmp1 tmp2)
  (fun _ => Aobs O ** channel ([[ch]]) gv v) channels_invs sp.
Proof.
  assert (NDtmp: NoDup(tmp::front2::next_front::tmp2::size::last::front1::rear::lastval::nextnode::incv::tmp1::nil)).
  {
  eapply NoDup_concat'.
  replace (q::mv::s::v1::tmp::front2::next_front::tmp2::size::last::front1::rear::lastval::nextnode::incv::tmp1::nil)
    with ((q::mv::s::v1::nil)++tmp::front2::next_front::tmp2::size::last::front1::rear::lastval::nextnode::incv::tmp1::nil)
    in NODUP.
  apply NODUP. reflexivity.
  }

  assert (NDq: NoDup(q::mv::s::v1::tmp::front2::next_front::tmp2::size::last::front1::rear::lastval::nextnode::incv::tmp1::nil)).
  {
  eapply NoDup_concat'.
  replace (q::mv::s::v1::tmp::front2::next_front::tmp2::size::last::front1::rear::lastval::nextnode::incv::tmp1::nil)
    with ((nil)++q::mv::s::v1::tmp::front2::next_front::tmp2::size::last::front1::rear::lastval::nextnode::incv::tmp1::nil)
    in NODUP.
  apply NODUP. reflexivity.
  }

  assert (NDmv: NoDup(mv::s::v1::tmp::front2::next_front::tmp2::size::last::front1::rear::lastval::nextnode::incv::tmp1::nil)).
  {
  eapply NoDup_concat'.
  replace (q::mv::s::v1::tmp::front2::next_front::tmp2::size::last::front1::rear::lastval::nextnode::incv::tmp1::nil)
    with ((q::nil)++mv::s::v1::tmp::front2::next_front::tmp2::size::last::front1::rear::lastval::nextnode::incv::tmp1::nil)
    in NODUP.
  apply NODUP. reflexivity.
  }

  assert (NDs: NoDup(s::v1::tmp::front2::next_front::tmp2::size::last::front1::rear::lastval::nextnode::incv::tmp1::nil)).
  {
  eapply NoDup_concat'.
  replace (q::mv::s::v1::tmp::front2::next_front::tmp2::size::last::front1::rear::lastval::nextnode::incv::tmp1::nil)
    with ((q::mv::nil)++s::v1::tmp::front2::next_front::tmp2::size::last::front1::rear::lastval::nextnode::incv::tmp1::nil)
    in NODUP.
  apply NODUP. reflexivity.
  }

  assert (NDv1: NoDup(v1::tmp::front2::next_front::tmp2::size::last::front1::rear::lastval::nextnode::incv::tmp1::nil)).
  {
  eapply NoDup_concat'.
  replace (q::mv::s::v1::tmp::front2::next_front::tmp2::size::last::front1::rear::lastval::nextnode::incv::tmp1::nil)
    with ((q::mv::s::nil)++v1::tmp::front2::next_front::tmp2::size::last::front1::rear::lastval::nextnode::incv::tmp1::nil)
    in NODUP.
  apply NODUP. reflexivity.
  }

  unfold channel.
  apply rule_conseq1 with (EX m,(EX fm, (EX fv, (
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Aobs O **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\
    v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))))).
  apply rule_exists1.
  intros m.
  apply rule_exists1.
  intros fm.
  apply rule_exists1.
  intros fv.
  apply rule_Let with (fun z' => (Abool (Z.eqb z' ([[m]])) &*
    Apointsto fm (cell_loc (Eplus ch (Enum 1))) m) **
    (Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Aobs O **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\
    v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).

  apply rule_conseq1 with (Apointsto fm (cell_loc (Eplus ch (Enum 1))) m **
    (Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Aobs O **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\
    v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).
  apply rule_frame.
  apply rule_Lookup.
  {
  intros. assumption.
  }
  simpl.
  intros.
  rewrite subse_free.
  apply rule_conseq1 with (Apointsto fv (cell_loc (Eplus ch (Enum 2))) (Enum (Aof v)) **
    (Abool (z =? ([[m]])) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Aobs O **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\
    v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).
  apply rule_Let with (fun z' => (Abool (Z.eqb z' (Aof v)) &*
    Apointsto fv (cell_loc (Eplus ch (Enum 2))) (Enum (Aof v))) **
    (Abool (z =? ([[m]])) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Aobs O **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\
    v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).
  apply rule_frame.
  apply rule_Lookup.
  simpl.
  intros.
  rewrite eqz.
  rewrite subse_free.
  rewrite subse_free.
  apply rule_Let with (fun _ => (EX wt, (EX ot, (
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)::O) ** 
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) wt ot **
    (subsas (snd (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)))
    (channels_invs (fst (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil))) wt ot))))) **
    (Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\  v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof v)) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).
  apply rule_conseq1 with ((Abool (Z.eqb ([[Enum z]]) ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]])) &*
    Aprop (prcl (evalol (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil))) (map evalol O)) &* 
    Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) ** 
    Aobs O) **
    (Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\  v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof v)) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).
  apply rule_frame.
  apply rule_Acquire.
  {
  intros.
  apply rule_assoc_pure in SAT; try assumption.
  destruct SAT as (SAT, SAT1).
  apply sat_star_imps with ((Abool
       (([[Enum z]]) =?
        ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]])) **
     Aprop
       (prcl
          (evalol
             (Oof
                (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)))
          (map evalol O))) **
    Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
    Aobs O)
   (Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
   Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
   Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
   Atic (Enum gv) **
   Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\  v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
   Abool ((z =? ([[m]])) && (z0 =? Aof v)) **
   Abool
     (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
      forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_comm in SAT1; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply rule_star_pure in SAT1; try assumption.
  destruct SAT1 as (SAT1,SAT2).
  apply Z.eqb_eq in SAT1. rewrite SAT1 in *.
  apply rule_pure_star'; try assumption. split. apply Z.eqb_eq. reflexivity.
  apply rule_comm in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_comm in SAT2; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply rule_star_pure in SAT2; try assumption.
  destruct SAT2 as (SAT2,SAT3).
  apply rule_star_pure in SAT3; try assumption.
  destruct SAT3 as (SAT3,SAT4).
  apply rule_pure_star'; try assumption.
  split. simpl.
  unfold prcl. unfold Xofo, Oof. simpl.
  apply andb_true_iff in SAT3.
  destruct SAT3 as (SAT3,SAT31).
  apply forallb_forall.
  intros.
  apply in_map_iff in H.
  destruct H as (x0,(EQ,IN)).
  eapply forallb_forall with (x:=x0) in SAT31.
  apply Qlt_bool_trans with receive_level.
  apply Qle_bool_iff. unfold Qle. simpl. omega.
  rewrite <- EQ. apply SAT31. assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc in SAT4; try assumption.
  apply rule_assoc in SAT4; try assumption.
  apply rule_assoc in SAT4; try assumption.
  apply rule_comm in SAT4; try assumption.
  apply rule_assoc in SAT4; try assumption.
  apply sat_star_imps with (Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil))
          ((Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) ** Aobs O ** Atic (Enum gv)) **
          Apointsto fv (cell_loc (Eplus ch (Enum 2))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m); try assumption.
  intros. assumption.
  intros. apply rule_assoc in SAT0; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil))
          ((Aobs O ** Atic (Enum gv)) **
          Apointsto fv (cell_loc (Eplus ch (Enum 2))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m); try assumption.
  intros. assumption.
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc in SAT5; try assumption.
  apply sat_star_imps with (Aobs O)
          (Atic (Enum gv) **
          Apointsto fv (cell_loc (Eplus ch (Enum 2))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Atic (Enum gv))
          (Apointsto fv (cell_loc (Eplus ch (Enum 2))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m); try assumption.
  intros. assumption.
  intros.
  apply rule_comm; try assumption.

  apply sat_star_imps with (Apointsto fv (cell_loc (Eplus ch (Enum 2))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m) (Abool true); try assumption.
  apply rule_pure_star; try assumption. split. assumption. reflexivity.
  intros.
  apply sat_star_imps with (Apointsto fv (cell_loc (Eplus ch (Enum 2))) (Enum (Aof v)))
          (Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m); try assumption.
  intros. apply next_plus2; try assumption. intros. assumption.
  intros.
  apply rule_prop_star'; try assumption. split. assumption.
  apply rule_pure_star'; try assumption. split.
  apply andb_true_iff. split. apply Z.eqb_eq. reflexivity. assumption. assumption.
  intros.
  apply rule_pure_prop_star'; try assumption.
  apply rule_assoc in SAT0; try assumption.
  intros. assumption.
  }
  simpl.
  intros.
  rewrite subse_free.
  apply rule_conseq1 with (EX wt, (EX ot, (EX y, (EX y0, (EX y1, (EX y2, (EX y3, (EX y4,
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) wt ot **
    (Aprop (0 < y3 /\ y3 < 1 /\ 0 < y4 < 1) **
    Apointsto y3 (Enum ([[ch]]), 0%Qc, Enum ([[ch]]), None, false, ND, ND, nil) (Enum y) **
    Apointsto y4 (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0%Qc, Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) (Enum y2) **
    subsa (subsa (queue y y0) (subse chInv ([[ch]]))) (subse gcInv gv) ** Actr (Enum gv) y1) **
    Abool ((wt y2 <=? ot y2)%nat && (wt y2 + y1 <=? ot y2 + y0)%nat) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\  v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof v)) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))))))))).

  apply rule_exists1.
  intros Wt.
  apply rule_exists1.
  intros Ot.
  apply rule_exists1.
  intros qi.
  apply rule_exists1.
  intros sizei.
  apply rule_exists1.
  intros Ct.
  apply rule_exists1.
  intros vi.
  apply rule_exists1.
  intros fqi.
  apply rule_exists1.
  intros fvi.
  simpl.

  apply rule_conseq1 with (
    Apointsto fqi (cell_loc ch) (Enum qi) **
    (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot **
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    queue qi sizei **
    Actr (Enum gv) Ct **
    Abool ((Wt (Aof v) <=? Ot (Aof v))%nat && (Wt (Aof v) + Ct <=? Ot (Aof v) + sizei)%nat) **
    Apointsto fvi (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).

  apply rule_Let with (fun z' => (Abool (Z.eqb z' ([[Enum qi]])) &*
    Apointsto fqi (cell_loc ch) (Enum qi)) **
    (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot **
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    queue qi sizei **
    Actr (Enum gv) Ct **
    Abool ((Wt (Aof v) <=? Ot (Aof v))%nat && ((Wt (Aof v)) + Ct <=? Ot (Aof v) + sizei)%nat) **
    Apointsto fvi (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).
  apply rule_frame.
  apply rule_Lookup.
  simpl.
  intros.
  rewrite neqz; try omega.
  rewrite neqz; try omega.
  simpl.
  rewrite eqz.
  repeat rewrite subse_free; try reflexivity.
  rewrite subs_size_of; try reflexivity.
  simpl.
  rewrite neqz; try omega.
  rewrite subs_size_of; try reflexivity.
  simpl.
  rewrite neqz; try omega.
  rewrite subs_size_of; try reflexivity.
  simpl.
  rewrite neqz; try omega.
  simpl.
  rewrite subs_size_of; try reflexivity.
  simpl.
  rewrite eqz.
  rewrite subs_dequeue.
  simpl.
  rewrite neqz; try omega.
  rewrite subs_dequeue.
  simpl.
  rewrite neqz; try omega.
  rewrite subs_dequeue.
  simpl.
  rewrite neqz; try omega.
  rewrite subs_dequeue.
  simpl.
  rewrite neqz; try omega.
  simpl.
  rewrite eqz.
  simpl.

  apply rule_Let with (fun _ => EX Wt', (EX Ot', (EX size', (EX Ct', (EX fqi',(EX fv',(
    Abool (Nat.ltb 0 size') &*
    Apointsto fqi' (cell_loc ch) (Enum z2)) **
    (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot' **
    Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1) **
    queue z2 size' **
    Actr (Enum gv) Ct' **
    Abool ((Wt' (Aof v) <=? Ot' (Aof v))%nat && (Wt' (Aof v) + Ct' <=? Ot' (Aof v) + size')%nat) **
    Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)))))))).
{
  simpl.
  apply rule_conseq1 with (
   (EX Wt,(EX Ot,(EX sizei,(EX Ct,(EX fqi,(EX fvi,(
   Apointsto fqi (cell_loc ch) (Enum z2) **
   (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot **
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
    queue z2 sizei **
    Actr (Enum gv) Ct **
    Abool ((Wt (Aof v) <=? Ot (Aof v))%nat && (Wt (Aof v) + Ct <=? Ot (Aof v) + sizei)%nat) **
    Apointsto fvi (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
    Abool
      (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
       forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)))))))))).

  apply rule_conseq2 with (fun _ : Z => EX ms,
   (EX Wt',
   (EX Ot',
    (EX size',
     (EX Ct',(EX fqi',(EX fv',(
      (Abool ((ms =? 1 - Z.of_nat size')%Z) **
      Apointsto fqi' (cell_loc ch) (Enum z2)) **
      (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
       Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot' **
       Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1) **
       queue z2 size' **
       Actr (Enum gv) Ct' **
       Abool ((Wt' (Aof v) <=? Ot' (Aof v))%nat && (Wt' (Aof v) + Ct' <=? Ot' (Aof v) + size')%nat) **
       Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
       Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
       Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
       Atic (Enum gv) **
       Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
       Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
       Abool
         (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
          forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))))))))) &*
       Abool (Z.leb ms 0)).
  {
  apply rule_While.
  {
  apply rule_exists1. intros WT0.
  apply rule_exists1. intros OT0.
  apply rule_exists1. intros size0.
  apply rule_exists1. intros CT0.
  apply rule_exists1. intros fqi0.
  apply rule_exists1. intros fv0.

  apply rule_conseq1 with (queue z2 size0 **
    Apointsto fqi0 (cell_loc ch) (Enum z2) **
    (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT0 OT0 **
    Aprop (0 < fqi0 /\ fqi0 < 1 /\ 0 < fv0 < 1) **
    Actr (Enum gv) CT0 **
    Abool ((WT0 (Aof v) <=? OT0 (Aof v))%nat && (WT0 (Aof v) + CT0 <=? OT0 (Aof v) + size0)%nat) **
    Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
    Abool
      (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
       forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).
  apply rule_Let with (fun z' => (queue z2 size0 &* Abool (Z.eqb z' (Z.of_nat size0))) **
    Apointsto fqi0 (cell_loc ch) (Enum z2) **
    (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT0 OT0 **
    Aprop (0 < fqi0 /\ fqi0 < 1 /\ 0 < fv0 < 1) **
    Actr (Enum gv) CT0 **
    Abool ((WT0 (Aof v) <=? OT0 (Aof v))%nat && (WT0 (Aof v) + CT0 <=? OT0 (Aof v) + size0)%nat) **
    Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
    Abool
      (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
       forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).
  apply rule_frame.
  apply rule_size_of; try assumption.
  {
  inversion NODUP. inversion H2. inversion H6. inversion H10. inversion H14. inversion H18.
  inversion H22. inversion H26. inversion H30. assumption.
  }
  simpl. repeat split; reflexivity.
  simpl.
  intros.
  rewrite eqz.
  apply rule_conseq1 with (Abool true ** queue z2 size0 ** Abool (Z.eqb z3 (Z.of_nat size0)) **
    Apointsto fqi0 (cell_loc ch) (Enum z2) **
    (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT0 OT0 **
    Aprop (0 < fqi0 /\ fqi0 < 1 /\ 0 < fv0 < 1) **
    Actr (Enum gv) CT0 **
    Abool ((WT0 (Aof v) <=? OT0 (Aof v))%nat && (WT0 (Aof v) + CT0 <=? OT0 (Aof v) + size0)%nat) **
    Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
    Abool
      (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
       forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).
  apply rule_conseq2 with (fun z' => Abool (Z.eqb z' ([[(Eplus (Enum 1) (Eneg (Enum z3)))]])) ** queue z2 size0 ** Abool (Z.eqb z3 (Z.of_nat size0)) **
    Apointsto fqi0 (cell_loc ch) (Enum z2) **
    (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT0 OT0 **
    Aprop (0 < fqi0 /\ fqi0 < 1 /\ 0 < fv0 < 1) **
    Actr (Enum gv) CT0 **
    Abool ((WT0 (Aof v) <=? OT0 (Aof v))%nat && (WT0 (Aof v) + CT0 <=? OT0 (Aof v) + size0)%nat) **
    Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
    Abool
      (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
       forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).
  apply rule_frame.
  apply rule_Val.
  intros.
  exists WT0, OT0, size0, CT0, fqi0, fv0.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT1).
  apply rule_comm in SAT1; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply rule_star_pure in SAT1; try assumption.
  destruct SAT1 as (SAT1,SAT2).
  simpl in SAT, SAT1.
  rewrite Z.eqb_eq in SAT, SAT1.
  rewrite SAT1 in *.
  apply rule_assoc'; try assumption.
  apply rule_pure_star'; try assumption.
  split. simpl.
  apply Z.eqb_eq.
  destruct size0. simpl in SAT. rewrite SAT. simpl. reflexivity.
  simpl in SAT. rewrite SAT. simpl. reflexivity.
  {
  apply rule_assoc in SAT2; try assumption.
  apply sat_star_imps with (Apointsto fqi0 (cell_loc ch) (Enum z2))
          ((Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
           Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT0 OT0 **
           Aprop (0 < fqi0 /\ fqi0 < 1 /\ 0 < fv0 < 1) **
           Actr (Enum gv) CT0 **
           Abool ((WT0 (Aof v) <=? OT0 (Aof v))%nat && (WT0 (Aof v) + CT0 <=? OT0 (Aof v) + size0)%nat) **
           Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
           Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
           Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
           Atic (Enum gv) **
           Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
           Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
           Abool
             (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
              forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)) **
          queue z2 size0); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_comm in SAT0; try assumption.
  apply sat_star_imps with (queue z2 size0)
          (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
          Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT0 OT0 **
          Aprop (0 < fqi0 /\ fqi0 < 1 /\ 0 < fv0 < 1) **
          Actr (Enum gv) CT0 **
          Abool ((WT0 (Aof v) <=? OT0 (Aof v))%nat && (WT0 (Aof v) + CT0 <=? OT0 (Aof v) + size0)%nat) **
          Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Atic (Enum gv) **
          Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros. assumption. intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  }
  {
  intros.
  apply rule_pure_star'; try assumption. split. reflexivity.
  apply rule_assoc; try assumption.
  apply sat_star_imps with ((queue z2 size0 &* Abool (z3 =? Z.of_nat size0)))
         (Apointsto fqi0 (cell_loc ch) (Enum z2) **
         Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
         Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT0 OT0 **
         Aprop (0 < fqi0 /\ fqi0 < 1 /\ 0 < fv0 < 1) **
         Actr (Enum gv) CT0 **
         Abool ((WT0 (Aof v) <=? OT0 (Aof v))%nat && (WT0 (Aof v) + CT0 <=? OT0 (Aof v) + size0)%nat) **
         Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
         Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
         Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
         Atic (Enum gv) **
         Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
         Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
         Abool
           (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
            forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros. apply rule_pure_star; try assumption.
  intros. assumption.
  }
  {
  intros.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (queue z2 size0)
         ((Actr (Enum gv) CT0 **
          Abool ((WT0 (Aof v) <=? OT0 (Aof v))%nat && (WT0 (Aof v) + CT0 <=? OT0 (Aof v) + size0)%nat) **
          Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Atic (Enum gv) **
          Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)) **
         ((Apointsto fqi0 (cell_loc ch) (Enum z2) **
           Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O)) **
          Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT0 OT0) **
         Aprop (0 < fqi0 /\ fqi0 < 1 /\ 0 < fv0 < 1)); try assumption.
  intros. assumption.
  intros.
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  }
  }
  {
  intros.
  apply rule_exists1. intros WT0.
  apply rule_exists1. intros OT0.
  apply rule_exists1. intros size0.
  apply rule_exists1. intros CT0.
  apply rule_exists1. intros fqi0.
  apply rule_exists1. intros fv0.
  apply rule_conseq1 with ((Actr (Enum gv) CT0 ** Atic (Enum gv)) ** 
    Abool (z3 =? 1 - Z.of_nat size0) ** Apointsto fqi0 (cell_loc ch) (Enum z2) **
    (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT0 OT0 **
    Aprop (0 < fqi0 /\ fqi0 < 1 /\ 0 < fv0 < 1) **
    queue z2 size0 **
    Abool ((WT0 (Aof v) <=? OT0 (Aof v))%nat && (WT0 (Aof v) + CT0 <=? OT0 (Aof v) + size0)%nat) **
    Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
    Abool
      (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
       forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).

  apply rule_Let with (fun _ => (Actr (Enum gv) (CT0-1) &* Abool (Nat.ltb 0 CT0)) ** 
    Abool (z3 =? 1 - Z.of_nat size0) ** Apointsto fqi0 (cell_loc ch) (Enum z2) **
    (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT0 OT0 **
    Aprop (0 < fqi0 /\ fqi0 < 1 /\ 0 < fv0 < 1) **
    queue z2 size0 **
    Abool ((WT0 (Aof v) <=? OT0 (Aof v))%nat && (WT0 (Aof v) + CT0 <=? OT0 (Aof v) + size0)%nat) **
    Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
    Abool
      (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
       forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).
  apply rule_frame.
  apply rule_g_ctrdec.
  {
  intros.
  apply rule_conseq1 with (
    ((Abool (andb (Z.eqb ([[(Enum z0)]]) ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]]))
    (andb (Z.eqb ([[(Enum z)]]) ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]]))
    (andb (Z.eqb ([[Lof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]])
                 ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]]))
    (safe_obs (evall (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil))
              (S (WT0 ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]])))
              (OT0 ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]])))))) &*
    (Aprop (prcl (evalol (Oof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil))) (map evalol O)) &*
    Aprop (prcl (evalol (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)))
    (map evalol (M'of (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) ++ O)))) &* 
    ((subsas (snd (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)))
    (channels_invs (fst (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)))
    (upd Z.eq_dec WT0 ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]])
    (S (WT0 ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]])))) OT0)) ** 
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT0 OT0)))
    **
    (EX fqi, (EX fv, (
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fv < 1) **
    Apointsto fqi (cell_loc ch) (Enum z2) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))))).

  apply rule_conseq2 with (fun _ => (EX wt', (EX ot', 
    (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: M'of (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) ++ O) **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) wt' ot' **
    (subsas (snd (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)))
    (channels_invs (fst (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil))) wt' ot')) ** 
    (subsas (snd (Mof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)))
    (channels_invs (fst (Mof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil))) empb empb)))))
    **
    (EX fqi, (EX fv, (
    Aprop (0 < fqi /\ fqi < 1 /\ 0 < fv < 1) **
    Apointsto fqi (cell_loc ch) (Enum z2) **
    Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))))).
    apply rule_frame.
    apply rule_Wait.
  {
  intros.
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (wt,SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (ot,SAT).
  exists wt, ot.

  apply rule_assoc in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.

  apply sat_star_imps with 
  (a':=(EX q, (EX size, (EX Ct, (EX v, (EX fq, (EX fv', (
  Aprop (Qclt 0 fq /\ Qclt fq 1 /\ Qclt 0 fv' /\ Qclt fv' 1) **
  Apointsto fq (cell_loc (Enum ([[ch]]))) (Enum q) **
  Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum v) **
  subsa (subsa (queue q size) (subse chInv ([[ch]]))) (subse gcInv gv) **
  Actr (Enum gv) Ct **
  Abool (andb (Nat.leb (wt v)%nat (ot v)%nat)
        (Nat.leb (wt v + Ct) (ot v + size)))))))))))
  (b':=subsas (snd (Mof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)))
           (channels_invs (fst (Mof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil))) empb empb) **
         (((EX fqi,
            (EX fv,
             Aprop (0 < fqi /\ fqi < 1 /\ 0 < fv < 1) **
             Apointsto fqi (cell_loc ch) (Enum z2) **
             Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
             Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
             Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
             Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
             Abool
               (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
                forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))) **
           Aobs
             (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
              :: M'of (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) ++ O)) **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)) **
         Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) wt ot)
  in SAT; try assumption.
  {
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (q',SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (size',SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (CT',SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (v',SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (fq',SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (fv',SAT).
  exists size', CT'.
  apply rule_assoc' in SAT; try assumption .
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption .
  apply rule_assoc in SAT; try assumption .
  apply rule_assoc in SAT; try assumption .
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (fqq,SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (fvv,SAT).
  exists fqq, fvv.
  assert (EQ1: z2 = q').
  {
  apply rule_assoc in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (S1,S2).
  apply sat_star_imps with (a':=Apointsto fqq (cell_loc ch) (Enum z2))
    (b':=Apointsto fq' (cell_loc ch) (Enum q')) in S2; try assumption.
  apply rule_points_to_value in S2; try assumption.
  destruct S2. assumption.
  intros.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (S3,S4). assumption.
  intros.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (S3,S4).
  apply rule_star_pure in S4; try assumption.
  destruct S4 as (S4,S5).
  apply rule_star_pure in S4; try assumption.
  destruct S4 as (S4,S6).
  apply rule_star_pure in S6; try assumption.
  destruct S6 as (S6,S7).
  assumption.
  }

  assert (EQ2: (Aof v) = v').
  {
  apply rule_assoc in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (S1,S2).
  apply sat_star_imps with (a':=Apointsto fvv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)))
    (b':=Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum v')) in S2; try assumption.
  apply rule_points_to_value in S2; try assumption.
  destruct S2.
  assumption.
  intros.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (S3,S4).
  apply rule_star_pure in S4; try assumption.
  destruct S4 as (S4,S5).
  assumption.
  intros.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (S3,S4).
  apply rule_star_pure in S4; try assumption.
  destruct S4 as (S4,S5).
  apply rule_star_pure in S4; try assumption.
  destruct S4 as (S4,S6).
  apply rule_star_pure in S6; try assumption.
  destruct S6 as (S6,S7).
  apply rule_star_pure in S7; try assumption.
  destruct S7 as (S7,S8).
  assumption.
  }
  rewrite EQ1, <- EQ2 in *.
  apply rule_assoc in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT1).
  apply rule_assoc in SAT1; try assumption.
  apply sat_star_imps with (Apointsto fqq (cell_loc ch) (Enum q'))
          ((Apointsto fvv (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
             (Enum (Aof v)) **
           Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
           Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
           Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
           Abool
             (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
              forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x))
                O)) **
          Aobs
            (Oof
               (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
             :: M'of (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) ++ O) **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Alocked
            (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) wt
            ot **
          (Aprop (0 < fq' /\ fq' < 1 /\ 0 < fv' < 1) **
           Apointsto fq' (cell_loc (Enum ([[ch]]))) (Enum q') **
           Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
             (Enum (Aof v)) **
           subsa (subsa (queue q' size') (subse chInv ([[ch]]))) (subse gcInv gv) **
           Actr (Enum gv) CT' **
           Abool
             ((wt (Aof v) <=? ot (Aof v))%nat &&
              (wt (Aof v) + CT' <=? ot (Aof v) + size')%nat)) **
          subsas
            (snd (Mof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)))
            (channels_invs
               (fst (Mof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)))
               empb empb)); try assumption.
  intros. assumption. intros.
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply sat_star_imps with (Aobs
            (Oof
               (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
             :: M'of (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) ++ O))
          ((Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
           Alocked
             (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) wt
             ot **
           (Aprop (0 < fq' /\ fq' < 1 /\ 0 < fv' < 1) **
            Apointsto fq' (cell_loc (Enum ([[ch]]))) (Enum q') **
            Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
              (Enum (Aof v)) **
            subsa (subsa (queue q' size') (subse chInv ([[ch]])))
              (subse gcInv gv) **
            Actr (Enum gv) CT' **
            Abool
              ((wt (Aof v) <=? ot (Aof v))%nat &&
               (wt (Aof v) + CT' <=? ot (Aof v) + size')%nat)) **
           subsas
             (snd (Mof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)))
             (channels_invs
                (fst (Mof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)))
                empb empb)) **
          Apointsto fvv (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
            (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros. rewrite app_nil_l in SAT0. assumption. intros.
  apply rule_assoc in SAT2; try assumption.
  apply rule_comm in SAT2; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply sat_star_imps with (Alocked
            (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) wt
            ot) (((Aprop (0 < fq' /\ fq' < 1 /\ 0 < fv' < 1) **
            Apointsto fq' (cell_loc (Enum ([[ch]]))) (Enum q') **
            Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
              (Enum (Aof v)) **
            subsa (subsa (queue q' size') (subse chInv ([[ch]])))
              (subse gcInv gv) **
            Actr (Enum gv) CT' **
            Abool
              ((wt (Aof v) <=? ot (Aof v))%nat &&
               (wt (Aof v) + CT' <=? ot (Aof v) + size')%nat)) **
           subsas
             (snd (Mof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)))
             (channels_invs
                (fst (Mof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)))
                empb empb)) **
          (Apointsto fvv (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
             (Enum (Aof v)) **
           Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
           Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
           Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
           Abool
             (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
              forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x))
                O)) **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)); try assumption.
  intros. assumption. intros.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_star_pure in SAT3; try assumption.
  destruct SAT3 as (SAT3,SAT4).
  apply rule_prop_star'; try assumption.
  split. assumption.
  apply rule_comm in SAT4; try assumption.
  apply rule_assoc in SAT4; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (subsas
            (snd
               (Mof
                  (Enum (Aof v), Rof v, m, None, false, ND, 
                  Mv gv, nil)))
            (channels_invs
               (fst
                  (Mof
                     (Enum (Aof v), Rof v, m, None, false, ND, 
                     Mv gv, nil))) empb empb))
          (((Apointsto fvv
              (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
              (Enum (Aof v)) **
            Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
            Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
            Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
            Abool
              (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x))
                 O &&
               forallb
                 (fun x : olocation exp =>
                  Qlt_bool receive_level (Rofo x)) O)) **
           Acond
             (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)) **
          Apointsto fq' (cell_loc (Enum ([[ch]]))) (Enum q') **
          Apointsto fv'
            (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
            (Enum (Aof v)) **
          subsa (subsa (queue q' size') (subse chInv ([[ch]])))
            (subse gcInv gv) **
          Actr (Enum gv) CT' **
          Abool
            ((wt (Aof v) <=? ot (Aof v))%nat &&
             (wt (Aof v) + CT' <=? ot (Aof v) + size')%nat)); try assumption.
  intros. assumption. intros.
  apply rule_assoc in SAT5; try assumption.
  apply rule_assoc in SAT5; try assumption.
  apply rule_comm in SAT5; try assumption.
  apply rule_assoc in SAT5; try assumption.
  apply rule_assoc in SAT5; try assumption.
  apply rule_comm in SAT5; try assumption.
  apply rule_assoc in SAT5; try assumption.
  apply rule_star_pure in SAT5; try assumption.
  destruct SAT5 as (SAT5,SAT6).
  apply rule_assoc'; try assumption.
  apply rule_prop_star'; try assumption.
  split. apply rule_star_pure in SAT5; try assumption.
  destruct SAT5 as (S1,SAT5). assumption.
  apply rule_assoc'; try assumption.
  apply rule_pure_star'; try assumption.
  split.
  apply rule_star_pure in SAT5; try assumption.
  destruct SAT5 as (SAT51,SAT5).
  apply rule_star_pure in SAT5; try assumption.
  destruct SAT5 as (SAT5,SAT52). assumption.
  apply rule_pure_star'; try assumption.
  split.
  apply rule_star_pure in SAT5; try assumption.
  destruct SAT5 as (SAT51,SAT5).
  apply rule_star_pure in SAT5; try assumption.
  destruct SAT5 as (SAT5,SAT52). assumption.
  apply rule_comm; try assumption.
  apply rule_assoc in SAT6; try assumption.
  apply rule_assoc in SAT6; try assumption.
  apply sat_star_imps with (Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil))
          ((Apointsto fq' (cell_loc (Enum ([[ch]]))) (Enum q') **
           Apointsto fv'
             (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
             (Enum (Aof v)) **
           subsa (subsa (queue q' size') (subse chInv ([[ch]])))
             (subse gcInv gv) **
           Actr (Enum gv) CT' **
           Abool
             ((wt (Aof v) <=? ot (Aof v))%nat &&
              (wt (Aof v) + CT' <=? ot (Aof v) + size')%nat)) **
          Apointsto fvv
            (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
            (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m); try assumption.
  intros. assumption. intros.
  apply rule_assoc'; try assumption.

  apply sat_star_imps with ((Apointsto fq' (cell_loc (Enum ([[ch]]))) (Enum q') **
           Apointsto fv'
             (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
             (Enum (Aof v)) **
           subsa (subsa (queue q' size') (subse chInv ([[ch]])))
             (subse gcInv gv) **
           Actr (Enum gv) CT' **
           Abool
             ((wt (Aof v) <=? ot (Aof v))%nat &&
              (wt (Aof v) + CT' <=? ot (Aof v) + size')%nat)))
          (Apointsto fvv
            (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
            (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m); try assumption.
  intros.
  apply rule_assoc' in SAT8; try assumption.
  apply rule_star_pure in SAT8; try assumption.
  destruct SAT8 as (S,SAT8).
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (subsa (subsa (queue q' size') (subse chInv ([[ch]])))
            (subse gcInv gv))
          (Actr (Enum gv) CT' **
          Abool
            ((wt (Aof v) <=? ot (Aof v))%nat &&
             (wt (Aof v) + CT' <=? ot (Aof v) + size')%nat)); try assumption.
  eapply subsa_queue2; try assumption. intros. assumption.
  intros. assumption.
  }
  intros. assumption.
  intros. assumption.
  }
  intros.
  apply sat_star_imps with (((Abool
       ((([[Enum z0]]) =? ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]])) &&
        ((([[Enum z]]) =? ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]])) &&
         ((([[Lof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]]) =?
           ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]])) &&
          safe_obs (evall (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil))
            (S (WT0 ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]])))
            (OT0 ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]]))))) **
     (Aprop (prcl (evalol (Oof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil))) (map evalol O)) **
      Aprop
        (prcl (evalol (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)))
           (map evalol (M'of (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) ++ O))))) **
    subsas (snd (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)))
      (channels_invs (fst (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)))
         (upd Z.eq_dec WT0 ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]])
            (S (WT0 ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]])))) OT0) **
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT0 OT0))
   ((EX fqi1,
    (EX fv1,
     Aprop (0 < fqi1 /\ fqi1 < 1 /\ 0 < fv1 < 1) **
     Apointsto fqi1 (cell_loc ch) (Enum z2) **
     Apointsto fv1 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
     Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
     Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
     Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
     Abool
       (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
        forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)))); try assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_pure_star'; try assumption.
  split.
  {
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT0,SAT).
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT1,SAT).
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT2,SAT).
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT3,SAT).
  apply andb_true_iff in SAT3.
  destruct SAT3 as (SAT3,SAT4).
  destruct SAT0 as (SAT00,SAT0).
  apply Nat.ltb_lt in SAT0.
  apply Nat.leb_le in SAT4.
  apply Z.eqb_eq in SAT1.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT5,SAT).
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT6).
  apply andb_true_iff in SAT.
  destruct SAT as (SAT,SAT7).
  apply Z.eqb_eq in SAT.
  apply Z.eqb_eq in SAT7.
  rewrite SAT, SAT7.
  apply andb_true_iff. split. apply Z.eqb_eq. reflexivity.
  apply andb_true_iff. split. apply Z.eqb_eq. reflexivity.
  apply andb_true_iff. split. apply Z.eqb_eq. reflexivity.
  unfold safe_obs. simpl.
  apply andb_true_iff. split.
  apply Nat.ltb_lt.
  omega.
  destruct (opQc_eq_dec (Xof (evall (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil))) None).
  reflexivity. contradiction.
  }
  apply rule_assoc'; try assumption.
  apply rule_prop_star'; try assumption.
  split. simpl.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT0,SAT).
  apply andb_true_iff in SAT.
  destruct SAT as (SAT,SAT1).
  apply precedence_relaxed; try assumption. reflexivity.
  apply rule_prop_star'; try assumption.
  split. simpl.
  apply precedence_relaxed; try assumption.
  apply forallb_forall. intros. simpl.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT0,SAT).
  apply andb_true_iff in SAT.
  destruct SAT as (SAT,SAT1).

  eapply forallb_forall in SAT1. simpl in SAT1.
  apply Qlt_bool_trans with receive_level.
  unfold receive_level.
  apply Qle_bool_iff.
  unfold Qle. simpl. omega. apply SAT1. assumption. reflexivity.
  apply sat_star_imps with ((
(
EX q, (EX size, (EX Ct, (EX v', (EX fq, (EX fv, (
  Aprop (Qclt 0 fq /\ Qclt fq 1 /\ Qclt 0 fv /\ Qclt fv 1) **
  Apointsto fq (cell_loc ch) (Enum q) **
  Apointsto fv (next_loc (next_loc (cell_loc ch))) (Enum v') **
  (subsa (subsa (queue q size) (subse chInv ([[ch]]))) (subse gcInv gv)) **
  Actr (Enum gv) Ct **
  Abool (andb (Nat.leb ((upd Z.eq_dec WT0 ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]])
            (S (WT0 ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]])))) v')%nat (OT0 v')%nat)
        (Nat.leb ((upd Z.eq_dec WT0 ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]])
            (S (WT0 ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]])))) v' + Ct) (OT0 v' + size)))))))))
)
 **
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT0 OT0))
   ((EX fqi1,
    (EX fv1,
     Aprop (0 < fqi1 /\ fqi1 < 1 /\ 0 < fv1 < 1) **
     Apointsto fqi1 (cell_loc ch) (Enum z2) **
     Apointsto fv1 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
     Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
     Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
     Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
     Abool
       (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
        forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)))); try assumption.
  {
  apply rule_assoc'; try assumption.
  apply rule_exists_dist'; try assumption.
  exists z2.
  apply rule_exists_dist'; try assumption.
  exists size0.
  apply rule_exists_dist'; try assumption.
  exists (CT0 - 1)%nat.
  apply rule_exists_dist'; try assumption.
  exists (Aof v).
  apply rule_exists_dist'; try assumption.
  exists (fqi0/(1+1)).
  apply rule_exists_dist'; try assumption.
  exists (fv0/(1+1)).
  apply rule_assoc'; try assumption.
  apply rule_prop_star'; try assumption.
  assert (bnd: 0 < fqi0 / (1 + 1) /\ fqi0 / (1 + 1) < 1 /\ 0 < fv0 / (1 + 1) < 1).
  {
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT0,SAT).
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT2).
  destruct SAT as (s1,(s2,s3)).
  split. apply frac2_pos. assumption.
  split. apply frac2_bound. split; assumption.
  split. apply frac2_pos. destruct s3. assumption.
  apply frac2_bound. assumption.
  }
  split. assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_exists_dist'; try assumption.
  exists (fqi0/(1+1)).
  apply rule_exists_dist'; try assumption.
  exists (fv0/(1+1)).
  apply rule_assoc'; try assumption.
  apply rule_prop_star'; try assumption.
  split. simpl. assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.

  apply sat_star_imps with (Aobs
           (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
            :: O))
         ((Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
            WT0 OT0 **
          Aprop (0 < fqi0 /\ fqi0 < 1 /\ 0 < fv0 < 1) **
          queue z2 size0 **
          Abool
            ((WT0 (Aof v) <=? OT0 (Aof v))%nat &&
             (WT0 (Aof v) + CT0 <=? OT0 (Aof v) + size0)%nat) **
          Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
            (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)) **
         ((Actr (Enum gv) (CT0 - 1) &* Abool (0 <? CT0)%nat) **
          Abool (z3 =? 1 - Z.of_nat size0)) **
         Apointsto fqi0 (cell_loc ch) (Enum z2)); try assumption.
  intros. assumption. intros.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)
            WT0 OT0)
          ((Aprop (0 < fqi0 /\ fqi0 < 1 /\ 0 < fv0 < 1) **
           queue z2 size0 **
           Abool
             ((WT0 (Aof v) <=? OT0 (Aof v))%nat &&
              (WT0 (Aof v) + CT0 <=? OT0 (Aof v) + size0)%nat) **
           Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
             (Enum (Aof v)) **
           Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
           Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
           Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
           Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
           Abool
             (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
              forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)) **
          ((Actr (Enum gv) (CT0 - 1) &* Abool (0 <? CT0)%nat) **
           Abool (z3 =? 1 - Z.of_nat size0)) **
          Apointsto fqi0 (cell_loc ch) (Enum z2)); try assumption.
  intros. assumption. intros.
  apply rule_assoc in SAT1; try assumption.
  apply rule_star_pure in SAT1; try assumption.
  destruct SAT1 as (SAT1,SAT2).
  apply rule_comm; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply sat_star_imps with (queue z2 size0)
          ((Abool
             ((WT0 (Aof v) <=? OT0 (Aof v))%nat &&
              (WT0 (Aof v) + CT0 <=? OT0 (Aof v) + size0)%nat) **
           Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
             (Enum (Aof v)) **
           Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
           Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
           Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
           Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
           Abool
             (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
              forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)) **
          ((Actr (Enum gv) (CT0 - 1) &* Abool (0 <? CT0)%nat) **
           Abool (z3 =? 1 - Z.of_nat size0)) **
          Apointsto fqi0 (cell_loc ch) (Enum z2)); try assumption.
  intros.
  eapply subsa_queue2'; try assumption. intros.
  apply rule_assoc'; try assumption.
  apply rule_comm in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply sat_star_imps with (a':= (Actr (Enum gv) (CT0 - 1) ** Abool (0 <? CT0)%nat))
          (b':=Abool (z3 =? 1 - Z.of_nat size0) **
          Apointsto fqi0 (cell_loc ch) (Enum z2) **
          Abool ((WT0 (Aof v) <=? OT0 (Aof v))%nat && (WT0 (Aof v) + CT0 <=? OT0 (Aof v) + size0)%nat) **
          Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))
    in SAT3; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply sat_star_imps with (Actr (Enum gv) (CT0 - 1))
          (Abool (0 <? CT0)%nat **
          Abool (z3 =? 1 - Z.of_nat size0) **
          Apointsto fqi0 (cell_loc ch) (Enum z2) **
          Abool ((WT0 (Aof v) <=? OT0 (Aof v))%nat && (WT0 (Aof v) + CT0 <=? OT0 (Aof v) + size0)%nat) **
          Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros. assumption. intros.
  apply rule_star_pure in SAT4; try assumption.
  destruct SAT4 as (SAT4,SAT5).
  apply rule_star_pure in SAT5; try assumption.
  destruct SAT5 as (SAT5,SAT6).
  apply rule_comm in SAT6; try assumption.
  apply rule_assoc in SAT6; try assumption.
  apply rule_star_pure in SAT6; try assumption.
  destruct SAT6 as (SAT6,SAT7).
  apply rule_pure_star'; try assumption.
  split.
  apply Coq.Bool.Bool.andb_true_iff in SAT6.
  destruct SAT6 as (SAT6,SAT61).
  apply Nat.leb_le in SAT6.
  apply Nat.leb_le in SAT61.
  apply Z.eqb_eq in SAT5.
  apply Coq.Bool.Bool.andb_true_iff.
  apply Nat.ltb_lt in SAT4.
  assert (LE1: (S (WT0 (Aof v)) + (CT0 - 1) <= OT0 (Aof v) + size0)%nat). omega.
  split.
  apply Nat.leb_le. simpl. unfold upd. rewrite eqz. omega.
  apply Nat.leb_le. simpl. unfold upd. rewrite eqz. omega.
  apply rule_comm in SAT7; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc' in SAT7; try assumption.
  apply rule_assoc' in SAT7; try assumption.
  apply rule_comm in SAT7; try assumption.
  apply rule_assoc in SAT7; try assumption.
  apply sat_star_imps with (Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil))
          ((Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
           Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
           Abool
             (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
              forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)) **
          (Apointsto fqi0 (cell_loc ch) (Enum z2) **
           Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m); try assumption.
  intros. assumption. intros.
  apply rule_star_pure in SAT8; try assumption.
  destruct SAT8 as (SAT8,SAT9).  
  apply rule_comm; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with ((Apointsto fqi0 (cell_loc ch) (Enum z2) **
           Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v))))
          (Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m); try assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Apointsto (fqi0 / (1 + 1)) (cell_loc ch) (Enum z2))
   (Apointsto (fqi0 / (1 + 1)) (cell_loc ch) (Enum z2) **
    Apointsto (fv0 / (1 + 1)) (next_loc (next_loc (cell_loc ch))) (Enum (Aof v)) **   
   Apointsto (fv0 / (1 + 1)) (next_loc (next_loc (cell_loc ch))) (Enum (Aof v))); try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (Apointsto fqi0 (cell_loc ch) (Enum z2))
           (Apointsto fv0 (next_loc (next_loc (cell_loc ch))) (Enum (Aof v))); try assumption.
  intros. apply rule_points_to_fraction'; try assumption.
  destruct bnd. assumption.
  destruct bnd. assumption.
  replace (fqi0 / (1 + 1) + fqi0 / (1 + 1)) with fqi0. assumption.
  apply frac2_plus.
  destruct bnd as (b1,(b2,(b3,b4))).
  intros. apply rule_points_to_fraction'; try assumption.
  rewrite <- frac2_plus. assumption.
  intros. assumption.
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  intros.
  apply sat_star_imps with (Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m)
   (Abool true); try assumption. 
  apply rule_pure_star; try assumption. split. assumption. reflexivity.
  intros. assumption.
  intros.
  apply rule_star_pure in SAT8; try assumption.
  destruct SAT8 as (S8,S9).
  apply rule_star_pure in S9; try assumption.
  destruct S9 as (S9,S10).
  apply rule_prop_star'; try assumption. split.
  assumption.
  apply rule_pure_star'; try assumption. split; assumption.
  intros. apply rule_pure_star; try assumption.
  intros. assumption.
  }
  intros.
  apply sat_star_imps with ((EX q,
           (EX size,
            (EX Ct,
             (EX v',
              (EX fq,
               (EX fv,
                Aprop (0 < fq /\ fq < 1 /\ 0 < fv < 1) **
                Apointsto fq (cell_loc ch) (Enum q) **
                Apointsto fv (next_loc (next_loc (cell_loc ch))) (Enum v') **
                subsa (subsa (queue q size) (subse chInv ([[ch]])))
                  (subse gcInv gv) **
                Actr (Enum gv) Ct **
                Abool
                  ((upd Z.eq_dec WT0 ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]])
                      (S (WT0 ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]]))) v' <=? 
                    OT0 v')%nat &&
                   (upd Z.eq_dec WT0 ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]])
                      (S (WT0 ([[Aof (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)]]))) v' + Ct <=?
                    OT0 v' + size)%nat))))))))
          (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT0 OT0); try assumption.
  intros. assumption.
  intros. assumption.
  intros. assumption.
  intros.
  apply rule_star_pure in SAT0; try assumption.
  destruct SAT0 as (SAT1,SAT2).
  split; try assumption.
  apply rule_star_pure in SAT1; try assumption.
  destruct SAT1 as (SAT3,SAT4).
  split; try assumption.
  apply rule_star_pure in SAT4; try assumption.
  intros. assumption.
  }
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_pure_star'; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT1,SAT2).
  split; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_comm in SAT2; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply sat_star_imps with (Actr (Enum gv) CT0)
          ((Abool ((WT0 (Aof v) <=? OT0 (Aof v))%nat && (WT0 (Aof v) + CT0 <=? OT0 (Aof v) + size0)%nat) **
           Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
           Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
           Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
           Atic (Enum gv) **
           Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
           Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
           Abool
             (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
              forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)) **
          (((Apointsto fqi0 (cell_loc ch) (Enum z2) **
             Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O)) **
            Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT0 OT0) **
           Aprop (0 < fqi0 /\ fqi0 < 1 /\ 0 < fv0 < 1)) ** queue z2 size0); try assumption.
  intros. assumption. intros.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (Atic (Enum gv))
         ((Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)) **
         (((((((Apointsto fqi0 (cell_loc ch) (Enum z2) **
                Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O)) **
               Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT0 OT0) **
              Aprop (0 < fqi0 /\ fqi0 < 1 /\ 0 < fv0 < 1)) ** queue z2 size0) **
            Abool ((WT0 (Aof v) <=? OT0 (Aof v))%nat && (WT0 (Aof v) + CT0 <=? OT0 (Aof v) + size0)%nat)) **
           Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v))) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m) **
         Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)); try assumption.
  intros. assumption. intros.
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  }
  intros.
  destruct SAT as (WT',(OT',(size',(Ct',(fqi',(fv',SAT)))))).
  exists WT', OT', size', Ct', fqi', fv'.
  apply sat_star_imps with ((Abool (z3 =? 1 - Z.of_nat size') ** Apointsto fqi' (cell_loc ch) (Enum z2)))
         (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
         Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT' OT' **
         Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1) **
         queue z2 size' **
         Actr (Enum gv) Ct' **
         Abool ((WT' (Aof v) <=? OT' (Aof v))%nat && (WT' (Aof v) + Ct' <=? OT' (Aof v) + size')%nat) **
         Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
         Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
         Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
         Atic (Enum gv) **
         Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
         Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
         Abool
           (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
            forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros. apply rule_star_pure in SAT0; try assumption.
  destruct SAT0. assumption.
  intros. assumption.
  }
  {
  intros.

  destruct SAT as (ms,SAT).
  destruct SAT as (SAT,MS).
  destruct SAT as (WT',(OT',(size',(Ct',(fqi',(fv',SAT)))))).
  exists WT', OT', size', Ct', fqi', fv'.

  apply sat_star_imps with ((Abool (ms =? 1 - Z.of_nat size') ** Apointsto fqi' (cell_loc ch) (Enum z2)))
         (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
         Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT' OT' **
         Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1) **
         queue z2 size' **
         Actr (Enum gv) Ct' **
         Abool ((WT' (Aof v) <=? OT' (Aof v))%nat && (WT' (Aof v) + Ct' <=? OT' (Aof v) + size')%nat) **
         Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
         Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
         Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
         Atic (Enum gv) **
         Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
         Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
         Abool
           (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
            forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros.
  apply rule_star_pure in SAT0; try assumption.
  destruct SAT0 as (SAT0,SAT1).
  split.
  apply Nat.ltb_lt.
  apply Z.eqb_eq in SAT0.
  apply Z.leb_le in MS.
  omega.
  assumption.
  intros. assumption.
  }
  intros.
  exists Wt, Ot, sizei, Ct, fqi, fvi.
  assert (EQ1: z2 = qi).
  {
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT1,SAT2).
  destruct SAT1 as (SAT1,SAT11).
  apply Z.eqb_eq in SAT1.
  assumption.
  }
  rewrite EQ1 in *.
  apply sat_star_imps with ((Abool (qi =? qi) &* Apointsto fqi (cell_loc ch) (Enum qi)))
         (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
         Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt Ot **
         Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
         queue qi sizei **
         Actr (Enum gv) Ct **
         Abool ((Wt (Aof v) <=? Ot (Aof v))%nat && (Wt (Aof v) + Ct <=? Ot (Aof v) + sizei)%nat) **
         Apointsto fvi (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
         Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
         Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
         Atic (Enum gv) **
         Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
         Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
         Abool
           (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
            forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros.


  destruct SAT0 as (SAT0,SAT1). assumption.
  intros. assumption.
  }
  simpl.
  intros.
  apply rule_exists1.
  intros Wt'.
  apply rule_exists1.
  intros Ot'.
  apply rule_exists1.
  intros size'.
  apply rule_exists1.
  intros Ct'.
  simpl.
  rewrite subs_dequeue.
  simpl.

  apply rule_conseq1 with (EX size'', (EX fqi',
   (EX fv', (
    Apointsto fqi' (cell_loc ch) (Enum z2) **
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot' **
    Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1) **
    queue z2 (S size'') **
    Actr (Enum gv) Ct' **
    Abool ((Wt' (Aof v) <=? Ot' (Aof v))%nat && (Wt' (Aof v) + Ct' <=? Ot' (Aof v) + S size'')%nat) **
    Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? Aof v)) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))))).
  apply rule_exists1.
  intros size''.
  apply rule_exists1.
  intros fqi'.
  apply rule_exists1.
  intros fv'.

  apply rule_conseq1 with (queue z2 (S size'') **
    (Apointsto fqi' (cell_loc ch) (Enum z2) **
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot' **
    Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1) **
    Actr (Enum gv) Ct' **
    Abool ((Wt' (Aof v) <=? Ot' (Aof v))%nat && (Wt' (Aof v) + Ct' <=? Ot' (Aof v) + S size'')%nat) **
    Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).

  apply rule_Let with (fun _ => queue z2 size'' **
    (Apointsto fqi' (cell_loc ch) (Enum z2) **
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot' **
    Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1) **
    Actr (Enum gv) Ct' **
    Abool ((Wt' (Aof v) <=? Ot' (Aof v))%nat && (Wt' (Aof v) + Ct' <=? Ot' (Aof v) + S size'')%nat) **
    Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Atic (Enum gv) **
    Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).
  apply rule_frame.
  apply rule_dequeue.
  {
  inversion NDtmp.
  eapply NoDup_concat.
  apply H2.
  }
  simpl. split; reflexivity.
  simpl.
  intros.
  apply rule_conseq1 with ((Actr (Enum gv) Ct' ** Atic (Enum gv)) **
    (queue z2 size'' **
    Apointsto fqi' (cell_loc ch) (Enum z2) **
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot' **
    Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1) **
    Abool ((Wt' (Aof v) <=? Ot' (Aof v))%nat && (Wt' (Aof v) + Ct' <=? Ot' (Aof v) + S size'')%nat) **
    Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).

  apply rule_Let with (fun _ => (Actr (Enum gv) (Ct'-1) &* Abool (Nat.ltb 0 Ct')) **
    (queue z2 size'' **
    Apointsto fqi' (cell_loc ch) (Enum z2) **
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot' **
    Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1) **
    Abool ((Wt' (Aof v) <=? Ot' (Aof v))%nat && (Wt' (Aof v) + Ct' <=? Ot' (Aof v) + S size'')%nat) **
    Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
    Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
    Abool (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
    forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))).
  apply rule_frame.
  apply rule_g_ctrdec.
  simpl.
  intros.

  apply rule_conseq1 with (EX fv', (
    (Abool (Z.eqb ([[Enum z]]) ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]])) &*
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)::O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot' **
    (subsas (snd (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)))
    (channels_invs (fst (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil))) Wt' Ot'))) **

    (Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv' < 1) /\
    v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil))))).
  apply rule_exists1.
  intros fv''.
  unfold channel.
  apply rule_conseq2 with (fun _ => (EX m0, (EX fm0, (EX fv0, (
    Aprop ((0 < fm0 /\ fm0 < 1 /\ 0 < fv0 < 1) /\
    v = (Aof v, Rof v, [[m0]], None, false, ND, Mv gv, nil)) &*
    Apointsto fm0 (next_loc (cell_loc (Enum ([[ch]])))) m0 **
    Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Alock (m0, new_channel_level, m0, None, false, Linv ([[ch]]) gv, ND, nil) **
    Acond (Enum (Aof v), Rof v, m0, None, false, ND, Mv gv, nil) **
    Aobs O))))).
  apply rule_exists2.
  exists m.
  apply rule_exists2.
  exists fm.
  apply rule_exists2.
  exists fv''.
  apply rule_conseq2 with (fun _ => (Aobs O **
    Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)) **
    (Apointsto fv'' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
    Aprop ((0 < fm /\ fm < 1 /\ 0 < fv'' < 1) /\
    v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)))).
  apply rule_frame.
  apply rule_Release.
  {
  intros.
  apply sat_star_imps with (a':=(Aobs O ** Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)))
         (b':=(Apointsto fv'' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv'' < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)))) in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT1).
  split. assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply sat_star_imps with (Aobs O)
         (Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
         Apointsto fv'' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
         Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
         Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil))
          (Apointsto fv'' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)); try assumption.
  intros. assumption. intros.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply sat_star_imps with (Apointsto fv'' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)))
          (Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)); try assumption.
  intros. assumption. intros.
  apply rule_comm; try assumption.
  intros. assumption.
  intros. assumption.
  }
  {
  intros.
  destruct SAT as (m0,(fm0,(fv0,SAT))).
  apply rule_comm; try assumption.
  apply rule_exists_dist'; try assumption.
  exists m0.
  apply rule_exists_dist'; try assumption.
  exists fm0.
  apply rule_exists_dist'; try assumption.
  exists fv0.
  apply rule_assoc'; try assumption.
  apply rule_prop_star'; try assumption.
  destruct SAT as (SAT1,SAT2).
  split; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_comm in SAT2; try assumption.

  apply sat_star_imps with (Aobs O)
          (((Apointsto fm0 (next_loc (cell_loc (Enum ([[ch]])))) m0 **
            Apointsto fv0 (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v))) **
           Alock (m0, new_channel_level, m0, None, false, Linv ([[ch]]) gv, ND, nil)) **
          Acond (Enum (Aof v), Rof v, m0, None, false, ND, Mv gv, nil)); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  }
  {
  intros.
  assert (fv'b: 0 < fv' / (1 + 1) < 1).
  {
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT5).
  apply rule_star_pure in SAT5; try assumption.
  destruct SAT5 as (SAT5,SAT6).
  destruct SAT5 as (SAT5,(SAT51,(SAT52,SAT53))).
  split. apply frac2_pos. assumption.
  apply frac2_bound. split; assumption.
  }
  exists (fv'/(1+1)).
  apply sat_star_imps with (a':=(Actr (Enum gv) (Ct' - 1) ** Abool (0 <? Ct')%nat))
         (b':=((((queue z2 size'' **
             Apointsto fqi' (cell_loc ch) (Enum z2) **
             Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
             Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot' **
             Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1) **
             Abool ((Wt' (Aof v) <=? Ot' (Aof v))%nat && (Wt' (Aof v) + Ct' <=? Ot' (Aof v) + S size'')%nat) **
             Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
             Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m ** Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)) **
            Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil))) ** Abool ((z =? ([[m]])) && (z0 =? (Aof v)))) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))) in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT1).
  apply rule_comm in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT2).
  apply rule_comm in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT3).
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT4).

  apply sat_star_imps with ((Abool (([[Enum z]]) =? ([[Aof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)]])) **
    Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
    Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot' **
    subsas (snd (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil)))
      (channels_invs (fst (Iof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil))) Wt' Ot')))
   ((Apointsto (fv' / (1 + 1)) (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
    Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) ** Aprop ((0 < fm /\ fm < 1 /\ 0 < fv' / (1 + 1) < 1) /\
    v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)))); try assumption.

  apply rule_assoc'; try assumption.
  apply rule_pure_star'; try assumption.
  apply andb_true_iff in SAT3.
  destruct SAT3 as (SAT3,SAT31).
  apply Z.eqb_eq in SAT3.
  split.
  rewrite SAT3 in *. apply Z.eqb_eq. reflexivity.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O))
         ((Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot' **
          Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1) **
          Abool ((Wt' (Aof v) <=? Ot' (Aof v))%nat && (Wt' (Aof v) + Ct' <=? Ot' (Aof v) + S size'')%nat) **
          Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m ** Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)) **
         (Actr (Enum gv) (Ct' - 1) ** queue z2 size'') ** Apointsto fqi' (cell_loc ch) (Enum z2)); try assumption.
  intros. assumption. intros.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot')
          ((Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1) **
           Abool ((Wt' (Aof v) <=? Ot' (Aof v))%nat && (Wt' (Aof v) + Ct' <=? Ot' (Aof v) + S size'')%nat) **
           Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
           Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m ** Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)) **
          (Actr (Enum gv) (Ct' - 1) ** queue z2 size'') ** Apointsto fqi' (cell_loc ch) (Enum z2)); try assumption.
  intros. assumption. intros.
  apply rule_assoc in SAT5; try assumption.
  apply rule_star_pure in SAT5; try assumption.
  destruct SAT5 as (SAT5,SAT6).
  apply rule_assoc in SAT6; try assumption.
  apply rule_star_pure in SAT6; try assumption.
  destruct SAT6 as (SAT6,SAT7).
  apply rule_comm in SAT7; try assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc' in SAT7; try assumption.
  apply rule_comm in SAT7; try assumption.
  apply sat_star_imps with ((Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m ** Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)))
          (((Actr (Enum gv) (Ct' - 1) ** queue z2 size'') ** Apointsto fqi' (cell_loc ch) (Enum z2)) **
          Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v))); try assumption.
  intros.
  apply rule_assoc; try assumption.
  apply rule_prop_star; try assumption.
  split; try assumption.
  {
  simpl.
  destruct SAT4 as ((SAT4,SAT41),SAT42).
  split. split. assumption. split. assumption. assumption. assumption.
  }
  intros.
  apply sat_star_imps with (
EX q, (EX size, (EX Ct, (EX v, (EX fq, (EX fv, (
  Aprop (Qclt 0 fq /\ Qclt fq 1 /\ Qclt 0 fv /\ Qclt fv 1) **
  Apointsto fq (cell_loc ch) (Enum q) **
  Apointsto fv (next_loc (next_loc (cell_loc ch))) (Enum v) **
  subsa (subsa (queue q size) (subse chInv ([[ch]]))) (subse gcInv gv) **
  Actr (Enum gv) Ct **
  Abool (andb (Nat.leb (Wt' v)%nat (Ot' v)%nat)
        (Nat.leb (Wt' v + Ct) (Ot' v + size)))))))))
)
   (Apointsto (fv' / (1 + 1)) (next_loc (next_loc (cell_loc ch))) (Enum (Aof v))); try assumption.
  {
  apply rule_exists_dist'; try assumption.
  exists z2.
  apply rule_exists_dist'; try assumption.
  exists size''.
  apply rule_exists_dist'; try assumption.
  exists (Ct' - 1)%nat.
  apply rule_exists_dist'; try assumption.
  exists (Aof v).
  apply rule_exists_dist'; try assumption.
  exists fqi'.
  apply rule_exists_dist'; try assumption.
  exists (fv'/(1+1)).
  apply rule_assoc'; try assumption.
  apply rule_prop_star'; try assumption.
  split.
  destruct SAT5 as (SAT5,(SAT51,SAT52)).
  split. assumption. split. assumption. assumption.
  apply rule_comm; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc in SAT8; try assumption.
  apply rule_assoc in SAT8; try assumption.
  apply sat_star_imps with (Actr (Enum gv) (Ct' - 1))
          (queue z2 size'' **
          Apointsto fqi' (cell_loc ch) (Enum z2) **
          Apointsto fv' (next_loc (next_loc (cell_loc ch)))
            (Enum (Aof v))); try assumption.
  intros. assumption. intros.
  apply rule_pure_star'; try assumption.
  split.
  apply andb_true_iff in SAT6.
  destruct SAT6 as (SAT6,SAT61).
  apply Nat.leb_le in SAT61.
  apply andb_true_iff.
  split. assumption.
  apply Nat.leb_le.
  apply Nat.ltb_lt in SAT2. omega.
  apply rule_comm; try assumption.
  apply sat_star_imps with (queue z2 size'')
          (Apointsto fqi' (cell_loc ch) (Enum z2) **
          Apointsto fv' (next_loc (next_loc (cell_loc ch)))
            (Enum (Aof v))); try assumption.
  intros.
  apply subsa_queue2'; try assumption. intros.
  apply rule_assoc'; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Apointsto fqi' (cell_loc ch) (Enum z2))
           (Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]])))))
             (Enum (Aof v))); try assumption.
  intros. assumption. intros.

  apply rule_points_to_fraction'; try assumption.
  destruct fv'b. assumption.
  destruct fv'b. assumption.
  rewrite <- frac2_plus. assumption.
  }
  intros. assumption.
  intros. assumption.
  intros.
  apply rule_star_pure in SAT0; try assumption.
  intros.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_star_pure in SAT0; try assumption.
  destruct SAT0 as (SAT0,SAT01).
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_prop_star; try assumption.
  split; try assumption.
  intros.
  apply rule_pure_star; try assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.

  apply sat_star_imps with (queue z2 size'')
          (Apointsto fqi' (cell_loc ch) (Enum z2) **
          Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
          Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot' **
          Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1) **
          Abool
            ((Wt' (Aof v) <=? Ot' (Aof v))%nat &&
             (Wt' (Aof v) + Ct' <=? Ot' (Aof v) + S size'')%nat) **
          Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros. assumption. intros.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.


  apply sat_star_imps with ((((((((Apointsto fqi' (cell_loc ch) (Enum z2) **
                 Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O)) **
                Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot') **
               Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1)) **
              Abool
                ((Wt' (Aof v) <=? Ot' (Aof v))%nat &&
                 (Wt' (Aof v) + Ct' <=? Ot' (Aof v) + S size'')%nat)) **
             Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v))) **
            Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m) **
           Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)))
          (Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  intros. assumption.
  }
  {

  intros.
  apply rule_assoc'; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.

  apply sat_star_imps with (Actr (Enum gv) Ct')
         ((Abool
            ((Wt' (Aof v) <=? Ot' (Aof v))%nat &&
             (Wt' (Aof v) + Ct' <=? Ot' (Aof v) + S size'')%nat) **
          Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Atic (Enum gv) **
          Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)) **
         (((queue z2 size'' ** Apointsto fqi' (cell_loc ch) (Enum z2)) **
           Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O)) **
          Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot') **
         Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1)); try assumption.
  intros. assumption.
  intros.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Abool
            ((Wt' (Aof v) <=? Ot' (Aof v))%nat &&
             (Wt' (Aof v) + Ct' <=? Ot' (Aof v) + S size'')%nat))
          ((Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
           Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
           Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
           Atic (Enum gv) **
           Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
           Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
           Abool
             (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
              forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)) **
          (((queue z2 size'' ** Apointsto fqi' (cell_loc ch) (Enum z2)) **
            Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O)) **
           Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot') **
          Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1)); try assumption.
  intros. assumption. intros.
  apply rule_assoc'; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply sat_star_imps with (Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)))
          ((Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
           Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
           Atic (Enum gv) **
           Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
           Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
           Abool
             (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
              forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)) **
          (((queue z2 size'' ** Apointsto fqi' (cell_loc ch) (Enum z2)) **
            Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O)) **
           Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot') **
          Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1)); try assumption.
  intros. assumption. intros.
  apply rule_assoc'; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply sat_star_imps with (Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m)
          ((Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
           Atic (Enum gv) **
           Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
           Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
           Abool
             (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
              forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)) **
          (((queue z2 size'' ** Apointsto fqi' (cell_loc ch) (Enum z2)) **
            Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O)) **
           Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot') **
          Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1)); try assumption.
  intros. assumption. intros.
  apply rule_assoc'; try assumption.
  apply rule_assoc in SAT3; try assumption.
  apply sat_star_imps with (Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil))
          ((Atic (Enum gv) **
           Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
           Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
           Abool
             (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
              forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)) **
          (((queue z2 size'' ** Apointsto fqi' (cell_loc ch) (Enum z2)) **
            Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O)) **
           Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot') **
          Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1)); try assumption.
  intros. assumption. intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc in SAT4; try assumption.
  apply sat_star_imps with (Atic (Enum gv))
          ((Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
           Abool ((z =? ([[m]])) && (z0 =? (Aof v))) **
           Abool
             (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
              forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)) **
          (((queue z2 size'' ** Apointsto fqi' (cell_loc ch) (Enum z2)) **
            Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O)) **
           Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot') **
          Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1)); try assumption.
  intros. assumption. intros.
  apply rule_comm in SAT5; try assumption.
  apply rule_assoc in SAT5; try assumption.
  apply rule_assoc in SAT5; try assumption.
  apply rule_assoc in SAT5; try assumption.
  apply rule_assoc in SAT5; try assumption.
  }
  {
  intros.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_assoc' in SAT; try assumption.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply sat_star_imps with (queue z2 (S size''))
         ((Actr (Enum gv) Ct' **
          Abool
            ((Wt' (Aof v) <=? Ot' (Aof v))%nat &&
             (Wt' (Aof v) + Ct' <=? Ot' (Aof v) + S size'')%nat) **
          Apointsto fv' (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Atic (Enum gv) **
          Aprop ((0 < fm /\ fm < 1) /\ v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof v)) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)) **
         ((Apointsto fqi' (cell_loc ch) (Enum z2) **
           Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O)) **
          Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt' Ot') **
         Aprop (0 < fqi' /\ fqi' < 1 /\ 0 < fv' < 1)); try assumption.

  intros. assumption.
  intros.
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  apply rule_assoc in SAT0; try assumption.
  }
  {
  intros.
  exists (size' - 1)%nat.
  destruct SAT as (fqi',SAT).
  destruct SAT as (fv',SAT).
  apply rule_assoc_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT1).
  replace (S (size' - 1)) with size'.
  exists fqi', fv'.
  assumption.
  apply Nat.ltb_lt in SAT. omega.
  }
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp. left. reflexivity.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp. simpl. auto 10.
  apply neq_symm. eapply nodup_neq. apply NDq. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDq. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDq. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDq. simpl. auto 10.
  apply neq_symm. eapply nodup_neq. apply NDq. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp. simpl. auto 10.
  apply neq_symm. eapply nodup_neq. apply NDq. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDv1. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDv1. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDv1. simpl. auto 10.
  apply neq_symm. eapply nodup_neq.
  apply NDs. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDmv. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDmv. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDmv. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDq. simpl. auto 10.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDq. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDq. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDq. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDq. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDq. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDq. simpl. auto 15.
  apply neq_symm. eapply nodup_neq. apply NDq. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDtmp. simpl. auto 15.
  apply neq_symm. eapply nodup_neq. apply NDq. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDv1. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDv1. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDv1. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDv1. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDv1. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDv1. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDv1. simpl. auto 15.
  apply neq_symm. eapply nodup_neq. apply NDq. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDmv. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDmv. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDmv. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDmv. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDmv. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDmv. simpl. auto 15.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDmv. simpl. auto 15.
  simpl. rewrite neqz. simpl. destruct (tmp =? s) eqn:CO. apply Z.eqb_eq in CO.
  assert (CO1: tmp <> s). apply neq_symm. eapply nodup_neq. apply NDs. simpl. auto 15. contradiction. reflexivity.
  apply neq_symm. eapply nodup_neq. apply NDs. simpl. auto 15.
  simpl. rewrite neqz. simpl. destruct (q =? s) eqn:CO. apply Z.eqb_eq in CO.
  assert (CO1: q <> s). eapply nodup_neq. apply NDq. simpl. auto 15. contradiction. reflexivity.
  apply neq_symm. eapply nodup_neq. apply NDs. simpl. auto 15.
  simpl. rewrite neqz. simpl. destruct (tmp =? s) eqn:CO. apply Z.eqb_eq in CO.
  assert (CO1: tmp <> s). apply neq_symm. eapply nodup_neq. apply NDs. simpl. auto 15. contradiction. reflexivity.
  apply neq_symm. eapply nodup_neq. apply NDs. simpl. auto 15.
  eapply nodup_neq. apply NDmv. simpl. auto 15.
  eapply nodup_neq. apply NDmv. simpl. auto 15.
  {
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Aobs
           (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O))
         (Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt
           Ot **
         (Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
          Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil)
            (Enum qi) **
          Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
            Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil)
            (Enum vi) **
            subsa (subsa (queue qi sizei) (subse chInv ([[ch]])))
            (subse gcInv gv) ** Actr (Enum gv) Ct) **
         Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
         Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
         Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
         Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
         Atic (Enum gv) **
         Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\  v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
         Abool ((z =? ([[m]])) && (z0 =? Aof v)) **
         Abool
           (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
            forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros. assumption. intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) Wt
            Ot)
          ((Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1) **
           Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil)
             (Enum qi) **
           Apointsto fvi
             (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
             Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND,
             nil) (Enum vi) **
           subsa (subsa (queue qi sizei) (subse chInv ([[ch]]))) (subse gcInv gv)
          ** Actr (Enum gv) Ct) **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Atic (Enum gv) **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\  v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof v)) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros. assumption. intros.
  apply rule_assoc'; try assumption.
  apply rule_assoc in SAT1; try assumption.
  apply sat_star_imps with (Aprop (0 < fqi /\ fqi < 1 /\ 0 < fvi < 1))
          ((Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil)
             (Enum qi) **
           Apointsto fvi
             (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
             Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND,
             nil) (Enum vi) **
             subsa (subsa (queue qi sizei) (subse chInv ([[ch]]))) (subse gcInv gv) ** Actr (Enum gv) Ct) **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Atic (Enum gv) **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\  v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof v)) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros. assumption. intros.
  apply rule_comm; try assumption.
  apply rule_assoc in SAT2; try assumption.
  apply sat_star_imps with (Apointsto fqi (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum qi))
          ((Apointsto fvi
             (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
             Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
             (Enum vi) **
           subsa (subsa (queue qi sizei) (subse chInv ([[ch]]))) (subse gcInv gv)
              ** Actr (Enum gv) Ct) **
          Abool ((Wt vi <=? Ot vi)%nat && (Wt vi + Ct <=? Ot vi + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Atic (Enum gv) **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\  v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof v)) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros. assumption. intros.
  apply rule_assoc in SAT3; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.

  assert (EQ1: vi = (Aof v)).
  {
  apply rule_star_pure in SAT2; try assumption.
  destruct SAT2 as (SAT4,SAT2).
  apply rule_assoc' in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_star_pure in SAT2; try assumption.
  destruct SAT2 as (SAT2,SAT5).
  apply rule_comm in SAT2; try assumption.
  apply rule_assoc' in SAT2; try assumption.
  apply rule_star_pure in SAT2; try assumption.
  destruct SAT2 as (SAT2,SAT6).
  apply rule_assoc' in SAT2; try assumption.
  apply rule_star_pure in SAT2; try assumption.
  destruct SAT2 as (SAT2,SAT7).
  apply rule_points_to_value in SAT2; try assumption.
  destruct SAT2 as (SAT8,SAT2). simpl in SAT2. symmetry. assumption.
  }
  rewrite EQ1 in *.

  apply sat_star_imps with (Apointsto fvi
            (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
            Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil)
            (Enum (Aof v)))
          ((subsa (subsa (queue qi sizei) (subse chInv ([[ch]]))) (subse gcInv gv)
              ** Actr (Enum gv) Ct) **
          Abool ((Wt (Aof v) <=? Ot (Aof v))%nat && (Wt (Aof v) + Ct <=? Ot (Aof v) + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Atic (Enum gv) **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\  v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof v)) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros.
  apply next_plus2; try assumption.

  apply pointsto_loc_eval with (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
            Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil); try assumption.
  unfold evall, evalol.
  simpl.
  unfold Aofo, Rofo, Lofo, Xofo, Pofo, Iof, Mof, Aof, Rof, Lof, Xof, Pof, Aofo, Rofo, Lofo, Xofo, Pofo.
  simpl.
  replace 2%Z with (1+1)%Z.
  rewrite Z.add_assoc. reflexivity.
  omega.
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with ((subsa (subsa (queue qi sizei) (subse chInv ([[ch]]))) (subse gcInv gv)
          ** Actr (Enum gv) Ct))
          (Abool ((Wt (Aof v) <=? Ot (Aof v))%nat && (Wt (Aof v) + Ct <=? Ot (Aof v) + sizei)%nat) **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Atic (Enum gv) **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\  v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof v)) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros.
  apply sat_star_imps with (subsa (subsa (queue qi sizei) (subse chInv ([[ch]]))) (subse gcInv gv)
            ) (Actr (Enum gv) Ct); try assumption.
  intros.
  eapply subsa_queue2; try assumption. apply SAT6.
  intros. assumption.
  intros.
  apply rule_assoc' in SAT5; try assumption.
  apply sat_star_imps with ((Abool
             ((Wt (Aof v) <=? Ot (Aof v))%nat &&
              (Wt (Aof v) + Ct <=? Ot (Aof v) + sizei)%nat) **
           Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v))))
          (Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Atic (Enum gv) **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\  v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof v)) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros.
  apply rule_star_pure in SAT6; try assumption.
  destruct SAT6. assumption.
  intros.
  apply rule_assoc' in SAT6; try assumption.
  apply rule_assoc' in SAT6; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (((Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
            Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)) **
           Atic (Enum gv)))
          (Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\  v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof v)) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros. assumption. intros.
  apply rule_star_pure in SAT7; try assumption.
  destruct SAT7 as (SAT7,SAT8).
  apply rule_prop_star'; try assumption.
  split.
  destruct SAT7 as ((SAT7,(s1,s2)),SAT71).
  split. split; assumption. assumption.
  assumption.
  }
  {
  intros.
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (WT,SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (OT,SAT).
  apply sat_star_imps with (a':=(
          (EX y,
           (EX y0,
            (EX y1,
             (EX y2,
              (EX y3,
               (EX y4,
                Aprop (0 < y3 /\ y3 < 1 /\ 0 < y4 < 1) **
                Apointsto y3 (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum y) **
                Apointsto y4
                  (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
                  Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
                  (Enum y2) **
                subsa (subsa (queue y y0) (subse chInv ([[ch]]))) (subse gcInv gv) **
                Actr (Enum gv) y1 ** Abool ((WT y2 <=? OT y2)%nat && (WT y2 + y1 <=? OT y2 + y0)%nat)))))))) **
  (Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
          Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT OT))
         (b':=Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
         Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
         Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
         Atic (Enum gv) **
         Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\  v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
         Abool ((z =? ([[m]])) && (z0 =? Aof v)) **
         Abool
           (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
            forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O))
  in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (y',SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (y0',SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (y1',SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (y2',SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (y3',SAT).
  apply rule_exists_dist in SAT; try assumption.
  destruct SAT as (y4',SAT).
  exists WT, OT, y',y0',y1',y2',y3',y4'.
  apply rule_comm in SAT; try assumption.
  apply rule_assoc in SAT; try assumption.
  apply rule_assoc; try assumption.

  apply sat_star_imps with ((Aobs (Oof (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) :: O) **
          Alocked (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) WT OT))
         ((Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Atic (Enum gv) **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\  v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof v)) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)) **
         Aprop (0 < y3' /\ y3' < 1 /\ 0 < y4' < 1) **
         Apointsto y3' (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum y') **
         Apointsto y4'
           (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
           Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
           (Enum y2') **
         subsa (subsa (queue y' y0') (subse chInv ([[ch]]))) (subse gcInv gv) **
         Actr (Enum gv) y1' ** Abool ((WT y2' <=? OT y2')%nat && (WT y2' + y1' <=? OT y2' + y0')%nat)); try assumption.
  intros. assumption.
  intros.
  apply rule_comm in SAT0; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with ((Aprop (0 < y3' /\ y3' < 1 /\ 0 < y4' < 1) **
           Apointsto y3' (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum y') **
           Apointsto y4'
             (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
             Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
             (Enum y2') **
           subsa (subsa (queue y' y0') (subse chInv ([[ch]]))) (subse gcInv gv) **
           Actr (Enum gv) y1' **
           Abool ((WT y2' <=? OT y2')%nat && (WT y2' + y1' <=? OT y2' + y0')%nat)))
          (Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
          Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Atic (Enum gv) **
          Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\  v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
          Abool ((z =? ([[m]])) && (z0 =? Aof v)) **
          Abool
            (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
             forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply rule_assoc' in SAT1; try assumption.
  apply sat_star_imps with (((((Aprop (0 < y3' /\ y3' < 1 /\ 0 < y4' < 1) **
              Apointsto y3' (Enum ([[ch]]), 0, Enum ([[ch]]), None, false, ND, ND, nil) (Enum y')) **
             Apointsto y4'
               (Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), 0,
               Eplus (Eplus (Enum ([[ch]])) (Enum 1)) (Enum 1), None, false, ND, ND, nil) 
               (Enum y2')) ** subsa (subsa (queue y' y0') (subse chInv ([[ch]]))) (subse gcInv gv)) **
           Actr (Enum gv) y1'))
          (Abool ((WT y2' <=? OT y2')%nat && (WT y2' + y1' <=? OT y2' + y0')%nat)); try assumption.
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc in SAT2; try assumption.
  intros. assumption.
  intros. assumption.
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  intros. assumption.
  }
  assumption. assumption. reflexivity.
  {
  intros.
  apply rule_assoc_pure in SAT; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  destruct SAT as (EQ,SAT).
  apply rule_assoc' in SAT; try assumption.
  apply sat_star_imps with ((Apointsto fm (cell_loc (Eplus ch (Enum 1))) m **
          Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v))))
         (Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
         Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
         Aobs O **
         Atic (Enum gv) **
         Aprop ((0 < fm /\ fm < 1 /\ 0 < fv < 1) /\  v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)) **
         Abool
           (forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) O &&
            forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) O)); try assumption.
  intros.
  apply rule_comm; try assumption.
  apply sat_star_imps with (Apointsto fm (cell_loc (Eplus ch (Enum 1))) m)
          (Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v))); try assumption.
  intros. assumption.
  intros.
  apply rule_pure_star; try assumption.
  split; try assumption.
  apply next_plus2' in SAT1; try assumption.
  intros. assumption.
  }
  assumption.
  {
  intros.
  destruct SAT as (SAT1,SAT2).
  apply rule_comm in SAT1; try assumption.
  unfold channel in SAT1.
  apply rule_assoc in SAT1; try assumption.
  apply rule_exists_dist in SAT1; try assumption.
  destruct SAT1 as (m,SAT1).
  apply rule_exists_dist in SAT1; try assumption.
  destruct SAT1 as (fm,SAT1).
  apply rule_exists_dist in SAT1; try assumption.
  destruct SAT1 as (fv,SAT1).
  exists m, fm, fv.
  apply rule_assoc in SAT1; try assumption.
  apply rule_star_pure in SAT1; try assumption.
  destruct SAT1 as (SAT0,SAT1).
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with ((Apointsto fm (next_loc (cell_loc (Enum ([[ch]])))) m **
           Apointsto fv (next_loc (next_loc (cell_loc (Enum ([[ch]]))))) (Enum (Aof v)) **
           Alock (m, new_channel_level, m, None, false, Linv ([[ch]]) gv, ND, nil) **
           Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)))
          (Atic (Enum gv) ** Aobs O); try assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  intros.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_pure_star; try assumption.
  split; try assumption.
  apply rule_prop_star; try assumption.
  split; try assumption.
  apply rule_comm; try assumption.
  }
Qed.

Theorem rule_dupchannel:
  forall ch gv v,
    channel ch gv v |= channel ch gv v ** channel ch gv v.
Proof.
  unfold channel.
  intros.
  destruct SAT as (m,(fm,(fv,SAT))).
  assert (FR: (0 < fm / (1 + 1) /\ fm / (1 + 1) < 1 /\ 0 < fv / (1 + 1) < 1) /\
    v = (Aof v, Rof v, [[m]], None, false, ND, Mv gv, nil)).
  {
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT0,SAT).
  destruct SAT0 as (SAT0,SAT1).
  simpl. split.
  destruct SAT0 as (s1,(s2,(s3,s4))).
  split.
  apply frac2_pos; try assumption. split.
  apply frac2_bound. split; assumption. split.
  apply frac2_pos; try assumption.
  apply frac2_bound. split; assumption. assumption.
  }
  apply rule_exists_dist'; try assumption.
  exists m.
  apply rule_exists_dist'; try assumption.
  exists (fm/(1+1)).
  apply rule_exists_dist'; try assumption.
  exists (fv/(1+1)).
  apply rule_comm; try assumption.
  apply rule_exists_dist'; try assumption.
  exists m.
  apply rule_exists_dist'; try assumption.
  exists (fm/(1+1)).
  apply rule_exists_dist'; try assumption.
  exists (fv/(1+1)).
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT0,SAT).
  apply rule_assoc'; try assumption.
  apply rule_prop_star'; try assumption. split.
  assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_prop_star'; try assumption. split.
  assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Apointsto (fm / (1 + 1)) (next_loc (cell_loc (Enum ch))) m)
   (Apointsto (fm / (1 + 1)) (next_loc (cell_loc (Enum ch))) m **
   (Apointsto (fv / (1 + 1)) (next_loc (next_loc (cell_loc (Enum ch)))) (Enum (Aof v)) **
    Alock (m, new_channel_level, m, None, false, Linv ch gv, ND, nil) **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)) **
   Apointsto (fv / (1 + 1)) (next_loc (next_loc (cell_loc (Enum ch)))) (Enum (Aof v)) **
   Alock (m, new_channel_level, m, None, false, Linv ch gv, ND, nil) **
   Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)); try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (Apointsto fm (next_loc (cell_loc (Enum ch))) m)
         (Apointsto fv (next_loc (next_loc (cell_loc (Enum ch)))) (Enum (Aof v)) **
         Alock (m, new_channel_level, m, None, false, Linv ch gv, ND, nil) **
         Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)); try assumption.
  intros.
  destruct FR as ((fmp,r1),r2).
  apply rule_points_to_fraction'; try assumption.
  rewrite <- frac2_plus. assumption.
  intros.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Apointsto (fv / (1 + 1)) (next_loc (next_loc (cell_loc (Enum ch)))) (Enum (Aof v)))
   (Apointsto (fv / (1 + 1)) (next_loc (next_loc (cell_loc (Enum ch)))) (Enum (Aof v)) **
    Alock (m, new_channel_level, m, None, false, Linv ch gv, ND, nil) **
    Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
   Alock (m, new_channel_level, m, None, false, Linv ch gv, ND, nil) **
   Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)); try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (Apointsto fv (next_loc (next_loc (cell_loc (Enum ch)))) (Enum (Aof v)))
          (Alock (m, new_channel_level, m, None, false, Linv ch gv, ND, nil) **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)); try assumption.
  intros.
  destruct FR as ((fmp,(r1,(r2,r3))),r4).
  apply rule_points_to_fraction'; try assumption.
  rewrite <- frac2_plus. assumption.
  intros.
  apply sat_star_imps with (Alock (m, new_channel_level, m, None, false, Linv ch gv, ND, nil))
   (Alock (m, new_channel_level, m, None, false, Linv ch gv, ND, nil) **
   Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
   Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)); try assumption.
  apply rule_assoc; try assumption.
  apply sat_star_imps with (Alock (m, new_channel_level, m, None, false, Linv ch gv, ND, nil))
          (Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)); try assumption.
  intros. apply rule_dupl; try assumption.
  intros. apply rule_dupc; try assumption.
  intros. assumption. intros.
  apply rule_assoc' in SAT3; try assumption.
  apply rule_comm in SAT3; try assumption.
  intros. assumption. intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Apointsto (fv / (1 + 1)) (next_loc (next_loc (cell_loc (Enum ch)))) (Enum (Aof v)))
          (Alock (m, new_channel_level, m, None, false, Linv ch gv, ND, nil) **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil) **
          Alock (m, new_channel_level, m, None, false, Linv ch gv, ND, nil) **
          Acond (Enum (Aof v), Rof v, m, None, false, ND, Mv gv, nil)); try assumption.
  intros. assumption. intros.
  apply rule_assoc'; try assumption. intros. assumption.
  intros.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
Qed.

Lemma subs_send:
  forall se e value m v q ndv rearv tmpv tmp
    (EQ1: se (Eplus e (Enum 1)) = (Eplus (se e) (Enum 1)))
    (EQ2: se (Eplus e (Enum 2)) = (Eplus (se e) (Enum 2)))
    (EQ3: se (Evar m) = Evar m)
    (EQ5: se (Evar v) = Evar v)
    (EQ6: se (Evar q) = Evar q)
    (EQ7: se (Eplus (Evar q) (Enum 1)) = Eplus (se (Evar q)) (Enum 1))
    (EQ8: se (Evar rearv) = Evar rearv)
    (EQ9: se (Evar ndv) = Evar ndv)
    (EQ10: se (Eplus (Evar rearv) (Enum 1)) = Eplus (Evar rearv) (Enum 1))
    (EQ11: se (Enum value) = Enum value),
    subs (send e value m v q ndv rearv tmpv tmp) se = 
    send (se e) value m v q ndv rearv tmpv tmp.
Proof.
  unfold send.
  simpl.
  intros.
  rewrite subs_enqueue; try assumption.
  rewrite EQ1, EQ2, EQ3, EQ5, EQ6.
  reflexivity.
Qed.

Lemma subs_receive:
  forall se e q2 m2 v2 s size2 last2 front2 front22 next_front2 rear2
        lastval2 nextnode2 inc2 tmp2 tmp22 tmp222
    (EQ1: se (Eplus e (Enum 1)) = (Eplus (se e) (Enum 1)))
    (EQ2: se (Eplus e (Enum 2)) = (Eplus (se e) (Enum 2)))
    (EQ3: se (Evar m2) = Evar m2)
    (EQ5: se (Evar v2) = Evar v2)
    (EQ6: se (Evar q2) = Evar q2)
    (EQ7: se (Evar front22) = Evar front22)
    (EQ8: se (Evar next_front2) = Evar next_front2)
    (EQ9: se (Eplus (Evar front22) (Enum 1)) = Eplus (Evar front22) (Enum 1))
    (EQ10: se (Evar last2) = Evar last2)
    (EQ11: se (Evar front2) = Evar front2)
    (EQ12: se (Evar size2) = Evar size2)
    (EQ13: se (Eplus (Evar q2) (Enum 1)) = Eplus (se (Evar q2)) (Enum 1))
    (EQ14: se (Evar lastval2) = Evar lastval2)
    (EQ15: se (Evar rear2) = Evar rear2)
    (EQ16: se (Evar nextnode2) = Evar nextnode2)
    (EQ17: se (Eplus (Evar inc2) (Enum 1)) = Eplus (Evar inc2) (Enum 1))
    (EQ18: se (Eplus (Evar lastval2) (Eneg (Evar rear2))) = Eplus (se (Evar lastval2)) (Eneg (se (Evar rear2))))
    (EQ19: se (Eplus (Evar rear2) (Eneg (Evar lastval2))) = Eplus (se (Evar rear2)) (Eneg (se (Evar lastval2))))
    (EQ20: se (Enum 0) = Enum 0)
    (EQ21: se (Enum 1) = Enum 1)
    (EQ22: se (Eplus (Enum 1) (Eneg (Evar s))) = Eplus (Enum 1) (Eneg (Evar s))),
    subs (receive e q2 m2 v2 s size2 last2 front2 front22 next_front2 rear2
        lastval2 nextnode2 inc2 tmp2 tmp22 tmp222) se = 
    receive (se e) q2 m2 v2 s size2 last2 front2 front22 next_front2 rear2
        lastval2 nextnode2 inc2 tmp2 tmp22 tmp222.
Proof.
  unfold receive.
  simpl.
  intros.
  rewrite subs_size_of; try assumption.
  rewrite subs_dequeue; try assumption.
  rewrite EQ1, EQ2, EQ3, EQ5, EQ6, EQ22.
  reflexivity.
Qed.

Opaque new_channel.
Opaque send.
Opaque receive.
Opaque channel.

(** # <font size="5"><b> Channels Example </b></font> # *)

Definition main ch tmp ch1 q1 nd1 m1 v1 tmp1 tmp11 
                q2 m2 v2 s size2 last2 front2 front22 next_front2 rear2 lastval2 
                nextnode2 inc2 tmp2 tmp22 tmp222 m3 v3 q3 nd3 rear3 tmp3 tmp33 := 
  Let ch (new_channel ch1 q1 nd1 m1 v1 tmp1 tmp11)
  (Let tmp (Fork (receive (Evar ch) q2 m2 v2 s size2 last2 front2 front22 next_front2
                                    rear2 lastval2 nextnode2 inc2 tmp2 tmp22 tmp222))
  (send (Evar ch) 12 m3 v3 q3 nd3 rear3 tmp3 tmp33)).

Definition main_level := (1+1)%Qc.

Lemma rule_main ch tmp ch1 q1 nd1 m1 v1 tmp1 tmp11 q2 m2 v2 s size2 last2 front2 front22 next_front2
                rear2 lastval2 nextnode2 inc2 tmp2 tmp22 tmp222 m3 v3 q3 nd3 rear3 tmp3 tmp33
                (NODUP: NoDup (ch :: tmp :: q3 :: tmp3 :: v3 :: m3 :: nd3 :: rear3 :: tmp33 :: ch1 ::
                        q1 :: nd1 :: m1 :: v1 :: tmp1 :: tmp11 ::   q2 :: m2 :: s :: v2 :: tmp2 ::
                        front22 :: next_front2 :: tmp222 :: size2 :: last2 :: front2 :: rear2 ::
                        lastval2 :: nextnode2 :: inc2 :: tmp22 :: nil)): correct
  (Aobs nil)
  (main ch tmp ch1 q1 nd1 m1 v1 tmp1 tmp11 q2 m2 v2 s size2 last2 front2 front22 next_front2 rear2
        lastval2 nextnode2 inc2 tmp2 tmp22 tmp222 m3 v3 q3 nd3 rear3 tmp3 tmp33)
  (fun _ => Aobs nil) channels_invs false.
Proof.
  assert (NDt: NoDup (tmp :: q3 :: tmp3 :: v3 :: m3 :: nd3 :: rear3 :: tmp33 ::   ch1 :: q1 :: nd1 :: m1 :: v1 :: tmp1 :: tmp11 ::   q2 :: m2 :: s :: v2 :: tmp2 :: front22 :: next_front2 :: tmp222 :: size2 :: last2 :: front2 :: rear2 :: lastval2 :: nextnode2 :: inc2 :: tmp22 :: nil)).
  inversion NODUP. assumption.

  apply rule_Let with (fun ch => EX v, (EX gv, (Aobs (Oof v::nil) **
    channel ch gv (evall v) **
    Atic (Enum gv) &*
    (Abool (Qeq_bool (Rof v) main_level))))).
  apply rule_new_channel.
  {
  assert (ND1: NoDup (ch1 :: q1 :: nd1 :: m1 :: v1 :: tmp1 :: tmp11 ::   q2 :: m2 :: s :: v2 :: tmp2 :: front22 :: next_front2 :: tmp222 :: size2 :: last2 :: front2 :: rear2 :: lastval2 :: nextnode2 :: inc2 :: tmp22 :: nil)).
  {
  eapply NoDup_concat'.
  replace (ch :: tmp :: q3 :: tmp3 :: v3 :: m3 :: nd3 :: rear3 :: tmp33 ::   ch1 :: q1 :: nd1 :: m1 :: v1 :: tmp1 :: tmp11 ::   q2 :: m2 :: s :: v2 :: tmp2 :: front22 :: next_front2 :: tmp222 :: size2 :: last2 :: front2 :: rear2 :: lastval2 :: nextnode2 :: inc2 :: tmp22 :: nil)
    with ((ch :: tmp :: q3 :: tmp3 :: v3 :: m3 :: nd3 :: rear3 :: tmp33 :: nil) ++ ch1 :: q1 :: nd1 :: m1 :: v1 :: tmp1 :: tmp11 ::   q2 :: m2 :: s :: v2 :: tmp2 :: front22 :: next_front2 :: tmp222 :: size2 :: last2 :: front2 :: rear2 :: lastval2 :: nextnode2 :: inc2 :: tmp22 :: nil)
    in NODUP.
  apply NODUP. reflexivity.
  }
  eapply NoDup_concat.
  replace (ch1 :: q1 :: nd1 :: m1 :: v1 :: tmp1 :: tmp11 :: q2 :: m2 :: s :: v2 :: tmp2 :: front22 :: next_front2 :: tmp222 :: size2 :: last2 :: front2 :: rear2 :: lastval2 :: nextnode2 :: inc2 :: tmp22 :: nil)
    with ((ch1 :: q1 :: nd1 :: m1 :: v1 :: tmp1 :: tmp11 :: nil) ++ q2 :: m2 :: s :: v2 :: tmp2 :: front22 :: next_front2 :: tmp222 :: size2 :: last2 :: front2 :: rear2 :: lastval2 :: nextnode2 :: inc2 :: tmp22 :: nil)
    in ND1.
  apply ND1. reflexivity.
  }
  simpl. intros.
  apply rule_exists1.
  intros v.
  apply rule_exists1.
  intros gv.
  apply rule_Let with (fun _ => Aobs (Oof v :: nil) **
    (channel z gv (evall v) **
    (Abool (Qeq_bool (Rof v) main_level)))).
  apply rule_conseq1 with ((Aobs ((Oof v :: nil) ++ nil) **
    channel z gv (evall v) **
    Atic (Enum gv) &*
    Abool (Qeq_bool (Rof v) main_level)) **
    (channel z gv (evall v) **
    Abool (Qeq_bool (Rof v) main_level))).
  apply rule_frame.
  apply rule_conseq1 with (Aobs ((Oof v :: nil) ++ nil) ** (channel z gv (evall v) ** Atic (Enum gv) &*
   Abool (Qeq_bool (Rof v) main_level))).
  apply rule_fork.
  rewrite subs_receive.
  simpl.
  rewrite eqz.
  apply rule_conseq1 with (Aobs nil **
    channel z gv (evall v) **
    Atic (Enum gv) &*
    Abool ((forallb (fun x : olocation exp => Qlt_bool (Rof v) (Rofo x)) nil) && 
    (forallb (fun x : olocation exp => Qlt_bool receive_level (Rofo x)) nil))).
  apply rule_conseq2 with (fun _ : Z => Aobs nil ** channel z gv (evall v)).
  apply rule_receive.
  reflexivity. reflexivity. reflexivity.
  eapply NoDup_concat'.
  replace (ch :: tmp :: q3 :: tmp3 :: v3 :: m3 :: nd3 :: rear3 :: tmp33 :: ch1 :: q1 :: nd1 :: m1 :: v1 :: tmp1 :: tmp11 :: q2 :: m2 :: s :: v2 :: tmp2 :: front22 :: next_front2 :: tmp222 :: size2 :: last2 :: front2 :: rear2 :: lastval2 :: nextnode2 :: inc2 :: tmp22 :: nil)
    with ((ch :: tmp :: q3 :: tmp3 :: v3 :: m3 :: nd3 :: rear3 :: tmp33 :: ch1 :: q1 :: nd1 :: m1 :: v1 :: tmp1 :: tmp11 :: nil) ++ q2 :: m2 :: s :: v2 :: tmp2 :: front22 :: next_front2 :: tmp222 :: size2 :: last2 :: front2 :: rear2 :: lastval2 :: nextnode2 :: inc2 :: tmp22 :: nil)
    in NODUP.
  apply NODUP. reflexivity.
  {
  intros.
  apply rule_star_pure in SAT; try assumption. destruct SAT. assumption.
  }
  {
  intros. split.
  apply sat_star_imps with (Aobs nil) ((channel z gv (evall v) ** Atic (Enum gv) &* Abool (Qeq_bool (Rof v) main_level))); try assumption.
  intros. assumption. intros.
  destruct SAT0. assumption.
  apply andb_true_iff. split.
  reflexivity. reflexivity.
  }
  simpl. rewrite eqz. reflexivity.
  simpl. rewrite eqz. reflexivity.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 20.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 20.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 20.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 25.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 25.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 25.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 30.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 30.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 30.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 30.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 30.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 30.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 30.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 35.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 35.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 35.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 35.
  {
  intros.
  apply sat_star_imps with (Aobs ((Oof v :: nil) ++ nil))
   ((channel z gv (evall v) ** Atic (Enum gv) ** Abool (Qeq_bool (Rof v) main_level))); try assumption.
  apply rule_assoc; try assumption.
  apply rule_assoc; try assumption.
  apply rule_pure_star; try assumption.
  destruct SAT. split; try assumption.
  apply rule_assoc'; try assumption.
  intros. assumption. intros.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_star_pure in SAT0; try assumption.
  }
  {
  intros.
  destruct SAT as (SAT,SAT1).
  apply sat_star_imps with ((Aobs ((Oof v :: nil) ++ nil) ** channel z gv (evall v) ** Atic (Enum gv) **
    Abool (Qeq_bool (Rof v) main_level)))(channel z gv (evall v) ** Abool (Qeq_bool (Rof v) main_level)); try assumption.
  apply rule_assoc'; try assumption.
  apply sat_star_imps with (Aobs (Oof v :: nil))(channel z gv (evall v) ** Atic (Enum gv)); try assumption.
  intros. assumption. intros.
  apply rule_assoc; try assumption.
  apply rule_pure_star; try assumption.
  split.
  apply rule_assoc'; try assumption.
  apply rule_comm; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_assoc'; try assumption.
  apply rule_comm in SAT0; try assumption.
  apply sat_star_imps with (Atic (Enum gv)) (channel z gv (evall v)); try assumption.
  intros. assumption. intros.
  apply rule_pure_star'; try assumption. split. assumption.
  apply rule_dupchannel; try assumption. assumption.
  intros.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_assoc' in SAT0; try assumption.
  apply rule_star_pure in SAT0; try assumption.
  destruct SAT0.
  split; try assumption.
  apply rule_assoc; try assumption.
  intros. assumption.
  }
  simpl. intros.
  rewrite subs_send.
  rewrite subs_send.
  simpl.
  rewrite eqz.
  simpl.
  apply rule_conseq1 with (Aobs (Oof v :: nil) ** channel ([[Enum z]]) gv (evall v) &*
    Abool (forallb (fun x : olocation exp => Qlt_bool send_level (Rofo x)) (Oof v :: nil))).
  apply rule_conseq2 with (fun _ => Aobs nil ** channel ([[Enum z]]) gv (evall v)).
  apply rule_send.
  reflexivity. reflexivity. reflexivity.
  inversion NODUP. inversion H2.
  eapply NoDup_concat. apply H6.
  {
  intros.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT. assumption.
  }
  {
  intros.
  split.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT. assumption. simpl.
  apply andb_true_iff. split.
  apply rule_assoc' in SAT; try assumption.
  apply rule_star_pure in SAT; try assumption.
  destruct SAT as (SAT,SAT1).
  apply Qeq_bool_eq in SAT1.
  replace (Rofo (Oof v)) with (Rof v).
  unfold Qlt_bool.
  apply andb_true_iff. split.
  apply Qle_bool_iff.
  rewrite SAT1.
  unfold Qle.
  simpl. omega.
  apply negb_true_iff.
  destruct (Qeq_bool send_level (Rof v)) eqn:CO.
  apply Qeq_bool_iff in CO.
  rewrite SAT1 in CO. inversion CO. reflexivity. reflexivity. reflexivity.
  }
  simpl. rewrite eqz. reflexivity.
  simpl. rewrite eqz. reflexivity.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDt. simpl. auto 35.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDt. simpl. auto 35.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDt. simpl. auto 35.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDt. simpl. auto 35.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDt. simpl. auto 35.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDt. simpl. auto 35.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NDt. simpl. auto 35.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 35.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 35.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 35.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 35.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 35.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 35.
  simpl. rewrite neqz. reflexivity.
  eapply nodup_neq. apply NODUP. simpl. auto 35.
  simpl. reflexivity.
Qed.

Theorem main_is_safe:
  forall ch tmp ch1 q1 nd1 m1 v1 tmp1 tmp11 q2 m2 v2 s size2 last2 front2 front22 next_front2
         rear2 lastval2 nextnode2 inc2 tmp2 tmp22 tmp222 m3 v3 q3 nd3 rear3 tmp3 tmp33
         (NODUP: NoDup (ch :: tmp :: q3 :: tmp3 :: v3 :: m3 :: nd3 :: rear3 :: tmp33 ::
                 ch1 :: q1 :: nd1 :: m1 :: v1 :: tmp1 :: tmp11 ::   q2 :: m2 :: s :: v2 ::
                 tmp2 :: front22 :: next_front2 :: tmp222 :: size2 :: last2 :: front2 ::
                 rear2 :: lastval2 :: nextnode2 :: inc2 :: tmp22 :: nil)),
  forall n id,
    safe n (upd Z.eq_dec (emp (cmd * context)) id 
      (Some ((main ch tmp ch1 q1 nd1 m1 v1 tmp1 tmp11 q2 m2 v2 s size2 last2 front2 front22
                   next_front2 rear2 lastval2 nextnode2 inc2 tmp2 tmp22 tmp222 m3 v3 q3 nd3 rear3 tmp3 tmp33)
      ,done))) (emp Z).
Proof.
  intros.
  eapply verified_program_is_safe.
  repeat split; tauto.
  apply rule_main. assumption.
Qed.
