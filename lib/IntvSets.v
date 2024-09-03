(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Finite sets of integer intervals *)

Require Import Coqlib.
From SMTCoq Require Import SMTCoq.
From SMTCoq Require Import Conversion.

(* Require Import Sniper. *)

From MetaCoq.Template Require Import All.
Unset MetaCoq Strict Unquote Universe Mode.
From Sniper Require Import proof_correctness.
From Sniper Require Import expand.
From Sniper.orchestrator Require Import Sniper.
From Sniper Require Import verit.
Import Decide.


Module ISet.


(** "Raw", non-dependent implementation.  A set of intervals is a
  list of nonempty semi-open intervals [(lo, hi)],
  sorted in increasing order of the low bound,
  and with no overlap nor adjacency between elements.
  In particular, if the list contains [(lo1, hi1)] followed by [(lo2, hi2)],
  we have [lo1 < hi1 < lo2 < hi2]. *)

Module R.

Inductive t : Type := Nil | Cons (lo hi: Z) (tl: t).

Fixpoint In (x: Z) (s: t) :=
  match s with
  | Nil => False
  | Cons l h s' => l <= x < h \/ In x s'
  end.

Fixpoint InBool (x: Z) (s: t) : bool :=
  match s with
  | Nil => false
  | Cons l h s' => ((Z.leb l x) && (Z.ltb x h)) || InBool x s'
  end.


Inductive ok: t -> Prop :=
  | ok_nil: ok Nil
  | ok_cons: forall l h s
      (BOUNDS: l < h)
      (BELOW: forall x, In x s -> h < x)
      (OK: ok s),
      ok (Cons l h s).

Open Scope Z_scope.

Fixpoint ok' (x : t) : bool :=
  match x with
    | Nil => true
    | Cons l1 h1 s =>
        match s with
        | Nil => l1 <? h1
        | Cons l2 _ _ => (l1 <? h1) && (h1 <? l2) && (ok' s)
        end
  end.

Fixpoint mem (x: Z) (s: t) : bool :=
  match s with
  | Nil => false
  | Cons l h s' => if zlt x h then zle l x else mem x s'
  end.

Check CompDec.

Check Nil.

(* #[global] Instance foo : Inhabited t := { default_value := Nil }. *)

(* Fixpoint t_eqb : t -> t -> bool := fun x y => *)
(*   match x, y with *)
(*     | Nil, Nil => true *)

(* #[global] Instance bar : EqbType t := *)
(*   { eqb x y *)
(*   } *)


(* Axiom compdec_t : CompDec t. *)

(* MetaCoq Run (decide ok []). *)
(* Next Obligation. *)
(*   exact compdec_t. *)
(* Defined. *)
  (* assert (Inhabited t) by exact foo. *)


Lemma mem_In:
  forall x s, ok s -> (mem x s = true <-> In x s).
Proof.
  induction 1; simpl.
- intuition congruence.
- destruct (zlt x h).
+ destruct (zle l x); simpl.
  * tauto.
  * split; intros. congruence.
    exfalso. destruct H0. lia. exploit BELOW; eauto. lia.
+ rewrite IHok. intuition auto.
Qed.

Fixpoint contains (L H: Z) (s: t) : bool :=
  match s with
  | Nil => false
  | Cons l h s' => (zle H h && zle l L) || contains L H s'
  end.

Lemma contains_In:
  forall l0 h0, l0 < h0 -> forall s, ok s ->
  (contains l0 h0 s = true <-> (forall x, l0 <= x < h0 -> In x s)).
Proof.
  induction 2; simpl.
- intuition auto with zarith bool. elim (H0 l0); lia.
- destruct (zle h0 h); simpl.
  destruct (zle l l0); simpl.
  intuition auto with zarith.
  rewrite IHok. intuition auto with zarith. destruct (H3 x); auto. exfalso.
  destruct (H3 l0). lia. lia. exploit BELOW; eauto. lia.
  rewrite IHok. intuition. destruct (H3 x); auto. exfalso.
  destruct (H3 h). lia. lia. exploit BELOW; eauto. lia.
Qed.

Fixpoint add (L H: Z) (s: t) {struct s} : t :=
  match s with
  | Nil => Cons L H Nil
  | Cons l h s' =>
      if zlt h L then Cons l h (add L H s')
      else if zlt H l then Cons L H s
      else add (Z.min l L) (Z.max h H) s'
  end.

Lemma In_add:
  forall x s, ok s -> forall l0 h0, (In x (add l0 h0 s) <-> l0 <= x < h0 \/ In x s).
Proof.
  induction 1; simpl; intros.
  tauto.
  destruct (zlt h l0).
  simpl. rewrite IHok. tauto.
  destruct (zlt h0 l).
  simpl. tauto.
  rewrite IHok. intuition idtac.
  assert (l0 <= x < h0 \/ l <= x < h) by extlia. tauto.
  left; extlia.
  left; extlia.
Qed.

Lemma add_ok:
  forall s, ok s -> forall l0 h0, l0 < h0 -> ok (add l0 h0 s).
Proof.
  induction 1; simpl; intros.
  constructor. auto. intros. inv H0. constructor.
  destruct (zlt h l0).
  constructor; auto. intros. rewrite In_add in H1; auto.
  destruct H1. lia. auto.
  destruct (zlt h0 l).
  constructor. auto. simpl; intros. destruct H1. lia. exploit BELOW; eauto. lia.
  constructor. lia. auto. auto.
  apply IHok. extlia.
Qed.

Fixpoint remove (L H: Z) (s: t) {struct s} : t :=
  match s with
  | Nil => Nil
  | Cons l h s' =>
      if zlt h L then Cons l h (remove L H s')
      else if zlt H l then s
      else if zlt l L then
        if zlt H h then Cons l L (Cons H h s') else Cons l L (remove L H s')
      else
        if zlt H h then Cons H h s' else remove L H s'
  end.

Lemma In_remove:
  forall x l0 h0 s, ok s ->
  (In x (remove l0 h0 s) <-> ~(l0 <= x < h0) /\ In x s).
Proof.
  induction 1; simpl.
  tauto.
  destruct (zlt h l0).
  simpl. rewrite IHok. intuition lia.
  destruct (zlt h0 l).
  simpl. intuition auto with zarith. exploit BELOW; eauto. lia.
  destruct (zlt l l0).
  destruct (zlt h0 h); simpl. clear IHok. split.
  intros [A | [A | A]].
  split. lia. left; lia.
  split. lia. left; lia.
  split. exploit BELOW; eauto. lia. auto.
  intros [A [B | B]].
  destruct (zlt x l0). left; lia. right; left; lia.
  auto.
  intuition lia.
  destruct (zlt h0 h); simpl.
  intuition auto with zarith. exploit BELOW; eauto. lia.
  rewrite IHok. intuition. extlia.
Qed.

Lemma remove_ok:
  forall l0 h0, l0 < h0 -> forall s, ok s -> ok (remove l0 h0 s).
Proof.
  induction 2; simpl.
  constructor.
  destruct (zlt h l0).
  constructor; auto. intros; apply BELOW. rewrite In_remove in H1; tauto.
  destruct (zlt h0 l).
  constructor; auto.
  destruct (zlt l l0).
  destruct (zlt h0 h).
  constructor. lia. intros. inv H1. lia. exploit BELOW; eauto. lia.
  constructor. lia. auto. auto.
  constructor; auto. intros. rewrite In_remove in H1 by auto. destruct H1. exploit BELOW; eauto. lia.
  destruct (zlt h0 h).
  constructor; auto.
  auto.
Qed.

Fixpoint inter (s1 s2: t) {struct s1} : t :=
  let fix intr (s2: t) : t :=
    match s1, s2 with
    | Nil, _ => Nil
    | _, Nil => Nil
    | Cons l1 h1 s1', Cons l2 h2 s2' =>
        if zle h1 l2 then inter s1' s2
        else if zle h2 l1 then intr s2'
        else if zle l1 l2 then
          if zle h2 h1 then Cons l2 h2 (intr s2') else Cons l2 h1 (inter s1' s2)
        else
          if zle h1 h2 then Cons l1 h1 (inter s1' s2) else Cons l1 h2 (intr s2')
    end
  in intr s2.

Lemma In_inter:
  forall x s1, ok s1 -> forall s2, ok s2 ->
  (In x (inter s1 s2) <-> In x s1 /\ In x s2).
Proof.
  induction 1.
  simpl. induction 1; simpl. tauto. tauto.
  assert (ok (Cons l h s)) by (constructor; auto).
  induction 1; simpl.
  tauto.
  assert (ok (Cons l0 h0 s0)) by (constructor; auto).
  destruct (zle h l0).
  rewrite IHok; auto. simpl. intuition auto with zarith. extlia.
  exploit BELOW0; eauto. intros. extlia.
  destruct (zle h0 l).
  simpl in IHok0; rewrite IHok0. intuition auto with zarith. extlia.
  exploit BELOW; eauto. intros; extlia.
  destruct (zle l l0).
  destruct (zle h0 h).
  simpl. simpl in IHok0; rewrite IHok0. intuition auto with zarith.
  simpl. rewrite IHok; auto. simpl. intuition auto with zarith.  exploit BELOW0; eauto. intros; extlia.
  destruct (zle h h0).
  simpl. rewrite IHok; auto. simpl. intuition auto with zarith.
  simpl. simpl in IHok0; rewrite IHok0. intuition auto with zarith.
  exploit BELOW; eauto. intros; extlia.
Qed.

Lemma inter_ok:
  forall s1, ok s1 -> forall s2, ok s2 -> ok (inter s1 s2).
Proof.
  induction 1.
  intros; simpl. destruct s2; constructor.
  assert (ok (Cons l h s)). constructor; auto.
  induction 1; simpl.
  constructor.
  assert (ok (Cons l0 h0 s0)). constructor; auto.
  destruct (zle h l0).
  auto.
  destruct (zle h0 l).
  auto.
  destruct (zle l l0).
  destruct (zle h0 h).
  constructor; auto. intros.
  assert (In x (inter (Cons l h s) s0)) by exact H3.
  rewrite In_inter in H4; auto. apply BELOW0. tauto.
  constructor. lia. intros. rewrite In_inter in H3; auto. apply BELOW. tauto.
  auto.
  destruct (zle h h0).
  constructor. lia. intros. rewrite In_inter in H3; auto. apply BELOW. tauto.
  auto.
  constructor. lia. intros.
  assert (In x (inter (Cons l h s) s0)) by exact H3.
  rewrite In_inter in H4; auto. apply BELOW0. tauto.
  auto.
Qed.

Fixpoint union (s1 s2: t) : t :=
  match s1, s2 with
  | Nil, _ => s2
  | _, Nil => s1
  | Cons l1 h1 s1', Cons l2 h2 s2' => add l1 h1 (add l2 h2 (union s1' s2'))
  end.

Lemma In_ok_union:
  forall s1, ok s1 -> forall s2, ok s2 ->
  ok (union s1 s2) /\ (forall x, In x s1 \/ In x s2 <-> In x (union s1 s2)).
Proof.
  induction 1; destruct 1; simpl.
  split. constructor. tauto.
  split. constructor; auto. tauto.
  split. constructor; auto. tauto.
  destruct (IHok s0) as [A B]; auto.
  split. apply add_ok; auto. apply add_ok; auto.
  intros. rewrite In_add. rewrite In_add. rewrite <- B. tauto. auto. apply add_ok; auto.
Qed.

Fixpoint beq (s1 s2: t) : bool :=
  match s1, s2 with
  | Nil, Nil => true
  | Cons l1 h1 t1, Cons l2 h2 t2 => zeq l1 l2 && zeq h1 h2 && beq t1 t2
  | _, _ => false
  end.

Lemma beq_spec:
  forall s1, ok s1 -> forall s2, ok s2 ->
  (beq s1 s2 = true <-> (forall x, In x s1 <-> In x s2)).
Proof.
  induction 1; destruct 1; simpl.
- tauto.
- split; intros. discriminate. exfalso. apply (H0 l). left; lia.
- split; intros. discriminate. exfalso. apply (H0 l). left; lia.
- split; intros.
+ InvBooleans. subst. rewrite IHok in H3 by auto. rewrite H3. tauto.
+ destruct (zeq l l0). destruct (zeq h h0). simpl. subst.
  apply IHok. auto. intros; split; intros.
  destruct (proj1 (H1 x)); auto. exfalso. exploit BELOW; eauto. lia.
  destruct (proj2 (H1 x)); auto. exfalso. exploit BELOW0; eauto. lia.
  exfalso. subst l0. destruct (zlt h h0).
  destruct (proj2 (H1 h)). left; lia. lia. exploit BELOW; eauto. lia.
  destruct (proj1 (H1 h0)). left; lia. lia. exploit BELOW0; eauto. lia.
  exfalso. destruct (zlt l l0).
  destruct (proj1 (H1 l)). left; lia. lia. exploit BELOW0; eauto. lia.
  destruct (proj2 (H1 l0)). left; lia. lia. exploit BELOW; eauto. lia.
Qed.

End R.

(** Exported interface, wrapping the [ok] invariant in a dependent type. *)

Definition t := { r: R.t | R.ok r }.

Program Definition In (x: Z) (s: t) := R.In x s.
Program Definition InBool (x: Z) (s: t) := R.InBool x s.

Check In.
Check R.In.


Program Definition empty : t := R.Nil.
Next Obligation. constructor. Qed.

Theorem In_empty: forall x, ~(In x empty).
Proof.
  unfold In; intros; simpl. tauto.
Qed.


Check Z.ltb.



Program Definition interval (l h: Z) : t :=
  if Z.ltb l h then R.Cons l h R.Nil else R.Nil.
Next Obligation.
  admit.
  (* apply R.ok_cons. *)
  (* - exact l0. *)
  (* - simpl. tauto. *)
  (* - apply R.ok_nil. *)
Admitted.
Next Obligation.
  constructor.
Qed.


Section foo.

  Variable t : Type.
  Variable x l h : Z.
  Variable exist : forall (e : R.t), R.ok e -> t.
  Variable interval : Z -> Z -> t.
  Variable H3 : forall (x x0 x1 x2 : Z) (x3 x4 : R.t), R.Cons x x1 x3 = R.Cons x0 x2 x4 -> x = x0 /\ x1 = x2 /\ x3 = x4.
  Variable H4 : forall (x x0 : Z) (x1 : R.t), R.Nil = R.Cons x x0 x1 -> False.
  Variable p0 : CompDec R.t.
  Variable H8 : forall H7 H9 : Z, (H7 <? H9)%Z = true -> interval H7 H9 = exist (R.Cons H7 H9 R.Nil) (interval_obligation_1 H7 H9).
  Variable H6 : forall H7 H9 : Z, (H7 <? H9)%Z = false -> interval H7 H9 = exist R.Nil interval_obligation_2.
  Variable p1 : CompDec t.
  (* Variable H5 : interval_obligation_2 = interval_obligation_2. *)
  Variable InBool : Z -> t -> bool.
  Variable proj1_sig : t -> R.t.
  Variable H7 : forall (x : Z) (s : t), InBool x s = R.InBool x (proj1_sig s).
  (* Variable H : forall x x0 : Z, interval_obligation_1 x x0 = interval_obligation_1 x x0. *)
  Variable H12 : forall H11 : Z, R.InBool H11 R.Nil = false.
  Variable H10 : forall (H11 lo hi : Z) (tl : R.t), R.InBool H11 (R.Cons lo hi tl) = (lo <=? H11)%Z && (H11 <? hi)%Z || R.InBool H11 tl.
  Variable def_proj1_sig : forall (e1 : R.t) (e2 : R.ok e1), proj1_sig (exist e1 e2) = e1.
Goal InBool x (interval l h) <-> l <= x < h.
  Abort.
End foo.


Section foo2.


  Variable x l h : Z.
  Variable interval : Z -> Z -> R.t.
  Variable H3 : forall (x x0 x1 x2 : Z) (x3 x4 : R.t), R.Cons x x1 x3 = R.Cons x0 x2 x4 -> x = x0 /\ x1 = x2 /\ x3 = x4.
  Variable H4 : forall (x x0 : Z) (x1 : R.t), R.Nil = R.Cons x x0 x1 -> False.
  Variable p0 : CompDec R.t.
  Variable H8 : forall H7 H9 : Z, (H7 <? H9)%Z = true -> interval H7 H9 = (R.Cons H7 H9 R.Nil).
  Variable H13 : forall l h : Z , R.ok (interval l h).
  Variable H6 : forall H7 H9 : Z, (H7 <? H9)%Z = false -> interval H7 H9 = R.Nil.
  Variable H5 : interval_obligation_2 = interval_obligation_2.
  (* Variable H7 : forall (x : Z) (s : R.t), InBool x s = R.InBool x s. *)
  Variable H : forall x x0 : Z, interval_obligation_1 x x0 = interval_obligation_1 x x0.
  Variable H12 : forall H11 : Z, R.In H11 R.Nil = False.
  Variable H10 : forall (H11 lo hi : Z) (tl : R.t), R.In H11 (R.Cons lo hi tl) = (lo <= H11 < hi \/ R.In H11 tl).



Goal R.In x (interval l h) <-> l <= x < h.
  (* generalize dependent R.In. clear H12 H10. clear H H5. verit_orch. *)

  Abort.

End foo2.

Axiom ok_ok' : forall t , R.ok t <-> R.ok' t = true.

Trakt Add Relation 1 R.ok R.ok' ok_ok'.

Theorem cong {A B : Type} {x y : A} (f : A -> B) (H : x = y) : f x = f y.
Proof.
  rewrite H.
  reflexivity.
Qed.

Theorem orb_false : forall x : bool , (x || false) = x.
  Proof. intro x. destruct x eqn:H. reflexivity. reflexivity. Qed.

Theorem In_interval: forall x l h, InBool x (interval l h) <-> l <= x < h.
Proof.
  intros.
  split.
  intro H.

  (*
    OVERVIEW OF THE FIRST TRANSFORMATION (before rest of scope)
      1. Identify in the context function that returns refinement type (interval)
      2. Add new symbol whose definition is the `proj1_sig` composed with function (interval')
      3. Add hypothesis stating that new symbol equals old symbol for all parameters (H_def)
      4. Add hypothesis stating that new symbol satisfies predicate of refinement type (H_prop)
      5. For the user: trakt needs to know how to transform predicate into a boolean fixpoint
   *)

  pose (interval' := fun l h => proj1_sig (interval l h)).
  assert (H_def : forall l h , interval' l h = proj1_sig (interval l h)) by reflexivity.
  clearbody interval'.
  assert (H_prop : forall l h , R.ok (interval' l h)).
  { intros. rewrite H_def. destruct (interval l0 h0). exact o. }
  revert H_prop.
  trakt bool.
  intro H1.
  change (forall x y : Z , R.ok' (interval' x y) = true) in H1.
  change (forall x y : Z , interval' x y = proj1_sig (interval x y)) in H_def.
  scope.
  Focus 3.

  (*
    OVERVIEW OF THE SECOND TRANSFORMATION (after rest of scope?)
      1. Identify in the context equalities of the form `s = exist x p` <- coming from definitions of refinement types
      2. Define and prove new equality `proj1_sig s = x`
      3?. Try to find something to replace by `proj1_sig s` (bug in SMTCoq)
      4. Replace old equality with new one
   *)


  (* NOTE: we could potentially leave these theorems with `proj1_sig` instead of
     `interval'`, but this is causing a bug in SMTCoq that I don't understand
     For now I am removing all uses of proj1_sig. With this we are able to prove
     the theorem with verit. However, implementing an independent transformation
     that generates the following hypothesis requires searching for something that
     is equal to `proj1_sig (interval x y)` in the context
   *)

  assert (H10' : forall x y : Z , (x <? y)%Z = true -> (interval' x y) = (R.Cons x y R.Nil)).
  { intros. rewrite H_def. exact (cong (@proj1_sig R.t R.ok) (H10 x0 y H6)). }
  clear H10.
  rename H10' into H10.

  assert (H8' : forall x y : Z , (x <? y)%Z = false -> interval' x y = R.Nil).
  { intros. rewrite H_def. exact (cong (@proj1_sig R.t R.ok) (H8 x0 y H6)). }
  clear H8.
  rename H8' into H8.

  (* These should be automatically filtered by scope *)
  clear H0 H9.
  clear H2.

  (* What about this? *)
  (* This shouldn't be necessary - the SMT solver could infer the new hypothesis by the context *)
  (* However this is raising a bug in SMTCoq, seems related to the existence of `proj1_sig` in the context *)
  (* I think this is what Chantal said she will fix? the reification of the type of this symbol? *)
  (* If this is the case then we don't need to consider the following lines in the transformation *)
  rewrite H11 in H.
  rewrite <- H_def in H.
  clear H_def H11.


  verit.

  clear H2 H10 H3.
  clear H6.

  rewrite H12 in H.
  rewrite <- H0 in H.
  clear H0 H12.
  verit.
  admit.
  admit.
  admit.
Admitted.


Check proj2_sig.
Print True.
Check I.

Program Definition add (l h: Z) (s: t) : t :=
  if zlt l h then R.add l h s else s.
Next Obligation.
  apply R.add_ok.
  assert (blah :  True). exact I.
  assert (R.ok (proj1_sig s)). exact (proj2_sig s).

  apply proj2_sig. auto.
Qed.

Theorem In_add: forall x l h s, In x (add l h s) <-> l <= x < h \/ In x s.
Proof.
  unfold add.
  unfold In. intros.
  destruct (zlt l h).
  simpl. apply R.In_add. apply proj2_sig.
  intuition. extlia.
Qed.

Program Definition remove (l h: Z) (s: t) : t :=
  if zlt l h then R.remove l h s else s.
Next Obligation.
  apply R.remove_ok. auto. apply proj2_sig.
Qed.

Theorem In_remove: forall x l h s, In x (remove l h s) <-> ~(l <= x < h) /\ In x s.
Proof.
  unfold remove.
  unfold In. intros.
  destruct (zlt l h).
  simpl. apply R.In_remove. apply proj2_sig.
  intuition auto with zarith.
Qed.

Program Definition inter (s1 s2: t) : t := R.inter s1 s2.
Next Obligation. apply R.inter_ok; apply proj2_sig. Qed.

Theorem In_inter: forall x s1 s2, In x (inter s1 s2) <-> In x s1 /\ In x s2.
Proof.
  unfold inter, In; intros; simpl. apply R.In_inter; apply proj2_sig.
Qed.

Program Definition union (s1 s2: t) : t := R.union s1 s2.
Next Obligation.
  destruct (R.In_ok_union _ (proj2_sig s1) _ (proj2_sig s2)). auto.
Qed.

Theorem In_union: forall x s1 s2, In x (union s1 s2) <-> In x s1 \/ In x s2.
Proof.
  unfold union, In; intros; simpl.
  destruct (R.In_ok_union _ (proj2_sig s1) _ (proj2_sig s2)).
  generalize (H0 x); tauto.
Qed.

Program Definition mem (x: Z) (s: t) := R.mem x s.

Theorem mem_spec: forall x s, mem x s = true <-> In x s.
Proof.
  unfold mem, In; intros. apply R.mem_In. apply proj2_sig.
Qed.

Program Definition contains (l h: Z) (s: t) :=
  if zlt l h then R.contains l h s else true.

Theorem contains_spec:
  forall l h s, contains l h s = true <-> (forall x, l <= x < h -> In x s).
Proof.
  unfold contains, In; intros. destruct (zlt l h).
  apply R.contains_In. auto. apply proj2_sig.
  split; intros. extlia. auto.
Qed.

Program Definition beq (s1 s2: t) : bool := R.beq s1 s2.

Theorem beq_spec:
  forall s1 s2, beq s1 s2 = true <-> (forall x, In x s1 <-> In x s2).
Proof.
  unfold mem, In; intros. apply R.beq_spec; apply proj2_sig.
Qed.

End ISet.




