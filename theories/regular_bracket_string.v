Require Import Lia.
Require Import stdpp.list.
Require Import Coq.Program.Equality.
From Equations Require Import Equations.

Inductive bracket_t :=
  | open
  | close.

Inductive balanced : list bracket_t -> Prop :=
  | empty: balanced []
  | wrap {x : list bracket_t} : balanced x -> balanced ([open] ++ x ++ [close])
  | join {x y : list bracket_t} : balanced x -> balanced y -> balanced (x ++ y).

#[export] Instance bracket_t_eq_dec : EqDecision bracket_t.
Proof. solve_decision. Defined.

Inductive is_open : bracket_t -> Prop :=
| intro : is_open open.

#[export] Instance is_open_dec (a : bracket_t) : Decision (is_open a).
Proof.
  destruct a.
  - apply left.
    exact intro.
  - apply right.
    intro h.
    dependent induction h.
Defined.

Lemma single_close_not_balanced : ~ balanced [close].
Proof.
  intro h.
  dependent induction h.
  pose proof (app_singleton x0 y close).
  destruct H.
  destruct H0. auto.
  assert (h3 : x0 ++ y = x0 ++ y).
  { auto. }
  pose proof (H h3).
  destruct H0.
  - easy.
  - easy.
Qed.

Lemma single_open_not_balanced : ~ balanced [open].
Proof.
  intro h.
  dependent induction h.
  - pose proof (app_nil x0 [close]).
    destruct H.
    pose proof (H x).
    destruct H1.
    easy.
  - pose proof (app_singleton x0 y open).
    destruct H.
    pose proof (H x).
    destruct H1.
    + destruct H1. easy.
    + destruct H1. easy.
Qed.

Lemma double_close_not_balanced : ~ balanced [close; close].
Proof.
  intro h.
  dependent induction h.
  - destruct x0.
    + simpl in x. exact (IHh2 x).
    + simpl in x. injection x. intros h3 h4.
      pose proof (app_singleton x0 y close).
      destruct H.
      pose proof (H h3).
      destruct H1.
      * destruct H1. rewrite H1 in h1. rewrite h4 in h1.
        exact (single_close_not_balanced h1).
      * destruct H1. rewrite H1 in IHh1. rewrite h4 in IHh1. easy.
Qed.

Lemma double_open_not_balanced : ~ balanced [open; open].
Proof.
  intro h.
  dependent induction h.
  - pose proof (app_singleton x0 [close] open).
    destruct H.
    pose proof (H x).
    destruct H1.
    + easy.
    + easy.
  - destruct x0.
    + simpl in x.
      easy.
    + simpl in x.
      assert (H : b = open).
      { dependent induction x. easy. }
      assert (H1 : x0 ++ y = [open]).
      { dependent induction x. easy. }
      pose proof (app_singleton x0 y open).
      destruct H0.
      pose proof (H0 H1).
      destruct H3.
      * destruct H3.
        rewrite H4 in h2.
        exact (single_open_not_balanced h2).
      * destruct H3.
        rewrite H in IHh1.
        rewrite H3 in IHh1.
        easy.
Qed.

Compute (count_occ bracket_t_eq_dec [open; open; close; close; close] close).

Definition count_open (l : list bracket_t) := count_occ bracket_t_eq_dec l open.
Definition count_close (l : list bracket_t) := count_occ bracket_t_eq_dec l close.

Compute (count_open [open; open; close]).
Compute (count_close [open; close; open]).

Definition open_not_exhausted (l : list bracket_t) := forall l', prefix l' l -> count_close l' <= count_open l'.

Definition alternate_balanced_condition (l : list bracket_t) :=
  count_open l = count_close l /\ forall l', prefix l' l -> count_close l' <= count_open l'.

Lemma count_open_sum (l1 l2 : list bracket_t) : count_open (l1 ++ l2) = count_open l1 + count_open l2.
Proof.
  unfold count_open.
  apply count_occ_app.
Qed.

Lemma count_close_sum (l1 l2 : list bracket_t) : count_close (l1 ++ l2) = count_close l1 + count_close l2.
Proof.
  unfold count_close.
  apply count_occ_app.
Qed.

Lemma count_open_single_open : count_open [open] = 1.
Proof. easy. Qed.

Lemma count_open_single_close : count_open [close] = 0.
Proof. easy. Qed.

Lemma count_close_single_open : count_close [open] = 0.
Proof. easy. Qed.

Lemma count_close_single_close : count_close [close] = 1.
Proof. easy. Qed.

Lemma count_open_nil : count_open [] = 0.
Proof. easy. Qed.

Lemma count_close_nil : count_close [] = 0.
Proof. easy. Qed.

Lemma count_open_cons_open (l : list bracket_t) : count_open (open::l) = 1 + count_open l.
Proof. easy. Qed.

Lemma count_open_cons_close (l : list bracket_t) : count_open (close::l) = count_open l.
Proof. easy. Qed.

Lemma count_close_cons_open (l : list bracket_t) : count_close (open::l) = count_close l.
Proof. easy. Qed.

Lemma count_close_cons_close (l : list bracket_t) : count_close (close::l) = 1 + count_close l.
Proof. easy. Qed.

Equations alternate_balanced_condition_bool_aux (l : list bracket_t) (open_count close_count : nat) : bool :=
| (open::tl), open_count, close_count :=
    if bool_decide (open_count < close_count) then
      false
    else
      alternate_balanced_condition_bool_aux tl (open_count + 1) close_count
| (close::tl), open_count, close_count :=
    if bool_decide (open_count < close_count) then
      false
    else
      alternate_balanced_condition_bool_aux tl open_count (close_count + 1)
| [], open_count, close_count := bool_decide (open_count = close_count).

Lemma alternate_balanced_condition_bool_aux_nil (count : nat) :
  alternate_balanced_condition_bool_aux [] count count = true.
Proof.
  simp alternate_balanced_condition_bool_aux.
  rewrite bool_decide_eq_true.
  easy.
Qed.

Definition alternate_balanced_condition_bool (l : list bracket_t) :=
  alternate_balanced_condition_bool_aux l 0 0.

Lemma meaning_of_alternate_balanced_condition_bool_aux (l : list bracket_t) (open_count close_count : nat) : (alternate_balanced_condition_bool_aux l open_count close_count = true) -> open_count + count_open l >= close_count + count_close l.
Proof.
  revert open_count close_count.
  induction l.
  - intros open_count close_count.
    simp alternate_balanced_condition_bool_aux.
    intro h.
    rewrite bool_decide_eq_true in h.
    rewrite count_open_nil. rewrite count_close_nil.
    lia.
  - destruct a.
    + intros open_count close_count.
      simp alternate_balanced_condition_bool_aux.
      intro h.
      case_bool_decide.
      * easy.
      * rewrite count_open_cons_open. rewrite count_close_cons_open.
        pose proof (IHl (open_count + 1) close_count h).
        lia.
    + intros open_count close_count.
      simp alternate_balanced_condition_bool_aux.
      intro h.
      case_bool_decide.
      * easy.
      * rewrite count_open_cons_close. rewrite count_close_cons_close.
        pose proof (IHl open_count (close_count + 1) h).
        lia.
Qed.

Lemma alternate_balanced_condition_bool_implies_alternate_balanced_condition (l : list bracket_t) :
  (alternate_balanced_condition_bool l = true) -> open_not_exhausted l.
Proof.
  intro h.
