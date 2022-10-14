Require Import Lia.
Require Import stdpp.list.
Require Import Coq.Program.Equality.
From Equations Require Import Equations.

Inductive bracket_t :=
  | open
  | close.

Inductive balanced : list bracket_t -> Prop :=
  | empty : balanced []
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

Lemma second_meaning_of_alternate_balanced_condition_bool_aux (l : list bracket_t) (open_count close_count : nat) : (alternate_balanced_condition_bool_aux l open_count close_count = true) -> open_count >= close_count.
Proof.
  revert open_count close_count.
  induction l.
  - intros open_count close_count.
    simp alternate_balanced_condition_bool_aux.
    rewrite bool_decide_eq_true.
    lia.
  - intros open_count close_count.
    destruct a.
    + simp alternate_balanced_condition_bool_aux.
      case_bool_decide.
      * easy.
      * intro h.
        pose proof (IHl _ _ h).
        lia.
    + simp alternate_balanced_condition_bool_aux.
      case_bool_decide.
      * easy.
      * intro h.
        pose proof (IHl _ _ h).
        lia.
Qed.

Lemma alternate_balanced_condition_bool_aux_app (l1 l2 : list bracket_t) (initial_open_count initial_close_count : nat) : (alternate_balanced_condition_bool_aux (l1 ++ l2) initial_open_count initial_close_count = true) -> initial_open_count >= initial_close_count /\ initial_open_count + count_open l1 >= initial_close_count + count_close l1 /\ (alternate_balanced_condition_bool_aux l2 (initial_open_count + count_open l1) (initial_close_count + count_close l1) = true).
Proof.
  revert l2 initial_open_count initial_close_count.
  induction l1.
  - intros l2 initial_open_count initial_close_count h.
    rewrite -> count_open_nil, -> count_close_nil.
    split.
    + simpl in h. exact (second_meaning_of_alternate_balanced_condition_bool_aux _ _ _ h).
    + split.
      * rewrite -> Nat.add_0_r, -> Nat.add_0_r. simpl in h. exact (second_meaning_of_alternate_balanced_condition_bool_aux _ _ _ h).
      * simpl in h.
        rewrite -> Nat.add_0_r, -> Nat.add_0_r.
        assumption.
  - intros l2 initial_open_count initial_close_count h.
    simpl in h. split.
    + pose proof (second_meaning_of_alternate_balanced_condition_bool_aux _ _ _ h).
      assumption.
    + split.
      * destruct a.
        { rewrite -> count_open_cons_open, -> count_close_cons_open.
          simp alternate_balanced_condition_bool_aux in h.
          case_bool_decide.
          - easy.
          - pose proof (meaning_of_alternate_balanced_condition_bool_aux _ _ _ h).
            pose proof (IHl1 _ _ _ h). lia. }
        { rewrite -> count_open_cons_close, -> count_close_cons_close.
          simp alternate_balanced_condition_bool_aux in h.
          case_bool_decide.
          - easy.
          - pose proof (meaning_of_alternate_balanced_condition_bool_aux _ _ _ h).
            pose proof (IHl1 _ _ _ h). lia. }
      * destruct a.
        { rewrite -> count_open_cons_open, -> count_close_cons_open.
          simp alternate_balanced_condition_bool_aux in h.
          case_bool_decide.
          - easy.
          - pose proof (IHl1 _ _ _ h). rewrite Nat.add_assoc.
            easy. }
        { rewrite -> count_open_cons_close, -> count_close_cons_close.
          simp alternate_balanced_condition_bool_aux in h.
          case_bool_decide.
          - easy.
          - pose proof (IHl1 _ _ _ h). rewrite Nat.add_assoc.
            easy. }
Qed.

Definition alternate_balanced_condition_aux (l : list bracket_t) (open_count close_count : nat) := open_count + count_open l = close_count + count_close l /\ forall l', prefix l' l -> close_count + count_close l' <= open_count + count_open l'.

Lemma always_fail_if_close_count_exceeds_open_count (l : list bracket_t) (open_count close_count : nat) (h : open_count < close_count) : ~ alternate_balanced_condition_aux l open_count close_count.
Proof.
  unfold alternate_balanced_condition_aux.
  intro h1.
  destruct h1 as [_ h1].
  epose proof h1 [] ltac:(apply prefix_nil).
  rewrite -> count_close_nil, -> count_open_nil in H.
  lia.
Qed.

Lemma base_case (open_count close_count : nat) : open_count = close_count <-> alternate_balanced_condition_aux [] open_count close_count.
Proof.
  split.
  - intro h. unfold alternate_balanced_condition_aux.
    rewrite -> count_open_nil, -> count_close_nil.
    split.
    + lia.
    + intros l' h'. pose proof prefix_nil_inv _ h'.
      rewrite -> H, -> count_close_nil, -> count_open_nil. lia.
  - intro h. unfold alternate_balanced_condition_aux in h.
    rewrite -> count_open_nil, -> count_close_nil in h. lia.
Qed.

Lemma cons_open_recurse (l : list bracket_t) (open_count close_count : nat) (h : close_count <= open_count) : alternate_balanced_condition_aux (open::l) open_count close_count <-> alternate_balanced_condition_aux l (open_count + 1) close_count.
Proof.
  split.
  - intro h'. unfold alternate_balanced_condition_aux. unfold alternate_balanced_condition_aux in h'. rewrite -> count_open_cons_open, -> count_close_cons_open in h'. destruct h' as [h1 h2]. split.
    * lia.
    * intros l' h3.
      epose proof h2 (open::l') ltac:(shelve).
      rewrite -> count_close_cons_open, -> count_open_cons_open in H. lia.
  - unfold alternate_balanced_condition_aux. intro h'. destruct h' as [h1 h2]. rewrite -> count_open_cons_open, -> count_close_cons_open. split.
    * lia.
    * intros l' h'. destruct l'.
      { rewrite -> count_open_nil, -> count_close_nil. lia. }
      { pose proof prefix_cons_inv_1 _ _ _ _ h'. rewrite H. rewrite -> count_open_cons_open, -> count_close_cons_open. pose proof prefix_cons_inv_2 _ _ _ _ h'.  pose proof (h2 _ H0). lia. }
  Unshelve.
  apply prefix_cons. auto.
Qed.

Lemma cons_close_recurse (l : list bracket_t) (open_count close_count : nat) (h : close_count <= open_count) : alternate_balanced_condition_aux (close::l) open_count close_count <-> alternate_balanced_condition_aux l open_count (close_count + 1).
Proof.
  unfold alternate_balanced_condition_aux.
  split.
  - intro h'. destruct h' as [h1 h2]. rewrite -> count_open_cons_close, -> count_close_cons_close in h1. split.
    * lia.
    * intros l' h3.
      epose proof h2 (close::l') ltac:(apply prefix_cons; auto).
      rewrite -> count_close_cons_close, -> count_open_cons_close in H. lia.
  - intro h'. destruct h' as [h1 h2]. rewrite -> count_open_cons_close, -> count_close_cons_close. split.
    * lia.
    * intros l' h'. destruct l'.
      { rewrite -> count_open_nil, -> count_close_nil. lia. }
      { pose proof prefix_cons_inv_1 _ _ _ _ h'. rewrite H. rewrite -> count_open_cons_close, -> count_close_cons_close. pose proof (h2 l' (prefix_cons_inv_2 _ _ _ _ h')). lia. }
Qed.

Lemma prop_analog_equivalent (l : list bracket_t) (open_count close_count : nat) : alternate_balanced_condition_aux l open_count close_count <-> (alternate_balanced_condition_bool_aux l open_count close_count = true).
Proof.
  revert open_count close_count.
  induction l.
  - intros open_count close_count. unfold alternate_balanced_condition_aux. rewrite -> count_open_nil, -> count_close_nil.
    split.
    + intro h. destruct h as [h1 h2]. rewrite Nat.add_0_r, Nat.add_0_r in h1.
      simp alternate_balanced_condition_bool_aux. rewrite bool_decide_eq_true. assumption.
    + intro h. simp alternate_balanced_condition_bool_aux in h. rewrite bool_decide_eq_true in h. rewrite Nat.add_0_r, Nat.add_0_r. split.
      * assumption.
      * intros l' h'. rewrite (prefix_nil_inv _ h'). rewrite count_close_nil, count_open_nil. lia.
  - intros open_count close_count. destruct a.
    + simp alternate_balanced_condition_bool_aux.
      case_bool_decide.
      * unfold alternate_balanced_condition_aux. split.
        { intro h. destruct h as [_ h]. pose proof (h [] ltac:(apply prefix_nil)). rewrite count_close_nil, count_open_nil in H0. lia. }
        { intro h. easy. }
      * assert (H1 : close_count <= open_count). { lia. }
        rewrite (cons_open_recurse l _ _ H1). exact (IHl _ _).
    + simp alternate_balanced_condition_bool_aux.
      case_bool_decide.
      * unfold alternate_balanced_condition_aux. split.
        { intro h. destruct h as [_ h]. pose proof (h [] ltac:(apply prefix_nil)). rewrite count_close_nil, count_open_nil in H0. lia. }
        { intro h. easy. }
      * assert (H1 : close_count <= open_count). { lia. }
        rewrite (cons_close_recurse l _ _ H1). exact (IHl _ _).
Qed.

Lemma alternate_balanced_condition_aux_initialized_to_zero (l : list bracket_t) : alternate_balanced_condition_aux l 0 0 <-> alternate_balanced_condition l.
Proof.
  unfold alternate_balanced_condition. unfold alternate_balanced_condition_aux.
  easy.
Qed.

Lemma alternate_balanced_condition_bool_iff_alternate_balanced_condition (l : list bracket_t) :
  (alternate_balanced_condition_bool l = true) <-> alternate_balanced_condition l.
Proof.
  rewrite <- alternate_balanced_condition_aux_initialized_to_zero.
  unfold alternate_balanced_condition_bool.
  rewrite prop_analog_equivalent.
  reflexivity.
Qed.