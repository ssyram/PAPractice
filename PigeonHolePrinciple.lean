import Lake
import Init.Data.Nat.Basic
import Init.Data.Basic

-- A streamlined approach to demonstrating the Pigeonhole Principle without relying on the law of excluded middle.
-- This method is specifically tailored to this problem definition.
-- The underlying concept is that since every element in list l1 is present in list l2, we can transform the elements of l1 into a list of indices referring to the positions of the element in l2.
-- Consequently, the challenge becomes demonstrating the Pigeonhole Principle for a list of natural numbers, which is certainly decidable.
-- Given that natural numbers are decidable, we can confidently discuss whether n1 equals n2 or n1 does not equal n2 during the proof.

-- An additional technical point to consider is that the same element in l1 may not correspond to the same index in l2 (since l2 may contain duplicates).
-- However, we observe that:
-- (1) If there is repetition in the indices list, then there must also be repetition in the original list l1.
-- (2) Since the indices are fewer than the slots available, repetition must occur.

def within (x : X) l :=
  match l with
  | [] => False
  | x' :: l' => x = x' ∨ within x l'

def within_iff_split : within x l <-> ∃ l1 l2, l1 ++ x :: l2 = l := by
  constructor
  case mp => {
    intro h
    induction l; contradiction
    case cons x' l' Hind =>
      cases h
      case inl =>
        subst x'; exists [], l'
      case inr =>
        have : ∃ l1 l2, l1 ++ x :: l2 = l' := by apply Hind; assumption
        revert this; intro ⟨l1, l2, H⟩
        exists (x' :: l1), l2
        rw [<- H]
        simp
  }
  case mpr => {
    intro ⟨l1, l2, H⟩
    revert l2 l x
    induction l1
    case nil =>
      intro _ l l2 _
      subst l
      apply Or.inl
      rfl
    case cons x' l1' Hind =>
      intro x l l2 _
      subst l
      apply Or.inr
      simp
      apply Hind
      rfl
  }

inductive repeats : List X -> Prop where
  | RBase x l : within x l -> repeats (x :: l)
  | RInd x l : repeats l -> repeats (x :: l)

theorem repeats_app : repeats l -> repeats (s ++ l) := by
  revert l
  induction s
  case nil => simp; intros; trivial
  case cons x s' Hind =>
    intros; apply repeats.RInd; simp; apply Hind; trivial

theorem nat_decidable : ∀ x y : Nat, x = y ∨ x ≠ y := by
  intro x
  induction x
  case zero =>
    intro y; cases y
    case zero => trivial
    case succ => apply Or.inr; intro; trivial
  case succ x IH =>
    intro y
    cases y
    case zero => apply Or.inr; intro; trivial
    case succ y =>
      cases IH y
      . apply Or.inl; subst y; rfl
      . apply Or.inr; intro H; cases H; contradiction

theorem in_nat_list_decidable : ∀ (n : Nat) ns, within n ns ∨ ¬ within n ns := by
  intro n ns
  revert n
  induction ns
  case nil => intros; apply Or.inr; intro H; contradiction
  case cons n ns Hind =>
    intro n'
    cases (nat_decidable n n')
    case inl =>
      subst n'; apply Or.inl; apply Or.inl; rfl
    case inr =>
      cases (Hind n')
      case inl =>
        apply Or.inl; apply Or.inr; assumption
      case inr =>
        apply Or.inr
        intro H
        cases H
        . subst n'; contradiction
        . contradiction

theorem within_app : within x (l1 ++ l2) <-> within x l1 ∨ within x l2 := by
  revert l2
  induction l1
  case nil =>
    simp; intro l2; constructor
    case mp => intro; apply Or.inr; assumption
    case mpr => intro H; cases H; trivial; trivial
  case cons x l1' Hind =>
    simp; intro l2; constructor
    case mp => {
      intro H; cases H
      case inl =>
        subst x; apply Or.inl; apply Or.inl; rfl
      case inr x' H =>
        have H := Iff.mp Hind H
        cases H
        case inl =>
          apply Or.inl; apply Or.inr; assumption
        case inr =>
          apply Or.inr; assumption
    }
    case mpr => {
      intro H; cases H
      case inl H =>
        cases H
        case inl => subst x; apply Or.inl; rfl
        case inr H =>
          apply Or.inr; apply Iff.mpr Hind;
          apply Or.inl; assumption
      case inr H =>
        apply Or.inr; apply Iff.mpr Hind; apply Or.inr; assumption
    }

theorem nat_list_pigeon_hole_principle :
  (∀ x : Nat, within x l1 -> within x l2) ->
  (List.length l2 < List.length l1) ->
  repeats l1 := by
  revert l2
  induction l1; intros; contradiction
  rename_i n l1 Hind
  simp at *
  intro l2 Hi Hl
  cases (in_nat_list_decidable n l1)
  constructor; trivial
  apply repeats.RInd
  have : within n l2 := by apply Hi; apply Or.inl; rfl
  have H := Iff.mp within_iff_split this
  clear this
  revert H; intro ⟨l2e, l2f, Happ⟩
  have Hi : ∀ x, within x l1 -> within x (l2e ++ l2f) := by
    intro x Hxinl1
    have : within x l2e ∨ within x (n :: l2f) := by
      apply Iff.mp within_app
      rw [Happ]; apply Hi; apply Or.inr;
      assumption
    cases (nat_decidable n x);
    case inl => subst n; contradiction
    case inr =>
      apply Iff.mpr within_app
      cases this
      case inl => apply Or.inl; assumption
      case inr H =>
        apply Or.inr; cases H; subst x; contradiction; assumption
  apply Hind; apply Hi
  have : Nat.succ (List.length (l2e ++ l2f)) = List.length l2 := by subst l2; simp; rfl
  rw [← this] at Hl
  apply Nat.lt_of_succ_lt_succ
  assumption

def initLst m :=
  match m with
  | 0 => []
  | Nat.succ m => initLst m ++ [m]

theorem init_lst_st_0 : m > 0 -> ∃ l, 0 :: l = initLst m := by
  induction m
  case zero => intros; contradiction
  case succ m IH =>
    intro H
    cases H
    case refl => exists []
    case step =>
      simp at *
      unfold initLst
      have : ∃ l, 0 :: l = initLst m := by apply IH; trivial
      revert this; intro ⟨l, H⟩
      exists (l ++ [m])
      rw [← H]
      rfl

-- convert the problem to a which one it is in problem

inductive At (x : X) : List X -> Nat -> Prop where
  | Base l : At x (x :: l) 0
  | Rec : At x l n -> At x (x' :: l) (Nat.succ n)

theorem at_inj (l : List X) : At x1 l n -> At x2 l n -> x1 = x2 := by
  intro H
  induction H
  case Base l' =>
    intro H
    cases H
    trivial
  case Rec l' n' x' _ IH =>
    intro H'
    apply IH
    cases H'
    trivial

theorem within_eq_at : ∀ (x : X) l, within x l ↔ ∃ n, At x l n := by
  intro x l
  constructor
  case mp => {
    revert x
    induction l
    case nil =>
      intros
      contradiction
    case cons x' l' Hind =>
      intro x Hi
      cases Hi with
      | inl Heq => exists 0; subst x'; constructor
      | inr Hi =>
        cases Hind x Hi with
        | intro n Hat => exists (Nat.succ n); constructor; trivial
  }
  case mpr => {
    intro ⟨n, H⟩
    induction H
    case Base _ =>
      apply Or.inl
      trivial
    case Rec =>
      apply Or.inr
      trivial
  }

theorem at_not_change : At x l n -> At x (l ++ s) n := by
  revert x n s
  induction l
  case nil => simp; intros; contradiction
  case cons x' l' IH =>
    intro x n s H
    cases H
    case Base => constructor
    case Rec n Hat =>
      constructor; simp;
      apply IH; assumption

theorem at_prepend_move l : At x s n -> At x (l ++ s) (List.length l + n) := by
  revert x s n
  induction l
  case nil => simp; intros; assumption
  case cons xl l' IH =>
    intro x s n Hat
    simp
    rw [Nat.succ_add]
    apply At.Rec
    apply IH
    assumption

theorem init_lst_len : List.length (initLst n) = n := by
  induction n
  case zero => rfl
  case succ n IH =>
    unfold initLst; simp; assumption

theorem nat_list_lt_m_in_init_list : ∀ n : Nat, n < m -> At n (initLst m) n := by
  induction m
  case zero => intros; contradiction
  case succ m IH =>
    intro n Hlt
    cases Hlt
    case refl =>
      unfold initLst
      have : At m ([m]) 0 := by constructor
      have H := at_prepend_move (initLst m) this
      have : List.length (initLst m) = m := by apply init_lst_len
      simp at *
      rw [this] at H
      assumption
    case step H =>
      have H := Nat.lt_of_succ_le H
      unfold initLst
      apply at_not_change
      apply IH
      assumption

theorem nat_list_in_init_list : (∀ n : Nat, within n l -> n < m) -> ∀ n, within n l -> within n (initLst m) := by
  intro H n Hi
  apply Iff.mpr (within_eq_at n (initLst m))
  exists n
  have : n < m := by apply H; assumption
  apply nat_list_lt_m_in_init_list
  assumption





-- inductive IsConvLst (l1 l2 : List X) : (∀ x, within x l1 -> within x l2) -> List Nat -> Prop where

inductive IsPairList (P : X -> Nat -> Prop) : List X -> List Nat -> Prop where
  | nil : IsPairList P [] []
  | cons x n : P x n -> IsPairList P l l' -> IsPairList P (x :: l) (n :: l')

theorem convert : ∀ (l1 l2 : List X),
  (∀ x, within x l1 -> within x l2) ->
  ∃ ln, IsPairList (fun x n => At x l2 n) l1 ln := by
  intro l1
  induction l1
  case nil =>
    intros
    exists []
    constructor
  case cons x' l Hind =>
    intro l2 Hi
    have : ∃ ln, IsPairList (fun x n => At x l2 n) l ln := by
      apply Hind
      intro x H; apply Hi; apply Or.inr; trivial
    clear Hind
    have H' : ∃ n, At x' l2 n := by
      rw [← within_eq_at]
      apply Hi; apply Or.inl; trivial
    revert H'; intro ⟨n, HAt⟩
    revert this; intro ⟨ln, Hln⟩
    exists (n :: ln)
    constructor
    . assumption
    . assumption

theorem inj_repeats_implies P ns (xs : List X) : (∀ x1 x2 n, P x1 n -> P x2 n -> x1 = x2) -> IsPairList P xs ns -> repeats ns -> repeats xs := by
  intro Hinj Hpair Hrns
  induction Hpair
  case nil => contradiction
  case cons xs ns x n HPxn Hpair IH =>
  cases Hrns
  case RBase n ln => {
    constructor
    rw [within_eq_at]
    rw [within_eq_at] at ln
    revert ln
    intro ⟨m, Hatm⟩
    exists m
    clear IH
    revert xs
    induction Hatm
    case a.Base ns => {
      intro xs Hpair
      cases Hpair
      rename_i xs x' Pxsn Hpair
      have : x = x' := Hinj x x' n HPxn Pxsn
      subst x'
      constructor
    }
    case a.Rec ns' m' n'' _ HInd => {
      intro xs Hpair
      cases Hpair
      rename_i xs' x' Pxsn _
      apply At.Rec
      apply HInd
      assumption
    }
  }
  case RInd _ H => {
    apply repeats.RInd
    apply IH
    exact H
  }

theorem max_at : At x l n -> n < List.length l := by
  revert n
  induction l
  case nil => intros; contradiction
  case cons x l Hind =>
    intro n H
    cases H
    case Base => simp; apply Nat.zero_lt_succ
    case Rec x' n Hat =>
      let some := Hind Hat
      simp
      apply Nat.succ_lt_succ
      assumption

theorem same_length : IsPairList P xs ns -> List.length xs = List.length ns := by
  intro Hpair
  induction Hpair
  case nil => trivial
  case cons => simp; trivial

theorem max_n_ns : IsPairList (fun x n => At x l2 n) l1 ns -> ∀ n, within n ns -> n < List.length l2 := by
  intro Hpair
  induction Hpair
  case nil => intros; contradiction
  case cons =>
    intro n Hi
    rename_i Hat _ Hind
    cases Hi
    subst n
    apply (max_at Hat)
    rename_i Hi
    apply Hind
    assumption

theorem nat_list_repeats_decidability (ns : List Nat) : repeats ns ∨ ¬ repeats ns := by
  induction ns
  case nil => apply Or.inr; intro; contradiction
  case cons x xs Hind =>
    cases (in_nat_list_decidable x xs)
    case inl => apply Or.inl; constructor; assumption
    case inr =>
      cases Hind
      case inl => apply Or.inl; apply repeats.RInd; assumption
      case inr =>
        apply Or.inr
        intro H
        cases H
        . contradiction
        . contradiction

theorem pigeon_hole_nat_lt_m (ns : List Nat) : (∀ n, within n ns -> n < m) -> m < List.length ns -> repeats ns := by
  intro H
  have H' := nat_list_in_init_list H
  have Hl : List.length (initLst m) = m := by apply init_lst_len
  intro Hl'
  generalize H : (initLst m) = l2
  rw [H] at H'
  apply nat_list_pigeon_hole_principle
  assumption
  subst l2
  rw [Hl]
  exact Hl'

theorem pigeon_hole_principle : ∀ (l1 l2 : List X),
  (∀ x, within x l1 -> within x l2) ->
  List.length l2 < List.length l1 ->
  repeats l1 := by
  intro l1 l2 Hi Hl
  have H : ∃ ns, IsPairList (fun x n => At x l2 n) l1 ns ∧ repeats ns := by
    have H : ∃ ns, IsPairList (fun x n => At x l2 n) l1 ns := by
      clear Hl
      induction l1
      case nil => exists []; constructor
      case cons x xs Hind =>
        have H : (∀ (x : X), within x xs → within x l2) := by
          intro x Hx
          apply Hi; apply Or.inr; assumption
        have H' : within x l2 := by
          apply Hi; apply Or.inl; rfl
        rw [within_eq_at] at H'
        revert H'; intro ⟨n, Hn⟩
        have : ∃ ns, IsPairList (fun x n => At x l2 n) xs ns := by
          apply Hind
          assumption
        revert this; intro ⟨ns, Hns⟩
        exists (n :: ns)
        constructor; try trivial
        trivial
    revert H; intro ⟨ns, HNs⟩
    exists ns; constructor; trivial
    have H : ∀ n, within n ns -> n < List.length l2 := by
      intro n
      apply max_n_ns
      assumption
    have Hlen : List.length l2 < List.length ns := by
      have : List.length l1 = List.length ns := by
        apply same_length; assumption
      rw [<- this]
      assumption
    -- we are at a stage of dealing only with Nat lists
    apply pigeon_hole_nat_lt_m
    apply H
    assumption
  revert H; intro ⟨ns, ⟨Hpair, Hrns⟩⟩
  apply (inj_repeats_implies (fun x n => At x l2 n) ns l1); try trivial
  intro x1 x2 n
  apply at_inj
  assumption
  assumption
