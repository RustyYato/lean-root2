import  Root2.Nat
import Init.Data.Array.DecidableEq

@[simp]
def nat.less (a b: nat) : Prop :=
  match a with
    | nat.zero => match b with
      | nat.zero => False
      | nat.inc _ => True
    | nat.inc a₀ => match b with
      | nat.zero => False
      | nat.inc b₀ => less a₀ b₀

@[simp]
def nat.less_eq (a b: nat) : Prop :=
  match a with
    | nat.zero => True
    | nat.inc a₀ => match b with
      | nat.zero => False
      | nat.inc b₀ => less_eq a₀ b₀

instance : LT nat where
  lt := nat.less

instance : LE nat where
  le := nat.less_eq

syntax "unfold_le" : tactic

macro_rules
 | `(tactic| unfold_le) => `(tactic| unfold LE.le; unfold instLENat_1 )

syntax "unfold_lt" : tactic

macro_rules
 | `(tactic| unfold_lt) => `(tactic| unfold LT.lt; unfold instLTNat_1 )

theorem nat.zero_lt_inc : ∀ a: nat, nat.zero < nat.inc a := by
  intro
  trivial

theorem nat.inc_le_to_le : (nat.inc a) <= (nat.inc b) -> a <= b := by
  intro
  trivial

theorem nat.le_to_inc_le : a <= b -> (nat.inc a) <= (nat.inc b) := by
  unfold_le
  intro le_inc
  trivial

theorem nat.lt_inc : ((nat.inc a) < (nat.inc b)) = (a < b) := by
  trivial

theorem nat.le_inc : ((nat.inc a) <= (nat.inc b)) = (a <= b) := by
  trivial

theorem nat.not_lt_is_sym_le : (¬nat.less a b) = nat.less_eq b a := by
  unfold less
  unfold less_eq
  match a with
  | nat.zero => match b with
    | nat.zero => trivial
    | nat.inc _ => simp
  | nat.inc a₀ => match b with
    | nat.zero => simp
    | nat.inc b₀ => simp; exact @nat.not_lt_is_sym_le a₀ b₀

theorem nat.not_le_is_sym_lt : (¬nat.less_eq a b) = nat.less b a := by
  unfold less
  unfold less_eq
  match a with
  | nat.zero => match b with
    | nat.zero => trivial
    | nat.inc _ => simp
  | nat.inc a₀ => match b with
    | nat.zero => simp
    | nat.inc b₀ => simp; exact @nat.not_le_is_sym_lt a₀ b₀

theorem nat.not_lt_is_sym_le_op {{ a b: nat }} : (¬(a < b)) = (b <= a) := by
  apply nat.not_lt_is_sym_le

theorem nat.not_le_is_sym_lt_op {{ a b: nat }} : (¬(a <= b)) = (b < a) := by
  apply nat.not_le_is_sym_lt

theorem nat.eq_inc_irr : nat.inc a = nat.inc b <-> a = b := by
  apply Iff.intro
  . intro inc_eq; simp at inc_eq; assumption
  . intro eq; rw [eq]

theorem nat.lt_inc_irr (a b: nat) : (inc a < inc b) = (a < b) := by
  trivial
 
theorem nat.le_inc_irr (a b: nat) : (inc a <= inc b) = (a <= b) := by
  trivial

theorem nat.lt_to_ne : ∀{{a b: nat}}, (a < b) -> ¬(a = b) := by
  intro a b lt
  cases a
  cases b
  trivial
  intro
  trivial
  cases b
  intro
  trivial
  rw [lt_inc] at lt
  rw [nat.eq_inc_irr]
  apply nat.lt_to_ne
  trivial

theorem nat.lt_is_le : ∀ a b: nat, (a < b) -> (a <= b) := by
  intro a b
  match a with
  | nat.zero =>
    intro
    trivial
  | nat.inc a₀ => match b with
    | nat.zero =>
      intro
      trivial
    | nat.inc b₀ =>
      intro lt
      rw [nat.lt_inc_irr] at lt
      rw  [le_inc_irr]
      apply nat.lt_is_le
      assumption

theorem nat.zero_le : ∀ a: nat, nat.zero <= a := by
  intro
  trivial

theorem nat.le_id : ∀ a: nat, a <= a := by
  intro a
  match a with
  | nat.zero => trivial
  | nat.inc a₀ => rw [←nat.le_inc]; exact (nat.le_id a₀)

theorem nat.eq_to_le : ∀ {{a b: nat}}, a = b -> (a <= b) := by
  intro a b a_eq_b
  rw [a_eq_b]
  exact (nat.le_id b)

theorem nat.comp_dec {{a b: nat}} : a < b -> b <= a -> False := by
  intro a_lt_b b_le_a
  rw [←nat.not_lt_is_sym_le_op] at b_le_a
  contradiction

theorem nat.le_inc_zero : ∀ a: nat, ¬(nat.inc a <= zero) := by
  intro a b
  contradiction

theorem nat.le_le_to_eq : ∀ {{a b: nat}}, a <= b -> b <= a -> a = b := by
  intro a b a_lt_b b_lt_a
  match a with
  | nat.zero => match b with
    | nat.zero => rfl
    | nat.inc b₀ =>

      have _ := nat.le_inc_zero b b_lt_a
      contradiction
  | nat.inc a₀ => match b with
    | nat.zero => 

      have _ := nat.le_inc_zero b a_lt_b
      contradiction
    | nat.inc b₀ =>
      rw [←nat.le_inc] at *
      rw [nat.eq_inc_irr]
      apply nat.le_le_to_eq <;> assumption

theorem nat.le_zero : ∀ a: nat, a <= nat.zero -> a = nat.zero := by
  intro a a_le_zero
  have zero_le_a := nat.zero_le a
  exact (nat.le_le_to_eq a_le_zero zero_le_a)

theorem nat.not_lt_zero (a: nat) : ¬(a < nat.zero) := by
  intro a_le_zero
  match a with
  | nat.zero => contradiction

theorem nat.a_lt_inc_a : ∀ a: nat, a < nat.inc a := by
  intro a
  match a with
  | nat.zero => trivial
  | nat.inc a₀ => rw [nat.lt_inc]; apply nat.a_lt_inc_a

theorem nat.a_le_inc_a : ∀ a: nat, a <= nat.inc a := by
  intro a
  match a with
  | nat.zero => trivial
  | nat.inc a₀ => rw [nat.le_inc]; apply nat.a_le_inc_a
 

theorem nat.lt_to_nat : ∀ a b: nat, a < b <-> toNat a < toNat b := by
  intro a b
  apply Iff.intro
  . intro a_lt_b
    match a with
    | nat.zero => match b with
      | nat.inc b₀ => unfold toNat; apply Nat.zero_lt_succ
    | nat.inc a₀ => match b with
      | nat.inc b₀ =>
        apply Nat.succ_lt_succ
        rw [← nat.lt_inc] at a_lt_b
        exact (nat.lt_to_nat a₀ b₀).mp a_lt_b
  . intro a_lt_b
    match a with
      | nat.zero => match b with
        | nat.inc b₀ => apply nat.zero_lt_inc
      | nat.inc a₀ => match b with
        | nat.inc b₀ =>
          rw [nat.lt_inc]
          unfold toNat at a_lt_b
          have x := Nat.lt_of_succ_lt_succ a_lt_b
          have y := (nat.lt_to_nat a₀ b₀).mpr x
          assumption

theorem nat.le_trans : ∀ {{a b c: nat}}, a <= b -> b <= c -> a <= c := by
  intro a b c a_le_b b_le_c
  match a with
  | nat.zero => apply nat.zero_le
  | nat.inc a₀ => match b with
    | nat.zero => have _ := nat.le_inc_zero _ a_le_b; contradiction
    | nat.inc b₀ => match c with
      | nat.zero => have _ := nat.le_inc_zero _ b_le_c; contradiction
      | nat.inc c₀ =>
      rw [nat.le_inc] at *
      exact nat.le_trans a_le_b b_le_c

theorem nat.lt_trans : ∀ {{a b c: nat}}, a < b -> b < c -> a < c := by
  intro a b c a_lt_b b_lt_c
  match c with
  | nat.zero => match b with
     | nat.inc _ => contradiction
  | nat.inc c₀ => match b with
    | nat.zero => match a with
      | nat.inc _ => contradiction
    | nat.inc b₀ => match a with
      | nat.zero => apply nat.zero_lt_inc
      | nat.inc a₀ =>
      rw [nat.lt_inc] at *
      exact nat.lt_trans a_lt_b b_lt_c

def nat.compare_le (a b: nat) : Decidable (a <= b) :=
  match a with
  | nat.zero => Decidable.isTrue (by trivial)
  | nat.inc a₀ => match b with
    | nat.zero => Decidable.isFalse (by
      intro
      contradiction
    )
    | nat.inc b₀ =>
      by rw [@nat.le_inc a₀ b₀]; exact (nat.compare_le a₀ b₀)

def nat.compare_lt (a b: nat) : Decidable (a < b) :=
  match a with
  | nat.zero => match b with
    | nat.zero => Decidable.isFalse (by intro; contradiction)
    | nat.inc _ => Decidable.isTrue (by apply nat.zero_lt_inc)
  | nat.inc a₀ => match b with
    | nat.zero => Decidable.isFalse (by
      intro
      contradiction
    )
    | nat.inc b₀ =>
      by rw [@nat.lt_inc a₀ b₀]; exact (nat.compare_lt a₀ b₀)

def nat.beq (a b: nat) : Bool :=
  match a, b with
  | nat.zero, nat.zero => true
  | nat.zero, nat.inc _ => false
  | nat.inc _, nat.zero => false
  | nat.inc a₀, nat.inc b₀ => a₀.beq b₀

theorem nat.eq_of_beq_eq_true : (a b: nat) -> (a.beq b = true) -> a = b
  | nat.zero, nat.zero, _ => rfl
  | nat.inc a₀, nat.inc b₀, h => (a₀.eq_of_beq_eq_true b₀ h).substr rfl

theorem nat.ne_of_beq_eq_false : (a b: nat) -> (a.beq b = false) -> (a = b) -> False
  | nat.inc a₀, nat.inc b₀, h₁, h₂ => 
    nat.noConfusion h₂ (a₀.ne_of_beq_eq_false b₀ h₁)

def nat.compare_eq (a b: nat) : Decidable (a = b) :=
  match eq:a.beq b with
  | true => Decidable.isTrue (a.eq_of_beq_eq_true b eq)
  | false => Decidable.isFalse (a.ne_of_beq_eq_false b eq)

theorem nat.inc_le (a b: nat) : inc a <= b -> a <= b := by
  match b with
  | nat.zero => intro a; contradiction
  | nat.inc b₀ =>
    intro a_le_b
    have b_le_inc_b := nat.a_le_inc_a b₀
    exact (nat.le_trans a_le_b b_le_inc_b)

theorem nat.inc_gt_zero {{ a : nat }} : (a.inc <= nat.zero)=False := by
  trivial

theorem nat.zero_lt_all {{ a : nat }} : (a < nat.zero)=False := by
  cases a <;> trivial

theorem nat.lt_inc_to_le {{ a b: nat }} : (a < inc b) = (a <= b) := by
  match a with
  | nat.zero => trivial
  | nat.inc a₀ => match b with
    | nat.zero =>
      rw [nat.lt_inc_irr, @nat.inc_gt_zero a₀, nat.zero_lt_all]
    | nat.inc b₀ =>
      rw [nat.lt_inc_irr]
      apply nat.lt_inc_to_le
