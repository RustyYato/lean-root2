import  Root2.Nat

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

@[simp]
theorem nat.zero_lt_inc : ∀ a: nat, nat.zero < nat.inc a := by
  intro a
  unfold_lt
  simp

theorem nat.inc_le_to_le : (nat.inc a) <= (nat.inc b) -> a <= b := by
  unfold_le
  intro le_inc
  match a with
  | nat.zero => match b with
    | nat.zero => simp
    | nat.inc _ => simp
  | nat.inc a₀ => match b with
    | nat.zero => 
      simp at le_inc
    | nat.inc b₀ => simp; exact (inc_le_to_le le_inc)

@[simp]
theorem nat.le_to_inc_le : a <= b -> (nat.inc a) <= (nat.inc b) := by
  unfold_le
  intro le_inc
  match a with
  | nat.zero => match b with
    | nat.zero => simp
    | nat.inc _ => simp
  | nat.inc a₀ => match b with
    | nat.zero => simp at le_inc
    | nat.inc b₀ => simp; exact (inc_le_to_le le_inc)

theorem nat.inc_lt_to_lt : (nat.inc a) < (nat.inc b) -> a < b := by
  unfold_lt
  intro lt_inc
  match a with
  | nat.zero => match b with
    | nat.zero => unfold less at lt_inc; simp at lt_inc
    | nat.inc _ => simp
  | nat.inc a₀ => match b with
    | nat.zero => 
      simp at lt_inc
    | nat.inc b₀ => simp;  exact (inc_lt_to_lt lt_inc)

@[simp]
theorem nat.lt_to_inc_lt : a < b -> (nat.inc a) < (nat.inc b) := by
  unfold_lt
  intro lt_inc
  match a with
  | nat.zero => match b with
    | nat.zero => simp at lt_inc
    | nat.inc _ => simp
  | nat.inc a₀ => match b with
    | nat.zero => simp at lt_inc
    | nat.inc b₀ => exact (inc_lt_to_lt lt_inc)

theorem nat.lt_inc : a < b ↔ (nat.inc a) < (nat.inc b) := by
  apply Iff.intro
  . apply nat.lt_to_inc_lt
  . apply nat.inc_lt_to_lt

theorem nat.le_inc : a <= b ↔ (nat.inc a) <= (nat.inc b) := by
  apply Iff.intro
  . apply nat.le_to_inc_le
  . apply nat.inc_le_to_le

@[simp]
theorem nat.not_lt_is_sym_le : (¬nat.less a b) = nat.less_eq b a := by
  unfold less
  unfold less_eq
  match a with
  | nat.zero => match b with
    | nat.zero => simp
    | nat.inc _ => simp
  | nat.inc a₀ => match b with
    | nat.zero => simp
    | nat.inc b₀ => simp; exact @nat.not_lt_is_sym_le a₀ b₀

@[simp]
theorem nat.not_le_is_sym_lt : (¬nat.less_eq a b) = nat.less b a := by
  unfold less
  unfold less_eq
  match a with
  | nat.zero => match b with
    | nat.zero => simp
    | nat.inc _ => simp
  | nat.inc a₀ => match b with
    | nat.zero => simp
    | nat.inc b₀ => simp; exact @nat.not_le_is_sym_lt a₀ b₀

@[simp]
theorem nat.not_lt_is_sym_le_op {{ a b: nat }} : (¬(a < b)) = (b <= a) := by
  unfold LT.lt
  unfold instLTNat_1
  unfold LE.le
  unfold instLENat_1
  apply nat.not_lt_is_sym_le

@[simp]
theorem nat.not_le_is_sym_lt_op {{ a b: nat }} : (¬(a <= b)) = (b < a) := by
  unfold_lt
  unfold_le
  apply nat.not_le_is_sym_lt

@[simp]
theorem nat.eq_inc_irr : nat.inc a = nat.inc b <-> a = b := by
  apply Iff.intro
  . intro inc_eq; simp at inc_eq; assumption
  . intro eq; rw [eq]

@[simp]
theorem nat.lt_to_le : ∀ {{a b: nat}}, (less a b) -> (less_eq a b) := by
  intro a b
  match a with
  | nat.zero => 
    unfold less
    unfold less_eq
    simp
  | nat.inc a₀ => simp; match b with
    | nat.zero =>
      unfold less
      unfold less_eq
      simp
    | nat.inc b₀ => intro lt; exact nat.lt_to_le lt

@[simp]
theorem nat.lt_is_le_op : ∀ a b: nat, (a < b) -> (a <= b) := by
  unfold LE.le
  unfold LT.lt
  unfold instLTNat_1
  unfold instLENat_1
  apply nat.lt_to_le

@[simp]
theorem nat.zero_le : ∀ a: nat, nat.zero <= a := by
  intro a
  unfold LE.le
  unfold instLENat_1
  unfold less_eq
  simp

@[simp]
theorem nat.le_id : ∀ a: nat, less_eq a a := by
  intro a
  unfold less_eq
  match a with
  | nat.zero => simp
  | nat.inc a₀ => simp; apply nat.le_id

@[simp]
theorem nat.le_id_op : ∀ a: nat, a <= a := by
  intro a
  unfold LE.le
  unfold instLENat_1
  apply nat.le_id

@[simp]
theorem nat.eq_to_le : ∀ {{a b: nat}}, a = b -> (a <= b) := by
  intro a b a_eq_b
  rw [a_eq_b]
  simp
  

@[simp]
theorem nat.comp_dec {{a b: nat}} : a < b -> b <= a -> False := by
  intro a_lt_b b_le_a
  rw [←nat.not_lt_is_sym_le_op] at b_le_a
  contradiction

@[simp]
theorem nat.le_inc_zero : ∀ a: nat, ¬(nat.inc a <= zero) := by
  intro a
  unfold LE.le
  unfold instLENat_1
  unfold less_eq
  simp

@[simp]
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
      simp
      apply nat.le_le_to_eq <;> assumption

@[simp]
theorem nat.le_zero : ∀ a: nat, a <= nat.zero -> a = nat.zero := by
  intro a a_le_zero
  have zero_le_a := nat.zero_le a
  exact (nat.le_le_to_eq a_le_zero zero_le_a)

@[simp]
theorem nat.not_lt_zero (a: nat) : ¬(a < nat.zero) := by
  intro a_le_zero
  match a with
  | nat.zero => contradiction

@[simp]
theorem nat.a_lt_inc_a : ∀ a: nat, a < nat.inc a := by
  intro a
  match a with
  | nat.zero =>
    unfold_lt
    simp
  | nat.inc a₀ => rw [← nat.lt_inc]; apply nat.a_lt_inc_a

@[simp]
theorem nat.a_le_inc_a : ∀ a: nat, a <= nat.inc a := by
  intro a
  match a with
  | nat.zero =>
    unfold_le
    simp
  | nat.inc a₀ => rw [← nat.le_inc]; apply nat.a_le_inc_a
  

theorem nat.lt_to_nat : ∀ a b: nat, a < b <-> toNat a < toNat b := by
  intro a b
  apply Iff.intro
  . intro a_lt_b
    match a with
    | nat.zero => match b with
      | nat.inc b₀ => unfold toNat; apply Nat.zero_lt_succ
    | nat.inc a₀ => match b with
      | nat.inc b₀ =>
        unfold toNat
        simp
        apply Nat.succ_lt_succ
        rw [← nat.lt_inc] at a_lt_b
        exact (nat.lt_to_nat a₀ b₀).mp a_lt_b
  . intro a_lt_b
    match a with
      | nat.zero => match b with
        | nat.inc b₀ => apply nat.zero_lt_inc
      | nat.inc a₀ => match b with
        | nat.inc b₀ =>
          apply nat.lt_to_inc_lt
          unfold toNat at a_lt_b
          have x := Nat.lt_of_succ_lt_succ a_lt_b
          have y := (nat.lt_to_nat a₀ b₀).mpr x
          assumption

@[simp]
theorem nat.le_trans : ∀ {{a b c: nat}}, a <= b -> b <= c -> a <= c := by
  intro a b c a_le_b b_le_c
  match a with
  | nat.zero => apply nat.zero_le
  | nat.inc a₀ => match b with
    | nat.zero => have _ := nat.le_inc_zero _ a_le_b; contradiction
    | nat.inc b₀ => match c with
      | nat.zero => have _ := nat.le_inc_zero _ b_le_c; contradiction
      | nat.inc c₀ => 
      rw [←nat.le_inc] at *
      exact nat.le_trans a_le_b b_le_c

@[simp]
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
      rw [←nat.lt_inc] at *
      exact nat.lt_trans a_lt_b b_lt_c

def nat.compare_or_eq (a b: nat) : Decidable (a <= b) := 
  match a with
  | nat.zero => Decidable.isTrue (by
    unfold_le
    simp
    )
  | nat.inc a₀ => match b with
    | nat.zero => Decidable.isFalse (by
      unfold_le
      simp
    )
    | nat.inc b₀ =>
      by rw [←@nat.le_inc a₀ b₀]; exact (nat.compare_or_eq a₀ b₀)

def nat.compare (a b: nat) : Decidable (a < b) := 
  match a with
  | nat.zero => match b with
    | nat.zero => Decidable.isFalse (by intro; contradiction)
    | nat.inc _ => Decidable.isTrue (by apply nat.zero_lt_inc)
  | nat.inc a₀ => match b with
    | nat.zero => Decidable.isFalse (by
      unfold_lt
      simp
    )
    | nat.inc b₀ =>
      by rw [←@nat.lt_inc a₀ b₀]; exact (nat.compare a₀ b₀)

@[simp]
def nat.compare_eq (a b: nat) : Decidable (a = b) := 
  match a with
  | nat.zero => match b with
    | nat.zero => Decidable.isTrue rfl
    | nat.inc _ => Decidable.isFalse (by intro; contradiction)
  | nat.inc a₀ => match b with
    | nat.zero => Decidable.isFalse (by intro; contradiction)
    | nat.inc b₀ =>
      by rw [@nat.eq_inc_irr a₀ b₀]; exact (nat.compare_eq a₀ b₀)

@[simp]
theorem nat.lt_inc_irr (a b: nat) : (inc a < inc b) = (a < b) := by
  unfold LT.lt instLTNat_1
  match a with
  | nat.zero => simp
  | nat.inc a₀ =>simp

@[simp]
theorem nat.le_inc_irr (a b: nat) : (inc a <= inc b) = (a <= b) := by
  match a with
  | nat.zero => simp
  | nat.inc a₀ =>
    unfold LE.le instLENat_1
    simp

@[simp]
theorem nat.inc_le (a b: nat) : inc a <= b -> a <= b := by
  match b with
  | nat.zero => simp
  | nat.inc b₀ =>
    unfold LE.le instLENat_1
    simp
    intro a_le_b
    have b_le_inc_b := nat.a_le_inc_a b₀
    exact (nat.le_trans a_le_b b_le_inc_b)

@[simp]
theorem nat.lt_inc_to_le {{ a b: nat }} : (a < inc b) = (a <= b) := by
  match a with
  | nat.zero => simp
  | nat.inc a₀ => match b with
    | nat.zero => simp
    | nat.inc b₀ => simp; apply nat.lt_inc_to_le
