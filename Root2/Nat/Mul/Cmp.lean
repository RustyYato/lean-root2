import Root2.Nat.Mul
import Root2.Nat.Cmp
import Root2.Nat.Add.Cmp

theorem nat.a_le_a_mul_b (a b: nat) (b_nz : nat.zero < b) : a <= mul a b := by
  match b with
  | nat.zero => simp; contradiction
  | nat.inc b₀ =>
    rw [nat.mul_inc_r]
    apply nat.a_less_a_plus_b

theorem nat.mul_imp_le {{a b c: nat}} (a_nz: nat.zero < a) : mul a b <= c -> b <= c := by
  match a with
  | nat.zero => contradiction
  | nat.inc a₀ =>
    simp
    intro inc_add_le_c
    rw [nat.add_comm] at inc_add_le_c
    exact nat.add_imp_le inc_add_le_c

theorem nat.mul_output_imp_le {{a b c: nat}} (c_nz: nat.zero < c) : mul a b = c -> a <= c := by
  match b with
  | nat.zero =>
    rw [nat.mul_zero_r]
    intro x
    rw [←x] at c_nz
    contradiction
  | nat.inc b₀ =>
    simp
    intro inc_add_eq_c
    rw [nat.mul_inc_r] at inc_add_eq_c
    exact (nat.add_eq_imp_le inc_add_eq_c)

theorem nat.mul_nonzero {{a b c: nat}} (c_nz: nat.zero < c) : mul a b = c -> nat.zero < a ∧ nat.zero < b := by
  match a with
  | nat.zero =>
    rw [nat.mul_zero]
    intro x
    rw [←x] at c_nz
    contradiction
  | nat.inc a₀ =>
    match b with
    | nat.zero =>
      rw [nat.mul_zero_r]
      intro x
      rw [←x] at c_nz
      contradiction
    | nat.inc b₀ =>
    intro
    apply And.intro <;> apply nat.zero_lt_inc

theorem nat.mul_output_ne {{a b c: nat}} (a_gt_one: nat.zero.inc < a) (b_gt_one: nat.zero.inc < b) : c =mul a b -> a ≠ c := by
  match a with
  | nat.zero => contradiction
  | nat.inc nat.zero => contradiction
  | nat.inc (nat.inc a₀) =>
  match b with
  | nat.zero => contradiction
  | nat.inc nat.zero => contradiction
  | nat.inc (nat.inc b₀) =>
    simp
    intro inc_add_eq_c
    intro a_eq_c
    rw [←a_eq_c] at inc_add_eq_c
    rw [
      nat.mul_inc_r,
      nat.add_inc,
      nat.add_inc,
      nat.eq_inc_irr,
      nat.eq_inc_irr,
      nat.add_perm9 b₀,
      ←nat.add_perm0,
      ←nat.add_inc,
      ←nat.add_inc,
      nat.eq_add_const_irr
    ] at inc_add_eq_c
    contradiction

theorem nat.mul_output_lt {{a b c: nat}} (a_gt_one: nat.zero.inc < a) (b_gt_one: nat.zero.inc < b) : c = mul a b -> a < c := by
  match a with
  | nat.zero => contradiction
  | nat.inc nat.zero => contradiction
  | nat.inc (nat.inc a₀) =>
  match b with
  | nat.zero => contradiction
  | nat.inc nat.zero => contradiction
  | nat.inc (nat.inc b₀) =>
    intro inc_add_eq_c
    rw [inc_add_eq_c]
    rw [
      nat.mul_inc_r,
      nat.add_inc_r,
      nat.add_inc_r,
      nat.lt_inc_irr,
      nat.lt_inc_irr,
      nat.lt_add_const_irr
    ]
    apply nat.zero_lt_inc

theorem nat.mul_le_irr_r {{a b c: nat}} : b <= c -> mul a b <= mul a c := by
  intro b_le_c
  match a with
  | .zero =>
    rw [nat.mul_zero, nat.mul_zero]; exact nat.le_id _
  | .inc a₀ =>
    rw [nat.mul_inc, nat.mul_inc]
    have := @nat.mul_le_irr_r a₀ b c b_le_c
    apply nat.le_add_irr2
    assumption
    assumption

theorem nat.mul_le_irr_l {{a b c: nat}} (a_gt_zero: nat.zero < a) : mul a b <= mul a c -> b <= c := by
  match b with
  | nat.zero => 
  rw [nat.mul_zero_r]
  cases c
  rw [nat.mul_zero_r]
  exact id
  intro
  exact nat.zero_le _
  | nat.inc b₀ =>
  rw [nat.mul_inc_r]
  match c with
  | nat.zero =>
    rw [nat.mul_zero_r]
    intro x
    match a with
    | .inc a₀ => 
    rw [nat.add_inc_r] at x
    cases x <;> contradiction
  | .inc c₀ => 
    simp
    rw [nat.mul_inc_r, nat.le_add_irr]
    intro h
    rw [nat.le_inc_irr]
    apply @nat.mul_le_irr_l a _ _ a_gt_zero
    assumption

theorem nat.mul_le_irr {{a b c: nat}} (a_gt_zero: nat.zero < a) : (mul a b <= mul a c) = (b <= c) := by
  rw [Iff.intro (nat.mul_le_irr_l a_gt_zero) (@nat.mul_le_irr_r a b c)]

theorem nat.mul_le : a <= b -> mul c a <= mul c b := by
  intro a_le_b 
  match c with
  | .zero => rw [nat.mul_zero, nat.mul_zero]; exact nat.le_id _
  | .inc c₀ =>
    rw [nat.mul_inc, nat.mul_inc]
    apply nat.le_add_irr2
    assumption
    apply nat.mul_le a_le_b