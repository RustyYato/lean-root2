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

theorem nat.le_mul_irr2 (a b c d: nat) (a_le_c: a <= c) (b_le_d: b <= d) : (mul a b <= mul c d) := by
  match c with
  | .zero =>
    have a_eq_zero := nat.le_zero a a_le_c
    rw [a_eq_zero]
    simp
  | .inc c₀ =>
  match a with
  | .zero =>
    simp
    apply nat.zero_le
  | .inc a₀ =>
  rw [nat.le_inc_irr] at a_le_c
  apply nat.le_add_irr2
  assumption
  apply nat.le_mul_irr2 <;> assumption

theorem nat.mul_le : a <= b -> mul c a <= mul c b := by
  intro a_le_b 
  match c with
  | .zero => rw [nat.mul_zero, nat.mul_zero]; exact nat.le_id _
  | .inc c₀ =>
    rw [nat.mul_inc, nat.mul_inc]
    apply nat.le_add_irr2
    assumption
    apply nat.mul_le a_le_b

theorem nat.add_le_cmp (m: nat.add a b = nat.add c d) : c ≤ a -> b <= d := by
  intro c_le_a
  match a with
  | .zero => 
    have c_eq_zero : c = nat.zero := nat.le_zero _ c_le_a
    rw [c_eq_zero] at m
    simp at m
    rw [m]
    apply nat.le_id
  | .inc a₀ =>
  match b with
  | .zero =>
    apply nat.zero_le
  | .inc b₀ =>
  match c with
  | .zero => 
    rw [nat.add_zero] at m
    rw  [←m]
    rw [nat.add_comm]
    exact nat.a_less_a_plus_b b₀.inc a₀.inc
  | .inc c₀ =>
  match d with
  | .zero =>
    rw [nat.add_zero_r] at m
    simp at m
    rw [nat.le_inc_irr] at c_le_a
    rw [←m] at c_le_a
    have := a₀.a_lt_a_plus_b b₀
    have := @Compare.not_lt_and_le nat _ _ _ this c_le_a
    contradiction
  | .inc d₀ =>
  simp at m
  rw [nat.add_inc, nat.add_inc, nat.eq_inc_irr] at m
  rw [nat.le_inc_irr]
  rw [nat.le_inc_irr] at c_le_a
  apply nat.add_le_cmp <;> assumption

theorem nat.mul_le_cmp (m: nat.mul a b <= nat.mul c d) : nat.zero < a -> nat.zero < b -> c ≤ a -> b <= d := by
  intro a_ne_zero b_ne_zero c_le_a
  match h₄:a with
  | .inc a₀ =>
  match h₂:b with
  | .inc b₀ =>
  clear a_ne_zero 
  match h₀:c with
  | .zero => simp at m
  | .inc c₀ =>
  match h₁:d with
  | .zero =>
    rw [nat.mul_zero_r] at m
    simp at m
  | .inc d₀ =>
  rw [←h₀] at m
  rw [←h₁] at m
  rw [←h₂] at m
  rw [←h₁]
  rw [←h₂]
  simp at m
  match h₃:a₀ with
  | nat.zero =>
    rw [nat.mul_zero, nat.add_zero_r] at m
    rw [h₀] at m
    match c₀ with
    | .zero =>
    rw [nat.mul_one] at m
    assumption
  | nat.inc a₁ =>
  have := (mul a₁.inc b).a_less_a_plus_b b
  rw [nat.add_comm] at this
  have := nat.le_trans this m
  rw [←h₂] at b_ne_zero
  rw [←h₃, ←h₀] at c_le_a
  match c_le_a with
  | .inr c_eq_a =>
    repeat clear this
    rw [←nat.mul_inc, ←h₄] at m
    rw [h₃, ←h₄] at c_eq_a
    have c_eq_a : c = a := Compare.ord_implies_eq c_eq_a
    rw [c_eq_a] at m
    rw [←h₃] at h₄
    rw [h₄] at m
    rw [nat.mul_le_irr (nat.zero_lt_inc _)] at m
    assumption
  | .inl c_lt_a =>
  apply @nat.mul_le_cmp a₁.inc b c d this (nat.zero_lt_inc _) b_ne_zero
  rw [←nat.lt_inc_to_le]
  apply Compare.ord_implies_lt
  rw [h₃] at c_lt_a
  assumption