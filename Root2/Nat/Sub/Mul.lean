import Root2.Nat.Mul.Cmp
import Root2.Nat.Sub.Add

theorem nat.mul_sub_left (a b c: nat) : ∀ h₀ h₁, mul a (b.checked_sub c h₀) = (mul a b).checked_sub (mul a c) h₁ := by
  intro h₀ h₁

  match a with
  | nat.zero =>
  repeat rw [nat.mul_zero]
  trivial
  | nat.inc a₀ =>
  rw [nat.mul_inc, nat.mul_sub_left a₀]
  have := @nat.sub_equality_left (mul (inc a₀) b) (add b (mul a₀ b)) (mul (inc a₀) c)
    (by rw [nat.mul_inc]) (by assumption) (by rw [←nat.mul_inc]; assumption)
  rw [this]
  clear this
  have := @nat.sub_equality_right (mul (inc a₀) c) (add c (mul a₀ c)) (add b (mul a₀ b))
    (by rw [nat.mul_inc]) (by assumption) (by rw [←nat.mul_inc]; assumption)
  rw [this]
  clear this
  rw [nat.add_sub_assoc]
  rw [nat.mul_le_irr (nat.zero_lt_inc a₀)] at h₁
  apply nat.mul_le h₁

theorem nat.mul_sub_right (a b c: nat) : ∀ h₀ h₁, mul (b.checked_sub c h₀) a = (mul b a).checked_sub (mul c a) h₁ := by
  intro h₀ h₁
  rw [nat.mul_comm]
  rw [nat.mul_sub_left]
  apply nat.add_to_sub
  rw [nat.mul_comm a]
  rw [nat.sub_add_inv]
  apply nat.mul_comm