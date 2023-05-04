import Root2.Nat.Add
import Root2.Nat.Cmp

theorem nat.a_less_a_plus_b (a b: nat) : a <= add a b := by
  match a with
  | nat.zero => apply nat.zero_le
  | nat.inc a₀ =>
    rw [nat.add_inc_r, nat.le_inc_irr]
    apply nat.a_less_a_plus_b

theorem nat.le_add_irr (a b c: nat) : (add a b <= add a c) = (b <= c) := by
  match a with
  | nat.zero => simp
  | nat.inc a₀ =>
  simp
  apply nat.le_add_irr a₀

theorem nat.add_imp_le {{a b c: nat}} : add a b <= c -> b <= c := by
  match a with
  | nat.zero => rw [nat.add_zero]; exact id
  | nat.inc a₀ =>
    intro inc_add_le_c
    have qq := nat.inc_le (add a₀ b) c
    exact (nat.add_imp_le (qq inc_add_le_c))

theorem nat.add_eq_imp_le {{a b c: nat}} : add a b = c -> a <= c := by
  match b with
  | nat.zero => rw [nat.add_zero_r]; apply nat.eq_to_le
  | nat.inc b₀ =>
    intro inc_add_le_c
    have q := inc_add_le_c
    rw [nat.add_inc] at inc_add_le_c
    have := nat.inc_le _ _ (nat.eq_to_le inc_add_le_c)
    apply @nat.add_imp_le b₀ a c
    rw [nat.add_comm]
    assumption

theorem nat.add_gt_zero {{a: nat}} : nat.zero < a -> ∀b, nat.zero < a.add b := by
  intro a_gt_zero
  intro b
  cases a
  contradiction
  rw [nat.add_inc_r]
  trivial