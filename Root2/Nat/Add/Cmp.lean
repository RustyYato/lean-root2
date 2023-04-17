import Root2.Nat.Add
import Root2.Nat.Cmp

@[simp]
theorem nat.a_less_a_plus_b (a b: nat) : a <= add a b := by
  match a with
  | nat.zero => simp
  | nat.inc a₀ => simp; apply nat.a_less_a_plus_b

@[simp]
theorem nat.add_imp_le {{a b c: nat}} : add a b <= c -> b <= c := by
  match a with
  | nat.zero => simp; exact id
  | nat.inc a₀ =>
    simp
    intro inc_add_le_c
    have qq := nat.inc_le (add a₀ b) c
    exact (nat.add_imp_le (qq inc_add_le_c))

@[simp]
theorem nat.le_add_irr (a b c: nat) : add a b <= add a c -> b <= c := by
  match a with
  | nat.zero => simp; exact id
  | nat.inc a₀ => simp; intro; apply nat.le_add_irr; assumption
