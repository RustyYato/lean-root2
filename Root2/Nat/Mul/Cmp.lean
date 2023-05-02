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
