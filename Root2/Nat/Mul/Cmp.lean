import Root2.Nat.Mul
import Root2.Nat.Cmp
import Root2.Nat.Add.Cmp

@[simp]
theorem nat.a_le_a_mul_b (a b: nat) (b_nz : nat.zero < b) : a <= mul a b := by
  match b with
  | nat.zero => simp; contradiction
  | nat.inc b₀ => simp

-- @[simp]
-- theorem nat.mul_imp_le {{a b c: nat}} (a_nz: nat.zero < a) : mul a b <= c -> b <= c := by
--   match a with
--   | nat.zero => simp; exact id
--   | nat.inc a₀ =>
--     simp
--     intro inc_add_le_c
--     have qq := nat.inc_le (add a₀ b) c
--     exact (nat.add_imp_le (qq inc_add_le_c))
