import Root2.Divisible.DivRem

theorem root2_is_irrational : ∀ a b: nat, (nat.mul a a) = (nat.mul 2 (nat.mul b b)) -> False := by
  intro a b a_sq_eq_2_b_sq

  -- match b with
  -- | nat.zero => admit
  -- | 
  admit