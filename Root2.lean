import Root2.Divisible.DivRem
import Root2.Prime.PrimeFactor
import Root2.Nat.Reduction
import Root2.Nat.Gcd
import Root2.Nat.Gcd.PrimeFactor

theorem root2_is_irrational : ∀ a b: nat, (nat.mul a a) = (nat.mul nat.zero.inc.inc (nat.mul b b)) -> False := by
  intro a b a_sq_eq_2_b_sq
  
  -- match b with
  -- | nat.zero => admit
  -- | 
  admit