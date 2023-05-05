import Root2.Prime
import Root2.Prime.PrimeFactor

theorem a_sq_divis_prime : divisible a b -> divisible (nat.mul a a) b := by
  intro divis_a_b
  have ⟨ m, prf ⟩ := divis_a_b
  exists (nat.mul m (nat.mul b m))
  rw [prf]
  rw [nat.mul_perm2 b m, nat.mul_comm m b]

theorem sq_a_divis_prime : b.prime -> divisible (nat.mul a a) b -> divisible a b := by
  match h:a with
  | nat.zero =>
    intro _ _
    apply divisible.zero
  | nat.inc a₀ => 
  intro b_prime divis_asq_b
  have a_gt_zero := nat.zero_lt_inc a₀
  rw [←h] at *
  have factors := a.factorize a_gt_zero
  have := factors.merge factors
  
  admit