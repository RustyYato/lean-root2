import Root2.Prime
import Root2.Prime.PrimeFactor

theorem a_sq_dvd_prime : dvd a b -> dvd (nat.mul a a) b := by
  intro dvd_a_b
  have ⟨ m, prf ⟩ := dvd_a_b
  exists (nat.mul m (nat.mul b m))
  rw [prf]
  rw [nat.mul_perm2 b m, nat.mul_comm m b]

theorem sq_a_dvd_prime : b.prime -> dvd (nat.mul a a) b -> dvd a b := by
  match h:a with
  | nat.zero =>
    intro _ _
    apply dvd.zero
  | nat.inc a₀ => 
  intro b_prime dvd_asq_b
  have a_gt_zero := nat.zero_lt_inc a₀
  rw [←h] at *
  have factors := a.factorize a_gt_zero
  have := factors.merge factors
  
  admit
