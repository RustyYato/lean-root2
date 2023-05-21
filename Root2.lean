import Root2.Divisible.DivRem
import Root2.Prime.PrimeFactor
import Root2.Nat.Reduction
import Root2.Nat.Gcd
import Root2.Nat.Gcd.Coprime
import Root2.Nat.Gcd.PrimeFactor

def two_prime : nat.prime nat.zero.inc.inc := by decide

#print axioms two_prime

theorem distr_terms : (nat.mul (nat.add a b) (nat.add a b)) = nat.add (nat.mul a a) (nat.add (nat.mul nat.zero.inc.inc (nat.mul a b)) (nat.mul b b)) := by
  repeat rw [nat.mul_add]
  repeat rw [nat.add_mul]
  repeat rw [nat.mul_inc]
  repeat rw [nat.add_mul]
  repeat rw [nat.mul_add]
  repeat rw [nat.add_mul]
  rw [
    ←nat.add_perm0,
    nat.add_irr,
    ←nat.add_perm0,
    nat.mul_comm,
    nat.add_irr,
    nat.mul_zero,
    nat.add_zero_r
  ]

theorem sq_dvd_two_implies_dvd_two : dvd (nat.mul a a) nat.zero.inc.inc -> dvd a nat.zero.inc.inc := by
  intro sq_dvd
  apply Decidable.byContradiction
  intro not_dvd
  have dr := divrem.calc a nat.zero.inc.inc (nat.zero_lt_inc _)
  have rem_gt_zero := dr.not_dvd_remainder not_dvd
  rw [←dr.def, distr_terms] at sq_dvd
  have sq_dvd := dvd.cancel_right sq_dvd (by
    generalize (nat.mul (divrem.remainder dr) (nat.mul (divrem.quocient dr) (nat.inc (nat.inc nat.zero)))) = g₀
    generalize divrem.quocient dr = g₁
    generalize h:nat.zero.inc.inc = two
    clear sq_dvd rem_gt_zero dr not_dvd a
    rw [←nat.mul_perm2]
    rw [←nat.mul_add, nat.mul_comm]
    exact dvd.mul_left _ _)
  have := dr.remainder_lt
  match h:dr.remainder with
  | .zero =>
    rw [h] at rem_gt_zero
    contradiction
  | .inc (.inc a₀) =>
    rw [h] at this
    rw [nat.lt_inc_irr, nat.lt_inc_irr] at this
    have := nat.not_lt_zero _ this
    contradiction
  | .inc .zero => 
  rw [h, nat.mul_one] at sq_dvd
  have ⟨ x, prf ⟩ := sq_dvd
  match x with
  | .zero => rw [nat.mul_zero_r] at prf; contradiction
  | .inc x₀ =>
    rw [nat.mul_inc_r] at prf
    have := nat.zero.inc.a_lt_inc_a
    have := nat.lt_le_trans this (nat.a_le_a_plus_b nat.zero.inc.inc (nat.mul  nat.zero.inc.inc x₀))
    rw [←prf] at this
    have := nat.not_lt_id nat.zero.inc
    contradiction

#print axioms sq_dvd_two_implies_dvd_two

theorem root2_is_irrational_given_coprime : ∀ a b: nat, nat.coprime a b -> (nat.mul a a) = (nat.mul nat.zero.inc.inc (nat.mul b b)) -> False := by
  intro a b cp a_sq_eq_2_b_sq
  have dvd_a_two : dvd a nat.zero.inc.inc := sq_dvd_two_implies_dvd_two (by
    have := dvd.mul_right (nat.inc (nat.inc nat.zero)) (nat.mul b b)
    rw [←a_sq_eq_2_b_sq] at this
    exact this)
  
  have ⟨ x, prf ⟩ := dvd_a_two
  rw [prf] at a_sq_eq_2_b_sq
  rw [←nat.mul_perm0] at a_sq_eq_2_b_sq
  rw [nat.mul_irr (nat.zero_lt_inc _)] at a_sq_eq_2_b_sq
  have a_sq_eq_2_b_sq := a_sq_eq_2_b_sq.symm
  rw [nat.mul_perm7] at a_sq_eq_2_b_sq

  have dvd_b_two : dvd b nat.zero.inc.inc := sq_dvd_two_implies_dvd_two (by
    have := dvd.mul_right (nat.inc (nat.inc nat.zero)) (nat.mul x x)
    rw [←a_sq_eq_2_b_sq] at this
    exact this)
  
  exact cp.no_common_dvd nat.zero.inc.inc (nat.a_lt_inc_a _) dvd_a_two dvd_b_two
