import Root2.Nat.Gcd
import Root2.Divisible
import Root2.Prime

theorem nat.coprime.cancel_left (cp: nat.coprime a c) (d: dvd (nat.mul a b) c) : dvd b c := by
  have g := gcd.of_dvd (dvd.mul_left b c) d
  rw [nat.mul_comm a b, gcd.mul_left,
      gcd.comm, cp.to_gcd, nat.mul_one_r] at g
  assumption

#print axioms nat.coprime.cancel_left

theorem nat.coprime.cancel_right (cp: nat.coprime b c) (d: dvd (nat.mul a b) c) : dvd a c := by
  rw [nat.mul_comm] at d
  apply cp.cancel_left d

#print axioms nat.coprime.cancel_right

theorem nat.prime.to_coprime_or_dvd (p: nat.prime n) : ∀m, nat.coprime n m ∨ dvd m n := by
  intro m
  have ⟨ _, _ ⟩  := gcd.is_dvd n m
  match (p (gcd n m)).left with
  | .inl _ => contradiction
  | .inr (.inl gcd_eq_one) =>
    rw [gcd.bounded_eq] at gcd_eq_one
    apply Or.inl
    assumption
  | .inr (.inr n_eq_gcd) =>
    apply Or.inr
    rw [n_eq_gcd]
    assumption

#print axioms nat.prime.to_coprime_or_dvd

theorem nat.prime.to_coprime_or_eq (pn: nat.prime n) (pm: nat.prime m) : nat.coprime n m ∨ n = m := by
  cases nat.prime.to_coprime_or_dvd pn m
  apply Or.inl
  assumption
  match (pm n).left with
  | .inr (.inr m_eq_n) => exact Or.inr m_eq_n.symm
  | .inr (.inl gcd_eq_one) => exact ((nat.prime_ne_one pn) gcd_eq_one).elim
  | .inl _ => contradiction

#print axioms nat.prime.to_coprime_or_eq
