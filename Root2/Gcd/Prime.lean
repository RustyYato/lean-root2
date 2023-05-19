import Root2.Gcd
import Root2.Prime

theorem Gcd.of_prime (p: nat.prime n) :
  ∀x, ∀g: Gcd x n, (¬ dvd x n ∧ g.eval = nat.zero.inc) ∨ dvd x n := by
  intro x g
  match x.is_dvd n with
  | .isTrue x_eq_n => apply Or.inr; assumption
  | .isFalse x_ne_n =>
    apply Or.inl
    apply And.intro
    assumption

    match h:g.eval with
    | .zero =>
      rw [Gcd.eq_zero] at h
      have ⟨ x_eq_zero, n_eq_zero ⟩ := h
      rw [n_eq_zero] at p
      contradiction
    | .inc .zero => rfl
    | .inc (.inc _) =>
      apply False.elim
      have ⟨ _, dvd_n ⟩  := g.implies_dvd (dvd.id _)
      have ⟨ not_dvd, _ ⟩ := p g.eval
      match not_dvd with
      | .inl _ => contradiction
      | .inr (.inl h₀) =>
        rw [h₀] at h
        rw [nat.eq_inc_irr] at h
        contradiction
      | .inr (.inr h) =>
        have := g.eq_implies_dvd h.symm
        contradiction

theorem gcd.of_prime (p: nat.prime n) :
  ∀x, (¬ dvd x n ∧ gcd x n = nat.zero.inc) ∨ dvd x n := by
  intro x
  exact Gcd.of_prime p x (Gcd.calc x n)

theorem gcd.between_primes (p: nat.prime n) (q: nat.prime m) :
  (¬ n = m ∧ gcd m n = nat.zero.inc) ∨ n = m := by
  match gcd.of_prime p m with
  | .inl ⟨ not_dvd, gcd_eq_one ⟩  =>
    apply Or.inl
    apply And.intro
    intro n_eq_m
    apply not_dvd
    exists nat.zero.inc
    rw [nat.mul_one_r, n_eq_m]
    assumption
  | .inr m_dvd_n =>
    apply Or.inr
    match (q n).left with
    | .inl h => contradiction
    | .inr (.inl h) =>  
      have := nat.prime_ne_one p
      contradiction
    | .inr (.inr h) =>  
      exact h.symm

theorem gcd.between_different_primes (p: nat.prime n) (q: nat.prime m) :
  ¬ n = m -> gcd m n = nat.zero.inc := match gcd.between_primes p q with
  | .inl ⟨ _, cond ⟩ => fun _ => cond
  | .inr n_eq_m => fun not_n_eq_m => (not_n_eq_m n_eq_m).elim
