import Root2.Nat.Gcd
import Root2.SortedList.Intersection
import Root2.Prime.PrimeFactor
import Root2.Nat.Gcd.Coprime

theorem coprime.of_not_contains
  (f: PrimeFactorization n)
  (not_cont: ¬ contains f.factors x)
  (xprime: x.prime)
  : nat.coprime x n := by
  match nat.prime.to_coprime_or_dvd xprime n with
  | .inl h => exact h
  | .inr dvd_n_x =>
  have := f.is_complete x xprime dvd_n_x
  exact (not_cont this).elim

theorem gcd.factorize_raw :
    ∀
    (afactors: List nat)
    (bfactors: List nat)
    {a b: nat}
    (_: afactors.allP nat.prime) (_: afactors.sorted) (_: a = list_product afactors)
    (_: bfactors.allP nat.prime) (_: bfactors.sorted) (_: b = list_product bfactors)
    (gfactors: List nat) (_: gfactors.allP nat.prime) (_: gfactors.sorted) (_: gcd a b = list_product gfactors),
    gfactors = afactors.intersect_sorted bfactors := by
    apply intersect_sorted.induction
    {
      intro bs'
      intro a b _ _ adef _ _ _ gfactors gprimes _ gdef
      rw [intersect_sorted.empty_right]
      simp at adef
      rw [adef] at gdef 
      rw [gcd.one_left] at gdef
      have := list_product_eq_one gdef.symm
      have := (gfactors.all_and_not_all · this)
      have := this (List.mapAllP gprimes (fun x xprime => (xprime x).right))
      rw [this]
    }
    {
      intro a' as'
      intro a b _ _ _ _ _ bdef gfactors gprimes _ gdef
      rw [intersect_sorted.empty_left]
      simp at bdef
      rw [bdef] at gdef 
      rw [gcd.one_right] at gdef
      have := list_product_eq_one gdef.symm
      have := (gfactors.all_and_not_all · this)
      have := this (List.mapAllP gprimes (fun x xprime => (xprime x).right))
      rw [this]
    }
    {
      intro a' b' as' bs' a'_ord_b' prev
      intro a b aprimes asorted adef bprimes bsorted bdef gfactors gprimes gsorted gdef
      unfold List.intersect_sorted
      simp only; rw [a'_ord_b']; simp
      have : gcd a b = gcd a (list_product bs') := by
        rw [bdef]
        conv => {
          lhs
          unfold list_product
        }
        rw [gcd.comm, gcd.coprime.cancel_left, gcd.comm]
        have := sorted.not_contains asorted a'_ord_b'
        exact coprime.of_not_contains (
          PrimeFactorization.PrimeFactors (a'::as') aprimes asorted adef) this bprimes.left
      rw [this] at gdef
      exact prev aprimes asorted adef bprimes.right (sorted.pop bsorted) rfl gfactors gprimes gsorted gdef
    }
    {
      intro a' b' as' bs' a'_ord_b' prev
      intro a b aprimes asorted adef bprimes bsorted bdef gfactors gprimes gsorted gdef
      unfold List.intersect_sorted
      have a'_eq_b' : a' = b' := Compare.ord_implies_eq a'_ord_b'
      simp only; rw [a'_ord_b']; simp
      simp at gdef
      rw [←a'_eq_b'] at bdef
      have dvd_a : dvd a a' := ⟨ list_product as', adef ⟩
      have dvd_b : dvd b a' := ⟨ list_product bs', bdef ⟩
      have := gcd.of_dvd dvd_a dvd_b
      rw [gdef] at this
      match gfactors with
      | [] =>
        have := dvd.to_eq (dvd.one _) this
        have a'prime := aprimes.left
        rw [this] at a'prime
        exact (nat.prime_implies_not_composite a'prime one_composite).elim
      | g::gfactors' =>
        simp at this
        have g_eq_a' : g = a' := by
          clear prev a'_ord_b'
          apply nat.le_le_to_eq
          have abiggest := nat.biggest_prime_factor (PrimeFactorization.PrimeFactors (a'::as') aprimes asorted adef) rfl
          apply abiggest.right g gprimes.left (dvd.trans (gcd.is_dvd a b).left _)
          rw [gdef]
          exists list_product gfactors'
          exact (nat.biggest_prime_factor (
            PrimeFactorization.PrimeFactors (g::gfactors') gprimes gsorted gdef
          ) rfl).right a' aprimes.left (gcd.of_dvd dvd_a dvd_b)
        congr
        apply prev aprimes.right (sorted.pop asorted) rfl bprimes.right (sorted.pop bsorted) rfl gfactors' gprimes.right (sorted.pop gsorted)
        rw [adef, bdef] at gdef
        simp at gdef
        rw [gcd.mul_left] at gdef
        rw [g_eq_a'] at gdef
        rw [nat.mul_irr] at gdef
        exact gdef
        exact nat.prime_gt_zero aprimes.left
    }
    {
      intro a' b' as' bs' a'_ord_b' prev
      intro a b aprimes asorted adef bprimes bsorted bdef gfactors gprimes gsorted gdef
      unfold List.intersect_sorted
      simp only; rw [a'_ord_b']; simp
      have : gcd a b = gcd (list_product as') b := by
        rw [adef]
        conv => {
          lhs
          unfold list_product
        }
        rw [gcd.coprime.cancel_left]
        have := sorted.not_contains bsorted (Compare.flip a'_ord_b')
        exact coprime.of_not_contains (
          PrimeFactorization.PrimeFactors (b'::bs') bprimes bsorted bdef) this aprimes.left
      rw [this] at gdef
      exact prev aprimes.right (sorted.pop asorted) rfl bprimes bsorted bdef gfactors gprimes gsorted gdef
    }

#print axioms gcd.factorize_raw

theorem gcd.factorize
    {a b: nat}
    (fa: PrimeFactorization a)
    (fb: PrimeFactorization b) 
    (fg: PrimeFactorization (gcd a b)) :
    fg.factors = fa.factors.intersect_sorted fb.factors :=
    match fa with
    | .PrimeFactors afactors aprimes asorted adef =>
    match fb with
    | .PrimeFactors bfactors bprimes bsorted bdef =>
    match fg with
    | .PrimeFactors gfactors gprimes gsorted gdef =>
    gcd.factorize_raw afactors bfactors aprimes asorted adef bprimes bsorted bdef gfactors gprimes gsorted gdef
    
#print axioms gcd.factorize
