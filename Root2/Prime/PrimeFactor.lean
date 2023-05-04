import Root2.Prime
import Root2.Prime.Factors

instance nat_gt_one {n: nat} : nat.zero.inc < nat.inc (nat.inc n) := by
  rw [nat.lt_inc_irr]
  apply nat.zero_lt_inc

def nat.has_prime_factor (n: nat) {n_gt_one: nat.zero.inc < n} : ∃m, m.prime ∧ divisible n m := by
  match n.classify_prime with
  | .Prime prime _ =>
    exists n
    apply And.intro
    assumption
    exact divisible.id n
  | .Composite _ composite =>
    have ⟨ a, factor ⟩ := composite
    match factor with
    | .inr n_eq_one =>
      rw [n_eq_one] at n_gt_one
      contradiction
    | .inl factor =>
    have ⟨ ⟨ b, n_eq_ab ⟩ , ⟨ a_ne_one, n_ne_a ⟩  ⟩ := factor
    match nat.zero.inc.compare_lt a, nat.zero.inc.compare_lt b with
    | .isFalse h₀, .isFalse h₁ => 
      rw [nat.not_lt_is_sym_le_op] at *
      match a, b with
      | nat.zero, nat.zero => simp at n_eq_ab; rw [n_eq_ab] at n_gt_one; contradiction
      | nat.zero, nat.inc nat.zero => simp at n_eq_ab; rw [n_eq_ab] at n_gt_one; contradiction
      | nat.inc nat.zero, nat.zero => simp at n_eq_ab; rw [n_eq_ab] at n_gt_one; contradiction
      | nat.inc nat.zero, nat.inc nat.zero => simp at n_eq_ab; rw [n_eq_ab] at n_gt_one; contradiction
    | .isTrue h₀, .isFalse h₁ =>
      rw [nat.not_lt_is_sym_le_op] at *
      match b with
      | nat.zero => simp at n_eq_ab; rw [n_eq_ab, nat.mul_zero_r] at n_gt_one; contradiction
      | nat.inc nat.zero => 
        rw [nat.mul_one_r] at n_eq_ab
        contradiction
    | .isFalse h₀, .isTrue h₁ =>
      rw [nat.not_lt_is_sym_le_op] at *
      match a with
      | nat.zero => simp at n_eq_ab; rw [n_eq_ab] at n_gt_one; contradiction
      | nat.inc nat.zero => 
        rw [nat.mul_one] at n_eq_ab
        contradiction
    | .isTrue h₀, .isTrue h₁ =>
      have ⟨ f, f_prime, is_factor ⟩  := @has_prime_factor a h₀
      exists f
      apply And.intro
      assumption
      rw [n_eq_ab]
      apply divisible.mul
      assumption
  decreasing_by {
    simp_wf
    apply nat.size_of_lt
    rw [nat.mul_comm] at n_eq_ab
    have := nat.mul_imp_le (nat.lt_trans (nat.zero_lt_inc _) h₁) (nat.eq_to_le (Eq.symm n_eq_ab))
    apply nat.ne_and_le_to_lt
    apply Ne.symm
    assumption
    assumption
  }

inductive PrimeFactorization : nat -> Type :=
  | One : PrimeFactorization nat.zero.inc
  | Succ : ∀{{n m: nat}},
      nat.prime n ->
      PrimeFactorization m
      -> PrimeFactorization (nat.mul m n)

def prime_factor_list (p: PrimeFactorization n) : List nat := match p with
  | .One => []
  | @PrimeFactorization.Succ f _ _ p => f :: prime_factor_list p


instance : Repr (PrimeFactorization n) where
  reprPrec n := reprPrec (prime_factor_list n)


def sorted (p: PrimeFactorization n): Prop := match p with
  | .One => True
  | @PrimeFactorization.Succ n₀ _ _ prev => match prev with
    | .One => True
    | @PrimeFactorization.Succ n₁ _ _ prev_prev => sorted prev ∧ n₁ < n₀

inductive SortedPrimeFactorization (n: nat) : Type := 
  | Factors : (p: PrimeFactorization n) -> sorted p -> SortedPrimeFactorization n

def merge_factors {{a b: nat}} (pa: PrimeFactorization a) (pb: PrimeFactorization b) : PrimeFactorization (nat.mul a b) := by
  
  admit

def nat.factorize (n: nat) (_: nat.zero < n) : PrimeFactorization n := 
  match h:n with
  | nat.inc nat.zero => PrimeFactorization.One
  | nat.inc (nat.inc n₀) => by
    rw [←h]
    match n.classify_prime with
    | .Prime p _ => 
      have factors := PrimeFactorization.Succ p PrimeFactorization.One
      rw [nat.mul_one] at factors
      assumption
    | .Composite _ composite =>
      
      match n.get_factors (plus_two_gt_one h) composite with
      | .MkFactors a b a_gt_one b_gt_one _ _ n_eq_ab =>

      have a_gt_zero := nat.lt_trans (nat.zero_lt_inc _) a_gt_one
      have b_gt_zero := nat.lt_trans (nat.zero_lt_inc _) b_gt_one
      
      have a_factors := a.factorize a_gt_zero
      have b_factors := b.factorize b_gt_zero

      rw [n_eq_ab]
      exact (merge_factors a_factors b_factors)
  decreasing_by {
    simp_wf
    apply nat.size_of_lt
    rw [←h] 
    assumption
  }
-- #eval prime_factor_list (factorize nat.zero.inc.inc (nat.zero_lt_inc _))
