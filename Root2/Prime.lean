import Root2.Divisible.DivRem

def nat.prime_cond (n m: nat) : Prop := ((¬divisible n m) ∨ m = nat.zero.inc ∨ n = m) ∧ n ≠ nat.zero.inc
def nat.prime (n: nat) : Prop := ∀ m, prime_cond n m

@[simp]
def nat.is_factor (n m: nat) := (divisible n m ∧ m ≠ nat.zero.inc ∧ n ≠ m) ∨ n = nat.zero.inc
@[simp]
def nat.composite (n: nat) : Prop := ∃ m, nat.is_factor n m

@[simp]
def nat.prime_until (n o: nat) : Prop := ∀ m, m < o -> prime_cond n m

@[simp]
def nat.has_smaller_factor (n o: nat) : Prop := ∃ m, m <= o ∧ is_factor n m

inductive PrimeClassifier (n: nat) where
| Prime : nat.prime n -> ¬nat.composite n -> PrimeClassifier n
| Composite : ¬ nat.prime n -> nat.composite n -> PrimeClassifier n

theorem not_prime_and_composite {{n:nat}} (p: nat.prime n) (c: nat.composite n) : False := by
  let ⟨ m, cond ⟩ := c
  let ⟨ divis_cond, n_not_one ⟩ := p m

  match cond with
  | .inl cond₀ => 
    let ⟨ divis, ⟨ m_ne_one, m_ne_n ⟩  ⟩ := cond₀
    match divis_cond with
    | .inl con => contradiction
    | .inr (.inl con) => contradiction
    | .inr (.inr con) => contradiction
  | .inr x => contradiction

theorem nat.prime_implies_not_composite {{n:nat}} (p: nat.prime n) : ¬ nat.composite n := 
  fun c => not_prime_and_composite p c
theorem nat.composite_implies_not_prime {{n:nat}} (c: nat.composite n) : ¬ nat.prime n := 
  fun p => not_prime_and_composite p c

def nat.has_smaller_factor_dec (x n: nat) (n_gt_one: nat.zero.inc < n) : Decidable (nat.has_smaller_factor n x) := by
  match h₀:n with
  | nat.inc (nat.inc n₀) => 
  match h₁:x with
  | nat.zero => 
    apply Decidable.isFalse
    intro no_smaller_factor
    have ⟨ x, ⟨ x_le_zero, zero_divides_n ⟩  ⟩ := no_smaller_factor
    have x_eq_zero := nat.le_zero x x_le_zero
    rw [x_eq_zero] at zero_divides_n
    match zero_divides_n with
    | .inl zero_factor =>
    have ⟨ ⟨ m, divis_zero ⟩, ⟨ _, _ ⟩ ⟩  := zero_factor
    rw [nat.mul_zero] at divis_zero
    contradiction
  | nat.inc nat.zero =>
    apply Decidable.isFalse
    intro no_smaller_factor
    have ⟨ q, ⟨ q_le_one, q_divides_n ⟩  ⟩ := no_smaller_factor
    match q_divides_n with
    | .inl q_factor =>
    have ⟨ ⟨ m, divis_q ⟩, ⟨ _, _ ⟩ ⟩  := q_factor
    match q with
    | nat.zero => contradiction
    | nat.inc nat.zero => contradiction
    | nat.inc (nat.inc _) => contradiction
  | nat.inc (nat.inc x₀) =>
    rw [←h₀] at n_gt_one
    match x₀.inc.has_smaller_factor_dec n n_gt_one with
    | .isTrue smaller =>
      apply Decidable.isTrue
      have ⟨ m, ⟨ m_le_x₀, is_factor_n_m ⟩  ⟩  := smaller
      exists m
      apply And.intro
      exact (nat.le_trans m_le_x₀ (nat.a_le_inc_a _))
      rw [← h₀]
      assumption
    | .isFalse no_smaller =>
    match n.compare_eq x with
    | .isTrue n_eq_x =>
      rw [←h₀, ←h₁]
      apply Decidable.isFalse
      intro smaller_factor
      have ⟨ q, ⟨ q_le_x, is_factor_n_q ⟩ ⟩ := smaller_factor
      match is_factor_n_q with
      | .inl h =>
        have ⟨ _, ⟨ _, n_ne_q ⟩ ⟩ := h
        rw [n_eq_x] at n_ne_q
        have q_lt_x := nat.ne_and_le_to_lt (Ne.symm n_ne_q) q_le_x
        apply no_smaller
        exists q
        rw [h₁, nat.lt_inc_to_le] at q_lt_x
        apply And.intro
        assumption
        assumption
      | .inr h => 
        rw [h₀] at h
        rw [nat.eq_inc_irr] at h
        contradiction
    | .isFalse n_ne_x =>
    match n.is_divisible x with
    | .isTrue divis_x =>
      rw [←h₀, ←h₁]
      apply Decidable.isTrue
      exists x
      apply And.intro
      apply nat.le_id
      apply Or.inl
      apply And.intro
      assumption
      apply And.intro
      rw [h₁]
      intro x
      rw [nat.eq_inc_irr] at x
      contradiction
      intro x
      contradiction
    | .isFalse not_divis_x =>
      apply Decidable.isFalse
      rw [←h₀, ←h₁]
      intro smaller_factor
      have ⟨ q, ⟨ q_le_x, is_factor_n_q ⟩ ⟩ := smaller_factor
      match q.compare_eq x with
      | .isTrue q_eq_x =>
        rw [q_eq_x] at is_factor_n_q
        match is_factor_n_q with
        | .inl h =>
          have ⟨ _, _ ⟩ := h
          contradiction
        | .inr h =>
          rw [h₀, nat.eq_inc_irr] at h
          contradiction
      | .isFalse h =>
        have q_lt_x := nat.ne_and_le_to_lt (Ne.intro h) q_le_x
        apply no_smaller
        unfold has_smaller_factor
        exists q
        rw [h₁, nat.lt_inc_to_le] at q_lt_x
        apply And.intro
        assumption
        assumption

instance nat.classify_prime : PrimeClassifier n := by
  match h:n with
  | nat.zero =>
    apply PrimeClassifier.Composite
    {
      -- zero is not prime
      intro prime
      have ⟨ not_divis, _ ⟩  := prime nat.zero.inc.inc
      match not_divis with
      | .inl not_divis =>
      apply not_divis
      apply divisible.zero
    }
    {
      -- zero is composite
      exists nat.zero.inc.inc
      simp
      exists nat.zero
    }
  | nat.inc nat.zero =>
    apply PrimeClassifier.Composite
    {
      -- one is not prime
      intro prime
      have ⟨ _, _ ⟩  := prime nat.zero
      contradiction
    }
    {
      -- one is composite
      simp
      exists nat.zero
    }
  | nat.inc (nat.inc n₀) =>
  have has_smaller_factor := n.has_smaller_factor_dec n (by
    rw [h, nat.lt_inc_irr]
    apply nat.zero_lt_inc
    )
  rw [←h]
  match has_smaller_factor with
  | .isTrue smaller_factor =>
    apply PrimeClassifier.Composite
    all_goals have ⟨ m, ⟨ _, prf ⟩  ⟩ := smaller_factor
    {
      -- n is not prime
      intro prime
      have ⟨ not_divis, _ ⟩  := prime m
      unfold nat.is_factor at prf

      match prf with
      | .inr prf => rw [prf] at h; contradiction
      | .inl prf => 
      have ⟨ divi, m_not_one, m_not_n ⟩ := prf 
      -- cases not_divis <;> contradiction
      match not_divis with
      | .inl not_divis => contradiction
      | .inr (.inl x) => contradiction
      | .inr (.inr x) => contradiction
    }
    {
      -- n is composite
      exists m
    }
  | .isFalse no_smaller_factor =>
    apply PrimeClassifier.Prime
    {
      -- n is prime
      intro m
      unfold nat.prime_cond
      apply And.intro
      {
        unfold nat.has_smaller_factor nat.is_factor at no_smaller_factor
        match n.compare_eq m with
        | .isTrue n_eq_m =>
          repeat apply Or.inr
          assumption
        | .isFalse n_ne_m =>
        match m.compare_eq nat.zero.inc with
        | .isTrue m_eq_one =>
          apply Or.inr
          apply Or.inl
          assumption
        | .isFalse m_ne_one =>
          apply Or.inl
          intro divis
          apply no_smaller_factor
          exists m
          rw [h] at divis
          rw [h]
          have _ := divis.is_le (nat.zero_lt_inc _)
          apply And.intro
          assumption
          apply Or.inl
          apply And.intro
          assumption
          apply And.intro
          assumption
          rw [←h]
          assumption
      }
      intro n_eq_one
      rw [n_eq_one, nat.eq_inc_irr] at h
      contradiction
    }
    {
      -- n isn't composite
      intro c
      apply no_smaller_factor
      have ⟨ m, prf ⟩ := c
      exists m
      match prf with
      | .inr h₀ =>
        rw [h₀] at h
        rw [nat.eq_inc_irr] at h
        contradiction
      | .inl h₀ =>
      apply And.intro
      have ⟨ divis_n_m, _ ⟩ := h₀
      rw [h] at divis_n_m
      rw [h]
      exact (divis_n_m.is_le (nat.zero_lt_inc _))
      assumption
    }

instance nat.is_composite {n: nat} : Decidable (nat.composite n) :=
  match n.classify_prime with
  | .Prime _ not_composite => Decidable.isFalse not_composite
  | .Composite _ composite => Decidable.isTrue composite

instance nat.is_prime {n: nat} : Decidable (nat.prime n) :=
  match n.classify_prime with
  | .Prime prime _ => Decidable.isTrue prime
  | .Composite not_prime _ => Decidable.isFalse not_prime

instance nat.not_prime_implies_composite {{n:nat}} (p: ¬ nat.prime n) : nat.composite n := by
  match n.classify_prime with
  | .Prime prime _ => contradiction
  | .Composite _ composite => exact composite

instance nat.not_composite_implies_prime {{n:nat}} (p: ¬ nat.composite n) : nat.prime n := by
  match n.classify_prime with
  | .Prime prime _ => exact prime
  | .Composite _ composite => contradiction
