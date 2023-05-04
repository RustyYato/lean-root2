import Root2.Nat.Cmp

theorem nat.bump_lt : a < n -> inc a ≠ n -> inc a < n := by
  intro a_lt_n inca_ne_n
  match a, n with
  | .zero, .inc n₀ => 
    rw [nat.ne_inc_irr] at inca_ne_n
    rw [nat.lt_inc_irr]
    match n₀ with
    | .inc n₁ => 
      apply nat.zero_lt_inc
  | .inc a₀, .inc n₀ =>
    rw [nat.lt_inc_irr]
    rw [nat.ne_inc_irr] at inca_ne_n
    rw [nat.lt_inc_irr] at a_lt_n
    exact (nat.bump_lt a_lt_n inca_ne_n)

theorem nat.bump_le : a <= n -> a ≠ n -> inc a <= n := by
  intro a_lt_n inca_ne_n
  match a, n with
  | .zero, .zero => contradiction
  | .zero, .inc n₀ => 
    rw [nat.le_inc_irr]
    match n₀ with
    | .zero => apply nat.le_id
    | .inc n₁ => 
      apply nat.zero_lt_inc
      assumption
  | .inc a₀, .inc n₀ =>
    rw [nat.le_inc_irr]
    rw [nat.ne_inc_irr] at inca_ne_n
    rw [nat.le_inc_irr] at a_lt_n
    exact (nat.bump_le a_lt_n inca_ne_n)
  

theorem nat.bounded_reduction_step : ∀(P: nat -> Sort _), (x: nat) ->
  P x -> (∀a:nat, (nat.inc x <= a) -> P a) -> ∀a:nat, (x <= a) -> P a := by
  intro P x Px all_after a x_le_a
  match x.compare_eq a with
  | .isTrue incx_eq_a =>
    rw [←incx_eq_a]
    assumption
  | .isFalse incx_ne_a =>
    apply all_after
    exact (nat.bump_le x_le_a incx_ne_a)
