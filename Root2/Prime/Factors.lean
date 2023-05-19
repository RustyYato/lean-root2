import Root2.Prime

inductive Factors : nat -> Type :=
  | MkFactors : ∀ {{n: nat}}  (a b: nat),
    nat.zero.inc < a ->
    nat.zero.inc < b ->
    a < n ->
    b < n ->
    n = nat.mul a b -> Factors n

def Factors.get {{n:nat}} (f: Factors n) : List nat := match f with
  | @Factors.MkFactors _ a b _ _ _ _ _ => [a, b]

def plus_two_gt_one : x = nat.inc (nat.inc a) -> nat.zero.inc < x := by
  intro x_eq
  rw [x_eq]
  rw [nat.lt_inc_irr]
  apply nat.zero_lt_inc

def search_factors
  (x n: nat)
  (composite: n.composite)
  (n_gt_one: nat.zero.inc < n)
  (x_lt_n: x < n)
  (no_factors_after_x: ∀m, x < m -> ¬nat.is_factor n m) : 
  Factors n := 
  match h₀:x with
  | nat.zero =>
    False.elim (by
      have ⟨ f, is_factor ⟩ := composite
      match is_factor with
      | .inr n_eq_one =>
        rw [n_eq_one] at n_gt_one
        contradiction
      | .inl divis =>
        have ⟨ divis, f_ne_one, n_ne_f ⟩ := divis
        have  not_factor := no_factors_after_x f (dvd.is_nonzero divis (nat.lt_trans (nat.zero_lt_inc _) n_gt_one))
        apply not_factor
        unfold nat.is_factor
        apply Or.inl
        apply And.intro
        assumption
        apply And.intro
        assumption
        assumption
    )
  | nat.inc nat.zero =>
    False.elim (by
      have ⟨ f, is_factor ⟩ := composite
      match is_factor with
      | .inr n_eq_one =>
        rw [n_eq_one] at n_gt_one
        contradiction
      | .inl divis =>
        have ⟨ divis, f_ne_one, n_ne_f ⟩ := divis
        have  not_factor := no_factors_after_x f (by
          have f_gt_zero := dvd.is_nonzero divis (nat.lt_trans (nat.zero_lt_inc _) n_gt_one)
          exact nat.bump_lt f_gt_zero (Ne.symm f_ne_one)
          )
        apply not_factor
        unfold nat.is_factor
        apply Or.inl
        apply And.intro
        assumption
        apply And.intro
        assumption
        assumption
    )
  | nat.inc (nat.inc x₁) => by
    match n.is_dvd x with
    | .isTrue dvd_n_x =>
      have n_gt_zero := nat.lt_trans (nat.zero_lt_inc _) n_gt_one
      match dvd_n_x.quocient n_gt_zero with
      | .Quocient q n_eq_xq =>
      match h₁:q with
      | nat.zero => rw [nat.mul_zero_r] at n_eq_xq; rw [n_eq_xq] at n_gt_one; contradiction
      | nat.inc nat.zero =>
        rw [nat.mul_one_r] at n_eq_xq
        rw [n_eq_xq] at x_lt_n
        rw [←h₀] at x_lt_n
        have := nat.not_lt_id x
        contradiction
      | nat.inc (nat.inc q₀) =>
      rw [←h₁] at n_eq_xq
      have a_gt_one := plus_two_gt_one h₀
      have b_gt_one := plus_two_gt_one h₁
      have a_ne_n := nat.mul_output_lt a_gt_one b_gt_one n_eq_xq
      rw [nat.mul_comm] at n_eq_xq
      have b_ne_n := nat.mul_output_lt b_gt_one a_gt_one n_eq_xq
      rw [nat.mul_comm] at n_eq_xq
      exact Factors.MkFactors _ _ a_gt_one b_gt_one a_ne_n b_ne_n n_eq_xq
    | .isFalse not_dvd_n_x =>
      have := search_factors (nat.inc x₁) n composite n_gt_one
      exact search_factors (nat.inc x₁) n composite n_gt_one (nat.lt_trans (nat.a_lt_inc_a _) x_lt_n) (by
        intro m x₀_lt_m  is_factor_nm
        match m.compare_eq x with
        | .isTrue m_eq_x =>
          rw [m_eq_x] at is_factor_nm
          unfold nat.is_factor at is_factor_nm
          match is_factor_nm with
          | .inr h =>
            rw [h] at n_gt_one
            contradiction
          | .inl is_factor_nm =>
          have ⟨ divis, _ ⟩ := is_factor_nm
          contradiction
        | .isFalse m_ne_x =>
          rw [h₀] at m_ne_x
          have x_lt_m := nat.bump_lt x₀_lt_m (Ne.symm m_ne_x)
          have := no_factors_after_x m x_lt_m 
          contradiction
      )

def nat.get_factors (n: nat) (n_gt_one : nat.zero.inc < n) : n.composite -> Factors n := by
  intro composite
  match n with
  | nat.zero => contradiction
  | nat.inc n₀ =>
  apply search_factors n₀ n₀.inc composite n_gt_one (nat.a_lt_inc_a _)
  intro m n_lt_m is_factor_nm
  match is_factor_nm with
  | .inr h => 
    rw [h] at n_gt_one
    contradiction
  | .inl h =>
  have ⟨ divis, ⟨ _, n_ne_m ⟩  ⟩ := h
  have m_le_n := divis.is_le (nat.lt_trans (nat.a_lt_inc_a _) n_gt_one)
  have m_lt_incn := nat.ne_and_le_to_lt (Ne.symm n_ne_m) m_le_n
  exact nat.no_between_inc n_lt_m m_lt_incn
