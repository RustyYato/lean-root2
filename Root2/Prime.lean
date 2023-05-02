import Root2.Divisible
import Root2.DivRem
import Root2.Divisible.DivRem
import Lean

@[simp]
def nat.prime_cond (n m: nat) : Prop := (¬divisible n m) ∨  m = nat.zero.inc ∨ n = m
@[simp]
def nat.prime (n: nat) : Prop := ∀ m, prime_cond n m
@[simp]
def nat.prime_until (n o: nat) : Prop := ∀ m, m < o -> prime_cond n m

def nat.check_prime_inc (n o: nat) : Decidable (nat.prime_until n o) := by
  match h:o with
  | nat.zero =>
    apply Decidable.isTrue
    intro m
    have x := nat.not_lt_zero m
    intro m_lt_zero
    contradiction
  | nat.inc o₀ =>
    match n.check_prime_inc o₀ with
    | Decidable.isTrue prev =>
      match n.is_divisible o₀ with
      | Decidable.isTrue divis =>
        match o₀.compare_eq nat.zero.inc with
        | Decidable.isTrue o₀_is_one =>
          apply Decidable.isTrue
          unfold prime_until at *
          intro m
          intro m_lt_o₀_inc
          have x := prev m
          match m.compare_lt o₀ with
          | Decidable.isTrue m_lt_o₀ => exact (x m_lt_o₀)
          | Decidable.isFalse m_not_lt_o₀ =>
            rw [nat.not_lt_is_sym_le_op] at m_not_lt_o₀
            clear x divis prev h
            rw [nat.lt_inc_to_le] at m_lt_o₀_inc
            have x := nat.le_le_to_eq m_lt_o₀_inc m_not_lt_o₀
            rw [o₀_is_one] at x
            unfold prime_cond
            apply Or.inr
            apply Or.inl
            assumption
        | Decidable.isFalse o₀_not_one =>
        match n.compare_eq o₀ with
        | Decidable.isTrue o₀_is_n =>
          apply Decidable.isTrue
          unfold prime_until at *
          intro m
          intro m_lt_o₀_inc
          have x := prev m
          match m.compare_lt o₀ with
          | Decidable.isTrue m_lt_o₀ => exact (x m_lt_o₀)
          | Decidable.isFalse m_not_lt_o₀ =>
            rw [nat.not_lt_is_sym_le_op] at m_not_lt_o₀
            clear x divis prev h
            rw [nat.lt_inc_to_le] at m_lt_o₀_inc
            have x := nat.le_le_to_eq m_not_lt_o₀ m_lt_o₀_inc
            rw [←o₀_is_n] at x
            unfold prime_cond
            apply Or.inr
            apply Or.inr
            assumption
        | Decidable.isFalse o₀_not_n =>
        apply Decidable.isFalse
        intro prf
        match prf o₀ (nat.a_lt_inc_a _) with
        | Or.inl a => contradiction
        | Or.inr (Or.inl a) => contradiction
        | Or.inr (Or.inr a) => contradiction
      | Decidable.isFalse divis =>
        apply Decidable.isTrue
        unfold prime_until
        intro m m_lt_inc_o₀
        unfold prime_until prime_cond at *


        match m.compare_eq nat.zero.inc with
        | Decidable.isTrue _ => apply Or.inr; apply Or.inl; assumption
        | Decidable.isFalse _ => match n.compare_eq m with
        | Decidable.isTrue _ => apply Or.inr; apply Or.inr; assumption
        | Decidable.isFalse _ => match m.compare_lt o₀ with
        | Decidable.isTrue h₂ =>
          apply Or.inl
          have x := prev m h₂
          match x with
          | Or.inl _ => assumption
          | Or.inr (Or.inl _) => contradiction
          | Or.inr (Or.inr _) => contradiction
        | Decidable.isFalse h =>
          rw [nat.not_lt_is_sym_le_op] at h
          rw [nat.lt_inc_to_le] at m_lt_inc_o₀
          have o₀_eq_m := nat.le_le_to_eq h m_lt_inc_o₀
          rw [←o₀_eq_m]
          apply Or.inl
          assumption
    | Decidable.isFalse prev =>
      apply Decidable.isFalse
      intro prf
      exact prev (by
        intro m₀ m₀_lt_o₀
        have y := prf m₀ (nat.lt_trans m₀_lt_o₀ (nat.a_lt_inc_a o₀))
        assumption
      )

instance nat.is_prime (n: nat) : Decidable (nat.prime n) := by
  match nat.check_prime_inc n n.inc.inc.inc with
  | Decidable.isTrue h =>
    apply Decidable.isTrue
    intro m
    unfold nat.prime_cond
    match m.compare_le n with
    | Decidable.isTrue m_le_n =>
      unfold nat.prime_until at *
      rw [←nat.lt_inc_to_le] at m_le_n
      have x := h m (nat.lt_trans m_le_n (nat.lt_trans (nat.a_lt_inc_a _) (nat.a_lt_inc_a _)))
      assumption
    | Decidable.isFalse n_lt_m =>
      apply Or.inl
      intro divis
      match n with
      | nat.zero =>
        unfold nat.prime_until nat.prime_cond divisible at h
        match h nat.zero.inc.inc (nat.a_lt_inc_a _) with
        | Or.inl d => exact d ⟨ nat.zero, by rw [nat.mul_zero_r] ⟩ 
        | Or.inr (Or.inl h) => rw [nat.eq_inc_irr] at h; contradiction
        | Or.inr (Or.inr h) => contradiction
      | nat.inc _ =>
      exact n_lt_m (divis.is_le (nat.zero_lt_inc _))
  | Decidable.isFalse h =>
    apply Decidable.isFalse
    intro prime
    exact h (by 
      intro m _
      exact prime m
    )

-- theorem two_is_prime : nat.prime (nat.inc (nat.inc nat.zero)) := by
--   intro m divis
--   match m with
--   | nat.zero =>
--     simp
--     have ⟨ _, cs ⟩ := divis
--     simp at cs
--   | nat.inc m₀ =>
--     simp
--     match m₀ with
--     | nat.zero => 
--       simp at divis
--       have ⟨ c, cs ⟩ := divis
--       simp at cs
--       exact (Or.inl rfl)
--     | nat.inc m₁ =>
--       match m₁ with
--       | nat.zero =>
--         exact (Or.inr rfl)
--       | nat.inc m₂ =>
--         have is_le := divis.is_le (nat.zero_lt_inc _)
--         contradiction

-- theorem divisible.split_mul_contra (p: nat.prime n) (a_not_divis_n: ¬(divisible a n)) (b_not_divis_n: ¬(divisible b n)): ¬(divisible (nat.mul a b) n) := by
--   intro ab_divisible_n
--   have a_not_divis_n := a_not_divis_n.not_divisible_def
--   have b_not_divis_n := b_not_divis_n.not_divisible_def
--   unfold not_divisible at *

--   admit

-- theorem divisible.split_mul (divis_ab_n: divisible (nat.mul a b) n) (p: nat.prime n) : (divisible a n) ∨ (divisible b n) :=
--   match is_divisible a n with
--   | Decidable.isTrue a_divisible_by_n => Or.inl a_divisible_by_n
--   | Decidable.isFalse a_not_divisible_by_n => match is_divisible b n with
--     | Decidable.isTrue b_divisible_by_n => Or.inr b_divisible_by_n
--     | Decidable.isFalse b_not_divisible_by_n => by
--       have _ := divisible.split_mul_contra p a_not_divisible_by_n b_not_divisible_by_n
--       contradiction
