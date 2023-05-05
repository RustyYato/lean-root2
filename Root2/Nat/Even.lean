import Root2.Nat.Mul

def nat.even (n: nat) : Prop := ∃n₀, nat.mul nat.zero.inc.inc n₀ = n

instance is_even (n: nat) : Decidable n.even := by
  match n with
  | nat.zero =>
        apply Decidable.isTrue
        exists nat.zero
  | nat.inc n₀ => match n₀ with
    | nat.zero => 
        apply Decidable.isFalse
        intro one_even
        let ⟨ half, prf ⟩ := one_even
        match half with
        | nat.zero => simp at prf
        | nat.inc _ =>
          simp at prf
          rw [nat.add_inc] at prf
          contradiction
    | nat.inc n₁ => match is_even n₁ with
      | .isTrue n₁_even =>
        apply Decidable.isTrue
        let ⟨ n₁₀, x ⟩ := n₁_even
        exists n₁₀.inc
        simp
        simp at x
        rw [nat.add_inc, nat.eq_inc_irr]
        assumption
      | .isFalse n₁_odd =>
        apply Decidable.isFalse
        intro n₁_even
        let ⟨n₁₀, h⟩ := n₁_even
        simp at h
        match n₁₀ with
        | nat.zero => 
          simp at h
        | nat.inc n₁₁ =>
          simp at h 
          rw [nat.add_inc, nat.eq_inc_irr] at h
          apply n₁_odd
          exists n₁₁

theorem check_is_even : nat.even nat.zero.inc.inc  := by 
  decide

@[simp]
def AsTrue (dec : Decidable p) : Prop :=
  match dec with
  | .isTrue _ => True
  | .isFalse _ => False

theorem force_eval (dec : Decidable p) : AsTrue dec → p :=
  match dec with
  | .isTrue h => fun _ => h
  | .isFalse _ => False.elim

theorem two_is_even : nat.even (nat.inc (nat.inc nat.zero)) :=
  force_eval (is_even nat.zero.inc.inc) trivial
