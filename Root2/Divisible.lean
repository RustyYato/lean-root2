import Root2.Nat.Mul
import Root2.Nat.Cmp
import Root2.Nat.Mul.Cmp

@[simp]
def divisible (a b: nat) : Prop := ∃ c, a = nat.mul b c

@[simp]
def not_divisible (a b: nat) : Prop := ∀ c, ¬(a = nat.mul b c)

@[simp]
theorem divisible.zero (a: nat) : divisible nat.zero a := ⟨ nat.zero, (Eq.symm (nat.mul_zero_r a)) ⟩

@[simp]
theorem divisible.one (a: nat) : divisible a (nat.inc nat.zero) := ⟨ a, (Eq.symm (nat.mul_one a)) ⟩

@[simp]
theorem divisible.id (a: nat) : divisible a a := ⟨ nat.inc nat.zero, Eq.symm (nat.mul_one_r a) ⟩

@[simp]
theorem divisible.one_or_id (a b: nat) : b = nat.zero.inc ∨ a = b -> divisible a b := by
  intros conditions
  match conditions with
  | Or.inl a => rw [a]; apply divisible.one
  | Or.inr a => rw [a]; apply divisible.id

@[simp]
theorem divisible.is_le (divis: divisible a b) (a_nz : nat.zero < a) : b <= a := by
  have ⟨ c, d ⟩ := divis
  rw [d]
  match c with
  | nat.zero => simp at d; rw [d] at a_nz; contradiction
  | nat.inc _ => apply nat.a_le_a_mul_b; simp

theorem Not.not_divisible_def (d: ¬divisible a b): not_divisible a b := by
  intro c a_bc
  exact (d ⟨ c, a_bc ⟩)
