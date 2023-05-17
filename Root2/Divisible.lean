import Root2.Nat.Mul
import Root2.Nat.Cmp
import Root2.Nat.Mul.Cmp

def divisible (a b: nat) : Prop := ∃ c, a = nat.mul b c

@[simp]
def not_divisible (a b: nat) : Prop := ∀ c, ¬(a = nat.mul b c)

theorem divisible.zero (a: nat) : divisible nat.zero a := ⟨ nat.zero, (Eq.symm (nat.mul_zero_r a)) ⟩

theorem divisible.one (a: nat) : divisible a (nat.inc nat.zero) := ⟨ a, (Eq.symm (nat.mul_one a)) ⟩

theorem divisible.id (a: nat) : divisible a a := ⟨ nat.inc nat.zero, Eq.symm (nat.mul_one_r a) ⟩

theorem divisible.one_or_id (a b: nat) : b = nat.zero.inc ∨ a = b -> divisible a b := by
  intros conditions
  match conditions with
  | Or.inl a => rw [a]; apply divisible.one
  | Or.inr a => rw [a]; apply divisible.id

theorem divisible.is_le (divis: divisible a b) (a_nz : nat.zero < a) : b <= a := by
  have ⟨ c, d ⟩ := divis
  rw [d]
  match c₁:c with
  | nat.zero =>
    rw [nat.mul_zero_r] at d
    rw [d] at a_nz
    contradiction
  | nat.inc c₀ =>
    apply nat.a_le_a_mul_b
    apply nat.zero_lt_inc

theorem divisible.is_nonzero (divis: divisible a b) (a_nz : nat.zero < a) : nat.zero < b := by
  match a with
  | nat.inc a₀ =>
  have ⟨ c, a_eq_bc ⟩ := divis
  match b with
  | nat.zero => rw [nat.mul_zero] at a_eq_bc; contradiction
  | nat.inc b₀ => apply nat.zero_lt_inc

theorem Not.not_divisible_def (d: ¬divisible a b): not_divisible a b := by
  intro c a_bc
  exact (d ⟨ c, a_bc ⟩)

theorem divisible.mul (d: divisible a b): divisible (nat.mul a c) b := by
  have ⟨ b₀, a_eq_bb₀ ⟩ := d
  exists nat.mul b₀ c
  rw [a_eq_bb₀]
  rw [nat.mul_perm0]

theorem divisible.not (nd: ¬ divisible a b) : not_divisible a b := by
  intro x a_eq_bx
  apply nd
  exists x

theorem divisible.to_ne : (∃ x, divisible a x ≠ divisible b x) -> a ≠ b := by
  intro exists_divis_ne a_eq_b
  rw [a_eq_b] at exists_divis_ne
  have ⟨ _, prf ⟩ := exists_divis_ne
  contradiction


theorem divisible.ab_eq_ba_implies_eq : divisible a b -> divisible b a -> a = b := by
  intro divis_ab divis_ba
  have ⟨ x, prf₀ ⟩ := divis_ab
  have ⟨ y, prf₁ ⟩ := divis_ba
  rw [prf₀] at prf₁
  rw [←nat.mul_perm0] at prf₁
  have := nat.mul_one_r b
  conv at prf₁ => {
    lhs
    rw [←this]
  }
  clear this
  match b with
  | .zero =>
    simp at prf₀
    assumption
  | .inc b₀ =>
    rw [nat.mul_irr (nat.zero_lt_inc _)] at prf₁
    have ⟨ x_eq_one, y_eq_one ⟩  := nat.mul_eq_one _ _ (Eq.symm prf₁)
    rw [x_eq_one, nat.mul_one_r] at prf₀
    assumption
