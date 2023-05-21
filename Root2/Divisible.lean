import Root2.Nat.Mul
import Root2.Nat.Cmp
import Root2.Nat.Mul.Cmp
import Root2.Nat.Sub
import Root2.Nat.Sub.Mul

def dvd (a b: nat) : Prop := ∃ c, a = nat.mul b c

@[simp]
def not_dvd (a b: nat) : Prop := ∀ c, ¬(a = nat.mul b c)

theorem dvd.zero (a: nat) : dvd nat.zero a := ⟨ nat.zero, (Eq.symm (nat.mul_zero_r a)) ⟩

theorem dvd.by_zero (a: nat) : dvd a nat.zero -> a = nat.zero := by
  intro a_dvd_zero
  have ⟨ _, prf ⟩ := a_dvd_zero
  simp at prf
  assumption

theorem dvd.one (a: nat) : dvd a (nat.inc nat.zero) := ⟨ a, (Eq.symm (nat.mul_one a)) ⟩

theorem dvd.id (a: nat) : dvd a a := ⟨ nat.inc nat.zero, Eq.symm (nat.mul_one_r a) ⟩

theorem dvd.one_or_id (a b: nat) : b = nat.zero.inc ∨ a = b -> dvd a b := by
  intros conditions
  match conditions with
  | Or.inl a => rw [a]; apply dvd.one
  | Or.inr a => rw [a]; apply dvd.id

theorem dvd.is_le (d: dvd a b) (a_nz : nat.zero < a) : b <= a := by
  have ⟨ c, d ⟩ := d
  rw [d]
  match c₁:c with
  | nat.zero =>
    rw [nat.mul_zero_r] at d
    rw [d] at a_nz
    contradiction
  | nat.inc c₀ =>
    apply nat.a_le_a_mul_b
    apply nat.zero_lt_inc

theorem dvd.is_nonzero (d: dvd a b) (a_nz : nat.zero < a) : nat.zero < b := by
  match a with
  | nat.inc a₀ =>
  have ⟨ c, a_eq_bc ⟩ := d
  match b with
  | nat.zero => rw [nat.mul_zero] at a_eq_bc; contradiction
  | nat.inc b₀ => apply nat.zero_lt_inc

theorem Not.not_dvd_def (d: ¬dvd a b): not_dvd a b := by
  intro c a_bc
  exact (d ⟨ c, a_bc ⟩)

theorem dvd.add (da: dvd a c) (db: dvd b c): dvd (nat.add a b) c := by
  have ⟨ x, prfx ⟩ := da
  have ⟨ y, prfy ⟩ := db
  exists x.add y
  rw [prfx, prfy]
  rw [nat.mul_add]

theorem dvd.mul (d: dvd a b): dvd (nat.mul a c) b := by
  have ⟨ b₀, a_eq_bb₀ ⟩ := d
  exists nat.mul b₀ c
  rw [a_eq_bb₀]
  rw [nat.mul_perm0]

theorem dvd.mul_left (a b: nat): dvd (nat.mul a b) b := by
  exists a
  rw [nat.mul_comm]

theorem dvd.mul_right (a b: nat): dvd (nat.mul a b) a := by
  exists b

theorem dvd.not (nd: ¬ dvd a b) : not_dvd a b := by
  intro x a_eq_bx
  apply nd
  exists x

theorem dvd.to_ne : (∃ x, dvd a x ≠ dvd b x) -> a ≠ b := by
  intro exists_dvd_ne a_eq_b
  rw [a_eq_b] at exists_dvd_ne
  have ⟨ _, prf ⟩ := exists_dvd_ne
  contradiction


theorem dvd.to_eq : dvd a b -> dvd b a -> a = b := by
  intro dvd_ab dvd_ba
  have ⟨ x, prf₀ ⟩ := dvd_ab
  have ⟨ y, prf₁ ⟩ := dvd_ba
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

theorem dvd.trans : dvd a b -> dvd b c -> dvd a c := by
  intro dvd_ab dvd_bc
  have ⟨ x, prfx ⟩ := dvd_ab
  have ⟨ y, prfy ⟩ := dvd_bc
  exists y.mul x
  rw [prfx, prfy]
  apply Eq.symm
  apply nat.mul_perm0

theorem dvd.eq (a_eq_c: a = c) (b_eq_d: b = d) : dvd a b = dvd c d := by
  rw [a_eq_c]
  rw [b_eq_d]

theorem dvd.gt {a b c} (a_gt_c: c < a) : dvd b a -> c < b ∨ b = nat.zero := by
  intro dvd_a_b
  have ⟨ x, prf ⟩ := dvd_a_b
  match x with
  | .zero =>  
    rw [nat.mul_zero_r] at prf
    exact Or.inr prf
  | .inc x₀ =>
  apply Or.inl
  rw [prf]
  have :=  @nat.mul_output_imp_le a x₀.inc (nat.mul a x₀.inc) (by
    match b with
    | .zero =>  
      match  nat.mul_eq_zero _ _ prf.symm with
      | .inl a_eq_zero =>
      rw [a_eq_zero] at a_gt_c
      have := nat.not_lt_zero c
      contradiction
    | .inc b₀ =>
    rw [←prf]
    apply nat.zero_lt_inc
  ) rfl
  exact nat.lt_le_trans a_gt_c this

theorem dvd.sat_sub : dvd a b -> dvd (a.saturating_sub b) b := by
  intro dvd_a_b
  have ⟨ x, prf ⟩ := dvd_a_b
  match x with
  | .zero =>
    rw [nat.mul_zero_r] at prf
    rw [prf, nat.sat_sub_zero]
    exact dvd.zero _
    apply nat.zero_le
  | .inc x₀ =>
    exists x₀
    rw [prf, nat.mul_inc_r, nat.sat_sub_add_inv2]

theorem dvd.cancel_right : dvd (nat.add a b) c -> dvd b c -> dvd a c := by
  intro d_ab_c d_b_c
  have ⟨ x, prfx ⟩ := d_ab_c
  have ⟨ y, prfy ⟩ := d_b_c
  exists x.saturating_sub y
  rw [prfy] at prfx
  rw [nat.mul_sat_sub_left]
  rw [←prfx]
  rw [nat.add_comm,
      nat.sat_sub_add_inv2]