import Root2.Divisible
import Root2.DivRem

theorem divrem.divisible_quocient (d: divrem a b) (divis: divisible a b) : a = nat.mul b d.quocient := by
  have ⟨ c, a_eq_bc ⟩ := divis
  match d with
    | divrem.remain h =>
      simp
      match c with
      | nat.zero => simp at a_eq_bc; assumption
      | nat.inc c₀ =>
        simp at a_eq_bc
        rw [nat.add_comm] at a_eq_bc
        have bc_le_a := nat.eq_to_le (Eq.symm a_eq_bc)
        have x := nat.add_imp_le bc_le_a
        have contra := nat.comp_dec h x
        contradiction
    | @divrem.step _ _ h d₀ => match c with
      | nat.zero =>
        simp at a_eq_bc
        rw [a_eq_bc] at h
        have _ := d.div_nz
        match b with
        | nat.zero => contradiction
        | nat.inc _ => contradiction
      | nat.inc c₀ => 
        simp
        simp at a_eq_bc
        rw [nat.add_comm] at a_eq_bc
        rw [nat.add_comm]
        apply Eq.symm
        apply nat.sub_to_add
        have y := d₀.divisible_quocient (by 
          have x := nat.add_to_sub (Eq.symm a_eq_bc)
          exact ⟨ c₀, x ⟩
        )
        exact y

theorem divrem.divisible_remainder (d: divrem a b) (divis: divisible a b) : d.remainder = nat.zero := by
  have x := d.def
  have ⟨ c, divis_def ⟩ := divis
  have quot := d.divisible_quocient divis
  have quot_eq_c: d.quocient = c := by {
    rw  [quot] at divis_def
    exact (nat.mul_irr_l d.div_nz divis_def)
  }
  rw [quot_eq_c, nat.mul_comm, ←divis_def] at x
  have y := @nat.add_to_sub d.remainder a a x
  simp at y
  apply Eq.symm
  repeat assumption

@[simp]
def nat.is_divisible (a b: nat) : Decidable (divisible a b) := by
  match b with
  | nat.zero =>
    match a with
    | nat.zero =>
      apply Decidable.isTrue
      apply divisible.id
    | nat.inc a₀ =>
      apply Decidable.isFalse
      intro divis
      have ⟨ _, prf ⟩ := divis
      simp at prf
  | nat.inc b₀ => 
    have d := divrem.calc a (nat.inc b₀) (nat.zero_lt_inc _)
    generalize rem : d.remainder = r
    match r with
    | nat.zero =>
      apply Decidable.isTrue
      have divis_def := d.def
      rw [rem, nat.add_zero] at divis_def
      unfold divisible
      exists d.quocient 
      rw [nat.mul_comm]
      apply Eq.symm
      assumption
    | nat.inc r₀ =>
      apply Decidable.isFalse
      intro divis
      have x := d.divisible_remainder divis
      rw [rem] at x
      contradiction
