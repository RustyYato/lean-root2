import Root2.Divisible
import Root2.DivRem
import Root2.Nat.Reduction

theorem divrem.divisible_quocient (d: divrem a b) (divis: divisible a b) : a = nat.mul b d.quocient := by
  have ⟨ c, a_eq_bc ⟩ := divis
  match d with
    | divrem.remain h =>
      simp
      match c with
      | nat.zero => simp at a_eq_bc; assumption
      | nat.inc c₀ =>
        simp at a_eq_bc
        rw [nat.mul_inc_r, nat.add_comm] at a_eq_bc
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
        | nat.inc _ =>
          rw [nat.mul_zero_r] at h
          contradiction
      | nat.inc c₀ => 
        simp
        rw [nat.mul_inc_r, nat.add_comm] at a_eq_bc
        rw [nat.mul_inc_r, nat.add_comm]
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
  have y := nat.add_to_sub x
  rw [nat.checked_sub_aa] at y
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

inductive Quocient (n m: nat) :=
  | Quocient : ∀ q, n = nat.mul m q -> Quocient n m

def divisible.find_quocient
  (divis: divisible a b)
  (a_gt_zero : nat.zero < a)
  (x: nat)
  (no_multiples_after: ∀n, x <= n -> a ≠ nat.mul b n) : Quocient a b :=
  match x with
  | .zero =>
    False.elim (by
      have ⟨ c, a_eq_bc ⟩ := divis
      have c_not_multiple := no_multiples_after c (nat.zero_le _)
      contradiction
    )
  | .inc x₀ => by
    match a.compare_eq (nat.mul b x₀) with
    | .isTrue _ =>
      apply Quocient.Quocient x₀
      assumption
    | .isFalse h₀ =>
      exact divis.find_quocient a_gt_zero x₀ (by
        have := nat.bounded_reduction_step (λq => ¬ (a = nat.mul b q)) x₀ h₀ no_multiples_after 
        assumption
      )

def divisible.quocient (divis: divisible a b) (a_gt_zero : nat.zero < a) : Quocient a b := by
  have b_gt_zero := divis.is_nonzero a_gt_zero
  exact divis.find_quocient a_gt_zero a.inc (by
    intro n a_le_n a_eq_bn
    rw [a_eq_bn] at a_le_n
    have n_le_mul := @nat.a_le_a_mul_b n b b_gt_zero
    rw [nat.mul_comm] at n_le_mul
    exact (nat.comp_dec (nat.a_lt_inc_a _) (nat.le_trans a_le_n n_le_mul))
  )
