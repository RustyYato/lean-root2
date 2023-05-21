import Root2.Divisible
import Root2.DivRem
import Root2.Nat.Reduction


theorem divrem.dvd_quocient (div: divrem a b) (d: dvd a b) : a = nat.mul b div.quocient := by
  have ⟨ c, a_eq_bc ⟩ := d
  match div with
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
        have _ := div.div_nz
        match b with
        | nat.zero => contradiction
        | nat.inc _ =>
          rw [nat.mul_zero_r] at h
          simp at h
      | nat.inc c₀ => 
        simp
        rw [nat.mul_inc_r, nat.add_comm] at a_eq_bc
        rw [nat.mul_inc_r, nat.add_comm]
        apply Eq.symm
        apply nat.sub_to_add
        have y := d₀.dvd_quocient (by 
          have x := nat.add_to_sub (Eq.symm a_eq_bc)
          exact ⟨ c₀, x ⟩
        )
        exact y

theorem divrem.dvd_remainder (div: divrem a b) (d: dvd a b) : div.remainder = nat.zero := by
  have x := div.def
  have ⟨ c, dvd_def ⟩ := d
  have quot := div.dvd_quocient d
  have quot_eq_c: div.quocient = c := by {
    rw  [quot] at dvd_def
    exact (nat.mul_irr_l div.div_nz dvd_def)
  }
  rw [quot_eq_c, nat.mul_comm, ←dvd_def] at x
  have y := nat.add_to_sub x
  rw [nat.checked_sub_aa] at y
  apply Eq.symm
  repeat assumption

theorem divrem.not_dvd_remainder (div: divrem a b) (d: ¬dvd a b) : nat.zero < div.remainder := by
  match h:div.remainder with
  | .zero =>
    apply False.elim
    have dvd_def := div.def
    rw [h] at dvd_def
    simp at dvd_def
    apply d
    exists div.quocient
    apply Eq.symm
    rw [nat.mul_comm]
    assumption
  | .inc r =>
    apply nat.zero_lt_inc


@[simp]
def nat.is_dvd (a b: nat) : Decidable (dvd a b) := by
  match b with
  | nat.zero =>
    match a with
    | nat.zero =>
      apply Decidable.isTrue
      apply dvd.id
    | nat.inc a₀ =>
      apply Decidable.isFalse
      intro d
      have ⟨ _, prf ⟩ := d
      simp at prf
  | nat.inc b₀ => 
    have div := divrem.calc a (nat.inc b₀) (nat.zero_lt_inc _)
    generalize rem : div.remainder = r
    match r with
    | nat.zero =>
      apply Decidable.isTrue
      have dvd_def := div.def
      rw [rem, nat.add_zero] at dvd_def
      unfold dvd
      exists div.quocient 
      rw [nat.mul_comm]
      apply Eq.symm
      assumption
    | nat.inc r₀ =>
      apply Decidable.isFalse
      intro d
      have x := div.dvd_remainder d
      rw [rem] at x
      contradiction

inductive Quocient (n m: nat) :=
  | Quocient : ∀ q, n = nat.mul m q -> Quocient n m

def dvd.find_quocient
  (d: dvd a b)
  (a_gt_zero : nat.zero < a)
  (x: nat)
  (no_multiples_after: ∀n, x <= n -> a ≠ nat.mul b n) : Quocient a b :=
  match x with
  | .zero =>
    False.elim (by
      have ⟨ c, a_eq_bc ⟩ := d
      have c_not_multiple := no_multiples_after c (nat.zero_le _)
      contradiction
    )
  | .inc x₀ => by
    match a.compare_eq (nat.mul b x₀) with
    | .isTrue _ =>
      apply Quocient.Quocient x₀
      assumption
    | .isFalse h₀ =>
      exact d.find_quocient a_gt_zero x₀ (by
        have := nat.bounded_reduction_step (λq => ¬ (a = nat.mul b q)) x₀ h₀ no_multiples_after 
        assumption
      )

def dvd.quocient (d: dvd a b) (a_gt_zero : nat.zero < a) : Quocient a b := by
  have b_gt_zero := d.is_nonzero a_gt_zero
  exact d.find_quocient a_gt_zero a.inc (by
    intro n a_le_n a_eq_bn
    rw [a_eq_bn] at a_le_n
    have n_le_mul := @nat.a_le_a_mul_b n b b_gt_zero
    rw [nat.mul_comm] at n_le_mul
    exact (nat.comp_dec (nat.a_lt_inc_a _) (nat.le_trans a_le_n n_le_mul))
  )

theorem dvd.remainder_zero : a < b -> nat.add a (nat.mul b c) = nat.mul b d -> a = nat.zero := by
  intro a_lt_b mul
  have b_gt_zero := nat.gt_implies_gt_zero a_lt_b
  have bd_divrem := divrem.calc (nat.mul b d) b b_gt_zero
  have abc_divrem := divrem.calc (nat.add a (nat.mul b c)) b b_gt_zero
  have bd_rem := bd_divrem.dvd_remainder (by exists d)
  have ⟨ abd_rem_eq_bd_rem, _ ⟩  := abc_divrem.eq bd_divrem mul
  rw [←abd_rem_eq_bd_rem] at bd_rem
  have ⟨ abc_divrem_rem, _ ⟩ := abc_divrem.from_def a_lt_b
  rw [←abc_divrem_rem]
  assumption

theorem dvd.divdef (n_dvd: dvd (nat.add (nat.mul a b) c) b): dvd c b := by
  match c.is_dvd b with
  | .isTrue _ => assumption
  | .isFalse c_not_dvd =>
    match b with
    | .zero =>
      rw [nat.mul_zero_r, nat.add_zero] at n_dvd
      contradiction
    | .inc b₀ =>
    apply False.elim
    have d := divrem.calc c b₀.inc (nat.zero_lt_inc _)
    have ⟨ x, prf ⟩ := n_dvd
    rw [←d.def] at prf
    rw [nat.add_perm1, nat.add_comm] at prf
    conv at prf => {
      lhs
      rhs
      rw [nat.mul_comm]
      rhs
      rw [nat.mul_comm]
    }
    rw [←nat.mul_add] at prf
    generalize nat.add a d.quocient = ingore at prf
    have rem_gt_zero := divrem.not_dvd_remainder d c_not_dvd
    have drem_lt := d.remainder_lt
    have := dvd.remainder_zero drem_lt prf
    rw [this] at rem_gt_zero
    contradiction
    
theorem dvd.from_ne : a ≠ b -> (∃ x, dvd a x ≠ dvd b x) := by
  intro a_eq_b
  match a.is_dvd b with
  | .isFalse _ =>
    exists b
    intro dvd_eq_dvd
    have := dvd_eq_dvd.mpr (dvd.id _)
    contradiction
  | .isTrue a_dvd_b => 
  match b.is_dvd a with
  | .isFalse _ =>
    exists a
    intro dvd_eq_dvd
    have := dvd_eq_dvd.mp (dvd.id _)
    contradiction
  | .isTrue b_dvd_a =>
  have := dvd.to_eq a_dvd_b b_dvd_a
  contradiction

instance dvd.dec a b : Decidable (dvd a b) := match a, b with
| .zero, _ => Decidable.isTrue (dvd.zero _)
| _, .inc .zero => Decidable.isTrue (dvd.one _)
| .inc a₀, .zero => Decidable.isFalse (fun ⟨ x, prf ⟩  => by
  rw [nat.mul_zero] at prf
  contradiction
  )
| .inc a₀, .inc b₀ => by
  have d := divrem.calc a₀.inc b₀.inc (nat.zero_lt_inc _)
  match d.remainder.compare_eq .zero with
  | .isTrue rem_eq_zero =>  
    apply Decidable.isTrue
    exists d.quocient
    have := d.def
    conv => {
      lhs
      rw [←this]
    }
    rw [rem_eq_zero]
    rw [nat.add_zero, nat.mul_comm]
  | .isFalse rem_ne_zero =>
    apply Decidable.isFalse
    intro dv
    have := d.dvd_remainder dv
    contradiction

#print axioms dvd.dec


theorem mul_div_inv (dr: divrem a b) (d: dvd a b) : nat.mul b dr.quocient = a := by
  
  admit

#print axioms mul_div_inv