import Root2.Nat
import Root2.Nat.Sub
import Root2.Nat.Mul

inductive divrem : nat -> nat -> Type where
  | remain : ∀ {{r d}}, ∀_: r < d, divrem r d
  | step : ∀ {{n d}}, ∀ {{h: d <= n}}, divrem (nat.checked_sub n d h) d -> divrem n d

@[simp]
def divrem.quocient (n: divrem a b) : nat :=
  match n with
    | remain _ => nat.zero
    | step n => nat.inc n.quocient

@[simp]
def divrem.remainder (n: divrem a b) : nat :=
  match n with
    | @remain r _ _ => r
    | step n => n.remainder

@[simp]
def divrem.remainder_lt (n: divrem a b) : n.remainder < b :=
  match n with
    | @remain r _ prf => prf
    | step n => n.remainder_lt

def divrem.calc_imp (a b c: nat) (b_gt_0: nat.zero < b) (c_le_a: c <= a) : divrem (a.checked_sub c c_le_a) b :=
  match c with
  | nat.inc c₀ => by
    match a with
    | nat.zero => simp at c_le_a
    | nat.inc a₀ =>
    simp
    apply divrem.calc_imp
    assumption
  | nat.zero =>
  match nat.compare_lt a b with
    | Decidable.isTrue h => by
      simp
      exact (divrem.remain h)
    | Decidable.isFalse h => 
    by
      rw [nat.not_lt_is_sym_le] at h
      match h₀:b with
      | nat.zero => contradiction
      | nat.inc b₀ =>
      match h₁:a with
      | nat.zero => simp at h
      | nat.inc a₀ =>
      rw [←h₀] at b_gt_0
      have prev := divrem.calc_imp a₀ b b₀ b_gt_0 h
      apply divrem.step
      simp
      rw [←h₀]
      exact prev
      simp
      exact h

def divrem.calc (a b: nat) (b_gt_0: nat.zero < b) : divrem a b := by
  have x := divrem.calc_imp a b nat.zero b_gt_0 (nat.zero_le _)
  simp at x
  assumption

#print axioms divrem.calc

def example_val := divrem.calc nat.zero.inc.inc.inc.inc.inc.inc.inc.inc.inc.inc.inc.inc.inc nat.zero.inc.inc.inc.inc.inc.inc.inc (nat.zero_lt_inc _)
example : example_val.remainder = nat.zero.inc.inc.inc.inc.inc.inc := by decide

inductive nat_divrem_fmt where
  | dr : nat -> nat -> nat_divrem_fmt
  deriving Repr

instance : Repr (divrem a b) where
  reprPrec x := Repr.reprPrec (nat_divrem_fmt.dr x.quocient x.remainder)

theorem divrem.def : ∀ {{a b: nat}} (d: divrem a b), nat.add d.remainder (nat.mul d.quocient b) = a := by
  intro a b d
  match d with
    | divrem.remain _ => 
      unfold divrem.remainder divrem.quocient
      rw [nat.mul_zero, nat.add_zero_r]
    | divrem.step d₀ => 
      unfold divrem.remainder divrem.quocient
      simp
      rw [nat.add_perm1, nat.sub_to_add]
      . assumption
      . {
        rw [divrem.def d₀]
      }


theorem divrem.eq (adivc: divrem a c) (bdivc: divrem b c) (aeqb: a = b) : adivc.remainder = bdivc.remainder ∧ adivc.quocient = bdivc.quocient := by 
  match adivc, bdivc with
  | .remain arem, .remain brem =>
    simp
    assumption
  | .step adiv, .step bdiv =>
    simp
    apply adiv.eq bdiv
    rw [nat.add_to_sub]
    rw [nat.sub_add_inv]
    apply Eq.symm
    assumption
  | .step _, .remain b_lt_c =>
    simp
    next c_le_a _ => {
      match c_le_a with
      | .inl c_lt_a =>
        have c_lt_a : c < a := Compare.ord_implies_lt c_lt_a
        have b_lt_a := nat.lt_trans  b_lt_c c_lt_a
        rw [aeqb] at b_lt_a
        have := b.not_lt_id
        contradiction
      | .inr c_eq_a =>
        have c_eq_a : c = a := Compare.ord_implies_eq c_eq_a
        rw [c_eq_a, aeqb] at b_lt_c
        have := b.not_lt_id
        contradiction
    }
  | .remain a_lt_c, .step _ =>
    simp
    next c_le_b _ => {
      match c_le_b with
      | .inl c_lt_b =>
        have c_lt_b : c < b := Compare.ord_implies_lt c_lt_b
        have b_lt_a := nat.lt_trans  a_lt_c c_lt_b
        rw [aeqb] at b_lt_a
        have := b.not_lt_id
        contradiction
      | .inr c_eq_b =>
        have c_eq_a : c = b := Compare.ord_implies_eq c_eq_b
        rw [c_eq_a, aeqb] at a_lt_c
        have := b.not_lt_id
        contradiction
    }

theorem divrem.from_def (d: divrem (nat.add a (nat.mul b c)) b) : a < b -> d.remainder = a ∧ d.quocient = c := by
  intro a_lt_b
  match d with
    | divrem.remain x => 
      simp
      match c with
      | .zero =>
        rw [nat.mul_zero_r, nat.add_zero_r]
        exact ⟨ rfl, rfl ⟩
      | .inc c₀ =>
        simp
        conv at x => {
          rw [nat.mul_inc_r]
          rw [nat.add_perm0, nat.add_comm a, ←nat.add_perm0]
        }
        have := nat.a_le_a_plus_b b (nat.add a (nat.mul b c₀))
        have := @Compare.not_lt_and_le nat _ _ _ x this
        contradiction
    | divrem.step d₀ => 
      match c with
      | .zero =>
        simp
        next b_le_a => {
          rw [@nat.sub_equality_left_prf (nat.add a (nat.mul b .zero)) a b (by
            rw [nat.mul_zero_r, nat.add_zero_r]
            ) b_le_a] at d₀
          rw [nat.mul_zero_r, nat.add_zero_r] at b_le_a
          have := nat.comp_dec a_lt_b b_le_a
          contradiction
        }
      | .inc c₀ =>
        simp
        next h => {
          have : nat.checked_sub (nat.add a (nat.mul b (nat.inc c₀))) b h = nat.add a (nat.mul b c₀) :=  by
            rw [nat.sub_add, nat.mul_inc_r, nat.add_perm7, nat.add_comm]
          have d₁ := d₀
          rw [this] at d₁
          have ⟨ deq_rem, deq_quo ⟩ := d₀.eq d₁ this
          rw [deq_rem, deq_quo]
          exact d₁.from_def a_lt_b
        }

theorem divrem.div_nz (d: divrem a b) : nat.zero < b :=
  match d with
  | divrem.remain q => match a with
     | nat.zero => q
     | nat.inc _ => nat.lt_trans (nat.zero_lt_inc _) q
  | divrem.step d => d.div_nz
