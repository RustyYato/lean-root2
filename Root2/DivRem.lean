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

def divrem.calc_imp (a b c: nat) (b_gt_0: nat.zero < b) (c_le_a: c <= a) : divrem (a.checked_sub c c_le_a) b :=
  match c with
  | nat.inc c₀ => by
    match a with
    | nat.zero => contradiction
    | nat.inc a₀ =>
    simp
    apply divrem.calc_imp
    assumption
  | nat.zero =>
  match nat.compare a b with
    | Decidable.isTrue h => by
      simp
      exact (divrem.remain h)
    | Decidable.isFalse h => 
    by
      rw [nat.not_lt_is_sym_le_op] at h
      match h₀:b with
      | nat.zero => contradiction
      | nat.inc b₀ =>
      match h₁:a with
      | nat.zero => contradiction
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

theorem divrem.div_nz (d: divrem a b) : nat.zero < b :=
  match d with
  | divrem.remain q => match a with
     | nat.zero => q
     | nat.inc _ => nat.lt_trans (nat.zero_lt_inc _) (q)
  | divrem.step d => d.div_nz
