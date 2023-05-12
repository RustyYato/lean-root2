import Root2.Nat.Add.Cmp
import Root2.Nat.Cmp

@[simp]
def nat.mul (a b : nat) := match a with
  | nat.zero => nat.zero
  | nat.inc n => add b (mul n b)

theorem nat.mul_zero (a: nat) : mul zero a = zero := by
  trivial

theorem nat.mul_zero_r (a: nat) : mul a zero = zero := by
  match a with
    | nat.zero => trivial
    | nat.inc a₀ => simp; apply nat.mul_zero_r

theorem nat.mul_zero_imp (a b: nat) : a = nat.zero ∨ b = nat.zero -> mul a b = zero := by
  intro a_or_b_is_zero
  match a_or_b_is_zero with
  | .inl a_is_zero => rw [a_is_zero, mul_zero]
  | .inr b_is_zero => rw [b_is_zero, mul_zero_r]

theorem nat.mul_eq_zero (a b: nat) : mul a b = zero -> a = nat.zero ∨ b = nat.zero := by
  intro a_or_b_is_zero
  match a, b with
  | .zero, _ => exact Or.inl rfl
  | _, .zero => exact Or.inr rfl
  | .inc a₀, .inc b₀ => simp at a_or_b_is_zero

theorem nat.mul_eq_one (a b: nat) : mul a b = zero.inc -> a = nat.zero.inc ∧ b = nat.zero.inc := by
  intro ab_one
  match a, b with
  | .zero, _ => simp at ab_one
  | _, .zero => rw [nat.mul_zero_r] at ab_one;  contradiction
  | .inc .zero, .inc .zero => trivial
  | .inc (.inc a₀), .inc b₀ =>
    simp at ab_one
    rw [nat.add_inc] at ab_one
    contradiction
  | .inc a₀, .inc (.inc b₀) =>
    simp at ab_one
  
theorem nat.mul_gt_one {{ a b: nat }} : nat.inc nat.zero < nat.mul a b -> nat.zero.inc < a ∨ nat.zero.inc < b := by
  match a, b with
  | .zero, _ => simp
  | _, .zero => rw [nat.mul_zero_r]; simp
  | inc .zero, .inc .zero => simp
  | _, .inc (.inc b₀) =>
    intro
    apply Or.inr
    rw [nat.lt_inc_irr]
    exact nat.zero_lt_inc _
  | .inc (.inc a₀), _ =>
    intro
    apply Or.inl
    rw [nat.lt_inc_irr]
    exact nat.zero_lt_inc _


theorem nat.mul_one (a: nat) : mul (inc zero) a = a := by
  unfold mul
  rw [nat.mul_zero a, nat.add_comm, nat.add_zero]

theorem nat.mul_one_r (a: nat) : mul a (inc zero) = a := by
  match a with
  | nat.zero => trivial
  | nat.inc a₀ => simp; rw [nat.mul_one_r a₀]

theorem nat.mul_inc (a b: nat) : mul (inc b) a = add a (mul b a) := by
  trivial

theorem nat.mul_inc_r (a b: nat) : mul a (inc b) = add a (mul a b) := by
  match a with
  | nat.zero => trivial
  | nat.inc a₀ =>
    simp
    rw [nat.add_perm2, ←nat.add_perm0, nat.add_irr]
    apply nat.mul_inc_r

theorem nat.mul_irr_r {{a b c: nat}} : b = c -> mul a b = mul a c := by
  intro b_eq_c
  rw [b_eq_c]

theorem nat.mul_irr_l {{a b c: nat}} (a_gt_zero: nat.zero < a) : mul a b = mul a c -> b = c := by
  match b with
  | nat.zero => 
  rw [nat.mul_zero_r]
  cases c
  rw [nat.mul_zero_r]
  exact id
  rw [nat.mul_inc_r]
  intro x
  let _ := nat.lt_to_ne ((nat.add_gt_zero a_gt_zero) _) x
  contradiction
  | nat.inc b₀ =>
  rw [nat.mul_inc_r]
  match c with
  | nat.zero =>
  rw [nat.mul_zero_r]
  intro x
  let _ := nat.lt_to_ne ((nat.add_gt_zero a_gt_zero) _) (x.symm)
  contradiction
  | nat.inc c₀ =>
  rw [nat.mul_inc_r, nat.add_irr, nat.eq_inc_irr]
  apply nat.mul_irr_l
  assumption

theorem nat.mul_irr {{a b c: nat}} (a_gt_zero: nat.zero < a) : (mul a b = mul a c) = (b = c) := by
  rw [Iff.intro (nat.mul_irr_l a_gt_zero) (@nat.mul_irr_r a b c)]

theorem nat.mul_comm (a b: nat) : mul a b = mul b a := by
  cases a
  rw [nat.mul_zero, nat.mul_zero_r]
  rw [nat.mul_inc, nat.mul_inc_r]
  rw [nat.add_irr]
  apply nat.mul_comm

theorem nat.mul_add (a b c: nat) : mul a (add b c) = add (mul a b) (mul a c) := by
  match a with
  | nat.zero =>
  repeat rw [nat.mul_zero]
  trivial
  | nat.inc a₀ =>
  rw [nat.mul_inc, nat.mul_add a₀, nat.mul_inc, nat.mul_inc]
  rw [←nat.add_perm0 b, ←nat.add_perm0, nat.add_irr, ←nat.add_perm7]

theorem nat.add_mul (a b c: nat) : mul (add a b) c = add (mul a c) (mul b c) := by
  rw [nat.mul_comm, nat.mul_add, nat.mul_comm c, nat.mul_comm c]

theorem nat.mul_assoc (a b c: nat) : mul a (mul b c) = mul (mul a b) c := by
  match a with
  | nat.zero => match b with
    | nat.zero => simp
    | nat.inc b₀ =>
      unfold mul
      simp
  | nat.inc a₀ => 
    simp
    rw [nat.add_mul, nat.add_irr, nat.mul_assoc a₀]

theorem nat.mul_perm0 (a b c: nat) : mul a (mul b c) = mul (mul a b) c := by
  apply nat.mul_assoc

theorem nat.mul_perm1 (a b c: nat) : mul a (mul b c) = mul (mul a c) b := by
  rw [nat.mul_comm b c]
  apply nat.mul_assoc

theorem nat.mul_perm2 (a b c: nat) : mul a (mul b c) = mul (mul b a) c := by
  rw [nat.mul_comm b a]
  apply nat.mul_assoc

theorem nat.mul_perm3 (a b c: nat) : mul a (mul b c) = mul (mul b c) a := by
  rw [nat.mul_comm]

theorem nat.mul_perm4 (a b c: nat) : mul a (mul b c) = mul (mul c a) b := by
  rw [nat.mul_comm b c]
  rw [nat.mul_comm c a]
  apply nat.mul_assoc

theorem nat.mul_perm5 (a b c: nat) : mul a (mul b c) = mul (mul c b) a := by
  rw [nat.mul_comm b c, nat.mul_comm]

theorem nat.mul_perm6 (a b c: nat) : mul a (mul b c) = mul a (mul c b) := by
  simp
  rw [nat.mul_comm b c]

theorem nat.mul_perm7 (a b c: nat) : mul a (mul b c) = mul b (mul a c) := by
  rw [nat.mul_assoc, nat.mul_comm a b, ←nat.mul_assoc]

theorem nat.mul_perm8 (a b c: nat) : mul a (mul b c) = mul b (mul c a) := by
  rw [nat.mul_perm7, nat.mul_comm a c]

theorem nat.mul_perm9 (a b c: nat) : mul a (mul b c) = mul c (mul a b) := by
  rw [nat.mul_comm b c, nat.mul_perm7]

theorem nat.mul_perm10 (a b c: nat) : mul a (mul b c) = mul c (mul b a) := by
  rw [nat.mul_comm b c, nat.mul_perm8]
