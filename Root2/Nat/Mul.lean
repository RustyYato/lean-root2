import Root2.Nat.Add
import Root2.Nat.Cmp

@[simp]
def nat.mul (a b : nat) := match a with
  | nat.zero => nat.zero
  | nat.inc n => add b (mul n b)

@[simp]
theorem nat.mul_zero (a: nat) : mul zero a = zero := by
  unfold mul
  simp

@[simp]
theorem nat.mul_zero_r (a: nat) : mul a zero = zero := by
  unfold mul
  match a with
    | nat.zero => simp
    | nat.inc a₀ => simp; apply nat.mul_zero_r

@[simp]
theorem nat.mul_one (a: nat) : mul (inc zero) a = a := by
  unfold mul
  rw [nat.mul_zero a, nat.add_comm, nat.add_zero]

@[simp]
theorem nat.mul_one_r (a: nat) : mul a (inc zero) = a := by
  unfold mul
  match a with
  | nat.zero => simp
  | nat.inc a₀ => simp; apply nat.mul_one_r

@[simp]
theorem nat.mul_inc (a b: nat) : mul (inc b) a = add a (mul b a) := by
  simp

@[simp]
theorem nat.mul_inc_r (a b: nat) : mul a (inc b) = add a (mul a b) := by
  unfold mul
  simp
  match a with
  | nat.zero => simp
  | nat.inc a₀ =>
    simp
    rw [nat.add_perm2, ←nat.add_perm0, nat.add_irr]
    apply nat.mul_inc_r

theorem nat.mul_irr_r {{a b c: nat}} : b = c -> mul a b = mul a c := by
  intro b_eq_c
  rw [b_eq_c]

@[simp]
theorem nat.mul_irr_l {{a b c: nat}} (a_gt_zero: nat.zero < a) : mul a b = mul a c -> b = c := by
  match a with
  | nat.zero => contradiction
  | nat.inc a₀ => simp; match b with
    | nat.zero =>
      simp
      intro zero_eq_ac
      rw [nat.add_comm] at zero_eq_ac
      have ⟨ _, c_eq_zero ⟩ := nat.add_ab_eq_zero (mul a₀ c) c (Eq.symm zero_eq_ac)
      exact (Eq.symm c_eq_zero)
    | nat.inc b₀ => match c with
      | nat.zero => simp
      | nat.inc c₀ => 
        simp
        rw [←nat.add_perm7, ←nat.add_perm7 a₀ c₀, nat.add_irr]
        rw [←nat.mul_inc, ←nat.mul_inc]
        intro x
        have y := nat.mul_irr_l a_gt_zero x
        assumption

theorem nat.mul_comm (a b: nat) : mul a b = mul b a := by
  match a with
  | nat.zero => match b with
    | nat.zero => simp
    | nat.inc b₀ =>
      unfold mul
      simp
  | nat.inc a₀ => match b with
    | nat.zero => simp
    | nat.inc b₀ => 
      rw  [nat.mul_inc, nat.mul_inc]
      rw  [nat.mul_inc_r, nat.mul_inc_r]
      simp
      rw [←nat.add_perm7, nat.add_irr, nat.add_irr]
      apply nat.mul_comm

@[simp]
theorem nat.add_distr (a b c: nat) : mul a (add b c) = add (mul a b) (mul a c) := by
  match b with
  | nat.zero => simp
  | nat.inc b₀ => simp; rw [←nat.add_perm0, nat.add_irr]; simp; apply nat.add_distr

theorem nat.mul_assoc (a b c: nat) : mul a (mul b c) = mul (mul a b) c := by
  match a with
  | nat.zero => match b with
    | nat.zero => simp
    | nat.inc b₀ =>
      unfold mul
      simp
  | nat.inc a₀ => 
    simp
    rw [nat.mul_comm (add _ _) c]
    simp
    rw [nat.mul_comm c b]
    simp
    rw [nat.mul_comm c (mul _ _)]
    apply nat.mul_assoc

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
