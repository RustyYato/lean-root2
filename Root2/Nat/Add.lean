import Root2.Nat

@[simp]
def nat.add (a b : nat) := match a with
  | nat.zero => b
  | nat.inc n => nat.inc (add n b)

@[simp]
theorem nat.add_zero (a: nat) : add zero a = a := by
  unfold add
  simp

@[simp]
theorem nat.add_zero_r (a: nat) : add a zero = a := by
  unfold add
  match a with
    | nat.zero => simp
    | nat.inc a₀ => simp; apply nat.add_zero_r

@[simp]
theorem nat.add_ab_eq_zero (a b: nat) : add a b = zero -> a = nat.zero /\ b = nat.zero := by
  unfold add
  match a with
    | nat.zero => simp; intro b_eq_zero; simp; assumption
    | nat.inc a₀ => simp

@[simp]
theorem nat.add_inc (a b: nat) : add a (inc b) = inc (add a b) := by
  unfold add
  match a with
    | nat.zero => simp
    | nat.inc a₀ => simp; apply nat.add_inc

@[simp]
theorem nat.add_inc_r (a b: nat) : add (inc a) b = inc (add a b) := by
  unfold add
  match a with
    | nat.zero => simp
    | nat.inc a₀ => simp

theorem nat.add_comm (a b: nat) : add a b = add b a := by
  match a with
  | nat.zero => match b with
    | nat.zero => simp
    | nat.inc b₀ => 
      unfold add
      simp
  | nat.inc a₀ => match b with
    | nat.zero => simp
    | nat.inc b₀ =>
      simp
      apply nat.add_comm

@[simp]
theorem nat.add_irr (a b c: nat) : add a b = add a c <-> b = c := by
  apply Iff.intro
  . match a with
      | nat.zero => simp; exact id
      | nat.inc a₀ =>simp; intro _ ; apply (nat.add_irr a₀ b c).mp; assumption
  . match a with
      | nat.zero => simp; exact id
      | nat.inc a₀ =>simp; intro _ ; apply (nat.add_irr a₀ b c).mpr; assumption

theorem nat.add_assoc (a b c: nat) : add a (add b c) = add (add a b) c := by
  match a with
  | nat.zero => match b with
    | nat.zero => simp
    | nat.inc b₀ => 
      unfold add
      simp
  | nat.inc a₀ => match b with
    | nat.zero => simp
    | nat.inc b₀ =>
      simp
      apply nat.add_assoc

theorem nat.add_perm0 (a b c: nat) : add a (add b c) = add (add a b) c := by
  apply nat.add_assoc

theorem nat.add_perm1 (a b c: nat) : add a (add b c) = add (add a c) b := by
  rw [nat.add_comm b c]
  apply nat.add_assoc

theorem nat.add_perm2 (a b c: nat) : add a (add b c) = add (add b a) c := by
  rw [nat.add_comm b a]
  apply nat.add_assoc

theorem nat.add_perm3 (a b c: nat) : add a (add b c) = add (add b c) a := by
  rw [nat.add_comm]

theorem nat.add_perm4 (a b c: nat) : add a (add b c) = add (add c a) b := by
  rw [nat.add_comm b c]
  rw [nat.add_comm c a]
  apply nat.add_assoc

theorem nat.add_perm5 (a b c: nat) : add a (add b c) = add (add c b) a := by
  rw [nat.add_comm b c, nat.add_comm]

theorem nat.add_perm6 (a b c: nat) : add a (add b c) = add a (add c b) := by
  simp
  apply nat.add_comm

theorem nat.add_perm7 (a b c: nat) : add a (add b c) = add b (add a c) := by
  rw [nat.add_assoc, nat.add_comm a b, ←nat.add_assoc]

theorem nat.add_perm8 (a b c: nat) : add a (add b c) = add b (add c a) := by
  rw [nat.add_perm7, nat.add_comm a c]

theorem nat.add_perm9 (a b c: nat) : add a (add b c) = add c (add a b) := by
  rw [nat.add_comm b c, nat.add_perm7]

theorem nat.add_perm10 (a b c: nat) : add a (add b c) = add c (add b a) := by
  rw [nat.add_comm b c, nat.add_perm8]
