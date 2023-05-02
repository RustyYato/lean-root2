import Root2.Nat.Cmp

@[simp]
def nat.add (a b : nat) := match a with
  | nat.zero => b
  | nat.inc n => nat.inc (add n b)

theorem nat.add_zero (a: nat) : add zero a = a := by
  trivial

theorem nat.add_zero_r (a: nat) : add a zero = a := by
  unfold add
  match a with
    | nat.zero => trivial
    | nat.inc a₀ => simp; apply nat.add_zero_r

theorem nat.add_ab_eq_zero (a b: nat) : add a b = zero -> a = nat.zero /\ b = nat.zero := by
  unfold add
  match a with
    | nat.zero => trivial
    | nat.inc a₀ => intro; trivial

theorem nat.add_inc (a b: nat) : add a (inc b) = inc (add a b) := by
  unfold add
  match a with
    | nat.zero => simp
    | nat.inc a₀ => simp; apply nat.add_inc

theorem nat.add_inc_r (a b: nat) : add (inc a) b = inc (add a b) := by
  match a with
    | nat.zero => trivial
    | nat.inc a₀ => trivial

theorem nat.add_comm (a b: nat) : add a b = add b a := by
  match a with
  | nat.zero => match b with
    | nat.zero => trivial
    | nat.inc b₀ => rw [nat.add_zero, nat.add_zero_r]
  | nat.inc a₀ => match b with
    | nat.zero => rw [nat.add_zero, nat.add_zero_r]
    | nat.inc b₀ =>
      repeat rw [nat.add_inc, nat.add_inc_r]
      rw [nat.add_comm a₀ b₀]

theorem nat.add_irr (a b c: nat) : (add a b = add a c) = (b = c) := by
  cases a
  rw [nat.add_zero, nat.add_zero]
  rw [nat.add_inc_r, nat.add_inc_r]
  rw [nat.eq_inc_irr]
  apply nat.add_irr

theorem nat.add_assoc (a b c: nat) : add a (add b c) = add (add a b) c := by
  match a with
  | nat.zero => repeat rw [nat.add_zero]
  | nat.inc a₀ => 
      repeat rw [nat.add_inc_r]
      rw [nat.add_assoc a₀]

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
  rw [nat.add_comm b]

theorem nat.add_perm7 (a b c: nat) : add a (add b c) = add b (add a c) := by
  rw [nat.add_assoc, nat.add_comm a b, ←nat.add_assoc]

theorem nat.add_perm8 (a b c: nat) : add a (add b c) = add b (add c a) := by
  rw [nat.add_perm7, nat.add_comm a c]

theorem nat.add_perm9 (a b c: nat) : add a (add b c) = add c (add a b) := by
  rw [nat.add_comm b c, nat.add_perm7]

theorem nat.add_perm10 (a b c: nat) : add a (add b c) = add c (add b a) := by
  rw [nat.add_comm b c, nat.add_perm8]
