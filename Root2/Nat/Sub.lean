import Root2.Nat
import Root2.Nat.Cmp
import Root2.Nat.Add
import Root2.Nat.Add.Cmp

@[simp]
def nat.checked_sub (a b: nat) : (b <= a) -> nat := 
  match b with
  | nat.zero => fun _ => a
  | nat.inc b₀ => match a with
    | nat.zero => fun h => h.elim
    | nat.inc a₀ => fun h => checked_sub a₀ b₀ (inc_le_to_le h)

theorem nat.checked_sub_dec : ∀ a b: nat, nat.zero < b -> (h: b <= a) -> a.checked_sub b h < a := by
  intro a b zero_lt_b b_le_a
  have zero_le_b := nat.lt_is_le _ _ zero_lt_b
  match a with 
  | nat.zero =>
      have b_eq_0 := nat.le_le_to_eq zero_le_b b_le_a
      rw [←b_eq_0] at zero_lt_b
      contradiction
  | nat.inc a₀ => match b with
    | nat.zero => contradiction
    | nat.inc b₀ =>
      unfold nat.checked_sub
      simp
      rw [←nat.le_inc] at b_le_a
      match b₀ with
      | nat.zero => simp; apply nat.a_lt_inc_a
      | nat.inc b₁ =>
        have checked_sub_ind := checked_sub_dec a₀ (nat.inc b₁) (nat.zero_lt_inc b₁) b_le_a
        have a_lt_inc_a := nat.a_lt_inc_a a₀
        exact (nat.lt_trans checked_sub_ind a_lt_inc_a)

theorem nat.checked_sub_less_eq : ∀ {{a b: nat}}, (h: b <= a) -> a.checked_sub b h <= a := by
  intro a b b_le_a
  match a with
    | nat.zero => match b with
      | nat.zero => simp; apply nat.le_id
    | nat.inc a₀ => match b with
      | nat.zero => simp; apply nat.le_id
      | nat.inc b₀ =>
        simp
        rw [nat.le_inc_irr] at b_le_a
        have x := nat.checked_sub_less_eq b_le_a
        have y := nat.a_le_inc_a a₀
        exact (nat.le_trans x y)

theorem nat.eq_sub {{a b: nat}} (h: b = a) : checked_sub a b (nat.eq_to_le h) = zero := by
  match a with
  | nat.zero => match b with
    | nat.zero => simp
  | nat.inc a₀ => match b with
    | nat.inc b₀ =>
      simp
      rw [nat.eq_inc_irr] at h
      apply nat.eq_sub
      assumption

theorem nat.add_to_sub {{a b c: nat}} (h: add a b = c) : checked_sub c b (nat.add_imp_le (nat.eq_to_le h)) = a := by
  match b with
  | nat.zero => simp; rw [nat.add_zero_r] at h; apply Eq.symm; assumption
  | nat.inc b₀ => match c with
    | nat.zero =>
      have ⟨ _, inc_b_eq_zero ⟩  := nat.add_ab_eq_zero a (inc b₀) h
      contradiction
    | nat.inc c₀ =>
      simp
      apply nat.add_to_sub
      rw [nat.add_inc, nat.eq_inc_irr] at h
      assumption

theorem nat.sub_to_add {{a b c: nat}} (h: b <= c) (s: checked_sub c b h = a) : add a b = c  := by
  match c with
  | nat.zero =>
    match b with
    | nat.zero => simp at s; rw [←s]; simp
  | nat.inc c₀ => match b with
    | nat.zero => simp at s; rw [nat.add_zero_r]; apply Eq.symm; assumption
    | nat.inc b₀ => rw [nat.add_inc, nat.eq_inc_irr]; simp at s; simp at h; apply nat.sub_to_add <;> assumption


theorem nat.checked_sub_aa : ∀ a: nat, a.checked_sub a (nat.eq_to_le rfl) = nat.zero := by
  intro a
  apply nat.add_to_sub
  rw [nat.add_zero]

theorem nat.checked_sub_zero : ∀ a: nat, a.checked_sub nat.zero (nat.zero_le _) = a := by
  intro a
  simp
