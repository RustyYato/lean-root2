import Root2.Nat
import Root2.Nat.Cmp
import Root2.Nat.Add
import Root2.Nat.Add.Cmp

@[simp]
def nat.checked_sub (a b: nat) : (b <= a) -> nat := 
  match b with
  | nat.zero => fun _ => a
  | nat.inc b₀ => match a with
    | nat.zero => fun h => (nat.le_inc_zero h).elim
    | nat.inc a₀ => fun h => checked_sub a₀ b₀ (inc_le_to_le h)

@[simp]
def nat.saturating_sub (a b: nat) : nat := 
  match b with
  | nat.zero => a
  | nat.inc b₀ => match a with
    | nat.zero => nat.zero
    | nat.inc a₀ => saturating_sub a₀ b₀

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

theorem nat.checked_sub_le : ∀ {{a b: nat}}, (h: b <= a) -> a.checked_sub b h <= a := by
  intro a b b_le_a
  match a with
    | nat.zero => match b with
      | nat.zero => simp
    | nat.inc a₀ => match b with
      | nat.zero => simp; apply nat.le_id
      | nat.inc b₀ =>
        simp
        rw [nat.le_inc_irr] at b_le_a
        have x := nat.checked_sub_le b_le_a
        have y := nat.a_le_inc_a a₀
        exact (nat.le_trans x y)

theorem nat.checked_sub_lt : ∀ {{a b: nat}}, (h: b <= a) -> (nat.zero < b) -> a.checked_sub b h < a := by
  intro a b b_le_a b_nz
  match a with
    | .zero => match b with
      | .zero => contradiction
    | .inc a₀ => match b with
      | .inc .zero =>
        simp
        apply nat.a_lt_inc_a
      | .inc (.inc b₀) =>
        simp
        rw [nat.le_inc_irr] at b_le_a
        have x := nat.checked_sub_lt b_le_a b_nz
        have y := nat.a_lt_inc_a a₀
        exact (nat.lt_trans x y)

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


theorem nat.add_to_sub_gen {{a b c: nat}} (h: add a b = c) : ∀h₀, checked_sub c b h₀ = a := by
  intro
  match b with
  | nat.zero => simp; rw [nat.add_zero_r] at h; apply Eq.symm; assumption
  | nat.inc b₀ => match c with
    | nat.zero =>
      have ⟨ _, inc_b_eq_zero ⟩  := nat.add_ab_eq_zero a (inc b₀) h
      contradiction
    | nat.inc c₀ =>
      simp
      apply nat.add_to_sub_gen
      rw [nat.add_inc, nat.eq_inc_irr] at h
      assumption

theorem nat.add_to_sub {{a b c: nat}} (h: add a b = c) : checked_sub c b (nat.add_imp_le (nat.eq_to_le h)) = a := by
  apply add_to_sub_gen <;> assumption


theorem nat.add_to_sub_le {{a b c: nat}} (h: add a b <= c) : ∀ h, a <= checked_sub c b h := by
  intro b_le_c
  match b with
  | .zero =>
    simp
    rw [nat.add_zero_r] at h
    assumption
  | .inc b₀ =>
  match c with
  | nat.zero => 
    cases b_le_c <;> contradiction
  | nat.inc c₀ =>
    simp
    rw [nat.add_inc, nat.le_inc_irr] at h
    apply nat.add_to_sub_le h

theorem nat.sub_to_add {{a b c: nat}} (h: b <= c) (s: checked_sub c b h = a) : add a b = c  := by
  match c with
  | nat.zero =>
    match b with
    | nat.zero => simp at s; rw [←s]; simp
  | nat.inc c₀ => match b with
    | nat.zero => simp at s; rw [nat.add_zero_r]; apply Eq.symm; assumption
    | nat.inc b₀ => rw [nat.add_inc, nat.eq_inc_irr]; simp at s; simp at h; apply nat.sub_to_add <;> assumption

theorem nat.sub_add {{ a b c }} (h: b <= c) : (checked_sub c b h = a) <-> (add a b = c) := by
  apply Iff.intro
  intro cs
  exact nat.sub_to_add h cs
  intro add
  exact nat.add_to_sub add

theorem nat.checked_sub_aa : ∀ a: nat, a.checked_sub a (nat.eq_to_le rfl) = nat.zero := by
  intro a
  apply nat.add_to_sub
  rw [nat.add_zero]

theorem nat.checked_sub_zero : ∀ a: nat, ∀ {h}, a.checked_sub nat.zero h = a := by
  intro a
  match a with
  | .zero =>
    intro
    simp
  | .inc a₀ =>
    intro
    simp

theorem nat.checked_zero_sub : ∀ a: nat, (h: a <= nat.zero) -> nat.zero.checked_sub a h = nat.zero := by
  intro a h
  match a with
  | .zero => trivial
  | .inc a₀ => cases h <;> contradiction

theorem nat.sub_add_inv (h: b <= a) : add (checked_sub a b h) b = a := by
  match a with
  | .zero =>
    rw [nat.checked_zero_sub]
    simp
    exact nat.le_zero b h
  | .inc a₀ =>
    match b with
    | .zero =>
      rw [nat.checked_sub_zero, nat.add_zero_r]
    | .inc b₀ =>
      simp
      rw [nat.add_inc, nat.eq_inc_irr]
      apply nat.sub_add_inv

theorem nat.sat_sub_add_inv2 : saturating_sub (add a b) a = b := by
  match a with
  | .zero =>
    simp
  | .inc a₀ =>
    simp
    apply nat.sat_sub_add_inv2

theorem nat.sat_sub_zero (a_le_b: a <= b) : saturating_sub a b = nat.zero := by
  match a with
  | .zero =>
    unfold saturating_sub
    split <;> simp
  | .inc a₀ =>
  match b with
  | .inc b₀ =>
  simp
  apply nat.sat_sub_zero
  assumption

theorem nat.sat_sub_eq_zero (sub_eq_zero: saturating_sub a b = nat.zero) : a <= b := by
  match a with
  | .zero => apply nat.zero_le
  | .inc a₀ =>
  match b with
  | .inc b₀ =>
  rw [nat.le_inc_irr]
  apply nat.sat_sub_eq_zero
  assumption

theorem nat.sat_sub_add_inv (h: b <= a) : add (saturating_sub a b) b = a := by
  match a with
  | .zero =>
    unfold saturating_sub
    have b_eq_zero := nat.le_zero b h
    rw [b_eq_zero]
    simp
  | .inc a₀ =>
    match b with
    | .zero =>
      simp
      rw [nat.add_zero_r]
    | .inc b₀ =>
      simp
      rw [nat.add_inc, nat.eq_inc_irr]
      apply nat.sat_sub_add_inv
      assumption

theorem nat.sat_sub_gt_zero (h: b < a) : nat.zero < saturating_sub a b := by
  match a with
  | .zero =>
    have := nat.not_lt_zero b
    contradiction
  | .inc a₀ =>
    match b with
    | .zero =>
      simp
      assumption
    | .inc b₀ =>
      simp
      apply nat.sat_sub_gt_zero
      assumption

theorem nat.sat_sub_le : saturating_sub a b <= a := by
  match a with
  | .zero => rw [nat.sat_sub_zero (nat.zero_le _)]; apply nat.zero_le
  | .inc a₀ =>
    match b with
    | .zero =>
      simp
      exact nat.le_id _
    | .inc b₀ =>
      simp
      have := @nat.sat_sub_le a₀ b₀
      apply nat.le_trans this
      apply nat.a_le_inc_a

theorem nat.sat_sub_common : nat.saturating_sub (nat.add a b) (nat.add a c) = nat.saturating_sub b c := by
  match a with
  | .zero => simp
  | .inc a₀ =>
    simp
    apply nat.sat_sub_common

theorem nat.sat_sub_id : nat.saturating_sub a a = nat.zero := by
  match a with
  | .zero => simp
  | .inc a₀ =>
    simp
    apply nat.sat_sub_id

theorem nat.sub_equality_left : a = b -> ∀h₀ h₁, checked_sub a c h₀ = checked_sub b c h₁ := by
  intro a_eq_b h₀ h₁
  match a, b with
  | .zero, .zero => simp
  | .inc a₀, .inc b₀ =>
    rw [eq_inc_irr] at a_eq_b
    match c with
    | .zero =>
      simp
      assumption
    | .inc c₀ =>
      simp
      apply nat.sub_equality_left
      assumption
  | .inc _, .zero | .zero, .inc _ => contradiction

theorem eq_le [Compare α] {{a b c: α}} (a_eq_b: a = b) (c_le_a: c <= a) : c <= b := by
  rw [←a_eq_b]
  assumption

theorem nat.sub_equality_left_prf (a_eq_b: a = b) : ∀h₀ : c <= a, checked_sub a c h₀ = checked_sub b c (eq_le a_eq_b h₀) := by
  intro h₀
  match a, b with
  | .zero, .zero => simp
  | .inc a₀, .inc b₀ =>
    rw [eq_inc_irr] at a_eq_b
    match c with
    | .zero =>
      simp
      assumption
    | .inc c₀ =>
      simp
      apply nat.sub_equality_left
      assumption
  | .inc _, .zero | .zero, .inc _ => contradiction

theorem nat.sub_equality_right : a = b -> ∀h₀ h₁, checked_sub c a h₀ = checked_sub c b h₁ := by
  intro a_eq_b h₀ h₁
  match c with
  | .zero => repeat rw [checked_zero_sub]
  | .inc c₀ =>
    match a, b with
    | .zero, .zero => simp
    | .inc a₀, .inc b₀ =>
      rw [eq_inc_irr] at a_eq_b
      simp
      apply nat.sub_equality_right
      assumption
    | .inc _, .zero | .zero, .inc _ => contradiction
