import Root2.Divisible.DivRem
import Root2.Nat.Sub.Mul

inductive Gcd : nat -> nat -> Type where
| Id : ∀ a, Gcd a a
| Left : ∀ a, nat.zero < a -> Gcd a nat.zero
| Right : ∀ a, nat.zero < a -> Gcd nat.zero a
| LeftSucc : ∀ a b, nat.zero < a -> nat.zero < b -> b > a -> Gcd a (b.saturating_sub a) -> Gcd a b
| RightSucc : ∀ a b, nat.zero < a -> nat.zero < b -> b < a -> Gcd (a.saturating_sub b) b -> Gcd a b

@[simp]
def Gcd.eval (g: Gcd a b) : nat := 
  match g with
  | .Id x | .Left x _ | .Right x _ => x
  | .LeftSucc _ _ _ _ _ g => g.eval
  | .RightSucc _ _ _ _ _ g => g.eval

@[simp]
def Gcd.depth (g: Gcd a b) : Nat := 
  match g with
  | .Id x | .Left x _ | .Right x _ => 0
  | .LeftSucc _ _ _ _ _ g => g.depth + 1
  | .RightSucc _ _ _ _ _ g => g.depth + 1

def Gcd.calc (a b: nat): Gcd a b := 
  match h:ord_imp a b with
  | .Eq => by
    rw [ord_imp_eq h]
    exact .Id b
  | .Less => match _h₀:a with
    | .zero => .Right b (Compare.ord_implies_lt h)
    | .inc a₀ => by
      apply Gcd.LeftSucc
      apply nat.zero_lt_inc
      apply Compare.ord_implies_lt
      exact nat.gt_implies_gt_zero h
      assumption
      have : nat.inc (nat.add a₀ (nat.saturating_sub b (nat.inc a₀))) < nat.inc (nat.add a₀ b) := by
        rw [←nat.add_inc_r, ←nat.add_inc_r]
        rw [←_h₀]
        rw [nat.add_comm, nat.sat_sub_add_inv]
        rw [nat.add_comm, nat.lt_add_const_irr]
        rw [_h₀]
        apply nat.zero_lt_inc
        apply Or.inl
        rw [_h₀]
        assumption
      apply Gcd.calc
  | .Greater => match h₀:b with
    | .zero => .Left a (Compare.ord_implies_lt (ord_imp_flip.mp h))
    | .inc b₀ =>by
      apply Gcd.RightSucc
      exact nat.gt_implies_gt_zero (ord_imp_flip.mp h)
      apply nat.zero_lt_inc
      apply Compare.ord_implies_gt
      assumption
      have : nat.add (nat.saturating_sub a (nat.inc b₀)) (nat.inc b₀) < nat.add a (nat.inc b₀) := by
        rw [←h₀]
        rw [nat.sat_sub_add_inv]
        rw [nat.lt_add_const_irr]
        rw [h₀]
        apply nat.zero_lt_inc
        apply Or.inl
        rw [Compare.ord_flip]
        rw [h₀]
        assumption
      apply Gcd.calc
  termination_by _ => nat.add a b
  decreasing_by {
    simp_wf
    apply nat.size_of_lt
    assumption
  }

def gcd (a b: nat): nat := (Gcd.calc a b).eval

theorem Gcd.le (g: Gcd a b) : g.eval <= a ∧ g.eval <= b ∨ a = nat.zero ∨ b = nat.zero := by
  match g with
  | .Id a =>
    simp
    apply Or.inl
    apply nat.le_id
  | .Left a _ => simp
  | .Right b _ => simp
  | .LeftSucc _ _ _ _ _ g =>
    simp
    match g.le with
    | .inl h =>
      have ⟨ _, gcd_le_sub ⟩ := h
      apply Or.inl
      apply And.intro
      assumption
      exact nat.le_trans gcd_le_sub nat.sat_sub_le
    | .inr (.inl h) =>
      apply Or.inr
      exact Or.inl h
    | .inr (.inr h) =>
      have := (nat.comp_dec · (nat.sat_sub_eq_zero h))
      contradiction
  | .RightSucc _ _ _ _ _ g =>
    simp
    match g.le with
    | .inl h =>
      have ⟨ gcd_le_sub, _ ⟩ := h
      apply Or.inl
      apply And.intro
      exact nat.le_trans gcd_le_sub nat.sat_sub_le
      assumption
    | .inr (.inl h) =>
      have := (nat.comp_dec · (nat.sat_sub_eq_zero h))
      contradiction
    | .inr (.inr h) =>
      apply Or.inr
      exact Or.inr h

def gcd.le (a b: nat) : gcd a b <= a ∧ gcd a b <= b ∨ a = nat.zero ∨ b = nat.zero := by
  apply Gcd.le


def Gcd.id (g: Gcd a a) : g.eval = a := by
  have := @nat.not_lt_id a
  match g with
  | .Id a => simp

def Gcd.right (g: Gcd nat.zero a) : g.eval = a := by
  have := nat.not_lt_zero a
  match g with
  | .Id _ | .Right _ _ => simp

def Gcd.left (g: Gcd a nat.zero) : g.eval = a := by
  cases g
  simp
  simp
  contradiction
  contradiction
  contradiction

def Gcd.comm (f: Gcd a b) (r: Gcd b a) : f.eval = r.eval := by
  cases f
  rw [r.id]
  rfl
  rw [r.right]
  simp
  rw [r.left]
  simp
  simp
  {
    have := @nat.not_lt_id a
    cases r
    contradiction
    contradiction
    contradiction
    have b_lt_a : b < a := by assumption
    have a_lt_b : a < b := by assumption
    have := nat.lt_trans a_lt_b b_lt_a
    contradiction
    apply Gcd.comm
  }
  {
    have := @nat.not_lt_id a
    cases r
    contradiction
    contradiction
    contradiction
    simp
    apply Gcd.comm
    have b_lt_a : b < a := by assumption
    have a_lt_b : a < b := by assumption
    have := nat.lt_trans a_lt_b b_lt_a
    contradiction
  }

def gcd.comm (a b: nat) : gcd a b = gcd b a := by
  apply Gcd.comm

def Gcd.correct (g: Gcd a b) :
  divisible a c ->
  divisible b c ->
  divisible g.eval c := by
  intro divis_a_c divis_b_c
  match g with
  | .Id _ | .Left _ _ | .Right _ _ =>
    simp
    assumption
  | .RightSucc _ _ _ _ _ _ =>
    simp
    apply Gcd.correct
    {
      have ⟨ x, prf₀ ⟩ := divis_a_c
      have ⟨ y, prf₁ ⟩ := divis_b_c
      exists x.saturating_sub y
      rw [nat.mul_sat_sub_left]
      rw [prf₀, prf₁]
    }
    assumption
  | .LeftSucc _ _ _ _ _ _ =>
    simp
    apply Gcd.correct
    assumption
    {
      have ⟨ x, prf₀ ⟩ := divis_a_c
      have ⟨ y, prf₁ ⟩ := divis_b_c
      exists y.saturating_sub x
      rw [nat.mul_sat_sub_left]
      rw [←prf₀, ←prf₁]
    }

def gcd.correct :
  divisible a c ->
  divisible b c ->
  divisible (gcd a b) c := by
  apply Gcd.correct

def Gcd.correct_rev (g: Gcd a b) :
  divisible g.eval c ->
  divisible a c ∧
  divisible b c := by
  intro divis_g_c
  match g with
  | .Id _ =>
    simp at divis_g_c
    apply And.intro <;> assumption
  | .Left _ _ =>
    simp at divis_g_c
    apply And.intro
    assumption
    apply divisible.zero
  | .Right _ _ =>
    simp at divis_g_c
    apply And.intro
    apply divisible.zero
    assumption
  | .RightSucc _ _ _ _ _ g =>
    simp at divis_g_c
    have ⟨ divis_sub_c, divis_b_c ⟩  := Gcd.correct_rev g divis_g_c
    apply And.intro
    {
      have ⟨ x, prf₀ ⟩ := divis_sub_c
      have ⟨ y, prf₁ ⟩ := divis_b_c
      exists x.add y
      rw [nat.mul_add, ←prf₀, ←prf₁]
      rw [nat.sat_sub_add_inv]
      apply Or.inl
      assumption
    }
    assumption
  | .LeftSucc _ _ _ _ _ g =>
    simp at divis_g_c
    have ⟨ divis_sub_c, divis_b_c ⟩  := Gcd.correct_rev g divis_g_c
    apply And.intro
    assumption
    {
      have ⟨ x, prf₀ ⟩ := divis_sub_c
      have ⟨ y, prf₁ ⟩ := divis_b_c
      exists x.add y
      rw [nat.mul_add, ←prf₀, ←prf₁]
      rw [nat.add_comm, nat.sat_sub_add_inv]
      apply Or.inl
      assumption
    }

def gcd.correct_rev :
  divisible (gcd a b) c ->
  divisible a c ∧ 
  divisible b c := by
  apply Gcd.correct_rev
