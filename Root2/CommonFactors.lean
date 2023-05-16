import Root2.Divisible.DivRem
import Root2.Nat.Sub.Mul

def gcd (a b : nat): nat := 
  match h:ord_imp a b with
  | .Eq => a
  | .Less => match _h₀:a with
    | .zero => b
    | .inc a₀ =>
      have : nat.add a (nat.saturating_sub b a) < nat.add a b := by
        rw [_h₀]
        rw [nat.add_comm, nat.sat_sub_add_inv]
        rw [nat.add_comm, nat.lt_add_const_irr]
        apply nat.zero_lt_inc
        apply Or.inl
        assumption
      gcd a (b.saturating_sub a)
  | .Greater => match _h₀:b with
    | .zero => a
    | .inc b₀ =>
      have : nat.add (nat.saturating_sub a b) b < nat.add a b := by
        rw [_h₀]
        rw [nat.sat_sub_add_inv]
        rw [nat.lt_add_const_irr]
        apply nat.zero_lt_inc
        apply Or.inl
        rw [Compare.ord_flip]
        assumption
      gcd (a.saturating_sub b) b
  termination_by _ => nat.add a b
  decreasing_by {
    simp_wf
    apply nat.size_of_lt
    assumption
  }

def gcd.le (a b: nat) : gcd a b <= a ∧ gcd a b <= b ∨ a = nat.zero ∨ b = nat.zero := by
  unfold gcd 
  split <;> simp
  {
    apply Or.inl
    apply And.intro
    apply nat.le_id
    have : a = b  := by apply ord_imp_eq; assumption
    rw [this]
    apply nat.le_id
  }
  {
    match a with
    | .zero =>
      apply Or.inr
      apply Or.inl
      rfl
    | .inc a₀ =>
      apply Or.inl
      simp
      have : nat.inc (nat.add a₀ (nat.saturating_sub b (nat.inc a₀))) < nat.inc (nat.add a₀ b) := by
        rw [nat.add_comm, ←nat.add_inc, nat.sat_sub_add_inv, ←nat.add_inc_r]
        rw [nat.add_comm, nat.lt_add_const_irr]
        apply nat.zero_lt_inc
        apply Or.inl
        assumption
      match gcd.le a₀.inc (b.saturating_sub a₀.inc) with
      | .inr (.inl _) => contradiction
      | .inr (.inr sub_eq_zero) =>
        rw [sub_eq_zero]
        unfold gcd
        simp
        apply And.intro
        apply nat.le_id
        apply Or.inl
        assumption
      | .inl h =>
        have ⟨ l, r ⟩ := h
        apply And.intro
        assumption
        clear l
        exact nat.le_trans r nat.sat_sub_le
  }
  {
    match b with
    | .zero =>
      apply Or.inr
      apply Or.inr
      rfl
    | .inc b₀ =>
      apply Or.inl
      simp
      have : nat.add (nat.saturating_sub a (nat.inc b₀)) (nat.inc b₀) < nat.add a (nat.inc b₀) := by
        rw [nat.sat_sub_add_inv, nat.lt_add_const_irr]
        apply nat.zero_lt_inc
        apply Or.inl
        rw [Compare.ord_flip]
        assumption
      match gcd.le (a.saturating_sub b₀.inc) b₀.inc with
      | .inr (.inl sub_eq_zero) => 
        rw [sub_eq_zero]
        unfold gcd
        simp
        apply And.intro
        apply Or.inl
        rw [Compare.ord_flip]
        assumption
        apply nat.le_id
      | .inr (.inr sub_eq_zero) =>
        contradiction
      | .inl h =>
        have ⟨ l, r ⟩ := h
        apply And.intro
        exact nat.le_trans l nat.sat_sub_le
        assumption
  }
  termination_by _ => nat.add a b
  decreasing_by {
    simp_wf
    apply nat.size_of_lt
    assumption
  }

def gcd.comm (a b: nat) : gcd a b = gcd b a := by
  unfold gcd
  split <;> simp
  have : a = b := by
    apply ord_imp_eq
    assumption
  {
    split
    rw [this]
    next h => {
      rw [this, ord_imp_id] at h
      contradiction
    }
    next h => {
      rw [this, ord_imp_id] at h
      contradiction
    }
  }
  {
    match a with
    | .zero =>
    simp
    split
    have :  b = nat.zero := by
      apply ord_imp_eq
      assumption
    rw [this]
    next h₀ h₁ => {
      rw [ord_imp_flip] at h₁
      simp at h₁
      rw [h₁] at h₀
      contradiction
    }
    rfl
    | .inc a₀ =>
    simp
    {
      split
      next h₀ h₁ => {
        rw [ord_imp_flip] at h₁ 
        rw [h₁] at h₀
        contradiction
      }
      next h₀ h₁ => {
        rw [ord_imp_flip] at h₁ 
        rw [h₁] at h₀
        contradiction
      }
      have : nat.inc (nat.add a₀ (nat.saturating_sub b (nat.inc a₀))) < nat.add a₀.inc b := by
        rw [←nat.add_inc_r, nat.add_comm, nat.sat_sub_add_inv, nat.add_comm, nat.lt_add_const_irr]
        apply nat.zero_lt_inc
        apply Or.inl
        assumption
      apply gcd.comm
    }
  }
  {
    match b with
    | .zero =>
    simp
    split
    next h₀ h₁ => {
      rw [ord_imp_flip] at h₁ 
      rw [h₁] at h₀
      contradiction
    }
    rfl
    next h₀ h₁ => {
      rw [ord_imp_flip] at h₁ 
      rw [h₁] at h₀
      contradiction
    }
    | .inc b₀ =>
    simp
    split
    next h₀ h₁ => {
      rw [ord_imp_flip] at h₁ 
      rw [h₁] at h₀
      contradiction
    }
    have : nat.add (nat.saturating_sub a (nat.inc b₀)) (nat.inc b₀) < nat.add a b₀.inc := by
      rw [nat.sat_sub_add_inv, nat.lt_add_const_irr]
      apply nat.zero_lt_inc
      apply Or.inl
      assumption
    apply gcd.comm
    next h₀ h₁ => {
      rw [ord_imp_flip] at h₁ 
      rw [h₁] at h₀
      contradiction
    }
  }
  termination_by _ => nat.add a b
  decreasing_by {
    simp_wf
    apply nat.size_of_lt
    
    assumption
  }

def gcd.correct {{ a b: nat }} (c: nat) :
  divisible a c ->
  divisible b c ->
  divisible (gcd a b) c := by
  intro divis_a_c divis_b_c
  unfold gcd
  simp
  split
  assumption
  {
    match a with
    | .zero => assumption
    | .inc a₀ =>
    have : nat.inc (nat.add a₀ (nat.saturating_sub b (nat.inc a₀))) < nat.inc (nat.add a₀ b) := by
      rw [←nat.add_inc_r, ←nat.add_inc_r]
      rw [nat.add_comm, nat.sat_sub_add_inv]
      rw [nat.add_comm, nat.lt_add_const_irr]
      apply nat.zero_lt_inc
      apply Or.inl
      assumption
    apply gcd.correct
    assumption
    have ⟨ x, prf₀ ⟩ := divis_a_c
    have ⟨ y, prf₁ ⟩ := divis_b_c
    rw [prf₀, prf₁]
    exists y.saturating_sub x
    rw [nat.mul_sat_sub_left]
  }
  {
    match b with
    | .zero => assumption
    | .inc b₀ =>
      simp
      have : nat.add (nat.saturating_sub a (nat.inc b₀)) (nat.inc b₀) < nat.add a (nat.inc b₀) := by
        rw [nat.sat_sub_add_inv, nat.lt_add_const_irr]
        apply nat.zero_lt_inc
        apply Or.inl
        rw [Compare.ord_flip]
        assumption
      apply gcd.correct
      {
        have ⟨ x, prf₀ ⟩ := divis_b_c
        have ⟨ y, prf₁ ⟩ := divis_a_c
        rw [prf₀, prf₁]
        exists y.saturating_sub x
        rw [nat.mul_sat_sub_left]
      }
      assumption
  }
  termination_by _ => nat.add a b
  decreasing_by {
    simp_wf
    apply nat.size_of_lt
    assumption
  }
