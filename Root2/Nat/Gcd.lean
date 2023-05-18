import Root2.Nat.Cmp
import Root2.Nat.Sub
import Root2.Divisible

def remainder (a b: nat): nat.zero < b -> nat :=
  fun zero_lt_b =>
    match Compare.dec_lt a b with
    | .isTrue _ => a
    | .isFalse _ => remainder (a.saturating_sub b) b zero_lt_b
decreasing_by {
  simp_wf
  apply nat.size_of_lt
  have : b <= a := (@nat.not_lt_is_sym_le _ _).mp (by assumption)
  have := @nat.sat_sub_le a b
  match @nat.sat_sub_le a b with
  | .inl _ => assumption
  | .inr sub_eq =>
  have := Compare.ord_implies_eq sub_eq
  match b with
  | .zero => contradiction
  | .inc b₀ => 
    apply nat.sat_sub_lt (nat.zero_lt_inc _)
    assumption
}

theorem remainder.induction {P : nat -> (b: nat) -> nat.zero < b -> Prop} : 
  (∀ (a b: nat), ∀ h, a < b -> P a b h) ->
  (∀ (a b: nat), ∀ h, ¬(a < b) -> P (a.saturating_sub b) b h -> P a b h) ->
  (∀a b h, P a b h)
 := fun base induct a b b_gt_zero => match Compare.dec_lt a b with
    | .isTrue a_lt_b => base a b b_gt_zero a_lt_b
    | .isFalse b_le_a => 
    induct a b b_gt_zero b_le_a (
      remainder.induction base induct _ _ b_gt_zero
    )
decreasing_by {
  simp_wf
  apply nat.size_of_lt
  have : b <= a := (@nat.not_lt_is_sym_le _ _).mp (by assumption)
  have := @nat.sat_sub_le a b
  match @nat.sat_sub_le a b with
  | .inl _ => assumption
  | .inr sub_eq =>
  have := Compare.ord_implies_eq sub_eq
  match b with
  | .zero => contradiction
  | .inc b₀ => 
    apply nat.sat_sub_lt (nat.zero_lt_inc _)
    assumption
}

theorem dec.pick_true : ∀(d: Decidable P) (p: P), d = Decidable.isTrue p := by
  intro d p 
  match d with
  | .isTrue q => rfl
  | .isFalse q => contradiction

theorem dec.pick_false : ∀(d: Decidable P) (p: ¬P), d = Decidable.isFalse p := by
  intro d p 
  match d with
  | .isTrue q => contradiction
  | .isFalse q => rfl

-- theorem remainder.template : ∀ a b h, remainder a b h = nat.zero -> divisible a b := by
--   apply remainder.induction
  
--   {
--     intro a b b_gt_zero a_lt_b
--     unfold remainder; rw [(dec.pick_true (Compare.dec_lt a b) a_lt_b)]; simp

--   }
  
--   {
--     intro a b b_gt_zero b_le_a prev
--     unfold remainder; rw [(dec.pick_false (Compare.dec_lt a b) b_le_a)]; simp

--   }

theorem remainder.lt : ∀ a b h, remainder a b h < b := by
  apply remainder.induction
  {
    intro a b b_gt_zero a_lt_b
    unfold remainder; rw [(dec.pick_true (Compare.dec_lt a b) a_lt_b)]; simp
    assumption
  }

  {
    intro a b b_gt_zero b_le_a prev
    unfold remainder; rw [(dec.pick_false (Compare.dec_lt a b) b_le_a)]; simp
    assumption
  }

theorem remainder.le : ∀ a b h, remainder a b h <= a := by
  apply remainder.induction
  
  {
    intro a b b_gt_zero a_lt_b
    unfold remainder; rw [(dec.pick_true (Compare.dec_lt a b) a_lt_b)]; simp
    apply nat.le_id
  }
  
  {
    intro a b b_gt_zero b_le_a prev
    unfold remainder; rw [(dec.pick_false (Compare.dec_lt a b) b_le_a)]; simp
    apply (nat.le_trans prev)
    apply nat.sat_sub_le
  }

theorem remainder.divisible : ∀ a b h, remainder a b h = nat.zero -> divisible a b := by
  apply remainder.induction
  
  {
    intro a b b_gt_zero a_lt_b
    unfold remainder; rw [(dec.pick_true (Compare.dec_lt a b) a_lt_b)]; simp
    intro a_eq_zero
    rw [a_eq_zero]
    apply divisible.zero
  }
  
  {
    intro a b b_gt_zero b_le_a prev
    unfold remainder; rw [(dec.pick_false (Compare.dec_lt a b) b_le_a)]; simp
    intro x
    have ⟨ x, prf ⟩  := prev x
    exists x.inc
    rw [nat.mul_inc_r]
    rw [←prf]
    rw [nat.add_comm, nat.sat_sub_add_inv]
    rw [←nat.not_lt_is_sym_le]
    assumption
  }

def gcd (a b: nat) : nat := match h:a with
| .zero => b
| .inc a₀ => gcd (remainder b a (by rw [h]; apply nat.zero_lt_inc)) a
decreasing_by {
  simp_wf
  apply nat.size_of_lt
  match a with
  | .inc a₀ =>
  conv => {
    rhs
    rw [←h]
  }
  apply remainder.lt b a₀.inc
}

def gcd.induction { P: nat -> nat -> Prop } :
  (∀a, P nat.zero a) ->
  (∀a b h, P (remainder b a h) a -> P a b) ->
  (∀ a b, P a b) := fun base induct a b => match a with
  | .zero => base b
  | .inc a₀ =>
    induct a₀.inc b (nat.zero_lt_inc _) (gcd.induction base induct _ _)
  decreasing_by {
    simp_wf
    apply nat.size_of_lt
    apply remainder.lt
  }

def coprime a b := gcd a b = nat.zero.inc

theorem gcd.zero_left: gcd nat.zero a = a := by 
  unfold gcd
  rfl

theorem gcd.le : ∀(a b: nat), gcd a b <= a ∧ gcd a b <= b ∨ a = nat.zero ∨ b = nat.zero := by
  apply gcd.induction
  intro b
  simp
  intro a b a_gt_zero prev
  match b with
  | .zero => simp
  | .inc b₀ =>
  match a with
  | .inc a₀ =>
  simp
  match prev with
  | .inr (.inl h) =>
    clear prev
    unfold gcd
    rw [h]
    unfold gcd
    apply And.intro
    apply nat.le_id
    have := remainder.divisible b₀.inc a₀.inc a_gt_zero h
    exact this.is_le (nat.zero_lt_inc _)
  | .inr (.inr h) =>  
    clear prev
    contradiction
  | .inl h =>
  have ⟨ l, _ ⟩ := h
  clear prev h
  unfold gcd
  simp
  apply And.intro
  apply nat.le_trans l
  apply Or.inl
  apply remainder.lt
  apply nat.le_trans l
  apply remainder.le
