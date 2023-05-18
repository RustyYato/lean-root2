import Root2.Nat.Cmp
import Root2.Nat.Sub

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

theorem remainder.lt (a b: nat) : ∀ h, remainder a b h < b := by
  intro h
  unfold remainder
  
  match Compare.dec_lt a b with
  | .isTrue a_lt_b =>
    simp
    assumption
  | .isFalse a_lt_b =>
    simp
    apply remainder.lt
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