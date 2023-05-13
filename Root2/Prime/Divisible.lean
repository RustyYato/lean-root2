import Root2.Prime
import Root2.Divisible
import Root2.Nat.Sub.Add
import Root2.Nat.Sub.Mul

theorem divisible.sub_r {{a b: nat}} (d: divisible a b) (b_le_a: b <= a) : divisible (a.checked_sub b b_le_a) b := by
  match a with
  | nat.zero =>
    exists nat.zero
    rw [nat.checked_zero_sub, nat.mul_zero_r]
  | .inc a₀ =>
  have ⟨ q, prf ⟩ := d
  have q_ge_one : nat.zero.inc <= q := by
    match q with
    | .zero =>
      rw [nat.mul_zero_r] at prf
      contradiction
    | .inc _ =>
      rw [nat.le_inc_irr]
      apply nat.zero_le
  match q with
  | .inc q₀ =>
  exists q₀
  rw [nat.sub_add, prf, nat.add_comm, ←nat.mul_inc_r]

theorem divisible.add_r {{a b: nat}} (d: divisible a b) : divisible (nat.add a b) b := by
  have ⟨ q, prf ⟩ := d
  exists q.inc
  rw [prf]
  rw [nat.mul_inc_r, nat.add_comm]

theorem divisible.sub {{a b: nat}} (b_le_a: b <= a) (d: divisible (a.checked_sub b b_le_a) b) : divisible a b := by
  have d_add := d.add_r
  rw [nat.sub_add_inv b_le_a] at d_add
  assumption

theorem divisible.sub_mul {{a b c: nat}} (b_le_a: b.mul c <= a) (d: divisible (a.checked_sub (b.mul c) b_le_a) b) : divisible a b := by
  match c with
  | .zero =>
    have sub_eq := @nat.sub_equality_right (nat.mul b nat.zero) nat.zero a (by rw [nat.mul_zero_r b]) (by
      rw [nat.mul_zero_r b]
      exact nat.zero_le _) (by
      exact nat.zero_le _)
    rw [sub_eq] at d
    clear sub_eq
    rw [nat.checked_sub_zero] at d
    assumption
  | .inc c₀ =>
    have sub_eq := @nat.sub_equality_right (nat.mul b c₀.inc) (nat.add b (nat.mul b c₀)) a (by
      rw [nat.mul_inc_r]) (by assumption) (by rw [←nat.mul_inc_r]; assumption)
    rw [sub_eq] at d
    clear sub_eq
    rw [nat.sub_add_to_sub_sub_right] at d
    apply (@divisible.sub (a.checked_sub (b.mul c₀)  _) b _ d).sub_mul
    rw [nat.mul_inc_r] at b_le_a
    have := (b.mul c₀).a_le_a_plus_b b
    rw [nat.add_comm] at this
    exact nat.le_trans this b_le_a
    apply nat.add_to_sub_le
    rw [←nat.mul_inc_r]
    assumption

theorem divisible.mul_sub_left {{ a b c: nat }} (d: divisible (nat.mul a b) c) : ∀ h, divisible (nat.mul (a.checked_sub c h) b) c := by
  intro c_le_a

  match a with
  | nat.zero =>
    rw [nat.checked_zero_sub]
    rw [nat.mul_zero]
    apply divisible.zero
  | nat.inc a₀ =>
  
  rw [nat.mul_sub_right]
  have ⟨ x, prf ⟩ := d
  
  exists (x.checked_sub b (by
    apply @nat.mul_le_cmp a₀.inc b c x
    rw [prf]
    apply nat.le_id
    apply nat.zero_lt_inc
    assumption))
  apply nat.add_to_sub_gen
  conv =>
    rhs
    rw [prf]
  rw [←nat.mul_add]
  match c with
  | .zero => rfl
  | .inc c₀ =>
    rw [nat.mul_irr]
    rw [nat.sub_add_inv]
    apply nat.zero_lt_inc
  have := @nat.mul_le c a₀.inc b c_le_a
  rw [nat.mul_comm _ a₀.inc, nat.mul_comm _ c] at this
  assumption

theorem divisible.mul_sub_right {{ a b c: nat }} (d: divisible (nat.mul a b) c) : ∀ h, divisible (nat.mul a (b.checked_sub c h)) c := by
  intro c_le_b 
  rw [nat.mul_comm]
  rw [nat.mul_comm] at d
  apply divisible.mul_sub_left
  assumption

theorem divisible.prime_ge {{ a b c: nat }} (cprime: c.prime) :
  divisible (nat.mul a b) c  -> nat.zero < nat.mul a b -> c <= a ∨ c <= b := by
  intro divis_ab_c ab_gt_zero
  have := divis_ab_c.is_le ab_gt_zero
  have ⟨ x, prf ⟩ := divis_ab_c

  admit

theorem divisible.prime2 {{ a b c: nat }} (aprime: a.prime) (cprime: c.prime) :
  divisible (nat.mul a b) c -> a ≠ c -> divisible b c := by
  intro divis_ab_c not_divis_a_c
  match b.is_divisible c with
  | .isTrue _ => assumption
  | .isFalse b_not_divis_c =>

  have ⟨ x, prf ⟩ := divis_ab_c
  apply False.elim
  apply not_divis_a_c


  
  admit


theorem divisible.prime {{ a b c: nat }} (cprime: c.prime) :
  divisible (nat.mul a b) c -> divisible a c ∨ divisible b c := by
  intro divis_ab_c
  match h₀:Compare.ord a c with
  | .Eq =>
    have a_eq_c := Compare.ord_implies_eq h₀
    rw [a_eq_c]
    apply Or.inl
    exact divisible.id _
  | .Greater =>
    have c_lt_a : c < a := by 
      rw [Compare.ord_flip] at h₀
      exact h₀
    have := divisible.mul_sub_left divis_ab_c (Or.inl c_lt_a) 
    match this.prime cprime with
    | .inl x =>
      have ⟨ x, prf ⟩ := x
      have := nat.sub_to_add _ prf
      apply Or.inl
      exists x.inc
      rw [nat.mul_inc_r, nat.add_comm, this]
    | .inr x =>
      exact Or.inr x
  | .Less =>
  match h₁:Compare.ord b c with
  | .Eq =>
    apply Or.inr
    have b_eq_c := Compare.ord_implies_eq h₁
    rw [b_eq_c]
    exact divisible.id _
  | .Greater =>
    have c_lt_b : c < b := by 
      rw [Compare.ord_flip] at h₁
      exact h₁
    clear h₁
    have := divisible.mul_sub_right divis_ab_c (Or.inl c_lt_b)
    match this.prime cprime with
    | .inl x =>
      exact Or.inl x
    | .inr x =>
      have ⟨ x, prf ⟩ := x
      have := nat.sub_to_add _ prf
      apply Or.inr
      exists x.inc
      rw [nat.mul_inc_r, nat.add_comm, this]
  | .Less =>
  have ⟨ x, prf ⟩ := divis_ab_c
  match a with
  | .zero =>
    apply Or.inl
    apply divisible.zero
  | .inc a₀ => 
  match b with
  | .zero =>
    apply Or.inr
    apply divisible.zero
  | .inc b₀ => 
  apply False.elim
  rw [nat.mul_inc_r] at prf
  simp at prf
  clear divis_ab_c
  -- a * b ≠ c * x (c prime, 0 < a < c, 0 < b < c)
  
  admit
  termination_by divisible.prime => a.add b
  decreasing_by {
    simp_wf
    admit
  }

-- theorem divisible.project_base (nd: ¬divisible a c) (cprime: c.prime): nat.mul a b = nat.mul c d -> divisible b c := by
--   intro mul
--   have dr := divrem.calc b c (nat.prime_gt_zero cprime)
--   have dr_def := Eq.symm dr.def
  
--   match h:dr.remainder with 
--   | .zero =>
--     exists dr.quocient
--     rw [h, nat.add_zero, nat.mul_comm] at dr_def
--     assumption
--   | .inc r =>
--     rw [h] at dr_def
--     apply False.elim
--     rw [dr_def] at mul
--     simp at mul
