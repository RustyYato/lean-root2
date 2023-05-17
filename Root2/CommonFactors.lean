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

theorem gcd.le (a b: nat) : gcd a b <= a ∧ gcd a b <= b ∨ a = nat.zero ∨ b = nat.zero := by
  apply Gcd.le

theorem Gcd.id (g: Gcd a a) : g.eval = a := by
  have := @nat.not_lt_id a
  match g with
  | .Id a => simp

theorem gcd.id : gcd a a = a := by apply Gcd.id

theorem Gcd.right (g: Gcd nat.zero a) : g.eval = a := by
  have := nat.not_lt_zero a
  match g with
  | .Id _ | .Right _ _ => simp

theorem gcd.right : gcd nat.zero a = a := by apply Gcd.right

theorem Gcd.left (g: Gcd a nat.zero) : g.eval = a := by
  cases g
  simp
  simp
  contradiction
  contradiction
  contradiction

theorem gcd.left : gcd a nat.zero = a := by apply Gcd.left

theorem Gcd.correct (g: Gcd a b) c :
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

theorem gcd.correct :
  divisible a c ->
  divisible b c ->
  divisible (gcd a b) c := by
  apply Gcd.correct

theorem Gcd.correct_rev (g: Gcd a b) :
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

theorem gcd.correct_rev :
  divisible (gcd a b) c ->
  divisible a c ∧ 
  divisible b c := by
  apply Gcd.correct_rev

theorem Gcd.comm (f: Gcd a b) (r: Gcd b a) : f.eval = r.eval := by
  have ⟨ divis_a_f, divis_b_f ⟩ := f.correct_rev (divisible.id _)
  have ⟨ divis_b_r, divis_a_r ⟩ := r.correct_rev (divisible.id _)

  have divis_r_f := Gcd.correct r f.eval divis_b_f divis_a_f
  have divis_f_r := Gcd.correct f r.eval divis_a_r divis_b_r
  
  exact divisible.ab_eq_ba_implies_eq divis_f_r divis_r_f

theorem gcd.comm (a b: nat) : gcd a b = gcd b a := by
  apply Gcd.comm

theorem Gcd.id_eval (g h: Gcd a b) : g.eval = h.eval := by
  rw [Gcd.comm g (Gcd.calc b a)]
  rw [Gcd.comm h (Gcd.calc b a)]

theorem gcd.id_eval (g h: Gcd a b) : g.eval = h.eval := by
  rw [Gcd.comm g (Gcd.calc b a)]
  rw [Gcd.comm h (Gcd.calc b a)]

theorem Gcd.assoc (g: Gcd a b) (h: Gcd b c) (i: Gcd g.eval c) (j: Gcd a h.eval) : i.eval = j.eval := by
  have ⟨ divis_g_i, divis_c_i ⟩ := i.correct_rev (divisible.id _)
  have ⟨ divis_a_g, divis_b_g ⟩ := g.correct_rev (divisible.id _)
  have divis_a_i := divis_a_g.trans divis_g_i
  have divis_b_i := divis_b_g.trans divis_g_i
  clear divis_a_g divis_b_g divis_g_i
  
  have ⟨ divis_a_j, divis_h_j ⟩ := j.correct_rev (divisible.id _)
  have ⟨ divis_b_h, divis_c_h ⟩ := h.correct_rev (divisible.id _)
  have divis_b_j := divis_b_h.trans divis_h_j
  have divis_c_j := divis_c_h.trans divis_h_j
  clear divis_c_h divis_b_h divis_h_j

  have divis_h_i := Gcd.correct h i.eval divis_b_i divis_c_i
  have divis_j_i := Gcd.correct j i.eval divis_a_i divis_h_i
  clear divis_h_i divis_a_i divis_b_i divis_c_i

  have divis_g_j := Gcd.correct g j.eval divis_a_j divis_b_j
  have divis_i_j := Gcd.correct i j.eval divis_g_j divis_c_j
  clear divis_g_j divis_a_j divis_b_j divis_c_j

  exact divisible.ab_eq_ba_implies_eq divis_i_j divis_j_i

theorem gcd.assoc : gcd a (gcd b c) = gcd (gcd a b) c := by
  apply Eq.symm
  apply Gcd.assoc

theorem Gcd.ne_zero (g: Gcd a b) : (nat.zero < g.eval) = (nat.zero < a ∨ nat.zero < b) := by
  simp
  match g with
  | .Id _ | .Left _ _ | .Right _ _ => simp
  | .LeftSucc _ _ a_gt_zero b_gt_zero b_gt_a g =>
    simp
    rw [g.ne_zero]
    apply Eq.propIntro
    repeat intro ; apply Or.inl; assumption
  | .RightSucc _ _ _ _ _ g =>
    simp
    rw [g.ne_zero]
    apply Eq.propIntro
    repeat intro ; apply Or.inl; assumption
    intro ; apply Or.inr; assumption

theorem gcd.ne_zero : (nat.zero < gcd a b) = (nat.zero < a ∨ nat.zero < b) := by
  apply Gcd.ne_zero

theorem Gcd.eq_zero (g: Gcd a b) : (g.eval = nat.zero) = (a = nat.zero ∧ b = nat.zero) := by
  match g with
  | .Id _ | .Left _ _ | .Right _ _ => simp
  | .LeftSucc _ _ a_gt_zero _ _ g =>
    simp
    apply Eq.propIntro
    intro g_eq_zero
    have := g.ne_zero.mpr (.inl a_gt_zero)
    rw [g_eq_zero] at this
    contradiction
    intro a_and_b_eq_zero
    have ⟨ a_eq_zero, b_eq_zero ⟩ := a_and_b_eq_zero
    rw [a_eq_zero] at a_gt_zero
    contradiction
  | .RightSucc _ _ _ b_gt_zero _ g =>
    simp
    apply Eq.propIntro
    intro g_eq_zero
    have := g.ne_zero.mpr (.inr b_gt_zero)
    rw [g_eq_zero] at this
    contradiction
    intro a_and_b_eq_zero
    have ⟨ a_eq_zero, b_eq_zero ⟩ := a_and_b_eq_zero
    rw [b_eq_zero] at b_gt_zero
    contradiction

theorem gcd.eq_zero : (gcd a b = nat.zero) = (a = nat.zero ∧ b = nat.zero) := by
  apply Gcd.eq_zero

theorem Gcd.divisible_by_left (g: Gcd a b) (d: divisible a b): g.eval = b := by
  match g with
  | .Id _ => simp
  | .Left _ _ =>
    simp
    rw [d.by_zero]
  | .Right _ _ => simp
  | .LeftSucc _ _ a_gt_zero _ _ _ =>
    simp
    have := (nat.comp_dec · (d.is_le a_gt_zero))
    contradiction
  | .RightSucc _ _ _ _ _ g =>
    simp
    apply Gcd.divisible_by_left g
    have ⟨ x, prf ⟩ := d
    match x with
    | .zero =>
      rw [nat.mul_zero_r] at prf
      rw [prf, nat.sat_sub_zero (nat.zero_le _)]
      exact divisible.zero _
    | .inc x₀ =>
    exists x₀
    rw [prf, nat.mul_inc_r, nat.sat_sub_add_inv2]

theorem Gcd.divisible_by_right (g: Gcd a b) (d: divisible b a): g.eval = a := by
  have : Gcd b a := Gcd.calc b a
  rw [Gcd.comm g this]
  apply Gcd.divisible_by_left
  assumption

theorem Gcd.repeat_right (g: Gcd a b) (h: Gcd a g.eval): h.eval = g.eval := by
  apply Gcd.divisible_by_left h
  have ⟨ _, _ ⟩ := Gcd.correct_rev g (divisible.id _)
  assumption

theorem Gcd.repeat_left (g: Gcd a b) (h: Gcd g.eval b): h.eval = g.eval := by
  apply Gcd.divisible_by_right h
  have ⟨ _, _ ⟩ := Gcd.correct_rev g (divisible.id _)
  assumption

theorem Gcd.eval_eq (g: Gcd a b) (h: Gcd c d) (a_eq_c: a = c) (b_eq_d: b = d) : g.eval = h.eval := by
  apply divisible.ab_eq_ba_implies_eq

  have ⟨ c_divis_h, d_divis_h ⟩  := h.correct_rev (divisible.id _)
  rw [divisible.eq a_eq_c.symm rfl] at c_divis_h
  rw [divisible.eq b_eq_d.symm rfl] at d_divis_h
  exact g.correct h.eval c_divis_h d_divis_h

  have ⟨ a_divis_g, b_divis_g ⟩  := g.correct_rev (divisible.id _)
  rw [divisible.eq a_eq_c rfl] at a_divis_g
  rw [divisible.eq b_eq_d rfl] at b_divis_g
  exact h.correct g.eval a_divis_g b_divis_g

theorem Gcd.eval_eq_right (g: Gcd a b) (h: Gcd a c) (eq: b = c) : g.eval = h.eval := by
  apply Gcd.eval_eq
  rfl
  assumption

theorem Gcd.eval_eq_left (g: Gcd a b) (h: Gcd c b) (eq: a = c) : g.eval = h.eval := by
  apply Gcd.eval_eq
  assumption
  rfl
