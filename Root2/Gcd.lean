import Root2.Divisible.DivRem
import Root2.Nat.Sub.Mul

inductive Gcd : nat -> nat -> Type where
| Id : ∀ a b, a = b -> Gcd a b
| Left : ∀ a b, nat.zero < a -> b = nat.zero -> Gcd a b
| Right : ∀ a b, a = nat.zero -> nat.zero < b -> Gcd a b
| LeftSucc : ∀ a b, nat.zero < a -> nat.zero < b -> b > a -> Gcd a (b.saturating_sub a) -> Gcd a b
| RightSucc : ∀ a b, nat.zero < a -> nat.zero < b -> b < a -> Gcd (a.saturating_sub b) b -> Gcd a b

@[simp]
def Gcd.eval (g: Gcd a b) : nat := 
  match g with
  | .Id x _ _ | .Left x _ _ _ | .Right _ x _ _ => x
  | .LeftSucc _ _ _ _ _ g => g.eval
  | .RightSucc _ _ _ _ _ g => g.eval

def Gcd.calc (a b: nat): Gcd a b := 
  match h:ord_imp a b with
  | .Eq => by
    exact .Id a b (ord_imp_eq h)
  | .Less => match _h₀:a with
    | .zero => .Right .zero b rfl (Compare.ord_implies_lt h)
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
    | .zero => .Left a .zero (Compare.ord_implies_lt (ord_imp_flip.mp h)) rfl
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

@[simp]
def coprime (a b: nat) : Prop := gcd a b = nat.zero.inc

theorem Gcd.le (g: Gcd a b) : g.eval <= a ∧ g.eval <= b ∨ a = nat.zero ∨ b = nat.zero := by
  match g with
  | .Id a _ a_eq_b =>
    simp
    rw [a_eq_b]
    apply Or.inl
    exact ⟨ nat.le_id _, nat.le_id _ ⟩
  | .Left a b _ b_eq_zero =>
    simp
    rw [b_eq_zero]
    simp
  | .Right a b a_eq_zero _ =>
    simp
    rw [a_eq_zero]
    simp
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
  | .Id a _ _ => simp

theorem gcd.id : gcd a a = a := by apply Gcd.id

theorem Gcd.right (g: Gcd nat.zero a) : g.eval = a := by
  have := nat.not_lt_zero a
  match g with
  | .Id _ _ a_eq_b =>
    simp
    rw [a_eq_b]
  | .Right _ _ _ _ =>
    simp

theorem gcd.right : gcd nat.zero a = a := by apply Gcd.right

theorem Gcd.left (g: Gcd a nat.zero) : g.eval = a := by
  cases g
  simp
  simp
  contradiction
  contradiction
  contradiction

theorem gcd.left : gcd a nat.zero = a := by apply Gcd.left

theorem Gcd.dvd_implies (g: Gcd a b) c :
  dvd a c ->
  dvd b c ->
  dvd g.eval c := by
  intro dvd_a_c dvd_b_c
  match g with
  | .Id _ _ _ | .Left _ _ _ _ | .Right _ _ _ _ =>
    simp
    assumption
  | .RightSucc _ _ _ _ _ _ =>
    simp
    apply Gcd.dvd_implies
    {
      have ⟨ x, prf₀ ⟩ := dvd_a_c
      have ⟨ y, prf₁ ⟩ := dvd_b_c
      exists x.saturating_sub y
      rw [nat.mul_sat_sub_left]
      rw [prf₀, prf₁]
    }
    assumption
  | .LeftSucc _ _ _ _ _ _ =>
    simp
    apply Gcd.dvd_implies
    assumption
    {
      have ⟨ x, prf₀ ⟩ := dvd_a_c
      have ⟨ y, prf₁ ⟩ := dvd_b_c
      exists y.saturating_sub x
      rw [nat.mul_sat_sub_left]
      rw [←prf₀, ←prf₁]
    }

theorem gcd.dvd_implies :
  dvd a c ->
  dvd b c ->
  dvd (gcd a b) c := by
  apply Gcd.dvd_implies

theorem Gcd.implies_dvd (g: Gcd a b) :
  dvd g.eval c ->
  dvd a c ∧
  dvd b c := by
  intro dvd_g_c
  match g with
  | .Id _ _ a_eq_b =>
    simp at dvd_g_c
    rw [←a_eq_b]
    apply And.intro <;> assumption
  | .Left _ _ _ b_eq_zero =>
    simp at dvd_g_c
    apply And.intro
    assumption
    rw [b_eq_zero]
    apply dvd.zero
  | .Right _ _ a_eq_zero _ =>
    simp at dvd_g_c
    apply And.intro
    rw [a_eq_zero]
    apply dvd.zero
    assumption
  | .RightSucc _ _ _ _ _ g =>
    simp at dvd_g_c
    have ⟨ dvd_sub_c, dvd_b_c ⟩  := Gcd.implies_dvd g dvd_g_c
    apply And.intro
    {
      have ⟨ x, prf₀ ⟩ := dvd_sub_c
      have ⟨ y, prf₁ ⟩ := dvd_b_c
      exists x.add y
      rw [nat.mul_add, ←prf₀, ←prf₁]
      rw [nat.sat_sub_add_inv]
      apply Or.inl
      assumption
    }
    assumption
  | .LeftSucc _ _ _ _ _ g =>
    simp at dvd_g_c
    have ⟨ dvd_sub_c, dvd_b_c ⟩  := Gcd.implies_dvd g dvd_g_c
    apply And.intro
    assumption
    {
      have ⟨ x, prf₀ ⟩ := dvd_sub_c
      have ⟨ y, prf₁ ⟩ := dvd_b_c
      exists x.add y
      rw [nat.mul_add, ←prf₀, ←prf₁]
      rw [nat.add_comm, nat.sat_sub_add_inv]
      apply Or.inl
      assumption
    }

theorem gcd.implies_dvd :
  dvd (gcd a b) c ->
  dvd a c ∧ 
  dvd b c := by
  apply Gcd.implies_dvd

theorem Gcd.comm (f: Gcd a b) (r: Gcd b a) : f.eval = r.eval := by
  have ⟨ dvd_a_f, dvd_b_f ⟩ := f.implies_dvd (dvd.id _)
  have ⟨ dvd_b_r, dvd_a_r ⟩ := r.implies_dvd (dvd.id _)

  have dvd_r_f := Gcd.dvd_implies r f.eval dvd_b_f dvd_a_f
  have dvd_f_r := Gcd.dvd_implies f r.eval dvd_a_r dvd_b_r
  
  exact dvd.to_eq dvd_f_r dvd_r_f

theorem gcd.comm (a b: nat) : gcd a b = gcd b a := by
  apply Gcd.comm

theorem Gcd.id_eval (g h: Gcd a b) : g.eval = h.eval := by
  rw [Gcd.comm g (Gcd.calc b a)]
  rw [Gcd.comm h (Gcd.calc b a)]

theorem gcd.id_eval (g h: Gcd a b) : g.eval = h.eval := by
  rw [Gcd.comm g (Gcd.calc b a)]
  rw [Gcd.comm h (Gcd.calc b a)]

theorem Gcd.assoc (g: Gcd a b) (h: Gcd b c) (i: Gcd g.eval c) (j: Gcd a h.eval) : i.eval = j.eval := by
  have ⟨ dvd_g_i, dvd_c_i ⟩ := i.implies_dvd (dvd.id _)
  have ⟨ dvd_a_g, dvd_b_g ⟩ := g.implies_dvd (dvd.id _)
  have dvd_a_i := dvd_a_g.trans dvd_g_i
  have dvd_b_i := dvd_b_g.trans dvd_g_i
  clear dvd_a_g dvd_b_g dvd_g_i
  
  have ⟨ dvd_a_j, dvd_h_j ⟩ := j.implies_dvd (dvd.id _)
  have ⟨ dvd_b_h, dvd_c_h ⟩ := h.implies_dvd (dvd.id _)
  have dvd_b_j := dvd_b_h.trans dvd_h_j
  have dvd_c_j := dvd_c_h.trans dvd_h_j
  clear dvd_c_h dvd_b_h dvd_h_j

  have dvd_h_i := Gcd.dvd_implies h i.eval dvd_b_i dvd_c_i
  have dvd_j_i := Gcd.dvd_implies j i.eval dvd_a_i dvd_h_i
  clear dvd_h_i dvd_a_i dvd_b_i dvd_c_i

  have dvd_g_j := Gcd.dvd_implies g j.eval dvd_a_j dvd_b_j
  have dvd_i_j := Gcd.dvd_implies i j.eval dvd_g_j dvd_c_j
  clear dvd_g_j dvd_a_j dvd_b_j dvd_c_j

  exact dvd.to_eq dvd_i_j dvd_j_i

theorem gcd.assoc : gcd a (gcd b c) = gcd (gcd a b) c := by
  apply Eq.symm
  apply Gcd.assoc

theorem Gcd.left_one (g: Gcd a nat.zero.inc) : g.eval = nat.zero.inc := by
  match h:g with
  | .Id _ _ _ =>
    simp
    assumption
  | .Right _ _ _ _ => simp
  | .Left a b _ b_eq_zero =>
    next b_eq_one _ => {
      rw [b_eq_zero] at b_eq_one
      contradiction
    }
  | .LeftSucc a b _ _ _ _ =>
    simp
    next b_eq_one _ => {
      match a with
      | .inc a₀ => 
      next b_gt_a₀ _ _ => {
        rw [←b_eq_one] at b_gt_a₀
        unfold GT.gt at b_gt_a₀
        rw [nat.lt_inc_irr] at b_gt_a₀
        have := nat.not_lt_zero a₀
        contradiction
      }
    }
  | .RightSucc a b _ _ _ g => {
    simp
    clear h
    match b with
    | .inc .zero =>
    exact g.left_one
  }

theorem Gcd.right_one (g: Gcd nat.zero.inc a) : g.eval = nat.zero.inc := by
  have gcd_a_one := Gcd.calc a nat.zero.inc
  have := gcd_a_one.left_one
  rw [Gcd.comm _ gcd_a_one]
  assumption

theorem gcd.left_one : gcd a nat.zero.inc = nat.zero.inc := by
  apply Gcd.left_one

theorem gcd.right_one : gcd nat.zero.inc a = nat.zero.inc := by
  apply Gcd.right_one

theorem Gcd.ne_zero (g: Gcd a b) : (nat.zero < g.eval) = (nat.zero < a ∨ nat.zero < b) := by
  simp
  match g with
  | .Id _ _ a_eq_b =>
    simp
    rw [a_eq_b]
    simp
  | .Left _ _ _ b_eq_zero =>
    simp
    rw [b_eq_zero]
    simp
  | .Right _ _ a_eq_zero _ =>
    simp
    rw [a_eq_zero]
    simp
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
  | .Id _ _ a_eq_b =>
    simp
    rw [a_eq_b]
    simp
  | .Left _ _ _ b_eq_zero =>
    simp
    rw [b_eq_zero]
    simp
  | .Right _ _ a_eq_zero _ =>
    simp
    rw [a_eq_zero]
    simp
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

theorem Gcd.dvd_by_left (g: Gcd a b) (d: dvd a b): g.eval = b := by
  apply dvd.to_eq
  exact Gcd.dvd_implies g b d (dvd.id _)
  exact (Gcd.implies_dvd g (dvd.id _)).right

theorem gcd.dvd_by_left (d: dvd a b) : gcd a b = b :=
  by apply Gcd.dvd_by_left _ d

theorem Gcd.dvd_by_right (g: Gcd a b) (d: dvd b a): g.eval = a := by
  apply dvd.to_eq
  exact Gcd.dvd_implies g a (dvd.id _) d
  exact (Gcd.implies_dvd g (dvd.id _)).left

theorem gcd.dvd_by_right (d: dvd b a) : gcd a b = a :=
  by apply Gcd.dvd_by_right _ d

theorem Gcd.repeat_right (g: Gcd a b) (h: Gcd a g.eval): h.eval = g.eval := by
  apply Gcd.dvd_by_left h
  have ⟨ _, _ ⟩ := Gcd.implies_dvd g (dvd.id _)
  assumption

theorem gcd.repeat_right : gcd a (gcd a b) = gcd a b :=
  by apply Gcd.repeat_right

theorem Gcd.repeat_left (g: Gcd a b) (h: Gcd g.eval b): h.eval = g.eval := by
  apply Gcd.dvd_by_right h
  have ⟨ _, _ ⟩ := Gcd.implies_dvd g (dvd.id _)
  assumption

theorem gcd.repeat_left : gcd (gcd a b) b = gcd a b :=
  by apply Gcd.repeat_left

theorem Gcd.eval_eq (g: Gcd a b) (h: Gcd c d) (a_eq_c: a = c) (b_eq_d: b = d) : g.eval = h.eval := by
  apply dvd.to_eq

  have ⟨ c_dvd_h, d_dvd_h ⟩  := h.implies_dvd (dvd.id _)
  rw [dvd.eq a_eq_c.symm rfl] at c_dvd_h
  rw [dvd.eq b_eq_d.symm rfl] at d_dvd_h
  exact g.dvd_implies h.eval c_dvd_h d_dvd_h

  have ⟨ a_dvd_g, b_dvd_g ⟩  := g.implies_dvd (dvd.id _)
  rw [dvd.eq a_eq_c rfl] at a_dvd_g
  rw [dvd.eq b_eq_d rfl] at b_dvd_g
  exact h.dvd_implies g.eval a_dvd_g b_dvd_g

theorem Gcd.eval_eq_right (g: Gcd a b) (h: Gcd a c) (eq: b = c) : g.eval = h.eval := by
  apply Gcd.eval_eq
  rfl
  assumption

theorem Gcd.eval_eq_left (g: Gcd a b) (h: Gcd c b) (eq: a = c) : g.eval = h.eval := by
  apply Gcd.eval_eq
  assumption
  rfl

theorem Gcd.from_gcd (P: ∀g: nat, Prop) : P (gcd a b) -> ∀g: Gcd a b, P g.eval := by
  intro p_gcd g
  rw [Gcd.eval_eq g (Gcd.calc a b) rfl rfl]
  assumption

theorem Gcd.eq_implies_dvd (g: Gcd a b) (g_eq_b: g.eval = b) : dvd a b := by
  have ⟨ dvd_a_g, _ ⟩ := g.implies_dvd (dvd.id _)
  rw [g_eq_b] at dvd_a_g
  assumption

theorem gcd.eq_implies_dvd_right : gcd a b = b -> dvd a b := by
  apply Gcd.eq_implies_dvd

theorem gcd.eq_implies_dvd_left : gcd a b = a -> dvd b a := by
  rw [gcd.comm]
  apply Gcd.eq_implies_dvd

theorem gcd.gcd_eq_implies_dvd_left : (gcd a b = a) = dvd b a := by
  apply Eq.propIntro
  rw [gcd.comm]
  apply Gcd.eq_implies_dvd
  intro dvd_b_a
  apply dvd.to_eq
  apply gcd.dvd_implies
  exact dvd.id _
  assumption
  rw [gcd.comm, gcd.dvd_by_left dvd_b_a]
  exact dvd.id _

theorem gcd.gcd_eq_implies_dvd_right : (gcd a b = b) = dvd a b := by
  rw [gcd.comm]
  apply gcd.gcd_eq_implies_dvd_left

theorem Gcd.gt_one_implies_gcd_mul_gt_one
  (gcd_a_c: Gcd a c)
  (gcd_b_c: Gcd b c)
  (gcd_p_c: Gcd p c)
  :
  p = a.mul b ->
  nat.zero < a ->
  nat.zero < b ->
  nat.zero.inc < gcd_a_c.eval ∨ 
  nat.zero.inc < gcd_b_c.eval ->
  nat.zero.inc < gcd_p_c.eval := by
  intro p_eq_a_mul_b a_gt_zero b_gt_zero gcd_a_c_gt_one_or_gcd_b_c_gt_one
  match gcd_a_c_gt_one_or_gcd_b_c_gt_one with
  | .inl gcd_a_c_gt_one =>
    have ⟨ dvd_a, dvd_c ⟩ := gcd_a_c.implies_dvd (dvd.id _)
    have := Gcd.dvd_implies gcd_p_c gcd_a_c.eval (by
      have ⟨ x, prf ⟩ := dvd_a
      exists x.mul b
      rw [p_eq_a_mul_b]
      conv => {
        lhs
        rw [prf]
      }
      rw [nat.mul_perm0]) dvd_c
    match dvd.gt gcd_a_c_gt_one this with
    | .inl _ => assumption
    | .inr gcd_p_c_eq_zero =>
      rw [Gcd.eq_zero] at gcd_p_c_eq_zero
      have ⟨ p_eq_zero, c_eq_zero ⟩ := gcd_p_c_eq_zero
      match p, c with
      | .zero, .zero =>
      rw [Gcd.left] at gcd_a_c_gt_one
      -- rw [Gcd.left] at gcd_b_c_gt_one
      match nat.mul_eq_zero _ _ p_eq_a_mul_b.symm with
      | .inl a_eq_zero =>
        match a with
        | .zero => contradiction
      | .inr b_eq_zero =>
        match b with
        | .zero => contradiction
  | .inr gcd_b_c_gt_one => 
    have ⟨ dvd_b, dvd_c ⟩ := gcd_b_c.implies_dvd (dvd.id _)
    have := Gcd.dvd_implies gcd_p_c gcd_b_c.eval (by
      have ⟨ x, prf ⟩ := dvd_b
      exists a.mul x
      rw [p_eq_a_mul_b]
      conv => {
        lhs
        rw [prf]
      }
      rw [nat.mul_perm7]) dvd_c
    match dvd.gt gcd_b_c_gt_one this with
    | .inl _ => assumption
    | .inr gcd_p_c_eq_zero =>
      rw [Gcd.eq_zero] at gcd_p_c_eq_zero
      have ⟨ p_eq_zero, c_eq_zero ⟩ := gcd_p_c_eq_zero
      match p, c with
      | .zero, .zero =>
      rw [Gcd.left] at gcd_b_c_gt_one
      match nat.mul_eq_zero _ _ p_eq_a_mul_b.symm with
      | .inl a_eq_zero =>
        match a with
        | .zero => contradiction
      | .inr b_eq_zero =>
        match b with
        | .zero => contradiction

-- theorem coprime.zero_left : coprime nat.zero a -> a = nat.zero.inc := by
--   unfold coprime
--   intro gcd_zero_a
--   rw [gcd.right] at gcd_zero_a
--   assumption

-- theorem coprime.zero_right : coprime a nat.zero -> a = nat.zero.inc := by
--   unfold coprime
--   intro gcd_zero_a
--   rw [gcd.left] at gcd_zero_a
--   assumption

-- theorem coprime.dvd_mul_left {m n k : nat} :
--   coprime k n -> (dvd (nat.mul m n) k ↔ dvd n k )
--    := by admit

-- theorem Gcd.mul
--   { a b c: nat }
--   (g: Gcd b c)
--  : gcd (nat.mul a b) (nat.mul a c) = nat.mul a g.eval := by
--   match g with
--   | .Id _ _ b_eq_c =>
--     simp
--     rw [b_eq_c, gcd.id]
--   | .Left _ _ _ c_eq_zero =>
--     simp
--     rw [c_eq_zero]
--     rw [nat.mul_zero_r, gcd.left]
--   | .Right _ _ b_eq_zero _ =>
--     simp
--     rw [b_eq_zero, nat.mul_zero_r, gcd.right]
--   | .LeftSucc _ _ _ _ _ g =>
--     simp
    
    
--     admit
--   | .RightSucc _ _ _ _ _ _ => admit

-- -- theorem gcd.mul : gcd (nat.mul a b) (nat.mul a c) = nat.mul a (gcd b c) := by
  

-- -- theorem coprime.dvd_of_dvd_mul_left {m n k : nat} (H1 : coprime k n) (H2 : dvd (nat.mul m n) k) : dvd m k := by
-- --   have := @coprime.dvd_mul_left m n k H1
-- --   have := (gcd.dvd_implies (@dvd.mul k k m (dvd.id k)) H2)
-- --   rw [nat.mul_comm k m] at this
  
-- --   rw []
-- --   -- by rw mul_comm at H2; exact H1.dvd_of_dvd_mul_right H2

-- -- theorem gcd.left_cancel : 
-- --   coprime k n -> gcd (nat.mul k m) n = gcd m n := by
-- --   intro cp_k_n
-- --   apply dvd.to_eq
-- --   exists k


-- --   admit

-- -- theorem gcd.one_one_to_one : coprime a c -> coprime b c -> coprime (a.mul b) c := by
-- --   intro a_c_coprime b_c_coprime
-- --   have ⟨ ab_abc, c_abc ⟩ := @gcd.implies_dvd (nat.mul a b) c _ (dvd.id _)

-- --   have := Nat.coprime_mul_iff

-- --   match h:(gcd (a.mul b) c) with
-- --   | .zero =>
-- --     rw [gcd.eq_zero] at h
-- --     have ⟨ ab_eq_zero, c_eq_zero ⟩ := h
-- --     match c with
-- --     | .zero =>
-- --     match  nat.mul_eq_zero _ _ ab_eq_zero with
-- --     | .inl _ =>
-- --       match a with
-- --       | .zero =>
-- --       unfold coprime at a_c_coprime
-- --       rw [gcd.id] at a_c_coprime
-- --       contradiction
-- --     | .inr _ =>
-- --       match b with
-- --       | .zero =>
-- --       unfold coprime at b_c_coprime
-- --       rw [gcd.id] at b_c_coprime
-- --       contradiction
-- --   | .inc .zero =>rfl
-- --   | .inc (.inc r) =>

-- --     rw [h] at c_abc ab_abc
-- --     have ⟨ x, prf ⟩ := c_abc
-- --     clear h

-- --     rw [prf, gcd.comm] at a_c_eq_one
-- --     have ⟨ _, _ ⟩ := gcd.one_to_one_one a_c_eq_one
-- --     admit

-- -- -- -- theorem Gcd.mul_gt_one_implies_gcd_gt_one
-- -- -- --   (gcd_a_c: Gcd a c)
-- -- -- --   (gcd_b_c: Gcd b c)
-- -- -- --   (gcd_p_c: Gcd p c)
-- -- -- --   :
-- -- -- --   p = a.mul b ->
-- -- -- --   nat.zero < a ->
-- -- -- --   nat.zero < b ->
-- -- -- --   nat.zero.inc < gcd_p_c.eval -> (
-- -- -- --     nat.zero.inc < gcd_a_c.eval ∨ 
-- -- -- --     nat.zero.inc < gcd_b_c.eval) := by
-- -- -- --   intro p_eq_a_mul_b a_gt_zero b_gt_zero gcd_p_c_gt_one

