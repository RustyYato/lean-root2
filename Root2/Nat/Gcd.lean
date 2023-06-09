import Root2.Nat.Cmp
import Root2.Nat.Sub
import Root2.Divisible.DivRem

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

theorem remainder.induction_nz {P : nat -> (b: nat) -> nat.zero < b -> Prop} :
  (∀ (a b: nat), ∀ h, a < b -> P a b h) ->
  (∀ (a b: nat), ∀ h, ¬(a < b) -> P (a.saturating_sub b) b h -> P a b h) ->
  (∀a b h, P a (nat.inc b) h)
 := fun base induct a b h => remainder.induction base induct a (nat.inc b) h

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

-- theorem remainder.template : ∀ a b h, remainder a b h = nat.zero -> dvd a b := by
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

theorem remainder.zero : remainder nat.zero a h = nat.zero := by
  unfold remainder
  rw [dec.pick_true (Compare.dec_lt nat.zero a) h]

theorem remainder.of_dvd : ∀ {a b h}, dvd a b -> remainder a b h = nat.zero := by
  apply remainder.induction
  
  {
    intro a b b_gt_zero a_lt_b
    unfold remainder; rw [(dec.pick_true (Compare.dec_lt a b) a_lt_b)]; simp
    intro d
    have ⟨ x , prf ⟩ := d
    rw [prf] at a_lt_b
    conv at a_lt_b => {
      rhs
      rw [←nat.mul_one_r b]
    }
    rw [nat.lt_mul_irr] at a_lt_b
    match x with
      | .inc x₀ => 
        rw [nat.lt_inc_irr] at a_lt_b
        have := nat.not_lt_zero x₀
        contradiction
      | .zero =>
      rw [nat.mul_zero_r] at prf
      assumption
    assumption  
  }
  
  {
    intro a b b_gt_zero b_le_a prev
    unfold remainder; rw [(dec.pick_false (Compare.dec_lt a b) b_le_a)]; simp
    intro d
    exact prev (dvd.sat_sub d)
  }

theorem remainder.to_dvd : ∀ {a b h}, remainder a b h = nat.zero -> dvd a b := by
  apply remainder.induction
  
  {
    intro a b b_gt_zero a_lt_b
    unfold remainder; rw [(dec.pick_true (Compare.dec_lt a b) a_lt_b)]; simp
    intro a_eq_zero
    rw [a_eq_zero]
    apply dvd.zero
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

theorem remainder.eq_lt : ∀ a b h, a < b -> remainder a b h = a := by
  intro a b h a_lt_b
  unfold remainder
  rw [dec.pick_true (Compare.dec_lt _ _) a_lt_b]

theorem nat.sat_sub_add_assoc :
  b <= a ->
  nat.saturating_sub (nat.add a c) b = nat.add (nat.saturating_sub a b) c := by
  intro b_le_a
  match a with
  | .zero =>
    match b with
    | .zero => simp
  | .inc a₀ =>
    match b with
    | .zero => simp
    | .inc b₀ =>
      simp
      apply nat.sat_sub_add_assoc
      assumption

theorem remainder.add_left : ∀ a b h c, remainder (nat.add a c) b h = remainder (nat.add (remainder a b h) c) b h := by
  apply remainder.induction
  {
    intro a b h a_lt_b c
    conv => {
      rhs
      congr
      lhs
      unfold remainder
    }
    rw [dec.pick_true (Compare.dec_lt a b) a_lt_b]
  }
  {
    intro a b h b_le_a prev c
    conv => {
      rhs
      congr
      unfold remainder
    }
    rw [dec.pick_false (Compare.dec_lt a b) b_le_a]; simp
    have := prev c
    rw [←this]
    conv => {
      lhs
      unfold remainder
    }
    cases Compare.dec_lt _ b <;> simp
    next h => {
      rw [nat.sat_sub_add_assoc]
      exact nat.not_lt_is_sym_le.mp b_le_a
    }
    next h => {
      rw [nat.not_lt_is_sym_le] at b_le_a
      clear prev this
      apply False.elim
      have := nat.le_trans b_le_a (nat.a_le_a_plus_b a c)
      have := nat.comp_dec h
      contradiction
    }
  }

theorem remainder.def : ∀a b h, ∃x, a = nat.add (remainder a b h) (nat.mul b x) := by
  apply remainder.induction
  {
    intro a b h a_lt_b
    exists nat.zero
    unfold remainder
    rw [dec.pick_true (Compare.dec_lt _ _) a_lt_b]
    rw [nat.mul_zero_r, nat.add_zero_r]
  }
  {
    intro a b h not_a_lt_b prev
    have ⟨ x, prf ⟩ := prev
    exists x.inc
    unfold remainder
    rw [dec.pick_false (Compare.dec_lt _ _) not_a_lt_b]
    rw [nat.mul_inc_r, nat.add_perm7, ←prf]
    rw [nat.add_comm, nat.sat_sub_add_inv]
    exact nat.not_lt_is_sym_le.mp not_a_lt_b
  }

theorem remainder.add : ∀ a b h c, remainder (nat.add a c) b h = remainder (nat.add (remainder a b h) (remainder c b h)) b h := by
  apply remainder.induction
  {
    intro a b h a_lt_b c
    conv => {
      rhs
      congr
      lhs
      unfold remainder
    }
    rw [dec.pick_true (Compare.dec_lt a b) a_lt_b]
    simp
    rw [nat.add_comm _ (remainder _ _ _)]
    have := remainder.add_left c b h a
    rw [←this]
    rw [nat.add_comm]
  }
  {
    intro a b h not_a_lt_b prev c
    have b_le_a := not_a_lt_b
    rw [nat.not_lt_is_sym_le] at b_le_a
    have b_le_ac := nat.le_trans b_le_a (nat.a_le_a_plus_b a c)
    conv => {
      rhs
      congr
      lhs
      unfold remainder
      rw [dec.pick_false (Compare.dec_lt _ _) not_a_lt_b]
      simp
    }
    conv => {
      lhs
      unfold remainder
      rw [dec.pick_false (Compare.dec_lt _ _) (by
        intro ac_lt_b
        have := nat.comp_dec ac_lt_b
        contradiction)]
      simp
    } 
    rw [nat.sat_sub_add_assoc b_le_a]
    rw [prev]
  }

theorem remainder.inc : ∀ a b h, remainder a.inc b h = (remainder a b h).inc ∨ remainder a.inc b h = nat.zero
 := by
  apply remainder.induction
  {
    intro a b h a_lt_b
    unfold remainder
    rw [dec.pick_true (Compare.dec_lt _ _) a_lt_b]
    cases Compare.dec_lt a.inc b <;> simp
    next g => {
      rw [nat.not_lt_is_sym_le] at g
      match g with
      | .inl g =>
        have : b < a.inc := Compare.ord_implies_lt g
        have := nat.no_between_inc a_lt_b
        contradiction
      | .inr g =>
        have b_eq_ainc : b = a.inc := Compare.ord_implies_eq g
        apply Or.inr
        conv => {
          lhs
          congr
          rw [b_eq_ainc]
        }
        rw [nat.sat_sub_id, remainder.zero]
    }
  }
  {
    intro a b h not_a_lt_b prev
    unfold remainder
    rw [dec.pick_false (Compare.dec_lt _ _) not_a_lt_b]
    simp
    cases Compare.dec_lt a.inc b <;> simp
    {
      match nat.sat_sub_inc a b with
      | .inr g =>
        next g₀ => {
          apply Or.inr
          rw [nat.not_lt_is_sym_le] at g₀
          have := nat.le_le_to_eq g g₀
          rw [this]
          rw [nat.sat_sub_id]
          rw [remainder.zero]
        }
      | .inl g =>
        rw [g]
        apply prev
    }
    {
      rw [nat.not_lt_is_sym_le] at not_a_lt_b

      next inca_lt_b => {
        have := nat.lt_le_trans inca_lt_b not_a_lt_b
        have := nat.lt_trans (nat.a_lt_inc_a a) this
        have := nat.not_lt_id a
        contradiction
      }
    }
  }

theorem remainder.dec : ∀ {a b: nat} {h}, remainder a.inc b h = nat.zero -> nat.inc (remainder a b h) = b
 := by
  apply remainder.induction
  {
    intro a b h a_lt_b rem_eq_zero
    unfold remainder
    rw [dec.pick_true (Compare.dec_lt _ _) a_lt_b]
    simp
    have := remainder.to_dvd rem_eq_zero
    match this.is_le (nat.zero_lt_inc _) with
    | .inr _ =>
      apply Compare.ord_implies_eq
      apply Compare.ord_symm
      assumption
    | .inl g =>
      have := Compare.ord_implies_lt g
      have := nat.no_between_inc a_lt_b
      contradiction
  }
  {
    intro a b h not_a_lt_b prev rem_eq_zero
    unfold remainder
    rw [dec.pick_false (Compare.dec_lt _ _) not_a_lt_b]
    simp
    apply prev
    have := remainder.to_dvd rem_eq_zero
    have d := this.sat_sub
    match nat.sat_sub_inc a b with
    | .inl sub_inc =>
      rw [sub_inc] at d
      rw [remainder.of_dvd d]
    | .inr (.inl inca_lt_b) =>
      have inca_lt_b := Compare.ord_implies_lt inca_lt_b
      rw [nat.not_lt_is_sym_le] at not_a_lt_b
      have := nat.lt_le_trans inca_lt_b not_a_lt_b
      have := nat.lt_trans (nat.a_lt_inc_a _) this
      have := nat.not_lt_id a
      contradiction
    | .inr (.inr inca_eq_b) =>
      have inca_eq_b := Compare.ord_implies_eq inca_eq_b
      rw [←inca_eq_b] at not_a_lt_b
      have := nat.a_lt_inc_a a
      contradiction
  }

theorem remainder.eq_add_right_irr : ∀ a b h c d, remainder a b h = remainder c b h -> remainder (nat.add a d) b h = remainder (nat.add c d) b h := by
  intro a b h c d rem_a_eq_rem_c
  match d with
  | .zero =>  
    rw [nat.add_zero_r, nat.add_zero_r]
    assumption
  | .inc d₀ =>
    have rem_d₀ := remainder.eq_add_right_irr a b h c d₀ rem_a_eq_rem_c
    rw [nat.add_inc, nat.add_inc]
    match remainder.inc (nat.add a d₀) b h with
    | .inr g => 
      rw [g]
      match remainder.inc (nat.add c d₀) b h with
      | .inr g => rw [g]
      | .inl g₀ =>
      apply False.elim
      rw [←rem_d₀] at g₀
      have := remainder.dec g
      rw [this] at g₀
      clear this
      have := remainder.lt (nat.inc (nat.add c d₀)) b h
      rw [g₀] at this
      have := nat.not_lt_id b
      contradiction
    | .inl g =>
    rw [g]
    match remainder.inc (nat.add c d₀) b h with
    | .inl g =>
      rw [g]
      rw [nat.eq_inc_irr]
      assumption
    | .inr g₀ =>
      apply False.elim
      rw [rem_d₀] at g
      have := remainder.dec g₀
      rw [this] at g
      clear this
      have := remainder.lt (nat.inc (nat.add a d₀)) b h
      rw [g] at this
      have := nat.not_lt_id b
      contradiction

theorem remainder.eq_add_left_irr : ∀ a b h c d, remainder a b h = remainder c b h -> remainder (nat.add d a) b h = remainder (nat.add d c) b h := by
  intro _ _ _ _ d
  rw [nat.add_comm d _, nat.add_comm d _]
  apply remainder.eq_add_right_irr

theorem remainder.mul : ∀ a b h c g, remainder (nat.mul c a) (nat.mul c b) g = (nat.mul c (remainder a b h)) := by
  -- (c * a) % (c * b) = c * (a % b)
  -- assert c * (a % b) < c * b
  -- (c * 0) % (c * b) = c * (0 % b)

  -- (c * (a + 1)) % (c * b) = c * ((a + 1) % b)
  -- (c + c * a) % (c * b) = c * ((a + 1) % b)
    -- if b | a + 1
      -- (c * (a + 1)) % (c * b) = c * 0
      -- c * b | c * (a + 1)
      -- 0 = c * 0
    -- else ¬ b | a + 1
      -- (c + c * a) % (c * b) = (c * (a + 1) % b) % (c * b)
      -- (c + c * a) % (c * b) = (c * (1 + a % b)) % (c * b)
      -- (c + c * a) % (c * b) = (c + c * (a % b)) % (c * b)
      -- (c * a) % (c * b) = (c * (a % b)) % (c * b) (inductive case)
  intro a b h c g
  have mul_rem_lt : remainder a b h < b := remainder.lt a b h
  match Compare.dec_lt nat.zero c with
  | .isFalse c_le_zero =>
    rw [nat.not_lt_is_sym_le] at c_le_zero
    match c with
    | .zero =>
    simp
    rw [remainder.zero]
  | .isTrue c_gt_zero =>
  rw [←nat.lt_mul_irr c_gt_zero] at mul_rem_lt
  match a with
  | .zero =>
    rw [nat.mul_zero_r, remainder.zero, remainder.zero, nat.mul_zero_r]
  | .inc a₀ =>
    match remainder.inc a₀ b h with
    | .inr a_dvd_b =>
      rw [a_dvd_b]
      rw [nat.mul_zero_r]
      have := remainder.to_dvd a_dvd_b
      have : dvd (nat.mul c a₀.inc) (nat.mul c b) := by
        have ⟨ x, prf ⟩ := this
        exists x
        rw [prf]
        rw [nat.mul_perm0]
      rw [remainder.of_dvd this]
    | .inl reminc =>
      rw [reminc]
      rw [reminc] at mul_rem_lt
      have := remainder.eq_lt (
        nat.mul c (nat.inc (remainder a₀ b h))
      ) (
        nat.mul c b
      ) g mul_rem_lt
      conv => {
        rhs
        rw [←this]
      }
      rw [nat.mul_inc_r]
      rw [nat.mul_inc_r]
      apply remainder.eq_add_left_irr
      rw [nat.mul_inc_r] at mul_rem_lt
      rw [nat.add_comm] at mul_rem_lt
      have := nat.le_lt_trans (
        nat.a_le_a_plus_b _ _
      ) mul_rem_lt
      rw [nat.add_comm] at mul_rem_lt
      rw [remainder.eq_lt _ _ _ this]
      apply remainder.mul

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

def remainder.bounded (x a b: nat):
   nat.zero < b -> nat := match x with
  | .zero => fun _ => .zero
  | .inc x₀ =>
  fun zero_lt_b =>
    match Compare.dec_lt a b with
    | .isTrue _ => a
    | .isFalse _ => remainder.bounded x₀ (a.saturating_sub b) b zero_lt_b

@[reducible]
def gcd.bounded_imp (x a b: nat) : nat :=
  match x with
  | .zero => .zero
  | .inc x₀ => 
      match h:a with
    | .zero => b
    | .inc a₀ => gcd.bounded_imp x₀ (remainder.bounded (nat.inc b) b a (by rw [h]; apply nat.zero_lt_inc)) a

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

@[reducible]
def gcd.bounded a b := gcd.bounded_imp (nat.add a b).inc a b

theorem remainder.bounded_check : ∀ a b h,
    a < x ->
    a < y ->
    bounded x a b h
  = bounded y a b h := by
  intro a b h a_lt_x a_lt_y
  have x_gt_zero := nat.gt_implies_gt_zero a_lt_x
  have y_gt_zero := nat.gt_implies_gt_zero a_lt_y
  match x, y with
  | .inc x₀, .inc y₀ =>
  clear x_gt_zero y_gt_zero
  unfold bounded
  cases Compare.dec_lt a b <;> simp
  match b with
  | .inc b₀ =>
  have b_le_a : b₀.inc <= a := by
    apply (@nat.not_lt_is_sym_le a b₀.inc).mp
    assumption
  have := @nat.sat_sub_lt a b₀.inc (nat.zero_lt_inc _) b_le_a
  apply remainder.bounded_check
  rw [nat.lt_inc_to_le] at a_lt_x
  exact nat.lt_le_trans this a_lt_x
  rw [nat.lt_inc_to_le] at a_lt_y
  exact nat.lt_le_trans this a_lt_y

theorem remainder.bounded_eq : ∀a b h, remainder a b h = remainder.bounded a.inc a b h := by
  apply remainder.induction
  {
    intro a b h a_lt_b
    unfold remainder remainder.bounded
    rw [dec.pick_true (Compare.dec_lt _ _) a_lt_b]
  }
  {
    intro a b h not_a_lt_b prev
    unfold remainder remainder.bounded
    rw [dec.pick_false (Compare.dec_lt _ _) not_a_lt_b]
    simp
    rw [prev]
    apply remainder.bounded_check
    apply nat.a_lt_inc_a
    apply nat.sat_sub_lt
    assumption
    apply (@nat.not_lt_is_sym_le a b).mp
    assumption
  }

theorem gcd.bounded_check : ∀ a b,
    a < x ->
    a < y ->
    bounded_imp x a b
  = bounded_imp y a b := by
  intro a b a_lt_x a_lt_y
  have x_gt_zero := nat.gt_implies_gt_zero a_lt_x
  have y_gt_zero := nat.gt_implies_gt_zero a_lt_y
  match x, y with
  | .inc x₀, .inc y₀ =>
  clear x_gt_zero y_gt_zero
  unfold bounded_imp
  match a with
  | .zero => simp
  | .inc a₀ =>
  simp
  apply gcd.bounded_check
  have a_lt_x : a₀ < x₀ := a_lt_x
  apply nat.le_lt_trans _ a_lt_x
  apply (@nat.lt_inc_to_le _ _).mp
  rw [←remainder.bounded_eq]
  apply remainder.lt
  
  have a_lt_y : a₀ < y₀ := a_lt_y
  apply nat.le_lt_trans _ a_lt_y
  apply (@nat.lt_inc_to_le _ _).mp
  rw [←remainder.bounded_eq]
  apply remainder.lt
  

theorem gcd.bounded_imp_eq : ∀a b, gcd a b = gcd.bounded_imp (nat.add a b).inc a b := by
  apply gcd.induction
  {
    intro a
    rfl
  }
  {
    intro a b h prev
    unfold gcd gcd.bounded_imp
    match a with
    | .zero => contradiction
    | .inc a₀ =>
    simp
    rw [prev]
    clear prev
    rw [remainder.bounded_eq]
    apply gcd.bounded_check
    apply nat.lt_trans (nat.a_lt_inc_a _)
    rw [nat.lt_inc_irr]
    rw [nat.lt_add_const_irr]
    apply nat.zero_lt_inc

    rw [←remainder.bounded_eq]
    have := remainder.lt b a₀.inc h
    apply nat.lt_le_trans (remainder.lt b a₀.inc h)
    rw [nat.le_inc_irr]
    conv => {
      lhs
      rw [←nat.add_zero_r a₀]
    }
    rw [nat.le_add_irr]
    apply nat.zero_le
  }

theorem gcd.bounded_eq : ∀a b, gcd a b = gcd.bounded a b := 
  fun a b => gcd.bounded_imp_eq a b

def nat.coprime a b := gcd.bounded a b = nat.zero.inc

theorem nat.coprime.to_gcd (c: nat.coprime a b) : gcd a b = nat.zero.inc := by  
  rw [gcd.bounded_eq]
  assumption

instance : Decidable (nat.coprime a b) := by
  unfold nat.coprime
  apply nat.compare_eq

-- check that coprime is reducible
example : nat.coprime nat.zero.inc.inc.inc nat.zero.inc.inc.inc.inc := by decide

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
    have := remainder.to_dvd h
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

theorem gcd.id : gcd a a = a := by
  unfold gcd
  cases a
  simp
  simp
  next a => {
    rw [(remainder.of_dvd (dvd.id a.inc))]
    rw [gcd.zero_left]
  }

theorem gcd.zero_right : gcd a nat.zero = a := by
  unfold gcd
  cases a
  simp
  simp
  next a => {
    simp
    rw [remainder.zero]
    rw [gcd.zero_left]
  }

theorem gcd.of_dvd : 
  ∀ {a b},
  dvd a c ->
  dvd b c ->
  dvd (gcd a b) c := by
  apply gcd.induction
  {
    intro a
    intro _ dvd_a_c
    rw [gcd.zero_left]
    assumption
  }
  {
    intro a b zero_lt_a prev dvd_a_c dvd_b_c
    unfold gcd
    cases a
    contradiction
    simp
    apply prev
    clear prev
    {
      have ⟨ x, prfx ⟩ := dvd_a_c
      have ⟨ y, prfy ⟩ := dvd_b_c
      exists remainder y x (by
        match x with
        | .zero => rw [nat.mul_zero_r] at prfx; contradiction
        | .inc _ => apply nat.zero_lt_inc)
      rw [prfy]
      conv => {
        lhs
        lhs
        rw [prfx]
      }
      rw [remainder.mul]
    }
    assumption
  }

theorem gcd.to_dvd {a b c} : 
  dvd (gcd a b) c ->
  dvd a c ∧ 
  dvd b c := by
  apply @gcd.induction (fun a b => ∀c, dvd (gcd a b) c -> dvd a c ∧ dvd b c) _ _ a b
  {
    intro a b dvd_gcd
    rw [gcd.zero_left] at dvd_gcd
    apply And.intro
    exact dvd.zero _
    assumption
  }
  {
    intro a b a_gt_zero prev c dvd_gcd
    unfold gcd at dvd_gcd
    match a with
    | .zero => contradiction
    | .inc a₀ =>
    simp at dvd_gcd
    have ⟨ dvd_a, dvd_b ⟩  := prev c dvd_gcd
    apply And.intro
    assumption
    have ⟨ x, prf ⟩  := remainder.def b a₀.inc a_gt_zero
    rw [prf]
    apply dvd.add
    assumption
    apply dvd.mul
    assumption
  }

theorem gcd.is_dvd a b : 
  dvd a (gcd a b) ∧ dvd b (gcd a b) := 
    gcd.to_dvd (dvd.id _)

theorem gcd.comm a b : gcd a b = gcd b a := by 
  have ⟨ a_ab, b_ab ⟩  := gcd.is_dvd a b
  have ⟨ a_ba, b_ba ⟩  := gcd.is_dvd b a
  apply dvd.to_eq <;> apply gcd.of_dvd <;> assumption

theorem gcd.assoc : gcd a (gcd b c) = gcd (gcd a b) c := by
  have ⟨ _, bc ⟩  := gcd.is_dvd a (gcd b c)
  have ⟨ b_bc, c_bc ⟩ := gcd.is_dvd b c
  have _ := dvd.trans b_bc bc
  have _ := dvd.trans c_bc bc

  have ⟨ ab, _ ⟩  := gcd.is_dvd (gcd a b) c
  have ⟨ a_ab, b_ab ⟩ := gcd.is_dvd a b
  have _ := dvd.trans a_ab ab
  have _ := dvd.trans b_ab ab

  apply dvd.to_eq
  repeat any_goals apply gcd.of_dvd
  all_goals assumption

theorem gcd.one_left : gcd nat.zero.inc a = nat.zero.inc := by
  have ⟨ dvd_one, _ ⟩   := gcd.is_dvd nat.zero.inc a 
  apply dvd.to_eq
  exact dvd.one _
  assumption

theorem gcd.one_right : gcd a nat.zero.inc = nat.zero.inc := by
  have ⟨ _, dvd_one ⟩   := gcd.is_dvd a nat.zero.inc
  apply dvd.to_eq
  exact dvd.one _
  assumption

theorem gcd.zero : ∀ { a b }, (gcd a b = nat.zero) = (a = nat.zero ∧ b = nat.zero) := by
  apply gcd.induction
  {
    intro a
    rw [gcd.zero_left]
    simp
  }
  {
    intro a b h prev
    unfold gcd
    match a with
    | .zero => simp
    | .inc a₀ =>
    conv => {
      lhs 
      lhs
      simp
    }
    apply Eq.propIntro
    intro x 
    have ⟨ _, _ ⟩  := prev.mp x
    contradiction
    intro h
    have ⟨ _, _ ⟩ := h
    contradiction
  }

theorem gcd.dvd_left : (gcd a b = b) = dvd a b := by
  apply Eq.propIntro
  intro g
  have ⟨ d, _ ⟩  := gcd.is_dvd a b
  rw [g] at d
  assumption
  intro d
  apply dvd.to_eq
  apply gcd.of_dvd d (dvd.id _)
  have ⟨ _, _ ⟩  := gcd.is_dvd a b
  assumption

theorem gcd.dvd_right : (gcd a b = a) = dvd b a := by
  rw [gcd.comm]
  apply gcd.dvd_left

theorem gcd.of_dvd_mul : 
  ∀ {a b},
  dvd (nat.mul f a) c ->
  dvd (nat.mul f b) c ->
  dvd (nat.mul f (gcd a b)) c := by
  apply gcd.induction
  {
    intro a
    intro _ dvd_a_c
    rw [gcd.zero_left]
    assumption
  }
  {
    match f with
    | .zero =>
      intro a b zero_lt_a _ _ _
      rw [nat.mul_zero]
      exact dvd.zero _
    | .inc f₀ =>
    intro a b zero_lt_a prev dvd_a_c dvd_b_c
    unfold gcd
    cases a
    contradiction
    simp
    apply prev
    clear prev
    {
      rw [←remainder.mul]
      have ⟨ x, prfx ⟩ := dvd_a_c
      have ⟨ y, prfy ⟩ := dvd_b_c
      exists remainder y x (by
        match x with
        | .zero =>
          rw [nat.mul_zero_r] at prfx
          contradiction
        | .inc _ => apply nat.zero_lt_inc)
      rw [prfy]
      conv => {
        lhs
        lhs
        rw [prfx]
      }
      rw [remainder.mul]
      simp; apply nat.zero_lt_inc
    }
    assumption
  }

theorem gcd.mul_left : gcd (nat.mul a b) (nat.mul a c) = nat.mul a (gcd b c) := by
  have ⟨ dvd_ab, dvd_ac ⟩  := gcd.is_dvd (nat.mul a b) (nat.mul a c)
  have ⟨ dvd_b, dvd_c ⟩  := gcd.is_dvd b c

  apply dvd.to_eq
  {
    apply gcd.of_dvd
    have ⟨ x, prf ⟩ := dvd_b
    exists x
    conv => {
      lhs
      rw [prf]
    }
    rw [nat.mul_perm0]
    have ⟨ x, prf ⟩ := dvd_c
    exists x
    conv => {
      lhs
      rw [prf]
    }
    rw [nat.mul_perm0]
  }
  {
    apply gcd.of_dvd_mul
    have ⟨ x, prf ⟩ := dvd_ab
    exists x
    have ⟨ x, prf ⟩ := dvd_ac
    exists x
  }

theorem nat.coprime.comm (c: nat.coprime a b) : nat.coprime b a := by
  unfold nat.coprime
  rw [←gcd.bounded_eq]
  rw [gcd.comm]
  rw [gcd.bounded_eq]
  assumption
