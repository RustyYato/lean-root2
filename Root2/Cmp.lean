inductive Order := | Less | Eq | Greater

@[simp]
def Order.flip (c: Order) : Order := match c with
| Less => Greater | Eq => Eq | Greater => Less

class Compare (α: Sort _) where
  ord (_ _: α) : Order

  ord_transitive {{ o: Order }} (_: ord a b = o) (_: ord b c = o) : (ord a c = o)
  ord_flip {{ o: Order }} : (ord a b = o) = (ord b a = o.flip)

  ord_id : (ord a a = Order.Eq) 
  ord_implies_eq (_: ord a b = Order.Eq) : a = b

  lt a b := ord a b = Order.Less

instance ord_lt [Compare α] : LT α where
  lt a b := Compare.ord a b = Order.Less
instance ord_le [Compare α] : LE α where
  le a b := Compare.ord a b = Order.Less ∨ Compare.ord a b = Order.Eq

theorem Compare.ord_symm {{ α: Type }} [Compare α] (a b: α) : ord a b = Order.Eq -> ord b a = Order.Eq := by
  intro ab_eq
  have ab_eq := ord_implies_eq ab_eq
  rw [ab_eq]
  exact ord_id

def Compare.ord_ne_transitive {{ α: Sort _ }} [Compare α] {{ a b c : α }} {{ o : Order }} : 
    o ≠ Order.Eq -> ord a b ≠ o -> ord b c ≠ o  -> ord a c ≠ o := by
      intro o_not_eq ab_ne_o bc_ne_o
      match h:o with
      | .Eq => contradiction
      | .Less =>
        intro ac_less
        match h₀:ord a b with
        | .Less => contradiction
        | .Eq =>
            match h₁:ord b c with  
              | .Less => contradiction
              | .Eq =>
                have ac_eq := ord_transitive h₀ h₁
                rw [ac_less] at ac_eq
                contradiction
              | .Greater =>
                have a_eq_b := ord_implies_eq h₀
                rw [←a_eq_b] at h₁
                rw [ac_less] at h₁
                contradiction
        | .Greater =>
          match h₁:ord b c with  
            | .Less => contradiction
            | .Eq =>
              have a_eq_b := ord_implies_eq h₁
              rw [a_eq_b] at h₀
              rw [ac_less] at h₀
              contradiction
            | .Greater =>
              have ac_eq := ord_transitive h₀ h₁
              rw [ac_less] at ac_eq
              contradiction
      | .Greater =>
        intro ac_greater
        match h₀:ord a b with
        | .Less =>
          match h₁:ord b c with  
            | .Less => 
              have ac_eq := ord_transitive h₀ h₁
              rw [ac_greater] at ac_eq
              contradiction
            | .Eq =>
              have a_eq_b := ord_implies_eq h₁
              rw [a_eq_b] at h₀
              rw [ac_greater] at h₀
              contradiction
            | .Greater => contradiction
        | .Eq =>
            match h₁:ord b c with  
              | .Less => 
                have a_eq_b := ord_implies_eq h₀
                rw [←a_eq_b] at h₁
                rw [ac_greater] at h₁
                contradiction
              | .Eq =>
                have ac_eq := ord_transitive h₀ h₁
                rw [ac_greater] at ac_eq
                contradiction
              | .Greater => contradiction
        | .Greater => contradiction

def Order.flip_flip (o: Order) : o = o.flip.flip := by
  cases o <;> simp

def Compare.ord_not_less {{ α: Sort _ }} [Compare α] {{ a b : α }} (ord_ab: ord a b ≠ Order.Less) : (ord a b = Order.Greater) ∨ (ord a b = Order.Eq) := by
  cases h:ord a b
  contradiction
  apply Or.inr; rfl
  apply Or.inl; rfl

def Compare.ord_not_eq {{ α: Sort _ }} [Compare α] {{ a b : α }} (ord_ab: ord a b ≠ Order.Eq) : (ord a b = Order.Greater) ∨ (ord a b = Order.Less) := by
  cases h:ord a b
  apply Or.inr; rfl
  contradiction
  apply Or.inl; rfl

def Compare.ord_not_greater {{ α: Sort _ }} [Compare α] {{ a b : α }} (ord_ab: ord a b ≠ Order.Greater) : (ord a b = Order.Less) ∨ (ord a b = Order.Eq) := by
  cases h:ord a b
  apply Or.inl; rfl
  apply Or.inr; rfl
  contradiction

def Compare.ord_flip_ne {{ α: Sort _ }} [Compare α] {{ a b : α }} {{ o: Order }} (ord_ab: ord a b ≠ o) : (ord b a ≠ o.flip) := by
  intro ord_ba
  rw [ord_flip] at ord_ba
  simp at ord_ba
  cases o <;> contradiction

def Compare.ord_from_eq {{ α: Sort _ }} [Compare α] {{ a b : α }} : a = b -> ord a b = Order.Eq := by
  intro a_eq_b
  rw [a_eq_b]
  apply ord_id

def Compare.ord_implies_gt {{ α: Sort _ }} [Compare α] {{ a b: α }}
  (a_gt_b: ord a b = Order.Greater) : a > b := by
  rw [ord_flip] at a_gt_b
  exact a_gt_b

def Compare.ord_implies_ge {{ α: Sort _ }} [Compare α] {{ a b: α }}
  (a_ge_b: ord a b ≠ Order.Less) : a >= b := by
  exact (ord_not_greater (ord_flip_ne a_ge_b))

def Compare.ord_implies_ne {{ α: Sort _ }} [Compare α] {{ a b: α }}
  (a_gt_b: ord a b ≠ Order.Eq) : a ≠ b := by
  intro a_eq_b
  match h:ord a b with
  | .Less | .Greater =>
    rw [a_eq_b] at h
    rw [ord_id] at h
    contradiction
  | .Eq => contradiction

def Compare.lt_trans {{ α: Sort _ }} [Compare α] {{ a b c: α }} :
  a < b -> b < c -> a < c := by
  intro a_lt_b b_lt_c
  have a_lt_c := ord_transitive a_lt_b b_lt_c
  exact a_lt_c

def Compare.le_trans {{ α: Sort _ }} [Compare α] {{ a b c: α }} :
  a <= b -> b <= c -> a <= c := by
  intro a_lt_b b_lt_c
  cases a_lt_b <;> cases b_lt_c
  apply Or.inl
  apply @Compare.lt_trans _ _ a b c
  assumption
  assumption
  apply Or.inl
  have b_eq_c : b = c := Compare.ord_implies_eq (by assumption)
  rw [←b_eq_c]
  assumption
  apply Or.inl
  have a_eq_b : a = b := Compare.ord_implies_eq (by assumption)
  rw [a_eq_b]
  assumption
  apply Or.inr
  apply @Compare.ord_transitive _ _ a b c <;> assumption

def Compare.gt_trans {{ α: Sort _ }} [Compare α] {{ a b c: α }} :
  a < b -> b < c -> a < c := by
  apply Compare.lt_trans

def Compare.ge_trans {{ α: Sort _ }} [Compare α] {{ a b c: α }} :
  a <= b -> b <= c -> a <= c := by
  apply Compare.le_trans

def dec_true : Decidable True := Decidable.isTrue True.intro
def dec_false : Decidable False := Decidable.isFalse False.elim

def dec_or : Decidable A -> Decidable B -> Decidable (A ∨ B) := by
  intro deca decb
  cases deca <;> cases decb
  apply Decidable.isFalse
  intro a_or_b
  cases a_or_b <;> contradiction
  all_goals apply Decidable.isTrue
  any_goals (apply Or.inr; assumption)
  apply Or.inl; assumption

instance Order.dec_eq (a b: Order) : Decidable (a = b) := by
  cases a <;> cases b <;> simp
  any_goals apply dec_true
  any_goals apply dec_false

instance Order.dec_ne (a b: Order) : Decidable (¬a = b) := by
  cases a <;> cases b <;> simp
  any_goals apply dec_true
  any_goals apply dec_false

instance Compare.dec_eq [Compare α] (a b: α) : Decidable (a = b) := by
  match h:Compare.ord a b with
  | .Greater | .Less =>
    apply Decidable.isFalse
    apply Compare.ord_implies_ne
    intro a
    rw [h] at a
    contradiction
  | .Eq =>
    apply Decidable.isTrue
    apply Compare.ord_implies_eq
    assumption

instance [Compare α] (a b: α) : Decidable (a ≠ b) := by
  match h:Compare.ord a b with
  | .Greater | .Less =>
    apply Decidable.isTrue
    apply Compare.ord_implies_ne
    intro a
    rw [h] at a
    contradiction
  | .Eq =>
    apply Decidable.isFalse
    simp
    intro not_eq
    apply not_eq
    apply Compare.ord_implies_eq
    assumption

instance [Compare α] (a b: α) : Decidable (a < b) := by
  simp
  apply Order.dec_eq

instance [Compare α] (a b: α) : Decidable (a <= b) := by
  simp
  apply dec_or <;> apply Order.dec_eq

instance [Compare α] (a b: α) : Decidable (a > b) := by
  simp
  apply Order.dec_eq

instance [Compare α] (a b: α) : Decidable (a >= b) := by
  simp
  apply dec_or <;> apply Order.dec_eq