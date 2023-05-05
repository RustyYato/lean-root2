import  Root2.Nat
import Root2.Cmp
import Init.Data.Array.DecidableEq

@[simp]
def ord_imp (a b: nat) := match a, b with
  | .zero, .zero => Order.Eq
  | .zero, .inc _ => Order.Less
  | .inc _, .zero => Order.Greater
  | .inc a₀, .inc b₀ => ord_imp a₀ b₀

def ord_imp_id {a:nat} : ord_imp a a = Order.Eq := by
    match a with
    | nat.zero => rfl
    | nat.inc a₀ =>
      simp
      exact ord_imp_id

def ord_imp_flip {a b:nat} {o: Order} : (ord_imp a b = o) = (ord_imp b a = o.flip) := by
    cases a <;> cases b <;> simp <;> split <;> simp <;> apply ord_imp_flip

def ord_imp_trans {a b c:nat} {o: Order} : ord_imp a b = o -> ord_imp b c = o -> ord_imp a c = o := by
    intro ord_ab ord_bc
    cases a <;> cases b <;> cases c <;> cases o <;> simp <;> simp at *
    apply ord_imp_trans ord_ab ord_bc
    apply ord_imp_trans ord_ab ord_bc
    apply ord_imp_trans ord_ab ord_bc

def ord_imp_eq {a b:nat} : ord_imp a b = Order.Eq -> a = b := by
    intro ord_ab
    cases a <;> cases b <;> simp <;> simp at *
    apply ord_imp_eq ord_ab

@[simp]
instance compare_nat : Compare nat where
  ord := ord_imp
  
  ord_id := ord_imp_id
  ord_flip := ord_imp_flip
  ord_transitive := by apply ord_imp_trans
  ord_implies_eq := by apply ord_imp_eq

theorem nat.zero_lt_inc : ∀ a: nat, nat.zero < nat.inc a := by
  intro
  trivial

theorem nat.zero_le_inc : ∀ a: nat, nat.zero <= nat.inc a := by
  intro
  unfold ord_le
  simp

theorem nat.inc_le_to_le : (nat.inc a) <= (nat.inc b) -> a <= b := by
  intro
  trivial

theorem nat.le_to_inc_le : a <= b -> (nat.inc a) <= (nat.inc b) := by
  unfold ord_le
  simp
  exact id

theorem nat.lt_inc : ((nat.inc a) < (nat.inc b)) = (a < b) := by
  trivial

theorem nat.le_inc : ((nat.inc a) <= (nat.inc b)) = (a <= b) := by
  trivial

theorem nat.not_lt_is_sym_le {{ a b: nat }} : (¬(a < b)) = (b <= a) := by
  unfold ord_lt ord_le
  simp
  match a with
  | nat.zero => match b with
    | nat.zero => simp
    | nat.inc _ => simp
  | nat.inc a₀ => match b with
    | nat.zero => simp
    | nat.inc b₀ => simp; exact @nat.not_lt_is_sym_le a₀ b₀

theorem nat.not_le_is_sym_lt {{ a b: nat }} : (¬(a <= b)) = (b < a) := by
  unfold ord_lt ord_le
  simp
  match a with
  | nat.zero => match b with
    | nat.zero => simp
    | nat.inc _ => simp
  | nat.inc a₀ => match b with
    | nat.zero => simp
    | nat.inc b₀ => simp; exact @nat.not_le_is_sym_lt a₀ b₀

theorem nat.eq_inc_irr : nat.inc a = nat.inc b <-> a = b := by
  apply Iff.intro
  . intro inc_eq; simp at inc_eq; assumption
  . intro eq; rw [eq]

theorem nat.lt_inc_irr (a b: nat) : (inc a < inc b) = (a < b) := by
  trivial

theorem nat.le_inc_irr (a b: nat) : (inc a <= inc b) = (a <= b) := by
  trivial

theorem nat.ne_inc_irr (a b: nat) : (inc a ≠ inc b) = (a ≠ b) := by
  simp

theorem nat.le_id : ∀ a: nat, a <= a := by
  intro a
  match a with
  | nat.zero =>
    unfold ord_le
    simp
  | nat.inc a₀ => rw [←nat.le_inc]; exact (nat.le_id a₀)

theorem nat.zero_le : ∀ a: nat, nat.zero <= a := by
  intro a
  cases a
  apply nat.le_id
  apply nat.zero_le_inc

theorem nat.lt_to_ne : ∀{{a b: nat}}, (a < b) -> ¬(a = b) := by
  intro a b lt
  cases a
  cases b
  trivial
  intro
  trivial
  cases b
  intro
  trivial
  rw [lt_inc] at lt
  rw [nat.eq_inc_irr]
  apply nat.lt_to_ne
  trivial

theorem nat.lt_is_le : ∀ a b: nat, (a < b) -> (a <= b) := by
  intro a b
  match a with
  | nat.zero =>
    intro
    simp
    apply nat.zero_le
    
  | nat.inc a₀ => match b with
    | nat.zero =>
      intro
      trivial
    | nat.inc b₀ =>
      intro lt
      rw [nat.lt_inc_irr] at lt
      rw  [le_inc_irr]
      apply nat.lt_is_le
      assumption

theorem nat.eq_to_le : ∀ {{a b: nat}}, a = b -> (a <= b) := by
  intro a b a_eq_b
  rw [a_eq_b]
  exact (nat.le_id b)

theorem nat.ne_and_le_to_lt : ∀ {{a b: nat}}, a ≠ b -> (a <= b) -> a < b := by
  intro a b a_ne_b a_le_b
  match a, b with
  | nat.zero, nat.inc b₀ => apply nat.zero_lt_inc
  | nat.inc a₀, nat.inc b₀ => 
      rw [nat.ne_inc_irr] at a_ne_b
      rw [nat.le_inc_irr] at a_le_b
      rw [nat.lt_inc_irr]
      apply nat.ne_and_le_to_lt <;> assumption

theorem nat.comp_dec {{a b: nat}} : a < b -> ¬(b <= a) := by
  unfold ord_lt ord_le
  simp
  intro ab ba
  rw [ord_imp_flip] at ab
  simp at ab
  rw [ab] at ba
  cases ba <;> contradiction

@[simp]
theorem nat.le_inc_zero : ∀ {a: nat}, ¬(nat.inc a <= zero) := by
  intro a inca_le_zero
  cases inca_le_zero <;> contradiction

theorem nat.le_le_to_eq : ∀ {{a b: nat}}, a <= b -> b <= a -> a = b := by
  intro a b a_lt_b b_lt_a
  match a with
  | nat.zero => match b with
    | nat.zero => rfl
    | nat.inc b₀ =>

      have _ := nat.le_inc_zero b_lt_a
      contradiction
  | nat.inc a₀ => match b with
    | nat.zero => 

      have _ := nat.le_inc_zero a_lt_b
      contradiction
    | nat.inc b₀ =>
      rw [←nat.le_inc] at *
      rw [nat.eq_inc_irr]
      apply nat.le_le_to_eq <;> assumption

theorem nat.le_zero : ∀ a: nat, a <= nat.zero -> a = nat.zero := by
  intro a a_le_zero
  have zero_le_a := nat.zero_le a
  exact (nat.le_le_to_eq a_le_zero zero_le_a)

theorem nat.not_lt_zero (a: nat) : ¬(a < nat.zero) := by
  intro a_le_zero
  match a with
  | nat.zero => contradiction

theorem nat.a_lt_inc_a : ∀ a: nat, a < nat.inc a := by
  intro a
  match a with
  | nat.zero => trivial
  | nat.inc a₀ => rw [nat.lt_inc]; apply nat.a_lt_inc_a

theorem nat.a_le_inc_a : ∀ a: nat, a <= nat.inc a := by
  intro a
  match a with
  | nat.zero => apply nat.zero_le_inc
  | nat.inc a₀ => rw [nat.le_inc]; apply nat.a_le_inc_a

theorem nat.no_between_inc : ∀ {{a b: nat}}, a < b -> b < nat.inc a -> False := by
  intro a b a_lt_b b_lt_inca
  match a, b with
  | nat.zero, nat.inc _ =>
    rw [nat.lt_inc_irr] at b_lt_inca
    apply nat.not_lt_zero
    assumption
  | nat.inc a₀, nat.inc b₀ =>
    rw [nat.lt_inc_irr] at a_lt_b
    rw [nat.lt_inc_irr] at b_lt_inca
    exact no_between_inc a_lt_b b_lt_inca

theorem nat.lt_to_nat : ∀ a b: nat, a < b <-> toNat a < toNat b := by
  intro a b
  apply Iff.intro
  . intro a_lt_b
    match a with
    | nat.zero => match b with
      | nat.inc b₀ => unfold toNat; apply Nat.zero_lt_succ
    | nat.inc a₀ => match b with
      | nat.inc b₀ =>
        apply Nat.succ_lt_succ
        rw [← nat.lt_inc] at a_lt_b
        exact (nat.lt_to_nat a₀ b₀).mp a_lt_b
  . intro a_lt_b
    match a with
      | nat.zero => match b with
        | nat.inc b₀ => apply nat.zero_lt_inc
      | nat.inc a₀ => match b with
        | nat.inc b₀ =>
          rw [nat.lt_inc]
          unfold toNat at a_lt_b
          have x := Nat.lt_of_succ_lt_succ a_lt_b
          have y := (nat.lt_to_nat a₀ b₀).mpr x
          assumption

theorem nat.le_trans : ∀ {{a b c: nat}}, a <= b -> b <= c -> a <= c := by
  intro a b c a_le_b b_le_c
  match a with
  | nat.zero => apply nat.zero_le
  | nat.inc a₀ => match b with
    | nat.zero => have _ := nat.le_inc_zero a_le_b; contradiction
    | nat.inc b₀ => match c with
      | nat.zero => have _ := nat.le_inc_zero b_le_c; contradiction
      | nat.inc c₀ =>
      rw [nat.le_inc] at *
      exact nat.le_trans a_le_b b_le_c

theorem nat.lt_trans : ∀ {{a b c: nat}}, a < b -> b < c -> a < c := by
  intro a b c a_lt_b b_lt_c
  match c with
  | nat.zero => match b with
     | nat.inc _ => contradiction
  | nat.inc c₀ => match b with
    | nat.zero => match a with
      | nat.inc _ => contradiction
    | nat.inc b₀ => match a with
      | nat.zero => apply nat.zero_lt_inc
      | nat.inc a₀ =>
      rw [nat.lt_inc] at *
      exact nat.lt_trans a_lt_b b_lt_c

theorem nat.lt_le_trans : ∀ {{a b c: nat}}, a < b -> b <= c -> a < c := by
  intro a b c a_lt_b b_lt_c
  match c with
  | nat.zero => match b with
     | nat.zero => assumption
     | nat.inc _ => have := nat.le_inc_zero b_lt_c; contradiction
  | nat.inc c₀ => match b with
    | nat.zero => match a with
      | nat.inc _ => contradiction
    | nat.inc b₀ => match a with
      | nat.zero => apply nat.zero_lt_inc
      | nat.inc a₀ =>
      rw [nat.lt_inc] at *
      exact nat.lt_le_trans a_lt_b b_lt_c

def nat.compare_le (a b: nat) : Decidable (a <= b) :=
  match a with
  | nat.zero => Decidable.isTrue (by unfold ord_le; cases b <;> simp)
  | nat.inc a₀ => match b with
    | nat.zero => Decidable.isFalse (by
      exact nat.le_inc_zero
    )
    | nat.inc b₀ =>
      by rw [@nat.le_inc a₀ b₀]; exact (nat.compare_le a₀ b₀)

def nat.compare_lt (a b: nat) : Decidable (a < b) :=
  match a with
  | nat.zero => match b with
    | nat.zero => Decidable.isFalse (by intro; contradiction)
    | nat.inc _ => Decidable.isTrue (by apply nat.zero_lt_inc)
  | nat.inc a₀ => match b with
    | nat.zero => Decidable.isFalse (by
      intro
      contradiction
    )
    | nat.inc b₀ =>
      by rw [@nat.lt_inc a₀ b₀]; exact (nat.compare_lt a₀ b₀)

def nat.compare_eq (a b: nat) : Decidable (a = b) :=
  match a, b with
   | nat.zero, nat.zero => Decidable.isTrue rfl
   | nat.zero, nat.inc _ => Decidable.isFalse nat.noConfusion
   | nat.inc _, nat.zero => Decidable.isFalse nat.noConfusion
   | nat.inc a₀, nat.inc b₀ => (nat.compare_eq a₀ b₀).byCases
      (fun a₀_eq_b₀ => Decidable.isTrue (a₀_eq_b₀.substr rfl))
      (fun a₀_ne_b₀ => Decidable.isFalse (fun a_eq_b => a₀_ne_b₀ (nat.eq_inc_irr.mp a_eq_b)))

theorem nat.inc_le (a b: nat) : inc a <= b -> a <= b := by
  match b with
  | nat.zero => intro a; have := nat.le_inc_zero a; contradiction
  | nat.inc b₀ =>
    intro a_le_b
    have b_le_inc_b := nat.a_le_inc_a b₀
    exact (nat.le_trans a_le_b b_le_inc_b)

theorem nat.inc_gt_zero {{ a : nat }} : (a.inc <= nat.zero)=False := by
  simp

theorem nat.zero_lt_all {{ a : nat }} : (a < nat.zero)=False := by
  unfold ord_lt; cases a <;> simp

theorem nat.not_lt_id {{ a : nat }} : ¬(a < a) := by
  match a with
  | nat.zero => intro; trivial
  | nat.inc a₀ => rw [nat.lt_inc_irr]; apply nat.not_lt_id

theorem nat.lt_inc_to_le {{ a b: nat }} : (a < inc b) = (a <= b) := by
  match a with
  | nat.zero => unfold ord_lt ord_le; cases b <;> simp
  | nat.inc a₀ => match b with
    | nat.zero =>
      rw [nat.lt_inc_irr, @nat.inc_gt_zero a₀, nat.zero_lt_all]
    | nat.inc b₀ =>
      rw [nat.lt_inc_irr]
      apply nat.lt_inc_to_le

theorem nat.size_of_lt {{ a b : nat }} :  a < b -> sizeOf a < sizeOf b := by
  unfold sizeOf instSizeOfNat_1 toNat
  unfold ord_lt
  match a, b with
  | nat.zero, nat.zero =>
    split <;> (intro; contradiction)
  | nat.zero, nat.inc b₀ => 
    simp
    apply Nat.zero_lt_succ
  | nat.inc a₀, nat.zero =>
    intro
    contradiction
  | nat.inc a₀, nat.inc b₀ => 
    rw [nat.lt_inc_irr]
    intro inc_lt_inc
    simp
    apply Nat.succ_lt_succ
    apply nat.size_of_lt
    assumption

theorem beq_true_implies_eq {{a b: nat}} : (a == b) -> (a = b) := by
  intro a_eq_b
  match a, b with
  | nat.zero, nat.zero => simp
  | nat.inc _, nat.zero => contradiction
  | nat.zero, nat.inc _ => contradiction
  | nat.inc a₀, nat.inc b₀ =>
      rw [nat.eq_inc_irr]
      apply beq_true_implies_eq
      exact a_eq_b

theorem beq_id (a: nat) : a == a := by 
  match a with
  | nat.zero => rfl
  | nat.inc a₀ => apply beq_id a₀

theorem eq_implies_beq_true {{a b: nat}} : (a = b) -> (a == b) := by
  intro a_eq_b
  rw [←a_eq_b]
  apply beq_id

theorem beq_is_eq {{a b: nat}} : (a == b) = (a = b) := by
  have biject : a == b ↔ a =b := Iff.intro (by apply beq_true_implies_eq) (by apply eq_implies_beq_true)
  rw [biject]

theorem beq_false_implies_ne {{a b: nat}} : ((a == b) = false) -> (a ≠ b) := by
  intro a_ne_b
  match a, b with
  | nat.zero, nat.zero => contradiction
  | nat.inc _, nat.zero => intro; contradiction
  | nat.zero, nat.inc _ => intro; contradiction
  | nat.inc a₀, nat.inc b₀ =>
      rw [nat.ne_inc_irr]
      apply beq_false_implies_ne
      exact a_ne_b

theorem ne_implies_beq_false {{a b: nat}} : (a ≠ b) -> ((a == b) = false) := by
  intro a_ne_b
  match a, b with
  | nat.zero, nat.zero => contradiction
  | nat.inc _, nat.zero => rfl
  | nat.zero, nat.inc _ => rfl
  | nat.inc a₀, nat.inc b₀ =>
      rw [nat.ne_inc_irr] at a_ne_b
      have := ne_implies_beq_false a_ne_b
      assumption

theorem beq_is_ne {{a b: nat}} : ((a == b) = false) = (a ≠ b) := by
  have biject : (a == b) = false ↔ a ≠ b := Iff.intro (by apply beq_false_implies_ne) (by apply ne_implies_beq_false)
  rw [biject]


theorem beq_symm {{a b: nat}} {{c: Bool}} : ((a == b) = c) = ((b == a) = c) := by
  match c with
  | true => 
  rw [beq_is_eq, beq_is_eq]
  have := Iff.intro (@Eq.symm _ a b) (@Eq.symm _ b a)
  rw [this]
  | false =>
    rw [beq_is_ne, beq_is_ne]
    have := Iff.intro (@Ne.symm _ a b) (@Ne.symm _ b a)
    rw [this]


theorem nat.not_le_implies_le_symm {{a b: nat}} : ¬ a <= b -> b <= a := by
  intro not_a_le_b
  rw [nat.not_le_is_sym_lt] at not_a_le_b
  exact nat.lt_is_le _ _ not_a_le_b


instance {{a b: nat}} : Decidable (a = b) := nat.compare_eq a b
instance {{a b: nat}} : Decidable (a < b) := nat.compare_lt a b
instance {{a b: nat}} : Decidable (a <= b) := nat.compare_le a b
