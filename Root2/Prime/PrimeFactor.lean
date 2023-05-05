import Root2.Prime
import Root2.Prime.Factors

instance nat_gt_one {n: nat} : nat.zero.inc < nat.inc (nat.inc n) := by
  rw [nat.lt_inc_irr]
  apply nat.zero_lt_inc

@[simp]
def list_product (list: List nat) : nat := match list with
  | [] => nat.zero.inc
  | n :: ns => nat.mul n (list_product ns)

@[simp]
def List.allP (list: List a) (P : a -> Prop) : Prop := match list with
  | [] => True
  | x :: xs => P x ∧ allP xs P

@[simp]
def List.anyP (list: List a) (P : a -> Prop) : Prop := match list with
  | [] => False
  | x :: xs => P x ∨ anyP xs P

@[simp]
def List.sorted_by (list: List a) (P : a -> a -> Prop) : Prop := match list with
  | [] | [_] => True
  | a :: b :: xs => P a b ∧ sorted_by (b :: xs) P

@[simp]
def List.sorted (list: List nat) : Prop := match list with
  | [] | [_] => True
  | a :: b :: xs => b <= a ∧ sorted (b :: xs)

@[simp]
def List.concat_sorted (a b: List nat) : List nat := match a with
| [] => b
| a₀::as => match b with
| [] => a₀::as
| b₀::bs => if a₀ <= b₀ then b₀::(List.concat_sorted (a₀::as) bs) else a₀::(List.concat_sorted as (b₀::bs))
termination_by List.concat_sorted a b => (a, b)

theorem pop_sorted {{a: nat}} {{as: List nat}} : (a::as).sorted -> as.sorted := by
  intro list_sorted
  match as with
  | [] => trivial
  | a₀::as₀ => exact list_sorted.right

theorem singleton_list_is_sorted {a: nat} : [a].sorted := by simp

theorem list_concat_sorted_fst (b_lt_a: b < a) : List.concat_sorted (a::as) (b::bs) = a :: (List.concat_sorted as (b::bs)) := by
  simp
  split
  have := nat.comp_dec b_lt_a (by assumption)
  contradiction
  rfl

theorem list_concat_sorted_snd (_: a <= b) : List.concat_sorted (a::as) (b::bs) = b :: (List.concat_sorted (a::as) bs) := by
  simp
  split
  rfl
  contradiction

theorem concat_sorted_keeps_sorted (a b: List nat) (a_sorted: a.sorted) (b_sorted: b.sorted) : (a.concat_sorted b).sorted := 
by
  unfold List.concat_sorted
  match a, b with
  | [], _ =>
    simp
    assumption
  | _, [] =>
    simp
    split
    simp
    assumption
  | [a₀], [b₀] =>
    simp
    split
    {
      simp
      assumption
    }
    {
      simp
      have b₀_lt_a₀ : b₀ < a₀ := by
        rw [←nat.not_le_is_sym_lt]
        assumption
      exact (nat.lt_is_le _ _ b₀_lt_a₀)
    }
  | [a₀], b₀::b₁::bs =>
    simp
    split <;> simp
    split <;> simp
    apply And.intro
    exact b_sorted.left
    rw [←list_concat_sorted_snd]
    apply concat_sorted_keeps_sorted
    repeat assumption
    exact b_sorted.right
    assumption
    apply And.intro
    assumption
    apply And.intro
    apply nat.not_le_implies_le_symm
    assumption
    exact b_sorted.right
    apply And.intro
    apply nat.not_le_implies_le_symm
    assumption
    apply And.intro
    exact b_sorted.left
    exact b_sorted.right
  | a₀::a₁::as, [b₀] =>
    simp
    split <;> simp
    apply And.intro <;> assumption
    split <;> simp
    repeat any_goals apply And.intro
    repeat any_goals (apply nat.not_le_implies_le_symm; assumption)
    repeat any_goals assumption
    any_goals exact a_sorted.left
    any_goals exact a_sorted.right
    rw [←list_concat_sorted_fst]
    apply concat_sorted_keeps_sorted
    repeat any_goals apply And.intro
    repeat any_goals (apply nat.not_le_implies_le_symm; assumption)
    repeat any_goals (rw [←nat.not_le_is_sym_lt]; assumption)
    repeat any_goals assumption
    any_goals exact a_sorted.right
  | a₀::a₁::as, b₀::b₁::bs =>
    unfold List.concat_sorted
    simp
    split <;> simp <;> split <;> simp
    {
      apply And.intro
      repeat assumption
      exact b_sorted.left
      rw [←list_concat_sorted_snd]
      apply concat_sorted_keeps_sorted
      repeat assumption
      exact b_sorted.right
      repeat assumption
    }
    {
      apply And.intro
      assumption
      split <;> simp
      {
        apply And.intro
        apply nat.not_le_implies_le_symm
        assumption
        rw [←list_concat_sorted_snd]
        apply concat_sorted_keeps_sorted
        exact a_sorted.right
        exact b_sorted.right
        repeat assumption
      }
      {
        apply And.intro
        exact a_sorted.left
        rw [←list_concat_sorted_fst]
        apply concat_sorted_keeps_sorted
        exact a_sorted.right
        exact b_sorted.right
        rw [←nat.not_le_is_sym_lt]
        assumption
      }
    }
    {
      apply And.intro
      apply nat.not_le_implies_le_symm
      assumption
      split
      simp
      apply And.intro
      exact b_sorted.left
      rw [←list_concat_sorted_snd]
      apply concat_sorted_keeps_sorted
      exact a_sorted.right
      exact b_sorted.right
      assumption
      simp
      apply And.intro
      assumption
      rw [←list_concat_sorted_fst]
      apply concat_sorted_keeps_sorted
      exact a_sorted.right
      exact b_sorted.right
      rw [←nat.not_le_is_sym_lt]
      assumption
    }
    {
      apply And.intro
      exact a_sorted.left
      rw [←list_concat_sorted_fst]
      apply concat_sorted_keeps_sorted
      exact a_sorted.right
      assumption
      rw [←nat.not_le_is_sym_lt]
      assumption
    }
  termination_by concat_sorted_keeps_sorted => a.length + b.length
  decreasing_by {
    simp_wf
    try { exact Nat.add_lt_add_left (Nat.lt_succ_self _) (Nat.succ 0) }
    try { exact Nat.add_lt_add_right (Nat.lt_succ_self _) (Nat.succ 0) }
    try {
      repeat rw [Nat.succ_add]
      rw [Nat.add_comm _ (Nat.succ _)]
      repeat rw [Nat.succ_add]
      rw [Nat.add_comm _ (Nat.succ _)]
      repeat rw [Nat.succ_add]
      repeat apply Nat.succ_lt_succ
      repeat rw [←Nat.succ_add]
      apply Nat.add_lt_add_right
      apply Nat.le_succ
    }
    try {
      repeat rw [Nat.succ_add]
      rw [Nat.add_comm _ (Nat.succ _)]
      rw [Nat.succ_add]
      apply Nat.succ_lt_succ
      apply Nat.lt_succ_self
    }
  }

inductive PrimeFactorization (n: nat) : Type :=
  | PrimeFactors : (factors: List nat)
    -> List.allP factors nat.prime
    -> factors.sorted
    -> n = list_product factors
    -> PrimeFactorization n 

def not_zero : nat -> Prop := fun n => nat.zero < n

theorem mul_list_products (a_no_zeros: a.allP not_zero) (b_no_zeros: b.allP not_zero) : nat.mul (list_product a) (list_product b) = list_product (a ++ b) := by 
  match a with
  | [] => simp; rw [nat.add_zero_r]
  | a₀ :: as =>
    simp
    have ⟨ a₀_ne_zero, a_no_zeros ⟩ := a_no_zeros
    have x := nat.zero
    have y := nat.zero
    rw [←nat.mul_perm0, nat.mul_irr a₀_ne_zero]
    apply mul_list_products
    assumption
    assumption

theorem all_implies {{ α: Type _ }} {{ A B: α -> Prop }} :
  (list: List α) ->
  list.allP A ->
  (∀a, A a -> B a) ->
  list.allP B := by
  intro list all_a A_to_B
  match list with
  | [] => trivial
  | x :: xs => 
  have ⟨ Ax, Axs ⟩ := all_a
  apply And.intro
  exact (A_to_B _ Ax)
  exact all_implies xs Axs A_to_B

theorem concat_preserves_all {{ α: Type _ }} {{ P: α -> Prop }} {{a b: List α}} :
  (List.allP a P) -> (List.allP b P) -> (List.allP (a ++ b) P) := by
  intro all_a all_b
  match a with
  | [] => simp; assumption
  | a₀ :: as =>
    have ⟨ pa, pas ⟩ := all_a
    simp
    apply And.intro
    assumption
    apply concat_preserves_all
    assumption
    assumption

theorem concat_preserves_any {{ α: Type _ }} {{ P: α -> Prop }} {{a b: List α}} :
  (List.anyP a P) ∨ (List.anyP b P) -> (List.anyP (a ++ b) P) := by
  intro all_a_or_all_b
  match all_a_or_all_b with
  | .inl any_a =>
    match a with
    | [] => contradiction
    | a₀ :: as =>
      match any_a with
      | .inl any_a₀ => 
        apply Or.inl
        assumption
      | .inr any_as => 
        apply Or.inr
        apply concat_preserves_any
        apply Or.inl
        assumption
  | .inr any_b =>
    match b with
    | [] => contradiction
    | b₀ :: bs =>
      match a with
      | [] =>
        simp
        assumption
      | a :: as =>
        apply Or.inr
        apply concat_preserves_any
        apply Or.inr
        assumption

def prime_gt_zero (n: nat) (_: nat.prime n) : nat.zero < n := match n with
  | nat.inc _ => nat.zero_lt_inc _

def PrimeFactorization.to_list (p: PrimeFactorization n) : List nat := match p with
  | .PrimeFactors factors _ _ _ => factors

instance : Repr (PrimeFactorization n) where
  reprPrec n := reprPrec n.to_list

def PrimeFactorization.merge {{a b: nat}}
  (pa: PrimeFactorization a)
  (pb: PrimeFactorization b) :
  PrimeFactorization (nat.mul a b) := by
  match pa, pb with
  | .PrimeFactors a_products a_primes a_sorted a_product, .PrimeFactors b_products b_primes b_sorted b_product =>
    apply PrimeFactorization.PrimeFactors (a_products ++ b_products)
    apply concat_preserves_all <;> assumption
    {

      admit
    }
    {
      rw [a_product, b_product]
      apply mul_list_products
      exact all_implies a_products a_primes prime_gt_zero
      exact all_implies b_products b_primes prime_gt_zero
    }

def nat.factorize (n: nat) (_: nat.zero < n) : PrimeFactorization n := by
  match h:n with
  | nat.inc nat.zero => 
    apply PrimeFactorization.PrimeFactors []
    all_goals trivial
  | nat.inc (nat.inc n₀) => 
    rw [←h]
    match n.classify_prime with
    | .Prime p _ => 
      apply PrimeFactorization.PrimeFactors [n]
      simp
      assumption
      simp
      simp
      rw [nat.mul_one_r]
    | .Composite _ composite =>
      
      match n.get_factors (plus_two_gt_one h) composite with
      | .MkFactors a b a_gt_one b_gt_one _ _ n_eq_ab =>

      have a_gt_zero := nat.lt_trans (nat.zero_lt_inc _) a_gt_one
      have b_gt_zero := nat.lt_trans (nat.zero_lt_inc _) b_gt_one
      
      have a_factors := a.factorize a_gt_zero
      have b_factors := b.factorize b_gt_zero

      rw [n_eq_ab]
      exact (a_factors.merge b_factors)
  decreasing_by {
    simp_wf
    apply nat.size_of_lt
    rw [←h] 
    assumption
  }
