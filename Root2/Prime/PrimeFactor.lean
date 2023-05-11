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
def List.sorted [Compare α] (list: List α) : Prop := match list with
  | [] | [_] => True
  | a :: b :: xs => b <= a ∧ sorted (b :: xs)

@[simp]
def List.concat_sorted [Compare α] (a b: List α) : List α := match a with
| [] => b
| a₀::as => match b with
| [] => a₀::as
| b₀::bs => match Compare.ord a₀ b₀ with
| .Eq => a₀ :: b₀ :: as.concat_sorted bs
| .Less => b₀::(List.concat_sorted (a₀::as) bs)
| .Greater => a₀::(List.concat_sorted as (b₀::bs))
termination_by List.concat_sorted a b => (a, b)

theorem list_concat_sorted_empty [Compare α] {{as: List α}} : List.concat_sorted as [] = as := by
  cases as <;> simp

theorem pop_sorted [Compare α] {{a: α}} {{as: List α}} : (a::as).sorted -> as.sorted := by
  intro list_sorted
  match as with
  | [] => trivial
  | a₀::as₀ => exact list_sorted.right

theorem singleton_list_is_sorted [Compare α] {a: α} : [a].sorted := by simp

theorem list_concat_sorted_fst [Compare α] {{ a b : α }} (b_lt_a: b < a) : a :: (List.concat_sorted as (b::bs)) = List.concat_sorted (a::as) (b::bs) := by
  simp
  rw [Compare.flip]
  rw [b_lt_a]
  simp

theorem list_concat_sorted_snd [Compare α] {{ a b : α }} (a_lt_b: a < b) : b :: (List.concat_sorted (a::as) bs) = List.concat_sorted (a::as) (b::bs)  := by
  simp
  rw [a_lt_b]

theorem list_sorted_snd_fst_empty [Compare α] {{ b : α }} (bbs_sorted : (b :: bs).sorted) :
  List.sorted (b :: List.concat_sorted [] bs) := by
  simp
  assumption

theorem list_sorted_fst_snd_empty [Compare α] {{ a : α }} (aas_sorted : (a :: as).sorted) :
  List.sorted (a :: List.concat_sorted as []) := by
  rw [list_concat_sorted_empty]
  assumption

mutual
  theorem list_sorted_fst_snd_nonempty [Compare α] {{ a b : α }} {{ as : List α }} (b_le_a: b <= a) (aas_sorted : (a :: as).sorted) (bbs_sorted : (b :: bs).sorted) :
    List.sorted (a :: List.concat_sorted as (b :: bs)) := by
    match as with
    | [] => 
      simp
      apply And.intro
      assumption
      assumption
    | a' :: as' =>
    simp
    cases h:Compare.ord a' b <;> simp 
    repeat any_goals apply And.intro
    assumption
    apply list_sorted_snd_fst_nonempty
    apply Or.inl
    assumption
    exact aas_sorted.right
    assumption
    exact aas_sorted.left
    apply Or.inr
    apply Compare.ord_symm
    assumption
    have a'_eq_b : a' = b := Compare.ord_implies_eq h
    match bs with
    | [] =>
      apply list_sorted_fst_snd_empty
      rw [←a'_eq_b]
      exact aas_sorted.right
    | b'::bs' =>
      rw [←a'_eq_b]
      apply list_sorted_fst_snd_nonempty
      rw [a'_eq_b]
      exact bbs_sorted.left
      exact aas_sorted.right
      exact bbs_sorted.right
    exact aas_sorted.left
    apply list_sorted_fst_snd_nonempty
    apply Or.inl
    rw [Compare.ord_flip]
    assumption
    exact aas_sorted.right
    exact bbs_sorted
  theorem list_sorted_snd_fst_nonempty [Compare α] {{ a b : α }} {{ as : List α }} (a_le_b: a <= b) (aas_sorted : (a :: as).sorted) (bbs_sorted : (b :: bs).sorted) :
    List.sorted (b :: List.concat_sorted (a :: as) bs) := by
    match bs with
    | [] => 
      simp
      apply And.intro
      assumption
      assumption
    | b' :: bs' =>
    simp
    cases h:Compare.ord a b' <;> simp 
    repeat any_goals apply And.intro
    exact bbs_sorted.left
    apply list_sorted_snd_fst_nonempty
    apply Or.inl; assumption
    assumption
    exact bbs_sorted.right
    assumption
    apply Or.inr
    apply Compare.ord_symm
    assumption
    match as with
    | [] =>
      apply list_sorted_snd_fst_empty
      exact bbs_sorted.right
    | a'::as' => 
      apply list_sorted_snd_fst_nonempty
      have a_eq_b' : a = b' := by
        apply Compare.ord_implies_eq
        assumption
      rw [←a_eq_b']
      exact aas_sorted.left
      exact aas_sorted.right
      exact bbs_sorted.right
    assumption
    apply list_sorted_fst_snd_nonempty
    rw [Compare.ord_flip] at h
    simp at h
    apply Or.inl
    assumption
    exact aas_sorted
    exact bbs_sorted.right
end
  termination_by
    list_sorted_fst_snd_nonempty => (as, bs)
    list_sorted_snd_fst_nonempty => (as, bs)

theorem concat_sorted_empty_right [Compare α] (a_list: List α) : List.concat_sorted a_list [] = a_list := by
  cases a_list <;> simp

def len_le_than_two (list: List a) : Prop := match list with
  | [] | [_] | [_, _] => True
  | _ => False

theorem concat_sorted_comm 
  [Compare α]
  {{alist blist: List α}}
  (a_sorted: alist.sorted) (b_sorted: blist.sorted)
  : alist.concat_sorted blist = blist.concat_sorted alist := by
  unfold List.concat_sorted
  match alist, blist with
  | [], _ => simp; split <;> rfl
  | _, [] => simp; split <;> rfl
  | a::as, b::bs => 
    simp
    split <;> simp
    have a_eq_b : a = b := by
      apply Compare.ord_implies_eq
      assumption
    rw [a_eq_b]
    rw [Compare.ord_id]
    simp
    apply concat_sorted_comm <;> (apply pop_sorted; assumption)
    next a_lt_b => {
      rw [Compare.ord_flip] at a_lt_b
      simp at a_lt_b
      rw [a_lt_b]
      simp
      apply concat_sorted_comm
      assumption
      apply pop_sorted
      assumption
    }
    next a_gt_b => {
      rw [Compare.ord_flip] at a_gt_b
      simp at a_gt_b
      rw [a_gt_b]
      simp
      apply concat_sorted_comm
      apply pop_sorted
      assumption
      assumption
    }
  termination_by concat_sorted_comm => (alist, blist)

theorem concat_sorted_keeps_sorted_small
  [inst: Compare α]
  (alist blist: List α)
  (a_sorted: alist.sorted) (b_sorted: blist.sorted)
  (a_or_b_small: len_le_than_two a_list ∨ len_le_than_two b_list)
  : (alist.concat_sorted blist).sorted := 
by
  match h₁:alist, h₂:blist with
  | [], _ => simp; assumption
  | _, [] => unfold List.concat_sorted; split; assumption; exact a_sorted
  | [a], [b] =>
    unfold List.concat_sorted
    split <;> simp
    next a' ns list_a_eq => {
      match ns with 
      | _ :: _ => simp at list_a_eq
      | [] => 
      simp at list_a_eq
      rw [←list_a_eq]
      simp
      split
      simp
      apply Or.inr
      apply Compare.ord_symm
      assumption
      simp
      apply Or.inl
      assumption
      simp
      apply Or.inl
      rw [Compare.ord_flip]
      assumption
    }
  | [a], b₀ :: b₁ :: bs =>
    simp
    split <;> simp
    repeat any_goals apply And.intro
    apply Or.inr
    apply Compare.ord_symm
    assumption
    exact b_sorted.left
    exact b_sorted.right
    admit
    apply Or.inl
    rw [Compare.ord_flip]
    simp
    assumption
    exact b_sorted.left
    exact b_sorted.right
  | a₀ :: a₁ :: as, [b] =>
    rw [concat_sorted_comm a_sorted b_sorted]
    simp
    split <;> simp
    repeat any_goals apply And.intro
    apply Or.inr
    apply Compare.ord_symm
    assumption
    exact a_sorted.left
    exact a_sorted.right
    admit
    apply Or.inl
    rw [Compare.ord_flip]
    simp
    assumption
    exact a_sorted.left
    exact a_sorted.right
  | [a₀, a₁], [b₀,b₁] => 
    unfold List.concat_sorted
    simp
    split <;> simp
    have a₀_eq_b₀ : a₀ = b₀ := by
      apply Compare.ord_implies_eq
      assumption
    rw [a₀_eq_b₀]
    apply And.intro
    apply Or.inr
    exact Compare.ord_id
    split <;> simp
    have a₁_eq_b₁ : a₁ = b₁ := by
      apply Compare.ord_implies_eq
      assumption
    rw [a₁_eq_b₁]
    apply And.intro
    exact b_sorted.left
    apply Or.inr
    exact Compare.ord_id
    
    apply And.intro
    exact b_sorted.left
    apply Or.inl
    assumption
    apply And.intro
    rw [←a₀_eq_b₀]
    exact a_sorted.left
    apply Or.inl
    rw [Compare.ord_flip]
    simp
    assumption
    
    split
    have a₀_eq_b₁ : a₀ = b₁ := by
      apply Compare.ord_implies_eq
      assumption
    rw [a₀_eq_b₁]
    simp
    repeat any_goals apply And.intro
    exact b_sorted.left
    exact Or.inr Compare.ord_id
    rw [←a₀_eq_b₁]
    exact a_sorted.left
    exact b_sorted.left
    
    apply Or.inl
    assumption
    exact a_sorted.left
    exact singleton_list_is_sorted
    apply Or.inl
    assumption
    
    split <;> simp
    have a₁_eq_b₁ : a₁ = b₁ := by
      apply Compare.ord_implies_eq
      assumption
    apply And.intro
    exact a_sorted.left
    rw [a₁_eq_b₁]
    apply Or.inr; exact Compare.ord_id
    apply And.intro
    apply Or.inl
    rw [Compare.ord_flip]
    assumption
    apply Or.inl
    assumption
    apply And.intro
    exact a_sorted.left
    apply Or.inl
    rw [Compare.ord_flip]
    assumption
    
    split <;> simp
    have a₁_eq_b₀ : a₁ = b₀ := by
      apply Compare.ord_implies_eq
      assumption
    repeat any_goals apply And.intro
    exact a_sorted.left
    rw [a₁_eq_b₀]
    apply Or.inr; exact Compare.ord_id
    exact b_sorted.left
    apply Or.inl
    rw [Compare.ord_flip]
    assumption
    split <;> simp
    have a₁_eq_b₁ : a₁ = b₁ := by
      apply Compare.ord_implies_eq
      assumption
    apply And.intro
    rw [a₁_eq_b₁]
    exact b_sorted.left
    rw [a₁_eq_b₁]
    apply Or.inr; exact Compare.ord_id
    apply And.intro
    exact b_sorted.left
    apply Or.inl
    assumption
    apply And.intro
    apply Or.inl
    assumption
    apply Or.inl
    rw [Compare.ord_flip]
    assumption
    exact a_sorted.left
    apply Or.inl
    rw [Compare.ord_flip]
    assumption
    exact b_sorted.left
  | [a₀, a₁], b₀::b₁::bs =>
    simp
    split
    admit
    admit
    admit
  | a₀::a₁::as, [b₀, b₁] =>
    admit
  | _::_::_::_, _::_::_::_ =>
    admit

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
