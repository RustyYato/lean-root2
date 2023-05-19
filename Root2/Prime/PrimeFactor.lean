import Root2.Prime
import Root2.Prime.Factors
import Root2.Prime.Divisible

instance nat_gt_one {n: nat} : nat.zero.inc < nat.inc (nat.inc n) := by
  rw [nat.lt_inc_irr]
  apply nat.zero_lt_inc

@[simp]
def contains (as: List α) (a: α) : Prop := match as with
  | [] => False
  | x :: xs => a = x ∨ contains xs a

@[simp]
def list_product (list: List nat) : nat := match list with
  | [] => nat.zero.inc
  | n :: ns => nat.mul n (list_product ns)

@[simp]
def List.allP  (list: List a) (P : a -> Prop) : Prop := match list with
  | [] => True
  | x :: xs => P x ∧ allP xs P

@[simp]
def List.anyP (list: List a) (P : a -> Prop) : Prop := match list with
  | [] => False
  | x :: xs => P x ∨ anyP xs P

@[simp]
def List.mapAllP {{list: List a}} {{ P R: a -> Prop }} (all: list.allP P) (F: ∀a, P a -> R a) : list.allP R := by
  match list with
  | [] => trivial
  | x :: xs =>
    simp
    apply And.intro
    exact F x all.left
    exact List.mapAllP all.right F

@[simp]
def List.mapAnyP {{list: List a}} {{ P R: a -> Prop }} (any: list.anyP P) (F: ∀a, P a -> R a) : list.anyP R := by
  match list with
  | [] => trivial
  | x :: xs =>
    simp
    match any with
    | .inl prf => exact .inl (F x prf)
    | .inr prf => exact .inr (List.mapAnyP prf F)

@[simp]
def List.any_and_not_all {{list: List a}} {{ P: a -> Prop }} (not_all: list.allP fun x => ¬ P x) (any: list.anyP P) : False := by
  match list with
  | [] => trivial
  | x :: xs =>
    simp
    match any with
    | .inl prf => 
      have not_p := not_all.left
      contradiction
    | .inr prf => 
      apply any_and_not_all not_all.right prf

@[simp]
def List.all_and_not_all {{list: List a}} {{ P: a -> Prop }} (not_all: list.allP fun x => ¬ P x) (all: list.allP P) : list = [] := by
  match list with
  | [] => rfl
  | x :: xs =>
    simp
    have not_p := not_all.left
    have p := all.left
    contradiction

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
  have : Compare.ord a b = Order.Greater := Compare.flip b_lt_a
  rw [this]

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
    exact Compare.flip h
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
    apply Or.inl
    exact Compare.flip h
    exact aas_sorted
    exact bbs_sorted.right
end
  termination_by
    list_sorted_fst_snd_nonempty => (as, bs)
    list_sorted_snd_fst_nonempty => (as, bs)

theorem concat_sorted_empty_left [Compare α] (a_list: List α) : List.concat_sorted [] a_list = a_list := by
  cases a_list <;> simp

theorem concat_sorted_empty_right [Compare α] (a_list: List α) : List.concat_sorted a_list [] = a_list := by
  cases a_list <;> simp

@[simp]
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
      rw [Compare.flip a_lt_b]
      simp
      apply concat_sorted_comm
      assumption
      apply pop_sorted
      assumption
    }
    next a_gt_b => {
      rw [Compare.flip a_gt_b]
      simp
      apply concat_sorted_comm
      apply pop_sorted
      assumption
      assumption
    }
  termination_by concat_sorted_comm => (alist, blist)

theorem concat_sorted_keeps_sorted
  [inst: Compare α]
  (alist blist: List α)
  (a_sorted: alist.sorted) (b_sorted: blist.sorted)
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
      apply Compare.of_flip
      assumption
    }
  | a :: as, b :: bs =>
    simp
    cases h:Compare.ord a b <;> simp
    {
      apply list_sorted_snd_fst_nonempty
      apply Or.inl
      assumption
      assumption
      assumption
    }
    {
      apply And.intro
      {
        apply Or.inr
        apply Compare.ord_symm
        assumption
      }
      match as with
      | [] => apply list_sorted_snd_fst_empty; assumption
      | a'::as' =>
        apply list_sorted_snd_fst_nonempty
        have a_eq_b := Compare.ord_implies_eq h
        rw [←a_eq_b]
        exact a_sorted.left
        exact a_sorted.right
        assumption
    }
    {
      apply list_sorted_fst_snd_nonempty
      apply Or.inl
      apply Compare.of_flip
      assumption
      assumption
      assumption
    }

theorem concat_sorted_all [Compare α] {{alist blist: List α}} {{P : α -> Prop}} :
  (alist.allP P) -> (blist.allP P) ->
  (alist.concat_sorted blist).allP P := by
  intro allA allB
  match alist, blist with
  | [], _ =>
    rw [concat_sorted_empty_left]
    assumption
  | _, [] =>
    rw [concat_sorted_empty_right]
    assumption
  | a::as, b::bs =>
  simp
  cases h:Compare.ord a b <;> simp
  repeat any_goals apply And.intro
  exact allB.left
  apply concat_sorted_all allA allB.right
  exact allA.left
  exact allB.left
  apply concat_sorted_all allA.right allB.right
  exact allA.left
  apply concat_sorted_all allA.right allB
termination_by concat_sorted_all => (alist, blist)

theorem concat_sorted_any [Compare α] {{alist blist: List α}} {{P : α -> Prop}} :
  (alist.anyP P) ∨ (blist.anyP P) ->
  (alist.concat_sorted blist).anyP P := by
  intro anyA_or_anyB
  match alist, blist with
  | [], _ =>
    rw [concat_sorted_empty_left]
    match anyA_or_anyB with
    | .inr _ => assumption
  | _, [] =>
    rw [concat_sorted_empty_right]
    match anyA_or_anyB with
    | .inl _ => assumption
  | a::as, b::bs =>
  simp
  cases h:Compare.ord a b <;> simp
  repeat any_goals apply And.intro
  match anyA_or_anyB with
  | .inl anyA =>
    apply Or.inr
    apply concat_sorted_any
    apply Or.inl
    assumption
  | .inr (.inl anyB) =>
    exact .inl anyB
  | .inr (.inr anyB) =>
    apply Or.inr
    apply concat_sorted_any
    apply Or.inr
    assumption
  match anyA_or_anyB with
  | .inl (.inl anyA) =>
    exact .inl anyA
  | .inl (.inr anyA) =>
    apply Or.inr
    apply Or.inr
    apply concat_sorted_any
    apply Or.inl
    assumption
  | .inr (.inl anyB) =>
    exact Or.inr (Or.inl anyB)
  | .inr (.inr anyB) =>
    apply Or.inr
    apply Or.inr
    apply concat_sorted_any
    apply Or.inr
    assumption
  match anyA_or_anyB with
  | .inr anyB =>
    apply Or.inr
    apply concat_sorted_any
    apply Or.inr
    assumption
  | .inl (.inl anyA) =>
    exact .inl anyA
  | .inl (.inr anyA) =>
    apply Or.inr
    apply concat_sorted_any
    apply Or.inl
    assumption
termination_by concat_sorted_any => (alist, blist)

theorem one_not_dvd_prime : ∀ p, p.prime -> ¬ dvd nat.zero.inc p := by
  intro p pprime dvd_one_p
  have ⟨ x, prf ⟩ := dvd_one_p
  have ⟨ p_eq_one, _ ⟩  := nat.mul_eq_one _ _ (Eq.symm prf)
  have pe_ne_one := nat.prime_ne_one pprime
  contradiction

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
    rw [←nat.mul_perm0, nat.mul_irr a₀_ne_zero]
    apply mul_list_products
    assumption
    assumption

theorem combine_list_product {{ a:nat }} {{ as: List nat }} : nat.mul a (list_product as) = (list_product (a::as)) := by
  rfl

theorem mul_sorted_list_products (a_no_zeros: alist.allP not_zero) (b_no_zeros: blist.allP not_zero)
  : nat.mul (list_product alist) (list_product blist) = list_product (alist.concat_sorted blist) := by 
  match alist, blist with
  | [], _ => simp; rw [nat.add_zero_r]
  | _, [] =>
    rw [concat_sorted_empty_right]
    simp
    rw [nat.mul_one_r]
  | a::as, b::bs =>
    simp
    cases h:ord_imp a b <;> simp
    {
      rw [nat.mul_comm, ←nat.mul_perm0, nat.mul_irr]
      rw [combine_list_product, nat.mul_comm]
      apply mul_sorted_list_products
      assumption
      exact b_no_zeros.right
      exact b_no_zeros.left
    }
    {
      rw [nat.mul_perm1, nat.mul_comm, ←nat.mul_perm0 a (list_product _)]
      rw [nat.mul_perm7, nat.mul_irr, nat.mul_irr]
      apply mul_sorted_list_products
      exact a_no_zeros.right
      exact b_no_zeros.right
      exact b_no_zeros.left
      exact a_no_zeros.left
    }
    {
      rw [←nat.mul_perm0, nat.mul_irr]
      rw [combine_list_product]
      apply mul_sorted_list_products
      exact a_no_zeros.right
      assumption
      exact a_no_zeros.left
    }
  termination_by mul_sorted_list_products => (alist, blist)

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

theorem concat_sorted_preserves_all {{ α: Type _ }} [Compare α] {{ P: α -> Prop }} {{alist blist: List α}} :
  (List.allP alist P) -> (List.allP blist P) -> (List.allP (alist.concat_sorted blist) P) := by
  intro all_a all_b
  
  match alist, blist with
  | [], _ => simp; assumption
  | _, [] =>
    rw [list_concat_sorted_empty]
    assumption
  | a :: as, b :: bs =>
    simp
    cases h:Compare.ord a b <;> simp
    repeat any_goals apply And.intro
    exact all_b.left
    {
      apply concat_sorted_preserves_all
      assumption
      exact all_b.right  
    }
    exact all_a.left
    exact all_b.left
    {
      apply concat_sorted_preserves_all
      exact all_a.right
      exact all_b.right
    }
    exact all_a.left
    {
      apply concat_sorted_preserves_all
      exact all_a.right
      exact all_b
    }
  termination_by concat_sorted_preserves_all => (alist, blist)

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
    apply PrimeFactorization.PrimeFactors (a_products.concat_sorted b_products)

    apply concat_sorted_preserves_all <;> assumption
    apply concat_sorted_keeps_sorted <;> assumption
    {
      rw [a_product, b_product]
      apply mul_sorted_list_products
      exact all_implies a_products a_primes nat.prime_gt_zero
      exact all_implies b_products b_primes nat.prime_gt_zero
    }

def nat.factorize (n: nat) (_: nat.zero < n) : PrimeFactorization n := by
  match n with
  | nat.inc nat.zero => 
    apply PrimeFactorization.PrimeFactors []
    all_goals trivial
  | nat.inc (nat.inc n₀) => 
    match n₀.inc.inc.classify_prime with
    | .Prime p _ => 
      apply PrimeFactorization.PrimeFactors [n₀.inc.inc]
      simp
      assumption
      simp
      simp
      rw [nat.mul_one_r]
    | .Composite _ composite =>
      
      match n₀.inc.inc.get_factors rfl composite with
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
    assumption
  }

theorem list_product_eq_zero : list_product as = nat.zero -> as.anyP (λ a => a = nat.zero) := by
  intro prod
  match as with
  | [] => simp at prod
  | a::as' =>
    simp at prod
    match nat.mul_eq_zero _ _ prod with
    | .inl prf =>
      exact Or.inl prf
    | .inr prf =>
      apply Or.inr
      apply list_product_eq_zero prf

theorem list_product_eq_one : list_product as = nat.zero.inc -> as.allP (λ a => a = nat.zero.inc) := by
  intro prod
  match as with
  | [] => simp
  | a::as' =>
    simp
    simp at prod
    have ⟨ q, r ⟩ := nat.mul_eq_one _ _ prod
    apply And.intro
    exact q
    apply list_product_eq_one
    exact r

theorem primes_gt_one {{a:nat}}{{as: List nat}} (all_primes: (a::as).allP nat.prime) : nat.zero.inc < list_product (a::as) := by
  match h:(list_product (a::as)) with
  | .zero =>
    have some_zero := list_product_eq_zero h
    have not_zero := List.mapAllP all_primes (by
      intro x xprime
      match Compare.dec_eq x nat.zero with
      | .isTrue x_one => rw [x_one] at xprime; contradiction
      | .isFalse not_one => exact not_one)
    have := List.any_and_not_all not_zero some_zero
    contradiction
  | .inc .zero => 
    have all_ones := list_product_eq_one h
    have no_ones := List.mapAllP all_primes (by
      intro x xprime
      match Compare.dec_eq x nat.zero.inc with
      | .isTrue x_one => rw [x_one] at xprime; contradiction
      | .isFalse not_one => exact not_one)
    have := List.all_and_not_all no_ones all_ones
    contradiction
  | .inc (.inc x₀) =>
    rw [nat.lt_inc_irr]
    exact nat.zero_lt_inc _

theorem sorted_def [Compare α] {{ a: α }} (as_sorted: (a :: as).sorted) : as.allP (fun x => x <= a) := by
  match as with
  | [] => trivial
  | a'::as' =>
    apply And.intro
    exact as_sorted.left
    have := sorted_def as_sorted.right
    exact List.mapAllP this (by
      intro x x_le_a'
      exact Compare.le_trans x_le_a' as_sorted.left)

def apply_all {{as: List α}} (all: List.allP as P) (a: α) (c: contains as a) : P a := by
  match as with
  | [] => contradiction
  | x :: xs =>
    match c with
    | .inl a_eq_x =>
      rw [a_eq_x]
      exact all.left
    | .inr xs_contains =>
      apply apply_all all.right a xs_contains

@[simp]
def PrimeFactorization.factors (f: PrimeFactorization n) : List nat := match f with
  | .PrimeFactors factors _ _ _ => factors

theorem all_factors_dvd (f: PrimeFactorization n) : f.factors.allP (λ x => dvd n x) := by
  have .PrimeFactors factors fprimes fsorted fdef := f
  match factors with
  | [] => trivial
  | f::fs =>
    apply And.intro
    exists (list_product fs)
    have := all_factors_dvd (.PrimeFactors fs fprimes.right (pop_sorted fsorted) (by rfl))
    simp at this
    apply List.mapAllP this
    intro x xf
    have ⟨ xf, prf ⟩ := xf
    simp
    exists (nat.mul f xf)
    rw [nat.mul_perm0, nat.mul_comm x, ← nat.mul_perm0, ←prf]
    exact fdef

theorem PrimeFactorization.of_prime (f: PrimeFactorization n) (nprime: n.prime) : f.factors = [n] := by
  match f with
  | .PrimeFactors nfactors nprimes nsorted ndef =>
  simp
  match nfactors with
  | [] =>
    simp at ndef
    have := nat.prime_ne_one nprime
    contradiction
  | [n₀] =>
    simp
    simp at ndef
    rw [nat.mul_one_r] at ndef
    rw [ndef]
  | a::b::fs =>
    simp
    simp at ndef
    match (nprime a).left with
    | .inl not_dvd_na =>
      apply not_dvd_na
      exists (nat.mul b (list_product fs))
    | .inr (.inl _) =>
      have := nat.prime_ne_one nprimes.left
      contradiction
    | .inr (.inr n_eq_a) =>
    rw [n_eq_a] at ndef
    conv at ndef => {
      lhs
      rw [←nat.mul_one_r a]
    }
    rw [nat.mul_irr] at ndef
    {
      have ⟨ b_eq_one, _ ⟩:= nat.mul_eq_one _ _ (Eq.symm ndef)
      have := nat.prime_ne_one nprimes.right.left
      contradiction
    }
    exact nat.prime_gt_zero nprimes.left

theorem PrimeFactorization.is_complete_inv (f: PrimeFactorization n) :
  ∀p:nat, ¬dvd n p -> ¬contains f.factors p := by
    intro p not_dvd fcontains
    have := all_factors_dvd f
    have _ := apply_all this p fcontains
    contradiction

theorem not_contains_pop : ¬ contains (x :: xs) y -> ¬ contains xs y := by 
  intro not_contains_xxs_y contains_xs_y
  apply not_contains_xxs_y
  apply Or.inr
  assumption

theorem not_contains_pop2 : ¬ contains (x :: xs) y -> x ≠ y ∧ ¬contains xs y := by 
  intro not_contains_xxs_y
  apply And.intro
  {
    intro x_eq_y
    have : contains (x :: xs) x := by simp
    rw [←x_eq_y] at not_contains_xxs_y
    contradiction
  }
  intro contains_xs_y
  apply not_contains_xxs_y
  apply Or.inr
  assumption

theorem force_contains [Compare α] {{alist blist: List α}} (anot: ¬ contains alist x)  (bnot: ¬ contains blist x) : ¬ contains (alist.concat_sorted blist) x := by
  match alist, blist with
  | [], _ =>
    simp
    assumption
  | _, [] =>
    rw [concat_sorted_empty_right]
    assumption
  | a::as, b::bs =>
    simp
    cases h:Compare.ord a b <;> simp
    {
      intro cond
      match cond with
      | .inl x_eq_b =>
        rw [x_eq_b] at bnot
        apply bnot; simp
      | .inr cond =>
        exact force_contains anot (not_contains_pop bnot) cond
    }
    {
      intro cond
      match cond with
      | .inl x_eq_a =>
        rw [x_eq_a] at anot
        apply anot; simp
      | .inr (.inl x_eq_b) =>
        rw [x_eq_b] at bnot
        apply bnot; simp
      | .inr (.inr cond) =>
        exact force_contains (not_contains_pop anot) (not_contains_pop bnot) cond
    }
    {
      intro cond
      match cond with
      | .inl x_eq_a =>
        rw [x_eq_a] at anot
        apply anot; simp
      | .inr cond =>
        exact force_contains (not_contains_pop anot) bnot cond
    }
  termination_by force_contains => (alist, blist)

theorem nat.distribute_terms :
  nat.mul (nat.add c (nat.mul b a)) (nat.add e (nat.mul d a)) =
  nat.add
  (nat.mul (nat.add (nat.mul b (nat.mul a d))
                    (nat.add (nat.mul d c) (nat.mul b e)))
           a)
  (nat.mul c e) := by
  conv => {
    lhs
    rw [nat.mul_add]
    rw [nat.add_mul]
    rw [nat.add_mul]
  }
  conv => {
    rhs
    rw [nat.add_mul]
    rw [nat.add_mul]
    rw [nat.add_comm]
  }
  rw [←nat.add_perm0]
  rw [nat.add_irr]
  conv => {
    rhs
    rw [nat.add_perm9]
    conv => {
      rhs 
      rw [nat.add_comm]
      lhs
      rw [←nat.mul_perm2]
    }
    lhs
    rw [←nat.mul_perm0,nat.mul_perm1]
  }
  rw [nat.add_irr]
  rw [nat.add_irr]
  conv => {
    rhs
    rw [nat.mul_comm]
    rw [nat.mul_perm0]
    rw [nat.mul_comm a]
    rw [nat.mul_comm a]
  }

theorem PrimeFactorization.is_complete (f: PrimeFactorization n) :
  ∀p:nat, p.prime -> dvd n p -> contains f.factors p := by
  match f with
  | .PrimeFactors nfactors nprimes nsorted ndef =>
  intro p pprime pdvd
  match nfactors with
  | [] => 
    simp at ndef
    rw [ndef] at pdvd
    have p_le_one := pdvd.is_le (nat.zero_lt_inc _)
    have p_gt_one := nat.prime_gt_one pprime
    have := Compare.not_lt_and_le _ _ p_gt_one p_le_one
    contradiction
  | [x] =>
    simp
    simp at ndef
    rw [nat.mul_one_r] at ndef
    rw [ndef] at pdvd
    have xprime := nprimes.left
    match (xprime p).left with
    | .inl _ => contradiction
    | .inr (.inl _) =>
      have := nat.prime_ne_one pprime
      contradiction
    | .inr (.inr x_eq_p) => rw [x_eq_p]
  | x::xs =>
    simp
    match Compare.dec_eq x p with
    | .isTrue x_eq_p =>
      rw [x_eq_p]
      apply Or.inl
      rfl
    | .isFalse x_ne_p =>
    apply Or.inr
    have xs_complete := (PrimeFactorization.PrimeFactors xs nprimes.right (pop_sorted nsorted) (by rfl)).is_complete
    apply xs_complete p pprime
    clear xs_complete
    rw [ndef] at pdvd
    
    have xprime := nprimes.left
    exact dvd.prime.cancel_left xprime pprime x_ne_p pdvd

#print axioms PrimeFactorization.is_complete

theorem PrimeFactorization.unique (a b: PrimeFactorization n) : a = b := by
  match a with
  | .PrimeFactors afactors aprimes asorted adef =>
  match b with
  | .PrimeFactors bfactors bprimes bsorted bdef =>
  simp
  match afactors, bfactors with
  | [], [] => rfl
  | [], b::bs =>
    have bprime := bprimes.left
    have := primes_gt_one bprimes
    simp at adef
    rw [adef] at bdef
    rw [bdef] at this
    have := nat.not_lt_id _ this
    contradiction
  | a::as, [] =>
    have := primes_gt_one aprimes
    simp at bdef
    rw [bdef] at adef
    rw [adef] at this
    have := nat.not_lt_id _ this
    contradiction
  | a::as, b::bs =>
    simp
    have a_eq_b : a = b := by
      have asorted_def := sorted_def asorted
      have bsorted_def := sorted_def bsorted
      have aprime := aprimes.left
      have bprime := bprimes.left
      admit
    apply And.intro
    exact a_eq_b
    simp at adef
    have := PrimeFactorization.unique (
      .PrimeFactors as aprimes.right (pop_sorted asorted) (by rfl)
    ) (
      .PrimeFactors bs bprimes.right (pop_sorted bsorted) (by 
        rw [adef] at bdef
        simp at bdef
        rw [a_eq_b] at bdef
        rw [nat.mul_irr] at bdef
        assumption
        match b with
        | .zero => 
          have := bprimes.left
          contradiction
        | .inc b₀ =>
          apply nat.zero_lt_inc
      )
    )
    simp at this
    exact this

#print axioms PrimeFactorization.unique