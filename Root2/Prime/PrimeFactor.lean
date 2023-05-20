import Root2.Prime
import Root2.Prime.Factors
import Root2.Prime.Divisible
import Root2.SortedList.Concat

instance nat_gt_one {n: nat} : nat.zero.inc < nat.inc (nat.inc n) := by
  rw [nat.lt_inc_irr]
  apply nat.zero_lt_inc

@[simp]
def list_product (list: List nat) : nat := match list with
  | [] => nat.zero.inc
  | n :: ns => nat.mul n (list_product ns)

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
    rw [concat_sorted.empty_left]
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

    apply concat_sorted.all <;> assumption
    apply concat_sorted.keeps_sorted <;> assumption
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

def zero_composite : nat.composite nat.zero := ⟨ nat.zero.inc.inc, .inl (⟨ ⟨ .zero, rfl ⟩ , fun x => nat.noConfusion (nat.eq_inc_to_eq x), nat.noConfusion ⟩ ) ⟩ 
def one_composite : nat.composite nat.zero.inc := ⟨ nat.zero.inc.inc, .inr rfl ⟩ 

theorem primes_gt_one {{a:nat}}{{as: List nat}} (all_primes: (a::as).allP nat.prime) : nat.zero.inc < list_product (a::as) := by
  match h:(list_product (a::as)) with
  | .zero =>
    have some_zero := list_product_eq_zero h
    have not_zero : List.allP (a::as) (λx => x ≠ .zero) := List.mapAllP all_primes (by
      intro x xprime
      match Compare.dec_eq x nat.zero with
      | .isTrue x_zero => 
        rw [x_zero] at xprime
        exact (nat.prime_implies_not_composite xprime zero_composite).elim
      | .isFalse not_one => exact not_one
      )
    have := List.any_and_not_all not_zero some_zero
    contradiction
  | .inc .zero => 
    have all_ones := list_product_eq_one h
    have no_ones := List.mapAllP all_primes (by
      intro x xprime
      match Compare.dec_eq x nat.zero.inc with
      | .isTrue x_one =>  
        rw [x_one] at xprime
        exact (nat.prime_implies_not_composite xprime one_composite).elim
      | .isFalse not_one => exact not_one)
    have := List.all_and_not_all no_ones all_ones
    contradiction
  | .inc (.inc x₀) =>
    rw [nat.lt_inc_irr]
    exact nat.zero_lt_inc _

#print axioms primes_gt_one

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
    have := all_factors_dvd (.PrimeFactors fs fprimes.right (sorted.pop fsorted) (by rfl))
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
    rw [concat_sorted.empty_left]
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

theorem PrimeFactorization.is_complete_raw 
  {n}
  (nfactors: List nat) (nprimes: nfactors.allP nat.prime) (ndef: n = list_product nfactors)
 : ∀p:nat, p.prime -> dvd n p -> contains nfactors p := by
  intro p pprime pdvd
  match nfactors with
  | [] => 
    simp only at ndef
    rw [ndef] at pdvd
    have p_le_one := pdvd.is_le (nat.zero_lt_inc _)
    have p_gt_one := nat.prime_gt_one pprime
    have := Compare.not_lt_and_le _ _ p_gt_one p_le_one
    contradiction
  | [x] =>
    unfold contains
    apply Or.inl
    unfold list_product at ndef
    simp at ndef
    rw [nat.mul_one_r] at ndef
    rw [ndef] at pdvd
    have xprime := nprimes.left
    match (xprime p).left with
    | .inl _ => contradiction
    | .inr (.inl h) => 
      exact ((nat.prime_ne_one pprime) h).elim
    | .inr (.inr h) => exact h.symm
  | x::xs =>
    simp
    match Compare.dec_eq x p with
    | .isTrue x_eq_p =>
      rw [x_eq_p]
      apply Or.inl
      rfl
    | .isFalse x_ne_p =>
    apply Or.inr
    apply PrimeFactorization.is_complete_raw xs nprimes.right rfl p pprime
    rw [ndef] at pdvd
    have xprime := nprimes.left
    exact dvd.prime.cancel_left xprime pprime x_ne_p pdvd

theorem PrimeFactorization.is_complete (f: PrimeFactorization n) :
  ∀p:nat, p.prime -> dvd n p -> contains f.factors p := 
  match f with
  | .PrimeFactors nfactors nprimes _ ndef => PrimeFactorization.is_complete_raw 
    nfactors nprimes ndef

#print axioms PrimeFactorization.is_complete

def sorted_max [Compare α] {x:α} {xs: List α} (xsorted: (x::xs).sorted) : ∀y, contains (x::xs) y -> y <= x := by
  intro y xs_contains
  match xs_contains with
  | .inl y_eq_x => apply Or.inr (Compare.ord_from_eq y_eq_x)
  | .inr xs_contains =>
  match xs with
  | [] => contradiction
  | x'::xs' =>
    have y_le_x' := sorted_max (sorted.pop xsorted) y xs_contains
    apply Compare.le_trans y_le_x'
    exact xsorted.left

#print axioms sorted_max

def nat.biggest_prime_factor (f: PrimeFactorization n) : f.factors = x :: xs ->
  x.prime ∧ ∀y, y.prime -> dvd n y -> y <= x
  := by
    match f with
    | .PrimeFactors nfactors nprimes nsorted ndef =>
    intro factors
    simp at factors
    rw [factors] at nprimes nsorted ndef
    clear factors nfactors f
    apply And.intro
    exact nprimes.left
    intro y yprime ydvd
    have is_complete := PrimeFactorization.is_complete_raw (x::xs) nprimes ndef
    exact sorted_max nsorted y (is_complete y yprime ydvd)

#print axioms nat.biggest_prime_factor

theorem PrimeFactorization.unique_raw
  {n}
  (afactors: List nat) (aprimes: afactors.allP nat.prime) (asorted: afactors.sorted) (adef: n = list_product afactors)
  (bfactors: List nat) (bprimes: bfactors.allP nat.prime) (bsorted: bfactors.sorted) (bdef: n = list_product bfactors)
  : afactors = bfactors := by
  simp
  match afactors, bfactors with
  | [], [] => rfl
  | [], b::bs =>
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
      have aprime := aprimes.left
      have bprime := bprimes.left
      have ⟨ _, aprf ⟩  := nat.biggest_prime_factor (.PrimeFactors (a::as) aprimes asorted adef) rfl
      have ⟨ _, bprf ⟩  := nat.biggest_prime_factor (.PrimeFactors (b::bs) bprimes bsorted bdef) rfl
      have b_le_a := aprf b bprime (by exists list_product bs)
      have a_le_b := bprf a aprime (by exists list_product as)
      exact nat.le_le_to_eq a_le_b b_le_a
    apply And.intro
    exact a_eq_b
    simp at adef
    exact PrimeFactorization.unique_raw  as aprimes.right (sorted.pop asorted) rfl
        bs bprimes.right (sorted.pop bsorted) (by 
        rw [adef] at bdef
        simp at bdef
        rw [a_eq_b] at bdef
        rw [nat.mul_irr] at bdef
        assumption
        match b with
        | .zero => 
          have := bprimes.left
          exact (nat.prime_implies_not_composite this zero_composite).elim
        | .inc b₀ =>
          apply nat.zero_lt_inc
      )

#print axioms PrimeFactorization.unique_raw

theorem PrimeFactorization.unique (a b: PrimeFactorization n) : a = b := by
  match a with
  | .PrimeFactors afactors aprimes asorted adef =>
  match b with
  | .PrimeFactors bfactors bprimes bsorted bdef =>
  congr
  exact PrimeFactorization.unique_raw afactors aprimes asorted adef bfactors bprimes bsorted bdef

#print axioms PrimeFactorization.unique