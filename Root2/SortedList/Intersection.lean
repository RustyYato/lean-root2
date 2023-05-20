import Root2.SortedList


def List.intersect_sorted [Compare α] (a b: List α) : List α := match a with
| [] => []
| a₀::as => match b with
| [] => []
| b₀::bs => match Compare.ord a₀ b₀ with
| .Eq => 
  have : length as + length bs < Nat.succ (length as) + Nat.succ (length bs) := by
    apply Nat.add_lt_add <;> apply Nat.lt_succ_self
  a₀ :: as.intersect_sorted bs
| .Less =>
  have : Nat.succ (length as) + length bs < Nat.succ (length as) + Nat.succ (length bs) := by
    apply Nat.add_lt_add_left; apply Nat.lt_succ_self
  (a₀::as).intersect_sorted bs
| .Greater =>
  have : length as + Nat.succ (length bs) < Nat.succ (length as) + Nat.succ (length bs) := by
    apply Nat.add_lt_add_right; apply Nat.lt_succ_self
  as.intersect_sorted (b₀::bs)
termination_by _ => a.length + b.length
decreasing_by {
  simp_wf
  assumption
}

@[simp]
def intersect_sorted.induction [Compare α]
  {P: List α -> List α -> Prop}
  (empty_left: ∀ bs, P [] bs)
  (empty_right: ∀ a as, P (a::as) [])
  (induct_lt: ∀a b as bs, Compare.ord a b = Order.Less -> P (a::as) bs -> P (a::as) (b::bs))
  (induct_eq: ∀a b as bs, Compare.ord a b = Order.Eq -> P as bs -> P (a::as) (b::bs))
  (induct_gt: ∀a b as bs, Compare.ord a b = Order.Greater -> P as (b::bs) -> P (a::as) (b::bs)):
  ∀ as bs, P as bs := fun as bs =>
  match as with
| [] => empty_left bs
| a::as => match bs with
| [] => empty_right a as
| b::bs => match h:Compare.ord a b with
| .Eq =>
  have : as.length + bs.length < Nat.succ as.length + Nat.succ bs.length := by
    apply Nat.add_lt_add <;> apply Nat.lt_succ_self
  induct_eq a b as bs h (intersect_sorted.induction empty_left empty_right induct_lt induct_eq induct_gt as bs)
| .Less =>
  have : Nat.succ as.length + bs.length < Nat.succ as.length + Nat.succ bs.length := by
    apply Nat.add_lt_add_left; apply Nat.lt_succ_self
  induct_lt a b as bs h (intersect_sorted.induction empty_left empty_right induct_lt induct_eq induct_gt (a::as) bs)
| .Greater =>
  have : as.length + Nat.succ bs.length < Nat.succ as.length + Nat.succ bs.length := by
    apply Nat.add_lt_add_right; apply Nat.lt_succ_self
  induct_gt a b as bs h (intersect_sorted.induction empty_left empty_right induct_lt induct_eq induct_gt as (b::bs))
termination_by intersect_sorted.induction a b => a.length + b.length
decreasing_by {
  simp_wf
  assumption
}

#print axioms intersect_sorted.induction

theorem intersect_sorted.empty_left [Compare α] (xs: List α) : xs.intersect_sorted [] = [] := by 
  unfold List.intersect_sorted
  simp
  split <;> rfl

#print axioms intersect_sorted.empty_left

theorem intersect_sorted.empty_right [Compare α] (xs: List α) : [].intersect_sorted xs = [] := by 
  unfold List.intersect_sorted
  rfl

#print axioms intersect_sorted.empty_right

theorem intersect_sorted.eq_is_sorted_helper [Compare α]
  (x: α)
  (as: List α)
  (bs: List α)
  (asorted: (x::as).sorted)
  (bsorted: (x::bs).sorted)
  (isorted: (as.intersect_sorted bs).sorted) :
  (x::(as.intersect_sorted bs)).sorted := by
  match as, bs with
  | [], [] => simp
  | _::_, [] => simp
  | [], _::_ => simp
  | a::as', b::bs' => 
    unfold List.intersect_sorted at isorted
    simp only at isorted
    unfold List.intersect_sorted
    simp only
    cases h:Compare.ord a b <;> simp
    {
      rw [h] at isorted; simp at isorted
      have : Nat.succ (List.length as') + List.length bs' < Nat.succ (List.length as') + Nat.succ (List.length bs') := by
        apply Nat.add_lt_add_left; apply Nat.lt_succ_self
      apply intersect_sorted.eq_is_sorted_helper
      assumption
      exact sorted.pop_snd bsorted
      assumption
    }
    {
      rw [h] at isorted; simp at isorted
      apply And.intro
      exact asorted.left
      assumption
    }
    {
      rw [h] at isorted; simp at isorted
      have : List.length as' + Nat.succ (List.length bs') < Nat.succ (List.length as') + Nat.succ (List.length bs') := by
        apply Nat.add_lt_add_right; apply Nat.lt_succ_self
      apply intersect_sorted.eq_is_sorted_helper
      exact sorted.pop_snd asorted
      assumption
      assumption
    }
  termination_by _ => as.length + bs.length
  decreasing_by {
    simp_wf
    assumption
  }

#print axioms intersect_sorted.eq_is_sorted_helper

theorem intersect_sorted.keeps_sorted [Compare α]   :
  ∀ (alist blist: List α) (_: alist.sorted) (_: blist.sorted),
  (alist.intersect_sorted blist).sorted := by
  apply intersect_sorted.induction
  {
    intro bs _ _
    simp
    rw [empty_right bs]
    simp
  }
  {
    intro a as _ _
    simp
  }
  {
    intro a b as bs a_lt_b prev asorted bsorted
    unfold List.intersect_sorted
    simp only
    rw [a_lt_b]
    simp
    apply prev
    assumption
    exact sorted.pop bsorted
  }
  {
    intro a b as bs a_eq_b prev asorted bsorted
    unfold List.intersect_sorted
    simp only
    rw [a_eq_b]
    have a_eq_b := Compare.ord_implies_eq a_eq_b
    simp
    apply intersect_sorted.eq_is_sorted_helper
    assumption
    rw [a_eq_b]
    assumption
    apply prev
    exact sorted.pop asorted
    exact sorted.pop bsorted
  }
  {
    intro a b as bs a_gt_b prev asorted bsorted
    unfold List.intersect_sorted
    simp only
    rw [a_gt_b]
    simp
    apply prev
    exact sorted.pop asorted
    assumption
  }

#print axioms intersect_sorted.keeps_sorted

def sorted.contains_le [Compare α] 
  {x a: α} {as: List α} (asorted: (a::as).sorted)
  : contains (a::as) x -> x <= a := by
  intro con
  match con with
  | .inl x_eq_a =>
    rw [x_eq_a]; apply Compare.le_id
  | .inr con' =>
    match as with
    | a'::as' =>
    have := sorted.contains_le (sorted.pop asorted) con'
    exact Compare.le_trans this asorted.left

#print axioms sorted.contains_le

def sorted.not_contains [Compare α] 
  {x a: α} {as: List α} (asorted: (a::as).sorted)
  : a < x -> ¬ contains (a::as) x := by
  intro a_lt_x con
  have := sorted.contains_le asorted con
  exact @Compare.not_lt_and_le α _ _ _ a_lt_x this

#print axioms sorted.not_contains

def intersect_sorted.of_contains [Compare α] :
  ∀(alist blist: List α) (_: alist.sorted) (_: blist.sorted),
  ∀x, contains alist x -> contains blist x ->
  contains (alist.intersect_sorted blist) x := by
  apply intersect_sorted.induction
  {
    intro bs _ _ x acontains _
    contradiction
  }
  {
    intro a as _ _ x _ bcontains
    contradiction
  }
  {
    intro a b as bs a_lt_b prev asorted bsorted x acontains bcontains
    unfold List.intersect_sorted
    simp only
    rw [a_lt_b]
    simp
    match bcontains with
    | .inl h =>
      rw [h] at acontains
      have := sorted.not_contains asorted a_lt_b
      contradiction
    | .inr bcontains => 
      apply prev asorted (sorted.pop bsorted)
      assumption
      assumption
  }
  {
    intro a b as bs a_eq_b prev asorted bsorted x acontains bcontains
    unfold List.intersect_sorted
    simp only
    rw [a_eq_b]
    simp
    have a_eq_b : a = b := Compare.ord_implies_eq a_eq_b
    rw [←a_eq_b] at bcontains
    match acontains, bcontains with
    | .inl h, _ 
    | _, .inl h => apply Or.inl h
    | .inr acontains, .inr bcontains =>
      apply Or.inr
      apply prev
      exact sorted.pop asorted
      exact sorted.pop bsorted
      assumption
      assumption
  }
  {
    intro a b as bs a_gt_b prev asorted bsorted x acontains bcontains
    unfold List.intersect_sorted
    simp only
    rw [a_gt_b]
    simp
    match acontains with
    | .inl h =>
      rw [h] at bcontains
      have := sorted.not_contains bsorted (Compare.flip a_gt_b)
      contradiction
    | .inr bcontains => 
      apply prev (sorted.pop asorted) bsorted
      assumption
      assumption
  }

#print axioms intersect_sorted.of_contains

def intersect_sorted.to_contains [Compare α] :
  ∀(alist blist: List α) (_: alist.sorted) (_: blist.sorted),
  ∀x, contains (alist.intersect_sorted blist) x ->
  contains alist x ∧ contains blist x := by
  apply intersect_sorted.induction
  {
    intro bs _ _ x con 
    rw [empty_right] at con
    contradiction
  }
  {
    intro a as _ _ x con
    rw [empty_left] at con
    contradiction
  }
  {
    intro a b as bs a_lt_b prev asorted bsorted x con
    unfold List.intersect_sorted at con
    simp only at con
    rw [a_lt_b] at con
    simp at con
    have ⟨ acon, bcon ⟩ := prev asorted (sorted.pop bsorted) x con
    exact ⟨ acon, Or.inr bcon ⟩
  }
  {
    intro a b as bs a_eq_b prev asorted bsorted x con
    unfold List.intersect_sorted at con
    simp only at con
    rw [a_eq_b] at con
    simp at con
    match con with
    | .inl h =>
      rw [←Compare.ord_implies_eq a_eq_b]
      exact ⟨ Or.inl h, Or.inl h ⟩
    | .inr con =>
    have ⟨ acon, bcon ⟩ := prev (sorted.pop asorted) (sorted.pop bsorted) x con
    exact ⟨ Or.inr acon, Or.inr bcon ⟩
  }
  {
    intro a b as bs a_lt_b prev asorted bsorted x con
    unfold List.intersect_sorted at con
    simp only at con
    rw [a_lt_b] at con
    simp at con
    have ⟨ acon, bcon ⟩ := prev (sorted.pop asorted) bsorted x con
    exact ⟨ Or.inr acon, bcon ⟩
  }

#print axioms intersect_sorted.to_contains

def intersect_sorted.of_all [Compare α] {P : α -> Prop} :
  ∀(alist blist: List α),
  alist.allP P ∨ blist.allP P ->
  (alist.intersect_sorted blist).allP P := by
  apply intersect_sorted.induction
  {
    intro bs _
    rw [empty_right]
    exact True.intro
  }
  {
    intro a as _
    rw [empty_left]
    exact True.intro
  }
  {
    intro a b as bs a_lt_b prev alla_or_allb
    unfold List.intersect_sorted
    simp only; rw [a_lt_b]; simp
    apply prev
    match alla_or_allb with
    | .inl alla => exact Or.inl alla
    | .inr ⟨ _, allb ⟩ => exact Or.inr allb
  }
  {
    intro a b as bs a_eq_b prev alla_or_allb
    unfold List.intersect_sorted
    simp only; rw [a_eq_b]; simp
    have : a = b := Compare.ord_implies_eq  a_eq_b
    match alla_or_allb with
    | .inl ⟨ pa, alla ⟩ =>
      apply And.intro
      exact pa
      exact prev (Or.inl alla)
    | .inr ⟨ pb, allb ⟩ => 
      apply And.intro
      rw [this]
      exact pb
      exact prev (Or.inr allb)
  }
  {
    intro a b as bs a_gt_b prev alla_or_allb
    unfold List.intersect_sorted
    simp only; rw [a_gt_b]; simp
    apply prev
    match alla_or_allb with
    | .inl ⟨ _, alla ⟩  => exact Or.inl alla
    | .inr allb => exact Or.inr allb
  }

#print axioms intersect_sorted.of_all
