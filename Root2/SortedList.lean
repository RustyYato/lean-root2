import Root2.Cmp

@[simp]
def contains (as: List α) (a: α) : Prop := match as with
  | [] => False
  | x :: xs => a = x ∨ contains xs a

#print axioms List.contains

@[simp]
def List.allP  (list: List a) (P : a -> Prop) : Prop := match list with
  | [] => True
  | x :: xs => P x ∧ allP xs P

#print axioms List.allP

@[simp]
def List.anyP (list: List a) (P : a -> Prop) : Prop := match list with
  | [] => False
  | x :: xs => P x ∨ anyP xs P

#print axioms List.anyP

@[simp]
def List.mapAllP {{list: List a}} {{ P R: a -> Prop }} (all: list.allP P) (F: ∀a, P a -> R a) : list.allP R := by
  match list with
  | [] => trivial
  | x :: xs =>
    simp
    apply And.intro
    exact F x all.left
    exact List.mapAllP all.right F

#print axioms List.mapAllP

@[simp]
def List.mapAnyP {{list: List a}} {{ P R: a -> Prop }} (any: list.anyP P) (F: ∀a, P a -> R a) : list.anyP R := by
  match list with
  | [] => trivial
  | x :: xs =>
    simp
    match any with
    | .inl prf => exact .inl (F x prf)
    | .inr prf => exact .inr (List.mapAnyP prf F)

#print axioms List.mapAnyP

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

#print axioms List.any_and_not_all

@[simp]
def List.all_and_not_all {{list: List a}} {{ P: a -> Prop }} (not_all: list.allP fun x => ¬ P x) (all: list.allP P) : list = [] := by
  match list with
  | [] => rfl
  | x :: xs =>
    simp
    have not_p := not_all.left
    have p := all.left
    contradiction

#print axioms List.all_and_not_all

@[simp]
def List.sorted_by (list: List a) (P : a -> a -> Prop) : Prop := match list with
  | [] | [_] => True
  | a :: b :: xs => P a b ∧ sorted_by (b :: xs) P

#print axioms List.sorted_by

@[simp]
def List.sorted [Compare α] (list: List α) : Prop := match list with
  | [] | [_] => True
  | a :: b :: xs => b <= a ∧ sorted (b :: xs)

#print axioms List.sorted

theorem sorted.pop [Compare α] {{a: α}} {{as: List α}} : (a::as).sorted -> as.sorted := by
  intro list_sorted
  match as with
  | [] => trivial
  | a₀::as₀ => exact list_sorted.right

#print axioms sorted.pop

theorem sorted.pop_snd [Compare α] {{a: α}} {{as: List α}} : (a::a'::as).sorted -> (a::as).sorted := by
  intro list_sorted
  match as with
  | [] => trivial
  | a₀::as' =>
    apply And.intro
    apply Compare.le_trans list_sorted.right.left list_sorted.left
    exact list_sorted.right.right

#print axioms sorted.pop_snd
