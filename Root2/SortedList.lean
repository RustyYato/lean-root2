import Root2.Cmp

@[simp]
def contains (as: List α) (a: α) : Prop := match as with
  | [] => False
  | x :: xs => a = x ∨ contains xs a

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
termination_by List.concat_sorted a b => a.length + b.length
decreasing_by {
  simp_wf
  try {
    rw [Nat.add_succ, Nat.add_comm (Nat.succ _), Nat.add_succ, Nat.add_comm]
    next ys => {
      generalize length xs + length ys = l
      exact Nat.lt_trans (Nat.lt_succ_self l) (Nat.lt_succ_self (Nat.succ l))
    }
  }
  try {
    rw [Nat.add_succ]
    rw [Nat.add_comm (Nat.succ _), Nat.add_succ]
    apply Nat.succ_lt_succ
    apply Nat.lt_succ_self
  }
  try {
    rw [Nat.add_succ]
    rw [Nat.add_comm (Nat.succ _), Nat.add_succ]
    apply Nat.succ_lt_succ
    rw [Nat.add_comm (Nat.succ _), Nat.add_succ]
    apply Nat.lt_succ_self
  }
}

@[simp]
def List.concat_sorted.induction [Compare α]
  {P: List α -> List α -> Prop}
  (empty_left: ∀ bs, P [] bs)
  (empty_right: ∀ a as, P (a::as) [])
  (induct_lt: ∀a b as bs, P (a::as) bs -> P (a::as) (b::bs))
  (induct_eq: ∀a b as bs, P as bs -> P (a::as) (b::bs))
  (induct_gt: ∀a b as bs, P as (b::bs) -> P (a::as) (b::bs)):
  ∀ as bs, P as bs := fun as bs =>
  match as with
| [] => empty_left bs
| a::as => match bs with
| [] => empty_right a as
| b::bs => match Compare.ord a b with
| .Eq =>
  induct_eq a b as bs (List.concat_sorted.induction empty_left empty_right induct_lt induct_eq induct_gt as bs)
| .Less =>
  induct_lt a b as bs (List.concat_sorted.induction empty_left empty_right induct_lt induct_eq induct_gt (a::as) bs)
| .Greater =>
  induct_gt a b as bs (List.concat_sorted.induction empty_left empty_right induct_lt induct_eq induct_gt as (b::bs))
termination_by List.concat_sorted.induction a b => a.length + b.length
decreasing_by {
  simp_wf
  try {
    apply Nat.add_lt_add <;> (apply Nat.lt_succ_self)
    done
  }
  try {
    apply Nat.add_lt_add_left
    apply Nat.lt_succ_self
  }
  try {
    apply Nat.add_lt_add_right
    apply Nat.lt_succ_self
  }
}

section concat_sorted
  theorem empty_left [Compare α] {{as: List α}} : List.concat_sorted as [] = as := by
    cases as <;> simp

  theorem empty_right [Compare α] {{as: List α}} : List.concat_sorted [] as = as := by
    cases as <;> simp

  theorem pop [Compare α] {{a: α}} {{as: List α}} : (a::as).sorted -> as.sorted := by
    intro list_sorted
    match as with
    | [] => trivial
    | a₀::as₀ => exact list_sorted.right

  theorem singleton_list_is_sorted [Compare α] {a: α} : [a].sorted := by simp

  theorem take_fst [Compare α] {{ a b : α }} (b_lt_a: b < a) :
    a :: (List.concat_sorted as (b::bs)) = List.concat_sorted (a::as) (b::bs) := by
    simp
    have : Compare.ord a b = Order.Greater := Compare.flip b_lt_a
    rw [this]

  theorem take_snd [Compare α] {{ a b : α }} (a_lt_b: a < b) :
    b :: (List.concat_sorted (a::as) bs) = List.concat_sorted (a::as) (b::bs)  := by
    simp
    rw [a_lt_b]

  theorem list_sorted_fst_snd_empty [Compare α] {{ a : α }} (aas_sorted : (a :: as).sorted) :
    List.sorted (a :: List.concat_sorted as []) := by
    rw [empty_left]
    assumption

  theorem list_sorted_snd_fst_empty [Compare α] {{ a : α }} (bbs_sorted : (a :: as).sorted) :
    List.sorted (a :: List.concat_sorted [] as) := by
    rw [empty_right]
    assumption

  theorem list_sorted_nonempty [Compare α] {{ a b: α }} (as bs : List α)
      (aas: (a::as).sorted) (bbs : (b::bs).sorted)
    :
      (b <= a -> List.sorted (a::List.concat_sorted as (b::bs)))
      ∧ 
      (a <= b -> List.sorted (b::List.concat_sorted (a::as) bs)) := by
      match as with
      | [] =>
        rw [empty_right]
        apply And.intro
        {
          intro b_le_a
          apply And.intro
          assumption
          assumption
        }
        {
          intro a_le_b
          match bs with
          | [] =>
            rw [empty_left]
            apply And.intro <;>
            assumption
          | b'::bs' =>
            have :  List.length bs' < Nat.succ (List.length bs') := Nat.lt_succ_self _
            have ⟨ _, right ⟩  := @list_sorted_nonempty α _ a b' [] bs' aas bbs.right
            unfold List.concat_sorted
            simp only
            cases h:Compare.ord a b' <;> simp
            apply And.intro
            exact bbs.left
            exact right (Or.inl h)
            apply And.intro
            exact a_le_b
            apply And.intro
            exact (Or.inr (Compare.flip h))
            exact bbs.right
            apply And.intro
            exact a_le_b
            apply And.intro
            exact (Or.inl (Compare.flip h))
            exact bbs.right
        }
      | a'::as' => 
        match bs with
        | [] =>
          rw [empty_left]
          apply And.intro
          {
            intro b_le_a
            unfold List.concat_sorted
            simp only
            cases h:Compare.ord a' b <;> simp
            apply And.intro
            exact b_le_a
            apply And.intro
            exact Or.inl h
            exact aas.right
            apply And.intro
            exact aas.left
            apply And.intro
            exact (Or.inr (Compare.flip h))
            rw [empty_left]
            have : a' = b := Compare.ord_implies_eq h 
            rw [← this]
            exact aas.right
            apply And.intro
            exact aas.left
            have : List.length as' < List.length as' + 1 := Nat.lt_succ_self _
            have ⟨ left, _ ⟩  := @list_sorted_nonempty α _ a' b as' [] aas.right bbs
            exact left (Or.inl (Compare.flip h))
          }
          {
            intro a_le_b
            apply And.intro
            exact a_le_b
            exact aas
          }
        | b'::bs' =>
          simp only
          apply And.intro
          {
            unfold List.concat_sorted
            intro b_le_a
            simp only
            cases h₀:Compare.ord a' b
            {
              apply And.intro
              exact b_le_a
              have : List.length as' + Nat.succ (List.length bs') < Nat.succ (List.length as') + Nat.succ (List.length bs') := by
                apply Nat.add_lt_add_right
                apply Nat.lt_succ_self
              have ⟨ _, right ⟩  := @list_sorted_nonempty α _ a' b as' (b'::bs') aas.right bbs
              exact right (Or.inl h₀)
            }
            {
              apply And.intro
              exact aas.left
              apply And.intro
              exact Or.inr (Compare.flip h₀)
              match as' with
              | [] =>
                rw [empty_right]
                exact bbs
              | a''::as'' =>
                have : List.length as'' + Nat.succ (List.length bs') < Nat.succ (Nat.succ (List.length as'')) + Nat.succ (List.length bs') := by
                  apply Nat.add_lt_add_right
                  apply Nat.lt_trans (Nat.lt_succ_self _)
                  apply Nat.lt_succ_self
                have ⟨ _, right ⟩  := @list_sorted_nonempty α _ a'' b as'' (b'::bs') aas.right.right bbs
                apply right
                have : a' = b := Compare.ord_implies_eq h₀
                rw [←this]
                exact aas.right.left
            }
            {
              apply And.intro
              exact aas.left
              have : List.length as' + Nat.succ (List.length bs') < Nat.succ (List.length as') + Nat.succ (List.length bs') := by
                apply Nat.add_lt_add_right
                apply Nat.lt_succ_self
              have ⟨ left, _ ⟩  := @list_sorted_nonempty α _ a' b as' (b'::bs') aas.right bbs
              exact left (Or.inl (Compare.flip h₀))
            }
          }
          {
            unfold List.concat_sorted
            intro a_le_b
            simp only
            cases h₀:Compare.ord a b'
            {
              apply And.intro
              exact bbs.left
              have : Nat.succ (List.length as') + List.length bs' < Nat.succ (List.length as') + Nat.succ (List.length bs') := by
                apply Nat.add_lt_add_left
                apply Nat.lt_succ_self
              have ⟨ _, right ⟩  := @list_sorted_nonempty α _ a b' (a'::as') bs' aas bbs.right
              exact right (Or.inl h₀)
            }
            {
              apply And.intro
              exact a_le_b
              apply And.intro
              exact Or.inr (Compare.flip h₀)
              match bs' with
              | [] => 
                rw [empty_left]
                rw [←Compare.ord_implies_eq h₀]
                exact aas
              | b''::bs'' =>
                have : List.length as' + Nat.succ (List.length bs'') < Nat.succ (List.length as') + Nat.succ (Nat.succ (List.length bs'')) := by
                  apply Nat.add_lt_add <;>
                  apply Nat.lt_succ_self
                have ⟨ _, right ⟩  := @list_sorted_nonempty α _ a' b' as' (b''::bs'') aas.right bbs.right
                apply right
                have : a = b' := Compare.ord_implies_eq h₀
                rw [←this]
                exact aas.left
            }
            {
              apply And.intro
              exact a_le_b
              have : Nat.succ (List.length as') + List.length bs' < Nat.succ (List.length as') + Nat.succ (List.length bs') := by
                apply Nat.add_lt_add_left
                apply Nat.lt_succ_self
              have ⟨ left, _ ⟩  := @list_sorted_nonempty α _ a b' (a'::as') bs' aas bbs.right
              exact left (Or.inl (Compare.flip h₀))
            }
          }
    termination_by _ => as.length + bs.length
    decreasing_by {
      simp_wf
      try { assumption }
      try { admit }
    }
  
  theorem list_sorted_nonempty_left [Compare α] {{ a b: α }} (as bs : List α)
      (aas: (a::as).sorted) (bbs : (b::bs).sorted) (b_le_a: b <= a):
      List.sorted (a::List.concat_sorted as (b::bs)) := (list_sorted_nonempty  as bs aas bbs).left b_le_a

  theorem list_sorted_nonempty_right [Compare α] {{ a b: α }} (as bs : List α)
      (aas: (a::as).sorted) (bbs : (b::bs).sorted)
      (a_le_b: a <= b) : List.sorted (b::List.concat_sorted (a::as) bs) := (list_sorted_nonempty  as bs aas bbs).right a_le_b

end concat_sorted