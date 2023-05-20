import Root2.SortedList

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
  try {
    apply Nat.add_lt_add <;> apply Nat.lt_succ_self
  }
}

#print axioms List.concat_sorted

@[simp]
def concat_sorted.induction [Compare α]
  {P: List α -> List α -> Prop}
  (empty_left: ∀ bs, P [] bs)
  (empty_right: ∀ a as, P (a::as) [])
  (induct_lt: ∀a b as bs, a < b -> P (a::as) bs -> P (a::as) (b::bs))
  (induct_eq: ∀a b as bs, a = b -> P as bs -> P (a::as) (b::bs))
  (induct_gt: ∀a b as bs, a > b -> P as (b::bs) -> P (a::as) (b::bs)):
  ∀ as bs, P as bs := fun as bs =>
  match as with
| [] => empty_left bs
| a::as => match bs with
| [] => empty_right a as
| b::bs => match h:Compare.ord a b with
| .Eq =>
  induct_eq a b as bs (Compare.ord_implies_eq h) (concat_sorted.induction empty_left empty_right induct_lt induct_eq induct_gt as bs)
| .Less =>
  induct_lt a b as bs h (concat_sorted.induction empty_left empty_right induct_lt induct_eq induct_gt (a::as) bs)
| .Greater =>
  induct_gt a b as bs (Compare.flip h) (concat_sorted.induction empty_left empty_right induct_lt induct_eq induct_gt as (b::bs))
termination_by concat_sorted.induction a b => a.length + b.length
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

#print axioms concat_sorted.induction

theorem concat_sorted.empty_left [Compare α] {{as: List α}} : List.concat_sorted as [] = as := by
  cases as <;> simp

#print axioms concat_sorted.empty_left

theorem concat_sorted.empty_right [Compare α] {{as: List α}} : List.concat_sorted [] as = as := by
  cases as <;> simp

#print axioms concat_sorted.empty_right

theorem concat_sorted.singleton_list_is_sorted [Compare α] {a: α} : [a].sorted := by simp

#print axioms concat_sorted.singleton_list_is_sorted

theorem concat_sorted.take_fst [Compare α] {{ a b : α }} (b_lt_a: b < a) :
  a :: (List.concat_sorted as (b::bs)) = List.concat_sorted (a::as) (b::bs) := by
  simp
  have : Compare.ord a b = Order.Greater := Compare.flip b_lt_a
  rw [this]

#print axioms concat_sorted.take_fst

theorem concat_sorted.take_snd [Compare α] {{ a b : α }} (a_lt_b: a < b) :
  b :: (List.concat_sorted (a::as) bs) = List.concat_sorted (a::as) (b::bs)  := by
  simp
  rw [a_lt_b]

#print axioms concat_sorted.take_snd

theorem concat_sorted.list_sorted_fst_snd_empty [Compare α] {{ a : α }} (aas_sorted : (a :: as).sorted) :
  List.sorted (a :: List.concat_sorted as []) := by
  rw [empty_left]
  assumption

#print axioms concat_sorted.list_sorted_fst_snd_empty

theorem concat_sorted.list_sorted_snd_fst_empty [Compare α] {{ a : α }} (bbs_sorted : (a :: as).sorted) :
  List.sorted (a :: List.concat_sorted [] as) := by
  rw [empty_right]
  assumption

#print axioms concat_sorted.list_sorted_snd_fst_empty

theorem concat_sorted.list_sorted_nonempty [Compare α] {{ a b: α }} (as bs : List α)
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

#print axioms concat_sorted.list_sorted_nonempty

theorem concat_sorted.nonempty_left [Compare α] {{ a b: α }} (as bs : List α)
    (aas: (a::as).sorted) (bbs : (b::bs).sorted) (b_le_a: b <= a):
    List.sorted (a::List.concat_sorted as (b::bs)) := (list_sorted_nonempty  as bs aas bbs).left b_le_a

#print axioms concat_sorted.nonempty_left

theorem concat_sorted.nonempty_right [Compare α] {{ a b: α }} (as bs : List α)
    (aas: (a::as).sorted) (bbs : (b::bs).sorted)
    (a_le_b: a <= b) : List.sorted (b::List.concat_sorted (a::as) bs) := (list_sorted_nonempty  as bs aas bbs).right a_le_b

#print axioms concat_sorted.nonempty_right

theorem concat_sorted.comm 
  [Compare α]
  {{alist blist: List α}}
  (a_sorted: alist.sorted) (b_sorted: blist.sorted)
  : alist.concat_sorted blist = blist.concat_sorted alist := by
  unfold List.concat_sorted
  match alist, blist with
  | [], x => simp; cases x <;> rfl
  | x, [] => simp; cases x <;> rfl
  | a::as, b::bs => 
    simp
    cases h:Compare.ord a b <;> simp
    {
      rw [Compare.flip h]
      simp
      apply concat_sorted.comm
      assumption
      apply sorted.pop; assumption
    }
    {
      rw [Compare.flip h]; simp
      have : a = b := Compare.ord_implies_eq h
      apply And.intro
      assumption
      apply And.intro
      exact this.symm
      apply concat_sorted.comm <;> (apply sorted.pop; assumption)
    }
    {
      rw [Compare.flip h]; simp
      apply concat_sorted.comm
      apply sorted.pop; assumption
      assumption
    }
termination_by concat_sorted.comm => alist.length + blist.length
decreasing_by {
  simp_wf
  
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
  try {
    apply Nat.add_lt_add <;> (apply Nat.lt_succ_self)
  }
}

#print axioms concat_sorted.comm

theorem concat_sorted.keeps_sorted
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
    split
    assumption
    next a' ns list_a_eq => {
      match ns with 
      | _ :: _ => simp at list_a_eq
      | [] => 
      simp at list_a_eq
      rw [←list_a_eq,empty_left, empty_left, empty_right]
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
      apply nonempty_right
      assumption
      assumption
      exact Or.inl h
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
        apply nonempty_right
        exact a_sorted.right
        assumption
        have a_eq_b := Compare.ord_implies_eq h
        rw [←a_eq_b]
        exact a_sorted.left
    }
    {
      apply nonempty_left
      assumption
      assumption
      apply Or.inl
      apply Compare.of_flip
      assumption
    }

#print axioms concat_sorted.keeps_sorted

theorem concat_sorted.all [Compare α] {{P : α -> Prop}} :
  ∀{{alist blist: List α}},
  (alist.allP P) -> (blist.allP P) ->
  (alist.concat_sorted blist).allP P := by
  apply concat_sorted.induction
  {
    intro bs _ all_bs
    rw [empty_right]
    exact all_bs
  }
  {
    intro a as all_as _
    rw [empty_left]
    exact all_as
  }
  {
    intro a b as bs a_lt_b prev all_as all_bs
    unfold List.concat_sorted
    simp only
    rw [a_lt_b]
    simp
    apply And.intro
    exact all_bs.left
    exact prev all_as all_bs.right
  }
  {
    intro a b as bs a_eq_b prev all_as all_bs
    rw [a_eq_b]
    simp
    rw [Compare.ord_id]
    simp
    apply And.intro
    exact all_bs.left
    apply And.intro
    exact all_bs.left
    exact prev all_as.right all_bs.right
  }
  {
    intro a b as bs a_gt_b prev all_as all_bs
    unfold List.concat_sorted
    simp
    rw [Compare.flip a_gt_b]
    simp
    apply And.intro
    exact all_as.left
    exact prev all_as.right all_bs
  }

#print axioms concat_sorted.all 

theorem concat_sorted.any [Compare α] {{P : α -> Prop}} :
  ∀{{alist blist: List α}},
  (alist.anyP P) ∨ (blist.anyP P) ->
  (alist.concat_sorted blist).anyP P := by
  apply concat_sorted.induction
  {
    intro bs any_as_or_bs
    rw [empty_right]
    simp at any_as_or_bs
    exact any_as_or_bs
  }
  {
    intro a as any_as_or_bs
    rw [empty_left]
    simp at any_as_or_bs
    exact any_as_or_bs
  }
  {
    intro a b as bs a_lt_b prev any_as_or_bs
    unfold List.concat_sorted
    simp only
    rw [a_lt_b]
    simp
    exact match any_as_or_bs with 
    | .inl any_as => Or.inr (prev (Or.inl any_as))
    | .inr (.inl pb) => Or.inl pb
    | .inr (.inr any_bs) => Or.inr (prev (Or.inr any_bs))
  }
  {
    intro a b as bs a_eq_b prev any_as_or_bs
    simp
    rw [Compare.ord_from_eq a_eq_b]
    simp
    exact match any_as_or_bs with 
    | .inl (.inl pa) => Or.inl pa
    | .inl (.inr any_as) => Or.inr (Or.inr (prev (Or.inl any_as)))
    | .inr (.inl pb) => Or.inr (Or.inl pb)
    | .inr (.inr any_bs) => Or.inr (Or.inr (prev (Or.inr any_bs)))
  }
  {
    intro a b as bs a_gt_b prev any_as_or_bs
    unfold List.concat_sorted
    simp
    rw [Compare.flip a_gt_b]
    simp
    exact match any_as_or_bs with 
    | .inl (.inl pa) => Or.inl pa
    | .inl (.inr any_as) => Or.inr (prev (Or.inl any_as))
    | .inr any_bs => Or.inr (prev (Or.inr any_bs))
  }

#print axioms concat_sorted.any