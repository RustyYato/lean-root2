@[simp]
def List.sub_seq (a b: List α) := match a with
| [] => True
| a'::as' => match b with
  | [] => False
  | b'::bs' => (a' = b' ∧ sub_seq as' bs') ∨ sub_seq (a'::as') bs'

#print axioms List.sub_seq

theorem List.sub_seq.pop {a: α} {as bs: List α} : (a::as).sub_seq bs -> as.sub_seq bs := by
  intro ss
  unfold List.sub_seq at ss
  match bs with
  | b'::bs' =>
  simp at ss
  match as with
  | [] => trivial
  | a'::as' =>
  simp
  apply Or.inr
  match ss with
  | .inl ⟨ _, is_sub_seq ⟩ =>
    assumption
  | .inr h =>
    simp
    exact sub_seq.pop h

#print axioms List.sub_seq.pop

theorem List.sub_seq.id (as: List α) : as.sub_seq as := by
  unfold List.sub_seq
  match as with
  | [] =>
    simp only
  | a'::as' =>
  apply Or.inl
  apply And.intro
  exact rfl
  exact List.sub_seq.id _

#print axioms List.sub_seq.id

theorem List.sub_seq.tail {a: α} {as: List α} : as.sub_seq (a::as) := by
  unfold sub_seq
  match as with
  | [] => trivial
  | a'::as' =>
  apply Or.inr
  apply Or.inl
  apply And.intro
  rfl
  exact List.sub_seq.id _

#print axioms List.sub_seq.tail

instance sub_seq.dec [DecidableEq α] (a b : List α) : Decidable (a.sub_seq b) := match a with
  | [] => Decidable.isTrue (by simp)
  | a'::as' => match b with
    | [] => Decidable.isFalse False.elim
    | b'::bs' => match decEq a' b' with
      | .isTrue a_eq_b => match sub_seq.dec as' bs' with
        | .isTrue is_sub_seq => Decidable.isTrue (Or.inl ⟨ a_eq_b, is_sub_seq ⟩)
        | .isFalse not_sub_seq => Decidable.isFalse (by 
          simp
          intro  x
          match x with
          | .inl ⟨ _, _ ⟩ => contradiction
          | .inr h =>
            exact (not_sub_seq h.pop).elim
          )
      | .isFalse a_ne_b => match sub_seq.dec (a'::as') bs' with
        | .isTrue is_sub_seq => Decidable.isTrue (Or.inr is_sub_seq)
        | .isFalse not_sub_seq => Decidable.isFalse (by 
          simp
          intro x
          match x with
          | .inr _ => contradiction
          | .inl ⟨ _, _ ⟩ => contradiction)

#print axioms sub_seq.dec

example : [0, 2].sub_seq [0, 1, 2] := by decide
example : ¬[0, 1, 2].sub_seq [0, 2] := by decide

def List.sub_seq.empty {{ a: List α }} : a.sub_seq [] -> a = [] := by
  intro
  match a with
  | [] => rfl
  | _::_ => contradiction

#print axioms List.sub_seq.empty

def List.sub_seq.trans {a b c: List αs} : a.sub_seq b -> b.sub_seq c -> a.sub_seq c := by
  intro ab bc
  unfold List.sub_seq 
  match a with
  | [] => simp
  | a'::as' =>
    simp
    match c with
    | [] =>
      simp at bc
      rw [bc.empty] at ab
      contradiction
    | c'::cs' =>
      simp
      match b with
      | [] => contradiction
      | b'::bs' =>
      unfold List.sub_seq at ab bc
      simp at ab bc
      match ab, bc with
      | .inl ⟨ a_eq_b, ab ⟩ , .inl ⟨ b_eq_c, bc ⟩ =>
        apply Or.inl
        apply And.intro
        exact a_eq_b.trans b_eq_c
        exact ab.trans bc
      | .inl _, .inr bc =>
        apply Or.inr
        apply sub_seq.trans _ bc
        simp
        assumption
      | .inr ab, .inl ⟨ _, bc' ⟩ =>
        apply Or.inr
        apply sub_seq.trans ab
        simp
        assumption
      | .inr ab, .inr bc =>
        apply Or.inr
        exact ab.trans bc.pop

#print axioms List.sub_seq.trans
