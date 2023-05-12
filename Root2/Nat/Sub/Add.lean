import Root2.Nat.Add.Cmp
import Root2.Nat.Sub

-- (a - c) + (b - d) = (a + b) - (c + d)
theorem nat.add_sub_assoc (a b c: nat) : ∀ h₀ h₁ h₂, add (a.checked_sub c h₀) (b.checked_sub d h₁) = (add a b).checked_sub (add c d) h₂ := by
  intro _ _ _
  apply Eq.symm
  apply nat.add_to_sub
  rw [nat.add_perm0, nat.add_comm _ c, nat.add_perm0, nat.add_comm c]
  rw [nat.sub_add_inv]
  rw [nat.add_comm]
  rw [nat.add_perm4]
  rw [nat.sub_add_inv]
  rw [nat.add_comm]


-- (a - c) + (b - d) = (a + b) - (c + d)
theorem nat.sub_add_to_sub_sub_left (a b c: nat) :
  ∀ h₀ h₁ h₂, (a.checked_sub (add b c) h₀) = (a.checked_sub b h₁).checked_sub c h₂ := by
  intro _ _ _
  apply nat.add_to_sub
  rw [nat.add_perm0, nat.add_comm _ c, nat.add_perm0, nat.add_comm c]
  rw [nat.sub_add_inv]
  rw [nat.sub_add_inv]


-- (a - c) + (b - d) = (a + b) - (c + d)
theorem nat.sub_add_to_sub_sub_right (a b c: nat) :
  ∀ h₀ h₁ h₂, (a.checked_sub (add b c) h₀) = (a.checked_sub c h₁).checked_sub b h₂ := by
  intro _ _ _
  apply nat.add_to_sub
  rw [nat.add_comm b c]
  rw [nat.add_perm0, nat.add_comm _ b, nat.add_perm0, nat.add_comm b]
  rw [nat.sub_add_inv]
  rw [nat.sub_add_inv]

