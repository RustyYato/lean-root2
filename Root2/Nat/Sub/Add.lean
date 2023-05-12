import Root2.Nat.Add.Cmp
import Root2.Nat.Sub

-- (a - c) + (b - d) = (a + b) - (c + d)
theorem nat.add_sub_assoc (a b c: nat) : ∀ h₀ h₁ h₂, add (a.checked_sub c h₀) (b.checked_sub d h₁) = (add a b).checked_sub (add c d) h₂ := by
  intro c_le_a d_le_b _
  apply Eq.symm
  apply nat.add_to_sub
  rw [nat.add_perm0, nat.add_comm _ c, nat.add_perm0, nat.add_comm c]
  rw [nat.sub_add_inv]
  rw [nat.add_comm]
  rw [nat.add_perm4]
  rw [nat.sub_add_inv]
  rw [nat.add_comm]

