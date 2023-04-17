import Root2.Prime

def AsTrue (dec : Decidable p) : Prop :=
  match dec with
  | .isTrue _ => True
  | .isFalse _ => False

theorem of_asTrue (dec : Decidable p) : AsTrue dec → p :=
  match dec with
  | .isTrue h => fun _ => h
  | .isFalse _ => False.elim

#eval nat.zero.inc.inc.check_prime

theorem two_is_prime : nat.prime (nat.inc (nat.inc nat.zero)) := 
  of_asTrue (nat.check_prime nat.zero.inc.inc) trivial


-- theorem two_is_prime : nat.prime (nat.inc (nat.inc nat.zero)) := by decide