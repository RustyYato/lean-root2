import Lean

inductive nat where
  | zero : nat
  | inc : nat -> nat

instance : OfNat nat Nat.zero where
    ofNat : nat := nat.zero
instance [OfNat nat n] : OfNat nat (n + 1) where
  ofNat : nat := nat.inc (OfNat.ofNat n)

@[simp]
def toNat (n: nat): Nat := match n with
  | nat.zero => Nat.zero
  | nat.inc n => Nat.succ (toNat n)

instance : SizeOf nat where
  sizeOf := toNat

instance : Repr nat where
  reprPrec n := Repr.reprPrec (toNat n)
