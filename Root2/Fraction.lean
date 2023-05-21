import Root2.Nat
import Root2.Nat.Gcd

structure fraction where
  top: nat
  bot: nat

@[simp]
def fraction.is_reduced (f: fraction) : Prop := gcd f.top f.bot <= nat.zero.inc

#print axioms fraction.is_reduced

@[simp]
def fraction.eq (a b: fraction) := nat.mul a.top b.bot = nat.mul a.bot b.top

#print axioms fraction.eq

def fraction.reduce (f: fraction): fraction := 
  match ht:f.top, hb:f.bot with
  | .zero, .zero => f
  | .zero, .inc _ => fraction.mk .zero nat.zero.inc
  | .inc _ , _ =>
  let gcd_nz : nat.zero < gcd.bounded f.top f.bot := (by
    rw [←gcd.bounded_eq]
    generalize gdef:gcd f.top f.bot = g
    match hg:g with
    | .zero =>
      rw [gcd.zero] at gdef
      have ⟨ left, _ ⟩ := gdef
      rw [left] at ht
      contradiction
    | .inc _ =>
      apply nat.zero_lt_inc)
  let tdr := divrem.calc f.top (gcd.bounded f.top f.bot) gcd_nz
  let bdr := divrem.calc f.bot (gcd.bounded f.top f.bot) gcd_nz
  fraction.mk tdr.quocient bdr.quocient

#print axioms fraction.reduce

def fraction.reduce.eq.helper { a b } (da: divrem a (gcd.bounded a b)) (db :divrem b (gcd.bounded a b)) : nat.mul a db.quocient = nat.mul b da.quocient := by
  have gdvd := gcd.is_dvd a b
  rw [gcd.bounded_eq] at gdvd
  have ⟨ ga, gb ⟩ := gdvd
  conv => { lhs; lhs; rw [da.dvd_quocient ga] }
  conv => { rhs; lhs; rw [db.dvd_quocient gb] }
  rw [←nat.mul_perm0, nat.mul_perm1]

def fraction.reduce.eq : ∀ f: fraction, f.eq f.reduce := by
  intro f
  match f with
  | fraction.mk .zero .zero =>  simp
  | fraction.mk .zero (.inc b) =>
    unfold reduce
    simp
    rw [nat.mul_zero_r]
  | fraction.mk (.inc t) _ =>
    unfold reduce
    simp only
    unfold eq
    simp only
    apply fraction.reduce.eq.helper

#print axioms fraction.reduce.eq

def fraction.reduce.is_reduced.helper { a b } (da: divrem a (gcd.bounded a b)) (db :divrem b (gcd.bounded a b)) : gcd da.quocient db.quocient <= nat.zero.inc := by
  apply Or.inr
  apply Compare.ord_from_eq
  
  have gcd_mul : gcd (nat.mul (gcd a b) da.quocient) (nat.mul (gcd a b) db.quocient) = nat.mul (gcd a b) (gcd da.quocient db.quocient) := 
    gcd.mul_left
  have := gcd.is_dvd a b
  rw [gcd.bounded_eq] at this
  have ⟨ ga, gb ⟩ := this
  have adef := da.dvd_quocient ga
  have bdef := db.dvd_quocient gb
  rw [gcd.bounded_eq, gcd.bounded_eq] at gcd_mul
  rw [←adef, ←bdef] at gcd_mul
  clear this ga gb adef bdef
  match nat.mul_eq_id gcd_mul with
  | .inr _ => assumption
  | .inl eq_zero =>
    have := da.div_nz
    rw [eq_zero] at this
    contradiction

def fraction.reduce.is_reduced : ∀f:fraction, f.reduce.is_reduced := by
  intro f
  match f with
  | fraction.mk .zero .zero => simp
  | fraction.mk .zero (.inc b) =>
    unfold reduce
    simp
  | fraction.mk (.inc t) _ =>
    unfold reduce
    unfold is_reduced
    simp only
    apply fraction.reduce.is_reduced.helper

#print axioms fraction.reduce.is_reduced

