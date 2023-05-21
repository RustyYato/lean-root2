import Root2.Prime.PrimeFactor

theorem nat.dvd_implies_sub_seq
  (fn: PrimeFactorization n)
  (fm: PrimeFactorization m)
  (d: dvd n m)
  : fm.factors.sub_seq fn.factors := by
  
  admit