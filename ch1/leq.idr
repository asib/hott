-- Proofs concerning properties of the less than or equal (LEQ) binary predicate.

leq_lem : (n:Nat) -> (m:Nat) -> n = m -> LTE n m
leq_lem Z m prf = LTEZero
leq_lem (S k) Z prf = absurd (SIsNotZ prf)
leq_lem (S k) (S j) prf = LTESucc (leq_lem k j keqj)
  where
    keqj : k = j
    keqj = succInjective k j prf

leq_lem2 : LTE (n+k) m -> LTE n m
leq_lem2 {k = Z} {n} x = rewrite (plusCommutative 0 n) in x
leq_lem2 {k = (S k)} {n} {m} x = leq_lem2 xre2
  where
    xRewrite : LTE (S (n+k)) m
    xRewrite = rewrite (plusSuccRightSucc n k) in x
    xre2 : LTE (n+k) m
    xre2 = lteSuccLeft xRewrite

-- n <= m if there exists a k : Nat s.t. n+k = m
leq : (n:Nat) -> (m:Nat) -> (k:Nat ** n+k = m) -> (LTE n m)
leq Z m (k ** pf) = LTEZero
leq (S j) m (k ** pf) =
  leq_lem2 (leq_lem (S (j+k)) m pf)

infixl 6 <:=

(<:=) : (n:Nat) -> (m:Nat) -> Type
n <:= m = (k:Nat ** n+k = m)

lteZero : 0 <:= n
lteZero {n} = (n ** Refl)

lteRefl : n <:= n
lteRefl {n = Z} = (0 ** Refl)
lteRefl {n = (S m)} = (0 ** (rewrite (plusCommutative m 0) in Refl))

lteSuccRight : n <:= m -> n <:= (S m)
lteSuccRight {n} {m} (x ** pf) =
  ((S x) ** rewrite (sym (plusSuccRightSucc n x)) in
            rewrite (eqSucc (n+x) m pf) in Refl)

lteSuccLeft : (S n) <:= m -> n <:= m
lteSuccLeft {n} {m} (x ** pf) =
  ((S x) ** rewrite (sym (plusSuccRightSucc n x)) in pf)

lteTransitive : n <:= m -> m <:= p -> n <:= p
lteTransitive {n} {m} (k1 ** pf1) (k2 ** pf2) =
  (k1+k2 ** rewrite (plusAssociative n k1 k2) in
            rewrite pf1 in pf2)

lteAddRight : (n : Nat) -> n <:= (n+m)
lteAddRight Z = lteZero
lteAddRight {m} (S k) = (m ** Refl)

-- We show the following two ways of defining less than (<: and <::) are equivalent.
infixr 6 <:

(<:) : (n:Nat) -> (m:Nat) -> Type
n <: m = (k:Nat ** n+(S k) = m)

infixr 6 <::

(<::) : Nat -> Nat -> Type
n <:: m = (n <:= m, Not (n=m))

plusSuccAbsurd : {k:Nat} -> {l:Nat} -> Not (k+(S l) = k)
plusSuccAbsurd {k = Z} {l = l} eq = SIsNotZ eq
plusSuccAbsurd {k = (S k)} {l = l} pf =
  plusSuccAbsurd (succInjective (k+S l) k pf)

lt_equiv_1 : (n:Nat) -> (m:Nat) -> n <: m -> n <:: m
lt_equiv_1 Z m (l ** pf) =
  ((S l ** pf), \neqm => SIsNotZ (trans pf (sym neqm)))
lt_equiv_1 (S k) m (l ** pf) =
  ( (S l ** pf)
  , \pf2 => plusSuccAbsurd (succInjective (k + S l) k (trans pf (sym pf2))))

lt_equiv_2 : (n:Nat) -> (m:Nat) -> n <:: m -> n <: m
lt_equiv_2 n m ((Z ** pf), f) = absurd (f (trans (sym (plusZeroRightNeutral n)) pf))
lt_equiv_2 n m (((S l) ** pf), f) = (l ** pf)


