-- Extra proofs that I wanted to try.

-- If for all x : A, P(x) and Q(x) then (for all x : A, P(x)) and (for all x : A, Q(x))

prf_1 : {a:Type} -> {p:a -> Type} -> {q:a -> Type}
     -> ((x:a) -> (p x, q x))
     -> (((x:a) -> p x), ((x:a) -> q x))
prf_1 f = (\x => fst (f x), \x => snd (f x))

pred_leq_rhs_2 : (x : LTE n right) -> LTE n (S right)
pred_leq_rhs_2 LTEZero = LTEZero
pred_leq_rhs_2 (LTESucc x) = LTESucc (pred_leq_rhs_2 x)

pred_leq : (n:Nat) -> (m:Nat) -> (LTE (S n) m) -> (LTE n m)
pred_leq n (S right) (LTESucc x) = pred_leq_rhs_2 x

-- n <= m if there exists a k : Nat s.t. n+k = m
leq : (n:Nat) -> (m:Nat) -> (k:Nat ** n+k = m) -> (LTE n m)
leq Z m (k ** pf) = LTEZero
leq (S j) m (k ** pf) =
  ?h
    where
      lem : j + (S k) = m
      lem = rewrite sym (plusSuccRightSucc j k) in pf
      t : LTE j m
      t = leq j m (S k ** lem)
