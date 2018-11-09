-- Using the propositions as types interpretation, derive the following tautologies.
--   (i) If A, then (if B then A).
--   (ii) If A, then not (not A).
--   (iii) If (not A or not B), then not (A and B).

not : Type -> Type
not a = a -> Void

prf_i : a -> (b -> a)
prf_i x y = x

prf_ii : a -> not (not a)
prf_ii x = \f => f x

-- Using sum type definition from ex 5.
infixl 6 +:

(+:) : (a:Type) -> (b:Type) -> Type
a +: b = (f:Bool ** if f then a else b)

inl : {a:Type} -> {b:Type} -> a -> a +: b
inl x = (True ** x)

inr : {a:Type} -> {b:Type} -> b -> a +: b
inr x = (False ** x)

prf_iii : (not a) +: (not b) -> not (a, b)
prf_iii (True ** x) = x . fst
prf_iii (False ** y) = y . snd
