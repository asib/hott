-- Extra proofs that I wanted to try.

-- If for all x : A, P(x) and Q(x) then (for all x : A, P(x)) and (for all x : A, Q(x))

prf_1 : {a:Type} -> {p:a -> Type} -> {q:a -> Type}
     -> ((x:a) -> (p x, q x))
     -> (((x:a) -> p x), ((x:a) -> q x))
prf_1 f = (\x => fst (f x), \x => snd (f x))
