-- Derive the induction principle for products indA×B, using only the projections and
-- the propositional uniqueness principle uniqA×B. Verify that the definitional equalities are valid.

uniq_prod : {a:Type} -> {b:Type}
         -> (x:(a,b))
         -> (fst x, snd x) = x
uniq_prod (a, b) = Refl

ind_prod : {a:Type} -> {b:Type}
        -> (c:(a,b) -> Type)
        -> ((x:a) -> (y:b) -> c (x,y))
        -> (x:(a,b)) -> c x
ind_prod c f x = rewrite sym (uniq_prod x) in f (fst x) (snd x)

prf_ind_prof : {a:Type} -> {b:Type}
            -> (c:(a,b) -> Type)
            -> (g:(x:a) -> (y:b) -> c (x,y))
            -> (x:a) -> (y:b)
            -> ind_prod c g (x,y) = g x y
prf_ind_prof c g x y = Refl
