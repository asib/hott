-- Derive the recursion principle for products recA×B using only the projections, and
-- verify that the definitional equalities are valid. Do the same for Σ-types.
-- rec∑(x:A) B(x): ∏(C:U). (∏(x:A). B(x) → C) → (∑(x:A)B(x)) → C

rec_prod : {a:Type} -> {b:Type}
        -> (c:Type)
        -> (a -> b -> c)
        -> (a,b) -> c
rec_prod c f x =
  f (fst x) (snd x)

prf_rec_prod : (c:Type) -> (f:(a -> b -> c))
            -> (x:a) -> (y:b)
            -> rec_prod c f (x,y) = f x y
prf_rec_prod c f x y = Refl

proj_1 : {a:Type} -> (a, b) -> a
proj_1 {a} = rec_prod a (\x, y => x)

proj_2 : {b:Type} -> (a, b) -> b
proj_2 {b} = rec_prod b (\x, y => y)

pf_pr1 : (p:(a, b)) -> fst p = proj_1 p
pf_pr1 p = Refl

pf_pr2 : (p:(a, b)) -> snd p = snd p
pf_pr2 p = Refl

rec_dprod : {a:Type} -> {b:a ->Type}
         -> (c:Type)
         -> ((x:a) -> b x -> c)
         -> (x:a ** b x)
         -> c
rec_dprod c f x = f (fst x) (snd x)

prf_rec_dprod : {a:Type} -> {b:a -> Type}
             -> (c:Type)
             -> (f:(x:a) -> b x -> c)
             -> (x:a)
             -> (y:b x)
             -> rec_dprod c f (x ** y) = f x y
