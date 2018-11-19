-- ind': ∏(a:A). ∏(C:∏(x:A). (a=x)→U). C(a,refl) → ∏(x:A). ∏(p:a=x). C(x, p)

ind' : {a:Type}
    -> (a':a)
    -> (c:((x:a) -> (a'=x) -> Type))
    -> (c a' Refl)
    -> (x:a) -> (p:a'=x) -> c x p
ind' a c c' a Refl = c'

-- ind: ∏(C:∏(x,y:A) (x=y)→U). (∏(x:A). C(x, x,refl)) → ∏(x,y:A). ∏(p:x=y). C(x, y, p)

ind : {a:Type}
   -> (c:((x:a) -> (y:a) -> (x=y) -> Type))
   -> (pc:((x:a) -> c x x Refl))
   -> (x:a) -> (y:a) -> (p:x=y) -> c x y p
ind c c' x y p = ind' x (c x) (c' x) y p
