-- Show that if we define A + B :≡ ∑(x:2) rec2(U, A, B, x), then we can give a
-- definition of indA+B for which the definitional equalities stated in §1.7 hold.

ind_2 : (f:(Bool -> Type))
     -> f True
     -> f False
     -> ((b:Bool) -> f b)
ind_2 f x y True = x
ind_2 f x y False = y

ind_dp : {a:Type} -> {b:a -> Type}
      -> (fam:((x:a ** b x) -> Type))
      -> ((x:a) -> (y:b x) -> fam (x**y))
      -> ((p:(x:a ** b x)) -> fam p)
ind_dp fam f (x ** pf) = f x pf

infixl 6 +:

(+:) : (a:Type) -> (b:Type) -> Type
a +: b = (f:Bool ** if f then a else b)

inl : {a:Type} -> {b:Type} -> a -> a +: b
inl x = (True ** x)

inr : {a:Type} -> {b:Type} -> b -> a +: b
inr x = (False ** x)

ind_coprod_lem : {a:Type} -> {b:Type}
              -> (family : (a +: b -> Type))
              -> (p:Bool)
              -> Type
ind_coprod_lem {a} {b} family True = (z:a) -> family (True ** z)
ind_coprod_lem {a} {b} family False = (z:b) -> family (False ** z)

ind_coprod : {a:Type} -> {b:Type}
          -> (family : (a +: b -> Type))
          -> ((x:a) -> family (inl x))
          -> ((x:b) -> family (inr x))
          -> ((x:a +: b) -> family x)
ind_coprod {a} {b} family f g x =
  ind_dp family (ind_2 (ind_coprod_lem family) f g) x
