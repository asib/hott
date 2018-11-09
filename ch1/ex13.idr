-- Using propositions-as-types, derive the double negation of the principle of excluded
-- middle, i.e. prove not (not (P or not P))

not : Type -> Type
not a = a -> Void

-- Using sum type definition from ex 5.
infixl 6 +:

(+:) : (a:Type) -> (b:Type) -> Type
a +: b = (f:Bool ** if f then a else b)

inl : {a:Type} -> {b:Type} -> a -> a +: b
inl x = (True ** x)

inr : {a:Type} -> {b:Type} -> b -> a +: b
inr x = (False ** x)

prf : {p:Type} -> not (not (p +: (not p)))
prf {p} f = f (inr {a=p} {b=not p} (\x => f (inl {a=p} {b=not p} x)))
