-- Show that for any type A, we have ¬¬¬A → ¬A

not : Type -> Type
not a = a -> Void

prf : {a:Type} -> not (not (not a)) -> not a
prf x = \a => x (\f => f a)
