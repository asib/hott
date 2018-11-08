-- Given functions f : A → B and g : B → C, define their composite g ◦ f : A → C.
-- Show that we have h ◦ (g ◦ f) ≡ (h ◦ g) ◦ f.

infixr 6 .:

(.:) : (b -> c) -> (a -> b) -> (a -> c)
(.:) g f = \x => g (f x)

comp_assoc : (f:(a -> b))
          -> (g:(b -> c))
          -> (h:(c -> d))
          -> h .: (g .: f) = (h .: g) .: f
comp_assoc f g h = Refl
