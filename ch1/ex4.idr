-- Assuming as given only the iterator for natural numbers
-- 	iter : ∏C:U. C → (C → C) → N → C
-- with the defining equations
-- 	iter(C, c0, cs, 0) :≡ c0,
-- 	iter(C, c0, cs,succ(n)) :≡ cs(iter(C, c0, cs, n)),
-- derive a function having the type of the recursor recN. Show that the defining equations of the
-- recursor hold propositionally for this function, using the induction principle for N.

-- recN : ∏(C:U). C → (N → C → C) → N → C
-- recN(C, c0, cs, 			 0) :≡ c0
-- recN(C, c0, cs, succ(n)) :≡ cs(n, recN(C, c0, cs, n))


-- indN : ∏(C:N→U). C(0) → (∏(n:N). C(n) → C(succ(n))) → ∏(n:N). C(n)
-- indN(C, c0, cs, 			 0) :≡ c0,
-- indN(C, c0, cs, succ(n)) :≡ cs(n, indN(C, c0, cs, n)).

iter : (c:Type)
		-> (c0:c)
		-> (cs:c -> c)
		-> (n:Nat)
		-> c
iter c c0 cs Z = c0
iter c c0 cs (S n) = cs (iter c c0 cs n)

rec_n : (c:Type)
		 -> (c0:c)
		 -> (cs:Nat -> c -> c)
		 -> (n:Nat)
		 -> c
rec_n c c0 cs n = Prelude.Basics.snd (iter (Nat, c) (Z, c0) (\(n, d) => (S n, cs n d)) n)
  {-
   -where z' : (Nat, c)
   -      z' = (Z, c0)
   -      s' : (Nat, c) -> (Nat, c)
   -      s' (n, d) = (S n, cs n d)
   -}

ind_n : (c:Nat -> Type)
		 -> (c0:c 0)
		 -> (cs:(m:Nat) -> c m -> c (S m))
		 -> (n:Nat) -> c n
ind_n c c0 cs Z = c0
ind_n c c0 cs (S n) = cs n (ind_n c c0 cs n)

rec_n_def : (c:Type)
         -> (c0:c)
         -> (cs:Nat -> c -> c)
         -> (n:Nat)
         -> c
rec_n_def c c0 cs Z = c0
rec_n_def c c0 cs (S n) = cs n (rec_n_def c c0 cs n)

prf_base_rec_n : (c:Type)
              -> (c0:c)
              -> (cs:Nat -> c -> c)
              -> rec_n_def c c0 cs Z = rec_n c c0 cs Z
prf_base_rec_n c c0 cs = Refl

prf_ih_rec_n : (c:Type)
            -> (c0:c)
            -> (cs:Nat -> c -> c)
            -> (n:Nat)
            -> (prf:rec_n_def c c0 cs n = rec_n c c0 cs n)
            -> rec_n_def c c0 cs (S n) = rec_n c c0 cs (S n)
prf_ih_rec_n c c0 cs n prf = rewrite prf in ?h

{-
 -prf_rec_n : (c:Type)
 -         -> (c0:c)
 -         -> (cs:Nat -> c -> c)
 -         -> (n:Nat)
 -         -> rec_n_def c c0 cs n = rec_n c c0 cs n
 -prf_rec_n c c0 cs = ind_n (prf_rec_n c c0 cs) ?h1 ?h2
 -}
