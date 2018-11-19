-- ack(0, n) ≡ succ(n)
-- ack(succ(m), 0) ≡ ack(m, 1)
-- ack(succ(m),succ(n)) ≡ ack(m, ack(succ(m), n))

-- recN : ∏(C:U). C → (N → C → C) → N → C

rec_n : {c:Type} -> c -> (Nat -> c -> c) -> Nat -> c
rec_n x f Z = x
rec_n x f (S k) = f k (rec_n x f k)

ack_def : Nat -> Nat -> Nat
ack_def    Z     n  = S n
ack_def (S m)    Z  = ack_def m 1
ack_def (S m) (S n) = ack_def m (ack_def (S m) n)

ack : Nat -> Nat -> Nat
ack = rec_n S (\_, g => rec_n (g 1) (\_ => g))

prf_ack : (m:Nat) -> (n:Nat) -> ack m n = ack_def m n
prf_ack Z n = Refl
prf_ack (S m) Z = prf_ack m 1
prf_ack (S m) (S n) = rewrite prf_ack (S m) n in prf_ack m (ack_def (S m) n)
