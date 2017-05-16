%default total

fibo : (n : Nat) -> Nat
fibo Z = Z
fibo (S Z) = (S Z)
fibo (S (S k)) = fibo (S k) + fibo k

fibo_tail' : (n, a, b : Nat) -> Nat
fibo_tail' Z a b = b
fibo_tail' (S k) a b = fibo_tail' k (a + b) a

fibo_tail : Nat -> Nat
fibo_tail k = fibo_tail' k 1 0

fibo_tail_lemma : (n, m : Nat) -> fibo_tail' n (fibo (S m)) (fibo m) = fibo (n + m)
fibo_tail_lemma Z m = Refl
fibo_tail_lemma (S k) m =
  rewrite plusSuccRightSucc k m
  in rewrite fibo_tail_lemma k (S m)
  in Refl

fibo_tail_correct : (n : Nat) -> fibo_tail' n 1 0 = fibo n
fibo_tail_correct n =
  rewrite fibo_tail_lemma n 0
  in rewrite plusZeroRightNeutral n
  in Refl
