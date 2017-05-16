%default total

sum : List Nat -> Nat
sum [] = 0
sum (x :: xs) = x + sum xs

sum_tail' : List Nat -> Nat -> Nat
sum_tail' [] k = k
sum_tail' (x :: xs) k = sum_tail' xs (x + k)

sum_tail : List Nat -> Nat
sum_tail xs = sum_tail' xs 0

sum_tail_lemma1 : (xs : List Nat) -> (k : Nat) -> sum_tail' xs k = plus (sum_tail' xs 0) k
sum_tail_lemma1 [] k =
  Refl
sum_tail_lemma1 (x :: xs) Z =
  rewrite plusZeroRightNeutral (sum_tail' xs (plus x 0))
  in Refl
sum_tail_lemma1 (x :: xs) (S k) =
  rewrite (sum_tail_lemma1 xs (plus x (S k)))
  in rewrite (plusZeroRightNeutral x)
  in rewrite (plusCommutative x (S k))
  in rewrite (plusCommutative (sum_tail' xs 0) (S (plus k x)))
  in rewrite (plusCommutative (sum_tail' xs x) (S k))
  in rewrite (sum_tail_lemma1 xs x)
  in rewrite (plusCommutative (sum_tail' xs 0) x)
  in rewrite (plusAssociative k x (sum_tail' xs 0))
  in Refl

sum_tail_correct : (l : List Nat) -> sum_tail l = sum l
sum_tail_correct [] = Refl
sum_tail_correct (x :: xs) =
  rewrite (plusZeroRightNeutral x)
  in rewrite (plusCommutative x (sum xs))
  in rewrite (sym (sum_tail_correct xs))
  in rewrite (sym (sum_tail_lemma1 xs x))
  in Refl

sum_cont' : {a : Type} -> List Nat -> (Nat -> a) -> a
sum_cont' [] k = k 0
sum_cont' (x :: xs) k = sum_cont' xs (\ans => k (x + ans))

sum_cont : List Nat -> Nat
sum_cont l = sum_cont' l (\x => x)

sum_cont_correct' : (k : Nat -> ty) -> (xs : List Nat) -> sum_cont' xs k = k (sum xs)
sum_cont_correct' k [] = Refl
sum_cont_correct' k (x :: xs) = sum_cont_correct' (k . (plus x)) xs

sum_cont_correct : (xs : List Nat) -> sum_cont xs = sum xs
sum_cont_correct xs = sum_cont_correct' (\x => x) xs
