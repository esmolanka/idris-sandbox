%default total

rev : List a -> List a
rev [] = []
rev (x :: xs) = rev xs ++ [x]

rev_tail' : List a -> List a -> List a
rev_tail' [] acc = acc
rev_tail' (x :: xs) acc = rev_tail' xs (x :: acc)

rev_tail : List a -> List a
rev_tail xs = rev_tail' xs []

rev_lemma1
  : (xs : List a)
 -> (rest : List a)
 -> rev_tail' xs [] ++ rest = rev_tail' xs rest
rev_lemma1 [] rest = Refl
rev_lemma1 (x :: xs) rest =
  rewrite (sym (rev_lemma1 xs [x]))
  in rewrite (sym (appendAssociative (rev_tail' xs []) [x] rest))
  in rewrite (sym (rev_lemma1 xs (x :: rest)))
  in Refl

rev_tail_correct : (xs : List a) -> rev xs = rev_tail xs
rev_tail_correct [] = Refl
rev_tail_correct (x :: xs) =
  rewrite rev_tail_correct xs
  in rewrite rev_lemma1 xs [x]
  in Refl
