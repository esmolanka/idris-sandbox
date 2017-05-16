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

----------------------------------------------------------------------

map : (f : a -> b) -> (l : List a) -> List b
map f [] = []
map f (x :: xs) = f x :: map f xs

map_tail' : (f : a -> b) -> (l : List a) -> (acc : List b) -> List b
map_tail' f [] acc = rev_tail acc
map_tail' f (x :: xs) acc = map_tail' f xs (f x :: acc)

map_tail : (f : a -> b) -> (l : List a) -> List b
map_tail f l = map_tail' f l []

map_lemma1
  : (f : a -> b) -> (xs : List a) -> (ys : List b)
 -> rev_tail' ys [] ++ map_tail' f xs [] = map_tail' f xs ys
map_lemma1 f [] ys = rewrite (appendNilRightNeutral (rev_tail' ys [])) in Refl
map_lemma1 f (x :: xs) ys =
  rewrite (sym (map_lemma1 f xs [f x]))
  in rewrite (appendAssociative (rev_tail' ys []) [f x] (map_tail' f xs []))
  in rewrite (rev_lemma1 ys [f x])
  in rewrite (sym (map_lemma1 f xs (f x :: ys)))
  in Refl

map_tail_correct : (l : List a) -> map f l = map_tail f l
map_tail_correct [] = Refl
map_tail_correct {f} (x :: xs) =
  rewrite (map_tail_correct {f=f} xs)
  in rewrite (sym (map_lemma1 f xs [f x]))
  in Refl
