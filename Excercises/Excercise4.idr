%default total

data Expr : Type where
  Const : Nat -> Expr
  Plus  : Expr -> Expr -> Expr

eval : Expr -> Nat
eval (Const k) = k
eval (Plus x y) = eval x + eval y

eval_tail' : Expr -> Nat -> Nat
eval_tail' (Const k) acc = k + acc
eval_tail' (Plus x y) acc = eval_tail' x (eval_tail' y acc)

eval_tail : Expr -> Nat
eval_tail e = eval_tail' e 0

----------------------------------------------------------------------

eval_tail_plus_acc : (e : Expr) -> (acc : Nat) -> eval_tail' e acc = eval_tail' e 0 + acc
eval_tail_plus_acc (Const k) _ =
  rewrite plusZeroRightNeutral k in Refl
eval_tail_plus_acc (Plus x y) acc =
  rewrite eval_tail_plus_acc y acc
  in rewrite eval_tail_plus_acc x (plus (eval_tail' y 0) acc)
  in rewrite plusAssociative (eval_tail' x 0) (eval_tail' y 0) acc
  in rewrite sym (eval_tail_plus_acc x (eval_tail' y 0))
  in Refl

eval_tail_correct : (e : Expr) -> eval e = eval_tail e
eval_tail_correct (Const k)  =
  rewrite plusZeroRightNeutral k in Refl
eval_tail_correct (Plus x y) =
  rewrite sym (eval_tail_correct y)
  in rewrite (eval_tail_plus_acc x (eval y))
  in rewrite sym (eval_tail_correct x)
  in Refl

----------------------------------------------------------------------

eval_cont' : {a : Type} -> Expr -> (Nat -> a) -> a
eval_cont' (Const k) f = f k
eval_cont' (Plus x y) f =
  eval_cont' y $ \b =>
  eval_cont' x $ \a =>
    f (a + b)

eval_cont : Expr -> Nat
eval_cont x = eval_cont' x id

eval_cont_lemma : (e : Expr) -> (f : Nat -> ty) -> eval_cont' e f = f (eval e)
eval_cont_lemma (Const k) f = Refl
eval_cont_lemma (Plus x y) f =
  rewrite eval_cont_lemma y (\b => eval_cont' x (\a => f (plus a b)))
  in rewrite eval_cont_lemma x (\a => f (plus a (eval y)))
  in Refl

eval_cont_correct : (e : Expr) -> eval e = eval_cont e
eval_cont_correct e = rewrite sym $ eval_cont_lemma e id in Refl

----------------------------------------------------------------------

data Instr : Type where
  Push : Nat -> Instr
  Add  : Instr

Prog : Type
Prog = List Instr

Stack : Type
Stack = List Nat

run : Prog -> Stack -> Stack
run [] s = s
run (Push n :: prg) s = run prg (n :: s)
run (Add :: prg) [] = run prg []
run (Add :: prg) (x :: []) = run prg [x]
run (Add :: prg) (x :: y :: s) = run prg (x + y :: s)

compile : Expr -> Prog
compile (Const n) = [Push n]
compile (Plus x y) = compile x ++ compile y ++ [Add]

run_lemma' : (i : Instr) -> (p : Prog) -> (s : Stack) -> run (i :: p) s = run p (run [i] s)
run_lemma' (Push k) p s = Refl
run_lemma' Add p [] = Refl
run_lemma' Add p (x :: []) = Refl
run_lemma' Add p (x :: (y :: xs)) = Refl

run_lemma : (p1, p2 : Prog) -> (s : Stack) -> run (p1 ++ p2) s = run p2 (run p1 s)
run_lemma [] p2 s = Refl
run_lemma (x :: xs) p2 s =
  rewrite run_lemma' x (xs ++ p2) s
  in rewrite run_lemma' x xs s
  in rewrite sym $ run_lemma xs p2 (run [x] s)
  in Refl

compile_correct' : (e : Expr) -> (s : Stack) -> run (compile e) s = eval e :: s
compile_correct' (Const k) s = Refl
compile_correct' (Plus x y) s =
  rewrite run_lemma (compile x) (compile y ++ [Add]) s in
  rewrite run_lemma (compile y) [Add] (run (compile x) s) in
  rewrite compile_correct' x s in
  rewrite compile_correct' y (eval x :: s) in
  rewrite plusCommutative (eval x) (eval y) in Refl

compile_correct : (e : Expr) -> run (compile e) [] = [eval e]
compile_correct e = compile_correct' e []
