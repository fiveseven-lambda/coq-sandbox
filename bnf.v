Inductive Expr0 :=
  | ex01 : Expr1 -> Expr0
  | add : Expr0 -> Expr1 -> Expr0
with Expr1 :=
  | ex12 : Expr2 -> Expr1
  | mul : Expr1 -> Expr2 -> Expr1
with Expr2 :=
  | lit : nat -> Expr2
  | grp : Expr0 -> Expr2.

Variant Token :=
  | Lit : nat -> Token
  | Plus
  | Times
  | Open
  | Close.

Require Import List.
Import ListNotations.

Fixpoint Expr0ToStr x := match x with
  | ex01 x1 => Expr1ToStr x1
  | add x0 x1 => Expr0ToStr x0 ++ [Plus] ++ Expr1ToStr x1
end with Expr1ToStr x := match x with
  | ex12 x2 => Expr2ToStr x2
  | mul x1 x2 => Expr1ToStr x1 ++ [Times] ++ Expr2ToStr x2
end with Expr2ToStr x := match x with
  | lit id => [ Lit id ]
  | grp x => [Open] ++ Expr0ToStr x ++ [Close]
end.

Theorem NoAmbiguity : forall x y, Expr0ToStr x = Expr0ToStr y -> x = y.
