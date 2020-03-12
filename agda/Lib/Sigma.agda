{-# OPTIONS --no-unicode #-}

module Lib.Sigma where

record _><_ (A : Set) (P : A -> Set) : Set where
  constructor _,_

  field
    fst : A
    snd : P fst

open _><_ public

infixr 20 _><_ _*_ _,_

_*_ : (A B : Set) -> Set
_*_ A B = A >< \ _ → B
