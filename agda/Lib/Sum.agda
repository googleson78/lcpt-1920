module Lib.Sum where

open import Lib.Zero

data _+_ (A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B

infixr 10 _+_

Dec : Set -> Set
Dec P = (Zero -> P) + P
