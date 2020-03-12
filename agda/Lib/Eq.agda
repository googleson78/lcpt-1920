module Lib.Eq where

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}

ap : {A : Set} {x y : A} (f : A -> A) -> x == y -> f x == f y
ap f refl = refl
