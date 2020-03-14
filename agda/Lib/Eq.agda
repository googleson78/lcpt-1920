module Lib.Eq where

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

==-symm : {A : Set} {x y : A} -> x == y -> y == x
==-symm refl = refl

{-# BUILTIN EQUALITY _==_ #-}

ap : {A : Set} {x y : A} (f : A -> A) -> x == y -> f x == f y
ap f refl = refl
