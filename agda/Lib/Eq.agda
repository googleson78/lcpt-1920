module Lib.Eq where

open import Lib.Sum

data _==_ {l} {A : Set l} (x : A) : A -> Set where
  refl : x == x

infix 15 _==_

==-symm : {A : Set} {x y : A} -> x == y -> y == x
==-symm refl = refl

{-# BUILTIN EQUALITY _==_ #-}

ap : {A : Set} {x y : A} (f : A -> A) -> x == y -> f x == f y
ap f refl = refl


record Eq (A : Set) : Set where
  field
    dec : (x y : A) -> Dec (x == y)

open Eq {{...}} public
