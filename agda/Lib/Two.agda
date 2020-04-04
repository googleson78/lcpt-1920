module Lib.Two where

open import Lib.Eq
open import Lib.Sum
open import Lib.Zero
open import Lib.One
open import Lib.Sigma

data Two : Set where
  ff tt : Two

instance
  EqTwo : Eq Two
  EqTwo = record { dec = decTwo }
    where
    decTwo : (x y : Two) -> Dec (x == y)
    decTwo ff ff = inr refl
    decTwo ff tt = inl (\ ())
    decTwo tt ff = inl (\ ())
    decTwo tt tt = inr refl

infixr 40 _&&_
_&&_ : Two -> Two -> Two
ff && _ = ff
tt && ff = ff
tt && tt = tt

infixr 30 _||_
_||_ : Two -> Two -> Two
tt || _ = tt
ff || ff = ff
ff || tt = tt

||-commut : (p q : Two) -> p || q == q || p
||-commut ff ff = refl
||-commut ff tt = refl
||-commut tt ff = refl
||-commut tt tt = refl

||-idL : {x : Two} -> ff || x == x
||-idL {ff} = refl
||-idL {tt} = refl

||-tt-consumeR : {x : Two} -> x || tt == tt
||-tt-consumeR {ff} = refl
||-tt-consumeR {tt} = refl

So : Two -> Set
So ff = Zero
So tt = One

not : Two -> Two
not ff = tt
not tt = ff

if_then_else_ : {A : Set} -> (b : Two) -> ({So b} -> A) -> ({So (not b)} -> A) -> A
if ff then t else e = e
if tt then t else e = t

eq? : {A : Set} {{eqA : Eq A}} -> A -> A -> Two
eq? x y with dec x y
... | inl x1 = ff
... | inr x1 = tt

data _==>_ : Two -> Two -> Set where
  fx : {x : Two} -> ff ==> x
  tt : tt ==> tt

==>-unique : {x y : Two} (im1 im2 : x ==> y) -> im1 == im2
==>-unique fx fx = refl
==>-unique tt tt = refl

==>-refl : {x : Two} -> x ==> x
==>-refl {ff} = fx
==>-refl {tt} = tt

==>-trans : {x y z : Two} -> x ==> y -> y ==> z -> x ==> z
==>-trans fx y==>z = fx
==>-trans tt tt = tt

==>tt : {x : Two} -> x ==> tt
==>tt {ff} = fx
==>tt {tt} = tt

==>-|| : {x y z : Two} -> x ==> z -> y ==> z -> x || y ==> z
==>-|| tt y==>z = tt
==>-|| fx fx = fx
==>-|| fx tt = tt

||-==>-L : (x y z : Two) -> x || y ==> z -> x ==> z
||-==>-L ff y z x||y==>z = fx
||-==>-L tt y z x||y==>z = x||y==>z

||-monoL-==> : (x y : Two) -> y ==> x || y
||-monoL-==> x ff = fx
||-monoL-==> x tt rewrite ||-tt-consumeR {x} = tt
