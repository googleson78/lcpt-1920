{-# OPTIONS --no-unicode #-}
{-# OPTIONS --sized-types #-}

module Lambda where

open import Lib.Eq
open import Lib.Nat
open import Lib.Sigma
open import Lib.Sum
open import Lib.Two
open import Lib.Zero
open import Lib.One
open import Lib.NatSet

-- need these to prove that renaming doesn't change the size
-- so that we can continue our recursive call in _[_=>_]
{-# BUILTIN SIZE Size #-}
{-# BUILTIN SIZESUC sizeSuc #-}
{-# BUILTIN SIZEINF sizeInf #-}

infixl 30 _app_
data Lambda : Size -> Set where
  v : {i : Size} -> (n : Nat) -> Lambda (sizeSuc i)
  _app_ : {i : Size} -> Lambda i -> Lambda i -> Lambda (sizeSuc i)
  lam_>_ : {i : Size} -> Nat -> Lambda i -> Lambda (sizeSuc i)

freeVars : {i : Size} -> Lambda i -> NatSet
freeVars (v n) = [ n ]
freeVars (M app N) = union (freeVars M) (freeVars N)
freeVars (lam x > M) = delete x (freeVars M)

freeVars-Can : {i : Size} -> (M : Lambda i) -> Can (freeVars M)
freeVars-Can (v n) = can1 [ n ]-Can1
freeVars-Can (M1 app M2) =
  union-preserves-Can
    (freeVars M1) (freeVars M2)
    (freeVars-Can M1) (freeVars-Can M2)
freeVars-Can (lam x > M) = minus-Can (freeVars M) [ x ]

boundVars : {i : Size} -> Lambda i -> NatSet
boundVars (v n) = empty 0
boundVars (M app N) = union (boundVars M) (boundVars N)
boundVars (lam x > M) = x <: boundVars M

vars : {i : Size} -> Lambda i -> NatSet
vars x = union (freeVars x) (boundVars x)

_[_=r>_] : {i : Size} -> Lambda i -> Nat -> Nat -> Lambda i
v k [ n =r> m ] with dec k n
... | inl no = v k
... | inr yes = v m
(M1 app M2) [ n =r> m ] = (M1 [ n =r> m ]) app (M2 [ n =r> m ])
(lam x > N) [ n =r> m ] with dec x n
... | inl no = lam x > (N [ n =r> m ])
... | inr yes = lam x > N

infix 40 _[_=>_]
_[_=>_] : {i : Size} -> Lambda i -> Nat -> Lambda sizeInf -> Lambda sizeInf
v n [ k => N ] with dec n k
... | inl x = v n
... | inr x = N
(M1 app M2) [ k => N ] = M1 [ k => N ] app M2 [ k => N ]
(lam x > M) [ k => N ] with dec x k
... | inr yes = lam x > M
... | inl x/=k with has x (freeVars N)
... | ff = lam x > (M [ k => N ])
... | tt with firstNotIn (freeVars N)
... | x1 = lam x1 > ((M [ x =r> x1 ]) [ k => N ])

infix 25 _=a=_
data _=a=_ : {i : Size} -> Lambda i -> Lambda i -> Set where
  a-v : {i : Size} -> {n : Nat} -> v {i} n =a= v {i} n
  a-app : {i : Size} {M1 N1 M2 N2 : Lambda i} -> M1 =a= M2 -> N1 =a= N2 -> M1 app N1 =a= M2 app N2
  a-lam : {i : Size} {k : Nat} {M N : Lambda i} -> M =a= N -> (lam k > M) =a= (lam k > N)
  a-rnm : {i : Size} {p q : Nat} {M M' : Lambda i} -> (So (not (has q (vars M)))) -> (M [ p =r> q ]) =a= M' -> (lam p > M) =a= (lam q > M')

=a=-refl : {i : Size} (M : Lambda i) -> M =a= M
=a=-refl (v {i} n) = a-v {i}
=a=-refl (x app x1) = a-app (=a=-refl x) (=a=-refl x1)
=a=-refl (lam x > x1) = a-lam (=a=-refl x1)

_ : v 0 =a= v 0
_ = a-v

_ : v 1 app v 2 =a= v 1 app v 2
_ = a-app a-v a-v

_ : (lam 2 > v 3 app v 2) =a= (lam 1 > v 3 app v 1)
_ = a-rnm <> (=a=-refl _)

_ : (lam 2 > lam 1 > v 1 app v 2) =a= (lam 3 > lam 4 > v 4 app v 3)
_ = a-rnm <> (a-rnm <> (=a=-refl _))
