{-# OPTIONS --no-unicode #-}

module Lib.Nat where

open import Lib.One
open import Lib.Zero
open import Lib.Sigma
open import Lib.Sum
open import Lib.Eq

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

suc-inj : {n m : Nat} -> suc n == suc m -> n == m
suc-inj refl = refl

suc-inj-/= : {n m : Nat} -> (suc n == suc m -> Zero) -> n == m -> Zero
suc-inj-/= sucn/=sucm refl = sucn/=sucm refl

{-# BUILTIN NATURAL Nat #-}

data _<=_ : Nat -> Nat -> Set where
  ozero : {n : Nat} -> 0 <= n
  osuc : {n m : Nat} -> n <= m -> suc n <= suc m

infix 30 _<=_

_<_ : Nat -> Nat -> Set
n < m = n <= m * (n == m -> Zero)

<-suc : {n m : Nat} -> n < m -> suc n < suc m
<-suc (n<=m , n/=m) = osuc n<=m , \ sucn==sucm -> n/=m (suc-inj sucn==sucm)

<=-is-<-or-== : {n m : Nat} -> n <= m -> n < m + n == m
<=-is-<-or-== {.0} {zero} ozero = inr refl
<=-is-<-or-== {.0} {suc m} ozero = inl (ozero , (\ ()))
<=-is-<-or-== (osuc n<=m) with <=-is-<-or-== n<=m
<=-is-<-or-== (osuc n<=m) | inl n<m = inl (<-suc (n<=m , snd n<m))
<=-is-<-or-== (osuc n<=m) | inr refl = inr refl

Fin : Nat -> Set
Fin n = Nat >< \ m -> m < n

FinEq : {n m : Nat} -> Fin n -> Fin m -> Set
FinEq (n , _) (m , _) = n == m

<=-trans : {n m k : Nat} -> n <= m -> m <= k -> n <= k
<=-trans ozero ozero = ozero
<=-trans ozero (osuc m<=k) = ozero
<=-trans (osuc n<=m) (osuc m<=k) = osuc (<=-trans n<=m m<=k)

<=-antisymmetric : {n m : Nat} -> n <= m -> m <= n -> n == m
<=-antisymmetric ozero ozero = refl
<=-antisymmetric (osuc n<=m) (osuc m<=n) = ap suc (<=-antisymmetric n<=m m<=n)

<-asymmetric : {n m : Nat} -> n < m -> m < n -> Zero
<-asymmetric (n<=m , n/=m) (m<=n , m=/n) = n/=m (<=-antisymmetric n<=m m<=n)

<=-refl : {n : Nat} -> n <= n
<=-refl {zero} = ozero
<=-refl {suc n} = osuc <=-refl

==-implies-<= : {n m : Nat} -> n == m -> n <= m
==-implies-<= refl = <=-refl

<-trans : {n m k : Nat} -> n < m -> m < k -> n < k
<-trans (n<=m , n/=m) (m<=k , m/=k) = <=-trans n<=m m<=k , \ n==k -> help n==k (n<=m , n/=m) (m<=k , m/=k)
  where
  help : {n m k : Nat} -> n == k -> n < m -> m < k -> Zero
  help refl x y = <-asymmetric x y

<-osuc : {n : Nat} -> n < suc n
<-osuc {zero} = ozero , (\ ())
<-osuc {suc n} = <-suc <-osuc

<-zero-impossible : {n : Nat} -> n < zero -> Zero
<-zero-impossible (ozero , n/=m) = n/=m refl

<=-between : {n m : Nat} -> n <= m -> m <= suc n -> m == n + m == suc n
<=-between ozero ozero = inl refl
<=-between ozero (osuc ozero) = inr refl
<=-between (osuc n<m) (osuc m<=sucn) with <=-between n<m m<=sucn
<=-between (osuc n<m) (osuc m<=sucn) | inl refl = inl refl
<=-between (osuc n<m) (osuc m<=sucn) | inr refl = inr refl

suc-nothing-between : {n m : Nat} -> n < m -> m < suc n -> Zero
suc-nothing-between (n<=m , n/=m) (m<=sucn , m/=sucn) with <=-between n<=m m<=sucn
suc-nothing-between (n<=m , n/=m) (m<=sucn , m/=sucn) | inl refl = n/=m refl
suc-nothing-between (n<=m , n/=m) (m<=sucn , m/=sucn) | inr refl = m/=sucn refl

maxFin : {n m : Nat} -> n < m -> Fin m >< \x -> (y : Fin n) -> fst y == fst x -> Zero
maxFin {n} {zero} n<m = naughtE (<-zero-impossible n<m)
maxFin {n} {suc m} n<m = (m , <-osuc) , \{ (y , y<n) refl -> suc-nothing-between y<n n<m}
