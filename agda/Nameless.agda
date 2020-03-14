{-# OPTIONS --no-unicode #-}

module Nameless where

open import Lib.Nat
open import Lib.Sigma
open import Lib.Eq
open import Lib.Zero

data Nameless : Nat -> Set where
  v : {n : Nat} -> Fin n -> Nameless n
  _ap_ : {n : Nat} -> Nameless n -> Nameless n -> Nameless n
  lam : {n : Nat} -> Nameless (suc n) -> Nameless n

Nameless* : Set
Nameless* = {n : Nat} -> Nameless n

NamelessEq : {n m : Nat} -> Nameless n -> Nameless m -> Set
NamelessEq (v x) (v y) = FinEq x y
NamelessEq (m ap n) (p ap q) = NamelessEq m p * NamelessEq n q
NamelessEq (lam m) (lam n) = NamelessEq m n
-- if I delete these it gives the wtf blue colour
NamelessEq (v x) (y ap y₁) = Zero
NamelessEq (v x) (lam y) = Zero
NamelessEq (x ap x₁) (v x₂) = Zero
NamelessEq (x ap x₁) (lam y) = Zero
NamelessEq (lam x) (v x₁) = Zero
NamelessEq (lam x) (y ap y₁) = Zero

NamelessEq-refl : {n : Nat} (x : Nameless n) -> NamelessEq x x
NamelessEq-refl (v (_ , _)) = refl
NamelessEq-refl (x ap y) = NamelessEq-refl x , NamelessEq-refl y
NamelessEq-refl (lam x) = NamelessEq-refl x

-- task 2.9
promoNameless : {n m : Nat} -> n <= m -> (x : Nameless n) -> Nameless m >< \y -> NamelessEq x y
promoNameless n<=m (v (x , x<n)) = v (x , <-<=-trans x<n n<=m) , refl
promoNameless n<=m (x ap y) with promoNameless n<=m x | promoNameless n<=m y
promoNameless n<=m (x ap y) | x' , eqxx' | y' , eqyy' = (_ap_ x' y') , eqxx' , eqyy'
promoNameless n<=m (lam x) with promoNameless (osuc n<=m) x
promoNameless n<=m (lam x) | x' , eqxx' = lam x' , eqxx'

namelessStrictSubset : {n m : Nat} -> n < m -> Nameless m >< \x -> (y : Nameless n) -> NamelessEq x y -> Zero
namelessStrictSubset {n} {zero} n<m = naughtE (<-zero-impossible n<m)
namelessStrictSubset {n} {suc m} n<sucm = v (m , <-suc) , help
  where
  help : (y : Nameless n) -> NamelessEq (v (m , <-suc)) y -> Zero
  help (v (_ , m<n)) refl = naughtE (suc-nothing-between m<n n<sucm)
  help (_ ap _) ()
  help (lam _) ()
