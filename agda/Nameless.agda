{-# OPTIONS --no-unicode #-}

module Nameless where

open import Lib.Nat
open import Lib.Sigma
open import Lib.Eq
open import Lib.Zero
open import Lib.Sum

data Nameless : Nat -> Set where
  v : {n : Nat} -> Fin n -> Nameless n
  _app_ : {n : Nat} -> Nameless n -> Nameless n -> Nameless n
  lam : {n : Nat} -> Nameless (suc n) -> Nameless n

infixl 30 _app_

Nameless* : Set
Nameless* = {n : Nat} -> Nameless n

NamelessEq : {n m : Nat} -> Nameless n -> Nameless m -> Set
NamelessEq (v x) (v y) = FinEq x y
NamelessEq (m app n) (p app q) = NamelessEq m p * NamelessEq n q
NamelessEq (lam m) (lam n) = NamelessEq m n
-- if I delete these it gives the wtf blue colour
NamelessEq (v x) (y app y₁) = Zero
NamelessEq (v x) (lam y) = Zero
NamelessEq (x app x₁) (v x₂) = Zero
NamelessEq (x app x₁) (lam y) = Zero
NamelessEq (lam x) (v x₁) = Zero
NamelessEq (lam x) (y app y₁) = Zero

NamelessEq-refl : {n : Nat} (x : Nameless n) -> NamelessEq x x
NamelessEq-refl (v (_ , _)) = refl
NamelessEq-refl (x app y) = NamelessEq-refl x , NamelessEq-refl y
NamelessEq-refl (lam x) = NamelessEq-refl x

-- task 2.9
promoNameless : {n m : Nat} -> n <= m -> (x : Nameless n) -> Nameless m >< \y -> NamelessEq x y
promoNameless n<=m (v (x , x<n)) = v (x , <-<=-trans x<n n<=m) , refl
promoNameless n<=m (x app y) with promoNameless n<=m x | promoNameless n<=m y
promoNameless n<=m (x app y) | x' , eqxx' | y' , eqyy' = x' app y' , eqxx' , eqyy'
promoNameless n<=m (lam x) with promoNameless (osuc n<=m) x
promoNameless n<=m (lam x) | x' , eqxx' = lam x' , eqxx'

namelessStrictSubset : {n m : Nat} -> n < m -> Nameless m >< \x -> (y : Nameless n) -> NamelessEq x y -> Zero
namelessStrictSubset {n} {zero} n<m = naughtE (<-zero-impossible n<m)
namelessStrictSubset {n} {suc m} n<sucm = v (m , <-suc) , help
  where
  help : (y : Nameless n) -> NamelessEq (v (m , <-suc)) y -> Zero
  help (v (_ , m<n)) refl = naughtE (suc-nothing-between m<n n<sucm)
  help (_ app _) ()
  help (lam _) ()

-- if we don't insist on the equality then we can skip recursing via NamelessEq-refl here
restruct : {n m : Nat} -> n == m -> (x : Nameless n) -> Nameless m >< \y -> NamelessEq x y
restruct refl x = x , NamelessEq-refl x

-- could use ↑⇑
shiftUp : {n : Nat} (d c : Nat) -> Nameless n -> Nameless (d +N n)
shiftUp d c (v k) with dec< (fst k) c
shiftUp {n} d c (v k) | inr k<c = fst (promoNameless (+N-monotone-<=-l n d) (v k))
shiftUp {n} d c (v (m , m<n)) | inl k>=c = v (d +N m , +N-monotone2-<-l m n d m<n)
shiftUp d c (x app y) = shiftUp d c x app shiftUp d c y
shiftUp {n} d c (lam x) = lam (fst (restruct (==-symm (+N-right-suc d n)) (shiftUp d (suc c) x)))

_[_=>_] : {n : Nat} -> Nameless n -> Nat -> Nameless n -> Nameless n
v (k' , _) [ k => N ] with dec== k k'
(v (k' , k'<n) [ k => N ]) | inl _ = v (k' , k'<n)
(v (k' , _) [ k => N ]) | inr _ = N
(A app B) [ k => N ] = (A [ k => N ]) app (B [ k => N ])
lam M [ k => N ] = lam (M [ suc k => shiftUp 1 0 N ])
