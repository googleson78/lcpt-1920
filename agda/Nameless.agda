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
