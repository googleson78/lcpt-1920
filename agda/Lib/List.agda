{-# OPTIONS --no-unicode #-}

module Lib.List where

open import Lib.Zero
open import Lib.One
open import Lib.Sigma
open import Lib.Sum
open import Lib.Eq
open import Lib.Nat

variable
  A : Set

infixr 50 _,-_
data List (A : Set) : Set where
  [] : List A
  _,-_ : A -> List A -> List A

length : List A -> Nat
length [] = 0
length (x ,- xs) = suc (length xs)

infixr 40 _+L_
_+L_ : List A -> List A -> List A
[] +L ys = ys
(x ,- xs) +L ys = x ,- (xs +L ys)

--_+Ls_ : List A -> List A -> List A
--xs +Ls ys = {!!}

infix 20 _In_
data _In_ (x : A) : List A -> Set where
  here : {xs : List A} -> x In (x ,- xs)
  there : {y : A} {ys : List A} -> x In ys -> x In (y ,- ys)

NoDup : List A -> Set
NoDup {A} xs = {x : A} (in1 in2 : x In xs) -> in1 == in2

NoDup-uncons : {x : A} {xs : List A} -> NoDup (x ,- xs) -> NoDup xs
NoDup-uncons NoDupxxs in1 in2 with NoDupxxs (there in1) (there in2)
... | refl = refl

NoDup-cons : (x : A) (xs : List A) -> NoDup xs -> (x In xs -> Zero) -> NoDup (x ,- xs)
NoDup-cons x xs nodup xnInxs here here = refl
NoDup-cons x xs nodup xnInxs here (there in2) = naughtE (xnInxs in2)
NoDup-cons x xs nodup xnInxs (there in1) here = naughtE (xnInxs in1)
NoDup-cons x xs nodup xnInxs (there in1) (there in2) rewrite nodup in1 in2 = refl

nowhere : {x y : A} {ys : List A} -> (x == y -> Zero) -> (x In ys -> Zero) -> x In y ,- ys -> Zero
nowhere x/=y xNotInYs here = x/=y refl
nowhere x/=y xNotInYs (there z) = xNotInYs z

nothingIn[] : {x : A} -> x In [] -> Zero
nothingIn[] ()

+L-monoL-In : {y : A} {ys : List A} -> (xs : List A) -> y In ys -> y In xs +L ys
+L-monoL-In [] yInys = yInys
+L-monoL-In (x ,- xs) yInys = there (+L-monoL-In xs yInys)

index : (xs : List A) -> Fin (length xs) -> A
index [] (zero , _ , 0/=0) = naughtE (0/=0 refl)
index (x ,- _) (zero , n<len) = x
index (_ ,- xs) (suc n , sucn<len) = index xs (n , <-rev-osuc sucn<len)

index-In : (xs : List A) -> (n : Fin (length xs)) -> index xs n In xs
index-In [] (n , n<zero) = naughtE (<-zero-impossible n<zero)
index-In (x ,- xs) (zero , n<suclen) = here
index-In (x ,- xs) (suc n , n<suclen) = there (index-In xs (n , <-rev-osuc n<suclen))

indexOf : {xs : List A} {x : A} -> x In xs -> Fin (length xs)
indexOf here = zero , ozero , (\ ())
indexOf (there xInxs) with indexOf xInxs
... | n , n<lengthxs = suc n , <-osuc n<lengthxs

indexOf-index-id : (xs : List A) (x : Fin (length xs)) -> FinEq x (indexOf (index-In xs x))
indexOf-index-id {_} [] (n , n<zero) = naughtE (<-zero-impossible n<zero)
indexOf-index-id {_} (x ,- xs) (zero , n<suclen) = refl
indexOf-index-id {_} (x ,- xs) (suc n , n<suclen) = ap suc (indexOf-index-id xs (n , <-rev-osuc n<suclen))

find : {{eqA : Eq A}} (x : A) (xs : List A) -> Dec (x In xs)
find x [] = inl (\ ())
find x (y ,- xs) with dec x y
... | inr refl = inr here
... | inl no with find x xs
... | inl notail = inl (nowhere no notail)
... | inr yes = inr (there yes)

data _EmbedsIn_ : List A -> List A -> Set where
  e[] : _EmbedsIn_ {A} [] []
  e-cons : {x : A} {xs ys : List A} -> xs EmbedsIn ys -> (x ,- xs) EmbedsIn (x ,- ys)
  e-skip : {x : A} {xs ys : List A} -> xs EmbedsIn ys -> xs EmbedsIn (x ,- ys)

EmbedsIn-trans : {xs ys zs : List A} -> xs EmbedsIn ys -> ys EmbedsIn zs -> xs EmbedsIn zs
EmbedsIn-trans xsEys e[] = xsEys
EmbedsIn-trans (e-cons xsEys) (e-cons ysEzs) = e-cons (EmbedsIn-trans xsEys ysEzs)
EmbedsIn-trans (e-skip xsEys) (e-cons ysEzs) = e-skip (EmbedsIn-trans xsEys ysEzs)
EmbedsIn-trans xsEys (e-skip ysEzs) = e-skip (EmbedsIn-trans xsEys ysEzs)

e[]-all : {xs : List A} -> [] EmbedsIn xs
e[]-all {_} {[]} = e[]
e[]-all {_} {x ,- xs} = e-skip e[]-all

e-refl : {xs : List A} -> xs EmbedsIn xs
e-refl {_} {[]} = e[]
e-refl {_} {x ,- xs} = e-cons e-refl

+L-monoL-EmbedsIn : {xs ys : List A} -> xs EmbedsIn (xs +L ys)
+L-monoL-EmbedsIn {_} {[]} {ys} = e[]-all
+L-monoL-EmbedsIn {_} {x ,- xs} {ys} = e-cons +L-monoL-EmbedsIn

+L-monoR-EmbedsIn : {xs ys : List A} -> xs EmbedsIn (ys +L xs)
+L-monoR-EmbedsIn {_} {xs} {[]} = e-refl
+L-monoR-EmbedsIn {_} {xs} {y ,- ys} = e-skip +L-monoR-EmbedsIn

+L-splits-In : {x : A} (xs ys : List A) -> x In xs +L ys -> x In xs + x In ys
+L-splits-In [] ys xInxs+Lys = inr xInxs+Lys
+L-splits-In (x ,- xs) ys here = inl here
+L-splits-In (x1 ,- xs) ys (there inapp) with +L-splits-In xs ys inapp
... | inl inxs = inl (there inxs)
... | inr inys = inr inys

+L-right-zero : (xs : List A) -> xs +L [] == xs
+L-right-zero [] = refl
+L-right-zero (x ,- xs) rewrite +L-right-zero xs = refl

remove : {{eqA : Eq A}} -> (x : A) -> (xs : List A) -> List A
remove x [] = []
remove x (y ,- xs) with dec x y
... | inl no = y ,- remove x xs
... | inr refl = remove x xs

remove-x-No-x : {{eqA : Eq A}} {x : A} (xs : List A) -> x In remove x xs -> Zero
remove-x-No-x {_} {x} (y ,- ys) xInRemovex with dec x y
... | inr refl = remove-x-No-x ys xInRemovex
remove-x-No-x {_} {.y} (y ,- ys) here | inl x/=y = x/=y refl
remove-x-No-x {_} {x} (y ,- ys) (there xInRemovex) | inl x/=y = remove-x-No-x ys xInRemovex

remove-x-Has-All-Not-x : {{eqA : Eq A}} {x : A} {xs : List A} (y : A) -> y In xs -> (x == y -> Zero) -> y In remove x xs
remove-x-Has-All-Not-x {_} {x} {y ,- xs} .y here x/=y with dec x y
... | inl x1 = here
... | inr refl = naughtE (x/=y refl)
remove-x-Has-All-Not-x {_} {x} {y ,- xs} z (there zInxs) x/=z with dec x y
... | inl x1 = there (remove-x-Has-All-Not-x z zInxs x/=z)
... | inr refl = remove-x-Has-All-Not-x z zInxs x/=z

_Sub_ : (xs ys : List A) -> Set
_Sub_ {A} xs ys = {x : A} -> x In xs -> x In ys

infix 25 _Sub_

[]-Sub : {xs : List A} -> [] Sub xs
[]-Sub = \ ()

Sub-refl : {xs : List A} -> xs Sub xs
Sub-refl = \ z -> z

Sub-suc : {x : A} {xs ys : List A} -> xs Sub ys -> x ,- xs Sub x ,- ys
Sub-suc xsSubys = \{ here -> here ; (there zInxxs) -> there (xsSubys zInxxs)}

Sub-grow : {y : A} {xs ys : List A} -> xs Sub ys -> xs Sub y ,- ys
Sub-grow xsSubys = \ zInxs -> there (xsSubys zInxs)

+L-monoR-Sub : (xs ys : List A) -> xs Sub xs +L ys
+L-monoR-Sub [] ys = []-Sub
+L-monoR-Sub (x ,- xs) ys = Sub-suc (+L-monoR-Sub xs ys)

+L-monoL-Sub : (xs ys : List A) -> ys Sub xs +L ys
+L-monoL-Sub xs ys = \ x1 -> +L-monoL-In xs x1

Sub-+L-both-Sub : {xs ys zs : List A} -> xs Sub zs -> ys Sub zs -> xs +L ys Sub zs
Sub-+L-both-Sub {_} {xs} {ys} xsSubzs ysSubzs zInxs+Lys with +L-splits-In xs ys zInxs+Lys
... | inl x = xsSubzs x
... | inr x = ysSubzs x

Sub-trans : {xs ys zs : List A} -> xs Sub ys -> ys Sub zs -> xs Sub zs
Sub-trans xsSubys ysSubzs = \ z -> ysSubzs (xsSubys z)

remove-Adjoint,- : {{eqA : Eq A}} {x : A} {xs ys : List A} -> remove x xs Sub ys -> xs Sub x ,- ys
remove-Adjoint,- {_} {x} {xs} {ys} sub {y} yInxs with dec x y
... | inr refl = here
... | inl x/=y = there (sub (remove-x-Has-All-Not-x y yInxs x/=y))

remove-is-Sub : {{eqA : Eq A}} {x : A} (xs : List A) -> remove x xs Sub xs
remove-is-Sub {_} {x} (z ,- xs) {y} sub with dec x y
... | inr refl = naughtE (remove-x-No-x (z ,- xs) sub)
... | inl x/=y with dec x z
remove-is-Sub {_} {x} (z ,- xs) {.z} here | inl x/=y | inl x/=z = here
remove-is-Sub {_} {x} (z ,- xs) {y} (there sub) | inl x/=y | inl x/=z = there (remove-is-Sub xs sub)
... | inr refl = there (remove-is-Sub xs sub)

,-Adjoint-remove : {{eqA : Eq A}} {x : A} {xs ys : List A} -> xs Sub x ,- ys -> remove x xs Sub ys
,-Adjoint-remove {_} {x} {xs} {ys} xsSubxys {y} yInremovexxs with dec x y
... | inr refl = naughtE (remove-x-No-x xs yInremovexxs)
... | inl x/=y with xsSubxys (remove-is-Sub xs yInremovexxs)
... | here = naughtE (x/=y refl)
... | there z = z

largest : (xs : List Nat) -> Nat
largest [] = 0
largest (x ,- xs) = max x (largest xs)

largest-<=-all : (xs : List Nat) -> (n : Nat) -> n In xs -> n <= largest xs
largest-<=-all (.n ,- xs) n here = max-monoR-<= n (largest xs)
largest-<=-all (x ,- xs) n (there ninxs) = <=-trans (largest-<=-all xs n ninxs) (max-monoL-<= (largest xs) x)

firstNotIn : List Nat -> Nat
firstNotIn xs = suc (largest xs)

firstNotIn-/=-All : (xs : List Nat) -> (x : Nat) -> x In xs -> x == firstNotIn xs -> Zero
firstNotIn-/=-All xs x xInxs x==suclargest with <=-<-trans (largest-<=-all xs x xInxs) <-suc
... | _ , x/=suclargest = x/=suclargest x==suclargest

firstNotIn-not-In : (xs : List Nat) -> firstNotIn xs In xs -> Zero
firstNotIn-not-In xs inxs = firstNotIn-/=-All xs (firstNotIn xs) inxs refl

firstNotIn-preserves-NoDup : (xs : List Nat) -> NoDup xs -> NoDup (firstNotIn xs ,- xs)
firstNotIn-preserves-NoDup xs noDup = NoDup-cons (suc (largest xs)) xs noDup (firstNotIn-not-In xs)
