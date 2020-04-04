{-# OPTIONS --no-unicode #-}

module Lib.NatSet where

open import Lib.Nat
open import Lib.Two
open import Lib.Sum
open import Lib.Sigma
open import Lib.Eq
open import Lib.Zero
open import Lib.One

infixr 25 _,-_
data NatSet : Set where
  [] : NatSet
  _,-_ : Two -> NatSet -> NatSet
  -- a tt at index n means that the number n is in the set

-- "canonical" sets are sets that don't have "trailing" ffs
-- it's necessary to shrink sets when removing items, so that we can have properties like
-- xs Sub ys -> minus xs ys Sub []
data Can1 : NatSet -> Set where
  tt[] : Can1 (tt ,- [])
  can1-cons : {x : Two} {xs : NatSet} -> Can1 xs -> Can1 (x ,- xs)

Can1-[]-impossible : Can1 [] -> Zero
Can1-[]-impossible ()

data Can : NatSet -> Set where
  [] : Can []
  can1 : {xs : NatSet} -> Can1 xs -> Can xs

canonicalise : NatSet -> NatSet
canonicalise [] = []
canonicalise (tt ,- xs) = tt ,- canonicalise xs
canonicalise (ff ,- xs) with canonicalise xs
... | [] = []
... | xs'@(_ ,- _) = ff ,- xs'

canonicalise-Can : (xs : NatSet) -> Can (canonicalise xs)
canonicalise-Can [] = []
canonicalise-Can (tt ,- xs) with canonicalise xs | canonicalise-Can xs
... | .[] | [] = can1 tt[]
... | z | can1 x = can1 (can1-cons x)
canonicalise-Can (ff ,- xs)  with canonicalise xs | canonicalise-Can xs
... | .[] | [] = []
... | _ ,- _ | can1 x = can1 (can1-cons x)

size : NatSet -> Nat
size [] = 0
size (_ ,- xs) = suc (size xs)

empty : Nat -> NatSet
empty zero = []
empty (suc n) = ff ,- empty n

infix 50 [_]
[_] : (n : Nat) -> NatSet
[ zero ] = tt ,- []
[ suc n ] = ff ,- [ n ]

[_]-Can1 : (n : Nat) -> Can1 [ n ]
[ zero ]-Can1 = tt[]
[ suc n ]-Can1 = (can1-cons [ n ]-Can1)

union : NatSet -> NatSet -> NatSet
union [] ys = ys
union xs [] = xs
union (x ,- xs) (y ,- ys) = x || y ,- union xs ys

union-right-zero : (xs : NatSet) -> union xs [] == xs
union-right-zero [] = refl
union-right-zero (x ,- xs) = refl

union-commut : (xs ys : NatSet) -> union xs ys == union ys xs
union-commut [] ys rewrite union-right-zero ys = refl
union-commut (x ,- xs) [] = refl
union-commut (x ,- xs) (y ,- ys) rewrite union-commut xs ys | ||-commut x y = refl

union-preserves-Can1 : (xs ys : NatSet) -> Can1 xs -> Can1 ys -> Can1 (union xs ys)
union-preserves-Can1 (.tt ,- .[]) (.tt ,- .[]) tt[] tt[] = tt[]
union-preserves-Can1 (.tt ,- .[]) (y ,- ys) tt[] (can1-cons can1ys) = can1-cons can1ys
union-preserves-Can1 (x ,- xs) (.tt ,- .[]) (can1-cons can1xs) tt[] rewrite union-right-zero xs = can1-cons can1xs
union-preserves-Can1 (x ,- xs) (y ,- ys) (can1-cons can1xs) (can1-cons can1ys) = can1-cons (union-preserves-Can1 xs ys can1xs can1ys)

union-preserves-Can : (xs ys : NatSet) -> Can xs -> Can ys -> Can (union xs ys)
union-preserves-Can [] ys canxs canys = canys
union-preserves-Can xs [] canxs canys rewrite union-right-zero xs = canxs
union-preserves-Can (x ,- xs) (y ,- ys) (can1 canxs) (can1 canys) = can1 (union-preserves-Can1 (x ,- xs) (y ,- ys) canxs canys)

infixr 40 _<:_
_<:_ : Nat -> NatSet -> NatSet
x <: xs = union [ x ] xs

<:-preserves-Can1 : (n : Nat) (xs : NatSet) -> Can1 xs -> Can1 (n <: xs)
<:-preserves-Can1 n xs = union-preserves-Can1 [ n ] xs [ n ]-Can1

-- the "opposite" of implication
-- this is useful to reduce the cases we need to look at in a lot of places
-- by using decCoImplies in minus, instead of pattern matching
-- CoImplies gives unification hints
data CoImplies : Two -> Two -> Set where
  coim : CoImplies tt ff

not-CoImplies-Implies : {x y : Two} -> (CoImplies x y -> Zero) -> x ==> y
not-CoImplies-Implies {tt} {ff} not = naughtE (not coim)
not-CoImplies-Implies {ff} {ff} not = fx
not-CoImplies-Implies {ff} {tt} not = fx
not-CoImplies-Implies {tt} {tt} not = tt

decCoImplies : (x y : Two) -> Dec (CoImplies x y)
decCoImplies tt ff = inr coim
decCoImplies _ tt = inl (\ ())
decCoImplies ff _ = inl (\ ())

minus : NatSet -> NatSet -> NatSet
minus [] _ = []
minus xs [] = xs
minus (x ,- xs) (y ,- ys) with decCoImplies x y
... | inr coim = tt ,- minus xs ys
... | inl x1 with minus xs ys
... | [] = []
... | zs@(_ ,- _) = ff ,- zs

minus-[]-[] : (xs : NatSet) -> minus xs [] == xs
minus-[]-[] [] = refl
minus-[]-[] (x ,- xs) = refl

minus-preserves-Can : (xs ys : NatSet) -> Can xs -> Can (minus xs ys)
minus-preserves-Can [] _ _ = []
minus-preserves-Can xs [] canxs rewrite minus-[]-[] xs = canxs
minus-preserves-Can (.tt ,- .[]) (ff ,- ys) (can1 tt[]) = can1 tt[]
minus-preserves-Can (.tt ,- .[]) (tt ,- ys) (can1 tt[]) = []
minus-preserves-Can (x ,- xs) (y ,- ys) (can1 (can1-cons can1xs)) with decCoImplies x y
... | inl x2 with minus xs ys | minus-preserves-Can xs ys (can1 can1xs)
... | .[] | [] = []
... | z ,- zs | can1 can1zs = can1 (can1-cons can1zs)
minus-preserves-Can (x ,- xs) (y ,- ys) (can1 (can1-cons can1xs)) | inr coim with minus xs ys | minus-preserves-Can xs ys (can1 can1xs)
... | .[] | [] = can1 tt[]
... | zs | can1 can1zs = can1 (can1-cons can1zs)

delete : Nat -> NatSet -> NatSet
delete n m = minus m [ n ]

has : Nat -> NatSet -> Two
has n [] = ff
has zero (x ,- _) = x
has (suc n) (_ ,- xs) = has n xs

dec-has : (n : Nat) (xs : NatSet) -> Dec (So (has n xs))
dec-has n xs with has n xs
... | ff = inl (\ x -> x)
... | tt = inr <>

data _Has_ : NatSet -> Nat -> Set where
  here : {xs : NatSet} -> tt ,- xs Has 0
  there : {b : Two} {n : Nat} {xs : NatSet} -> xs Has n -> b ,- xs Has (suc n)

Has-unique : {xs : NatSet} {x : Nat} (has1 has2 : xs Has x) -> has1 == has2
Has-unique here here = refl
Has-unique (there has1) (there has2) rewrite Has-unique has1 has2 = refl

_HasSub_ : (xs ys : NatSet) -> Set
xs HasSub ys = (n : Nat) -> xs Has n -> ys Has n

Has-suc-inj : {x : Two} {xs : NatSet} {n : Nat} -> (xs Has n -> Zero) -> x ,- xs Has suc n -> Zero
Has-suc-inj {x} {xs} {n} noxshasn (there xxsHassucn) = noxshasn xxsHassucn

decHas : (xs : NatSet) (n : Nat) -> Dec (xs Has n)
decHas [] n = inl (\ ())
decHas (ff ,- xs) zero = inl (\ ())
decHas (tt ,- xs) zero = inr here
decHas (x ,- xs) (suc n) with decHas xs n
... | inl no = inl (Has-suc-inj no)
... | inr yes = inr (there yes)

[]-Has-impossible : (n : Nat) -> [] Has n -> Zero
[]-Has-impossible n ()

ffxs-Has-0-impossible : {xs : NatSet} -> (ff ,- xs) Has zero -> Zero
ffxs-Has-0-impossible ()

[_]-Has : (n : Nat) -> [ n ] Has n
[ zero ]-Has = here
[ suc n ]-Has = there [ n ]-Has

[_]-Has-eq : (n x : Nat) -> [ n ] Has x -> n == x
[ zero ]-Has-eq .0 here = refl
[ suc n ]-Has-eq (suc x) (there nhasx) = ap suc ([ n ]-Has-eq x nhasx)

<:-Has : (n : Nat) (xs : NatSet) -> n <: xs Has n
<:-Has n [] rewrite union-right-zero [ n ] = [ n ]-Has
<:-Has zero (x ,- xs) = here
<:-Has (suc n) (x ,- xs) = there (<:-Has n xs)

<:-monoL-Has : (n : Nat) (xs : NatSet) (x : Nat) -> xs Has n -> (x <: xs) Has n
<:-monoL-Has .0 .(tt ,- _) zero here = here
<:-monoL-Has .(suc _) .(_ ,- _) zero (there xsHasn) = there xsHasn
<:-monoL-Has .0 .(tt ,- _) (suc x) here = here
<:-monoL-Has (suc n) (_ ,- xs) (suc x) (there xsHasn) = there (<:-monoL-Has n xs x xsHasn)

<:-split-Has : (n : Nat) (xs : NatSet) (x : Nat) -> x <: xs Has n -> x == n + xs Has n
<:-split-Has zero xs zero xxsHasn = inl refl
<:-split-Has zero (tt ,- xs) (suc x) here = inr here
<:-split-Has (suc n) [] zero (there xxsHasn) = naughtE ([]-Has-impossible n xxsHasn)
<:-split-Has (suc n) (x ,- xs) zero (there xxsHasn) = inr (there xxsHasn)
<:-split-Has (suc n) [] (suc x) (there xxsHasn) rewrite [_]-Has-eq x n xxsHasn = inl refl
<:-split-Has (suc n) (x' ,- xs) (suc x) (there xxsHasn) with <:-split-Has n xs x xxsHasn
... | inl refl = inl refl
... | inr x1 = inr (there x1)

data _Sub_ : NatSet -> NatSet -> Set where
  sub-[] : {xs : NatSet} -> [] Sub xs
  sub-cons-im : {x y : Two} {xs ys : NatSet} -> x ==> y -> xs Sub ys -> x ,- xs Sub y ,- ys

Sub-unique : {xs ys : NatSet} (sub1 sub2 : xs Sub ys) -> sub1 == sub2
Sub-unique sub-[] sub-[] = refl
Sub-unique (sub-cons-im im1 sub1) (sub-cons-im im2 sub2) rewrite ==>-unique im1 im2 | Sub-unique sub1 sub2 = refl

Sub-[]-impossible : (x : Two) (xs : NatSet) -> x ,- xs Sub [] -> Zero
Sub-[]-impossible x xs ()

Can1-Sub-[]-impossible : (xs : NatSet) -> Can1 xs -> xs Sub [] -> Zero
Can1-Sub-[]-impossible .(tt ,- []) tt[] ()
Can1-Sub-[]-impossible .(_ ,- _) (can1-cons can1xs) ()

Sub-tt-ff-impossible : {xs ys : NatSet} -> tt ,- xs Sub ff ,- ys -> Zero
Sub-tt-ff-impossible (sub-cons-im () sub)

Sub-refl : {xs : NatSet} -> xs Sub xs
Sub-refl {[]} = sub-[]
Sub-refl {x ,- xs} = sub-cons-im ==>-refl Sub-refl

Sub-trans : {xs ys zs : NatSet} -> xs Sub ys -> ys Sub zs -> xs Sub zs
Sub-trans sub-[] ysSubzs = sub-[]
Sub-trans (sub-cons-im im1 xsSubys) (sub-cons-im im2 ysSubzs) = sub-cons-im (==>-trans im1 im2) (Sub-trans xsSubys ysSubzs)

union-monoL-Sub : (xs ys : NatSet) -> ys Sub union xs ys
union-monoL-Sub [] ys = Sub-refl
union-monoL-Sub (x ,- xs) [] = sub-[]
union-monoL-Sub (x ,- xs) (y ,- ys) = sub-cons-im (||-monoL-==> x y) (union-monoL-Sub xs ys)

Sub-both-Sub-union : {xs ys zs : NatSet} -> xs Sub zs -> ys Sub zs -> union xs ys Sub zs
Sub-both-Sub-union sub-[] ysSubzs = ysSubzs
Sub-both-Sub-union (sub-cons-im x xsSubys) sub-[] = sub-cons-im x xsSubys
Sub-both-Sub-union (sub-cons-im p xsSubys) (sub-cons-im q ysSubzs) = sub-cons-im (==>-|| p q) (Sub-both-Sub-union xsSubys ysSubzs)

Sub-union-SubL : (xs ys zs : NatSet) -> union xs ys Sub zs -> xs Sub zs
Sub-union-SubL [] ys zs sub = sub-[]
Sub-union-SubL (x ,- xs) [] zs sub = sub
Sub-union-SubL (x ,- xs) (y ,- ys) (z ,- zs) (sub-cons-im im sub) = sub-cons-im (||-==>-L x y z im) (Sub-union-SubL xs ys zs sub)

Sub-union-SubR : (xs ys zs : NatSet) -> union xs ys Sub zs -> ys Sub zs
Sub-union-SubR xs ys rewrite union-commut xs ys = Sub-union-SubL ys xs

Sub-minus-Sub-[] : (xs ys : NatSet) -> xs Sub ys -> minus xs ys Sub []
Sub-minus-Sub-[] [] ys xsSubys = sub-[]
Sub-minus-Sub-[] xs [] xsSubys rewrite minus-[]-[] xs = xsSubys
Sub-minus-Sub-[] (x ,- xs) (y ,- ys) (sub-cons-im x1 xsSubys) with decCoImplies x y
Sub-minus-Sub-[] (.tt ,- xs) (.ff ,- ys) (sub-cons-im () xsSubys) | inr coim
... | inl x2 with minus xs ys | Sub-minus-Sub-[] xs ys xsSubys
... | .[] | sub-[] = sub-[]

firstNotIn : NatSet -> Nat
firstNotIn [] = zero
firstNotIn (ff ,- xs) = zero
firstNotIn (tt ,- xs) = suc (firstNotIn xs)

nonEmpty : (xs : NatSet) -> Can1 xs -> Nat
nonEmpty .(tt ,- []) tt[] = zero
nonEmpty (ff ,- xs) (can1-cons canxs1) = suc (nonEmpty xs canxs1)
nonEmpty (tt ,- xs) (can1-cons canxs1) = zero

nonEmpty-Sub : (xs : NatSet) -> (can : Can1 xs) -> xs Has nonEmpty xs can
nonEmpty-Sub (.tt ,- .[]) tt[] = here
nonEmpty-Sub (ff ,- xs) (can1-cons can) = there (nonEmpty-Sub xs can)
nonEmpty-Sub (tt ,- xs) (can1-cons can) = here

Has-Sub-impossible : (n : Nat) (xs : NatSet) -> (xs Has n) -> xs Sub [] -> Zero
Has-Sub-impossible n .[] () sub-[]

decEmpty : (xs : NatSet) -> Can xs -> xs == [] + Nat >< (_Has_ xs)
decEmpty .[] [] = inl refl
decEmpty (.tt ,- .[]) (can1 tt[]) = inr (zero , here)
decEmpty (x ,- xs) (can1 (can1-cons can1xs)) with decEmpty xs (can1 (can1xs))
decEmpty (ff ,- .[]) (can1 (can1-cons ())) | inl refl
decEmpty (tt ,- .[]) (can1 (can1-cons can1xs)) | inl refl = inr (zero , here)
... | inr (n , has) = inr (suc n , there has)

Has-uncons : forall {x y xs ys} -> (x ,- xs HasSub y ,- ys) -> xs HasSub ys
Has-uncons has 0 here with has 1 (there here)
... | there z = z
Has-uncons {x} {y} {b ,- xs} {ys} has (suc n) (there xsHasn) with has (suc (suc n)) (there (there xsHasn))
... | there (there z) = there z

all-Has-Sub : (xs ys : NatSet) -> Can xs -> ((n : Nat) -> xs Has n -> ys Has n) -> xs Sub ys
all-Has-Sub [] ys canxs hasall = sub-[]
all-Has-Sub xs [] canxs hasall with decEmpty xs canxs
... | inl refl = sub-[]
... | inr (n , has) = naughtE ([]-Has-impossible n (hasall n has))
all-Has-Sub (.tt ,- .[]) (ff ,- ys) (can1 tt[]) hasall = naughtE (ffxs-Has-0-impossible (hasall zero here))
all-Has-Sub (.tt ,- .[]) (tt ,- ys) (can1 tt[]) hasall = sub-cons-im tt sub-[]
all-Has-Sub (x ,- xs) (y ,- ys) (can1 (can1-cons can1xs)) hasall with decCoImplies x y
... | inr coim = naughtE (ffxs-Has-0-impossible (hasall zero here))
... | inl notcoim with all-Has-Sub xs ys (can1 can1xs) (Has-uncons hasall)
... | sub-cons-im im z = sub-cons-im (not-CoImplies-Implies notcoim) (sub-cons-im im z)

union-adjoint-minus : (xs ys zs : NatSet) -> xs Sub union ys zs -> minus xs ys Sub zs
union-adjoint-minus xs ys [] xsSubunionyszs rewrite union-right-zero ys = Sub-minus-Sub-[] xs ys xsSubunionyszs
union-adjoint-minus [] ys zs xsSubunionyszs = sub-[]
union-adjoint-minus (x ,- xs) [] zs xsSubunionyszs = xsSubunionyszs
union-adjoint-minus (x ,- xs) (y ,- ys) (z ,- zs) (sub-cons-im im xsSubunionyszs) with decCoImplies x y
union-adjoint-minus (.tt ,- xs) (.ff ,- ys) (tt ,- zs) (sub-cons-im im xsSubunionyszs) | inr coim = sub-cons-im im (union-adjoint-minus xs ys zs xsSubunionyszs)
... | inl x1 with minus xs ys | union-adjoint-minus xs ys zs xsSubunionyszs
... | [] | rec = sub-[]
... | z' ,- zs' | rec = sub-cons-im fx rec

Canxs-Sub-[]-==[] : (xs : NatSet) -> Can xs -> xs Sub [] -> xs == []
Canxs-Sub-[]-==[] .[] [] sub-[] = refl

decSub : (xs ys : NatSet) -> Can xs -> Can1 (minus xs ys) + xs Sub ys
decSub [] ys canxs = inr sub-[]
decSub xs [] (can1 can1xs) rewrite minus-[]-[] xs = inl can1xs
decSub (.tt ,- .[]) (ff ,- ys) (can1 tt[]) = inl tt[]
decSub (.tt ,- .[]) (tt ,- ys) (can1 tt[]) = inr (sub-cons-im tt sub-[])
decSub (x ,- xs) (y ,- ys) (can1 (can1-cons can1xs)) with decCoImplies x y | decSub xs ys (can1 can1xs)
... | inr coim | inl nosub = inl (can1-cons nosub)
... | inr coim | inr yessub
                 rewrite Canxs-Sub-[]-==[]
                           (minus xs ys)
                           (minus-preserves-Can xs ys (can1 can1xs))
                           (Sub-minus-Sub-[] xs ys yessub)
                 = inl tt[]
... | inl nocoim | inr xsSubys = inr (sub-cons-im (not-CoImplies-Implies nocoim) xsSubys)
... | inl nocoim | inl can1zzs with minus xs ys
... | z ,- zs = inl (can1-cons can1zzs)

minus-Sub-[]-Sub : (xs ys : NatSet) -> Can xs -> minus xs ys Sub [] -> xs Sub ys
minus-Sub-[]-Sub xs ys canxs sub with decSub xs ys canxs
... | inr yes = yes
... | inl canzs rewrite Canxs-Sub-[]-==[] (minus xs ys) (minus-preserves-Can xs ys canxs) sub
  = naughtE (Can1-[]-impossible canzs)

-- ;_;
-- the last cases are copy and pasted (some of them literally..)
minus-minus-minus-union : (xs ys zs : NatSet) -> minus xs (union ys zs) == minus (minus xs ys) zs
minus-minus-minus-union [] ys zs = refl
minus-minus-minus-union xs [] zs rewrite minus-[]-[] xs = refl
minus-minus-minus-union xs ys [] rewrite minus-[]-[] (minus xs ys) | union-right-zero ys = refl
minus-minus-minus-union (tt ,- xs) (ff ,- ys) (ff ,- zs) = ap (tt ,-_) (minus-minus-minus-union xs ys zs)
minus-minus-minus-union (tt ,- xs) (ff ,- ys) (tt ,- zs) rewrite minus-minus-minus-union xs ys zs with minus xs (union ys zs)
... | [] = refl
... | x ,- w = refl
minus-minus-minus-union (ff ,- xs) (ff ,- ys) (ff ,- zs) with minus xs (union ys zs) | minus xs ys | minus-minus-minus-union xs ys zs
... | [] | [] | rec = refl
... | [] | x ,- w | rec with minus (x ,- w) zs
... | [] = refl
minus-minus-minus-union (ff ,- xs) (ff ,- ys) (ff ,- zs) | x ,- q | x1 ,- w | rec with minus (x1 ,- w) zs
minus-minus-minus-union (ff ,- xs) (ff ,- ys) (ff ,- zs) | .x2 ,- .e | x1 ,- w | refl | x2 ,- e = refl
minus-minus-minus-union (ff ,- xs) (ff ,- ys) (tt ,- zs) with minus xs (union ys zs) | minus xs ys | minus-minus-minus-union xs ys zs
... | [] | [] | rec = refl
... | [] | x ,- w | rec with minus (x ,- w) zs
... | [] = refl
minus-minus-minus-union (ff ,- xs) (ff ,- ys) (tt ,- zs) | x ,- q | x1 ,- w | rec with minus (x1 ,- w) zs
minus-minus-minus-union (ff ,- xs) (ff ,- ys) (tt ,- zs) | .x2 ,- .e | x1 ,- w | refl | x2 ,- e = refl
minus-minus-minus-union (ff ,- xs) (tt ,- ys) (ff ,- zs) with minus xs (union ys zs) | minus xs ys | minus-minus-minus-union xs ys zs
... | [] | [] | rec = refl
... | [] | x ,- w | rec with minus (x ,- w) zs
... | [] = refl
minus-minus-minus-union (ff ,- xs) (tt ,- ys) (ff ,- zs) | x ,- q | x1 ,- w | rec with minus (x1 ,- w) zs
minus-minus-minus-union (ff ,- xs) (tt ,- ys) (ff ,- zs) | .x2 ,- .lol | x1 ,- w | refl | x2 ,- lol = refl
minus-minus-minus-union (ff ,- xs) (tt ,- ys) (tt ,- zs) with minus xs (union ys zs) | minus xs ys | minus-minus-minus-union xs ys zs
... | [] | [] | rec = refl
... | [] | x ,- w | rec with minus (x ,- w) zs
... | [] = refl
minus-minus-minus-union (ff ,- xs) (tt ,- ys) (tt ,- zs) | x ,- q | x1 ,- w | rec with minus (x1 ,- w) zs
minus-minus-minus-union (ff ,- xs) (tt ,- ys) (tt ,- zs) | .x2 ,- .lol | x1 ,- w | refl | x2 ,- lol = refl
minus-minus-minus-union (tt ,- xs) (tt ,- ys) (ff ,- zs) with minus xs (union ys zs) | minus xs ys | minus-minus-minus-union xs ys zs
... | [] | [] | rec = refl
... | [] | x ,- w | rec with minus (x ,- w) zs
... | [] = refl
minus-minus-minus-union (tt ,- xs) (tt ,- ys) (ff ,- zs) | x ,- q | x1 ,- w | rec with minus (x1 ,- w) zs
minus-minus-minus-union (tt ,- xs) (tt ,- ys) (ff ,- zs) | .x2 ,- .lol | x1 ,- w | refl | x2 ,- lol = refl
minus-minus-minus-union (tt ,- xs) (tt ,- ys) (tt ,- zs) with minus xs (union ys zs) | minus xs ys | minus-minus-minus-union xs ys zs
... | [] | [] | rec = refl
... | [] | x ,- w | rec with minus (x ,- w) zs
... | [] = refl
minus-minus-minus-union (tt ,- xs) (tt ,- ys) (tt ,- zs) | x ,- q | x1 ,- w | rec with minus (x1 ,- w) zs
minus-minus-minus-union (tt ,- xs) (tt ,- ys) (tt ,- zs) | .x2 ,- .lol | x1 ,- w | refl | x2 ,- lol = refl

minus-adjoint-union : (xs ys zs : NatSet) -> Can xs -> minus xs ys Sub zs -> xs Sub union ys zs
minus-adjoint-union xs ys zs canxs sub with decSub xs (union ys zs) canxs
... | inr x = x
... | inl x rewrite minus-minus-minus-union xs ys zs
  = naughtE (Can1-Sub-[]-impossible (minus (minus xs ys) zs) x (Sub-minus-Sub-[] (minus xs ys) zs sub))

Has-Sub-trans : (x : Nat) (xs ys : NatSet) -> xs Has x -> xs Sub ys -> ys Has x
Has-Sub-trans .0 .(tt ,- _) .(tt ,- _) here (sub-cons-im tt xsSubys) = here
Has-Sub-trans (suc n) (_ ,- xs) (_ ,- ys) (there xsHasx) (sub-cons-im x xsSubys) = there (Has-Sub-trans n xs ys xsHasx xsSubys)

noHasSuc : (y : Two) (ys : NatSet) (n : Nat) -> ((y ,- ys) Has suc n -> Zero) -> ys Has n -> Zero
noHasSuc y ys n nohassuc has = nohassuc (there has)

minus-no-has-has : (n : Nat) (xs ys : NatSet) -> xs Has n -> (ys Has n -> Zero) -> minus xs ys Has n
minus-no-has-has n (x ,- xs) [] xshas ysnohas = xshas
minus-no-has-has .0 (.tt ,- xs) (ff ,- ys) here ysnohas with minus xs ys
... | [] = here
... | x ,- z = here
minus-no-has-has .0 (.tt ,- xs) (tt ,- ys) here ysnohas = naughtE (ysnohas here)
minus-no-has-has (suc n) (x ,- xs) (y ,- ys) (there xshas) ysnohas with decCoImplies x y
... | inr coim = there (minus-no-has-has n xs ys xshas (noHasSuc ff ys n ysnohas))
... | inl nocoim with minus xs ys | minus-no-has-has n xs ys xshas (noHasSuc y ys n ysnohas)
... | x1 ,- q | rec = there rec

delete-adjoint-<: : (n : Nat) (xs ys : NatSet) -> Can xs -> delete n xs Sub ys -> xs Sub n <: ys
delete-adjoint-<: n xs ys = minus-adjoint-union xs [ n ] ys

<:-Sub-[]-impossible : (x : Nat) (xs : NatSet) -> x <: xs Sub [] -> Zero
<:-Sub-[]-impossible zero [] ()
<:-Sub-[]-impossible zero (x ,- xs) ()
<:-Sub-[]-impossible (suc x) [] ()
<:-Sub-[]-impossible (suc x) (x1 ,- xs) ()

<:adjoint-delete : (n : Nat) (xs ys : NatSet) -> xs Sub n <: ys -> delete n xs Sub ys
<:adjoint-delete n xs ys = union-adjoint-minus xs [ n ] ys

sing-Sub-Has : (n : Nat) (xs : NatSet) -> [ n ] Sub xs -> xs Has n
sing-Sub-Has (suc n) [] ()
sing-Sub-Has zero (.tt ,- xs) (sub-cons-im tt sub) = here
sing-Sub-Has (suc n) (x ,- xs) (sub-cons-im fx sub) = there (sing-Sub-Has n xs sub)

sub-has : (xs ys : NatSet) -> xs Sub ys -> (x : Nat) -> xs Has x -> ys Has x
sub-has .(tt ,- _) .(tt ,- _) (sub-cons-im tt xsSubys) .0 here = here
sub-has (_ ,- xs) (_ ,- ys) (sub-cons-im x xsSubys) (suc n) (there xsHasx) = there (sub-has xs ys xsSubys n xsHasx)

[_]-has : (x : Nat) -> So (has x [ x ])
[_]-has zero = <>
[_]-has (suc x) = [_]-has x

<:-has : (n : Nat) (xs : NatSet) -> So (has n (n <: xs))
<:-has zero [] = <>
<:-has zero (x ,- xs) = <>
<:-has (suc n) [] = [_]-has n
<:-has (suc n) (x ,- xs) = <:-has n xs

sing-sub-add : (n : Nat) (xs : NatSet) -> [ n ] Sub (n <: xs)
sing-sub-add zero [] = sub-cons-im tt sub-[]
sing-sub-add zero (x ,- xs) = sub-cons-im tt sub-[]
sing-sub-add (suc n) [] = sub-cons-im fx Sub-refl
sing-sub-add (suc n) (x ,- xs) = sub-cons-im fx (sing-sub-add n xs)

add-Sub : (n : Nat) (xs : NatSet) -> xs Sub n <: xs
add-Sub zero [] = sub-[]
add-Sub zero (x ,- xs) = sub-cons-im ==>tt Sub-refl
add-Sub (suc n) [] = sub-[]
add-Sub (suc n) (x ,- xs) rewrite ||-idL {x} = sub-cons-im ==>-refl (union-monoL-Sub [ n ] xs)

-- "tests"
_ : firstNotIn (1 <: [ 2 ]) == 0
_ = refl

_ : firstNotIn (0 <: 1 <: [ 2 ]) == 3
_ = refl

_ : delete 4 [ 3 ] == [ 3 ]
_ = refl

_ : delete 3 [ 3 ] == []
_ = refl

_ : delete 0 [ 0 ] == []
_ = refl

_ : delete 2 [ 3 ] == [ 3 ]
_ = refl

_ : delete 2 (1 <: 2 <: 3 <: [ 3 ]) == (1 <: 3 <: [ 3 ])
_ = refl

_ : delete 2 (1 <: 2 <: 3 <: 2 <: 1 <: [ 3 ]) == (1 <: 3 <: [ 3 ])
_ = refl
