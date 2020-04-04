{-# OPTIONS --no-unicode #-}

module Nameless where

open import Lib.One
open import Lib.Two
open import Lib.Nat
open import Lib.Sigma
open import Lib.Eq
open import Lib.Zero
open import Lib.Sum
import Lib.List as List
open List using (List; []; _,-_; length; index; indexOf; _In_; index-In)
import Lib.NatSet as S
open S renaming (_,-_ to _s,-_)

data Nameless (n : Nat) : Set where
  v : Fin n -> Nameless n
  _app_ : Nameless n -> Nameless n -> Nameless n
  lam : Nameless (suc n) -> Nameless n

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
v (k' , _) [ k => N ] with dec k k'
(v (k' , k'<n) [ k => N ]) | inl _ = v (k' , k'<n)
(v (k' , _) [ k => N ]) | inr _ = N
(A app B) [ k => N ] = (A [ k => N ]) app (B [ k => N ])
lam M [ k => N ] = lam (M [ suc k => shiftUp 1 0 N ])

-- sanity checks
_ :
  NamelessEq
    (lam {1} (v (fin 0)) [ 0 => v (fin 0) ])
    (lam {1} (v (fin 0)))
_ = refl

_ :
  NamelessEq
    (v (fin 0) app lam {2} (v (fin 0)) [ 0 => v (fin 0) ])
    (v (fin 0) app lam {2} (v (fin 0)))
_ = refl , refl

_ :
  NamelessEq
    (lam {1} (v (fin 1) app v (fin 0)) [ 0 => v (fin 0) ])
    (lam {1} (v (fin 1) app v (fin 0)))
_ = refl , refl

_ :
  NamelessEq
    (lam {3} (v (fin 1) app v (fin 0)) [ 0 => v (fin 1) ])
    (lam {3} (v (fin 2) app v (fin 0)))
_ = refl , refl

open import Lambda renaming (_[_=>_] to _n[_=>_])

dom : List Nat -> NatSet
dom [] = []
dom (x ,- xs) = x <: dom xs

index-sub-dom : (ctxt : List Nat) -> (x : Fin (length ctxt)) -> [ index ctxt x ] Sub dom ctxt
index-sub-dom [] (n , n<0) = naughtE (<-zero-impossible n<0)
index-sub-dom (x ,- ctxt) (zero , n<suclen) = sing-sub-add x (dom ctxt)
index-sub-dom (x ,- ctxt) (suc n , n<suclen) = Sub-trans (index-sub-dom ctxt (n , <-rev-osuc n<suclen)) (add-Sub x (dom ctxt))

in-has-dom : (n : Nat) (xs : List Nat) -> n In xs -> dom xs Has n
in-has-dom n (n ,- xs) _In_.here = <:-Has n (dom xs)
in-has-dom n (y ,- ys) (_In_.there xInxs) = <:-monoL-Has n (dom ys) y (in-has-dom n ys xInxs)

dom-has-in : (n : Nat) (xs : List Nat) -> dom xs Has n -> n In xs
dom-has-in n (x ,- xs) sub with <:-split-Has n (dom xs) x sub
... | inl refl = _In_.here
... | inr domxsHasn = _In_.there (dom-has-in n xs domxsHasn)

sing-sub-dom-in : (ctxt : List Nat) (n : Nat) -> [ n ] Sub dom ctxt -> n In ctxt
sing-sub-dom-in ctxt n sub = dom-has-in n ctxt (sing-Sub-Has n (dom ctxt) sub)

christen : (ctxt : List Nat) -> Nameless (length ctxt) -> Lambda sizeInf
christen ctxt (v x) = v (index ctxt x)
christen ctxt (M app N) = christen ctxt M app christen ctxt N
christen ctxt (lam M) = lam List.firstNotIn ctxt > christen (List.firstNotIn ctxt ,- ctxt) M

christen-freeVars : (ctxt : List Nat) -> (M : Nameless (length ctxt)) -> freeVars (christen ctxt M) Sub (dom ctxt)
christen-freeVars ctxt (v x) = index-sub-dom ctxt x
christen-freeVars ctxt (M app N) =
  Sub-both-Sub-union
    (christen-freeVars ctxt M)
    (christen-freeVars ctxt N)
christen-freeVars ctxt (lam M) =
  <:adjoint-delete
    (List.firstNotIn ctxt)
    (freeVars (christen (List.firstNotIn ctxt ,- ctxt) M))
    (dom ctxt)
    (christen-freeVars (List.firstNotIn ctxt ,- ctxt) M)

satanise : {i : Size} -> (ctxt : List Nat) -> (M : Lambda i) -> freeVars M Sub dom ctxt -> Nameless (length ctxt)
satanise ctxt (v n) sub = v (indexOf (sing-sub-dom-in ctxt n sub))
satanise ctxt (M app N) sub =
  satanise ctxt M (Sub-union-SubL (freeVars M) (freeVars N) (dom ctxt) sub)
  app
  satanise ctxt N (Sub-union-SubR (freeVars M) (freeVars N) (dom ctxt) sub)
satanise ctxt (lam x > M) sub = lam (satanise (x ,- ctxt) M (delete-adjoint-<: x (freeVars M) (dom ctxt) (freeVars-Can M) sub))

indexOf-sing-sub-dom-in-index-id : (ctxt : List Nat) -> List.NoDup ctxt -> (n : Fin (length ctxt)) -> FinEq n (indexOf (sing-sub-dom-in ctxt (index ctxt n) (index-sub-dom ctxt n)))
indexOf-sing-sub-dom-in-index-id [] noDup (n , n<0) = naughtE (<-zero-impossible n<0)
indexOf-sing-sub-dom-in-index-id (x ,- ctxt) noDup (zero , n<suclen) rewrite noDup (sing-sub-dom-in (x ,- ctxt) x (sing-sub-add x (dom ctxt))) _In_.here = refl
indexOf-sing-sub-dom-in-index-id (x ,- ctxt) noDup (suc n , n<suclen) with
-- look at where inserting n in xs has put us
  <:-split-Has
    (index ctxt (n , <-rev-osuc n<suclen))
    (dom ctxt)
    x
    (sing-Sub-Has
      (index ctxt (n , <-rev-osuc n<suclen))
      (union [ x ] (dom ctxt))
      (Sub-trans (index-sub-dom ctxt (n , <-rev-osuc n<suclen)) (add-Sub x (dom ctxt))))
-- either it's somewhere in xs, and we need to do a recursive step
... | inr x1
  rewrite
    Has-unique
      x1
      (sing-Sub-Has
        (index ctxt (n , <-rev-osuc n<suclen))
        (dom ctxt)
        (index-sub-dom ctxt (n , <-rev-osuc n<suclen)))
    = ap suc (indexOf-sing-sub-dom-in-index-id ctxt (List.NoDup-uncons noDup) (n , <-rev-osuc n<suclen))
-- or it's at the head of the new xs - but that's impossible, because there are no duplicates in the list
-- and we know that it's actually somewhere in xs, because when we index with suc n, it's definitely not at the head
-- information about this comes from index-In, which provides the proof that the result of an index was in the list we indexed
... | inl refl with noDup _In_.here (index-In (x ,- ctxt) ((suc n , n<suclen)))
... | ()

satanise-christen-id : (ctxt : List Nat) -> List.NoDup ctxt -> (M : Nameless (length ctxt)) -> NamelessEq M (satanise ctxt (christen ctxt M) (christen-freeVars ctxt M))
satanise-christen-id ctxt noDup (v x) = indexOf-sing-sub-dom-in-index-id ctxt noDup x
satanise-christen-id ctxt noDup (M app N)
  rewrite
    Sub-unique
      (Sub-union-SubL (freeVars (christen ctxt M)) (freeVars (christen ctxt N)) (dom ctxt) (Sub-both-Sub-union (christen-freeVars ctxt M) (christen-freeVars ctxt N)))
      (christen-freeVars ctxt M)
  | Sub-unique
      (Sub-union-SubR (freeVars (christen ctxt M)) (freeVars (christen ctxt N)) (dom ctxt) (Sub-both-Sub-union (christen-freeVars ctxt M) (christen-freeVars ctxt N)))
      (christen-freeVars ctxt N)
         = satanise-christen-id ctxt noDup M , satanise-christen-id ctxt noDup N
satanise-christen-id ctxt noDup (lam M)
  rewrite
    Sub-unique
      (delete-adjoint-<: (List.firstNotIn ctxt)
              (freeVars (christen (List.firstNotIn ctxt ,- ctxt) M)) (dom ctxt)
              (freeVars-Can (christen (List.firstNotIn ctxt ,- ctxt) M))
              (<:adjoint-delete (List.firstNotIn ctxt)
               (freeVars (christen (List.firstNotIn ctxt ,- ctxt) M)) (dom ctxt)
               (christen-freeVars (List.firstNotIn ctxt ,- ctxt) M)))
      (christen-freeVars (List.firstNotIn ctxt ,- ctxt) M)
        = satanise-christen-id (List.firstNotIn ctxt ,- ctxt) (List.firstNotIn-preserves-NoDup ctxt noDup) M
