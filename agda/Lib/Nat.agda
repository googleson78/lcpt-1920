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

_+N_ : Nat -> Nat -> Nat
zero +N m = m
suc n +N m = suc (n +N m)

infixl 40 _+N_

+N-right-zero : (n : Nat) -> n == n +N zero
+N-right-zero zero = refl
+N-right-zero (suc n) = ap suc (+N-right-zero n)

+N-right-suc : (n m : Nat) -> suc (n +N m) == n +N suc m
+N-right-suc zero m = refl
+N-right-suc (suc n) m = ap suc (+N-right-suc n m)

+N-commut : (n m : Nat) -> n +N m == m +N n
+N-commut zero m = +N-right-zero m
+N-commut (suc n) m rewrite +N-commut n m | +N-right-suc m n = refl

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

+N-monotone-<=-r : (n k : Nat) -> n <= n +N k
+N-monotone-<=-r zero k = ozero
+N-monotone-<=-r (suc n) k = osuc (+N-monotone-<=-r n k)

+N-monotone-<=-l : (n k : Nat) -> n <= k +N n
+N-monotone-<=-l n k rewrite +N-commut k n = +N-monotone-<=-r n k

+N-monotone2-<=-l : (n m k : Nat) -> n <= m -> k +N n <= k +N m
+N-monotone2-<=-l n m zero n<=m = n<=m
+N-monotone2-<=-l n m (suc k) n<=m = osuc (+N-monotone2-<=-l n m k n<=m)

+N-inj : (n m k : Nat) -> k +N n == k +N m -> n == m
+N-inj n m zero k+n==k+m = k+n==k+m
+N-inj n m (suc k) k+n==k+m rewrite +N-inj n m k (suc-inj k+n==k+m) = refl

+N-monotone2-<-l : (n m k : Nat) -> n < m -> k +N n < k +N m
+N-monotone2-<-l n m k ( n<=m , n/=m ) with +N-monotone2-<=-l n m k n<=m
... | z = z , \{ x -> n/=m (+N-inj n m k x)}

dec<= : (n m : Nat) -> Dec (n <= m)
dec<= zero m = inr ozero
dec<= (suc n) zero = inl (\ ())
dec<= (suc n) (suc m) with dec<= n m
dec<= (suc n) (suc m) | inl no = inl \{ (osuc n<=m) -> no n<=m}
dec<= (suc n) (suc m) | inr yes = inr (osuc yes)

dec== : (n m : Nat) -> Dec (n == m)
dec== zero zero = inr refl
dec== zero (suc m) = inl (\ ())
dec== (suc n) zero = inl (\ ())
dec== (suc n) (suc m) with dec== n m
dec== (suc n) (suc m) | inl no = inl \{ refl -> no refl}
dec== (suc n) (suc m) | inr yes = inr (ap suc yes)

dec< : (n m : Nat) -> Dec (n < m)
dec< n m with dec== n m
dec< n .n | inr refl = inl (\ x -> snd x refl)
dec< n m | inl notEq with dec<= n m
dec< n m | inl notEq | inl notLeq = inl (\ x -> notLeq (fst x))
dec< n m | inl notEq | inr yesLeq = inr (yesLeq , notEq)

<-osuc : {n m : Nat} -> n < m -> suc n < suc m
<-osuc (n<=m , n/=m) = osuc n<=m , \ sucn==sucm -> n/=m (suc-inj sucn==sucm)

<=-is-<-or-== : {n m : Nat} -> n <= m -> n < m + n == m
<=-is-<-or-== {.0} {zero} ozero = inr refl
<=-is-<-or-== {.0} {suc m} ozero = inl (ozero , (\ ()))
<=-is-<-or-== (osuc n<=m) with <=-is-<-or-== n<=m
<=-is-<-or-== (osuc n<=m) | inl n<m = inl (<-osuc (n<=m , snd n<m))
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

<-suc : {n : Nat} -> n < suc n
<-suc {zero} = ozero , (\ ())
<-suc {suc n} = <-osuc <-suc

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

<-<=-trans : {n m k : Nat} -> n < m -> m <= k -> n < k
<-<=-trans (n<=m , n/=m) m<=k = <=-trans n<=m m<=k , \{ refl -> n/=m (<=-antisymmetric n<=m m<=k)}

maxFin : {n m : Nat} -> n < m -> Fin m >< \x -> (y : Fin n) -> fst y == fst x -> Zero
maxFin {n} {zero} n<m = naughtE (<-zero-impossible n<m)
maxFin {n} {suc m} n<m = (m , <-suc) , \{ (y , y<n) refl -> suc-nothing-between y<n n<m}
