{-# OPTIONS --no-unicode #-}

module Lib.Zero where

data Zero : Set where

naughtE : {a : Set} -> Zero -> a
naughtE ()
