{-# OPTIONS --no-unicode #-}

module Lib.One where

record One : Set where
  constructor <>

{-# BUILTIN UNIT One #-}

open One
