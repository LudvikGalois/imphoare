{-|
Module      : Data.Precedence
Description : A module for defining precedence
Copyright   : (c) Robert `Probie' Offner, 2018
License     : MIT
Maintainer  : ludvikgalois@gmail.com

This module defines precedence typeclass, which is primarily
used to annotate things with precedence for the purposes of
pretty printing
-}
module Data.Precedence where

-- | Associativity
data Assoc
  = L -- ^ Left associative
  | R -- ^ Right associative
  | None -- ^ No associativity
  deriving (Eq, Ord, Show)

-- | A class for things with precedence
class HasPrecedence a where
  -- | Return the precedence and associativity
  precedence ∷ a → (Int, Assoc)
