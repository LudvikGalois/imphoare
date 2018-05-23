{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE StandaloneDeriving #-}

{-|
Module      : Language.Imp
Description : The syntax of the Imp language
Copyright   : (c) Robert `Probie' Offner, 2018
License     : MIT
Maintainer  : ludvikgalois@gmail.com

This module defines the syntax of the Imp language
as well as an instance of `pretty` for it
-}
module Language.Imp ( ImpType (..), UnaryOp (..)
                    , BinaryOp (..), Expr (..), Statement (..)) where

import           Data.Precedence
import           Data.Text.Prettyprint.Doc

-- Sequence is right associative
infixr `Seq`

-- | Imp has two types. These values are only intended to be used
-- at the type level
data ImpType
  = ℤ -- ^ The Integer type
  | 𝔹 -- ^ The Boolean type
  deriving (Eq, Show)

-- | The unary operations in Imp
data UnaryOp (α ∷ ImpType) (β ∷ ImpType) where
  -- | Boolean not
  Not    ∷ UnaryOp '𝔹 '𝔹
  -- | Integer negation
  Negate ∷ UnaryOp 'ℤ 'ℤ

deriving instance Eq (UnaryOp α β)
deriving instance Show (UnaryOp α β)

-- | The binary operations in Imp
data BinaryOp (α ∷ ImpType) (β ∷ ImpType) (γ ∷ ImpType) where
  -- | Integer addition
  Add  ∷ BinaryOp 'ℤ 'ℤ 'ℤ
  -- | Integer subtraction
  Sub  ∷ BinaryOp 'ℤ 'ℤ 'ℤ
  -- | Integer multiplication
  Mult ∷ BinaryOp 'ℤ 'ℤ 'ℤ
  -- | Integer division
  Div  ∷ BinaryOp 'ℤ 'ℤ 'ℤ
  -- | Integer modulus
  Mod  ∷ BinaryOp 'ℤ 'ℤ 'ℤ
  -- | Integer exponentiation
  Pow  ∷ BinaryOp 'ℤ 'ℤ 'ℤ
  -- | Boolean and
  And ∷ BinaryOp '𝔹 '𝔹 '𝔹
  -- | Boolean or
  Or  ∷ BinaryOp '𝔹 '𝔹 '𝔹
  -- | Boolean iff (or equality)
  Iff ∷ BinaryOp '𝔹 '𝔹 '𝔹
  -- | Boolean xor (or inequality)
  Xor ∷ BinaryOp '𝔹 '𝔹 '𝔹
  -- | Integer equality
  Eq  ∷ BinaryOp 'ℤ 'ℤ '𝔹
  -- | Integer inequality
  Neq ∷ BinaryOp 'ℤ 'ℤ '𝔹
  -- | Integer less-than
  Lt  ∷ BinaryOp 'ℤ 'ℤ '𝔹
  -- | Integer less-than-or-equal
  Le  ∷ BinaryOp 'ℤ 'ℤ '𝔹
  -- | Integer greater-than
  Gt  ∷ BinaryOp 'ℤ 'ℤ '𝔹
  -- | Integer greater-than-or-equal
  Ge  ∷ BinaryOp 'ℤ 'ℤ '𝔹

deriving instance Eq (BinaryOp α β γ)
deriving instance Show (BinaryOp α β γ)

-- | Expressions with type τ and variables of type ν
data Expr τ ν where
  -- | A variable (Imp only has integer variables)
  Var      ∷ ν → Expr 'ℤ ν
  -- | An integer literal
  IntLit   ∷ Integer → Expr 'ℤ ν
  -- | A boolean literal
  BoolLit  ∷ Bool → Expr '𝔹 ν
  -- | A unary operation
  UnaryOp  ∷ UnaryOp α β → Expr α ν → Expr β ν
  -- | A binary operation
  BinaryOp ∷ BinaryOp α β γ → Expr α ν → Expr β ν → Expr γ ν

deriving instance (Show ν) ⇒ Show (Expr τ ν)
deriving instance Functor (Expr τ)

-- | Statements with variables of type ν
data Statement ν where
  -- | Assign a variable to an expression
  Assign ∷ ν → Expr 'ℤ ν → Statement ν
  -- | An if statement
  If     ∷ Expr '𝔹 ν → Statement ν → Statement ν → Statement ν
  -- | A while loop
  While  ∷ Expr '𝔹 ν → Statement ν → Statement ν
  -- | Sequence two instructions
  Seq    ∷ Statement ν → Statement ν → Statement ν

deriving instance (Show ν) ⇒ Show (Statement ν)
deriving instance Functor Statement

-- We need a lot of boilerplate for equality because of
-- how we defined expressions

unOpEq ∷ UnaryOp α β → UnaryOp γ δ → Bool
unOpEq Not Not       = True
unOpEq Negate Negate = True
unOpEq _ _           = False

binOpEq ∷ BinaryOp α β γ → BinaryOp δ ε ζ → Bool
binOpEq Add Add   = True
binOpEq Sub Sub   = True
binOpEq Mult Mult = True
binOpEq Div Div   = True
binOpEq Mod Mod   = True
binOpEq Pow Pow   = True
binOpEq Eq Eq     = True
binOpEq Neq Neq   = True
binOpEq And And   = True
binOpEq Or Or     = True
binOpEq Lt Lt     = True
binOpEq Le Le     = True
binOpEq Gt Gt     = True
binOpEq Ge Ge     = True
binOpEq _ _       = False

-- In theory this could return True for differently typed terms
-- if we had polymorphic ground terms. Luckily we don't
exprEq ∷ (Eq ν) ⇒ Expr τ ν → Expr σ ν → Bool
exprEq (Var v) (Var v') = v == v'
exprEq (IntLit m) (IntLit n) = m == n
exprEq (BoolLit p) (BoolLit q) = p == q
exprEq (UnaryOp op e) (UnaryOp op' e') = unOpEq op op' && exprEq e e'
exprEq (BinaryOp op e1 e2) (BinaryOp op' e1' e2') =
  binOpEq op op' && exprEq e1 e1' && exprEq e2 e2'
exprEq _ _ = False

instance (Eq ν) ⇒ Eq (Expr τ ν) where
  -- We need a separate function, because the type of (==)
  -- is too restrictive
  (==) = exprEq

deriving instance (Eq ν) ⇒ Eq (Statement ν)

-- Boilerplate for pretty printing

instance Pretty (UnaryOp α β) where
  pretty op = case op of
    Not    → "!"
    Negate → "-"

instance Pretty (BinaryOp α β γ) where
  pretty op = case op of
    Add  → "+"
    Sub  → "-"
    Mult → "*"
    Div  → "/"
    Mod  → "%"
    Pow  → "^"
    And  → "&&"
    Or   → "||"
    Eq   → "=="
    Iff  → "=="
    Neq  → "/="
    Xor  → "/="
    Lt   → "<"
    Le   → "<="
    Gt   → ">"
    Ge   → ">="

instance HasPrecedence (BinaryOp α β γ) where
  precedence op = case op of
    Add  → (6, L)
    Sub  → (6, L)
    Mult → (7, L)
    Div  → (7, L)
    Mod  → (7, L)
    Pow  → (8, R)
    And  → (3, R)
    Or   → (2, R)
    Eq   → (4, None)
    Neq  → (4, None)
    Iff  → (4, None)
    Xor  → (4, None)
    Le   → (4, None)
    Lt   → (4, None)
    Ge   → (4, None)
    Gt   → (4, None)

instance (Pretty ν, Show ν) ⇒ Pretty (Expr τ ν) where
  pretty = go 0
    where
      go ∷ (Pretty ν) ⇒ Int → Expr τ ν → Doc ann
      go prec expr = case expr of
        Var v → pretty v
        IntLit n → pretty n
        BoolLit p → pretty p
        UnaryOp op expr' → pretty op <> go 10 expr'
        BinaryOp op expr1 expr2 →
          let (prec', assoc) = precedence op
              bracketFun = if prec' < prec then parens else id
          in align $ bracketFun $ case assoc of
            None → go (prec' + 1) expr1 <+> pretty op <+> go (prec' + 1) expr2
            L →  go prec' expr1 <+> pretty op <+> go (prec' + 1) expr2
            R →  go (prec' + 1) expr1 <+> pretty op <+> go prec' expr2

instance (Pretty ν, Show ν) ⇒ Pretty (Statement ν) where
  pretty statement = case statement of
    Assign v e → pretty v <+> ":=" <+> pretty e
    Seq s1 s2 → vsep [pretty s1 <> ";", pretty s2]
    While e s → vsep [ "while" <+> pretty e <+> "do"
                     , indent 4 (pretty s)
                     , "end"
                     ]
    If e s1 s2 → vsep ["if" <+> pretty e <+> "then"
                      , indent 4 (pretty s1)
                      , "else"
                      , indent 4 (pretty s2)
                      , "end"
                      ]
