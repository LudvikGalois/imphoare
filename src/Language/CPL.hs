{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE RankNTypes    #-}

{-|
Module      : Language.CPL
Description : The syntax of CPL and a prover
Copyright   : (c) Robert `Probie' Offner, 2018
License     : MIT
Maintainer  : ludvikgalois@gmail.com

This module defines the syntax of classical propositional logic
with integer arithmetic, an instance of `pretty` for it and
a prover (using [Microsoft's Z3 theorem prover](https://github.com/Z3Prover/z3)
)
-}
module Language.CPL ( BinProp (..), Comparison (..), UnNumOp (..)
                    , BinNumOp (..), NumExpr (..), Prop (..)
                    , simplify, prove) where

import           Control.Monad             (when)
import qualified Data.Map.Strict           as M
import           Data.Precedence
import qualified Data.Set                  as S
import           Data.Text.Prettyprint.Doc
import qualified Z3.Monad                  as Z3

-- | A binary operand over propositions
data BinProp = And -- ^ Logical and
             | Or -- ^ Logical or
             | Imp -- ^ Logical implication
             | Iff -- ^ Logical if-and-only-if
  deriving (Eq, Show)

instance HasPrecedence BinProp where
  precedence op = case op of
    And → (3, R)
    Or  → (2, R)
    Imp → (1, R)
    Iff → (1, None)

-- | An integer comparison
data Comparison = Lt -- ^ Less-than
                | Le -- ^ Less-than-or-equal
                | Gt -- ^ Greater-than
                | Ge -- ^ Greater-than-or-equal
                | Eq -- ^ Equal
                | Neq -- ^ Not equal
  deriving (Eq, Show)

-- | A unary integer operation
data UnNumOp = Negate -- ^ Integer negation
             | Abs -- ^ Absolute value
  deriving (Eq, Show)

-- | A binary integer operation
data BinNumOp = Add -- ^ Integer addition
              | Sub -- ^ Integer subtraction
              | Mult -- ^ Integer multiplication
              | Div -- ^ Integer division
              | Mod -- ^ Integer modulus
              | Pow -- ^ Integer exponentiation
  deriving (Eq, Show)

instance HasPrecedence BinNumOp where
  precedence op = case op of
    Add  → (6, L)
    Sub  → (6, L)
    Mult → (7, L)
    Div  → (7, L)
    Mod  → (7, L)
    Pow  → (8, R)

-- | An integer expression with variables of type ν
data NumExpr ν where
  -- | A variable
  Var ∷ ν → NumExpr ν
  -- | An integer literal
  Lit ∷ Integer → NumExpr ν
  -- | A unary operation
  UnNumOp ∷ UnNumOp → NumExpr ν → NumExpr ν
  -- | A binary operation
  BinNumOp ∷ BinNumOp → NumExpr ν → NumExpr ν → NumExpr ν
  deriving (Show, Functor, Eq)

-- | A proposition in CPL
data Prop ν where
  -- | True
  TT ∷ Prop ν
  -- | False
  FF ∷ Prop ν
  -- | Logical negation
  Not ∷ Prop ν → Prop ν
  -- | A binary logical operation
  BinProp ∷ BinProp → Prop ν → Prop ν → Prop ν
  -- | An integer comparison
  Comparison ∷ Comparison → NumExpr ν → NumExpr ν → Prop ν
  deriving (Show, Functor, Eq)

instance Pretty UnNumOp where
  pretty Negate = "-"
  pretty Abs    = "abs"  -- Not used

instance Pretty BinNumOp where
  pretty x = case x of
    Add  → "+"
    Mult → "*"
    Sub  → "-"
    Div  → "/"
    Mod  → "%"
    Pow  → "^"

instance Pretty Comparison where
  pretty x = case x of
    Le  → "<="
    Lt  → "<"
    Ge  → ">="
    Gt  → ">"
    Eq  → "="
    Neq → "=/="

instance Pretty BinProp where
  pretty x = case x of
    And → "/\\"
    Or  → "\\/"
    Imp → "=>"
    Iff → "<=>"

instance (Pretty ν, Show ν) ⇒ Pretty (NumExpr ν) where
  pretty = go 0
    where
      go prec expr = case expr of
        Var v → pretty v
        Lit n → pretty n
        UnNumOp Abs expr' → "|" <> go 0 expr' <> "|"
        UnNumOp op expr' → pretty op <> go 10 expr'
        BinNumOp op expr1 expr2 →
          let (prec', assoc) = precedence op
              bracketFun = if prec' < prec then parens else id
          in align $ bracketFun $ case assoc of
            None → go (prec' + 1) expr1 <+> pretty op <+> go (prec' + 1) expr2
            L → go prec' expr1 <+> pretty op <+> go (prec' + 1) expr2
            R → go (prec' + 1) expr1 <+> pretty op <+> go prec' expr2

instance (Pretty ν, Show ν) ⇒ Pretty (Prop ν) where
  pretty = go 0
    where
      go prec expr = case expr of
        TT → "TT"
        FF → "FF"
        Not expr' → "~" <> go 10 expr'
        Comparison op expr1 expr2 →
          (if prec == 10 then parens else id) $
              pretty expr1 <+> pretty op <+> pretty expr2
        BinProp op expr1 expr2 →
          let (prec', assoc) = precedence op
              bracketFun = if prec' < prec then parens else id
          in align $ bracketFun $ case assoc of
            None → go (prec' + 1) expr1 <+> pretty op <+> go (prec' + 1) expr2
            L →  go prec' expr1 <+> pretty op <+> go (prec' + 1) expr2
            R →  go (prec' + 1) expr1 <+> pretty op <+> go prec' expr2

-- | Attempt to simplify an expression by apply absorbtion,
-- reducing expressions only involving literals
-- and unfolding multiplication and exponentiation by a constant
simplify ∷ Prop ν → Prop ν
simplify prop = case prop of
  -- Base cases
  TT → TT
  FF → FF
  Not e1 → case simplify e1 of
    -- Literals
    FF  → TT
    TT  → FF
    -- Double negation
    Not e1' → e1'
    e1' → Not e1'
  -- And absorbtion
  BinProp And e1 e2 → case (simplify e1, simplify e2) of
    (TT, e2') → e2'
    (e1',TT)  → e1'
    (e1',e2') → BinProp And e1' e2'
  -- Or absorbtion
  BinProp Or e1 e2 → case (simplify e1, simplify e2) of
    (FF,e2')  → e2'
    (e1',FF)  → e1'
    (e1',e2') → BinProp Or e1' e2'
  -- Recurse on BinProp
  BinProp x e1 e2 → BinProp x (simplify e1) (simplify e2)
  -- Rewrite Gt to Lt
  Comparison Gt e1 e2 → simplify $ Comparison Lt e2 e1
  -- Rewrite Ge to Le
  Comparison Ge e1 e2 → simplify $ Comparison Le e2 e1
  -- Rewrite Le to Lt
  Comparison Le e1 e2 → simplify
    $ Comparison Lt e1 (BinNumOp Add (Lit 1) e2)
  -- Rewrite Neq to Not Eq
  Comparison Neq e1 e2 → simplify $ Not (Comparison Eq e1 e2)
  -- Recurse on comparison
  Comparison x eNum1 eNum2 → Comparison x (simplifyNum eNum1)
                                          (simplifyNum eNum2)
    where
      simplifyNum expr = case expr of
        -- Base cases
        Var{} → expr
        Lit{} → expr
        -- Remove multiple absolute values
        UnNumOp Abs expr'@(UnNumOp Abs _) → simplifyNum expr'
        -- Remove double negation
        UnNumOp Negate (UnNumOp Negate expr') → simplifyNum expr'
        -- Remove negation under absolute value
        UnNumOp Abs (UnNumOp Negate expr') → simplifyNum (UnNumOp Abs expr')
        -- Recurse on Unary Numeric op
        UnNumOp op expr' → UnNumOp op (simplifyNum expr')
        -- Cases for Add (sub-expressions are simplified and oriented)
        BinNumOp Add e1 e2 → case simplifyCommute e1 e2 of
          -- 0+n = n
          (Lit 0, e2')   → e2'
          -- Literals are added
          (Lit m, Lit n) → Lit (m+n)
          -- Nothing to simplify
          (e1',e2')      → BinNumOp Add e1' e2'
        -- Cases for Sub (sub-expressions are simplified)
        BinNumOp Sub e1 e2 → case (simplifyNum e1, simplifyNum e2) of
          -- n-0 = n
          (e1', Lit 0) → e1'
          -- Literals are subtracted
          (Lit m, Lit n) → Lit (m-n)
          -- Nothing to simplify
          (e1', e2')     → BinNumOp Sub e1' e2'
        -- Cases for Mul (sub-expressions are simplifiedand oriented)
        BinNumOp Mult e1 e2 → case simplifyCommute e1 e2 of
          -- Literals are multiplied
          (Lit l1, Lit l2) → Lit (l1 * l2)
          -- 0*n = 0
          (Lit 0, _) → Lit 0
          -- 1*n = n
          (Lit 1, e2') → e2'
          -- Unfold multiplication by literal to repeated addition
          (Lit l, e2') | abs l <= maxUnfolding → case compare l 0 of
            LT → UnNumOp Negate $
              foldl1 (BinNumOp Add) (replicate (fromIntegral (abs l)) e2')
            EQ → Lit 0 -- Can't happen, but just in case
            GT → foldl1 (BinNumOp Add) (replicate (fromIntegral l) e2')
          -- Nothing to simplify
          (e1',e2') → BinNumOp Mult e1' e2'
        -- Cases for Div (sub-expressions are simplified)
        BinNumOp Div e1 e2 → case (simplifyNum e1, simplifyNum e2) of
          -- n/1 = n
          (e1', Lit 1)                    → e1'
          -- Literals are divided if they'd divide evenly
          (Lit m, Lit n) | m `mod` n == 0 → Lit (m `div` n)
          -- Nothing to simplify
          (e1', e2')                      → BinNumOp Div e1' e2'
        -- Cases for Mod (sub-expressions are simplified)
        BinNumOp Mod e1 e2 → case (simplifyNum e1, simplifyNum e2) of
          -- Literals are mod-ed
          (Lit m, Lit n) → Lit (m `mod` n)
          -- Nothing to simplify
          (e1', e2')     → BinNumOp Mod e1' e2'
        -- Cases for Pow (sub-expressions are simplified)
        BinNumOp Pow e1 e2 → case (simplifyNum e1, simplifyNum e2) of
          -- n^0 = 1, note this means 0^0 = 1
          (_, Lit 0) → Lit 1
          -- n≠0 ⇒ 0^n = 0
          (Lit 0, _) → Lit 0
          -- 1^n = 1
          (Lit 1, _) → Lit 1
          -- Literals evaluated
          (Lit m, Lit n) | n >= 0 → Lit (m^n)
          -- Unfold positive literal exponents to repeated multiplication
          (e1', Lit n) | n >= 1, n <= maxUnfolding  → foldl1 (BinNumOp Mult) $
            replicate (fromIntegral n) e1'
          -- a^(m+n) = a^m * a^n
          (e1', BinNumOp Add e2l e2r) → simplifyNum (BinNumOp Mult
                                                (BinNumOp Pow e1' e2l)
                                                (BinNumOp Pow e1' e2r))
          -- Nothing to simplify
          (e1', e2') → BinNumOp Pow e1' e2'
      -- Simplify and orient
      simplifyCommute expr1 expr2 = case (simplifyNum expr1,
                                          simplifyNum expr2) of
        (v@Var{}, l@Lit{}) → (l,v)
        exprs              → exprs
      -- Maximum size to unfold for
      maxUnfolding = 15

-- | Attempt to prove an expression using z3 by asserting its negation
-- and checking if it's unsatisfiable
prove ∷ Int -- ^ Timeout in milliseconds
      → Prop String -- ^ The statement to prove
      → IO (Maybe Bool) -- ^ The result, `Just` `True` if the
                        --   statement is proven, `Just` False` if it's
                        --   shown to be false, and `Nothing`
                        --   if we can't decide
prove timeout prop = do
  env <- Z3.newEnv Nothing
                   (Z3.stdOpts Z3.+? Z3.opt "timeout" timeout)
  Z3.evalZ3WithEnv go env
  where
    go = do
      addConstraints prop
      res <- Z3.solverCheck
      return $ case res of
        Z3.Unsat → Just True
        Z3.Sat   → Just False
        Z3.Undef → Nothing

-- We need to know if an expression contains pow
-- because if it doesn't, we don't need to define it in z3
containsPow ∷ Prop ν → Bool
containsPow p = case p of
  BinProp _ e1 e2  → containsPow e1 || containsPow e2
  Not e            → containsPow e
  Comparison _ l r → containsPowNum l || containsPowNum r
  _                → False
  where
    containsPowNum expr = case expr of
      BinNumOp Pow _ _ → True
      BinNumOp _ l r   → containsPowNum l || containsPowNum r
      UnNumOp _ e      → containsPowNum e
      _                → False

-- Add the constraints to z3
addConstraints ∷ (Z3.MonadZ3 z3) ⇒ Prop String → z3 ()
addConstraints prop = do
  syms ← addVars (getVars prop)
  makeLtRule
  pow ← makePow (containsPow prop)
  buildAST syms pow (simplify prop) >>= Z3.mkNot >>= Z3.assert

-- Convert a Prop to a z3 AST
buildAST ∷ (Z3.MonadZ3 z3) ⇒ M.Map String Z3.AST → Z3.FuncDecl → Prop String
         → z3 Z3.AST
buildAST vars pow prop = case prop of
  TT → Z3.mkTrue
  FF → Z3.mkFalse
  Not prop' → buildAST vars pow prop' >>= Z3.mkNot
  BinProp op e1 e2 → case op of
    And → traverse (buildAST vars pow) [e1,e2] >>= Z3.mkAnd
    Or → traverse (buildAST vars pow) [e1,e2] >>= Z3.mkOr
    Imp → do
      e1AST ← buildAST vars pow e1
      e2AST ← buildAST vars pow e2
      Z3.mkImplies e1AST e2AST
    Iff → do
      e1AST ← buildAST vars pow e1
      e2AST ← buildAST vars pow e2
      Z3.mkIff e1AST e2AST
  Comparison Lt e1 e2 → do
    e1AST ← buildNumAST vars pow e1
    e2AST ← buildNumAST vars pow e2
    Z3.mkLt e1AST e2AST
  Comparison Le e1 e2 → do
    e1AST ← buildNumAST vars pow e1
    e2AST ← buildNumAST vars pow e2
    Z3.mkLe e1AST e2AST
  Comparison Gt e1 e2 → do
    e1AST ← buildNumAST vars pow e1
    e2AST ← buildNumAST vars pow e2
    Z3.mkGt e1AST e2AST
  Comparison Ge e1 e2 → do
    e1AST ← buildNumAST vars pow e1
    e2AST ← buildNumAST vars pow e2
    Z3.mkGe e1AST e2AST
  Comparison Eq e1 e2 → do
    e1AST ← buildNumAST vars pow e1
    e2AST ← buildNumAST vars pow e2
    Z3.mkEq e1AST e2AST
  _ → error "buildAST: Contains invalid comparison"

-- Convert a numeric expression to a z3 AST
buildNumAST ∷ (Z3.MonadZ3 z3) ⇒ M.Map String Z3.AST → Z3.FuncDecl
            → NumExpr String → z3 Z3.AST
buildNumAST vars pow expr = case expr of
  Lit n → Z3.mkInteger n
  Var v → return (vars M.! v)
  UnNumOp Abs e → do
    eAST ← buildNumAST vars pow e
    negAST ← Z3.mkUnaryMinus eAST
    isNegative ← Z3.mkInteger 0 >>= Z3.mkLt eAST
    Z3.mkIte isNegative negAST eAST
  UnNumOp Negate e → buildNumAST vars pow e >>= Z3.mkUnaryMinus
  BinNumOp Add e1 e2 → traverse (buildNumAST vars pow) [e1,e2] >>= Z3.mkAdd
  BinNumOp Sub e1 e2 → traverse (buildNumAST vars pow) [e1,e2] >>= Z3.mkSub
  BinNumOp Mult e1 e2 → traverse (buildNumAST vars pow) [e1,e2] >>= Z3.mkMul
  BinNumOp Div e1 e2 → do
    e1AST ← buildNumAST vars pow e1
    e2AST ← buildNumAST vars pow e2
    Z3.mkDiv e1AST e2AST
  BinNumOp Mod e1 e2 → do
    e1AST ← buildNumAST vars pow e1
    e2AST ← buildNumAST vars pow e2
    Z3.mkMod e1AST e2AST
  BinNumOp Pow e1 e2 → traverse (buildNumAST vars pow) [e1,e2] >>= Z3.mkApp pow

-- Get all variables from a Prop
getVars ∷ Prop String → [String]
getVars = S.toList . go S.empty
  where
    go set p = case p of
      Not e              → go set e
      BinProp _ e1 e2    → go (go set e1) e2
      Comparison _ e1 e2 → getNumVars (getNumVars set e1) e2
      _                  → set
    getNumVars set e = case e of
      Var v            → S.insert v set
      UnNumOp _ e'     → getNumVars set e'
      BinNumOp _ e1 e2 → getNumVars (getNumVars set e1) e2
      _                → set

-- x < y + 1 ∧ ~(x < y) ⇒ x=y
makeLtRule ∷ Z3.MonadZ3 z3 ⇒ z3 ()
makeLtRule = do
  iSort ← Z3.mkIntSort
  x ← Z3.mkIntSymbol (1 ∷ Int)
  y ← Z3.mkIntSymbol (2 ∷ Int)
  xInt ← Z3.mkBound 0 iSort
  yInt ← Z3.mkBound 1 iSort
  xEQy ← Z3.mkEq xInt yInt
  one ← Z3.mkInteger 1
  y' ← Z3.mkAdd [yInt, one]
  xLty' ← Z3.mkLt xInt y'
  xLty ← Z3.mkLt xInt yInt
  notxLty ← Z3.mkNot xLty
  comp ← Z3.mkAnd [xLty', notxLty]
  Z3.mkIff xEQy comp >>= Z3.mkForall [] [x,y] [iSort, iSort] >>= Z3.assert 

-- Oh boy...
makePow ∷ (Z3.MonadZ3 z3) ⇒ Bool → z3 Z3.FuncDecl
makePow giveDefinition = do
  pow ← Z3.mkStringSymbol "-pow"
  iSort ← Z3.mkIntSort
  decl ← Z3.mkFuncDecl pow [iSort, iSort] iSort
  x ← Z3.mkIntSymbol (1 ∷ Int)
  y ← Z3.mkIntSymbol (2 ∷ Int)
  xInt ← Z3.mkBound 0 iSort
  yInt ← Z3.mkBound 1 iSort
  zero ← Z3.mkInteger 0
  one ← Z3.mkInteger 1
  xToZero ← Z3.mkApp decl [xInt, zero]
  -- ∀x. x^0 = 1
  when giveDefinition $
    Z3.mkEq one xToZero >>= Z3.mkForall [] [x] [iSort] >>= Z3.assert
  greaterThanZero ← Z3.mkGt yInt zero
  step ← do
    lhs ← Z3.mkApp decl [xInt, yInt]
    rhs ← do
      ySub ← Z3.mkSub [yInt, one]
      smaller ←  Z3.mkApp decl [xInt, ySub]
      Z3.mkMul [xInt, smaller]
    Z3.mkEq lhs rhs
  -- ∀xy. y>0 ⇒ x^y = x*x^(y-1)
  when giveDefinition $
    Z3.mkImplies greaterThanZero step >>=
      Z3.mkForall [] [x,y] [iSort,iSort] >>= Z3.assert
  return decl

-- Make a map from variable names to the AST that represents them
addVars ∷ (Z3.MonadZ3 z3) ⇒ [String] → z3 (M.Map String Z3.AST)
addVars = go M.empty
  where
    go m [] = return m
    go m (x:xs)
      | x `M.member` m = go m xs
      | otherwise = do
          sym ← Z3.mkStringSymbol x
          var ← Z3.mkIntVar sym
          go (M.insert x var m) xs
