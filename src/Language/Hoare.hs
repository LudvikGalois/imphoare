{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs         #-}
{-|
Module      : Language.Hoare
Description : Hoare logic proofs
Copyright   : (c) Robert `Probie' Offner, 2018
License     : MIT
Maintainer  : ludvikgalois@gmail.com

A module for defining Hoare Logic proofs
-}
module Language.Hoare
  ( HoareTriple (..), ProofStep (..), ProofValidity (..)
  , StringProofStep, StringProof, LinearProofStep, LinearProof
  , compileLinearProof, checkProof) where

import qualified Language.CPL              as L
import           Language.Imp              (ImpType (..))
import qualified Language.Imp              as I

import           Data.Array
import           Data.Text.Prettyprint.Doc hiding (line)

-- | A Hoare Triple
data HoareTriple ν = Hoare
  { _precon  ∷ L.Prop ν -- ^ The precondition
  , _code    ∷ I.Statement ν -- ^ The code block
  , _postcon ∷ L.Prop ν -- ^ The postcondition
  }
  deriving (Show, Eq, Functor)

-- | A single proof step, with references of type τ
data ProofStep τ ν where
  -- | The Assignment Axiom
  Assign ∷ ν → I.Expr 'ℤ ν → L.Prop ν → ProofStep τ ν
  -- | Precondition weakening
  PreconWeaken ∷ L.Prop ν → τ → ProofStep τ ν
  -- | Postcondition strengthening
  PostconStrengthen ∷ L.Prop ν → τ → ProofStep τ ν
  -- | The sequencing rule
  Sequence ∷ τ → τ → ProofStep τ ν
  -- | The if rule
  If ∷ I.Expr '𝔹 ν → τ → τ → ProofStep τ ν
  -- | The while rule
  While ∷ I.Expr '𝔹 ν → τ → ProofStep τ ν
  deriving (Show, Functor)

-- Pull out the dependencies of a proof step
containedTriples ∷ ProofStep τ ν → [τ]
containedTriples p = case p of
  Assign{}              → []
  PreconWeaken _ t      → [t]
  PostconStrengthen _ t → [t]
  Sequence t1 t2        → [t1,t2]
  If _ t1 t2            → [t1,t2]
  While _ t             → [t]

replaceVar ∷ (Eq ν) ⇒ ν → L.NumExpr ν → L.Prop ν → L.Prop ν
replaceVar var new prop = case prop of
  L.Not prop' → L.Not (replaceVar var new prop')
  L.BinProp op e1 e2 → L.BinProp op (replaceVar var new e1)
                                    (replaceVar var new e2)
  L.Comparison op e1 e2 → L.Comparison op (updateExpr e1) (updateExpr e2)
  x → x
  where
    updateExpr expr = case expr of
        L.Var v | v == var → new
                | otherwise → expr
        L.Lit{} → expr
        L.UnNumOp op expr' → L.UnNumOp op (updateExpr expr')
        L.BinNumOp op e1 e2 → L.BinNumOp op (updateExpr e1) (updateExpr e2)

-- Conversion boilerplate
propNum ∷ I.Expr 'ℤ ν → L.NumExpr ν
propNum expr = case expr of
  I.Var v                  → L.Var v
  I.IntLit n               → L.Lit n
  I.UnaryOp I.Negate expr' → L.UnNumOp L.Negate (propNum expr')
  I.BinaryOp I.Add e1 e2   → L.BinNumOp L.Add (propNum e1) (propNum e2)
  I.BinaryOp I.Sub e1 e2   → L.BinNumOp L.Sub (propNum e1) (propNum e2)
  I.BinaryOp I.Mult e1 e2  → L.BinNumOp L.Mult (propNum e1) (propNum e2)
  I.BinaryOp I.Div e1 e2   → L.BinNumOp L.Div (propNum e1) (propNum e2)
  I.BinaryOp I.Mod e1 e2   → L.BinNumOp L.Mod (propNum e1) (propNum e2)
  I.BinaryOp I.Pow e1 e2   → L.BinNumOp L.Pow (propNum e1) (propNum e2)

propBool ∷ I.Expr '𝔹 ν → L.Prop ν
propBool expr = case expr of
  I.BoolLit True → L.TT
  I.BoolLit False → L.FF
  I.UnaryOp I.Not expr' → L.Not (propBool expr')
  I.BinaryOp I.Iff e1 e2 → L.BinProp L.Iff (propBool e1) (propBool e2)
  I.BinaryOp I.Xor e1 e2 → L.BinProp L.Iff (propBool e1) (L.Not (propBool e2))
  I.BinaryOp I.And e1 e2 → L.BinProp L.And (propBool e1) (propBool e2)
  I.BinaryOp I.Or e1 e2 → L.BinProp L.Or (propBool e1) (propBool e2)
  I.BinaryOp I.Eq e1 e2 → L.Comparison L.Eq (propNum e1) (propNum e2)
  I.BinaryOp I.Neq e1 e2 → L.Comparison L.Neq (propNum e1) (propNum e2)
  I.BinaryOp I.Lt e1 e2 → L.Comparison L.Lt (propNum e1) (propNum e2)
  I.BinaryOp I.Le e1 e2 → L.Comparison L.Le (propNum e1) (propNum e2)
  I.BinaryOp I.Gt e1 e2 → L.Comparison L.Gt (propNum e1) (propNum e2)
  I.BinaryOp I.Ge e1 e2 → L.Comparison L.Ge (propNum e1) (propNum e2)

removeProp ∷ (Eq ν) ⇒ L.Prop ν → L.Prop ν → L.Prop ν
removeProp expr (L.BinProp L.And p q)
  | expr == p && expr == q = L.TT
  | expr == q = p
  | expr == p = q
  | otherwise = L.BinProp L.And (removeProp expr p) (removeProp expr q)
removeProp expr prop
  | expr == prop = L.TT
  | otherwise = prop

has ∷ (Eq ν) ⇒ L.Prop ν → L.Prop ν → Bool
has p q                     | p == q = True
has (L.BinProp L.And p q) r = p `has` r || q `has` r
has _ _                     = False

-- Convert a `ProofStep` to a `HoareTriple` (mainly for pretty printing)
proofToTriple ∷ (Eq ν) ⇒ ProofStep (HoareTriple ν) ν → HoareTriple ν
proofToTriple proof = case proof of
  Assign var expr prop →
    Hoare (replaceVar var (propNum expr) prop) (I.Assign var expr) prop
  PreconWeaken precon triple → triple {_precon = precon}
  PostconStrengthen postcon triple → triple {_postcon = postcon}
  Sequence t1 t2 → Hoare { _precon = _precon t1
                         , _code = I.Seq (_code t1) (_code t2)
                         , _postcon = _postcon t2
                         }
  If p t1 t2 → Hoare { _precon = removeProp (propBool p) (_precon t1)
                     , _code = I.If p (_code t1) (_code t2)
                     , _postcon = _postcon t1
                     }
  While p t1 → Hoare { _precon = L.BinProp L.And (_postcon t1) (propBool p)
                     , _code = I.While p (_code t1)
                     , _postcon = L.BinProp L.And (_postcon t1)
                                                  (L.Not (propBool p))
                     }

-- | A type for proof validity
data ProofValidity
  = NotValid -- ^ The proof is not valid
  | Unknown -- ^ We can't decide if the proof is valid or not
  | Valid -- ^ The proof is valid
  deriving (Eq, Show, Ord)

-- | A proof step with Hoare triples (with string variables) for previous steps
type StringProofStep = ProofStep (HoareTriple String) String
-- | A proof step with line numbers for previous steps
type LinearProofStep = ProofStep Int String
-- | A proof built from `StringProofStep`
type StringProof = [StringProofStep]
-- | A proof built from `LinearProofStep`
type LinearProof = [LinearProofStep]

-- | Compile a `LinearProof` to a `StringProof`
compileLinearProof
  ∷ LinearProof -- ^ The input proof
  → Either String StringProof -- ^ Either the output proof or an error message
compileLinearProof proof
  | validOrdering = Right (elems compiled)
  | otherwise = Left "Invalid References"
  where
    len = length proof
    validOrdering = and [all ((&&) <$> (<n) <*> (>= 1)) (containedTriples x)
                        | (n,x) ← zip [1..] proof]
    compiled = listArray (1, len) (map compileLine proof)
    fetch n = proofToTriple (compiled ! n)
    compileLine line = case line of
      Assign var expr prop → Assign var expr prop
      PreconWeaken precon lineNum → PreconWeaken precon (fetch lineNum)
      PostconStrengthen precon lineNum →
        PostconStrengthen precon (fetch lineNum)
      Sequence lineNum1 lineNum2 → Sequence (fetch lineNum1) (fetch lineNum2)
      If prop lineNum1 lineNum2 → If prop (fetch lineNum1) (fetch lineNum2)
      While prop lineNum → While prop (fetch lineNum)

-- Our default proof time
proofTime ∷ Int
proofTime = 2 * second
  where
    second = 1000

checkProp ∷ L.Prop String → IO ProofValidity
checkProp prop = do
  valid ← L.prove proofTime prop
  return $ case valid of
      Nothing    → Unknown
      Just False → NotValid
      Just True  → Valid

-- Is an individual proof step valid?
validProofStep ∷ StringProofStep → IO ProofValidity
validProofStep step = case step of
  Assign{} → return Valid
  PreconWeaken newcon Hoare{_precon = oldcon} →
    checkProp (L.BinProp L.Imp newcon oldcon)
  PostconStrengthen newcon Hoare{_postcon = oldcon} →
    checkProp (L.BinProp L.Imp oldcon newcon)
  Sequence e1 e2
    | _postcon e1 == _precon e2 → return Valid
    | otherwise → return NotValid
  If p e1 e2
    | _postcon e1 == _postcon e2,
      p' ← propBool p,
      removeProp p' (_precon e1) == removeProp (L.Not p') (_precon e2),
      _precon e1 `has` p',
      _precon e2 `has` L.Not p' → return Valid
    | otherwise → return NotValid
  While p e1
    | p' ← propBool p,
      _precon e1 `has` p',
      _postcon e1 == removeProp p' (_precon e1) → return Valid
    | otherwise → return NotValid

-- | Check if a proof is valid
checkProof ∷ StringProof → IO ProofValidity
checkProof = go Valid []
  where
    go NotValid _ _ = return NotValid
    go validity _ [] = return validity
    go validity proven (x:xs) =
      let continue = do
            stepValidity ← validProofStep x
            go (min validity stepValidity) (proofToTriple x : proven) xs
          known = (`elem` proven)
      in if all known (containedTriples x) then continue else return NotValid

instance (Show ν, Pretty ν) ⇒ Pretty (HoareTriple ν) where
  pretty (Hoare precon code postcon) = vsep [ braces (pretty precon)
                                            , pretty code
                                            , braces (pretty postcon)
                                            ]

