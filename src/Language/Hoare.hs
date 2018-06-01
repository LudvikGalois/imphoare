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
  , compileLinearProof, linearTriples, checkProof
  , cumulativeProofValidity) where

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
  | expr == q = p
  | expr == p = q
  | q' ← removeProp expr q, q /= q' = L.BinProp L.And p q'
  | otherwise = L.BinProp L.And (removeProp expr p) q
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
  While p t1 → Hoare { _precon = _postcon t1
                     , _code = I.While p (_code t1)
                     , _postcon = L.BinProp L.And (_postcon t1)
                                                  (L.Not (propBool p))
                     }

-- | A type for proof validity
data ProofValidity
  = NotValid String -- ^ The proof is not valid, and a reason why
  | Unknown -- ^ We can't decide if the proof is valid or not
  | Valid -- ^ The proof is valid
  deriving (Eq, Show, Ord)

-- | A proof step with Hoare triples (with string variables) for previous steps
type StringProofStep = ProofStep (HoareTriple String) String
-- | A proof step with line numbers for previous steps and string variables
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

-- | Get the Hoare Triples of a `LinearProof`
linearTriples
  ∷ LinearProof -- ^ The input proof
  → Either String [HoareTriple String] -- ^ Either the triples of the proof,
                                       --   or an error message
linearTriples = (map proofToTriple <$>) . compileLinearProof

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
      Just False → NotValid "Proposition is false."
      Just True  → Valid

pp ∷ Pretty α ⇒ α  → String
pp = show . pretty

-- Is an individual proof step valid?
validProofStep ∷ StringProofStep → IO ProofValidity
validProofStep step = case step of
  Assign{} → return Valid
  PreconWeaken newcon Hoare{_precon = oldcon} → do
    res ← checkProp (L.BinProp L.Imp newcon oldcon)
    return $ case res of
      NotValid _ → NotValid $
        "(" ++ pp newcon ++ ") does not imply ("
        ++ pp oldcon ++")."
      _ → res
  PostconStrengthen newcon Hoare{_postcon = oldcon} → do
    res ← checkProp (L.BinProp L.Imp oldcon newcon)
    return $ case res of
      NotValid _ → NotValid $
        "(" ++ pp oldcon ++ ") does not imply ("
        ++ pp newcon ++")."
      _ → res
  Sequence e1 e2
    | _postcon e1 == _precon e2 → return Valid
    | _precon e1 == _postcon e2 →
      return $ NotValid $ "The postcondition of the first statement ("
        ++ pp (_postcon e1) ++ ") doesn't "
        ++ "match the precondition (" ++ pp (_precon e2) ++ ") of the "
        ++ "second statement (try swapping the order)."
    | otherwise →
      return $ NotValid $ "The postcondition of the first statement ("
        ++ pp (_postcon e1) ++ ") doesn't "
        ++ "match the precondition (" ++ pp (_precon e2) ++ ") of the "
        ++ "second statement."
  If p e1 e2 → return $
    case _postcon e1 == _postcon e2 of
      False →
        NotValid $ "The postconditions (" ++ pp (_postcon e1) ++ ") and ("
          ++ pp (_postcon e2) ++ ") don't match"
      True → case (_precon e1 `has` p', _precon e2 `has` (L.Not p')) of
        (False,_) →
          NotValid $ "For the \"True \" case, we can't find " ++ pp p'
            ++ " in " ++ pp (_precon e1) ++ ". If it looks like it's"
            ++ " there, make sure it's on the outside and not part of"
            ++ " an Or."
        (_,False) →
          NotValid $ "For the \"False \" case, we can't find "
            ++ pp (L.Not p') ++ " in " ++ pp (_precon e2)
            ++ ". If it looks like it's"
            ++ " there, make sure it's on the outside and not part of"
            ++ " an Or."
        _ → case removeProp p' (_precon e1) ==
                  removeProp (L.Not p') (_precon e2) of
              False →
                NotValid $ "I tried removing the \"if condition\" from"
                  ++ " both preconditions, but they didn't match. I"
                  ++ " got (" ++ pp (removeProp p' (_precon e1))
                  ++ ") and (" ++ pp (removeProp (L.Not p') (_precon e2))
                  ++ "). If these are actually the same, but just"
                  ++ " specify terms in a different order, use"
                  ++ " precondition weakening to put them in the same"
                  ++ " order."
              True → Valid
    where p' = propBool p
  While p e1 → return $ 
    case _precon e1 `has` p' of
        True → case removeProp p' (_precon e1) == _postcon e1 of
          True → Valid
          False → NotValid $ "The precondition (" ++ pp (_precon e1)
            ++ ") and postcondition (" ++ pp (_postcon e1) ++ ") don't match."
        False → 
          NotValid $ "The precondition doesn't contain (" ++ pp p' ++ ")"
            ++ "."
    where p' = propBool p

-- | Check if a proof is valid
checkProof ∷ StringProof → IO ProofValidity
checkProof = go Valid []
  where
    go (NotValid reason) _ _ = return $ NotValid reason
    go validity _ [] = return validity
    go validity proven (x:xs) =
      let continue = do
            stepValidity ← validProofStep x
            go (min validity stepValidity) (proofToTriple x : proven) xs
          known = (`elem` proven)
      in if all known (containedTriples x)
         then continue else return (NotValid "Unknown step")

-- | Return the cumulative proof validity
cumulativeProofValidity ∷ StringProof → IO [ProofValidity]
cumulativeProofValidity = go Valid []
  where
    go (NotValid _) _ xs = return $
      map (const (NotValid "Earlier step invalid")) xs
    go _ _ [] = return []
    go validity proven (x:xs) =
      let continue = do
            stepValidity ← validProofStep x
            let newValidity = min validity stepValidity
            (newValidity:) <$> go newValidity (proofToTriple x : proven) xs
          known = (`elem` proven)
      in if all known (containedTriples x) then continue
         else (NotValid "Unknown step":) <$>
              go (NotValid "Earlier step invalid") [] xs

instance (Show ν, Pretty ν) ⇒ Pretty (HoareTriple ν) where
  pretty (Hoare precon code postcon) = vsep [ braces (pretty precon)
                                            , pretty code
                                            , braces (pretty postcon)
                                            ]

