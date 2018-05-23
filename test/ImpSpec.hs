module ImpSpec (spec) where

import Language.Imp.Parser
import Language.Imp

import Test.Hspec

spec ∷ Spec
spec = do
  describe "The parser" $ do
    it "Can parse a trivial program" $ do
      imp "x := x" `shouldBe` (Right (Assign "x" (Var "x")))
      imp "x := y" `shouldBe` (Right (Assign "x" (Var "y")))
      imp "x := 9001" `shouldBe` (Right (Assign "x" (IntLit 9001)))
    it "Can parse an absolute value program" $ do
      imp "if x < 0 then absx := -x else absx := x end" `shouldBe`
        (Right (If (BinaryOp Lt (Var "x") (IntLit 0))
                (Assign "absx" (UnaryOp Negate (Var "x")))
                (Assign "absx" (Var "x"))))
    it "Can parse a fibonacci program" $ do
      imp "x := 0;\
          \y := 1;\
          \while n > 0 do\
          \  tmp := x;\
          \  x := y;\
          \  y := y + tmp;\
          \  n := n - 1;\
          \end;\
          \result := y;" `shouldBe` (Right $
        Assign "x" (IntLit 0) `Seq`
        Assign "y" (IntLit 1) `Seq`
        While (BinaryOp Gt (Var "n") (IntLit 0))
          (Assign "tmp" (Var "x") `Seq`
           Assign "x" (Var "y") `Seq`
           Assign "y" (BinaryOp Add (Var "y") (Var "tmp")) `Seq`
           Assign "n" (BinaryOp Sub (Var "n") (IntLit 1))) `Seq`
        Assign "result" (Var "y"))
    it "Should return a parse error on an invalid program" $ do
      imp "x = 0" `shouldSatisfy` (either (const True) (const False))
      imp "0 := x" `shouldSatisfy` (either (const True) (const False))
      imp "x := 0 +" `shouldSatisfy` (either (const True) (const False))
