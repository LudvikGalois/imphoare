{
{-# Language DataKinds #-}
{-|
Module      : Language.Imp.Parser
Description : A parser for the Imp language
Copyright   : (c) Robert `Probie' Offner, 2018
License     : MIT
Maintainer  : ludvikgalois@gmail.com

This module defines a parser for the Imp language
-} 

module Language.Imp.Parser (imp, intExpr) where

import qualified Language.Imp.Lexer as T
import Language.Imp
}

%name impParser Stmt
%name impIntParser IntExpr
%name impBoolParser BoolExpr
%monad {Either String} {(>>=)} {return}
%tokentype { ((Int,Int), T.Token) }
%error { parseError }
%token
  if {(_, T.If)}
  then {(_,T.Then)}
  else {(_,T.Else)}
  end {(_,T.End)}
  while {(_,T.While)}
  do {(_,T.Do)}
  var {(_,T.Ident $$)}
  int {(_,T.IntLit $$)}
  bool {(_,T.BoolLit $$)}
  '(' {(_,T.LParen)}
  ')' {(_,T.RParen)}
  ';' {(_,T.Semi)}
  ':=' {(_,T.Assign)}
  '+' {(_,T.Plus)}
  '-' {(_,T.Sub)}
  '*' {(_,T.Mult)}
  '/' {(_,T.Div)}
  '%' {(_,T.Mod)}
  '^' {(_,T.Pow)}
  '==' {(_,T.Eq)}
  '/=' {(_,T.Neq)}
  '>' {(_,T.Gt)}
  '>=' {(_,T.Ge)}
  '<' {(_,T.Lt)}
  '<=' {(_,T.Le)}
  '!' {(_,T.Not)}
  '&&' {(_,T.And)}
  '||' {(_,T.Or)}

%right ';'
%right '||'
%right '&&'
%nonassoc '>' '>=' '<=' '<' '==' '/='
%left '+' '-'
%left '*' '/' '%'
%right '^'
%left NEG '!'

%%
Stmt : Stmt ';' Stmt { Seq $1 $3 }
     | Stmt ';' {$1}
     | var ':=' IntExpr {Assign $1 $3}
     | if BoolExpr then Stmt else Stmt end {If $2 $4 $6}
     | while BoolExpr do Stmt end {While $2 $4}

IntExpr : var {Var $1}
        | int {IntLit $1}
        | '(' IntExpr ')' {$2}
        | IntExpr '+' IntExpr {BinaryOp Add $1 $3}
        | IntExpr '-' IntExpr {BinaryOp Sub $1 $3}
        | IntExpr '*' IntExpr {BinaryOp Mult $1 $3}
        | IntExpr '/' IntExpr {BinaryOp Div $1 $3}
        | IntExpr '%' IntExpr {BinaryOp Mod $1 $3}
        | IntExpr '^' IntExpr {BinaryOp Pow $1 $3}
        | '-' IntExpr %prec NEG {UnaryOp Negate $2}

BoolExpr : bool {BoolLit $1}
         | '(' BoolExpr ')' {$2}
         | '!' BoolExpr {UnaryOp Not $2}
         | BoolExpr '&&' BoolExpr {BinaryOp And $1 $3}
         | BoolExpr '||' BoolExpr {BinaryOp Or $1 $3}
         | IntExpr '<' IntExpr {BinaryOp Lt $1 $3}
         | IntExpr '<=' IntExpr {BinaryOp Le $1 $3}
         | IntExpr '>' IntExpr {BinaryOp Gt $1 $3}
         | IntExpr '>=' IntExpr {BinaryOp Ge $1 $3}
         | IntExpr '==' IntExpr {BinaryOp Eq $1 $3}
         | BoolExpr '==' BoolExpr {BinaryOp Iff $1 $3}
         | IntExpr '/=' IntExpr {BinaryOp Neq $1 $3}
         | BoolExpr '/=' BoolExpr {BinaryOp Xor $1 $3}


{

parseError :: [((Int,Int), T.Token)] -> Either String a
parseError [] = Left "Unexpected end of input"
parseError (((line, col),(T.LexError s)):xs) =
  Left $ "Lexical error " ++ show s ++
         " at " ++ show line ++ ":" ++ show col 
parseError (((line, col),_):xs) =
  Left $ "Parse error at " ++
          show line ++ ":" ++ show col 

-- | A parser for Imp
imp :: String -> Either String (Statement String)
imp = impParser . T.lexer

intExpr :: String -> Either String (Expr ℤ String)
intExpr = impIntParser . T.lexer

boolExpr :: String -> Either String (Expr 𝔹 String)
boolExpr = impBoolParser . T.lexer

}
