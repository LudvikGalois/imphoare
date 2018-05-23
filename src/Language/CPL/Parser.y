{
{-|
Module      : Language.CPL.Parser
Description : A parser for the Imp language
Copyright   : (c) Robert `Probie' Offner, 2018
License     : MIT
Maintainer  : ludvikgalois@gmail.com

This module defines a parser for Classic Propositional Logic
with integer arithmetic 
-} 
module Language.CPL.Parser (cpl) where

import qualified Language.CPL.Lexer as T
import Language.CPL
}

%name cplParser
%monad {Either String} {(>>=)} {return}
%tokentype { ((Int, Int), T.Token) }
%error { parseError }
%token
  var {(_,T.Ident $$)}
  int {(_,T.IntLit $$)}
  bool {(_,T.BoolLit $$)}
  '(' {(_,T.LParen)}
  ')' {(_,T.RParen)}
  '+' {(_,T.Plus)}
  '-' {(_,T.Sub)}
  '*' {(_,T.Mult)}
  '/' {(_,T.Div)}
  '%' {(_,T.Mod)}
  '^' {(_,T.Pow)}
  '=' {(_,T.Eq)}
  '=/=' {(_,T.Neq)}
  '>' {(_,T.Gt)}
  '>=' {(_,T.Ge)}
  '<' {(_,T.Lt)}
  '<=' {(_,T.Le)}
  '~' {(_,T.Not)}
  '|' {(_,T.VBar)}
  '/\\' {(_,T.And)}
  '\\/' {(_,T.Or)}
  '=>' {(_,T.Imp)}
  '<=>' {(_,T.Iff)}

%nonassoc '<=>'
%right '=>' 
%right '\\/'
%right '/\\'
%nonassoc '>' '>=' '<=' '<' '=' '=/='
%left '+' '-'
%left '*' '/' '%'
%right '^'
%left NEG '~'

%%
BoolExpr : bool {if $1 then TT else FF}
         | '(' BoolExpr ')' {$2}
         | '~' BoolExpr {Not $2}
         | BoolExpr '/\\' BoolExpr {BinProp And $1 $3}
         | BoolExpr '\\/' BoolExpr {BinProp Or $1 $3}
         | BoolExpr '=>' BoolExpr {BinProp Imp $1 $3}
         | BoolExpr '<=>' BoolExpr {BinProp Iff $1 $3}
         | IntExpr '<' IntExpr {Comparison Lt $1 $3}
         | IntExpr '<=' IntExpr {Comparison Le $1 $3}
         | IntExpr '>' IntExpr {Comparison Gt $1 $3}
         | IntExpr '>=' IntExpr {Comparison Ge $1 $3}
         | IntExpr '=' IntExpr {Comparison Eq $1 $3}
         | IntExpr '=/=' IntExpr {Comparison Neq $1 $3}

IntExpr : var {Var $1}
        | int {Lit $1}
        | '(' IntExpr ')' {$2}
        | '|' IntExpr '|' {UnNumOp Abs $2}
        | IntExpr '+' IntExpr {BinNumOp Add $1 $3}
        | IntExpr '-' IntExpr {BinNumOp Sub $1 $3}
        | IntExpr '*' IntExpr {BinNumOp Mult $1 $3}
        | IntExpr '/' IntExpr {BinNumOp Div $1 $3}
        | IntExpr '%' IntExpr {BinNumOp Mod $1 $3}
        | IntExpr '^' IntExpr {BinNumOp Pow $1 $3}
        | '-' IntExpr %prec NEG {UnNumOp Negate $2}

{

parseError :: [((Int,Int), T.Token)] -> Either String a
parseError [] = Left "Unexpected end of input"
parseError (((line, col),(T.LexError s)):xs) =
  Left $ "Lexical error " ++ show s ++
         " at " ++ show line ++ ":" ++ show col 
parseError (((line, col),_):xs) =
  Left $ "Parse error at " ++
          show line ++ ":" ++ show col 

-- | A parser for CPL
cpl :: String -> Either String (Prop String)
cpl = cplParser . T.lexer

}
