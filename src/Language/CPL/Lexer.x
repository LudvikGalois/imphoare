{
{-|
Module      : Language.CPL.Lexer
Description : A lexer for CPL
Copyright   : (c) Robert `Probie' Offner, 2018
License     : MIT
Maintainer  : ludvikgalois@gmail.com

This module defines a lexer for CPL
-}
module Language.CPL.Lexer (Token (..), lexer) where
}
%wrapper "posn"

$digit = 0-9
$alphaNum = [0-9a-zA-Z]
$alpha = [a-zA-Z]

tokens :-
  $white+ ;
  "(" {\pos _ -> (getLineCol pos, LParen)}
  ")" {\pos _ -> (getLineCol pos, RParen)}
  "+" {\pos _ -> (getLineCol pos, Plus)}
  "-" {\pos _ -> (getLineCol pos, Sub)}
  "*" {\pos _ -> (getLineCol pos, Mult)}
  "/" {\pos _ -> (getLineCol pos, Div)}
  "%" {\pos _ -> (getLineCol pos, Mod)}
  "^" {\pos _ -> (getLineCol pos, Pow)}
  "=/=" {\pos _ -> (getLineCol pos, Neq)}
  "=>" {\pos _ -> (getLineCol pos, Imp)}
  "=" {\pos _ -> (getLineCol pos, Eq)}
  "<=>" {\pos _ -> (getLineCol pos, Iff)}
  "<=" {\pos _ -> (getLineCol pos, Le)}
  "<" {\pos _ -> (getLineCol pos, Lt)}
  ">=" {\pos _ -> (getLineCol pos, Ge)}
  ">" {\pos _ -> (getLineCol pos, Gt)}
  "~" {\pos _ -> (getLineCol pos, Not)}
  "|" {\pos _ -> (getLineCol pos, VBar)}
  "/\" {\pos _ -> (getLineCol pos, And)}
  "\/" {\pos _ -> (getLineCol pos, Or)}
  $digit+ {\pos n -> (getLineCol pos, IntLit (read n))}
  $alpha $alphaNum* {\pos str -> (getLineCol pos, identOrKeyword str)}
  . {\pos s -> (getLineCol pos, LexError s)}
  
{
-- | Tokens for CPL
data Token = LParen
           | RParen
           | VBar
           | Ident String
           | Plus
           | Sub
           | Mult
           | Div
           | Mod
           | Pow
           | Eq
           | Neq
           | Lt
           | Le
           | Gt
           | Ge
           | And
           | Or
           | Imp
           | Iff
           | Not
           | IntLit Integer
           | BoolLit Bool
           | LexError String
  deriving Show

identOrKeyword :: String -> Token
identOrKeyword s = case s of
  "True" -> BoolLit True
  "False" -> BoolLit False
  "TT" -> BoolLit True
  "FF" -> BoolLit False
  _ -> Ident s

getLineCol :: AlexPosn -> (Int,Int)
getLineCol (AlexPn _ line col) = (line, col)

-- | A lexer for CPL
lexer = alexScanTokens
}
