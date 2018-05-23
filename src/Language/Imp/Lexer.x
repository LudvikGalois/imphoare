{
{-|
Module      : Language.Imp.Lexer
Description : A lexer for the Imp language
Copyright   : (c) Robert `Probie' Offner, 2018
License     : MIT
Maintainer  : ludvikgalois@gmail.com

This module defines a lexer for the Imp language
-}
module Language.Imp.Lexer (Token (..), lexer) where
}
%wrapper "posn"

$digit = 0-9
$alphaNum = [0-9a-zA-Z]
$alpha = [a-zA-Z]

tokens :-
  $white+ ;
  "(" {\pos _ -> (getLineCol pos, LParen)}
  ")" {\pos _ -> (getLineCol pos, RParen)}
  ";" {\pos _ -> (getLineCol pos, Semi)}
  ":=" {\pos _ -> (getLineCol pos, Assign)}
  "+" {\pos _ -> (getLineCol pos, Plus)}
  "-" {\pos _ -> (getLineCol pos, Sub)}
  "*" {\pos _ -> (getLineCol pos, Mult)}
  "/=" {\pos _ -> (getLineCol pos, Neq)}
  "/" {\pos _ -> (getLineCol pos, Div)}
  "%" {\pos _ -> (getLineCol pos, Mod)}
  "^" {\pos _ -> (getLineCol pos, Pow)}
  "==" {\pos _ -> (getLineCol pos, Eq)}
  "<=" {\pos _ -> (getLineCol pos, Le)}
  "<" {\pos _ -> (getLineCol pos, Lt)}
  ">=" {\pos _ -> (getLineCol pos, Ge)}
  ">" {\pos _ -> (getLineCol pos, Gt)}
  "!" {\pos _ -> (getLineCol pos, Not)}
  "&&" {\pos _ -> (getLineCol pos, And)}
  "||" {\pos _ -> (getLineCol pos, Or)}
  $digit+ {\pos n -> (getLineCol pos, IntLit (read n))}
  $alpha $alphaNum* {\pos str -> (getLineCol pos, identOrKeyword str)}
  . {\pos s -> (getLineCol pos, LexError s)}
  
{
-- | Tokens for Imp
data Token = LParen
           | RParen
           | Semi
           | Assign
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
           | Not
           | IntLit Integer
           | If
           | Then
           | Else
           | End
           | While
           | Do
           | BoolLit Bool
           | LexError String
           
  deriving Show

identOrKeyword :: String -> Token
identOrKeyword s = case s of
  "if" -> If
  "then" -> Then
  "else" -> Else
  "end" -> End
  "while" -> While
  "do" -> Do
  "true" -> BoolLit True
  "false" -> BoolLit False
  "True" -> BoolLit True
  "False" -> BoolLit False
  _ -> Ident s

getLineCol :: AlexPosn -> (Int,Int)
getLineCol (AlexPn _ line col) = (line, col)

-- | A lexer for Imp
lexer = alexScanTokens
}
