{-# LANGUAGE TypeFamilies #-}

module Funk.Parser where

import Data.Functor (($>))
import Funk.Term
import Funk.Token
import Text.Parsec

type Parser = Parsec [Located Token] ()

type PType = Type (Located Ident)

newtype PBinding = PBinding
  { unPBinding :: Located Ident
  }
  deriving (Show, Eq)

instance Binding PBinding where
  type BTVar PBinding = Located Ident
  type BVar PBinding = ()
  type BLam PBinding = ()
  type BApp PBinding = ()
  type BTyLam PBinding = ()
  type BTyApp PBinding = ()

type PTerm = Term PBinding

tok :: Token -> Parser ()
tok expected =
  tokenPrim show updatePos testTok
  where
    testTok (Located _ t)
      | t == expected = Just ()
      | otherwise = Nothing
    updatePos _ (Located pos _) _ = pos

identTok :: Parser (Located String)
identTok = tokenPrim show updatePos testTok <?> "identifier"
  where
    testTok (Located pos (TokIdent s)) = Just (Located pos s)
    testTok _ = Nothing
    updatePos _ (Located pos _) _ = pos

typeVar :: Parser PType
typeVar = TVar . fmap Ident <$> identTok

parensType :: Parser PType
parensType = tok TokLParen *> typeExpr <* tok TokRParen

forallType :: Parser PType
forallType = do
  tok TokForall
  v <- fmap (Ident <$>) identTok
  tok TokDot
  TForall v <$> typeExpr

atomicType :: Parser PType
atomicType =
  choice
    [ try forallType,
      typeVar,
      parensType
    ]

typeExpr :: Parser PType
typeExpr = chainr1 atomicType (tok TokArrow $> TArrow)

varTerm :: Parser PTerm
varTerm = Var () . PBinding . fmap Ident <$> identTok

parensTerm :: Parser PTerm
parensTerm = tok TokLParen *> term <* tok TokRParen

lambdaTerm :: Parser PTerm
lambdaTerm = do
  tok TokLambda
  Located pos s <- identTok
  let v = PBinding $ Located pos (Ident s)
  ty <- optionMaybe (tok TokColon *> typeExpr)
  tok TokDot
  Lam () v ty <$> term

tyLamTerm :: Parser PTerm
tyLamTerm = do
  tok TokTypeLambda
  Located pos s <- identTok
  let v = Located pos (Ident s)
  tok TokDot
  TyLam () v <$> term

atomicTerm :: Parser PTerm
atomicTerm =
  choice
    [ varTerm,
      parensTerm
    ]

appTerm :: Parser PTerm
appTerm = do
  f0 <- atomicTerm
  rest f0
  where
    rest f =
      ( do
          tok TokLBracket
          ty <- typeExpr
          tok TokRBracket
          rest (TyApp () f ty)
      )
        <|> try
          ( do
              arg <- atomicTerm
              rest (App () f arg)
          )
        <|> return f

term :: Parser PTerm
term =
  choice
    [ try lambdaTerm,
      tyLamTerm,
      appTerm
    ]

parseTerm :: [Located Token] -> Either ParseError PTerm
parseTerm = parse (term <* eof) "<input>"
