{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Funk.Token where

import Text.Parsec hiding (token)
import Text.Parsec.String

data Located a = Located
  { locatedPos :: SourcePos,
    unLocated :: a
  }
  deriving (Eq, Functor)

instance (Show a) => Show (Located a) where
  show (Located _ a) = show a

data Token
  = TokIdent String
  | TokLambda
  | TokTypeLambda
  | TokForall
  | TokArrow
  | TokDot
  | TokColon
  | TokLParen
  | TokRParen
  | TokLBracket
  | TokRBracket
  | TokEq
  | TokSemicolon
  deriving (Eq)

instance Show Token where
  show = \case
    TokIdent _ -> "identifier"
    TokLambda -> "'\\'"
    TokTypeLambda -> "'/\\'"
    TokForall -> "'\\/'"
    TokArrow -> "'->'"
    TokDot -> "'.'"
    TokColon -> "':'"
    TokLParen -> "'('"
    TokRParen -> "')'"
    TokLBracket -> "'['"
    TokRBracket -> "']'"
    TokEq -> "'='"
    TokSemicolon -> "';'"

token :: Parser (Located Token)
token = do
  pos <- getPosition
  t <-
    choice
      [ TokTypeLambda <$ try (string "/\\"),
        TokForall <$ try (string "\\/"),
        TokLambda <$ char '\\',
        TokArrow <$ try (string "->"),
        TokDot <$ char '.',
        TokColon <$ char ':',
        TokLParen <$ char '(',
        TokRParen <$ char ')',
        TokLBracket <$ char '[',
        TokRBracket <$ char ']',
        TokEq <$ char '=',
        TokSemicolon <$ char ';',
        identToken
      ]
  return $ Located pos t
  where
    identToken = do
      c <- letter <|> char '_'
      cs <- many (alphaNum <|> char '_')
      return $ TokIdent (c : cs)

tokenize :: String -> Either ParseError [Located Token]
tokenize = parse (spaces *> many (token <* spaces) <* eof) ""
