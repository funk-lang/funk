{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Funk.Token where

import Control.Monad (void)
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
  | TokString String
  | TokInt Int
  | TokTrue
  | TokFalse
  | TokLambda
  | TokForall
  | TokArrow
  | TokConstraintArrow
  | TokDot
  | TokColon
  | TokDoubleColon
  | TokStar
  | TokLParen
  | TokRParen
  | TokLBracket
  | TokRBracket
  | TokLBrace
  | TokRBrace
  | TokEq
  | TokSemicolon
  | TokType
  | TokData
  | TokTrait
  | TokImpl
  | TokInstance
  | TokFor
  | TokAt
  | TokComma
  | TokLet
  | TokMod
  | TokPub  
  | TokUse
  | TokPrim String
  deriving (Eq)

instance Show Token where
  show = \case
    TokIdent _ -> "identifier"
    TokString _ -> "string literal"
    TokInt _ -> "integer literal"
    TokTrue -> "'#true'"
    TokFalse -> "'#false'"
    TokLambda -> "'\\'"
    TokForall -> "'forall'"
    TokArrow -> "'->'"
    TokConstraintArrow -> "=>"
    TokDot -> "."
    TokColon -> ":"
    TokDoubleColon -> "'::''"
    TokStar -> "'*'"
    TokLParen -> "'('"
    TokRParen -> "')'"
    TokLBracket -> "'['"
    TokRBracket -> "]"
    TokLBrace -> "'{'"
    TokRBrace -> "}'"
    TokEq -> "'='"
    TokSemicolon -> ";"
    TokType -> "'type'"
    TokData -> "'data'"
    TokTrait -> "'trait'"
    TokImpl -> "'impl'"
    TokInstance -> "'instance'"
    TokFor -> "'for'"
    TokAt -> "'@'"
    TokComma -> ","
    TokLet -> "'let'"
    TokMod -> "'mod'"
    TokPub -> "'pub'"
    TokUse -> "'use'"
    TokPrim s -> "'" ++ s ++ "'"

token :: Parser (Located Token)
token = do
  pos <- getPosition
  t <-
    choice
      [ TokLambda <$ char '\\',
        TokArrow <$ try (string "->"),
        TokConstraintArrow <$ try (string "=>"),
        TokDoubleColon <$ try (string "::"),
        TokDot <$ char '.',
        TokColon <$ char ':',
        TokStar <$ char '*',
        TokLParen <$ char '(',
        TokRParen <$ char ')',
        TokLBracket <$ char '[',
        TokRBracket <$ char ']',
        TokLBrace <$ char '{',
        TokRBrace <$ char '}',
        TokEq <$ char '=',
        TokSemicolon <$ char ';',
        TokComma <$ char ',',
        TokAt <$ char '@',
        stringToken,
        intToken,
        identToken
      ]
  return $ Located pos t
  where
    stringToken = do
      _ <- char '"'
      chars <- many stringChar
      _ <- char '"'
      return $ TokString chars
    stringChar = 
      (char '\\' >> escapeChar) <|> noneOf "\""
    escapeChar = choice
      [ char 'n' >> return '\n'
      , char 't' >> return '\t'
      , char 'r' >> return '\r'
      , char '\\' >> return '\\'
      , char '"' >> return '"'
      ]
    intToken = do
      digits <- many1 digit
      return $ TokInt (read digits)
    identToken = do
      c <- letter <|> char '_' <|> char '#'
      cs <- many (alphaNum <|> char '_')
      return $ case c : cs of
        "type" -> TokType
        "data" -> TokData
        "forall" -> TokForall
        "trait" -> TokTrait
        "impl" -> TokImpl
        "instance" -> TokInstance
        "for" -> TokFor
        "let" -> TokLet
        "mod" -> TokMod
        "pub" -> TokPub
        "use" -> TokUse
        "#true" -> TokTrue
        "#false" -> TokFalse
        s@('#':_) -> TokPrim s
        s -> TokIdent s

tokenize :: String -> Either ParseError [Located Token]
tokenize = parse (many (token <* whitespace) <* eof) ""
  where
    whitespace = skipMany (skipSpace <|> skipLineComment)
    skipSpace = void $ oneOf " \t\r\n"
    skipLineComment = void $ try (string "--") *> skipMany (noneOf "\n")

-- | Check if a primitive string is supported
isSupportedPrimitive :: String -> Bool
isSupportedPrimitive = flip elem supportedPrimitives

-- | List of all supported primitive strings
supportedPrimitives :: [String]
supportedPrimitives =
  [ "#List", "#Unit", "#String", "#Int", "#Bool", "#IO"  -- Types
  , "#nil", "#cons"                                      -- List operations
  , "#print", "#fmapIO", "#pureIO", "#applyIO", "#bindIO" -- IO operations
  , "#intEq", "#stringEq", "#stringConcat", "#ifThenElse", "#intSub", "#exit" -- Other operations
  ]
