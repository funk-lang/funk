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
  type BLam PBinding = SourcePos
  type BApp PBinding = SourcePos
  type BTyLam PBinding = SourcePos
  type BTyApp PBinding = SourcePos
  type BLet PBinding = ()
  type BBlock PBinding = SourcePos
  type BRecord PBinding = ()
  type BRecordCreation PBinding = SourcePos

type PExpr = Expr PBinding

type PStmt = Stmt PBinding

type PBlock = Block PBinding

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

varExpr :: Parser PExpr
varExpr = Var () . PBinding . fmap Ident <$> identTok

parensExpr :: Parser PExpr
parensExpr = tok TokLParen *> expr <* tok TokRParen

lambdaExpr :: Parser PExpr
lambdaExpr = do
  pos <- getPosition
  tok TokLambda
  Located pos' s <- identTok
  let v = PBinding $ Located pos' (Ident s)
  ty <- optionMaybe (tok TokColon *> typeExpr)
  tok TokDot
  Lam pos v ty <$> expr

recordCreationExprDebug :: Parser PExpr
recordCreationExprDebug = do
  pos <- getPosition
  constructorName <- fmap Ident <$> identTok <?> "constructor name"
  tok TokLBrace <?> "opening brace"
  fields <-
    sepBy
      ( do
          field <- fmap Ident <$> identTok <?> "field name"
          tok TokColon <?> "colon after field name"
          e <- expr <?> "field value"
          return (unLocated field, e)
      )
      (tok TokComma <?> "comma between fields")
  tok TokRBrace <?> "closing brace"
  let constructorExpr = Var () (PBinding constructorName)
  return $ RecordCreation pos constructorExpr fields

atomicExpr :: Parser PExpr
atomicExpr =
  choice
    [ try recordCreationExpr,
      varExpr,
      parensExpr,
      try blockExpr
    ]

appExpr :: Parser PExpr
appExpr = do
  f0 <- atomicExpr
  rest f0
  where
    rest f =
      ( do
          pos <- getPosition
          tok TokLBracket
          ty <- typeExpr
          tok TokRBracket
          rest (TyApp pos f ty)
      )
        <|> try
          ( do
              pos <- getPosition
              arg <- atomicExpr
              rest (App pos f arg)
          )
        <|> return f

letStmt :: Parser PStmt
letStmt = do
  v <- fmap (PBinding . fmap Ident) identTok
  ty <- optionMaybe (tok TokColon *> typeExpr)
  tok TokEq
  body <- expr <* tok TokSemicolon
  return $ Let () v ty body

typeStmt :: Parser PStmt
typeStmt = do
  tok TokType
  v <- fmap Ident <$> identTok
  tok TokEq
  ty <- typeExpr <* tok TokSemicolon
  return $ Type v ty

stmt :: Parser PStmt
stmt = choice [try letStmt, try typeStmt, try dataStmt]

dataStmt :: Parser PStmt
dataStmt = do
  tok TokData
  v <- fmap Ident <$> identTok
  tok TokLBrace
  fields <-
    sepBy
      ( do
          field <- fmap Ident <$> identTok
          tok TokColon
          ty <- typeExpr
          return (unLocated field, ty)
      )
      (tok TokComma)
  tok TokRBrace
  return $ Data v fields

recordLiteral :: Parser [(Ident, PExpr)]
recordLiteral = do
  tok TokLBrace
  fields <-
    sepBy
      ( do
          field <- fmap Ident <$> identTok
          tok TokColon
          e <- expr
          return (unLocated field, e)
      )
      (tok TokComma)
  tok TokRBrace
  return fields

recordCreationExpr :: Parser PExpr
recordCreationExpr = do
  pos <- getPosition
  constructorName <- fmap Ident <$> identTok
  tok TokLBrace
  fields <-
    sepBy
      ( do
          field <- fmap Ident <$> identTok
          tok TokColon
          e <- expr
          return (unLocated field, e)
      )
      (tok TokComma)
  tok TokRBrace
  let constructorExpr = Var () (PBinding constructorName)
  return $ RecordCreation pos constructorExpr fields

recordCreationExpr' :: Parser PExpr
recordCreationExpr' = do
  pos <- getPosition
  constructorName <- fmap Ident <$> identTok
  tok TokLBrace
  fields <- fieldList
  tok TokRBrace
  let constructorExpr = Var () (PBinding constructorName)
  return $ RecordCreation pos constructorExpr fields
  where
    fieldList = sepBy fieldAssignment (tok TokComma)
    fieldAssignment = do
      field <- fmap Ident <$> identTok
      tok TokColon
      e <- expr
      return (unLocated field, e)

blockExpr :: Parser PExpr
blockExpr = do
  pos <- getPosition
  tok TokLBrace
  stmts <- many (try stmt)
  e <- expr
  tok TokRBrace
  return $ BlockExpr pos (Block stmts e)

expr :: Parser PExpr
expr =
  choice
    [ try lambdaExpr,
      appExpr
    ]

parseTopLevel :: [Located Token] -> Either ParseError PBlock
parseTopLevel = parse (block <* eof) "<input>"
  where
    block = Block <$> many (try stmt) <*> expr
