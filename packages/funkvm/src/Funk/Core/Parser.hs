{-|
Module      : Funk.Core.Parser
Description : Parser for Funk Core IR language (.funkc files)
Copyright   : (c) 2025
License     : MIT

This module provides parsers for the Funk Core intermediate representation.
Core files (.funkc) can contain either library modules with bindings or
programs with a main function.
-}
module Funk.Core.Parser where

import Funk.Core
import Text.Parsec
import Text.Parsec.String (Parser)
import Text.Parsec.Language (haskellDef)
import qualified Text.Parsec.Token as Tok

-- Token definitions for the Core language
lexer :: Tok.TokenParser ()
lexer = Tok.makeTokenParser haskellDef
  { Tok.reservedNames = ["let", "forall", "case", "of", "data", "return", "True", "False", "Unit", "String", "Int", "Bool", "IO", "List"]
  , Tok.reservedOpNames = ["=", "->", "\\", ".", "@", "::", "#", ">>=" ]
  , Tok.commentLine = "--"
  , Tok.commentStart = "{-"
  , Tok.commentEnd = "-}"
  }

-- Use qualified access to avoid naming conflicts
identifier :: Parser String
identifier = Tok.identifier lexer

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = Tok.reservedOp lexer

parens :: Parser a -> Parser a
parens = Tok.parens lexer

symbol :: String -> Parser String
symbol = Tok.symbol lexer

whiteSpace :: Parser ()
whiteSpace = Tok.whiteSpace lexer

integer :: Parser Integer
integer = Tok.integer lexer

stringLiteral :: Parser String
stringLiteral = Tok.stringLiteral lexer

colon :: Parser String
colon = Tok.colon lexer

-- Parse variables (including underscores)
parseVar :: Parser Var
parseVar = Var <$> (symbol "_" <|> identifier)

-- Parse type variables (including single letters and numbers)
parseTyVar :: Parser TyVar
parseTyVar = TyVar <$> (identifier <|> do
    -- Handle numbered type variables like a0, a1, etc.
    char1 <- letter
    rest <- many alphaNum
    return $ char1 : rest)

-- Parse core types
parseCoreType :: Parser CoreType
parseCoreType = parseForallType <|> parseArrowType

parseForallType :: Parser CoreType
parseForallType = do
  reserved "forall"
  tv <- parseTyVar
  reservedOp "."
  ty <- parseCoreType
  return $ TyForall tv ty

parseArrowType :: Parser CoreType
parseArrowType = parseArrowType' where
  parseArrowType' = do
    ty1 <- parseAtomicType
    option ty1 $ do
      reservedOp "->"
      ty2 <- parseArrowType'
      return $ TyArrow ty1 ty2

parseParenType :: Parser CoreType
parseParenType = parens parseCoreType

parseAtomicType :: Parser CoreType
parseAtomicType = 
      parseParenType
  <|> parseBuiltinType
  <|> (CoreTyVar <$> parseTyVar)

parseBuiltinType :: Parser CoreType
parseBuiltinType = 
      (reserved "Unit" >> return TyUnit)
  <|> (reserved "String" >> return TyString)
  <|> (reserved "Int" >> return TyInt)
  <|> (reserved "Bool" >> return TyBool)
  <|> (TyIO <$> (reserved "IO" >> parseAtomicType))
  <|> (TyList <$> (reserved "List" >> parseAtomicType))
  <|> (symbol "_" >> return (CoreTyVar (TyVar "_")))  -- Type wildcard
  <|> (TyCon <$> identifier)

parseTypeApp :: Parser CoreType
parseTypeApp = do
  base <- parseBuiltinType
  args <- many parseAtomicType
  return $ foldl TyApp base args

-- Parse core expressions
parseCoreExpr :: Parser CoreExpr
parseCoreExpr = 
      parseLet
  <|> parseLambda
  <|> parseCase
  <|> parseApplication

parseLet :: Parser CoreExpr
parseLet = do
  reserved "let"
  var <- parseVar
  reservedOp "="
  val <- parseCoreExpr
  -- Check for semicolon and continuation
  option val $ do
    _ <- symbol ";"
    body <- parseCoreExpr  -- This could be another let or the final expression
    return $ CoreLet var val body

parseLambda :: Parser CoreExpr
parseLambda = do
  reservedOp "\\"
  var <- parseVar
  _ <- colon
  ty <- parseCoreType
  reservedOp "."
  body <- parseCoreExpr
  return $ CoreLam var ty body

parseCase :: Parser CoreExpr
parseCase = do
  reserved "case"
  scrut <- parseCoreExpr
  reserved "of"
  alts <- many1 parseAlt
  return $ CoreCase scrut alts

parseAlt :: Parser (CorePat, CoreExpr)
parseAlt = do
  pat <- parsePattern
  reservedOp "->"
  expr <- parseCoreExpr
  return (pat, expr)

parsePattern :: Parser CorePat
parsePattern = 
      (symbol "()" >> return PatUnit)
  <|> (PatVar <$> parseVar)
  <|> parseConPattern

parseConPattern :: Parser CorePat
parseConPattern = do
  conName <- identifier
  vars <- many parseVar
  return $ PatCon conName vars

parseApplication :: Parser CoreExpr
parseApplication = do
  base <- parseAtomicExpr
  args <- many parseAtomicExpr
  return $ foldl CoreApp base args

parseAtomicExpr :: Parser CoreExpr
parseAtomicExpr = 
      parseLiteral
  <|> parseParenExpr
  <|> parseVariable
  <|> parsePrimitive

parseParenExpr :: Parser CoreExpr
parseParenExpr = do
  _ <- symbol "("
  -- Try to parse empty parentheses as unit
  (symbol ")" >> return CoreUnit) <|> do
    expr <- parseCoreExpr
    _ <- symbol ")"
    return expr

parseVariable :: Parser CoreExpr
parseVariable = CoreVar . Var <$> (symbol "_" <|> identifier)

parseLiteral :: Parser CoreExpr
parseLiteral = 
      (CoreString <$> stringLiteral)
  <|> (CoreInt . fromIntegral <$> integer)
  <|> (reserved "True" >> return CoreTrue)
  <|> (reserved "False" >> return CoreFalse)

parsePrimitive :: Parser CoreExpr
parsePrimitive = do
  _ <- symbol "#"
  primName <- identifier
  args <- many parseAtomicExpr
  prim <- case primName of
    "print" -> return PrimPrint
    "fmapIO" -> return PrimFmapIO
    "pureIO" -> return PrimPureIO
    "applyIO" -> return PrimApplyIO
    "bindIO" -> return PrimBindIO
    "intEq" -> return PrimIntEq
    "stringEq" -> return PrimStringEq
    "stringConcat" -> return PrimStringConcat
    "ifThenElse" -> return PrimIfThenElse
    "intSub" -> return PrimIntSub
    "exit" -> return PrimExit
    _ -> fail $ "Unknown primitive: " ++ primName
  return $ CorePrim prim args

-- Parse core bindings (for library modules)
parseCoreBinding :: Parser CoreBinding
parseCoreBinding = do
  reserved "let"
  name <- identifier
  _ <- colon
  ty <- parseCoreType
  reservedOp "="
  expr <- parseCoreExpr
  return $ CoreBinding name ty expr

-- Parse core modules (can be either proper modules with bindings or just expressions)
parseCoreModule :: Parser CoreModule
parseCoreModule = do
  whiteSpace
  -- First check if this looks like it starts with "let" - if so, parse as module
  isModule <- option False (lookAhead (reserved "let" >> return True))
  if isModule
    then do
      bindings <- many1 (parseCoreBinding <* whiteSpace)
      eof
      return $ CoreLibrary [] bindings
    else do
      -- Parse as a single expression (treat as main)
      expr <- parseCoreExpr
      whiteSpace
      eof
      -- Wrap the expression as a main binding
      let mainBinding = CoreBinding "main" (TyIO TyUnit) expr
      return $ CoreLibrary [] [mainBinding]

-- Parse a .funkc file
parseFunkcFile :: String -> Either ParseError CoreModule
parseFunkcFile input = parse parseCoreModule "funkc" input
