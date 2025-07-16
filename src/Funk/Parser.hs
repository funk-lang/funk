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
  type BTyApp PBinding = SourcePos
  type BLet PBinding = ()
  type BBlock PBinding = SourcePos
  type BRecord PBinding = ()
  type BRecordCreation PBinding = ()

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
  vars <- many1 (fmap Ident <$> identTok)
  tok TokDot
  body <- typeExpr
  return $ foldr TForall body vars

atomicType :: Parser PType
atomicType =
  choice
    [ try forallType,
      typeVar,
      parensType
    ]

typeAppExpr :: Parser PType
typeAppExpr = do
  t0 <- atomicType
  rest t0
  where
    rest t =
      ( do
          arg <- atomicType
          rest (TApp t arg)
      )
        <|> return t

typeExpr :: Parser PType
typeExpr = chainr1 typeAppExpr (tok TokArrow $> TArrow)

varExpr :: Parser PExpr
varExpr = Var () . PBinding . fmap Ident <$> identTok

parensExpr :: Parser PExpr
parensExpr = tok TokLParen *> expr <* tok TokRParen

lambdaExpr :: Parser PExpr
lambdaExpr = do
  pos <- getPosition
  tok TokLambda
  ( do
      -- Type abstraction
      tok TokForall
      vars <- sepBy1 (fmap Ident <$> identTok) (tok TokComma)
      tok TokDot
      body <- expr
      return $ foldr (\v acc -> TyApp pos acc (TVar v)) body vars
    )
    <|> ( do
            -- Multiple parameter lambda: \f reader -> expr
            params <- many1 identTok
            tok TokArrow
            body <- expr
            return $ foldr (\(Located pos' s) acc -> 
              let v = PBinding $ Located pos' (Ident s)
              in Lam pos v Nothing acc) body params
        )
    <|> ( do
            -- Single parameter lambda: \f . expr (old syntax)
            Located pos' s <- identTok
            let v = PBinding $ Located pos' (Ident s)
            ty <- optionMaybe (tok TokColon *> typeExpr)
            tok TokDot
            Lam pos v ty <$> expr
        )

recordCreationExprDebug :: Parser PExpr
recordCreationExprDebug = do
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
  return $ RecordCreation () constructorExpr fields

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
  tok TokLet
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
stmt = choice [try letStmt, try typeStmt, try dataStmt, try traitStmt, try implStmt]

-- Updated dataStmt to handle forall syntax
dataStmt :: Parser PStmt
dataStmt = do
  tok TokData
  v <- fmap Ident <$> identTok
  tok TokEq
  -- Handle optional forall quantification
  mbForallPart <- optionMaybe $ do
    tok TokForall
    vars <- many1 (fmap Ident <$> identTok)
    tok TokDot
    return vars
  -- Parse the record type
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
  case mbForallPart of
    Nothing -> return $ Data v fields
    Just vars -> return $ DataForall v vars fields

traitStmt :: Parser PStmt
traitStmt = do
  tok TokTrait
  v <- fmap Ident <$> identTok
  vars <- many (fmap Ident <$> identTok)
  tok TokLBrace
  methods <-
    sepBy
      ( do
          method <- fmap Ident <$> identTok
          tok TokColon
          ty <- typeExpr
          return (unLocated method, ty)
      )
      (tok TokComma)
  tok TokRBrace
  return $ Trait v vars methods

implStmt :: Parser PStmt
implStmt = do
  tok TokInstance
  traitName <- fmap Ident <$> identTok
  -- Optionally parse 'forall <vars> .'
  (vars, targetType) <-
    (do
      tok TokForall
      vs <- many1 (fmap Ident <$> identTok)
      tok TokDot
      ty <- typeExpr
      return (vs, ty)
    ) <|> (do
      ty <- typeExpr
      return ([], ty)
    )
  tok TokEq
  tok TokLBrace
  methods <-
    sepBy
      ( do
          method <- fmap Ident <$> identTok
          tok TokEq
          e <- expr
          return (unLocated method, e)
      )
      (tok TokComma)
  tok TokRBrace
  return $ Impl traitName vars targetType methods

recordLiteral :: Parser [(Ident, PExpr)]
recordLiteral = do
  tok TokLBrace
  fields <-
    sepBy
      ( do
          field <- fmap Ident <$> identTok
          tok TokEq
          e <- expr
          return (unLocated field, e)
      )
      (tok TokComma)
  tok TokRBrace
  return fields

recordCreationExpr :: Parser PExpr
recordCreationExpr = do
  constructorName <- fmap Ident <$> identTok
  tok TokLBrace
  fields <-
    sepBy
      ( do
          field <- fmap Ident <$> identTok
          tok TokEq
          e <- expr
          return (unLocated field, e)
      )
      (tok TokComma)
  tok TokRBrace
  let constructorExpr = Var () (PBinding constructorName)
  return $ RecordCreation () constructorExpr fields

recordCreationExpr' :: Parser PExpr
recordCreationExpr' = do
  constructorName <- fmap Ident <$> identTok
  tok TokLBrace
  fields <- fieldList
  tok TokRBrace
  let constructorExpr = Var () (PBinding constructorName)
  return $ RecordCreation () constructorExpr fields
  where
    fieldList = sepBy fieldAssignment (tok TokComma)
    fieldAssignment = do
      field <- fmap Ident <$> identTok
      tok TokEq
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
