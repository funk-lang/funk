{-# LANGUAGE TypeFamilies #-}

module Funk.Parser where

import Data.Functor (($>))
import Funk.Term
import Funk.Token
import Text.Parsec

type Parser = Parsec [Located Token] ()

type PType = Type (Located Ident)

type PKind = Kind (Located Ident)

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

primTok :: String -> Parser ()
primTok expected =
  tokenPrim show updatePos testTok
  where
    testTok (Located _ (TokPrim s))
      | s == expected = Just ()
      | otherwise = Nothing
    testTok _ = Nothing
    updatePos _ (Located pos _) _ = pos

typeVar :: Parser PType
typeVar = TVar . fmap Ident <$> identTok

listType :: Parser PType
listType = primTok "#List" *> (TList <$> atomicType)

unitType :: Parser PType
unitType = primTok "#Unit" $> TUnit

stringType :: Parser PType
stringType = primTok "#String" $> TString

intType :: Parser PType
intType = primTok "#Int" $> TInt

boolType :: Parser PType
boolType = primTok "#Bool" $> TBool

ioType :: Parser PType
ioType = do
  primTok "#IO"
  arg <- atomicType
  return (TIO arg)

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
      listType,
      ioType,
      unitType,
      stringType,
      intType,
      boolType,
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

constraintType :: Parser PType
constraintType = do
  traitName <- fmap Ident <$> identTok
  typeVars <- many (fmap Ident <$> identTok)
  tok TokConstraintArrow
  targetType <- typeAppExpr
  tok TokArrow
  TConstraint traitName typeVars targetType <$> typeExpr

typeExpr :: Parser PType
typeExpr = try constraintType <|> chainr1 typeAppExpr (tok TokArrow $> TArrow)

kindVar :: Parser PKind
kindVar = KVar . fmap Ident <$> identTok

starKind :: Parser PKind
starKind = tok TokStar $> KStar

parensKind :: Parser PKind
parensKind = tok TokLParen *> kindExpr <* tok TokRParen

atomicKind :: Parser PKind
atomicKind =
  choice
    [ kindVar,
      starKind,
      parensKind
    ]

kindExpr :: Parser PKind
kindExpr = chainr1 atomicKind (tok TokArrow $> KArrow)

varExpr :: Parser PExpr
varExpr = do
  firstIdent <- identTok
  rest <- many (tok TokDot *> identTok)
  case rest of
    [] -> return $ Var () (PBinding (fmap Ident firstIdent))
    _ -> let allIdents = firstIdent : rest
             modPathParts = map (Ident . unLocated) (init allIdents)
             varName = PBinding (fmap Ident (last allIdents))
             modPath = ModulePath modPathParts
         in return $ QualifiedVar () modPath varName

primUnitExpr :: Parser PExpr
primUnitExpr = primTok "#Unit" $> PrimUnit ()

primStringExpr :: Parser PExpr
primStringExpr = do
  Located _ (TokString s) <- tokenPrim show updatePos testTok <?> "string literal"
  return $ PrimString () s
  where
    testTok (Located _ (TokString s)) = Just (Located undefined (TokString s))
    testTok _ = Nothing
    updatePos _ (Located pos _) _ = pos

primIntExpr :: Parser PExpr
primIntExpr = do
  Located _ (TokInt i) <- tokenPrim show updatePos testTok <?> "integer literal"
  return $ PrimInt () i
  where
    testTok (Located _ (TokInt i)) = Just (Located undefined (TokInt i))
    testTok _ = Nothing
    updatePos _ (Located pos _) _ = pos

primTrueExpr :: Parser PExpr
primTrueExpr = tok TokTrue $> PrimTrue ()

primFalseExpr :: Parser PExpr
primFalseExpr = tok TokFalse $> PrimFalse ()

primNilExpr :: Parser PExpr
primNilExpr = do
  primTok "#nil"
  tok TokLBracket
  ty <- typeExpr
  tok TokRBracket
  return $ PrimNil () ty

primConsExpr :: Parser PExpr
primConsExpr = do
  primTok "#cons"
  tok TokLBracket
  ty <- typeExpr
  tok TokRBracket
  headExpr <- atomicExpr
  PrimCons () ty headExpr <$> atomicExpr

primPrintExpr :: Parser PExpr
primPrintExpr = 
  try (do
    primTok "#print"
    arg <- atomicExpr
    return $ PrimPrint () arg
  ) <|> (primTok "#print" $> PrimPrintValue ())

primFmapIOExpr :: Parser PExpr
primFmapIOExpr = 
  try (do
    primTok "#fmapIO"
    f <- atomicExpr
    io <- atomicExpr
    return $ PrimFmapIO () f io
  ) <|> (primTok "#fmapIO" $> PrimFmapIOValue ())

primPureIOExpr :: Parser PExpr
primPureIOExpr = 
  try (do
    primTok "#pureIO"
    arg <- atomicExpr
    return $ PrimPureIO () arg
  ) <|> (primTok "#pureIO" $> PrimPureIOValue ())

primApplyIOExpr :: Parser PExpr
primApplyIOExpr = 
  try (do
    primTok "#applyIO"
    iof <- atomicExpr
    iox <- atomicExpr
    return $ PrimApplyIO () iof iox
  ) <|> (primTok "#applyIO" $> PrimApplyIOValue ())

primBindIOExpr :: Parser PExpr
primBindIOExpr = 
  try (do
    primTok "#bindIO"
    iox <- atomicExpr
    f <- atomicExpr
    return $ PrimBindIO () iox f
  ) <|> (primTok "#bindIO" $> PrimBindIOValue ())

primIntEqExpr :: Parser PExpr
primIntEqExpr = 
  try (do
    primTok "#intEq"
    e1 <- atomicExpr
    e2 <- atomicExpr
    return $ PrimIntEq () e1 e2
  ) <|> (primTok "#intEq" $> PrimIntEqValue ())

primStringEqExpr :: Parser PExpr
primStringEqExpr = 
  try (do
    primTok "#stringEq"
    e1 <- atomicExpr
    e2 <- atomicExpr
    return $ PrimStringEq () e1 e2
  ) <|> (primTok "#stringEq" $> PrimStringEqValue ())

primIfThenElseExpr :: Parser PExpr
primIfThenElseExpr = 
  try (do
    _ <- primTok "#ifThenElse"
    c <- atomicExpr
    t <- atomicExpr
    e <- atomicExpr
    return $ PrimIfThenElse () c t e
  ) <|> (primTok "#ifThenElse" $> PrimIfThenElseValue ())

primIntSubExpr :: Parser PExpr
primIntSubExpr = 
  try (do
    _ <- primTok "#intSub"
    e1 <- atomicExpr
    e2 <- atomicExpr
    return $ PrimIntSub () e1 e2
  ) <|> (primTok "#intSub" $> PrimIntSubValue ())

primExitExpr :: Parser PExpr
primExitExpr = 
  try (do
    primTok "#exit"
    arg <- atomicExpr
    return $ PrimExit () arg
  ) <|> (primTok "#exit" $> PrimExitValue ())

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

atomicExpr :: Parser PExpr
atomicExpr =
  choice
    [ try recordCreationExpr,
      primUnitExpr,
      primStringExpr,
      primIntExpr,
      primTrueExpr,
      primFalseExpr,
      primNilExpr,
      primConsExpr,
      primPrintExpr,
      primFmapIOExpr,
      primPureIOExpr,
      primApplyIOExpr,
      primBindIOExpr,
      primIntEqExpr,
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

pubLetStmt :: Parser PStmt
pubLetStmt = do
  tok TokPub
  tok TokLet
  v <- fmap (PBinding . fmap Ident) identTok
  ty <- optionMaybe (tok TokColon *> typeExpr)
  tok TokEq
  body <- expr <* tok TokSemicolon
  return $ PubLet () v ty body

typeStmt :: Parser PStmt
typeStmt = do
  tok TokType
  v <- fmap Ident <$> identTok
  tok TokEq
  ty <- typeExpr <* tok TokSemicolon
  return $ Type v ty

pubTypeStmt :: Parser PStmt
pubTypeStmt = do
  tok TokPub
  tok TokType
  v <- fmap Ident <$> identTok
  tok TokEq
  ty <- typeExpr <* tok TokSemicolon
  return $ PubType v ty

stmt :: Parser PStmt
stmt = choice [try pubLetStmt, try letStmt, try pubTypeStmt, try typeStmt, try pubDataStmt, try dataStmt, try pubTraitStmt, try traitStmt, try implStmt, try useStmt, try pubUseStmt]

-- Updated dataStmt to handle forall syntax
dataStmt :: Parser PStmt
dataStmt = do
  tok TokData
  v <- fmap Ident <$> identTok
  typeParams <- many (fmap Ident <$> identTok)
  tok TokEq
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
  if null typeParams
    then return $ Data v fields
    else return $ DataForall v typeParams fields

traitStmt :: Parser PStmt
traitStmt = do
  tok TokTrait
  v <- fmap Ident <$> identTok
  vars <- many (do
    tok TokLParen
    var <- fmap Ident <$> identTok
    tok TokDoubleColon
    kind <- kindExpr
    tok TokRParen
    return (var, Just kind))
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
  case vars of
    [] -> return $ Trait v [] methods
    _ -> return $ TraitWithKinds v vars methods

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
  return $ RecordCreation () (Var () (PBinding constructorName)) fields

recordCreationExpr' :: Parser PExpr
recordCreationExpr' = do
  constructorName <- fmap Ident <$> identTok
  tok TokLBrace
  fields <- fieldList
  tok TokRBrace
  return $ RecordCreation () (Var () (PBinding constructorName)) fields
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
      try primIfThenElseExpr,
      try primIntSubExpr,
      try primStringEqExpr,
      try primStringConcatExpr,
      try primExitExpr,
      appExpr
    ]

-- Helper parser for module paths like "Foo.Bar.Baz"  
modulePath :: Parser ModulePath
modulePath = do
  first <- fmap (Ident . unLocated) identTok
  rest <- many (try (tok TokDot *> fmap (Ident . unLocated) identTok))
  return $ ModulePath (first : rest)

-- Parser for pub data statements
pubDataStmt :: Parser PStmt
pubDataStmt = do
  tok TokPub
  tok TokData
  v <- fmap Ident <$> identTok
  typeParams <- many (fmap Ident <$> identTok)
  tok TokEq
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
  if null typeParams
    then return $ PubData v fields
    else return $ PubDataForall v typeParams fields

-- Parser for pub trait statements  
pubTraitStmt :: Parser PStmt
pubTraitStmt = do
  tok TokPub
  tok TokTrait
  v <- fmap Ident <$> identTok
  vars <- many (do
    tok TokLParen
    var <- fmap Ident <$> identTok
    tok TokDoubleColon
    kind <- kindExpr
    tok TokRParen
    return (var, Just kind))
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
  if null vars
    then return $ PubTrait v [] methods
    else return $ PubTraitWithKinds v vars methods

-- Parser for use statements
useStmt :: Parser PStmt
useStmt = do
  tok TokUse
  modPath <- modulePath
  items <- choice [
    tok TokDot *> tok TokStar $> [],  -- use Module.*
    tok TokLBrace *> sepBy (fmap (Ident . unLocated) identTok) (tok TokComma) <* tok TokRBrace,  -- use Module { item1, item2 }
    return []  -- use Module (import all)
    ]
  tok TokSemicolon
  if null items
    then return $ UseAll modPath
    else return $ Use modPath items

-- Parser for pub use statements
pubUseStmt :: Parser PStmt  
pubUseStmt = do
  tok TokPub
  tok TokUse
  modPath <- modulePath
  items <- choice [
    tok TokDot *> tok TokStar $> [],  -- pub use Module.*
    tok TokLBrace *> sepBy (fmap (Ident . unLocated) identTok) (tok TokComma) <* tok TokRBrace,  -- pub use Module { item1, item2 }
    return []  -- pub use Module (import all)
    ]
  tok TokSemicolon
  if null items
    then return $ PubUseAll modPath
    else return $ PubUse modPath items

parseTopLevel :: [Located Token] -> Either ParseError PBlock
parseTopLevel = parse (topLevelBlock <* eof) ""
  where
    topLevelBlock = do
      stmts <- many (try stmt)
      -- Top level programs contain only statements, no final expression
      -- We add a unit expression as a placeholder to satisfy the Block type
      return $ Block stmts (PrimUnit ())

primStringConcatExpr :: Parser PExpr
primStringConcatExpr = 
  try (do
    primTok "#stringConcat"
    e1 <- atomicExpr
    e2 <- atomicExpr
    return $ PrimStringConcat () e1 e2
  ) <|> (primTok "#stringConcat" $> PrimStringConcatValue ())