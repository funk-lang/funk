
module Funk.Core where

import Text.PrettyPrint hiding ((<>))
import qualified Text.PrettyPrint as PP

-- | Core language based on System F with explicit type abstractions and applications
-- This is the target language for compilation from the surface language

-- | Variables in the core language
newtype Var = Var String
  deriving (Eq, Ord, Show)

-- | Type variables in the core language  
newtype TyVar = TyVar String
  deriving (Eq, Ord, Show)

-- | Core types (System F types)
data CoreType
  = CoreTyVar TyVar                       -- Type variables
  | TyArrow CoreType CoreType            -- Function types
  | TyForall TyVar CoreType              -- Universal quantification
  | TyApp CoreType CoreType              -- Type application
  | TyUnit                               -- Unit type
  | TyString                             -- String type
  | TyInt                                -- Int type
  | TyBool                               -- Bool type
  | TyList CoreType                      -- List type
  | TyIO CoreType                        -- IO type
  | TyCon String                         -- Type constructors (State, etc.)
  deriving (Eq)

-- | Core expressions (System F terms)
data CoreExpr
  = CoreVar Var                          -- Variables
  | CoreLam Var CoreType CoreExpr        -- Lambda abstractions (typed)
  | CoreApp CoreExpr CoreExpr            -- Function application
  | CoreTyLam TyVar CoreExpr             -- Type lambda (type abstraction)
  | CoreTyApp CoreExpr CoreType          -- Type application
  | CoreLet Var CoreExpr CoreExpr        -- Let bindings
  | CoreCase CoreExpr [(CorePat, CoreExpr)] -- Case expressions
  | CoreCon String [CoreExpr]            -- Constructor applications
  | CoreUnit                             -- Unit value
  | CoreString String                    -- String literal
  | CoreInt Int                          -- Integer literal
  | CoreTrue                             -- True literal
  | CoreFalse                            -- False literal
  | CoreNil CoreType                     -- Empty list
  | CoreCons CoreType CoreExpr CoreExpr  -- List constructor
  | CoreDict String CoreType [CoreExpr]  -- Dictionary construction
  | CoreDictAccess CoreExpr String       -- Dictionary method access
  | CoreReturn CoreExpr                  -- IO return (pure value wrapped in IO)
  | CoreBind CoreExpr CoreExpr           -- IO bind (monadic sequencing)
  | CorePrint CoreExpr                   -- Primitive print function
  | CoreFmapIO CoreExpr CoreExpr         -- Primitive fmap for IO
  | CorePureIO CoreExpr                  -- Primitive pure for IO
  | CoreApplyIO CoreExpr CoreExpr        -- Primitive apply for IO
  | CoreBindIO CoreExpr CoreExpr         -- Primitive bind for IO
  | CoreIntEq CoreExpr CoreExpr          -- Primitive int equality
  | CoreStringEq CoreExpr CoreExpr       -- Primitive string equality
  | CoreIfThenElse CoreExpr CoreExpr CoreExpr -- Primitive if/then/else
  | CoreIntSub CoreExpr CoreExpr         -- Primitive integer subtraction
  | CoreExit CoreExpr                    -- Exit with code
  deriving (Eq)

-- | Core patterns for case expressions
data CorePat
  = PatVar Var                           -- Variable patterns
  | PatCon String [Var]                  -- Constructor patterns
  | PatUnit                              -- Unit pattern
  deriving (Eq, Show)

-- | Core data type definitions
data CoreDataType = CoreDataType
  { coreDataName :: String
  , coreDataTyVars :: [TyVar]
  , coreDataCons :: [(String, [CoreType])]
  } deriving (Eq)

-- | Core program consisting of data types and a main function
data CoreProgram = CoreProgram
  { coreDataTypes :: [CoreDataType]
  , coreMain :: CoreExpr  -- This should be of type IO ()
  } deriving (Eq)

-- | Pretty printing for core types
prettyTyVar :: TyVar -> Doc
prettyTyVar (TyVar s) = text s

prettyCoreType :: Int -> CoreType -> Doc
prettyCoreType _ (CoreTyVar tv) = prettyTyVar tv
prettyCoreType p (TyArrow t1 t2) =
  let s1 = prettyCoreType (p+1) t1
      s2 = prettyCoreType p t2
  in parensIf (p > 0) (s1 <+> text "->" <+> s2)
prettyCoreType p (TyForall tv t) =
  let tv' = prettyTyVar tv
      t' = prettyCoreType p t
  in parensIf (p > 0) ((text "forall" <+> tv' <+> text ".") <+> t')
prettyCoreType p (TyApp t1 t2) =
  let s1 = prettyCoreType p t1
      s2 = prettyCoreType (p+1) t2
  in parensIf (p > 0) (s1 <+> s2)
prettyCoreType _ TyUnit = text "Unit"
prettyCoreType _ TyString = text "String"
prettyCoreType _ TyInt = text "Int"
prettyCoreType _ TyBool = text "Bool"
prettyCoreType p (TyList t) =
  let t' = prettyCoreType (p+1) t
  in parensIf (p > 0) (text "List" <+> t')
prettyCoreType p (TyIO t) =
  let t' = prettyCoreType (p+1) t
  in parensIf (p > 0) (text "IO" <+> t')
prettyCoreType _ (TyCon name) = text name

-- | Pretty printing for core expressions
prettyVar :: Var -> Doc
prettyVar (Var s) = text s

prettyCoreExpr :: Int -> CoreExpr -> Doc
prettyCoreExpr _ (CoreVar v) = prettyVar v
prettyCoreExpr p (CoreLam v ty body) =
  let v' = prettyVar v
      ty' = prettyCoreType 0 ty
      body' = prettyCoreExpr 0 body
  in parensIf (p > 0) ((text "\\" <> v' <> text ":" <> ty' <> text ".") <+> body')
prettyCoreExpr p (CoreApp e1 e2) =
  let e1' = prettyCoreExpr p e1
      e2' = prettyCoreExpr (p+1) e2
  in parensIf (p > 0) (e1' <+> e2')
prettyCoreExpr p (CoreTyLam tv body) =
  let tv' = prettyTyVar tv
      body' = prettyCoreExpr 0 body
  in parensIf (p > 0) ((text "forall" <> tv' <> text ".") <+> body')
prettyCoreExpr p (CoreTyApp expr ty) =
  let expr' = prettyCoreExpr p expr
      ty' = prettyCoreType 0 ty
  in parensIf (p > 0) (expr' <+> (text "@" <> ty'))
prettyCoreExpr p (CoreLet v val body) =
  let v' = prettyVar v
      val' = prettyCoreExpr 0 val
      body' = prettyCoreExpr 0 body
  in parensIf (p > 0) (text "let" <+> v' <+> text "=" <+> (val' <> text ";") <+> body')
prettyCoreExpr p (CoreCase scrut alts) =
  let scrut' = prettyCoreExpr 0 scrut
      alts' = vcat $ map prettyAlt alts
  in parensIf (p > 0) (text "case" <+> scrut' <+> text "of" <+> alts')
prettyCoreExpr p (CoreCon name args) =
  let args' = map (prettyCoreExpr (p+1)) args
  in parensIf (p > 0 && not (null args)) (text name <+> hsep args')
prettyCoreExpr _ CoreUnit = text "()"
prettyCoreExpr _ (CoreString s) = doubleQuotes (text s)
prettyCoreExpr _ (CoreInt i) = int i
prettyCoreExpr _ CoreTrue = text "True"
prettyCoreExpr _ CoreFalse = text "False"
prettyCoreExpr p (CoreNil ty) =
  let ty' = prettyCoreType 0 ty
  in parensIf (p > 0) ((text "[]" <> text "@") <> ty')
prettyCoreExpr p (CoreCons ty headExpr tailExpr) =
  let ty' = prettyCoreType 0 ty
      head' = prettyCoreExpr (p+1) headExpr
      tail' = prettyCoreExpr (p+1) tailExpr
  in parensIf (p > 0) (head' <+> (text "::" <> text "@" <> ty') <+> tail')
prettyCoreExpr p (CoreDict traitName targetType methods) =
  let traitName' = text traitName
      targetType' = prettyCoreType 0 targetType
      methods' = map (prettyCoreExpr (p+1)) methods
  in parensIf (p > 0) ((traitName' <> text "@" <> targetType') <+> text "{" <+> hsep (PP.punctuate (text ",") methods') <+> text "}")
prettyCoreExpr p (CoreDictAccess dict methodName) =
  let dict' = prettyCoreExpr (p+1) dict
      methodName' = text methodName
  in parensIf (p > 0) (dict' <> text "." <> methodName')
prettyCoreExpr p (CoreReturn expr) =
  let expr' = prettyCoreExpr (p+1) expr
  in parensIf (p > 0) (text "return" <+> expr')
prettyCoreExpr p (CoreBind expr1 expr2) =
  let expr1' = prettyCoreExpr (p+1) expr1
      expr2' = prettyCoreExpr (p+1) expr2
  in parensIf (p > 0) (expr1' <+> text ">>=" <+> expr2')
prettyCoreExpr p (CorePrint expr) =
  let expr' = prettyCoreExpr (p+1) expr
  in parensIf (p > 0) (text "print" <+> expr')
prettyCoreExpr p (CoreFmapIO f io) =
  let f' = prettyCoreExpr (p+1) f
      io' = prettyCoreExpr (p+1) io
  in parensIf (p > 0) (text "fmapIO" <+> f' <+> io')
prettyCoreExpr p (CorePureIO expr) =
  let expr' = prettyCoreExpr (p+1) expr
  in parensIf (p > 0) (text "pureIO" <+> expr')
prettyCoreExpr p (CoreApplyIO iof iox) =
  let iof' = prettyCoreExpr (p+1) iof
      iox' = prettyCoreExpr (p+1) iox
  in parensIf (p > 0) (text "applyIO" <+> iof' <+> iox')
prettyCoreExpr p (CoreBindIO iox f) =
  let iox' = prettyCoreExpr (p+1) iox
      f' = prettyCoreExpr (p+1) f
  in parensIf (p > 0) (text "bindIO" <+> iox' <+> f')

prettyCoreExpr p (CoreIntEq e1 e2) =
  let e1' = prettyCoreExpr (p+1) e1
      e2' = prettyCoreExpr (p+1) e2
  in parensIf (p > 0) (text "intEq" <+> e1' <+> e2')

prettyCoreExpr p (CoreStringEq e1 e2) =
  let e1' = prettyCoreExpr (p+1) e1
      e2' = prettyCoreExpr (p+1) e2
  in parensIf (p > 0) (text "stringEq" <+> e1' <+> e2')

prettyCoreExpr p (CoreIfThenElse c t e) =
  let c' = prettyCoreExpr (p+1) c
      t' = prettyCoreExpr (p+1) t
      e' = prettyCoreExpr (p+1) e
  in parensIf (p > 0) (text "if" <+> c' <+> text "then" <+> t' <+> text "else" <+> e')

prettyCoreExpr p (CoreIntSub e1 e2) =
  let e1' = prettyCoreExpr (p+1) e1
      e2' = prettyCoreExpr (p+1) e2
  in parensIf (p > 0) (text "intSub" <+> e1' <+> e2')

prettyCoreExpr p (CoreExit e) =
  let e' = prettyCoreExpr (p+1) e
  in parensIf (p > 0) (text "exit" <+> e')

prettyAlt :: (CorePat, CoreExpr) -> Doc
prettyAlt (pat, expr) =
  let pat' = prettyPat pat
      expr' = prettyCoreExpr 0 expr
  in pat' <+> text "->" <+> expr'

prettyPat :: CorePat -> Doc
prettyPat (PatVar v) = prettyVar v
prettyPat (PatCon name vars) = text name <+> hsep (map prettyVar vars)
prettyPat PatUnit = text "()"

-- | Pretty printing for data types
prettyCoreDataType :: CoreDataType -> Doc
prettyCoreDataType (CoreDataType name tyvars cons) =
  let name' = text name
      tyvars' = hsep (map prettyTyVar tyvars)
      cons' = vcat $ map prettyCon cons
  in text "data" <+> name' <+> tyvars' <+> text "=" <+> cons'
  where
    prettyCon (conName, types) =
      let types' = map (prettyCoreType 1) types
      in text conName <+> hsep types'

-- | Pretty printing for core programs
prettyCoreProgram :: CoreProgram -> Doc
prettyCoreProgram (CoreProgram datatypes main) =
  let datatypes' = vcat $ map prettyCoreDataType datatypes
      main' = prettyCoreExpr 0 main
  in datatypes' $$ text "" $$ main'

-- | Helper function for parentheses
parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id

-- | Show instances using pretty printing
instance Show CoreType where
  show = render . prettyCoreType 0

instance Show CoreExpr where
  show = render . prettyCoreExpr 0

instance Show CoreProgram where
  show = render . prettyCoreProgram