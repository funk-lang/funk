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

-- | Core primitive operations
data CorePrimitive
  = PrimPrint                            -- Primitive print function
  | PrimFmapIO                           -- Primitive fmap for IO
  | PrimPureIO                           -- Primitive pure for IO
  | PrimApplyIO                          -- Primitive apply for IO
  | PrimBindIO                           -- Primitive bind for IO
  | PrimIntEq                            -- Primitive int equality
  | PrimStringEq                         -- Primitive string equality
  | PrimStringConcat                     -- Primitive string concatenation
  | PrimIfThenElse                       -- Primitive if/then/else
  | PrimIntSub                           -- Primitive integer subtraction
  | PrimExit                             -- Exit with code
  deriving (Eq, Show)

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
  | CorePrim CorePrimitive [CoreExpr]    -- Primitive operations with arguments
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

-- | Core module can be either a program with main or a library
data CoreModule 
  = CoreProgram' CoreProgram              -- Program with main function
  | CoreLibrary [CoreDataType] [CoreBinding]  -- Library with data types and bindings
  deriving (Eq)

-- | Core binding (for libraries)
data CoreBinding = CoreBinding
  { bindingName :: String
  , bindingType :: CoreType
  , bindingExpr :: CoreExpr
  } deriving (Eq)

-- | Pretty printing for core types
prettyTyVar :: TyVar -> Doc
prettyTyVar (TyVar s) = text s

-- | Pretty printing for core primitives
prettyCorePrimitive :: CorePrimitive -> Doc
prettyCorePrimitive PrimPrint = text "print"
prettyCorePrimitive PrimFmapIO = text "fmapIO"
prettyCorePrimitive PrimPureIO = text "pureIO"
prettyCorePrimitive PrimApplyIO = text "applyIO"
prettyCorePrimitive PrimBindIO = text "bindIO"
prettyCorePrimitive PrimIntEq = text "intEq"
prettyCorePrimitive PrimStringEq = text "stringEq"
prettyCorePrimitive PrimStringConcat = text "stringConcat"
prettyCorePrimitive PrimIfThenElse = text "ifThenElse"
prettyCorePrimitive PrimIntSub = text "intSub"
prettyCorePrimitive PrimExit = text "exit"

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
prettyCoreExpr p (CorePrim prim args) =
  let prim' = prettyCorePrimitive prim
      args' = map (prettyCoreExpr (p+1)) args
  in case args of
       [] -> text "#" <> prim'  -- Primitive value (partially applied)
       _  -> parensIf (p > 0) ((text "#" <> prim') <+> hsep args')

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

-- | Pretty printing for core modules
prettyCoreModule :: CoreModule -> Doc
prettyCoreModule (CoreProgram' prog) = prettyCoreProgram prog
prettyCoreModule (CoreLibrary datatypes bindings) =
  let datatypes' = vcat $ map prettyCoreDataType datatypes
      bindings' = vcat $ map prettyCoreBinding bindings
  in datatypes' $$ bindings'

-- | Pretty printing for core bindings
prettyCoreBinding :: CoreBinding -> Doc
prettyCoreBinding (CoreBinding name ty expr) =
  text "let" <+> text name <+> text ":" <+> prettyCoreType 0 ty <+> text "=" <+> prettyCoreExpr 0 expr

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

instance Show CoreModule where
  show = render . prettyCoreModule

instance Show CoreBinding where
  show = render . prettyCoreBinding