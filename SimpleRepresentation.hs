{-# LANGUAGE TemplateHaskell
           , FlexibleContexts
           , StandaloneDeriving
           , DeriveDataTypeable 
           , KindSignatures
           , TypeFamilies
           , MultiParamTypeClasses
           , FlexibleInstances
           , UndecidableInstances
           #-}
module SimpleRepresentation where

import Control.Reference hiding (element)

import Data.Data
import Data.Generics.Uniplate.Data
import Data.Maybe
import Control.Applicative
import Control.Monad.Identity
import Control.Monad.IO.Class

import qualified GHC
import qualified Name as GHC  
import qualified SrcLoc as GHC  
import qualified Var 
import qualified Type 
import qualified IdInfo as GHC  
import qualified Module as GHC  
import qualified Unique as GHC  
import qualified Outputable as GHC  
import qualified FastString as GHC  
import TysWiredIn (intTy)  
import GHC.Paths ( libdir )

       
-- | Semantic and source code related information for an AST node.
data NodeInfo sema src 
  = NodeInfo { _semanticInfo :: sema
             , _sourceInfo :: src
             }
  deriving Show
             
makeReferences ''NodeInfo

-- * SEMANTIC INFORMATION * --

-- | Semantic information for an AST node. Semantic information is
-- currently heterogeneous.
data NoSemanticInfo
  = NoSemanticInfo -- ^ Semantic info type for any node not 
                   -- carrying additional semantic information
  deriving Show
data ScopeInfo
  = ScopeInfo { _exprScopedLocals :: [[GHC.Name]] 
              }

deriving instance Show ScopeInfo

makeReferences ''ScopeInfo

data NameInfo n
  = NameInfo { _nameScopedLocals :: [[GHC.Name]]
             , _isDefined :: Bool
             , _nameInfo :: n
             } -- ^ Info corresponding to a name
makeReferences ''NameInfo

deriving instance Show n => Show (NameInfo n)

-- * DOMAIN DEFINITION * --

data RangeStage
data RngTemplateStage
data SrcTemplateStage

data Dom name

deriving instance (Data name, Typeable name) => Data (Dom name)

type SemanticInfo (domain :: *) (node :: * -> * -> *) = SemanticInfo' domain (SemaInfoClassify node)

data SameInfoNameCls
data SameInfoExprCls
data SameInfoDefaultCls

type family SemaInfoClassify (node :: * -> * -> *) where
  SemaInfoClassify Name = SameInfoNameCls
  SemaInfoClassify Expr = SameInfoExprCls
  SemaInfoClassify a    = SameInfoDefaultCls

type family SemanticInfo' (domain :: *) (nodecls :: *)

type instance SemanticInfo' (Dom n) SameInfoNameCls = NameInfo n
type instance SemanticInfo' (Dom n) SameInfoExprCls = ScopeInfo
type instance SemanticInfo' (Dom n) SameInfoDefaultCls = NoSemanticInfo

class ( Typeable d
      , Data d
      , Data (SemanticInfo' d SameInfoNameCls)
      , Data (SemanticInfo' d SameInfoExprCls)
      , Data (SemanticInfo' d SameInfoDefaultCls)
      , Show (SemanticInfo' d SameInfoNameCls)
      , Show (SemanticInfo' d SameInfoExprCls)
      , Show (SemanticInfo' d SameInfoDefaultCls)
      ) => Domain d where

instance ( Typeable d
         , Data d
         , Data (SemanticInfo' d SameInfoNameCls)
         , Data (SemanticInfo' d SameInfoExprCls)
         , Data (SemanticInfo' d SameInfoDefaultCls)
         , Show (SemanticInfo' d SameInfoNameCls)
         , Show (SemanticInfo' d SameInfoExprCls)
         , Show (SemanticInfo' d SameInfoDefaultCls)
         ) => Domain d where


class ( Data (SemanticInfo' d (SemaInfoClassify e))
      , Show (SemanticInfo' d (SemaInfoClassify e))
      , Domain d
      ) => DomainWith e d where

instance ( Data (SemanticInfo' d (SemaInfoClassify e))
         , Show (SemanticInfo' d (SemaInfoClassify e))
         , Domain d
         ) => DomainWith e d where

class ( Typeable stage
      , Data stage
      , Data (SpanInfo stage)
      , Data (ListInfo stage)
      , Show (SpanInfo stage)
      , Show (ListInfo stage)
      ) 
         => SourceInfo stage where
  data SpanInfo stage :: *
  data ListInfo stage :: *

instance SourceInfo RangeStage where
  data SpanInfo RangeStage = NodeSpan { _nodeSpan :: GHC.SrcSpan }
    deriving Show
  data ListInfo RangeStage = ListPos  { _listBefore :: String
                                      , _listAfter :: String
                                      , _listDefaultSep :: String
                                      , _listIndented :: Bool
                                      , _listPos :: GHC.SrcLoc 
                                      }
    deriving Show

nodeSpan :: Simple Lens (SpanInfo RangeStage) GHC.SrcSpan
nodeSpan = lens _nodeSpan (\b s -> s { _nodeSpan = b })

listPos :: Simple Lens (ListInfo RangeStage) GHC.SrcLoc
listPos = lens _listPos (\b s -> s { _listPos = b })

data SourceTransform f from to 
  = SourceTransform { transformSpans :: SpanInfo from -> f (SpanInfo to)
                    , transformLists :: ListInfo from -> f (ListInfo to)
                    }

-- * CREATE GENERAL AST ELEMENTS * --

data Ann elem dom stage
-- The type parameters are organized this way because we want the annotation type to
-- be more flexible, but the annotation is the first parameter because it eases 
-- pattern matching.
  = Ann { _annotation :: NodeInfo (SemanticInfo dom elem) (SpanInfo stage) -- ^ The extra information for the AST part
        , _element    :: elem dom stage -- ^ The original AST part
        }

-- | A list of AST elements
data AnnList e dom stage = AnnList { _annListAnnot :: NodeInfo (SemanticInfo dom (AnnList e)) (ListInfo stage)
                                   , _annListElems :: [Ann e dom stage]
                                   }
                   

-- * CREATE SPECIAL AST ELEMENTS * --

data Expr dom st
  = Var            { _exprName :: Ann Name dom st
                   } -- ^ A variable or a data constructor (@ a @)
  | App            { _exprFun :: Ann Expr dom st
                   , _exprArg :: Ann Expr dom st
                   } -- ^ Function application (@ f 4 @)
                   -- unary minus omitted
  | Lambda         { _exprBindings :: AnnList Pattern dom st -- ^ at least one
                   , _exprInner :: Ann Expr dom st
                   } -- ^ Lambda expression (@ \a b -> a + b @)

-- | Representation of patterns for pattern bindings
data Pattern dom st
  = VarPat        { _patternName :: Ann Name dom st
                  } -- ^ Pattern name binding

data Name dom st
  = Name { _nameStr :: String
         }

-- create references 

makeReferences ''Ann
makeReferences ''AnnList

makeReferences ''Expr
makeReferences ''Pattern
makeReferences ''Name

-- create structural traversal

class SourceInfoTraversal elem where
  traverseUpSI :: Monad f => f () -> f () -> SourceTransform f from to -> elem dom from -> f (elem dom to)
  traverseDownSI :: Monad f => f () -> f () -> SourceTransform f from to -> elem dom from -> f (elem dom to)

instance SourceInfoTraversal elem => SourceInfoTraversal (Ann elem) where
  traverseUpSI desc asc f (Ann (NodeInfo sema src) e) 
    = flip Ann <$> (desc *> traverseUpSI desc asc f e <* asc) <*> (NodeInfo sema <$> transformSpans f src)
  traverseDownSI desc asc f (Ann (NodeInfo sema src) e) 
    = Ann <$> (NodeInfo sema <$> transformSpans f src) <*> (desc *> traverseDownSI desc asc f e <* asc)

instance SourceInfoTraversal elem => SourceInfoTraversal (AnnList elem) where
  traverseUpSI desc asc f (AnnList (NodeInfo sema src) ls) 
    = flip AnnList <$> sequenceA (map (\e -> desc *> traverseUpSI desc asc f e <* asc) ls) <*> (NodeInfo sema <$> transformLists f src)
  traverseDownSI desc asc f (AnnList (NodeInfo sema src) ls) 
    = AnnList <$> (NodeInfo sema <$> transformLists f src) <*> sequenceA (map (\e -> desc *> traverseDownSI desc asc f e <* asc) ls)

-- TODO: should be derived
--deriveStructTrav ''Expr
--deriveStructTrav ''Pattern
--deriveStructTrav ''Name

instance SourceInfoTraversal Expr where
  traverseUpSI desc asc f (Var name) = Var <$> traverseUpSI desc asc f name
  traverseUpSI desc asc f (App fun arg) = App <$> traverseUpSI desc asc f fun <*> traverseUpSI desc asc f arg
  traverseUpSI desc asc f (Lambda bnds e) = Lambda <$> traverseUpSI desc asc f bnds <*> traverseUpSI desc asc f e
  traverseDownSI desc asc f (Var name) = Var <$> traverseDownSI desc asc f name
  traverseDownSI desc asc f (App fun arg) = App <$> traverseDownSI desc asc f fun <*> traverseDownSI desc asc f arg
  traverseDownSI desc asc f (Lambda bnds e) = Lambda <$> traverseDownSI desc asc f bnds <*> traverseDownSI desc asc f e

instance SourceInfoTraversal Pattern where
  traverseUpSI desc asc f (VarPat name) = VarPat <$> traverseUpSI desc asc f name
  traverseDownSI desc asc f (VarPat name) = VarPat <$> traverseDownSI desc asc f name

instance SourceInfoTraversal Name where
  traverseUpSI desc asc f (Name name) = pure $ Name name
  traverseDownSI desc asc f (Name name) = pure $ Name name


-- * deriving instances * --

deriving instance (Typeable e, SourceInfo st, Data (e d st), DomainWith e d) => Data (Ann e d st)
deriving instance (Typeable e, SourceInfo st, Data (e d st), DomainWith e d) => Data (AnnList e d st)

deriving instance (DomainWith elem dom, SourceInfo stage, Show (elem dom stage)) => Show (Ann elem dom stage)        
deriving instance (DomainWith elem dom, SourceInfo stage, Show (elem dom stage)) => Show (AnnList elem dom stage)        

deriving instance (Domain d, SourceInfo st) => Data (Expr d st)
deriving instance (Domain d, SourceInfo st) => Data (Pattern d st)
deriving instance (Domain d, SourceInfo st) => Data (Name d st)

deriving instance (Domain d, SourceInfo st) => Show (Expr d st)
deriving instance (Domain d, SourceInfo st) => Show (Pattern d st)
deriving instance (Domain d, SourceInfo st) => Show (Name d st)

deriving instance (Data sema, Data src) => Data (NodeInfo sema src)
deriving instance (Data n) => Data (NameInfo n)
deriving instance Data NoSemanticInfo
deriving instance Data ScopeInfo
deriving instance Data RangeStage
deriving instance Data (SpanInfo RangeStage)
deriving instance Data (ListInfo RangeStage)

deriving instance Data GHC.SrcLoc

instance Show GHC.Name where
  show = GHC.showSDocUnsafe . GHC.ppr
instance Show GHC.Id where
  show = GHC.showSDocUnsafe . GHC.ppr
  
instance Data GHC.RealSrcLoc where
    gfoldl k z rsl = z GHC.mkRealSrcLoc `k` GHC.srcLocFile rsl `k` GHC.srcLocLine rsl `k` GHC.srcLocCol rsl

    gunfold k z c = case constrIndex c of
                        1 -> k (k (k (z GHC.mkRealSrcLoc)))

    toConstr _ = con_RSL
    dataTypeOf _ = ty_RSL

con_RSL = mkConstr ty_RSL "RSL" [] Prefix
ty_RSL   = mkDataType "SrcLoc.RealSrcLoc" [con_RSL]

-- construct the test expression

varF :: GHC.Id
varF = Var.mkGlobalVar GHC.VanillaId (createName 0 (mkSpan 2 3) "f") (Type.mkFunTy intTy intTy) GHC.vanillaIdInfo

varA :: GHC.Id
varA = Var.mkGlobalVar GHC.VanillaId (createName 1 (mkSpan 5 6) "a") intTy GHC.vanillaIdInfo

createName :: Int -> GHC.SrcSpan -> String -> GHC.Name
createName i sp str = GHC.mkExternalName (GHC.getUnique i) thisModule (GHC.mkOccName GHC.varName str) sp

thisModule = GHC.mkModule GHC.mainUnitId (GHC.mkModuleName "Test")

fileName = GHC.mkFastString "test.hs"

mkSpan :: Int -> Int -> GHC.SrcSpan
mkSpan from to = GHC.mkSrcSpan (GHC.mkSrcLoc fileName 1 from) (GHC.mkSrcLoc fileName 1 from)

src = "\f a -> f a"

test = GHC.runGhc (Just libdir) $ liftIO $ 
  do putStrLn "testExpr: "
     print testExpr
     putStrLn "testReference: "
     print testReference
     putStrLn "testBiplate: "
     print testBiplate
     putStrLn "testStructuralTraveral: "
     print testStructuralTraveral


testExpr :: Ann Expr (Dom GHC.Id) RangeStage
testExpr 
  = Ann 
      (NodeInfo (ScopeInfo []) (NodeSpan (mkSpan 1 12)))
      (Lambda 
        (AnnList 
           (NodeInfo NoSemanticInfo (ListPos "" "" " " False GHC.noSrcLoc)) 
           [ (Ann 
                (NodeInfo NoSemanticInfo (NodeSpan (mkSpan 2 3)))
                (VarPat 
                  (Ann (NodeInfo (NameInfo [] True varF) (NodeSpan (mkSpan 2 3)))
                       (Name "f"))))  
           , (Ann 
                (NodeInfo NoSemanticInfo (NodeSpan (mkSpan 5 6)))
                (VarPat 
                  (Ann (NodeInfo (NameInfo [] True varA) (NodeSpan (mkSpan 5 6)))
                       (Name "a"))))  
           ])
        (Ann 
          (NodeInfo (ScopeInfo [[GHC.getName varF, GHC.getName varA]]) (NodeSpan (mkSpan 9 12)))
          (App 
            (Ann 
              (NodeInfo (ScopeInfo [[GHC.getName varF, GHC.getName varA]]) (NodeSpan (mkSpan 9 10)))
              (Var 
                (Ann 
                  (NodeInfo (NameInfo [[GHC.getName varF, GHC.getName varA]] False varF) (NodeSpan (mkSpan 9 10)))
                  (Name "f"))))
            (Ann 
              (NodeInfo (ScopeInfo [[GHC.getName varF, GHC.getName varA]]) (NodeSpan (mkSpan 11 12)))
              (Var 
                (Ann 
                  (NodeInfo (NameInfo [[GHC.getName varF, GHC.getName varA]] False varA) (NodeSpan (mkSpan 11 12)))
                  (Name "a")))) ))) 


-- should be Just "f"
testReference :: Maybe String
testReference = testExpr ^? element&exprInner&element&exprFun&element&exprName&element&nameStr

-- should be ["f", "a", "f", "a"]
testBiplate :: [String]    
testBiplate = map (GHC.occNameString . GHC.nameOccName . Var.varName) 
                $ map (\n -> n ^. annotation&semanticInfo&nameInfo) -- itt a ^. operátort lehetne használni
                $ (testExpr ^? biplateRef :: [Ann Name (Dom GHC.Id) RangeStage])

testStructuralTraveral :: Ann Expr (Dom GHC.Id) RangeStage
testStructuralTraveral 
  = runIdentity $ traverseUpSI (return ()) (return ()) nullspan $ testExpr
  where nullspan = SourceTransform (nodeSpan != GHC.noSrcSpan) (listPos != GHC.noSrcLoc)


