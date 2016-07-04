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
import Data.StructuralTraversal

import Data.Data
import Data.Generics.Uniplate.Data
import Data.Maybe
import Control.Applicative
import Control.Monad.Identity

import qualified GHC
import qualified Name as GHC  
import qualified SrcLoc as GHC  
import qualified Var 
import qualified Type 
import qualified IdInfo as GHC  
import qualified Module as GHC  
import qualified Unique as GHC  
import qualified FastString as GHC  
import TysWiredIn (intTy)  

       
-- | Semantic and source code related information for an AST node.
data NodeInfo sema src 
  = NodeInfo { _semanticInfo :: sema
             , _sourceInfo :: src
             }
             
makeReferences ''NodeInfo

-- * SEMANTIC INFORMATION * --

-- | Semantic information for an AST node. Semantic information is
-- currently heterogeneous.
data NoSemanticInfo
  = NoSemanticInfo -- ^ Semantic info type for any node not 
                   -- carrying additional semantic information
data ScopeInfo
  = ScopeInfo { _exprScopedLocals :: [[GHC.Name]] 
              }

makeReferences ''ScopeInfo

data NameInfo n
  = NameInfo { _nameScopedLocals :: [[GHC.Name]]
             , _isDefined :: Bool
             , _nameInfo :: n
             } -- ^ Info corresponding to a name

makeReferences ''NameInfo

-- * SOURCE INFORMATION * --

-- | Location info for different types of nodes
data NodeSpan 
  = NodeSpan { _nodeSpan :: GHC.SrcSpan }

makeReferences ''NodeSpan

data ListPos
  = ListPos { _listBefore :: String
            , _listAfter :: String
            , _listDefaultSep :: String
            , _listIndented :: Bool
            , _listPos :: GHC.SrcLoc 
            }

makeReferences ''ListPos

-- * DOMAIN DEFINITION * --

data RangeStage
data RngTemplateStage
data SrcTemplateStage

data Dom name stage

type SemanticInfo (domain :: *) (node :: * -> *) = SemanticInfo' domain (SemaInfoClassify node)

data SameInfoNameCls
data SameInfoExprCls
data SameInfoDefaultCls

type family SemaInfoClassify (node :: * -> *) where
  SemaInfoClassify Name = SameInfoNameCls
  SemaInfoClassify Expr = SameInfoExprCls
  SemaInfoClassify a    = SameInfoDefaultCls

type family SemanticInfo' (domain :: *) (nodecls :: *)

type instance SemanticInfo' (Dom n st) SameInfoNameCls = NameInfo n
type instance SemanticInfo' (Dom n st) SameInfoExprCls = ScopeInfo
type instance SemanticInfo' (Dom n st) SameInfoDefaultCls = NoSemanticInfo

type SourceInfo (domain :: *) (node :: * -> *) = SourceInfo' domain (SrcInfoClassify node)

data SrcInfoListCls
data SrcInfoNodeCls

type family SrcInfoClassify (node :: * -> *) where
  SrcInfoClassify (AnnList a) = SrcInfoListCls
  SrcInfoClassify a           = SrcInfoNodeCls

type family SourceInfo' (domain :: *) (nodecls :: *)

type instance SourceInfo' (Dom n RangeStage) SrcInfoListCls = ListPos
type instance SourceInfo' (Dom n RangeStage) SrcInfoNodeCls = NodeSpan


class ( Typeable d
      , Data d
      , Data (SemanticInfo' d SameInfoNameCls)
      , Data (SemanticInfo' d SameInfoExprCls)
      , Data (SemanticInfo' d SameInfoDefaultCls)
      , Data (SourceInfo' d SrcInfoListCls)
      , Data (SourceInfo' d SrcInfoNodeCls)
      ) => Domain d where

instance ( Typeable d
         , Data d
         , Data (SemanticInfo' d SameInfoNameCls)
         , Data (SemanticInfo' d SameInfoExprCls)
         , Data (SemanticInfo' d SameInfoDefaultCls)
         , Data (SourceInfo' d SrcInfoListCls)
         , Data (SourceInfo' d SrcInfoNodeCls)
         ) => Domain d where


class ( Data (SemanticInfo' d (SemaInfoClassify e))
      , Data (SourceInfo' d (SrcInfoClassify e))
      , Domain d
      ) => DomainWith e d where

instance ( Data (SemanticInfo' d (SemaInfoClassify e))
         , Data (SourceInfo' d (SrcInfoClassify e))
         , Domain d
         ) => DomainWith e d where

-- * CREATE GENERAL AST ELEMENTS * --

data Ann elem dom
-- The type parameters are organized this way because we want the annotation type to
-- be more flexible, but the annotation is the first parameter because it eases 
-- pattern matching.
  = Ann { _annotation :: NodeInfo (SemanticInfo dom elem) (SourceInfo dom elem) -- ^ The extra information for the AST part
        , _element    :: elem dom -- ^ The original AST part
        }
        

-- | A list of AST elements
data AnnList e dom = AnnList { _annListAnnot :: NodeInfo (SemanticInfo dom (AnnList e)) (SourceInfo dom (AnnList e))
                             , _annListElems :: [Ann e dom]
                             }
                           

-- * CREATE SPECIAL AST ELEMENTS * --

data Expr dom
  = Var            { _exprName :: Ann Name dom
                   } -- ^ A variable or a data constructor (@ a @)
  | App            { _exprFun :: Ann Expr dom
                   , _exprArg :: Ann Expr dom
                   } -- ^ Function application (@ f 4 @)
                   -- unary minus omitted
  | Lambda         { _exprBindings :: AnnList Pattern dom -- ^ at least one
                   , _exprInner :: Ann Expr dom
                   } -- ^ Lambda expression (@ \a b -> a + b @)

-- | Representation of patterns for pattern bindings
data Pattern dom
  = VarPat        { _patternName :: Ann Name dom
                  } -- ^ Pattern name binding

data Name dom
  = Name { _nameStr :: String
         }

-- create references 

makeReferences ''Ann
makeReferences ''AnnList

makeReferences ''Expr
makeReferences ''Pattern
makeReferences ''Name

-- create structural traversal

--instance StructuralTraversable elem => StructuralTraversable (Ann elem) where
--  traverseUp desc asc f (Ann ann e) = flip Ann <$> (desc *> traverseUp desc asc f e <* asc) <*> f ann
--  traverseDown desc asc f (Ann ann e) = Ann <$> f ann <*> (desc *> traverseDown desc asc f e <* asc)

--instance StructuralTraversable elem => StructuralTraversable (AnnList elem) where
--  traverseUp desc asc f (AnnList a ls) 
--    = flip AnnList <$> sequenceA (map (\e -> desc *> traverseUp desc asc f e <* asc) ls) <*> f a
--  traverseDown desc asc f (AnnList a ls) 
--    = AnnList <$> f a <*> sequenceA (map (\e -> desc *> traverseDown desc asc f e <* asc) ls)

--deriveStructTrav ''Expr
--deriveStructTrav ''Pattern
--deriveStructTrav ''Name

-- deriving Data instances

deriving instance (Typeable e, Data (e d), DomainWith e d) => Data (Ann e d)
deriving instance (Typeable e, Data (e d), DomainWith e d) => Data (AnnList e d)

deriving instance (Domain d) => Data (Expr d)
deriving instance (Domain d) => Data (Pattern d)
deriving instance (Domain d) => Data (Name d)

deriving instance (Data sema, Data src) => Data (NodeInfo sema src)
deriving instance (Data n) => Data (NameInfo n)
deriving instance Data ScopeInfo
deriving instance Data NodeSpan
deriving instance Data ListPos

deriving instance Data GHC.SrcLoc
  
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

testExpr :: Ann Expr (Dom GHC.Id RangeStage)
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
--testReference :: Maybe String
--testReference = testExpr ^? element&exprInner&element&exprFun&element&exprName&element&nameStr

-- should be ["f", "a", "f", "a"]
--testBiplate :: [String]    
--testBiplate = map (GHC.occNameString . GHC.nameOccName . Var.varName) 
--                $ catMaybes $ map (\n -> n ^? annotation&semanticInfo&nameInfo) -- itt a ^. operátort lehetne használni
--                $ (testExpr ^? biplateRef :: [Ann Name I])

--type I2 = NodeInfo (SemanticInfo GHC.Name) ()

--testStructuralTraveral :: Ann Expr I2
--testStructuralTraveral 
--  = runIdentity $ traverseUp (return ()) (return ()) (Identity . (semanticInfo .- toNameInfo)) 
--      $ runIdentity $ traverseUp (return ()) (return ()) (Identity . (sourceInfo .= ())) 
--      $ testExpr
--  where toNameInfo NoSemanticInfo = NoSemanticInfo
--        toNameInfo (ScopeInfo sc) = ScopeInfo sc
--        toNameInfo (NameInfo sc dd id) = NameInfo sc dd (GHC.getName id)


