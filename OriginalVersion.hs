{-# LANGUAGE TemplateHaskell, FlexibleContexts, StandaloneDeriving, DeriveDataTypeable #-}
module OriginalVersion where

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

data Ann elem annot
-- The type parameters are organized this way because we want the annotation type to
-- be more flexible, but the annotation is the first parameter because it eases 
-- pattern matching.
  = Ann { _annotation :: annot -- ^ The extra information for the AST part
        , _element    :: elem annot -- ^ The original AST part
        }
        
makeReferences ''Ann
        
-- | Semantic and source code related information for an AST node.
data NodeInfo sema src 
  = NodeInfo { _semanticInfo :: sema
             , _sourceInfo :: src
             }
             
makeReferences ''NodeInfo

-- | Semantic information for an AST node. Semantic information is
-- currently heterogeneous.
data SemanticInfo n
  = NoSemanticInfo -- ^ Semantic info type for any node not 
                   -- carrying additional semantic information
  | ScopeInfo { _scopedLocals :: [[GHC.Name]] 
              }
  | NameInfo { _scopedLocals :: [[GHC.Name]]
             , _isDefined :: Bool
             , _nameInfo :: n
             } -- ^ Info corresponding to a name

makeReferences ''SemanticInfo


-- | Location info for different types of nodes
data SpanInfo 
  = NodeSpan { _nodeSpan :: GHC.SrcSpan }
  | ListPos { _listBefore :: String
            , _listAfter :: String
            , _listDefaultSep :: String
            , _listIndented :: Bool
            , _listPos :: GHC.SrcLoc 
            }

makeReferences ''SpanInfo


-- | A list of AST elements
data AnnList e a = AnnList { _annListAnnot :: a 
                           , _annListElems :: [Ann e a]
                           }
                           
makeReferences ''AnnList


data Expr a
  = Var            { _exprName :: Ann Name a 
                   } -- ^ A variable or a data constructor (@ a @)
  | App            { _exprFun :: Ann Expr a
                   , _exprArg :: Ann Expr a
                   } -- ^ Function application (@ f 4 @)
                   -- unary minus omitted
  | Lambda         { _exprBindings :: AnnList Pattern a -- ^ at least one
                   , _exprInner :: Ann Expr a
                   } -- ^ Lambda expression (@ \a b -> a + b @)


-- | Representation of patterns for pattern bindings
data Pattern a
  = VarPat        { _patternName :: Ann Name a 
                  } -- ^ Pattern name binding

data Name a 
  = Name { _nameStr :: String
         }

-- create references 

makeReferences ''Expr
makeReferences ''Pattern
makeReferences ''Name

-- create structural traversal

instance StructuralTraversable elem => StructuralTraversable (Ann elem) where
  traverseUp desc asc f (Ann ann e) = flip Ann <$> (desc *> traverseUp desc asc f e <* asc) <*> f ann
  traverseDown desc asc f (Ann ann e) = Ann <$> f ann <*> (desc *> traverseDown desc asc f e <* asc)

instance StructuralTraversable elem => StructuralTraversable (AnnList elem) where
  traverseUp desc asc f (AnnList a ls) 
    = flip AnnList <$> sequenceA (map (\e -> desc *> traverseUp desc asc f e <* asc) ls) <*> f a
  traverseDown desc asc f (AnnList a ls) 
    = AnnList <$> f a <*> sequenceA (map (\e -> desc *> traverseDown desc asc f e <* asc) ls)

deriveStructTrav ''Expr
deriveStructTrav ''Pattern
deriveStructTrav ''Name

-- deriving Data instances

deriving instance (Typeable a, Data a, Typeable e, Data (e a)) => Data (Ann e a)
deriving instance (Typeable a, Data a, Typeable e, Data (e a)) => Data (AnnList e a)

deriving instance Data a => Data (Expr a)
deriving instance Data a => Data (Pattern a)
deriving instance Data a => Data (Name a)

deriving instance (Data sema, Data src) => Data (NodeInfo sema src)
deriving instance (Data n) => Data (SemanticInfo n)
deriving instance Data SpanInfo

deriving instance Data GHC.SrcLoc
  
instance Data GHC.RealSrcLoc where
    gfoldl k z rsl = z GHC.mkRealSrcLoc `k` GHC.srcLocFile rsl `k` GHC.srcLocLine rsl `k` GHC.srcLocCol rsl

    gunfold k z c = case constrIndex c of
                        1 -> k (k (k (z GHC.mkRealSrcLoc)))

    toConstr _ = con_RSL
    dataTypeOf _ = ty_RSL

con_RSL = mkConstr ty_RSL "RSL" [] Prefix
ty_RSL   = mkDataType "SrcLoc.RealSrcLoc" [con_RSL]

type I = NodeInfo (SemanticInfo GHC.Id) SpanInfo

-- construct the test expression

varF :: GHC.Id
varF = Var.mkGlobalVar GHC.VanillaId (createName 0 (mkSpan 2 3) "f") (Type.mkFunTy intTy intTy) GHC.vanillaIdInfo

varA :: GHC.Id
varA = Var.mkGlobalVar GHC.VanillaId (createName 1 (mkSpan 5 6) "a") intTy GHC.vanillaIdInfo

createName :: Int -> GHC.SrcSpan -> String -> GHC.Name
createName i sp str = GHC.mkExternalName (GHC.getUnique i) thisModule (GHC.mkOccName GHC.varName str) sp

thisModule = GHC.mkModule GHC.mainPackageKey (GHC.mkModuleName "Test")

fileName = GHC.mkFastString "test.hs"

mkSpan :: Int -> Int -> GHC.SrcSpan
mkSpan from to = GHC.mkSrcSpan (GHC.mkSrcLoc fileName 1 from) (GHC.mkSrcLoc fileName 1 from)

src = "\f a -> f a"

testExpr :: Ann Expr I
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
                $ catMaybes $ map (\n -> n ^? annotation&semanticInfo&nameInfo) -- itt a ^. operátort lehetne használni
                $ (testExpr ^? biplateRef :: [Ann Name I])

type I2 = NodeInfo (SemanticInfo GHC.Name) ()

testStructuralTraveral :: Ann Expr I2
testStructuralTraveral 
  = runIdentity $ traverseUp (return ()) (return ()) (Identity . (semanticInfo .- toNameInfo)) 
      $ runIdentity $ traverseUp (return ()) (return ()) (Identity . (sourceInfo .= ())) 
      $ testExpr
  where toNameInfo NoSemanticInfo = NoSemanticInfo
        toNameInfo (ScopeInfo sc) = ScopeInfo sc
        toNameInfo (NameInfo sc dd id) = NameInfo sc dd (GHC.getName id)


