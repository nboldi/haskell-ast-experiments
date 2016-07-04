{-# LANGUAGE TemplateHaskell
           , FlexibleContexts
           , StandaloneDeriving
           , DeriveDataTypeable
           , KindSignatures
           , TypeOperators
           , TypeFamilies
           , RankNTypes
           , UndecidableInstances
           , PolyKinds
           , DataKinds
           , ConstraintKinds
           #-}



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



data a :| b = a :| b
  deriving (Typeable, Data)

infixr 4 :|


data (t :: *) ::- (nodeann :: *) -- = a ::- b
  deriving (Typeable)

data (node :: * -> * -> * -> *) :- (ann :: *) -- = a :- b
  deriving (Typeable)

infixr 5 ::-
infixr 6 :-


-- Selector type
data (a :: *) :& b
  deriving (Typeable)

infixr 7 :&
{-
deriving instance (Data (a), Data b, Typeable a, Typeable b) => Data (a ::- b)
deriving instance (Data (a), Data b, Typeable a, Typeable b) => Data (a :- b)

-}
{-
--type family (n :: (* -> * -> *) -> * -> * -> *) :<-- (edom :: *) where
type family astnode :<-- edom where
  astnode :<-- (e :<- dom) = astnode dom (AstInfo (NodeSemantic (Syntactic :& Step) e dom) (NodeSemantic Semantic e dom) )
  --n e dom (NodeSemantic e dom)
data e :<- dom

infixr 5 :<--
infixr 6 :<-
-}


--type Applied e dom = Node e dom (NodeSemantic e dom)

--data InfoType = 
data Syntactic
data Semantic
data Step
{-
type family NodeSemantic t n dom where
    NodeSemantic t1 n1 ((t1 ::- n1 :- i1) :| (t2 ::- n2 :- i2)) = i1
    NodeSemantic t2 n2 ((t1 ::- n1 :- i1) :| (t2 ::- n2 :- i2)) = i2
    NodeSemantic t3 n3 ((t1 ::- n1 :- i1) :| (t2 ::- n2 :- i2)) = ()
    NodeSemantic t1 n1 ((t1 ::- n1 :- i1) :| l)                 = i1
    NodeSemantic t2 n1 ((t1 ::- n2 :- i1) :| l)                 = NodeSemantic t1 n1 l
-}

--type NodeType = Step -> * -> * -> *

data AstNode (node :: * -> * -> * -> *) (step :: *) (dom :: *) (ann :: *)
  = AstNode
  { _astinfo :: ann
  , _astnode :: node step dom ann
  }

makeReferences ''AstNode

data AstNodeList (node :: * -> * -> * -> *) (step :: *) (dom :: *) (ann :: *)
  = AstNodeList
  { _astNodeList :: [node step dom ann] -- itt annotált elemeknek kellene lenniük
  }

makeReferences ''AstNodeList

data AstInfo (syn :: *) (sem :: *)
  = AstInfo
  { _syn :: syn
  , _sem :: sem
  }

makeReferences ''AstInfo


type Node (astnode :: (* -> * -> * -> *) -> * -> * -> * -> *) (node :: * -> * -> * -> *) (dom :: *) (step :: *)
    = astnode node step dom (AstInfoT node step dom)

type AstInfoT node step dom
    = AstInfo (NodeSemantic (Syntactic :& step) node dom) (NodeSemantic (Semantic :& step) node dom)

data ANY (step :: *) (dom :: *) (ann :: *) deriving (Typeable)

{-type family NodeSemantic (t :: *) (node :: * -> * -> * -> *) (dom :: *) where
    NodeSemantic t1 (aggr x) ((t1 ::- (aggr ANY) :- i1) :| l)                 = i1
    NodeSemantic t2 (aggr x) ((t1 ::- n1 :- i1) :| (t2 ::- (aggr ANY) :- i2)) = i2
    NodeSemantic t1 n1 ((t1 ::- n1 :- i1) :| (t2 ::- n2 :- i2)) = i1
    NodeSemantic t2 n2 ((t1 ::- n1 :- i1) :| (t2 ::- n2 :- i2)) = i2
    NodeSemantic t3 n3 ((t1 ::- n1 :- i1) :| (t2 ::- n2 :- i2)) = ()
    NodeSemantic t1 n1 ((t1 ::- n1 :- i1) :| l)                 = i1
    NodeSemantic t2 n1 ((t1 ::- n2 :- i1) :| l)                 = NodeSemantic t1 n1 l
-}


type family NodeSemantic (t :: *) (node :: * -> * -> * -> *) (dom :: *) where
    NodeSemantic t n d = NormNodeSemantic (SearchNodeSemantic t n d)

type family NormNodeSemantic t where
    NormNodeSemantic Ambiguous = Ambiguous
    NormNodeSemantic NoFound = ()
    NormNodeSemantic (Found i) = i
    NormNodeSemantic (FoundAggrANY i) = i
    NormNodeSemantic (FoundANY i) = i

{-
    NodeSemantic t n (a :| b) = UnitOr (NodeSemantic t n a) (NodeSemantic t n b)
    NodeSemantic t (aggr x) (t ::- (aggr ANY) :- i) = i
    NodeSemantic t n (t ::- n :- i) = i
    NodeSemantic t1 n1 (t2 ::- n2 :- i) = ()
-}
data NoFound
data Ambiguous
data Found a
data FoundAggrANY a
data FoundANY a

type family SearchNodeSemantic (t :: *) (node :: * -> * -> * -> *) (dom :: *) where
    SearchNodeSemantic t n (a :| b) = MergeNS (SearchNodeSemantic t n a) (SearchNodeSemantic t n b)
    SearchNodeSemantic t (aggr x) (t ::- (aggr ANY) :- i) = FoundAggrANY i
    SearchNodeSemantic t x (t ::- ANY :- i) = FoundANY i
    SearchNodeSemantic t n (t ::- n :- i) = Found i
    SearchNodeSemantic t1 n1 (t2 ::- n2 :- i) = NoFound

type family MergeNS t1 r2 where
    MergeNS NoFound NoFound = NoFound
    MergeNS x Ambiguous = Ambiguous
    MergeNS Ambiguous x = Ambiguous
    MergeNS a NoFound = a
    MergeNS NoFound b = b
    MergeNS (Found a) (Found b) = Found a
    MergeNS (Found a) x = Found a
    MergeNS x (Found b) = Found b
    MergeNS (FoundAggrANY a) x = FoundAggrANY a
    MergeNS x (FoundAggrANY b) = FoundAggrANY b
    MergeNS (FoundANY a) x = FoundANY a
    MergeNS x (FoundANY b) = FoundANY b




data Pattern (step :: *) (dom :: *) (ann :: *)
  = VarPat        { _patternName :: Node AstNode Name dom step-- AstNode :<-- Name :<- dom -- Node Name dom ann
                  } -- ^ Pattern name binding

data Name step dom ann
  = Name { _nameStr :: String
         }

--data NameInfo = NameInfo String
--data TypeInfo = TypeInfo (Type ())


-- | Semantic information for an AST node. Semantic information is
-- currently heterogeneous.
--data SemanticInfo n
data NoSemanticInfo = NoSemanticInfo -- ^ Semantic info type for any node not 
                   -- carrying additional semantic information
data ScopeInfo = ScopeInfo { _scscopedLocals :: [[GHC.Name]] 
              }
data NameInfo n = NameInfo { _niscopedLocals :: [[GHC.Name]]
             , _isDefined :: Bool
             , _nameInfo :: n
             } -- ^ Info corresponding to a name

--makeReferences ''SemanticInfo
makeReferences ''NoSemanticInfo
makeReferences ''ScopeInfo
makeReferences ''NameInfo


-- | Location info for different types of nodes
--data SpanInfo 
data NodeSpan = NodeSpan { _nodeSpan :: GHC.SrcSpan }
data ListPos = ListPos { _listBefore :: String
            , _listAfter :: String
            , _listDefaultSep :: String
            , _listIndented :: Bool
            , _listPos :: GHC.SrcLoc 
            }

--makeReferences ''SpanInfo
makeReferences ''NodeSpan
makeReferences ''ListPos



data Expr step dom ann
  = Var            { _exprName     :: Node AstNode Name dom step -- Applied Name dom --Node Name dom (Semantic Name dom)
                   } -- ^ A variable or a data constructor (@ a @)
  | App            { _exprFun      :: Node AstNode Expr dom step -- Applied Expr dom --Node Expr dom (Semantic Expr dom)
                   , _exprArg      :: Node AstNode Expr dom step -- Applied Expr dom --Node Expr dom ann
                   } -- ^ Function application (@ f 4 @)
                   -- unary minus omitted
  | Lambda         { _exprBindings :: Node AstNode (AstNodeList Pattern) dom step -- NodeList Pattern dom ann -- ^ at least one
                   , _exprInner    :: Node AstNode Expr dom step -- Node Expr dom ann
                   } -- ^ Lambda expression (@ \a b -> a + b @)

--Node AstNode Name dom step

-- create references 

makeReferences ''Expr
makeReferences ''Pattern
makeReferences ''Name




type Domain
  =  Syntactic :& Step ::- Expr             :- ScopeInfo
  :| Semantic  :& Step ::- Expr             :- ()
  :| Syntactic :& Step ::- Name             :- (NameInfo String)
  :| Syntactic :& Step ::- AstNodeList ANY  :- Int
  :| Syntactic :& Step ::- AstNodeList Name :- [String]
--  :| Pattern ::- NodeInfo (NameInfo Type.Var) ()
--  :| NodeList Pattern ::- ListPos


{-

The Domain is a table where every line is a annotation directive.
The first row defines the the compiling state. In this example we have got two types: Syntactic and Semantic.
The second row defines the step of AST processing. Actualy the compiler state and step are a separeted tuple.
That means, the semantic of these elements are not fixed, they just recomendation.
If you have an compiling evironment where you can descibe the processing in one dimension, you can use one row.
And naturally you can use more dimension than two also, just you need an appropriate compositional type.
The a third row defines the node type and the fourth defines the annotation type.

Let be Node an abstract generic ast node type.
The Node is a simple type synonym. Paremetrization of it is a custom issue.
It can be different in another processing environment.
In this case they have four type parameter:
  * skeleton-type  - the wrapping type which hold together the ast elements
  * node-type      - a concete ast element type for example: expression, name or pattern
  * domain         - a set of annotation directives
  * step           - explicit parameter of processing state

A parametrized Node type mappings  to AstNode.
The AstNode is the skeleton type and a real haskell type.
The parametrization of it:
  * node-type
  * step
  * domain
  * annotation-type
Can see, these paramers are similar as the elements of annotation directives.
That means, if you specified an annotation of node-type in every step and compiling state.
The a framework find the right annotation type for a concrete step and collect all for every compiling state.
The AstNode can store these annotations with a collection type (AstInfo).

So in this example we have two compiling state(Syntactic, Semantic) and one processing step(Step)
The annotation type of Expr in Syntactic and Step is ScopeInfo.
And in Semantic and Step is ().
In this case the paramtrization of AstNode with Step is "AstNode AstNode Expr Step Domain (AstInfo ScopeInfo ())"
That means AstNode contains an "AstInfo ScopeInfo ()" and the AstInfo store the two annotation.
AstInfo has two parameter. The first is the Syntactic and the second is the Semantic annotation in a specified step.

-}


type E1 = Node AstNode Expr Domain Step
type E1R = AstNode Expr Step Domain (AstInfo ScopeInfo ())
type E2 = Node AstNode (AstNodeList Expr) Domain Step
type E2R = AstNode (AstNodeList Expr) Step Domain (AstInfo Int ())
type E3 = Node AstNode (AstNodeList Name) Domain Step
type E3R = AstNode (AstNodeList Name) Step Domain (AstInfo [String] ())

type Test =
    ( E1 ~ E1R
    , E2 ~ E2R
    , E3 ~ E3R
    )

check :: Test => a
check = undefined




-- create structural traversal

instance (StructuralTraversable (node step dom)) => StructuralTraversable (AstNode node step dom) where
  traverseUp desc asc f (AstNode info node) = flip AstNode <$> (desc *> traverseUp desc asc f node <* asc) <*> f info
  traverseDown desc asc f (AstNode info node) = AstNode <$> f info <*> (desc *> traverseDown desc asc f node <* asc)
{-
instance (StructuralTraversable (e dom)) => StructuralTraversable (NodeList e dom) where
  traverseUp desc asc f (NodeList a ls) 
    = flip NodeList <$> sequenceA (map (\e -> desc *> traverseUp desc asc f e <* asc) ls) <*> f a
  traverseDown desc asc f (NodeList a ls) 
    = NodeList <$> f a <*> sequenceA (map (\e -> desc *> traverseDown desc asc f e <* asc) ls)
-}
instance (StructuralTraversable (node step dom)) => StructuralTraversable (AstNodeList node step dom) where
  traverseUp desc asc f (AstNodeList nodes) = AstNodeList <$> sequenceA (map (traverseUp desc asc f) nodes)
  traverseDown desc asc f (AstNodeList nodes) = AstNodeList <$> sequenceA (map (traverseDown desc asc f) nodes)


deriveStructTrav ''Expr
deriveStructTrav ''Pattern
deriveStructTrav ''Name
deriveStructTrav ''AstInfo




-- deriving Data instances

deriving instance ( Typeable node, Typeable step, Typeable dom, Typeable ann
                  , Data ann, Data (node step dom ann)
                  ) => Data (AstNode node step dom ann)
deriving instance ( Typeable node, Typeable step, Typeable dom, Typeable ann
                  , Data (node step dom ann), Data ann
                  ) => Data (AstNodeList node step dom ann)

deriving instance ( Typeable step, Typeable dom, Typeable ann
                  , Data (AstInfoT Name step dom), Data (AstInfoT Expr step dom), Data (AstInfoT (AstNodeList Pattern) step dom)
                  , Data (Node AstNode Name dom step), Data (Node AstNode (AstNodeList Pattern) dom step)
                  ) => Data (Expr step dom ann)

deriving instance ( Typeable step, Typeable dom, Typeable ann
                  , Data (AstInfoT Name step dom)
                  , Data (Node AstNode Name dom step)
                  ) => Data (Pattern step dom ann)

--deriving instance Typeable Name
--deriving instance ( Typeable step, Typeable dom, Typeable ann
--                  ) => Data (Name step dom ann)


-- NodeInfo NoSemanticInfo ScopeInfo NameInfo NodeSpan ListPos


deriving instance Data NoSemanticInfo
deriving instance Data ScopeInfo
deriving instance (Data name) => Data (NameInfo name)
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



type Domain2 n
  = Semantic  :& Step ::- Expr :- ScopeInfo
 :| Semantic  :& Step ::- Name :- NameInfo n
 :| Semantic  :& Step ::- ANY :- NoSemanticInfo
 :| Syntactic :& Step ::- AstNodeList ANY :- ListPos
 :| Syntactic :& Step ::- ANY :- NodeSpan

testExpr :: Node AstNode Expr (Domain2 GHC.Id) Step
testExpr 
  = AstNode
      (AstInfo (NodeSpan (mkSpan 1 12)) (ScopeInfo []))
      (Lambda 
        (AstNode -- ezt itt el kéne tűntetni
          (AstInfo (ListPos "" "" " " False GHC.noSrcLoc) NoSemanticInfo)
          (AstNodeList
            [ -- (AstNode 
              --    (AstInfo (NodeSpan (mkSpan 2 3)) NoSemanticInfo)
                 (VarPat 
                   (AstNode (AstInfo (NodeSpan (mkSpan 2 3)) (NameInfo [] True varF))
                            (Name "f"))) -- )  
            , -- (AstNode 
              --    (AstInfo (NodeSpan (mkSpan 5 6)) NoSemanticInfo)
                 (VarPat 
                   (AstNode (AstInfo (NodeSpan (mkSpan 5 6)) (NameInfo [] True varA))
                            (Name "a"))) -- )  
            ]))
        (AstNode 
          (AstInfo (NodeSpan (mkSpan 9 12)) (ScopeInfo [[GHC.getName varF, GHC.getName varA]]))
          (App 
            (AstNode 
              (AstInfo (NodeSpan (mkSpan 9 10)) (ScopeInfo [[GHC.getName varF, GHC.getName varA]]))
              (Var 
                (AstNode 
                  (AstInfo (NodeSpan (mkSpan 9 10)) (NameInfo [[GHC.getName varF, GHC.getName varA]] False varF))
                  (Name "f"))))
            (AstNode 
              (AstInfo (NodeSpan (mkSpan 11 12)) (ScopeInfo [[GHC.getName varF, GHC.getName varA]]))
              (Var 
                (AstNode 
                  (AstInfo (NodeSpan (mkSpan 11 12)) (NameInfo [[GHC.getName varF, GHC.getName varA]] False varA))
                  (Name "a")))) )))


-- should be Just "f"
testReference :: Maybe String
testReference = testExpr ^? astnode & exprInner & astnode & exprFun & astnode & exprName & astnode & nameStr


-- should be ["f", "a", "f", "a"]
--testBiplate :: [String]    
testBiplate = map (GHC.occNameString . GHC.nameOccName . Var.varName) 
                $ map (\n -> n ^. astinfo & sem & nameInfo) -- itt a ^. operátort lehetne használni
                $ (testExpr ^? biplateRef :: [Node AstNode Name (Domain2 GHC.Id) Step])


testStructuralTraveral :: Node AstNode Expr (Domain2 GHC.Id) Step
testStructuralTraveral 
  = runIdentity $ traverseUp (return ()) (return ()) (Identity . (sem .- _)) 
    -- $ runIdentity $ traverseUp (return ()) (return ()) (Identity . (syn .= ())) 
      $ testExpr
  --where toNameInfo NoSemanticInfo = NoSemanticInfo
  --      toNameInfo (ScopeInfo sc) = ScopeInfo sc
  --      toNameInfo (NameInfo sc dd id) = NameInfo sc dd (GHC.getName id)




