-- A port of https://github.com/sweirich/pi-forall
-- This version distinguishes between global and local names
-- Global names are strings (which must be unique). Local names 
-- are represented by indices.
module PiForall.Syntax where

import AutoEnv
import AutoEnv.LocalName
import qualified AutoEnv.Bind as B
import qualified AutoEnv.Pat.Simple as Pat
import qualified AutoEnv.Pat.Scoped as Scoped
import qualified AutoEnv.Pat.LocalBind as Local

import AutoEnv.MonadScoped

import Text.ParserCombinators.Parsec.Pos (SourcePos, newPos)
import Data.Maybe qualified as Maybe
import Data.Set qualified as Set
import Data.Vec qualified as Vec


import Unsafe.Coerce (unsafeCoerce)

inScope :: Scope n -> (SNatI n => a) -> a 
inScope s = withSNat (scope_size s) 

getScope :: Pattern p -> Scope p
getScope p = Scope { scope_size = Pat.size p, scope_locals = patLocals p }

-- | names of top level declarations/definitions
-- must be unique
type GlobalName = String

-- | names of type constructors, like 'list'
type TyConName = String

-- | names of data constructors, like 'cons'
type DataConName = String


-- | types and terms (combined syntax)
type Typ = Term

data Term (n :: Nat)
  = TyType
  | Lam (Local.Bind Term Term n)
  | Var (Fin n)
  | Global GlobalName
  | Pi (Typ n) (Local.Bind Term Typ n)
  | Pos SourcePos (Term n)
  | Let (Term n) (Local.Bind Term Term n)
  | TyCon TyConName [Typ n]
  | DataCon DataConName [Term n]
  | Case (Term n) [Match n]
  | App (Term n) (Term n)
  | Ann (Term n) (Typ n)
  | -- | Equality type  `a = b`
    TyEq (Term n) (Term n)
  | -- | Proof of equality `Refl`
    TmRefl 
  | -- | equality type elimination  `subst a by pf`
    Subst (Term n) (Term n) 
  | -- | witness to an equality contradiction
    Contra (Term n)
  | TrustMe
  | PrintMe 

-- | Patterns (without embedded type annotations)
-- `p` is the number of variables bound by the pattern
-- `n` is the number of free variables in type annotations in the pattern
-- There are none, so this variable is always unconstrained.
-- LocalName is used for printing only, irrelevant for alpha-equivalence
data Pattern (p :: Nat)  where
  PatCon :: DataConName -> PatList p -> Pattern p
  PatVar :: LocalName -> Pattern N1

-- | lists of patterns where variables at each position bind 
-- later in the pattern

data PatList p where
  PNil :: PatList N0
  PCons :: Pattern p1 -> PatList p2 -> PatList (Plus p2 p1)


-- A single branch in a match expression. Binds a pattern
-- with expression variables, with an expression body
data Match (n :: Nat)
  = forall p. SNatI p => Branch (Pat.Bind Term Term (Pattern p) n)

-- | Local assumption, either declarations of local variables or definitions (i.e. constraints on variables already in scope)
data Local p n where
  LocalDecl :: LocalName -> Typ n -> Local N1 n -- binding assumption
  LocalDef  :: Fin n -> Term n -> Local N0 n -- nonbinding assumption

-- | Telescopes: lists of local assumptions 
-- These are scoped patterns because they include terms 
-- that can mention variables that are already in scope
-- or that have been bound earlier in the pattern.
-- 'p' is the number of variables introduced by the telescope
-- 'n' is the scope depth for A1 (and A2 has depth S n, etc.)
data Telescope p n where
  Tele :: Telescope N0 n
  TCons :: Scoped.Rebind (Local p) (Telescope p1) n -> Telescope (Plus p1 p) n

(<:>) :: forall p p1 n. Local p n -> Telescope p1 (Plus p n) 
  -> Telescope (Plus p1 p) n
e <:> t = TCons (Scoped.Rebind e t)

infixr <:>

{-
-- | TODO snoc a new local entry to a telescope
(<:>) :: forall p1 p n. Telescope p n -> Local p1 (Plus p n) -> Telescope (Plus p1 p) n
Tele <:> e = 
  case axiomPlusZ @p1 of
    Refl -> TCons (Scoped.Rebind e Tele)
TCons (Scoped.Rebind (x :: Local p2 n) (t :: Telescope p3 (Plus p2 n))) <:> e = 
  case axiomAssoc @p1 @p3 @p2 of 
    Refl -> undefined
      -- let e' :: Local p1 (Plus (Plus p3 p2) n)
      --     e' = _  in
      -- TCons (Scoped.Rebind x (t <:> e'))
-}

-- | 
-- | Datatype definitions
data DataDef = forall n.
  DataDef
  { 
    data_delta :: Telescope n Z,
    data_sort :: Typ Z,
    data_constructors :: [ConstructorDef n]
  }
  

data ConstructorDef n = forall m.
  ConstructorDef
  { con_name :: DataConName,
    con_theta :: Telescope m n
  }

data ScopedConstructorDef = forall n. 
  ScopedConstructorDef 
    (Telescope n Z) (ConstructorDef n)


-- | The names of type/data constructors used in the module
data ConstructorNames = ConstructorNames
  { tconNames :: Set.Set String,
    dconNames :: Set.Set String
  }


-- Toplevel components of modules
data ModuleEntry
  = ModuleDecl { declName :: GlobalName, declType :: Typ Z }
  | ModuleDef  { declName :: GlobalName, declTerm :: Term Z }
  | ModuleData { declName :: GlobalName, declData :: DataDef }
  
-- | module names
type ModuleName = String

-- | A Module has a name, a list of imports, a list of declarations,
--   and a set of constructor names (which affect parsing).
data Module = Module
  { moduleName :: ModuleName,
    moduleImports :: [ModuleImport],
    moduleEntries :: [ModuleEntry],
    moduleConstructors :: ConstructorNames
  }
  
-- | References to other modules (brings declarations and definitions into scope)
newtype ModuleImport = ModuleImport ModuleName
  deriving (Show, Eq, Ord)
  

-------------------------------------------------------

-- * Definitions related to datatypes

-- | Is this the syntax of a number?
isNumeral :: Term n -> Maybe Int
isNumeral (Pos _ t) = isNumeral t
isNumeral (DataCon c []) | c == "Zero" = Just 0
isNumeral (DataCon c [t]) | c == "Succ" =
  do n <- isNumeral t; return (n + 1)
isNumeral _ = Nothing

-- | Is this pattern a variable
isPatVar :: Pattern p -> Bool
isPatVar (PatVar _) = True
isPatVar _ = False

strip :: Term n -> Term n
strip (Pos _ tm) = strip tm
strip (Ann tm _) = strip tm
strip tm = tm

-- | Partial inverse of Pos
unPos :: Term n -> Maybe SourcePos
unPos (Pos p _) = Just p
unPos _ = Nothing

-- | Tries to find a Pos inside a term, otherwise just gives up.
unPosFlaky :: Term n -> SourcePos
unPosFlaky t = Maybe.fromMaybe (newPos "unknown location" 0 0) (unPos t)

----------------------------------------------
----------------------------------------------
--  Size instances
----------------------------------------------

-- simple patterns

instance Pat.Sized (Pattern p) where
    type Size (Pattern p) = p
    size (PatCon _ p) = Pat.size p
    size (PatVar _) = s1

instance Pat.Sized (PatList p) where
    type Size (PatList p) = p
    size PNil = s0
    size (PCons p1 p2) = sPlus (Pat.size p2) (Pat.size p1)

instance Named (Pattern p) where
  patLocals :: Pattern p -> Vec p LocalName
  patLocals (PatVar x) = x ::: VNil
  patLocals (PatCon _ p) = patLocals p

instance Named (PatList p) where
  patLocals :: PatList p -> Vec p LocalName
  patLocals PNil = VNil
  patLocals (PCons (p1 :: Pattern p1) (ps :: PatList ps)) = 
    Vec.append @ps @p1 (patLocals ps) (patLocals p1)

-- scoped patterns

instance Pat.Sized (Local p n) where
    type Size (Local p n) = p
    size (LocalDecl _ _) = s1
    size (LocalDef _ _) = s0

instance Scoped.Sized (Local p) where
    type Size (Local p) = p

instance Named (Local p n) where
  patLocals (LocalDecl x _) = x ::: VNil
  patLocals (LocalDef _ _) = VNil

instance Pat.Sized (Telescope p n) where
    type Size (Telescope p n) = p
    size Tele = s0
    size (TCons rb) = Pat.size rb

instance Scoped.Sized (Telescope p) where
    type Size (Telescope p) = p

instance Named (Telescope p n) where
  patLocals Tele = VNil
  patLocals (TCons (Scoped.Rebind (p :: Local p1 n) (ps :: Telescope ps (Plus p1 n)))) = 
    Vec.append @ps @p1 (patLocals ps) (patLocals p)

----------------------------------------------
--  Subst instances
----------------------------------------------

instance SubstVar Term where
  var = Var

instance Subst Term Term where
  applyE r TyType = TyType
  applyE r (Lam bnd) = Lam (applyE r bnd)
  applyE r (TyCon c es) = TyCon c (map (applyE r) es)
  applyE r (DataCon c es) = DataCon c (map (applyE r) es)
  applyE r (Pi a b) = Pi (applyE r a) (applyE r b)
  applyE r (Var x) = applyEnv r x
  applyE r (Global n) = Global n
  applyE r (App e1 e2) = App (applyE r e1) (applyE r e2)
  applyE r (Case t brs) = Case (applyE r t) (map (applyE r) brs)
  applyE r (Ann a t) = Ann (applyE r a) (applyE r t)
  applyE r (Let e1 bnd) = Let (applyE r e1) (applyE r bnd)
  applyE r (Pos sp e) = Pos sp (applyE r e)
  applyE r (TyEq a b) = TyEq (applyE r a) (applyE r b)
  applyE r TmRefl = TmRefl
  applyE r (Subst a b) = Subst (applyE r a) (applyE r b)
  applyE r (Contra p) = Contra (applyE r p)
  applyE r TrustMe = TrustMe
  applyE r PrintMe = PrintMe 

{-
instance Subst Term (Pattern p) where
  applyE r (PatCon s ps) = PatCon s (applyE r ps)
  applyE r (PatVar x) = PatVar x
-}
instance Subst Term Match where
  applyE r (Branch (b :: Pat.Bind Term Term (Pattern p) n)) =
    Branch (applyE r b)

{-
instance Subst Term (PatList p) where
  applyE r PNil = PNil
  applyE r (PCons rb) = PCons (applyE r rb) 
-}


-- substitution could fail if the constraints in the 
-- telescope are not satisifiable. So we define a 
-- special purpose substitution operation for that 
-- called doSubst in TypeCheck

instance Subst Term (Telescope p) where
  applyE r Tele = Tele
  applyE r (TCons rb) = TCons (applyE r rb)

instance Subst Term (Local p) where
  applyE r (LocalDecl ln t) = LocalDecl ln (applyE r t)
  applyE r (LocalDef x u) = 
    case applyE r (Var x) of
      Var y -> LocalDef y (applyE r u)
      _ -> error "TODO! can only rename LocalDefs"

    

----------------------------------------------
-- Free variable calculation
----------------------------------------------

t00 :: Term N2
t00 = App (Var f0) (Var f0)

t01 :: Term N2
t01 = App (Var f0) (Var f1)

-- >>> appearsFree f0 t00

-- >>> appearsFree f1 t00
-- False

instance FV Term where
  appearsFree n TyType = False
  appearsFree n (Var x) = n == x
  appearsFree n (Global _) = False
  appearsFree n (Pi a b) = appearsFree n a || appearsFree n b
  appearsFree n (Lam b) = appearsFree n b
  appearsFree n (App a b) = appearsFree n a || appearsFree n b
  appearsFree n (TyCon _ args) = any (appearsFree n) args
  appearsFree n (DataCon _ args) = any (appearsFree n) args
  appearsFree n (Case t b) = appearsFree n t || any (appearsFree n) b
  appearsFree n (Ann a t) = appearsFree n a || appearsFree n t
  appearsFree n (Pos _ a) = appearsFree n a
  appearsFree n (Let a b) = appearsFree n a || appearsFree n b
  appearsFree n (TyEq a b) = appearsFree n a || appearsFree n b
  appearsFree n TmRefl = False
  appearsFree n (Subst a b) = appearsFree n a || appearsFree n b
  appearsFree n (Contra a) = appearsFree n a
  appearsFree n TrustMe = False
  appearsFree n PrintMe = False

instance FV Match where
  appearsFree n (Branch bnd) = appearsFree n bnd

instance FV (Local p) where
  appearsFree n (LocalDecl x y) = appearsFree n y
  appearsFree n (LocalDef x y) = n == x || appearsFree n y

{-
instance FV (Pattern p) where
  appearsFree n (PatVar _) = False
  appearsFree n (PatCon _ ps) = False
-}
----------------------------------------------
-- weakening (convenience functions)
----------------------------------------------

-- >>> :t weaken' s1 t00
-- weaken' s1 t00 :: Term ('S ('S N1))

-- >>> weaken' s1 t00
-- 0 0

weaken' :: SNat m -> Term n -> Term (Plus m n)
weaken' m = applyE @Term (weakenE' m)

weakenBind' :: SNat m -> B.Bind Term Term n -> B.Bind Term Term (Plus m n)
weakenBind' m = applyE @Term (weakenE' m)

----------------------------------------------
-- strengthening
----------------------------------------------

-- >>> strengthen' s1 s1 t00
-- Just (0 0)

-- >>> strengthen' s1 s1 t01
-- Nothing

instance Strengthen Term where
  -- strengthen' :: SNat m -> SNat n -> Term (Plus m n) -> Maybe (Term n)
  strengthen' m n (Var x) = Var <$> strengthen' m n x
  strengthen' m n (Global s) = pure (Global s)
  strengthen' m n TyType = pure TyType
  strengthen' m n (Lam b) = Lam <$> strengthen' m n b
  strengthen' m n (DataCon c args) = DataCon c <$> mapM (strengthen' m n) args
  strengthen' m n (TyCon c args) = TyCon c <$> mapM (strengthen' m n) args
  strengthen' m n (Pi a b) = Pi <$> strengthen' m n a <*> strengthen' m n b
  strengthen' m n (App a b) = App <$> strengthen' m n a <*> strengthen' m n b
  strengthen' m n (Case a b) = Case <$> strengthen' m n a <*> mapM (strengthen' m n) b
  strengthen' m n (Ann a t) = Ann <$> strengthen' m n a <*> strengthen' m n t
  strengthen' m n (Pos p a) = Pos p <$> strengthen' m n a
  strengthen' m n (Let a b) = Let <$> strengthen' m n a <*> strengthen' m n b
  strengthen' m n (TyEq a b) = TyEq <$> strengthen' m n a <*> strengthen' m n b
  strengthen' m n TmRefl = return TmRefl
  strengthen' m n (Subst a b) = Subst <$> strengthen' m n a <*> strengthen' m n b
  strengthen' m n (Contra a) = Contra <$> strengthen' m n a
  strengthen' m n TrustMe = pure TrustMe
  strengthen' m n PrintMe = pure PrintMe


instance Strengthen Match where
  strengthen' m n (Branch bnd) = Branch <$> strengthen' m n bnd

--------------------------------------------------------
-- Alpha equivalence (Eq type class)
--------------------------------------------------------

instance Eq (Term n) where
  (Pos _ a) == b = a == b
  a == Pos _ b = a == b
  TyType == TyType = True
  Lam b1 == Lam b2 = b1 == b2
  Var x == Var y = x == y
  Global x == Global y = x == y
  Pi a1 b1 == Pi a2 b2 = a1 == a2 && b1 == b2
  Let a1 b1 == Let a2 b2 = a1 == a2 && b1 == b2
  TyCon n1 a1 == TyCon n2 a2 = n1 == n2 && a1 == a2
  DataCon n1 a1 == DataCon n2 a2 = n1 == n2 && a1 == a2
  Case a1 b1 == Case a2 b2 = a1 == a2 && b1 == b2
  App a1 b1 == App a2 b2 =  a1 == a2 && b1 == b2
  Ann a1 b1 == Ann a2 b2 =  a1 == a2 && b1 == b2
  TyEq a1 b1 == TyEq a2 b2 = a1 == a2 && b1 == b2
  Subst a1 b1 == Subst a2 b2 = a1 == a2 && b1 == b2
  TmRefl == TmRefl = True
  Contra a == Contra b = a == b
  _ == _ = False

instance Pat.PatEq (Pattern p1) (Pattern p2) where
  patEq :: Pattern p1 -> Pattern p2 ->
     Maybe (Pat.Size (Pattern p1) :~: Pat.Size (Pattern p2))
  -- ignore local names
  patEq (PatVar _) (PatVar _) = Just Refl
  patEq (PatCon s1 ps1) (PatCon s2 ps2) | s1 == s2 =
    Pat.patEq ps1 ps2
  patEq _ _ = Nothing


instance Pat.PatEq (PatList p1) (PatList p2) where
  patEq :: PatList p1 -> PatList p2 -> Maybe (p1 :~: p2)
  patEq PNil PNil = Just Refl
  patEq (PCons p1 ps1) (PCons p2 ps2) = do
    Refl <- Pat.patEq p1 p2
    Refl <- Pat.patEq ps1 ps2
    return Refl
  patEq _ _ = Nothing

{-
testEquality2 :: Pattern p1 n1 -> Pattern p2 n2 -> Maybe (p1 :~: p2)
testEquality2 PatVar PatVar = Just Refl
testEquality2 (PatCon s1 ps1) (PatCon s2 ps2) | s1 == s2 = 
  testEq2 ps1 ps2
testEquality2 _ _ = Nothing

testEq2 :: PatList p1 n1 -> PatList p2 n2 -> Maybe (p1 :~: p2)
testEq2 PNil PNil = Just Refl
testEq2 (PCons p1 ps1) (PCons p2 ps2) = do
  Refl <- testEquality2 p1 p2 
  Refl <- testEq2 ps1 ps2
  return Refl
testEq2 _ _ = Nothing
-}

instance Eq (Match n) where
  (Branch p1) == (Branch p2) =
      case Pat.patEq (Pat.getPat p1) (Pat.getPat p2) of
         Just Refl ->
            Pat.getBody p1 == Pat.getBody p2
         Nothing -> False

-- To compare pattern binders, we need to unbind, but also
-- make sure that the patterns are equal
instance (SNatI m, Eq (Term n)) => Eq (Pat.Bind Term Term (Pattern m) n) where
  b1 == b2 =
    Maybe.isJust (Pat.patEq (Pat.getPat b1) (Pat.getPat b2))
      && Pat.getBody b1 == Pat.getBody b2

-- To compare binders, we only need to `unbind` them
instance (Eq (Term n)) => Eq (Local.Bind Term Term n) where
  b1 == b2 = Local.getBody b1 == Local.getBody b2

-- With the instance above the derivable equality instance
-- is alpha-equivalence
-- deriving instance (Eq (Term n))


-------------------------------------------------------
-- Prelude datatypes
-------------------------------------------------------

{-
eqDef :: DataDef
eqDef = 
  DataDef 
  { 
    data_delta = 
        LocalDecl (LocalName "A")  TyType <:>  -- "A"
        LocalDecl (LocalName "a1") (Var f0) <:>
        LocalDecl (LocalName "a2") (Var f1) <:> Tele,  -- "B"
    data_sort = TyType,
    data_constructors = [reflCon]
  }

reflCon :: ConstructorDef N3
reflCon = 
  ConstructorDef
  { con_name = "Refl",
    con_theta = 
      LocalDef f0 (Var f1) <:> Tele -- "a1 = a2"
  }
  -}

sigmaDef :: DataDef
sigmaDef = 
  DataDef
  { 
    data_delta = 
      LocalDecl @N0 (LocalName "A") TyType <:>
      LocalDecl @N1 (LocalName "B") (Pi (Var f0) (Local.bind (LocalName "x") TyType)) <:> Tele,
    data_sort = TyType,
    data_constructors = [prodCon]
  }

prodCon :: ConstructorDef N2
prodCon = 
  ConstructorDef 
  { con_name = "Prod",
    con_theta = 
    LocalDecl (LocalName "a") (Var f1) 
    <:> LocalDecl (LocalName "b")
         (App (Var f1) (Var f0))
    <:> Tele
  }


unitDef :: DataDef
unitDef =
  DataDef
    { 
      data_delta = Tele,
      data_sort = TyType,
      data_constructors = [unitCon]
    }

unitCon :: ConstructorDef N0
unitCon =
  ConstructorDef
    { con_name = "()",
      con_theta = Tele
    }

boolDef :: DataDef
boolDef =
  DataDef
    { 
      data_delta = Tele,
      data_sort = TyType,
      data_constructors = [boolCon False, boolCon True]
    }

boolCon :: Bool -> ConstructorDef N0
boolCon b = ConstructorDef {con_name = show b, con_theta = Tele}

eitherDef :: DataDef
eitherDef =
  DataDef
    { 
      data_delta = 
          LocalDecl (LocalName "A") TyType 
          <:> LocalDecl (LocalName "B") TyType
          <:> Tele,
      data_sort = TyType,
      data_constructors = [eitherLeft, eitherRight]
    }

eitherLeft :: ConstructorDef N2
eitherLeft =
  ConstructorDef
    { 
      con_name = "Left",
      con_theta = LocalDecl (LocalName "a") (Var f0) <:> Tele
    }

eitherRight :: ConstructorDef N2
eitherRight =
  ConstructorDef
    { 
      con_name = "Right",
      con_theta = 
        LocalDecl (LocalName "b") (Var f1) <:> Tele
    }

prelude :: [ModuleEntry]
prelude = [ModuleData "Unit" unitDef,
           ModuleData "Bool" boolDef,
           ModuleData "Either" eitherDef,
           ModuleData "Sigma" sigmaDef]


initialConstructorNames :: ConstructorNames
initialConstructorNames = 
  foldr g (ConstructorNames Set.empty Set.empty) prelude where
    g (ModuleData dn (DataDef _ _ dc)) cn = 
      ConstructorNames {
        tconNames = Set.insert dn(tconNames cn),
        dconNames = Set.union (Set.fromList (map con_name dc)) (dconNames cn)
      }
    g _ cn = cn




--------------------------------------------------------
-- Show instances
--------------------------------------------------------

deriving instance (Show (Term n))
deriving instance (Show (Match n))
deriving instance (Show (Pattern p))
deriving instance (Show (PatList p))

instance Show (Pat.Bind Term Term (Pattern p) n) where
  show b = show (Pat.getPat b) ++ "=>" ++ show (Pat.getBody b)

instance Show (Local.Bind Term Term n) where
  show b = Local.unbind b $ \(x, body) -> show x ++ "." ++ show body
