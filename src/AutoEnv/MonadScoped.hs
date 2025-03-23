-- | Monads supporting scopes of names
module AutoEnv.MonadScoped
  ( Sized (..),
    MonadScoped (..),
    Scope (..),
    emptyScope,
    extendScope,
    ScopedReader (..),
    ScopedReaderT (..),
    withSize,
    LocalName (..),
    push,
  )
where

import AutoEnv.Classes
import AutoEnv.Lib
import Control.Monad.Identity
import Control.Monad.Reader
import Data.SNat as SNat
import Data.Vec as Vec

-----------------------------------------------------------------------

-- * Scopes

-----------------------------------------------------------------------

-- | Scopes know how big they are and remember names for printing
data Scope d n = Scope
  { scope_size :: SNat n, -- number of names in scope
    scope_data :: Vec n d -- stack of data currently in scope
  }
  deriving (Eq, Show)

-- TODO: should we represent the sequence of names in scope using
-- a more efficient data structure than a vector? Maybe a size-indexed
-- Data.Sequence?

emptyScope :: Scope d Z
emptyScope =
  Scope
    { scope_size = SZ,
      scope_data = VNil
    }

extendScope ::
  forall p n d.
  (SNatI p) =>
  Vec p d ->
  Scope d n ->
  Scope d (p + n)
extendScope v s =
  Scope
    { scope_size = sPlus (snat @p) (scope_size s),
      scope_data = Vec.append v (scope_data s)
    }

instance Sized (Scope d n) where
  type Size (Scope d n) = n
  size :: Scope d n -> SNat n
  size = scope_size

-- instance Named d (Scope d n) where
--   names :: Scope d n -> Vec n d
--   names = scope_data

-----------------------------------------------------------------------

-- * MonadScoped class

-----------------------------------------------------------------------

-- | Scoped monads provide implicit access to the current scope
-- and a way to extend that scope with a vector containing new names
class (forall n. Monad (m n)) => MonadScoped d m | m -> d where
  scope :: m n (Scope d n)
  pushVec :: (SNatI p) => Vec p d -> m (p + n) a -> m n a

push :: forall p d m n a. (Sized p, Linearize p d, MonadScoped d m) => p -> m (Size p + n) a -> m n a
push p m = withSNat (size p) $ pushVec (linearize p) m

-- | Access the current size of the scope as an implicit argument
withSize :: (MonadScoped d m) => ((SNatI n) => m n a) -> m n a
withSize f = do
  s <- scope
  withSNat (scope_size s) f

-----------------------------------------------------------------------

-- * ScopedReader monad

-----------------------------------------------------------------------

-- Trivial instance of MonadScoped
type ScopedReader d = ScopedReaderT d Identity

-----------------------------------------------------------------------

-- * ScopedReaderT monad transformer

-----------------------------------------------------------------------

-- | A monad transformer that adds a scope environment to any existing monad
-- This is the Reader monad containing a Scope
-- However, we don't make it an instance of the MonadReader class so that
-- the underlying monad can already be a reader.
-- We also cannot make it an instance of the MonadTrans class because
-- the scope size n needs to be the next-to-last argument instead of the
-- underlying monad
newtype ScopedReaderT d m n a = ScopedReaderT {runScopedReaderT :: Scope d n -> m a}
  deriving (Functor)

instance (Applicative m) => Applicative (ScopedReaderT d m n) where
  pure f = ScopedReaderT $ \x -> pure f
  ScopedReaderT f <*> ScopedReaderT x = ScopedReaderT (\e -> f e <*> x e)

instance (Monad m) => Monad (ScopedReaderT d m n) where
  ScopedReaderT m >>= k = ScopedReaderT $ \e ->
    m e >>= (\v -> let x = k v in runScopedReaderT x e)

instance (MonadReader e m) => MonadReader e (ScopedReaderT d m n) where
  ask = ScopedReaderT (const ask)
  local f m = ScopedReaderT (local f . runScopedReaderT m)

instance
  (Monad m) =>
  MonadScoped d (ScopedReaderT d m)
  where
  scope = ScopedReaderT $ \s -> return s
  pushVec n m = ScopedReaderT $ \env -> runScopedReaderT m (extendScope n env)
