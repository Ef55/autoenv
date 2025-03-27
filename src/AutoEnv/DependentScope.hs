{-# LANGUAGE UndecidableSuperClasses #-}

module AutoEnv.DependentScope
  ( Sized (..),
    MonadScoped (..),
    Telescope (..),
    Scope (..),
    ScopedReader (..),
    ScopedReaderT (..),
    LocalName (..),
    append,
    runScopedReader,
    empty,
    singleton,
    projectScope,
    scope,
    scopeSize,
    fromScope,
    withScopeSize,
    mapScope,
    push,
    push1,
    pushu,
    push1u,
    WithData (..),
  )
where

import AutoEnv.Classes (Sized (..))
import AutoEnv.Context
import AutoEnv.Env (Env, Subst (..), SubstVar, fromVec, shiftNE, weakenE', zeroE, (.++), (.>>))
import AutoEnv.Lib
import AutoEnv.MonadScoped qualified as SimpleScope
import Control.Monad.Error.Class (MonadError (..))
import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.Reader (MonadReader (ask, local))
import Control.Monad.Writer (MonadWriter (..))
import Data.SNat qualified as SNat
import Data.Scoped.Const
import Data.Vec qualified as Vec
import Prelude hiding (map)

-----------------------------------------------------------------------
-- Scopes
-----------------------------------------------------------------------

-- | Unlike 'Scoped.TeleList', this datatype does not nest: it is effectively a
-- 'List'/'Vec' but extra spicy.
data Telescope u s n m where
  TNil :: Telescope u s Z m
  TCons :: (u, s (n + m)) -> !(Telescope u s n m) -> Telescope u s (S n) m

map :: (forall k. u -> s k -> (u', s' k)) -> Telescope u s n m -> Telescope u' s' n m
map f TNil = TNil
map f (TCons (u, s) xs) = TCons (f u s) (map f xs)

empty :: Telescope u s Z m
empty = TNil

singleton :: (u, s n) -> Telescope u s (S Z) n
singleton h = TCons h TNil

append :: forall u s nl nr m. Telescope u s nl (nr + m) -> Telescope u s nr m -> (SNat nl, Telescope u s (nl + nr) m)
append TNil r = (SZ, r)
append (TCons l ls) r =
  case axiomAssoc @nl @nr @m of
    Refl -> let (k, ls') = append ls r in withSNat k (SS, TCons l ls')

toTelescope :: forall p n u s. (SubstVar s) => Vec p (u, s n) -> Telescope u s p n
toTelescope = snd . iter
  where
    iter :: forall p. Vec p (u, s n) -> (SNat p, Telescope u s p n)
    iter Vec.VNil = (SZ, TNil)
    iter ((Vec.:::) @_ @p' (u, s) xs) =
      let (sp', sc') :: (SNat p', Telescope u s p' n) = iter xs
          s' :: s (p' + n) = applyE (shiftNE @s sp') s
       in (withSNat sp' SS, TCons (u, s') sc')

fromTelescope :: forall t s u p n. (Subst t s) => Telescope u s p n -> (SNat p, Vec p (u, s (p + n)))
fromTelescope = iter @t SZ
  where
    iter :: forall t u s k n m. (Subst t s) => SNat k -> Telescope u s n m -> (SNat (k + n), Vec n (u, s (k + n + m)))
    iter sk TNil = case axiomPlusZ @k of Refl -> (sk, Vec.empty)
    iter sk (TCons @_ @_ @n' (u, s) sc) =
      case axiomSus @k @n' of
        Refl ->
          let x' :: (u, s (k + n + m)) = case axiomAssoc @k @n' @m of Refl -> (u, applyE (shiftNE @t $ addOne sk) s)
              (sn', sc') :: (SNat (k + n), Vec n' (u, s (k + n + m))) = iter @t (addOne sk) sc
           in (sn', x' Vec.::: sc')

    addOne :: SNat k -> SNat (S k)
    addOne k = withSNat k SS

emptyTelescope = TNil

nth :: forall t s n m u. (Subst t s) => Fin n -> Telescope u s n m -> (u, s (n + m))
nth i s = snd (fromTelescope @t s) Vec.! i

instance Sized (Telescope u s n m) where
  type Size (Telescope u s n m) = n
  size :: Telescope u s n m -> SNat n
  size TNil = s0
  size (TCons _ t) = withSNat (size t) SS

-----------------------------------------------------------------------
-- MonadScoped class
-----------------------------------------------------------------------

-- Note that we could parametrize all subsequent definitions by an initial
-- scope. We instead make the choice of fixing the outer scope to Z. This
-- simplifies all subsequent definition, and working in a latent undefined scope
-- seems exotic and can be emulated fairly easily.
type Scope u s n = Telescope u s n Z

-- | Scoped monads provide implicit access to the current scope
-- and a way to extend that scope with a vector containing new names
class (forall n. Monad (m n), Subst t s, Subst t b) => MonadScoped t u s b m | m -> t, m -> u, m -> s, m -> b where
  scope' :: m n (SNat n, Scope u s n)
  pushTelescope :: Telescope u s p n -> m (p + n) a -> m n a
  blob :: m n (b n)
  local :: (b n -> b n) -> m n a -> m n a

scope :: (MonadScoped t u s b m) => m n (Scope u s n)
scope = snd <$> scope'

scopeSize :: (MonadScoped t u s b m) => m n (SNat n)
scopeSize = fst <$> scope'

fromScope :: forall t u s b m n. (MonadScoped t u s b m) => Fin n -> m n (u, s n)
fromScope i = case axiomPlusZ @n of Refl -> nth @t i <$> scope

withScopeSize :: forall t n u s b m a. (MonadScoped t u s b m) => ((SNatI n) => m n a) -> m n a
withScopeSize k = do
  size <- scopeSize
  withSNat size k

projectScope :: Scope u s n -> SimpleScope.Scope u n
projectScope s = let (k, v) = iter SZ s in SimpleScope.Scope k v
  where
    iter :: forall k u s n. SNat k -> Scope u s n -> (SNat (k + n), Vec n u)
    iter k TNil = case axiomPlusZ @k of Refl -> (k, Vec.empty)
    iter k (TCons @_ @_ @n' @_ (u, _) xs) =
      case axiomSus @k @n' of
        Refl -> let (k', xs') = withSNat k $ iter @(S k) SS xs in (k', u Vec.::: xs')

-----------------------------------------------------------------------
-- ScopedReader monad
-----------------------------------------------------------------------

-- Trivial instance of MonadScoped
type ScopedReader (t :: Nat -> Type) u s b n = ScopedReaderT t u s b Identity n

runScopedReader :: forall t n u s b a. (SubstVar s, SNatI n) => Scope u s n -> b n -> ScopedReader t u s b n a -> a
runScopedReader d b m = runIdentity $ runScopedReaderT m (size d, d, b)

-----------------------------------------------------------------------
-- ScopedReaderT monad transformer
-----------------------------------------------------------------------

-- | A monad transformer that adds a scope environment to any existing monad
-- This is the Reader monad containing a Scope
-- However, we don't make it an instance of the MonadReader class so that
-- the underlying monad can already be a reader.
-- We also cannot make it an instance of the MonadTrans class because
-- the scope size n needs to be the next-to-last argument instead of the
-- underlying monad
newtype ScopedReaderT (t :: Nat -> Type) u s b m n a = ScopedReaderT {runScopedReaderT :: (SNat n, Scope u s n, b n) -> m a}
  deriving (Functor)

mapScope :: (Monad m) => (forall n. u -> s n -> (u', s' n)) -> ScopedReaderT t u' s' b m n a -> ScopedReaderT t u s b m n a
mapScope f m = ScopedReaderT $ \(k, s, b) ->
  let s' = map f s
   in runScopedReaderT m (k, s', b)

instance (Applicative m) => Applicative (ScopedReaderT t u s b m n) where
  pure f = ScopedReaderT $ \x -> pure f
  ScopedReaderT f <*> ScopedReaderT x = ScopedReaderT (\e -> f e <*> x e)

instance (Monad m) => Monad (ScopedReaderT t u s b m n) where
  ScopedReaderT m >>= k = ScopedReaderT $ \e ->
    m e >>= (\v -> let x = k v in runScopedReaderT x e)

-- instance (MonadReader e m) => MonadReader e (ScopedReaderT t u s b m n) where
--   ask = ScopedReaderT $ const ask
--   local f m = ScopedReaderT (local f . runScopedReaderT m)

instance (MonadError e m) => MonadError e (ScopedReaderT t u s b m n) where
  throwError e = ScopedReaderT $ const (throwError e)
  catchError m k = ScopedReaderT $ \s -> runScopedReaderT m s `catchError` (\err -> runScopedReaderT (k err) s)

instance (MonadWriter w m) => MonadWriter w (ScopedReaderT t u s b m n) where
  writer w = ScopedReaderT $ const (writer w)
  listen m = ScopedReaderT $ \s -> listen $ runScopedReaderT m s
  pass m = ScopedReaderT $ \s -> pass $ runScopedReaderT m s

instance (Monad m, Subst t s, Subst t b) => MonadScoped t u s b (ScopedReaderT t u s b m) where
  scope' = ScopedReaderT $ \(u, s, _) -> return (u, s)
  pushTelescope (v :: Telescope u s p n) m =
    case axiomPlusZ @n of
      Refl -> ScopedReaderT $ \(sz, ss, sb) ->
        let (k, s) = append @_ @_ @p @n v ss
            sb' = applyE (shiftNE @t k) sb
         in runScopedReaderT m (sPlus k sz, s, sb')
  blob = ScopedReaderT $ \(_, _, b) -> return b
  local f m = ScopedReaderT $ \(k, s, b) -> runScopedReaderT m (k, s, f b)

-----------------------------------------------------------------------
-- Extracting data from binders/patterns
-----------------------------------------------------------------------

-- | Extract data from the pattern. This typeclass should be used when the
-- binders are dependent, i.e. the data associated to a binder can refer to
-- previous binders in the same pattern. If you don't need scoped data, use
-- 'MonadScoped.MonadScoped' instead.
class (Sized p) => WithData p u s m where
  getData :: p -> Telescope u s (Size p) m

fromScopedData :: (SubstVar s) => Vec p (u, s m) -> Telescope u s p m
fromScopedData = toTelescope

push :: (MonadScoped t u s b m, WithData p u s n) => p -> m (Size p + n) a -> m n a
push p = pushTelescope (getData p)

push1 :: (MonadScoped t u s b m) => (u, s n) -> m (S n) a -> m n a
push1 p = pushTelescope (TCons p TNil)

pushu :: forall t p u s b n m a. (MonadScoped t u Const b m, WithData p u s n) => p -> m (Size p + n) a -> m n a
pushu p = pushTelescope (map (\u _ -> (u, Const)) $ getData @_ @u @s p)

push1u :: (MonadScoped t u Const b m) => u -> m (S n) a -> m n a
push1u u = pushTelescope (TCons (u, Const) TNil)