module Control.Scoped.Monad (ScopedFunctor (..), ScopedMonad (..), csmap, (>>%)) where

import Data.Kind
import Data.Nat (Nat)

class ScopedFunctor (m :: (Nat -> Type) -> Nat -> Type) where
  (<$>%) :: forall a a' n n'. (a n -> a' n') -> m a n -> m a' n'

csmap :: (ScopedFunctor m) => (a n -> a' n) -> m a n -> m a' n
csmap = (<$>%)

class (ScopedFunctor m) => ScopedMonad (m :: (Nat -> Type) -> Nat -> Type) where
  sreturn :: forall a n. a n -> m a n
  (>>=%) :: m a n -> (a n -> m a' n') -> m a' n'

(>>%) :: (ScopedMonad m) => m a n -> m a' n' -> m a' n'
l >>% r = l >>=% const r