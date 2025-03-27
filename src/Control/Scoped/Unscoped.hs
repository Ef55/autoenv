module Control.Scoped.Unscoped where
import Control.Scoped.Monad (ScopedFunctor(..))

newtype Unscoped (t :: Type) (n :: Nat) = Unscoped t

instance ScopedFunctor Unscoped where