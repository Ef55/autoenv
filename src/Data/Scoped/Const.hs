module Data.Scoped.Const where

import AutoEnv (Subst(..), SubstVar(..))

data Const n = Const

instance SubstVar Const where
  var _ = Const

instance (SubstVar a) => Subst a Const where
  applyE _ _ = Const
