-- | single binder, but includes a name for pretty printing
-- type synonym for Pat.Bind with an opaque name as the pattern
module AutoEnv.Bind.Local
  ( module AutoEnv.Classes,
    type Bind,
    bind,
    getLocalName,
    internalBind,
    getBody,
    unbind,
    unbindC,
    instantiate,
    applyUnder,
  )
where

import AutoEnv
import AutoEnv.Bind.Pat qualified as Pat
import AutoEnv.Classes

---------------------------------------------------------------
-- LocalBind operations (convenience wrappers)

type Bind v c n = Pat.Bind v c LocalName n

-- deriving instance (Eq (Bind v c n))
-- deriving instance (Subst v (Bind v c))
-- deriving instance (FV (Bind v c))
-- deriving instance (Strengthen (Bind v c))

bind :: (Subst v c) => LocalName -> c (S n) -> Bind v c n
bind = Pat.bind

getLocalName :: Bind v c n -> LocalName
getLocalName = Pat.getPat

internalBind :: (Subst v c) => c (S n) -> Bind v c n
internalBind = Pat.bind internalName

getBody :: (Subst v v, Subst v c) => Bind v c n -> c (S n)
getBody = Pat.getBody

-- unbind, but also provide access to the local name
-- if one is available
unbind ::
  (Subst v v, Subst v c) =>
  Bind v c n ->
  (LocalName, c (S n))
unbind b = (getLocalName b, getBody b)

unbindC ::
  (Subst v v, Subst v c) =>
  Bind v c n ->
  ((LocalName, c (S n)) -> d) ->
  d
unbindC b f = f $ unbind b

instantiate :: (Subst v c) => Bind v c n -> v n -> c n
instantiate b e = Pat.instantiate b (oneE e)

applyUnder ::
  (Subst v v, Subst v c) =>
  (forall m n. Env v m n -> c m -> c n) ->
  Env v n1 n2 ->
  Bind v c n1 ->
  Bind v c n2
applyUnder = Pat.applyUnder

-- TODO: unbindWith
-- TODO: instantiatiateWith