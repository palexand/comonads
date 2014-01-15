-- |Comonad class based on the presentation of T. Uustalu and V. Vene
-- |"The Essence of Dataflow Programming"
module Comonad where

import qualified Data.List

-- | The Comonad class declares constructors counit and cobind for some
-- | type constructor d
class Comonad d where
    counit :: d a -> a
    cobind :: (d a -> b) -> d a -> d b

-- | 'cmap' is a standard map function over a comonad constructed with
-- | recursive applications of cobind
cmap :: Comonad d => (a -> b) -> d a -> d b
cmap f = cobind (f . counit)

-- | The ComonadZip class declares a zip operator defined over pairs of
-- | comonads
class Comonad d => ComonadZip d where
    czip :: d a -> d b -> d (a, b)
