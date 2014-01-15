-- Comonad class based on the presentation of T. Uustalu and V. Vene
-- "The Essence of Dataflow Programming"

module Comonad where

import qualified Data.List

class Comonad d where
    counit :: d a -> a
    cobind :: (d a -> b) -> d a -> d b

cmap :: Comonad d => (a -> b) -> d a -> d b
cmap f = cobind (f . counit)

class Comonad d => ComonadZip d where
    czip :: d a -> d b -> d (a, b)
