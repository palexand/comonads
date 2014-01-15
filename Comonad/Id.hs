-- |Id comonad based on the presentation of T. Uustalu and V. Vene
-- |"The Essence of Dataflow Programming"

module Comonad.Id where

import Comonad

-- |The Id comonad is the trivial comonad with only one consructor
data Id a = Id a

instance Comonad Id where
    counit (Id a) = a
    cobind k d = Id (k d)

instance ComonadZip Id where
    czip (Id a) (Id b) = Id (a, b)
