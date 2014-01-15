-- |Product comonad based on the presentation of T. Uustalu and V. Vene,
-- |"The Essence of Dataflow Programming"

module Comonad.Product where

import Comonad

-- |Product is defined in the classical fashion as a pair of values.
-- |This definition is interesting becaus the product is lazy.
data Prod e a = a :& e

instance Comonad (Prod e) where
    counit (a :& _) = a
    cobind k d@(_ :& e) = (k d) :& e

askP :: Prod e a -> e
askP (_ :& e) = e

localP :: (e -> e) -> Prod e a -> Prod e a
localP g (a :& e) = a :& (g e)
