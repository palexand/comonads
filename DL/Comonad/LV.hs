-- LV comonad based on the presentation of T. Uustalu and V. Vene
-- "The Essence of Dataflow Programming"

module Comonad.LV where

import Comonad
import Comonad.Stream
import Comonad.LVS

instance Comonad LV where
    counit (_ := a) = a
    cobind k d@(past := _) = cobindL k past := (k d)
        where cobindL k Nil = Nil
              cobindL k (past :> a) = cobindL k past :> (k (past := a))

runLV :: (LV a -> b) -> Stream a -> Stream b
runLV k (a' :< as') = runLV' k (Nil := a' :! as')
    where runLV' k (d@(az := a) :! (a' :< as')) = (k d) :< runLV' k (az :> a := a' :! as')

fbyLV :: a -> (LV a -> a)
fbyLV a0 (Nil := _) = a0
fbyLV _ ((_ :> a') := _) = a'

instance ComonadZip LV where
    czip (past := a) (past' := b) = zipP past past' := (a, b)
