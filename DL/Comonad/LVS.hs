-- LVS comonad based on the presentation of T. Uustalu and V. Vene
-- "The Essence of Dataflow Programming"

-- List is replaced by Past to disambiguate from standard Haskell List

module Comonad.LVS where

import Comonad
import Comonad.Stream

data Past a = Nil | (Past a) :> a deriving Show

data LV a = (Past a) := a

data LVS a = (LV a) :! (Stream a)

instance Comonad LVS where
    counit (past := a :! future) = a
    cobind k d = cobindL d := (k d) :! cobindS d
        where cobindL (Nil          := a :! future) = Nil
              cobindL (past' :> a'  := a :! future) = cobindL d' :> k d'
                  where d' = past' := a' :! (a :< future)
              cobindS (past := a :! (a' :< future')) = k d' :< cobindS d'
                  where d' = past :> a := a' :! future'

runLVS :: (LVS a -> b) -> Stream a -> Stream b
runLVS k (a' :< as') = runLVS' k (Nil := a' :! as')
    where runLVS' k d@(az := a :! (a' :< as')) = (k d) :< (runLVS' k (az :> a := a' :! as'))

fbyLVS :: a -> (LVS a -> a)
fbyLVS a0 (Nil := _ :! _)  = a0
fbyLVS _ ((_ :> a') := _ :! _) = a'

nextLVS :: LVS a -> a
nextLVS (_ := _ :! (a :< _)) = a

showLVS :: (Show a) => LVS a -> IO ()
showLVS (Nil := a0 :! future) = (putStr . show) a0 >> putStr ", " >> showLVS' future
    where showLVS' (a' :< as') = (putStr . show) a' >> putStr ", " >> showLVS' as'

zipP :: Past a -> Past b -> Past (a, b)
zipP Nil _ = Nil
zipP _ Nil = Nil
zipP (az :> a) (bz :> b) = (zipP az bz) :> (a, b)

instance ComonadZip LVS where
    czip (past := a :! future) (past' := b :! future') = zipP past past' := (a, b) :! zipS future future'
