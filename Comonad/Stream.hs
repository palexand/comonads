-- |Stream comonad based on the presentation of T. Uustalu and V. Vene
-- |"The Essence of Dataflow Programming"

module Comonad.Stream where

import Comonad

data Stream a = a :< (Stream a) deriving Show

instance Comonad Stream where
    counit (a :< _) = a
    cobind k d@(_ :< az) = (k d) :< (cobind k az)

nextS :: Stream a -> Stream a
nextS (a :< az) = az

takeS :: Int -> Stream a -> [a]
takeS 0 _ = []
takeS i (a :< az) = a : takeS (i-1) az

str2fun :: Stream a -> Int -> a
str2fun (a :< az) 0 = a
str2fun (_ :< az) i = (str2fun az (i-1))

fun2str :: (Int -> a) -> Stream a
fun2str f = fun2str' f 0
    where fun2str' f i = (f i) :< (fun2str' f (i + 1))

zipS :: Stream a -> Stream b -> Stream (a, b)
zipS (a :< az) (b :< bz) = (a, b) :< (zipS az bz)
