{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Longboi 
  ( Longboi(..)
  , toList
  , fromList
  , head
  , tail
  , append
  , map
  , uncons
  , init
  , last
  , zipWith
  , zipWithSame
  , null
  ) where

import Control.Applicative ((<$>))
import Data.Maybe
import Data.Monoid
import Prelude ( Bool(..) )
import Prelude ( Eq (..), Ord (..), Show(..) )
import Prelude ( ($), (.), (||) )
import qualified Prelude as P

data Nat = Z | S Nat deriving (Show)

infixl 6 :+
infixl 7 :*
infixl 9 :~

type family   (n :: Nat) :+ (m :: Nat) :: Nat where
  Z     :+ m = m
  (S n) :+ m = S (n :+ m)

type family   (n :: Nat) :* (m :: Nat) :: Nat where
  Z     :* m = Z
  (S n) :* m = (n :* m) :+ m

type family   (n :: Nat) :~ (m :: Nat) :: Nat where
  Z :~ Z         = Z
  Z :~ (S _)     = Z
  (S _) :~ Z     = Z
  (S m) :~ (S n) = S (m :~ n)

data SNat n where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

data Longboi (a :: *) (n :: Nat) where
  Nil  :: Longboi a Z
  (:-) :: a -> Longboi a n -> Longboi a (S n)
infixr 5 :-

deriving instance Eq a => Eq (Longboi a n)

instance Show a => Show (Longboi a n) where
  showsPrec d = showsPrec d . toList

append :: Longboi a n -> Longboi a m -> Longboi a (n :+ m)
append (x :- xs) ys = x :- append xs ys
append Nil ys       = ys

(++) = append
infixr 5 ++

head :: Longboi a (S n) -> a
head (x :- _) = x

last :: Longboi a n -> a
last (x :- Nil) = x
last (x :- xs)  = last xs

tail :: Longboi a (S n) -> Longboi a n
tail (_ :- xs) = xs

init :: Longboi a (S n) -> Longboi a n
init (x :- xs) = 
  case xs of
    Nil      -> Nil
    (_ :- _) -> x :- init xs

uncons :: Longboi a (S n) -> (a, Longboi a n)
uncons (x :- xs) = (x, xs)

null :: Longboi a n -> Bool
null Nil = True
null _   = False

map :: (a -> b) -> Longboi a n -> Longboi b n
map _ Nil       = Nil
map f (x :- xs) = f x :- map f xs

foldl :: (a -> b -> a) -> a -> Longboi b n -> a
foldl _ x Nil       = x
foldl f y (x :- xs) = foldl f (f y x) xs

foldr :: (a -> b -> b) -> b -> Longboi a n -> b
foldr _ y Nil = y
foldr f y (x :- xs) = f x (foldr f y xs)

toList :: Longboi a n -> [a]
toList Nil       = []
toList (x :- xs) = x : toList xs

fromList :: forall (n :: Nat) a. SNat n -> [a] -> Maybe (Longboi a n)
fromList SZ _            = Just Nil
fromList (SS n) (x : xs) = (x :-) <$> fromList n xs
fromList (SS n) []       = Nothing

zipWithSame :: (a -> b -> c) -> Longboi a n -> Longboi b n -> Longboi c n
zipWithSame _ Nil Nil             = Nil
zipWithSame f (a :- as) (b :- bs) = f a b :- zipWithSame f as bs

zipWith :: (a -> b -> c) -> Longboi a n -> Longboi b m -> Longboi c (n :~ m)
zipWith _ Nil Nil             = Nil
zipWith _ Nil (_ :- _)        = Nil
zipWith _ (_ :- _)   Nil      = Nil
zipWith f (a :- as) (b :- bs) = f a b :- zipWith f as bs
