{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Longboi where 

import Data.Kind
import qualified Prelude
import Prelude (Bool(..))

data Nat = Z | S Nat

infixl 6 +,-
--infixl 7 *

type family (n :: Nat) + (m :: Nat) :: Nat where
  Z + m = m
  (S n) + m = S (n + m)

--type family (n :: Nat) * (m :: Nat) :: Nat where
--  Z * m = Z
--  (S n) * m = (n * m) + m

type family (n :: Nat) - (m :: Nat) :: Nat where
  Z - m = Z
  (S n) - Z = S n
  (S n) - m = S (n - m)

type family Min (n :: Nat) (m :: Nat) :: Nat where
  Min Z Z = Z
  Min Z (S m) = Z 
  Min (S n) Z = Z
  Min (S n) (S m) = S (Min n m)

type family Max (n :: Nat) (m :: Nat) :: Nat where
  Max Z Z = Z
  Max Z (S m) = S m 
  Max (S n) Z = S n
  Max (S n) (S m) = S (Max n m)

data Longboi a (n :: Nat) where
  Nil :: Longboi a Z
  Cons :: a -> Longboi a n -> Longboi a (S n)

deriving instance Prelude.Eq a => Prelude.Eq (Longboi a n)

type family Length (xs :: Longboi a (n :: Nat)) :: Nat where
  Length Nil = Z
  Length (Cons x xs) = (S Z) + Length xs

type family Contains (xs :: Longboi a (n :: Nat)) (elem :: a) :: Bool where
  Contains Nil _ = False
  Contains (Cons x xs) x = True
  Contains (Cons x xs) y = Contains xs y

infixr 5 ++
(++) :: Longboi a n -> Longboi a m -> Longboi a (n + m)
(Cons x xs) ++ ys = Cons x (xs ++ ys)
Nil         ++ ys = ys

type family Append (xs :: Longboi a (n :: Nat)) (ys :: Longboi a (m :: Nat)) :: Longboi a (n + m) where
  Append (Cons x xs) ys = Cons x (Append xs ys)
  Append Nil ys = ys

type family Head (xs :: Longboi a (n :: Nat)) :: a where
  Head (Cons x _) = x

type family Last (xs :: Longboi a (n :: Nat)) :: a where
  Last (Cons x Nil) = x
  Last (Cons x xs)  = Last xs

type family Tail (xs :: Longboi a ((S n) :: Nat)) :: Longboi a (n :: Nat) where
  Tail (Cons _ xs) = xs

type family Init (xs :: Longboi a ((S n) :: Nat)) :: Longboi a (n :: Nat) where
  Init (Cons _ Nil) = Nil
  Init (Cons x xs ) = Cons x (Init xs)

type family Null (xs :: Longboi a (n :: Nat)) :: Bool where
  Null Nil = True
  Null _   = False

type family VMap (f :: a -> b) (xs :: Longboi a (n :: Nat)) :: Longboi b (n :: Nat) where
  VMap _ Nil = Nil
  VMap f (Cons x xs) = Cons (f x) (VMap f xs)

type family Foldl (f :: a -> b -> a) (x :: a) (ys :: Longboi b (n :: Nat)) :: a where
  Foldl _ x Nil = x
  Foldl f y (Cons x xs) = Foldl f (f y x) xs

type family Foldr (f :: a -> b -> b) (x :: b) (ys :: Longboi a (n :: Nat)) :: b where
  Foldr _ y Nil = y
  Foldr f y (Cons x xs) = f x (Foldr f y xs)

type family ZipWithSame (f :: a -> b -> c) (xs :: Longboi a (n :: Nat)) (ys :: Longboi a (n :: Nat)) :: Longboi c (n :: Nat) where
  ZipWithSame _ Nil Nil = Nil
  ZipWithSame f (Cons a as) (Cons b bs) = Cons (f a b) (ZipWithSame f as bs)

type family ZipWith (f :: a -> b -> c) (xs :: Longboi a (n :: Nat)) (ys :: Longboi a (m :: Nat)) :: Longboi c (Min n m) where
  ZipWith _ Nil Nil = Nil
  ZipWith _ Nil (Cons _ _) = Nil
  ZipWith _ (Cons _ _) Nil = Nil
  ZipWith f (Cons a as) (Cons b bs) = Cons (f a b) (ZipWith f as bs)

head :: Longboi a (S n) -> a
head (Cons x _) = x

last :: Longboi a n -> a
last (Cons x Nil) = x
last (Cons x xs)  = last xs

tail :: Longboi a (S n) -> Longboi a n
tail (Cons _ xs) = xs

init :: Longboi a (S n) -> Longboi a n
init (Cons x xs) =
  case xs of
    Nil -> Nil
    (Cons _ _) -> Cons x (init xs)

uncons :: Longboi a (S n) -> (a, Longboi a n)
uncons (Cons x xs) = (x, xs)

null :: Longboi a n -> Bool
null Nil = True
null _   = False

vmap :: (a -> b) -> Longboi a n -> Longboi b n
vmap _ Nil = Nil
vmap f (Cons x xs) = Cons (f x) (vmap f xs)

foldl :: (a -> b -> a) -> a -> Longboi b n -> a
foldl _ x Nil = x
foldl f y (Cons x xs) = foldl f (f y x) xs

foldr :: (a -> b -> b) -> b -> Longboi a n -> b
foldr _ y Nil = y
foldr f y (Cons x xs) = f x (foldr f y xs)

toList :: Longboi a n -> [a]
toList Nil = []
toList (Cons x xs) = x : toList xs

zipWithSame :: (a -> b -> c) -> Longboi a n -> Longboi b n -> Longboi c n
zipWithSame _ Nil Nil = Nil
zipWithSame f (Cons a as) (Cons b bs) = Cons (f a b) (zipWithSame f as bs)

zipWith :: (a -> b -> c) -> Longboi a n -> Longboi b m -> Longboi c (Min n m)
zipWith _ Nil Nil = Nil
zipWith _ Nil (Cons _ _) = Nil
zipWith _ (Cons _ _) Nil = Nil
zipWith f (Cons a as) (Cons b bs) = Cons (f a b) (zipWith f as bs)
