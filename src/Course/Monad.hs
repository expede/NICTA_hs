{-# LANGUAGE NoImplicitPrelude #-}

module Course.Monad where

import Course.Core
import qualified Prelude as P
import Course.Id
import Course.Optional
import Course.List
import Course.Functor
import Course.Apply
import Course.Bind

-- | setup
-- import Course.Core(Eq(..), Num(..), Ord(..), even, (.))
-- import Course.List(product, sum, length, filter, listh)

class (Apply m, Bind m) => Monad m where
  bind :: (a -> m b)
       -> m a
       -> m b
  return :: a -> m a

  -- Exercise 6
  -- Relative Difficulty: 3
  -- (use bind and return)
  --
  -- | Witness that all things with bind and return also have fmap.
  --
  -- >>> fmap' (+1) (Id 2)
  -- Id 3
  --
  -- >>> fmap' (+1) Nil
  -- []
  --
  -- >>> fmap' (+1) (1 :. 2 :. 3 :. Nil)
  -- [2,3,4]
  fmap' :: (a -> b)
        -> m a
        -> m b
  fmap' f = bind $ return . f

-- Exercise 7
-- Relative Difficulty: 1
--
-- | Binds a function on the Id monad.
--
-- >>> bind (\x -> Id(x+1)) (Id 2)
-- Id 3
--
-- prop> return x == Id x
instance Monad Id where
  bind f (Id a) = f a
  return        = Id

-- Exercise 8
-- Relative Difficulty: 2
--
-- | Binds a function on the List monad.
--
-- >>> bind (\n -> n :. n :. Nil) (1 :. 2 :. 3 :. Nil)
-- [1,1,2,2,3,3]
--
-- prop> return x == x :. Nil
instance Monad List where
  bind f m  = join (f <$> m)
  return a  = (a :. Nil)

-- Exercise 9
-- Relative Difficulty: 2
--
-- | Binds a function on the Optional monad.
--
-- >>> bind (\n -> Full (n + n)) (Full 7)
-- Full 14
--
-- prop> return x == Full x
instance Monad Optional where
  bind   = bindOptional
  return = Full

-- Exercise 10
-- Relative Difficulty: 3
--
-- | Binds a function on the reader ((->) t) monad.
--
-- >>> bind (*) (+10) 7
-- 119
--
-- prop> return x y == x
instance Monad ((->) r) where
  (f `bind` g) r = (f . g) r r
  return r _     = r

-- Exercise 11
-- Relative Difficulty: 2
--
-- | Flattens a combined structure to a single structure.
--
-- >>> flatten' ((1 :. 2 :. 3 :. Nil) :. (1 :. 2 :. Nil) :. Nil)
-- [1,2,3,1,2]
--
-- >>> flatten' (Full Empty)
-- Empty
--
-- >>> flatten' (Full (Full 7))
-- Full 7
--
-- >>> flatten' (+) 7
-- 14
flatten' :: Monad m =>
           m (m a)
         -> m a
flatten' = bind id

-- Exercise 12
-- Relative Difficulty: 10
--
-- | Applies a structure on functions to a structure on values.
--
-- >>> apply (Id (+1)) (Id 2)
-- Id 3
--
-- >>> apply ((+1) :. (*2) :. Nil) (4 :. 5 :. 6 :. Nil)
-- [5,6,7,8,10,12]
--
-- >>> apply (Full (+1)) (Full 2)
-- Full 3
--
-- >>> apply (Full (+1)) Empty
-- Empty
--
-- >>> apply Empty (Full 2)
-- Empty
--
-- >>> apply Empty Empty
-- Empty
--
-- >>> apply (*) (+10) 6
-- 96
apply :: Monad m =>
        m (a -> b)
      -> m a
      -> m b
apply = (<*>)

-- Exercise 13
-- Relative Difficulty: 6
-- (bonus: use apply + fmap')
--
-- | Apply a binary function in the Monad environment.
--
-- >>> liftM2 (+) (Id 7) (Id 8)
-- Id 15
--
-- >>> liftM2 (+) (1 :. 2 :. 3 :. Nil) (4 :. 5 :. Nil)
-- [5,6,6,7,7,8]
--
-- >>> liftM2 (+) (Full 7) (Full 8)
-- Full 15
--
-- >>> liftM2 (+) (Full 7) Empty
-- Empty
--
-- >>> liftM2 (+) Empty (Full 8)
-- Empty
--
-- >>> liftM2 (+) length sum (listh [4,5,6])
-- 18
liftM2 :: Monad m =>
        (a -> b -> c)
      -> m a
      -> m b
      -> m c
liftM2 a b c = a <$> b <*> c

-- Exercise 14
-- Relative Difficulty: 6
-- (bonus: use apply + lift2)
--
-- | Apply a ternary function in the Monad environment.
--
-- >>> liftM3 (\a b c -> a + b + c) (Id 7) (Id 8) (Id 9)
-- Id 24
--
-- >>> liftM3 (\a b c -> a + b + c) (1 :. 2 :. 3 :. Nil) (4 :. 5 :. Nil) (6 :. 7 :. 8 :. Nil)
-- [11,12,13,12,13,14,12,13,14,13,14,15,13,14,15,14,15,16]
--
-- >>> liftM3 (\a b c -> a + b + c) (Full 7) (Full 8) (Full 9)
-- Full 24
--
-- >>> liftM3 (\a b c -> a + b + c) (Full 7) (Full 8) Empty
-- Empty
--
-- >>> liftM3 (\a b c -> a + b + c) Empty (Full 8) (Full 9)
-- Empty
--
-- >>> liftM3 (\a b c -> a + b + c) Empty Empty (Full 9)
-- Empty
--
-- >>> liftM3 (\a b c -> a + b + c) length sum product (listh [4,5,6])
-- 138
liftM3 :: Monad m =>
        (a -> b -> c -> d)
        -> m a
        -> m b
        -> m c
        -> m d
liftM3 a b c d = a <$> b <*> c <*> d

-- Exercise 15
-- Relative Difficulty: 6
-- (bonus: use apply + lift3)
--
-- | Apply a quaternary function in the Monad environment.
--
-- >>> liftM4 (\a b c d -> a + b + c + d) (Id 7) (Id 8) (Id 9) (Id 10)
-- Id 34
--
-- >>> liftM4 (\a b c d -> a + b + c + d) (1 :. 2 :. 3 :. Nil) (4 :. 5 :. Nil) (6 :. 7 :. 8 :. Nil) (9 :. 10 :. Nil)
-- [20,21,21,22,22,23,21,22,22,23,23,24,21,22,22,23,23,24,22,23,23,24,24,25,22,23,23,24,24,25,23,24,24,25,25,26]
--
-- >>> liftM4 (\a b c d -> a + b + c + d) (Full 7) (Full 8) (Full 9) (Full 10)
-- Full 34
--
-- >>> liftM4 (\a b c d -> a + b + c + d) (Full 7) (Full 8) Empty  (Full 10)
-- Empty
--
-- >>> liftM4 (\a b c d -> a + b + c + d) Empty (Full 8) (Full 9) (Full 10)
-- Empty
--
-- >>> liftM4 (\a b c d -> a + b + c + d) Empty Empty (Full 9) (Full 10)
-- Empty
--
-- >>> liftM4 (\a b c d -> a + b + c + d) length sum product (sum . filter even) (listh [4,5,6])
-- 148
liftM4 :: Monad m =>
        (a -> b -> c -> d -> e)
      -> m a
      -> m b
      -> m c
      -> m d
      -> m e
liftM4 a b c d e = a <$> b <*> c <*> d <*> e

-- Exercise 16
-- Relative Difficulty: 3
--
-- | Sequences a list of structures to a structure of list.
--
-- >>> seequence (Id 7 :. Id 8 :. Id 9 :. Nil)
-- Id [7,8,9]
--
-- >>> seequence ((1 :. 2 :. 3 :. Nil) :. (1 :. 2 :. Nil) :. Nil)
-- [[1,1],[1,2],[2,1],[2,2],[3,1],[3,2]]
--
-- >>> seequence (Full 7 :. Empty :. Nil)
-- Empty
--
-- >>> seequence (Full 7 :. Full 8 :. Nil)
-- Full [7,8]
--
-- >>> seequence ((*10) :. (+2) :. Nil) 6
-- [60,8]
seequence :: Monad m =>
            List (m a)
          -> m (List a)
seequence = foldRight (liftM2 (:.)) (return Nil)

-- Exercise 17
-- Relative Difficulty: 3
--
-- | Traverse (map) a list of values with an effect.
--
-- >>> traaverse (\n -> Id (n + 4)) (1 :. 2 :. 3 :. Nil)
-- Id [5,6,7]
--
-- >>> traaverse (\n -> n :. n * 2 :. Nil) (1 :. 2 :. 3 :. Nil)
-- [[1,2,3],[1,2,6],[1,4,3],[1,4,6],[2,2,3],[2,2,6],[2,4,3],[2,4,6]]
--
-- >>> traaverse (\n -> if n < 7 then Full (n * 3) else Empty) (1 :. 2 :. 3 :. Nil)
-- Full [3,6,9]
--
-- >>> traaverse (\n -> if n < 7 then Full (n * 3) else Empty) (1 :. 2 :. 3 :. 14 :. Nil)
-- Empty
--
-- >>> traaverse (*) (1 :. 2 :. 3 :. Nil) 15
-- [15,30,45]
traaverse :: Monad m =>
            (a -> m b)
          -> List a
          -> m (List b)
traaverse f = seequence . (map f)

-- Exercise 18
-- Relative Difficulty: 4
--
-- | Replicate an effect a given number of times.
--
-- >>> reeplicate 4 (Id "hi")
-- Id ["hi","hi","hi","hi"]
--
-- >>> reeplicate 4 (Full "hi")
-- Full ["hi","hi","hi","hi"]
--
-- >>> reeplicate 4 Empty
-- Empty
--
-- >>> reeplicate 4 (*2) 5
-- [10,10,10,10]
reeplicate :: Monad m =>
             Int
           -> m a
           -> m (List a)
reeplicate times = seequence . (replicate times)

-- Exercise 19
-- Relative Difficulty: 9
--
-- | Filter a list with a predicate that produces an effect.
--
-- >>> filtering (Id . even) (4 :. 5 :. 6 :. Nil)
-- Id [4,6]
--
-- >>> filtering (\a -> if a > 13 then Empty else Full (a <= 7)) (4 :. 5 :. 6 :. Nil)
-- Full [4,5,6]
--
-- >>> filtering (\a -> if a > 13 then Empty else Full (a <= 7)) (4 :. 5 :. 6 :. 7 :. 8 :. 9 :. Nil)
-- Full [4,5,6,7]
--
-- >>> filtering (\a -> if a > 13 then Empty else Full (a <= 7)) (4 :. 5 :. 6 :. 13 :. 14 :. Nil)
-- Empty
--
-- >>> filtering (>) (4 :. 5 :. 6 :. 7 :. 8 :. 9 :. 10 :. 11 :. 12 :. Nil) 8
-- [9,10,11,12]
filtering :: (P.Monad m, Monad m) => -- Need `P.Monad` for `do` because `>>=` wasn't defined on the class in Bind.hs
            (a -> m Bool)
          -> List a
          -> m (List a)
filtering _ Nil     = return Nil
-- filtering c (x:.xs) = c x >>= \this -> filtering c xs >>= \rest -> return $ if this then x:.rest else rest
filtering criterion (x:.xs) =
  do this <- criterion x
     rest <- filtering criterion xs
     return $ if this then (x:.rest) else rest

-----------------------
-- SUPPORT LIBRARIES --
-----------------------

instance Monad IO where
  bind   = (=<<)
  return = P.return

instance Monad [] where
  bind   = (P.=<<)
  return = P.return
