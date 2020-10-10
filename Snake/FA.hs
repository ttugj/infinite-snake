{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ConstrainedClassMethods #-}

module Snake.FA ( -- * Abelian groups
                  Ab(..)
                  -- * Free abelian groups
                ,  FA(..), gen
                  -- * reduction/normalisation
                , reduce, Normalise(..)
                ) where

import Data.Monoid
import Data.Functor
import Data.Maybe
import Control.Applicative
import Control.Monad

import qualified Data.Map.Strict    as M

infixl 6 ^+^
infixl 6 ^-^
infixl 7 *^

-- | Abelian group
class Ab a where
    zero    :: a
    (^+^)   :: a -> a -> a
    neg     :: a -> a
    (^-^)   :: a -> a -> a
    a ^-^ b = a ^+^ neg b
    (*^)    :: Int -> a -> a
    n *^ a | n > 0  = a ^+^ (n-1) *^ a
           | n < 0  = n *^ (neg a)
           | True   = zero 

-- | Free abelian group
newtype FA t = FA { runFA :: forall a. Ab a => (t -> a) -> a }

instance Ab (FA t) where
    zero    = FA $ const zero
    x ^+^ y = FA $ \f -> runFA x f ^+^ runFA y f
    neg x   = FA $ \f -> neg (runFA x f)
    x ^-^ y = FA $ \f -> runFA x f ^-^ runFA y f
    n *^ x  = FA $ \f -> n *^ runFA x f

gen :: t -> FA t
gen t = FA $ \f -> f t

instance Functor FA where
    fmap h x    = FA $ \f -> runFA x (f . h)

instance Applicative FA where
    pure    = gen
    h <*> x = FA $ \f -> runFA h (\h' -> runFA x (\x' -> f (h' x')))

muFA   :: FA (FA t) -> FA t
muFA x = FA $ \f -> runFA x (\y -> runFA y f) 

instance Monad FA where
    x >>= h = muFA (h <$> x)

par :: String -> String
par s | any (==' ') s = "(" <> s <> ")"
      | True          = s

instance Ab String where
    zero    = ""
    "" ^+^ t= t
    s ^+^ t = s <> " + " <> t
    neg s   = "-" <> par s
    s ^-^ t = s <> " - " <> t
    n *^ s  = show n <> par s

instance Show t => Show (FA t) where
    show x  = runFA x show

instance Ord t => Ab (M.Map t Int) where
    zero    = M.empty
    x ^+^ y = M.filter (/= 0) $ M.unionWithKey (const (+)) x y
    neg     = M.map negate
    0 *^ _  = M.empty
    n *^ x  = M.map (n *) x

reduce   :: Ord t => FA t -> FA t
reduce x = M.foldlWithKey f zero $ runFA x (\t -> M.singleton t 1)
            where
                f x t 1     = x ^+^ gen t
                f x t (-1)  = x ^-^ gen t
                f x t i     = x ^+^ i *^ gen t

class Normalise a where
    normalise'  :: a -> FA a
    normalise   :: Ord a => FA a -> FA a
    normalise x = reduce $ x >>= normalise'

