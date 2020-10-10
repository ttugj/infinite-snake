{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ConstrainedClassMethods #-}

module Snake.Recur ( -- * elementary recurrence relations
                     rrG, rrW
                     -- * recursively defined rests
                   , rest, checkRest
                     -- * special recurrence forms
                   , rr, rr', rrId, rrId'
                   ) where

import Data.Monoid
import Data.Functor
import Data.Maybe
import Control.Applicative
import Control.Monad

import Snake.Ambient
import Snake.FA

-- | recurrence relation on generators
rrG     :: G -> FA E
rrG g   = gen (EL (WZ g)) ^+^ (ES (wtG g) <$> (genW (WZ g) ^+^ wtG g *^ gen EH))

-- | recurrence relation on words
rrW             :: W -> FA E
rrW (WZ g)      = rrG g
rrW (WS g w)    = rrG g >< rrW w

-- | rests 
rest    :: W -> FA W
rest    = rec (const zero) su
            where
                su g w r    = let gr    = WS g <$> r
                                  g'    = gen (WZ g)
                                  w'    = gen w 
                                  r'    = r >>= \u -> wt u *^ gen u
                                  terms = [ (1                , gr)
                                          , (wtG g            , r')
                                          , (wtG g * wt w     , r)
                                          , ( 2 * wtG g * wt w, gen w)
                                          , (-2 * wtG g * mu w, gen (WZ g))
                                          ]
                               in foldr (^+^) zero $ uncurry (*^) <$> terms

-- | check validity of rests
checkRest     :: W -> FA E
checkRest w   = let r = gen (EL w) ^+^ (ES (wt w) <$> (gen (EW w) ^+^ mu w *^ gen EH ^+^ (EW <$> rest w)))
                 in normalise $ rrW w ^-^ r    

-- | basic recurrence forms
rr  :: Int -> FA E
rr  = normalise . rrW . alpha

rr' :: Int -> FA E
rr' = normalise . rrW . inv . alpha

-- | hypothesised recurrence identities
rrId    :: Int -> FA E
rrId k  = normalise $ gen (EL w) ^+^ (ES (wt w) <$> (gen (EW w) ^+^ rest ^+^ mu w *^ gen EH))
          where
            w       = alpha k
            rest    = foldr (^+^) zero $ f <$> [1..k-1]
            f i     = let a = gen . EW . alpha $ i
                          e = k `div` 2 - i `div` 2
                       in ((-1) ^ (k-i) * 2 ^ e) *^ (a ^-^ inv a)   

rrId'   :: Int -> FA E
rrId'   = normalise . inv . rrId


