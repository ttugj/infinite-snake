-- Basic recursive relation:   ζ = e + z σ (ζ + h/2)

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
rrG g   = gen (EL (WZ g)) ^+^ (ES (wtG g) <$> (gen (EW (WZ g)) ^+^ wtG g *^ gen EH))

-- | recurrence relation on words
rrW             :: W -> FA E
rrW (WZ g)      = rrG g
rrW (WS g w)    = rrG g >< rrW w

-- | rests (recursively defined)
rest    :: W -> FA W
rest    = rec (const zero) su
            where
                su g w x    = let gx    = WS g <$> x
                                  g'    = gen (WZ g)
                                  w'    = gen w 
                                  x'    = x >>= \u -> wt u *^ gen u
                               in gx ^+^ x' ^+^ g' ^+^ w'   -- TODO: coefficients

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


