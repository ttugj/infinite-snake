{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ConstrainedClassMethods #-}

module Snake.Recur ( -- * recurrence relations: right hand sides
                     rrG, rrW
                     -- * recursively defined rests
                   , rest, testRest
                     -- * explicit rests 
                   , alphaRest, testAlphaRest
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

testRest    :: W -> FA E
testRest w  = let r = gen (EL w) ^+^ (ES (wt w) <$> (gen (EW w) ^+^ mu w *^ gen EH ^+^ (EW <$> rest w)))
               in normalise $ rrW w ^-^ r    

alphaRest   :: Int -> FA E
alphaRest k = foldr (^+^) zero $ f <$> [1..k-1]
                where  
                    f i = let a = gen . EW . alpha $ i
                              e = k `div` 2 - i `div` 2
                           in ((-1) ^ (k-i) * 2 ^ e) *^ (a ^-^ inv a)   

testAlphaRest   :: Int -> FA E
testAlphaRest k = normalise $ (EW <$> rest (alpha k)) ^-^ alphaRest k
