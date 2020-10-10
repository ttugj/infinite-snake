{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ConstrainedClassMethods #-}

module Snake.Ambient ( -- * Generators
                       G(..), wtG 
                       -- * Words
                     , W(..), rec, word, alpha
                     , ell, wt, mu
                       -- * Expressions 
                     , E(..), (><), genG, genW 
                       -- * Involution
                     , Inv(..)
                     ) where

import Data.Monoid
import Data.Functor
import Data.Maybe
import Control.Applicative
import Control.Monad

import Snake.FA

-- | generator
data G = A | A' deriving (Eq, Ord, Show)

wtG :: G -> Int
wtG A   =  1
wtG A'  = -1

-- | word
data W where
    WZ  :: G -> W
    WS  :: G -> W -> W

rec     :: forall a. (G -> a) -> (G -> W -> a -> a) -> W -> a
rec z s = \case { WZ g -> z g; WS g w -> s g w (rec z s w) } 

deriving instance Eq W
deriving instance Ord W

instance Show W where
    show (WZ g)   = show g
    show (WS g w) = show g <> show w

word        :: [G] -> W
word [g]    = WZ g
word (g:w)  = WS g (word w)

-- | expression
data E where
    EW :: W -> E           -- ^ interpreted word
    EL :: W -> E           -- ^ sl2-interpreted word
    EH :: E                -- ^ H/2
    ES :: Int -> E -> E    -- ^ z^i sigma

deriving instance Eq E
deriving instance Ord E

instance Show E where
    show (EW w) = show w
    show (EL w) = show w <> "_sl2"
    show  EH    = "H/2"
    show (ES 0 e) = "σ" <> show e
    show (ES i e) = "z^{" <> show i <> "}σ" <> show e

-- | length, weight, sl2-coef of words
ell, wt, mu :: W -> Int
ell = rec (const 1) $ \_ _ n -> n + 1
wt  = rec wtG $ \g _ n ->  wtG g             + n
mu  = rec wtG $ \g w n -> (wtG g * wt w - 1) * n

-- | lie bracket
infixr 5 ><
(><)    :: FA E -> FA E -> FA E
x >< y  = join $ liftA2 bkt x y where
            bkt (EW (WZ g)) (EW w) = gen (EW $ WS g w)
            bkt EH (EW w)          =   wt w  *^ gen (EW w) 
            bkt (EW w) EH          = (-wt w) *^ gen (EW w)
            bkt EH EH              = zero
            bkt (EW w) (ES i e)    = ( mu w * i) *^ gen (ES (i + wt w) e)
            bkt (ES i e) (EW w)    = (-mu w * i) *^ gen (ES (i + wt w) e)
            bkt EH (ES i e)        =   i  *^ gen (ES i e)
            bkt (ES i e) EH        = (-i) *^ gen (ES i e)
            bkt (ES i e) (ES j f)  = ES (i+j) <$> bkt e f
            bkt (EL (WZ g)) (EL w) = gen (EL $ WS g w)
            bkt EH (EL w)          =   wt w  *^ gen (EL w) 
            bkt (EL w) EH          = (-wt w) *^ gen (EL w)
            bkt (EL w) (ES i e)    = ( mu w * i) *^ gen (ES (i + wt w) e)
            bkt (ES i e) (EL w)    = (-mu w * i) *^ gen (ES (i + wt w) e)
            bkt e f                = error $ "this bracket should never occur: [" <> show e <> ", " <> show f <> "]"

-- | involution
class Inv a where
    inv :: a -> a

instance Inv G where
    inv A  = A'
    inv A' = A

instance Inv W where
    inv = rec (WZ . inv) (\g _ w' -> WS (inv g) w')

instance Inv (FA E) where
        inv e = e >>= \case
                        EW w    -> gen $ EW (inv w)
                        EL w    -> gen $ EL (inv w)
                        EH      -> neg $ gen EH
                        ES i e  -> ES (-i) <$> inv (gen e)

-- | embeddings
genG :: G -> FA E
genW :: W -> FA E
genG = genW . WZ
genW = gen . EW

-- | basic words
alpha   :: Int -> W
alpha n = word . reverse . take n . cycle $ [A',A]

instance Normalise W where
    normalise' w@(WZ _)       =       gen w
    normalise' (WS A' (WZ A)) = neg $ gen (WS A (WZ A'))
    normalise' (WS A (WZ A')) =       gen (WS A (WZ A'))
    normalise' (WS A (WZ A))  = zero
    normalise' (WS A' (WZ A'))= zero
    normalise' (WS g w)       = WS g <$> normalise' w

instance Normalise E where
    normalise' (EW w)   = EW <$> normalise' w
    normalise' (EL w) | abs (wt w) <= 1 
                        = EL <$> normalise' w
                      | otherwise
                        = zero
    normalise' EH       = gen EH
    normalise' (ES i e) = ES i <$> normalise' e

-- | lawless instance, for the sake of defining Eq (FA E)
instance Ab Bool where
    zero    = True
    neg     = id
    (^+^)   = (&&)

instance Eq (FA E) where
    x == y  = runFA (normalise $ x ^-^ y) (const False)

