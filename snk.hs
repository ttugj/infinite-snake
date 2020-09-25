{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ConstrainedClassMethods #-}

import Data.Monoid
import Data.Functor
import Data.Maybe
import Control.Applicative
import Control.Monad

import qualified Data.Map.Strict    as M

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
bkt :: FA E -> FA E -> FA E
bkt x y = muFA $ liftA2 bkt' x y where
            bkt' (EW (WZ g)) (EW w) = gen (EW $ WS g w)
            bkt' EH (EW w)          =   wt w  *^ gen (EW w) 
            bkt' (EW w) EH          = (-wt w) *^ gen (EW w)
            bkt' EH EH              = zero
            bkt' (EW w) (ES i e)    = ( mu w * i) *^ gen (ES (i + wt w) e)
            bkt' (ES i e) (EW w)    = (-mu w * i) *^ gen (ES (i + wt w) e)
            bkt' EH (ES i e)        =   i  *^ gen (ES i e)
            bkt' (ES i e) EH        = (-i) *^ gen (ES i e)
            bkt' (ES i e) (ES j f)  = ES (i+j) <$> bkt' e f
            bkt' (EL (WZ g)) (EL w) = gen (EL $ WS g w)
            bkt' EH (EL w)          =   wt w  *^ gen (EL w) 
            bkt' (EL w) EH          = (-wt w) *^ gen (EL w)
            bkt' (EL w) (ES i e)    = ( mu w * i) *^ gen (ES (i + wt w) e)
            bkt' (ES i e) (EL w)    = (-mu w * i) *^ gen (ES (i + wt w) e)
            bkt' e f                = error $ "this bracket should never occur: [" <> show e <> ", " <> show f <> "]"

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

-- | recurrence relation on generators
rrG     :: G -> FA E
rrG g   = gen (EL (WZ g)) ^+^ (ES (wtG g) <$> (gen (EW (WZ g)) ^+^ wtG g *^ gen EH))

-- | recurrence relation on words
rrW             :: W -> FA E
rrW (WZ g)      = rrG g
rrW (WS g w)    = rrG g `bkt` rrW w

-- | basic words
alpha   :: Int -> W
alpha n = word . reverse . take n . cycle $ [A',A]

-- | normalisation
class Normalise a where
    normalise'  :: a -> FA a
    normalise   :: Ord a => FA a -> FA a
    normalise x = reduce $ x >>= normalise'

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

-- | basic recurrence forms
rr  :: Int -> FA E
rr  = normalise . rrW . alpha

rr' :: Int -> FA E
rr' = normalise . rrW . inv . alpha

-- | hypothesised forms
rrHyp   :: Int -> FA E
rrHyp k = normalise $ gen (EL w) ^+^ (ES (wt w) <$> (gen (EW w) ^+^ rest ^+^ mu w *^ gen EH))
          where
            w       = alpha k
            rest    = foldr (^+^) zero $ f <$> [1..k-1]
            f i     = let a = gen . EW . alpha $ i
                          e = k `div` 2 - i `div` 2
                       in ((-1) ^ (k-i) * 2 ^ e) *^ (a ^-^ inv a)   

rrHyp'  :: Int -> FA E
rrHyp'  = normalise . inv . rrHyp

-- | lawless instance, for the sake of defining Eq (FA E)
instance Ab Bool where
    zero    = True
    neg     = id
    (^+^)   = (&&)

instance Eq (FA E) where
    x == y  = runFA (normalise $ x ^-^ y) (const False)

-- free abelian groups...

infixl 6 ^+^
infixl 6 ^-^
infixl 7 *^

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

main    :: IO ()
main    = forM_ [2..] $ \i -> do
            let w = alpha i
                k = wt w
                g | k > 0 = Just A
                  | k < 0 = Just A'
                  | True  = Nothing
                w' = flip WS w <$> g
            putStrLn $ unwords $ catMaybes [ Just $ f w, (h . f) <$> w' ]
            where
                f w = show w <> " = " <> show (normalise . rrW $ w) <> " and μ = " <> show (mu w)
                h s = ";\t killed " <> s
