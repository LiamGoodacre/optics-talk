
-- stack exec ghcid -- -c "stack --resolver=lts-13.2 repl --package refined Talk.hs"
-- stack --resolver=lts-13.2 repl --package refined Talk.hs

{-# language
  RankNTypes,
  TypeInType,
  GADTs,
  FlexibleInstances,
  InstanceSigs,
  UnicodeSyntax,
  LambdaCase,
  ScopedTypeVariables,
  TypeApplications,
  ConstraintKinds,
  TypeOperators,
  TypeFamilies,
  MultiParamTypeClasses,
  FunctionalDependencies,
  DeriveTraversable,
  AllowAmbiguousTypes,
  FlexibleContexts,
  UndecidableInstances,
  TypeFamilyDependencies,
  ViewPatterns,
  StandaloneDeriving,
  PolyKinds,
  EmptyCase,
  BlockArguments,
  TemplateHaskell
#-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Talk where

import Data.Void
import Data.Kind
import Data.Monoid (First(..))
import GHC.TypeLits
import Data.Monoid (Sum(..))
import Data.Functor.Identity (Identity(..))
import Refined
import Control.Applicative
import Data.Foldable
import qualified Control.Category as Cat
import qualified Data.Set as Set

lmap :: (e -> f) -> Either e a -> Either f a
lmap f = \case
  Left e -> Left (f e)
  Right a -> Right a

swap :: Either a b -> Either b a
swap = \case
  Left a -> Right a
  Right b -> Left b


-- Disclaimers:

-- Will write `Lens a b s t` instead of `Lens s t a b`
-- because things will line up better.

-- Only going through Profunctor optics as the Van Laarhoven
-- style has a lot of unnecessary noise (but is equivalent).


type DataFun a b = a -> b

data DataEqual :: Type -> Type -> Type where
  Refl :: ∀ x . DataEqual x x

data DataIso a b s t =
  DataIso (s -> a) (b -> t)

data DataLens a b s t =
  DataLens (s -> a) (b -> s -> t)

data DataPrism a b s t =
  DataPrism (s -> Either t a) (b -> t)

data DataEquality a b s t =
  DataEquality (DataEqual s a) (DataEqual b t)

data DataCoprism a b s t =
  DataCoprism (s -> a) (b -> Either a t)

data DataLR a b l r s t =
  DataLR (l s a) (r b t)


type Exchange = DataIso
type Shop = DataLens
type Market = DataPrism


type DataIso' ab st = DataIso ab ab st st
type DataLens' ab st = DataLens ab ab st st
type DataPrism' ab st = DataPrism ab ab st st
type DataEquality' ab st = DataEquality ab ab st st
type DataCoprism' ab st = DataCoprism ab ab st st
type DataLR' ab l r st = DataLR ab ab l r st st


equalFun ::
  DataEqual a b -> DataFun a b
equalFun Refl = id

equalityIso ::
  DataEquality a b s t -> DataIso a b s t
equalityIso (DataEquality Refl Refl) =
  DataIso id id

isoLens ::
  DataIso a b s t -> DataLens a b s t
isoLens (DataIso sa bt) =
  DataLens sa (\b _s -> bt b)

isoPrism ::
  DataIso a b s t -> DataPrism a b s t
isoPrism (DataIso sa bt) =
  DataPrism (Right . sa) bt

isoCoprism ::
  DataIso a b s t -> DataCoprism a b s t
isoCoprism (DataIso sa bt) =
  DataCoprism sa (Right . bt)

isoLR ::
  ((s -> a) -> l s a) ->
  ((b -> t) -> r b t) ->
  DataIso a b s t ->
  DataLR a b l r s t
isoLR sal btr (DataIso sa bt) = DataLR (sal sa) (btr bt)


identityFun ::
  DataFun x x
identityFun = id

identityEqual ::
  DataEqual x x
identityEqual = Refl

identityIso ::
  DataIso x y x y
--DataIso' xy xy
identityIso = DataIso id id

identityLens ::
  DataLens x y x y
--DataLens' xy xy
identityLens = DataLens id const

identityPrism ::
  DataPrism x y x y
--DataPrism' xy xy
identityPrism = DataPrism Right id

identityEquality ::
  DataEquality x y x y
--DataEquality' xy xy
identityEquality = DataEquality Refl Refl

identityCoprism ::
  DataCoprism x y x y
--DataCoprism' xy xy
identityCoprism = DataCoprism id Right

identityLR ::
  ( Cat.Category l
  , Cat.Category r
  ) =>
  DataLR a b l r a b
identityLR = DataLR Cat.id Cat.id


composeFun ::
  DataFun b c -> (DataFun a) b -> (DataFun a) c
composeFun f g = f . g

composeEqual ::
  DataEqual b c -> (DataEqual a) b -> (DataEqual a) c
composeEqual Refl Refl = Refl

composeIso ::
  DataIso x y i o -> (DataIso a b) x y -> (DataIso a b) i o
--DataIso' xy io  -> (DataIso' ab) xy  -> (DataIso' ab) io
composeIso (DataIso ix yo) (DataIso xa by) =
  DataIso (xa . ix) (yo . by)

composeLens ::
  DataLens x y i o -> (DataLens a b) x y -> (DataLens a b) i o
--DataLens' xy io  -> (DataLens' ab) xy  -> (DataLens' ab) io
composeLens (DataLens ix yio) (DataLens xa bxy) =
  DataLens (xa . ix) (\b i -> yio (bxy b (ix i)) i)

composePrism ::
  DataPrism x y i o -> (DataPrism a b) x y -> (DataPrism a b) i o
--DataPrism' xy io  -> (DataPrism' ab) xy  -> (DataPrism' ab) io
composePrism (DataPrism iox yo) (DataPrism xya by) =
  DataPrism (\i -> iox i >>= lmap yo . xya) (yo . by)

composeEquality ::
  DataEquality x y i o -> (DataEquality a b) x y -> (DataEquality a b) i o
--DataEquality' xy io  -> (DataEquality' ab) xy  -> (DataEquality' ab) io
composeEquality (DataEquality ix yo) (DataEquality xa by) =
  DataEquality (composeEqual xa ix) (composeEqual yo by)

composeCoprism ::
  DataCoprism x y i o -> (DataCoprism a b) x y -> (DataCoprism a b) i o
--DataCoprism' xy io  -> (DataCoprism' ab) xy  -> (DataCoprism' ab) io
composeCoprism (DataCoprism ix yxo) (DataCoprism xa bay) =
  DataCoprism (xa . ix) (\b -> case bay b of
                              Left a -> Left a
                              Right y -> case yxo y of
                                Left x -> Left (xa x)
                                Right o -> Right o)

composeLR ::
  ( Cat.Category l
  , Cat.Category r
  ) =>
  DataLR x y l r i o -> (DataLR a b l r) x y -> (DataLR a b l r) i o
--DataLR' xy l r io  -> (DataLR' ab l r) xy  -> (DataLR' ab l r) io
composeLR (DataLR lix ryo) (DataLR lxa rby) =
  DataLR (lxa Cat.<<< lix) (ryo Cat.<<< rby)


-- class Functor f where
class FunFunctor f where
  funMap :: DataFun b c -> f b -> f c

class EqualFunctor f where
  equalMap :: DataEqual b c -> f b -> f c

-- class Profunctor p where
class EqualityFunctor p => IsoFunctor p where
  isoMap :: DataIso x y i o -> p x y -> p i o
  --     :: DataIso' xy io  -> p xy  -> p io

-- class Profunctor p => Strong p where
class IsoFunctor p => LensFunctor p where
  lensMap :: DataLens x y i o -> p x y -> p i o
  --      :: DataLens' xy io  -> p xy  -> p io

-- class Profunctor p => Choice p where
class IsoFunctor p => PrismFunctor p where
  prismMap :: DataPrism x y i o -> p x y -> p i o
  --       :: DataPrism' xy io  -> p xy  -> p io

class EqualityFunctor p where
  equalityMap :: DataEquality x y i o -> p x y -> p i o
  --          :: DataEquality' xy io  -> p xy  -> p io

class IsoFunctor p => CoprismFunctor p where
  coprismMap :: DataCoprism x y i o -> p x y -> p i o
  --         :: DataCoprism' xy io  -> p xy  -> p io

class LRFunctor l r p where
  lrMap :: DataLR x y l r i o -> p x y -> p i o
  --    :: DataLR' xy l r io  -> p l r xy  -> p l r io


instance FunFunctor ((->) a) where
  funMap = composeFun

--instance EqualFunctor (Equal a) where
--  equalMap = composeEqual

instance EqualFunctor f where
  equalMap Refl x = x

instance IsoFunctor (DataIso a b) where
  isoMap = composeIso

instance LensFunctor (DataLens a b) where
  lensMap = composeLens

instance PrismFunctor (DataPrism a b) where
  prismMap = composePrism

--instance EqualityFunctor (Equality a b) where
--  equalityMap = composeEquality

instance EqualityFunctor p where
  equalityMap (DataEquality Refl Refl) x = x

instance CoprismFunctor (DataCoprism a b) where
  coprismMap = composeCoprism

instance (Cat.Category l, Cat.Category r) => LRFunctor l r (DataLR a b l r) where
  lrMap = composeLR


instance IsoFunctor (DataLens a b) where
  isoMap = lensMap . isoLens

instance IsoFunctor (DataPrism a b) where
  isoMap = prismMap . isoPrism

instance IsoFunctor (DataCoprism a b) where
  isoMap = coprismMap . isoCoprism


type Fun b c = ∀ f . FunFunctor f => f b -> f c
type Equal b c = ∀ f . EqualFunctor f => f b -> f c

--   Iso s t a b = ∀ p . Profunctor p => p a b -> p s t
type Iso a b s t = ∀ p . IsoFunctor p => p a b -> p s t

--   Lens s t a b = ∀ p . Strong p => p a b -> p s t
type Lens a b s t = ∀ p . LensFunctor p => p a b -> p s t

--   Prism s t a b = ∀ p . Choice p => p a b -> p s t
type Prism a b s t = ∀ p . PrismFunctor p => p a b -> p s t

--   Equality s t a b = ∀ p . p a b -> p s t
type Equality a b s t = ∀ p . EqualityFunctor p => p a b -> p s t

type Coprism a b s t = ∀ p . CoprismFunctor p => p a b -> p s t

type LR l r a b s t = ∀ p . LRFunctor l r p => p a b -> p s t


type Iso' ab st = Iso ab ab st st
type Lens' ab st = Lens ab ab st st
type Prism' ab st = Prism ab ab st st
type Equality' ab st = Equality ab ab st st
type Coprism' ab st = Coprism ab ab st st
type LR' l r ab st = LR l r ab ab st st


toFun :: DataFun a b -> Fun a b
toFun = funMap

toEqual :: DataEqual a b -> Equal a b
toEqual = equalMap

toIso :: DataIso a b s t -> Iso a b s t
toIso = isoMap

toLens :: DataLens a b s t -> Lens a b s t
toLens = lensMap

toPrism :: DataPrism a b s t -> Prism a b s t
toPrism = prismMap

toEquality :: DataEquality a b s t -> Equality a b s t
toEquality = equalityMap

toCoprism :: DataCoprism a b s t -> Coprism a b s t
toCoprism = coprismMap

toLR :: DataLR a b l r s t -> LR l r a b s t
toLR = lrMap


fromFun :: Fun a b -> DataFun a b
fromFun f = f identityFun

fromEqual :: Equal a b -> DataEqual a b
fromEqual f = f identityEqual

fromIso :: Iso a b s t -> DataIso a b s t
fromIso f = f identityIso

fromLens :: Lens a b s t -> DataLens a b s t
fromLens f = f identityLens

fromPrism :: Prism a b s t -> DataPrism a b s t
fromPrism f = f identityPrism

fromEquality :: Equality a b s t -> DataEquality a b s t
fromEquality f = f identityEquality

fromCoprism :: Coprism a b s t -> DataCoprism a b s t
fromCoprism f = f identityCoprism

fromLR :: (Cat.Category l, Cat.Category r) => LR l r a b s t -> DataLR a b l r s t
fromLR f = f identityLR


equal :: Equal a a
equal = toEqual Refl

fun :: (a -> b) -> Fun a b
fun f = toFun f

iso :: (s -> a) -> (b -> t) -> Iso a b s t
iso f g = toIso (DataIso f g)

lens :: (s -> a) -> (b -> s -> t) -> Lens a b s t
lens f g = toLens (DataLens f g)

prism :: (s -> Either t a) -> (b -> t) -> Prism a b s t
prism f g = toPrism (DataPrism f g)

equality :: Equality a b a b
equality = toEquality (DataEquality Refl Refl)

coprism :: (s -> a) -> (b -> Either a t) -> Coprism a b s t
coprism f g = toCoprism (DataCoprism f g)

lr :: l s a -> r b t -> LR l r a b s t
lr l r = toLR (DataLR l r)


notted :: Iso' Bool Bool
notted = iso not not

swapped :: Iso (Either a b) (Either x y) (Either b a) (Either y x)
swapped = iso swap swap

first :: Lens a b (a, x) (b, x)
first = lens fst (\b (_, x) -> (b, x))

second :: Lens a b (x, a) (x, b)
second = lens snd (\b (x, _) -> (x, b))

right :: Prism a b (Either x a) (Either x b)
right = prism (lmap Left) Right

left :: Prism a b (Either a x) (Either b x)
left = prism (lmap Right . swap) Left

unright :: Coprism (Either x a) (Either x b) a b
unright = coprism Right (lmap Left)

unleft :: Coprism (Either a x) (Either b x) a b
unleft = coprism Left (lmap Right . swap)

data Red = Red deriving Show
data Green = Green deriving Show
data Blue = Blue deriving Show
data Colour = ColourRed Red | ColourGreen Green | ColourBlue Blue deriving Show

red :: Prism' Red Colour
red = re unred

unred :: Coprism' Colour Red
unred = ColourRed `coprism` \case
  ColourRed r -> Right r
  ColourGreen g -> Left (ColourGreen g)
  ColourBlue b -> Left (ColourBlue b)

eithered :: Iso' (Either () ()) Bool
eithered = iso bte etb where
  bte = \case
    True -> Right ()
    False -> Left ()
  etb = \case
    Right () -> True
    Left () -> False


instance IsoFunctor (->) where
  isoMap (DataIso ix yo) xy =
    yo . xy . ix

instance LensFunctor (->) where
  lensMap (DataLens ix yio) xy i =
    yio (xy (ix i)) i

instance PrismFunctor (->) where
  prismMap (DataPrism iox yo) xy i =
    case iox i of
      Left o -> o
      Right x -> yo (xy x)

instance CoprismFunctor (->) where
  coprismMap (DataCoprism ix yxo) xy i =
    spinX (ix i)
    where
      spinX x =
        case yxo (xy x) of
          Left x -> spinX x
          Right o -> o


over ::
  ((a -> b) -> s -> t) ->
  (a -> b) -> s -> t
over = id


newtype Tagged a b =
  Tagged { unTagged :: b }

instance PrismFunctor Tagged where
  prismMap (DataPrism _iox yo) (Tagged y) =
    Tagged (yo y)

instance IsoFunctor Tagged where
  isoMap = prismMap . isoPrism

review ::
  (Tagged a b -> Tagged s t) ->
  b -> t
review f b = unTagged (f (Tagged b))


newtype Forget r s t =
  Forget { unForget :: s -> r }

instance LensFunctor (Forget r) where
  lensMap (DataLens ix _yo) (Forget xr) =
    Forget (xr . ix)

instance IsoFunctor (Forget r) where
  isoMap = lensMap . isoLens

instance Monoid r => PrismFunctor (Forget r) where
  prismMap (DataPrism iox _yo) (Forget xr) =
    Forget (\i -> case iox i of
                    Left _o -> mempty
                    Right x -> xr x)

instance CoprismFunctor (Forget r) where
  coprismMap (DataCoprism ix _yxo) (Forget xr) =
    Forget (xr . ix)

view ::
  (Forget a a b -> Forget a s t) ->
  s -> a
view f s = unForget (f (Forget id)) s

preview ::
  (Forget (First a) a b -> Forget (First a) s t) ->
  s -> Maybe a
preview f s =
  getFirst $
    unForget (f (Forget (First . Just))) s


newtype Re p a b s t =
  Re { unRe :: p t s -> p b a }

instance IsoFunctor p => IsoFunctor (Re p a b) where
  isoMap (DataIso ix yo) (Re yxba) =
    Re (yxba . isoMap (DataIso yo ix))

instance PrismFunctor p => CoprismFunctor (Re p a b) where
  coprismMap (DataCoprism ix yxo) (Re yxba) =
    Re (yxba . prismMap (DataPrism yxo ix))

instance CoprismFunctor p => PrismFunctor (Re p a b) where
  prismMap (DataPrism iox yo) (Re yxba) =
    Re (yxba . coprismMap (DataCoprism yo iox))

re ::
  (Re p a b a b -> Re p a b s t) ->
  p t s -> p b a
re f = unRe (f (Re id))


newtype Matched b s t =
  Matched { unMatched :: b -> Maybe t }

instance IsoFunctor (Matched b) where
  isoMap = coprismMap . isoCoprism

instance CoprismFunctor (Matched b) where
  coprismMap (DataCoprism ix yxo) (Matched bmy) =
    Matched (\b -> bmy b >>= \y -> case yxo y of
                Left _ -> Nothing
                Right o -> Just o)

match ::
  (Matched b a b -> Matched b s t) ->
  b -> Maybe t
match f = unMatched (f (Matched Just))

hush :: Either a b -> Maybe b
hush (Left _) = Nothing
hush (Right b) = Just b

note :: a -> Maybe b -> Either a b
note a Nothing = Left a
note _ (Just b) = Right b

newtype FallOver a b s t =
  FallOver { unFallOver :: (a -> b) -> s -> Maybe t }
  deriving Functor

instance IsoFunctor (FallOver a b) where
  isoMap = coprismMap . isoCoprism

instance CoprismFunctor (FallOver a b) where
  coprismMap (DataCoprism ix yxo) (FallOver abxmy) =
    FallOver \ab i -> (hush . yxo) =<< abxmy ab (ix i)

instance PrismFunctor (FallOver a b) where
  prismMap (DataPrism iox yo) (FallOver f) =
    FallOver \ab i ->
      case iox i of
        Left o -> Just o
        Right x -> yo <$> f ab x

instance LensFunctor (FallOver a b) where
  lensMap (DataLens ix yio) (FallOver f) =
    FallOver \ab i -> (\y -> yio y i) <$> f ab (ix i)

setterFallOver ::
  ((a -> b) -> s -> t) ->
  ((a -> b) -> s -> Maybe t)
setterFallOver abst ab s =
  Just (abst ab s)

fallOver ::
  (FallOver a b a b -> FallOver a b s t) ->
  (a -> b) -> s -> Maybe t
fallOver l ab s = unFallOver (l (FallOver (Just .))) ab s

(%?~) = fallOver
infix 4 %?~
(&) x f = f x
infixl 0 &

pos42 :: Refined Positive Int
pos42 = $$(refineTH 42)

refined :: forall c d a . Predicate d a => Coprism a a (Refined c a) (Refined d a)
refined = coprism unrefine \b -> const b `lmap` refine b

fined :: forall c d a . Predicate c a => Prism (Refined c a) (Refined d a) a a
fined = re refined


data Coyoneda :: (Type -> Type) -> (Type -> Type) where
  Coyoneda :: (x -> y) -> f x -> Coyoneda f y

instance Foldable f => Foldable (Coyoneda f) where
  foldMap g (Coyoneda xy fx) = foldMap (g . xy) fx

newtype Yoneda f a = Yoneda (forall i . (a -> i) -> f i)
  deriving Functor

instance Foldable f => Foldable (Yoneda f) where
  foldMap g (Yoneda y) = fold (y g)

-- fold (Coyoneda xy fx) = foldMap xy fx
-- foldMap g (Yoneda y) = fold (y g)

--maximum :: Foldable f => f Int -> Int
-- coyoneda says: `f Int ~= ∃ i . (i -> x, f i)`
--maximum :: ∀ f . Foldable f => (∃ i . (i -> Int, f i)) -> Int
-- lift out `i`
--maximumBy :: ∀ f i . Foldable f => (i -> Int, f i) -> Int
-- curry
maximumBy :: ∀ f i . Foldable f => (i -> Int) -> f i -> Int
maximumBy f xs = maximum (Coyoneda f xs)



refined' ::
  forall c a m .
  (Predicate c a, Alternative m, Monad m) =>
  (a -> m a) ->
  Refined c a -> m (Refined c a)
refined' f r = f (unrefine r) >>= asum . Coyoneda pure . refine

refined'' ::
  forall c d a b m .
  (Predicate d b, Alternative m, Monad m) =>
  (a -> m b) ->
  Refined c a -> m (Refined d b)
refined'' f r = f (unrefine r) >>= asum . Coyoneda pure . refine



newtype Star m a b = Star { unStar :: a -> m b }

instance Monad m => Cat.Category (Star m) where
  id = Star pure
  Star f . Star g = Star \x -> g x >>= f

instance Functor m => IsoFunctor (Star m) where
  isoMap (DataIso ix yo) (Star xmy) =
    Star (fmap yo . xmy . ix)

instance (Monad m, Alternative m) => CoprismFunctor (Star m) where
  coprismMap (DataCoprism ix yxo) (Star xmy) =
    Star \i -> xmy (ix i) >>= \y ->
      case yxo y of
        Left _ -> empty
        Right o -> pure o

instance Applicative m => PrismFunctor (Star m) where
  prismMap (DataPrism iox yo) (Star f) =
    Star \i ->
      case iox i of
        Left o -> pure o
        Right x -> yo <$> f x

instance Functor m => LensFunctor (Star m) where
  lensMap (DataLens ix yio) (Star f) =
    Star \i -> (\y -> yio y i) <$> f (ix i)

fallen ::
  (Star Maybe a b -> Star Maybe s t) ->
  (a -> b) -> s -> Maybe t
fallen l ab s = unStar (l (Star $ Just . ab)) s


(%??~) o f = o (Just . f)


{-

data Options = One | Two deriving Show
showOptions :: Options -> String
showOptions One = "ONE"
showOptions Two = "TWO"
readOptions :: String -> Either String Options
readOptions "ONE" = Right One
readOptions "TWO" = Right Two
readOptions s = Left s
optionsString :: Prism' Options String
optionsString = prism readOptions showOptions
stringOptions :: Coprism' String Options
stringOptions = coprism showOptions readOptions

-- lots of things you can do with a prism

prism_review :: DataPrism a b s t -> b -> t
prism_review (DataPrism _sta bt) = bt

prism_preview :: DataPrism a b s t -> s -> Maybe a
prism_preview (DataPrism sta _bt) s =
  case sta s of
    Left _t -> Nothing
    Right a -> Just a

prism_nomatch :: DataPrism a b s t -> s -> Maybe t
prism_nomatch (DataPrism sta _bt) s =
  case sta s of
    Left t -> Just t
    Right _a -> Nothing

prism_over :: DataPrism a b s t -> (a -> b) -> s -> t
prism_over (DataPrism sta bt) ab s =
  case sta s of
    Left t -> t
    Right a -> bt (ab a)

prism_foldMap :: Monoid m => DataPrism a b s t -> (a -> m) -> s -> m
prism_foldMap (DataPrism sta _bt) am s =
  case sta s of
    Left _t -> mempty
    Right a -> am a

prism_traverse :: Applicative f => DataPrism a b s t -> (a -> f b) -> s -> f t
prism_traverse (DataPrism sta bt) afb s =
  case sta s of
    Left t -> pure t
    Right a -> bt <$> afb a

prism_over2 :: DataPrism a b s t -> (a -> a -> b) -> s -> s -> t
prism_over2 (DataPrism sta bt) aab sl sr =
  case (sta sl, sta sr) of
    (Left tl, _ta) -> tl
    (_ta, Left tr) -> tr
    (Right al, Right ar) -> bt (aab al ar)

prism_foldMap2 :: Monoid m => DataPrism a b s t -> (a -> a -> m) -> s -> s -> m
prism_foldMap2 (DataPrism sta bt) aam sl sr =
  case (sta sl, sta sr) of
    (Left _tl, _ta) -> mempty
    (_ta, Left _tr) -> mempty
    (Right al, Right ar) -> aam al ar

prism_traverse2 :: Applicative f => DataPrism a b s t -> (a -> a -> f b) -> s -> s -> f t
prism_traverse2 (DataPrism sta bt) aafb sl sr =
  case (sta sl, sta sr) of
    (Left tl, _ta) -> pure tl
    (_ta, Left tr) -> pure tr
    (Right al, Right ar) -> bt <$> aafb al ar

prism_overTraversable :: Traversable g => DataPrism a b s t -> (g a -> b) -> g s -> t
prism_overTraversable (DataPrism sta bt) gab gs =
  case gab <$> traverse sta gs of
    Left t -> t
    Right b -> bt b

prism_traverseTraversable :: (Traversable g, Applicative f) => DataPrism a b s t -> (g a -> f b) -> g s -> f t
prism_traverseTraversable (DataPrism sta bt) gab gs =
  case gab <$> traverse sta gs of
    Left t -> pure t
    Right b -> bt <$> b

prism_bicase :: DataPrism a b s t -> (a -> r) -> (t -> r) -> s -> r
prism_bicase (DataPrism sta _bt) ar tr s =
  case sta s of
    Left t -> tr t
    Right a -> ar a

prism_par :: DataPrism a b s t -> DataPrism c d s t -> (a -> c -> Either b d) -> s -> t
prism_par (DataPrism sta bt) (DataPrism stc dt) f s =
  case (sta s, stc s) of
    (Left tl, _tc) -> tl
    (_ta, Left tr) -> tr
    (Right a, Right c) ->
      case f a c of
        Left b -> bt b
        Right d -> dt d

prism_rap :: DataPrism a b s t -> DataPrism a b u v -> (a -> b) -> s -> Either t v
prism_rap (DataPrism sta _bt) (DataPrism _uva bv) ab s =
  case sta s of
    Left t -> Left t
    Right a -> Right (bv (ab a))

prism_rapt :: DataPrism a b s t -> DataPrism a b u v -> (a -> a -> r) -> (Either t v -> r) -> s -> u -> r
prism_rapt (DataPrism sta bt) (DataPrism uva bv) aar tvr s u =
  case (sta s, uva u) of
    (Left t, _va) -> tvr (Left t)
    (_ta, Left v) -> tvr (Right v)
    (Right al, Right ar) -> aar al ar

prism_raptt :: DataPrism a b s t -> DataPrism a b u v -> (a -> r) -> (t -> v -> r) -> s -> u -> r
prism_raptt (DataPrism sta bt) (DataPrism uva bv) ar tvr s u =
  case (sta s, uva u) of
    (Right a, _va) -> ar a
    (_ta, Right a) -> ar a
    (Left t, Left v) -> tvr t v

data Nav =
  Forwards Nav |
  Backwards Nav |
  Done
  deriving (Show, Eq, Ord, Read)

_Forwards :: Prism' Nav Nav
_Forwards =
  prism
    (\case
      Forwards n -> Right n
      other -> Left other)
    Forwards

_Backwards :: Prism' Nav Nav
_Backwards =
  prism
    (\case
      Backwards n -> Right n
      other -> Left other)
    Backwards

_Done :: Prism' () Nav
_Done =
  prism
    (\case
      Done -> Right ()
      other -> Left other)
    (const Done)

data SpaceF r =
  SpaceF
    { forwardF :: r
    , backwardF :: r
    }
  deriving (Show, Eq, Ord, Read, Foldable, Functor, Traversable)

atForwardF :: Lens' r (SpaceF r)
atForwardF = lens forwardF (\b c -> c { forwardF = b })

atBackwardF :: Lens' r (SpaceF r)
atBackwardF = lens backwardF (\b c -> c { backwardF = b })

data Cofree f a = Cofree { arg :: a, next :: f (Cofree f a) }
  deriving (Functor)

atArg :: Lens' a (Cofree f a)
atArg = lens arg (\b c -> c { arg = b })

atNext :: Lens' (f (Cofree f a)) (Cofree f a)
atNext = lens next (\b c -> c { next = b })

type Space = Cofree SpaceF

forward :: Lens' (Space a) (Space a)
forward = atNext . atForwardF

backward :: Lens' (Space a) (Space a)
backward = atNext . atBackwardF

done :: Lens' a (Space a)
done = atArg

atNav :: Nav -> Lens' a (Space a)
atNav = \case
  Forwards k -> forward . atNav k
  Backwards k -> backward . atNav k
  Done -> done

levelSpace :: Space Int
levelSpace =
  Cofree
    { arg = 0
    , next =
        SpaceF
          { forwardF = succ <$> levelSpace
          , backwardF = succ <$> levelSpace
          }
    }

data DataKeyLens k a b s t =
  DataKeyLens (s -> (k, a)) (b -> s -> t)

type DataKeyLens' k ab st = DataKeyLens k ab ab st st

class KeyLensFunctor k p q | p -> q where
  keyLensMap :: DataKeyLens k x y i o -> p x y -> q i o

--instance KeyLensFunctor DataLens where
--  keyLensMap (DataKeyLens ika kayio) =
--    DataLens (snd . ika) (kayio . const)

instance KeyLensFunctor k (->) (->) where
  keyLensMap (DataKeyLens ikx kyio) xy i =
    kyio (xy (snd $ ikx i)) i

newtype KeyPro k p x y = KeyPro { kfn :: p (k, x) y }

instance LensFunctor p => KeyLensFunctor k (KeyPro k p) p where
  keyLensMap (DataKeyLens ikx kyio) (KeyPro kxy) =
    lensMap (DataLens ikx kyio) kxy

type KeyLens k a b s t = ∀ p q . KeyLensFunctor k p q => p a b -> q s t

toKeyLens :: DataKeyLens k a b s t -> KeyLens k a b s t
toKeyLens = keyLensMap

keyLens :: (s -> (k, a)) -> (b -> s -> t) -> KeyLens k a b s t
keyLens f g = toKeyLens (DataKeyLens f g)

iover :: (KeyPro k (->) a b -> s -> t) -> (k -> a -> b) -> s -> t
iover l = l . KeyPro . uncurry

keyFirst :: KeyLens Bool x y (x, a) (y, a)
keyFirst =
  keyLens
    (\(l, _) -> (False, l))
    (\l (_, r) -> (l, r))

keySecond :: KeyLens Bool x y (a, x) (a, y)
keySecond =
  keyLens
    (\(_, r) -> (True, r))
    (\r (l, _) -> (l, r))

newtype DataKeyTraversal k a b s t =
  DataKeyTraversal
    (∀ f . Applicative f => (k -> a -> f b) -> s -> f t)

type DataKeyTraversal' k ab st = DataKeyTraversal k ab ab st st

class KeyTraversalFunctor k p q | p -> q where
  keyTraversalMap :: DataKeyTraversal k x y i o -> p x y -> q i o

instance KeyTraversalFunctor k (->) (->) where
  keyTraversalMap (DataKeyTraversal f) xy =
    runIdentity . f (\_ -> Identity . xy)

instance KeyTraversalFunctor k (KeyPro k (->)) (->) where
  keyTraversalMap (DataKeyTraversal f) (KeyPro kxy) =
    runIdentity . f (curry $ Identity . kxy)

type KeyTraversal k a b s t = ∀ p q . KeyTraversalFunctor k p q => p a b -> q s t

type KeyTraversal' k ab st = KeyTraversal k ab ab st st

toKeyTraversal :: DataKeyTraversal k a b s t -> KeyTraversal k a b s t
toKeyTraversal = keyTraversalMap

keyTraversal :: (∀ f . Applicative f => (k -> a -> f b) -> s -> f t) -> KeyTraversal k a b s t
keyTraversal f = toKeyTraversal (DataKeyTraversal f)

newtype Star f a b = Star { unStar :: a -> f b }

keyTraversed :: (KeyPro k (Star f) a b -> Star f s t) -> (k -> a -> f b) -> s -> f t
keyTraversed l f = unStar $ l (KeyPro (Star (uncurry f)))

itemsWithKey :: ∀ a b . KeyTraversal Integer a b [a] [b]
itemsWithKey = keyTraversal go where
  go :: ∀ f . Applicative f => (Integer -> a -> f b) -> [a] -> f [b]
  go f = how 0 where
    how k = \case
      [] -> pure []
      (x : xs) -> (:) <$> f k x <*> how (k + 1) xs

newtype DataXTraversal g a b s t =
  DataXTraversal
    (∀ f . Applicative f => (g a -> f b) -> s -> f t)

type DataXTraversal' g ab st = DataXTraversal g ab ab st st

class (IsoFunctor p, IsoFunctor q) => XTraversalFunctor g p q | p -> q where
  xTraversalMap :: DataXTraversal g x y i o -> p x y -> q i o

type XTraversal g a b s t = ∀ p q . XTraversalFunctor g p q => p a b -> q s t

type XTraversal' g ab st = XTraversal g ab ab st st

isoXTraversal :: DataIso a b s t -> DataXTraversal Identity a b s t
isoXTraversal (DataIso sa bt) = DataXTraversal (\ia_fb s -> bt <$> ia_fb (Identity (sa s)))

instance IsoFunctor (DataXTraversal g a b) where
  isoMap (DataIso ix yo) r =
    DataXTraversal (\gafb i -> do
      let DataXTraversal gavb_x_vy = r
      yo <$> gavb_x_vy gafb (ix i))

instance Comonad g => XTraversalFunctor g (DataXTraversal g a b) (DataXTraversal g a b) where
  xTraversalMap (DataXTraversal gxuy_i_uo) (DataXTraversal gavb_x_vy) =
    DataXTraversal (\gafb i -> gxuy_i_uo (\gx -> gavb_x_vy gafb (extract gx)) i)

toXTraversal :: DataXTraversal g a b s t -> XTraversal g a b s t
toXTraversal = xTraversalMap

identityXTraversal :: DataXTraversal g a b (g a) b
identityXTraversal = DataXTraversal id

identityTraversal :: DataXTraversal Identity a b a b
identityTraversal = DataXTraversal (. Identity)

fromX :: DataXTraversal g a b s t -> DataXTraversal Identity (g a) b s t
fromX (DataXTraversal h) = DataXTraversal (\iga_fb -> h (iga_fb . Identity))

toX :: DataXTraversal Identity (g a) b s t -> DataXTraversal g a b s t
toX (DataXTraversal h) = DataXTraversal (\ga_fb -> h (ga_fb . runIdentity))

fromTraversal :: XTraversal Identity a b s t -> DataXTraversal Identity a b s t
fromTraversal f = f identityTraversal

fromXTraversal :: forall g a b s t . (DataXTraversal g a b (g a) b -> DataXTraversal g a b s t) -> DataXTraversal g a b s t
fromXTraversal f = f identityXTraversal

class Comonad w where
  extract :: w a -> a
  extend :: w a -> (w a -> b) -> w b

instance Comonad Identity where
  extract = runIdentity
  extend w f = Identity (f w)

instance Comonad ((,) l) where
  extract = snd
  extend (x, a) f = (x, f (x, a))

instance Comonad g => XTraversalFunctor g (->) (->) where
  xTraversalMap (DataXTraversal f) xy =
    runIdentity . f (\gx -> Identity (xy (extract gx)))

instance IsoFunctor p => IsoFunctor (KeyPro k p) where
  isoMap (DataIso ix yo) (KeyPro kxy) =
    KeyPro (isoMap (DataIso (second ix) yo) kxy)

instance XTraversalFunctor Identity p q => XTraversalFunctor ((,) k) (KeyPro k p) q where
  xTraversalMap f (KeyPro kxy) =
    xTraversalMap (fromX f) kxy

class C a b | a -> b where
  ccc :: a -> b
instance C Int String where
  ccc = show

class D a b where
  ddd :: a -> b
instance b ~ String => D Int b where
  ddd = show


-- length-indexed free monoid
data Vect ∷ Nat → Type → Type where
  Cons ∷ ∀ t . Vect 0 t
  Nil ∷ ∀ t n . t → Vect n t → Vect (1 + n) t

data Day ∷ (Type → Type) → (Type → Type) → Type → Type where
  MkDay ∷ ∀ f g a x y . f x → g y → (x → y → a) → Day f g a

deriving instance Functor (Day f g)
instance (Foldable f, Foldable g) => Foldable (Day f g) where
  foldMap t (MkDay fx gy xyz) = foldMap (\x -> foldMap (\y -> t (xyz x y)) gy) fx

dayL ∷ (∀ i . f i -> r) -> Day f g x -> r
dayL t (MkDay f _ _) = t f

dayR ∷ (∀ i . g i -> r) -> Day f g x -> r
dayR t (MkDay _ g _) = t g

-- size-indexed free Applicative
data Days ∷ Nat → (Type → Type) → Type → Type where
  Next ∷ ∀ f i n . Day f (Days n f) i → Days (1 + n) f i
  None ∷ ∀ f i . i → Days 0 f i

coerce0Days :: Days 0 f x -> Days 0 g x
coerce0Days (None a) = None a
coerce0Days (Next i) = undefined

unNone :: Days 0 f x -> x
unNone (None x) = x
unNone (Next x) = undefined

-- depth-indexed free monad
data Iter ∷ Nat → (Type → Type) → Type → Type where
  Roll ∷ ∀ f i n . f (Iter n f i) → Iter (1 + n) f i
  Pure ∷ ∀ f i . i → Iter 0 f i

instance Functor f ⇒ Functor (Iter n f) where
  fmap f (Roll fa) = Roll (fmap f <$> fa)
  fmap f (Pure a) = Pure (f a)

infixr 0 ~>
type f ~> g = forall x. f x → g x

infixr 0 :→, $$
newtype f :→ g = NT { ($$) ∷ f ~> g }

type family (f ∷ k) ▷ (g ∷ k) ∷ Type where
  f ▷ g = f → g
  f ▷ g = f :→ g

class Monoid_ m where
  mempty_ ∷ (0 `Vect` m) ▷ m
  append_ ∷ (2 `Vect` m) ▷ m

class Functor m ⇒ Applicative_ m where
  pure_ ∷ (0 `Days` m) ▷ m
  apply_ ∷ (2 `Days` m) ▷ m

class Applicative_ m ⇒ Monad_ m where
  unit_ ∷ (0 `Iter` m) ▷ m
  join_ ∷ (2 `Iter` m) ▷ m

class Functor m => Comonad_ m where
  counit_ ∷ m ▷ (0 `Iter` m)
  duplicate_ ∷ m ▷ (2 `Iter` m)

class Functor m => Branchable_ m where
  copure_ ∷ m ▷ (0 `Days` m)
  branch_ ∷ m ▷ (2 `Days` m)


data Huh f a where
  MkHuh ∷ f a -> Day (Huh f) (Huh f) a -> Huh f a

instance Functor f ⇒ Functor (Huh f) where
  fmap f (MkHuh fa d) = MkHuh (f <$> fa) (fmap f d)

instance Branchable_ f => Branchable_ (Huh f) where
  copure_ = NT $ \(MkHuh fa _) -> coerce0Days (copure_ $$ fa)
  branch_ = NT $ \(MkHuh fa d) -> twoDays' d

copure' ∷ ∀ m i . Branchable_ m => m i -> i
copure' mi = unNone $ (copure_ $$ mi)

branch' ∷ ∀ m i . Branchable_ m => m i -> Day m m i
branch' mi = unTwoDays' $ (branch_ $$ mi)

instance Branchable_ Identity where
  copure_ = NT $ \(Identity a) -> None a
  branch_ = NT $ \ia -> twoDays' (MkDay ia ia const)

replicated ∷ Monoid a => f a -> Huh f a
replicated fa = let out = MkHuh fa (MkDay out out (<>)) in out

eg0 = replicated (Identity "!")
eg1 = copure' eg0

data Lat a = Lat { latA :: a, latI :: Int }
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance Branchable_ Lat where
  copure_ = NT $ \(Lat a _) -> None a
  branch_ = NT $ \(Lat a i) -> twoDays'
    (MkDay
      (Lat a (i - 1))
      (Lat a (i + 1))
      (\a b -> if mod i 2 == 0 then a else b))

toPure_ ∷ ∀ m . (∀ a . a → m a) → (0 `Days` m) ▷ m
toPure_ p = NT $ \(None foo) → p foo

pure' ∷ ∀ m a . Applicative_ m ⇒ a → m a
pure' a = pure_ $$ None a


--(a -> x * y) * (x * y -> r) -> (a -> r)
--(a -> r) -> (a -> x * y) * (x * y -> r)



toApply_ ∷
  ∀ m . Functor m ⇒
  (∀ a b c . m a → m b → (a → b → c) → m c) →
  (2 `Days` m) ▷ m
toApply_ mabc = NT $ \(unTwoDays' -> MkDay ma mb abc) -> mabc ma mb abc

apply' ∷ ∀ m a b c . Applicative_ m ⇒ m a → m b → (a → b → c) → m c
apply' ma mb abc = apply_ $$ twoDays' (MkDay ma mb abc)


toUnit_ ∷ ∀ m . (∀ a . a → m a) → (0 `Iter` m) ▷ m
toUnit_ u = NT $ \(Pure foo) → u foo

unit' ∷ ∀ m a . Monad_ m ⇒ a → m a
unit' a = unit_ $$ Pure a


toJoin_ ∷ ∀ m . Functor m ⇒ (∀ a . m (m a) → m a) → (2 `Iter` m) ▷ m
toJoin_ j = NT (j . unTwoIter')

join' ∷ Monad_ m ⇒ m (m a) → m a
join' mma = join_ $$ twoIter' mma


mapDay ∷ (x ~> i) → (y ~> o) → (s → t) → Day x y s → Day i o t
mapDay xi yo st (MkDay xa yb abs) = MkDay (xi xa) (yo yb) (\a b → st (abs a b))

twoDays' ∷ Day f f a → Days 2 f a
twoDays' ffa = Next (mapDay id (\fa → Next (MkDay fa (None ()) const)) id ffa)

unTwoDays' ∷ Functor f ⇒ Days 2 f a → Day f f a
unTwoDays' (Next (MkDay ma (Next (MkDay mb (None s) yst)) xyz)) =
  MkDay ma ((\b -> yst b s) <$> mb) xyz
unTwoDays' _ = undefined

twoIter' ∷ Functor m ⇒ m (m a) → Iter 2 m a
twoIter' mma = Roll ((\ma → Roll (Pure <$> ma)) <$> mma)

unTwoIter' ∷ Functor m ⇒ Iter 2 m a → m (m a)
unTwoIter' (Roll fi) = (\(Roll i) → (\(Pure a) → a) <$> i) <$> fi


newtype F f a = F { unF :: ∀ m . Monad_ m ⇒ (f ~> m) → m a }
data F2 f a = forall n . F2 { unF2 :: Iter n f a }

instance Functor f ⇒ Functor (F2 f) where
  fmap f (F2 i) = F2 (fmap f i)

instance Functor f ⇒ Applicative_ (F2 f) where
  pure_ = NT $ \(None i) → F2 (Pure i)
  apply_ = toApply_ $ \fa fb abc →
    join' ((\a → (\b → abc a b) <$> fb) <$> fa)

instance Functor f ⇒ Monad_ (F2 f) where
  unit_ = toUnit_ $ \i → F2 (Pure i)
  join_ = undefined





class Semigroupoid_ (k ∷ (o, o) → Type) where (∘) ∷ k '(b, c) → k '(a, b) → k '(a, c)
class Semigroupoid_ k ⇒ Category_ k where identity ∷ k '(x, x)

class Functor_ (f ∷ x → y) (c ∷ (x, x) → Type) (d ∷ (y, y) → Type) | f → c d where
  map_ ∷ c '(a, b) → d '(f a, f b)

infixl 0 $$$
data Fn ∷ (Type, Type) → Type where Fn ∷ { ($$$) :: i -> o } → Fn '(i, o)
instance Semigroupoid_ Fn where Fn f ∘ Fn g = Fn (f . g)
instance Category_ Fn where identity = Fn id

data Nt ∷ ((d, d) -> Type) -> ((c, c) -> Type) -> (d → c, d → c) → Type where
  Nt ∷ ∀ f g d c .
    (Functor_ f d c, Functor_ g d c) ⇒
    { runNt ∷ ∀ i . c '(f i, g i) } →
    Nt d c '(f, g)

instance (Semigroupoid_ l, Semigroupoid_ r) ⇒ Semigroupoid_ (Nt l r) where
  Nt f ∘ Nt g = Nt (f ∘ g)

data Product ∷ ((l, l) → Type) → ((r, r) → Type) → ((l, r), (l, r)) → Type where
  (:×:) ∷
    { first_ ∷ l '(a, s)
    , second_ ∷ r '(b, t) } →
    Product l r '( '(a, b), '(s, t) )

infixr 4 :/\:
data Pair ∷ (Type, Type) -> Type where
  (:/\:) ∷ ∀ l r . { fst_ ∷ l, snd_ ∷ r } → Pair '(l, r)

instance Functor_ Pair (Product Fn Fn) Fn where
  map_ (as :×: bt) = Fn (\(a :/\: b) → (as $$$ a) :/\: (bt $$$ b))

data Op ∷ ((o, o) → Type) → (o, o) → Type where
  Op ∷ { getOp ∷ k '(b, a) } → Op k '(a, b)

instance Functor_ Fn (Product (Op Fn) Fn) Fn where
  map_ (Op sa :×: bt) = Fn (\ab → bt ∘ ab ∘ sa)

data Yoneda ∷ ((d, d) -> Type) -> (d → Type, d) → Type where
  Yoneda ∷ ∀ k f g a i .
    Functor_ g k Fn ⇒
    { runYoneda ∷
        Nt k Fn '(f, g) →
        k '(a, i) →
        g i } →
    Yoneda k '(f, a)

instance Semigroupoid_ k ⇒ Functor_ (Yoneda k) (Product (Nt k Fn) k) Fn where
  map_ (n :×: f) = Fn (\(Yoneda y) → Yoneda (\a b -> y (a ∘ n) (b ∘ f)))

-- Bifunctors
lmap_ ∷ (Category_ r, Functor_ f (Product l r) d) ⇒ l '(a, s) → d '(f '(a, x), f '(s, x))
lmap_ l = map_ (l :×: identity)

rmap_ ∷ (Category_ l, Functor_ f (Product l r) d) ⇒ r '(b, t) → d '(f '(x, b), f '(x, t))
rmap_ r = map_ (identity :×: r)

-- Profunctors
lcmap_ ∷ (Category_ r, Functor_ f (Product (Op l) r) d) ⇒ l '(s, a) → d '(f '(a, x), f '(s, x))
lcmap_ l = lmap_ (Op l)


eg6 ∷ Pair '(Int, String)
eg6 = rmap_ (Fn show) $$$ (1 :/\: True)

newtype Compose f g a = Compose (f (g a))

class Functor_ m k k ⇒ Monad'_ m k | m → k where
  unit'_ ∷ Nt k k '(Identity, m)
  join'_ ∷ Nt k k '(Compose m m, m)

--instance Monad'_ (Yoneda k) k where

data Coyoneda :: (Type -> Type) -> (Type -> Type) where
  Coyo :: f x -> (x -> y) -> Coyoneda f y

www :: f a -> Compose (Coyoneda f) Maybe a
www f = Compose (Coyo f Just)


{-
data Zero ∷ Type where

data One ∷ Type where
  One0 ∷ One

data Two ∷ Type where
  Two0 ∷ Two
  Two1 ∷ Two

data Three ∷ Type where
  Three0 ∷ Three
  Three1 ∷ Three
  Three2 ∷ Three
-}

-- ...

data N = S N | Z

data Fin ∷ N → Type where
  Fin ∷ Maybe (Fin n) → Fin ('S n)

{-
type Zero = Fin 0
type One = Fin 1
type Two = Fin 2
type Three = Fin 3
-}

--

{-
data Zero ∷ Type → Type where Zero ∷ ∀ t . Zero t
data One ∷ Type → Type where One ∷ ∀ t . t → One t
data Two ∷ Type → Type where Two ∷ ∀ t . t → t → Two t
data Three ∷ Type → Type where Three ∷ ∀ t . t → t → t → Three t
-}

data Vec ∷ N → Type → Type where
  Vec ∷ ∀ t n . (Fin n → t) → Vec n t

nil ∷ Vec Z t
nil = Vec \case

how ∷ Vec (S Z) Int
how = Vec \case
  Fin Nothing -> 0
  Fin (Just v) -> case v of {}

{-
v0 ∷ Vec 1 Int
v0 = Vec (\case
  Fin Nothing -> 42
  Fin (Just _) -> undefined)
-}

-}

{-
data Combination :: Type -> Type where
  Zero :: Combination t
  More :: Foldable f => (a -> b -> c) -> f a -> Combination b -> Combination c
-}


data LST :: Type -> Type where
  LO :: a -> LST a
  LC :: (a -> b -> c) -> a -> LST b -> LST c

instance Functor LST where
  fmap f (LO v) = LO (f v)
  fmap f (LC g h t) = LC (\a b -> f (g a b)) h t

huh :: LST m -> m
huh (LO v) = v
huh (LC f h t) = huh (f h <$> t)

lst0 :: LST Integer
lst0 = LC (+) 10 (LC (+) 42 (LO 12))

data Night :: Type -> Type where
  NN :: Foldable f => f t -> Night t
  NC ::
    Foldable f =>
    (a -> b -> c) ->
    f a ->
    Night b ->
    Night c

instance Foldable Night where
  foldMap t (NN v) = foldMap t v
  foldMap t (NC abc fa nb) = foldMap (\a -> foldMap (t . abc a) nb) fa

nct :: Foldable f => f a -> Night b -> Night (a, b)
nct = NC (,)

night0 :: Night (Int, (String, Bool))
night0 = nct [1, 2] (nct (Just "Hi") (NN (Set.fromList [ True, False ])))

night1 :: String
night1 = night0 & foldMap show

data After :: (Type -> Type) -> Type -> Type -> Type where
  After :: (k -> v) -> f k -> After f k v

instance Foldable f => Foldable (After f k) where
  foldMap t (After kv sk) = foldMap (t . kv) sk


