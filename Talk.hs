{-# language
  RankNTypes,
  TypeInType,
  GADTs,
  FlexibleInstances,
  InstanceSigs,
  UnicodeSyntax,
  LambdaCase,
  ScopedTypeVariables,
  TypeApplications
#-}

module Talk where

import Data.Kind
import Data.Monoid (First(..))

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


type Exchange = DataIso
type Shop = DataLens
type Market = DataPrism


type DataIso' ab st = DataIso ab ab st st
type DataLens' ab st = DataLens ab ab st st
type DataPrism' ab st = DataPrism ab ab st st
type DataEquality' ab st = DataEquality ab ab st st


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


instance IsoFunctor (DataLens a b) where
  isoMap = lensMap . isoLens

instance IsoFunctor (DataPrism a b) where
  isoMap = prismMap . isoPrism


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


type Iso' ab st = Iso ab ab st st
type Lens' ab st = Lens ab ab st st
type Prism' ab st = Prism ab ab st st
type Equality' ab st = Equality ab ab st st


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

re ::
  (Re p a b a b -> Re p a b s t) ->
  p t s -> p b a
re f = unRe (f (Re id))

