{-# language
  RankNTypes,
  TypeInType,
  GADTs,
  FlexibleInstances,
  InstanceSigs,
  UnicodeSyntax,
  LambdaCase,
  ScopedTypeVariables,
  MultiParamTypeClasses,
  FunctionalDependencies
#-}

module Optics where

import Data.Kind

class Category k where
  compose :: ∀ a b c . k b c -> k a b -> k a c
  identity :: ∀ a . k a a

instance Category (->) where
  compose = (.)
  identity = id

newtype Star f a b = Star (a -> f b)

hmapStar :: (∀ i . f i -> g i) -> Star f a b -> Star g a b
hmapStar fg (Star afb) = Star (fg . afb)

instance Monad f => Category (Star f) where
  compose (Star f) (Star g) = Star (\x -> g x >>= f)
  identity = Star pure

data Equal :: Type -> Type -> Type where
  Refl :: ∀ x . Equal x x

instance Category Equal where
  compose Refl Refl = Refl
  identity = Refl

lmap :: (e -> f) -> Either e a -> Either f a
lmap f = \case
  Right a -> Right a
  Left e -> Left (f e)



-- Concrete Equality
-- Types are on-the-nose identical
data Same a b s t =
  Same (Equal s a) (Equal b t)

type Same' a s = Same a a s s

-- Concrete Iso
-- Types are equivalent - can convert back and forth without information loss
data Exchange a b s t =
 Exchange ((->) s a) ((->) b t)

type Exchange' a s = Exchange a a s s

-- every same is an exchange
-- every equality is an iso
sameExchange :: ∀ a b s t . Same a b s t -> Exchange a b s t
sameExchange (Same Refl Refl) = Exchange identity identity

-- Concrete Prism
-- Type is equivalent to an Either - can discriminate between two cases
data Market a b s t =
 Market (Star (Either t) s a) ((->) b t)

type Market' a s = Market a a s s

-- every exchange is a market
-- every iso is a prism
exchangeMarket :: ∀ a b s t . Exchange a b s t -> Market a b s t
exchangeMarket (Exchange sa bt) = Market (Star (pure . sa)) bt

-- Concrete Lens
-- Type is equivalent to a Tuple - can split into two parts
data Shop a b s t =
 Shop ((->) s a) (Star ((->) s) b t)

type Shop' a s = Shop a a s s

-- every exchange is a shop
-- every iso is a lens
exchangeShop :: ∀ a b s t . Exchange a b s t -> Shop a b s t
exchangeShop (Exchange sa bt) = Shop sa (Star (pure . bt))

-- Concrete Grate
-- Type is equivalent to a Function from some type - can read from an env
newtype Grating a b s t =
  Grating (((s -> a) -> b) -> t)

type Grating' a s = Grating a a s s

-- every exchange is a grating
-- every iso is a grate
exchangeGrating :: ∀ a b s t . Exchange a b s t -> Grating a b s t
exchangeGrating (Exchange sa bt) = Grating (\sab -> bt (sab sa))


-- Written as a class for symmetry
class Given p where
  given :: ∀ x y i o . Same x y i o -> p x y -> p i o

-- works for any (Type -> Type -> Type) type constructor
instance Given p where
  given (Same Refl Refl) = id

-- e.g.
-- instance Given (Same a b)


{-
class Functor f where
  fmap :: ∀ xy io . (->) xy io -> f xy -> f io

-- the domain arrow itself is an instance
instance Functor ((->) a) where
  fmap :: ∀ xy io . (->) xy io -> (->) a xy -> (->) a io
  fmap = (.)

class Profunctor p where
  dimap :: ∀ x y i o . (i -> x) -> (y -> o) -> p x y -> p i o
-}

-- a functor maps arrows to arrows, therefore the
-- `(i -> x, y -> o)`
-- is an arrow is some category
-- this is our `Exchange x y i o` type

class Profunctor p where
  dimap :: ∀ x y i o . Exchange x y i o -> p x y -> p i o

-- the domain arrow itself is an instance
instance Profunctor (Exchange a b) where
  --dimap :: ∀ xy io . Exchange' xy io -> Exchange' ab xy -> Exchange' ab io
  dimap :: ∀ x y i o . Exchange x y i o -> Exchange a b x y -> Exchange a b i o
  dimap (Exchange f g) (Exchange x y) = Exchange (x . f) (g . y)

-- not how this is defined
class Profunctor p => Choice p where
  choice :: ∀ x y i o . Market x y i o -> p x y -> p i o

-- the domain arrow itself is an instance
instance Choice (Market a b) where
  --choice :: ∀ xy io . Market' xy io -> Market' ab xy -> Market' ab io
  choice :: ∀ x y i o . Market x y i o -> Market a b x y -> Market a b i o
  choice (Market ieox yo) (Market xeya by) =
    Market
      (compose (hmapStar (lmap yo) xeya) ieox)
      (compose yo by)

instance Profunctor (Market a b) where
  dimap = choice . exchangeMarket


-- not how this is defined
class Profunctor p => Strong p where
  strong :: ∀ x y i o . Shop x y i o -> p x y -> p i o

-- the domain arrow itself is an instance
instance Strong (Shop a b) where
  --strong :: ∀ xy io . Shop' xy io -> Shop' ab xy -> Shop' ab io
  strong :: ∀ x y i o . Shop x y i o -> Shop a b x y -> Shop a b i o
  strong (Shop ix iyo) (Shop xa xby) =
    Shop
      (compose xa ix)
      (compose iyo (hmapStar (. ix) xby))

instance Profunctor (Shop a b) where
  dimap = strong . exchangeShop


-- not how this is defined
class Profunctor p => Closed p where
  closed :: ∀ x y i o . Grating x y i o -> p x y -> p i o

-- the domain arrow itself is an instance
instance Closed (Grating a b) where
  --closed :: ∀ xy io . Grating' xy io -> Grating' ab xy -> Grating' ab io
  closed :: ∀ x y i o . Grating x y i o -> Grating a b x y -> Grating a b i o
  closed (Grating f) (Grating g) =
    Grating (\ia_b -> f (\ix -> g (\xa -> ia_b (xa . ix))))

instance Profunctor (Grating a b) where
  dimap = closed . exchangeGrating


type Equality s t a b = ∀ p . Given p => p a b -> p s t
type Iso s t a b = ∀ p . Profunctor p => p a b -> p s t
type Prism s t a b = ∀ p . Choice p => p a b -> p s t
type Lens s t a b = ∀ p . Strong p => p a b -> p s t
type Grate s t a b = ∀ p . Closed p => p a b -> p s t


type Equality' s a = Equality s s a a
type Iso' s a = Iso s s a a
type Prism' s a = Prism s s a a
type Lens' s a = Lens s s a a
type Grate' s a = Grate s s a a


prism :: ∀ s t a b . (s -> Either t a) -> (b -> t) -> Prism s t a b
prism l r = choice (Market (Star l) r)

lens :: ∀ s t a b . (s -> a) -> (b -> s -> t) -> Lens s t a b
lens l r = strong (Shop l (Star r))

-- ∀ p a b x . Choice p => p a b -> p (Either x a) (Either x b)
right :: ∀ x a b . Prism (Either x a) (Either x b) a b
right = prism (lmap Left) Right

second :: ∀ x a b . Lens (x, a) (x, b) a b
second = lens snd (\b (x, _) -> (x, b))

grate :: ∀ s t a b . (((s -> a) -> b) -> t) -> Grate s t a b
grate f = closed (Grating f)

codomain :: ∀ x a b . Grate (x -> a) (x -> b) a b
codomain = grate (\g x -> g (\f -> f x))

what :: (Choice p, Strong p, Closed p) =>
  p a b ->
  p (Either x (x1, x2 -> a)) (Either x (x1, x2 -> b))
what = right . second . codomain


type Optic p s t a b = p a b -> p s t


instance Profunctor (->) where
  dimap (Exchange f g) h = g . h . f

instance Choice (->) where
  choice (Market (Star f) g) h i =
    case f i of
      Left o -> o
      Right x -> g (h x)

instance Strong (->) where
  strong (Shop f (Star g)) h i =
    g (h (f i)) i

instance Closed (->) where
  closed (Grating f) h i =
    f (\ix -> h (ix i))

modify :: Optic (->) s t a b -> (a -> b) -> (s -> t)
modify = id


newtype Forget r i o = Forget { unForget :: i -> r }

instance Profunctor (Forget a) where
  dimap (Exchange f _) (Forget h) = Forget (h . f)

instance Strong (Forget a) where
  strong :: ∀ x y i o .
    Shop x y i o -> Forget a x y -> Forget a i o
  strong (Shop f _) (Forget r) =
    Forget (r . f)

instance Monoid a => Choice (Forget a) where
  choice (Market (Star f) _) (Forget g) =
    Forget (\i -> case f i of
                    Left _ -> mempty
                    Right x -> g x)


shopForget :: ∀ a b s t . Shop a b s t -> Forget a s t
shopForget (Shop f _) = Forget f

marketForget :: ∀ a b s t . Monoid a => Market a b s t -> Forget a s t
marketForget (Market (Star f) _) =
  Forget (\s -> case f s of
                  Left _ -> mempty
                  Right a -> a)


class Strong p => Gettable p r | p -> r where
  gettable :: ∀ x y i o . Forget x i o -> p x y -> p i o

instance Gettable (Forget a) a where
  gettable :: ∀ x y i o . Forget x i o -> Forget a x y -> Forget a i o
  gettable (Forget f) (Forget g) =
    Forget (g . f)

type Getter s t a b = ∀ p r . Gettable p r => p a b -> p s t

type Fold r s t a b = ∀ p . Gettable p r => p a b -> p s t

type AFold r s t a b = Forget r a b -> Forget r s t

view :: AFold a s t a b -> s -> a
view f = unForget (f (Forget id))


{-
class (Gettable p, Choice p, Monoid r) => MonoidOf p r | p -> r where
  monoidOf :: ∀ x y i o . Forget x i o -> p x y -> p i o
-}

{-
instance Monoid a => MonoidOf (Forget a) a where
  monoidOf (Forget f) (Forget g) = Forget (g . f)

type Fold r s t a b = ∀ p . MonoidOf p r => p a b -> p s t

foldOf :: ∀ r s t a b . Monoid a => Fold a s t a b -> s -> a
foldOf f = unForget (f (Forget id))
-}

