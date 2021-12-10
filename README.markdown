# What we talk about when we talk about Optics

## Types and how they relate

With any type `A`, we have the trivial equality relationship of `A` with
itself.  Here are some example programs that feature this relationship:

```haskell
id :: A -> A
id, ($) :: ∀ r . (A -> r) -> A -> r
flip id :: A -> (∀ r . (A -> r) -> r)
($ id) :: (∀ r . (A -> r) -> r) -> A
-- and infinitely more
```

With `Tuple A A` and `Tuple A A` we have the trivial equality relationship as
above.  But, we also have a 'swapping' relationship.  That is, with any
computation involving `Tuple A A`, we could think of an equivalent computation
that consistently swapped the first and second components of the tuples
involved.

With `A` and `Tuple X A` we can do:

```haskell
id, ($) :: (A -> Tuple X A) -> A -> Tuple X A
snd :: Tuple X A -> A
fmap :: (A -> B) -> Tuple X A -> Tuple X B
foldMap :: ∀ r . Monoid r => (A -> r) -> Tuple X A -> r
-- and infinitely more
```

With `A` and `Either X A` we can do:

```haskell
id, ($) :: (A -> Either X A) -> A -> Either X A
Right :: A -> Either X A
rightMaybe :: Either X A -> Maybe A
fmap :: (A -> B) -> Either X A -> Either X B
foldMap :: ∀ r . Monoid r => (A -> r) -> Either X A -> r
-- and infinitely more
```

With `A` and `(X -> A)` we can do:

```haskell
id, ($) :: (X -> A) -> (X -> A)
pure, const :: A -> (X -> A)
fmap, (.) :: (A -> B) -> (X -> A) -> (X -> B)
-- and infinitely more
```


## Equivalent relationships

Suppose we have a type:

```haskell
data T x = A x | B Boolean
```

`T X` is equivalent to `Either X Boolean`. Following from this: the
relationship of `X` with `T X` is, in some sense, the 'same' as `X` with
`Either X Boolean`.

That is to say; the relationships between types are 'transportable' across type
equivalences.  For example, given a function that works with `T X`, we should
be able to write a function that instead works with `Either X Boolean` by
consistently transforming back and forth along the equivalence.


## Computations and variance

### Terminology

Relative to a given type expression:
* by 'input' I mean "doesn't appear in positive position"
* by 'output' I mean "doesn't appear in negative position"

That is, relative to `(X -> Y)` the `X` is not in positive position and can be
considered an input, and the `Y` is not in negative position and can be
considered an output.  But, relative to `(X -> Y) -> Z`, the `(X -> Y)`
function is in negative position, so `X` (now not in negative position) is
considered an output, and `Y` (now not in positive position) is considered an
input.

Think of every sub-expression being annotated with a `+1` or `-1` relative to
it's immediate parent expression.  Then pick a starting expression and an
ending sub-expression, to calculate if something is in negative position is to
multiply at each level.

### Functor variance

We call type constructors with parameters by different names depending on
whether those parameters are considered input or output.

The one you know is a 'Covariant' functor.  This allows us to post-process an
output parameter.

```haskell
class Functor f where
  fmap :: ∀ a b . (a -> b) -> f a -> f b
```

Examples:

```haskell
data Maybe t = Just t | Nothing
newtype Identity t = Identity t
data Proxy t = Proxy
data Const x y = Const x
(->) X
```

You may also have heard of a 'Contravariant' functor.  This is when the mapping
function allows us to pre-process an input parameter before consuming:

```haskell
class Contravariant f where
  cmap :: ∀ a b . (b -> a) -> f a -> f b
```

Examples:

```haskell
newtype Op c d = Op (d -> c)
newtype Pred t = Pred (t -> Boolean)
data Proxy t = Proxy
data Const x y = Const x
```

Note that `Proxy` and `Const X` appear as examples of both.  This is because
they don't use the type parameter in any data constructor.  A functor that is
both a `Functor` and `Contravariant` is called a 'Bivariant' functor:

```haskell
class (Contravariant f, Functor f) => Bivariant f where
  coerceMap :: ∀ a b . f a -> f b

instance (Contravariant f, Functor f) => Bivariant f where
  coerceMap = fmap absurd . cmap absurd
```

There are also type constructors that use a type parameter in both
positive and negative position.  These are called 'Invariant' functors:

```haskell
class Invariant f where
  invmap :: ∀ a b . (b -> a) -> (a -> b) -> f a -> f b

-- Every covariant functor is invariant
class Invariant f => Functor f where ...
-- satisfying `invmap _ f = fmap f`

-- Every contravariant functor is invariant
class Invariant f => Contravariant f where ...
-- satisfying `invmap g _ = cmap g`
```

Referring to the "'transportable' along equivalences", a 'nice' input to
`invmap` would be an equivalence.  E.g going between `f (Tuple X Y)` and `f
(Tuple Y X)` by swapping.

So,
* 'Covariant' functors want `a -> b`.
* 'Contravariant' functors want `b -> a`.
* 'Invariant' functors want both.
* 'Bivariant' functors want neither.

There is another kind of functor which is trivially satisfied for every (`Type
-> Type`) type constructor.  This is a functor whose input arrow is proof that
the two type arguments are equal.

```haskell
data Equal :: Type -> Type -> Type where
  Refl :: ∀ x . Equal x x

class TypeConstructor f where
  equalMap :: ∀ a b f . Equal a b -> f a -> f b

instance TypeConstructor f where
  equalMap Refl x = x
```

### Computations

Let's talk about types of computation that deal with input of type `A` and
output of type `B`.

```haskell
A -> B
A -> Maybe B
A -> IO B
A -> f B
A -> r
Monoid r => A -> r
∀ p . Profunctor p => p A B
∀ f . Functor f => f A -> f B
```

### All can be generalised to the form:

```haskell
P A B
```

With `P` being:

```haskell
(->)
Star Maybe
Star IO
Star f
Forget r
Forget r -- given (Monoid r)
```

Given:

```haskell
newtype Star f a b = Star (a -> f b)
newtype Forget r a b = Forget (a -> r)
```


## Optics

Optics transport suitable computations along a relationship

```haskell
id : p A B -> p A B
right : Choice p => p A B -> p (Either X A) (Either X B)
second : Strong p => p A B -> p (Tuple X A) (Tuple X B)
```

`Choice p` classifies computations that can be transported to one side of an `Either`

`Strong p` classifies computations that can be transported to one side of a `Tuple`

If you can show how your type is isomorphic to a `Either`, then you can combine
that with `right` to get a `Prism`

If you can show how your type is isomorphic to a `Tuple`, then you can combine
that with `second` to get a `Lens`


## Encoding

```haskell
newtype L a b = L (forall f . f a -> f b)
```

Only possible instance requires `a` and `b` to be the same, because the
implementation can't know anything about `f`.

```haskell
refl :: L a a
refl = L id
```

If we allow `Invariant`:

```haskell
class Invariant f where
  invmap :: (a -> b) -> (b -> a) -> f a -> f b

newtype I a b = I (forall f . Invariant f => f a -> f b)
```

Then with `I a b` we get to talk about bijections between `a` and `b`.

```haskell
iso :: (a -> b) -> (b -> a) -> I a b
iso to fro = I (invmap to fro)
```

If we only allow `Functor`:

```haskell
newtype F a b = F (forall f . Functor f => f a -> f b)
```

Then with `F a b` we only get to talk about functions `a -> b`.

```haskell
mkF :: (a -> b) -> F a b
mkF f = F (map f)
```

To recover, pick `f` to be `a -> _`:

```haskell
unF :: F a b -> (a -> b)
unF (F f) = f id
```

That is:

```haskell
forall f . Functor f => f a -> f b
-- becomes
(a -> a) -> (a -> b)
```


# TODO

∀ f . Functor f => f b -> f t
∀ f . Functor f => ((b ->) ~> f) -> f t
b -> t

type Fn = (->)

data Exchange x y i o = Exchange (Fn i x) (Fn y o)
instance Profunctor (Exchange a b) where
  dimap :: Exchange x y i o -> Exchange a b x y -> Exchange a b i o
  compose :: (xy -> io) -> (ab -> xy) -> (ab -> io)
  dimap (Exchange ix yo) (Exchange xa by) = Exchange (xa . ix) (yo . by)

instance Category (Exchange a b) where
  compose
class Profunctor p where
  dimap :: ∀ x y i o . Exchange x y i o -> p x y -> p i o
∀ p . Profunctor p => p a b -> p s t
∀ p . Profunctor p => (∀ x y . Exchange a b x y -> p x y) -> p s t
doIt :: ∀ s t a b . Exchange a b s t -> (∀ p . Profunctor p => p a b -> p s t)
doIt = dimap
itDo :: ∀ s t a b . (∀ p . Profunctor p => p a b -> p s t) -> Exchange a b s t
itDo f = f 



newtype Star f a b = Star (a -> f b)
-- Monad f => Category (Star f)

-- data Market a b x y =
--   Market (Star (Either y) x a) (b -> y)

data Market a b x y =
  Market (x -> Either y a) (b -> y)


class Profunctor p => Choice p where
  --choice :: ∀ x y i o . Market x y i o -> p x y -> p i o
  right :: ∀ x i o . p i o -> p (Either x i) (Either x o)

instance Choice (Market a b) where
  choice :: Market x y i o -> Market a b x y -> Market a b i o
  choice :: Market xy io -> Market ab xy -> Market ab io
  choice (Market ieox yo) (Market xeya by) = Market ieoa (yo . by)
    where
      ieoa :: i -> Either a o
      ieoa i = ieox i >>= lmap yo . xeya

toChoice :: ∀ x y i o . Market x y i o -> (∀ p . Choice p => p x y -> p i o)
toChoice = choice

marketIdentity :: ∀ x y . Market x y x y
marketIdentity = Market Right id

--fromChoice :: ∀ x y i o . (Market x y x y -> Market x y i o) -> Market x y i o
fromChoice :: ∀ x y i o . (∀ p . Choice p => p x y -> p i o) -> Market x y i o
fromChoice pxypio = pxypio marketIdentity



ex2Mk :: ∀ x y i o . Exchange x y i o -> Market x y i o
ex2Mk (Exchange ix yo) = Market (Right . ix) yo

choiceDimap :: ∀ x y i o r . (Market x y i o -> r) -> (Exchange x y i o -> r)
choiceDimap c = c . ex2Mk



(s -> a, b -> t)
p a b
p s t

class Choice p where
  dimap :: ∀ x y i o . Exchange x y i o -> p x y -> p i o
  right :: ∀ x a b . p a b -> p (Either x a) (Either x b)

∀ p . Choice p => p a b -> p s t
∀ p . Choice p => (Exchange a b ~> p) -> p s t

```haskell
type Equality s t a b = forall p . p a b -> p s t
type Iso s t a b = forall p . Profunctor p => p a b -> p s t
type Lens s t a b = forall p . Strong p => p a b -> p s t
type Prism s t a b = forall p . Choice p => p a b -> p s t
type AffineTraversal s t a b = forall p . (Strong p, Choice p) => p a b -> p s t
```


