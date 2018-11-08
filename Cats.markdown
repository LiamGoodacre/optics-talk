A category C consists of objects & arrows.

Objects are names that represent something.

```haskell
-- X : Object C
-- Y : Object C
-- Z : Object C
```

An arrow represents a connection between two objects.

```haskell
-- f : Arrow C X Y
-- g : Arrow C Y Z
-- h : Arrow C Z X
```

For arrow `f`, `X` is the source/domain object, and `Y` is the target/codomain object.

Notation: when in haskell I will use braces `{` & `}` to encase category theory
expressions.  For example `f :: {Arrow C X Y}` will mean: when we work out what
`Arrow C X Y` is, we can substitute it in.  Suppose we find out that
`{Arrow C X Y}` is the type `X -> Y`, then we will end up with `f :: X -> Y`.

Two arrows with the same source and target aren't necessarily the same arrow.

For each object there is an identity arrow, whose source and target is that
object:

```haskell
-- id @X : Arrow C X X
-- id @Y : Arrow C Y Y
-- id @Z : Arrow C Z Z
```

An arrow whose source and target objects are the same isn't necessarily an
identity arrow.  But an identity arrow must exist.

Any two compatible arrows can be composed:

```haskell
-- f : Arrow C X Y
-- g : Arrow C Y Z
-- g . f : Arrow C X Z
```

Composition is associative:

```haskell
-- h . (g . f) = (h . g) . f
```

Composition with an identity arrow does nothing:

```haskell
-- h . id = h
-- h = id . h
```

Mappings between categories are called functors.

Functors map every object and arrow from one category to another.

To be a functor, this mapping cannot delete or disconnect any arrows or
objects, but it can merge them.

Intuition: a functor is a picture of one category in another.

A hom-set is the 'collection' of arrows from one object to another.

Sometimes this 'collection' is a type.

A category in which every hom-set is a type is called 'locally small'.

There is a category CAT in which objects represent locally small categories and arrows
represent functors.  CAT is not locally small.

Other than CAT we will only really consider locally small categories.

When we write `f : Arrow C X Y`, the `Arrow C X Y` bit is the hom-set.

So we can think of `f` as being a term of type `C X Y`.

```haskell
-- category
-- f : Arrow C X Y

-- haskell
f :: {Arrow C X Y}
```

For any two categories C and D, there is a category C × D.

Objects in C × D represent pairs of objects, one from C, one from D.

```haskell
-- A : Object C
-- B : Object D
-- (A , B) : Object (C × D)
```

Arrows in C × D represent pairs of arrows, one from C, one from D.

```haskell
-- A : Object C
-- B : Object C
-- X : Object D
-- Y : Object D
-- (A , X) : Object (C × D)
-- (B , Y) : Object (C × D)
-- f : Arrow C A B
-- g : Arrow D X Y
-- (f , g) : Arrow (C × D) (A , X) (B , Y)
```

There is a category TYPE whose objects represent types and arrows represent functions.

The hom-sets of every locally small category are represented by objects in TYPE.

```haskell
-- X : Object C
-- Y : Object C
-- Z : Object C

-- f : Arrow C X Y
-- g : Arrow C Y Z
-- g . f : Arrow C X Z
f :: {Arrow C X Y}
g :: {Arrow C Y Z}
g . f :: C X Z

-- Arrow C X Y : Object TYPE
{Arrow C X Y} :: Type

-- Arrow C Y Z : Object TYPE
{Arrow C Y Z} :: Type
```

In a locally small category, because hom-sets are types, it means that arrow
composition `(.)` is a function.

```haskell
(.) :: {Arrow C Y Z} -> {Arrow C X Y} -> {Arrow C X Z}
```

Unsaturated composition `(.)` is itself an arrow in TYPE.

```haskell
-- (.) : Arrow TYPE (C Y Z) (C X Y -> C X Z)
```

Hom-set 'constructor' `Arrow C X` is a functor from C to TYPE:

```haskell
-- X : Object C
-- Y : Object C

-- C : Object CAT
-- TYPE : Object CAT

-- Arrow C X Y : Object TYPE
{Arrow C X Y} :: Type

-- Recall that for every functor between locally
-- small categories there exists an arrow in CAT.

-- If we chop off the Y from the arrow above we
-- get a functor from C to TYPE
-- Arrow C X : Arrow CAT C TYPE
-- Which is therefore an arrow in CAT

-- can't write in haskell until
-- we know what category C is
```

If we pick category C to be TYPE.

```haskell
-- X : Object TYPE
-- Y : Object TYPE
X :: Type
Y :: Type

-- Arrow TYPE X Y : Object TYPE
{Arrow TYPE X Y} :: Type
{Arrow TYPE X Y} = X -> Y

-- f : Arrow TYPE X Y
f :: X -> Y

{Arrow CAT TYPE TYPE} :: Kind
{Arrow CAT TYPE TYPE} = Type -> Typ

-- Arrow TYPE X _ : Arrow CAT TYPE TYPE
{Arrow TYPE X _} :: Type -> Type
{Arrow TYPE X _} = (->) X

-- TODO: fmap

```

If we pick category C to be TYPE × TYPE.

```haskell
-- (A , B) : Object (TYPE × TYPE)
-- (X , Y) : Object (TYPE × TYPE)
A :: Type
B :: Type
X :: Type
Y :: Type
-- note that `(A, B) :: Type` is not relevant here

-- Arrow TYPE (A , B) (X , Y) : Object TYPE
A -> X :: Type
B -> Y :: Type

data TxT a b x y = TxTComma (a -> x) (b -> y)

{Arrow (TYPE × TYPE) (A , B) (X , Y)} :: Type
{Arrow (TYPE × TYPE) (A , B) (X , Y)}
  = TxT A B X Y

-- (f , g) :: Arrow (TYPE × TYPE) (A , B) (X , Y)
f :: A -> X
g :: B -> Y
TxTComma f g :: TxT (->) (->) A B X Y

{Arrow CAT (TYPE × TYPE) TYPE}
  = Type -> Type -> Type

-- Arrow (TYPE × TYPE) (A , B) _ : Arrow CAT (TYPE × TYPE) TYPE
{Arrow (TYPE × TYPE) (A , B) _} :: Type -> Type -> Type
{Arrow (TYPE × TYPE) (A , B) _} = TxT A B

-- TODO: bimap
```

