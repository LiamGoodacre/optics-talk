A category C consists of objects & arrows.

Objects are names that represent something.

```
-- X : Object C
-- Y : Object C
-- Z : Object C
```

An arrow represents a connection between two objects.

```
-- f : Arrow C X Y
-- g : Arrow C Y Z
-- h : Arrow C Z X
```

For arrow `f`, `X` is the source/domain object, and `Y` is the target/codomain object.

Two arrows with the same source and target aren't necessarily the same arrow.

For each object there is an identity arrow, whose source and target is that
object:

```
-- id @X : Arrow C X X
-- id @Y : Arrow C Y Y
-- id @Z : Arrow C Z Z
```

An arrow whose source and target objects are the same isn't necessarily an
identity arrow.  But an identity arrow must exist.

Any two compatible arrows can be composed:

```
-- f : Arrow C X Y
-- g : Arrow C Y Z
-- g . f : Arrow C X Z
```

Composition is associative:

```
-- h . (g . f) = (h . g) . f
```

Composition with an identity arrow does nothing:

```
-- h . id = h
-- h = id . h
```

Mappings between categories are called functors.

Functors map every object and arrow from one category to another.

To be a functor, this mapping cannot delete or disconnect any arrows or
objects, but it can merge them.

Intuition: a functor is a picture of one category in another.

A hom-set is the collection of arrows from one object to another.

Some hom-sets represent types/small-sets.

A category in which every hom-set is a type/set is called 'locally small'.

There is a category CAT in which objects represent locally small categories and arrows
represent functors.  CAT is not locally small.

Other than CAT we will only really consider locally small categories.

When we write `f : Arrow C X Y`, the `Arrow C X Y` bit is the hom-set.

So we can think of `f` as being a term of type `C X Y`.

```
-- category
-- f : Arrow C X Y

-- haskell
f :: C X Y
```

For any two categories C and D, there is a category C × D.

Objects in C × D represent pairs of objects, one from C, one from D.

```
-- A : Object C
-- B : Object D
-- (A , B) : Object (C × D)
```

Arrows in C × D represent pairs of arrows, one from C, one from D.

```
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

```
-- X : Object C
-- Y : Object C
-- Z : Object C

-- f : Arrow C X Y
-- g : Arrow C Y Z
-- g . f : Arrow C X Z
f :: C X Y
g :: C Y Z
g . f :: C X Z

-- Arrow C X Y : Object TYPE
C X Y :: Type

-- Arrow C Y Z : Object TYPE
C Y Z :: Type
```

Unsaturated arrow composition `(.)` of a locally small category is itself an
arrow in TYPE.

```
-- (.) : Arrow TYPE (C Y Z) (C X Y -> C X Z)
(.) :: C Y Z -> C X Y -> C X Z
```

Hom-set 'constructor' `Arrow C X` is a functor from C to TYPE:

```
-- X : Object C
-- Y : Object C
-- C : Object CAT
-- TYPE : Object CAT
-- Arrow C X Y : Object TYPE
C X Y :: Type

-- A functor from C to TYPE
-- Arrow C X _ : Arrow CAT C TYPE

-- can't write in haskell until
-- we know what category C is
```

If we pick category C to be TYPE.

```
-- X : Object TYPE
-- Y : Object TYPE
X :: Type
Y :: Type

-- Arrow TYPE X Y : Object TYPE
X -> Y :: Type

-- f : Arrow TYPE X Y
f :: X -> Y

-- Arrow CAT TYPE TYPE
Type -> Type :: Kind

-- Arrow C X _ : Arrow CAT TYPE TYPE
(->) X :: Type -> Type

-- TODO: fmap

```

If we pick category C to be TYPE × TYPE.

```
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
data Cross c d a b x y = Comma (c a x) (d b y)
Cross (->) (->) A B X Y :: Type

-- (f , g) :: Arrow (TYPE × TYPE) (A , B) (X , Y)
f :: A -> X
g :: B -> Y
Comma f g :: Cross (->) (->) A B X Y

-- Arrow CAT (TYPE × TYPE) TYPE
Type -> Type -> Type :: Kind

-- Arrow (TYPE × TYPE) (A , B) _ : Arrow CAT (TYPE × TYPE) TYPE
(Cross (->) (->)) A B :: Type -> Type -> Type

-- TODO: bimap
```

