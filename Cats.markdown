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

Two arrows with the same source and target aren't necessarily the same arrow.

When all arrows are unique, the category is described as 'thin'.

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

Some hom-sets are types/small-sets.

A category in which every hom-set is a type/set is called 'locally small'.

There is a category CAT in which objects are locally small categories and objects
are functors.  CAT is not locally small.

Other than CAT we will only really consider locally small categories.

When we write `f : Arrow C X Y`, the `Arrow C X Y` bit is the hom-set.

So we can think of `f` as being a term of type `C X Y`.

```
-- category
-- f : Arrow C X Y

-- haskell
f :: C X Y
```

There is a category TYPE whose objects are types and arrows are functions.

The hom-sets of every locally small category are objects in TYPE.

Unsaturated arrow composition `(.)` of a locally small category is itself an
arrow in TYPE.

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

-- (.) : Arrow TYPE (C Y Z) (C X Y -> C X Z)
(.) :: C Y Z -> C X Y -> C X Z
```

Partially applying the hom-set `Arrow C` with a single argument is a functor in
the other.

```
-- X : Object C
-- Y : Object C
-- C : Object CAT
-- TYPE : Object CAT
-- Arrow C X Y : Object TYPE
C X Y :: Type

-- A functor from C to TYPE
-- Arrow C X _ : Arrow CAT C TYPE
C X :: C -> Type
```

