---
title: cats
author: Liam Goodacre
patat:
  wrap: true
  slideLevel: 2
  theme:
    codeBlock: [bold, onDullBlack]
  margins:
    left: 3
    right: 3
...

# Category Theory & Haskell

## Notation in this talk

When in Haskell I will use comment braces `{- -}` to encase category theory expressions.

For example, the following will mean that when we work out what `{- E -}` is, we can substitute it in.

```haskell
f ∷ {- E -}
```

Suppose we find out that `{- E -}` is the *type* `X → Y`, then we will end up with:

```haskell
f ∷ X → Y
```

## Category

A *category* `C` consists of:

1. *objects* - names that represent "something".
    ```haskell
    {- X : Object C
       Y : Object C -}
    ```

1. *arrows* - a directed relationship between two *objects*.
    ```haskell
    {- f : X -C-> Y -}
    ```

1. *laws* - properties that must be true regarding all *objects* and *arrows* in the *category*.

## Arrows

An *arrow* represents a connection between two *objects*.

Notationally, when `f` is a *arrow* in *category* `C` from `X` to `Y`, we will write.

```haskell
{- f : X -C-> Y -}
```

For *arrow* `f`:

* `X` is the source/domain *object*
* `Y` is the target/codomain *object*

Two *arrows* with the same source and target *object* aren't necessarily the same *arrow*.

But when all pairs of *arrows* like this are necessarily the same, the *category* is described as 'thin'.

## Identity

For each *object* there is an identity *arrow*, whose source and target is that *object*:

```haskell
{- id X : X -C-> X
   id Y : Y -C-> Y
   ... -}
```

An *arrow* whose source and target *objects* are the same isn't necessarily an identity *arrow*.

But an identity *arrow* must exist for each *object*.

## Composition

Any two compatible *arrows* can be composed:

```haskell
{- f : X -C-> Y
   g : Y -C-> Z
   g ∘ f : X -C-> Z -}
```

As `Y` is both the source of `g` and the target of `f`, we compose them to get `g ∘ f`.

The following properties hold:

- Associativity: `h ∘ (g ∘ f)` ⇔ `(h ∘ g) ∘ f`
- Left identity: `id C ∘ h` ⇔ `h`
- Right identity: `h` ⇔ `h ∘ id C`

Where ⇔ denotes some appropriate kind of equivalence.

## Hom - Definition

A *hom* is the 'collection' of *arrows* from one *object* to another.

When we write `f : X -C-> Y`, the `X -C-> Y` bit is the *hom*.

Sometimes this 'collection' is a proper *type*.

```haskell
{- X -C-> Y -} ∷ Type
```

A *category* in which every *hom* is a proper *type* is called 'locally small'.

When the *hom* are *types*, it means that *arrow* composition can be written as a function.

## Hom - Continued

We will only really consider *categories* whose *hom* are *types*.  (The 'locally small' *categories*)

So, for example, we can have:

```haskell
f ∷ {- X -C-> Y -}
```

That is, `f` is a *term* of *type* `{- X -C-> Y- }` (what ever that *type* may be).

To know what the *type* `{- X -C-> Y -}` actually is, we will need to know what *category* `C` is.

## Category TYPE - Types and Functions

There is a *category* `TYPE` whose *objects* represent proper *types* and *arrows* represent functions (and have function *types*).

Here we pun the name of an *object* to be the same as the name of the *type* that it represents.  So there is an *object* `Int` that represents the *type* `Int`:

```haskell
{- Int : Object TYPE -}
   Int ∷ Type

{- String : Object TYPE -}
   String ∷ Type

{- Int -TYPE-> String -}
   Int → String ∷ Type

{- show : Int -TYPE-> String -}
   show ∷ Int → String
```

Not all examples will be a mapping as straight forward as this.  Importantly, not all *objects* are proper *types*.

## Category of pairs - Objects

For any two *categories* `C` and `D`, there is a *category* `C × D`.

An *object* in `C × D` represents one *object* from `C` and one *object* from `D`.  Written using the notation `(A , B)`.

```haskell
{- A : Object C
   B : Object D
   (A , B) : Object (C × D) -}
```

__Note__: This does not necessarily mean that the Haskell representation of `(A , B)` is a tuple, a tuple-type, or even a proper type at all!

## Category of pairs - Arrows

Just like with the *objects*, an *arrow* in `C × D` represents one *arrow* from `C` and one *arrow* from `D`.

The notation for writing an *arrow* is (possibly confusingly) the same as with *objects*: `(f , g)` - except that `f` and `g` are *arrows* not *objects*.

```haskell
{- f : A -C-> B
   g : X -D-> Y
   (f , g) : (A , X) -(C × D)-> (B , Y) -}
```

Assuming the following *objects* exist:

```haskell
{- A : Object C
   B : Object C
   X : Object D
   Y : Object D
   (A , X) : Object (C × D)
   (B , Y) : Object (C × D) -}
```

## TYPE × TYPE

If we pair up `TYPE` with itself, we get the category `TYPE × TYPE` (`T×T` for short).

An *object* represents two *types*.

__!__ not necessarily a tuple of types or a tuple-type __!__

An *arrow* represents two functions.

```haskell
{- show : Int -TYPE-> String -}
show ∷ Int → String

{- isZero : Int -TYPE-> Boolean -}
isZero ∷ Int → Boolean

{- (show , isZero) :
     (Int , Int) -T×T-> (String, Boolean) -}
```

## TYPE × TYPE - Arrows

Recall that *arrows* in a locally small *category* can be represented by a *type*.  In `TYPE × TYPE` this could look something like the following:

```haskell
{- (a , b) -T×T-> (s , t) -}
data Arrow a b s t = Comma (a → s) (b → t)
```

Here, an *object* `(a , b)` is represented by two *type* parameters to the `Arrow` *type* constructor.

```haskell
{- (show , isZero) :
     (Int , Int) -T×T-> (String , Boolean) -}

Comma show isZero ∷
  Arrow Int Int String Boolean
```

## TYPE × TYPE - Composition

```haskell
{- (a , b) -T×T-> (s , t) -}
data Arrow a b s t = Comma (a → s) (b → t)
```

If this *type* is sufficient to represent *arrows* in `TYPE × TYPE`, then it must support an associative composition with identities.  Indeed it does:

```haskell
compose ∷
  Arrow x y i o →
  Arrow a b x y →
  Arrow a b i o
compose (Comma xi yo) (Comma ax by) =
  Comma (xi . ax) (yo . by)

identity ∷ Arrow x y x y
identity = Comma identity identity
```

## Functors

Mappings between *categories* are called *functors*.

Intuition: a *functor* is a picture of one *category* in another.

*Functors* map every *object* and *arrow* from one *category* to another.

So with an *object* `X`, we may refer to the *object* that a *functor* `F` maps `X` to as `F X`.

Similarly with an *arrow* `f`, we may refer to the *arrow* mapped to as `F f`.

To be a *functor*, this mapping cannot delete or disconnect any *arrows* or *objects*, but it can merge them.

## Functors - 2 and TYPE

Consider a *category* `2` with only two *objects* (`fst` and `snd`) and only identity *arrows*.

Any *functor* `F` from `2` to `TYPE`:

Maps `fst : Object 2` to a *type* `F fst : Object TYPE`.

Maps from the *arrow* ```id fst``` to ```F (id fst)``` which is ```id (F fst) : F fst -TYPE-> F fst```.  This a function:

```haskell
id ∷ {- F fst -} → {- F fst -}
```

And similarly for `snd`.

## Functors - 2 and TYPE (Continued)

`F` is like a 'picture' of `2` in `TYPE`.  I.e. it is a selection of two *types* and their identity *functions*.

Suppose `F fst` is `Int` and `F snd` is `String`.

Notice how similar this is to an *object* in `TYPE × TYPE`.

It's not only similar, a *functor* from `2` to `TYPE` is equivalent to the *category* `TYPE × TYPE`.

# TODO

The *hom* 'constructor' `Arrow C X` is a *functor* from `C` to `TYPE`:

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
```

If we pick *category* `C` to be `TYPE`.

```haskell
-- X : Object TYPE
-- Y : Object TYPE
X :: Type
Y :: Type

-- Arrows in TYPE are functions
-- The hom is therefore a function type
-- Arrow TYPE X Y : Object TYPE
{Arrow TYPE X Y} :: Type
{Arrow TYPE X Y} = X -> Y

-- f : Arrow TYPE X Y
f :: X -> Y

{Arrow CAT TYPE TYPE} :: Kind
{Arrow CAT TYPE TYPE} = Type -> Type

-- chopping off the last argument gives us
-- a functor from TYPE to TYPE
-- Arrow TYPE X _ : Arrow CAT TYPE TYPE
{Arrow TYPE X _} :: Type -> Type
{Arrow TYPE X _} = (->) X

-- TODO: fmap
```

If we pick *category* `C` to be `TYPE × TYPE`.

```haskell
-- (A , B) : Object (TYPE × TYPE)
-- (X , Y) : Object (TYPE × TYPE)
A :: Type
B :: Type
X :: Type
Y :: Type

-- Arrow TYPE (A , B) (X , Y) : Object TYPE
A -> X :: Type
B -> Y :: Type

data TxT a b x y = TxTComma (a -> x) (b -> y)

{Arrow (TYPE × TYPE) (A , B) (X , Y)} :: Type
{Arrow (TYPE × TYPE) (A , B) (X , Y)}
  = TxT A B X Y

-- (f , g) : Arrow (TYPE × TYPE) (A , B) (X , Y)
f :: A -> X
g :: B -> Y
{(f , g)} = TxTComma f g :: TxT A B X Y

{Arrow CAT (TYPE × TYPE) TYPE} :: Kind
{Arrow CAT (TYPE × TYPE) TYPE}
  = Type -> Type -> Type

-- Arrow (TYPE × TYPE) (A , B) _ : Arrow CAT (TYPE × TYPE) TYPE
{Arrow (TYPE × TYPE) (A , B) _} :: Type -> Type -> Type
{Arrow (TYPE × TYPE) (A , B) _} = TxT A B

-- TODO: bimap
```

There is a *category* `CAT` in which *objects* represent locally small categories and *arrows* represent *functors*.  `CAT` itself is not locally small.

Other than `CAT` we will only really consider locally small *categories*.

```haskell
data Nat = S Nat | Z
data Nat (n ∷ Nat) = Nat

data (≤) ∷ Nat → Nat → Type where
  ZZ ∷ Z ≤ Z
  SZ ∷ l ≤ r → l ≤ S r
  SS ∷ l ≤ r → S l ≤ S r

identity ∷ (n ∷ Nat) → n ≤ n
identity Z = ZZ
identity S k = SS (identity k)

compose ∷
  (n, m, o ∷ Nat) →
  m ≤ o →
  n ≤ m →
  n ≤ o
compose n m o l r = ?what
```
