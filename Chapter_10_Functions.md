# Chapter 10 — Functions

Source chapter: https://hrmacbeth.github.io/math2001/08_Functions.html

This chapter records the mathematics of the function examples from Math2001
Chapter 8. The goal here is only to write the mathematical content cleanly. Litex
examples and any extra implementation commentary can be added later.

Functions bring three recurring proof patterns.

First, a function is **injective** if equal outputs force equal inputs. To prove
injectivity, start with `f(x1) = f(x2)` and derive `x1 = x2`. To disprove
injectivity, find two different inputs with the same output.

Second, a function is **surjective** if every target value is hit. To prove
surjectivity, take an arbitrary output value `y` and build an input `x` with
`f(x) = y`. To disprove surjectivity, find one target value which no input can
hit.

Third, a function is **bijective** if it is both injective and surjective. Often
the most efficient way to prove bijectivity is to produce an inverse function
and check both compositions.

## 10.1 Injectivity And Surjectivity

### 10.1.1 Functions, Domains, And Codomains

A function has a domain, where its inputs live, and a codomain, where its outputs
live. For example, the Fibonacci sequence can be viewed as a function from
natural numbers to integers: it takes an index `n` and returns the `n`th integer
in the sequence.

A function can also be defined by a formula. If `q(x) = x + 3`, then `q` is a
function from real numbers to real numbers. The input is a real number `x`, and
the output is the real number `x + 3`.

When a function is only needed once, it is often written anonymously, such as
`x |-> x^2`. Mathematically this still has a domain and codomain, for example
from `R` to `R`.

### 10.1.2 Injective Functions

A function `f : X -> Y` is injective when

```text
f(x1) = f(x2)  implies  x1 = x2.
```

The important point is that the equality starts in the codomain and must be
pulled back to equality in the domain.

### 10.1.3 Example: `q(x) = x + 3` Is Injective

Let `q : R -> R` be defined by `q(x) = x + 3`. Suppose `q(x1) = q(x2)`.
Then

```text
x1 + 3 = x2 + 3.
```

Subtracting `3` from both sides gives `x1 = x2`. Therefore `q` is injective.

The mathematical reason is that adding a fixed number is reversible. Equal
outputs differ from the inputs by the same shift, so the inputs were equal.

### 10.1.4 Example: `x |-> x^2` On `R` Is Not Injective

To disprove injectivity, find two different inputs with the same output.
For the square function on real numbers, the witnesses are `-1` and `1`:

```text
(-1)^2 = 1^2,
```

but `-1 != 1`. Therefore the square function from `R` to `R` is not injective.

This is the standard counterexample pattern: one collision in the output is
enough to refute injectivity.

### 10.1.5 Surjective Functions

A function `f : X -> Y` is surjective when every `y` in `Y` is hit by some input:

```text
for every y in Y, there exists x in X such that f(x) = y.
```

A surjectivity proof is usually a witness construction. Given the target output
`y`, solve the equation `f(x) = y` for `x`.

### 10.1.6 Example: `s(a) = 3a + 2` Is Surjective On `Q`

Let `s : Q -> Q` be defined by `s(a) = 3a + 2`. Given a rational number `y`,
choose

```text
a = (y - 2) / 3.
```

Then

```text
s((y - 2) / 3)
  = 3 * ((y - 2) / 3) + 2
  = y.
```

Since every rational `y` has a rational preimage, `s` is surjective.

### 10.1.7 Example: `x |-> x^2` On `R` Is Not Surjective

To disprove surjectivity, find one output value which is not hit. For the square
function from `R` to `R`, the value `-1` is not hit.

For every real number `x`, we have

```text
0 <= x^2.
```

So `x^2` can never equal `-1`. Therefore the square function is not surjective
as a function from `R` to `R`.

### 10.1.8 Example: A Finite Function Which Is Not Injective

Consider a finite set with three elements:

```text
Musketeer = {athos, porthos, aramis}.
```

Define a function `f : Musketeer -> Musketeer` by

```text
f(athos) = aramis,
f(porthos) = aramis,
f(aramis) = athos.
```

This function is not injective because `athos` and `porthos` are different
inputs but have the same output:

```text
f(athos) = aramis = f(porthos).
```

Finite functions make injectivity especially concrete: inspect the arrows and
look for two arrows landing at the same output.

### 10.1.9 Example: The Same Finite Function Is Not Surjective

The same function `f` is not surjective. The element `porthos` is never hit:

```text
f(athos) = aramis,
f(porthos) = aramis,
f(aramis) = athos.
```

The outputs are only `aramis` and `athos`. Since no input maps to `porthos`, the
function is not surjective.

### 10.1.10 Example: A Finite Function Which Is Injective

Define `g : Musketeer -> Musketeer` by

```text
g(athos) = porthos,
g(porthos) = aramis,
g(aramis) = athos.
```

Every output appears exactly once. Therefore if `g(x1) = g(x2)`, the two inputs
must be the same. This proves that `g` is injective.

On a small finite set, injectivity can be proved by checking the finite table:
no two different inputs share an output.

### 10.1.11 Example: The Same Finite Function Is Surjective

The same function `g` is also surjective. Each target has a preimage:

```text
porthos = g(athos),
aramis = g(porthos),
athos = g(aramis).
```

Thus every element of `Musketeer` is hit.

### 10.1.12 Example: `x |-> x^3` On `R` Is Injective

Suppose `x1^3 = x2^3`. Then

```text
(x1 - x2)(x1^2 + x1*x2 + x2^2) = x1^3 - x2^3 = 0.
```

So either `x1 - x2 = 0`, in which case `x1 = x2`, or

```text
x1^2 + x1*x2 + x2^2 = 0.
```

The second case is impossible unless both variables are forced into the same
degenerate situation. One way to see the contradiction is to split on whether
`x1 = 0`.

If `x1 = 0`, then `x2^3 = x1^3 = 0`, so `x2 = 0` as well, hence `x1 = x2`.

If `x1 != 0`, then the expression

```text
x1^2 + ((x1 + x2)^2 + x2^2)
```

is strictly positive, but it is also equal to

```text
2(x1^2 + x1*x2 + x2^2),
```

which is `0` in the second case. That is impossible. Therefore only the first
factor can vanish, and `x1 = x2`. Thus the cube function is injective.

## 10.2 Bijectivity

### 10.2.1 Bijective Functions

A function is bijective when it is both injective and surjective. This means it
has no collisions and misses no target values.

### 10.2.2 Example: `p(x) = 2x - 5` Is Bijective

Let `p : R -> R` be defined by `p(x) = 2x - 5`.

For injectivity, suppose `p(x1) = p(x2)`. Then

```text
2x1 - 5 = 2x2 - 5.
```

Adding `5` and dividing by `2` gives `x1 = x2`.

For surjectivity, given any real number `y`, choose

```text
x = (y + 5) / 2.
```

Then

```text
p((y + 5) / 2) = 2 * ((y + 5) / 2) - 5 = y.
```

So `p` is both injective and surjective, hence bijective.

### 10.2.3 Example: `a(t) = t^3 - t` Is Not Bijective

Let `a : R -> R` be defined by `a(t) = t^3 - t`. This function is not
injective, because

```text
a(0) = 0^3 - 0 = 0,
a(1) = 1^3 - 1 = 0,
```

but `0 != 1`. Since bijective implies injective, the function is not bijective.

### 10.2.4 Example: A Finite Function Which Is Not Bijective

Let

```text
Celestial = {sun, moon}
Subatomic = {proton, neutron, electron}.
```

Define `f : Celestial -> Subatomic` by

```text
f(sun) = proton,
f(moon) = electron.
```

This function is not surjective because `neutron` is not hit. Therefore it is
not bijective.

This also illustrates a counting obstruction: a function from a two-element set
to a three-element set cannot hit all three target values.

### 10.2.5 Example: Bijective Means Unique Preimages

A function `f : X -> Y` is bijective if and only if every `y` in `Y` has a
unique preimage in `X`.

If `f` is bijective, surjectivity gives at least one `x` with `f(x) = y`.
Injectivity gives uniqueness: if `f(x') = y = f(x)`, then `f(x') = f(x)`, so
`x' = x`.

Conversely, suppose every `y` has a unique preimage. Surjectivity is immediate:
each `y` has some preimage. For injectivity, assume `f(x1) = f(x2)`. Apply the
unique-preimage property to the target value `f(x1)`. Both `x1` and `x2` are
preimages of this same target, so uniqueness gives `x1 = x2`.

### 10.2.6 Example: Injective Implies Bijective On A Two-Element Set

For functions from the two-element set `Celestial` to itself, injectivity already
forces bijectivity.

There are only two possible target values. If an injective function sends `sun`
and `moon` to distinct outputs, then the two outputs must be exactly `sun` and
`moon` in some order. Thus every target value is hit, so the function is
surjective. Since injectivity was assumed, the function is bijective.

The proof is a finite case analysis over the possible values of `f(sun)` and
`f(moon)`.

### 10.2.7 Example: Injective Does Not Always Imply Bijective

The statement "injective implies bijective" fails for functions from `N` to `N`.
The counterexample is

```text
f(n) = n + 1.
```

This function is injective: if `n1 + 1 = n2 + 1`, then `n1 = n2`.

But it is not surjective, because `0` is never hit. For every natural number
`n`, `n + 1 > 0`. So there is no `n` with `f(n) = 0`. Therefore `f` is injective
but not bijective.

## 10.3 Composition And Inverses

### 10.3.1 Composition

If `f : X -> Y` and `g : Y -> Z`, then the composite `g o f : X -> Z` sends
`x` to `g(f(x))`.

### 10.3.2 Example: A Simple Composite

Let `f : R -> R` be defined by `f(a) = a + 3`, let `g : R -> R` be defined by
`g(b) = 2b`, and let `h : R -> R` be defined by `h(c) = 2c + 6`.

For every real number `x`,

```text
(g o f)(x)
  = g(f(x))
  = 2(x + 3)
  = 2x + 6
  = h(x).
```

Since the two functions agree on every input, `g o f = h`.

### 10.3.3 Identity Function

The identity function on `X` sends each `x` in `X` to itself. It is usually
written `Id_X`.

### 10.3.4 Example: A Function Which Is Its Own Inverse

Let `s : R -> R` be defined by `s(x) = 5 - x`. Then for every real number `x`,

```text
(s o s)(x) = s(5 - x) = 5 - (5 - x) = x.
```

Thus `s o s = Id_R`. The function is an involution: applying it twice gives the
identity.

### 10.3.5 Inverse Functions

A function `g : Y -> X` is an inverse of `f : X -> Y` if both compositions are
identity functions:

```text
g o f = Id_X,
f o g = Id_Y.
```

The first equation says that starting in `X`, applying `f`, then applying `g`
returns the original input. The second says the same for starting in `Y`.

### 10.3.6 Example: An Inverse On A Finite Set

Let

```text
Humour = {melancholic, choleric, phlegmatic, sanguine}.
```

Define `p : Humour -> Humour` by

```text
p(melancholic) = choleric,
p(choleric) = sanguine,
p(phlegmatic) = phlegmatic,
p(sanguine) = melancholic.
```

An inverse `q` must reverse each arrow:

```text
q(melancholic) = sanguine,
q(choleric) = melancholic,
q(phlegmatic) = phlegmatic,
q(sanguine) = choleric.
```

Checking `q o p = Id` and `p o q = Id` is a finite case check over the four
elements of `Humour`.

### 10.3.7 Example: A Bijective Function Has An Inverse

Let `f : X -> Y` be bijective. We construct an inverse `g : Y -> X`.

For each `y` in `Y`, surjectivity gives at least one `x` in `X` such that
`f(x) = y`. Define `g(y)` to be that `x`. Then

```text
f(g(y)) = y
```

for every `y`, so `f o g = Id_Y`.

To prove the other composition, take `x` in `X`. Since `f(g(f(x))) = f(x)`, and
`f` is injective, we get

```text
g(f(x)) = x.
```

Thus `g o f = Id_X`, so `g` is an inverse of `f`.

### 10.3.8 Example: A Function With An Inverse Is Bijective

Suppose `g : Y -> X` is an inverse of `f : X -> Y`. That means

```text
g o f = Id_X,
f o g = Id_Y.
```

To prove injectivity, suppose `f(x1) = f(x2)`. Then

```text
x1 = Id_X(x1)
   = (g o f)(x1)
   = g(f(x1))
   = g(f(x2))
   = (g o f)(x2)
   = Id_X(x2)
   = x2.
```

To prove surjectivity, take `y` in `Y`. The input `g(y)` maps to `y`, because

```text
f(g(y)) = (f o g)(y) = Id_Y(y) = y.
```

Therefore `f` is bijective.

### 10.3.9 Example: Bijective If And Only If It Has An Inverse

The previous two examples combine into the fundamental equivalence:

```text
f is bijective  if and only if  f has an inverse.
```

One direction constructs the inverse from bijectivity. The other direction uses
the inverse equations to prove injectivity and surjectivity.

## 10.4 Product Types

Product types are ordered-pair types. Equality of ordered pairs is coordinatewise:

```text
(a, b) = (c, d)  if and only if  a = c and b = d.
```

This is why function proofs on products often split a pair equality into
coordinate equations.

### 10.4.1 Example: A Function From `Z` To `Z^2`

Define `q : Z -> Z^2` by

```text
q(m) = (m + 1, 2 - m).
```

This function is injective. If `q(m1) = q(m2)`, then

```text
(m1 + 1, 2 - m1) = (m2 + 1, 2 - m2).
```

Coordinate equality gives

```text
m1 + 1 = m2 + 1,
2 - m1 = 2 - m2.
```

Either equation already gives `m1 = m2`.

The function is not surjective. The target pair `(0, 1)` is not hit. If
`q(m) = (0, 1)`, then

```text
m + 1 = 0,
2 - m = 1.
```

Adding these equations in the combination `(m + 1) + (2 - m) - 2` gives

```text
1 = -1,
```

which is impossible. Therefore no integer `m` maps to `(0, 1)`.

### 10.4.2 Example: A Bijective Linear Map On `Z^2`

Consider the function

```text
(m, n) |-> (m + n, m + 2n)
```

from `Z^2` to `Z^2`.

To find its inverse, solve

```text
a = m + n,
b = m + 2n.
```

Subtracting gives `b - a = n`. Then

```text
m = a - n = a - (b - a) = 2a - b.
```

So the inverse candidate is

```text
(a, b) |-> (2a - b, b - a).
```

Checking both compositions gives

```text
(2(m+n) - (m+2n), (m+2n) - (m+n)) = (m, n),
```

and

```text
((2a-b) + (b-a), (2a-b) + 2(b-a)) = (a, b).
```

Therefore the original function is bijective.

### 10.4.3 Example: Same Formula Over `R^2` And `Z^2`

The function

```text
(m, n) |-> (m + n, m - n)
```

from `R^2` to `R^2` is bijective. Solving

```text
a = m + n,
b = m - n
```

gives

```text
m = (a + b) / 2,
n = (a - b) / 2.
```

This inverse is valid over `R`.

Over `Z^2`, however, the same formula is not always integer-valued. In fact the
map from `Z^2` to `Z^2` is not surjective. The pair `(0, 1)` is not hit. If

```text
m + n = 0,
m - n = 1,
```

then adding gives

```text
2m = 1,
```

which is impossible for integers. Equivalently, modulo `2`, this would say
`0 = 1`.

### 10.4.4 Example: An Injective Map From `R^2` To `R^3`

Consider

```text
(x, y) |-> (x + y, x - y, y).
```

Suppose two inputs have the same output:

```text
(x1 + y1, x1 - y1, y1) = (x2 + y2, x2 - y2, y2).
```

Coordinate equality gives

```text
x1 + y1 = x2 + y2,
x1 - y1 = x2 - y2,
y1 = y2.
```

Using `y1 = y2` in the first equation gives `x1 = x2`. Therefore
`(x1, y1) = (x2, y2)`, so the function is injective.

### 10.4.5 Example: Addition From `R^2` To `R`

The function

```text
(x, y) |-> x + y
```

from `R^2` to `R` is not injective but is surjective.

It is not injective because

```text
(0, 0) != (1, -1),
```

but

```text
0 + 0 = 1 + (-1) = 0.
```

It is surjective because for any real number `a`, the input `(a, 0)` maps to
`a`:

```text
a + 0 = a.
```

### 10.4.6 Example: `5m + 8n` From `Z^2` To `Z`

The function

```text
(m, n) |-> 5m + 8n
```

from `Z^2` to `Z` is not injective but is surjective.

It is not injective because

```text
5*0 + 8*0 = 5*8 + 8*(-5),
```

but `(0, 0) != (8, -5)`.

It is surjective because `5` and `8` are coprime. Explicitly, for any integer
`a`,

```text
5(-3a) + 8(2a) = a.
```

So the input `(-3a, 2a)` maps to `a`.

### 10.4.7 Example: `5m + 10n` From `Z^2` To `Z`

The function

```text
(m, n) |-> 5m + 10n
```

from `Z^2` to `Z` is not injective and not surjective.

It is not surjective because every value has the form

```text
5m + 10n = 5(m + 2n),
```

so every output is divisible by `5`. The integer `1` is not divisible by `5`,
so it is not hit.

It is also not injective: for example, changing `(m, n)` by `(2, -1)` does not
change the value, because

```text
5(m + 2) + 10(n - 1) = 5m + 10n.
```

### 10.4.8 Example: Swapping Coordinates

Define `g : R^2 -> R^2` by

```text
g(x, y) = (y, x).
```

Then `g` is its own inverse. For every `(x, y)`,

```text
g(g(x, y)) = g(y, x) = (x, y).
```

Thus `g o g = Id`.

### 10.4.9 Example: A Bijection From `N^2` To `N`

There exists a bijection from pairs of natural numbers to natural numbers. One
standard construction lists pairs by diagonals:

```text
(0,0),
(1,0), (0,1),
(2,0), (1,1), (0,2),
...
```

Let `A_n = 0 + 1 + ... + n`, the triangular-number sequence. Define

```text
p(a, b) = A_(a+b) + b.
```

The value `a + b` chooses the diagonal, and the additional `+ b` chooses the
position along that diagonal.

Injectivity comes from the fact that the triangular-number blocks are ordered
and non-overlapping: if

```text
A_(a1+b1) + b1 = A_(a2+b2) + b2,
```

then first the diagonal indices agree, so `a1 + b1 = a2 + b2`; then the within-
diagonal positions agree, so `b1 = b2`; finally `a1 = a2`.

Surjectivity can be proved by walking through the enumeration one step at a
time. Starting from `(0, 0)`, define a successor operation on pairs:

```text
(0, b)     |-> (b + 1, 0),
(a + 1, b) |-> (a, b + 1).
```

This operation advances the value of `p` by exactly `1`. Since `p(0,0) = 0`,
every natural number is eventually reached. Therefore `p` is a bijection from
`N^2` to `N`.
