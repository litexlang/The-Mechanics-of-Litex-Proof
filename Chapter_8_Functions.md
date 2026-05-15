# Chapter 8 — Functions

Try all snippets in browser: https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Chapter_8_Functions

GitHub source: https://github.com/litexlang/The-Mechanics-of-Litex-Proof/blob/main/Chapter_8_Functions.md

So far, most of our examples have lived close to numbers. We have studied
properties of numbers, such as being odd, positive, prime, or divisible by
another number, and operations on numbers, such as addition, remainders, and
greatest common divisors.

In this chapter we go up one level of abstraction and study properties of and
operations on functions. The new properties include injectivity, surjectivity,
bijectivity, and being inverse to another function. The central operation is
composition.

In Litex, it is fairly easy to write functions and their properties. Since functions are just ordinary objects, they can be used directly in proofs, and the properties of functions can be proved using the same proof patterns as other objects.

## 8.1 Basics

### 8.1.1 Defining Functions with `have fn`

Before proving properties of functions, we need ways to introduce functions.
Litex's main statement for this is `have fn`. There are several common forms.

If a function is given by one formula, write one defining equation:

```text
have fn f(x S) T = body
```

For example, `have fn f(x R: x > 1) R = x + 1` introduces a function whose input is a
real number greater than 1, whose output is a real number, and whose value at `x` is `x + 1`.

```litex
have fn f(x R: x > 1) R = x + 1
f(2) = 3
```

One of the most powerful features of Litex is anonymous function. An anonymous function is
a function expression without a separate name. It has the form `'(x S: condition) T {body}`:
the part before `T` gives the input variable and its domain, `T` is the output type, and
`body` gives the value of the function.

For example:

```litex
have f set = '(x R: x > 0) R {x + 1}
```

This has the same essential meaning as introducing a named function by:

```litex
have fn f(x R: x > 0) R = x + 1
```

When the input set and the output set are the same, and there is no extra domain
condition, Litex also supports a shorter form. For example, the function from `R` to
`R` sending `x` to `x + 1` can be written as:

```litex
'R(x){x + 1} = '(x R) R {x + 1}
```

The difference is only the surface form. The anonymous function expression builds the
function value first, and `have f set = ...` gives that function value the name `f`.
The `have fn` form introduces the same function directly by its defining equation.

**Anonymous functions are very very useful when a function is only needed for one specific purpose, so giving it a separate name would add noise.** This often happens
when we pass a function as an argument to another object. For example, the summation/product
operator reads a function as its third argument: that function tells Litex which term
to use for each index. (Think for yourself how to define integral functions with anonymous functions.)

```litex
eval sum(1, 3, '(x Z) Z {x + x})
eval product(1, 3, '(x Z) Z {x^2})
eval sum(1, 2, '(x Z) Z {sum(2, 3, '(y Z) Z {x + y})})
```

If the formula depends on cases, write a `case` branch for each condition:

```text
have fn g(x S) T:
    case condition_1: value_1
    case condition_2: value_2
```

The cases should cover the part of the domain where the function will be used.
This is the natural Litex form for functions such as absolute value, maximum, or
finite lookup tables.

```litex
have fn g(x, y R) R:
    case x > y: x
    case x <= y: y

g(2, 1) = 2
```

Sometimes a function is not first given by a formula. Instead, mathematics tells
us that for every input there exists a unique output. In that situation, Litex
can introduce the function from the corresponding `forall ... exist!` fact:

```text
have fn f by forall x A:
    condition(x)
    =>:
        exist! y B st {relation(x, y)}
```

After this, `f(x)` names the unique `y` related to `x`.

```litex
abstract_prop p(x, x2)
abstract_prop F(x, x2, y)
have A set
have B set
have C set

know forall x A, x2 B:
    $p(x, x2)
    =>:
        exist! y C st {$F(x, x2, y)}

have fn f by forall x A, x2 B:
    $p(x, x2)
    =>:
        exist! y C st {$F(x, x2, y)}

f $in fn(x A, x2 B: $p(x, x2)) C

forall x A, x2 B:
    $p(x, x2)
    =>:
        $F(x, x2, f(x, x2))
```

That's the set theory definition of a function. In Litex, we can also use it to define a function.

Finally, recursive functions on inductive domains can be introduced by
`have fn by induc`. Base cases and the recursive step are again written as
`case` branches:

```text
have fn by induc from 0: h(x Z: x >= 0) T:
    case x = 0: base_value
    case x >= 1: expression_using_earlier_values
```

This form is useful for sequences and functions defined by recurrence. It says
that values are built in order from the starting point, so the recursive branch
may use earlier values such as `h(x - 1)`.

For example, Fibonacci sequence can be defined by:

```litex
have fn by induc from 0: f(x Z: x >= 0) R:
    case x = 0: 1
    case x = 1: 1
    case x >= 2: f(x - 2) + f(x - 1)

f(2) = f(0) + f(1) = 1 + 1 = 2
```

### 8.1.2 Injective Functions

A function `f : X -> Y` is injective when

```text
f(x1) = f(x2)  implies  x1 = x2.
```

The important point is that the equality starts in the codomain and must be
pulled back to equality in the domain.

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2
```

### 8.1.3 Example: `q(x) = x + 1` Is Injective

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

have fn q(x R) R = x + 1

forall x1, x2 R:
    q(x1) = q(x2)
    =>:
        x2 + 1 = q(x2) = q(x1) = x1 + 1
        x1 = x1 + 1 - 1 = x2 + 1 - 1 = x2

$injective_fn(R, R, q)
```

Equivalently, you can use `forall` to prove this statement without defining the specific function.

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

claim:
    prove:
        forall f fn(x R) R:
            forall a R:
                f(a) = a + 1
            =>:
                $injective_fn(R, R, f)
    forall x1, x2 R:
        f(x1) = f(x2)
        =>:
            x1 = x1 + 1 - 1 = f(x1) - 1 = f(x2) - 1 = x2 + 1 - 1 = x2
```

Equivalently, you can use anonymous function to define the function.

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

forall x1, x2 R:
    'R(x){x + 1}(x1) = 'R(x){x + 1}(x2)
    =>:
        x1 = (x1 + 1) - 1 = 'R(x){x + 1}(x1) - 1 = 'R(x){x + 1}(x2) - 1 = (x2 + 1) - 1 = x2

$injective_fn(R, R, 'R(x){x + 1})
```

### 8.1.4 Example: `x |-> x^2` On `R` Is Not Injective

To disprove injectivity, find two different inputs with the same output.
For the square function on real numbers, the witnesses are `-1` and `1`:

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

by contra not $injective_fn(R, R, 'R(x){x^2}):
    'R(x){x^2}(1) = 1 = 'R(x){x^2}(-1)
    impossible 1 = -1
```

### 8.1.5 Surjective Functions

A function `f : X -> Y` is surjective when every `y` in `Y` is hit by some input:

```text
for every y in Y, there exists x in X such that f(x) = y.
```

A surjectivity proof is usually a witness construction. Given the target output
`y`, solve the equation `f(x) = y` for `x`.

```litex
prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}
```

### 8.1.6 Example: `s(a) = 3a + 2` Is Surjective On `Q`

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

```litex
prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

have fn s(a Q) Q = 3 * a + 2

claim:
    prove:
        forall y Q:
            exist x Q st {y = s(x)}

    have a Q = (y - 2) / 3
    witness exist x Q st {y = s(x)} from a:
        y = 3 * ((y - 2) / 3) + 2 = 3 * a + 2 = s(a)

$surjective_fn(Q, Q, s)
```

### 8.1.7 Example: `x |-> x^2` On `R` Is Not Surjective

To disprove surjectivity, find one output value which is not hit. For the square
function from `R` to `R`, the value `-1` is not hit.

For every real number `x`, we have

```text
0 <= x^2.
```

So `x^2` can never equal `-1`. Therefore the square function is not surjective
as a function from `R` to `R`.

```litex
prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

have fn square(x R) R = x^2

by contra not $surjective_fn(R, R, square):
    have by exist x R st {-1 = square(x)}: x
    0 <= x^2
    -1 = square(x) = x^2
    0 <= -1
    impossible 0 <= -1
```

### 8.1.8 Example: A Finite Function Which Is Not Injective

Consider a finite set with three elements:

```text
Musketeer = {athos, porthos, aramis}.
```

Define a function `f : Musketeer -> Musketeer` by

```text
f(athos) = aramis,
f(porthos) = aramis,
f(aramis) = aramis.
```

This function is not injective because `athos` and `porthos` are different
inputs but have the same output:

```text
f(athos) = aramis = f(porthos).
```

Finite functions make injectivity especially concrete: inspect the arrows and
look for two arrows landing at the same output.

In the Litex example below, `{1, 2, 3}` represents `{athos, porthos, aramis}`.
The function `f` sends every element to `3`, so `1` and `2` are different inputs
with the same output.

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

have fn f(x {1, 2, 3}) {1, 2, 3} = 3

by contra not $injective_fn({1, 2, 3}, {1, 2, 3}, f):
    f(1) = 3 = f(2)
    impossible 1 = 2
```

### 8.1.9 Example: The Same Finite Function Is Not Surjective

The same function `f` is not surjective. The element `porthos` is never hit:

```text
f(athos) = aramis,
f(porthos) = aramis,
f(aramis) = aramis.
```

The only output is `aramis`. Since no input maps to `porthos`, the function is
not surjective.

```litex
prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

have fn f(x {1, 2, 3}) {1, 2, 3} = 3

by enumerate finite_set:
    prove:
        forall x {1, 2, 3}:
            f(x) = 3

by contra not $surjective_fn({1, 2, 3}, {1, 2, 3}, f):
    have by exist x {1, 2, 3} st {2 = f(x)}: x
    f(x) = 3
    2 = f(x) = 3
    impossible 2 = 3
```

### 8.1.10 Example: A Finite Function Which Is Injective

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

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

have fn g(x {1, 2, 3}) {1, 2, 3}:
    case x = 1: 2
    case x = 2: 3
    case x = 3: 1

claim:
    prove:
        forall x1, x2 {1, 2, 3}:
            g(x1) = g(x2)
            =>:
                x1 = x2

    by cases:
        prove:
            x1 = x2
        case x1 = 1:
            by cases:
                prove:
                    x1 = x2
                case x2 = 1:
                    x1 = 1 = x2
                case x2 = 2:
                    g(x1) = g(1) = 2
                    g(x2) = g(2) = 3
                    impossible g(x1) = g(x2)
                case x2 = 3:
                    g(x1) = g(1) = 2
                    g(x2) = g(3) = 1
                    impossible g(x1) = g(x2)
        case x1 = 2:
            by cases:
                prove:
                    x1 = x2
                case x2 = 1:
                    g(x1) = g(2) = 3
                    g(x2) = g(1) = 2
                    impossible g(x1) = g(x2)
                case x2 = 2:
                    x1 = 2 = x2
                case x2 = 3:
                    g(x1) = g(2) = 3
                    g(x2) = g(3) = 1
                    impossible g(x1) = g(x2)
        case x1 = 3:
            by cases:
                prove:
                    x1 = x2
                case x2 = 1:
                    g(x1) = g(3) = 1
                    g(x2) = g(1) = 2
                    impossible g(x1) = g(x2)
                case x2 = 2:
                    g(x1) = g(3) = 1
                    g(x2) = g(2) = 3
                    impossible g(x1) = g(x2)
                case x2 = 3:
                    x1 = 3 = x2

$injective_fn({1, 2, 3}, {1, 2, 3}, g)
```



### 8.1.11 Example: The Same Finite Function Is Surjective

The same function `g` is also surjective. Each target has a preimage:

```text
athos = g(aramis),
porthos = g(athos),
aramis = g(porthos).
```

Thus every element of `Musketeer` is hit.

```litex
prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

have fn g(x {1, 2, 3}) {1, 2, 3}:
    case x = 1: 2
    case x = 2: 3
    case x = 3: 1

claim:
    prove:
        forall y {1, 2, 3}:
            exist x {1, 2, 3} st {y = g(x)}

    by cases:
        prove:
            exist x {1, 2, 3} st {y = g(x)}
        case y = 1:
            witness exist x {1, 2, 3} st {y = g(x)} from 3:
                y = 1 = g(3)
        case y = 2:
            witness exist x {1, 2, 3} st {y = g(x)} from 1:
                y = 2 = g(1)
        case y = 3:
            witness exist x {1, 2, 3} st {y = g(x)} from 2:
                y = 3 = g(2)

$surjective_fn({1, 2, 3}, {1, 2, 3}, g)
```

### 8.1.12 Example: `x |-> x^3` On `R` Is Injective

Suppose `x1^3 = x2^3`. Then

```text
(x1 - x2)(x1^2 + x1*x2 + x2^2) = x1^3 - x2^3 = 0.
```

So either `x1 = x2` or `x1^2 + x1*x2 + x2^2 = 0`. We just need to show the latter is impossible.

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

have fn f(x R) R = x^3

claim:
    prove:
        forall x1, x2 R:
            f(x1) = f(x2)
            =>:
                x1 = x2

    0 = f(x1) - f(x2) = x1^3 - x2^3 = (x1 - x2)*(x1^2 + x1*x2 + x2^2)

    by cases:
        prove:
            x1 = x2
        case x1 - x2 = 0:
            x1 = x2
        case x1^2 + x1*x2 + x2^2 = 0:
            by cases x1 = x2:
                case x1 != 0:
                    0 < x1^2
                    0 < x1^2 +((x1+x2)^2+x2^2) = 2 * (x1^2 + x1 * x2 + x2^2) = 2 * 0 = 0
                    impossible 0 < 0
                case x1 = 0:
                    0 = 0 - x2^3
                    x2^3 = 0
                    by contra x2 = 0:
                        impossible x2^3 != 0
```

## 8.2 Bijectivity

### 8.2.1 Bijective Functions

A function is bijective when it is both injective and surjective. This means it
has no collisions and misses no target values.

### 8.2.2 Example: `p(x) = 2x - 5` Is Bijective

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

### 8.2.3 Example: `a(t) = t^3 - t` Is Not Bijective

Let `a : R -> R` be defined by `a(t) = t^3 - t`. This function is not
injective, because

```text
a(0) = 0^3 - 0 = 0,
a(1) = 1^3 - 1 = 0,
```

but `0 != 1`. Since bijective implies injective, the function is not bijective.

### 8.2.4 Example: A Finite Function Which Is Not Bijective

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

### 8.2.5 Example: Bijective Means Unique Preimages

A function `f : X -> Y` is bijective if and only if every `y` in `Y` has a
unique preimage in `X`.

If `f` is bijective, surjectivity gives at least one `x` with `f(x) = y`.
Injectivity gives uniqueness: if `f(x') = y = f(x)`, then `f(x') = f(x)`, so
`x' = x`.

Conversely, suppose every `y` has a unique preimage. Surjectivity is immediate:
each `y` has some preimage. For injectivity, assume `f(x1) = f(x2)`. Apply the
unique-preimage property to the target value `f(x1)`. Both `x1` and `x2` are
preimages of this same target, so uniqueness gives `x1 = x2`.

### 8.2.6 Example: Injective Implies Bijective On A Two-Element Set

For functions from the two-element set `Celestial` to itself, injectivity already
forces bijectivity.

There are only two possible target values. If an injective function sends `sun`
and `moon` to distinct outputs, then the two outputs must be exactly `sun` and
`moon` in some order. Thus every target value is hit, so the function is
surjective. Since injectivity was assumed, the function is bijective.

The proof is a finite case analysis over the possible values of `f(sun)` and
`f(moon)`.

### 8.2.7 Example: Injective Does Not Always Imply Bijective

The statement "injective implies bijective" fails for functions from `N` to `N`.
The counterexample is

```text
f(n) = n + 1.
```

This function is injective: if `n1 + 1 = n2 + 1`, then `n1 = n2`.

But it is not surjective, because `0` is never hit. For every natural number
`n`, `n + 1 > 0`. So there is no `n` with `f(n) = 0`. Therefore `f` is injective
but not bijective.

## 8.3 Composition And Inverses

### 8.3.1 Composition

If `f : X -> Y` and `g : Y -> Z`, then the composite `g o f : X -> Z` sends
`x` to `g(f(x))`.

### 8.3.2 Example: A Simple Composite

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

### 8.3.3 Identity Function

The identity function on `X` sends each `x` in `X` to itself. It is usually
written `Id_X`.

### 8.3.4 Example: A Function Which Is Its Own Inverse

Let `s : R -> R` be defined by `s(x) = 5 - x`. Then for every real number `x`,

```text
(s o s)(x) = s(5 - x) = 5 - (5 - x) = x.
```

Thus `s o s = Id_R`. The function is an involution: applying it twice gives the
identity.

### 8.3.5 Inverse Functions

A function `g : Y -> X` is an inverse of `f : X -> Y` if both compositions are
identity functions:

```text
g o f = Id_X,
f o g = Id_Y.
```

The first equation says that starting in `X`, applying `f`, then applying `g`
returns the original input. The second says the same for starting in `Y`.

### 8.3.6 Example: An Inverse On A Finite Set

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

### 8.3.7 Example: A Bijective Function Has An Inverse

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

### 8.3.8 Example: A Function With An Inverse Is Bijective

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

### 8.3.9 Example: Bijective If And Only If It Has An Inverse

The previous two examples combine into the fundamental equivalence:

```text
f is bijective  if and only if  f has an inverse.
```

One direction constructs the inverse from bijectivity. The other direction uses
the inverse equations to prove injectivity and surjectivity.

## 8.4 Product Types

Product types are ordered-pair types. Equality of ordered pairs is coordinatewise:

```text
(a, b) = (c, d)  if and only if  a = c and b = d.
```

This is why function proofs on products often split a pair equality into
coordinate equations.

### 8.4.1 Example: A Function From `Z` To `Z^2`

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

### 8.4.2 Example: A Bijective Linear Map On `Z^2`

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

### 8.4.3 Example: Same Formula Over `R^2` And `Z^2`

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

### 8.4.4 Example: An Injective Map From `R^2` To `R^3`

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

### 8.4.5 Example: Addition From `R^2` To `R`

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

### 8.4.6 Example: `5m + 8n` From `Z^2` To `Z`

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

### 8.4.7 Example: `5m + 10n` From `Z^2` To `Z`

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

### 8.4.8 Example: Swapping Coordinates

Define `g : R^2 -> R^2` by

```text
g(x, y) = (y, x).
```

Then `g` is its own inverse. For every `(x, y)`,

```text
g(g(x, y)) = g(y, x) = (x, y).
```

Thus `g o g = Id`.

### 8.4.9 Example: A Bijection From `N^2` To `N`

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
