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

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

prop bijective_fn(S, T set, f fn(x S) T):
    $injective_fn(S, T, f)
    $surjective_fn(S, T, f)
```

### 8.2.2 Example: `p(x) = 2x - 5` Is Bijective

Let `p : R -> R` be defined by `p(x) = 2x - 5`.

To prove that `p` is bijective, prove injectivity and surjectivity separately.
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

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

prop bijective_fn(S, T set, f fn(x S) T):
    $injective_fn(S, T, f)
    $surjective_fn(S, T, f)

have fn p(x R) R = 2 * x - 5

claim:
    prove:
        forall x1, x2 R:
            p(x1) = p(x2)
            =>:
                x1 = x2

    x1 = ((2 * x1 - 5) + 5) / 2 = (p(x1) + 5) / 2 = (p(x2) + 5) / 2 = ((2 * x2 - 5) + 5) / 2 = x2

$injective_fn(R, R, p)

claim:
    prove:
        forall y R:
            exist x R st {y = p(x)}

    witness exist x R st {y = p(x)} from (y + 5) / 2:
        y = 2 * ((y + 5) / 2) - 5 = p((y + 5) / 2)

$surjective_fn(R, R, p)

$bijective_fn(R, R, p)
```

### 8.2.3 Example: `a(t) = t^3 - t` Is Not Bijective

Let `a : R -> R` be defined by `a(t) = t^3 - t`. This function is not
injective, because

```text
a(0) = 0^3 - 0 = 0,
a(1) = 1^3 - 1 = 0,
```

but `0 != 1`. Since bijective implies injective, the function is not bijective.

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

prop bijective_fn(S, T set, f fn(x S) T):
    $injective_fn(S, T, f)
    $surjective_fn(S, T, f)

have fn a(t R) R = t^3 - t

by contra not $injective_fn(R, R, a):
    a(0) = 0 = a(1)
    impossible 0 = 1

by contra not $bijective_fn(R, R, a):
    $injective_fn(R, R, a)
    impossible $injective_fn(R, R, a)
```

### 8.2.4 Example: A Finite Function Which Is Not Bijective

Let

```text
Celestial = {sun, moon}
Subatomic = {proton, neutron, electron}.
```

Define `f : Celestial -> Subatomic` by

```text
f(sun) = proton,
f(moon) = proton.
```

This function is not surjective because `neutron` is not hit. Therefore it is
not bijective.

This also illustrates a counting obstruction: a function from a two-element set
to a three-element set cannot hit all three target values.

In Litex, we represent `Celestial` by `{1, 2}` and `Subatomic` by `{1, 2, 3}`.
The function sends both inputs to `1`, so the target value `2` is not hit.

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

prop bijective_fn(S, T set, f fn(x S) T):
    $injective_fn(S, T, f)
    $surjective_fn(S, T, f)

have fn f(x {1, 2}) {1, 2, 3} = 1

by enumerate finite_set:
    prove:
        forall x {1, 2}:
            f(x) = 1

by contra not $surjective_fn({1, 2}, {1, 2, 3}, f):
    have by exist x {1, 2} st {2 = f(x)}: x
    f(x) = 1
    2 = f(x) = 1
    impossible 2 = 1

by contra not $bijective_fn({1, 2}, {1, 2, 3}, f):
    $surjective_fn({1, 2}, {1, 2, 3}, f)
    impossible $surjective_fn({1, 2}, {1, 2, 3}, f)
```

### 8.2.5 Example: Bijective Means Unique Preimages

A function `f : X -> Y` is bijective if and only if, for every `y` of type `Y`,
there exists a unique `x` of type `X` such that `f(x) = y`.

In Litex-style notation, the unique-preimage condition is:

```text
forall y Y:
    exist! x X st {f(x) = y}
```

If `f` is bijective, surjectivity gives at least one `x` with `f(x) = y`.
Injectivity gives uniqueness: if `f(x') = y = f(x)`, then `f(x') = f(x)`, so
`x' = x`.

Conversely, suppose every `y` has a unique preimage. Surjectivity is immediate:
each `y` has some preimage. For injectivity, assume `f(x1) = f(x2)`. Apply the
unique-preimage property to the target value `f(x1)`. Both `x1` and `x2` are
preimages of this same target, so uniqueness gives `x1 = x2`.

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

prop bijective_fn(S, T set, f fn(x S) T):
    $injective_fn(S, T, f)
    $surjective_fn(S, T, f)

prop exist_unique_preimage(S, T set, f fn(x S) T):
    forall y T:
        exist! x S st {y = f(x)}

claim:
    prove:
        forall S, T set, f fn(x S) T:
            $bijective_fn(S, T, f)
            =>:
                $exist_unique_preimage(S, T, f)

    $injective_fn(S, T, f)
    $surjective_fn(S, T, f)

    claim:
        prove:
            forall y T:
                exist! x S st {y = f(x)}

        have by exist x S st {y = f(x)}: x

        claim:
            prove:
                forall x1, x2 S:
                    y = f(x1)
                    y = f(x2)
                    =>:
                        x1 = x2

            f(x1) = y = f(x2)
            x1 = x2

        exist! x S st {y = f(x)}

    $exist_unique_preimage(S, T, f)

claim:
    prove:
        forall S, T set, f fn(x S) T:
            $exist_unique_preimage(S, T, f)
            =>:
                $bijective_fn(S, T, f)

    claim:
        prove:
            forall y T:
                exist x S st {y = f(x)}

        exist! x S st {y = f(x)}
        exist x S st {y = f(x)}

    $surjective_fn(S, T, f)

    claim:
        prove:
            forall x1, x2 S:
                f(x1) = f(x2)
                =>:
                    x1 = x2

        exist! x S st {f(x1) = f(x)}

        claim:
            prove:
                forall a, b S:
                    f(x1) = f(a)
                    f(x1) = f(b)
                    =>:
                        a = b

        f(x1) = f(x2)
        x1 = x2

    $injective_fn(S, T, f)
    $bijective_fn(S, T, f)
    
    
```

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

In Litex, we can introduce the composite as another function whose body applies
the outside function to the inside function:

```litex
have fn f_add3_R(a R) R = a + 3
have fn g_times2_R(b R) R = 2 * b
have fn h_lin_R(c R) R = 2 * c + 6

have fn gf_R(x R) R = g_times2_R(f_add3_R(x))

claim:
    prove:
        forall x R:
            gf_R(x) = h_lin_R(x)
    gf_R(x) = 2 * (x + 3) = 2 * x + 6 = h_lin_R(x)
```

### 8.3.3 Identity Function

The identity function on `X` sends each `x` in `X` to itself. It is usually
written `Id_X`.

For a concrete domain such as `R`, the identity function is just another
`have fn` definition:

```litex
have fn id_R(t R) R = t

forall x R:
    id_R(x) = x
```

### 8.3.4 Example: A Function Which Is Its Own Inverse

Let `s : R -> R` be defined by `s(x) = 5 - x`. Then for every real number `x`,

```text
(s o s)(x) = s(5 - x) = 5 - (5 - x) = x.
```

Thus `s o s = Id_R`. The function is an involution: applying it twice gives the
identity.

In Litex, define the second iterate `ss_R` explicitly and prove that it agrees
with the identity function pointwise:

```litex
have fn id_R(t R) R = t
have fn s_reflect_R(x R) R = 5 - x

have fn ss_R(x R) R = s_reflect_R(s_reflect_R(x))

claim:
    prove:
        forall x R:
            ss_R(x) = id_R(x)
    ss_R(x) = 5 - (5 - x) = x = id_R(x)
```

### 8.3.5 Inverse Functions

A function `g : Y -> X` is an inverse of `f : X -> Y` if both compositions are
identity functions:

```text
g o f = Id_X,
f o g = Id_Y.
```

The first equation says that starting in `X`, applying `f`, then applying `g`
returns the original input. The second says the same for starting in `Y`.

```litex
prop is_inverse(S, T set, f fn(a S) T, g fn(b T) S):
    forall x S:
        g(f(x)) = x
    forall y T:
        y = f(g(y))
```

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

In Litex, we can represent the four constructors by a finite displayed set:

```text
1 = melancholic, 2 = choleric, 3 = phlegmatic, 4 = sanguine.
```

Then `p` and its inverse `q` are written as case-defined functions. The proof is
just the two finite checks `q(p(x)) = x` and `p(q(x)) = x`.

```litex
have fn p(x {1, 2, 3, 4}) {1, 2, 3, 4}:
    case x = 1: 2
    case x = 2: 4
    case x = 3: 3
    case x = 4: 1

have fn q(x {1, 2, 3, 4}) {1, 2, 3, 4}:
    case x = 1: 4
    case x = 2: 1
    case x = 3: 3
    case x = 4: 2

claim:
    prove:
        forall x {1, 2, 3, 4}:
            q(p(x)) = x

    by cases:
        prove:
            q(p(x)) = x
        case x = 1:
            p(x) = 2
            q(2) = 1
            q(p(x)) = 1 = x
        case x = 2:
            p(x) = 4
            q(4) = 2
            q(p(x)) = 2 = x
        case x = 3:
            p(x) = 3
            q(3) = 3
            q(p(x)) = 3 = x
        case x = 4:
            p(x) = 1
            q(1) = 4
            q(p(x)) = 4 = x

claim:
    prove:
        forall x {1, 2, 3, 4}:
            p(q(x)) = x

    by cases:
        prove:
            p(q(x)) = x
        case x = 1:
            q(x) = 4
            p(4) = 1
            p(q(x)) = 1 = x
        case x = 2:
            q(x) = 1
            p(1) = 2
            p(q(x)) = 2 = x
        case x = 3:
            q(x) = 3
            p(3) = 3
            p(q(x)) = 3 = x
        case x = 4:
            q(x) = 2
            p(2) = 4
            p(q(x)) = 4 = x
```

### 8.3.7 Example: Bijective If And Only If It Has An Inverse

The inverse equations are packaged into `is_inverse`. To say that `f : X -> Y`
has an inverse, we say there exists some `g : Y -> X` satisfying that prop.

This gives the fundamental equivalence:

```text
f is bijective  if and only if  f has an inverse.
```

The forward direction constructs the inverse from unique preimages. For every
`y` in `Y`, bijectivity gives a unique `x` with `f(x) = y`; `have fn g as set`
turns that unique witness into a function value `g(y)`. The reverse direction is
the usual argument: if `g(f(x)) = x` and `f(g(y)) = y`, then `f` is injective and
surjective.

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

prop bijective_fn(S, T set, f fn(x S) T):
    $injective_fn(S, T, f)
    $surjective_fn(S, T, f)

prop exist_unique_preimage(S, T set, f fn(x S) T):
    forall y T:
        exist! x S st {y = f(x)}

know forall S, T set, f fn(x S) T:
    =>:
        $bijective_fn(S, T, f)
    <=>:
        $exist_unique_preimage(S, T, f)

prop is_inverse(S, T set, f fn(a S) T, g fn(b T) S):
    forall x S:
        g(f(x)) = x
    forall y T:
        y = f(g(y))

prop has_inverse(S, T set, f fn(x S) T):
    exist g fn(y T) S st {$is_inverse(S, T, f, g)}

claim:
    prove:
        forall S, T set, f fn(x S) T:
            $bijective_fn(S, T, f)
            =>:
                exist h fn(y T) S st {$is_inverse(S, T, f, h)}

    $exist_unique_preimage(S, T, f)

    have fn g as set:
        forall y T:
            exist! x S st {y = f(x)}

    claim:
        prove:
            forall y T:
                y = f(g(y))

    claim:
        prove:
            forall x S:
                g(f(x)) = x

        f(x) = f(g(f(x)))
        x = g(f(x))
        g(f(x)) = x

    forall x S:
        g(f(x)) = x
    forall y T:
        y = f(g(y))

    g $in fn(y T) S

    witness exist h fn(y T) S st {$is_inverse(S, T, f, h)} from g

claim:
    prove:
        forall S, T set, f fn(x S) T, g fn(y T) S:
            $is_inverse(S, T, f, g)
            =>:
                $bijective_fn(S, T, f)

    claim:
        prove:
            forall x1, x2 S:
                f(x1) = f(x2)
                =>:
                    x1 = x2

        x1 = g(f(x1)) = g(f(x2)) = x2

    $injective_fn(S, T, f)

    claim:
        prove:
            forall y T:
                exist x S st {y = f(x)}

        witness exist x S st {y = f(x)} from g(y)

    $surjective_fn(S, T, f)
    $bijective_fn(S, T, f)

claim:
    prove:
        forall S, T set, f fn(x S) T:
            $has_inverse(S, T, f)
            =>:
                $bijective_fn(S, T, f)

    have by exist g fn(y T) S st {$is_inverse(S, T, f, g)}: g
    $is_inverse(S, T, f, g)

    claim:
        prove:
            forall x1, x2 S:
                f(x1) = f(x2)
                =>:
                    x1 = x2

        x1 = g(f(x1)) = g(f(x2)) = x2

    $injective_fn(S, T, f)

    claim:
        prove:
            forall y T:
                exist x S st {y = f(x)}

        witness exist x S st {y = f(x)} from g(y)

    $surjective_fn(S, T, f)
    $bijective_fn(S, T, f)

claim:
    prove:
        forall S, T set, f fn(x S) T:
            $bijective_fn(S, T, f)
            =>:
                $has_inverse(S, T, f)

    exist h fn(y T) S st {$is_inverse(S, T, f, h)}
    $has_inverse(S, T, f)

know forall S, T set, f fn(x S) T:
    =>:
        $bijective_fn(S, T, f)
    <=>:
        $has_inverse(S, T, f)
```

## 8.4 Product Types

Product types are ordered-pair types. Equality of ordered pairs is coordinatewise:

```text
(a, b) = (c, d)  if and only if  a = c and b = d.
```

This is why function proofs on products often split a pair equality into
coordinate equations.

In Litex, Cartesian products are written with `cart`. For example, `cart(Z, Z)`
is the product of two copies of `Z`, and `cart(R, Q, Z)` is a three-factor
product. Tuple values are written with parentheses, such as `(1, 2)` or
`(x, y, z)`. Tuple projections are one-based:

```litex
(1, 2)[1] = 1
(1, 2)[2] = 2
```

If Litex knows `u $in cart(A, B)`, then it treats `u` as a two-tuple, with
`u[1] $in A` and `u[2] $in B`. Similarly, equality of tuples gives equality of
the corresponding coordinates. This is why product-type proofs often introduce
coordinate equations by writing projections such as `u[1]` and `u[2]`.

```litex
have u cart(Z, Z)

$is_tuple(u)
tuple_dim(u) = 2
u[1] $in Z
u[2] $in Z
```

### 8.4.1 Example: An Injective But Not Surjective Function From `Z` To `cart(Z, Z)`

Define

```text
q : Z -> cart(Z, Z),
q(m) = (m + 1, 2 - m).
```

This function is injective: if `q(m1) = q(m2)`, then the first coordinates are
equal, so `m1 + 1 = m2 + 1`, and hence `m1 = m2`.

It is not surjective. The tuple `(0, 0)` is not in its image. If
`(0, 0) = q(n)`, then `(0, 0) = (n + 1, 2 - n)`, so `n = -1` and `n = 2`,
which is impossible.

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

have fn q(m Z) cart(Z, Z) = (m + 1, 2 - m)

claim:
    prove:
        forall n Z:
            q(n) = (n + 1, 2 - n)

claim:
    prove:
        $injective_fn(Z, cart(Z, Z), q)

    claim:
        prove:
            forall m1, m2 Z:
                q(m1) = q(m2)
                =>:
                    m1 = m2

        q(m1) = (m1 + 1, 2 - m1)
        q(m2) = (m2 + 1, 2 - m2)
        m1 + 1 = q(m1)[1] = q(m2)[1] = m2 + 1
        m1 = (m1 + 1) - 1 = (m2 + 1) - 1 = m2

    $injective_fn(Z, cart(Z, Z), q)

claim:
    prove:
        not $surjective_fn(Z, cart(Z, Z), q)

    by contra:
        prove:
            not $surjective_fn(Z, cart(Z, Z), q)
        $surjective_fn(Z, cart(Z, Z), q)
        forall y cart(Z, Z):
            exist n Z st {y = q(n)}
        exist n Z st {(0, 0) = q(n)}
        have by exist n Z st {(0, 0) = q(n)}: n
        (0, 0) = q(n)
        q(n) = (n + 1, 2 - n)
        (0, 0) = (n + 1, 2 - n)
        0 = n + 1
        0 = 2 - n
        n = -1
        n = 2
        impossible -1 = 2
```

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

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

prop bijective_fn(S, T set, f fn(x S) T):
    $injective_fn(S, T, f)
    $surjective_fn(S, T, f)

know forall t cart(Z, Z):
    t = (t[1], t[2])

have fn F_Z2(t cart(Z, Z)) cart(Z, Z) = (t[1] + t[2], t[1] + 2 * t[2])
have fn Finv_Z2(s cart(Z, Z)) cart(Z, Z) = (2 * s[1] - s[2], s[2] - s[1])

claim:
    prove:
        forall t cart(Z, Z):
            Finv_Z2(F_Z2(t)) = t
    F_Z2(t) = (t[1] + t[2], t[1] + 2 * t[2])
    Finv_Z2(F_Z2(t)) = (2 * (t[1] + t[2]) - (t[1] + 2 * t[2]), (t[1] + 2 * t[2]) - (t[1] + t[2])) = (t[1], t[2]) = t

claim:
    prove:
        forall s cart(Z, Z):
            F_Z2(Finv_Z2(s)) = s
    Finv_Z2(s) = (2 * s[1] - s[2], s[2] - s[1])
    F_Z2(Finv_Z2(s)) = (2 * s[1] - s[2] + (s[2] - s[1]), 2 * s[1] - s[2] + 2 * (s[2] - s[1])) = (s[1], s[2]) = s

claim:
    prove:
        $injective_fn(cart(Z, Z), cart(Z, Z), F_Z2)
    claim:
        prove:
            forall u, v cart(Z, Z):
                F_Z2(u) = F_Z2(v)
                =>:
                    u = v
        u = Finv_Z2(F_Z2(u)) = Finv_Z2(F_Z2(v)) = v
    $injective_fn(cart(Z, Z), cart(Z, Z), F_Z2)

claim:
    prove:
        $surjective_fn(cart(Z, Z), cart(Z, Z), F_Z2)
    claim:
        prove:
            forall y cart(Z, Z):
                exist x cart(Z, Z) st {y = F_Z2(x)}
        witness exist x cart(Z, Z) st {y = F_Z2(x)} from Finv_Z2(y):
            y = F_Z2(Finv_Z2(y))
    $surjective_fn(cart(Z, Z), cart(Z, Z), F_Z2)

$bijective_fn(cart(Z, Z), cart(Z, Z), F_Z2)
```

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

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

prop bijective_fn(S, T set, f fn(x S) T):
    $injective_fn(S, T, f)
    $surjective_fn(S, T, f)

know forall t cart(R, R):
    t = (t[1], t[2])

have fn F_R2(t cart(R, R)) cart(R, R) = (t[1] + t[2], t[1] - t[2])
have fn Finv_R2(s cart(R, R)) cart(R, R) = ((s[1] + s[2]) / 2, (s[1] - s[2]) / 2)

claim:
    prove:
        forall t cart(R, R):
            Finv_R2(F_R2(t)) = t
    F_R2(t) = (t[1] + t[2], t[1] - t[2])
    Finv_R2(F_R2(t)) = ((t[1] + t[2] + (t[1] - t[2])) / 2, ((t[1] + t[2]) - (t[1] - t[2])) / 2) = (t[1], t[2]) = t

claim:
    prove:
        forall s cart(R, R):
            F_R2(Finv_R2(s)) = s
    Finv_R2(s) = ((s[1] + s[2]) / 2, (s[1] - s[2]) / 2)
    F_R2(Finv_R2(s)) = ((s[1] + s[2]) / 2 + (s[1] - s[2]) / 2, (s[1] + s[2]) / 2 - (s[1] - s[2]) / 2) = (s[1], s[2]) = s

claim:
    prove:
        $injective_fn(cart(R, R), cart(R, R), F_R2)
    claim:
        prove:
            forall u, v cart(R, R):
                F_R2(u) = F_R2(v)
                =>:
                    u = v
        u = Finv_R2(F_R2(u)) = Finv_R2(F_R2(v)) = v
    $injective_fn(cart(R, R), cart(R, R), F_R2)

claim:
    prove:
        $surjective_fn(cart(R, R), cart(R, R), F_R2)
    claim:
        prove:
            forall y cart(R, R):
                exist x cart(R, R) st {y = F_R2(x)}
        witness exist x cart(R, R) st {y = F_R2(x)} from Finv_R2(y):
            y = F_R2(Finv_R2(y))
    $surjective_fn(cart(R, R), cart(R, R), F_R2)

$bijective_fn(cart(R, R), cart(R, R), F_R2)
```

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

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

know forall u, v cart(R, R):
    u[1] = v[1]
    u[2] = v[2]
    =>:
        u = v

have fn rho_R3(t cart(R, R)) cart(R, R, R) = (t[1] + t[2], t[1] - t[2], t[2])

claim:
    prove:
        $injective_fn(cart(R, R), cart(R, R, R), rho_R3)
    claim:
        prove:
            forall u, v cart(R, R):
                rho_R3(u) = rho_R3(v)
                =>:
                    u = v
        rho_R3(u) = (u[1] + u[2], u[1] - u[2], u[2])
        rho_R3(v) = (v[1] + v[2], v[1] - v[2], v[2])
        u[2] = rho_R3(u)[3] = rho_R3(v)[3] = v[2]
        u[1] + u[2] = rho_R3(u)[1] = rho_R3(v)[1] = v[1] + v[2]
        u[1] = (u[1] + u[2]) - u[2] = (v[1] + v[2]) - v[2] = v[1]
        u = v
    $injective_fn(cart(R, R), cart(R, R, R), rho_R3)
```

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

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

have fn add_R2(p cart(R, R)) R = p[1] + p[2]

claim:
    prove:
        not $injective_fn(cart(R, R), R, add_R2)
    by contra:
        prove:
            not $injective_fn(cart(R, R), R, add_R2)
        $injective_fn(cart(R, R), R, add_R2)
        add_R2((0, 0)) = 0
        add_R2((1, -1)) = 0
        add_R2((0, 0)) = add_R2((1, -1))
        (0, 0) = (1, -1)
        0 = (0, 0)[1] = (1, -1)[1] = 1
        impossible 0 = 1

claim:
    prove:
        $surjective_fn(cart(R, R), R, add_R2)
    claim:
        prove:
            forall a R:
                exist p cart(R, R) st {a = add_R2(p)}
        witness exist p cart(R, R) st {a = add_R2(p)} from (a, 0):
            a = a + 0 = add_R2((a, 0))
    $surjective_fn(cart(R, R), R, add_R2)
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

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

have fn Z_lin58(u cart(Z, Z)) Z = 5 * u[1] + 8 * u[2]

claim:
    prove:
        not $injective_fn(cart(Z, Z), Z, Z_lin58)
    by contra:
        prove:
            not $injective_fn(cart(Z, Z), Z, Z_lin58)
        $injective_fn(cart(Z, Z), Z, Z_lin58)
        Z_lin58((0, 0)) = 0
        Z_lin58((8, -5)) = 0
        Z_lin58((0, 0)) = Z_lin58((8, -5))
        (0, 0) = (8, -5)
        0 = (0, 0)[1] = (8, -5)[1] = 8
        impossible 0 = 8

claim:
    prove:
        $surjective_fn(cart(Z, Z), Z, Z_lin58)
    claim:
        prove:
            forall a Z:
                exist u cart(Z, Z) st {a = Z_lin58(u)}
        witness exist u cart(Z, Z) st {a = Z_lin58(u)} from (-3 * a, 2 * a):
            a = 5 * (-3 * a) + 8 * (2 * a) = Z_lin58((-3 * a, 2 * a))
    $surjective_fn(cart(Z, Z), Z, Z_lin58)
```

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

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

have fn Z_lin510(u cart(Z, Z)) Z = 5 * u[1] + 10 * u[2]

claim:
    prove:
        forall k Z:
            (5 * k) % 5 = 0
    (5 * k) % 5 = ((5 % 5) * (k % 5)) % 5 = (0 * (k % 5)) % 5 = 0 % 5 = 0

claim:
    prove:
        not $injective_fn(cart(Z, Z), Z, Z_lin510)
    by contra:
        prove:
            not $injective_fn(cart(Z, Z), Z, Z_lin510)
        $injective_fn(cart(Z, Z), Z, Z_lin510)
        Z_lin510((0, 0)) = 0
        Z_lin510((2, -1)) = 0
        Z_lin510((0, 0)) = Z_lin510((2, -1))
        (0, 0) = (2, -1)
        0 = (0, 0)[1] = (2, -1)[1] = 2
        impossible 0 = 2

claim:
    prove:
        not $surjective_fn(cart(Z, Z), Z, Z_lin510)
    by contra:
        prove:
            not $surjective_fn(cart(Z, Z), Z, Z_lin510)
        $surjective_fn(cart(Z, Z), Z, Z_lin510)
        forall y Z:
            exist u cart(Z, Z) st {y = Z_lin510(u)}
        exist u cart(Z, Z) st {1 = Z_lin510(u)}
        have by exist u cart(Z, Z) st {1 = Z_lin510(u)}: u
        1 = Z_lin510(u)
        Z_lin510(u) = 5 * u[1] + 10 * u[2] = 5 * (u[1] + 2 * u[2])
        1 = 5 * (u[1] + 2 * u[2])
        (5 * (u[1] + 2 * u[2])) % 5 = 0
        1 % 5 = (5 * (u[1] + 2 * u[2])) % 5 = 0
        impossible 1 % 5 = 0
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

```litex
have fn swap_R2(t cart(R, R)) cart(R, R) = (t[2], t[1])
have fn id_R2(t cart(R, R)) cart(R, R) = t
have fn swap_swap_R2(t cart(R, R)) cart(R, R) = swap_R2(swap_R2(t))

claim:
    prove:
        forall t cart(R, R):
            swap_swap_R2(t) = id_R2(t)
    swap_R2(t) = (t[2], t[1])
    swap_swap_R2(t) = (t[1], t[2])
    id_R2(t) = t
    know forall u cart(R, R):
        u = (u[1], u[2])
    swap_swap_R2(t) = (t[1], t[2]) = t = id_R2(t)
```

### 8.4.9 Example: A Bijection From `N^2` To `N`

There exists a bijection from pairs of natural numbers to natural numbers. A
standard construction is the Cantor pairing function. It lists pairs by
diagonals:
