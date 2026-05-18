# Chapter 10 — Relations

Try all snippets in browser: https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Chapter_10_Relations

GitHub source: https://github.com/litexlang/The-Mechanics-of-Litex-Proof/blob/main/Chapter_10_Relations.md

This chapter studies relations and their basic properties, such as reflexivity, symmetry, antisymmetry, and transitivity. These properties appear throughout mathematics whenever we compare, identify, order, or group objects.

## 10.1 Reflexive, symmetric, antisymmetric, transitive

Let a relation (prop) R be defined on a set or type X. You can read "x $R y" as "x is
related to y under R (in that order)".

- Reflexive means: every element of X is related to itself under R.
- Symmetric means: for any two elements x and y in X, if x is related to y under R,
  then y is related to x under R.
- Antisymmetric means: for any two elements x and y in X, if x is related to y under R
  and y is related to x under R, then x and y are the same element.
- Transitive means: for any three elements x, y, and z in X, if x is related to
  y under R and y is related to z under R, then x is related to z under R.

These four properties are about the relation (prop) itself, not about one particular
pair of objects.

In Litex, once you have proved that a user-defined relation has one of these
properties, you can register that fact with a `by ..._prop` statement. The point
is not to prove a new goal immediately, but to let Litex remember the property
and use it later during proof checking.

The four registration keywords are:

- `by reflexive_prop`: after proving `forall x set: $p(x, x)`, Litex can later
  close goals of the form `$p(a, a)`.
- `by symmetric_prop`: after proving `$p(x, y) => $p(y, x)`, Litex can later use
  a known `$p(a, b)` to prove `$p(b, a)`.
- `by transitive_prop`: after proving `$p(x, y)` and `$p(y, z) => $p(x, z)`,
  Litex can use chains like `a $p b $p c` and remember `$p(a, c)`.
- `by antisymmetric_prop`: after proving `$p(x, y)` and `$p(y, x) => x = y`,
  Litex can later prove `a = b` from `$p(a, b)` and `$p(b, a)`.

Here is the basic pattern:

```litex
abstract_prop rel(x, y)

by reflexive_prop:
    prove:
        forall x set:
            $rel(x, x)
    know $rel(x, x)

by symmetric_prop:
    prove:
        forall x, y set:
            $rel(x, y)
            =>:
                $rel(y, x)
    know $rel(y, x)

by transitive_prop:
    prove:
        forall x, y, z set:
            $rel(x, y)
            $rel(y, z)
            =>:
                $rel(x, z)
    know $rel(x, z)

by antisymmetric_prop:
    prove:
        forall x, y set:
            $rel(x, y)
            $rel(y, x)
            =>:
                x = y
    know x = y

have a, b, c set

claim:
    prove:
        $rel(a, a)

claim:
    prove:
        forall a, b set:
            $rel(a, b)
            =>:
                $rel(b, a)

claim:
    prove:
        forall a, b, c set:
            $rel(a, b)
            $rel(b, c)
            =>:
                $rel(a, c)
    a $rel b $rel c

claim:
    prove:
        forall a, b set:
            $rel(a, b)
            $rel(b, a)
            =>:
                a = b
```

After these registrations, later proofs can be shorter: you state the local
facts, and Litex uses the registered relation properties as background steps.
These keywords are for user-defined relations such as `$rel(...)`; they are not
used to register builtin predicates such as `=`, `<`, `$in`, or `$subset`.

### 10.1.1 Divisibility on the natural numbers

Say that "a divides b" when there is some natural number k with b equal to a
times k. It has the following properties:
- Reflexive: every x in N divides itself.
- Transitive: if a divides b and b divides c, then a divides c.
- Antisymmetric: if a divides b and b divides a, then a equals b.
- Not symmetric: 1 divides 2 but not vice versa.

```litex
prop divides(a N, b N):
    exist k N st {b = a * k}

# Reflexive
claim:
    prove:
        forall x N:
            $divides(x, x)
    witness exist k N st {x = x * k} from 1:
        x = x * 1

# Transitive
claim:
    prove:
        forall a, b, c N:
            $divides(a, b)
            $divides(b, c)
            =>:
                $divides(a, c)
    have by exist k N st {b = a * k}: k1
    have by exist k N st {c = b * k}: k2
    witness exist k N st {c = a * k} from k1 * k2:
        c = b * k2 = (a * k1) * k2 = a * (k1 * k2)

# Antisymmetric
claim:
    prove:
        forall a, b N:
            $divides(a, b)
            $divides(b, a)
            =>:
                a = b
    have by exist k N st {b = a * k}: k1
    have by exist k N st {a = b * k}: k2
    by cases b >= a:
        case k1 = 0:
            b = a * k1 = a * 0 = 0
            a = b * k2 = 0 * k2 = 0
            a = b
        case k1 != 0:
            k1 >= 1
            b = a * k1 >= a * 1 = a
    by cases a >= b:
        case k2 = 0:
            a = b * k2 = b * 0 = 0
            b = a * k1 = 0 * k1 = 0
            a = b
        case k2 != 0:
            a = b * k2 >= b * 1 = b

    a = b

# Not symmetric
claim:
    prove:
        $divides(1, 2)
        not $divides(2, 1)
    witness exist k N st {2 = 1 * k} from 2:
        2 = 1 * 2

    $divides(1, 2)

    by contra not $divides(2, 1):
        $divides(2, 1)
        impossible 1 = 2
```

As you can see, the formalization of those common properties is very straightforward in Litex. It's just a matter of defining the relation and proving the properties using plain logic.

### 10.1.2 Equality

Equality is a relation on any set. It has the following properties:
- Reflexive: every element of X is equal to itself.
- Symmetric: if x is equal to y, then y is equal to x.
- Antisymmetric: if x is equal to y and y is equal to x, then x and y are the same element.
- Transitive: if x is equal to y and y is equal to z, then x is equal to z.

```litex
forall x R:
    x = x

forall x, y R:
    x = y
    =>:
        y = x

forall x, y R:
    x = y
    y = x
    =>:
        x = y

forall x, y, z R:
    x = y
    y = z
    =>:
        x = z
```

### 10.1.3 Example

Define a relation $gap_square_less_than_one on R by "the square of the gap between x and y is less than 1". It has the following properties:
- Symmetric: if x is less than y, then y is less than x.
- Reflexive: every element of R is less than itself.
- Not Antisymmetric: 1.5 is less than 1 but not vice versa.
- Not Transitive: 1 is less than 1.5 and 1.5 is less than 2, but not less than 1.

```litex
prop gap_square_less_than_one(x, y R):
    (y - x)^2 < 1

# Symmetric
forall x, y R:
    $gap_square_less_than_one(x, y)
    =>:
        (x - y)^ 2 = (y - x)^2 < 1
        $gap_square_less_than_one(y, x)
    
# Reflexive
forall x R:
    (x - x)^2 = 0 < 1
    $gap_square_less_than_one(x, x)

# Not Antisymmetric
(1.5 - 1)^2 = (1 - 1.5)^2 = 0.25 < 1
$gap_square_less_than_one(1, 1.5)
$gap_square_less_than_one(1.5, 1)
1.5 != 1

# Not Transitive
$gap_square_less_than_one(1, 1.5)
$gap_square_less_than_one(1.5, 2)
not (2 - 1)^2 < 1
```

### 10.1.4 Rock-paper-scissors

```litex
by enumerate finite_set:
    prove:
        forall x {0, 1, 2}, y {0, 1, 2}:
            x = 0 and y = 0 or x = 0 and y = 1 or x = 0 and y = 2 or x = 1 and y = 0 or x = 1 and y = 1 or x = 1 and y = 2 or x = 2 and y = 0 or x = 2 and y = 1 or x = 2 and y = 2

# 1 means winning, 0 means losing or draw
have fn rock_paper_scissors(x {0, 1, 2}, y {0, 1, 2}) {0, 1}:
    case x = 0 and y = 0: 0
    case x = 0 and y = 1: 1
    case x = 0 and y = 2: 0
    case x = 1 and y = 0: 0
    case x = 1 and y = 1: 0
    case x = 1 and y = 2: 1
    case x = 2 and y = 0: 1
    case x = 2 and y = 1: 0
    case x = 2 and y = 2: 0
    
# Not Reflexive
rock_paper_scissors(0, 0) = 0

# Not Symmetric
rock_paper_scissors(0, 1) = 1
rock_paper_scissors(1, 0) = 0

# Antisymmetric
claim:
    prove:
        forall x, y {0, 1, 2}:
            rock_paper_scissors(x, y) = rock_paper_scissors(y, x)
            =>:
                x = y

    by cases x = y:
        case x = 0 and y = 0:
            do_nothing
        case x = 0 and y = 1:
            1 = rock_paper_scissors(0, 1) = rock_paper_scissors(x, y) = rock_paper_scissors(y, x) = rock_paper_scissors(1, 0) = 0
            impossible 0 = 1
        case x = 0 and y = 2:
            0 = rock_paper_scissors(0, 2) = rock_paper_scissors(x, y) = rock_paper_scissors(y, x) = rock_paper_scissors(2, 0) = 1
            impossible 0 = 1
        case x = 1 and y = 0:
            0 = rock_paper_scissors(1, 0) = rock_paper_scissors(x, y) = rock_paper_scissors(y, x) = rock_paper_scissors(0, 1) = 1
            impossible 0 = 1
        case x = 1 and y = 1:
            do_nothing
        case x = 1 and y = 2:
            1 = rock_paper_scissors(1, 2) = rock_paper_scissors(x, y) = rock_paper_scissors(y, x) = rock_paper_scissors(2, 1) = 0
            impossible 0 = 1
        case x = 2 and y = 0:
            1 = rock_paper_scissors(2, 0) = rock_paper_scissors(x, y) = rock_paper_scissors(y, x) = rock_paper_scissors(0, 2) = 0
            impossible 1 = 0
        case x = 2 and y = 1:
            0 = rock_paper_scissors(2, 1) = rock_paper_scissors(x, y) = rock_paper_scissors(y, x) = rock_paper_scissors(1, 2) = 1
            impossible 0 = 1
        case x = 2 and y = 2:
            do_nothing


# Not Transitive
rock_paper_scissors(0, 1) = 1
rock_paper_scissors(1, 2) = 1
rock_paper_scissors(0, 2) = 0
```

## 10.2 Equivalence relations

A relation is an equivalence relation if it is reflexive, symmetric, and
transitive. Antisymmetry is not part of the definition.

Equivalence relations formalize the idea that two objects are "the same for the
purpose currently being studied". Equality itself is an equivalence relation,
but many equivalence relations identify objects which are not literally equal.

### 10.2.1 Congruence modulo

Congruence modulo is symmetric and transitive.

```litex
prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}

claim:
    prove:
        forall x, y, n Z:
            $mod_eq(x, y, n)
            =>:
                $mod_eq(y, x, n)
    have by exist k Z st {x - y = n * k}: k
    witness exist k2 Z st {y - x = n * k2} from -k:
        y - x = -(x - y) = -(n * k) = n * (-k)

claim:
    prove:
        forall x, y, z, n Z:
            $mod_eq(x, y, n)
            $mod_eq(y, z, n)
            =>:
                $mod_eq(x, z, n)
    have by exist k Z st {x - y = n * k}: k1
    have by exist k Z st {y - z = n * k}: k2
    witness exist k Z st {x - z = n * k} from k1 + k2:
        x - z = (x - y) + (y - z) = n * k1 + n * k2 = n * (k1 + k2)
```



### 10.2.2 Equality of squares

The relation on Z defined by `x^2 = y^2` is reflexive, symmetric, and transitive, thus an equivalence relation.

```litex
prop square_eq(x Z, y Z):
    x^2 = y^2

claim:
    prove:
        forall x Z:
            $square_eq(x, x)
    x^2 = x^2

claim:
    prove:
        forall x, y Z:
            $square_eq(x, y)
            =>:
                $square_eq(y, x)
    x^2 = y^2
    y^2 = x^2

claim:
    prove:
        forall x, y, z Z:
            $square_eq(x, y)
            $square_eq(y, z)
            =>:
                $square_eq(x, z)
    x^2 = y^2
    y^2 = z^2
    x^2 = z^2
```

### 10.2.3 Equivalence classes

An equivalence relation on a set `X` is a relation which is reflexive,
symmetric, and transitive on `X`.

For an element `a` of `X`, its equivalence class is the set of all elements
related to `a`:

```text
{b X: $rel(a, b)}
```

These equivalence classes form a partition of `X`: elements in the same class
produce the same class, and different classes do not overlap. The key step is:
if `a1` is related to `a2`, then the class generated by `a1` is the same set as
the class generated by `a2`, i.e. `{b X: $rel(a1, b)} = {b X: $rel(a2, b)}`

This particular fact only needs symmetry and transitivity. Reflexivity is needed
for the larger statement that every element belongs to its own class. The
`by symmetric_prop` and `by transitive_prop` registrations below mean that, after
we have proved those two properties once, Litex can use them automatically in the
two short inner claims.

```litex
abstract_prop rel(x, y)

by symmetric_prop:
    prove:
        forall x, y set:
            $rel(x, y)
            =>:
                $rel(y, x)
    know $rel(y, x)

by transitive_prop:
    prove:
        forall x, y, z set:
            $rel(x, y)
            $rel(y, z)
            =>:
                $rel(x, z)
    know $rel(x, z)

claim:
    prove:
        forall X set, a1, a2 X:
            $rel(a1, a2)
            =>:
                {b X: $rel(a1, b)} = {b X: $rel(a2, b)}
    claim:
        prove:
            forall b X:
                $rel(a1, b)
                =>:
                    $rel(a2, b)
        a2 $rel a1 $rel b

    claim:
        prove:
            forall b X:
                $rel(a2, b)
                =>:
                    $rel(a1, b)
        a1 $rel a2 $rel b

    by extension:
        prove:
            {b X: $rel(a1, b)} = {b X: $rel(a2, b)}
```

### 10.2.4 Example

Equality is an equivalence relation on any set. This is already proved previously by example 10.1.2.

### 10.2.5 Integer pairs representing rational numbers

In Litex, we write this relation as a named prop on `cart(Z, N)`:

```litex
prop rational_pair_eq(p cart(Z, N), q cart(Z, N)):
    p[1] * (q[2] + 1) = q[1] * (p[2] + 1)

claim:
    prove:
        forall p cart(Z, N):
            $rational_pair_eq(p, p)
    p[1] * (p[2] + 1) = p[1] * (p[2] + 1)

claim:
    prove:
        forall p, q cart(Z, N):
            $rational_pair_eq(p, q)
            =>:
                $rational_pair_eq(q, p)
    p[1] * (q[2] + 1) = q[1] * (p[2] + 1)
    q[1] * (p[2] + 1) = p[1] * (q[2] + 1)

claim:
    prove:
        forall p, q, r cart(Z, N):
            $rational_pair_eq(p, q)
            $rational_pair_eq(q, r)
            =>:
                $rational_pair_eq(p, r)
    (q[2] + 1) * (p[1] * (r[2] + 1)) = (p[1] * (q[2] + 1)) * (r[2] + 1) = (q[1] * (p[2] + 1)) * (r[2] + 1) = (q[1] * (r[2] + 1)) * (p[2] + 1) = (r[1] * (q[2] + 1)) * (p[2] + 1) = (q[2] + 1) * (r[1] * (p[2] + 1))
    q[2] + 1 > 0
    q[2] + 1 != 0
    p[1] * (r[2] + 1) = ((q[2] + 1) * (p[1] * (r[2] + 1))) / (q[2] + 1) = ((q[2] + 1) * (r[1] * (p[2] + 1))) / (q[2] + 1) = r[1] * (p[2] + 1)
```

### 10.2.6 Bijection between sets

Here the relation is between sets, not between elements of one fixed set.
We say that two sets `S` and `T` are related when there exists a bijective
function from `S` to `T`. In ordinary mathematics, this means that the two sets
have the same cardinality.

The code below first recalls the definitions from Chapter 8: injective,
surjective, bijective, and "there exists a bijection". Then it proves that this
relation is an equivalence relation on sets.

- Reflexive: every set is bijective with itself by the identity function.
- Symmetric: if there is a bijection `f : S -> T`, then the inverse function
  gives a bijection `T -> S`.
- Transitive: if `S` is bijective with `T`, and `T` is bijective with `U`, then
  the composition of the two bijections gives a bijection `S -> U`.

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

prop exist_bijection(S, T set):
    exist f fn(x S) T st {$bijective_fn(S, T, f)}

prop is_inverse_of_fn(S, T set, f fn(x S) T, g fn(x T) S):
    forall x S:
        g(f(x)) = x
    forall y T:
        y = f(g(y))

# Fact from chapter 9: If a function is bijective, then there exists an inverse function.
know forall A, B set, f fn(x A) B:
    $bijective_fn(A, B, f)
    =>:
        exist g fn(x B) A st {$is_inverse_of_fn(A, B, f, g)}

# The relation "there exists a bijection between the two sets" is an
# equivalence relation on sets.

# Reflexive: every set has the identity bijection to itself.
claim:
    prove:
        forall S set:
            $exist_bijection(S, S)
    have fn id(x S) S = x

    claim:
        prove:
            forall x1, x2 S:
                id(x1) = id(x2)
                =>:
                    x1 = x2
        x1 = id(x1) = id(x2) = x2
    $injective_fn(S, S, id)

    claim:
        prove:
            forall y S:
                exist x S st {y = id(x)}
        witness exist x S st {y = id(x)} from y
    $surjective_fn(S, S, id)

    $bijective_fn(S, S, id)
    witness exist f fn(x S) S st {$bijective_fn(S, S, f)} from id
    $exist_bijection(S, S)


# Symmetric: if f is a bijection from S to T, then its inverse is a bijection
# from T to S.
claim:
    prove:
        forall S, T set:
            $exist_bijection(S, T)
            =>:
                $exist_bijection(T, S)
    have by exist f fn(x S) T st {$bijective_fn(S, T, f)}: f
    exist g fn(x T) S st {$is_inverse_of_fn(S, T, f, g)}
    have by exist g fn(x T) S st {$is_inverse_of_fn(S, T, f, g)}: g

    claim:
        prove:
            forall y1, y2 T:
                g(y1) = g(y2)
                =>:
                    y1 = y2
        y1 = f(g(y1)) = f(g(y2)) = y2
    $injective_fn(T, S, g)

    claim:
        prove:
            forall x S:
                exist y T st {x = g(y)}
        witness exist y T st {x = g(y)} from f(x):
            x = g(f(x))
    $surjective_fn(T, S, g)

    $bijective_fn(T, S, g)
    witness exist f fn(x T) S st {$bijective_fn(T, S, f)} from g
    $exist_bijection(T, S)


# Transitive: compose two bijections.
claim:
    prove:
        forall S, T, U set:
            $exist_bijection(S, T)
            $exist_bijection(T, U)
            =>:
                $exist_bijection(S, U)
    have by exist f fn(x S) T st {$bijective_fn(S, T, f)}: f
    have by exist g fn(x T) U st {$bijective_fn(T, U, g)}: g
    have fn h(x S) U = g(f(x))

    claim:
        prove:
            forall x1, x2 S:
                h(x1) = h(x2)
                =>:
                    x1 = x2
        g(f(x1)) = h(x1) = h(x2) = g(f(x2))
        f(x1) = f(x2)
        x1 = x2
    $injective_fn(S, U, h)

    claim:
        prove:
            forall z U:
                exist x S st {z = h(x)}
        have by exist y T st {z = g(y)}: y
        have by exist x S st {y = f(x)}: x
        witness exist x S st {z = h(x)} from x:
            z = g(y) = g(f(x)) = h(x)
    $surjective_fn(S, U, h)

    $bijective_fn(S, U, h)
    witness exist f fn(x S) U st {$bijective_fn(S, U, f)} from h
    $exist_bijection(S, U)


```

## Summary

Relations let us talk about how two objects are connected. The four recurring
properties are:

- Reflexive: every object is related to itself.
- Symmetric: a relation can be reversed.
- Antisymmetric: two-way related objects must be equal.
- Transitive: two related steps can be composed into one.

In ordinary proofs, these properties are useful because they become reusable
background facts. Litex mirrors that idea with `by reflexive_prop`,
`by symmetric_prop`, `by transitive_prop`, and `by antisymmetric_prop`: first you
prove the property for a user-defined relation, then Litex can use it later
without making you restate the same argument. This is why equivalence relations
and order-like relations are so convenient: once their basic properties are
registered, later proofs can focus on the mathematical idea rather than on
repeating routine relation steps.
