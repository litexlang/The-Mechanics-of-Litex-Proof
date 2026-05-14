# Chapter 4 — Proofs With Structure II

In Chapter 2, we started using proof structures that go beyond a single
calculation: intermediate facts, case splits, and contradiction arguments. In
Litex, these are not mainly about choosing tactics from a library. They are
about writing the mathematical structure explicitly enough that Litex can check
which facts are available, which facts have been proved, and which statement is
being established next.

This chapter continues that work. We look more systematically at the proof
grammar for `forall`, implication, `iff`, uniqueness, contradictory hypotheses,
and proof by contradiction. In each case, the Litex version focuses on two
questions: how do you use such a statement when it is already known, and how do
you prove such a statement when it is the goal?

The examples are organized as one mathematical problem paired with one Litex
idea. Some snippets state standard facts with `know` so the example can stand
alone; in a longer development, those facts would usually come from earlier
proved lemmas.

The main things to watch for while reading are:

- how a `forall` statement is instantiated by matching the goal;
- how an implication becomes a new assumption before `=>:`;
- how an "if and only if" proof is split into two ordinary implications;
- how uniqueness is unfolded into existence plus a uniqueness argument;
- how contradictions are isolated inside a branch.

## 4.1 “For all” and Implication

### 4.1.1

Problem: Let `a` be a real number and suppose that for all real numbers `x`,
`a <= x^2 - 2x`. Show that `a <= -1`.

The hypothesis gives a whole family of inequalities, one for each real number
`x`. To prove the goal, we only need the particular member of that family where
`x = 1`.

```litex
claim:
    prove:
        forall a R:
            forall x R:
                a <= x^2 - 2 * x
            =>:
                a <= -1
    a <= 1^2 - 2 * 1 = -1
```

Do not overlook the parameter type in the outer quantifier. The header
`forall a R:` introduces an arbitrary object `a` together with the domain fact
`a $in R`, so Litex can use real-number arithmetic involving `a`.

The line `a <= 1^2 - 2 * 1` is matched against the available `forall`
hypothesis

```text
a $in R
forall x R:
    a <= x^2 - 2 * x
```

by taking the universally quantified variable `x` to be the concrete value
`1`. After that, the final equality `1^2 - 2 * 1 = -1` is just arithmetic.

A Litex parameter type is the mathematical constraint written after a variable.
It can be a membership constraint such as `R`, `Z`, or `N`, or a structural
constraint such as `set`, `nonempty_set`, or `finite_set`. The same notation
appears in `prop`, `forall`, and `exist`.

```text
prop p(a R, s set):
    ...

forall x R:
    ...

exist y Z st {...}
```

Read `forall x R:` as: for every object `x` satisfying `x $in R`.

### 4.1.2

Problem: Let `n` be a natural number which is a factor of every natural number
`m`. Show that `n = 1`.

The assumption says that `n` divides every natural number. The useful special
case is the smallest positive natural number, `m = 1`: if `n` divides `1`,
then `n` cannot be larger than `1`.

```litex
prop dvdN(a N, b N):
    a >= 1
    exist c N st {b = a * c}

know:
    forall a, b N:
        $dvdN(a, b)
        b > 0
        =>:
            a <= b

claim:
    prove:
        forall n N:
            forall m N:
                $dvdN(n, m)
            =>:
                n = 1
    $dvdN(n, 1)
    1 > 0
    n <= 1
    n >= 1
    n = 1
```

Inside the proof, `$dvdN(n, 1)` is obtained by matching the known hypothesis

```text
forall m N:
    $dvdN(n, m)
```

with the concrete value `m = 1`. The outer statement `forall n N:` also gives
the domain fact `n $in N`, so the proposition `$dvdN(n, 1)` is well-formed.
The `know` block records a divisibility fact proved earlier. It gives
`n <= 1`, while the definition of `$dvdN` includes `a >= 1`, so `$dvdN(n, 1)`
also gives `n >= 1`.
Together these two inequalities force `n = 1`.

### 4.1.3

Problem: Let `a` and `b` be real numbers and suppose that every real number `x`
is either at least `a` or at most `b`. Show that `a <= b`.

Here we use the universal hypothesis at the midpoint `x = (a + b) / 2`. That
produces an `or` statement, and `by cases` lets us finish the proof in the two
possible branches.

```litex
claim:
    prove:
        forall a, b R:
            forall x R:
                x >= a or x <= b
            =>:
                a <= b
    (a + b) / 2 >= a or (a + b) / 2 <= b
    by cases a <= b:
        case (a + b) / 2 >= a:
            b = 2 * ((a + b) / 2) - a >= 2 * a - a = a
            a <= b
        case (a + b) / 2 <= b:
            a = 2 * ((a + b) / 2) - b <= 2 * b - b = b
            a <= b
```

In the first branch, the midpoint is at least `a`, so solving the inequality
for `b` gives `b >= a`. In the second branch, the midpoint is at most `b`, so
solving the inequality for `a` gives `a <= b`.

In `by cases a <= b:`, the header is the goal of the case split. The case
labels come from the available `or` fact.

### 4.1.4

Problem: Two real numbers `a` and `b` both have square at most `2`, and each is
greater than or equal to every real number whose square is at most `2`. Prove
that `a = b`.

The two universal hypotheses say that both `a` and `b` are upper bounds for
all real numbers whose square is at most `2`. Since `a^2 <= 2`, the second
universal hypothesis can be applied with `y = a`, giving `a <= b`. Since
`b^2 <= 2`, the first one can be applied with `y = b`, giving `b <= a`.

```litex
know:
    forall a, b R:
        a <= b
        b <= a
        =>:
            a = b

claim:
    prove:
        forall a, b R:
            a^2 <= 2
            b^2 <= 2
            forall y R:
                y^2 <= 2
                =>:
                    y <= a
            forall y R:
                y^2 <= 2
                =>:
                    y <= b
            =>:
                a = b
    a <= b
    b <= a
    a = b
```

The final line uses a small known fact: two real numbers that are both
`<=` each other are equal. The interesting part is not that last step, but how
the two `forall y R` assumptions are instantiated with `y = a` and `y = b`.

### 4.1.5

Problem: Show that there exists a real number `b` such that for every real
number `x`, `b <= x^2 - 2x`.

This is an existence proof whose witness is a whole lower-bound statement. We
choose `b = -1`, and then prove that this chosen value works for every real
number `x`.

```litex
prop lower_bound_for_parabola(b R):
    forall x R:
        b <= x^2 - 2 * x

claim:
    prove:
        exist b R st {$lower_bound_for_parabola(b)}
    witness exist b R st {$lower_bound_for_parabola(b)} from -1:
        forall x R:
            -1 <= -1 + (x - 1)^2 = x^2 - 2 * x
            -1 <= x^2 - 2 * x
```

Inside the `witness` block, the line `forall x R:` proves the universal part
of the proposition `$lower_bound_for_parabola(-1)`. The calculation rewrites
`x^2 - 2x` as `-1 + (x - 1)^2`, which is visibly at least `-1`.

### 4.1.6

Problem: Show that there exists a real number `c` such that for all real
numbers `x` and `y`, if `x^2 + y^2 <= 4`, then `x + y >= c`.

Again we prove an existence statement by choosing a concrete witness. This time
the property of the witness has both universal variables and an implication:
for arbitrary `x` and `y`, assuming `x^2 + y^2 <= 4`, prove the desired lower
bound for `x + y`.

```litex
prop lower_bound_on_disk(c R):
    forall x, y R:
        x^2 + y^2 <= 4
        =>:
            x + y >= c

know:
    forall x, y R:
        x^2 <= y^2
        y >= 0
        =>:
            -y <= x
            x <= y

claim:
    prove:
        exist c R st {$lower_bound_on_disk(c)}
    witness exist c R st {$lower_bound_on_disk(c)} from -3:
        forall x, y R:
            x^2 + y^2 <= 4
            =>:
                (x + y)^2 <= (x + y)^2 + (x - y)^2 = 2 * (x^2 + y^2) <= 2 * 4 = 8 <= 9 = 3^2
                x + y >= -3
```

The calculation shows `(x + y)^2 <= 3^2`. The known fact about squares then
turns that into `x + y >= -3`. This is a typical Litex pattern: write the
estimate you would write on paper, and let the previously stated rule bridge
from the squared inequality to the final inequality.

### 4.1.7

Definition: a property is true for all sufficiently large integers if there is
some threshold `M` such that the property holds for every `n >= M`.

The phrase "for all sufficiently large integers" is naturally an existential
statement: there exists a threshold `M`, and after that point the property
always holds. The proposition below packages the part after a proposed
threshold has been chosen.

```litex
prop cubic_eventually_large(M Z):
    forall n Z:
        n >= M
        =>:
            n^3 >= 4 * n^2 + 7

know:
    forall n Z:
        n >= 5
        =>:
            n^3 >= 4 * n^2 + 7

claim:
    prove:
        exist M Z st {$cubic_eventually_large(M)}
    witness exist M Z st {$cubic_eventually_large(M)} from 5:
        forall n Z:
            n >= 5
            =>:
                n^3 >= 4 * n^2 + 7
```

The proof supplies `M = 5`. The `know` block records the estimate needed after
the threshold is chosen.

### 4.1.8 and 4.1.9

Prime numbers combine a lower bound and a universal implication about divisors:
`p` must be at least `2`, and every divisor of `p` must be either `1` or `p`.
The example `p = 2` is small enough that the divisor condition can be checked
from the general divisibility facts already established.

```litex
prop dvdN(a N, b N):
    a >= 1
    exist c N st {b = a * c}

prop Prime(p N):
    2 <= p
    forall m N:
        $dvdN(m, p)
        =>:
            m = 1 or m = p

know:
    forall a, b N:
        $dvdN(a, b)
        b > 0
        =>:
            a <= b
            a >= 1
    forall m N:
        m <= 2
        m >= 1
        =>:
            m = 1 or m = 2

claim:
    prove:
        $Prime(2)
    2 <= 2
    forall m N:
        $dvdN(m, 2)
        =>:
            0 < 2
            m <= 2
            m >= 1
            m = 1 or m = 2
```

After proving `2 <= 2`, the proof turns to the universal divisor condition.
For an arbitrary natural number `m`, assuming `$dvdN(m, 2)`, the known
divisibility bound gives `m <= 2` and `m >= 1`; the final known fact converts
those two inequalities into `m = 1 or m = 2`.

One syntax point is worth keeping in mind. In a Litex `forall` fact, the
requirements before `=>:` may themselves include `forall` facts, but the facts
after `=>:` should not be `forall` facts. If you want the conclusion to be
universal, move the universally quantified variables into the outer `forall`
header instead. Also, when there are no extra requirements on the arguments
beyond their parameter types, do not write `=>:` at all; just put the conclusion
directly in the body of the `forall`.

## 4.2 “If and Only If”

In Litex, an "if and only if" proof can be unfolded into two separate `claim`s,
one for each direction.

This is intentionally less compact than Lean's `constructor`, but it has a
useful teaching advantage: each direction has its own assumptions and its own
goal, so it is clear which implication is being proved.

### 4.2.1

Problem: Let `a` be a rational number. Show that `3a + 1 <= 7` iff `a <= 2`.

```litex
forall a Q:
    3 * a + 1 <= 7
    =>:
        a = ((3 * a + 1) - 1) / 3 <= (7 - 1) / 3 = 2

forall a Q:
    a <= 2
    =>:
        3 * a + 1 <= 3 * 2 + 1 = 7

forall a Q:
    =>:
        a <= 2
    <=>:
        3 * a + 1 <= 7
```

For a `forall`-level iff fact, put the quantified variables outside:

```text
forall a Q:
    shared_hypothesis
    =>:
        left_fact
    <=>:
        right_fact
```

Read this as: for every rational number `a`, `left_fact` and `right_fact` are
equivalent. The two ordinary implication facts establish the two directions;
the final `forall ... <=>:` line records them as one reusable translation rule.
The same style works for parity:

```text
forall n Z:
    =>:
        $odd(n)
    <=>:
        $mod_eq(n, 1, 2)
```

The Litex layout keeps both the quantifier and the two directions visible.

### 4.2.2

Problem: Let `n` be an integer. Show that `5n` is a multiple of `8` iff `n` is.

```litex
prop dvdZ(a Z, b Z):
    exist c Z st {b = a * c}

claim:
    prove:
        forall n, a Z:
            5 * n = 8 * a
            =>:
                $dvdZ(8, n)
    witness exist c Z st {n = 8 * c} from -3 * a + 2 * n:
        n = -3 * (5 * n) + 16 * n = -3 * (8 * a) + 16 * n = 8 * (-3 * a + 2 * n)

claim:
    prove:
        forall n, a Z:
            n = 8 * a
            =>:
                $dvdZ(8, 5 * n)
    witness exist c Z st {5 * n = 8 * c} from 5 * a:
        5 * n = 5 * (8 * a) = 8 * (5 * a)
```

### 4.2.3 and 4.2.4

Problem: characterize oddness and evenness by congruence modulo `2`.

```litex
prop odd(a Z):
    exist k Z st {a = 2 * k + 1}

prop even(a Z):
    exist k Z st {a = 2 * k}

prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}

claim:
    prove:
        forall n Z:
            $odd(n)
            =>:
                $mod_eq(n, 1, 2)
    have by exist k Z st {n = 2 * k + 1}: k
    witness exist c Z st {n - 1 = 2 * c} from k:
        n - 1 = 2 * k + 1 - 1 = 2 * k

claim:
    prove:
        forall n Z:
            $mod_eq(n, 1, 2)
            =>:
                $odd(n)
    have by exist k Z st {n - 1 = 2 * k}: k
    witness exist c Z st {n = 2 * c + 1} from k:
        n = n - 1 + 1 = 2 * k + 1

claim:
    prove:
        forall n Z:
            $even(n)
            =>:
                $mod_eq(n, 0, 2)
    have by exist k Z st {n = 2 * k}: k
    witness exist c Z st {n - 0 = 2 * c} from k:
        n - 0 = n = 2 * k

claim:
    prove:
        forall n Z:
            $mod_eq(n, 0, 2)
            =>:
                $even(n)
    have by exist k Z st {n - 0 = 2 * k}: k
    witness exist c Z st {n = 2 * c} from k:
        n = n - 0 = 2 * k
```

### 4.2.5 and 4.2.6

Solving equations is also an iff proof: narrow down all solutions, then check
the listed solutions.

```litex
claim:
    prove:
        forall x R:
            x^2 + x - 6 = 0
            =>:
                x = -3 or x = 2
    (x + 3) * (x - 2) = x^2 + x - 6 = 0
    x + 3 = 0 or x - 2 = 0
    by cases x = -3 or x = 2:
        case x + 3 = 0:
            x = -3
        case x - 2 = 0:
            x = 2

claim:
    prove:
        forall x R:
            x = -3 or x = 2
            =>:
                x^2 + x - 6 = 0
    by cases x^2 + x - 6 = 0:
        case x = -3:
            ...
        case x = 2:
            ...
```

Here `...` is not a placeholder for omitted proof text. In Litex, it is the
special `do_nothing` statement. It tells Litex that no extra proof step is
needed at that point.

In the two cases above, the case assumption is enough. Under `case x = -3`,
Litex checks the goal `x^2 + x - 6 = 0` after substituting `x = -3`, and the
arithmetic identity is immediate. The same happens under `case x = 2`.

### 4.2.7 to 4.2.9

Once an iff theorem is known, use it as a translation rule. Here oddness is
translated to modulo `2`. The `know` block repeats the Chapter 3 modular facts
so the snippet can stand alone.

```litex
prop odd(a Z):
    exist k Z st {a = 2 * k + 1}

prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}

prop mod_eq_trans(a Z, b Z, c Z, n Z):
    $mod_eq(a, c, n)

know:
    forall a Z:
        $odd(a)
        =>:
            $mod_eq(a, 1, 2)
    forall a Z:
        $mod_eq(a, 1, 2)
        =>:
            $odd(a)
    forall a, n Z:
        =>:
            $mod_eq(a, a, n)
    forall a, b, c, n Z:
        $mod_eq(a, b, n)
        $mod_eq(b, c, n)
        =>:
            $mod_eq_trans(a, b, c, n)
    forall a, b, c, d, n Z:
        $mod_eq(a, b, n)
        $mod_eq(c, d, n)
        =>:
            $mod_eq(a + c, b + d, n)

claim:
    prove:
        forall x, y Z:
            $odd(x)
            $odd(y)
            =>:
                $odd(x + y + 1)
    $mod_eq(x, 1, 2)
    $mod_eq(y, 1, 2)
    $mod_eq(x + y, 1 + 1, 2)
    $mod_eq(1, 1, 2)
    $mod_eq(x + y + 1, 1 + 1 + 1, 2)
    witness exist k Z st {1 + 1 + 1 - 1 = 2 * k} from 1:
        1 + 1 + 1 - 1 = 2 * 1
    $mod_eq(1 + 1 + 1, 1, 2)
    $mod_eq_trans(x + y + 1, 1 + 1 + 1, 1, 2)
    $mod_eq(x + y + 1, 1, 2)
    $odd(x + y + 1)
```

## 4.3 “There Exists a Unique”

In Litex, uniqueness can be unfolded into two steps: first give a witness for
existence, then prove that any object satisfying the same condition must equal
that witness.

This chapter uses that unfolded form instead of trying to hide the work behind
a single symbol. It mirrors the paper proof: "this object works" and "nothing
else works."

### 4.3.1

Problem: Show that there exists a unique real number `a` such that `3a + 1 = 7`.

```litex
witness exist a R st {3 * a + 1 = 7} from 2

forall a R:
    3 * a + 1 = 7
    =>:
        a = (3 * a + 1 - 1) / 3 = (7 - 1) / 3 = 2

exist! a R st {3 * a + 1 = 7}
```

The final `exist!` line uses the two facts just proved: a witness exists, and
any value satisfying the same equation must equal that witness.

### 4.3.2 to 4.3.4

For more complex uniqueness proofs, split the work into small claims:
existence, uniqueness, and any estimate lemmas needed along the way.

```litex
prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}

prop remainder_property(r Z):
    0 <= r
    r < 5
    $mod_eq(14, r, 5)

know:
    forall r Z:
        $remainder_property(r)
        =>:
            r = 4

claim:
    prove:
        exist r Z st {$remainder_property(r)}
    witness exist r Z st {$remainder_property(r)} from 4:
        0 <= 4
        4 < 5
        witness exist k Z st {14 - 4 = 5 * k} from 2:
            14 - 4 = 5 * 2
        $mod_eq(14, 4, 5)

claim:
    prove:
        forall r Z:
            $remainder_property(r)
            =>:
                r = 4
    r = 4
```

## 4.4 Contradictory Hypotheses

When hypotheses contradict each other, the case is impossible.

The statement `impossible F` has a precise meaning in Litex. It asks Litex to
check that both `F` and the reverse of `F` are true in the current local context.
For example, if Litex knows both `x * y <= 0` and `0 < x * y`, then
`impossible x * y <= 0` closes the branch.

This same rule is used inside `by cases` and `by contra`. A case branch may add
one side of the contradiction, while earlier hypotheses prove the other side.
In a `by contra` block, Litex first assumes the reverse of the goal being
proved; the proof then derives an `impossible` fact from that temporary
assumption.

In small examples, the contradiction may be a direct impossible inequality. In
larger examples, the contradiction is usually reached after a case split or a
translation, such as turning a modular statement into a normalized residue.

### 4.4.1

Problem: Let `x` and `y` be real numbers, and suppose that `0 < x*y` and
`0 <= x`. Show that `0 < y`.

```litex
claim:
    prove:
        forall x, y R:
            0 < x * y
            0 <= x
            =>:
                0 < y
    by contra:
        prove:
            0 < y
        y <= 0
        x * y <= x * 0 = 0
        impossible x * y <= 0
```

### 4.4.2

Problem: Let `t` be an integer with `t < 3` and `t - 1 = 6`. Show that `t != 13`.

This is the explosion principle: once the hypotheses imply an impossible
numeric fact, the branch is closed.

```litex
claim:
    prove:
        forall t Z:
            t < 3
            t - 1 = 6
            =>:
                t != 13
    by contra t != 13:
        t = 13
        t = 7
        impossible 13 = 7
```

### 4.4.3 to 4.4.5

The modular contradiction and prime-testing examples combine Chapter 3 modular
arithmetic, `by cases`, and `impossible`. They are good exercises after the
basic contradiction pattern is familiar.

These are not new proof forms. They are longer versions of the same pattern:
split into finitely many cases, finish the possible cases directly, and close
the impossible cases by deriving a contradiction.

## 4.5 Proof by Contradiction

### 4.5.1

Problem: Show that it is not true that every real number `x` satisfies
`x^2 >= x`.

To refute a universal statement, provide a counterexample.

```litex
by contra:
    prove:
        not forall x R:
            x^2 >= x
    impossible 0.5^2 >= 0.5
```

In this `by contra` proof, Litex temporarily assumes the reverse of the goal:
`forall x R: x^2 >= x`. From that universal hypothesis, it gets
`0.5^2 >= 0.5`. Direct calculation also gives `not 0.5^2 >= 0.5`, so
`impossible 0.5^2 >= 0.5` closes the contradiction.

### 4.5.2

Problem: Show that `13` is not a multiple of `3`.

The contradiction is that `$dvdN(3, 13)` would force `13 % 3 = 0`, while direct
calculation gives `13 % 3 != 0`.

```litex
prop dvdN(a N, b N):
    exist c N st {b = a * c}

claim:
    prove:
        not $dvdN(3, 13)
    by contra not $dvdN(3, 13):
        have by exist k N st {13 = 3 * k}: a
        witness exist k Z st {13 = 3 * k + 0} from a
        impossible 13 % 3 = 0
```

The witness line writes `13 = 3 * k + 0` on purpose. The builtin modulo facts
match equations in the form `a = m * r + k`, where the last term is the
remainder. To match the remainder with `0`, the equation must include the final
`+ 0`; writing only `13 = 3 * k` does not expose the remainder slot that the
builtin rule expects.

```litex
forall a Z, m N_pos, k N:
    a % m = k
    =>:
        exist r Z st {a = m * r + k}

forall a Z, m N_pos, k N:
    k < m
    exist r Z st {a = m * r + k}
    =>:
        a % m = k
```

### 4.5.3

Problem: Let `x` and `y` be real numbers and suppose `x + y = 0`. Show that it
is not possible for both `x` and `y` to be positive.

```litex
claim:
    prove:
        forall x, y R:
            x + y = 0
            =>:
                x <= 0 or y <= 0
    x > 0 or x <= 0
    by cases:
        prove:
            x <= 0 or y <= 0
        case x <= 0:
            x <= 0
        case x > 0:
            y = x + y - x = 0 - x < 0
            y <= 0
```

`x > 0 or x <= 0` is a builtin comparison split: for comparable real
expressions, Litex can use `a > b or a <= b`.

### 4.5.4

Problem: Show that there does not exist a natural number `n` such that
`n^2 = 2`.

```litex
claim:
    prove:
        forall n N:
            =>:
                n^2 != 2
    n <= 1 or n >= 2
    by cases:
        prove:
            n^2 != 2
        case n <= 1:
            n^2 <= 1^2 = 1 < 2
            n^2 != 2
        case n >= 2:
            n^2 >= 2^2 = 4 > 2
            n^2 != 2
```

`n <= 1 or n >= 2` is the integer comparison split. For integers, Litex can use
`n <= m or n >= m + 1`.

### 4.5.5 to 4.5.9

The remaining examples combine earlier tools:

- parity can be reduced to modulo `2` and then handled by cases;
- `n^2` is never congruent to `2` modulo `3`, proved by a residue split;
- a nontrivial factorization proves a number is not prime;
- prime tests reduce to excluding possible middle divisors.

The Litex knowledge point is not a new command, but combining `by cases`,
`by contra`, `witness`, `have by exist`, and the modular facts from Chapter 3.

## 4.6 Litex statements and ideas in this chapter

This chapter revisits the structural proof tools from Chapter 2 in more
logical settings: universal statements, implications, equivalences, uniqueness,
contradictory hypotheses, and refutations.

### Litex statements and syntax used

1. Nested `forall` statements express hypotheses that can later be instantiated
   with concrete values:

   ```text
   forall x R:
       a <= x^2 - 2 * x
   ```

2. Assumptions before `=>:` form the antecedent of an implication. To prove an
   implication, write a `forall` block whose body assumes those facts before
   proving the facts after `=>:`.

3. `prop ...:` packages longer logical properties, such as lower-bound
   statements, primality, or uniqueness-style conditions.

4. `witness exist ... from ...:` proves existence statements whose witnesses
   may themselves have universal or implication properties.

5. `by cases:` uses an available disjunction, comparison split, or finite
   residue split to prove a goal branch by branch.

6. `by contra:` proves a goal by assuming its negation in a temporary local
   context and deriving an `impossible` fact.

7. `not <FACT>` writes negated facts, including negated universal statements
   such as `not forall x R: ...`.

8. `impossible <FACT>` closes a contradiction when the current context also
   proves the opposite or an incompatible fact.

9. `know:` is used to state standard facts needed by a standalone example, such
   as order facts, divisibility bounds, and modular facts.

### Litex knowledge points

1. To use a `forall` fact, write the needed instance as a proof line. Litex
   matches the line against the universal statement and checks the required
   assumptions.

2. An implication is handled by context: assumptions before `=>:` are available
   while proving the conclusion after `=>:`.

3. Existence goals can have rich bodies. A witness block may contain a nested
   `forall` proof or an implication proof, not just a calculation.

4. An `iff` proof can be organized as two implications, one in each direction.

5. A uniqueness proof usually has two parts: first show existence, then show
   that any two objects satisfying the property are equal.

6. Contradictory hypotheses should be isolated inside `by contra` or a case
   branch. The surrounding proof only receives the final proved fact.

7. Refuting universal or existential statements often means choosing a
   counterexample or showing that any proposed witness leads to an impossible
   fact.

8. Later proofs can combine earlier chapters' tools freely: proposition
   definitions from Chapter 3, witness extraction, modular cases, comparison
   splits, and contradiction all work inside the same context-growing proof
   model.
