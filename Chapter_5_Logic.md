# Chapter 5 — Logic

Online: https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Chapter_5_Logic

GitHub source: https://github.com/litexlang/The-Mechanics-of-Litex-Proof/blob/main/Chapter_5_Logic.md

Chapters 2 and 4 introduced the grammar of logical symbols such as `and`,
`or`, `forall`, and `=>` in concrete mathematical proofs. This chapter looks at
the logical patterns themselves: when two statement forms can always be
converted into each other, and how negation can be pushed inward.

There is one important difference from the Lean chapter. Lean can quantify over
abstract propositions:

```text
forall P Prop, Q Prop:
    P
    =>:
        P or Q
```

Litex does not have this form. A proposition is not an object that can be passed
as a parameter to `forall`, `exist`, or `prop`. So we do not write `forall P
Prop:` or `exist P Prop:` in Litex.

This is intentional. Basic propositional reasoning is built into Litex's fact
checker. If Litex already knows a fact `A`, then `A or B` can be verified
directly because the left branch holds; there is no need to prove or cite a
separate theorem saying "from `A`, infer `A or B`." Similarly, `and`, `or`,
case splits, and contradictions are handled as ordinary fact shapes.

This reflects a design choice. Lean starts from a very abstract foundation;
Litex takes more mathematical infrastructure as built in: numbers such as
`1234`, standard sets such as `N` and `R`, and basic logical rules are part of
the language. The goal is that users write the mathematical facts they want to
check, instead of first turning logic itself into data.

When this chapter needs schematic propositions, we use `abstract_prop` names.
For pure propositional patterns, the names can have no parameters:

```litex
abstract_prop p()
abstract_prop q()
abstract_prop r()
```

The names are not important. Any `abstract_prop` or ordinary `prop` with the
same arity would do; these names only give Litex facts such as `$p()` and
`$q()` to manipulate.


## 5.1 Logical Equivalence

### 5.1.1

These examples show logical patterns using proposition names with no
parameters. They are not meant to prove a special mathematical theorem; they
show how Litex handles `or`, `not`, and implication-shaped facts.

If P ∨ Q and ¬ Q, then P.

```litex
abstract_prop p()
abstract_prop q()

claim:
    prove:
        forall:
            $p() or $q()
            not $q()
            =>:
                $p()
    by cases:
        prove:
            $p()
        case $p():
            ...
        case $q():
            impossible not $q()
```

P implies P ∨ (not Q).

```litex
abstract_prop p()
abstract_prop q()

forall:
    $p()
    =>:
        $p() or not $q()
```

### 5.1.2/5.1.3

Truth tables are a paper-and-pencil way to check a propositional pattern.
Assign truth values to the basic propositions first, then evaluate the compound
formula from the inside out.

For example, to analyze `not (P and not Q)`, first decide the values of `P` and
`Q`, then `not Q`, then `P and not Q`, and finally its negation. Litex does not
need a special truth-table command for the proofs below; the same logical rules
are already built into the checker. Truth tables are still useful as a quick
human sanity check before writing the proof.

Exercise: make the truth table for `P <=> (not P or Q)`. The important question
is not the notation, but whether the two sides have the same truth value on
every row.

### 5.1.4

Two formulas are logically equivalent when each one implies the other. In
Litex, we usually write the two directions explicitly.

Here is the equivalence between `P or P` and `P`. The direction from `P` to
`P or P` is immediate. The other direction is a case split, but both cases are
the same.

```litex
abstract_prop p()

claim:
    prove:
        forall:
            $p()
            =>:
                $p() or $p()
    $p()

claim:
    prove:
        forall:
            $p() or $p()
            =>:
                $p()
    by cases $p():
        case $p():
            ...
        case $p():
            ...
```

### 5.1.5

Now we prove the distributive law: `P and (Q or R)` is logically equivalent to
`(P and Q) or (P and R)`.

Litex does not treat a compound proposition like `P and (Q or R)` as an object
that can be passed around. So, when we want to talk schematically, we name the
compound pieces with small `prop` definitions. This keeps the proof readable
while still showing the logical work.

The first direction splits on `Q or R`. The reverse direction splits on whether
we have `P and Q` or `P and R`.

```litex
abstract_prop p()
abstract_prop q()
abstract_prop r()

prop q_or_r():
    $q() or $r()

prop p_and_q():
    $p()
    $q()

prop p_and_r():
    $p()
    $r()

claim:
    prove:
        forall:
            $p()
            $q_or_r()
            =>:
                $p_and_q() or $p_and_r()
    by cases:
        prove:
            $p_and_q() or $p_and_r()
        case $q():
            $p_and_q()
        case $r():
            $p_and_r()

claim:
    prove:
        forall:
            $p_and_q() or $p_and_r()
            =>:
                $p()
                $q_or_r()
    by cases:
        prove:
            $p()
        case $p_and_q():
            $p()
        case $p_and_r():
            $p()
    by cases:
        prove:
            $q_or_r()
        case $p_and_q():
            $q()
            $q_or_r()
        case $p_and_r():
            $r()
            $q_or_r()
```

### 5.1.6

The same idea works for predicates. If `P(x)` holds for every integer `x`, and
`Q(x)` holds for every integer `x`, then for any particular integer `a`, both
`P(a)` and `Q(a)` hold.

```litex
abstract_prop p(x)
abstract_prop q(x)

claim:
    prove:
        forall a Z:
            forall x Z:
                =>:
                    $p(x)
            forall x Z:
                =>:
                    $q(x)
            =>:
                $p(a) and $q(a)
    $p(a)
    $q(a)
    $p(a) and $q(a)
```

Next, suppose there is one integer `x` that works for every integer `y`. Then,
for each chosen `y`, there exists an `x` that works for that `y`: use the same
witness.

There is a small Litex-specific point here. A `forall` fact cannot appear after
the `=>:` as the conclusion of another `forall` fact. So instead of writing the
goal as one nested statement, we move the later universal variable `y` to the
top level.

```litex
abstract_prop pxy(x, y)

prop p_for_all_y(x Z):
    forall y Z:
        $pxy(x, y)

claim:
    prove:
        forall y Z:
            exist x Z st {$p_for_all_y(x)}
            =>:
                exist x Z st {$pxy(x, y)}
    have by exist x Z st {$p_for_all_y(x)}: x0
    witness exist x Z st {$pxy(x, y)} from x0:
        $pxy(x0, y)
```

Finally, here is the common equivalence between "there is no `x` satisfying
`P(x)`" and "every `x` fails to satisfy `P(x)`." We again name the existential
statement with a small `prop`, because `not exist ...` is harder to use directly
inside every proof shape.

```litex
abstract_prop p(x)

prop some_p():
    exist x Z st {$p(x)}

claim:
    prove:
        forall a Z:
            not $some_p()
            =>:
                not $p(a)
    by contra not $p(a):
        witness exist x Z st {$p(x)} from a:
            $p(a)
        $some_p()
        impossible $some_p()

claim:
    prove:
        forall:
            forall x Z:
                not $p(x)
            =>:
                not $some_p()
    by contra not $some_p():
        have by exist x Z st {$p(x)}: x0
        not $p(x0)
        impossible $p(x0)
```

## 5.2 The Law Of The Excluded Middle

This section uses one new Litex statement: `by for`. It proves a `forall`
statement over a finite range by checking each value in that range. The range
`range(a, b)` means the integers from `a` up to but not including `b`.
The range `closed_range(a, b)` includes both endpoints, and can also be written
as `a...b`.

The check is literal finite enumeration. For example, `forall i range(2, 17)`
is proved by substituting `i = 2`, then `i = 3`, and so on up to `i = 16`, and
checking the conclusion each time.

Here is the basic shape:

```text
by for:
    prove:
        forall n range(a, b):
            goal_about(n)

by for:
    prove:
        forall n a...b:
            goal_about(n)
```

As a useful example, define primality by saying directly that there are no
divisors between `2` and `x - 1`.

```litex
prop Prime(x N_pos):
    2 <= x
    forall y range(2, x):
        x % y != 0
```

For a concrete number, `by for` proves the bounded universal condition, and
then the definition of `Prime` can be unfolded directly.

```litex
prop Prime(x N_pos):
    2 <= x
    forall y range(2, x):
        x % y != 0

by for:
    prove:
        forall n range(2, 17):
            17 % n != 0

$Prime(17)
```

Now we can use this finite-checking pattern inside the logic problem.

### 5.2.1 to 5.2.4

The original example studies numbers `k` such that `k^(k^n) + 1` is always
prime. In this Litex version, `k` is positive, and primality is the `Prime`
predicate above.

```litex
prop Prime(x N_pos):
    2 <= x
    forall y range(2, x):
        x % y != 0

prop superpowered(k N_pos):
    forall n N_pos:
        $Prime(k ^ (k ^ n) + 1)

by for:
    prove:
        forall n range(2, 2):
            2 % n != 0

$Prime(2)

forall n N_pos:
    1^n = 1
    1^(1^n) + 1 = 1^1 + 1 = 2
    $Prime(1^(1^n) + 1)

$superpowered(1)

by contra not $superpowered(2):
    $Prime(2^(2^5) + 1)
    (2^(2^5) + 1) % 641 = 0
    impossible (2^(2^5) + 1) % 641 = 0

claim:
    prove:
        exist k N_pos st {$superpowered(k) and not $superpowered(k + 1)}
    witness exist k N_pos st {$superpowered(k) and not $superpowered(k + 1)} from 1:
        $superpowered(1)
        not $superpowered(1 + 1)
        $superpowered(1) and not $superpowered(1 + 1)
```

The first `by for` block proves `2` is prime. The identity `1^n = 1` is builtin,
so `$superpowered(1)` follows by reducing `1^(1^n) + 1` to `2`. The proof of
`not $superpowered(2)` uses Euler's factor `641`: if `2` were superpowered, then
`2^(2^5) + 1` would be prime, but it is divisible by `641`. The final claim
packages these two facts into an existential statement.

### 5.2.5

Classically, `not not P` implies `P`. The proof splits into the two cases
`P` and `not P`. In the first case the goal is immediate. In the second case,
`not P` contradicts the assumption `not not P`.

Litex's current checker normalizes this double-negation pattern aggressively,
but the written proof still displays the intended excluded-middle structure.

```litex
abstract_prop p()

claim:
    prove:
        forall:
            not not $p()
            =>:
                $p()
    $p() or not $p()
    by cases:
        prove:
            $p()
        case $p():
            $p()
        case not $p():
            impossible not $p()
```

## 5.3 Normal Forms For Negation

The goal of this section is to push `not` inward until it is attached only to
atomic facts.

The basic rules are:

```text
not not P          becomes  P
not (P or Q)      becomes  (not P) and (not Q)
not (P and Q)     becomes  (not P) or (not Q)
not (P => Q)      becomes  P and (not Q)
not exist x, P x  becomes  forall x, not P x
not forall x, P x becomes  exist x, not P x
not (a < b)       becomes  a >= b
not (a <= b)      becomes  a > b
```

Litex does not have a separate `push_neg` tactic. Write the pushed form
directly, and give compound propositions small `prop` names when that keeps the
statement readable.

### 5.3.1

First, here is De Morgan's law for `or`: `not (P or Q)` is equivalent to
`not P` and `not Q`. We name `P or Q` as `$p_or_q()` so the negation is easy to
write and reuse.

```litex
abstract_prop p()
abstract_prop q()

prop p_or_q():
    $p() or $q()

claim:
    prove:
        forall:
            not $p_or_q()
            =>:
                not $p()
                not $q()
    by contra not $p():
        $p()
        $p_or_q()
        impossible $p_or_q()
    by contra not $q():
        $q()
        $p_or_q()
        impossible $p_or_q()

claim:
    prove:
        forall:
            not $p()
            not $q()
            =>:
                not $p_or_q()
    by contra not $p_or_q():
        $p_or_q()
        by cases:
            prove:
                $p()
            case $p():
                $p()
            case $q():
                impossible $q()
        impossible $p()
```

Next, `not (P and Q)` is equivalent to `not P or not Q`. One direction is
constructive: if either `not P` or `not Q` is known, then `P and Q` is
impossible. The other direction uses excluded middle: split on whether `P` is
true.

```litex
abstract_prop p()
abstract_prop q()

prop p_and_q():
    $p()
    $q()

claim:
    prove:
        forall:
            not $p() or not $q()
            =>:
                not $p_and_q()
    by cases:
        prove:
            not $p_and_q()
        case not $p():
            by contra not $p_and_q():
                impossible $p()
        case not $q():
            by contra not $p_and_q():
                impossible $q()

claim:
    prove:
        forall:
            not $p_and_q()
            =>:
                not $p() or not $q()
    $p() or not $p()
    by cases:
        prove:
            not $p() or not $q()
        case not $p():
            not $p() or not $q()
        case $p():
            by contra not $q():
                $p_and_q()
                impossible $p_and_q()
            not $p() or not $q()
```

Finally, here is the existential rule from Section 5.1 again. Naming the
existential statement as `$some_p()` makes both directions straightforward.

```litex
abstract_prop p(x)

prop some_p():
    exist x Z st {$p(x)}

claim:
    prove:
        forall a Z:
            not $some_p()
            =>:
                not $p(a)
    by contra not $p(a):
        witness exist x Z st {$p(x)} from a:
            $p(a)
        $some_p()
        impossible $some_p()

claim:
    prove:
        forall:
            forall x Z:
                not $p(x)
            =>:
                not $some_p()
    by contra not $some_p():
        have by exist x Z st {$p(x)}: x0
        not $p(x0)
        impossible $p(x0)
```

### 5.3.2

Now push the negation through a more structured statement:

```text
not (forall m Z, m != 2 => exist n Z, n^2 = m)
```

The negation says that there is a counterexample `m`: it is not equal to `2`,
and no integer square is equal to it. In normal form:

```text
exist m Z such that m != 2 and forall n Z, n^2 != m
```

In Litex, it is clearer to name the pieces.

```litex
prop every_non_two_is_square():
    forall m Z:
        m != 2
        =>:
            exist n Z st {n^2 = m}

prop no_square_for(m Z):
    forall n Z:
        n^2 != m

prop counterexample_to_every_non_two_is_square():
    exist m Z st {m != 2, $no_square_for(m)}
```

### 5.3.3

Here is another push-negation example:

```text
not (forall n N, exist m N with n^2 < m and m < (n + 1)^2)
```

After pushing the negation inward, this becomes:

```text
exist n N such that forall m N, n^2 >= m or m >= (n + 1)^2
```

The strict inequalities turn around because `not (a < b)` is the same as
`a >= b`.

```litex
prop gap_property(n N, m N):
    n^2 < m
    m < (n + 1)^2

prop every_n_has_gap_point():
    forall n N:
        exist m N st {$gap_property(n, m)}

prop no_gap_point_for(n N):
    forall m N:
        n^2 >= m or m >= (n + 1)^2

prop counterexample_to_every_gap():
    exist n N st {$no_gap_point_for(n)}
```

### 5.3.4

A `push_neg` command in a tactic-based system repeatedly applies the rules at
the top of this section. In Litex, the normal workflow is to write the pushed
form yourself.

For example:

```text
not exist a Z such that P(a) or forall b Z, not Q(a, b)
```

pushes to:

```text
forall a Z, not P(a) and exist b Z such that Q(a, b)
```

Naming the compound subformulas keeps the statement readable.

```litex
abstract_prop p(a)
abstract_prop q(a, b)

prop all_not_q(a Z):
    forall b Z:
        not $q(a, b)

prop has_p_or_all_not_q(a Z):
    $p(a) or $all_not_q(a)

prop original_exists():
    exist a Z st {$has_p_or_all_not_q(a)}

prop pushed_neg():
    forall a Z:
        not $p(a)
        exist b Z st {$q(a, b)}
```

### 5.3.5

As an application, there is no natural number whose square is `2`. First prove
the pointwise statement `forall n N, n^2 != 2`; then use it to rule out an
existential witness.

```litex
prop square_two_exists():
    exist n N st {n^2 = 2}

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

claim:
    prove:
        not $square_two_exists()
    by contra not $square_two_exists():
        have by exist n N st {n^2 = 2}: w
        w^2 != 2
        impossible w^2 = 2
```

## 5.4 Litex statements and ideas in this chapter

This chapter separates logical patterns from the particular mathematical facts
that instantiate them.

1. Litex does not quantify over `Prop`. Use `abstract_prop` (without specific meanings) or small `prop` (with specific meanings)
   definitions to name schematic facts, then prove the logical pattern on those
   facts.

2. Basic propositional moves are built in. If `A` is known, then `A or B` can be
   checked directly; if both a fact and its reverse are known, `impossible`
   closes the branch.

3. Logical equivalence is usually written as two directions. For compound
   statements, naming subformulas with `prop` often makes the proof clearer than
   trying to write one large formula everywhere.

4. `by for` proves a `forall` statement over a finite range by checking all
   values. This is useful for bounded arithmetic tasks such as checking a
   concrete number is prime.

5. Negation normal form is a writing discipline: push `not` inward by hand, and
   use `by contra`, `by cases`, `witness`, and `have by exist` to justify the
   transformed statement.
