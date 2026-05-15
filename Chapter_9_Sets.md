# Chapter 9 — Sets

Try all snippets in browser: https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Chapter_9_Sets

GitHub source: https://github.com/litexlang/The-Mechanics-of-Litex-Proof/blob/main/Chapter_9_Sets.md

This chapter is where Litex's set-theoretic design becomes especially visible.
In Litex, sets are ordinary mathematical objects. Membership is written directly
with `$in`, subsets are written with `$subset`, set-builder notation is part of
the language, and power sets are ordinary objects too.

A set can be
an element of another set, because a set is also an object. Nested membership is
therefore written in the same language as ordinary membership:

```litex
{1, 2} $in {{}, {1, 2}}
{{3}} $in {{{3}}}
```

This does not mean that every membership claim is true. It means the expression
is mathematically well-formed at the surface level. Litex can then verify or
refute it from definitions, known facts, and builtin set rules. The proof script
spends less effort on representation and more effort on the mathematical reason.

> In Litex, there is no visible hierarchy that forces the user to keep separate levels for objects, sets of objects, sets of sets, which Lean requires. The existence of this hierarchy is a principled design choice of Lean, making it extremely simple at its implementation level, but it also means that the user has to keep track of the exact hierarchy level for each membership claim. It also requires the user to learn the PhD-level mathematical type theory before being able to use Lean.

## 9.1 Membership

### 9.1.1 Membership In A Set Builder

A set-builder expression describes the objects satisfying a condition. To prove
membership, prove the defining condition:

```litex
1 $in {n Z : n <= 3}
```

The set builder `{n Z : n <= 3}` means "the set of integers `n` such that
`n <= 3`." A membership claim of the form `xxx $in {n Z : condition}` is checked
by substituting `xxx` for the free variable `n` in the condition, then verifying
the resulting fact. In the example above, Litex checks `1 <= 3`.

Litex does not ask the user to unfold an encoding before writing the membership
fact.

Finite displayed sets behave the same way:

```litex
2 $in {1, 2, 3}
not 4 $in {1, 2, 3}
```

`x $in {1, 2, 3}` is equivalent to `x = 1 or x = 2 or x = 3`.

```litex
forall a {1, 2, 3}:
    a = 1 or a = 2 or a = 3
```

```litex
forall a R:
    a = 1 or a = 2 or a = 3
    =>:
        a $in {1, 2, 3}
```

When an object belongs to a finite displayed set, Litex can use the finite list of possibilities. The command `by enumerate finite_set` is for this kind of
finite-domain universal proof: it takes a `forall` statement whose parameters
range over displayed finite sets, then checks the goal by enumerating each
possible value. 

In the next example, Litex proves the statement by checking the three cases
`x = 1`, `x = 3`, and `x = 6`:

```litex
by enumerate finite_set:
    prove:
        forall x {1, 3, 6}:
            x < 10
```

Then `forall x {1, 3, 6}: x < 10` is proved by checking the three cases.

### 9.1.2 Nonmembership In A Set Builder

Nonmembership is written with `not ... $in ...`. For a set builder, Litex reads
this as the negation of the defining condition after substitution.

```text
prop odd(a N):
    exist k N st {a = 2 * k + 1}

by contra not 10 $in {n N : $odd(n)}:
    $odd(10)
    have by exist k N st {10 = 2 * k + 1}: k
    k = (10 - 1) / 2 = 4.5
    impossible 4.5 $in N
```

The important pattern is simple: prove the negation of the condition defining
the set.

### 9.1.3 Subset As A Membership Implication

To prove a subset statement, prove the corresponding membership implication:
take an arbitrary element of the left-hand set and show that it belongs to the
right-hand set.

For multiples, the proof is just a witness calculation.

```text
prop dvdN(a N, b N):
    a >= 1
    exist c N st {b = a * c}

claim:
    prove:
        forall a {x N: $dvdN(4, x)}:
            a $in {x N: $dvdN(2, x)}
    have by exist k N st {a = 4 * k}: k
    witness exist l N st {a = 2 * l} from 2 * k:
        a = 4 * k = 2 * (2 * k)

{x N: $dvdN(4, x)} $subset {x N: $dvdN(2, x)}
```

`subset` is a builtin predicate. `a $subset b` can be verified by `forall! x a => {x $in b}`.

### 9.1.4 Not A Subset

To prove that one set is not a subset of another, give a counterexample: an
object which is in the first set but not in the second.

For example, every real number has a nonnegative square, but not every real
number is nonnegative. The witness `-1` proves the failure of subset.

```litex
by contra not {x R: 0 <= x^2} $subset {x R: 0 <= x}:
    -1 $in {x R: 0 <= x}
    impossible -1 < 0
```

The set-theoretic idea is the usual one: one counterexample is enough.

### 9.1.5 Equality Of Set Builders

Set equality is extensional. To prove two set builders equal, prove that their
membership conditions are equivalent.

The command `by extension` is named after the axiom of extensionality in set
theory: two sets are equal exactly when they have the same elements. So for a
goal

```text
A = B
```

`by extension` checks the two membership directions

```text
forall x A:
    x $in B

forall x B:
    x $in A
```

Equivalently, it verifies that every element of the left set belongs to the
right set, and every element of the right set belongs to the left set.

The odd integers can be described in either of these two ways:

```text
{x Z : $odd(x)}
{a Z : exist k Z st {a = 2 * k - 1}}
```

The proof is two witness transformations:

```text
if x = 2 * l + 1, then x = 2 * (l + 1) - 1
if x = 2 * k - 1, then x = 2 * (k - 1) + 1
```

In Litex style, those two calculations become the two directions of the
membership proof.

```text
prop odd(a Z):
    exist k Z st {a = 2 * k + 1}

prop odd2(a Z):
    exist k Z st {a = 2 * k - 1}

by extension:
    prove:
        {x Z : $odd(x)} = {a Z : $odd2(a)}

    claim:
        prove:
            forall x Z:
                $odd(x)
                =>:
                    $odd2(x)
        have by exist l Z st {x = 2 * l + 1}: l
        witness exist k Z st {x = 2 * k - 1} from l + 1:
            x = 2 * l + 1 = 2 * (l + 1) - 1

    claim:
        prove:
            forall x Z:
                $odd2(x)
                =>:
                    $odd(x)
        have by exist l Z st {x = 2 * l - 1}: l
        witness exist k Z st {x = 2 * k + 1} from l - 1:
            x = 2 * l - 1 = 2 * (l - 1) + 1
```

For set builders, membership in the set builder is unfolded into the defining
condition. In the example above, `x $in {x Z : $odd(x)}` becomes `$odd(x)`, and
`x $in {a Z : $odd2(a)}` becomes `$odd2(x)`. So the two `claim` blocks prove
exactly the two membership directions that `by extension` needs.



### 9.1.6 Inequality Of Sets

To prove two sets are not equal, find an element that separates them. The sets
of multiples of `4` and multiples of `2` are not equal because `6` is a multiple
of `2`, but not a multiple of `4`.

```litex
by contra {a N: a % 4 = 0} != {a N: a % 2 = 0}:
    2 $in {a N: a % 2 = 0}
    2 $in {a N: a % 4 = 0}
    impossible 2 % 4 = 0
```

This is the same extensional principle used negatively: unequal membership
behavior proves unequal sets.

Lean Example:

```Lean
example : {a : ℕ | 4 ∣ a} ≠ {b : ℕ | 2 ∣ b} := by
  ext
  dsimp
  push_neg
  use 6
  right
  constructor
  · apply Nat.not_dvd_of_exists_lt_and_lt
    use 1
    constructor <;> numbers
  · use 3
    numbers
```

### 9.1.7 A Set Equality From A Divisibility Calculation

Some set equalities are disguised algebra. The sets

```text
{k Z : $dvdZ(8, 5 * k)}
{l Z : $dvdZ(8, l)}
```

are equal because `8 | 5n` if and only if `8 | n`.

The hard direction uses the identity

```text
n = -3 * (5 * n) + 16 * n.
```

If `5n = 8a`, then

```text
n = -3 * (8 * a) + 16 * n
  = 8 * (-3 * a + 2 * n),
```

so `8 | n`. The other direction is direct: if `n = 8a`, then
`5n = 8 * (5a)`.

```litex
prop multiple8(x Z):
    exist a Z st {x = 8 * a}

claim:
    prove:
        forall x Z:
            $multiple8(5 * x)
            =>:
                $multiple8(x)
    have by exist a Z st {5 * x = 8 * a}: b
    witness exist c Z st {x = 8 * c} from 5 * b - 3 * x:
        x = 25 * x - 24 * x = 5 * (5 * x) - 3 * (8 * x) = 5 * (8 * b) - 3 * (8 * x) = 8 * (5 * b - 3 * x)

claim:
    prove:
        forall x Z:
            $multiple8(x)
            =>:
                $multiple8(5 * x)
    have by exist a Z st {x = 8 * a}: b
    witness exist c Z st {5 * x = 8 * c} from 5 * b:
        5 * x = 5 * (8 * b) = 8 * (5 * b)

```

### 9.1.8 Finite Sets As Listed Alternatives


```litex
by extension:
    prove:
        {-1, 2} = {x R: x^2 - x - 2 = 0}

    claim:
        prove:
            forall a {x R: x^2 - x - 2 = 0}:
                a $in {-1, 2}

        (a - 2) * (a + 1) = a^2 - a - 2 = 0
        a - 2 = 0 or a + 1 = 0

        by cases a $in {-1, 2}:
            case a - 2 = 0:
                a = 2
            case a + 1 = 0:
                a = -1

    claim:
        prove:
            forall a {-1, 2}:
                a $in {x R: x^2 - x - 2 = 0}

        by cases a $in {x R: x^2 - x - 2 = 0}:
            case a = -1:
                ...
            case a = 2:
                ...

```

Lean Example as comparison:

```Lean
example : {x : ℝ | x ^ 2 - x - 2 = 0} = {-1, 2} := by
  ext x
  dsimp
  constructor
  · intro h
    have hx :=
    calc
      (x + 1) * (x - 2) = x ^ 2 - x - 2 := by ring
        _ = 0 := by rw [h]
    rw [mul_eq_zero] at hx
    obtain hx | hx := hx
    · left
      addarith [hx]
    · right
      addarith [hx]
  · intro h
    obtain h | h := h
    · calc x ^ 2 - x - 2 = (-1) ^ 2 - (-1) - 2 := by rw [h]
        _ = 0 := by numbers
    · calc x ^ 2 - x - 2 = 2 ^ 2 - 2 - 2 := by rw [h]
        _ = 0 := by numbers
```

9.1.9. Example

```litex
by enumerate finite_set:
    prove:
        forall t {1, 3, 6}:
            t $in {x Q: x < 10}

{1, 3, 6} $subset {x Q: x < 10}
```

Lean Example as comparison:

```Lean
example : {1, 3, 6} ⊆ {t : ℚ | t < 10} := by
  dsimp [Set.subset_def]
  intro t ht
  obtain h1 | h3 | h6 := ht
  · addarith [h1]
  · addarith [h3]
  · addarith [h6]
```

## 9.2 Set Operations

Set operations build new sets from old ones. The basic membership rules are the
mathematics:

- `x` is in `A union B` exactly when `x` is in `A` or `x` is in `B`.
- `x` is in `A intersect B` exactly when `x` is in both `A` and `B`.
- `x` is in `set_minus(A, B)` exactly when `x` is in `A` and not in `B`.

The examples below are written as ordinary mathematical arguments. They are
intended to make the set-theoretic reason clear; the Litex code can then follow
the same membership-by-membership structure.

### 9.2.1 Example

The first example is a union of two intervals:

```text
union({x R : x < 0}, {x R : x > 0}) = {x R : x != 0}
```

The proof is just the trichotomy of real numbers around `0`. Since `forall! x, y R => {x < y or x = y or x > y}` we can prove `x != 0` by `x < 0 or x > 0`.

```litex
by extension:
    prove:
        union({x R: x < 0}, {x R: x > 0}) = {x R: x != 0}

    claim:
        prove:
            forall y {x R: x != 0}:
                y $in union({x R: x < 0}, {x R: x > 0})

        by cases y $in union({x R: x < 0}, {x R: x > 0}):
            case y < 0:
                y $in {x R: x < 0}
            case y = 0:
                impossible y != 0
            case y > 0:
                y $in {x R: x > 0}

    claim:
        prove:
            forall y union({x R: x < 0}, {x R: x > 0}):
                y $in {x R: x != 0}

        by cases y $in {x R: x != 0}:
            case y $in {x R: x < 0}:
                ...
            case y $in {x R: x > 0}:
                ...
```

This example is the basic pattern for union proofs: one direction splits the
union assumption into cases, and the other direction proves that the target
condition lands in at least one of the two sets.

### 9.2.2 Example

Finite displayed unions reduce to finite alternatives. The typical statement is

```text
{1, 2} union {2, 4} = {1, 2, 4}.
```

If `x` is in the union, then either `x = 1 or x = 2`, or `x = 2 or x = 4`.
So the possible values of `x` are exactly `1`, `2`, and `4`.

Conversely, if `x` is in `{1, 2, 4}`, split into the three cases. The cases
`x = 1` and `x = 2` put `x` in `{1, 2}`; the case `x = 4` puts `x` in
`{2, 4}`. Hence `x` is in the union. Notice that the repeated element `2`
appears only once in the final displayed set.

```litex
by extension union({1, 2}, {2, 4}) = {1, 2, 4}:
    claim forall! x union({1, 2}, {2, 4}) => {x $in {1, 2, 4}}:
        by cases x $in {1, 2, 4}:
            case x $in {1, 2}:
                by cases x $in {1, 2, 4}:
                    case x = 1:
                        ...
                    case x = 2:
                        ...
            case x $in {2, 4}:
                by cases x $in {1, 2, 4}:
                    case x = 2:
                        ...
                    case x = 4:
                        ...

    claim forall! x {1, 2, 4} => {x $in union({1, 2}, {2, 4})}:
        by cases x $in union({1, 2}, {2, 4}):
            case x = 1:
                ...
            case x = 2:
                ...
            case x = 4:
                ...
```

Use `by enumerate finite_set` instead of `by cases`

```litex
by extension union({1, 2}, {2, 4}) = {1, 2, 4}:
    claim forall! x union({1, 2}, {2, 4}) => {x $in {1, 2, 4}}:
        by cases x $in {1, 2, 4}:
            case x $in {1, 2}:
                by enumerate finite_set:
                    prove:
                        forall a {1, 2}:
                            a $in {1, 2, 4}
            case x $in {2, 4}:
                by enumerate finite_set:
                    prove:
                        forall b {2, 4}:
                            b $in {1, 2, 4}

    by enumerate finite_set:
        prove:
            forall x {1, 2, 4}:
                x $in union({1, 2}, {2, 4})
```

**`by enumerate finite_set`.** When the objects you must handle already live in a
**displayed list set** such as `{1, 2, 4}`, this form is especially handy: Litex
**enumerates the listed elements one by one** and asks you to prove the goal for
each. That matches the mathematical picture (“finite roster”), but you avoid
writing a long ladder of nested **`by cases`** just to spell out the same three
alternatives.

Lean Example as comparison:

```Lean
example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  constructor
  · intro h
    obtain (h | h) | (h | h) := h
    · left
      apply h
    · right
      left
      apply h
  -- and much, much more
    · sorry
    · sorry
  · sorry
```

Or use `exhaust` tactic

```Lean
example : {2, 1} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  exhaust
```

> **Lean and Litex (a small contrast).** Lean can stay *conceptually* lightweight in theory: elaborate mathematics is often packaged behind definitions and lemmas with short names, and when a domain feels awkward at first, mature libraries usually fill many of the gaps. Litex takes a different emphasis—it tries to keep the proof script close to ordinary mathematical steps without asking you to memorize a large catalog of situation-specific tactics. Neither story replaces the other; where libraries are still thin, the tactic footprint can matter more for day-to-day proving.

### 9.2.3 Example

Intersections require both membership conditions. A representative example is

```text
{-2, 3} intersect {x Q : x^2 = 9} $subset {a Q : 0 < a}.
```

```litex
claim forall! x intersect({-2, 3}, {y Q: y^2 = 9}) => {x $in {a Q: 0 < a}}:
    x $in {-2, 3}
    by cases x = 3:
        case x = -2:
            x^2 = (-2)^2 = 4
            impossible x^2 = 9
        case x = 3:
            ...

    3 $in {a Q: 0 < a}

intersect({-2, 3}, {y Q: y^2 = 9}) $subset {a Q: 0 < a}
```

This is the standard intersection-subset proof: use one side of the
intersection to get a short list of candidates, and use the other side to
discard the candidates that do not satisfy the target condition.

Lean Example as comparison:

```Lean
example : {-2, 3} ∩ {x : ℚ | x ^ 2 = 9} ⊆ {a : ℚ | 0 < a} := by
  dsimp [Set.subset_def]
  intro t h
  obtain ⟨(h1 | h1), h2⟩ := h
  · have :=
    calc (-2) ^ 2 = t ^ 2 := by rw [h1]
      _ = 9 := by rw [h2]
    numbers at this
  · addarith [h1]
```

### 9.2.4 Example

Bounded integer conditions often collapse to a short finite list. For example,

```text
{n N : 4 <= n} intersect {n N : n < 7} $subset {4, 5, 6}.
```

```litex
claim forall! x intersect({n N: 4 <= n}, {n N: n < 7}) => {x $in {4, 5, 6}}:
    x $in range(4, 7)
    by for:
        prove:
            forall i range(4, 7):
                i $in {4, 5, 6}
    x $in {4, 5, 6}
```

**`by for` on an integer `range`.** Here `range(4, 7)` is the half-open integer
interval `{4, 5, 6}`. A **`by for`** proof over that range is a convenient way to
do exactly what you would do on paper: treat the bounded segment as a finite list
and **check the goal after substituting each value in turn** (`4`, then `5`,
then `6`). Litex automates that bookkeeping instead of writing three separate
cases by hand. That matches the mathematical picture (“finite roster”), but you avoid
writing a long ladder of nested **`by cases`** just to spell out the same alternatives.

Lean Example as comparison:

```Lean
example : {n : ℕ | 4 ≤ n} ∩ {n : ℕ | n < 7} ⊆ {4, 5, 6} := by
  dsimp [Set.subset_def]
  intro n h
  obtain ⟨h1, h2⟩ := h
  interval_cases n <;> exhaust
```

### 9.2.5 Example

Complements turn a membership condition into its negation. In the integer
setting, the complement of the even integers is the set of odd integers:

```text
({k Z : k % 2 = 0})^c = {k Z : k % 2 = 1}.
```

```litex
forall a, b set, x set_minus(a, b):
    x $in a
    not x $in b

by extension set_minus(Z, {n Z: n % 2 = 0}) = {n Z: n % 2 = 1}:
    claim forall! x set_minus(Z, {n Z: n % 2 = 0}) => {x $in {n Z: n % 2 = 1}}:
        x $in Z
        not x $in {n Z: n % 2 = 0}
        x % 2 = 0 or x % 2 = 1
        by cases x % 2 = 1:
            case x % 2 = 0:
                x $in {n Z: n % 2 = 0}
                impossible x $in {n Z: n % 2 = 0}
            case x % 2 = 1:
                do_nothing
    claim forall! x {n Z: n % 2 = 1} => {x $in set_minus(Z, {n Z: n % 2 = 0})}:
        x $in Z
        x % 2 = 1
        by contra not x $in {n Z: n % 2 = 0}:
            x $in {n Z: n % 2 = 0}
            x % 2 = 0
            impossible x % 2 = 1

set_minus(Z, {n Z: n % 2 = 0}) = {n Z: n % 2 = 1}
```

### 9.2.6 Example

The empty set has no elements. A common way to prove that a set equals the empty
set is to show that its membership condition is impossible. For example,

```text
{n N : n < 0} = {}.
```

If `n` belongs to the left-hand set, then `n` is a natural number and `n < 0`.
But natural numbers are nonnegative. This contradiction shows that no object
can be in the left-hand set.

In Litex `{}` is a set with no elements. It is subset of any set.

```litex
claim:
    prove:
        forall s set:
            {} $subset s
    by enumerate finite_set:
        prove:
            forall x {}:
                x $in s
```

Now we prove that the intersection of two sets of numbers that are congruent to 1 and 2 modulo 5 is the empty set.

```litex
claim intersect({n Z: n % 5 = 1}, {n Z: n % 5 = 2}) = {}:
    by contra not $is_nonempty_set(intersect({n Z: n % 5 = 1}, {n Z: n % 5 = 2})):
        have x intersect({n Z: n % 5 = 1}, {n Z: n % 5 = 2})
        x % 5 = 1
        x % 5 = 2
        impossible 1 = 2
```

The line

```text
have x intersect({n Z: n % 5 = 1}, {n Z: n % 5 = 2})
```

is the key move. In general, `have x OBJECT` means that Litex takes one element
from `OBJECT` and names it `x`. This is only legitimate when `OBJECT` is known
to satisfy `$is_nonempty_set(OBJECT)`: in ordinary words, when `OBJECT` is a
nonempty set. Here the surrounding `by contra not $is_nonempty_set(...)` has
temporarily assumed that the intersection is nonempty, so Litex is allowed to
take such an `x`. 

You can also use `have x set`, `have x nonempty_set`, `have x finite_set`, where `set` says `is_set(x)`, `nonempty_set` says `$is_nonempty_set(x)`, `finite_set` says `$is_finite_set(x)`. Notice `set`, `nonempty_set`, and `finite_set` are actions, not objects.

If nonemptiness has not been proved or assumed, Litex cannot take an element
from the set. This is just the usual mathematical rule: you cannot choose an
element from an empty set.

Litex also has the empty-set equivalence built in:

```text
not $is_nonempty_set(OBJECT)    means the same thing as    OBJECT = {}
```

So the proof above can establish equality with `{}` by proving that the set is
not nonempty. This is the familiar mathematical fact that a set is empty exactly
when it has no elements.



### 9.2.7 Example

As you might have noticed, For any set `s`, `s = {x s: 0 = 0}`. Here `0 = 0` is a trivial condition that always holds, which can be replaced with any other condition that always holds.

```litex
claim:
    prove:
        forall s set:
            s = {x s: 0 = 0}
    by extension s = {x s: 0 = 0}:
        ...
```

Here is an exmple of proving that the union of two sets of real numbers is the set of all real numbers.

```litex
by extension union({x R: -1 < x}, {x R: x < 1}) = R:
    claim:
        prove:
            forall a R:
                a $in union({x R: -1 < x}, {x R: x < 1})

        by cases a $in union({x R: -1 < x}, {x R: x < 1}):
            case a < -1:
                a < -1 < 1
                a $in {x R: x < 1}
            case a = -1:
                -1 $in {x R: x < 1}
                a $in {x R: x < 1}
            case a > -1:
                ...

    claim:
        prove:
            forall a union({x R: -1 < x}, {x R: x < 1}):
                a $in R

        by cases a $in R:
            case a $in {x R: -1 < x}:
                ...
            case a $in {x R: x < 1}:
                ...
```

## 9.3 Power Sets

The power set `power_set(A)` is the set of all subsets of `A`. Thus

```text
B $in power_set(A)
```

means the same mathematical thing as

```text
B $subset A.
```

For example,

```litex
{3, 4, 5} $in power_set(R)
{n N: 8 < n} $in power_set(N)
```

So proofs about power sets usually reduce to subset proofs: take an arbitrary
element of the proposed subset and show that it lies in the base set.

### 9.3.2 Example

We show that `{n N: n % 2 = 0}` is not an element of `{s power_set(N): 3 $in s}`, which is equivalent to `not 3 $in {n N: n % 2 = 0}`.

```litex
by contra not {n N: n % 2 = 0} $in {s power_set(N): 3 $in s}:
    {n N: n % 2 = 0} $in {s power_set(N): 3 $in s}
    3 $in {n N: n % 2 = 0}
    impossible 3 % 2 = 0
```

This proof flows smoothly: we assume the negation of the goal, and get the first statement `{n N: n % 2 = 0} $in {s power_set(N): 3 $in s}`, then by that we have `3 $in {n N: n % 2 = 0}`, then we get a contradiction by the fact that `3 % 2 = 0`.

You might think those objects are too length, actually you can give them a name for convenience.

```litex
have a set = {n N: n % 2 = 0}
have b set = {s power_set(N): 3 $in s}

by contra not a $in b:
    a $in b
    3 $in a
    impossible 3 % 2 = 0
```

### 9.3.3 Example

Here we show that the function

```text
p(x) = {n N: (n + 1) $in x}
```

is not injective as a function from `power_set(N)` to `power_set(N)`. The idea is
that both `{}` and `{0}` are sent to `{}`. If `p` were injective, then from
`p({}) = p({0})` we would get `{}` = `{0}`. But these two finite sets have
different sizes, since `count({}) = 0` and `count({0}) = 1`, so this gives a
contradiction.

```litex
prop injective_from_power_set_R_to_power_set_R(f fn(x power_set(R)) power_set(R)):
    forall a, b power_set(R):
        f(a) = f(b)
        =>:
            a = b

have fn p(x power_set(N)) power_set(N) = {n N: (n + 1) $in x}

p({0}) = {n N: (n + 1) $in {0}}

by contra {n N: (n + 1) $in {0}} = {}:
    have x {n N: (n + 1) $in {0}}
    by enumerate finite_set:
        prove:
            forall x {0}:
                x = 0
    (x + 1) = 0
    x = -1
    impossible x >= 0

p({0}) = {}

p({}) = {n N: (n + 1) $in {}}

by contra {n N: (n + 1) $in {}} = {}:
    have x {n N: (n + 1) $in {}}
    witness $is_nonempty_set({}) from x + 1
    impossible $is_nonempty_set({})

p({}) = {}

by contra not $injective_from_power_set_R_to_power_set_R(p):
    p({}) = p({0})
    {} = {0}
    0 = count({}) = count({0}) = 1
    impossible 0 = 1
```

This example uses three useful statements.

First, the line

```litex
have fn p(x power_set(N)) power_set(N) = {n N: (n + 1) $in x}
```

introduces a function by a defining equality. The part `p(x power_set(N))`
declares the input variable and its domain, the following `power_set(N)` declares
the return type, and the expression after `=` is the value of the function. After
this definition, Litex can unfold applications such as `p({0})` and `p({})` into
the corresponding set-builder expressions.

Likewise, we can define a function from R to R by f(x) = x + 1.

```litex
have fn f(x R) R = x + 1
```

Second, `witness $is_nonempty_set(s) from x` proves that a set is nonempty by
giving one concrete element of the set. For example, if the proof already knows
that `x $in s`, then the witness statement can derive `$is_nonempty_set(s)`.
When the witness needs a small proof, it can be written as a block:

```text
witness $is_nonempty_set(s) from x:
    know x $in s
```

Third, `count(list_set)` is the number of elements in a finite listed set. For
example, `count({}) = 0` and `count({0}) = 1`. This is useful when two listed
sets would be equal only if they had the same size.

Here is a more interesting example. The key point is that `by enumerate
finite_set` can also enumerate the empty set. Since the empty set has no
elements, a statement of the form `forall x {}: ...` has no cases to check, so
it is true no matter what property we put after it. For example, we can prove
the strange-looking statement `forall x {}: 0 = x = 1`.

This is useful in a contradiction proof. If the proof environment ever gives us
some object in `{}`, then we may apply such a vacuous property to that object and
derive an impossible equality like `0 = 1`.

```litex
prop injective_from_power_set_R_to_power_set_R(f fn(x power_set(R)) power_set(R)):
    forall a, b power_set(R):
        f(a) = f(b)
        =>:
            a = b

have fn p(x power_set(N)) power_set(N) = {n N: (n + 1) $in x}

p({0}) = {n N: (n + 1) $in {0}}

by contra {n N: (n + 1) $in {0}} = {}:
    have x {n N: (n + 1) $in {0}}
    by enumerate finite_set:
        prove:
            forall x {0}:
                x = 0
    (x + 1) = 0
    x = -1
    impossible x >= 0

p({0}) = {}

p({}) = {n N: (n + 1) $in {}}

# This true because the empty set has no elements, and we can apply any property to elements of the empty set.
by enumerate finite_set:
    prove:
        forall x {}:
            0 = x = 1

by contra {n N: (n + 1) $in {}} = {}:
    have x {n N: (n + 1) $in {}}
    (x + 1) $in {}
    0 = x + 1 = 1
    impossible 0 = 1

p({}) = {}

by contra not $injective_from_power_set_R_to_power_set_R(p):
    p({}) = p({0})
    {} = {0}
    0 $in {0}
    0 $in {}
    0 = 0 = 1
    impossible 0 = 1
```

### 9.3.4 Example

Now consider a function whose inputs and outputs are both subsets of `Z`.

```litex
prop injective_from_power_set_Z_to_power_set_Z(f fn(x power_set(Z)) power_set(Z)):
    forall a, b power_set(Z):
        f(a) = f(b)
        =>:
            a = b

have fn q(s power_set(Z)) power_set(Z) = {n Z: n + 1 $in s}

claim:
    prove:
        forall a, b power_set(Z):
            q(a) = q(b)
            =>:
                a = b

    by extension:
        prove:
            a = b
        claim:
            prove:
                forall x a:
                    x $in b
            x $in Z
            (x - 1) + 1 = x
            (x - 1) +1 $in a
            x - 1 $in {n Z: n + 1 $in a}
            {n Z: n + 1 $in a} = q(a)
            x - 1 $in q(a)
            x - 1 $in q(b)
            {n Z: n + 1 $in b} = q(b)
            x - 1 $in {n Z: n + 1 $in b}
            (x - 1) + 1 $in b
            x $in b
        claim:
            prove:
                forall y b:
                    y $in a
            y $in Z
            (y - 1) + 1 = y
            (y - 1) + 1 $in b
            y - 1 $in {n Z: n + 1 $in b}
            {n Z: n + 1 $in b} = q(b)
            y - 1 $in q(b)
            y - 1 $in q(a)
            {n Z: n + 1 $in a} = q(a)
            y - 1 $in {n Z: n + 1 $in a}
            (y - 1) + 1 $in a
            y $in a
            y $in b

$injective_from_power_set_Z_to_power_set_Z(q)

```

The predicate `injective_from_power_set_Z_to_power_set_Z` says exactly what
injective means for functions from `power_set(Z)` to `power_set(Z)`: if two
subsets `a` and `b` have the same image under `f`, then `a = b`.

The function `q` sends a set `s` of integers to the set of all integers whose
successor lies in `s`:

```text
q(s) = {n in Z : n + 1 is in s}.
```

In ordinary language, `q(s)` shifts the membership test one step backward. For
example, `0 $in q(s)` means `1 $in s`, and `-3 $in q(s)` means `-2 $in s`.

The goal of this example is to prove that `q` is injective. Mathematically, the
reason is that over all integers this backward shift loses no information. If
`q(a) = q(b)`, then to show `a = b` we use extensionality. Take `x $in a`.
Then `x - 1 $in q(a)`, because `(x - 1) + 1 = x` is in `a`. Since
`q(a) = q(b)`, we get `x - 1 $in q(b)`, hence `(x - 1) + 1 = x $in b`.
This proves `a $subset b`. The same argument with `a` and `b` switched proves
`b $subset a`, so `a = b`.

The important contrast with the previous power-set example is that the domain is
`Z`, not `N`. On `N`, shifting backward can lose information at `0`. On `Z`, every
integer has a predecessor, so the original set can be recovered from its shifted
membership test.



### 9.3.5 Example

This example proves a version of Cantor's theorem: for any set `X`, no function
from `X` to `power_set(X)` can be surjective. Here `surj_to_power(X, f)` means
that every subset of `X` is hit by some input of `f`.

The proof uses the diagonal set

```text
{x X: not x $in f(x)}.
```

If `f` were surjective, this set would be equal to `f(a)` for some `a $in X`.
Now ask whether `a` is in this diagonal set. If `a` is in it, then by definition
`a` is not in `f(a)`, contradiction. If `a` is not in it, then by definition
`a` is in `f(a)`, again contradiction.

```litex
prop surj_to_power(X set, f fn(x X) power_set(X)):
    forall y power_set(X):
        exist x X st {f(x) = y}

claim:
    prove:
        forall X set, f fn(x X) power_set(X):
            not $surj_to_power(X, f)

    by contra:
        prove:
            not $surj_to_power(X, f)
        have by exist a X st {f(a) = {x X: not x $in f(x)}}: a
        by cases:
            prove:
                a != a
            case a $in {x X: not x $in f(x)}:
                a $in {x X: not x $in f(x)}
                not a $in f(a)
                a $in f(a)
                impossible a $in f(a)
            case not a $in {x X: not x $in f(x)}:
                not a $in f(a)
                a $in {x X: not x $in f(x)}
                impossible a $in {x X: not x $in f(x)}
        a = a
        impossible a != a

```

Historically, this theorem is one of Cantor's central insights. It shows that
there is no largest infinity: every set has a strictly larger power set. The
same diagonal idea is also the source of the proof that the real numbers are
uncountable, and it became one of the basic tools of modern set theory, logic,
and later computability theory.

## 9.4 Litex statements and ideas in this chapter

This chapter extends the earlier proof style from numbers and logic to sets. The
main point is that sets are ordinary mathematical objects in Litex: they can be
named, compared, passed to functions, placed inside other sets, and described by
conditions.

### Litex statements and syntax used

1. Membership is written directly with `$in`:

   ```text
   x $in A
   ```

   For a set builder such as `{n Z: n <= 3}`, membership means that the object
   belongs to the base domain and satisfies the defining condition.

2. Finite displayed sets such as `{1, 2, 3}` behave like finite alternatives.
   Membership in such a set can be used as a case split over the listed values.

3. Subset and superset facts are written with `$subset` and `$superset`.
   A subset proof is a universal membership proof: take an arbitrary element of
   the smaller set and show that it belongs to the larger set.

4. `by extension` proves set equality by mutual membership. To prove `A = B`,
   Litex checks the two directions:

   ```text
   forall x A:
       x $in B

   forall x B:
       x $in A
   ```

5. Set operations such as `union`, `intersect`, `set_minus`, and `power_set`
   can be used as ordinary objects. Their membership facts unfold into the
   corresponding mathematical conditions.

6. `have x OBJECT` can introduce an element of a set-like object only when that
   object is known to be nonempty. In contradiction proofs about empty sets, a
   temporary assumption of nonemptiness lets Litex take such an element and then
   derive a contradiction.

7. Long set expressions can be named for readability:

```litex
have a set = {n N: n % 2 = 0}
have b set = {s power_set(N): 3 $in s}
```

   This does not change the mathematics; it only gives shorter names to objects
   that would otherwise make later lines hard to read.

### Litex knowledge points

1. Set-builder membership is a pattern. To prove `x $in {n S: P(n)}`, prove
   that `x $in S` and that `P(x)` holds.

2. Set equality is extensional. The proof is not about how two set expressions
   are written, but about whether they have exactly the same elements.

3. Empty-set proofs often work by contradiction: assume the set is nonempty,
   take an element, unfold the membership facts, and derive an impossible
   condition.

4. Power-set membership is subset membership. A fact such as
   `B $in power_set(A)` says that every element of `B` is an element of `A`.

5. Functions can take sets as inputs and return sets as outputs. A definition
   such as `q(s) = {n Z: n + 1 $in s}` is a function whose value is itself a
   set-builder expression.

6. The same proof patterns from earlier chapters still drive the work:
   `claim` opens local proof environments, `by contra` proves negations by
   contradiction, `by cases` splits membership alternatives, and `witness` or
   `have by exist` handles existential information.

7. The chapter's larger examples show why sets matter as first-class objects:
   they support ordinary finite reasoning, extensional equality, power-set
   arguments, shifted-set functions, and Cantor-style diagonal proofs without
   forcing the user to manage a separate visible hierarchy of set encodings.
