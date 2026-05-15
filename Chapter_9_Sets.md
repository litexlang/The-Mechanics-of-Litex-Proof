# Chapter 9 — Sets

Online: https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Chapter_9_Sets

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


### 9.2.6 Example

The empty set has no elements. A common way to prove that a set equals the empty
set is to show that its membership condition is impossible. For example,

```text
{n N : n < 0} = {}.
```

If `n` belongs to the left-hand set, then `n` is a natural number and `n < 0`.
But natural numbers are nonnegative. This contradiction shows that no object
can be in the left-hand set.

The reverse inclusion is automatic mathematically: every element of the empty
set belongs to any set, because there is no element to check.

### 9.2.7 Example

The universal set for a domain is proved by showing that the defining condition
is always true on that domain. For instance,

```text
{n Z : n % 2 = 0 or n % 2 = 1} = Z.
```

Take an arbitrary integer `n`. Every integer has remainder `0` or `1` modulo
`2`, so `n` satisfies the defining condition of the set builder. Thus every
integer belongs to the left-hand side.

The other inclusion is built into the set-builder domain: if `n` belongs to
`{n Z : n % 2 = 0 or n % 2 = 1}`, then in particular `n` is an integer. Hence
the set builder is exactly `Z`.

## 9.3 Power Sets

The power set `power_set(A)` is the set of all subsets of `A`. Thus

```text
B $in power_set(A)
```

means the same mathematical thing as

```text
B $subset A.
```

So proofs about power sets usually reduce to subset proofs: take an arbitrary
element of the proposed subset and show that it lies in the base set.

### 9.3.1 Example

The statement

```text
{-1, 1} $in power_set({x Z : x^2 = 1})
```

says that every element of `{-1, 1}` satisfies `x^2 = 1`. There are two cases.
If `x = -1`, then `x^2 = (-1)^2 = 1`. If `x = 1`, then `x^2 = 1^2 = 1`.
Therefore every element of `{-1, 1}` belongs to `{x Z : x^2 = 1}`, so
`{-1, 1}` is an element of the power set.

### 9.3.2 Example

To show that

```text
{0, 1, 4} $in power_set({x N : x < 5}),
```

prove that each displayed element is a natural number less than `5`. The
membership proof splits into three cases: `x = 0`, `x = 1`, and `x = 4`.
Each case satisfies `x < 5`, and each object is in `N`. Hence the whole
displayed set is a subset of `{x N : x < 5}`.

### 9.3.3 Example

Some power-set claims fail because a single listed element violates the target
condition. For example, to disprove

```text
{1, 2, 5} $in power_set({x N : x < 5}),
```

it is enough to look at `5`. The element `5` is in `{1, 2, 5}`, but it does not
satisfy `5 < 5`. Therefore `{1, 2, 5}` is not a subset of `{x N : x < 5}`, and
so it is not an element of the power set.

### 9.3.4 Example

Power-set membership can also be nested. A statement like

```text
{{1}, {1, 2}} $in power_set(power_set({1, 2}))
```

means that every element of `{{1}, {1, 2}}` is itself a subset of `{1, 2}`.
There are two outer cases. If the element is `{1}`, then every member of it is
`1`, hence belongs to `{1, 2}`. If the element is `{1, 2}`, then its members are
`1` or `2`, and both belong to `{1, 2}`. Thus both listed sets are elements of
`power_set({1, 2})`, so the whole outer displayed set is in the larger power
set.

### 9.3.5 Example

The empty set is always a subset of any set, so it is always an element of a
power set:

```text
{} $in power_set(A).
```

The proof has no cases. To prove `{}` is a subset of `A`, take an arbitrary
element of `{}`. There is no such element, so the implication is vacuously true.
This is often the easiest power-set membership proof: the empty set belongs to
every power set because it has no element that could fail the target membership
condition.
