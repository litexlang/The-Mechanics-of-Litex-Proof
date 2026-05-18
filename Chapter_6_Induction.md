# Chapter 6 — Induction

Online: https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Chapter_6_Induction

GitHub source: https://github.com/litexlang/The-Mechanics-of-Litex-Proof/blob/main/Chapter_6_Induction.lit

Induction is the standard way to prove a statement about all natural numbers.
The proof has two parts:

- a base case, where the statement is checked at the starting value;
- an induction step, where the statement at `m` is used to prove the statement
  at `m + 1`.

In Litex, the command is written as `by induc n from START:`. The body contains
the base case and the induction step. The induction step is an ordinary
`forall` fact: assume the current index is in the induction range, assume the
induction hypothesis, and prove the next instance.

The examples below follow the mathematical content of the induction chapter,
but they are written in a Litex-first way. Some later topics in the source text
use Lean's recursive definitions, termination checking, and standard library
objects. Here we keep the executable Litex code focused on the proof pattern.

## 6.1 Basic Induction

### 6.1.1

Problem: Let `n` be a natural number. Show that `2^n >= n + 1`.

The base case is `n = 0`. The step uses the induction hypothesis
`2^m >= m + 1` and multiplies by `2`.

```litex
claim:
    prove:
        forall n N:
            =>:
                2 ^ n >= n + 1
    by induc n from 0:
        prove:
            2 ^ n >= n + 1
        2^0 = 1 >= 0 + 1

        forall m Z:
            m >= 0
            2^m >= m + 1
            =>:
                2 ^ (m + 1) = 2 ^ m * 2^1 >= (m + 1) * 2 = (m + 1) + (m + 1) >= m + 1 + 1
```

### 6.1.2

Every integer is even or odd. This can be proved by induction, but Litex also
has builtin modulo facts that make the proof very direct: an integer has
remainder `0` or `1` modulo `2`, and a remainder statement gives the
corresponding quotient witness.

```litex
prop even(a Z):
    exist k Z st {a = 2 * k}

prop odd(a Z):
    exist k Z st {a = 2 * k + 1}

claim:
    prove:
        forall n Z:
            =>:
                $even(n) or $odd(n)
    n % 2 = 0 or n % 2 = 1
    by cases:
        prove:
            $even(n) or $odd(n)
        case n % 2 = 0:
            have by exist k Z st {n = 2 * k + 0}: k
            witness exist l Z st {n = 2 * l} from k:
                n = 2 * k + 0 = 2 * k
            $even(n)
            $even(n) or $odd(n)
        case n % 2 = 1:
            have by exist k Z st {n = 2 * k + 1}: k
            witness exist l Z st {n = 2 * l + 1} from k:
                n = 2 * k + 1
            $odd(n)
            $even(n) or $odd(n)
```

This example is a useful reminder: induction is not always the shortest proof.
If a builtin arithmetic fact gives exactly the needed split, use it.

### 6.1.3

A typical induction step may depend on an already-known algebraic or modular
rule. For example, the power rule for congruences says:

```text
if a is congruent to b modulo d, then a^n is congruent to b^n modulo d.
```

The proof is inductive: the `n + 1` case follows from the `n` case by
factoring

```text
a^(n+1) - b^(n+1)
```

into terms known to be divisible by `d`. In a short tutorial chapter, it is
better to state this as a reusable modular fact than to bury the induction
idea under a long modulo calculation.

```litex
prop mod_eq(a Z, b Z, d Z):
    d != 0
    exist k Z st {a - b = d * k}

prop congruence_power_rule(a Z, b Z, d Z):
    forall n N_pos:
        $mod_eq(a^n, b^n, d)

know:
    forall a, b, d Z:
        $mod_eq(a, b, d)
        =>:
            $congruence_power_rule(a, b, d)
```

### 6.1.4

Induction often combines with case splits. To prove that `4^n` is congruent to
either `1` or `4` modulo `15`, the induction hypothesis has two alternatives.
In one branch the next residue is `4`; in the other branch the next residue is
`1`.

```litex
prop mod_eq(a Z, b Z, d Z):
    d != 0
    exist k Z st {a - b = d * k}

prop residue_is_one_or_four(n N):
    $mod_eq(4^n, 1, 15) or $mod_eq(4^n, 4, 15)

know:
    forall n N:
        =>:
            $residue_is_one_or_four(n)

claim:
    prove:
        forall n N:
            =>:
                $residue_is_one_or_four(n)
    $residue_is_one_or_four(n)
```

The code above records the theorem as a reusable fact. A fully expanded proof
would be an induction whose step is a `by cases` block on the previous
residue.

### 6.1.5

Induction can start somewhere other than `0`. To prove a statement for all
`n >= 2`, start the induction at `2`.

Problem: Let `n >= 2`. Show that `3^n >= 2^n + 5`.

```litex
know:
    forall a Z:
        =>:
            2^a > 0

claim:
    prove:
        forall n Z:
            n >= 2
            =>:
                3^n >= 2^n + 5
    by induc k from 2:
        prove:
            3^k >= 2^k + 5
        3^2 = 9 >= 2^2 + 5 = 4 + 5 = 9

        forall m Z:
            m >= 2
            3^m >= 2^m + 5
            =>:
                3^(m + 1) = 3^1 * 3^m >= 3^1 * (2^m + 5) = 3 * (2^m + 5)
                3 * (2^m + 5) = 3 * 2^m + 3 * 5 = 3 * 2^m + 15
                15 > 10
                10 > 5
                2^m > 0
                3 * 2^m + 15 = 2 * 2^m + 2^m + 15 >= 2 * 2^m + 2^m + 10 >= 2 * 2^m + 0 + 5 = 2 * 2^m + 5 = 2^(m + 1) + 5
                3^(m + 1) = 3^1 * 3^m >= 3^1 * (2^m + 5) = 3 * (2^m + 5) = 3 * 2^m + 15 = 2 * 2^m + 2^m + 15 >= 2 * 2^m + 2^m + 10 >= 2 * 2^m + 0 + 5 = 2 * 2^m + 5 = 2^(m + 1) + 5
                3^(m + 1) >= 2^(m + 1) + 5
```

### 6.1.6

"For all sufficiently large `n`" means "there exists a threshold `N0` such
that the statement holds for every `n >= N0`." For example, the theorem
`2^n >= n^2` is true for all `n >= 4`.

```litex
prop sufficiently_large_power_bound(N0 Z):
    forall n Z:
        n >= N0
        =>:
            2^n >= n^2

know:
    $sufficiently_large_power_bound(4)

claim:
    prove:
        exist N0 Z st {$sufficiently_large_power_bound(N0)}
    witness exist N0 Z st {$sufficiently_large_power_bound(N0)} from 4:
        $sufficiently_large_power_bound(4)
```

The full induction proof starts at `4`. The base case is `2^4 = 16 = 4^2`.
The step proves that if `2^m >= m^2`, then `2^(m+1) >= (m+1)^2`; the key
estimate is that `m^2 >= 2m + 1` once `m >= 3`.

## 6.2 Recursively Defined Sequences

Many induction problems involve a sequence defined by an initial value and a
recurrence. In Litex, the clean way to present such examples is to state the
sequence as a function parameter and include the initial value and recurrence
as hypotheses.

### 6.2.1 Example

The sequence `a(n)` is defined by the initial value `a(0) = 3` and the recurrence `a(k + 1) = a(k)^2 - 2` for all natural numbers `k`. Show that for all natural numbers `n`, `a(n)` is odd.

```litex
prop odd(a Z):
    exist k Z st {a = 2 * k + 1}

claim:
    prove:
        forall a fn(n Z: n >= 0) Z, n Z:
            a(0) = 3
            forall k Z:
                k >= 0
                =>:
                    a(k + 1) = a(k)^2 - 2
            n >= 0
            =>:
                $odd(a(n))
    by induc n from 0:
        prove:
            $odd(a(n))
        witness exist k Z st {a(0) = 2 * k + 1} from 1:
            a(0) = 3 = 2 * 1 + 1

        claim:
            prove:
                forall m Z:
                    m >= 0
                    $odd(a(m))
                    =>:
                        $odd(a(m + 1))
            have by exist k Z st {a(m) = 2 * k + 1}: k
            witness exist l Z st {a(m + 1) = 2 * l + 1} from 2 * k^2 + 2 * k - 1:
                a(m + 1) = a(m)^2 - 2 = (2 * k + 1)^2 - 2 = 4 * k^2 + 4 * k + 1 - 2 = 4 * k^2 + 4 * k - 1 = 2 * (2 * k^2 + 2 * k - 1) + 1
```

This is the main pattern in the sequence examples: prove the formula at the
initial index, then use the recurrence to rewrite the next term.

### 6.2.2 Example

The sequence `x(n)` is defined by the initial value `x(0) = 5` and the recurrence `x(k + 1) = 2 * x(k) - 1` for all natural numbers `k`. Show that for all natural numbers `n`, `x(n)` is congruent to 1 modulo 4.

```litex
prop mod_eq(a Z, b Z, n Z):
    n != 0
    exist k Z st {a - b = n * k}

claim:
    prove:
        forall x fn(n Z: n >= 0) Z, n Z:
            x(0) = 5
            forall k Z:
                k >= 0
                =>:
                    x(k + 1) = 2 * x(k) - 1
            n >= 0
            =>:
                $mod_eq(x(n), 1, 4)
    by induc n from 0:
        prove:
            $mod_eq(x(n), 1, 4)
        4 != 0
        witness exist k Z st {x(0) - 1 = 4 * k} from 1:
            x(0) - 1 = 5 - 1 = 4 = 4 * 1
        $mod_eq(x(0), 1, 4)

        claim:
            prove:
                forall m Z:
                    m >= 0
                    $mod_eq(x(m), 1, 4)
                    =>:
                        $mod_eq(x(m + 1), 1, 4)
            have by exist k Z st {x(m) - 1 = 4 * k}: k
            4 != 0
            witness exist l Z st {x(m + 1) - 1 = 4 * l} from 2 * k:
                x(m + 1) - 1 = (2 * x(m) - 1) - 1 = 2 * x(m) - 2 = 2 * (x(m) - 1) = 2 * (4 * k) = 4 * (2 * k)
            $mod_eq(x(m + 1), 1, 4)
```

### 6.2.3 Example

The sequence `x(n)` is defined by the initial value `x(0) = 5` and the recurrence `x(k + 1) = 2 * x(k) - 1` for all natural numbers `k`. Show that for all natural numbers `n`, `x(n)` is equal to `2^(n + 2) + 1`.

```litex
claim:
    prove:
        forall x fn(n Z: n >= 0) Z, n Z:
            x(0) = 5
            forall k Z:
                k >= 0
                =>:
                    x(k + 1) = 2 * x(k) - 1
            n >= 0
            =>:
                x(n) = 2^(n + 2) + 1
    by induc n from 0:
        prove:
            x(n) = 2^(n + 2) + 1
        x(0) = 5 = 2^2 + 1 = 2^(0 + 2) + 1

        claim:
            prove:
                forall m Z:
                    m >= 0
                    x(m) = 2^(m + 2) + 1
                    =>:
                        x(m + 1) = 2^((m + 1) + 2) + 1
            x(m + 1) = 2 * x(m) - 1
            2 * x(m) - 1 = 2 * (2^(m + 2) + 1) - 1 = 2 * 2^(m + 2) + 2 * 1 - 1 = 2^1 * 2^(m + 2) + 1 = 2^(1 + (m + 2)) + 1 = 2^(m + 3) + 1
            2^(m + 3) + 1 = 2^((m + 1) + 2) + 1
            x(m + 1) = 2^((m + 1) + 2) + 1
```

### 6.2.4 Example

The sequence `A(n)` is defined by the initial value `A(0) = 0` and the recurrence `A(k + 1) = A(k) + (k + 1)` for all natural numbers `k`. Show that for all natural numbers `n`, `A(n)` equals `n * (n + 1) / 2`.

```litex
claim:
    prove:
        forall A fn(n Z: n >= 0) Q, n Z:
            A(0) = 0
            forall k Z:
                k >= 0
                =>:
                    A(k + 1) = A(k) + (k + 1)
            n >= 0
            =>:
                A(n) = n * (n + 1) / 2
    by induc n from 0:
        prove:
            A(n) = n * (n + 1) / 2
        A(0) = 0 = 0 * (0 + 1) / 2

        claim:
            prove:
                forall m Z:
                    m >= 0
                    A(m) = m * (m + 1) / 2
                    =>:
                        A(m + 1) = (m + 1) * ((m + 1) + 1) / 2
            A(m + 1) = A(m) + (m + 1)
            A(m) + (m + 1) = m * (m + 1) / 2 + (m + 1)
            m * (m + 1) / 2 + (m + 1) = (m + 1) * (m / 2 + 1) = (m + 1) * ((m + 2) / 2)
            (m + 1) * ((m + 2) / 2) = (m + 1) * (((m + 1) + 1) / 2)
            A(m + 1) = (m + 1) * ((m + 1) + 1) / 2
```

### 6.2.5 Example

The sequence `f(n)` is defined by the initial value `f(0) = 1` and the recurrence `f(k + 1) = (k + 1) * f(k)` for all natural numbers `k`. Show that for all natural numbers `n`, for all `d` such that `1 <= d <= n`, `d` divides `f(n)`.

We use integer divisibility below. Since `d` and `f(n)` are natural numbers,
this still expresses the same divisibility fact.

```litex
prop divides(a Z, b Z):
    exist c Z st {b = a * c}

prop factorial_divisible(f fn(n Z: n >= 0) N, n Z):
    n >= 0
    forall d N:
        1 <= d
        d <= n
        =>:
            $divides(d, f(n))

claim:
    prove:
        forall f fn(n Z: n >= 0) N, n Z:
            f(0) = 1
            forall k Z:
                k >= 0
                =>:
                    f(k + 1) = (k + 1) * f(k)
            n >= 0
            =>:
                $factorial_divisible(f, n)
    by induc n from 0:
        prove:
            $factorial_divisible(f, n)
        claim:
            prove:
                forall d N:
                    1 <= d
                    d <= 0
                    =>:
                        $divides(d, f(0))
            by contra:
                prove:
                    $divides(d, f(0))
                impossible d <= 0
        $factorial_divisible(f, 0)

        claim:
            prove:
                forall m Z:
                    m >= 0
                    $factorial_divisible(f, m)
                    =>:
                        $factorial_divisible(f, m + 1)
            claim:
                prove:
                    forall d N:
                        1 <= d
                        d <= m + 1
                        =>:
                            $divides(d, f(m + 1))
                d <= m or d >= m + 1
                by cases:
                    prove:
                        $divides(d, f(m + 1))
                    case d <= m:
                        $divides(d, f(m))
                        have by exist c Z st {f(m) = d * c}: c
                        witness exist q Z st {f(m + 1) = d * q} from (m + 1) * c:
                            f(m + 1) = (m + 1) * f(m) = (m + 1) * (d * c) = d * ((m + 1) * c)
                    case d >= m + 1:
                        d = m + 1
                        witness exist q Z st {f(m + 1) = d * q} from f(m):
                            f(m + 1) = (m + 1) * f(m) = d * f(m)
            $factorial_divisible(f, m + 1)
```

### 6.2.6 Example

Show forall natural numbers `n`, `(n+1)! >= 2^n`.

```litex
claim:
    prove:
        forall f fn(n Z: n >= 0) N, n Z:
            f(0) = 1
            forall k Z:
                k >= 0
                =>:
                    f(k + 1) = (k + 1) * f(k)
            n >= 0
            =>:
                f(n + 1) >= 2^n
    by induc n from 0:
        prove:
            f(n + 1) >= 2^n
        f(0 + 1) = (0 + 1) * f(0) = 1 * f(0) = 1 * 1 = 1 >= 2^0

        claim:
            prove:
                forall k Z:
                    k >= 0
                    f(k + 1) >= 2^k
                    =>:
                        f(k + 1 + 1) >= 2^(k + 1)
            k + 2 >= 0 + 2 = 2
            f((k + 1) + 1) = ((k + 1) + 1) * f(k + 1) = (k + 2) * f(k + 1)
            (k + 2) * f(k + 1) >= 2 * f(k + 1)
            2 * f(k + 1) >= 2 * 2^k
            2 * 2^k = 2^1 * 2^k = 2^(1 + k) = 2^(k + 1)
            f(k + 1 + 1) = (k + 2) * f(k + 1) >= 2 * f(k + 1) >= 2 * 2^k = 2^(k + 1)
```

## 6.3 Two-Step Induction

Some recurrences depend on the previous two terms, such as Fibonacci-style
sequences. The proof must carry two consecutive facts at once:

```text
P(n) and P(n + 1)
```

Then the induction step proves:

```text
P(n + 1) and P(n + 2)
```

This is not a new logical idea. It is ordinary induction where the induction
predicate has been strengthened to remember two adjacent cases.

### 6.3.1 Example

Sequence `a(n)` is defined by the initial value `a(0) = 2`, `a(1) = 1`, `forall k: N => a(k + 2) = a(k + 1) + 2 * a(k)`. Show that for all natural numbers `n`, `a(n) = 2^n + (-1)^n`.

The useful induction predicate remembers two adjacent formulas at once. The
extra `know` line records the routine algebra identity used in the step.

```litex
prop seq_formula(a fn(n Z: n >= 0) Z, n Z):
    n >= 0
    a(n) = 2^n + (-1)^n

prop seq_formula_pair(a fn(n Z: n >= 0) Z, n Z):
    n >= 0
    $seq_formula(a, n)
    $seq_formula(a, n + 1)

know:
    forall m Z:
        m >= 0
        =>:
            2^(m + 1) + (-1)^(m + 1) + 2 * (2^m + (-1)^m) = 2^(m + 2) + (-1)^(m + 2)

claim:
    prove:
        forall a fn(n Z: n >= 0) Z, n Z:
            a(0) = 2
            a(1) = 1
            forall k Z:
                k >= 0
                =>:
                    a(k + 2) = a(k + 1) + 2 * a(k)
            n >= 0
            =>:
                $seq_formula_pair(a, n)
    by strong_induc n from 0:
        prove:
            $seq_formula_pair(a, n)
        claim:
            prove:
                $seq_formula_pair(a, 0)
            0 >= 0
            a(0) = 2 = 2^0 + (-1)^0
            $seq_formula(a, 0)
            0 + 1 >= 0
            2^1 = 2
            (-1)^1 = -1
            2^1 + (-1)^1 = 2 + (-1) = 1
            2^(0 + 1) + (-1)^(0 + 1) = 2^1 + (-1)^1 = 1
            a(0 + 1) = a(1) = 1 = 2^(0 + 1) + (-1)^(0 + 1)
            $seq_formula(a, 0 + 1)
            $seq_formula_pair(a, 0)

        claim:
            prove:
                forall m Z:
                    m >= 0
                    forall y Z:
                        y >= 0
                        y <= m
                        =>:
                            $seq_formula_pair(a, y)
                    =>:
                        $seq_formula_pair(a, m + 1)
            m >= 0
            $seq_formula_pair(a, m)
            $seq_formula(a, m)
            $seq_formula(a, m + 1)
            a(m) = 2^m + (-1)^m
            a(m + 1) = 2^(m + 1) + (-1)^(m + 1)
            m + 1 >= 0
            $seq_formula(a, m + 1)
            (m + 1) + 1 = m + 2
            a((m + 1) + 1) = a(m + 2) = a(m + 1) + 2 * a(m)
            a(m + 1) + 2 * a(m) = 2^(m + 1) + (-1)^(m + 1) + 2 * (2^m + (-1)^m)
            2^(m + 1) + (-1)^(m + 1) + 2 * (2^m + (-1)^m) = 2^(m + 2) + (-1)^(m + 2)
            a((m + 1) + 1) = 2^(m + 2) + (-1)^(m + 2) = 2^((m + 1) + 1) + (-1)^((m + 1) + 1)
            $seq_formula(a, (m + 1) + 1)
            $seq_formula_pair(a, m + 1)

claim:
    prove:
        forall a fn(n Z: n >= 0) Z, n Z:
            a(0) = 2
            a(1) = 1
            forall k Z:
                k >= 0
                =>:
                    a(k + 2) = a(k + 1) + 2 * a(k)
            n >= 0
            =>:
                a(n) = 2^n + (-1)^n
    $seq_formula_pair(a, n)
    $seq_formula(a, n)
```

### 6.3.2 Example

Sequence `a(n)` is defined by the initial value `a(0) = 2`, `a(1) = 1`, `forall k: N => a(k + 2) = a(k + 1) + 2 * a(k)`. Show that for all positive natural numbers `n`, `a(n)` is congruent to either 1 or 5 modulo 6.

Here the stronger statement says that consecutive residues are either `(1, 5)`
or `(5, 1)`. The induction step flips this pair.

```litex
prop mod_eq(a Z, b Z, n Z):
    n != 0
    exist k Z st {a - b = n * k}

prop seq_mod_pair_15(a fn(n Z: n >= 0) Z, n Z):
    n >= 1
    $mod_eq(a(n), 1, 6)
    $mod_eq(a(n + 1), 5, 6)

prop seq_mod_pair_51(a fn(n Z: n >= 0) Z, n Z):
    n >= 1
    $mod_eq(a(n), 5, 6)
    $mod_eq(a(n + 1), 1, 6)

prop seq_mod_pair(a fn(n Z: n >= 0) Z, n Z):
    n >= 1
    $seq_mod_pair_15(a, n) or $seq_mod_pair_51(a, n)

claim:
    prove:
        forall a fn(n Z: n >= 0) Z, n Z:
            a(0) = 2
            a(1) = 1
            forall k Z:
                k >= 0
                =>:
                    a(k + 2) = a(k + 1) + 2 * a(k)
            n >= 1
            =>:
                $seq_mod_pair(a, n)
    by strong_induc n from 1:
        prove:
            $seq_mod_pair(a, n)
        claim:
            prove:
                $seq_mod_pair(a, 1)
            1 >= 1
            6 != 0
            witness exist k Z st {a(1) - 1 = 6 * k} from 0:
                a(1) - 1 = 1 - 1 = 0 = 6 * 0
            $mod_eq(a(1), 1, 6)
            a(1 + 1) = a(2) = a(0 + 2) = a(0 + 1) + 2 * a(0) = a(1) + 2 * a(0) = 1 + 2 * 2 = 5
            witness exist l Z st {a(1 + 1) - 5 = 6 * l} from 0:
                a(1 + 1) - 5 = 5 - 5 = 0 = 6 * 0
            $mod_eq(a(1 + 1), 5, 6)
            $seq_mod_pair_15(a, 1)
            $seq_mod_pair_15(a, 1) or $seq_mod_pair_51(a, 1)
            $seq_mod_pair(a, 1)

        claim:
            prove:
                forall m Z:
                    m >= 1
                    forall y Z:
                        y >= 1
                        y <= m
                        =>:
                            $seq_mod_pair(a, y)
                    =>:
                        $seq_mod_pair(a, m + 1)
            m >= 1
            $seq_mod_pair(a, m)
            $seq_mod_pair_15(a, m) or $seq_mod_pair_51(a, m)
            by cases:
                prove:
                    $seq_mod_pair(a, m + 1)
                case $seq_mod_pair_15(a, m):
                    $mod_eq(a(m), 1, 6)
                    $mod_eq(a(m + 1), 5, 6)
                    have by exist k Z st {a(m) - 1 = 6 * k}: k
                    have by exist l Z st {a(m + 1) - 5 = 6 * l}: l
                    m + 1 >= 1
                    $mod_eq(a(m + 1), 5, 6)
                    a((m + 1) + 1) = a(m + 2) = a(m + 1) + 2 * a(m)
                    6 != 0
                    witness exist t Z st {a((m + 1) + 1) - 1 = 6 * t} from l + 2 * k + 1:
                        a((m + 1) + 1) - 1 = a(m + 1) + 2 * a(m) - 1 = (a(m + 1) - 5) + 2 * (a(m) - 1) + 6 = 6 * l + 2 * (6 * k) + 6 = 6 * (l + 2 * k + 1)
                    $mod_eq(a((m + 1) + 1), 1, 6)
                    $seq_mod_pair_51(a, m + 1)
                    $seq_mod_pair_15(a, m + 1) or $seq_mod_pair_51(a, m + 1)
                    $seq_mod_pair(a, m + 1)
                case $seq_mod_pair_51(a, m):
                    $mod_eq(a(m), 5, 6)
                    $mod_eq(a(m + 1), 1, 6)
                    have by exist k Z st {a(m) - 5 = 6 * k}: k
                    have by exist l Z st {a(m + 1) - 1 = 6 * l}: l
                    m + 1 >= 1
                    $mod_eq(a(m + 1), 1, 6)
                    a((m + 1) + 1) = a(m + 2) = a(m + 1) + 2 * a(m)
                    6 != 0
                    witness exist t Z st {a((m + 1) + 1) - 5 = 6 * t} from l + 2 * k + 1:
                        a((m + 1) + 1) - 5 = a(m + 1) + 2 * a(m) - 5 = (a(m + 1) - 1) + 2 * (a(m) - 5) + 6 = 6 * l + 2 * (6 * k) + 6 = 6 * (l + 2 * k + 1)
                    $mod_eq(a((m + 1) + 1), 5, 6)
                    $seq_mod_pair_15(a, m + 1)
                    $seq_mod_pair_15(a, m + 1) or $seq_mod_pair_51(a, m + 1)
                    $seq_mod_pair(a, m + 1)

claim:
    prove:
        forall a fn(n Z: n >= 0) Z, n Z:
            a(0) = 2
            a(1) = 1
            forall k Z:
                k >= 0
                =>:
                    a(k + 2) = a(k + 1) + 2 * a(k)
            n >= 1
            =>:
                $mod_eq(a(n), 1, 6) or $mod_eq(a(n), 5, 6)
    $seq_mod_pair(a, n)
    $seq_mod_pair_15(a, n) or $seq_mod_pair_51(a, n)
    by cases:
        prove:
            $mod_eq(a(n), 1, 6) or $mod_eq(a(n), 5, 6)
        case $seq_mod_pair_15(a, n):
            $mod_eq(a(n), 1, 6)
            $mod_eq(a(n), 1, 6) or $mod_eq(a(n), 5, 6)
        case $seq_mod_pair_51(a, n):
            $mod_eq(a(n), 5, 6)
            $mod_eq(a(n), 1, 6) or $mod_eq(a(n), 5, 6)
```

### 6.3.3 Example

Sequence `Fibonacci(n)` is defined by the initial value `Fibonacci(0) = 1`, `Fibonacci(1) = 1`, `forall k: N => Fibonacci(k + 2) = Fibonacci(k + 1) + Fibonacci(k)`. Show that for all natural numbers `n`, `Fibonacci(n) <= 2^n`.

Again, the induction predicate stores the bounds for `n` and `n + 1`; the
recurrence then gives the bound for `n + 2`.

```litex
prop fib_bound(Fibonacci fn(n Z: n >= 0) Z, n Z):
    n >= 0
    Fibonacci(n) <= 2^n

prop fib_bound_pair(Fibonacci fn(n Z: n >= 0) Z, n Z):
    n >= 0
    $fib_bound(Fibonacci, n)
    $fib_bound(Fibonacci, n + 1)

claim:
    prove:
        forall Fibonacci fn(n Z: n >= 0) Z, n Z:
            Fibonacci(0) = 1
            Fibonacci(1) = 1
            forall k Z:
                k >= 0
                =>:
                    Fibonacci(k + 2) = Fibonacci(k + 1) + Fibonacci(k)
            n >= 0
            =>:
                $fib_bound_pair(Fibonacci, n)
    by strong_induc n from 0:
        prove:
            $fib_bound_pair(Fibonacci, n)
        claim:
            prove:
                $fib_bound_pair(Fibonacci, 0)
            0 >= 0
            Fibonacci(0) = 1 = 2^0
            $fib_bound(Fibonacci, 0)
            0 + 1 >= 0
            Fibonacci(0 + 1) = Fibonacci(1) = 1 <= 2^1
            $fib_bound(Fibonacci, 0 + 1)
            $fib_bound_pair(Fibonacci, 0)

        claim:
            prove:
                forall m Z:
                    m >= 0
                    forall y Z:
                        y >= 0
                        y <= m
                        =>:
                            $fib_bound_pair(Fibonacci, y)
                    =>:
                        $fib_bound_pair(Fibonacci, m + 1)
            m >= 0
            $fib_bound_pair(Fibonacci, m)
            $fib_bound(Fibonacci, m)
            $fib_bound(Fibonacci, m + 1)
            Fibonacci(m) <= 2^m
            Fibonacci(m + 1) <= 2^(m + 1)
            m + 1 >= 0
            $fib_bound(Fibonacci, m + 1)
            (m + 1) + 1 = m + 2
            Fibonacci((m + 1) + 1) = Fibonacci(m + 2) = Fibonacci(m + 1) + Fibonacci(m)
            2^m <= 2 * 2^m = 2^1 * 2^m = 2^(1 + m) = 2^(m + 1)
            Fibonacci(m + 1) + Fibonacci(m) <= 2^(m + 1) + 2^m <= 2^(m + 1) + 2^(m + 1) = 2 * 2^(m + 1) = 2^1 * 2^(m + 1) = 2^(1 + (m + 1)) = 2^(m + 2)
            Fibonacci((m + 1) + 1) <= 2^(m + 2) = 2^((m + 1) + 1)
            $fib_bound(Fibonacci, (m + 1) + 1)
            $fib_bound_pair(Fibonacci, m + 1)

claim:
    prove:
        forall Fibonacci fn(n Z: n >= 0) Z, n Z:
            Fibonacci(0) = 1
            Fibonacci(1) = 1
            forall k Z:
                k >= 0
                =>:
                    Fibonacci(k + 2) = Fibonacci(k + 1) + Fibonacci(k)
            n >= 0
            =>:
                Fibonacci(n) <= 2^n
    $fib_bound_pair(Fibonacci, n)
    $fib_bound(Fibonacci, n)
```

### 6.3.4 Example

Sequence `Fibonacci(n)` is defined by the initial value `Fibonacci(0) = 1`, `Fibonacci(1) = 1`, `forall k: N => Fibonacci(k + 2) = Fibonacci(k + 1) + Fibonacci(k)`. Show that for all natural numbers `n`, `Fibonacci(n + 1)^2 - Fibonacci(n + 1) * Fibonacci(n) - Fibonacci(n)^2 = -((-1)^n)`.

The algebra identity in the `know` block is the Cassini step after substituting
`x = Fibonacci(m + 1)` and `y = Fibonacci(m)`.

```litex
prop cassini(Fibonacci fn(n Z: n >= 0) Z, n Z):
    n >= 0
    Fibonacci(n + 1)^2 - Fibonacci(n + 1) * Fibonacci(n) - Fibonacci(n)^2 = -((-1)^n)


forall x, y, m Z:
    x^2 - x * y - y^2 = -((-1)^m)
    =>:
        (x + y)^2 - (x + y) * x - x^2 = -1 * (x^2 - x * y - y^2) = -1 * (-((-1)^m)) = -((-1)^(m + 1))

claim:
    prove:
        forall Fibonacci fn(n Z: n >= 0) Z, n Z:
            Fibonacci(0) = 1
            Fibonacci(1) = 1
            forall k Z:
                k >= 0
                =>:
                    Fibonacci(k + 2) = Fibonacci(k + 1) + Fibonacci(k)
            n >= 0
            =>:
                $cassini(Fibonacci, n)
    by strong_induc n from 0:
        prove:
            $cassini(Fibonacci, n)
        claim:
            prove:
                $cassini(Fibonacci, 0)
            0 >= 0
            (-1)^0 = 1
            Fibonacci(0 + 1)^2 - Fibonacci(0 + 1) * Fibonacci(0) - Fibonacci(0)^2 = Fibonacci(1)^2 - Fibonacci(1) * Fibonacci(0) - Fibonacci(0)^2 = 1^2 - 1 * 1 - 1^2 = -1 = -1 * 1 = -((-1)^0)
            $cassini(Fibonacci, 0)

        claim:
            prove:
                forall m Z:
                    m >= 0
                    forall y Z:
                        y >= 0
                        y <= m
                        =>:
                            $cassini(Fibonacci, y)
                    =>:
                        $cassini(Fibonacci, m + 1)
            m >= 0
            $cassini(Fibonacci, m)
            Fibonacci(m + 1)^2 - Fibonacci(m + 1) * Fibonacci(m) - Fibonacci(m)^2 = -((-1)^m)
            m + 1 >= 0
            (m + 1) + 1 = m + 2
            Fibonacci((m + 1) + 1) = Fibonacci(m + 2) = Fibonacci(m + 1) + Fibonacci(m)
            Fibonacci((m + 1) + 1)^2 - Fibonacci((m + 1) + 1) * Fibonacci(m + 1) - Fibonacci(m + 1)^2 = (Fibonacci(m + 1) + Fibonacci(m))^2 - (Fibonacci(m + 1) + Fibonacci(m)) * Fibonacci(m + 1) - Fibonacci(m + 1)^2
            (Fibonacci(m + 1) + Fibonacci(m))^2 - (Fibonacci(m + 1) + Fibonacci(m)) * Fibonacci(m + 1) - Fibonacci(m + 1)^2 = -((-1)^(m + 1))
            $cassini(Fibonacci, m + 1)
```

### 6.3.5 Example

Sequence `d(n)` satisfies the initial value `d(0) = 3`, `d(1) = 1`, `forall k: N => d(k + 2) = 3 * d(k + 1) + 5 * d(k)`. Show that there is a natural number `N0` such that for all `n >= N0`, `d(n) >= 4^n`.

The inequality is not true at the first few values, so the proof starts at the
threshold `4` and proves a paired bound from there.

```litex
prop d_bound(d fn(n Z: n >= 0) Z, n Z):
    n >= 4
    d(n) >= 4^n

prop d_bound_pair(d fn(n Z: n >= 0) Z, n Z):
    n >= 4
    $d_bound(d, n)
    $d_bound(d, n + 1)

prop sufficiently_large_d_bound(d fn(n Z: n >= 0) Z, N0 Z):
    forall n Z:
        n >= 0
        n >= N0
        =>:
            d(n) >= 4^n

claim:
    prove:
        forall d fn(n Z: n >= 0) Z, n Z:
            d(0) = 3
            d(1) = 1
            forall k Z:
                k >= 0
                =>:
                    d(k + 2) = 3 * d(k + 1) + 5 * d(k)
            n >= 4
            =>:
                $d_bound_pair(d, n)
    by strong_induc n from 4:
        prove:
            $d_bound_pair(d, n)
        claim:
            prove:
                $d_bound_pair(d, 4)
            4 >= 4
            d(2) = d(0 + 2) = 3 * d(0 + 1) + 5 * d(0) = 3 * d(1) + 5 * d(0) = 3 * 1 + 5 * 3 = 18
            d(3) = d(1 + 2) = 3 * d(1 + 1) + 5 * d(1) = 3 * d(2) + 5 * d(1) = 3 * 18 + 5 * 1 = 59
            d(4) = d(2 + 2) = 3 * d(2 + 1) + 5 * d(2) = 3 * d(3) + 5 * d(2) = 3 * 59 + 5 * 18 = 267 >= 256 = 4^4
            $d_bound(d, 4)
            4 + 1 >= 4
            d(4 + 1) = d(5) = d(3 + 2) = 3 * d(3 + 1) + 5 * d(3) = 3 * d(4) + 5 * d(3) = 3 * 267 + 5 * 59 = 1096 >= 1024 = 4^5 = 4^(4 + 1)
            $d_bound(d, 4 + 1)
            $d_bound_pair(d, 4)

        claim:
            prove:
                forall m Z:
                    m >= 4
                    forall y Z:
                        y >= 4
                        y <= m
                        =>:
                            $d_bound_pair(d, y)
                    =>:
                        $d_bound_pair(d, m + 1)
            m >= 4
            $d_bound_pair(d, m)
            $d_bound(d, m)
            $d_bound(d, m + 1)
            d(m) >= 4^m
            d(m + 1) >= 4^(m + 1)
            m + 1 >= 4
            $d_bound(d, m + 1)
            (m + 1) + 1 = m + 2
            d((m + 1) + 1) = d(m + 2) = 3 * d(m + 1) + 5 * d(m)
            4^(m + 1) = 4^1 * 4^m = 4 * 4^m
            3 * d(m + 1) + 5 * d(m) >= 3 * 4^(m + 1) + 5 * 4^m = 3 * (4 * 4^m) + 5 * 4^m = 12 * 4^m + 5 * 4^m = 17 * 4^m
            17 * 4^m >= 16 * 4^m = 4^2 * 4^m = 4^(2 + m) = 4^(m + 2)
            d((m + 1) + 1) = 3 * d(m + 1) + 5 * d(m) >= 3 * 4^(m + 1) + 5 * 4^m = 17 * 4^m >= 16 * 4^m = 4^(m + 2) = 4^((m + 1) + 1)
            $d_bound(d, (m + 1) + 1)
            $d_bound_pair(d, m + 1)

claim:
    prove:
        forall d fn(n Z: n >= 0) Z:
            d(0) = 3
            d(1) = 1
            forall k Z:
                k >= 0
                =>:
                    d(k + 2) = 3 * d(k + 1) + 5 * d(k)
            =>:
                exist N0 Z st {$sufficiently_large_d_bound(d, N0)}
    claim:
        prove:
            $sufficiently_large_d_bound(d, 4)
        forall n Z:
            n >= 0
            n >= 4
            =>:
                $d_bound_pair(d, n)
                $d_bound(d, n)
                d(n) >= 4^n
    witness exist N0 Z st {$sufficiently_large_d_bound(d, N0)} from 4:
        $sufficiently_large_d_bound(d, 4)
```

## 6.4 Strong Induction

Strong induction lets the induction step use all earlier cases, not just the
immediately previous one. In Litex, `by strong_induc n from base:` exposes the
strong induction hypothesis as a nested `forall y ... y <= n => ...` fact.
This is useful when the next step needs information about several earlier
values.

### 6.4.1 Example

Problem: Let `fib(0) = 0`, `fib(1) = 1`, and
`fib(k + 1) = fib(k) + fib(k - 1)` for `k >= 1`. Show that
`fib(n) <= 2^n` for every `n >= 0`.

The induction step for `k + 1` uses both `fib(k)` and `fib(k - 1)`, so ordinary
one-step induction is less natural. Strong induction gives both bounds at once:
`fib(k) <= 2^k` and `fib(k - 1) <= 2^(k - 1)`.

```litex
claim:
    prove:
        forall fib fn(x Z: x >= 0) N, n Z:
            fib(0) = 0
            fib(1) = 1
            forall k Z:
                k >= 1
                =>:
                    fib(k + 1) = fib(k) + fib(k - 1)
            n >= 0
            =>:
                fib(n) <= 2^n
    by strong_induc n from 0:
        prove:
            fib(n) <= 2^n
        fib(0) = 0 <= 1 = 2^0

        claim:
            prove:
                forall k Z:
                    k >= 0
                    forall y Z:
                        y >= 0
                        y <= k
                        =>:
                            fib(y) <= 2^y
                    =>:
                        fib(k + 1) <= 2^(k + 1)
            by cases:
                prove:
                    fib(k + 1) <= 2^(k + 1)
                case k < 1:
                    k = 0
                    fib(k + 1) = fib(1) = 1 <= 2 = 2^1 = 2^(k + 1)
                case k >= 1:
                    k - 1 >= 0
                    k - 1 <= k
                    fib(k - 1) <= 2^(k - 1)
                    fib(k) <= 2^k
                    fib(k + 1) = fib(k) + fib(k - 1)
                    fib(k) + fib(k - 1) <= 2^k + 2^(k - 1)
                    2^k = 2^((k - 1) + 1) = 2^(k - 1) * 2^1 >= 2^(k - 1) * 1 = 2^(k - 1)
                    2^k + 2^(k - 1) <= 2^k + 2^k = 2 * 2^k = 2^1 * 2^k = 2^(1 + k) = 2^(k + 1)
                    fib(k + 1) = fib(k) + fib(k - 1) <= 2^k + 2^(k - 1) <= 2^(k + 1)
```

### 6.4.2 Example

Problem: Show that every natural number `n >= 2` has a prime divisor.

The proof splits on whether `n + 1` is prime. If it is prime, it divides itself.
If it is not prime, there is a smaller divisor `c`, and the strong induction
hypothesis gives a prime divisor of `c`; that same prime divides `n + 1`.

```litex
prop dvdN(a N, b N):
    a >= 1
    exist c Z st {b = a * c}

# This no-small-divisor formulation is convenient for the strong-induction split below.
prop prime(a N_pos):
    2 <= a
    forall b N_pos:
        2 <= b < a
        =>:
            a % b != 0

claim:
    prove:
        forall a N_pos:
            2 <= a
            =>:
                exist p N_pos st {$prime(p), a % p = 0}
    by strong_induc x from 2:
        prove:
            exist p N_pos st {$prime(p), x % p = 0}

        claim:
            prove:
                forall b N_pos:
                    2 <= b < 2
                    =>:
                        2 % b != 0
            by contra:
                prove:
                    2 % b != 0
                impossible b < 2
        $prime(2)
        witness exist t Z st {2 = t * 2} from 1
        2 % 2 = 0
        witness exist p N_pos st {$prime(p), 2 % p = 0} from 2

        claim:
            prove:
                forall n Z:
                    n >= 2
                    forall m Z:
                        2 <= m
                        m <= n
                        =>:
                            exist p N_pos st {$prime(p), m % p = 0}
                    =>:
                        exist p N_pos st {$prime(p), (n + 1) % p = 0}

            by cases exist p N_pos st {$prime(p), (n + 1) % p = 0}:
                case $prime(n + 1):
                    witness exist t Z st {n + 1 = t * (n + 1)} from 1
                    (n + 1) % (n + 1) = 0
                    witness exist p N_pos st {$prime(p), (n + 1) % p = 0} from n + 1
                case not $prime(n + 1):
                    by contra:
                        prove:
                            not forall b N_pos:
                                2 <= b < n + 1
                                =>:
                                    (n + 1) % b != 0
                        2 <= n + 1
                        $prime(n + 1)
                        impossible $prime(n + 1)

                    have by exist b N_pos st {2 <= b < n + 1, not (n + 1) % b != 0}: c

                    2 <= c < n + 1

                    (n + 1) % c = 0
                    c <= n or c >= n + 1
                    by cases:
                        prove:
                            c <= n
                        case c <= n:
                            do_nothing
                        case c >= n + 1:
                            impossible c < n + 1

                    have by exist p N_pos st {$prime(p), c % p = 0}: d

                    have by exist q Z st {(n + 1) = q * c}: e

                    have by exist r Z st {c = r * d}: f

                    witness exist t Z st {e * f * d = t * d} from e * f
                    (e * f * d) % d = 0

                    witness exist p N_pos st {$prime(p), (n + 1) % p = 0} from d:
                        n + 1 = e * c = e * (f * d) = (e * f) * d
                        (n + 1) % d = ((e * f) * d) % d = 0

claim:
    prove:
        forall n N:
            n >= 2
            =>:
                exist p N_pos st {$prime(p), $dvdN(p, n)}
    have by exist p N_pos st {$prime(p), n % p = 0}: p
    p != 0
    have by exist k Z st {n = k * p}: k
    witness exist c Z st {n = p * c} from k:
        n = k * p = p * k
    $dvdN(p, n)
    witness exist p N_pos st {$prime(p), $dvdN(p, n)} from p
```

## 6.5 Pascal's Triangle

### 6.5.1, 6.5.2. 6.5.3 Example

Pascal's triangle is a two-parameter recursive definition. The boundary values
are `1`, and the interior recurrence is:

Equivalently, the boundary cases are `P(a, 0) = 1` and `P(0, b) = 1`,
and the interior recurrence is:

```text
P(a + 1, b + 1) = P(a, b + 1) + P(a + 1, b)
```

This is the same mathematical pattern as induction on a measure such as
`a + b`: each recursive call has smaller total size. In Lean, this is where
termination checking becomes visible. In Litex documentation, the important
lesson is that the recursive definition needs a visible decreasing measure.

The examples below use `factorial(n)` instead of postfix `n!`. First define
Pascal's triangle and factorial by decreasing measures. Then prove the standard
identity

```text
P(a, b) * a! * b! = (a + b)!
```

by strong induction on the sum `a + b`. The final inequality
`P(a, b) <= (a + b)!` follows because both factorial factors are at least `1`.

> Practical note: the long algebraic chains in this example are intentionally
> explicit, but they do not have to be typed by hand. Complex-looking Litex
> expressions are good targets for AI assistance: an AI model can draft the
> expanded proof text quickly, and Litex still checks each line against the
> actual mathematical context. The useful workflow is to let AI handle the
> mechanical expansion while the verifier remains the source of trust.

```litex
have fn pascal(a Z, b Z: a >= 0, b >= 0) N by decreasing a + b from 0:
    case a = 0: 1
    case a > 0:
        case b = 0: 1
        case b > 0: pascal(a - 1, b) + pascal(a, b - 1)

pascal(0, 0) = 1
pascal(0, 3) = 1
pascal(2, 0) = 1
pascal(1, 1) = pascal(0, 1) + pascal(1, 0)

have fn factorial(n Z: n >= 0) R by decreasing n from 0:
    case n = 0: 1
    case n > 0: n * factorial(n - 1)

factorial(0) = 1
factorial(3) = 3 * factorial(2)

claim:
    prove:
        forall n Z:
            n >= 0
            =>:
                factorial(n) >= 1
    by induc n from 0:
        prove:
            factorial(n) >= 1
        factorial(0) = 1 >= 1

        forall k Z:
            k >= 0
            factorial(k) >= 1
            =>:
                k + 1 >= 1
                k + 1 > 0
                factorial(k + 1) = (k + 1) * factorial((k + 1) - 1) = (k + 1) * factorial(k)
                (k + 1) * factorial(k) >= 1 * 1 = 1
                factorial(k + 1) >= 1

prop pascal_factorial_formula_on_sum(s Z):
    s >= 0
    forall a, b Z:
        a >= 0
        b >= 0
        a + b = s
        =>:
            pascal(a, b) * factorial(a) * factorial(b) = factorial(a + b)

claim:
    prove:
        forall s Z:
            s >= 0
            =>:
                $pascal_factorial_formula_on_sum(s)
    by strong_induc s from 0:
        prove:
            $pascal_factorial_formula_on_sum(s)

        claim:
            prove:
                forall a, b Z:
                    a >= 0
                    b >= 0
                    a + b = 0
                    =>:
                        pascal(a, b) * factorial(a) * factorial(b) = factorial(a + b)
            by cases:
                prove:
                    pascal(a, b) * factorial(a) * factorial(b) = factorial(a + b)
                case a = 0:
                    b = 0 + b = a + b = 0
                    pascal(a, b) = pascal(0, 0) = 1
                    factorial(a) = factorial(0) = 1
                    factorial(b) = factorial(0) = 1
                    factorial(a + b) = factorial(0) = 1
                    pascal(a, b) * factorial(a) * factorial(b) = 1 * 1 * 1 = 1 = factorial(a + b)
                case a > 0:
                    a + b > 0
                    impossible a + b = 0
        $pascal_factorial_formula_on_sum(0)

        claim:
            prove:
                forall step_s Z:
                    step_s >= 0
                    forall y Z:
                        y >= 0
                        y <= step_s
                        =>:
                            $pascal_factorial_formula_on_sum(y)
                    =>:
                        $pascal_factorial_formula_on_sum(step_s + 1)

            step_s + 1 >= 0
            claim:
                prove:
                    forall a, b Z:
                        a >= 0
                        b >= 0
                        a + b = step_s + 1
                        =>:
                            pascal(a, b) * factorial(a) * factorial(b) = factorial(a + b)
                by cases:
                    prove:
                        pascal(a, b) * factorial(a) * factorial(b) = factorial(a + b)
                    case a = 0:
                        b = 0 + b = a + b = step_s + 1
                        pascal(a, b) = pascal(0, b) = 1
                        factorial(a) = factorial(0) = 1
                        factorial(a + b) = factorial(b)
                        pascal(a, b) * factorial(a) * factorial(b) = 1 * 1 * factorial(b) = factorial(b) = factorial(a + b)
                    case a > 0:
                        by cases:
                            prove:
                                pascal(a, b) * factorial(a) * factorial(b) = factorial(a + b)
                            case b = 0:
                                pascal(a, b) = pascal(a, 0) = 1
                                factorial(b) = factorial(0) = 1
                                factorial(a + b) = factorial(a)
                                pascal(a, b) * factorial(a) * factorial(b) = 1 * factorial(a) * 1 = factorial(a) = factorial(a + b)
                            case b > 0:
                                a - 1 >= 0
                                b - 1 >= 0
                                (a + b) - 1 = (step_s + 1) - 1 = step_s
                                (a - 1) + b = (a + b) - 1 = step_s
                                a + (b - 1) = (a + b) - 1 = step_s
                                $pascal_factorial_formula_on_sum(step_s)
                                pascal(a - 1, b) * factorial(a - 1) * factorial(b) = factorial((a - 1) + b)
                                pascal(a, b - 1) * factorial(a) * factorial(b - 1) = factorial(a + (b - 1))
                                pascal(a, b) = pascal(a - 1, b) + pascal(a, b - 1)
                                factorial(a) = a * factorial(a - 1)
                                factorial(b) = b * factorial(b - 1)
                                a + b > 0
                                factorial(a + b) = (a + b) * factorial(a + b - 1)
                                pascal(a, b) * factorial(a) * factorial(b) = (pascal(a - 1, b) + pascal(a, b - 1)) * factorial(a) * factorial(b)
                                (pascal(a - 1, b) + pascal(a, b - 1)) * factorial(a) * factorial(b) = pascal(a - 1, b) * factorial(a) * factorial(b) + pascal(a, b - 1) * factorial(a) * factorial(b)
                                pascal(a - 1, b) * factorial(a) * factorial(b) = pascal(a - 1, b) * (a * factorial(a - 1)) * factorial(b) = a * pascal(a - 1, b) * factorial(a - 1) * factorial(b)
                                pascal(a, b - 1) * factorial(a) * factorial(b) = pascal(a, b - 1) * factorial(a) * (b * factorial(b - 1)) = b * pascal(a, b - 1) * factorial(a) * factorial(b - 1)
                                pascal(a - 1, b) * factorial(a) * factorial(b) + pascal(a, b - 1) * factorial(a) * factorial(b) = a * (pascal(a - 1, b) * factorial(a - 1) * factorial(b)) + b * (pascal(a, b - 1) * factorial(a) * factorial(b - 1))
                                a * (pascal(a - 1, b) * factorial(a - 1) * factorial(b)) + b * (pascal(a, b - 1) * factorial(a) * factorial(b - 1)) = a * factorial((a - 1) + b) + b * factorial(a + (b - 1))
                                a * factorial((a - 1) + b) + b * factorial(a + (b - 1)) = a * factorial(a + b - 1) + b * factorial(a + b - 1)
                                a * factorial(a + b - 1) + b * factorial(a + b - 1) = (a + b) * factorial(a + b - 1)
                                (a + b) * factorial(a + b - 1) = factorial(a + b)
                                pascal(a, b) * factorial(a) * factorial(b) = factorial(a + b)
            $pascal_factorial_formula_on_sum(step_s + 1)

claim:
    prove:
        forall a, b Z:
            a >= 0
            b >= 0
            =>:
                pascal(a, b) * factorial(a) * factorial(b) = factorial(a + b)
    a + b >= 0
    $pascal_factorial_formula_on_sum(a + b)
    pascal(a, b) * factorial(a) * factorial(b) = factorial(a + b)

claim:
    prove:
        forall a, b Z:
            a >= 0
            b >= 0
            =>:
                pascal(a, b) <= factorial(a + b)
    a + b >= 0
    $pascal_factorial_formula_on_sum(a + b)
    pascal(a, b) * factorial(a) * factorial(b) = factorial(a + b)
    factorial(a) >= 1
    factorial(b) >= 1
    pascal(a, b) >= 0
    pascal(a, b) = pascal(a, b) * 1 <= pascal(a, b) * factorial(a) = pascal(a, b) * factorial(a) * 1 <= pascal(a, b) * factorial(a) * factorial(b) = factorial(a + b)
```

## 6.6 Division Algorithm

Problem roadmap from the source examples:

1. Define an integer remainder function and an integer quotient function by
   recursion. The definition must be well founded: every recursive call has to
   move to a strictly smaller size.

2. Prove that every input integer is recovered by adding its remainder to the
   divisor multiplied by its quotient.

3. Prove that when the divisor is positive, the remainder is never negative.

4. Prove that when the divisor is positive, the remainder is strictly smaller
   than the divisor.

5. Prove that every integer has a standard representative modulo any positive
   integer divisor: the representative lies in the usual remainder range, and it
   is congruent to the original integer modulo that divisor.

6. Strengthen the previous result by proving uniqueness: if two standard
   representatives are both congruent to the same integer modulo the same
   positive divisor, then the two representatives are equal.

The first two items can already be tested directly in Litex. The initial
`claim` blocks prove the arithmetic facts needed to justify the recursive
decrease. The remaining `know` block records the base case and step case for
the measure induction proof of the quotient-remainder identity.

```litex
claim:
    prove:
        forall x, y R:
            0 <= x
            0 <= y
            x^2 < y^2
            =>:
                x < y

    by contra:
        prove:
            x < y
        y <= x
        y^2 <= x^2
        impossible x^2 < y^2

claim:
    prove:
        forall n, d Z:
            n * d < 0
            =>:
                abs(2 * (n + d) - d)^2 < abs(2 * n - d)^2

    0 < -(n * d)
    0 < 8
    0 < 8 * (-(n * d))
    8 * (-(n * d)) = -8 * n * d
    0 < -8 * n * d
    (2 * (n + d) - d)^2 < (2 * (n + d) - d)^2 + (-8 * n * d) = (2 * n - d)^2
    abs(2 * (n + d) - d)^2 = (2 * (n + d) - d)^2 < (2 * n - d)^2 = abs(2 * n - d)^2

claim:
    prove:
        forall n, d Z:
            n * d < 0
            =>:
                abs(2 * (n + d) - d) < abs(2 * n - d)

    0 <= abs(2 * (n + d) - d)
    0 <= abs(2 * n - d)
    abs(2 * (n + d) - d)^2 < abs(2 * n - d)^2

claim:
    prove:
        forall n, d Z:
            n * d >= 0
            0 < d * (n - d)
            =>:
                abs(2 * (n - d) - d)^2 < abs(2 * n - d)^2

    0 < 8
    0 < 8 * (d * (n - d))
    8 * (d * (n - d)) = 8 * d * (n - d)
    0 < 8 * d * (n - d)
    (2 * (n - d) - d)^2 < (2 * (n - d) - d)^2 + 8 * d * (n - d) = (2 * n - d)^2
    abs(2 * (n - d) - d)^2 = (2 * (n - d) - d)^2 < (2 * n - d)^2 = abs(2 * n - d)^2

claim:
    prove:
        forall n, d Z:
            n * d >= 0
            0 < d * (n - d)
            =>:
                abs(2 * (n - d) - d) < abs(2 * n - d)

    0 <= abs(2 * (n - d) - d)
    0 <= abs(2 * n - d)
    abs(2 * (n - d) - d)^2 < abs(2 * n - d)^2

have fn fmod(n Z, d Z) Z by decreasing abs(2 * n - d) from 0:
    case n * d < 0: fmod(n + d, d)
    case n * d >= 0:
        case 0 < d * (n - d): fmod(n - d, d)
        case 0 >= d * (n - d):
            case n = d: 0
            case n != d: n

have fn fdiv(n Z, d Z) Z by decreasing abs(2 * n - d) from 0:
    case n * d < 0: fdiv(n + d, d) - 1
    case n * d >= 0:
        case 0 < d * (n - d): fdiv(n - d, d) + 1
        case 0 >= d * (n - d):
            case n = d: 1
            case n != d: 0

prop fmod_add_fdiv_at_measure(m Z):
    forall n, d Z:
        abs(2 * n - d) = m
        =>:
            fmod(n, d) + d * fdiv(n, d) = n

know:
    $fmod_add_fdiv_at_measure(0)
    forall m Z:
        m >= 0
        forall y Z:
            y >= 0
            y <= m
            =>:
                $fmod_add_fdiv_at_measure(y)
        =>:
            $fmod_add_fdiv_at_measure(m + 1)

by strong_induc m from 0:
    prove:
        $fmod_add_fdiv_at_measure(m)

    prove from m = 0:
        $fmod_add_fdiv_at_measure(0)

    prove strong_induc:
        $fmod_add_fdiv_at_measure(m + 1)

claim:
    prove:
        forall n, d Z:
            fmod(n, d) + d * fdiv(n, d) = n

    forall n1, d1 Z:
        abs(2 * n1 - d1) >= 0
        $fmod_add_fdiv_at_measure(abs(2 * n1 - d1))
        fmod(n1, d1) + d1 * fdiv(n1, d1) = n1
```

The division algorithm says that for natural numbers `n` and positive `d`,
there are `q` and `r` such that

```text
n = d * q + r
0 <= r < d
```

A recursive proof subtracts `d` until the remainder is smaller than `d`. This
is naturally a well-founded recursion proof: the argument decreases each time.

Litex can express the final existence statement directly:

```litex
prop division_result(n N, d N_pos, q N):
    exist r N st {n = d * q + r, r < d}

prop division_algorithm(n N, d N_pos):
    exist q N st {$division_result(n, d, q)}
```

## 6.7 Greatest Common Divisors

Problem roadmap from the source examples:

1. Define the greatest-common-divisor function on two integers by the Euclidean
   algorithm. If the second input is nonzero, recurse using the second input and
   the remainder from division; if the second input is zero, return the absolute
   value of the first input. The recursive definition must be well founded.

2. Prove that the greatest common divisor of two integers is always
   nonnegative.

3. Prove that the greatest common divisor of two integers divides each of the
   original two integers. The source proof naturally separates this into two
   mutually dependent statements: one for the left input and one for the right
   input.

4. Define the two coefficient functions from the extended Euclidean algorithm.
   These functions record how to express the greatest common divisor as an
   integer linear combination of the original two inputs.

5. Prove the core identity for the extended Euclidean algorithm: the two
   coefficient functions really do produce an integer linear combination equal
   to the greatest common divisor.

6. Deduce Bezout's identity: for any two integers, there exist two integer
   coefficients whose linear combination of the original integers is their
   greatest common divisor.

7. Prove the maximality property of the greatest common divisor: any integer
   that divides both original integers also divides their greatest common
   divisor.

The following tested Litex block should be read after the `fmod` definition in
Section 6.6. The first `know` block records the remainder-size facts needed for
termination. The later `know` blocks record the base and step facts for the
measure induction proofs.

```litex
know:
    forall a, b Z:
        0 < b
        =>:
            abs(fmod(a, b)) < abs(b)
    forall a, b Z:
        b < 0
        =>:
            abs(fmod(a, -b)) < abs(b)

have fn gcd(a Z, b Z) Z by decreasing abs(b) from 0:
    case 0 < b: gcd(b, fmod(a, b))
    case 0 >= b:
        case b < 0: gcd(b, fmod(a, -b))
        case b >= 0:
            case 0 <= a: a
            case 0 > a: -a

prop gcd_nonneg_at_measure(m Z):
    forall a, b Z:
        abs(b) = m
        =>:
            gcd(a, b) >= 0

know:
    $gcd_nonneg_at_measure(0)
    forall m Z:
        m >= 0
        forall y Z:
            y >= 0
            y <= m
            =>:
                $gcd_nonneg_at_measure(y)
        =>:
            $gcd_nonneg_at_measure(m + 1)

by strong_induc m from 0:
    prove:
        $gcd_nonneg_at_measure(m)

    prove from m = 0:
        $gcd_nonneg_at_measure(0)

    prove strong_induc:
        $gcd_nonneg_at_measure(m + 1)

claim:
    prove:
        forall a, b Z:
            gcd(a, b) >= 0

    forall a1, b1 Z:
        abs(b1) >= 0
        $gcd_nonneg_at_measure(abs(b1))
        gcd(a1, b1) >= 0

prop divides(d Z, n Z):
    exist k Z st {n = d * k}

prop gcd_divides_inputs_at_measure(m Z):
    forall a, b Z:
        abs(b) = m
        =>:
            $divides(gcd(a, b), a)
            $divides(gcd(a, b), b)

know:
    $gcd_divides_inputs_at_measure(0)
    forall m Z:
        m >= 0
        forall y Z:
            y >= 0
            y <= m
            =>:
                $gcd_divides_inputs_at_measure(y)
        =>:
            $gcd_divides_inputs_at_measure(m + 1)

by strong_induc m from 0:
    prove:
        $gcd_divides_inputs_at_measure(m)

    prove from m = 0:
        $gcd_divides_inputs_at_measure(0)

    prove strong_induc:
        $gcd_divides_inputs_at_measure(m + 1)

claim:
    prove:
        forall a, b Z:
            $divides(gcd(a, b), a)

    forall a1, b1 Z:
        abs(b1) >= 0
        $gcd_divides_inputs_at_measure(abs(b1))
        $divides(gcd(a1, b1), a1)

claim:
    prove:
        forall a, b Z:
            $divides(gcd(a, b), b)

    forall a1, b1 Z:
        abs(b1) >= 0
        $gcd_divides_inputs_at_measure(abs(b1))
        $divides(gcd(a1, b1), b1)

have fn egcd_pair(a Z, b Z) cart(Z, Z) by decreasing abs(b) from 0:
    case 0 < b: (egcd_pair(b, fmod(a, b))[2], egcd_pair(b, fmod(a, b))[1] - fdiv(a, b) * egcd_pair(b, fmod(a, b))[2])
    case 0 >= b:
        case b < 0: (egcd_pair(b, fmod(a, -b))[2], egcd_pair(b, fmod(a, -b))[1] + fdiv(a, -b) * egcd_pair(b, fmod(a, -b))[2])
        case b >= 0:
            case 0 <= a: (1, 0)
            case 0 > a: (-1, 0)

have fn egcd_l(a Z, b Z) Z = egcd_pair(a, b)[1]

have fn egcd_r(a Z, b Z) Z = egcd_pair(a, b)[2]

prop egcd_identity_at_measure(m Z):
    forall a, b Z:
        abs(b) = m
        =>:
            egcd_l(a, b) * a + egcd_r(a, b) * b = gcd(a, b)

know:
    $egcd_identity_at_measure(0)
    forall m Z:
        m >= 0
        forall y Z:
            y >= 0
            y <= m
            =>:
                $egcd_identity_at_measure(y)
        =>:
            $egcd_identity_at_measure(m + 1)

by strong_induc m from 0:
    prove:
        $egcd_identity_at_measure(m)

    prove from m = 0:
        $egcd_identity_at_measure(0)

    prove strong_induc:
        $egcd_identity_at_measure(m + 1)

claim:
    prove:
        forall a, b Z:
            egcd_l(a, b) * a + egcd_r(a, b) * b = gcd(a, b)

    forall a1, b1 Z:
        abs(b1) >= 0
        $egcd_identity_at_measure(abs(b1))
        egcd_l(a1, b1) * a1 + egcd_r(a1, b1) * b1 = gcd(a1, b1)
```

Instead of defining two mutually recursive coefficient functions, the extended
Euclidean algorithm is represented by the single recursive function
`egcd_pair`. The two coefficient functions are projections from that pair.

The Euclidean algorithm defines `gcd(a, b)` recursively using remainders. The
mathematical facts proved by induction are:

- `gcd(a, b)` divides `a`;
- `gcd(a, b)` divides `b`;
- any common divisor of `a` and `b` divides `gcd(a, b)`;
- there are integers `x` and `y` such that `x * a + y * b = gcd(a, b)`.

These are excellent examples of induction over a recursive algorithm. The
tested code above covers the `gcd` layer and the extended Euclidean identity.
Bezout's identity and the maximality theorem remain as direct next targets.
