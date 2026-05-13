# Chapter 3 — Parity and divisibility

This chapter is about elementary properties of natural numbers and integers:
parity, divisibility, and congruence modulo `n`. There are no major new proof
forms here. Instead, the point is to practice the style from the previous
chapters in a setting where definitions matter.

In Litex, we can
introduce predicates such as `$odd(a)` and `$even(a)` directly, define them by
existence of an integer witness, and then reuse the resulting facts in later
proofs. This makes the chapter a useful bridge from calculation proofs to
structured proofs: the user writes the mathematical definitions, witnesses, and
chains explicitly, while Litex checks the routine algebra and stores the facts
that have been established.

## 3.1 Definitions; parity

### 3.1.1

The definition of oddness and evenness can be introduced as a Litex proposition:

```litex
prop odd(a Z):
    exist k Z st {a = 2 * k + 1}

prop even(a Z):
    exist k Z st {a = 2 * k}
```

A `prop` definition has the general shape

<!-- litex:skip-test -->
```litex
prop prop_name(arg1 Type1, arg2 Type2, ...):
    Fact1
    Fact2
    ...
```

It defines a proposition whose arguments must satisfy the declared types, and
whose meaning is exactly the facts listed in the body. Here `$odd(a)` means:
`a` is an integer and there exists an integer `k` such that `a = 2 * k + 1`.

Here "type" is Litex's parameter-type notation, not a type-theory type. Litex
uses a set-theoretic view: 1. `a S` (S is an object) means `a $in S` 2.  action-like forms
: `A set`, `A nonempty_set`, and `A finite_set`, which means `$is_set(A)`, `$is_nonempty_set(A)`, and `$is_finite_set(A)` respectively.

> Litex also has the `%` keyword for remainders. A fact such as `3 % 2 = 1`
> corresponds to the existence of an integer quotient `k` with
> `3 = 2 * k + 1`. The proposition above writes that existential content
> explicitly.

Show that 7 is odd.

So proving `$odd(7)` means proving an existential fact: we must provide an
integer witness `k` such that `7 = 2 * k + 1`. 

```litex
prop odd(a Z):
    exist k Z st {a = 2 * k + 1}

witness exist k Z st {7 = 2 * k + 1} from 3
$odd(7)
```

In Litex, we can use the `witness <EXIST FACT> from <OBJECTS>` keyword to prove an existential fact by providing objects that satisfy the existentially quantified conditions.

```lean
def Odd (a : ℤ) : Prop := ∃ k, a = 2 * k + 1

example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers
```

Lean has rich libraries and expressive syntax, but it also has many tactics and
idioms to remember. Litex takes the opposite approach here: it gives the user a
small set of direct statements, such as `prove`, `witness exist`, and equality
chains, so the proof script stays close to the mathematical sentence being
written.

### 3.1.2

Show that -3 is odd.

```litex
prop odd(a Z):
    exist k Z st {a = 2 * k + 1}

witness exist k Z st {-3 = 2 * k + 1} from -2
$odd(-3)
```

### 3.1.3

Prove that if n is an odd integer, then 3n + 2 is odd.

```litex
prop odd(a Z):
    exist k Z st {a = 2 * k + 1}

claim:
    prove:
        forall n Z:
            $odd(n)
            =>:
                $odd(3 * n + 2)
    have by exist k Z st {n = 2 * k + 1}: k
    witness exist l Z st {3 * n + 2 = 2 * l + 1} from 3 * k + 2:
        3 * n + 2 = 3 * (2 * k + 1) + 2 = 2 * (3 * k + 2) + 1
```

The line `have by exist k Z st {n = 2 * k + 1}: k` uses the
existential information inside `$odd(n)` to introduce a concrete object `k`
that satisfies the displayed condition. The witness statement then proves the
new existential goal for `$odd(3 * n + 2)`: `from 3 * k + 2` proposes the
object, and the indented calculation proves that this object really satisfies
the condition `3 * n + 2 = 2 * l + 1`.

The name of an existentially bound parameter is local to that existential fact.
For example, `exist l Z st {3 * n + 2 = 2 * l + 1}` has the same meaning as
`exist m Z st {3 * n + 2 = 2 * m + 1}`. In this proof we use `l` in the second
existential statement instead of reusing `k`, because `k` has already been
introduced as the witness for `n = 2 * k + 1`.

Litex also has compact forms for common proof shapes. A multiline `forall` fact
can be written on one line as:

<!-- litex:skip-test -->
```litex
forall! <arg type, ...>: <FACT1> ... <FACTN> => {<THENFACT1> ... <THENFACTN>}
```

If there are no extra assumptions on the parameters, the `: <FACT1> ...
<FACTN>` part can be omitted.

For example, the theorem above could be written schematically as
`forall! n Z: $odd(n) => {$odd(3 * n + 2)}`. Similarly, a `claim` does not have
to be written in the longer

<!-- litex:skip-test -->
```litex
claim:
    prove:
        <FACT_YOU_WANT_TO_PROVE>
    <STATEMENT1>
    ...
```

form. It can also be written as:

<!-- litex:skip-test -->
```litex
claim <FACT_YOU_WANT_TO_PROVE>:
    <STATEMENT1>
    ...
```

```litex
prop odd(a Z):
    exist k Z st {a = 2 * k + 1}

claim forall! n Z: $odd(n) => {$odd(3 * n+ 2)}:
    have by exist k Z st {n = 2 * k + 1}: k
    witness exist l Z st {3 * n + 2 = 2 * l + 1} from 3 * k + 2:
        3 * n + 2 = 3 * (2 * k + 1) + 2 = 2 * (3 * k + 2) + 1
```

Litex provides both multi-line and one-line versions of `forall` and `claim`.
The multi-line form is easier to read when the assumptions or goal need space;
the one-line form is convenient for short statements where the mathematical
shape is already clear.

To help you be familiar with the one-line form, we write the following examples in one-line form.

### 3.1.4

Let n be an integer. Prove that if n is odd, then 7n - 4 is odd.

```litex
prop odd(a Z):
    exist k Z st {a = 2 * k + 1}

claim forall! n Z: $odd(n) => {$odd(7 * n - 4)}:
    have by exist k Z st {n = 2 * k + 1}: k
    witness exist l Z st {7 * n - 4 = 2 * l + 1} from 7 * k + 1:
        7 * n - 4 = 7 * (2 * k + 1) - 4 = 2 * (7 * k + 1) + 1
```

### 3.1.5

Prove that if the integers x and y are odd, then x + y + 1 is odd.

```litex
prop odd(a Z):
    exist k Z st {a = 2 * k + 1}

claim forall! x, y Z: $odd(x), $odd(y) => {$odd(x + y + 1)}:
    have by exist k Z st {x = 2 * k + 1}: k
    have by exist l Z st {y = 2 * l + 1}: l
    witness exist m Z st {x + y + 1 = 2 * m + 1} from k + l + 1:
        x + y + 1 = (2 * k + 1) + (2 * l + 1) + 1 = 2 * (k + l + 1) + 1
```

### 3.1.6

Prove that if the integers x and y are odd, then x*y + 2*y is odd.

```litex
prop odd(a Z):
    exist k Z st {a = 2 * k + 1}

claim forall! x, y Z: $odd(x), $odd(y) => {$odd(x * y + 2 * y)}:
    have by exist k Z st {x = 2 * k + 1}: k
    have by exist l Z st {y = 2 * l + 1}: l
    witness exist m Z st {x * y + 2 * y = 2 * m + 1} from 2 * k * l + 3 * l + k + 1:
        x * y + 2 * y = (2 * k + 1) * (2 * l + 1) + 2 * (2 * l + 1) = 2 * (2 * k * l + 3 * l + k + 1) + 1
```

### 3.1.7

Let m be an integer. Prove that if m is odd, then 3m - 5 is even.

```litex
prop odd(a Z):
    exist k Z st {a = 2 * k + 1}

prop even(a Z):
    exist k Z st {a = 2 * k}

claim forall! m Z: $odd(m) => {$even(3 * m - 5)}:
    have by exist k Z st {m = 2 * k + 1}: k
    witness exist l Z st {3 * m - 5 = 2 * l} from 3 * k - 1:
        3 * m - 5 = 3 * (2 * k + 1) - 5 = 2 * (3 * k - 1)
```



### 3.1.8

Let n be an even integer. Prove that n^2 + 2n - 5 is odd.

```litex
prop even(a Z):
    exist k Z st {a = 2 * k}

prop odd(a Z):
    exist k Z st {a = 2 * k + 1}

claim forall! n Z: $even(n) => {$odd(n^2 + 2 * n - 5)}:
    have by exist k Z st {n = 2 * k}: k
    witness exist l Z st {n^2 + 2 * n - 5 = 2 * l + 1} from 2 * k^2 + 2 * k - 3:
        n^2 + 2 * n - 5 = (2 * k)^2 + 2 * (2 * k) - 5 = 2 * (2 * k^2 + 2 * k - 3) + 1
```

### 3.1.9

In fact every integer is either even or odd.

Two builtin facts about remainders do the main work here. First, for any integer
`a` and positive integer `b`, Litex knows that the remainder must be one of
`0, 1, ..., b - 1`; in particular, `n % 2 = 0 or n % 2 = 1`. This is why the
`by cases` split below is accepted as covering all cases. Second, a remainder
fact such as `a % b = c` gives an existential quotient fact:
`exist k Z st {a = b * k + c}`. In the two branches below, that quotient witness
is exactly what lets us prove either `$even(n)` or `$odd(n)`.

```litex
prop even(a Z):
    exist k Z st {a = 2 * k}

prop odd(a Z):
    exist k Z st {a = 2 * k + 1}

claim:
    prove:
        forall n Z:
            $even(n) or $odd(n)
    by cases $even(n) or $odd(n):
        case n % 2 = 0:
            have by exist k Z st {n = 2 * k + 0}: k
            n = 2 * k + 0 = 2 * k
            witness exist l Z st {n = 2 * l} from k
            $even(n)
        case n % 2 = 1:
            have by exist k Z st {n = 2 * k + 1}: k
            $odd(n)

claim:
    prove:
        forall n Z:
            $even(n^2 + n + 4)
    by cases:
        prove:
            $even(n^2 + n + 4)
        case $even(n):
            have by exist k Z st {n = 2 * k}: k
            witness exist l Z st {n^2 + n + 4 = 2 * l} from 2 * k^2 + k + 2:
                n^2 + n + 4 = (2 * k)^2 + 2 * k + 4 = 2 * (2 * k^2 + k + 2)
        case $odd(n):
            have by exist k Z st {n = 2 * k + 1}: k
            witness exist l Z st {n^2 + n + 4 = 2 * l} from 2 * k^2 + 3 * k + 3:
                n^2 + n + 4 = (2 * k + 1)^2 + (2 * k + 1) + 4 = 2 * (2 * k^2 + 3 * k + 3)
```



## 3.2 Divisibility

Divisibility is another definition by existence. For integers, `$dvdZ(a, b)`
means that there is an integer `c` with `b = a * c`; for natural numbers,
`$dvdN(a, b)` means the same thing with `c` natural.

```litex
prop dvdZ(a Z, b Z):
    exist c Z st {b = a * c}
prop dvdN(a N, b N):
    exist c N st {b = a * c}
```

The key move is the same as in the parity examples. To prove a divisibility
statement, give the missing multiplier with `witness`. To use a divisibility
hypothesis, unpack the multiplier with `have by exist`.

### 3.2.1

Show that the natural number 88 is divisible by 11.

```litex
prop dvdN(a N, b N):
    exist c N st {b = a * c}

claim:
    prove:
        $dvdN(11, 88)
    witness exist c N st {88 = 11 * c} from 8:
        88 = 11 * 8
```

### 3.2.2

Show that the integer 6 is divisible by -2.

```litex
prop dvdZ(a Z, b Z):
    exist c Z st {b = a * c}

claim:
    prove:
        $dvdZ(-2, 6)
    witness exist c Z st {6 = (-2) * c} from -3:
        6 = (-2) * (-3)
```

### 3.2.3

Let a and b be integers and suppose that a | b. Show that a | b^2 + 2b.

```litex
prop dvdZ(a Z, b Z):
    exist c Z st {b = a * c}

claim forall! a, b Z: $dvdZ(a, b) => {$dvdZ(a, b^2 + 2 * b)}:
    have by exist k Z st {b = a * k}: k
    witness exist l Z st {b^2 + 2 * b = a * l} from a * k^2 + 2 * k:
        b^2 + 2 * b = (a * k)^2 + 2 * (a * k) = a^2 * k^2 + 2 * a * k = a * (a * k^2 + 2 * k)
```

Here `have by exist` names the multiplier hidden inside the assumption
`$dvdZ(a, b)`. Once `b = a * k` is available, the rest is just algebra:
factor one copy of `a` out of `b^2 + 2b`.

### 3.2.4

Let a, b and c be natural numbers and suppose that a | b and b^2 | c. Show that a^2 | c.

```litex
prop dvdN(a Z, b Z):
    exist t N st {b = a * t}

claim:
    prove:
        forall a, b, c N:
            $dvdN(a, b)
            $dvdN(b^2, c)
            =>:
                $dvdN(a^2, c)
    have by exist k N st {b = a * k}: k
    have by exist l N st {c = b^2 * l}: l
    witness exist t N st {c = a^2 * t} from k * k * l:
        c = b^2 * l = b * b * l = (a * k) * (a * k) * l = a^2 * (k * k * l)
```

This proof unpacks two divisibility hypotheses. If `b = a * k` and
`c = b^2 * l`, then `c = a^2 * (k * k * l)`, so the witness for `a^2 | c`
is `k * k * l`.

### 3.2.5

Let x, y and z be natural numbers and suppose that x*y | z. Show that x | z.

```litex
prop dvdN(a N, b N):
    exist c N st {b = a * c}

claim:
    prove:
        forall x, y, z N:
            $dvdN(x * y, z)
            =>:
                $dvdN(x, z)
    have by exist k N st {z = (x * y) * k}: k
    witness exist c N st {z = x * c} from y * k:
        z = (x * y) * k = x * (y * k)
```

This is a good example of why the witness matters. From `(x * y) | z`, Litex
extracts some `k` such that `z = (x * y) * k`. To show `x | z`, the new
witness is not `k`, but `y * k`.

### 3.2.6

Show that 12 is not divisible by 5.

```litex
prop dvdN(a N, b N):
    exist c N st {b = a * c}

claim:
    prove:
        not $dvdN(5, 12)
    by contra not $dvdN(5, 12):
        have by exist c N st {12 = 5 * c}: a
        a $in N
        a $in Z
        witness exist c Z st {12 = 5 * c + 0} from a
        12 % 5 = 0
        2 = 12 % 5
        impossible 2 = 0
```

> The statement `12 % 5 = 0` is the modulo form of an existential division fact: it says that there is an integer quotient `c` such that `12 = 5 * c + 0`. In Litex, these two styles express the same mathematical relationship. When the numbers are concrete, such as `12` and `5`, the `%` notation is often the shortest way to describe the integer remainder. When the quotient or the numbers are symbolic, an `exist` statement can be more natural because it gives a name to the quotient and lets later steps use that object directly. Neither style is more fundamental; choose the one that makes the current proof easier to read.

### 3.2.7

Let a and b be natural numbers, with b positive, and suppose that a divides b. Show that a <= b.

If `a | b`, then `b = a * k` for some natural number `k`. Since `b > 0`,
that multiplier cannot be `0`, so `k >= 1`. Therefore
`a = a * 1 <= a * k = b`.

```litex
prop dvdN(a N, b N):
    exist c N st {b = a * c}

claim:
    prove:
        forall a, b N:
            $dvdN(a, b)
            b > 0
            =>:
                a <= b
    have by exist k N st {b = a * k}: k
    by cases a <= b:
        case k = 0:
            b = a * k = 0
            impossible b > 0
        case k != 0:
            k >= 1
            a = a * 1 <= a * k = b
```

The reason `k >= 1` is true because `k $in N` and `k != 0` is a builtin rule. The case `k = 0` is impossible because `b > 0` and `b = a * k = 0`.

Lean Example for comparison:

```Lean
example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by
  obtain ⟨k, hk⟩ := hab
  have H1 :=
    calc
      0 < b := hb
      _ = a * k := hk
  cancel a at H1
  have H : 1 ≤ k := H1
  calc
    a = a * 1 := by ring
    _ ≤ a * k := by rel [H]
    _ = b := by rw [hk]
```

### 3.2.8

Let a and b be natural numbers, with b positive, and suppose that a divides b. Show that a is positive.

This is another contradiction proof. If `a = 0`, then every product `a * k`
is `0`; but from `a | b` we have `b = a * k`, contradicting `b > 0`.

```litex
prop dvdN(a N, b N):
    exist c N st {b = a * c}

claim:
    prove:
        forall a, b N:
            $dvdN(a, b)
            b > 0
            =>:
                0 < a
    by cases 0 < a:
        case a = 0:
            have by exist k N st {b = a * k}: k
            b = a * k = 0 * k = 0
            impossible b > 0
        case a != 0:
            a >= 1 > 0
```

## 3.3 Modular arithmetic: theory

In this chapter we write modular congruence as a `prop`. The statement
`$mod_eq(a, b, n)` means that `a - b` is a multiple of `n`.

```litex
prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}
```

This definition is intentionally close to the usual mathematical definition:
to prove a congruence, give the integer quotient as a `witness`.

### 3.3.1

Show that 11 ≡ 3 (mod 4).

```litex
prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}

claim:
    prove:
        $mod_eq(11, 3, 4)
    witness exist k Z st {11 - 3 = 4 * k} from 2:
        11 - 3 = 4 * 2
```

### 3.3.2

Show that -5 ≡ 1 (mod 3).

```litex
prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}

claim:
    prove:
        $mod_eq(-5, 1, 3)
    witness exist k Z st {(-5) - 1 = 3 * k} from -2:
        (-5) - 1 = 3 * (-2)
```

### 3.3.3

Addition rule for modular arithmetic: if `a ≡ b (mod n)` and
`c ≡ d (mod n)`, then `a + c ≡ b + d (mod n)`.

Litex's proof style is direct: extract the two quotients, then give the new
quotient.

```litex
prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}

claim:
    prove:
        forall a, b, c, d, n Z:
            $mod_eq(a, b, n)
            $mod_eq(c, d, n)
            =>:
                $mod_eq(a + c, b + d, n)
    have by exist x Z st {a - b = n * x}: x
    have by exist y Z st {c - d = n * y}: y
    witness exist k Z st {(a + c) - (b + d) = n * k} from x + y:
        (a + c) - (b + d) = (a - b) + (c - d) = n * x + n * y = n * (x + y)
```

### 3.3.4

Subtraction rule for modular arithmetic: if `a ≡ b (mod n)` and
`c ≡ d (mod n)`, then `a - c ≡ b - d (mod n)`.

```litex
prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}

claim:
    prove:
        forall a, b, c, d, n Z:
            $mod_eq(a, b, n)
            $mod_eq(c, d, n)
            =>:
                $mod_eq(a - c, b - d, n)
    have by exist x Z st {a - b = n * x}: x
    have by exist y Z st {c - d = n * y}: y
    witness exist k Z st {(a - c) - (b - d) = n * k} from x - y:
        (a - c) - (b - d) = (a - b) - (c - d) = n * x - n * y = n * (x - y)
```

### 3.3.5

Negation rule for modular arithmetic: if `a ≡ b (mod n)`, then
`-a ≡ -b (mod n)`.

```litex
prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}

claim:
    prove:
        forall a, b, n Z:
            $mod_eq(a, b, n)
            =>:
                $mod_eq(-a, -b, n)
    have by exist x Z st {a - b = n * x}: x
    witness exist k Z st {(-a) - (-b) = n * k} from -x:
        (-a) - (-b) = -(a - b) = -(n * x) = n * (-x)
```

### 3.3.6

Multiplication rule for modular arithmetic: if `a ≡ b (mod n)` and
`c ≡ d (mod n)`, then `a * c ≡ b * d (mod n)`.

```litex
prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}

claim:
    prove:
        forall a, b, c, d, n Z:
            $mod_eq(a, b, n)
            $mod_eq(c, d, n)
            =>:
                $mod_eq(a * c, b * d, n)
    have by exist x Z st {a - b = n * x}: x
    have by exist y Z st {c - d = n * y}: y
    witness exist k Z st {a * c - b * d = n * k} from x * c + b * y:
        a * c - b * d = (a - b) * c + b * (c - d) = n * x * c + b * (n * y) = n * (x * c + b * y)
```

### 3.3.7

There is no general division rule for modular arithmetic. For example,
`10 ≡ 18 (mod 4)` and `2 ≡ 6 (mod 4)`, but dividing both sides would compare
`10 / 2 = 5` and `18 / 6 = 3`; the difference is `2`, which is not divisible
by `4`. This is exactly the kind of non-divisibility argument from Example
3.2.6.

The lesson is that modular arithmetic is stable under addition, subtraction,
negation, multiplication, and powers, but not under division unless extra
conditions are added.

### 3.3.8

Squaring rule for modular arithmetic: if `a ≡ b (mod n)`, then
`a^2 ≡ b^2 (mod n)`.

```litex
prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}

claim:
    prove:
        forall a, b, n Z:
            $mod_eq(a, b, n)
            =>:
                $mod_eq(a^2, b^2, n)
    have by exist x Z st {a - b = n * x}: x
    witness exist k Z st {a^2 - b^2 = n * k} from x * (a + b):
        a^2 - b^2 = (a - b) * (a + b) = n * x * (a + b) = n * (x * (a + b))
```

### 3.3.9

Cubing rule for modular arithmetic: if `a ≡ b (mod n)`, then
`a^3 ≡ b^3 (mod n)`.

```litex
prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}

claim:
    prove:
        forall a, b, n Z:
            $mod_eq(a, b, n)
            =>:
                $mod_eq(a^3, b^3, n)
    have by exist x Z st {a - b = n * x}: x
    witness exist k Z st {a^3 - b^3 = n * k} from x * (a^2 + a * b + b^2):
        a^3 - b^3 = (a - b) * (a^2 + a * b + b^2) = n * x * (a^2 + a * b + b^2) = n * (x * (a^2 + a * b + b^2))
```

The same pattern works for higher powers: factor `a^m - b^m`, then use the
known quotient for `a - b`.

### 3.3.10

Reflexivity rule for modular arithmetic: `a ≡ a (mod n)`.

```litex
prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}

claim:
    prove:
        forall a, n Z:
            =>:
                $mod_eq(a, a, n)
    witness exist k Z st {a - a = n * k} from 0:
        a - a = n * 0
```

### 3.3.11

Let `a` and `b` be integers, and suppose that `a ≡ 2 (mod 4)`. Show that

`a*b^2 + a^2*b + 3*a ≡ 2*b^2 + 2^2*b + 3*2 (mod 4)`.

One way is to work directly from the definition and supply the quotient.

```litex
prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}

know:
    forall a Z:
        =>:
            a^2 $in Z
    forall a, n Z:
        =>:
            $mod_eq(a, a, n)
    forall a, b, c, d, n Z:
        $mod_eq(a, b, n)
        $mod_eq(c, d, n)
        =>:
            $mod_eq(a + c, b + d, n)
            $mod_eq(a * c, b * d, n)
    forall a, b, n Z:
        $mod_eq(a, b, n)
        =>:
            $mod_eq(a^2, b^2, n)

claim:
    prove:
        forall a, b Z:
            $mod_eq(a, 2, 4)
            =>:
                $mod_eq(a * b^2 + a^2 * b + 3 * a, 2 * b^2 + 2^2 * b + 3 * 2, 4)
    have by exist x Z st {a - 2 = 4 * x}: x
    witness exist k Z st {a * b^2 + a^2 * b + 3 * a - (2 * b^2 + 2^2 * b + 3 * 2) = 4 * k} from x * (b^2 + a * b + 2 * b + 3):
        a * b^2 + a^2 * b + 3 * a - (2 * b^2 + 2^2 * b + 3 * 2) = (a - 2) * (b^2 + a * b + 2 * b + 3) = 4 * x * (b^2 + a * b + 2 * b + 3) = 4 * (x * (b^2 + a * b + 2 * b + 3))
```

After the modular arithmetic rules above are known, the proof can also be
written in a shorter, more compositional way. Litex lets the earlier `claim`s
act as reusable mathematical facts.

```litex
prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}

know:
    forall a, n Z:
        =>:
            $mod_eq(a, a, n)
    forall a, b, c, d, n Z:
        $mod_eq(a, b, n)
        $mod_eq(c, d, n)
        =>:
            $mod_eq(a + c, b + d, n)
            $mod_eq(a * c, b * d, n)
    forall a, b, n Z:
        $mod_eq(a, b, n)
        =>:
            $mod_eq(a^2, b^2, n)

claim:
    prove:
        forall a, b Z:
            $mod_eq(a, 2, 4)
            =>:
                $mod_eq(a * b^2 + a^2 * b + 3 * a, 2 * b^2 + 2^2 * b + 3 * 2, 4)
    $mod_eq(b^2, b^2, 4)
    $mod_eq(a * b^2, 2 * b^2, 4)
    $mod_eq(a^2, 2^2, 4)
    $mod_eq(b, b, 4)
    $mod_eq(a^2 * b, 2^2 * b, 4)
    $mod_eq(a * b^2 + a^2 * b, 2 * b^2 + 2^2 * b, 4)
    $mod_eq(3, 3, 4)
    $mod_eq(3 * a, 3 * 2, 4)
    $mod_eq(a * b^2 + a^2 * b + 3 * a, 2 * b^2 + 2^2 * b + 3 * 2, 4)
```

## 3.4 Modular arithmetic: calculations

From now on, modular arithmetic calculation examples are written together. The
basic congruence rules are listed once at the top, then the examples use them
directly.

```litex
prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}

prop mod_eq_trans(a Z, b Z, c Z, n Z):
    $mod_eq(a, c, n)

know:
    forall a, b, c, n Z:
        $mod_eq(a, b, n)
        $mod_eq(b, c, n)
        =>:
            $mod_eq_trans(a, b, c, n)
    forall a, n Z:
        =>:
            $mod_eq(a, a, n)
    forall a, b, c, d, n Z:
        $mod_eq(a, b, n)
        $mod_eq(c, d, n)
        =>:
            $mod_eq(a + c, b + d, n)
            $mod_eq(a * c, b * d, n)
    forall a, b, n Z:
        $mod_eq(a, b, n)
        =>:
            $mod_eq(a^2, b^2, n)
            $mod_eq(a^3, b^3, n)
            $mod_eq(b, a, n)
    forall x Z:
        =>:
            $mod_eq(x, 0, 3) or $mod_eq(x, 1, 3) or $mod_eq(x, 2, 3)

claim:
    prove:
        forall a, b Z:
            $mod_eq(a, 2, 4)
            =>:
                $mod_eq(a * b^2 + a^2 * b + 3 * a, 2 * b^2 + 2^2 * b + 3 * 2, 4)
    $mod_eq(b^2, b^2, 4)
    $mod_eq(a * b^2, 2 * b^2, 4)
    $mod_eq(a^2, 2^2, 4)
    $mod_eq(b, b, 4)
    $mod_eq(a^2 * b, 2^2 * b, 4)
    $mod_eq(a * b^2 + a^2 * b, 2 * b^2 + 2^2 * b, 4)
    $mod_eq(3, 3, 4)
    $mod_eq(3 * a, 3 * 2, 4)
    $mod_eq(a * b^2 + a^2 * b + 3 * a, 2 * b^2 + 2^2 * b + 3 * 2, 4)

claim:
    prove:
        forall a, b Z:
            $mod_eq(a, 4, 5)
            $mod_eq(b, 3, 5)
            =>:
                $mod_eq(a * b + b^3 + 3, 2, 5)
    $mod_eq(a * b, 4 * 3, 5)
    $mod_eq(b^3, 3^3, 5)
    $mod_eq(a * b + b^3, 4 * 3 + 3^3, 5)
    $mod_eq(3, 3, 5)
    $mod_eq(a * b + b^3 + 3, 4 * 3 + 3^3 + 3, 5)
    witness exist k Z st {4 * 3 + 3^3 + 3 - 2 = 5 * k} from 8:
        4 * 3 + 3^3 + 3 - 2 = 5 * 8
    $mod_eq(4 * 3 + 3^3 + 3, 2, 5)
    $mod_eq_trans(a * b + b^3 + 3, 4 * 3 + 3^3 + 3, 2, 5)
    $mod_eq(a * b + b^3 + 3, 2, 5)

claim:
    prove:
        exist a Z st {$mod_eq(6 * a, 4, 11)}
    witness exist a Z st {$mod_eq(6 * a, 4, 11)} from 8:
        witness exist k Z st {6 * 8 - 4 = 11 * k} from 4:
            6 * 8 - 4 = 11 * 4
        $mod_eq(6 * 8, 4, 11)

claim:
    prove:
        forall x Z:
            =>:
                $mod_eq(x^3, x, 3)
    by cases:
        prove:
            $mod_eq(x^3, x, 3)
        case $mod_eq(x, 0, 3):
            $mod_eq(x^3, 0^3, 3)
            witness exist k Z st {0^3 - 0 = 3 * k} from 0:
                0^3 - 0 = 3 * 0
            $mod_eq(0^3, 0, 3)
            $mod_eq_trans(x^3, 0^3, 0, 3)
            $mod_eq(x^3, 0, 3)
            $mod_eq(0, x, 3)
            $mod_eq_trans(x^3, 0, x, 3)
            $mod_eq(x^3, x, 3)
        case $mod_eq(x, 1, 3):
            $mod_eq(x^3, 1^3, 3)
            witness exist k Z st {1^3 - 1 = 3 * k} from 0:
                1^3 - 1 = 3 * 0
            $mod_eq(1^3, 1, 3)
            $mod_eq_trans(x^3, 1^3, 1, 3)
            $mod_eq(x^3, 1, 3)
            $mod_eq(1, x, 3)
            $mod_eq_trans(x^3, 1, x, 3)
            $mod_eq(x^3, x, 3)
        case $mod_eq(x, 2, 3):
            $mod_eq(x^3, 2^3, 3)
            witness exist k Z st {2^3 - 2 = 3 * k} from 2:
                2^3 - 2 = 3 * 2
            $mod_eq(2^3, 2, 3)
            $mod_eq_trans(x^3, 2^3, 2, 3)
            $mod_eq(x^3, 2, 3)
            $mod_eq(2, x, 3)
            $mod_eq_trans(x^3, 2, x, 3)
            $mod_eq(x^3, x, 3)
```

The `know` block above is a compact way to state reusable facts. When a later
line asks for a fact, Litex tries to match it against the conclusion of a
`forall` fact and then checks that the matched assumptions are available.

For example, suppose Litex knows the multiplication rule
`a $in Z, b $in Z, c $in Z, d $in Z, n $in Z, $mod_eq(a, b, n), $mod_eq(c, d, n) => $mod_eq(a * c, b * d, n)`.
If the current goal is `$mod_eq(a * y, 2 * y, 4)`, Litex can match the rule with
`b = 2`, `c = y`, `d = y`, and `n = 4`. Then it only needs the assumptions
: `a $in Z`, `2 $in Z`, `y $in Z`, `4 $in Z`, `$mod_eq(a, 2, 4)`, and `$mod_eq(y, y, 4)`.

```litex
prop mod_eq(a Z, b Z, n Z):
    exist k Z st {a - b = n * k}

know:
    forall a, n Z:
        =>:
            $mod_eq(a, a, n)
    forall a, b, c, d, n Z:
        $mod_eq(a, b, n)
        $mod_eq(c, d, n)
        =>:
            $mod_eq(a * c, b * d, n)

claim:
    prove:
        forall a, y Z:
            $mod_eq(a, 2, 4)
            =>:
                $mod_eq(a * y, 2 * y, 4)
    $mod_eq(y, y, 4)
    $mod_eq(a * y, 2 * y, 4)
```

The facts in the `know` block are not magic. They are all short consequences of
the definition of `$mod_eq`, just like the lemmas proved in 3.3. A good exercise
is to replace each `know` line by a `claim` and prove it directly with witnesses.

### 3.4.1

This is the same problem as 3.3.11. After the rules in 3.3 are known, the
proof is just a sequence of congruence-preserving rewrites.

### 3.4.2

Let a and b be integers, with a ≡ 4 (mod 5) and b ≡ 3 (mod 5). Show that a*b + b^3 + 3 ≡ 2 (mod 5).

The Litex proof follows the same calculation: first replace `a` and `b` by
their residues, then check the final integer arithmetic by a witness.

### 3.4.3

Show that there exists an integer a such that 6a ≡ 4 (mod 11).

### 3.4.4

Let x be an integer. Show that x^3 ≡ x (mod 3).

This mirrors `mod_cases`: use the fact that every integer is congruent to
`0`, `1`, or `2` modulo `3`, then handle the three residues.

## 3.5 Bézout’s identity

The Bézout examples are also grouped together. The divisibility proposition is
defined once, then each claim supplies the corresponding witness.

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
            5 * n = 8 * a
            =>:
                $dvdZ(8, n)
    witness exist c Z st {n = 8 * c} from 5 * a - 3 * n:
        n = 5 * (5 * n) - 24 * n = 5 * (8 * a) - 24 * n = 8 * (5 * a - 3 * n)

claim:
    prove:
        forall n, x Z:
            3 * n = 5 * x
            =>:
                $dvdZ(5, n)
    witness exist c Z st {n = 5 * c} from 2 * x - n:
        n = 2 * (3 * n) - 5 * n = 2 * (5 * x) - 5 * n = 5 * (2 * x - n)

claim:
    prove:
        forall m, a, b Z:
            m = 8 * a
            m = 5 * b
            =>:
                $dvdZ(40, m)
    witness exist c Z st {m = 40 * c} from -3 * a + 2 * b:
        m = -15 * m + 16 * m = -15 * (8 * a) + 16 * (5 * b) = 40 * (-3 * a + 2 * b)
```

### 3.5.1

Let n be an integer and suppose that 5n is a multiple of 8. Show that n is also a multiple of 8.

If `5 * n = 8 * a`, then the Bézout identity `1 = -3 * 5 + 2 * 8`
gives the needed multiple of `8`.

The same problem can be solved with another Bézout combination.

### 3.5.2

Show that if 5 divides 3n, then 5 divides n.

### 3.5.3

Let m be an integer which is divisible by 8 and by 5. Show that it is also divisible by 40.

Here the two divisibility assumptions are written with their witnesses:
`m = 8 * a` and `m = 5 * b`.
