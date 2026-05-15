# Chapter 1 — Proofs By Calculation

Try all snippets in browser: https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Chapter_1_Proofs_By_Calculation

GitHub source: https://github.com/litexlang/The-Mechanics-of-Litex-Proof/blob/main/Chapter_1_Proofs_By_Calculation.md

Litex proofs are meant to look close to the mathematical sentence they justify.
In this first chapter the objects are only the usual number systems, `N`, `Z`,
`Q`, and `R`, and the goals are familiar algebraic equalities and inequalities.
The point is not that these examples are hard; the point is how little extra
proof language is needed around them.

A calculation proof in Litex is written as a chain of expressions. Each link in
the chain is a small claim whose shape already suggests the rule to try:
equalities invite calculation and substitution, inequalities invite order
reasoning, and the assumptions above the arrow provide patterns to match. The statement itself carries the hints that guide the proof search.

## How Facts Are Written

Most lines inside a Litex proof are facts. A fact is a mathematical sentence
that Litex should verify from the current context. There are three common
surface forms.

First, many basic relations are built in. Equalities, inequalities, order
relations, membership, subset, and similar relations can be written directly:

```litex
prove:
    1 + 1 = 2
    3 > 1
    2 <= 2
    2 $in {1, 2, 3}
    {1, 2} $in power_set({1, 2, 3})
```

Second, binary facts can be written in an infix style, with the predicate name
between the two arguments. This is why membership is written as

```litex
2 $in {1, 2, 3}
```

and subset is written as

```text
{1, 2} $subset {1, 2, 3}
```

This keeps common binary mathematical relations close to the way they are read:
"2 is in the set" and "`{1, 2}` is a subset of `{1, 2, 3}`."

Third, predicates with any number of arguments are written in function-call
style, with a dollar sign before the proposition name:

```litex
abstract_prop between(a, b, c)

know $between(1, 2, 3)

prove:
    $between(1, 2, 3)
```

The same form works for unary, binary, ternary, or longer predicates:

```text
$prime(7)
$parallel(line1, line2)
$collinear(A, B, C)
```

The dollar sign is meaningful. It tells Litex that the name is being used to
make a judgment, not to compute an object. For example, `f(1)` is an ordinary
function application: it denotes the value of the function `f` at `1`.
By contrast, `$p(1)` is a proposition call: it asserts that the predicate or
property `p` holds of `1`.

```text
f(1)      # an object: the value of function f at 1
$p(1)     # a fact: proposition p holds of 1
```

## 1.1 Proving equalities

### 1.1.1

Let a and b be rational numbers, and suppose that a - b = 4 and a*b = 1.
Show that (a+b)^2 = 20.

```litex
forall a, b Q:
    a - b = 4
    a * b = 1
    =>:
        (a + b)^2 = (a - b)^2 + 4 * (a * b) = 4^2 + 4 * 1 = 20
```

Read this chain one link at a time.

1. `(a + b)^2 = (a - b)^2 + 4 * (a * b)`: this is a purely algebraic
   rearrangement. After expanding both sides and simplifying, they are the same
   expression.

2. `(a - b)^2 + 4 * (a * b) = 4^2 + 4 * 1`: this is substitution from the
   assumptions `a - b = 4` and `a * b = 1`.

3. `4^2 + 4 * 1 = 20`: this is arithmetic calculation.

Litex does not ask you to label these links with tactics. Their shapes already
separate algebraic simplification, substitution from known equalities, and
numeric calculation.

### 1.1.2

Let r and s be real numbers, and suppose that r + 2s = -1 and s = 3.
Prove that r = -7.

```litex
forall r, s R:
    r + 2 * s = -1
    s = 3
    =>:
        r = (r + 2 * s) - 2 * s = -7
```

The last step is intentionally compressed. You could write
`(r + 2 * s) - 2 * s = -1 - 2 * 3 = -7`, but Litex can already see from the
assumptions that `r + 2 * s` has value `-1` and `s` has value `3`. Once those
subexpressions are resolved to numbers, the remaining step is ordinary
algebraic simplification and arithmetic.

### 1.1.3

Let a, b, m and n be integers, and suppose that b^2 = 2a^2 and a*m + b*n = 1. 
Show that (2a*n + b*m)^2 = 2. This fact is known as Brahmagupta’s identity.

```litex
forall a, b, m, n Z:
    b^2 = 2 * a^2
    a * m + b * n = 1
    =>:
        (2 * a * n + b * m)^2 = 2 * (a * m + b * n)^2 + (m^2 - 2 * n^2) * (b^2 - 2 * a^2) = 2 * 1^2 + (m^2 - 2 * n^2) * (2 * a^2 - 2 * a^2) = 2
```

### 1.1.4

Let a, b, c, d, e and f be integers, and suppose that a*d = b*c and c*f = d*e.
Show that d*(a*f - b*e) = 0.

```litex
forall a, b, c, d, e, f Z:
    a * d = b * c
    c * f = d * e
    =>:
        d * (a * f - b * e) = (a * d) * f - d * b * e = (b * c) * f - d * b * e = b * (c * f) - d * b * e = b * (d * e) - d * b * e = 0
```

## 1.2 Rosetta stone: Litex and Lean

In this section, we show the similarities and differences between Litex and Lean.

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>forall a, b Q:
    a - b = 4
    a * b = 1
    =&gt;:
        (a + b)^2 = (a - b)^2 + 4 * (a * b) = 4^2 + 4 * 1 = 20</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
    _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
    _ = 20 := by norm_num</code></pre>
    </td>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>forall r, s R:
    r + 2 * s = -1
    s = 3
    =&gt;:
        r = (r + 2 * s) - 2 * s = -7</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
  calc
    r = r + 2 * s - 2 * s := by ring
    _ = -1 - 2 * s := by rw [h2]
    _ = -1 - 2 * 3 := by rw [h1]
    _ = -7 := by norm_num</code></pre>
    </td>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>forall a, b, m, n Z:
    b^2 = 2 * a^2
    a * m + b * n = 1
    =&gt;:
        (2 * a * n + b * m)^2 = 2 * (a * m + b * n)^2 + (m^2 - 2 * n^2) * (b^2 - 2 * a^2) = 2 * 1^2 + (m^2 - 2 * n^2) * (2 * a^2 - 2 * a^2) = 2</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>example {a b m n : ℤ} (h1 : a * m + b * n = 1) (h2 : b ^ 2 = 2 * a ^ 2) :
    (2 * a * n + b * m) ^ 2 = 2 :=
  calc
    (2 * a * n + b * m) ^ 2
      = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2 * a ^ 2) := by ring
    _ = 2 * 1 ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by rw [h1, h2]
    _ = 2 := by ring</code></pre>
    </td>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>forall a, b, c, d, e, f Z:
    a * d = b * c
    c * f = d * e
    =&gt;:
        d * (a * f - b * e) = (a * d) * f - d * b * e = (b * c) * f - d * b * e = b * (c * f) - d * b * e = b * (d * e) - d * b * e = 0</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) :
    d * (a * f - b * e) = 0 :=
  calc
    d * (a * f - b * e) = (a * d) * f - d * b * e := by ring
    _ = (b * c) * f - d * b * e := by rw [h1]
    _ = b * (c * f) - d * b * e := by ring
    _ = b * (d * e) - d * b * e := by rw [h2]
    _ = 0 := by ring</code></pre>
    </td>
  </tr>
</table>

From the examples above, you can see that Litex and Lean express proofs very differently because they are based on different design principles. Key points to notice include:

1. In Litex, you do not have to announce the final theorem at the very beginning of the proof. You can write the assumptions and then follow the calculation forward.

2. Basic mathematics contains hundreds of concepts, and the relationships between them quickly become thousands of reusable facts. Litex has many built-in rules and tries them by matching the pattern of the expression, so the user does not have to remember a long list of tactic names.

3. Built-in rules are only the starting point. Users can also prove their own facts and define their own propositions; later chapters will introduce this.

Litex also prints how each line was verified. This makes a proof easier to
debug and easier to trust: you can see whether a line was proved by citing a
known fact, by calculation, or by some other built-in rule. This output does
not depend on an IDE-specific infoview: on the online version of this chapter,
you can click **Run** next to each example and inspect the output directly:
<https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Chapter_1_Proofs_By_Calculation>.
If you install Litex locally, the command-line runner prints the same kind of
verification output when you run a file or a snippet.
For example, run this Litex code:

```litex
forall x R:
    x = 1
    =>:
        x = 1
        x + x = 2
```

You may see a message like this:

```text
{
  "result": "success",
  "type": "Fact",
  "line": 1,
  "stmt": "forall x R:\n    ~1x = 1\n    =>:\n        ~1x = 1\n        ~1x + ~1x = 2",
  "verified_by": [
    {
      "type": "citation",
      "cite_source": {
        "line": 2,
        "source": "entry"
      },
      "cited_stmt": "~1x = 1",
      "verify_what": "~1x = 1"
    },
    {
      "type": "builtin rule",
      "rule": "calculation",
      "verify_what": "~1x + ~1x = 2"
    }
  ],
  "infer_facts": [],
  "inside_results": []
}
```


## 1.3 Tips and tricks (examples)

### 1.3.1

Let a and b be integers and suppose that a = 2b + 5 and b = 3. Show that a = 11.

```litex
forall a, b Z:
    a = 2 * b + 5
    b = 3
    =>:
        a = 2 * b + 5 = 11
```

### 1.3.2

Let x be an integer and suppose that x + 4 = 2. Show that x = -2.

```litex
forall x Z:
    x + 4 = 2
    =>:
        x = -2
```

You do not have to write the longer chain `x = 2 - 4 = -2`. When Litex sees a
previous equality with a simple shape such as `x + NUMBER = NUMBER`, it keeps
the solved value of `x` and can use it later. The same idea works for similar
linear simplifications using `+`, `-`, `*`, and `/`; writing the equation as
`4 + x = 2` is also fine.

### 1.3.3

Let a and b be real numbers and suppose that a - 5b = 4 and b + 2 = 3. Show that a = 9.

```litex
forall a, b R:
    a - 5 * b = 4
    b + 2 = 3
    =>:
        a = (a - 5 * b) + 5 * b = 4 + 5 * b = -6 + 5 * (b + 2) = 9
```

### 1.3.4

Let w be a rational number and suppose that 3w + 1 = 4. Show that w = 1.

```litex
forall w Q:
    3 * w + 1 = 4
    =>:
        w = (3 * w + 1) / 3 - 1 / 3 = 4 / 3 - 1 / 3 = 1
```

Division is handled a little differently from `+`, `-`, and `*`. For expressions
made only from addition, subtraction, and multiplication, Litex can often verify
a step by algebraic simplification, essentially polynomial simplification. For
an identity such as `a / b + c / d = ...`, Litex instead clears denominators:
it multiplies both sides by the denominators that appear on the two sides, and
then checks whether the resulting denominator-free expressions are equal.

### 1.3.5

Let x be an integer and suppose that 2x + 3 = x. Show that x = -3.

```litex
forall x Z:
    2 * x + 3 = x
    =>:
        x = (2 * x + 3) - x - 3 = x - x - 3 = -3
```

### 1.3.6

Let x and y be integers and suppose that 2x - y = 4 and y - x + 1 = 2. Prove that x = 5.

```litex
forall x, y Z:
    2 * x - y = 4
    y - x + 1 = 2
    =>:
        x = (2 * x - y) + (y - x + 1) - 1 = 4 + 2 - 1 = 5
```

### 1.3.7

Let u and v be rational numbers, and suppose that u + 2v = 4 and u - 2v = 6. Show that u = 5.

```litex
forall u, v Q:
    u + 2 * v = 4
    u - 2 * v = 6
    =>:
        u = ((u + 2 * v) + (u - 2 * v)) / 2 = (4 + 6) / 2 = 5
```

### 1.3.8

Let x and y be real numbers, and suppose that x + y = 4 and 5x - 3y = 4. Show that x = 2.

```litex
forall x, y R:
    x + y = 4
    5 * x - 3 * y = 4
    =>:
        x = (3 * (x + y) + (5 * x - 3 * y)) / 8 = (3 * 4 + 4) / 8 = 2
```

### 1.3.9

Let a and b be rational numbers and suppose that a - 3 = 2b.
Show that a^2 - a + 3 = 4b^2 + 10b + 9.

```litex
forall a, b Q:
    a - 3 = 2 * b
    =>:
        a^2 - a + 3 = (a - 3)^2 + 5 * (a - 3) + 9 = (2 * b)^2 + 5 * (2 * b) + 9 = 4 * b^2 + 10 * b + 9
```

### 1.3.10

Let z be a real number and suppose that z^2 - 2 = 0.
Show that z^4 - z^3 - z^2 + 2z + 1 = 3.

```litex
forall z R:
    z^2 - 2 = 0
    =>:
        z^4 - z^3 - z^2 + 2 * z + 1 = (z^2 - z + 1) * (z^2 - 2) + 3 = (z^2 - z + 1) * 0 + 3 = 3
```

## 1.4 Proving inequalities (examples)

### 1.4.1

Let x and y be integers, and suppose that x + 3 <= 2 and y + 2x >= 3. Show that y > 3.

```litex
forall x, y Z:
    x + 3 <= 2
    y + 2 * x >= 3
    =>:
        y = (y + 2 * x) - 2 * x >= 3 - 2 * x = 9 - 2 * (x + 3) >= 9 - 2 * 2 > 3
```

Two common built-in rule families appear in this proof.

1. `calculation and rational expression simplification`: this verifies algebraic
   rearrangements such as `y = (y + 2 * x) - 2 * x` and
   `3 - 2 * x = 9 - 2 * (x + 3)`.

2. Order-preserving transformations: Litex can transform known inequalities
   through addition, subtraction, and multiplication by a nonnegative number.
   In the printed proof you may see rules such as
   `a - d <= b - c from a <= b and c <= d` and
   `k * a <= k * b from 0 <= k and a <= b`.

Read the chain one link at a time.

1. `y = (y + 2 * x) - 2 * x`: this is algebraic simplification. The added
   `2 * x` and the subtracted `2 * x` cancel.

2. `(y + 2 * x) - 2 * x >= 3 - 2 * x`: this uses the assumption
   `y + 2 * x >= 3`. Subtracting the same expression `2 * x` from both sides
   preserves the inequality.

3. `3 - 2 * x = 9 - 2 * (x + 3)`: this is another algebraic rearrangement.
   Expanding the right-hand side gives `9 - 2 * x - 6`, which simplifies to
   `3 - 2 * x`.

4. `9 - 2 * (x + 3) >= 9 - 2 * 2`: this uses the assumption `x + 3 <= 2`.
   Since `2` is nonnegative, Litex can multiply both sides by `2`, and then
   subtract from `9`; subtracting a larger value gives a smaller result, so the
   direction is `>=`.

5. `9 - 2 * 2 > 3`: this is ordinary number comparison.

### 1.4.2

Let r and s be rational numbers, and suppose that s + 3 >= r and s + r <= 3. Show that r <= 3.

```litex
forall r, s Q:
    s + 3 >= r
    s + r <= 3
    =>:
        r = (s + r + r - s) / 2 <= (3 + (s + 3) - s) / 2 = 3
```

This example adds two useful order rules to the previous pattern.

1. `a / c <= b / c from 0 < c and a <= b`: dividing both sides of an
   inequality by the same positive number preserves the direction. Here the
   denominator is `2`, and Litex verifies `0 < 2` by number comparison.

2. `a + c <= b + d from a <= b and c <= d`: inequalities can be added
   componentwise. In this proof, Litex combines the assumptions
   `s + r <= 3` and `r <= s + 3` to get
   `s + r + r <= 3 + (s + 3)`.

Read the chain one link at a time.

1. `r = (s + r + r - s) / 2`: this is algebraic simplification. The numerator
   simplifies to `2 * r`, so dividing by `2` gives `r`.

2. `(s + r + r - s) / 2 <= (3 + (s + 3) - s) / 2`: this is the main order
   step. Litex first shows the numerator inequality by combining
   `s + r <= 3`, `r <= s + 3`, and `s <= s`; then it divides both sides by the
   positive number `2`.

3. `(3 + (s + 3) - s) / 2 = 3`: this is calculation and rational expression
   simplification. The numerator simplifies to `6`, and `6 / 2 = 3`.

### 1.4.3

Let x and y be real numbers and suppose that y <= x + 5 and x <= -2. Show that x + y < 2.

```litex
forall x, y R:
    y <= x + 5
    x <= -2
    =>:
        x + y <= x + (x + 5) = 2 * x + 5 <= 2 * (-2) + 5 < 2
```
### 1.4.4

Let u, v, x, y, A and B be real numbers. Suppose 0 < A <= 1, B >= 1, x <= B, y <= B,
0 <= u < A and 0 <= v < A. Show that u*y + v*x + u*v < 3*A*B.

```litex
forall u, v, x, y, A, B R:
    0 < A
    A <= 1
    1 <= B
    x <= B
    y <= B
    0 <= u
    0 <= v
    u < A
    v < A
    =>:
        u * y + v * x + u * v <= u * B + v * B + u * v <= A * B + A * B + A * v <= A * B + A * B + 1 * v <= A * B + A * B + B * v < A * B + A * B + B * A = 3 * A * B
```

New rules worth noticing here:

1. `x1 * x2 <= y1 * y2 from 0 <= factors and componentwise <=`: Litex can
   compare products when the factors are nonnegative and each factor on the
   left is bounded by the corresponding factor on the right.

2. `a + c < b + d from a <= b and c < d`: one strict inequality is enough to
   make the sum strict, as long as the other part is non-strict in the same
   direction.

3. `k * a < k * b from 0 < k and a < b`: multiplying by the same positive
   number preserves a strict inequality.

### 1.4.5

Show that if t is a real number and t >= 10 then t^2 - 3t + 17 >= 5.

```litex
forall t R:
    t >= 10
    =>:
        t^2 - 3 * t + 17 = t * t - 3 * t + 17 >= 10 * t - 3 * t + 17 = 7 * t + 17 >= 7 * 10 + 17 >= 5
```

New rules worth noticing here:

1. `equality: same algebraic context with equal arguments`: Litex can recognize
   that replacing equal subexpressions inside the same surrounding expression
   preserves equality.

2. `a <= b + c from a <= b and 0 <= c`: if `a <= b` and `c` is nonnegative,
   then `a <= b + c`. This is how Litex can finish a bound by adding a known
   nonnegative margin.

### 1.4.6

Let n >= 5 be an integer. Show that n^2 > 2n + 11.

```litex
forall n Z:
    n >= 5
    =>:
        n^2 = n * n >= 5 * n = 2 * n + 3 * n >= 2 * n + 3 * 5 = 2 * n + 11 + 4 > 2 * n + 11
```

New rule worth noticing here:

1. `a < a + b from 0 < b`: adding a strictly positive term makes an expression
   strictly larger.

### 1.4.7

Let m and n be integers, and suppose that m^2 + n <= 2. Show that n <= 2.

```litex
forall m, n Z:
    m^2 + n <= 2
    =>:
        n <= m^2 + n <= 2
```

New rules worth noticing here:

1. `0 <= a^n for even integer n`: even powers are nonnegative.

2. `a <= a + b from 0 <= b`: adding a nonnegative term makes an expression no
   smaller.

### 1.4.8

Let x and y be real numbers, and suppose that x^2 + y^2 <= 1. Show that (x + y)^2 < 3.

```litex
forall x, y R:
    x^2 + y^2 <= 1
    =>:
        (x + y)^2 <= (x + y)^2 + (x - y)^2 = 2 * (x^2 + y^2) <= 2 * 1 < 3
```

### 1.4.9

Let a and b be nonnegative rational numbers, and suppose that a + b <= 8.
Show that 3*a*b + a <= 7*b + 72.

```litex
forall a, b Q:
    a >= 0
    b >= 0
    a + b <= 8
    =>:
        3 * a * b + a <= 2 * b^2 + a^2 + (3 * a * b + a) = 2 * ((a + b) * b) + (a + b) * a + a <= 2 * (8 * b) + 8 * a + a = 7 * b + 9 * (a + b) <= 7 * b + 9 * 8 = 7 * b + 72
```

New rule worth noticing here:

1. `0 <= a * b from 0 <= a and 0 <= b`: the product of two nonnegative
   quantities is nonnegative. Litex uses this together with nonnegative powers
   to justify adding terms such as `2 * b^2 + a^2`.

### 1.4.10

Let a, b and c be real numbers. Show that a^2 * (a^6 + 8*b^3*c^3) <= (a^4 + b^4 + c^4)^2.

```litex
forall a, b, c R:
    =>:
        a^2 * (a^6 + 8 * b^3 * c^3) <= 2 * (a^2 * (b^2 - c^2))^2 + (b^4 - c^4)^2 + 4 * (a^2 * b * c - b^2 * c^2)^2 + a^2 * (a^6 + 8 * b^3 * c^3) = (a^4 + b^4 + c^4)^2
```

## 1.5 Chapter summary: common shortcuts and built-in rules

The examples in this chapter are short, but they already show the main style of
Litex calculation proofs: write the mathematical chain, and let the checker try
the rules suggested by each link. The most common built-in rules used here are
the following.

### Equality rules

1. **Citation.** If the same equality is already among the assumptions or known
   facts, Litex can cite it directly.

2. **Calculation and normalization.** If two sides reduce to the same number or
   the same normalized algebraic expression, Litex proves the equality by
   calculation.

3. **Substitution from known equalities.** If a subexpression has a known value,
   Litex may replace it before calculating the rest. For example, from
   `r + 2 * s = -1` and `s = 3`, the step
   `(r + 2 * s) - 2 * s = -7` can be checked without explicitly writing
   `= -1 - 2 * 3`.

4. **Simple equation solving.** Equalities such as `x + 4 = 2`, `4 + x = 2`,
   and similar one-variable forms using `+`, `-`, `*`, and `/` can give Litex a
   stored value for the variable.

5. **Equality chains.** A chain such as `A = B = C` is checked one link at a
   time, and the whole chain proves the equality from the first expression to
   the last.

For example:

```litex
forall x Z:
    x + 4 = 2
    =>:
        x = -2
```

### Comparison rules

1. **Reflexivity and numeric comparison.** Litex can use facts such as `x <= x`,
   `0 <= 2`, `0 < 2`, and direct number comparisons.

2. **Addition and subtraction preserve order.** From `a <= b` and `c <= d`,
   Litex can derive `a + c <= b + d`; it can also reason with subtractions such
   as `a - d <= b - c`.

3. **Nonnegative and positive multiplication preserve order.** Multiplying both
   sides by a nonnegative factor preserves `<=`; multiplying by a positive
   factor preserves `<`.

4. **Positive division preserves order.** From `0 < c` and `a <= b`, Litex can
   derive `a / c <= b / c`.

5. **Products of nonnegative terms are nonnegative.** Litex can also compare
   products when the factors are bounded componentwise and nonnegative.

6. **Even powers are nonnegative.** Terms like `m^2` or `(x - y)^2` can be used
   as nonnegative quantities, for example when adding a square to make an
   expression larger.

7. **Adding a nonnegative or positive term.** Adding a nonnegative term gives
   `a <= a + b`; adding a strictly positive term gives `a < a + b`.

> There is no separate tactic script saying `by rw`, `by ring`, or `by rel [hx]`, which languages like Lean use to tell the proof engine what one-step rule to try.

> In principle, Lean can package many tactics inside one tactic, and a mature
> library can make special classes of goals feel almost automatic. That is a real
> strength, and Litex should learn from the breadth of Lean's libraries. The
> design difference is that Litex tries to rely less on a large tactic library at
> the basic level. It gives a small proof language first, and then lets users
> package recurring mathematical ideas as `prop`s. So the same kind of
> convenience is still possible in principle, but it is built from named
> mathematical statements rather than from remembering many tactic names.

## 1.6 Litex statements and ideas in this chapter

This chapter uses only a small part of the Litex proof language.

### Litex statements and syntax used

1. `forall ...:` introduces arbitrary parameters, together with their parameter
   constraints such as `x R` or `a, b Q`, which means `x $in R`(x in real number set) and `a $in Q and b $in Q`(a and b in rational number set).

2. Assumption lines before `=>:` are the facts available in the proof body.

3. `=>:` starts the conclusion part of a `forall` statement. The indented facts
   after it are proved in order.

4. A bare fact line, such as `x = -2` or `a <= b`, asks Litex to verify that
   fact from the current context.

5. Equality and comparison chains, such as `A = B = C` or `A <= B = C < D`,
   are compact forms for several adjacent facts checked link by link.

### Litex knowledge points

1. A proof context grows line by line. Once Litex verifies a fact, later lines
   can use it.

2. Calculation proofs usually do not need tactic names. Litex chooses built-in
   rules from the shape of the fact: algebraic normalization for equalities,
   order reasoning for inequalities, and numeric calculation for concrete
   numbers.

3. Known equalities can be used as substitutions inside larger expressions.

4. Simple equations can store solved values, so later facts may use `x = -2`
   even if the earlier assumption was written as `x + 4 = 2`.

5. The standard number sets `N`, `Z`, `Q`, and `R` are enough for the first
   examples, and their parameter constraints give Litex the arithmetic domain
   information needed to check the proof.

