# Chapter 1 — Proofs by calculation

Litex proofs are meant to look close to the mathematical sentence they justify.
In this first chapter the objects are only the usual number systems, `N`, `Z`,
`Q`, and `R`, and the goals are familiar algebraic equalities and inequalities.
The point is not that these examples are hard; the point is how little extra
proof language is needed around them.

A calculation proof in Litex is written as a chain of expressions. Each link in
the chain is a small claim whose shape already suggests the rule to try:
equalities invite calculation and substitution, inequalities invite order
reasoning, and the assumptions above the arrow provide patterns to match. The statement itself carries the hints that guide the proof search.

> There is no separate tactic script saying `by rw`, `by ring`, or `by rel [hx]`, which languages like Lean use to tell the proof engine what one-step rule to try.

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

## 1.2 Proving equalities in Lean（本节仅作说明，无 Litex 正文）

## 1.3 Tips and tricks (examples)

### 1.3.1

Let a and b be integers and suppose that a = 2b + 5 and b = 3. Show that a = 11.

```litex
forall a, b Z:
    a = 2 * b + 5
    b = 3
    =>:
        a = 2 * b + 5 = 2 * 3 + 5 = 11
```

### 1.3.2

Let x be an integer and suppose that x + 4 = 2. Show that x = -2.

```litex
forall x Z:
    x + 4 = 2
    =>:
        x = (x + 4) - 4 = 2 - 4 = -2
```

### 1.3.3

Let a and b be real numbers and suppose that a - 5b = 4 and b + 2 = 3. Show that a = 9.

```litex
forall a, b R:
    a - 5 * b = 4
    b + 2 = 3
    =>:
        a = (a - 5 * b) + 5 * b = 4 + 5 * b = -6 + 5 * (b + 2) = -6 + 5 * 3 = 9
```

### 1.3.4

Let w be a rational number and suppose that 3w + 1 = 4. Show that w = 1.

```litex
forall w Q:
    3 * w + 1 = 4
    =>:
        w = (3 * w + 1) / 3 - 1 / 3 = 4 / 3 - 1 / 3 = 1
```

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
        y = y + 2 * x - 2 * x >= 3 - 2 * x = 9 - 2 * (x + 3) >= 9 - 2 * 2 > 3
```
### 1.4.2

Let r and s be rational numbers, and suppose that s + 3 >= r and s + r <= 3. Show that r <= 3.

```litex
forall r, s Q:
    s + 3 >= r
    s + r <= 3
    =>:
        r = (s + r + r - s) / 2 <= (3 + (s + 3) - s) / 2 = 3
```
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

### 1.4.5

Show that if t is a real number and t >= 10 then t^2 - 3t + 17 >= 5.
(书本笔算证明；多项式为 t^2 - 3t + 17。)

```litex
forall t R:
    t >= 10
    =>:
        t^2 - 3 * t + 17 = t * t - 3 * t + 17 >= 10 * t - 3 * t + 17 = 7 * t + 17 >= 7 * 10 + 17 >= 5
```

### 1.4.6

Let n >= 5 be an integer. Show that n^2 > 2n + 11.

```litex
forall n Z:
    n >= 5
    =>:
        n^2 = n * n >= 5 * n = 2 * n + 3 * n >= 2 * n + 3 * 5 = 2 * n + 11 + 4 > 2 * n + 11
```

### 1.4.7

Let m and n be integers, and suppose that m^2 + n <= 2. Show that n <= 2.

```litex
forall m, n Z:
    m^2 + n <= 2
    =>:
        n <= m^2 + n <= 2
```

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

### 1.4.10

Let a, b and c be real numbers. Show that a^2 * (a^6 + 8*b^3*c^3) <= (a^4 + b^4 + c^4)^2.

```litex
forall a, b, c R:
    =>:
        a^2 * (a^6 + 8 * b^3 * c^3) <= 2 * (a^2 * (b^2 - c^2))^2 + (b^4 - c^4)^2 + 4 * (a^2 * b * c - b^2 * c^2)^2 + a^2 * (a^6 + 8 * b^3 * c^3) = (a^4 + b^4 + c^4)^2
```

## 1.5 A shortcut (书本说明：仅加减项的变形可用 addarith；此处仅作陈述示例)

1.5 — 与例 1.3.2 相同结论，可用一步“加减整理”看待（正式 Litex 中若实现 addarith 则单独写）

Let x be an integer and suppose that x + 4 = 2. Show that x = -2.

```litex
forall x Z:
    x + 4 = 2
    =>:
        x = -2
```
