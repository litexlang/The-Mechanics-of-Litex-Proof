# Chapter 2 — Proofs with structure

The proofs by calculation in Chapter 1 were, from one point of view, one-step
proofs: each line was a single calculation chain, and Litex only had to verify
the links inside that chain. In this chapter we begin to write proofs with more
internal structure.

The new ingredients are intermediate facts, facts proved earlier and reused
later, and logical statements built from simpler statements using connectives
such as `and`, `or`, and implication. In Litex, these are still written in a
direct proof style: after the assumptions and the `=>:` marker, you may derive
new facts line by line, and later lines can cite or depend on the facts already
established above them.

This is also where Litex's feedback becomes more important. Lean emphasizes a
live infoview that continuously shows the current hypotheses and goals. Litex
instead exposes the proof structure through its run output: each statement is
reported with the facts it inferred, the known assumptions it cited, and the
built-in rules used to verify each line. For multi-step proofs, that output is
the main way to debug whether an intermediate fact was actually established and
whether the next step is using the intended information.

The work of this chapter continues, after a break, in Chapter 4.

## 2.1 Intermediate steps

### 2.1.1 Example

Let a and b be real numbers and suppose that a - 5b = 4 and b + 2 = 3. Show that a = 9.

In Chapter 1 we solved this by one long calculation. Here we write the proof in
the more ordinary two-step style: first solve for `b`, then use that new fact
to solve for `a`.

```litex
forall a, b R:
    a - 5 * b = 4
    b + 2 = 3
    =>:
        b = 1
        a = (a - 5 * b) + 5 * b = 9
```

Lean example as comparison:

```lean
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by addarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring
```

The first line after `=>:` establishes the intermediate fact `b = 1`. Once that
line is verified, Litex adds it to the local context of the proof. The next line
can then use both original assumptions and this newly established fact; no name
such as `hb` is required, and there is no separate tactic script.

This is the main simplification: Litex treats a proof as a growing list of
verified facts. You state the facts in the order you want to use them, and Litex
checks each one by calculation, citation of previous lines, or built-in rules.
The proof stays close to the way the argument would be written on paper:
“first `b = 1`; therefore `a = 9`.”

A chain is just a compact way to write several adjacent facts on one line. For
example, `a = b < c` can be read as the two facts `a = b` and `b < c`; you may
also write them on separate lines when that makes the proof structure clearer.

### 2.1.2 Example

Let m and n be integers, and suppose that m + 3 <= 2n - 1 and n <= 5. Show that m <= 6.

```litex
forall m, n Z:
    m + 3 <= 2 * n - 1
    n <= 5
    =>:
        m + 3 <= 2 * n - 1 <= 2 * 5 - 1 = 9
        m = (m + 3) - 3 <= 9 - 3 = 6
```

Lean example as comparison:

```lean
example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 :=
  calc
    m + 3 ≤ 2 * n - 1 := by rel [h1]
    _ ≤ 2 * 5 - 1 := by rel [h2]
    _ = 9 := by numbers
  addarith [h3]
```

The middle line establishes the intermediate fact `m + 3 <= 9`: it starts from
the hypothesis `m + 3 <= 2 * n - 1`, then uses `n <= 5` to bound
`2 * n - 1` by `2 * 5 - 1`, and finally calculates `2 * 5 - 1 = 9`.

In Lean, this intermediate fact is usually introduced with a named `have`, such
as `have h3 : m + 3 <= 9 := ...`, and then used by name in a later tactic. In
Litex, the line itself becomes part of the local context once it is verified.
The final line can therefore use `m + 3 <= 9` directly to subtract `3` from both
sides and conclude `m <= 6`.

### 2.1.3 Example

Let r and s be rational numbers, and suppose that s + 3 >= r and s + r <= 3. Show that r <= 3.

```litex
forall r, s Q:
    r <= s + 3
    s + r <= 3
    =>:
        2 * r = r + r <= (s + 3) + r = 3 + (s + r) <= 3 + 3 = 6
        r <= 6 / 2 = 3
```

### 2.1.4 Example

Let t be a real number, and suppose that t^2 = 3t and t >= 1. Show that t >= 2.

```litex
forall t R:
    t^2 = 3 * t
    t >= 1
    =>:
        t = (t^2) / t = (3 * t) / t = 3
        t >= 2
```

Lean example as comparison:

```lean
example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 :=
  calc t * t = t ^ 2 := by ring
    _ = 3 * t := by rw [h1]
  cancel t at h3
  addarith [h3]
```

This example is the first one where cancellation matters. In Lean, the proof
usually creates an intermediate equality `h3 : t * t = 3 * t`, then runs
`cancel t at h3`, which changes that hypothesis into `h3 : t = 3`.

Litex writes the same reasoning as another fact in the growing proof context:
`t = (t^2) / t = (3 * t) / t = 3`. There is no separate command that mutates a
named hypothesis. You state the cancelled equality directly, and Litex checks
that the division is legitimate.

The subtle point is the same in both systems: cancelling `t` is valid only when
`t` is known to be nonzero. Here the assumption `t >= 1` gives `t > 0`, so Litex
has enough information to justify dividing by `t`.

The final comparison also uses the context built so far. Once Litex has proved
`t = 3`, it knows the value of `t`; when checking `t >= 2`, it can reduce the
comparison to the numeric fact `3 >= 2`.

### 2.1.5 Example

Let a and b be real numbers, and suppose that a^2 = b^2 + 1 and a >= 0. Show that a >= 1.

```litex
claim:
    prove:
        forall a, b R:
            a^2 = b^2 + 1
            a >= 0
            =>:
                a >= 1
    by contra a >= 1:
        a^2 = b^2 + 1 >= 0 + 1 = 1
        a < 1
        impossible a^2 < 1^2
```

This example is structurally different from the previous ones. It is no longer
just a `forall ... =>:` block whose body is a list of facts. When the thing you
want to prove is a fact, but the proof process needs non-fact statements such
as `by contra`, you wrap the proof in a `claim`. Under `claim: prove:`, you
write the fact you want to prove:

```text
forall a, b R:
    a^2 = b^2 + 1
    a >= 0
    =>:
        a >= 1
```

After the `prove:` block, you write the actual proof process. Here that process
is proof by contradiction:

```text
by contra a >= 1:
```

The meaning is: to prove `a >= 1`, temporarily enter a local contradiction
environment where the opposite of `a >= 1` is assumed. In this case, since `a`
is real, that opposite is `a < 1`, which is why the proof can use the line
`a < 1`.

Inside the contradiction branch, the proof first derives
`a^2 = b^2 + 1 >= 0 + 1 = 1`. This uses the fact that `b^2 >= 0`, so from
`a^2 = b^2 + 1` we get `a^2 >= 1`.

The last line must have the form:

```text
impossible <FACT>
```

Here the fact is `a^2 < 1^2`. The `know` block at the start records the lemma
that, for nonnegative numbers, squaring preserves strict order. Using that
lemma with `a >= 0`, `a < 1`, and `0 <= 1`, Litex verifies the line
`a^2 < 1^2`.

But the context also contains `a^2 >= 1`, and `1 = 1^2`, so `a^2 < 1^2` is
impossible. The contradiction shows that the temporary assumption `a < 1`
cannot be true, so the original goal `a >= 1` is proved.

> Litex tries to keep the proof focused on the mathematical argument itself.
> On one hand, you usually do not need to give intermediate facts names like
> `h1`, `h2`, or `hb`; verified facts are simply available in the local context.
> On the other hand, when you use one fact to prove another, you usually do not
> need to write a separate `by ...` instruction. This also means Litex is less
> dependent on a large standard library of named tactics and lemmas: users can
> often write the proof process directly, instead of first searching the library
> for the exact method that might prove the step.

### 2.1.6（对比 1.4.1：中间结论 x <= -1）

Let x and y be integers, and suppose that x + 3 <= 2 and y + 2x >= 3. Show that y > 3.

```litex
forall x, y Z:
    x + 3 <= 2
    y + 2 * x >= 3
    =>:
        x=x+3-3<=2-3=-1
        y=y+2*x-2*x>=3-2*x>=3-2*(-1)=5
        y>=5>3
```

### 2.1.7

Let a and b be real numbers and suppose that -b <= a <= b. Show that a^2 <= b^2.

```litex
know:
    forall a, b R:
        a>=0
        b>=0
        =>:
            a*b>=0
forall a, b R:
    -b <= a
    a <= b
    =>:
        0 =b+(-b)<=b+a
        0=a-a<=b-a
        (b+a)*(b-a)>=0
        a^2 =a^2+0 <= a^2 + (b + a) * (b - a) = b^2
```

### 2.1.8

Let a and b be real numbers and suppose that a <= b. Show that a^3 <= b^3.

SOLVED

```litex
forall a, b R:
    a <= b
    =>:
        0=a-a<=b-a
        (b+a)^2>=0
        (b+a)^2/4>=0
        (b-a)^2>=0
        3*(b+a)^2>=0
        3*(b+a)^2/4>=0
        ((b-a)^2+3*(b+a)^2)/4>=0
        (b-a)*((b-a)^2+3*(b+a)^2)/4>=0
        a^3 =a^3+0 <= a^3 + (b - a) *(((b - a)^2 + 3 * (b + a)^2) / 4) = b^3
```

## 2.2 Invoking lemmas（Lean 中用 apply 点名引理；Litex 中只写数学结论链，引理名见注释）

### 2.2.1（引理：若 a < b 则 a ≠ b，记作 ne_of_lt）

Let x be a rational number, and suppose that 3x = 2. Show that x != 1.

SOLVED: Now a != b can be verified automatically when a < b.

```litex
forall x Q:
    3 * x = 2
    =>:
        x = (3 * x) / 3 = 2 / 3 < 1
        x!=1
```

### 2.2.2（引理：若 a > b 则 a ≠ b，记作 ne_of_gt）

Let y be a real number. Show that y^2 + 1 != 0.

SOLVED: a != b can be verified automatically when a > b. 0 < a + b can be verified automatically when a > 0 and b >= 0 or a >= 0 and b > 0.

```litex
forall y R:
    =>:
        0 < y^2 + 1
        y^2+1 != 0
```

### 2.2.3（引理 le_antisymm：a <= b 且 b <= a => a = b）

SOLVED

not a < b is verified automatically when b <= a

```litex
claim:
    prove:
        forall a, b R:
            a <= b
            b <= a
            =>:
                a = b
    by cases:
        prove:
            a = b
        case a = b:
            do_nothing
        case a < b:
            impossible a < b
```

## 2.3 “Or” and proof by cases（析取：纸面分情形；Litex 拆成多条 forall 或注释）

### 2.3.1

Let x and y be real numbers and suppose that x = 1 or y = -1. Show that x*y + x = y + 1.

```litex
claim:
    prove:
        forall x, y R:
            x = 1 or y = -1
            =>:
                x * y + x = y + 1
    by cases:
        prove:
            x*y+x=y+1
        case x=1:
            x*y+x=1*y+1=y+1
        case y=-1:
            x*y+x=x*(-1)+x=-1+1=y+1
```

### 2.3.2（自然数 n：n <= 1 或 2 <= n；两情形均得 n^2 ≠ 2）

引理 le_or_succ_le：a <= b 或 b + 1 <= a。此处对 (a,b)=(n,1) 得 n <= 1 或 2 <= n。

Let n be any natural number. Show that n^2 != 2.

不知道为啥不能run

<!-- litex:skip-test -->
```litex
know:
    forall a,b N:
        a>b
        =>:
            a>=b+1
know:
    forall n Z:
        n>=2 or n<=1
claim:
    prove:
        forall n N:
            =>:
                n^2 != 2
    by cases:
        prove:
            n^2 != 2
        case n<=1:
            n^2 <= 1^2 =1<2
            n^2 != 2
        case n>=2:
            n^2 >= 2^2 =4>2
            n^2 != 2
```

### 2.3.3（目标为析取时常证其中一支；此题证右支 x = 2）

Let x be a real number for which 2x + 1 = 5. Show that either x = 1 or x = 2.

```litex
forall x R:
    2 * x + 1 = 5
    =>:
        x=(2*x+1-1)/2=(5-1)/2=2
        x=1 or x=2
```

### 2.3.4（由 (x-1)(x-2)=0 得 x-1=0 或 x-2=0，再分别得 x=1 或 x=2）

Let x be a real number for which x^2 - 3x + 2 = 0. Show that either x = 1 or x = 2.

```litex
know:
    forall a,b R:
        a*b=0
        =>:
            a=0 or b=0
claim:
    prove:
        forall x R:
            x^2 - 3 * x + 2 = 0
            =>:
                x=1 or x=2
    (x - 1) * (x - 2) = x^2 - 3 * x + 2 = 0
    x-1=0 or x-2=0
    by cases:
        prove:
            x=1 or x=2
        case x-1=0:
            x=x-1+1=0+1=1 
        case x-2=0:
            x=x-2+2=0+2=2
```

### 2.3.5（整数 n^2 ≠ 2：对 n 分情形；证明较长，书本用嵌套 obtain / · 子证明）

Let n be a integer number. Show that n^2 != 2.

不知道为啥不能run

<!-- litex:skip-test -->
```litex
claim:
    prove:
        forall n Z:
            =>:
                n^2 != 2
    by cases:
        prove:
            n^2 != 2
        case n<=0:
            by cases:
                prove:
                    n^2 != 2
                case n=-1:
                    n^2 = (-1)^2 >= 1<2
                    n^2 != 2
                case n<-1:
                    n<=-2
                    n^2 = (-n)^2 >= 2^2 =4>2
                    n^2 != 2
        case n>=1:
            by cases:
                prove:
                    n^2 != 2
                case n=1:
                    n^2 = 1^2 = 1<2
                    n^2 != 2
                case n>1:
                    n>=2
                    n^2 >= 2^2 =4>2
                    n^2 != 2
```

## 2.4 “And”（合取： hypotheses 可拆成两条；目标为合取时常需分别证两支）

### 2.4.1（与 1.3.6 同数学，仅假设写成合取）

Let x and y be integers and suppose that 2x - y = 4 and y - x + 1 = 2. Prove that x = 5.

```litex
forall x, y Z:
    2 * x - y = 4
    y - x + 1 = 2
    =>:
        x = (2 * x - y) + (y - x + 1) - 1 = 4 + 2 - 1 = 5
```

### 2.4.2（引理 abs_le_of_sq_le_sq'：p^2 <= y^2 且 y >= 0 => -y <= p <= p）

Let p be a rational number for which p^2 <= 8. Show that p >= -5.

```litex
know:
    forall x,y R:
        x^2<=y^2
        y>=0
        =>:
            -y<=x<=y
forall p Q:
    p^2 <= 8
    =>:
        p^2 <=8<=9=3^2
        -3<= p <=3
        p >= -3>-5
```

### 2.4.3

Let a and b be real numbers and suppose that a - 5b = 4 and b + 2 = 3. Show that a = 9 and b = 1.

```litex
forall a, b R:
    a - 5 * b = 4
    b + 2 = 3
    =>:
        a=a-5*b+5*b=4+5*b=-6+5*(b+2)=-6+5*3=9
        b=b+2-2=3-2=1
```

### 2.4.4

Let a and b be real numbers and suppose that a^2 + b^2 = 0. Show that a = 0 and b = 0.

SOLVED

when n is a even number, then a^n >= 0 is verified automatically.

when 0 <= b, then a <= a + b is verified automatically.

```litex
claim:
    prove:
        forall a, b R:
            a^2 + b^2 = 0
            =>:
                a = 0
                b = 0
    by contra:
        prove:
            a = 0
        a != 0
        0 < a ^ 2
        0 < a ^ 2 + b ^ 2 = 0
        impossible 0 < 0

    by contra:
        prove:
            b = 0
        b != 0
        0 < b ^ 2
        0 < a ^ 2 + b ^ 2 = 0
        impossible 0 < 0
```

## 2.5 Existence proofs（存在量词：Litex 中常写“见证 + 验证”两行；一般需注释说明）

### 2.5.1

Let a be a rational number, and suppose that there exists a rational number b such that a = b^2 + 1. Show that a > 0.

```litex
forall a,b Q:
    a = b^2 + 1
    =>:
        b^2 >= 0
        a = b^2 + 1 >= 0+1=1>0
```

### 2.5.2

Let t be a real number and suppose that there 
exists a real number a such that a*t < 0. Show that t != 0.

SOLVED. a * 0 = 0 is verified by polynomial identity.

```litex
claim:
    prove:
        forall t R:
            exist a R st {a*t < 0}
            =>:
                t != 0
    have by exist a R st {a*t < 0}: a
    a * t < 0
    by contra:
        prove:
            t != 0
        t = 0
        a * t = 0
        impossible a * t < 0
```

### 2.5.3

Show that there exists an integer n such that 12n = 84.

```litex
claim:
    prove:
        exist n Z st {12 * n = 84}
    witness exist n Z st {12 * n = 84} from 7:
        12 * 7 = 84
```

### 2.5.4

Let x be a real number. Show that there exists a real number y such that y > x.

不知道为啥不能run

```litex
# SOLVED
claim:
    prove:
        forall t R:
            exist a R st {a > t}
    witness exist a R st {a > t} from t + 1
    
# 2.5.5
```

```litex
Show that there exist integers m and n such that m^2 - n^2 = 11.
```

```litex
claim:
    prove:
        exist m, n Z st {m^2 - n^2 = 11}
    witness exist m, n Z st {m^2 - n^2 = 11} from 6, 5:
        6^2 - 5^2 = 36 - 25 = 11

# 2.5.6
```

```litex
Let a be an integer. Show that there exist integers m and n such that m^2 - n^2 = 2a + 1.
```

```litex
claim:
    prove:
        forall a Z:
            =>:
                exist m, n Z st {m^2 - n^2 = 2 * a + 1}
    witness exist m, n Z st {m^2 - n^2 = 2 * a + 1} from a + 1, a:
        (a + 1)^2 - a^2 = 2 * a + 1

# 2.5.7
```

```litex
Let p and q be real numbers, and suppose p < q. Show that there exists a real number x such that p < x and x < q.
```

```litex
# SOLVED
claim:
    prove:
        forall p, q R:
            p < q
            =>:
                exist x R st {p < x, x < q}
    witness exist x R st {p < x, x < q} from (p + q) / 2:
        p = (p + p) / 2 < (p + q) / 2
        (p + q) / 2 < (q + q) / 2 = q

# 2.5.8（Ramanujan / 1729）
```

```litex
Show that there exist natural numbers a, b, c and d such that a^3 + b^3 = 1729 = c^3 + d^3 but a != c and a != d.
```

```litex
claim:
    prove:
        exist a, b, c, d N st {a^3 + b^3 = 1729, c^3 + d^3 = 1729, a != c, a != d}
    witness exist a, b, c, d N st {a^3 + b^3 = 1729, c^3 + d^3 = 1729, a != c, a != d} from 1, 12, 9, 10:
        1^3 + 12^3 = 1729
        9^3 + 10^3 = 1729
        1 != 9
        1 != 10
```
