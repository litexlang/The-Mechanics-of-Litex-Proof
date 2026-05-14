# Chapter 9 — Sets

Original chapter: https://hrmacbeth.github.io/math2001/09_Sets.html

This chapter is where Litex's foundational choice becomes especially visible.
Lean presents a set of elements of type `X` as `Set X`, essentially a predicate
on `X`. That is powerful, but it means the user often has to keep track of a
type-level hierarchy:

```lean
x : X
U : Set X
S : Set (Set X)
T : Set (Set (Set X))
```

Litex is deliberately closer to ordinary set-theoretic writing. Sets are
ordinary mathematical objects, membership is written directly with `$in`, and
there is no separate `Set X`, `Set (Set X)`, `Set (Set (Set X))` ladder that the
user has to manage. A set can itself be an element of another set, and nested
membership can be written exactly as it is read:

```litex
{1, 2} $in {{}, {1, 2}}
{{3}} $in {{{3}}}
```

This does not mean that every membership claim is true. It means the expression
is mathematically well-formed at the surface level. Litex can then try to verify
or refute it from the current context, definitions, and builtin set rules. That
is the core convenience: the proof script spends less effort on representation
and more effort on the mathematical reason.

## 9.1 Membership And Subsets

Macbeth starts the chapter with sets written by predicates, such as the set of
integers `n` satisfying `n <= 3`. In Lean, this lives at a specific type:
`Set Int`. In Litex, the same idea is a set-builder object:

```litex
prove:
    1 <= 3
    1 $in {n Z : n <= 3}
```

The point is small but important. The line `1 $in {n Z : n <= 3}` is already
the mathematical sentence. There is no need to unfold a predicate encoding or
choose a tactic for the membership relation.

### Subset

Subset is also built into the surface language:

```litex
prove:
    let A, B set:
        A $subset B
    forall x A:
        x $in B
```

From `A $subset B`, Litex records the expected membership consequence: every
element of `A` is an element of `B`. In Lean, this same idea is usually applied
as a function:

```lean
example {X : Type} {A B : Set X} (hAB : A ⊆ B) {x : X} (hx : x ∈ A) : x ∈ B := by
  exact hAB hx
```

Both are mathematically clean. The difference is ergonomic: Litex lets the
subset statement behave like the mathematical fact a beginner expects it to be.

### Example: Multiples Of Four Are Multiples Of Two

The original chapter proves subset facts such as

```text
{a : N | 4 divides a} subset {b : N | 2 divides b}.
```

In Litex, divisibility is just an existential definition, and the proof is a
witness calculation.

```litex
prop dvdN(a N, b N):
    a >= 1
    exist c N st {b = a * c}

claim:
    prove:
        forall a N:
            $dvdN(4, a)
            =>:
                $dvdN(2, a)
    have by exist k N st {a = 4 * k}: k
    witness exist l N st {a = 2 * l} from 2 * k:
        a = 4 * k = 2 * (2 * k)
```

The set-level reading is immediate: if `a` belongs to the set of multiples of
`4`, then `a` belongs to the set of multiples of `2`.

### Extensionality

To prove two sets equal, prove they have the same elements. Lean commonly uses
`ext`; Litex has the same mathematical idea as a proof pattern, and for many
set-builder or finite-display examples the membership conditions are directly
available.

```litex
claim:
    prove:
        {x R : x^2 - x - 2 = 0} = {-1, 2}
    forall x R:
        x^2 - x - 2 = 0
        =>:
            x $in {-1, 2}
        x^2 - x - 2 = (x + 1) * (x - 2)
        (x + 1) * (x - 2) = 0
        x + 1 = 0 or x - 2 = 0
        x = -1 or x = 2
        x $in {-1, 2}

    forall x {-1, 2}:
        x^2 - x - 2 = 0
```

The important feature is not that Litex hides extensionality. It makes the
extensional argument look like the usual mathematical argument: show both
membership directions.

## 9.2 Set Operations

Union, intersection, complement, empty set, and universal set are conceptually
simple. They become verbose in formal systems when the encoding gets in the
way. Litex treats the ordinary set operations and membership facts as basic
mathematical material.

### Union

Macbeth's example says every real number belongs to

```text
{x : R | -1 < x} union {x : R | x < 1}.
```

The proof is the same split one would write on paper: either `t <= 0` or
`t > 0`.

```litex
claim:
    prove:
        forall t R:
            t $in {x R : -1 < x} or t $in {x R : x < 1}
    t <= 0 or t > 0
    by cases:
        prove:
            t $in {x R : -1 < x} or t $in {x R : x < 1}
        case t <= 0:
            t < 1
            t $in {x R : x < 1}
        case t > 0:
            -1 < t
            t $in {x R : -1 < x}
```

For finite unions, Litex can reason directly with finite displays:

```litex
claim:
    prove:
        forall n N:
            n $in {1, 2} or n $in {2, 4}
            =>:
                n $in {1, 2, 4}
    by cases:
        prove:
            n $in {1, 2, 4}
        case n $in {1, 2}:
            n = 1 or n = 2
            n $in {1, 2, 4}
        case n $in {2, 4}:
            n = 2 or n = 4
            n $in {1, 2, 4}
```

### Intersection

Intersection proofs are usually just proofs with two membership facts. For
example, from

```text
t in {-2, 3} and t in {x : Q | x^2 = 9}
```

we can prove `0 < t`: the `t = -2` branch contradicts `t^2 = 9`, and the
`t = 3` branch is positive.

```litex
claim:
    prove:
        forall t Q:
            t $in {-2, 3}
            t $in {x Q : x^2 = 9}
            =>:
                t $in {a Q : 0 < a}
    t = -2 or t = 3
    by cases:
        prove:
            t $in {a Q : 0 < a}
        case t = -2:
            (-2)^2 = 4
            impossible t^2 = 9
        case t = 3:
            0 < t
            t $in {a Q : 0 < a}
```

### Empty And Universal Sets

Litex can use the empty set directly:

```litex
prove:
    not $is_nonempty_set({})
```

For universal-set reasoning, Litex often does not need a separate `univ` object.
A parameter declaration such as `forall t R:` already says that `t` ranges over
the real numbers. So a proof that every real number satisfies a membership
condition is written as an ordinary universal statement:

```litex
claim:
    prove:
        forall t R:
            t $in {x R : -1 < x} or t $in {x R : x < 1}
```

This is another place where the lack of a hierarchy helps. The user does not
have to decide whether to reason about `t : R`, `t ∈ Set.univ`, or a coercion
between the two. The surface sentence is the mathematical one.

## 9.3 Sets Of Sets

The original chapter then moves to sets whose elements are themselves sets.
This is exactly where Litex's set-theoretic surface is most convenient.

In Lean, nested set membership asks for explicit types:

```lean
example : ({1, 2} : Set Nat) ∈ ({∅, {1, 2}} : Set (Set Nat)) := by
  simp
```

In Litex, the nested set is written directly:

```litex
prove:
    {1, 2} $in {{}, {1, 2}}
```

The same applies to deeper nesting:

```litex
prove:
    {{3}} $in {{{3}}}
```

This is not a trick. It is the normal set-theoretic view: an object can be an
element of a set, and a set is also an object.

### Power Sets

Macbeth writes about `Set X`, the collection of all subsets of `X`. In Litex,
this is naturally expressed as `power_set(X)`.

```litex
prove:
    {1, 2} $in power_set({1, 2, 3})
```

Lean often turns this into the underlying subset proof:

```lean
example : ({1, 2} : Set Nat) ⊆ ({1, 2, 3} : Set Nat) := by
  intro x hx
  simp at hx
  simp [hx]
```

Litex keeps the statement at the level where the mathematician said it:
membership in the power set.

Power sets also let us write functions on sets without changing language level:

```litex
have product_of fn(s power_set(R): $is_finite_set(s)) R
```

Here `s` is a finite subset of `R`. There is no separate coercion from a
`Finset` to a `Set`, no decidable membership argument, and no typeclass search
visible to the user.

## 9.4 Functions On Sets

The chapter gives examples of functions whose inputs or outputs are sets. In
Litex, these are ordinary functions because sets are ordinary objects.

For example, define

```litex
have fn p_of(s set) set = {n N : (n + 1) $in s}
```

This map is not injective on sets of natural numbers: `{0}` and `{}` have the
same preimage under the shift, because no natural number `n` satisfies
`n + 1 = 0`.

```litex
claim:
    prove:
        exist s set, t set st {
            p_of(s) = p_of(t)
            s != t
        }
    witness exist s set, t set st {
        p_of(s) = p_of(t)
        s != t
    } from {0}, {}:
        p_of({0}) = {}
        p_of({}) = {}
        p_of({0}) = p_of({})
        0 $in {0}
        not 0 $in {}
```

On integers, the analogous shift is injective, because every integer `k` can be
written as `(k - 1) + 1`.

```litex
have fn q_of(s set) set = {n Z : (n + 1) $in s}

claim:
    prove:
        forall s set, t set:
            q_of(s) = q_of(t)
            =>:
                s = t
    forall k Z:
        k $in s
        <=>:
            (k - 1) $in q_of(s)
    forall k Z:
        k $in t
        <=>:
            (k - 1) $in q_of(t)
    forall k Z:
        k $in s
        <=>:
            k $in t
    s = t
```

Again, the proof is extensional. The value of the Litex syntax is that all the
objects involved are still just sets and elements.

## 9.5 Cantor's Theorem

The final major result is Cantor's theorem: there is no surjection from a set
onto its power set. The classical proof is diagonalization. Given a function
`f`, form the set

```text
D = {x | not x in f(x)}.
```

If `f` were surjective, then `D = f(a)` for some `a`. But then

```text
a in D  iff  not a in f(a)  iff  not a in D,
```

which is impossible.

In Lean, this proof is a good example of the strength of dependent type theory:
the theorem can be stated very generally and connected to Mathlib's library of
cardinality results. In Litex, the advantage is the opposite: the diagonal set
can be written in the same set-builder language as every earlier example.

```litex
# schematic Litex shape
have fn f(x X) power_set(X)

let D set:
    D = {x X : not x $in f(x)}
```

The proof idea is then ordinary membership reasoning:

```litex
a $in D
<=>:
    not a $in f(a)
```

Cantor's theorem is therefore a good summary of the chapter. Litex is not trying
to replace Lean's hierarchy of abstractions for large library engineering. It is
choosing a set-theoretic surface so that everyday set arguments can be written
in the language in which they are usually explained.

## Litex Takeaways

1. `x $in A` is a primitive mathematical sentence in Litex, not something the
   user has to route through a type-specific encoding.

2. Sets are objects. A set can be an element of another set without forcing the
   user to manually build a visible `Set (Set X)` hierarchy.

3. `A $subset B` behaves like the mathematical fact it denotes: membership in
   `A` gives membership in `B`.

4. `power_set(X)` lets the user write "a subset of `X`" directly as membership
   in a set of sets.

5. Extensionality remains the core proof principle: to prove two sets equal,
   prove that they have the same elements.

6. The main comparison with Lean is not that one system can express sets and
   the other cannot. Both can. The difference is surface friction. Lean exposes
   a precise type-theoretic hierarchy; Litex presents ordinary set-theoretic
   syntax first.
