# The Mechanics of Litex Proof

Jiachen Shen and The Litex Team, 2026-05-14. Email: litexlang@outlook.com

Special thanks to *Yunwen Guo* for helping with the book.

Try all snippets in browser: https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Introduction

Markdown source: https://github.com/litexlang/The-Mechanics-of-Litex-Proof/blob/main/README.md


## What is Litex?

_Truth is ever to be found in simplicity, and not in the multiplicity and confusion of things._

_– Isaac Newton_

Litex is an open-source formal language for writing mathematical proofs that
look close to ordinary mathematical writing. Users write facts, definitions, and
proof steps in a direct mathematical style; Litex checks them, stores verified
results, and reuses them as the proof context grows.

The central idea is: **users write facts; Litex grows a verified context**. A
Litex file introduces mathematical objects, states claims about them, verifies
those claims, and makes successful facts available to later lines.

Litex is designed around familiar proof structures: equalities, inequalities,
membership, subsets, functions, witnesses, contradiction, case splits, and
induction. Instead of asking users to spell out every small logical or algebraic
step, Litex provides builtin reasoning for routine calculation, order,
membership, substitution, and logical structure.

For example, a Litex proof can state the desired facts directly:

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

The user states the desired facts directly. Litex handles routine rewriting, arithmetic, and reuse of the assumption `x = 2`.

## About This Book

_A mathematician, like a painter or a poet, is a maker of patterns._

_– G. H. Hardy, *A Mathematician's Apology*_

This book reworks examples from Heather Macbeth's **The Mechanics of Proof** in
Litex. The original book is written around Lean; this version asks what the same
mathematical training looks like when proofs are written in a language whose
surface is closer to ordinary textbook reasoning.

The goal is not to replace the Lean version. Lean has a broad, mature ecosystem,
and Mathlib gives it far more coverage of advanced mathematics today. This book
instead explores a different interface for proof writing: one where the user
tries to write the mathematical argument itself, and the checker explains why
each accepted fact follows.

The online documentation can run examples directly in the page; for instance,
[Chapter 1 online](https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Chapter_1_Proofs_By_Calculation)
lets you click **Run** on each example and inspect the verification output.

If you install Litex locally (Visit [Setup](https://litexlang.com/doc/Setup) for installation instructions), the command-line runner prints the same kind of
output when you run a file or a snippet.

## Chapters

### Chapter 1 — Proofs by calculation

Chapter 1 begins with equalities and inequalities over the familiar number
systems `N`, `Z`, `Q`, and `R`. It introduces calculation chains, substitution,
order reasoning, and the habit of reading Litex's verification output to see why
each step was accepted.

### Chapter 2 — Proofs with structure

Chapter 2 moves from single calculation chains to structured proofs. It covers
universal statements, implications, local claims, existential witnesses, proof
by contradiction, and case splits.

### Chapter 3 — Parity and divisibility

Chapter 3 develops examples about evenness, divisibility, and modular
arithmetic. It shows how reusable predicates, witnesses, congruences, and
arithmetic facts work together in short forward proofs.

### Chapter 4 — Proofs with structure II

Chapter 4 revisits structured proof tools in larger examples. It discusses
multiple hypotheses, equivalence proofs, uniqueness, impossible branches, and
case splits over algebraic, order, and modular facts.

### Chapter 5 — Logic

Chapter 5 focuses on the logical patterns behind the earlier proofs. It explains
schematic propositions, builtin reasoning for `and`, `or`, `not`, and
implication-shaped facts, bounded universal proofs, and negation-normal forms.

### Chapter 6 — Induction

Chapter 6 develops induction, recursive definitions, and well-founded
definitions by decreasing measures. It includes ordinary induction, strong
induction, recursive sequences and functions, Pascal's triangle, factorial
identities, and examples where Litex checks long mechanical expansions.

### Chapter 7 — Number theory

Chapter 7 starts with Euclid's theorem that there are infinitely many primes.
It shows how standard number-theoretic facts can be recorded with `know`, how a
full proof can justify those facts inside the same file, and how Litex expresses
the core argument as a short forward proof script.

### Chapter 8 — Sets

Chapter 8 turns to set-theoretic reasoning. It introduces subsets, set
membership, set equality, unions, intersections, complements, products, and the
way Litex checks ordinary element-chasing arguments.

### Chapter 9 — Functions

Chapter 9 treats functions as mathematical objects. It discusses function
application, images and preimages, injective and surjective maps, inverse
functions, and how Litex represents functions in a set-theoretic style.

### Chapter 10 — Cardinality

Chapter 10 studies bijections, finite and infinite sets, countability, and
cardinality comparisons. It includes examples such as constructing bijections
and formalizing arguments in the spirit of Cantor-Schröder-Bernstein.

## References

- [The Mechanics of Proof](https://hrmacbeth.github.io/math2001/)
