# The Mechanics of Litex Proof

Jiachen Shen and The Litex Team, 2026-05-14. Email: litexlang@outlook.com

Try all snippets in browser: https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Introduction

Markdown source: https://github.com/litexlang/The-Mechanics-of-Litex-Proof/blob/main/README.md

Litex is a formal language for writing and checking mathematical proofs. Its
design emphasizes simplicity, learnability, and proof scripts that look close to
the mathematical facts they justify. Instead of asking users to build every
small logical or algebraic step by hand, Litex provides builtin reasoning for
routine calculation, order, membership, and logical structure.

This book reworks examples from Heather Macbeth's **The Mechanics of Proof** in
Litex. The original book is written around Lean; this version asks what the same
mathematical training looks like when proofs are written in a language whose
surface is closer to ordinary textbook reasoning.

Special thanks to *Yunwen Guo* for helping with the book.

## How Litex Proofs Work

The central idea of Litex is: **users write facts; Litex grows a verified context**. A file introduces objects, states facts, checks them, stores successful results, and reuses them later.

Litex proofs are built from three main ingredients:

- **Objects** are mathematical things, such as `2`, `R`, `{1, 2, 3}`, `x + 1`, or `cart(A, B)`.
- **Facts** are mathematical claims about objects, such as `x = 2`, `x $in R`, `0 <= x`, or `forall x R: x = x`.
- **Statements** are proof-script actions: introduce objects, state facts, prove facts, or store known information.

Unlike tactic-heavy proof scripts, Litex often lets the shape of a statement guide verification. An equality chain invites calculation and substitution; an inequality chain invites order reasoning; a membership statement invites set and type rules. The checker has many built-in rules for routine algebra, order, membership, functions, sets, tuples, and finite objects, and it also explains which rule or known fact verified each step.

Litex does not require an IDE-specific output panel to see this feedback. The
online documentation can run examples directly in the page; for instance,
[Chapter 1 online](https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Chapter_1_Proofs_By_Calculation)
lets you click **Run** on each example and inspect the verification output.
If you install Litex locally, the command-line runner prints the same kind of
output when you run a file or a snippet.

For example:

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

The user states the desired facts directly. Litex handles routine rewriting, arithmetic, and reuse of the assumption `x = 2`.

## Chapters

### Chapter 1 — Proofs by calculation

Chapter 1 begins with equalities and inequalities over the familiar number systems `N`, `Z`, `Q`, and `R`.

It introduces the main Litex style for calculation proofs:

- writing equality and inequality chains directly;
- letting Litex use built-in rules such as calculation, substitution, citation, and order reasoning;
- comparing short Litex proofs with Lean-style `calc` proofs;
- reading Litex's verification messages to see which fact or rule proved each step;
- using common shortcuts, such as stored values from simple equations like `x + 4 = 2`.

### Chapter 2 — Proofs with structure

Chapter 2 moves from single calculation chains to structured proofs.

It introduces:

- universal statements with `forall`;
- implications with `=>:`;
- local proof blocks with `claim`;
- existential statements with `witness` and `have by exist`;
- proof by contradiction with `by contra`;
- case splits with `by cases`.

### Chapter 3 — Parity and divisibility

Chapter 3 develops examples about evenness, divisibility, and modular arithmetic.

It shows how to:

- define reusable predicates with `prop`;
- use existential witnesses for divisibility;
- work with integer and natural-number divisibility;
- reason with congruences and modular residues;
- combine earlier proof structure with arithmetic facts.

### Chapter 4 — Proofs with structure II

Chapter 4 revisits structured proof tools in larger examples.

It covers:

- quantified statements with multiple hypotheses;
- equivalence proofs and `iff`-style reasoning;
- uniqueness and `exist_unique`;
- contradiction and impossible branches;
- case splits over algebraic, order, and modular facts.

### Chapter 5 — Logic

Chapter 5 focuses on the logical patterns behind the earlier proofs.

It explains:

- why Litex does not quantify over `Prop`;
- how to use `abstract_prop` for schematic logical examples;
- how built-in logic handles `and`, `or`, `not`, and implication-shaped facts;
- how `by for` proves bounded universal statements over finite ranges;
- how to write negation-normal forms directly in Litex.

### Chapter 7 — Number theory

Chapter 7 starts with Euclid's theorem that there are infinitely many primes.

It highlights:

- how Litex can express the core proof as a short forward proof script;
- how `know` facts can record standard mathematical facts before the main proof;
- how the full version can also prove those facts inside the same file;
- how the Litex style compares with Lean proofs that depend on remembered theorem and tactic names.

Feedback and corrections are welcome on [GitHub](https://github.com/litexlang/golitex) or at litexlang@outlook.com. Visit [Litex's website](https://litexlang.com), [Online Manual](https://litexlang.com/doc/Manual) for more information.

Reference:
- [The Mechanics of Proof](https://hrmacbeth.github.io/math2001/)

> **Learning hint.** Learning Litex is mostly learning how to transcribe ordinary mathematical writing faithfully. The extra effort you spend reading this chapter tracks the mathematics you express, more than memorizing proof-engine choreography.
>
> Lean is oriented differently at the tooling layer: besides the mathematics, you routinely invest in dependent type theory, Lean's notation and elaboration habits, locating and remembering facts in Mathlib, and assembling tactic scripts around each goal. Litex trims that outer stack early so informal math carries more of the weight.
