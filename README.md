# The Mechanics of Litex Proof

_Author: Jiachen Shen, Yunwen Guo_

This repository reworks examples from Heather Macbeth's **The Mechanics of Proof** in Litex. The original book is written around Lean; this version asks what the same mathematical training looks like when proofs are written in a language whose surface is closer to ordinary textbook reasoning.

Litex is a formal language still under active development. Its design emphasizes simplicity, learnability, and proof scripts that look close to the mathematical facts they justify. We hope this repository helps readers learn Litex while also comparing it with other formal languages.

## How Litex Proofs Work

The central idea of Litex is: **users write facts; Litex grows a verified context**. A file introduces objects, states facts, checks them, stores successful results, and reuses them later.

Litex proofs are built from three main ingredients:

- **Objects** are mathematical things, such as `2`, `R`, `{1, 2, 3}`, `x + 1`, or `cart(A, B)`.
- **Facts** are mathematical claims about objects, such as `x = 2`, `x $in R`, `0 <= x`, or `forall x R: x = x`.
- **Statements** are proof-script actions: introduce objects, state facts, prove facts, or store known information.

Unlike tactic-heavy proof scripts, Litex often lets the shape of a statement guide verification. An equality chain invites calculation and substitution; an inequality chain invites order reasoning; a membership statement invites set and type rules. The checker has many built-in rules for routine algebra, order, membership, functions, sets, tuples, and finite objects, and it also explains which rule or known fact verified each step.

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

[Chapter 1](./chapter_1_Proofs_by_calculation.md) begins with equalities and inequalities over the familiar number systems `N`, `Z`, `Q`, and `R`.

It introduces the main Litex style for calculation proofs:

- writing equality and inequality chains directly;
- letting Litex use built-in rules such as calculation, substitution, citation, and order reasoning;
- comparing short Litex proofs with Lean-style `calc` proofs;
- reading Litex's verification messages to see which fact or rule proved each step;
- using common shortcuts, such as stored values from simple equations like `x + 4 = 2`.

Future chapters can be added here as the Litex version of the book grows.

Feedback and corrections are welcome on [GitHub](https://github.com/litexlang/golitex) or at litexlang@outlook.com. Visit [Litex's website](https://litexlang.com) for more information.

Reference:
- [The Mechanics of Proof](https://hrmacbeth.github.io/math2001/)