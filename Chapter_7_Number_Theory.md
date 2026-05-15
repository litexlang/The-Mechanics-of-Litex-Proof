# Chapter 7 — Number Theory

Try all snippets in browser: https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Chapter_7_Number_Theory

GitHub source: https://github.com/litexlang/The-Mechanics-of-Litex-Proof/blob/main/Chapter_7_Number_Theory.md

This chapter has a different flavor from the earlier chapters. The theorems here
are classical results, and their proofs often depend on a one-time clever idea
rather than a reusable template. The question for Litex is simple: once the
mathematical idea is clear, can the formal proof still look like the proof one
would write on paper?

## 7.1 Infinitely Many Primes

The first example in Macbeth's chapter is Euclid's theorem: there are infinitely
many primes. In Litex, the proof can be written in the same forward order as the
mathematical idea. Take the factorial-like product
`product(1, a, 'N_pos(x){x})`, then take a prime factor `k` of this product plus
one. If `k <= a`, then `k` divides the product. But `k` also divides the product
plus one, so the same remainder would have to be both `0` and `1`, a
contradiction. Therefore `k > a`.

The point is not that Litex hides the mathematics. The point is that the proof
script is mostly the mathematics. The user writes the facts in order: an
inequality chain, an existential extraction, a case split, a contradiction, and
then the witness for the final existential statement.

Before the main proof, we record three ordinary mathematical facts in a `know`
block: every positive integer `k <= a` divides `1 * 2 * ... * a`; every positive
integer at least `2` has a prime factor; and `a <= 1 * 2 * ... * a`. The appendix
gives a full Litex proof of these facts.

```litex
prop prime(a N_pos):
    2 <= a
    forall b N_pos:
        2 <= b < a
        =>:
            a % b != 0

# can be verified by induction
know:
    forall a, k N_pos:
        k <= a
        =>:
            product(1, a, 'N_pos(x){x}) % k = 0

    forall a N_pos:
        2 <= a
        =>:
            exist k N_pos st {$prime(k), a % k = 0}

    forall a N_pos:
        a <= product(1, a, 'N_pos(x){x})
```

With these facts in the context, the whole proof body is the following 11 lines:

```litex
prop prime(a N_pos):
    2 <= a
    forall b N_pos:
        2 <= b < a
        =>:
            a % b != 0

know:
    forall a, k N_pos:
        k <= a
        =>:
            product(1, a, 'N_pos(x){x}) % k = 0

    forall a N_pos:
        2 <= a
        =>:
            exist k N_pos st {$prime(k), a % k = 0}

    forall a N_pos:
        a <= product(1, a, 'N_pos(x){x})

claim forall! a N_pos: 2 <= a => exist k N_pos st {k > a, $prime(k)}:
    2 <= a <= product(1, a, 'N_pos(x){x}) <= product(1, a, 'N_pos(x){x}) + 1
    have by exist k N_pos st {$prime(k), (product(1, a, 'N_pos(x){x}) + 1) % k = 0}: k
    by cases k > a:
        case k <= a:
            product(1, a, 'N_pos(x){x}) % k = 0
            (product(1, a, 'N_pos(x){x}) + 1) % k = (product(1, a, 'N_pos(x){x}) % k + 1 % k) % k = (0 + 1) % k = 1
            impossible (product(1, a, 'N_pos(x){x}) + 1) % k = 0
        case k > a:
            do_nothing
    witness exist k N_pos st {k > a, $prime(k)} from k
```

For comparison, here is the same proof body next to the Lean version from the
original chapter. The Litex side is the complete forward proof body after the
three `know` facts above have been placed in context.

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>claim forall! a N_pos: 2 <= a => exist k N_pos st {k > a, $prime(k)}:
    2 <= a <= product(1, a, 'N_pos(x){x}) <= product(1, a, 'N_pos(x){x}) + 1
    have by exist k N_pos st {$prime(k), (product(1, a, 'N_pos(x){x}) + 1) % k = 0}: k
    by cases k > a:
        case k <= a:
            product(1, a, 'N_pos(x){x}) % k = 0
            (product(1, a, 'N_pos(x){x}) + 1) % k = (product(1, a, 'N_pos(x){x}) % k + 1 % k) % k = (0 + 1) % k = 1
            impossible (product(1, a, 'N_pos(x){x}) + 1) % k = 0
        case k > a:
            do_nothing
    witness exist k N_pos st {k > a, $prime(k)} from k</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>example (N : ℕ) : ∃ p ≥ N, Prime p := by
  have hN0 : 0 < N ! := by apply factorial_pos
  have hN2 : 2 ≤ N ! + 1 := by addarith [hN0]
  -- `N! + 1` has a prime factor, `p`
  obtain ⟨p, hp, hpN⟩ : ∃ p : ℕ, Prime p ∧ p ∣ N ! + 1 := exists_prime_factor hN2
  have hp2 : 2 ≤ p
  · obtain ⟨hp', hp''⟩ := hp
    apply hp'
  obtain ⟨k, hk⟩ := hpN
  match k with
  | 0 => -- if `k` is zero, contradiction
    have k_contra :=
    calc 0 < N ! + 1 := by extra
      _ = p * 0 := hk
      _ = 0 := by ring
    numbers at k_contra
  | l + 1 => -- so `k = l + 1` for some `l`
    -- the key fact: `p` is not a factor of `N!`
    have key : ¬ p ∣ (N !)
    · apply Nat.not_dvd_of_exists_lt_and_lt (N !)
      use l
      constructor
      · have :=
        calc p * l + p = p * (l + 1) := by ring
          _ = N ! + 1 := by rw [hk]
          _ < N ! + p := by addarith [hp2]
        addarith [this]
      · calc N ! < N ! + 1 := by extra
          _ = p * (l + 1) := by rw [hk]
    -- so `p` is a prime number greater than or equal to `N`, as we sought
    use p
    constructor
    · obtain h_le | h_gt : p ≤ N ∨ N < p := le_or_lt p N
      · have : p ∣ (N !)
        · apply dvd_factorial
          · extra
          · addarith [h_le]
        contradiction
      · addarith [h_gt]
    · apply hp</code></pre>
    </td>
  </tr>
</table>

The Litex proof does not depend on any external import. It also does not ask the
user to remember a separate list of theorem or tactic names for this argument.
The proof is written from top to bottom as a sequence of mathematical facts, and
later lines use the context produced by earlier lines directly.

## 7.2 Gauss's Lemma From Bézout

The next useful number-theoretic move is Gauss's lemma. In Lean, after one has
Bézout's identity, the proof is a short calculation: if `d | a * b` and
`gcd(a, d) = 1`, take integers `x` and `y` with
`1 = x * a + y * d`, take `z` with `a * b = d * z`, and then rewrite

```text
b = b * 1
  = b * (x * a + y * d)
  = x * (a * b) + b * y * d
  = x * (d * z) + b * y * d
  = d * (x * z + b * y).
```

So the witness for `d | b` is `x * z + b * y`.

In the current Litex file we do not need to rebuild the Euclidean algorithm.
We first record Bézout's identity as known. Since this chapter has not defined a
first-class `gcd` function in Litex, the predicate `$gcd_eq_one(a, d)` is used
as the readable placeholder for the hypothesis `gcd(a, d) = 1`.

```litex
prop divides(a Z, b Z):
    exist k Z st {b = a * k}

abstract_prop gcd_eq_one(a, d)

know:
    forall a, d Z:
        $gcd_eq_one(a, d)
        =>:
            exist x Z, y Z st {1 = x * a + y * d}
```

With Bézout in context, Gauss's lemma is just an existential witness proof.
The two `have by exist` lines extract the Bézout coefficients and the quotient
coming from `d | a * b`. The final `witness` line supplies the quotient for
`d | b`.

```litex
prop divides(a Z, b Z):
    exist k Z st {b = a * k}

abstract_prop gcd_eq_one(a, d)

know:
    forall a, d Z:
        $gcd_eq_one(a, d)
        =>:
            exist x Z, y Z st {1 = x * a + y * d}

claim:
    prove:
        forall d, a, b Z:
            $divides(d, a * b)
            $gcd_eq_one(a, d)
            =>:
                $divides(d, b)

    have by exist x Z, y Z st {1 = x * a + y * d}: u, v
    have by exist z Z st {a * b = d * z}: z
    witness exist k Z st {b = d * k} from u * z + b * v:
        b = b * 1 = b * (u * a + v * d) = u * (a * b) + b * v * d = u * (d * z) + b * v * d = d * (u * z + b * v)
```

## Appendix: Full Litex Version

Here is the full version of the same example. The three `know` facts from the
main text are proved in the same file, and the final 11-line core proof is left
unchanged.

```litex
prop prime(a N_pos):
    2 <= a
    forall b N_pos:
        2 <= b < a
        =>:
            a % b != 0

claim:
    prove:
        forall a N_pos:
            product(1, a, 'N_pos(x){x}) % a = 0 and a <= product(1, a, 'N_pos(x){x})

    by induc a from 1:
        prove:
            product(1, a, 'N_pos(x){x}) % a = 0 and a <= product(1, a, 'N_pos(x){x})

        product(1, 1, 'N_pos(x){x}) = 1
        1 <= product(1, 1, 'N_pos(x){x})

        claim:
            prove:
                forall k Z:
                    k >= 1
                    product(1, k, 'N_pos(x){x}) % k = 0 and k <= product(1, k, 'N_pos(x){x})
                    =>:
                        product(1, k + 1, 'N_pos(x){x}) % (k + 1) = 0 and k + 1 <= product(1, k + 1, 'N_pos(x){x})

            product(1, k + 1, 'N_pos(x){x}) = product(1, k, 'N_pos(x){x}) * (k + 1)
            witness exist t Z st {product(1, k + 1, 'N_pos(x){x}) = t * (k + 1)} from product(1, k, 'N_pos(x){x})
            product(1, k + 1, 'N_pos(x){x}) % (k + 1) = 0
            k + 1 <= product(1, k + 1, 'N_pos(x){x})

claim:
    prove:
        forall a, k N_pos:
            k <= a
            =>:
                product(1, a, 'N_pos(x){x}) % k = 0

    by cases:
        prove:
            product(1, a, 'N_pos(x){x}) % k = 0
        case k = a:
            product(1, a, 'N_pos(x){x}) % a = 0
            product(1, a, 'N_pos(x){x}) % k = product(1, a, 'N_pos(x){x}) % a = 0
        case k < a:
            product(1, a, 'N_pos(x){x}) = product(1, k, 'N_pos(x){x}) * product(k + 1, a, 'N_pos(x){x})
            product(1, k, 'N_pos(x){x}) % k = 0
            have by exist r Z st {product(1, k, 'N_pos(x){x}) = r * k}: r
            witness exist t Z st {product(1, a, 'N_pos(x){x}) = t * k} from r * product(k + 1, a, 'N_pos(x){x}):
                product(1, a, 'N_pos(x){x}) = product(1, k, 'N_pos(x){x}) * product(k + 1, a, 'N_pos(x){x}) = (r * k) * product(k + 1, a, 'N_pos(x){x}) = (r * product(k + 1, a, 'N_pos(x){x})) * k
            product(1, a, 'N_pos(x){x}) % k = 0

claim:
    prove:
        forall a N_pos:
            a <= product(1, a, 'N_pos(x){x})

    product(1, a, 'N_pos(x){x}) % a = 0 and a <= product(1, a, 'N_pos(x){x})

claim:
    prove:
        forall a N_pos:
            2 <= a
            =>:
                exist k N_pos st {$prime(k), a % k = 0}

    by strong_induc x from 2:
        prove:
            exist k N_pos st {$prime(k), x % k = 0}

        claim:
            prove:
                forall b N_pos:
                    2 <= b < 2
                    =>:
                        2 % b != 0
            by contra 2 % b != 0:
                impossible b < 2
        $prime(2)

        witness exist t Z st {2 = t * 2} from 1
        2 % 2 = 0
        witness exist k N_pos st {$prime(k), 2 % k = 0} from 2

        claim:
            prove:
                forall n Z:
                    n >= 2
                    forall m Z:
                        2 <= m
                        m <= n
                        =>:
                            exist k N_pos st {$prime(k), m % k = 0}
                    =>:
                        exist k N_pos st {$prime(k), (n + 1) % k = 0}

            by cases exist k N_pos st {$prime(k), (n + 1) % k = 0}:
                case $prime(n+1):
                    witness exist t Z st {n + 1 = t * (n + 1)} from 1
                    (n + 1) % (n + 1) = 0
                    witness exist k N_pos st {$prime(k), (n + 1) % k = 0} from n+1
                case not $prime(n+1):
                    by contra:
                        prove:
                            not forall b N_pos:
                                2 <= b < n + 1
                                =>:
                                    (n + 1) % b != 0
                        2 <= n + 1
                        $prime(n+1)
                        impossible $prime(n+1)

                    have by exist b N_pos st {2 <= b < n+1, not (n + 1) % b != 0}: c

                    2 <= c < n+1

                    (n+1) % c = 0
                    c <= n or c >= n + 1
                    by cases:
                        prove:
                            c <= n
                        case c <= n:
                            ...
                        case c >= n + 1:
                            impossible c < n + 1

                    have by exist k N_pos st {$prime(k), c % k = 0}: d

                    have by exist k Z st {(n+1) = k * c}: e

                    have by exist k Z st {c = k * d}: f

                    witness exist t Z st {e * f * d = t * d} from e * f
                    (e * f * d) % d = 0

                    witness exist k N_pos st {$prime(k), (n + 1) % k = 0} from d:
                        n + 1 = e * c = e * (f * d) = (e * f) * d
                        (n + 1) % d = ((e * f) * d) % d = 0

claim forall! a N_pos: 2 <= a => exist k N_pos st {k > a, $prime(k)}:
    2 <= a <= product(1, a, 'N_pos(x){x}) <= product(1, a, 'N_pos(x){x}) + 1
    have by exist k N_pos st {$prime(k), (product(1, a, 'N_pos(x){x}) + 1) % k = 0}: k
    by cases k > a:
        case k <= a:
            product(1, a, 'N_pos(x){x}) % k = 0
            (product(1, a, 'N_pos(x){x}) + 1) % k = (product(1, a, 'N_pos(x){x}) % k + 1 % k) % k = (0 + 1) % k = 1
            impossible (product(1, a, 'N_pos(x){x}) + 1) % k = 0
        case k > a:
            do_nothing
    witness exist k N_pos st {k > a, $prime(k)} from k
```
