# The exact orientation threshold 4 of the cubic Padovan substitution, the quartic substitution and their twelve-letter tensor (inflation factor `ρQ`)

Kernel-checked, in Lean 4 + Mathlib. A substitution sends each letter of a finite alphabet to a
nonempty word; its factor language from a seed letter is the set of words that occur as a
contiguous block of some iterate. Call a length `L` *oriented* when no factor of length `L` has its
reversal among the factors. Being oriented passes to every longer length (the reversal of a long
factor contains the reversal of its length-`L` prefix), and it fails at `L` whenever some factor of
length `L` is a palindrome. The *orientation threshold* is the least oriented length. For three
substitutions this entry proves the threshold is exactly `4`: a palindrome of length three occurs,
and every factor of length at least four has a reversal that is not a factor. The three are the
cubic Padovan substitution (`x³ − x − 1`), the quartic substitution of `x⁴ − x − 1`, and their
twelve-letter tensor product, whose inflation factor is the product `ρQ` of the two real roots
`ρ > 1` and `Q > 1`. For the quartic and the tensor substitution the result holds from every seed
letter, and across seeds.

## The objects

- **The cubic Padovan substitution** on `{a, b, c}`: `a ↦ b, b ↦ c, c ↦ ab`. Its incidence matrix
  has characteristic polynomial `x³ − x − 1`; its inflation factor is the plastic number
  `ρ = 1.3247…`. Seed `a`.
- **The quartic substitution** on `{a, b, c, d}`: `a ↦ b, b ↦ c, c ↦ d, d ↦ ab`. Characteristic
  polynomial `x⁴ − x − 1`; inflation factor its real root `Q = 1.2207…` greater than one. Seed `a`.
- **The tensor substitution** on `{p, q, r} × {1, 2, 3, 4}`, writing `p, q, r` for the cubic letters
  and `1, 2, 3, 4` for the quartic ones: the letter `xi` goes to the word of the pairs `yj`, where `y`
  runs through the cubic image of `x` (outer) and `j` through the quartic image of `i` (inner):

  | | | |
  |---|---|---|
  | `p1 ↦ q2` | `q1 ↦ r2` | `r1 ↦ p2 q2` |
  | `p2 ↦ q3` | `q2 ↦ r3` | `r2 ↦ p3 q3` |
  | `p3 ↦ q4` | `q3 ↦ r4` | `r3 ↦ p4 q4` |
  | `p4 ↦ q1 q2` | `q4 ↦ r1 r2` | `r4 ↦ p1 p2 q1 q2` |

  Its incidence matrix is the Kronecker product of the two incidence matrices. Its characteristic
  polynomial is `x¹² − 3x⁹ − 2x⁸ + 2x⁶ − x⁵ − 3x⁴ − x³ + x − 1`, the minimal polynomial of
  `ρQ = 1.6171…`, which is therefore the inflation factor. Seed `p1`.
- `S` applies a substitution letterwise to words. `InLanguage u` means `∃ n, u <:+: S^[n] [seed]`,
  where `<:+:` is Mathlib's `List.IsInfix` (contiguous sub-block). `InLanguageFrom x u` is the same
  with seed `x`.

The characteristic polynomials and inflation factors are given so the reader can place the
substitutions. No compared statement uses them, and they are not proved in the package; the tensor
values were checked by direct computation.

## The compared statements (namespace `FourTickOrientation`)

`THR(InLanguage)` abbreviates
`(∃ u, InLanguage u ∧ u.length = 3 ∧ u.reverse = u) ∧ (∀ u, InLanguage u → 4 ≤ u.length → ¬ InLanguage u.reverse)`.

| # | name | statement |
|---|------|-----------|
| 1 | `Cubic.exact_orientation_threshold_four` | `THR(InLanguage)` for the cubic Padovan substitution, seed `a`. The palindrome is `a b a`, in `S^[8] [a] = c a b a b b c` |
| 2 | `Quartic.exact_orientation_threshold_four` | `THR(InLanguage)` for the quartic substitution, seed `a`. The palindrome is `a b a`, in `S^[11] [a] = d a b a b b c` |
| 3 | `Quartic.inLanguageFrom_iff` | `∀ x u, InLanguageFrom x u ↔ InLanguage u`: the quartic factor language does not depend on the seed |
| 4 | `Quartic.exact_orientation_threshold_four_any_seed` | for all seeds `x, y`: `(∃ u, InLanguageFrom x u ∧ u.length = 3 ∧ u.reverse = u) ∧ (∀ u, InLanguageFrom x u → 4 ≤ u.length → ¬ InLanguageFrom y u.reverse)` |
| 5 | `Tensor.exact_orientation_threshold_four` | `THR(InLanguage)` for the tensor substitution, seed `p1`. The palindrome is `q1 q2 q1`, at positions 15–17 of the 28-letter word `S^[8] [p1]` |
| 6 | `Tensor.inLanguageFrom_iff` | `∀ x u, InLanguageFrom x u ↔ InLanguage u` for the tensor substitution |
| 7 | `Tensor.exact_orientation_threshold_four_any_seed` | statement 4's form, for the tensor substitution |

Every compared theorem depends on no axiom outside `propext`, `Classical.choice` and `Quot.sound`
(the two `inLanguageFrom_iff` statements use only `propext` and `Quot.sound`). No `native_decide`
is used anywhere in the package: every finite check is `decide` or `decide +kernel`.

## The proof

1. **Window lemma.** Every image block is nonempty, so a factor of `S w` of length `≤ L` lies inside
   the image of a factor of `w` of length `≤ L` (`infix_window`).
2. **A finite certificate.** A finite list of short words contains the seed's factors and is closed
   under taking short windows of images. By induction on `n` it then contains every short factor of
   every iterate (`factors_complete`). It is used only as an upper bound on the factor set; that
   every listed word actually occurs is not needed. Cubic: 57 words of length `≤ 5`, closure by
   `decide`. Quartic: 72 words of length `≤ 4` (1 + 4 + 13 + 22 + 32 by length). Tensor: 456 words of
   length `≤ 4` (1 + 12 + 79 + 148 + 216). The quartic and tensor certificates are packed into a bit
   mask indexed by a base-5 or base-13 word code, and both checks run by `decide +kernel` over every
   word of length `≤ 4` (341 and 22,621 words).
3. **Length four.** No length-four word of the certificate has its reversal in the certificate
   (`decide` / `decide +kernel`). If `u` is a factor with `|u| ≥ 4` and `t` is its length-four
   prefix, then `t.reverse` is a factor of `u.reverse`. So `u.reverse` cannot be a factor
   (`reversal_forbidden_of_four_le`).
4. **Length three.** An explicit iterate, evaluated by `decide`, contains the palindrome.
5. **Seeds.** For the quartic and the tensor substitution, every letter occurs in an iterate of the
   seed and the seed occurs in an iterate of every letter (explicit iterates, by `decide`). Since
   `S` maps factors to factors, the languages coincide (statements 3, 6). Statements 4 and 7 transport
   statements 2 and 5 along them.

## Relation to the literature

- The cubic Padovan substitution is a standard example of a Pisot substitution (its inflation factor
  `ρ` is the smallest Pisot number). Palindromes in fixed points of substitutions are a long-studied
  topic: palindromic complexity, and the conditions under which a language is closed under reversal.
- Literature and prior-formalization search, run 2026-11-26. Sources: the arXiv API with full texts of the papers cited
  here; Crossref; the Palomar registry search API; Mathlib master; the Isabelle AFP; web search.
  - **The general fact behind the threshold is published.** Allouche, Campbell, Li, Shallit and Stipulanti (Theory
    Comput. Syst. 69 (2025), article 31, DOI 10.1007/s00224-025-10234-x; arXiv:2406.09302) call a factor *reflected*
    when its reversal is also a factor. Their Theorem 11 proves that a uniformly recurrent sequence is either closed
    under reversal or has no reflected factor beyond some length.
  - **The orientation threshold of this entry is that length.** It is one more than the greatest length of a reflected
    factor.
  - **Finiteness is therefore not new.** The three substitutions are primitive, so their languages are uniformly
    recurrent, and none is closed under reversal (for the cubic substitution this is the compared `padovan_chirality` of
    PALOMAR-2026-08-19-000006). Theorem 11 then gives a finite threshold. This entry proves its exact value, 4, by a
    finite certificate.
  - **A published statement of the same kind** is their Proposition 57: no paperfolding sequence has a reflected factor
    of length greater than 13. It is proved by the same prefix argument and a finite examination of factors.
  - **Related results.** A uniformly recurrent word with infinitely many palindromes has a language closed under reversal
    (Balková, Pelantová and Starosta, RAIRO-ITA 44 (2010), Theorem 3.2), so each of the three languages has only finitely
    many palindromes. The palindrome complexity of a fixed point of a primitive substitution is bounded (Damanik and Zare,
    Discrete Math. 222 (2000); see Allouche, Baake, Cassaigne and Damanik, Theoret. Comput. Sci. 292 (2003), Theorem 7).
    The reversal-closed side, palindromic substitutions and Hof, Knill and Simon's class P (Comm. Math. Phys. 174 (1995)),
    is studied by Tan (2007), Labbé (2014), Labbé and Pelantová (2016) and Harju, Vesti and Zamboni (2016).
  - **For the plastic number, a stronger statement exists.** Gähler (arXiv:2602.18501, Example 10) shows that the tiling
    spaces of the cubic rule (his ϱ_R after renaming a ↔ c) and of its mirror are not reflection symmetric. That
    statement is about tiling spaces up to mutual local derivability.
  - **No published statement of the exact threshold was found.** We found none, nor of the longest reflected factor, for
    any of the three substitutions. This is a search result, not a guarantee.
- Prior formalizations.
  - **Libraries.** Mathlib has `List.Palindrome` and `List.IsInfix`, but no factor languages of substitutions. The
    Isabelle AFP entry `Combinatorics_Words` (Holub, Raška and Starosta) treats reversed morphisms, but not morphic factor
    languages. Starosta (arXiv:2303.11445) formalizes morphic languages in Isabelle/HOL; we found no reversal or
    palindrome results there.
  - **Nearest registered result by another author.** PALOMAR-2026-11-24-000006 proves, among other things, an invariance
    of the language of a five-letter morphic word under reversal combined with a letter swap.
  - **Statement 1 is not new to the registry's repositories.** It is public, kernel-checked and not compared in the
    registered repository of PALOMAR-2026-08-19-000006 (version 2, commit dff2591), both as
    `PdtFourTickThreshold.exact_orientation_threshold_four` and in a stronger form for every seed,
    `padovan_exact_orientation_threshold_four` in `Supplement.lean`. The same repository proves, again without comparing
    them, that the twelve-letter tensor's language is not closed under reversal (`rhoQ_chirality`) and gives its
    characteristic polynomial (`rhoQ_substitution_charpoly`). `FourTickCubic.lean` copies that repository's
    `PdtChirality.lean` and `PdtFourTickThreshold.lean`.
  - **What this entry compares for the first time.** Statement 1, plus the quartic and tensor statements 2–7. We found
    no public repository containing statements 2–7.
- Within the author's own registered entries: PALOMAR-2026-08-19-000006 compares `padovan_no_long_palindrome` (no factor
  of length at least four of the cubic language, from any seed, is a palindrome) and `padovan_chirality` (`ca` is a
  factor, `ac` is not). For the seed `a`, statement 1 is stronger than the first, because a palindrome is a word equal to
  its reversal: "no factor of length `≥ 4` has its reversal in the language" excludes long palindromes and also every pair
  `u ≠ u.reverse` of factors. The every-seed form of statement 1 is proved, not compared, in the same repository.

## What is not claimed

- Nothing about general substitutions. The compared statements concern three specific substitutions,
  and the threshold `4` is not a property of the incidence matrix alone. By direct computation (not
  formalized), the tensor matrix has `768` realizations that differ only in the order of letters
  inside the images. Their thresholds are 4 (344 of them), 5 (80), 6 (256), 7 (32), 8 (46), 10 (6),
  and none up to length 16 (4); all eight realizations built as tensor products give 4. Tensoring does not pass
  the threshold on automatically either: the cubic substitution tensored with the Fibonacci
  substitution gives 14, 6 or 5, depending on the ordering.
- For the cubic substitution the compared statement is for the seed `a` only. The every-seed form is
  proved, not compared, in the registered repository of PALOMAR-2026-08-19-000006
  (`padovan_exact_orientation_threshold_four` in `Supplement.lean`).
- Not formalized: the exact numbers of factors of each length (cubic 11, 15, 20 at lengths 3, 4, 5;
  quartic 22, 32, 42), the number of length-three palindromes, and the occurrence of every
  certificate word. All of these were computed by closing the factor sets under the substitution.
- The characteristic polynomials and inflation factors (see "The objects") are not proved here.

## Prior computation credited

This entry is the kernel form of earlier computations in the author's development record (findings
log, cited by line number):

- the tensor substitution's threshold, computed 2026-08-29 (F:323: "mirror-closure violation
  saturating at L = 4, the same threshold as the Padovan case", on a factor language stabilised by
  computation), put in the kernel 2026-11-25 (F:653);
- the quartic substitution's threshold, computed 2026-11-21 by exact factor-set closure (F:559),
  put in the kernel 2026-11-26;
- the cubic threshold, kernel-proved 2026-09-04 (F:370).

The library modules are copies of those kernel proofs (see "Files" and the `Provenance` paragraph of
each module).

## Companion entries

The registered entries of the same project on the Padovan substitution and the arrow of time are
PALOMAR-2026-08-19-000006 ([stalex444/arithmetic-of-time](https://github.com/stalex444/arithmetic-of-time)),
whose `padovan_no_long_palindrome` is the weaker no-palindrome half of statement 1, PALOMAR-2026-09-04-000004
([stalex444/chiral-padovan-histories](https://github.com/stalex444/chiral-padovan-histories)) and
PALOMAR-2026-10-18-000019
([stalex444/arithmetic-of-time-slowest-clock](https://github.com/stalex444/arithmetic-of-time-slowest-clock)).
No compared statement is shared with any of them. Statement 1 is, in the same form, a public but uncompared theorem of the
repository of PALOMAR-2026-08-19-000006 (`PdtFourTickThreshold.exact_orientation_threshold_four` at commit dff2591, with
an every-seed form in `Supplement.lean`), and `FourTickCubic.lean` is a copy of that repository's `PdtChirality.lean` and
`PdtFourTickThreshold.lean`.

## Scope

The compared statements are **mathematical statements only**: they concern three substitutions on
finite alphabets and their factor languages, and nothing else. **No physical identification is an
axiom, a hypothesis or a conclusion of any statement in this package.** The author reads the cubic
threshold physically, as the readout length of the arrow of time: four ticks of history always
suffice to read the orientation, while three can show nothing. That reading is hers. In her
development canon it is recorded as an identification (ratified identification 25, at the
identification tier, T4), not as a theorem, and it is not asserted here. The theorems stand
independently of it.

## Building

```
lake exe cache get
lake build
```

Toolchain `leanprover/lean4:v4.31.0`; Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (tag
`v4.31.0`). The build record, axiom audit and statement-identity checks are in `BUILD.txt`.

## Files

- `Challenge.lean`: the seven statements, Mathlib-only, as `sorry` placeholders, together with the
  definitions the entry adds (for each substitution: `Letter`, `s`, `S`, `InLanguage`, and for the
  quartic and the tensor substitution `InLanguageFrom`).
- `Solution.lean`: the same seven statements with identical docstrings, each proved from the library.
- `FourTickWords.lean`: the one list lemma the three window lemmas share (`infix_append_split`).
- `FourTickCubic.lean`, `FourTickQuartic.lean`, `FourTickTensor.lean`: the proof library, one module
  per substitution. Each holds the definitions of `Challenge.lean` character for character, the
  window lemma, the certificate and its kernel checks, completeness, the length-four exclusion, the
  length-three witness and (quartic, tensor) the seed-occurrence lemmas.
- `Axioms.lean`: `#print axioms` for the compared statements and the main library theorems.
- `comparator.json`, `BUILD.txt`, `SHA256SUMS`: the comparator configuration, the build record and
  the file hashes.

License: MIT. Author: Stephanie Alexander.
