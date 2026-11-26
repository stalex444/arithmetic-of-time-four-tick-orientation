# The orientation threshold 4 for the substitutions of `xⁿ − x − 1`, `n ≥ 3`, and the twelve-letter `ρQ` tensor

Kernel-checked, in Lean 4 + Mathlib. A substitution sends each letter of a finite alphabet to a
nonempty word; its factor language from a seed letter is the set of words that occur as a
contiguous block of some iterate. Call a length `L` *oriented* when no factor of length `L` has its
reversal among the factors. Being oriented passes to every longer length (the reversal of a long
factor contains the reversal of its length-`L` prefix), and it fails at `L` whenever some factor of
length `L` is a palindrome. The *orientation threshold* is the least oriented length; in the terms
of Allouche, Campbell, Li, Shallit and Stipulanti (see the literature section) it is one more than
the greatest length of a *reflected* factor, a factor whose reversal is also a factor.

The lead theorem is a statement about an infinite family. For every `n ≥ 3`, the substitution
`σₙ : i ↦ i+1 (1 ≤ i < n), n ↦ 1 2`, whose incidence matrix has characteristic polynomial
`xⁿ − x − 1`, has orientation threshold exactly `4`: a palindrome of length three occurs, and every
factor of length at least four has a reversal that is not a factor. One proof covers every `n`: the
certificate is a set of index rules, checked by `omega` on index arithmetic, not an enumeration of
words. The factor language of `σₙ` is the same from every seed letter. The case `n = 3` is the
cubic Padovan substitution and `n = 4` the quartic substitution of `x⁴ − x − 1`. The entry proves
the same threshold, from every seed and across seeds, for one further substitution: the
twelve-letter tensor product of those two, whose inflation factor is the product `ρQ` of their real
roots `ρ > 1` and `Q > 1`. The tensor is not a member of the family.

## The objects

- **The family `σₙ`, `n ≥ 3`**, on the letters `1, …, n`, encoded as natural numbers:
  `i ↦ i+1` for `1 ≤ i < n`, and `n ↦ 1 2`. Its incidence matrix has characteristic polynomial
  `xⁿ − x − 1`. Seed `1`.
  - `n = 3` is the **cubic Padovan substitution** `a ↦ b, b ↦ c, c ↦ ab` (letters `a, b, c` =
    `1, 2, 3`); inflation factor the plastic number `ρ = 1.3247…`.
  - `n = 4` is the **quartic substitution** `a ↦ b, b ↦ c, c ↦ d, d ↦ ab` (letters `a, b, c, d` =
    `1, 2, 3, 4`); inflation factor the real root `Q = 1.2207…` of `x⁴ − x − 1` greater than one.
  - In Lean, `Family.s n x = if x < n then [x + 1] else [1, 2]`, a function on all of `ℕ`. It also
    sends `0 ↦ 1` and every `x > n` to `1 2`, but the iterates of the seeds `1, …, n` contain only
    the letters `1, …, n`, so these values play no part in the statements.
  - `n = 2` (`a ↦ b, b ↦ ab`, a Fibonacci substitution) is excluded: its language is Sturmian and
    closed under reversal (a classical property of Sturmian words; not formalized here), so it has no finite threshold.
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
- `S` applies a substitution letterwise to words. `InLanguage u` means `∃ k, u <:+: S^[k] [seed]`,
  where `<:+:` is Mathlib's `List.IsInfix` (contiguous sub-block). `InLanguageFrom x u` is the same
  with seed `x`. For the family both carry the parameter `n`: `Family.InLanguage n u`,
  `Family.InLanguageFrom n x u`.

The characteristic polynomials and inflation factors are given so the reader can place the
substitutions. No compared statement uses them, and they are not proved in the package; the tensor
values were checked by direct computation.

## The compared statements (namespace `FourTickOrientation`)

`THR(P)` abbreviates
`(∃ u, P u ∧ u.length = 3 ∧ u.reverse = u) ∧ (∀ u, P u → 4 ≤ u.length → ¬ P u.reverse)`.

| # | name | statement |
|---|------|-----------|
| 1 | `Family.exact_orientation_threshold_four` | `∀ n, 3 ≤ n → THR(Family.InLanguage n)`. The palindrome is `1 2 1`, reached from `[1]` by a chain of iterates (`3n − 1` applications of `σₙ` in all) |
| 2 | `Family.inLanguageFrom_iff` | `∀ n x, 1 ≤ x → x ≤ n → ∀ u, Family.InLanguageFrom n x u ↔ Family.InLanguage n u`: the factor language of `σₙ` does not depend on the seed letter |
| 3 | `Tensor.exact_orientation_threshold_four` | `THR(Tensor.InLanguage)`, seed `p1`. The palindrome is `q1 q2 q1`, at positions 15–17 of the 28-letter word `S^[8] [p1]` |
| 4 | `Tensor.inLanguageFrom_iff` | `∀ x u, Tensor.InLanguageFrom x u ↔ Tensor.InLanguage u`: the tensor factor language does not depend on the seed |
| 5 | `Tensor.exact_orientation_threshold_four_any_seed` | for all seeds `x, y`: `(∃ u, InLanguageFrom x u ∧ u.length = 3 ∧ u.reverse = u) ∧ (∀ u, InLanguageFrom x u → 4 ≤ u.length → ¬ InLanguageFrom y u.reverse)` |

Verbatim, from `Challenge.lean`:

```lean
theorem Family.exact_orientation_threshold_four (n : ℕ) (hn : 3 ≤ n) :
    (∃ u : List ℕ, InLanguage n u ∧ u.length = 3 ∧ u.reverse = u) ∧
      (∀ u : List ℕ, InLanguage n u → 4 ≤ u.length → ¬ InLanguage n u.reverse)

theorem Family.inLanguageFrom_iff (n x : ℕ) (hx1 : 1 ≤ x) (hxn : x ≤ n)
    (u : List ℕ) : InLanguageFrom n x u ↔ InLanguage n u
```

(each stated inside `namespace Family`; the three tensor statements inside `namespace Tensor`).

Every compared theorem depends on no axiom outside `propext`, `Classical.choice` and `Quot.sound`
(the two `inLanguageFrom_iff` statements use only `propext` and `Quot.sound`). No `native_decide`
is used anywhere in the package: the family proof uses `omega` and `simp`, and every finite check of
the tensor proof is `decide` or `decide +kernel`.

## The proof

**The family (statements 1, 2), uniformly in `n ≥ 3`.**

1. **Prefixes of images.** Every image block is nonempty, so the first `k` letters of `S n xs`
   depend only on the first `j ≥ k` letters of `xs` (`take_S`).
2. **A parametric certificate.** `Cert n` is an explicit predicate on words of length `≤ 4`, given
   by index rules: every letter lies in `1, …, n`; `1` is always followed by `2`; the third letter is
   the cyclic successor of the second unless the first two form an up-step `a, a+1`; and a rule
   `P4` for the fourth letter after an up-step. It is used only as an upper bound on the factor set.
   `G n w` says that the length-`≤ 4` prefix of every suffix of `w` is certified. `G n [1]` holds and
   `G` is preserved by `S n` (`G_S`): by `take_S` the step reduces to a finite symbolic case
   analysis on the shape of a word of length `≤ 4` (`closure`), each case closed by `omega` on the
   letter indices. So every length-four factor of every iterate is certified (`factors_complete`).
3. **Length four.** No certified length-four word has a certified reversal (`cert_reverse`, a second
   `omega` case analysis). If `u` is a factor with `|u| ≥ 4` and `t` is its length-four prefix, then
   `t.reverse` is a factor of `u.reverse`, so `u.reverse` is not a factor
   (`reversal_forbidden_of_four_le`).
4. **Length three.** Below the top letter `S n` is the shift `i ↦ i+1` (`iterate_shift`). The chain
   `[1] ↦ⁿ⁻¹ [n] ↦ [1, 2] ↦ⁿ⁻² [n−1, n] ↦ [n, 1, 2] ↦ [1, 2, 2, 3]`, then the factor `[2, 2]`
   `↦ⁿ⁻² [n, n] ↦ [1, 2, 1, 2]`, shows that `1 2 1` is a factor (`inLanguage_one_two_one`).
5. **Seeds.** `(S n)^[x−1] [1] = [x]`, and `(S n)^[n−x] [x] = [n]`, whose image `1 2` contains `1`.
   Since `S n` maps factors to factors, the languages from `x` and from `1` coincide (statement 2).

**The tensor (statements 3–5).**

1. **Window lemma.** Every image block is nonempty, so a factor of `S w` of length `≤ L` lies inside
   the image of a factor of `w` of length `≤ L` (`infix_window`).
2. **A finite certificate.** 456 words of length `≤ 4` (1 + 12 + 79 + 148 + 216 by length), packed
   into a bit mask indexed by a base-13 word code. It contains the seed and is closed under taking
   short windows of images; by induction on `k` it contains every short factor of every iterate
   (`factors_complete`). It is used only as an upper bound on the factor set. Both kernel checks
   run by `decide +kernel` over every word of length `≤ 4` (22,621 words).
3. **Length four.** As for the family: no length-four certificate word has its reversal in the
   certificate (`rev_check`), and factor closure gives every longer length.
4. **Length three.** The eighth iterate from `p1`, evaluated by `decide`, contains `q1 q2 q1`.
5. **Seeds.** Every letter occurs in an iterate of `p1` and `p1` occurs in an iterate of every
   letter (explicit iterates, by `decide`), so the languages coincide (statement 4). Statement 5
   transports statement 3 along statement 4.

## Relation to the literature

- The cubic Padovan substitution is a standard example of a Pisot substitution (its inflation factor
  `ρ` is the smallest Pisot number). The quartic member is not a Pisot substitution: besides `Q`,
  `x⁴ − x − 1` has a complex pair of roots of modulus `1.0633…`. (By the same numerical check, none of
  `n = 4, …, 8` gives a Pisot number.) So the threshold `4` is not tied to the Pisot property.
  Palindromes in fixed points of substitutions are a long-studied topic: palindromic complexity, and
  the conditions under which a language is closed under reversal.
- Literature and prior-formalization search, done 2026-11-26. Sources: the arXiv API with full texts of the papers cited
  here; Crossref; the Palomar registry search API; Mathlib master; the Isabelle AFP; web search.
  - **The general fact behind the threshold is published.** Allouche, Campbell, Li, Shallit and Stipulanti (Theory
    Comput. Syst. 69 (2025), article 31, DOI 10.1007/s00224-025-10234-x; arXiv:2406.09302) call a factor *reflected*
    when its reversal is also a factor. Their Theorem 11 proves that a uniformly recurrent sequence is either closed
    under reversal or has no reflected factor beyond some length.
  - **The orientation threshold of this entry is that length.** It is one more than the greatest length of a reflected
    factor.
  - **Finiteness is therefore not new.** Each `σₙ` (`n ≥ 3`) and the tensor substitution are primitive (standard: the incidence matrix of
    `σₙ` is a primitive Wielandt matrix; for the tensor, its 10th power is positive by computation; not formalized), so their
    languages are uniformly recurrent, and none is closed under reversal (this follows from statements 1 and 3, since the
    iterates have factors of length four; for the cubic substitution it is also the compared `padovan_chirality` of
    PALOMAR-2026-08-19-000006). Theorem 11 then gives a
    finite threshold for each substitution separately. This entry proves its exact value, `4`, for every `n ≥ 3` at
    once, and for the tensor.
  - **A published statement of the same kind** is their Proposition 57: no paperfolding sequence has a reflected factor
    of length greater than 13. It is proved by the same prefix argument and a finite examination of factors.
  - **Related results.** A uniformly recurrent word with infinitely many palindromes has a language closed under reversal
    (Balková, Pelantová and Starosta, RAIRO-ITA 44 (2010), Theorem 3.2), so each of these languages has only finitely
    many palindromes. The palindrome complexity of a fixed point of a primitive substitution is bounded (Damanik and Zare,
    Discrete Math. 222 (2000); see Allouche, Baake, Cassaigne and Damanik, Theoret. Comput. Sci. 292 (2003), Theorem 7).
    The reversal-closed side, palindromic substitutions and Hof, Knill and Simon's class P (Comm. Math. Phys. 174 (1995)),
    is studied by Tan (2007), Labbé (2014), Labbé and Pelantová (2016) and Harju, Vesti and Zamboni (2016).
  - **For the plastic number, a stronger statement exists.** Gähler (arXiv:2602.18501, Example 10) shows that the tiling
    spaces of the cubic rule (his ϱ_R after renaming a ↔ c) and of its mirror are not reflection symmetric. That
    statement is about tiling spaces up to mutual local derivability.
  - **No published statement of the exact threshold was found.** The search found none, nor of the longest reflected
    factor, for the cubic, the quartic or the tensor substitution, which it searched by name and by rule. This entry proves the exact value `4` for every `n ≥ 3`; the case `n = 3`
    was already public in the author's repository of PALOMAR-2026-08-19-000006 (see below). No published statement of
    the value for the family was found (see the next bullet). This is a search result, not a guarantee.
- **The family was also searched as a standalone question (2026-11-26).** Sources: web search under the names the
  family and its members carry (the xⁿ − x − 1 substitutions, Padovan, Perrin and smallest-Pisot substitutions); the
  full texts of the reflection-complexity papers that follow Allouche et al. (Dvořáková and Pelantová, Theory Comput.
  Syst. 70 (2026), article 35; Blažek, Dvořáková and Pelantová, arXiv:2610.14637); Shallit's 2025–2026 Walnut papers;
  OEIS; and every result in the Palomar registry. No statement of the exact value, of the longest reflected factor, or
  of the non-closure under reversal was found for any `σₙ` with `n ≥ 4`. This is a search result, not a guarantee.
  - **The nearest published results.** Allouche et al.'s Proposition 57 (above) is a bound of the same kind over an
    infinite family of sequences. For the sister trinomials `x^k − x^{k−1} − 1` (the Narayana-type substitutions
    `0 → 01`, `i → i+1`, `k−1 → 0`), non-closure under reversal for every `k ≥ 3` follows from the reversal criterion
    for simple Parry numbers (Frougny, Masáková and Pelantová, RAIRO-ITA 38 (2004) 163–185; restated in Ambrož,
    Frougny, Masáková and Pelantová, Ann. Inst. Fourier 56 (2006) 2131–2160, Proposition 3.2). For `k = 3`, Shallit
    (arXiv:2503.01026, Proposition 15) lists all of its palindromes. None of these concerns `xⁿ − x − 1`.
  - **The value is not specific to this family.** By our computation, which is not part of this entry, the
    Narayana-type substitutions also have longest reflected factor 3 for `k = 3, …, 10`.
- Prior formalizations.
  - **Libraries.** Mathlib has `List.Palindrome` and `List.IsInfix`, but no factor languages of substitutions. The
    Isabelle AFP entry `Combinatorics_Words` (Holub, Raška and Starosta) treats reversed morphisms, but not morphic factor
    languages. Starosta (arXiv:2303.11445) formalizes morphic languages in Isabelle/HOL; we found no reversal or
    palindrome results there.
  - **Nearest registered result by another author.** PALOMAR-2026-11-24-000006 proves, among other things, an invariance
    of the language of a five-letter morphic word under reversal combined with a letter swap.
  - **The case `n = 3` of statement 1 is not new to the registry's repositories.** For the seed `a` it is public,
    kernel-checked and not compared in the registered repository of PALOMAR-2026-08-19-000006 (version 2, commit
    dff2591), as `PDT.Padovan.exact_orientation_threshold_four` (in `PdtFourTickThreshold.lean`) (letters `a, b, c` instead of `1, 2, 3`), and
    in a stronger form for every seed, `padovan_exact_orientation_threshold_four` in `Supplement.lean`. The same
    repository proves, again without comparing them, that the twelve-letter tensor's language is not closed under
    reversal (`rhoQ_chirality`) and gives its characteristic polynomial (`rhoQ_substitution_charpoly`). Of this package, the list lemma `infix_append_split`
    (`FourTickWords.lean`) comes from that repository's `PdtChirality.lean`, and the tensor definitions `Letter`, `s`,
    `S` with the lemmas `S_nil` and `S_cons` (`FourTickTensor.lean`) come from its `PdtRhoQChirality.lean`. The rest of
    `FourTickTensor.lean` and all of `FourTickFamily.lean` come from later files that are not in that repository.
  - **What this entry compares for the first time.** Statements 1–5. Apart from the case `n = 3`, the search found no
    public repository containing any of them. It looked for the quartic case and the tensor statements; the family
    theorem was proved after the search.
- Within the author's own registered entries: PALOMAR-2026-08-19-000006 compares `padovan_no_long_palindrome` (no factor
  of length at least four of the cubic language, from any seed, is a palindrome) and `padovan_chirality` (`ca` is a
  factor, `ac` is not). Statements 1 and 2 at `n = 3` imply the first, up to the renaming of the letters, because a
  palindrome is a word equal to its reversal: "no factor of length `≥ 4` has its reversal in the language" excludes long
  palindromes and also every pair `u ≠ u.reverse` of factors.

## What is not claimed

- Nothing about general substitutions. The compared statements concern the family `σₙ` and one
  further substitution, and the threshold `4` is not a property of the incidence matrix alone. By
  direct computation (not formalized), the tensor matrix has `768` realizations that differ only in
  the order of letters inside the images. Their thresholds are 4 (344 of them), 5 (80), 6 (256),
  7 (32), 8 (46), 10 (6), and none up to length 16 (4); all eight realizations built as tensor
  products give 4. Tensoring does not pass the threshold on automatically either: the cubic
  substitution tensored with the Fibonacci substitution gives 14, 6 or 5, depending on the ordering.
- Statement 1 is for `n ≥ 3`; `n = 2` has no finite threshold (see "The objects").
- Statement 2 is stated for the letters `1 ≤ x ≤ n`. The cross-seed form of statement 1 for the
  family (the form of statement 5) is not a separate compared statement; it follows from statements
  1 and 2 in the way statement 5 follows from statements 3 and 4.
- Not formalized, computed by exact closure of the factor sets under the substitution:
  - for the family, the numbers of factors of lengths 2, 3, 4, which are `n² − n + 1`,
    `2n² − 3n + 2` and `3n² − 4n`;
  - the exactness of the index-rule certificate, which equals the factor set at lengths 1–4 (the
    kernel proof uses it only as an upper bound);
  - both checked for `n = 3, …, 40`. Also computed, for `n = 3, …, 20`: the reflected factors of
    length three are exactly the `2n − 2` palindromes of length three;
  - for the tensor, the factor counts per length and the occurrence of every certificate word.
- The characteristic polynomials and inflation factors (see "The objects") are not proved here.

## Prior computation credited

The cubic, quartic and tensor statements are the kernel form of earlier computations in the author's development
record (findings log, cited by line number). The family theorem goes further: the computations covered `n = 3, …, 40`
at most, and the statement for every `n ≥ 3` was recorded as open until this proof (F:655):

- the family: threshold 4 computed for `n = 3, …, 9` on 2026-10-18 (F:387, which also gives a
  two-line paper proof that every `σₙ`, `n ≥ 3`, is not closed under reversal), for `n = 3, …, 20` by exact factor-set closure on 2026-11-26,
  the index-rule certificate checked against the exact factor sets for `n = 3, …, 40`, and the
  theorem for every `n ≥ 3` proved in the kernel on 2026-11-26 (F:655);
- its first two members, earlier and separately: the cubic threshold, kernel-proved 2026-09-04
  (F:370); the quartic threshold, computed 2026-11-21 by exact factor-set closure (F:559) and put in
  the kernel 2026-11-26 (F:654). The family proof replaces both;
- the tensor substitution's threshold, computed 2026-08-29 (F:323: "mirror-closure violation
  saturating at L = 4, the same threshold as the Padovan case", on a factor language stabilised by
  computation), put in the kernel 2026-11-25 (F:653).

The library modules are copies of those kernel proofs (see "Files" and the `Provenance` paragraph of
each module).

## Companion entries

The registered entries of the same project on the Padovan substitution and the arrow of time are
PALOMAR-2026-08-19-000006 ([stalex444/arithmetic-of-time](https://github.com/stalex444/arithmetic-of-time)),
whose `padovan_no_long_palindrome` follows from the case `n = 3` of statements 1 and 2, PALOMAR-2026-09-04-000004
([stalex444/chiral-padovan-histories](https://github.com/stalex444/chiral-padovan-histories)) and
PALOMAR-2026-10-18-000019
([stalex444/arithmetic-of-time-slowest-clock](https://github.com/stalex444/arithmetic-of-time-slowest-clock)).
No compared statement is shared with any of them. The case `n = 3` of statement 1 (from the seed `a`) is, with the
letters `a, b, c`, a public but uncompared theorem of the repository of PALOMAR-2026-08-19-000006
(`PDT.Padovan.exact_orientation_threshold_four` (in `PdtFourTickThreshold.lean`) at commit dff2591, with an every-seed form in
`Supplement.lean`).

## Version history

- Version 1 (commit `b01b4fb`, 2026-11-26) compared seven statements: the orientation threshold of the cubic
  substitution (seed `a`), of the quartic substitution and of the twelve-letter tensor; for the quartic and the
  tensor, seed independence of the factor language and the every-seed, cross-seed form of the threshold.
- Version 2 (this version) replaces the separate cubic and quartic statements by the family theorem for every
  `n ≥ 3`, of which they are the cases `n = 3` and `n = 4`, and keeps the tensor statements. Version 1 remains in
  the repository history.

## Scope

The compared statements are **mathematical statements only**: they concern substitutions on finite
alphabets and their factor languages, and nothing else. **No physical identification is an axiom, a
hypothesis or a conclusion of any statement in this package.** The author reads the cubic threshold
physically, as the readout length of the arrow of time: four ticks of history always suffice to read
the orientation, while three can show nothing. That reading is hers. In her development canon it is
recorded as an identification (ratified identification 25, at the identification tier, T4), not as
a theorem, and it is not asserted here. The theorems stand independently of it.

## Building

```
lake exe cache get
lake build
```

Toolchain `leanprover/lean4:v4.35.0-rc2`; Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The build
record, axiom audit and statement-identity checks are in `BUILD.txt`.

## Files

- `Challenge.lean`: the five statements, Mathlib-only, as `sorry` placeholders, together with the
  definitions the entry adds (for the family: `s`, `S`, `InLanguage`, `InLanguageFrom`; for the
  tensor substitution: `Letter`, `s`, `S`, `InLanguage`, `InLanguageFrom`).
- `Solution.lean`: the same five statements with identical docstrings, each proved from the library.
- `FourTickFamily.lean`: the proof library for statements 1–2. It holds the family definitions of
  `Challenge.lean` character for character, `take_S`, the parametric certificate and its closure,
  completeness at length four, the length-four exclusion, the length-three witness and the shift
  lemma used for the seeds.
- `FourTickTensor.lean`: the proof library for statements 3–5, with the tensor definitions of
  `Challenge.lean` character for character: the window lemma, the certificate and its kernel checks,
  completeness, the length-four exclusion, the length-three witness and the seed-occurrence lemmas.
- `FourTickWords.lean`: the one list lemma of the tensor window lemma (`infix_append_split`).
- `Axioms.lean`: `#print axioms` for the compared statements and the main library theorems.
- `comparator.json`, `BUILD.txt`, `SHA256SUMS`: the comparator configuration, the build record and
  the file hashes.

License: MIT. Author: Stephanie Alexander.
