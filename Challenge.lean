module
public import Mathlib

@[expose] public section
/-!
# The orientation threshold 4 for the substitutions of `xⁿ − x − 1`, `n ≥ 3`, and the twelve-letter `ρQ` tensor

A substitution sends each letter to a nonempty word; `S` applies it letterwise to words, and the
factor language from a seed letter `x` is the set of words that occur as a contiguous block
(`List.IsInfix`, written `<:+:`) of some iterate `S^[k] [x]`. Call a length `L` *oriented* when no
factor of length `L` has its reversal among the factors. Being oriented is inherited by every longer
length (the reversal of a long factor contains the reversal of its length-`L` prefix), and fails at
`L` as soon as some factor of length `L` is a palindrome. The orientation threshold is the least
oriented length. This entry proves that it is exactly `4` for every substitution of an infinite
family and for one further substitution: a palindrome of length three occurs, and every factor of
length at least four has a reversal that is not a factor. The entry compares exactly these five
statements.

The substitutions (each is defined below, in its own namespace):

* `Family.s n`, for every `n ≥ 3`, the substitution `σₙ` on the letters `1, …, n` (natural
  numbers): `i ↦ i+1` for `i < n`, `n ↦ 1 2`. Its incidence matrix has characteristic polynomial
  `xⁿ − x − 1`. `n = 3` is the cubic Padovan substitution `a ↦ b, b ↦ c, c ↦ ab` (inflation factor
  the plastic number `ρ`), `n = 4` the quartic substitution `a ↦ b, b ↦ c, c ↦ d, d ↦ ab`
  (inflation factor the real root `Q > 1` of `x⁴ − x − 1`). Seed `1`.
* `Tensor.s`, the product of the cubic and the quartic substitution on the twelve letters
  `{p, q, r} × {1, 2, 3, 4}` (`p, q, r` the cubic letters, `1, 2, 3, 4` the quartic ones): the letter
  `xi` goes to the word of pairs `yj`, `y` running through the cubic image of `x` and, inside it, `j`
  through the quartic image of `i`. Its incidence matrix is the Kronecker product, with
  characteristic polynomial `x¹² − 3x⁹ − 2x⁸ + 2x⁶ − x⁵ − 3x⁴ − x³ + x − 1`, the minimal polynomial
  of `ρQ`; seed `p1`. It is not a member of the family.

The characteristic polynomials are named for orientation only; no statement uses them.

The compared statements:

1. `Family.exact_orientation_threshold_four` — for every `n ≥ 3`: some factor of length three from
   `1` is its own reversal (`1 2 1`), and every factor of length at least four has a reversal that
   is not a factor.
2. `Family.inLanguageFrom_iff` — for every `n` and every letter `1 ≤ x ≤ n`, the factor language
   from `x` is the factor language from `1`.
3. `Tensor.exact_orientation_threshold_four` — the same as statement 1 for the tensor substitution,
   seed `p1` (`q1 q2 q1`).
4. `Tensor.inLanguageFrom_iff` — the tensor factor language is the same from every seed letter.
5. `Tensor.exact_orientation_threshold_four_any_seed` — statement 3 from every seed `x`, with the
   reversal excluded from the factor language of every seed `y`.

Each statement is a statement about finite words and nothing else. The definitions below are the
only ones the entry adds, and the proof library repeats them character for character. Every
statement here is left unproved as a placeholder; `Solution.lean` proves each, with the identical
statement.
-/

namespace FourTickOrientation

/-! ## The family `σₙ`, `n ≥ 3` (characteristic polynomial `xⁿ − x − 1`) -/

namespace Family

/-- The substitution `σₙ` of the family, on the letters `1, …, n` (encoded as natural numbers):
`i ↦ i+1` for `i < n`, and `n ↦ 1 2`. Its incidence matrix on the letters `1, …, n` has
characteristic polynomial `xⁿ − x − 1` (named for orientation; not used in any proof). For `n = 3`
it is the cubic Padovan substitution `a ↦ b, b ↦ c, c ↦ ab`, for `n = 4` the quartic substitution
`a ↦ b, b ↦ c, c ↦ d, d ↦ ab` (letters `a, b, c, d` = `1, 2, 3, 4`). As a function on `ℕ` it also
sends `0 ↦ 1` and every `x > n` to `1 2`; the iterates of the seeds `1, …, n` contain only the
letters `1, …, n`. -/
def s (n x : ℕ) : List ℕ := if x < n then [x + 1] else [1, 2]

/-- `S n` applies `s n` letterwise to a word, concatenating the image blocks. -/
def S (n : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: w => s n x ++ S n w

/-- The factor language of `σₙ` from the seed `1`: the words that occur as a contiguous block
(`<:+:`, `List.IsInfix`) of some iterate `(S n)^[k] [1]`. -/
def InLanguage (n : ℕ) (u : List ℕ) : Prop :=
  ∃ k : ℕ, u <:+: (S n)^[k] [1]

/-- The factor language of `σₙ` from the seed letter `x`. -/
def InLanguageFrom (n x : ℕ) (u : List ℕ) : Prop :=
  ∃ k : ℕ, u <:+: (S n)^[k] [x]

/-- **1. Exact orientation threshold 4 for every member of the family (`n ≥ 3`, seed `1`).** For the
substitution `σₙ` (characteristic polynomial `xⁿ − x − 1`), some factor of length three is its own
reversal (`1 2 1`), and every factor of length at least four has a reversal that is not a factor. -/
theorem exact_orientation_threshold_four (n : ℕ) (hn : 3 ≤ n) :
    (∃ u : List ℕ, InLanguage n u ∧ u.length = 3 ∧ u.reverse = u) ∧
      (∀ u : List ℕ, InLanguage n u → 4 ≤ u.length → ¬ InLanguage n u.reverse) := by
  sorry

/-- **2. Seed independence of the family's factor languages.** For every letter `1 ≤ x ≤ n`, the
factor language of `σₙ` from the seed `x` is the factor language from `1`. -/
theorem inLanguageFrom_iff (n x : ℕ) (hx1 : 1 ≤ x) (hxn : x ≤ n)
    (u : List ℕ) : InLanguageFrom n x u ↔ InLanguage n u := by
  sorry

end Family

/-! ## The twelve-letter tensor substitution -/

namespace Tensor

/-- The twelve-letter product alphabet `{p, q, r} × {1, 2, 3, 4}`. -/
inductive Letter : Type
  | p1 | p2 | p3 | p4
  | q1 | q2 | q3 | q4
  | r1 | r2 | r3 | r4
deriving DecidableEq

open Letter

/-- The tensor substitution on `{p, q, r} × {1, 2, 3, 4}`: writing `p, q, r` for the cubic letters
`a, b, c` and `1, 2, 3, 4` for the quartic letters `a, b, c, d`, the letter `xi` goes to the word of
the pairs `yj` with `y` running through the cubic image of `x` (outer) and `j` through the quartic
image of `i` (inner). Its incidence matrix is the Kronecker product of the two incidence matrices,
with characteristic polynomial `x¹² − 3x⁹ − 2x⁸ + 2x⁶ − x⁵ − 3x⁴ − x³ + x − 1`, the minimal
polynomial of `ρQ` (named for orientation; not used in any proof). -/
def s : Letter → List Letter
  | p1 => [q2]        | q1 => [r2]        | r1 => [p2, q2]
  | p2 => [q3]        | q2 => [r3]        | r2 => [p3, q3]
  | p3 => [q4]        | q3 => [r4]        | r3 => [p4, q4]
  | p4 => [q1, q2]    | q4 => [r1, r2]    | r4 => [p1, p2, q1, q2]

/-- `S` applies `s` letterwise to a word, concatenating the image blocks. -/
def S : List Letter → List Letter
  | [] => []
  | x :: w => s x ++ S w

/-- The factor language from the seed `p1`: the words that occur as a contiguous block
(`<:+:`, `List.IsInfix`) of some iterate `S^[n] [p1]`. -/
def InLanguage (u : List Letter) : Prop :=
  ∃ n : ℕ, u <:+: S^[n] [Letter.p1]

/-- The factor language from an arbitrary seed letter `x`. -/
def InLanguageFrom (x : Letter) (u : List Letter) : Prop :=
  ∃ n : ℕ, u <:+: S^[n] [x]

/-- **3. Exact orientation threshold of the tensor substitution (seed `p1`).** Some factor of
length three is its own reversal, and every factor of length at least four has a reversal that is
not a factor. -/
theorem exact_orientation_threshold_four :
    (∃ u : List Letter, InLanguage u ∧ u.length = 3 ∧ u.reverse = u) ∧
      (∀ u : List Letter, InLanguage u → 4 ≤ u.length → ¬ InLanguage u.reverse) := by
  sorry

/-- **4. Seed independence of the tensor substitution's factor language.** The factor language
from any seed letter is the factor language from `p1`. -/
theorem inLanguageFrom_iff (x : Letter) (u : List Letter) :
    InLanguageFrom x u ↔ InLanguage u := by
  sorry

/-- **5. Exact orientation threshold of the tensor substitution, every seed and across seeds.** For
any seed letters `x, y`: some factor of length three from `x` is its own reversal, and no factor
from `x` of length at least four has its reversal among the factors from `y`. -/
theorem exact_orientation_threshold_four_any_seed (x y : Letter) :
    (∃ u : List Letter, InLanguageFrom x u ∧ u.length = 3 ∧ u.reverse = u) ∧
      (∀ u : List Letter, InLanguageFrom x u → 4 ≤ u.length →
        ¬ InLanguageFrom y u.reverse) := by
  sorry

end Tensor

end FourTickOrientation
