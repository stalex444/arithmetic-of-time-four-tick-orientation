module
public import Mathlib

@[expose] public section
/-!
# The exact orientation threshold 4 of the cubic Padovan substitution, the quartic substitution and their twelve-letter tensor (inflation factor `ρQ`)

A substitution `s` sends each letter of a finite alphabet to a nonempty word; `S` applies it
letterwise to words, and the factor language from a seed letter `x` is the set of words that occur
as a contiguous block (`List.IsInfix`, written `<:+:`) of some iterate `S^[n] [x]`. Call a length
`L` *oriented* when no factor of length `L` has its reversal among the factors. Being oriented is
inherited by every longer length (the reversal of a long factor contains the reversal of its
length-`L` prefix), and fails at `L` as soon as some factor of length `L` is a palindrome. The
orientation threshold is the least oriented length. This entry proves that it is exactly `4` for
three substitutions: a palindrome of length three occurs, and every factor of length at least four
has a reversal that is not a factor. The entry compares exactly these seven statements.

The substitutions (each is defined below, in its own namespace):

* `Cubic.s`, the cubic Padovan substitution on `{a, b, c}`: `a ↦ b, b ↦ c, c ↦ ab` (incidence
  matrix with characteristic polynomial `x³ − x − 1`, inflation factor the plastic number `ρ`);
  seed `a`.
* `Quartic.s`, the quartic substitution on `{a, b, c, d}`: `a ↦ b, b ↦ c, c ↦ d, d ↦ ab`
  (characteristic polynomial `x⁴ − x − 1`, inflation factor its real root `Q > 1`); seed `a`.
* `Tensor.s`, their product on the twelve letters `{p, q, r} × {1, 2, 3, 4}` (`p, q, r` the cubic
  letters, `1, 2, 3, 4` the quartic ones): the letter `xi` goes to the word of pairs `yj`, `y`
  running through the cubic image of `x` and, inside it, `j` through the quartic image of `i`.
  Its incidence matrix is the Kronecker product, with characteristic polynomial
  `x¹² − 3x⁹ − 2x⁸ + 2x⁶ − x⁵ − 3x⁴ − x³ + x − 1`, the minimal polynomial of `ρQ`; seed `p1`.

The characteristic polynomials are named for orientation only; no statement uses them.

The compared statements:

1. `Cubic.exact_orientation_threshold_four` — some factor of length three from `a` is its own
   reversal (`a b a`), and every factor of length at least four has a reversal that is not a
   factor.
2. `Quartic.exact_orientation_threshold_four` — the same for the quartic substitution (`a b a`).
3. `Quartic.inLanguageFrom_iff` — the quartic factor language is the same from every seed letter.
4. `Quartic.exact_orientation_threshold_four_any_seed` — statement 2 from every seed `x`, with the
   reversal excluded from the factor language of every seed `y`.
5. `Tensor.exact_orientation_threshold_four` — the same as statement 1 for the tensor substitution
   (`q1 q2 q1`).
6. `Tensor.inLanguageFrom_iff` — the tensor factor language is the same from every seed letter.
7. `Tensor.exact_orientation_threshold_four_any_seed` — statement 5 from every seed `x`, with the
   reversal excluded from the factor language of every seed `y`.

Each statement is a statement about finite words and nothing else. The definitions below are the
only ones the entry adds, and the proof library repeats them character for character. Every
statement here is left unproved as a placeholder; `Solution.lean` proves each, with the identical
statement.
-/

namespace FourTickOrientation

/-! ## The cubic Padovan substitution -/

namespace Cubic

/-- The three-letter alphabet of the cubic Padovan substitution. -/
inductive Letter : Type
  | a | b | c
deriving DecidableEq

open Letter

/-- The cubic Padovan substitution `a ↦ b, b ↦ c, c ↦ ab`. Its incidence matrix has
characteristic polynomial `x³ − x − 1` (named for orientation; not used in any proof). -/
def s : Letter → List Letter
  | a => [b]
  | b => [c]
  | c => [a, b]

/-- `S` applies `s` letterwise to a word, concatenating the image blocks. -/
def S : List Letter → List Letter
  | [] => []
  | x :: w => s x ++ S w

/-- The factor language from the seed `a`: the words that occur as a contiguous block
(`<:+:`, `List.IsInfix`) of some iterate `S^[n] [a]`. -/
def InLanguage (u : List Letter) : Prop :=
  ∃ n : ℕ, u <:+: S^[n] [Letter.a]

/-- **1. Exact orientation threshold of the cubic Padovan substitution (seed `a`).** Some factor of
length three is its own reversal, and every factor of length at least four has a reversal that is
not a factor. -/
theorem exact_orientation_threshold_four :
    (∃ u : List Letter, InLanguage u ∧ u.length = 3 ∧ u.reverse = u) ∧
      (∀ u : List Letter, InLanguage u → 4 ≤ u.length → ¬ InLanguage u.reverse) := by
  sorry

end Cubic

/-! ## The quartic substitution -/

namespace Quartic

/-- The four-letter alphabet of the quartic substitution. -/
inductive Letter : Type
  | a | b | c | d
deriving DecidableEq

open Letter

/-- The quartic substitution `a ↦ b, b ↦ c, c ↦ d, d ↦ ab`. Its incidence matrix has
characteristic polynomial `x⁴ − x − 1` (named for orientation; not used in any proof). -/
def s : Letter → List Letter
  | a => [b]
  | b => [c]
  | c => [d]
  | d => [a, b]

/-- `S` applies `s` letterwise to a word, concatenating the image blocks. -/
def S : List Letter → List Letter
  | [] => []
  | x :: w => s x ++ S w

/-- The factor language from the seed `a`: the words that occur as a contiguous block
(`<:+:`, `List.IsInfix`) of some iterate `S^[n] [a]`. -/
def InLanguage (u : List Letter) : Prop :=
  ∃ n : ℕ, u <:+: S^[n] [Letter.a]

/-- The factor language from an arbitrary seed letter `x`. -/
def InLanguageFrom (x : Letter) (u : List Letter) : Prop :=
  ∃ n : ℕ, u <:+: S^[n] [x]

/-- **2. Exact orientation threshold of the quartic substitution (seed `a`).** Some factor of
length three is its own reversal, and every factor of length at least four has a reversal that is
not a factor. -/
theorem exact_orientation_threshold_four :
    (∃ u : List Letter, InLanguage u ∧ u.length = 3 ∧ u.reverse = u) ∧
      (∀ u : List Letter, InLanguage u → 4 ≤ u.length → ¬ InLanguage u.reverse) := by
  sorry

/-- **3. Seed independence of the quartic substitution's factor language.** The factor language
from any seed letter is the factor language from `a`. -/
theorem inLanguageFrom_iff (x : Letter) (u : List Letter) :
    InLanguageFrom x u ↔ InLanguage u := by
  sorry

/-- **4. Exact orientation threshold of the quartic substitution, every seed and across seeds.** For
any seed letters `x, y`: some factor of length three from `x` is its own reversal, and no factor
from `x` of length at least four has its reversal among the factors from `y`. -/
theorem exact_orientation_threshold_four_any_seed (x y : Letter) :
    (∃ u : List Letter, InLanguageFrom x u ∧ u.length = 3 ∧ u.reverse = u) ∧
      (∀ u : List Letter, InLanguageFrom x u → 4 ≤ u.length →
        ¬ InLanguageFrom y u.reverse) := by
  sorry

end Quartic

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

/-- **5. Exact orientation threshold of the tensor substitution (seed `p1`).** Some factor of
length three is its own reversal, and every factor of length at least four has a reversal that is
not a factor. -/
theorem exact_orientation_threshold_four :
    (∃ u : List Letter, InLanguage u ∧ u.length = 3 ∧ u.reverse = u) ∧
      (∀ u : List Letter, InLanguage u → 4 ≤ u.length → ¬ InLanguage u.reverse) := by
  sorry

/-- **6. Seed independence of the tensor substitution's factor language.** The factor language
from any seed letter is the factor language from `p1`. -/
theorem inLanguageFrom_iff (x : Letter) (u : List Letter) :
    InLanguageFrom x u ↔ InLanguage u := by
  sorry

/-- **7. Exact orientation threshold of the tensor substitution, every seed and across seeds.** For
any seed letters `x, y`: some factor of length three from `x` is its own reversal, and no factor
from `x` of length at least four has its reversal among the factors from `y`. -/
theorem exact_orientation_threshold_four_any_seed (x y : Letter) :
    (∃ u : List Letter, InLanguageFrom x u ∧ u.length = 3 ∧ u.reverse = u) ∧
      (∀ u : List Letter, InLanguageFrom x u → 4 ≤ u.length →
        ¬ InLanguageFrom y u.reverse) := by
  sorry

end Tensor

end FourTickOrientation
