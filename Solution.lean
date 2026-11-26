module
public import Mathlib
public import FourTickWords
public import FourTickFamily
public import FourTickTensor

@[expose] public section
/-!
# The orientation threshold 4: proofs of the compared statements

Each of the five statements of `Challenge.lean` is proved here, with the identical statement and
docstring. The definitions of `Challenge.lean` (`s`, `S`, `InLanguage`, `InLanguageFrom` for the
family and, for the tensor substitution, also `Letter`) are those of the proof library, character for
character: `FourTickFamily.lean` and `FourTickTensor.lean`, with the one list lemma of the tensor
window lemma in `FourTickWords.lean`.

* Statement 1: `length_three_orientation_ambiguity` (the factor `1 2 1`, by an explicit chain of
  iterates, for every `n ≥ 3`) and `reversal_forbidden_of_four_le` (the parametric certificate at
  length four, propagated to every longer length by factor closure) of `FourTickFamily`.
* Statement 2: `iterate_shift` (from `1`, the iterates `(S n)^[x-1] [1] = [x]`, and from `x`,
  `(S n)^[n-x] [x] = [n]`, whose image `1 2` contains `1`) and `S_infix`; the proof is the source's,
  with its local lemma `iterate_infix_aux`.
* Statement 3: `length_three_orientation_ambiguity` (an explicit iterate, by `decide`, contains the
  palindrome) and `reversal_forbidden_of_four_le` (the finite certificate at length four) of
  `FourTickTensor`.
* Statement 4: `language_mono` in both directions, with `letter_in_p1_iterate` /
  `p1_in_letter_iterate`.
* Statement 5: statement 3 transported along statement 4.
-/

namespace FourTickOrientation

/-! ## The family `σₙ`, `n ≥ 3` (characteristic polynomial `xⁿ − x − 1`) -/

namespace Family

/-- **1. Exact orientation threshold 4 for every member of the family (`n ≥ 3`, seed `1`).** For the
substitution `σₙ` (characteristic polynomial `xⁿ − x − 1`), some factor of length three is its own
reversal (`1 2 1`), and every factor of length at least four has a reversal that is not a factor. -/
theorem exact_orientation_threshold_four (n : ℕ) (hn : 3 ≤ n) :
    (∃ u : List ℕ, InLanguage n u ∧ u.length = 3 ∧ u.reverse = u) ∧
      (∀ u : List ℕ, InLanguage n u → 4 ≤ u.length → ¬ InLanguage n u.reverse) := by
  exact ⟨length_three_orientation_ambiguity n hn, reversal_forbidden_of_four_le n hn⟩

/-- **2. Seed independence of the family's factor languages.** For every letter `1 ≤ x ≤ n`, the
factor language of `σₙ` from the seed `x` is the factor language from `1`. -/
theorem inLanguageFrom_iff (n x : ℕ) (hx1 : 1 ≤ x) (hxn : x ≤ n)
    (u : List ℕ) : InLanguageFrom n x u ↔ InLanguage n u := by
  constructor
  · rintro ⟨k, hk⟩
    have hseed : (S n)^[x - 1] [1] = [x] := by
      rw [iterate_shift n (x - 1) [1] (by simp; omega)]
      simp only [List.map_cons, List.map_nil]
      congr 1
      omega
    refine ⟨k + (x - 1), ?_⟩
    rw [Function.iterate_add_apply, hseed]
    exact hk
  · rintro ⟨k, hk⟩
    have htop : (S n)^[n - x] [x] = [n] := by
      rw [iterate_shift n (n - x) [x] (by simp; omega)]
      simp only [List.map_cons, List.map_nil]
      congr 1
      omega
    have hone : [1] <:+: (S n)^[n - x + 1] [x] := by
      rw [Function.iterate_succ_apply', htop]
      exact ⟨[], [2], by simp [S, s]⟩
    refine ⟨k + (n - x + 1), ?_⟩
    rw [Function.iterate_add_apply]
    exact hk.trans (iterate_infix_aux n k hone)
where
  iterate_infix_aux (n : ℕ) : ∀ (k : ℕ) {u w : List ℕ}, u <:+: w →
      (S n)^[k] u <:+: (S n)^[k] w
    | 0, _, _, h => h
    | k + 1, _, _, h => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact S_infix n (iterate_infix_aux n k h)

end Family

/-! ## The twelve-letter tensor substitution -/

namespace Tensor

/-- **3. Exact orientation threshold of the tensor substitution (seed `p1`).** Some factor of
length three is its own reversal, and every factor of length at least four has a reversal that is
not a factor. -/
theorem exact_orientation_threshold_four :
    (∃ u : List Letter, InLanguage u ∧ u.length = 3 ∧ u.reverse = u) ∧
      (∀ u : List Letter, InLanguage u → 4 ≤ u.length → ¬ InLanguage u.reverse) := by
  exact ⟨length_three_orientation_ambiguity, reversal_forbidden_of_four_le⟩

/-- **4. Seed independence of the tensor substitution's factor language.** The factor language
from any seed letter is the factor language from `p1`. -/
theorem inLanguageFrom_iff (x : Letter) (u : List Letter) :
    InLanguageFrom x u ↔ InLanguage u := by
  constructor
  · obtain ⟨k, hk⟩ := letter_in_p1_iterate x
    exact language_mono hk u
  · obtain ⟨k, hk⟩ := p1_in_letter_iterate x
    exact language_mono hk u

/-- **5. Exact orientation threshold of the tensor substitution, every seed and across seeds.** For
any seed letters `x, y`: some factor of length three from `x` is its own reversal, and no factor
from `x` of length at least four has its reversal among the factors from `y`. -/
theorem exact_orientation_threshold_four_any_seed (x y : Letter) :
    (∃ u : List Letter, InLanguageFrom x u ∧ u.length = 3 ∧ u.reverse = u) ∧
      (∀ u : List Letter, InLanguageFrom x u → 4 ≤ u.length →
        ¬ InLanguageFrom y u.reverse) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨u, hu, h3, hrev⟩ := length_three_orientation_ambiguity
    exact ⟨u, (inLanguageFrom_iff x u).2 hu, h3, hrev⟩
  · intro u hu hlen hrev
    exact reversal_forbidden_of_four_le u ((inLanguageFrom_iff x u).1 hu) hlen
      ((inLanguageFrom_iff y u.reverse).1 hrev)

end Tensor

end FourTickOrientation
