module
public import Mathlib
public import FourTickWords
public import FourTickCubic
public import FourTickQuartic
public import FourTickTensor

@[expose] public section
/-!
# The exact orientation threshold 4: proofs of the compared statements

Each of the seven statements of `Challenge.lean` is proved here, with the identical statement and
docstring. The definitions of `Challenge.lean` (`Letter`, `s`, `S`, `InLanguage` and, for the
quartic and tensor substitutions, `InLanguageFrom`) are those of the proof library, character for
character: `FourTickCubic.lean`, `FourTickQuartic.lean`, `FourTickTensor.lean`, with the one shared
list lemma in `FourTickWords.lean`.

* Statements 1, 2, 5: `length_three_orientation_ambiguity` (an explicit iterate, by `decide`,
  contains the palindrome) and `reversal_forbidden_of_four_le` (the finite certificate at length
  four, propagated to every longer length by factor closure) of the respective library module.
* Statements 3, 6: `language_mono` in both directions, with `letter_in_a_iterate` /
  `a_in_letter_iterate` (quartic) and `letter_in_p1_iterate` / `p1_in_letter_iterate` (tensor).
* Statements 4, 7: statements 2, 5 transported along statements 3, 6.
-/

namespace FourTickOrientation

/-! ## The cubic Padovan substitution -/

namespace Cubic

/-- **1. Exact orientation threshold of the cubic Padovan substitution (seed `a`).** Some factor of
length three is its own reversal, and every factor of length at least four has a reversal that is
not a factor. -/
theorem exact_orientation_threshold_four :
    (∃ u : List Letter, InLanguage u ∧ u.length = 3 ∧ u.reverse = u) ∧
      (∀ u : List Letter, InLanguage u → 4 ≤ u.length → ¬ InLanguage u.reverse) := by
  exact ⟨length_three_orientation_ambiguity, reversal_forbidden_of_four_le⟩

end Cubic

/-! ## The quartic substitution -/

namespace Quartic

/-- **2. Exact orientation threshold of the quartic substitution (seed `a`).** Some factor of
length three is its own reversal, and every factor of length at least four has a reversal that is
not a factor. -/
theorem exact_orientation_threshold_four :
    (∃ u : List Letter, InLanguage u ∧ u.length = 3 ∧ u.reverse = u) ∧
      (∀ u : List Letter, InLanguage u → 4 ≤ u.length → ¬ InLanguage u.reverse) := by
  exact ⟨length_three_orientation_ambiguity, reversal_forbidden_of_four_le⟩

/-- **3. Seed independence of the quartic substitution's factor language.** The factor language
from any seed letter is the factor language from `a`. -/
theorem inLanguageFrom_iff (x : Letter) (u : List Letter) :
    InLanguageFrom x u ↔ InLanguage u := by
  constructor
  · obtain ⟨k, hk⟩ := letter_in_a_iterate x
    exact language_mono hk u
  · obtain ⟨k, hk⟩ := a_in_letter_iterate x
    exact language_mono hk u

/-- **4. Exact orientation threshold of the quartic substitution, every seed and across seeds.** For
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

end Quartic

/-! ## The twelve-letter tensor substitution -/

namespace Tensor

/-- **5. Exact orientation threshold of the tensor substitution (seed `p1`).** Some factor of
length three is its own reversal, and every factor of length at least four has a reversal that is
not a factor. -/
theorem exact_orientation_threshold_four :
    (∃ u : List Letter, InLanguage u ∧ u.length = 3 ∧ u.reverse = u) ∧
      (∀ u : List Letter, InLanguage u → 4 ≤ u.length → ¬ InLanguage u.reverse) := by
  exact ⟨length_three_orientation_ambiguity, reversal_forbidden_of_four_le⟩

/-- **6. Seed independence of the tensor substitution's factor language.** The factor language
from any seed letter is the factor language from `p1`. -/
theorem inLanguageFrom_iff (x : Letter) (u : List Letter) :
    InLanguageFrom x u ↔ InLanguage u := by
  constructor
  · obtain ⟨k, hk⟩ := letter_in_p1_iterate x
    exact language_mono hk u
  · obtain ⟨k, hk⟩ := p1_in_letter_iterate x
    exact language_mono hk u

/-- **7. Exact orientation threshold of the tensor substitution, every seed and across seeds.** For
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
