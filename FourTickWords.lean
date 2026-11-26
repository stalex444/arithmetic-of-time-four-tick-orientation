module
public import Mathlib

@[expose] public section
/-!
# FourTickWords — one lemma about lists shared by the three substitutions

`infix_append_split`: an infix of `l₁ ++ l₂` is an infix of `l₁`, an infix of `l₂`, or splits as
a nonempty suffix of `l₁` followed by a prefix of `l₂`. It is the only step of the window lemmas
(`FourTickCubic`, `FourTickQuartic`, `FourTickTensor`) that does not depend on the alphabet.

Provenance: copied from `PDT.Padovan.infix_append_split` (`PdtChirality.lean` in the author's
development repository); the statement and the proof are unchanged, only the namespace differs.
-/

namespace FourTickOrientation

/-- Splitting an infix across an append: an infix of `l₁ ++ l₂` is an infix
of `l₁`, an infix of `l₂`, or splits as a nonempty suffix of `l₁` followed
by a prefix of `l₂`. -/
theorem infix_append_split {α : Type*} {u l₁ l₂ : List α} (h : u <:+: l₁ ++ l₂) :
    u <:+: l₁ ∨ u <:+: l₂ ∨
      ∃ u₁ u₂, u = u₁ ++ u₂ ∧ 1 ≤ u₁.length ∧ u₁ <:+ l₁ ∧ u₂ <+: l₂ := by
  obtain ⟨p, q, hpq⟩ := h
  by_cases hA : p.length + u.length ≤ l₁.length
  · left
    have htake := congrArg (List.take l₁.length) hpq
    rw [List.take_left] at htake
    rw [List.take_append, List.take_append] at htake
    have hp1 : p.length ≤ l₁.length := by omega
    have hp2 : u.length ≤ l₁.length - p.length := by omega
    rw [List.take_of_length_le hp1, List.take_of_length_le hp2] at htake
    exact ⟨p, _, htake⟩
  · by_cases hB : l₁.length ≤ p.length
    · right; left
      have hdrop := congrArg (List.drop l₁.length) hpq
      rw [List.drop_left] at hdrop
      rw [List.drop_append, List.drop_append] at hdrop
      have e1 : l₁.length - p.length = 0 := by omega
      have e2 : l₁.length - (p ++ u).length = 0 := by
        simp only [List.length_append]; omega
      rw [e1, e2] at hdrop
      simp only [List.drop_zero] at hdrop
      exact ⟨p.drop l₁.length, q, hdrop⟩
    · right; right
      refine ⟨u.take (l₁.length - p.length), u.drop (l₁.length - p.length),
        (List.take_append_drop _ u).symm, ?_, ?_, ?_⟩
      · rw [List.length_take]; omega
      · have htake := congrArg (List.take l₁.length) hpq
        rw [List.take_left] at htake
        rw [List.take_append, List.take_append] at htake
        have hp1 : p.length ≤ l₁.length := by omega
        have e2 : l₁.length - (p ++ u).length = 0 := by
          simp only [List.length_append]; omega
        rw [List.take_of_length_le hp1, e2] at htake
        simp only [List.take_zero, List.append_nil] at htake
        exact ⟨p, htake⟩
      · have hdrop := congrArg (List.drop l₁.length) hpq
        rw [List.drop_left] at hdrop
        rw [List.drop_append, List.drop_append] at hdrop
        have e2 : l₁.length - (p ++ u).length = 0 := by
          simp only [List.length_append]; omega
        have hp1 : p.length ≤ l₁.length := by omega
        rw [e2, List.drop_eq_nil_of_le hp1] at hdrop
        simp only [List.drop_zero, List.nil_append] at hdrop
        exact ⟨q, hdrop⟩

end FourTickOrientation
