module
public import Mathlib
public import FourTickWords

@[expose] public section
/-!
# FourTickTensor — the factor language of the twelve-letter tensor substitution, up to length four

The proof library for statements 5–7 of `Challenge.lean`. The definitions `Letter`, `s`, `S`,
`InLanguage`, `InLanguageFrom` are those of `Challenge.lean`, character for character.

* The window lemma (`infix_window`), as for the cubic substitution.
* The certificate `C4`, 456 words of length `≤ 4` (1 + 12 + 79 + 148 + 216 by length), packed into
  a bit mask indexed by a base-13 word code (`inCert`). Two kernel checks by `decide +kernel` over
  the 22,621 words of length `≤ 4` (by kernel reduction alone): `closed_check` and `rev_check`, as for the
  quartic substitution. `factors_complete` (used only as an upper bound on the factor set).
* `reversal_forbidden_of_four_le`; the eighth iterate from `p1` (28 letters) contains `q1 q2 q1`.
* Seed independence ingredients: `letter_in_p1_iterate`, `p1_in_letter_iterate`, `language_mono`.

Provenance: copied from the author's development repository, `PdtRhoQChirality.lean`
(`PdtRhoQ`: `Letter`, `s`, `S`, `S_nil`, `S_cons`) and `PdtRulerFourTick.lean`
(`PDT.RulerFourTick`: everything else). Statements and proofs are unchanged; the namespace is
`FourTickOrientation.Tensor`, `PDT.Padovan.infix_append_split` is replaced by the identical
`FourTickOrientation.infix_append_split`, the derived `Repr` instance of `Letter` is dropped, the
module-system header is added, and the theorems `inLanguageFrom_iff`,
`exact_orientation_threshold_four` and `exact_orientation_threshold_four_any_seed` are in
`Solution.lean` (their proofs unchanged).
-/

namespace FourTickOrientation.Tensor

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

@[simp] theorem S_nil : S [] = [] := rfl

@[simp] theorem S_cons (x : Letter) (w : List Letter) : S (x :: w) = s x ++ S w := rfl

/-! ## Block lengths -/

theorem one_le_length_s (x : Letter) : 1 ≤ (s x).length := by cases x <;> simp [s]

theorem length_s_le (x : Letter) : (s x).length ≤ 4 := by cases x <;> simp [s]

theorem length_S_le : ∀ w : List Letter, (S w).length ≤ 4 * w.length := by
  intro w
  induction w with
  | nil => simp
  | cons x w ih =>
    have hx := length_s_le x
    rw [S_cons, List.length_append, List.length_cons]
    omega

/-! ## The window lemma (as in `FourTickCubic`, for the 12-letter alphabet) -/

/-- **Prefix window lemma.** A prefix of `S w` is a prefix of the image of a
prefix of `w` that is no longer than it. -/
theorem prefix_window : ∀ (w u : List Letter), u <+: S w →
    ∃ v, v <+: w ∧ v.length ≤ u.length ∧ u <+: S v := by
  intro w
  induction w with
  | nil =>
    intro u hu
    rw [S_nil, List.prefix_nil] at hu
    subst hu
    exact ⟨[], List.nil_prefix, le_refl 0, List.nil_prefix⟩
  | cons x w' ih =>
    intro u hu
    rw [S_cons] at hu
    by_cases hlen : u.length ≤ (s x).length
    · have hux : u <+: s x :=
        List.prefix_of_prefix_length_le hu (List.prefix_append _ _) hlen
      rcases eq_or_ne u [] with rfl | hne
      · exact ⟨[], List.nil_prefix, by simp, List.nil_prefix⟩
      · have hpos : 0 < u.length := List.length_pos_iff.mpr hne
        refine ⟨[x], ⟨w', rfl⟩, ?_, ?_⟩
        · simp only [List.length_cons, List.length_nil]; omega
        · rw [S_cons, S_nil, List.append_nil]
          exact hux
    · have hlen' : (s x).length ≤ u.length := by omega
      have hsx : s x <+: u :=
        List.prefix_of_prefix_length_le (List.prefix_append _ _) hu hlen'
      obtain ⟨u₂, rfl⟩ := hsx
      have hu₂ : u₂ <+: S w' := (List.prefix_append_right_inj (s x)).1 hu
      obtain ⟨v', hv'p, hv'len, hv'⟩ := ih u₂ hu₂
      refine ⟨x :: v', ?_, ?_, ?_⟩
      · exact List.cons_prefix_cons.2 ⟨rfl, hv'p⟩
      · have h1 := one_le_length_s x
        simp only [List.length_cons, List.length_append]
        omega
      · rw [S_cons]
        exact (List.prefix_append_right_inj (s x)).2 hv'

/-- **Infix window lemma.** A nonempty factor of `S w` is a factor of the
image of a factor of `w` that is no longer than it. -/
theorem infix_window : ∀ (w u : List Letter), u <:+: S w →
    u = [] ∨ ∃ v, v <:+: w ∧ v.length ≤ u.length ∧ u <:+: S v := by
  intro w
  induction w with
  | nil =>
    intro u hu
    rw [S_nil, List.infix_nil] at hu
    exact Or.inl hu
  | cons x w' ih =>
    intro u hu
    rcases eq_or_ne u [] with rfl | hne
    · exact Or.inl rfl
    right
    rw [S_cons] at hu
    have hpos : 0 < u.length := List.length_pos_iff.mpr hne
    rcases FourTickOrientation.infix_append_split hu with h | h | ⟨u₁, u₂, rfl, h1len, h1suf, h2pre⟩
    · refine ⟨[x], ⟨[], w', rfl⟩, ?_, ?_⟩
      · simp only [List.length_cons, List.length_nil]; omega
      · rw [S_cons, S_nil, List.append_nil]
        exact h
    · rcases ih u h with rfl | ⟨v, ⟨pv, qv, hpv⟩, hvlen, huv⟩
      · exact absurd rfl hne
      · exact ⟨v, ⟨x :: pv, qv, by rw [List.cons_append, List.cons_append, hpv]⟩,
          hvlen, huv⟩
    · obtain ⟨v₂, hv₂p, hv₂len, hv₂⟩ := prefix_window w' u₂ h2pre
      obtain ⟨t, ht⟩ := hv₂p
      refine ⟨x :: v₂, ⟨[], t, by rw [List.nil_append, List.cons_append, ht]⟩, ?_, ?_⟩
      · simp only [List.length_cons, List.length_append]
        omega
      · rw [S_cons]
        obtain ⟨p, hp⟩ := h1suf
        obtain ⟨r, hr⟩ := hv₂
        exact ⟨p, r, by rw [← hp, ← hr]; simp [List.append_assoc]⟩

/-! ## The length-≤4 certificate -/

/-- The 456 words of length ≤ 4 forming the factor certificate
(1 + 12 + 79 + 148 + 216 by length). -/
def C4 : List (List Letter) := [
  [],
  [p1], [p2], [p3], [p4], [q1], [q2], [q3], [q4], [r1], [r2], [r3], [r4],
  [p1, p2], [p2, q1], [p2, q2], [p3, q3], [p4, q4], [q1, q2], [q2, p1], [q2, p2], [q2, p3],
  [q2, p4], [q2, q1], [q2, q2], [q2, q3], [q2, q4], [q2, r1], [q2, r2], [q2, r3], [q2, r4],
  [q3, p1], [q3, p2], [q3, p3], [q3, p4], [q3, q1], [q3, q2], [q3, q3], [q3, q4], [q3, r1],
  [q3, r2], [q3, r3], [q3, r4], [q4, p1], [q4, p2], [q4, p3], [q4, p4], [q4, q1], [q4, q2],
  [q4, q3], [q4, q4], [q4, r1], [q4, r2], [q4, r3], [q4, r4], [r1, r2], [r2, p1], [r2, p2],
  [r2, p3], [r2, p4], [r2, q1], [r2, q2], [r2, q3], [r2, q4], [r2, r1], [r2, r2], [r2, r3],
  [r2, r4], [r3, p1], [r3, p2], [r3, p3], [r3, p4], [r3, q1], [r3, q2], [r3, q3], [r3, q4],
  [r3, r1], [r3, r2], [r3, r3], [r3, r4], [r4, p1], [r4, p2], [r4, p3], [r4, p4], [r4, q1],
  [r4, q2], [r4, q3], [r4, q4], [r4, r1], [r4, r2], [r4, r3], [r4, r4],
  [p1, p2, q1], [p2, q1, q2], [p2, q2, p3], [p3, q3, p1], [p3, q3, p2], [p3, q3, p3],
  [p3, q3, p4], [p3, q3, q1], [p3, q3, q2], [p3, q3, q3], [p3, q3, q4], [p3, q3, r1],
  [p3, q3, r2], [p3, q3, r3], [p3, q3, r4], [p4, q4, p1], [p4, q4, p2], [p4, q4, p3],
  [p4, q4, p4], [p4, q4, q1], [p4, q4, q2], [p4, q4, q3], [p4, q4, q4], [p4, q4, r1],
  [p4, q4, r2], [p4, q4, r3], [p4, q4, r4], [q1, q2, p1], [q1, q2, p2], [q1, q2, p3],
  [q1, q2, p4], [q1, q2, q1], [q1, q2, q2], [q1, q2, q3], [q1, q2, q4], [q1, q2, r1],
  [q1, q2, r2], [q1, q2, r3], [q1, q2, r4], [q2, p1, p2], [q2, p2, q2], [q2, p3, q3],
  [q2, p4, q4], [q2, q1, q2], [q2, q2, q3], [q2, q3, r2], [q2, q3, r3], [q2, q4, r4],
  [q2, r1, r2], [q2, r2, r3], [q2, r3, r4], [q2, r4, p4], [q3, p1, p2], [q3, p2, q2],
  [q3, p3, q3], [q3, p4, q4], [q3, q1, q2], [q3, q2, q3], [q3, q3, r3], [q3, q4, r4],
  [q3, r1, r2], [q3, r2, r3], [q3, r3, q4], [q3, r3, r4], [q3, r4, p4], [q4, p1, p2],
  [q4, p2, q2], [q4, p3, q3], [q4, p4, q4], [q4, q1, q2], [q4, q2, q3], [q4, q3, r3],
  [q4, q4, r4], [q4, r1, r2], [q4, r2, r3], [q4, r3, r4], [q4, r4, p1], [q4, r4, p2],
  [q4, r4, p3], [q4, r4, p4], [q4, r4, q1], [q4, r4, q2], [q4, r4, q3], [q4, r4, q4],
  [q4, r4, r1], [q4, r4, r2], [q4, r4, r3], [q4, r4, r4], [r1, r2, p1], [r1, r2, p2],
  [r1, r2, p3], [r1, r2, p4], [r1, r2, q1], [r1, r2, q2], [r1, r2, q3], [r1, r2, q4],
  [r1, r2, r1], [r1, r2, r2], [r1, r2, r3], [r1, r2, r4], [r2, p1, p2], [r2, p2, q2],
  [r2, p3, q3], [r2, p4, q4], [r2, q1, q2], [r2, q2, q3], [r2, q3, r3], [r2, q4, r4],
  [r2, r1, r2], [r2, r2, r3], [r2, r3, p1], [r2, r3, p2], [r2, r3, p3], [r2, r3, p4],
  [r2, r3, q1], [r2, r3, q2], [r2, r3, q3], [r2, r3, q4], [r2, r3, r1], [r2, r3, r2],
  [r2, r3, r3], [r2, r3, r4], [r2, r4, p4], [r3, p1, p2], [r3, p2, q2], [r3, p3, q3],
  [r3, p4, q4], [r3, q1, q2], [r3, q2, q3], [r3, q3, r3], [r3, q4, r4], [r3, r1, r2],
  [r3, r2, r3], [r3, r3, r4], [r3, r4, p3], [r3, r4, p4], [r4, p1, p2], [r4, p2, q2],
  [r4, p3, q3], [r4, p4, q4], [r4, q1, q2], [r4, q2, q3], [r4, q3, r3], [r4, q4, r4],
  [r4, r1, r2], [r4, r2, r3], [r4, r3, r4], [r4, r4, p4],
  [p1, p2, q1, q2], [p2, q1, q2, p1], [p2, q1, q2, p2], [p2, q1, q2, p3], [p2, q1, q2, p4],
  [p2, q1, q2, q1], [p2, q1, q2, q2], [p2, q1, q2, q3], [p2, q1, q2, q4], [p2, q1, q2, r1],
  [p2, q1, q2, r2], [p2, q1, q2, r3], [p2, q1, q2, r4], [p2, q2, p3, q3], [p3, q3, p1, p2],
  [p3, q3, p2, q2], [p3, q3, p3, q3], [p3, q3, p4, q4], [p3, q3, q1, q2], [p3, q3, q2, q3],
  [p3, q3, q3, r3], [p3, q3, q4, r4], [p3, q3, r1, r2], [p3, q3, r2, r3], [p3, q3, r3, r4],
  [p3, q3, r4, p4], [p4, q4, p1, p2], [p4, q4, p2, q2], [p4, q4, p3, q3], [p4, q4, p4, q4],
  [p4, q4, q1, q2], [p4, q4, q2, q3], [p4, q4, q3, r3], [p4, q4, q4, r4], [p4, q4, r1, r2],
  [p4, q4, r2, r3], [p4, q4, r3, r4], [p4, q4, r4, p4], [q1, q2, p1, p2], [q1, q2, p2, q2],
  [q1, q2, p3, q3], [q1, q2, p4, q4], [q1, q2, q1, q2], [q1, q2, q2, q3], [q1, q2, q3, r3],
  [q1, q2, q4, r4], [q1, q2, r1, r2], [q1, q2, r2, r3], [q1, q2, r3, r4], [q1, q2, r4, p4],
  [q2, p1, p2, q1], [q2, p2, q2, p3], [q2, p3, q3, p1], [q2, p3, q3, p2], [q2, p3, q3, p3],
  [q2, p3, q3, p4], [q2, p3, q3, q1], [q2, p3, q3, q2], [q2, p3, q3, q3], [q2, p3, q3, q4],
  [q2, p3, q3, r1], [q2, p3, q3, r2], [q2, p3, q3, r3], [q2, p3, q3, r4], [q2, p4, q4, p1],
  [q2, q1, q2, r1], [q2, q2, q3, r2], [q2, q3, r2, r3], [q2, q3, r3, q4], [q2, q4, r4, q1],
  [q2, r1, r2, p1], [q2, r1, r2, p2], [q2, r1, r2, p3], [q2, r1, r2, p4], [q2, r1, r2, q1],
  [q2, r1, r2, q2], [q2, r1, r2, q3], [q2, r1, r2, q4], [q2, r1, r2, r1], [q2, r1, r2, r2],
  [q2, r1, r2, r3], [q2, r1, r2, r4], [q2, r2, r3, p2], [q2, r3, r4, p3], [q2, r4, p4, q4],
  [q3, p1, p2, q1], [q3, p2, q2, p3], [q3, p3, q3, p4], [q3, p4, q4, p1], [q3, p4, q4, p2],
  [q3, p4, q4, p3], [q3, p4, q4, p4], [q3, p4, q4, q1], [q3, p4, q4, q2], [q3, p4, q4, q3],
  [q3, p4, q4, q4], [q3, p4, q4, r1], [q3, p4, q4, r2], [q3, p4, q4, r3], [q3, p4, q4, r4],
  [q3, q1, q2, r1], [q3, q2, q3, r2], [q3, q3, r3, q4], [q3, q4, r4, q1], [q3, r1, r2, p1],
  [q3, r2, r3, p1], [q3, r2, r3, p2], [q3, r2, r3, p3], [q3, r2, r3, p4], [q3, r2, r3, q1],
  [q3, r2, r3, q2], [q3, r2, r3, q3], [q3, r2, r3, q4], [q3, r2, r3, r1], [q3, r2, r3, r2],
  [q3, r2, r3, r3], [q3, r2, r3, r4], [q3, r3, q4, r4], [q3, r3, r4, p3], [q3, r4, p4, q4],
  [q4, p1, p2, q1], [q4, p2, q2, p3], [q4, p3, q3, p4], [q4, p4, q4, p1], [q4, q1, q2, r1],
  [q4, q2, q3, r2], [q4, q3, r3, q4], [q4, q4, r4, q1], [q4, r1, r2, p1], [q4, r2, r3, p2],
  [q4, r3, r4, p3], [q4, r4, p1, p2], [q4, r4, p2, q2], [q4, r4, p3, q3], [q4, r4, p4, q4],
  [q4, r4, q1, q2], [q4, r4, q2, q3], [q4, r4, q3, r3], [q4, r4, q4, r4], [q4, r4, r1, r2],
  [q4, r4, r2, r3], [q4, r4, r3, r4], [q4, r4, r4, p4], [r1, r2, p1, p2], [r1, r2, p2, q2],
  [r1, r2, p3, q3], [r1, r2, p4, q4], [r1, r2, q1, q2], [r1, r2, q2, q3], [r1, r2, q3, r3],
  [r1, r2, q4, r4], [r1, r2, r1, r2], [r1, r2, r2, r3], [r1, r2, r3, r4], [r1, r2, r4, p4],
  [r2, p1, p2, q1], [r2, p2, q2, p3], [r2, p3, q3, p4], [r2, p4, q4, p1], [r2, q1, q2, r1],
  [r2, q2, q3, r2], [r2, q3, r3, q4], [r2, q4, r4, q1], [r2, r1, r2, p1], [r2, r2, r3, p2],
  [r2, r3, p1, p2], [r2, r3, p2, q2], [r2, r3, p3, q3], [r2, r3, p4, q4], [r2, r3, q1, q2],
  [r2, r3, q2, q3], [r2, r3, q3, r3], [r2, r3, q4, r4], [r2, r3, r1, r2], [r2, r3, r2, r3],
  [r2, r3, r3, r4], [r2, r3, r4, p3], [r2, r3, r4, p4], [r2, r4, p4, q4], [r3, p1, p2, q1],
  [r3, p2, q2, p3], [r3, p3, q3, p4], [r3, p4, q4, p1], [r3, q1, q2, r1], [r3, q2, q3, r2],
  [r3, q3, r3, q4], [r3, q4, r4, p1], [r3, q4, r4, p2], [r3, q4, r4, p3], [r3, q4, r4, p4],
  [r3, q4, r4, q1], [r3, q4, r4, q2], [r3, q4, r4, q3], [r3, q4, r4, q4], [r3, q4, r4, r1],
  [r3, q4, r4, r2], [r3, q4, r4, r3], [r3, q4, r4, r4], [r3, r1, r2, p1], [r3, r2, r3, p2],
  [r3, r3, r4, p3], [r3, r4, p3, q3], [r3, r4, p4, q4], [r4, p1, p2, q1], [r4, p2, q2, p3],
  [r4, p3, q3, p4], [r4, p4, q4, p1], [r4, p4, q4, r1], [r4, q1, q2, r1], [r4, q2, q3, r2],
  [r4, q3, r3, q4], [r4, q4, r4, q1], [r4, r1, r2, p1], [r4, r2, r3, p2], [r4, r3, r4, p3],
  [r4, r4, p4, q4]
]

/-- Cross-check against the computed factor counts: 456 = 1+12+79+148+216. -/
theorem C4_length : C4.length = 456 := by decide +kernel

/-- Cross-check: 216 certificate words of length four. -/
theorem C4_length_four : (C4.filter (fun w => w.length == 4)).length = 216 := by
  decide +kernel

/-- Letter index `0..11`. -/
def idx : Letter → ℕ
  | p1 => 0 | p2 => 1 | p3 => 2 | p4 => 3 | q1 => 4 | q2 => 5
  | q3 => 6 | q4 => 7 | r1 => 8 | r2 => 9 | r3 => 10 | r4 => 11

/-- Base-13 word code (digit 0 marks the end of the word). -/
def code : List Letter → ℕ
  | [] => 0
  | x :: w => idx x + 1 + 13 * code w

/-- The certificate packed as a bit mask: bit `code w` is set for `w ∈ C4`. -/
def mask : ℕ := C4.foldr (fun w acc => acc ||| (1 <<< code w)) 0

/-- Certificate membership, one bit lookup. -/
def inCert (w : List Letter) : Bool := mask.testBit (code w)

/-- The twelve letters. -/
def allLetters : List Letter := [p1, p2, p3, p4, q1, q2, q3, q4, r1, r2, r3, r4]

/-- All words of length at most `k`. -/
def words : ℕ → List (List Letter)
  | 0 => [[]]
  | k + 1 => [] :: allLetters.flatMap fun x => (words k).map (x :: ·)

theorem mem_allLetters (x : Letter) : x ∈ allLetters := by
  cases x <;> simp [allLetters]

theorem mem_words : ∀ (k : ℕ) (v : List Letter), v.length ≤ k → v ∈ words k
  | 0, [], _ => by simp [words]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => by simp [words]
  | k + 1, x :: v, h => by
    simp only [words, List.mem_cons, List.mem_flatMap, List.mem_map]
    right
    exact ⟨x, mem_allLetters x, v, mem_words k v (by simp at h; omega), rfl⟩

/-- Every length-≤4 window of `S v`, at any start position `< 17`. -/
def windowsOK (v : List Letter) : Bool :=
  (List.range 17).all fun i => (List.range 5).all fun j => inCert (((S v).drop i).take j)

/-- **Closure (kernel check).** Every certified word of length ≤ 4 has all its
length-≤4 image windows certified. -/
theorem closed_check : (words 4).all (fun v => !inCert v || windowsOK v) = true := by
  decide +kernel

/-- **Orientation (kernel check).** No certified word of length 4 has a
certified reversal. -/
theorem rev_check :
    (words 4).all (fun u => !(u.length == 4) || !inCert u || !inCert u.reverse) = true := by
  decide +kernel

theorem inCert_nil : inCert [] = true := by decide +kernel

theorem inCert_p1 : inCert [p1] = true := by decide +kernel

/-- A short factor of the image of a certified word is certified. -/
theorem inCert_of_infix {v u : List Letter} (hv : inCert v = true) (hvlen : v.length ≤ 4)
    (huv : u <:+: S v) (hlen : u.length ≤ 4) : inCert u = true := by
  have hall := List.all_eq_true.mp closed_check v (mem_words 4 v hvlen)
  rw [hv] at hall
  simp only [Bool.not_true, Bool.false_or, windowsOK, List.all_eq_true, List.mem_range] at hall
  have hSv : (S v).length ≤ 16 := le_trans (length_S_le v) (by omega)
  obtain ⟨p, q, hpq⟩ := huv
  have hplen : p.length ≤ (S v).length := by
    have hl := congrArg List.length hpq
    simp only [List.length_append] at hl
    omega
  have hdrop : (S v).drop p.length = u ++ q := by
    rw [← hpq, List.append_assoc, List.drop_left]
  have htake : (u ++ q).take u.length = u := List.take_left
  have hmem := hall p.length (by omega) u.length (by omega)
  rw [hdrop, htake] at hmem
  exact hmem

/-- **FACTOR COMPLETENESS AT LENGTH ≤ 4.** Every factor of length ≤ 4 of every
iterate `S^[n] [p1]` is certified. -/
theorem factors_complete : ∀ (n : ℕ) (u : List Letter),
    u <:+: S^[n] [p1] → u.length ≤ 4 → inCert u = true := by
  intro n
  induction n with
  | zero =>
    intro u hu _
    rw [Function.iterate_zero_apply] at hu
    have hlen := hu.length_le
    cases u with
    | nil => exact inCert_nil
    | cons x t =>
      cases t with
      | nil =>
        have hx : x ∈ ([p1] : List Letter) :=
          List.IsInfix.mem (List.mem_singleton_self x) hu
        rw [List.mem_singleton] at hx
        subst hx
        exact inCert_p1
      | cons y t' =>
        simp only [List.length_cons, List.length_nil] at hlen
        omega
  | succ m ih =>
    intro u hu hlen
    rw [Function.iterate_succ_apply'] at hu
    rcases infix_window (S^[m] [p1]) u hu with rfl | ⟨v, hvinf, hvlen, huv⟩
    · exact inCert_nil
    · exact inCert_of_infix (ih v hvinf (le_trans hvlen hlen)) (by omega) huv hlen

/-- No certified length-four word has a certified reversal. -/
theorem inCert_reverse_false {u : List Letter} (hlen : u.length = 4) (hu : inCert u = true) :
    inCert u.reverse = false := by
  have h := List.all_eq_true.mp rev_check u (mem_words 4 u (by omega))
  simp only [hlen, hu] at h
  simpa using h

/-- Every rhoQ factor of length at least four has a forbidden reversal.  The
only finite check is at length four; factor closure propagates it. -/
theorem reversal_forbidden_of_four_le (u : List Letter)
    (hu : InLanguage u) (hlen : 4 ≤ u.length) : ¬ InLanguage u.reverse := by
  obtain ⟨n, hun⟩ := hu
  let t := u.take 4
  have htlen : t.length = 4 := by
    simp only [t, List.length_take]
    omega
  have htu : t <:+: u := (List.take_prefix 4 u).isInfix
  have htn : t <:+: S^[n] [p1] := htu.trans hun
  have htC : inCert t = true := factors_complete n t htn (by omega)
  intro hrev
  obtain ⟨m, hrev_m⟩ := hrev
  have htrev_u : t.reverse <:+: u.reverse := htu.reverse
  have htrev_m : t.reverse <:+: S^[m] [p1] := htrev_u.trans hrev_m
  have htrevC : inCert t.reverse = true :=
    factors_complete m t.reverse htrev_m (by simp [htlen])
  rw [inCert_reverse_false htlen htC] at htrevC
  exact Bool.false_ne_true htrevC

/-- The eighth iterate from `p1` (28 letters); positions 14..16 read `q1 q2 q1`. -/
theorem iterate_eight :
    S^[8] [p1] =
      [r1, r2, p1, p2, q1, q2, r2, r3, p2, q2, p3, q3, p1, p2,
       q1, q2, q1, q2, r1, r2, p2, q2, p3, q3, q2, q3, r2, r3] := by
  decide

/-- A length-three factor can be its own reversal, so no uniform orientation
readout is possible at length three. -/
theorem length_three_orientation_ambiguity :
    ∃ u : List Letter, InLanguage u ∧ u.length = 3 ∧ u.reverse = u := by
  refine ⟨[q1, q2, q1], ?_, by decide, by decide⟩
  refine ⟨8, ?_⟩
  rw [iterate_eight]
  exact ⟨[r1, r2, p1, p2, q1, q2, r2, r3, p2, q2, p3, q3, p1, p2],
    [q2, r1, r2, p2, q2, p3, q3, q2, q3, r2, r3], rfl⟩

/-! ## Seed independence: the ingredients -/

theorem S_append : ∀ a b : List Letter, S (a ++ b) = S a ++ S b
  | [], _ => rfl
  | x :: a, b => by rw [List.cons_append, S_cons, S_cons, S_append a b, List.append_assoc]

theorem S_infix {u w : List Letter} (h : u <:+: w) : S u <:+: S w := by
  obtain ⟨p, q, rfl⟩ := h
  exact ⟨S p, S q, by rw [S_append, S_append]⟩

theorem iterate_infix (n : ℕ) {u w : List Letter} (h : u <:+: w) :
    S^[n] u <:+: S^[n] w := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact S_infix ih

theorem language_mono {x y : Letter} {k : ℕ} (hk : [x] <:+: S^[k] [y]) (u : List Letter) :
    InLanguageFrom x u → InLanguageFrom y u := by
  rintro ⟨n, hn⟩
  refine ⟨n + k, hn.trans ?_⟩
  rw [Function.iterate_add_apply]
  exact iterate_infix n hk

/-- Every letter occurs in an iterate from `p1`. -/
theorem letter_in_p1_iterate : ∀ x : Letter, ∃ k, [x] <:+: S^[k] [p1] := by
  intro x
  cases x
  exacts [⟨0, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨3, by decide⟩,
    ⟨4, by decide⟩, ⟨1, by decide⟩, ⟨5, by decide⟩, ⟨3, by decide⟩,
    ⟨4, by decide⟩, ⟨4, by decide⟩, ⟨2, by decide⟩, ⟨6, by decide⟩]

/-- `p1` occurs in an iterate from every letter. -/
theorem p1_in_letter_iterate : ∀ x : Letter, ∃ k, [p1] <:+: S^[k] [x] := by
  intro x
  cases x
  exacts [⟨0, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩,
    ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩,
    ⟨4, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨1, by decide⟩]

end FourTickOrientation.Tensor
