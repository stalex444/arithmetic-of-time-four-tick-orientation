module
public import Mathlib
public import FourTickWords

@[expose] public section
/-!
# FourTickCubic — the factor language of the cubic Padovan substitution, up to length four

The proof library for statement 1 of `Challenge.lean`. The definitions `Letter`, `s`, `S`,
`InLanguage` are those of `Challenge.lean`, character for character.

* The window lemma (`infix_window`): a nonempty factor of `S w` is a factor of the image of a
  factor of `w` that is no longer than it, because every block `s x` is nonempty.
* The certificate `F5`, 57 words of length `≤ 5`, contains the factors of the seed and is closed
  under length-`≤ 5` windows of images (`F5_closed`, by `decide`), so it contains every factor of
  length `≤ 5` of every iterate (`factors_complete`, induction on `n`). It is used only as an upper
  bound on the factor set.
* No length-four word of `F5` has its reversal in `F5` (`F5_no_reversal_pair_length_four`, by
  `decide`); factor closure carries this to every length `≥ 4` (`reversal_forbidden_of_four_le`).
* `S^[8] [a] = c a b a b b c` contains the palindrome `a b a` (`length_three_orientation_ambiguity`).

Provenance: the declarations below are copied from the author's development repository,
`PdtChirality.lean` (`PDT.Padovan`: the block lengths, the window lemmas, `F5`, `F5_short`,
`F5_closed`, `mem_F5_of_infix`, `factors_complete`) and `PdtFourTickThreshold.lean`
(`F5_no_reversal_pair_length_four`, `reversal_forbidden_of_four_le`, `iterate_eight`,
`length_three_orientation_ambiguity`). Statements and proofs are unchanged; the namespace is
`FourTickOrientation.Cubic`, the shared list lemma `infix_append_split` lives in `FourTickWords`,
and the module-system header is added.
-/

namespace FourTickOrientation.Cubic

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

@[simp] theorem S_nil : S [] = [] := rfl

@[simp] theorem S_cons (x : Letter) (w : List Letter) : S (x :: w) = s x ++ S w := rfl

/-- Every image block is nonempty. -/
theorem one_le_length_s (x : Letter) : 1 ≤ (s x).length := by cases x <;> simp [s]

/-- Every image block has length at most 2. -/
theorem length_s_le (x : Letter) : (s x).length ≤ 2 := by cases x <;> simp [s]

/-- The image of a word is at most twice as long. -/
theorem length_S_le : ∀ w : List Letter, (S w).length ≤ 2 * w.length := by
  intro w
  induction w with
  | nil => simp
  | cons x w ih =>
    have hx := length_s_le x
    rw [S_cons, List.length_append, List.length_cons]
    omega

/-! ## The window lemma: factors of images come from short factors -/

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

/-- **Prefix window lemma.** A prefix of `S w` is a prefix of the image of
a prefix of `w` that is no longer than it — because every block `s x` is
nonempty. -/
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
    rcases infix_append_split hu with h | h | ⟨u₁, u₂, rfl, h1len, h1suf, h2pre⟩
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

/-! ## Factor completeness at length ≤ 5, and no long palindromic factor -/

/-- The 57 words of length ≤ 5 over `{a,b,c}` forming the length-≤5 factor
certificate: it contains every length-≤5 factor of every `S^[n] [a]`
(`factors_complete`), because it contains the seed's factors and is closed
under length-≤5 windows of images (`F5_closed`). -/
def F5 : List (List Letter) :=
  [[],
  [a], [b], [c],
  [a, b], [b, a], [b, b], [b, c], [c, a], [c, b], [c, c],
  [a, b, a], [a, b, b], [a, b, c], [b, a, b], [b, b, c], [b, c, a],
  [b, c, b], [b, c, c], [c, a, b], [c, b, c], [c, c, a],
  [a, b, a, b], [a, b, b, c], [a, b, c, a], [b, a, b, b], [b, b, c, a],
  [b, b, c, b], [b, b, c, c], [b, c, a, b], [b, c, b, c], [b, c, c, a],
  [c, a, b, a], [c, a, b, b], [c, a, b, c], [c, b, c, c], [c, c, a, b],
  [a, b, a, b, b], [a, b, b, c, a], [a, b, b, c, b], [a, b, b, c, c],
  [a, b, c, a, b], [b, a, b, b, c], [b, b, c, a, b], [b, b, c, b, c],
  [b, b, c, c, a], [b, c, a, b, a], [b, c, a, b, b], [b, c, b, c, c],
  [b, c, c, a, b], [c, a, b, a, b], [c, a, b, b, c], [c, a, b, c, a],
  [c, b, c, c, a], [c, c, a, b, a], [c, c, a, b, b], [c, c, a, b, c]]

/-- Every certificate word has length at most 5. -/
theorem F5_short : ∀ v ∈ F5, v.length ≤ 5 := by decide

/-- **Closure**: every length-≤5 window of the image of a certificate word
is again a certificate word. -/
theorem F5_closed : ∀ v ∈ F5, ∀ i < 11, ∀ j < 6, ((S v).drop i).take j ∈ F5 := by
  decide

/-- A short factor of the image of a certificate word is a certificate
word. -/
theorem mem_F5_of_infix {v u : List Letter} (hv : v ∈ F5) (huv : u <:+: S v)
    (hlen : u.length ≤ 5) : u ∈ F5 := by
  have hvlen : v.length ≤ 5 := F5_short v hv
  have hSv : (S v).length ≤ 10 := le_trans (length_S_le v) (by omega)
  obtain ⟨p, q, hpq⟩ := huv
  have hplen : p.length ≤ (S v).length := by
    have hl := congrArg List.length hpq
    simp only [List.length_append] at hl
    omega
  have hdrop : (S v).drop p.length = u ++ q := by
    rw [← hpq, List.append_assoc, List.drop_left]
  have htake : (u ++ q).take u.length = u := List.take_left
  have hmem := F5_closed v hv p.length (by omega) u.length (by omega)
  rw [hdrop, htake] at hmem
  exact hmem

/-- **FACTOR COMPLETENESS AT LENGTH ≤ 5.** Every factor of length ≤ 5 of
every iterate `S^[n] [a]` is a certificate word. -/
theorem factors_complete : ∀ (n : ℕ) (u : List Letter),
    u <:+: S^[n] [Letter.a] → u.length ≤ 5 → u ∈ F5 := by
  intro n
  induction n with
  | zero =>
    intro u hu _
    rw [Function.iterate_zero_apply] at hu
    have hlen := hu.length_le
    cases u with
    | nil => decide
    | cons x t =>
      cases t with
      | nil =>
        have hx : x ∈ ([Letter.a] : List Letter) :=
          List.IsInfix.mem (List.mem_singleton_self x) hu
        rw [List.mem_singleton] at hx
        subst hx
        decide
      | cons y t' =>
        simp only [List.length_cons, List.length_nil] at hlen
        omega
  | succ m ih =>
    intro u hu hlen
    rw [Function.iterate_succ_apply'] at hu
    rcases infix_window (S^[m] [Letter.a]) u hu with rfl | ⟨v, hvinf, hvlen, huv⟩
    · decide
    · exact mem_F5_of_infix (ih v hvinf (le_trans hvlen hlen)) huv hlen

/-! ## The length-four exclusion and the length-three palindrome -/

/-- The length-four part of the finite certificate is completely oriented:
the reversal of none of its length-four words is itself in the certificate. -/
theorem F5_no_reversal_pair_length_four :
    ∀ u ∈ F5, u.length = 4 → u.reverse ∉ F5 := by
  decide

/-- Every canonical Padovan factor of length at least four has a forbidden
reversal.  The only finite check is at length four; factor closure propagates
it to every larger length. -/
theorem reversal_forbidden_of_four_le (u : List Letter)
    (hu : InLanguage u) (hlen : 4 ≤ u.length) : ¬ InLanguage u.reverse := by
  obtain ⟨n, hun⟩ := hu
  let t := u.take 4
  have htlen : t.length = 4 := by
    simp only [t, List.length_take]
    omega
  have htu : t <:+: u := (List.take_prefix 4 u).isInfix
  have htn : t <:+: S^[n] [Letter.a] := htu.trans hun
  have htF : t ∈ F5 := factors_complete n t htn (by omega)
  intro hrev
  obtain ⟨m, hrev_m⟩ := hrev
  have htrev_u : t.reverse <:+: u.reverse := htu.reverse
  have htrev_m : t.reverse <:+: S^[m] [Letter.a] := htrev_u.trans hrev_m
  have htrevF : t.reverse ∈ F5 := factors_complete m t.reverse htrev_m (by simp [htlen])
  exact F5_no_reversal_pair_length_four t htF htlen htrevF

/-- The eighth iterate contains the palindrome `aba`. -/
theorem iterate_eight :
    S^[8] [Letter.a] =
      [Letter.c, Letter.a, Letter.b, Letter.a, Letter.b, Letter.b, Letter.c] := by
  decide

/-- A length-three factor can remain unchanged by reversal, so no uniform
orientation readout is possible at length three. -/
theorem length_three_orientation_ambiguity :
    ∃ u : List Letter, InLanguage u ∧ u.length = 3 ∧ u.reverse = u := by
  refine ⟨[Letter.a, Letter.b, Letter.a], ?_, by decide, by decide⟩
  refine ⟨8, ?_⟩
  rw [iterate_eight]
  exact ⟨[Letter.c], [Letter.b, Letter.b, Letter.c], rfl⟩

end FourTickOrientation.Cubic
