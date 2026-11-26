module
public import Mathlib
public import FourTickWords

@[expose] public section
/-!
# FourTickQuartic — the factor language of the quartic substitution, up to length four

The proof library for statements 2–4 of `Challenge.lean`. The definitions `Letter`, `s`, `S`,
`InLanguage`, `InLanguageFrom` are those of `Challenge.lean`, character for character.

* The window lemma (`infix_window`), as for the cubic substitution.
* The certificate `C4`, 72 words of length `≤ 4` (1 + 4 + 13 + 22 + 32 by length), packed into a
  bit mask indexed by a base-5 word code (`inCert`). Two kernel checks by `decide +kernel` over the
  341 words of length `≤ 4` (by kernel reduction alone): `closed_check` (every length-`≤ 4` window of the
  image of a certified word is certified) and `rev_check` (no certified word of length 4 has a
  certified reversal). `factors_complete`: every factor of length `≤ 4` of every iterate is
  certified (used only as an upper bound on the factor set).
* `reversal_forbidden_of_four_le`; `S^[11] [a] = d a b a b b c` contains `a b a`.
* Seed independence ingredients: every letter occurs in an iterate of `a` and `a` occurs in an
  iterate of every letter (`letter_in_a_iterate`, `a_in_letter_iterate`), and `language_mono`.

Provenance: copied from the author's development repository, `PdtQuarticFourTick.lean`
(`PDT.QuarticFourTick`). Statements and proofs are unchanged; the namespace is
`FourTickOrientation.Quartic`, `PDT.Padovan.infix_append_split` is replaced by the identical
`FourTickOrientation.infix_append_split`, the derived `Repr` instance of `Letter` is dropped (no
proof uses it), the module-system header is added, and the theorems `inLanguageFrom_iff`,
`exact_orientation_threshold_four` and `exact_orientation_threshold_four_any_seed` are in
`Solution.lean` (their proofs unchanged).
-/

namespace FourTickOrientation.Quartic

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

@[simp] theorem S_nil : S [] = [] := rfl

@[simp] theorem S_cons (x : Letter) (w : List Letter) : S (x :: w) = s x ++ S w := rfl

/-! ## Block lengths -/

theorem one_le_length_s (x : Letter) : 1 ≤ (s x).length := by cases x <;> simp [s]

theorem length_s_le (x : Letter) : (s x).length ≤ 2 := by cases x <;> simp [s]

theorem length_S_le : ∀ w : List Letter, (S w).length ≤ 2 * w.length := by
  intro w
  induction w with
  | nil => simp
  | cons x w ih =>
    have hx := length_s_le x
    rw [S_cons, List.length_append, List.length_cons]
    omega

/-! ## The window lemma (as in `FourTickCubic`, for the 4-letter alphabet) -/

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

/-- The 72 words of length ≤ 4 forming the factor certificate
(1 + 4 + 13 + 22 + 32 by length). -/
def C4 : List (List Letter) := [
  [],
  [a], [b], [c], [d],
  [a, b], [b, a], [b, b], [b, c], [b, d], [c, a], [c, b], [c, c], [c, d], [d, a], [d, b],
  [d, c], [d, d],
  [a, b, a], [a, b, b], [a, b, c], [a, b, d], [b, a, b], [b, b, c], [b, c, a], [b, c, b],
  [b, c, c], [b, c, d], [b, d, a], [c, a, b], [c, b, c], [c, c, d], [c, d, a], [c, d, b],
  [c, d, c], [c, d, d], [d, a, b], [d, b, c], [d, c, d], [d, d, a],
  [a, b, a, b], [a, b, b, c], [a, b, c, d], [a, b, d, a], [b, a, b, b], [b, b, c, a],
  [b, b, c, b], [b, b, c, c], [b, b, c, d], [b, c, a, b], [b, c, b, c], [b, c, c, d],
  [b, c, d, a], [b, c, d, d], [b, d, a, b], [c, a, b, b], [c, b, c, c], [c, c, d, a],
  [c, c, d, b], [c, c, d, c], [c, c, d, d], [c, d, a, b], [c, d, b, c], [c, d, c, d],
  [c, d, d, a], [d, a, b, a], [d, a, b, b], [d, a, b, c], [d, a, b, d], [d, b, c, c],
  [d, c, d, d], [d, d, a, b]
]

/-- Cross-check against the computed factor counts: 72 = 1+4+13+22+32. -/
theorem C4_length : C4.length = 72 := by decide +kernel

/-- Cross-check: 22 certificate words of length three. -/
theorem C4_length_three : (C4.filter (fun w => w.length == 3)).length = 22 := by
  decide +kernel

/-- Cross-check: 32 certificate words of length four. -/
theorem C4_length_four : (C4.filter (fun w => w.length == 4)).length = 32 := by
  decide +kernel

/-- Cross-check: 6 certificate words of length three are palindromes. -/
theorem C4_palindromes_three :
    (C4.filter (fun w => w.length == 3 && w.reverse == w)).length = 6 := by
  decide +kernel

/-- Letter index `0..3`. -/
def idx : Letter → ℕ
  | a => 0 | b => 1 | c => 2 | d => 3

/-- Base-5 word code (digit 0 marks the end of the word). -/
def code : List Letter → ℕ
  | [] => 0
  | x :: w => idx x + 1 + 5 * code w

/-- The certificate packed as a bit mask: bit `code w` is set for `w ∈ C4`. -/
def mask : ℕ := C4.foldr (fun w acc => acc ||| (1 <<< code w)) 0

/-- Certificate membership, one bit lookup. -/
def inCert (w : List Letter) : Bool := mask.testBit (code w)

/-- The four letters. -/
def allLetters : List Letter := [a, b, c, d]

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

/-- Every length-≤4 window of `S v`, at any start position `< 9`. -/
def windowsOK (v : List Letter) : Bool :=
  (List.range 9).all fun i => (List.range 5).all fun j => inCert (((S v).drop i).take j)

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

theorem inCert_a : inCert [a] = true := by decide +kernel

/-- A short factor of the image of a certified word is certified. -/
theorem inCert_of_infix {v u : List Letter} (hv : inCert v = true) (hvlen : v.length ≤ 4)
    (huv : u <:+: S v) (hlen : u.length ≤ 4) : inCert u = true := by
  have hall := List.all_eq_true.mp closed_check v (mem_words 4 v hvlen)
  rw [hv] at hall
  simp only [Bool.not_true, Bool.false_or, windowsOK, List.all_eq_true, List.mem_range] at hall
  have hSv : (S v).length ≤ 8 := le_trans (length_S_le v) (by omega)
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
iterate `S^[n] [a]` is certified. -/
theorem factors_complete : ∀ (n : ℕ) (u : List Letter),
    u <:+: S^[n] [a] → u.length ≤ 4 → inCert u = true := by
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
        have hx : x ∈ ([a] : List Letter) :=
          List.IsInfix.mem (List.mem_singleton_self x) hu
        rw [List.mem_singleton] at hx
        subst hx
        exact inCert_a
      | cons y t' =>
        simp only [List.length_cons, List.length_nil] at hlen
        omega
  | succ m ih =>
    intro u hu hlen
    rw [Function.iterate_succ_apply'] at hu
    rcases infix_window (S^[m] [a]) u hu with rfl | ⟨v, hvinf, hvlen, huv⟩
    · exact inCert_nil
    · exact inCert_of_infix (ih v hvinf (le_trans hvlen hlen)) (by omega) huv hlen

/-- No certified length-four word has a certified reversal. -/
theorem inCert_reverse_false {u : List Letter} (hlen : u.length = 4) (hu : inCert u = true) :
    inCert u.reverse = false := by
  have h := List.all_eq_true.mp rev_check u (mem_words 4 u (by omega))
  simp only [hlen, hu] at h
  simpa using h

/-- Every quartic factor of length at least four has a forbidden reversal.  The
only finite check is at length four; factor closure propagates it. -/
theorem reversal_forbidden_of_four_le (u : List Letter)
    (hu : InLanguage u) (hlen : 4 ≤ u.length) : ¬ InLanguage u.reverse := by
  obtain ⟨n, hun⟩ := hu
  let t := u.take 4
  have htlen : t.length = 4 := by
    simp only [t, List.length_take]
    omega
  have htu : t <:+: u := (List.take_prefix 4 u).isInfix
  have htn : t <:+: S^[n] [a] := htu.trans hun
  have htC : inCert t = true := factors_complete n t htn (by omega)
  intro hrev
  obtain ⟨m, hrev_m⟩ := hrev
  have htrev_u : t.reverse <:+: u.reverse := htu.reverse
  have htrev_m : t.reverse <:+: S^[m] [a] := htrev_u.trans hrev_m
  have htrevC : inCert t.reverse = true :=
    factors_complete m t.reverse htrev_m (by simp [htlen])
  rw [inCert_reverse_false htlen htC] at htrevC
  exact Bool.false_ne_true htrevC

/-- The eleventh iterate from `a` (7 letters); positions 1..3 read `a b a`. -/
theorem iterate_eleven : S^[11] [a] = [d, a, b, a, b, b, c] := by
  decide

/-- A length-three factor can be its own reversal, so no uniform orientation
readout is possible at length three. -/
theorem length_three_orientation_ambiguity :
    ∃ u : List Letter, InLanguage u ∧ u.length = 3 ∧ u.reverse = u := by
  refine ⟨[a, b, a], ?_, by decide, by decide⟩
  refine ⟨11, ?_⟩
  rw [iterate_eleven]
  exact ⟨[d], [b, b, c], rfl⟩

/-! ## Seed independence: the ingredients -/

theorem S_append : ∀ w₁ w₂ : List Letter, S (w₁ ++ w₂) = S w₁ ++ S w₂
  | [], _ => rfl
  | x :: w₁, w₂ => by
    rw [List.cons_append, S_cons, S_cons, S_append w₁ w₂, List.append_assoc]

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

/-- Every letter occurs in an iterate from `a`. -/
theorem letter_in_a_iterate : ∀ x : Letter, ∃ k, [x] <:+: S^[k] [a] := by
  intro x
  cases x
  exacts [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]

/-- `a` occurs in an iterate from every letter. -/
theorem a_in_letter_iterate : ∀ x : Letter, ∃ k, [a] <:+: S^[k] [x] := by
  intro x
  cases x
  exacts [⟨0, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩]

end FourTickOrientation.Quartic
