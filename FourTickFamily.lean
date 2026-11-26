module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.SplitIfs

@[expose] public section
/-!
# FourTickFamily — the factor languages of the substitutions of `xⁿ − x − 1`, `n ≥ 3`, up to length four

The proof library for statements 1–2 of `Challenge.lean`. The definitions `s`, `S`, `InLanguage`,
`InLanguageFrom` are those of `Challenge.lean`, character for character. For every `n ≥ 3`, `σₙ` is
the substitution `i ↦ i+1` (`1 ≤ i < n`), `n ↦ 1 2` on the letters `1, …, n`; `n = 3` is the cubic
Padovan substitution and `n = 4` the quartic substitution.

The certificate is parametric in `n`: no enumeration of words, so one proof covers every `n ≥ 3`.

* `take_S`: every image block is nonempty, so the first `k` letters of `S n xs` depend only on
  the first `j ≥ k` letters of `xs`.
* `Cert n`: an explicit index-rule predicate on words of length `≤ 4` (rules `L`, `P2`, `P3`,
  `P4`). It is used only as an UPPER bound on the factor set. (That it equals the factor set at
  lengths 1–4 was checked by computation for `n = 3, …, 40`; that is not formalized.)
* `G n w`: the length-`≤ 4` prefix of every suffix of `w` is certified. `G n [1]` holds and `G` is
  preserved by `S n` (`G_S`), via the symbolic case analysis `closure`, discharged by `omega` on
  index arithmetic. Hence every length-four factor is certified (`factors_complete`).
* `cert_reverse`: no certified length-four word has a certified reversal (a second `omega` case
  analysis). Factor closure (take the length-four prefix) gives `reversal_forbidden_of_four_le`.
* `inLanguage_one_two_one`: `1 2 1` is a factor, for every `n ≥ 3`, by an explicit chain of iterates
  (`iterate_shift`: below the top letter, `S n` is the shift `i ↦ i+1`).

Provenance: copied from the author's development repository, `PdtFamilyFourTick.lean`
(`PDT.FamilyFourTick`). Statements and proofs are unchanged; the namespace is
`FourTickOrientation.Family`, the imports are the source's (`Mathlib.Logic.Function.Iterate`,
`Mathlib.Tactic.SplitIfs`; under all of `Mathlib` the simp set differs and one `simp` call of
`closure` no longer closes its goal), the module-system header is added, the
docstrings of `s`, `S`, `InLanguage`, `InLanguageFrom` are reworded, `InLanguageFrom` is moved to the
top, the source's `#print axioms` lines are dropped (they are in `Axioms.lean`), and the theorems
`exact_orientation_threshold_four` and `inLanguageFrom_iff` are in `Solution.lean` (their proofs
unchanged).

Pure combinatorics on words.
-/

namespace FourTickOrientation.Family

/-! ## The substitution -/

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

@[simp] theorem S_nil (n : ℕ) : S n [] = [] := rfl

@[simp] theorem S_cons (n x : ℕ) (w : List ℕ) : S n (x :: w) = s n x ++ S n w := rfl

theorem S_append (n : ℕ) : ∀ a b : List ℕ, S n (a ++ b) = S n a ++ S n b
  | [], _ => rfl
  | x :: a, b => by simp [S_append n a b, List.append_assoc]


/-! ## Image prefixes depend only on preimage prefixes -/

/-- Every image block is nonempty, so the first `k` letters of `S n xs` are
determined by the first `j ≥ k` letters of `xs`. -/
theorem take_S (n : ℕ) : ∀ (xs : List ℕ) (k j : ℕ), k ≤ j →
    (S n xs).take k = (S n (xs.take j)).take k := by
  intro xs
  induction xs with
  | nil => intro k j _; simp
  | cons x xs ih =>
    intro k j hkj
    rcases j with _ | j
    · have hk : k = 0 := by omega
      subst hk
      simp
    · rw [List.take_succ_cons, S_cons, S_cons]
      unfold s
      split_ifs with hx
      · rcases k with _ | k
        · simp
        · simp only [List.cons_append, List.nil_append, List.take_succ_cons]
          rw [ih k j (by omega)]
      · rcases k with _ | _ | k
        · simp
        · simp
        · simp only [List.cons_append, List.nil_append, List.take_succ_cons]
          rw [ih k j (by omega)]

/-! ## The parametric certificate -/

/-- A letter. -/
def L (n a : ℕ) : Prop := 1 ≤ a ∧ a ≤ n

/-- `y` is the cyclic successor of `x` (`n` is followed by `1`). -/
def step (n x y : ℕ) : Prop := (x < n ∧ y = x + 1) ∨ (x = n ∧ y = 1)

/-- Two-letter rule: `1` is always followed by `2`. -/
def P2 (n a b : ℕ) : Prop := L n a ∧ L n b ∧ (2 ≤ a ∨ b = 2)

/-- Three-letter rule: the third letter is the cyclic successor of the second,
unless the first two letters form an up-step `a, a+1`. -/
def P3 (n a b c : ℕ) : Prop := P2 n a b ∧ P2 n b c ∧ (step n b c ∨ b = a + 1)

/-- Four-letter rule: after an up-step `b, b+1` in positions 2–3, the fourth letter
is free when `a = b` or `(a, b) = (n, 1)`; it may be the successor of `c` when
`a, b` is itself an up-step; it may repeat `c` when `a ≥ 2`; nothing else. -/
def P4 (n a b c d : ℕ) : Prop := P3 n a b c ∧ P3 n b c d ∧
  (c = b + 1 → a = b ∨ (a = n ∧ b = 1) ∨ (step n c d ∧ b = a + 1) ∨ (d = c ∧ 2 ≤ a))

/-- The certificate: words of length `≤ 4` satisfying the index rules. -/
def Cert (n : ℕ) : List ℕ → Prop
  | [] => True
  | [a] => L n a
  | [a, b] => P2 n a b
  | [a, b, c] => P3 n a b c
  | [a, b, c, d] => P4 n a b c d
  | _ :: _ :: _ :: _ :: _ :: _ => False

/-- The length-`≤4` prefix of every suffix is certified. -/
def G (n : ℕ) : List ℕ → Prop
  | [] => True
  | x :: xs => Cert n ((x :: xs).take 4) ∧ G n xs

theorem G_cons (n x : ℕ) (xs : List ℕ) :
    G n (x :: xs) ↔ Cert n ((x :: xs).take 4) ∧ G n xs := Iff.rfl

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Closure (symbolic case analysis).** If `x :: r` (with `|r| ≤ 3`) is certified,
then so is the length-`≤4` prefix of every nonempty suffix of `s x` followed by
`S r`. -/
theorem closure (n : ℕ) (hn : 3 ≤ n) (x : ℕ) (r : List ℕ) (hr : r.length ≤ 3)
    (h : Cert n (x :: r)) :
    (x < n → Cert n (((x + 1) :: S n r).take 4)) ∧
    (¬ x < n → Cert n ((1 :: 2 :: S n r).take 4) ∧ Cert n ((2 :: S n r).take 4)) := by
  rcases r with _ | ⟨y, _ | ⟨z, _ | ⟨w, _ | ⟨v, r⟩⟩⟩⟩
  rotate_left 4
  · simp at hr
  all_goals
    simp only [Cert, L, P2, P3, P4, step, S_cons, S_nil, s] at h ⊢
    refine ⟨fun hx => ?_, fun hx => ⟨?_, ?_⟩⟩ <;>
      (try split_ifs) <;>
      simp only [Cert, L, P2, P3, P4, step, List.cons_append, List.nil_append, List.append_nil,
        List.take_succ_cons, List.take_nil, List.take_zero, true_or, or_true, and_true,
        true_and] <;> omega

/-- `G` is preserved by the substitution. -/
theorem G_S (n : ℕ) (hn : 3 ≤ n) : ∀ w : List ℕ, G n w → G n (S n w) := by
  intro w
  induction w with
  | nil => intro _; trivial
  | cons x xs ih =>
    intro h
    rw [G_cons] at h
    obtain ⟨hx, hxs⟩ := h
    have hc : Cert n (x :: xs.take 3) := by simpa [List.take_succ_cons] using hx
    have hcl := closure n hn x (xs.take 3) (by simp only [List.length_take]; omega) hc
    rw [S_cons]
    unfold s
    split_ifs with hxn
    · show G n ((x + 1) :: S n xs)
      rw [G_cons]
      refine ⟨?_, ih hxs⟩
      have h1 := hcl.1 hxn
      rw [List.take_succ_cons] at h1 ⊢
      rwa [take_S n xs 3 3 (Nat.le_refl 3)]
    · show G n (1 :: 2 :: S n xs)
      rw [G_cons, G_cons]
      obtain ⟨h1, h2⟩ := hcl.2 hxn
      refine ⟨?_, ?_, ih hxs⟩
      · rw [List.take_succ_cons, List.take_succ_cons] at h1 ⊢
        rwa [take_S n xs 2 3 (by omega)]
      · rw [List.take_succ_cons] at h2 ⊢
        rwa [take_S n xs 3 3 (Nat.le_refl 3)]

theorem G_seed (n : ℕ) (hn : 3 ≤ n) : G n [1] := by
  refine ⟨?_, trivial⟩
  show L n 1
  exact ⟨Nat.le_refl 1, by omega⟩

theorem G_iterate (n : ℕ) (hn : 3 ≤ n) : ∀ k : ℕ, G n ((S n)^[k] [1])
  | 0 => G_seed n hn
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact G_S n hn _ (G_iterate n hn k)

theorem G_suffix (n : ℕ) : ∀ (p q : List ℕ), G n (p ++ q) → G n q
  | [], _, h => h
  | _ :: p, q, h => G_suffix n p q h.2

/-- Every length-4 infix of a `G`-word is certified. -/
theorem cert_of_G (n : ℕ) {w u : List ℕ} (hw : G n w) (hu : u <:+: w)
    (hlen : u.length = 4) : Cert n u := by
  obtain ⟨p, q, rfl⟩ := hu
  have h := G_suffix n p (u ++ q) (by simpa [List.append_assoc] using hw)
  cases u with
  | nil => simp at hlen
  | cons a u' =>
    rw [List.cons_append, G_cons, ← List.cons_append, List.take_left' hlen] at h
    exact h.1

/-- **FACTOR COMPLETENESS AT LENGTH 4.** Every length-4 factor is certified. -/
theorem factors_complete (n : ℕ) (hn : 3 ≤ n) (u : List ℕ) (hu : InLanguage n u)
    (hlen : u.length = 4) : Cert n u := by
  obtain ⟨k, hk⟩ := hu
  exact cert_of_G n (G_iterate n hn k) hk hlen

/-- **Orientation (symbolic case analysis).** No certified length-4 word has a
certified reversal. -/
theorem cert_reverse (n : ℕ) (hn : 3 ≤ n) (u : List ℕ) (hlen : u.length = 4)
    (hu : Cert n u) : ¬ Cert n u.reverse := by
  match u, hlen with
  | [a, b, c, d], _ =>
    show ¬ Cert n [d, c, b, a]
    intro hr
    simp only [Cert, L, P2, P3, P4, step] at hu hr
    omega

/-! ## The threshold -/

/-- Every factor of length at least four has a forbidden reversal. -/
theorem reversal_forbidden_of_four_le (n : ℕ) (hn : 3 ≤ n) (u : List ℕ)
    (hu : InLanguage n u) (hlen : 4 ≤ u.length) : ¬ InLanguage n u.reverse := by
  obtain ⟨k, hk⟩ := hu
  let t := u.take 4
  have htlen : t.length = 4 := by
    simp only [t, List.length_take]
    omega
  have htu : t <:+: u := (List.take_prefix 4 u).isInfix
  have htC : Cert n t := factors_complete n hn t ⟨k, htu.trans hk⟩ htlen
  intro hrev
  obtain ⟨m, hm⟩ := hrev
  have htrevC : Cert n t.reverse :=
    factors_complete n hn t.reverse ⟨m, htu.reverse.trans hm⟩ (by simp [htlen])
  exact cert_reverse n hn t htlen htC htrevC

/-! ## The length-three palindrome -/

theorem S_infix (n : ℕ) {u w : List ℕ} (h : u <:+: w) : S n u <:+: S n w := by
  obtain ⟨p, q, rfl⟩ := h
  exact ⟨S n p, S n q, by rw [S_append, S_append]⟩

theorem inLanguage_S {n : ℕ} {u : List ℕ} (h : InLanguage n u) : InLanguage n (S n u) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by rw [Function.iterate_succ_apply']; exact S_infix n hk⟩

theorem inLanguage_iterate {n : ℕ} : ∀ (k : ℕ) {u : List ℕ}, InLanguage n u →
    InLanguage n ((S n)^[k] u)
  | 0, _, h => h
  | k + 1, _, h => by
    rw [Function.iterate_succ_apply']
    exact inLanguage_S (inLanguage_iterate k h)

theorem inLanguage_infix {n : ℕ} {u w : List ℕ} (hw : InLanguage n w) (h : u <:+: w) :
    InLanguage n u := by
  obtain ⟨k, hk⟩ := hw
  exact ⟨k, h.trans hk⟩

/-- Below the top letter the substitution is the shift `i ↦ i+1`. -/
theorem S_map_succ (n : ℕ) : ∀ w : List ℕ, (∀ x ∈ w, x < n) → S n w = w.map (· + 1)
  | [], _ => rfl
  | x :: w, h => by
    have hx : x < n := h x (List.mem_cons_self ..)
    rw [S_cons, S_map_succ n w (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    simp [s, hx]

theorem iterate_shift (n : ℕ) : ∀ (k : ℕ) (w : List ℕ), (∀ x ∈ w, x + k ≤ n) →
    (S n)^[k] w = w.map (· + k)
  | 0, w, _ => by simp
  | k + 1, w, h => by
    rw [Function.iterate_succ_apply, S_map_succ n w (fun x hx => by have := h x hx; omega),
      iterate_shift n k (w.map (· + 1)) (by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        have := h x hx
        omega), List.map_map]
    congr 1
    funext x
    simp only [Function.comp_apply]
    omega

/-- `1 2 1` is a factor, for every `n ≥ 3`. -/
theorem inLanguage_one_two_one (n : ℕ) (hn : 3 ≤ n) : InLanguage n [1, 2, 1] := by
  have h0 : InLanguage n [1] := ⟨0, List.infix_refl _⟩
  -- `[1] ↦ⁿ⁻¹ [n] ↦ [1,2]`
  have h1 : InLanguage n [n] := by
    have := inLanguage_iterate (n - 1) h0
    rwa [iterate_shift n (n - 1) [1] (by simp; omega), List.map_cons, List.map_nil,
      show 1 + (n - 1) = n by omega] at this
  have h2 : InLanguage n [1, 2] := by
    have := inLanguage_S h1
    simpa [s] using this
  -- `[1,2] ↦ⁿ⁻² [n-1, n] ↦ [n, 1, 2] ↦ [1, 2, 2, 3]`
  have h3 : InLanguage n [n - 1, n] := by
    have := inLanguage_iterate (n - 2) h2
    rwa [iterate_shift n (n - 2) [1, 2] (by simp; omega), List.map_cons, List.map_cons,
      List.map_nil, show 1 + (n - 2) = n - 1 by omega, show 2 + (n - 2) = n by omega] at this
  have h4 : InLanguage n [n, 1, 2] := by
    have := inLanguage_S h3
    have e1 : n - 1 < n := by omega
    simpa [s, e1, show n - 1 + 1 = n by omega] using this
  have h5 : InLanguage n [1, 2, 2, 3] := by
    have := inLanguage_S h4
    have e1 : 1 < n := by omega
    have e2 : 2 < n := by omega
    simpa [s, e1, e2] using this
  -- `[2,2] ↦ⁿ⁻² [n, n] ↦ [1, 2, 1, 2]`
  have h6 : InLanguage n [2, 2] := inLanguage_infix h5 ⟨[1], [3], rfl⟩
  have h7 : InLanguage n [n, n] := by
    have := inLanguage_iterate (n - 2) h6
    rwa [iterate_shift n (n - 2) [2, 2] (by simp; omega), List.map_cons, List.map_cons,
      List.map_nil, show 2 + (n - 2) = n by omega] at this
  have h8 : InLanguage n [1, 2, 1, 2] := by
    have := inLanguage_S h7
    simpa [s] using this
  exact inLanguage_infix h8 ⟨[], [2], rfl⟩

/-- A length-three factor can be its own reversal. -/
theorem length_three_orientation_ambiguity (n : ℕ) (hn : 3 ≤ n) :
    ∃ u : List ℕ, InLanguage n u ∧ u.length = 3 ∧ u.reverse = u :=
  ⟨[1, 2, 1], inLanguage_one_two_one n hn, rfl, rfl⟩

end FourTickOrientation.Family
