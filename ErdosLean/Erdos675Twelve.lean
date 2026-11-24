import FormalConjecturesUtil

namespace Erdos675

/--
`IsTranslation A n t` says that $t \geq 1$ and, for all $1 \leq a \leq n$, $a \in A$ if and
only if $a + t \in A$. Copied verbatim from `FormalConjectures/ErdosProblems/675.lean` on
formal-conjectures main, since the pinned commit has no file for problem 675.
-/
def IsTranslation (A : Set ℕ) (n t : ℕ) : Prop :=
  1 ≤ t ∧ ∀ a : ℕ, 1 ≤ a → a ≤ n → (a ∈ A ↔ a + t ∈ A)

end Erdos675

/-!
# Erdős Problem 675: infinitely many `12`-shifts of the sums of two squares

Let `E = {x ^ 2 + y ^ 2 : x, y ∈ ℕ}`, so `E ∩ [1, 12] = {1, 2, 4, 5, 8, 9, 10}`.
We prove `erdos_675.variants.sumsOfTwoSquares_infinite_twelve_shifts`: the set
`{t | IsTranslation E 12 t}` is infinite. Hence the same holds for every `n ≤ 12`
(`erdos_675.variants.sumsOfTwoSquares_infinite_shifts_of_le_twelve`), in particular for `n = 9`.
The statements use `Erdos675.IsTranslation` from `FormalConjectures/ErdosProblems/675.lean`
and have the same form as the `8`-shift variant
`erdos_675.variants.sumsOfTwoSquares_infinite_eight_shifts`.

Let `u ^ 2 = 2 W ^ 2 + 1` with `W ≥ 1`. Put `x = 16 u ^ 2 W ^ 2 - 1` and
`t = x ^ 2 - 1 = 256 u ^ 4 W ^ 4 - 32 u ^ 2 W ^ 2`. Then
* `t + 1 = x ^ 2`, `t + 2 = x ^ 2 + 1`, `t + 5 = x ^ 2 + 2 ^ 2`, `t + 10 = x ^ 2 + 3 ^ 2`;
* `t + 9 = (x - 2) ^ 2 + (8 u W) ^ 2` (no Pell condition needed);
* `t + 8 = (x - 1) ^ 2 + (8 W ^ 2 + 2) ^ 2` (uses `u ^ 2 = 2 W ^ 2 + 1`, cofactor `32 W ^ 2`);
* `t + 4 = (32 W ^ 4 + 8 W ^ 2 - 2) ^ 2 + (16 u W ^ 2) ^ 2`
  (uses the Pell equation, cofactor `512 W ^ 6 + 256 W ^ 4 u ^ 2 - 32 W ^ 2`).
Since `32 ∣ t`, the numbers `t + 3, t + 6, t + 7, t + 11, t + 12` are `3, 6, 7, 11, 12` modulo `16`,
and no sum of two squares is. The map `(u, W) ↦ (3 u + 4 W, 2 u + 3 W)` preserves
`u ^ 2 - 2 W ^ 2` and increases `W`, so `(3, 2)` gives arbitrarily large solutions.
-/

namespace ErdosLean.Erdos675Twelve

open _root_.Erdos675

/-- An integer identity `m = a ^ 2 + b ^ 2` makes `m` a sum of two squares of naturals. -/
lemma mem_of_int {m : ℕ} (a b : ℤ) (h : (m : ℤ) = a ^ 2 + b ^ 2) :
    m ∈ {m : ℕ | ∃ x y : ℕ, m = x ^ 2 + y ^ 2} :=
  ⟨a.natAbs, b.natAbs, by zify; simpa [sq_abs] using h⟩

/-- A sum of two squares is not `3`, `6`, `7`, `11` or `12` modulo `16`. -/
lemma not_mem_of_mod {m : ℕ}
    (h : m % 16 = 3 ∨ m % 16 = 6 ∨ m % 16 = 7 ∨ m % 16 = 11 ∨ m % 16 = 12) :
    m ∉ {m : ℕ | ∃ x y : ℕ, m = x ^ 2 + y ^ 2} := by
  rintro ⟨x, y, rfl⟩
  have key : ∀ a b : ZMod 16, a ^ 2 + b ^ 2 ≠ 3 ∧ a ^ 2 + b ^ 2 ≠ 6 ∧ a ^ 2 + b ^ 2 ≠ 7 ∧
      a ^ 2 + b ^ 2 ≠ 11 ∧ a ^ 2 + b ^ 2 ≠ 12 := by
    decide
  have hc : ((x ^ 2 + y ^ 2 : ℕ) : ZMod 16) = (((x ^ 2 + y ^ 2) % 16 : ℕ) : ZMod 16) :=
    (ZMod.natCast_mod _ 16).symm
  push_cast at hc
  obtain ⟨h3, h6, h7, h11, h12⟩ := key x y
  rcases h with h | h | h | h | h <;> rw [h] at hc <;> simp_all

/-- Every solution of `u ^ 2 = 2 W ^ 2 + 1` with `W ≥ 1` gives the `12`-shift
`t = 256 u ^ 4 W ^ 4 - 32 u ^ 2 W ^ 2`, written here as `t + 32 u ^ 2 W ^ 2 = 256 u ^ 4 W ^ 4`. -/
lemma isTranslation_of_pell {u W t : ℕ} (hP : u ^ 2 = 2 * W ^ 2 + 1) (hW : 1 ≤ W)
    (hT : t + 32 * u ^ 2 * W ^ 2 = 256 * u ^ 4 * W ^ 4) :
    IsTranslation {m : ℕ | ∃ x y : ℕ, m = x ^ 2 + y ^ 2} 12 t := by
  have hP' : (u : ℤ) ^ 2 = 2 * (W : ℤ) ^ 2 + 1 := by exact_mod_cast hP
  have hT' : (t : ℤ) + 32 * (u : ℤ) ^ 2 * (W : ℤ) ^ 2 = 256 * (u : ℤ) ^ 4 * (W : ℤ) ^ 4 := by
    exact_mod_cast hT
  have h32 : 32 ∣ t :=
    Int.natCast_dvd_natCast.mp ⟨8 * (u : ℤ) ^ 4 * (W : ℤ) ^ 4 - (u : ℤ) ^ 2 * (W : ℤ) ^ 2,
      by linear_combination hT'⟩
  have hu : 1 ≤ u := by nlinarith
  have hp : 1 ≤ u ^ 2 * W ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have ht : 1 ≤ t := by
    have h4 : u ^ 4 * W ^ 4 = (u ^ 2 * W ^ 2) ^ 2 := by ring
    rw [mul_assoc 256, h4, mul_assoc 32] at hT
    nlinarith
  refine ⟨ht, fun a ha1 ha12 ↦ ?_⟩
  interval_cases a
  · -- 1 = 1 ^ 2 + 0 ^ 2, t + 1 = x ^ 2
    exact iff_of_true ⟨1, 0, rfl⟩
      (mem_of_int (16 * u ^ 2 * W ^ 2 - 1) 0 (by push_cast; linear_combination hT'))
  · -- 2 = 1 ^ 2 + 1 ^ 2, t + 2 = x ^ 2 + 1 ^ 2
    exact iff_of_true ⟨1, 1, rfl⟩
      (mem_of_int (16 * u ^ 2 * W ^ 2 - 1) 1 (by push_cast; linear_combination hT'))
  · exact iff_of_false (not_mem_of_mod (by omega)) (not_mem_of_mod (by omega))
  · -- 4 = 2 ^ 2 + 0 ^ 2, t + 4 = (32 W ^ 4 + 8 W ^ 2 - 2) ^ 2 + (16 u W ^ 2) ^ 2
    exact iff_of_true ⟨2, 0, rfl⟩
      (mem_of_int (32 * W ^ 4 + 8 * W ^ 2 - 2) (16 * u * W ^ 2)
        (by push_cast
            linear_combination hT' +
              (512 * (W : ℤ) ^ 6 + 256 * (W : ℤ) ^ 4 * (u : ℤ) ^ 2 - 32 * (W : ℤ) ^ 2) * hP'))
  · -- 5 = 2 ^ 2 + 1 ^ 2, t + 5 = x ^ 2 + 2 ^ 2
    exact iff_of_true ⟨2, 1, rfl⟩
      (mem_of_int (16 * u ^ 2 * W ^ 2 - 1) 2 (by push_cast; linear_combination hT'))
  · exact iff_of_false (not_mem_of_mod (by omega)) (not_mem_of_mod (by omega))
  · exact iff_of_false (not_mem_of_mod (by omega)) (not_mem_of_mod (by omega))
  · -- 8 = 2 ^ 2 + 2 ^ 2, t + 8 = (x - 1) ^ 2 + (8 W ^ 2 + 2) ^ 2
    exact iff_of_true ⟨2, 2, rfl⟩
      (mem_of_int (16 * u ^ 2 * W ^ 2 - 2) (8 * W ^ 2 + 2)
        (by push_cast; linear_combination hT' + 32 * (W : ℤ) ^ 2 * hP'))
  · -- 9 = 3 ^ 2 + 0 ^ 2, t + 9 = (x - 2) ^ 2 + (8 u W) ^ 2
    exact iff_of_true ⟨3, 0, rfl⟩
      (mem_of_int (16 * u ^ 2 * W ^ 2 - 3) (8 * u * W) (by push_cast; linear_combination hT'))
  · -- 10 = 3 ^ 2 + 1 ^ 2, t + 10 = x ^ 2 + 3 ^ 2
    exact iff_of_true ⟨3, 1, rfl⟩
      (mem_of_int (16 * u ^ 2 * W ^ 2 - 1) 3 (by push_cast; linear_combination hT'))
  · exact iff_of_false (not_mem_of_mod (by omega)) (not_mem_of_mod (by omega))
  · exact iff_of_false (not_mem_of_mod (by omega)) (not_mem_of_mod (by omega))

/-- The orbit of `(3, 2)` under `(u, W) ↦ (3 u + 4 W, 2 u + 3 W)` gives solutions of
`u ^ 2 = 2 W ^ 2 + 1` with `W` arbitrarily large. -/
lemma exists_pell (j : ℕ) : ∃ u W : ℕ, u ^ 2 = 2 * W ^ 2 + 1 ∧ 1 ≤ W ∧ j ≤ W := by
  induction j with
  | zero => exact ⟨3, 2, by norm_num, by norm_num, by norm_num⟩
  | succ j ih =>
    obtain ⟨u, W, h, h1, hj⟩ := ih
    exact ⟨3 * u + 4 * W, 2 * u + 3 * W, by linear_combination h, by omega, by nlinarith⟩

/-- There are infinitely many `12`-shifts of the sums of two squares. -/
theorem erdos_675.variants.sumsOfTwoSquares_infinite_twelve_shifts :
    {t : ℕ | IsTranslation {m : ℕ | ∃ x y : ℕ, m = x ^ 2 + y ^ 2} 12 t}.Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨N, hN⟩ ↦ ?_
  obtain ⟨u, W, hP, hW, hN1⟩ := exists_pell (N + 1)
  have hu : 1 ≤ u := by nlinarith
  have hWP : W ≤ u ^ 2 * W ^ 2 := by
    have h1 : W ≤ W ^ 2 := by nlinarith
    have h2 : 1 ≤ u ^ 2 := Nat.one_le_pow _ _ hu
    nlinarith
  have h4 : 256 * u ^ 4 * W ^ 4 = 256 * (u ^ 2 * W ^ 2) ^ 2 := by ring
  have h2 : 32 * u ^ 2 * W ^ 2 = 32 * (u ^ 2 * W ^ 2) := by ring
  generalize hPd : u ^ 2 * W ^ 2 = P at hWP h4 h2
  have hle : 32 * P + P ≤ 256 * P ^ 2 := by nlinarith
  have hT : (256 * P ^ 2 - 32 * P) + 32 * u ^ 2 * W ^ 2 = 256 * u ^ 4 * W ^ 4 := by
    rw [h4, h2]; omega
  have hmem := hN (isTranslation_of_pell hP hW hT)
  omega

/-- A shift for `n` is a shift for every `m ≤ n`. -/
lemma IsTranslation.mono {A : Set ℕ} {m n t : ℕ} (h : IsTranslation A n t) (hmn : m ≤ n) :
    IsTranslation A m t :=
  ⟨h.1, fun a ha1 ham ↦ h.2 a ha1 (ham.trans hmn)⟩

/-- Consequently there are infinitely many `n`-shifts for every `n ≤ 12`. -/
theorem erdos_675.variants.sumsOfTwoSquares_infinite_shifts_of_le_twelve {n : ℕ} (hn : n ≤ 12) :
    {t : ℕ | IsTranslation {m : ℕ | ∃ x y : ℕ, m = x ^ 2 + y ^ 2} n t}.Infinite :=
  erdos_675.variants.sumsOfTwoSquares_infinite_twelve_shifts.mono fun _ ht ↦
    IsTranslation.mono ht hn

/-- In particular there are infinitely many `9`-shifts. -/
theorem erdos_675.variants.sumsOfTwoSquares_infinite_nine_shifts :
    {t : ℕ | IsTranslation {m : ℕ | ∃ x y : ℕ, m = x ^ 2 + y ^ 2} 9 t}.Infinite :=
  erdos_675.variants.sumsOfTwoSquares_infinite_shifts_of_le_twelve (by norm_num)

end ErdosLean.Erdos675Twelve
