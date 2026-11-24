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
# Erdős Problem 675: infinitely many `8`-shifts of the sums of two squares

Let `E = {x ^ 2 + y ^ 2 : x, y ∈ ℕ}`. We prove
`erdos_675.variants.sumsOfTwoSquares_infinite_eight_shifts`: there are infinitely many `t ≥ 1`
with `a ∈ E ↔ a + t ∈ E` for all `1 ≤ a ≤ 8`, that is, `{t | IsTranslation E 8 t}` is infinite.

Let `u ^ 2 + 119 = 21 s ^ 2`, put `x = 2 s ^ 2 - 1` and `t = x ^ 2 - 1 = 4 s ^ 2 (s ^ 2 - 1)`.
The members `1, 2, 4, 5, 8` of `E ∩ [1, 8]` go to sums of two squares:
`t + 1 = x ^ 2`, `t + 2 = x ^ 2 + 1`, `t + 4 = (x - 1) ^ 2 + (2 s) ^ 2`, `t + 5 = x ^ 2 + 2 ^ 2`
and `t + 8 = (x - 21) ^ 2 + (2 u) ^ 2`. The last identity uses `4 u ^ 2 = 84 s ^ 2 - 476`.
Since `s ^ 2 (s ^ 2 - 1)` is even, `8 ∣ t`, so `t + 3`, `t + 6`, `t + 7` are `3, 6, 7` modulo
`8`, and a sum of two squares never is. The map `(u, s) ↦ (55 u + 252 s, 12 u + 55 s)` preserves
`u ^ 2 - 21 s ^ 2` and increases `s`, so `(35, 8)` gives arbitrarily large solutions.
This is the Pell device of Choudhry and Maji (Int. J. Number Theory 2024, arXiv:2310.13317).

The statement is not in formal-conjectures at the commit pinned in `lakefile.toml`, so it is
copied verbatim from the proposed variant in `FormalConjectures/ErdosProblems/675.lean`. It uses
`Erdos675.IsTranslation`, also copied verbatim (the pinned commit has no file for 675).
-/

namespace ErdosLean.Erdos675

open _root_.Erdos675

/-- An integer identity `m = a ^ 2 + b ^ 2` makes `m` a sum of two squares of naturals. -/
lemma mem_of_int {m : ℕ} (a b : ℤ) (h : (m : ℤ) = a ^ 2 + b ^ 2) :
    m ∈ {m : ℕ | ∃ x y : ℕ, m = x ^ 2 + y ^ 2} :=
  ⟨a.natAbs, b.natAbs, by zify; simpa [sq_abs] using h⟩

/-- A sum of two squares is not `3`, `6` or `7` modulo `8`. -/
lemma not_mem_of_mod {m : ℕ} (h : m % 8 = 3 ∨ m % 8 = 6 ∨ m % 8 = 7) :
    m ∉ {m : ℕ | ∃ x y : ℕ, m = x ^ 2 + y ^ 2} := by
  rintro ⟨x, y, rfl⟩
  have key : ∀ a b : ZMod 8, a ^ 2 + b ^ 2 ≠ 3 ∧ a ^ 2 + b ^ 2 ≠ 6 ∧ a ^ 2 + b ^ 2 ≠ 7 := by
    decide
  have hc : ((x ^ 2 + y ^ 2 : ℕ) : ZMod 8) = (((x ^ 2 + y ^ 2) % 8 : ℕ) : ZMod 8) :=
    (ZMod.natCast_mod _ 8).symm
  push_cast at hc
  obtain ⟨h3, h6, h7⟩ := key x y
  rcases h with h | h | h <;> rw [h] at hc <;> simp_all

/-- Every solution of `u ^ 2 + 119 = 21 s ^ 2` gives the `8`-shift `t = 4 s ^ 2 (s ^ 2 - 1)`,
written here as `t + 4 s ^ 2 = 4 s ^ 4`. -/
lemma isTranslation_of_pell {u s t : ℕ} (hP : u ^ 2 + 119 = 21 * s ^ 2)
    (hT : t + 4 * s ^ 2 = 4 * s ^ 4) :
    IsTranslation {m : ℕ | ∃ x y : ℕ, m = x ^ 2 + y ^ 2} 8 t := by
  have hP' : (u : ℤ) ^ 2 + 119 = 21 * (s : ℤ) ^ 2 := by exact_mod_cast hP
  have hT' : (t : ℤ) + 4 * (s : ℤ) ^ 2 = 4 * (s : ℤ) ^ 4 := by exact_mod_cast hT
  have h8 : 8 ∣ t := by
    obtain ⟨k, hk⟩ := Int.even_mul_pred_self ((s : ℤ) ^ 2)
    exact Int.natCast_dvd_natCast.mp ⟨k, by linear_combination hT' + 4 * hk⟩
  have hs : 3 ≤ s := by nlinarith
  refine ⟨by nlinarith, fun a ha1 ha8 ↦ ?_⟩
  interval_cases a
  · exact iff_of_true ⟨1, 0, rfl⟩
      (mem_of_int (2 * s ^ 2 - 1) 0 (by push_cast; linear_combination hT'))
  · exact iff_of_true ⟨1, 1, rfl⟩
      (mem_of_int (2 * s ^ 2 - 1) 1 (by push_cast; linear_combination hT'))
  · exact iff_of_false (not_mem_of_mod (by omega)) (not_mem_of_mod (by omega))
  · exact iff_of_true ⟨2, 0, rfl⟩
      (mem_of_int (2 * s ^ 2 - 2) (2 * s) (by push_cast; linear_combination hT'))
  · exact iff_of_true ⟨2, 1, rfl⟩
      (mem_of_int (2 * s ^ 2 - 1) 2 (by push_cast; linear_combination hT'))
  · exact iff_of_false (not_mem_of_mod (by omega)) (not_mem_of_mod (by omega))
  · exact iff_of_false (not_mem_of_mod (by omega)) (not_mem_of_mod (by omega))
  · exact iff_of_true ⟨2, 2, rfl⟩
      (mem_of_int (2 * s ^ 2 - 22) (2 * u) (by push_cast; linear_combination hT' - 4 * hP'))

/-- The orbit of `(35, 8)` under `(u, s) ↦ (55 u + 252 s, 12 u + 55 s)` gives solutions of
`u ^ 2 + 119 = 21 s ^ 2` with `s` arbitrarily large. -/
lemma exists_pell (j : ℕ) : ∃ u s : ℕ, u ^ 2 + 119 = 21 * s ^ 2 ∧ j ≤ s := by
  induction j with
  | zero => exact ⟨35, 8, by norm_num, by norm_num⟩
  | succ j ih =>
    obtain ⟨u, s, h, hj⟩ := ih
    exact ⟨55 * u + 252 * s, 12 * u + 55 * s, by linear_combination h, by nlinarith⟩

/-- The statement, copied verbatim from the proposed formal-conjectures variant: there are
infinitely many `8`-shifts of the sums of two squares. -/
theorem erdos_675.variants.sumsOfTwoSquares_infinite_eight_shifts :
    {t : ℕ | IsTranslation {m : ℕ | ∃ x y : ℕ, m = x ^ 2 + y ^ 2} 8 t}.Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨N, hN⟩ ↦ ?_
  obtain ⟨u, s, hP, hs⟩ := exists_pell (N + 1)
  have hs1 : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hT : 4 * s ^ 2 * (s ^ 2 - 1) + 4 * s ^ 2 = 4 * s ^ 4 := by
    zify [hs1]; ring
  have := hN (isTranslation_of_pell hP hT)
  nlinarith

end ErdosLean.Erdos675
