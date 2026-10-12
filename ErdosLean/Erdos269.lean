import FormalConjectures.ErdosProblems.«269»

/-!
# Erdős Problem 269, rationality variant: the answer is no

For `P = {2, 3}` the series `∑ 1 / [a_0, …, a_{n-1}]` is irrational, so it is not true that the
series is rational for every finite set of at least two primes.

Write `e j = ⌊log₂ 3^j⌋` and `f i = ⌊log₃ 2^i⌋`. The least common multiple of all `3`-smooth
numbers up to `x = 2^i 3^j` is `2^(i + e j) 3^(f i + j)`, so (S. Fan's factorisation)

  `series {2,3} = 1 + S₁ S₂`,  `S₁ = ∑ 2^(-i) 3^(-f i)`,  `S₂ = ∑ 3^(-j) 2^(-e j)`.

Counting lattice points on the two sides of the line `2^a = 3^b` gives `S₁ + 2 S₂ = 4`, hence
`series = 1 + S₂ (4 - 2 S₂)`.

`S₂` has very good rational approximations. Take a Farey pair `c₁/d₁ < log₂ 3 < c/d`
(`c d₁ - c₁ d = 1`) with `d₁ ≥ d + K`; such pairs exist for every `K` by a Stern–Brocot descent.
Every fraction strictly between `log₂ 3` and `c/d` has denominator at least `d + d₁ ≥ 2d + K`,
which forces `e (j + d) = e j + c` for `1 ≤ j < d + K`. Summing this near-periodicity gives a
rational `N / D` with `D = 3^d 2^c - 1` and `0 < |S₂ - N/D| D² ≤ 18 · 9^(-K)` (the sign of the
error is fixed because `c/d` lies above `log₂ 3`, and the error is nonzero since `log₂ 3 ≠ c/d`).
If the series were `r/s`, then `s D² (series - 1 - (N/D)(4 - 2N/D))` would be a nonzero integer of
absolute value `≤ 6 s · 18 · 9^(-K) < 1` for large `K`.

This settles the variant in the negative; the companion irrationality variant (for every `P`) is
not addressed here, only the case `P = {2, 3}`.
-/

namespace ErdosLean.Erdos269

open Finset

-- ### Powers of two and three

lemma two_pow_ne_three_pow {m n : ℕ} (hn : 1 ≤ n) : 2 ^ m ≠ 3 ^ n := by
  intro h
  have h3 : Odd (3 ^ n) := Odd.pow (by decide)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : 3 ^ 1 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    simp at h
    omega
  · have h2 : Even (2 ^ m) := Nat.even_pow.mpr ⟨even_two, hm.ne'⟩
    rw [h] at h2
    exact (Nat.not_even_iff_odd.mpr h3) h2

-- ### Farey pairs around `log₂ 3`
-- A pair `(m, j)` stands for the fraction `m / j`; `2^m < 3^j` means `m / j < log₂ 3`.

lemma step {a b c d : ℕ} (hab : 2 ^ a < 3 ^ b) (hcd : 3 ^ d < 2 ^ c) (hd : 1 ≤ d) :
    ∃ s : ℕ, 2 ^ ((s + 1) * a + c) < 3 ^ ((s + 1) * b + d) ∧
      3 ^ (s * b + d) < 2 ^ (s * a + c) := by
  classical
  have hex : ∃ t : ℕ, 2 ^ (t * a + c) < 3 ^ (t * b + d) := by
    have hr : (1 : ℝ) < (3 : ℝ) ^ b / 2 ^ a := by
      rw [one_lt_div (by positivity)]; exact_mod_cast hab
    obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt ((2 : ℝ) ^ c) hr
    refine ⟨t, ?_⟩
    have h1 : (2 : ℝ) ^ c * (2 ^ a) ^ t < (3 ^ b) ^ t := by
      rw [div_pow, lt_div_iff₀ (by positivity)] at ht; linarith
    have h2 : ((2 : ℝ) ^ (t * a + c)) < (3 : ℝ) ^ (t * b + d) := by
      calc (2 : ℝ) ^ (t * a + c) = 2 ^ c * (2 ^ a) ^ t := by rw [pow_add, pow_mul']; ring
        _ < (3 ^ b) ^ t := h1
        _ ≤ (3 ^ b) ^ t * 3 ^ d := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
        _ = 3 ^ (t * b + d) := by rw [pow_add, pow_mul']
    exact_mod_cast h2
  have ht : 2 ^ (Nat.find hex * a + c) < 3 ^ (Nat.find hex * b + d) := Nat.find_spec hex
  have ht0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at ht
    simp only [zero_mul, zero_add] at ht
    exact absurd hcd (not_lt.mpr ht.le)
  obtain ⟨s, hs⟩ : ∃ s, Nat.find hex = s + 1 := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨s, hs ▸ ht, ?_⟩
  have hns : ¬ 2 ^ (s * a + c) < 3 ^ (s * b + d) := Nat.find_min hex (by omega)
  have hne : 2 ^ (s * a + c) ≠ 3 ^ (s * b + d) := two_pow_ne_three_pow (le_add_left hd)
  exact lt_of_le_of_ne (not_lt.mp hns) (fun h => hne h.symm)

lemma det_step (a b c d s : ℕ) (hdet : b * c = a * d + 1) :
    ((s + 1) * b + d) * (s * a + c) = ((s + 1) * a + c) * (s * b + d) + 1 := by
  have h : (b : ℤ) * c = a * d + 1 := by exact_mod_cast hdet
  zify
  linear_combination h

lemma pairs (K : ℕ) : ∃ a b c d : ℕ, 2 ^ a < 3 ^ b ∧ 3 ^ d < 2 ^ c ∧ b * c = a * d + 1 ∧
    1 ≤ d ∧ K ≤ b := by
  induction K with
  | zero => exact ⟨1, 1, 2, 1, by norm_num, by norm_num, by norm_num, le_rfl, Nat.zero_le _⟩
  | succ K ih =>
    obtain ⟨a, b, c, d, hab, hcd, hdet, hd, hK⟩ := ih
    obtain ⟨s, h1, h2⟩ := step hab hcd hd
    refine ⟨(s + 1) * a + c, (s + 1) * b + d, s * a + c, s * b + d, h1, h2,
      det_step a b c d s hdet, le_add_left hd, ?_⟩
    nlinarith

/-- A Farey pair `c₁/d₁ < log₂ 3 < c/d` (`c d₁ - c₁ d = 1`) with `d₁ ≥ d + K`. -/
lemma farey (K : ℕ) : ∃ c d c1 d1 : ℕ, 3 ^ d < 2 ^ c ∧ 2 ^ c1 < 3 ^ d1 ∧
    c * d1 = c1 * d + 1 ∧ 1 ≤ d ∧ d + K ≤ d1 := by
  obtain ⟨a, b, c, d, hab, hcd, hdet, hd, hK⟩ := pairs K
  obtain ⟨s, h1, h2⟩ := step hab hcd hd
  refine ⟨s * a + c, s * b + d, (s + 1) * a + c, (s + 1) * b + d, h2, h1, ?_, le_add_left hd, ?_⟩
  · have := det_step a b c d s hdet
    linarith [mul_comm ((s + 1) * b + d) (s * a + c)]
  · nlinarith

/-- No fraction strictly between `log₂ 3` and `c/d` has denominator below `2 d + K`. -/
lemma between_free {c d c1 d1 K : ℕ} (h1 : 2 ^ c1 < 3 ^ d1) (hdet : c * d1 = c1 * d + 1)
    (hK : d + K ≤ d1) {m j : ℕ} (hj : 3 ^ j < 2 ^ m) (hmj : m * d < c * j) : 2 * d + K ≤ j := by
  have hj0 : j ≠ 0 := by rintro rfl; simp at hmj
  have hd1 : d1 ≠ 0 := by rintro rfl; simp at hdet
  have key : c1 * j < m * d1 := by
    have : 2 ^ (c1 * j) < 2 ^ (m * d1) := by
      calc 2 ^ (c1 * j) = (2 ^ c1) ^ j := pow_mul _ _ _
        _ < (3 ^ d1) ^ j := Nat.pow_lt_pow_left h1 hj0
        _ = (3 ^ j) ^ d1 := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ < (2 ^ m) ^ d1 := Nat.pow_lt_pow_left hj hd1
        _ = 2 ^ (m * d1) := (pow_mul _ _ _).symm
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  have hdet' : (c : ℤ) * d1 = c1 * d + 1 := by exact_mod_cast hdet
  have hj : (j : ℤ) = d1 * ((c : ℤ) * j - m * d) + d * ((m : ℤ) * d1 - c1 * j) := by
    linear_combination (-(j : ℤ)) * hdet'
  have hv : (1 : ℤ) ≤ (c : ℤ) * j - m * d := by
    have : ((m * d : ℕ) : ℤ) < ((c * j : ℕ) : ℤ) := by exact_mod_cast hmj
    push_cast at this; linarith
  have hu : (1 : ℤ) ≤ (m : ℤ) * d1 - c1 * j := by
    have : ((c1 * j : ℕ) : ℤ) < ((m * d1 : ℕ) : ℤ) := by exact_mod_cast key
    push_cast at this; linarith
  have hK' : (d : ℤ) + K ≤ d1 := by exact_mod_cast hK
  have hd0 : (0 : ℤ) ≤ d := by positivity
  have hd10 : (0 : ℤ) ≤ d1 := by positivity
  have : (2 * d + K : ℤ) ≤ j := by nlinarith
  exact_mod_cast this

-- ### The series `S₂`

/-- `e j = ⌊log₂ 3^j⌋`. -/
def e (j : ℕ) : ℕ := Nat.log 2 (3 ^ j)

/-- `f i = ⌊log₃ 2^i⌋`. -/
def f (i : ℕ) : ℕ := Nat.log 3 (2 ^ i)

lemma e_le (j : ℕ) : 2 ^ e j ≤ 3 ^ j := Nat.pow_log_le_self 2 (by positivity)

lemma lt_e (j : ℕ) : 3 ^ j < 2 ^ (e j + 1) := Nat.lt_pow_succ_log_self (by norm_num) _

lemma f_le (i : ℕ) : 3 ^ f i ≤ 2 ^ i := Nat.pow_log_le_self 3 (by positivity)

/-- The terms of `S₂`. -/
noncomputable def t (j : ℕ) : ℝ := (1 / 3 : ℝ) ^ j * (1 / 2 : ℝ) ^ e j

/-- The terms of `S₁`. -/
noncomputable def u (i : ℕ) : ℝ := (1 / 2 : ℝ) ^ i * (1 / 3 : ℝ) ^ f i

noncomputable def S2 : ℝ := ∑' j, t j

noncomputable def S1 : ℝ := ∑' i, u i

lemma t_nonneg (j : ℕ) : 0 ≤ t j := by unfold t; positivity

lemma u_nonneg (i : ℕ) : 0 ≤ u i := by unfold u; positivity

lemma t_le (j : ℕ) : t j ≤ 2 * (1 / 9 : ℝ) ^ j := by
  have h : (3 : ℝ) ^ j ≤ 2 ^ (e j + 1) := by exact_mod_cast (lt_e j).le
  have h2 : (1 / 2 : ℝ) ^ e j ≤ 2 * (1 / 3) ^ j := by
    rw [one_div_pow, one_div_pow, ← div_eq_mul_one_div, div_le_div_iff₀ (by positivity)
      (by positivity), pow_succ] at *
    nlinarith [h]
  have h9 : (1 / 9 : ℝ) ^ j = (1 / 3) ^ j * (1 / 3) ^ j := by
    rw [← mul_pow]; norm_num
  unfold t
  rw [h9]
  have : (0 : ℝ) ≤ (1 / 3) ^ j := by positivity
  nlinarith

lemma u_le (i : ℕ) : u i ≤ 3 * (1 / 4 : ℝ) ^ i := by
  have h : (2 : ℝ) ^ i ≤ 3 ^ (f i + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) (2 ^ i)).le
  have h2 : (1 / 3 : ℝ) ^ f i ≤ 3 * (1 / 2) ^ i := by
    rw [one_div_pow, one_div_pow, ← div_eq_mul_one_div, div_le_div_iff₀ (by positivity)
      (by positivity), pow_succ] at *
    nlinarith [h]
  have h4 : (1 / 4 : ℝ) ^ i = (1 / 2) ^ i * (1 / 2) ^ i := by
    rw [← mul_pow]; norm_num
  unfold u
  rw [h4]
  have : (0 : ℝ) ≤ (1 / 2) ^ i := by positivity
  nlinarith

lemma t_summable : Summable t :=
  Summable.of_nonneg_of_le t_nonneg t_le
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2)

lemma u_summable : Summable u :=
  Summable.of_nonneg_of_le u_nonneg u_le
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 3)

lemma e_zero : e 0 = 0 := by simp [e]

lemma f_zero : f 0 = 0 := by simp [f]

lemma e_one_le : e 1 ≤ 1 := by
  have h : e 1 < 2 := by
    unfold e
    rw [Nat.log_lt_iff_lt_pow (by norm_num) (by norm_num)]
    norm_num
  omega

lemma t_zero : t 0 = 1 := by simp [t, e_zero]

lemma u_zero : u 0 = 1 := by simp [u, f_zero]

lemma S2_ge : 7 / 6 ≤ S2 := by
  have h := t_summable.sum_le_tsum (Finset.range 2) (fun j _ => t_nonneg j)
  have h1 : (1 / 2 : ℝ) ^ 1 ≤ (1 / 2) ^ e 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) e_one_le
  have ht1 : 1 / 6 ≤ t 1 := by
    unfold t
    have : (1 / 3 : ℝ) ^ 1 = 1 / 3 := by norm_num
    rw [this]
    norm_num at h1 ⊢
    linarith
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, t_zero] at h
  unfold S2
  linarith

lemma S2_le : S2 ≤ 9 / 4 := by
  have hg := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 9) (by norm_num)).mul_left 2
  have := t_summable.tsum_le_tsum t_le hg
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at this
  unfold S2
  norm_num at this ⊢
  linarith

-- ### Rational approximation of `S₂`

lemma e_add_le {c d : ℕ} (hcd : 3 ^ d < 2 ^ c) (j : ℕ) : e (j + d) ≤ e j + c := by
  have h : 2 ^ e (j + d) < 2 ^ (e j + c + 1) := by
    calc 2 ^ e (j + d) ≤ 3 ^ (j + d) := e_le _
      _ = 3 ^ j * 3 ^ d := pow_add _ _ _
      _ < 2 ^ (e j + 1) * 2 ^ c := Nat.mul_lt_mul'' (lt_e j) hcd
      _ = 2 ^ (e j + c + 1) := by rw [← pow_add]; ring_nf
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h
  omega

lemma e_add_le' {c d : ℕ} (hcd : 3 ^ d < 2 ^ c) (j : ℕ) : e (j + d + 1) ≤ e (j + 1) + c := by
  have := e_add_le hcd (j + 1)
  rwa [show j + 1 + d = j + d + 1 by ring] at this

lemma geom_two (n : ℕ) : ∑ i ∈ range n, (1 / 2 : ℝ) ^ (i + 1) = 1 - (1 / 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

lemma geom_three (n : ℕ) : ∑ i ∈ range n, (1 / 3 : ℝ) ^ (i + 1) = (1 - (1 / 3) ^ n) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

/-- `w = 3^(-d) 2^(-c)`. -/
noncomputable def w (c d : ℕ) : ℝ := (1 / 3 : ℝ) ^ d * (1 / 2 : ℝ) ^ c

/-- The defect of the near-periodicity `t (j + d + 1) ≈ w t (j + 1)`. -/
noncomputable def δ (c d j : ℕ) : ℝ := t (j + d + 1) - w c d * t (j + 1)

noncomputable def Ahead (d : ℕ) : ℝ := ∑ j ∈ range d, t (j + 1)

noncomputable def E (c d : ℕ) : ℝ := ∑' j, δ c d j

/-- The numerator of the approximation. -/
def M (c d : ℕ) : ℕ := ∑ j ∈ range d, 3 ^ (d - (j + 1)) * 2 ^ (c - e (j + 1))

lemma t_shift_summable : Summable (fun j => t (j + 1)) := (summable_nat_add_iff 1).mpr t_summable

lemma t_shift_summable' (d : ℕ) : Summable (fun j => t (j + d + 1)) := by
  have h := (summable_nat_add_iff (f := t) (d + 1)).mpr t_summable
  refine h.congr (fun j => ?_)
  rw [add_assoc]

lemma δ_summable (c d : ℕ) : Summable (δ c d) :=
  (t_shift_summable' d).sub (t_shift_summable.mul_left (w c d))

lemma core_eq (c d : ℕ) : S2 * (1 - w c d) = (1 - w c d) + Ahead d + E c d := by
  have hS2 : S2 = 1 + ∑' j, t (j + 1) := by
    unfold S2; rw [t_summable.tsum_eq_zero_add, t_zero]
  have hUA : Ahead d + ∑' j, t (j + d + 1) = ∑' j, t (j + 1) :=
    t_shift_summable.sum_add_tsum_nat_add d
  have hE : E c d = ∑' j, t (j + d + 1) - w c d * ∑' j, t (j + 1) := by
    unfold E δ
    rw [(t_shift_summable' d).tsum_sub (t_shift_summable.mul_left (w c d)), tsum_mul_left]
  rw [hS2, hE]
  linear_combination (-1 : ℝ) * hUA

lemma δ_eq (c d j : ℕ) : δ c d j = (1 / 3 : ℝ) ^ (j + d + 1) *
    ((1 / 2 : ℝ) ^ e (j + d + 1) - (1 / 2 : ℝ) ^ (e (j + 1) + c)) := by
  simp only [δ, t, w]
  ring

lemma δ_nonneg {c d : ℕ} (hcd : 3 ^ d < 2 ^ c) (j : ℕ) : 0 ≤ δ c d j := by
  rw [δ_eq]
  have h : (1 / 2 : ℝ) ^ (e (j + 1) + c) ≤ (1 / 2 : ℝ) ^ e (j + d + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (e_add_le' hcd j)
  have : (0 : ℝ) ≤ (1 / 3) ^ (j + d + 1) := by positivity
  nlinarith

lemma δ_le (c d j : ℕ) : δ c d j ≤ t (j + d + 1) := by
  have h1 := t_nonneg (j + 1)
  have h2 : 0 ≤ w c d := by unfold w; positivity
  unfold δ
  nlinarith

lemma E_pos {c d : ℕ} (hcd : 3 ^ d < 2 ^ c) (hne : ∃ j, e (j + d + 1) ≠ e (j + 1) + c) :
    0 < E c d := by
  obtain ⟨j, hj⟩ := hne
  have hlt : e (j + d + 1) < e (j + 1) + c := lt_of_le_of_ne (e_add_le' hcd j) hj
  have hpos : 0 < δ c d j := by
    rw [δ_eq]
    have : (1 / 2 : ℝ) ^ (e (j + 1) + c) < (1 / 2 : ℝ) ^ e (j + d + 1) :=
      pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hlt
    have : (0 : ℝ) < (1 / 3) ^ (j + d + 1) := by positivity
    nlinarith
  exact (δ_summable c d).tsum_pos (δ_nonneg hcd) j hpos

lemma E_le {c d K : ℕ} (hK : 1 ≤ K)
    (hval : ∀ j, j + d + 1 < 2 * d + K → e (j + d + 1) = e (j + 1) + c) :
    E c d ≤ 9 / 4 * (1 / 9 : ℝ) ^ (2 * d + K) := by
  have hsplit := (δ_summable c d).sum_add_tsum_nat_add (d + K - 1)
  have hzero : ∑ i ∈ range (d + K - 1), δ c d i = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have := Finset.mem_range.mp hi
    rw [δ_eq, hval i (by omega)]
    simp
  rw [hzero, zero_add] at hsplit
  have hb : ∀ i, δ c d (i + (d + K - 1)) ≤ 2 * (1 / 9 : ℝ) ^ (2 * d + K) * (1 / 9 : ℝ) ^ i := by
    intro i
    calc δ c d (i + (d + K - 1)) ≤ t (i + (d + K - 1) + d + 1) := δ_le _ _ _
      _ ≤ 2 * (1 / 9 : ℝ) ^ (i + (d + K - 1) + d + 1) := t_le _
      _ = 2 * (1 / 9 : ℝ) ^ (2 * d + K) * (1 / 9 : ℝ) ^ i := by
        rw [show i + (d + K - 1) + d + 1 = (2 * d + K) + i by omega, pow_add]; ring
  have hg := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 9)
    (by norm_num)).mul_left (2 * (1 / 9 : ℝ) ^ (2 * d + K))
  have h := ((summable_nat_add_iff (f := δ c d) (d + K - 1)).mpr (δ_summable c d)).tsum_le_tsum hb hg
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h
  unfold E
  rw [← hsplit]
  have h9 : (0 : ℝ) ≤ (1 / 9) ^ (2 * d + K) := by positivity
  have h98 : (1 - (1 / 9 : ℝ))⁻¹ = 9 / 8 := by norm_num
  rw [h98] at h
  linarith

lemma Ahead_mul {c d : ℕ} (hcd : 3 ^ d < 2 ^ c) :
    Ahead d * ((3 : ℝ) ^ d * 2 ^ c) = (M c d : ℝ) := by
  have hed : e d < c := by
    have : 2 ^ e d < 2 ^ c := lt_of_le_of_lt (e_le d) hcd
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  unfold Ahead M
  rw [Finset.sum_mul]
  push_cast
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjd : j + 1 ≤ d := Finset.mem_range.mp hj
  have hec : e (j + 1) ≤ c := by
    have : e (j + 1) ≤ e d := Nat.log_mono_right (Nat.pow_le_pow_right (by norm_num) hjd)
    omega
  have h3 : (3 : ℝ) ^ d = 3 ^ (j + 1) * 3 ^ (d - (j + 1)) := by
    rw [← pow_add, Nat.add_sub_cancel' hjd]
  have h2 : (2 : ℝ) ^ c = 2 ^ e (j + 1) * 2 ^ (c - e (j + 1)) := by
    rw [← pow_add, Nat.add_sub_cancel' hec]
  simp only [t]
  rw [h3, h2, one_div_pow, one_div_pow]
  field_simp

lemma w_mul (c d : ℕ) : w c d * ((3 : ℝ) ^ d * 2 ^ c) = 1 := by
  unfold w
  rw [one_div_pow, one_div_pow]
  field_simp

lemma key_identity {c d : ℕ} (hcd : 3 ^ d < 2 ^ c) :
    S2 * ((3 : ℝ) ^ d * 2 ^ c - 1) = ((3 : ℝ) ^ d * 2 ^ c - 1) + M c d
      + E c d * ((3 : ℝ) ^ d * 2 ^ c) := by
  have h1 := core_eq c d
  have hwX := w_mul c d
  have hAX := Ahead_mul hcd
  linear_combination ((3 : ℝ) ^ d * 2 ^ c) * h1 + (S2 - 1) * hwX + hAX

/-- The core estimate: a rational `N / D` with `0 < |S₂ - N/D| D² ≤ 18 / 9^K`. -/
lemma core {c d K : ℕ} (hK : 1 ≤ K) (hcd : 3 ^ d < 2 ^ c) (hc2 : 2 ^ c ≤ 2 * 3 ^ d)
    (hval : ∀ j, j + d + 1 < 2 * d + K → e (j + d + 1) = e (j + 1) + c)
    (hne : ∃ j, e (j + d + 1) ≠ e (j + 1) + c) :
    ∃ (D : ℕ) (N : ℤ), 0 < D ∧ S2 ≠ N / D ∧ |S2 - N / D| * D ^ 2 ≤ 18 / 9 ^ K := by
  have hX2 : 2 ≤ 3 ^ d * 2 ^ c := by
    have h1 : 1 ≤ 3 ^ d := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 2 ≤ 2 ^ c := by
      have : c ≠ 0 := by rintro rfl; simp at hcd
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  have hId := key_identity hcd
  have hEpos := E_pos hcd hne
  have hEle := E_le hK hval
  set X : ℝ := (3 : ℝ) ^ d * 2 ^ c with hX
  have hXr : (((3 ^ d * 2 ^ c - 1 : ℕ)) : ℝ) = X - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hX2r : (2 : ℝ) ≤ X := by
    have : ((2 : ℕ) : ℝ) ≤ ((3 ^ d * 2 ^ c : ℕ) : ℝ) := by exact_mod_cast hX2
    push_cast at this; rw [hX]; linarith
  have hX1 : (0 : ℝ) < X - 1 := by linarith
  have hX1' : X - 1 ≠ 0 := hX1.ne'
  refine ⟨3 ^ d * 2 ^ c - 1, ((3 ^ d * 2 ^ c - 1 : ℕ) : ℤ) + (M c d : ℤ), by omega, ?_, ?_⟩
  all_goals
    have hcast : ((((3 ^ d * 2 ^ c - 1 : ℕ) : ℤ) + (M c d : ℤ) : ℤ) : ℝ)
        = (X - 1) + M c d := by rw [Int.cast_add, Int.cast_natCast, Int.cast_natCast, hXr]
    rw [hcast, hXr]
    have hdiff : S2 - ((X - 1) + M c d) / (X - 1) = E c d * X / (X - 1) := by
      field_simp
      linarith [hId]
  · intro h
    have : S2 - ((X - 1) + M c d) / (X - 1) = 0 := by rw [← h]; ring
    rw [hdiff] at this
    have : 0 < E c d * X / (X - 1) := by positivity
    linarith
  · rw [hdiff, abs_of_pos (by positivity)]
    have hsimp : E c d * X / (X - 1) * (X - 1) ^ 2 = E c d * X * (X - 1) := by
      field_simp
    rw [hsimp]
    have hXsq : X ^ 2 ≤ 4 * (81 : ℝ) ^ d := by
      have hc2' : (2 : ℝ) ^ c ≤ 2 * 3 ^ d := by exact_mod_cast hc2
      have h81 : (81 : ℝ) ^ d = ((3 : ℝ) ^ d) ^ 4 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have h0 : (0 : ℝ) ≤ 3 ^ d := by positivity
      have h0' : (0 : ℝ) ≤ 2 ^ c := by positivity
      have hXle : X ≤ 2 * ((3 : ℝ) ^ d) ^ 2 := by rw [hX]; nlinarith
      have hX0 : 0 ≤ X := by rw [hX]; positivity
      rw [h81]
      nlinarith
    have hpow : (1 / 9 : ℝ) ^ (2 * d + K) * (81 : ℝ) ^ d = (1 / 9) ^ K := by
      rw [pow_add, pow_mul, show ((1 : ℝ) / 9) ^ 2 = 1 / 81 by norm_num, mul_comm,
        ← mul_assoc, ← mul_pow]
      norm_num
    have hK9 : (18 : ℝ) / 9 ^ K = 18 * (1 / 9) ^ K := by rw [one_div_pow]; ring
    have hE0 : 0 ≤ E c d := hEpos.le
    have h1 : E c d * X * (X - 1) ≤ E c d * X ^ 2 := by nlinarith
    have h2 : E c d * X ^ 2 ≤ (9 / 4 * (1 / 9 : ℝ) ^ (2 * d + K)) * (4 * 81 ^ d) :=
      mul_le_mul hEle hXsq (by positivity) (by positivity)
    have h3 : (9 / 4 * (1 / 9 : ℝ) ^ (2 * d + K)) * (4 * 81 ^ d) = 9 * (1 / 9 : ℝ) ^ K := by
      rw [← hpow]; ring
    have h4 : (0 : ℝ) ≤ (1 / 9) ^ K := by positivity
    rw [hK9]
    linarith

/-- For every `K ≥ 1`, a rational approximation of `S₂` of quality `18 / 9^K` relative to `D²`. -/
lemma approx (K : ℕ) (hK : 1 ≤ K) :
    ∃ (D : ℕ) (N : ℤ), 0 < D ∧ S2 ≠ N / D ∧ |S2 - N / D| * D ^ 2 ≤ 18 / 9 ^ K := by
  obtain ⟨c, d, c1, d1, hcd, h1, hdet, hd, hdK⟩ := farey K
  have hbf : ∀ {m j : ℕ}, 3 ^ j < 2 ^ m → m * d < c * j → 2 * d + K ≤ j :=
    fun hj hmj => between_free h1 hdet hdK hj hmj
  have hc0 : c ≠ 0 := by rintro rfl; simp at hcd
  refine core hK hcd ?_ ?_ ?_
  · -- `2^c ≤ 2 · 3^d`, else `(c - 1)/d` lies between `log₂ 3` and `c/d`
    by_contra hcon
    have hcon' : 2 * 3 ^ d < 2 ^ c := lt_of_not_ge hcon
    have h3 : 3 ^ d < 2 ^ (c - 1) := by
      have : 2 ^ c = 2 * 2 ^ (c - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    have : (c - 1) * d < c * d := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    have := hbf h3 this
    omega
  · intro j hj
    have hle := e_add_le' hcd j
    by_contra hne
    have hlt : e (j + d + 1) < e (j + 1) + c := lt_of_le_of_ne hle hne
    have h3 : 3 ^ (j + d + 1) < 2 ^ (e (j + 1) + c) :=
      (Nat.log_lt_iff_lt_pow (by norm_num) (by positivity)).mp hlt
    have hmul : e (j + 1) * d < c * (j + 1) := by
      have : 2 ^ (e (j + 1) * d) < 2 ^ (c * (j + 1)) := by
        calc 2 ^ (e (j + 1) * d) = (2 ^ e (j + 1)) ^ d := pow_mul _ _ _
          _ ≤ (3 ^ (j + 1)) ^ d := Nat.pow_le_pow_left (e_le _) _
          _ = (3 ^ d) ^ (j + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
          _ < (2 ^ c) ^ (j + 1) := Nat.pow_lt_pow_left hcd (by omega)
          _ = 2 ^ (c * (j + 1)) := (pow_mul _ _ _).symm
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    have hmj : (e (j + 1) + c) * d < c * (j + d + 1) := by nlinarith
    have := hbf h3 hmj
    omega
  · -- `e` is not eventually periodic with slope `c/d`
    by_contra hcon
    have hcon' : ∀ j, e (j + d + 1) = e (j + 1) + c := fun j => by
      by_contra h; exact hcon ⟨j, h⟩
    have hper : ∀ k, e (k * d + 1) = e 1 + k * c := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have := hcon' (k * d)
        rw [show (k + 1) * d + 1 = k * d + d + 1 by ring, this, ih]
        ring
    have hr : (1 : ℝ) < (2 : ℝ) ^ c / 3 ^ d := by
      rw [one_lt_div (by positivity)]; exact_mod_cast hcd
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (3 : ℝ) hr
    have hle := e_le (k * d + 1)
    rw [hper k] at hle
    have hle' : (2 : ℝ) ^ (e 1 + k * c) ≤ 3 ^ (k * d + 1) := by exact_mod_cast hle
    rw [div_pow, lt_div_iff₀ (by positivity)] at hk
    have h1 : (2 : ℝ) ^ (k * c) ≤ 2 ^ (e 1 + k * c) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (k * c) = (2 ^ c) ^ k := by rw [← pow_mul, mul_comm]
    have h3 : (3 : ℝ) ^ (k * d + 1) = 3 * (3 ^ d) ^ k := by
      rw [pow_succ, ← pow_mul, mul_comm d k]; ring
    linarith

-- ### `S₁ + 2 S₂ = 4`

noncomputable def Fp (p : ℕ × ℕ) : ℝ := (1 / 2 : ℝ) ^ (p.1 + 1) * (1 / 3 : ℝ) ^ (p.2 + 1)

/-- Lattice points with `2^(a+1) ≤ 3^(b+1)`. -/
noncomputable def G1 (p : ℕ × ℕ) : ℝ := if 2 ^ (p.1 + 1) ≤ 3 ^ (p.2 + 1) then Fp p else 0

/-- Lattice points with `3^(b+1) < 2^(a+1)`. -/
noncomputable def G2 (p : ℕ × ℕ) : ℝ := if 2 ^ (p.1 + 1) ≤ 3 ^ (p.2 + 1) then 0 else Fp p

lemma geo2_summable : Summable (fun a : ℕ => (1 / 2 : ℝ) ^ (a + 1)) :=
  (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))

lemma geo3_summable : Summable (fun b : ℕ => (1 / 3 : ℝ) ^ (b + 1)) :=
  (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))

lemma geo2_tsum : ∑' a : ℕ, (1 / 2 : ℝ) ^ (a + 1) = 1 := by
  have h := tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have h' := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).tsum_eq_zero_add
  rw [h] at h'
  norm_num at h' ⊢
  linarith

lemma geo3_tsum : ∑' b : ℕ, (1 / 3 : ℝ) ^ (b + 1) = 1 / 2 := by
  have h := tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num)
  have h' := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num)).tsum_eq_zero_add
  rw [h] at h'
  norm_num at h' ⊢
  linarith

lemma Fp_nonneg (p : ℕ × ℕ) : 0 ≤ Fp p := by unfold Fp; positivity

lemma Fp_summable : Summable Fp := by
  have := summable_mul_of_summable_norm (f := fun a : ℕ => (1 / 2 : ℝ) ^ (a + 1))
    (g := fun b : ℕ => (1 / 3 : ℝ) ^ (b + 1)) (by simpa using geo2_summable)
    (by simpa using geo3_summable)
  exact this

lemma Fp_tsum : ∑' p, Fp p = 1 / 2 := by
  have := tsum_mul_tsum_of_summable_norm (f := fun a : ℕ => (1 / 2 : ℝ) ^ (a + 1))
    (g := fun b : ℕ => (1 / 3 : ℝ) ^ (b + 1)) (by simpa using geo2_summable)
    (by simpa using geo3_summable)
  rw [geo2_tsum, geo3_tsum] at this
  unfold Fp
  rw [← this]
  ring

lemma G1_nonneg (p : ℕ × ℕ) : 0 ≤ G1 p := by
  unfold G1; split_ifs
  · exact Fp_nonneg p
  · exact le_rfl

lemma G2_nonneg (p : ℕ × ℕ) : 0 ≤ G2 p := by
  unfold G2; split_ifs
  · exact le_rfl
  · exact Fp_nonneg p

lemma G1_le (p : ℕ × ℕ) : G1 p ≤ Fp p := by
  unfold G1; split_ifs
  · exact le_rfl
  · exact Fp_nonneg p

lemma G2_le (p : ℕ × ℕ) : G2 p ≤ Fp p := by
  unfold G2; split_ifs
  · exact Fp_nonneg p
  · exact le_rfl

lemma G1_summable : Summable G1 := Summable.of_nonneg_of_le G1_nonneg G1_le Fp_summable

lemma G2_summable : Summable G2 := Summable.of_nonneg_of_le G2_nonneg G2_le Fp_summable

lemma G_split : ∑' p, Fp p = ∑' p, G1 p + ∑' p, G2 p := by
  rw [← G1_summable.tsum_add G2_summable]
  congr 1
  ext p
  unfold G1 G2
  split_ifs <;> simp

lemma G1_inner (b : ℕ) : ∑' a : ℕ, G1 (a, b) = (1 / 3 : ℝ) ^ (b + 1) - t (b + 1) := by
  rw [tsum_eq_sum (s := range (e (b + 1)))]
  · have hs : ∀ a ∈ range (e (b + 1)), G1 (a, b) = (1 / 3 : ℝ) ^ (b + 1) * (1 / 2) ^ (a + 1) := by
      intro a ha
      have hχ : 2 ^ (a + 1) ≤ 3 ^ (b + 1) := by
        have := Finset.mem_range.mp ha
        exact (Nat.le_log_iff_pow_le (by norm_num) (by positivity)).mp this
      simp only [G1, if_pos hχ, Fp]
      ring
    rw [Finset.sum_congr rfl hs, ← Finset.mul_sum, geom_two]
    simp only [t]
    ring
  · intro a ha
    have hχ : ¬ 2 ^ (a + 1) ≤ 3 ^ (b + 1) := by
      intro h
      have h' : a + 1 ≤ e (b + 1) := (Nat.le_log_iff_pow_le (by norm_num) (by positivity)).mpr h
      exact ha (Finset.mem_range.mpr (by omega))
    simp only [G1, if_neg hχ]

lemma G2_inner (a : ℕ) : ∑' b : ℕ, G2 (a, b) = (1 / 2 : ℝ) ^ (a + 1) / 2 - u (a + 1) / 2 := by
  rw [tsum_eq_sum (s := range (f (a + 1)))]
  · have hs : ∀ b ∈ range (f (a + 1)), G2 (a, b) = (1 / 2 : ℝ) ^ (a + 1) * (1 / 3) ^ (b + 1) := by
      intro b hb
      have hχ : ¬ 2 ^ (a + 1) ≤ 3 ^ (b + 1) := by
        have := Finset.mem_range.mp hb
        have h3 := (Nat.le_log_iff_pow_le (by norm_num) (by positivity)).mp this
        have hne : 2 ^ (a + 1) ≠ 3 ^ (b + 1) := two_pow_ne_three_pow (by omega)
        omega
      simp only [G2, if_neg hχ, Fp]
    rw [Finset.sum_congr rfl hs, ← Finset.mul_sum, geom_three]
    simp only [u]
    ring
  · intro b hb
    have hχ : 2 ^ (a + 1) ≤ 3 ^ (b + 1) := by
      by_contra h
      have h' : b + 1 ≤ f (a + 1) :=
        (Nat.le_log_iff_pow_le (by norm_num) (by positivity)).mpr (by omega)
      exact hb (Finset.mem_range.mpr (by omega))
    simp only [G2, if_pos hχ]

lemma G1_tsum : ∑' p, G1 p = 1 / 2 - (S2 - 1) := by
  have h1 : ∑' p, G1 p = ∑' a, ∑' b, G1 (a, b) := G1_summable.tsum_prod
  have h2 : ∑' b, ∑' a, G1 (a, b) = ∑' a, ∑' b, G1 (a, b) :=
    Summable.tsum_comm (f := fun a b => G1 (a, b)) G1_summable
  rw [h1, ← h2, tsum_congr G1_inner, geo3_summable.tsum_sub t_shift_summable, geo3_tsum]
  have := t_summable.tsum_eq_zero_add
  unfold S2
  rw [this, t_zero]
  ring

lemma G2_tsum : ∑' p, G2 p = (2 - S1) / 2 := by
  rw [G2_summable.tsum_prod' (fun a => G2_summable.prod_factor a), tsum_congr G2_inner]
  have hus1 : Summable (fun i => u (i + 1)) := (summable_nat_add_iff 1).mpr u_summable
  rw [(geo2_summable.div_const 2).tsum_sub (hus1.div_const 2), tsum_div_const, tsum_div_const,
    geo2_tsum]
  have := u_summable.tsum_eq_zero_add
  unfold S1
  rw [this, u_zero]
  ring

lemma S1_add : S1 + 2 * S2 = 4 := by
  have h := Fp_tsum
  rw [G_split, G1_tsum, G2_tsum] at h
  linarith

-- ### The series for `P = {2, 3}`

abbrev P23 : Set ℕ := ↑({2, 3} : Finset ℕ)

/-- The `3`-smooth numbers. -/
abbrev sm : ℕ → Prop := Erdos269.HasPrimeFactorsIn P23

lemma sm_iff (n : ℕ) : sm n ↔ ∃ i j : ℕ, n = 2 ^ i * 3 ^ j := by
  constructor
  · rintro ⟨hn, hp⟩
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases h1 : n = 1
      · exact ⟨0, 0, by simp [h1]⟩
      · have hmp := Nat.minFac_prime h1
        obtain ⟨m, hm⟩ := Nat.minFac_dvd n
        have hmem := hp _ hmp ⟨m, hm⟩
        have hm0 : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h | h
          · rw [h] at hm; omega
          · exact h
        have hmlt : m < n := by
          have := hmp.two_le
          calc m < 2 * m := by omega
            _ ≤ n.minFac * m := Nat.mul_le_mul_right _ this
            _ = n := hm.symm
        obtain ⟨i, j, hij⟩ := ih m hmlt hm0
          (fun q hq hqm => hp q hq (hm ▸ Dvd.dvd.mul_left hqm _))
        simp only [P23, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hmem
        rcases hmem with h2 | h3
        · exact ⟨i + 1, j, by rw [hm, h2, hij]; ring⟩
        · exact ⟨i, j + 1, by rw [hm, h3, hij]; ring⟩
  · rintro ⟨i, j, rfl⟩
    refine ⟨by positivity, fun p hp hdvd => ?_⟩
    simp only [P23, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    · right; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)

lemma sm_infinite : (Set.ofPred sm).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun i : ℕ => 2 ^ i)
    (Nat.pow_right_injective le_rfl) (fun i => (sm_iff _).mpr ⟨i, 0, by simp⟩)

lemma a_mono : StrictMono (Erdos269.a P23) := Nat.nth_strictMono sm_infinite

lemma a_mem (k : ℕ) : sm (Erdos269.a P23 k) := Nat.nth_mem_of_infinite sm_infinite k

lemma a_surj {x : ℕ} (hx : sm x) : ∃ k, Erdos269.a P23 k = x := by
  have : x ∈ Set.range (Nat.nth sm) := by rw [Nat.range_nth_of_infinite sm_infinite]; exact hx
  exact this

lemma log_mul_pow {b m : ℕ} (hb : 1 < b) (hm : m ≠ 0) (i : ℕ) :
    Nat.log b (m * b ^ i) = Nat.log b m + i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, ← mul_assoc, Nat.log_mul_base hb (mul_ne_zero hm (pow_ne_zero _ (by omega))), ih]
    ring

/-- The lcm of all smooth numbers up to `x`. -/
def L (x : ℕ) : ℕ := 2 ^ Nat.log 2 x * 3 ^ Nat.log 3 x

lemma partialLcm_succ (n : ℕ) :
    Erdos269.partialLcm P23 (n + 1) = L (Erdos269.a P23 n) := by
  have han : Erdos269.a P23 n ≠ 0 := (a_mem n).1.ne'
  unfold Erdos269.partialLcm L
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro k hk
    have hkn : Erdos269.a P23 k ≤ Erdos269.a P23 n :=
      a_mono.monotone (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    obtain ⟨i, j, hij⟩ := (sm_iff _).mp (a_mem k)
    rw [hij] at hkn ⊢
    have hi : 2 ^ i ≤ Erdos269.a P23 n :=
      le_trans (Nat.le_mul_of_pos_right _ (by positivity)) hkn
    have hj : 3 ^ j ≤ Erdos269.a P23 n :=
      le_trans (Nat.le_mul_of_pos_left _ (by positivity)) hkn
    exact mul_dvd_mul (pow_dvd_pow _ (Nat.le_log_of_pow_le (by norm_num) hi))
      (pow_dvd_pow _ (Nat.le_log_of_pow_le (by norm_num) hj))
  · have hcop : Nat.Coprime (2 ^ Nat.log 2 (Erdos269.a P23 n)) (3 ^ Nat.log 3 (Erdos269.a P23 n)) :=
      Nat.Coprime.pow _ _ (by norm_num)
    apply hcop.mul_dvd_of_dvd_of_dvd
    · obtain ⟨k, hk⟩ := a_surj ((sm_iff (2 ^ Nat.log 2 (Erdos269.a P23 n))).mpr
        ⟨Nat.log 2 (Erdos269.a P23 n), 0, by simp⟩)
      have hkn : k ≤ n := a_mono.le_iff_le.mp (by rw [hk]; exact Nat.pow_log_le_self 2 han)
      rw [← hk]
      exact Finset.dvd_lcm (Finset.mem_range.mpr (by omega))
    · obtain ⟨k, hk⟩ := a_surj ((sm_iff (3 ^ Nat.log 3 (Erdos269.a P23 n))).mpr
        ⟨0, Nat.log 3 (Erdos269.a P23 n), by simp⟩)
      have hkn : k ≤ n := a_mono.le_iff_le.mp (by rw [hk]; exact Nat.pow_log_le_self 3 han)
      rw [← hk]
      exact Finset.dvd_lcm (Finset.mem_range.mpr (by omega))

lemma L_smooth (i j : ℕ) : (1 : ℝ) / (L (2 ^ i * 3 ^ j) : ℝ) = u i * t j := by
  have h2 : Nat.log 2 (2 ^ i * 3 ^ j) = e j + i := by
    rw [mul_comm]; exact log_mul_pow (by norm_num) (by positivity) i
  have h3 : Nat.log 3 (2 ^ i * 3 ^ j) = f i + j := log_mul_pow (by norm_num) (by positivity) j
  simp only [L, h2, h3, u, t]
  push_cast
  rw [one_div_pow, one_div_pow, one_div_pow, one_div_pow, pow_add, pow_add]
  field_simp

lemma pair_injective : Function.Injective (fun p : ℕ × ℕ => 2 ^ p.1 * 3 ^ p.2) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only at h
  have h2 := congrArg (fun n => n.factorization 2) h
  have h3 := congrArg (fun n => n.factorization 3) h
  simp [Nat.factorization_mul, Nat.factorization_pow, Nat.prime_two.factorization,
    Nat.prime_three.factorization] at h2 h3
  simp [h2, h3]

open Classical in
/-- The summand, extended by zero off the smooth numbers. -/
noncomputable def F23 (x : ℕ) : ℝ := if sm x then 1 / (L x : ℝ) else 0

lemma F23_a (n : ℕ) : (1 : ℝ) / (Erdos269.partialLcm P23 (n + 1) : ℝ) = F23 (Erdos269.a P23 n) := by
  rw [partialLcm_succ]
  unfold F23
  rw [if_pos (a_mem n)]

lemma F23_pair (p : ℕ × ℕ) : F23 (2 ^ p.1 * 3 ^ p.2) = u p.1 * t p.2 := by
  unfold F23
  rw [if_pos ((sm_iff _).mpr ⟨p.1, p.2, rfl⟩)]
  exact L_smooth p.1 p.2

lemma F23_supp_a (x : ℕ) (hx : x ∉ Set.range (Erdos269.a P23)) : F23 x = 0 := by
  unfold F23
  rw [if_neg]
  intro h
  obtain ⟨k, hk⟩ := a_surj h
  exact hx ⟨k, hk⟩

lemma F23_supp_pair (x : ℕ) (hx : x ∉ Set.range (fun p : ℕ × ℕ => 2 ^ p.1 * 3 ^ p.2)) :
    F23 x = 0 := by
  unfold F23
  rw [if_neg]
  intro h
  obtain ⟨i, j, hij⟩ := (sm_iff x).mp h
  exact hx ⟨(i, j), hij.symm⟩

lemma ut_summable : Summable (fun p : ℕ × ℕ => u p.1 * t p.2) :=
  summable_mul_of_summable_norm (f := u) (g := t)
    (by simpa [Real.norm_eq_abs, abs_of_nonneg (u_nonneg _)] using u_summable)
    (by simpa [Real.norm_eq_abs, abs_of_nonneg (t_nonneg _)] using t_summable)

lemma series_eq : Erdos269.series P23 = 1 + S1 * S2 := by
  have hinj : Function.Injective (Erdos269.a P23) := a_mono.injective
  have hFsum : Summable F23 := by
    have : Summable (F23 ∘ fun p : ℕ × ℕ => 2 ^ p.1 * 3 ^ p.2) := by
      have : (F23 ∘ fun p : ℕ × ℕ => 2 ^ p.1 * 3 ^ p.2) = fun p => u p.1 * t p.2 := by
        ext p; exact F23_pair p
      rw [this]; exact ut_summable
    exact (pair_injective.summable_iff F23_supp_pair).mp this
  have hFa_sum : Summable (F23 ∘ Erdos269.a P23) := (hinj.summable_iff F23_supp_a).mpr hFsum
  have hshift : (fun n => (1 : ℝ) / (Erdos269.partialLcm P23 (n + 1) : ℝ))
      = F23 ∘ Erdos269.a P23 := by
    ext n; exact F23_a n
  have hser_sum : Summable (fun n => (1 : ℝ) / (Erdos269.partialLcm P23 n : ℝ)) := by
    apply (summable_nat_add_iff 1).mp
    rw [hshift]; exact hFa_sum
  unfold Erdos269.series
  rw [hser_sum.tsum_eq_zero_add, hshift]
  have h0 : Erdos269.partialLcm P23 0 = 1 := by simp [Erdos269.partialLcm]
  rw [h0]
  have e1 : ∑' n, (F23 ∘ Erdos269.a P23) n = ∑' x, F23 x := hinj.tsum_eq (by
    intro x hx; by_contra h; exact hx (F23_supp_a x h))
  have e2 : ∑' p : ℕ × ℕ, F23 (2 ^ p.1 * 3 ^ p.2) = ∑' x, F23 x := pair_injective.tsum_eq (by
    intro x hx; by_contra h; exact hx (F23_supp_pair x h))
  rw [e1, ← e2, tsum_congr F23_pair]
  rw [← tsum_mul_tsum_of_summable_norm
      (by simpa [Real.norm_eq_abs, abs_of_nonneg (u_nonneg _)] using u_summable)
      (by simpa [Real.norm_eq_abs, abs_of_nonneg (t_nonneg _)] using t_summable)]
  simp [S1, S2]

-- ### Irrationality

theorem series_irrational (q : ℚ) : (q : ℝ) ≠ Erdos269.series P23 := by
  intro hq
  rw [series_eq] at hq
  have hS1 : S1 = 4 - 2 * S2 := by linarith [S1_add]
  rw [hS1] at hq
  obtain ⟨K0, hK0⟩ := pow_unbounded_of_one_lt ((108 : ℝ) * q.den) (by norm_num : (1 : ℝ) < 9)
  obtain ⟨D, N, hD, hne, hbound⟩ := approx (K0 + 2) (by omega)
  set R : ℝ := (N : ℝ) / D with hR
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have h9 : (18 : ℝ) / 9 ^ (K0 + 2) ≤ 2 / 9 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num), pow_add]
    have : (1 : ℝ) ≤ 9 ^ K0 := one_le_pow₀ (by norm_num)
    nlinarith
  have hD2 : (1 : ℝ) ≤ (D : ℝ) ^ 2 := one_le_pow₀ hDr
  have habs : |S2 - R| ≤ 2 / 9 := by
    have h0 : 0 ≤ |S2 - R| := abs_nonneg _
    nlinarith
  have hpos : 0 < |S2 - R| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hlo := S2_ge
  have hhi := S2_le
  have hR1 : S2 - 2 / 9 ≤ R := by have := le_abs_self (S2 - R); linarith
  have hR2 : R ≤ S2 + 2 / 9 := by have := neg_abs_le (S2 - R); linarith
  set Xv : ℝ := (q : ℝ) - 1 - R * (4 - 2 * R) with hXv
  have hXv' : Xv = -((S2 - R) * (2 * (S2 + R) - 4)) := by rw [hXv, hq]; ring
  have hfac : 0 < 2 * (S2 + R) - 4 := by linarith
  have hXpos : 0 < |Xv| := by
    rw [hXv', abs_neg, abs_mul, abs_of_pos hfac]
    exact mul_pos hpos hfac
  have hXle : |Xv| ≤ 6 * |S2 - R| := by
    rw [hXv', abs_neg, abs_mul, abs_of_pos hfac]
    have : 2 * (S2 + R) - 4 ≤ 6 := by linarith
    nlinarith
  set Z : ℤ := q.num * D ^ 2 - q.den * D ^ 2 - q.den * (4 * N * D - 2 * N ^ 2) with hZ
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hD0 : (0 : ℝ) < (D : ℝ) := by positivity
  have hZv : (Z : ℝ) = Xv * q.den * (D : ℝ) ^ 2 := by
    have hqd : (q : ℝ) = q.num / q.den := by exact_mod_cast (Rat.num_div_den q).symm
    rw [hZ, hXv, hqd, hR]
    push_cast
    field_simp
  have hZne : Z ≠ 0 := by
    intro h0
    have h0' : (Z : ℝ) = 0 := by exact_mod_cast h0
    rw [hZv] at h0'
    have : Xv * q.den * (D : ℝ) ^ 2 ≠ 0 := by
      have : Xv ≠ 0 := fun h => by rw [h, abs_zero] at hXpos; exact lt_irrefl _ hXpos
      positivity
    exact this h0'
  have hZ1 : (1 : ℝ) ≤ |(Z : ℝ)| := by
    have : (1 : ℤ) ≤ |Z| := Int.one_le_abs hZne
    exact_mod_cast this
  rw [hZv, abs_mul, abs_mul, abs_of_pos hden, abs_of_pos (by positivity : (0 : ℝ) < (D : ℝ) ^ 2)]
    at hZ1
  have hA : |Xv| * q.den * (D : ℝ) ^ 2 ≤ 6 * q.den * (|S2 - R| * (D : ℝ) ^ 2) := by
    have := mul_le_mul_of_nonneg_right hXle (by positivity : (0 : ℝ) ≤ q.den * (D : ℝ) ^ 2)
    linarith [this]
  have hb2 : 6 * q.den * (|S2 - R| * (D : ℝ) ^ 2) ≤ 6 * q.den * (18 / 9 ^ (K0 + 2)) :=
    mul_le_mul_of_nonneg_left hbound (by positivity)
  have hfin : 6 * (q.den : ℝ) * (18 / 9 ^ (K0 + 2)) < 1 := by
    rw [mul_div_assoc', div_lt_one (by positivity), pow_add]
    nlinarith
  linarith

end ErdosLean.Erdos269

open Erdos269

namespace ErdosLean.Erdos269

/-- The answer to the rationality variant of Erdős 269 is negative. -/
theorem erdos_269.variants.rational_false :
    ¬ ∀ᵉ (P : Finset ℕ) (_ : ∀ p ∈ P, p.Prime) (_ : P.card ≥ 2),
      ∃ (q : ℚ), q = (series (P : Set ℕ)) := by
  intro h
  obtain ⟨q, hq⟩ := h {2, 3} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three) (by decide)
  exact series_irrational q hq

/-- The same statement with the answer filled in as `False`. -/
theorem erdos_269.variants.rational_answer :
    False ↔ ∀ᵉ (P : Finset ℕ) (_ : ∀ p ∈ P, p.Prime) (_ : P.card ≥ 2),
      ∃ (q : ℚ), q = (series (P : Set ℕ)) :=
  ⟨False.elim, fun h => erdos_269.variants.rational_false h⟩

/-- The repository statement `erdos_269.variants.rational` (with `answer(sorry)` elaborated as
`True`) is refuted. -/
theorem erdos_269.variants.rational_refuted :
    ¬ (type_of% _root_.Erdos269.erdos_269.variants.rational) :=
  fun h => erdos_269.variants.rational_false (h.mp trivial)

end ErdosLean.Erdos269
