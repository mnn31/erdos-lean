import FormalConjectures.ErdosProblems.«138»

/-!
# Erdős Problem 169: `f(k) > (2/3) log W(k)` for every `k ≥ 3`

We prove `erdos_169.variants.two_thirds`: for every `k ≥ 3`, `f(k) > (2/3) log W(k)`, where `f(k)`
is the supremum of `∑_{n ∈ A} 1/n` over sets `A` of positive integers with no `k`-term arithmetic
progression, and `W(k)` is the two-colour van der Waerden number. We also prove
`erdos_169.variants.const_gt_half`: some constant `c > 1/2` has `f(k) ≥ c log W(k)` for every
`k ≥ 3`. Erdős and Graham asked for this in 1979, and the problem page says it is open.

Put `N = W(k) - 1` and take a 2-colouring of `[1, N]` with no monochromatic `k`-term progression.
1. Each colour class `C`, shifted to start at `0`, is a `k`-free subset `S` of `[0, N - 1]`. The
   integers whose base `b = 2N - 1` digits all lie in `S` form a `k`-free set (Walker,
   arXiv:2203.06045, Prop. 1.1 and Thm. 1.2; here `prop11` and `Kf_APFree`). We work with the
   finite truncations `Kf S b j`, so only finite sums appear.
2. Counting by number of digits, the shifted set has reciprocal sum at least
   `1 + (h - 1) / (1 - |S| / b)` with `h = ∑_{s ∈ S} 1/(s + 1)` (`T_closed`, `kempner_bound`).
3. The two classes have sizes adding to `N`, and `b = 2N - 1`, so averaging gives
   `f(k) ≥ (2/3) H_N - 1/3` (`averaging`, `bound_of_good`).
4. The colouring `0, 0, 1, 1, 0, 0, 1, 1` of `[1, 8]` gives `W(k) ≥ 9`, and
   `H_N > log (N + 1) + 1/2` for `N ≥ 8` (`Hr_gt_log`).

If the set defining `W(k)` were empty, `W(k)` would be `0` and both statements hold trivially, so
van der Waerden's theorem is not needed.

The statements are not in formal-conjectures at the commit pinned in `lakefile.toml`, so `f` and
both theorems are copied verbatim from the proposed `FormalConjectures/ErdosProblems/169.lean`.
`W` is `Erdos138.W`, the two-colour van der Waerden number already in formal-conjectures, and
`f` uses `Set.IsAPOfLengthFree`. Both are unchanged between the pinned commit and the commit the
statement was written against.
-/

namespace ErdosLean.Erdos169

open Finset Filter Topology
open scoped ENNReal

/-- `f(k)`, copied verbatim from the proposed `FormalConjectures/ErdosProblems/169.lean`. -/
noncomputable def f (k : ℕ) : ℝ≥0∞ :=
  ⨆ (A : Set ℕ) (_ : 0 ∉ A) (_ : A.IsAPOfLengthFree k), ∑' n : A, ((n : ℕ) : ℝ≥0∞)⁻¹

/-- `A` contains no `k`-term arithmetic progression with positive common difference. -/
def APFree (k : ℕ) (A : Set ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → ¬ ∀ i < k, a + i * d ∈ A

/-- The 2-colouring `c` (restricted to `[1,N]`) has no monochromatic `k`-term AP. -/
def Good (k N : ℕ) (c : ℕ → Bool) : Prop :=
  ∀ a d : ℕ, 0 < d → 1 ≤ a → a + (k - 1) * d ≤ N → ¬ ∀ i < k, c (a + i * d) = c a

/-- Harmonic number as a real. -/
noncomputable def Hr (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, (1 : ℝ) / n

/- ### Arithmetic progressions in the sense of `Set.IsAPOfLength` -/

/-- With `d > 0`, the set `{a + n d | n < k}` is an arithmetic progression of length `k`. -/
lemma isAPOfLength_of_pos (a d k : ℕ) (hd : 0 < d) :
    ({a + n • d | (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞))} : Set ℕ).IsAPOfLength k := by
  refine ⟨a, d, ?_, rfl⟩
  have hset : ({a + n • d | (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞))} : Set ℕ) =
      (((range k).image (fun n => a + n * d) : Finset ℕ) : Set ℕ) := by
    ext x
    simp [smul_eq_mul]
  have hinj : Function.Injective (fun n : ℕ => a + n * d) := by
    intro x y hxy
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_right hd (by omega)
  rw [hset]
  change Set.encard _ = _
  rw [Set.encard_coe_eq_coe_finsetCard, card_image_of_injective _ hinj, card_range]

/-- An arithmetic progression of length `k ≥ 2` in `ℕ` has a positive difference. -/
lemma exists_of_isAPOfLength {t : Set ℕ} {k : ℕ} (hk : 2 ≤ k) (h : t.IsAPOfLength k) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ t := by
  obtain ⟨a, d, hcard, ht⟩ := h
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exfalso
    have hsub : t ⊆ {a} := by
      rw [ht]
      rintro x ⟨n, _, rfl⟩
      simp
    have h1 : t.encard ≤ 1 := by
      simpa using Set.encard_le_encard hsub
    have h2 : t.encard = k := hcard
    rw [h2] at h1
    have : k ≤ 1 := by exact_mod_cast h1
    omega
  · refine ⟨a, d, hd, fun i hi => ?_⟩
    rw [ht]
    exact ⟨i, by exact_mod_cast hi, by simp [smul_eq_mul]⟩

/-- `APFree` implies `Set.IsAPOfLengthFree`. -/
lemma isAPOfLengthFree_of_apFree {k : ℕ} {A : Set ℕ} (h : APFree k A) :
    A.IsAPOfLengthFree k := by
  intro t ht hAP
  by_contra hk
  have hk2 : 2 ≤ k := by
    by_contra hk'
    exact hk (by exact_mod_cast (show k ≤ 1 by omega))
  obtain ⟨a, d, hd, hmem⟩ := exists_of_isAPOfLength hk2 hAP
  exact h a d hd (fun i hi => ht (hmem i hi))

/- ### Lemma 1: finite AP-free sets bound `f` from below -/

lemma le_f {k : ℕ} (A : Finset ℕ) (h0 : 0 ∉ A) (hA : APFree k (A : Set ℕ)) :
    ENNReal.ofReal (∑ n ∈ A, (1 : ℝ) / n) ≤ f k := by
  have h1 : ENNReal.ofReal (∑ n ∈ A, (1 : ℝ) / n) =
      ∑' n : (A : Set ℕ), ((n : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity),
      Finset.tsum_subtype' A (fun n : ℕ => ((n : ℝ≥0∞))⁻¹)]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn0 : (0 : ℝ) < n := by
      have : n ≠ 0 := fun h => h0 (h ▸ hn)
      exact_mod_cast Nat.pos_of_ne_zero this
    rw [one_div, ENNReal.ofReal_inv_of_pos hn0, ENNReal.ofReal_natCast]
  rw [h1]
  exact le_iSup_of_le (A : Set ℕ) (le_iSup_of_le (by simpa using h0)
    (le_iSup_of_le (isAPOfLengthFree_of_apFree hA) le_rfl))

lemma f_ge_one {k : ℕ} (hk : 2 ≤ k) : ENNReal.ofReal 1 ≤ f k := by
  have := le_f (k := k) {1} (by simp) (by
    intro a d hd h
    have h0 := h 0 (by omega)
    have h1 := h 1 (by omega)
    simp at h0 h1
    omega)
  simpa using this

/- ### Lemma 2: Walker's Proposition 1.1 (residue form) -/

/-- If `S ⊆ [0,M]` is `k`-AP-free and `b > 2M`, then no `k`-AP with difference not divisible
by `b` has all its residues mod `b` in `S`. -/
lemma prop11 {k M b a d : ℕ} {S : Finset ℕ} (hSM : ∀ s ∈ S, s ≤ M) (hMb : 2 * M < b)
    (hS : APFree k (S : Set ℕ)) (hd : ¬ b ∣ d) : ¬ ∀ i < k, (a + i * d) % b ∈ S := by
  intro hres
  have hb : 0 < b := by omega
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℕ, ∀ i, r i = (a + i * d) % b := ⟨_, fun _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = d % b := ⟨_, rfl⟩
  have hD0 : 0 < D := by
    rw [hD]; exact Nat.pos_of_ne_zero (fun h => hd (Nat.dvd_of_mod_eq_zero h))
  have hDb : D < b := by rw [hD]; exact Nat.mod_lt _ hb
  have hrb : ∀ i, r i < b := fun i => by rw [hr]; exact Nat.mod_lt _ hb
  have hrS : ∀ i < k, r i ∈ S := fun i hi => by rw [hr]; exact hres i hi
  have hstep : ∀ i, r (i + 1) = (r i + D) % b := by
    intro i
    rw [hr, hr, hD, show a + (i + 1) * d = (a + i * d) + d by ring, Nat.add_mod]
  have hnw : ∀ i, r i + D < b → r (i + 1) = r i + D := fun i h => by
    rw [hstep, Nat.mod_eq_of_lt h]
  have hw : ∀ i, b ≤ r i + D → r (i + 1) = r i + D - b := fun i h => by
    rw [hstep, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by have := hrb i; omega)]
  by_cases hall : ∀ i < k - 1, r i + D < b
  · -- no carries: increasing AP r 0, r 0 + D, ...
    have hlin : ∀ i, i < k → r i = r 0 + i * D := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ i ih =>
        intro hi
        rw [hnw i (hall i (by omega)), ih (by omega)]
        ring
    exact hS (r 0) D hD0 (fun i hi => by
      rw [Finset.mem_coe, ← hlin i hi]; exact hrS i hi)
  by_cases hall' : ∀ i < k - 1, b ≤ r i + D
  · -- always a carry: decreasing AP with difference b - D
    have hlin : ∀ i, i < k → r i + i * (b - D) = r 0 := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ i ih =>
        intro hi
        have h1 := hw i (hall' i (by omega))
        have h2 := ih (by omega)
        have h3 : (i + 1) * (b - D) = i * (b - D) + (b - D) := by ring
        have := hall' i (by omega)
        omega
    refine hS (r (k - 1)) (b - D) (by omega) (fun i hi => ?_)
    have e1 := hlin (k - 1) (by omega)
    have e2 := hlin (k - 1 - i) (by omega)
    have e3 : (k - 1) * (b - D) = (k - 1 - i) * (b - D) + i * (b - D) := by
      rw [← add_mul, Nat.sub_add_cancel (by omega)]
    have : r (k - 1) + i * (b - D) = r (k - 1 - i) := by omega
    rw [Finset.mem_coe, this]
    exact hrS _ (by omega)
  · -- mixed: D ≤ M and D ≥ b - M, contradiction with b > 2M
    push Not at hall hall'
    obtain ⟨i, hi, hi'⟩ := hall
    obtain ⟨j, hj, hj'⟩ := hall'
    have h1 := hSM _ (hrS (j + 1) (by omega))
    have h2 := hSM _ (hrS i (by omega))
    rw [hnw j hj'] at h1
    omega

/- ### Lemma 3: truncated Kempner sets and Walker's Theorem 1.2 -/

/-- `Kf S b j` = integers with at most `j` base-`b` digits, all digits in `S`. -/
def Kf (S : Finset ℕ) (b : ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | j + 1 => ((Kf S b j) ×ˢ S).image (fun p => b * p.1 + p.2)

lemma mem_Kf_succ {S : Finset ℕ} {b j x : ℕ} :
    x ∈ Kf S b (j + 1) ↔ ∃ y ∈ Kf S b j, ∃ s ∈ S, b * y + s = x := by
  simp only [Kf, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨y, s, ⟨hy, hs⟩, rfl⟩; exact ⟨y, hy, s, hs, rfl⟩
  · rintro ⟨y, hy, s, hs, rfl⟩; exact ⟨y, s, ⟨hy, hs⟩, rfl⟩

lemma Kf_digit {S : Finset ℕ} {b j x : ℕ} (hSb : ∀ s ∈ S, s < b) (hx : x ∈ Kf S b (j + 1)) :
    x % b ∈ S ∧ x / b ∈ Kf S b j := by
  obtain ⟨y, hy, s, hs, rfl⟩ := mem_Kf_succ.1 hx
  have hsb := hSb s hs
  have hb : 0 < b := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsb]; exact hs
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hsb, zero_add]; exact hy

lemma zero_mem_Kf {S : Finset ℕ} {b : ℕ} (h0 : 0 ∈ S) : ∀ j, 0 ∈ Kf S b j
  | 0 => by simp [Kf]
  | j + 1 => mem_Kf_succ.2 ⟨0, zero_mem_Kf h0 j, 0, h0, by simp⟩

/-- Walker Thm 1.2 combined with Prop 1.1, for the truncations. -/
lemma Kf_APFree {k M b : ℕ} {S : Finset ℕ} (hk : 2 ≤ k) (hSM : ∀ s ∈ S, s ≤ M)
    (hMb : 2 * M < b) (hS : APFree k (S : Set ℕ)) : ∀ j, APFree k (Kf S b j : Set ℕ) := by
  have hb : 0 < b := by omega
  have hSb : ∀ s ∈ S, s < b := fun s hs => by have := hSM s hs; omega
  intro j
  induction j with
  | zero =>
    intro a d hd h
    have h0 := h 0 (by omega)
    have h1 := h 1 (by omega)
    simp [Kf] at h0 h1
    omega
  | succ j ih =>
    intro a d hd h
    by_cases hbd : b ∣ d
    · obtain ⟨e, rfl⟩ := hbd
      have he : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at hd)
      refine ih (a / b) e he (fun i hi => ?_)
      have := (Kf_digit hSb (h i hi)).2
      have heq : a + i * (b * e) = a + b * (i * e) := by ring
      rw [heq, Nat.add_mul_div_left _ _ hb] at this
      exact this
    · exact prop11 hSM hMb hS hbd (fun i hi => (Kf_digit hSb (h i hi)).1)

/- ### Lemma 4: the digit-level harmonic count -/

/-- `T j = ∑_{x ∈ Kf S b j} 1/(x+1)`. -/
noncomputable def T (S : Finset ℕ) (b j : ℕ) : ℝ := ∑ x ∈ Kf S b j, (1 : ℝ) / ((x : ℝ) + 1)

lemma T_zero (S : Finset ℕ) (b : ℕ) : T S b 0 = 1 := by simp [T, Kf]

lemma T_succ {S : Finset ℕ} {b : ℕ} (h0 : 0 ∈ S) (hSb : ∀ s ∈ S, s < b) (j : ℕ) :
    (∑ s ∈ S, (1 : ℝ) / ((s : ℝ) + 1)) + ((S.card : ℝ) / b) * (T S b j - 1) ≤ T S b (j + 1) := by
  have hb : 0 < b := hSb 0 h0
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hinj : Set.InjOn (fun p : ℕ × ℕ => b * p.1 + p.2) ((Kf S b j) ×ˢ S : Finset _) := by
    rintro ⟨y, s⟩ hys ⟨y', s'⟩ hys' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hys hys'
    have hs := hSb s hys.2
    have hs' := hSb s' hys'.2
    simp only at heq
    have e1 : (b * y + s) % b = (b * y' + s') % b := by rw [heq]
    have e2 : (b * y + s) / b = (b * y' + s') / b := by rw [heq]
    rw [Nat.add_comm (b * y), Nat.add_comm (b * y'), Nat.add_mul_mod_self_left,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hs'] at e1
    rw [Nat.add_comm (b * y), Nat.add_comm (b * y'), Nat.add_mul_div_left _ _ hb,
      Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hs, Nat.div_eq_of_lt hs'] at e2
    simp only [zero_add] at e2
    rw [e1, e2]
  have hsplit : T S b (j + 1) =
      ∑ y ∈ Kf S b j, ∑ s ∈ S, (1 : ℝ) / ((b : ℝ) * y + s + 1) := by
    rw [T, Kf, Finset.sum_image hinj, Finset.sum_product]
    push_cast
    rfl
  have h0K := zero_mem_Kf (b := b) h0 j
  rw [hsplit, ← Finset.add_sum_erase _ _ h0K, T, ← Finset.add_sum_erase _ _ h0K]
  simp only [Nat.cast_zero, mul_zero, zero_add, div_one]
  have key : ∀ y ∈ (Kf S b j).erase 0,
      ((S.card : ℝ) / b) * (1 / ((y : ℝ) + 1)) ≤ ∑ s ∈ S, (1 : ℝ) / ((b : ℝ) * y + s + 1) := by
    intro y _
    have : ∀ s ∈ S, (1 : ℝ) / ((b : ℝ) * (y + 1)) ≤ (1 : ℝ) / ((b : ℝ) * y + s + 1) := by
      intro s hs
      have hsb : (s : ℝ) + 1 ≤ b := by exact_mod_cast hSb s hs
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    calc ((S.card : ℝ) / b) * (1 / ((y : ℝ) + 1))
        = ∑ s ∈ S, (1 : ℝ) / ((b : ℝ) * (y + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; field_simp
      _ ≤ _ := Finset.sum_le_sum this
  have := Finset.sum_le_sum key
  rw [← Finset.mul_sum] at this
  linarith

lemma T_closed {S : Finset ℕ} {b : ℕ} (h0 : 0 ∈ S) (hSb : ∀ s ∈ S, s < b) (j : ℕ) :
    1 + ((∑ s ∈ S, (1 : ℝ) / ((s : ℝ) + 1)) - 1) *
      ∑ i ∈ range j, ((S.card : ℝ) / b) ^ i ≤ T S b j := by
  set h := ∑ s ∈ S, (1 : ℝ) / ((s : ℝ) + 1)
  set ρ := (S.card : ℝ) / b
  have hρ : 0 ≤ ρ := by positivity
  induction j with
  | zero => simp [T_zero]
  | succ j ih =>
    have hs := T_succ h0 hSb j
    rw [Finset.sum_range_succ', pow_zero]
    have : ∑ i ∈ range j, ρ ^ (i + 1) = ρ * ∑ i ∈ range j, ρ ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this]
    have := mul_le_mul_of_nonneg_left (sub_le_sub_right ih 1) hρ
    nlinarith

/-- The Kempner lift: `f k ≥ 1 + (h' - 1)/(1 - |S|/b)`. -/
lemma kempner_bound {k M b : ℕ} {S : Finset ℕ} (hk : 2 ≤ k) (hSM : ∀ s ∈ S, s ≤ M)
    (hMb : 2 * M < b) (hcard : S.card < b) (h0 : 0 ∈ S) (hS : APFree k (S : Set ℕ)) :
    ENNReal.ofReal (1 + ((∑ s ∈ S, (1 : ℝ) / ((s : ℝ) + 1)) - 1) /
      (1 - (S.card : ℝ) / b)) ≤ f k := by
  have hb : 0 < b := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hSb : ∀ s ∈ S, s < b := fun s hs => by have := hSM s hs; omega
  set h := ∑ s ∈ S, (1 : ℝ) / ((s : ℝ) + 1)
  set ρ := (S.card : ℝ) / b with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by
    rw [hρdef, div_lt_one hbR]; exact_mod_cast hcard
  -- each truncation, shifted by one, is a finite AP-free set of positive integers
  have hTj : ∀ j, ENNReal.ofReal (T S b j) ≤ f k := by
    intro j
    have hfree := Kf_APFree hk hSM hMb hS j
    have hinj : Set.InjOn (fun x : ℕ => x + 1) (Kf S b j : Set ℕ) :=
      fun x _ y _ hxy => by simpa using hxy
    have := le_f (k := k) ((Kf S b j).image (fun x => x + 1)) (by simp) (by
      intro a d hd hall
      have ha : ∀ i < k, ∃ x ∈ Kf S b j, x + 1 = a + i * d := by
        intro i hi; simpa using hall i hi
      obtain ⟨x0, _, hx0⟩ := ha 0 (by omega)
      refine hfree (a - 1) d hd (fun i hi => ?_)
      obtain ⟨x, hx, hxe⟩ := ha i hi
      have : a - 1 + i * d = x := by simp at hx0; omega
      rw [Finset.mem_coe, this]; exact hx)
    rw [Finset.sum_image hinj] at this
    simpa [T] using this
  have hlim : Tendsto (fun j => 1 + (h - 1) * ∑ i ∈ range j, ρ ^ i) atTop
      (𝓝 (1 + (h - 1) * (1 - ρ)⁻¹)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul
      (hasSum_geometric_of_lt_one hρ0 hρ1).tendsto_sum_nat)
  rw [div_eq_mul_inv]
  refine le_of_tendsto' (ENNReal.tendsto_ofReal hlim) (fun j => ?_)
  exact le_trans (ENNReal.ofReal_le_ofReal (T_closed h0 hSb j)) (hTj j)

/- ### Lemma 5: colour classes -/

/-- A colour class of a good colouring. -/
def cls (N : ℕ) (c : ℕ → Bool) (t : Bool) : Finset ℕ := (Icc 1 N).filter (fun n => c n = t)

lemma cls_APFree {k N : ℕ} {c : ℕ → Bool} (hk : 1 ≤ k) (hc : Good k N c) (t : Bool) :
    APFree k (cls N c t : Set ℕ) := by
  intro a d hd h
  have hmem : ∀ i < k, (1 ≤ a + i * d ∧ a + i * d ≤ N) ∧ c (a + i * d) = t := by
    intro i hi; simpa [cls] using h i hi
  have h0 := hmem 0 (by omega)
  have hl := hmem (k - 1) (by omega)
  simp at h0
  refine hc a d hd h0.1.1 hl.1.2 (fun i hi => ?_)
  rw [(hmem i hi).2, h0.2]

lemma cls_kempner {k N : ℕ} {c : ℕ → Bool} (hk : 2 ≤ k) (hN : 2 ≤ N) (hc : Good k N c)
    (t : Bool) :
    ENNReal.ofReal (1 + ((∑ n ∈ cls N c t, (1 : ℝ) / n) - 1) /
      (1 - ((cls N c t).card : ℝ) / ((2 * N - 1 : ℕ) : ℝ))) ≤ f k := by
  set C := cls N c t with hCdef
  set b := 2 * N - 1 with hbdef
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  rcases C.eq_empty_or_nonempty with hC | hne
  · have e1 : ∑ n ∈ C, (1 : ℝ) / n = 0 := by rw [hC]; simp
    have e2 : (C.card : ℝ) = 0 := by rw [hC]; simp
    rw [e1, e2]; norm_num
  have hCsub : ∀ x ∈ C, 1 ≤ x ∧ x ≤ N := fun x hx => by
    simpa [hCdef, cls] using (Finset.mem_filter.1 hx).1
  set m := C.min' hne
  have hmC : m ∈ C := C.min'_mem hne
  have hm1 : 1 ≤ m := (hCsub m hmC).1
  have hmle : ∀ x ∈ C, m ≤ x := fun x hx => C.min'_le x hx
  set S := C.image (fun x => x - m)
  have hinj : Set.InjOn (fun x => x - m) (C : Set ℕ) := by
    intro x hx y hy hxy
    have := hmle x hx; have := hmle y hy
    simp only at hxy; omega
  have hcard : S.card = C.card := Finset.card_image_of_injOn hinj
  have hCcard : C.card ≤ N := by
    calc C.card ≤ (Icc 1 N).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = N := by simp
  have hSM : ∀ s ∈ S, s ≤ N - 1 := by
    intro s hs
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hs
    have := hCsub x hx; omega
  have h0 : 0 ∈ S := Finset.mem_image.2 ⟨m, hmC, Nat.sub_self m⟩
  have hSfree : APFree k (S : Set ℕ) := by
    intro a d hd h
    refine cls_APFree (by omega) hc t (a + m) d hd (fun i hi => ?_)
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.1 (h i hi)
    have := hmle x hx
    have : a + m + i * d = x := by omega
    rw [Finset.mem_coe, this]; exact hx
  have hK := kempner_bound (M := N - 1) (b := b) hk hSM (by omega) (by omega) h0 hSfree
  rw [hcard] at hK
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hK
  have hρ1 : 0 < 1 - (C.card : ℝ) / b := by
    rw [sub_pos, div_lt_one hbR]; exact_mod_cast (show C.card < b by omega)
  have hsum : ∑ n ∈ C, (1 : ℝ) / n ≤ ∑ s ∈ S, (1 : ℝ) / ((s : ℝ) + 1) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_le_sum (fun x hx => ?_)
    have hmx := hmle x hx
    rw [Nat.cast_sub hmx]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    apply one_div_le_one_div_of_le
    · have : (m : ℝ) ≤ x := by exact_mod_cast hmx
      linarith
    · linarith
  have := div_le_div_of_nonneg_right (sub_le_sub_right hsum 1) hρ1.le
  linarith

/- ### Lemma 6: averaging over the two classes -/

lemma averaging (H1 H2 n1 n2 N b : ℝ) (hN : 2 ≤ N) (hb : b = 2 * N - 1) (hn : n1 + n2 = N)
    (hn1 : 0 ≤ n1) (hn2 : 0 ≤ n2) (hH : 2 ≤ H1 + H2) :
    (2 / 3) * (H1 + H2) - 1 / 3 ≤ 1 + (H1 - 1) / (1 - n1 / b) ∨
    (2 / 3) * (H1 + H2) - 1 / 3 ≤ 1 + (H2 - 1) / (1 - n2 / b) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hbpos : 0 < b := by linarith
  have hq1 : 0 < 1 - n1 / b := by rw [sub_pos, div_lt_one hbpos]; linarith
  have hq2 : 0 < 1 - n2 / b := by rw [sub_pos, div_lt_one hbpos]; linarith
  have e1 : H1 - 1 < ((2 / 3) * (H1 + H2) - 4 / 3) * (1 - n1 / b) := by
    rw [← div_lt_iff₀ hq1]; linarith
  have e2 : H2 - 1 < ((2 / 3) * (H1 + H2) - 4 / 3) * (1 - n2 / b) := by
    rw [← div_lt_iff₀ hq2]; linarith
  have hsum : n1 / b + n2 / b ≥ 1 / 2 := by
    rw [← add_div, hn, ge_iff_le, le_div_iff₀ hbpos]; linarith
  have ht : 0 ≤ (2 / 3) * (H1 + H2) - 4 / 3 := by linarith
  nlinarith

/- ### Lemma 7: harmonic numbers -/

lemma Hr_succ (N : ℕ) : Hr (N + 1) = Hr N + 1 / ((N : ℝ) + 1) := by
  rw [Hr, Hr, Finset.sum_Icc_succ_top (by omega)]
  push_cast; ring

/- ### Splitting `[1, N]` into the two colour classes -/

lemma split_sum (N : ℕ) (c : ℕ → Bool) :
    (∑ n ∈ cls N c true, (1 : ℝ) / n) + (∑ n ∈ cls N c false, (1 : ℝ) / n) = Hr N := by
  rw [Hr, ← Finset.sum_filter_add_sum_filter_not (Icc 1 N) (fun n => c n = true)]
  simp [cls]

lemma split_card (N : ℕ) (c : ℕ → Bool) :
    (cls N c true).card + (cls N c false).card = N := by
  have := Finset.card_filter_add_card_filter_not (s := Icc 1 N) (fun n => c n = true)
  simpa [cls] using this

/-- From a good colouring of `[1,N]` with `N ≥ 2` and `H_N ≥ 2`: `f k ≥ (2/3) H_N - 1/3`. -/
lemma bound_of_good {k N : ℕ} {c : ℕ → Bool} (hk : 3 ≤ k) (hc : Good k N c) (hN : 2 ≤ N)
    (hH : 2 ≤ Hr N) : ENNReal.ofReal ((2 / 3) * Hr N - 1 / 3) ≤ f k := by
  have hs := split_sum N c
  have hcard := split_card N c
  have hb : (((2 * N - 1 : ℕ)) : ℝ) = 2 * (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hav := averaging (∑ n ∈ cls N c true, (1 : ℝ) / n) (∑ n ∈ cls N c false, (1 : ℝ) / n)
    ((cls N c true).card) ((cls N c false).card) N ((2 * N - 1 : ℕ) : ℝ)
    (by exact_mod_cast hN) hb (by exact_mod_cast hcard) (by positivity) (by positivity)
    (by rw [hs]; exact hH)
  rw [hs] at hav
  rcases hav with h | h
  · exact le_trans (ENNReal.ofReal_le_ofReal h) (cls_kempner (by omega) hN hc true)
  · exact le_trans (ENNReal.ofReal_le_ofReal h) (cls_kempner (by omega) hN hc false)

/- ### `W(k) ≥ 9` and a good colouring of `[1, W(k) - 1]` -/

/-- The colouring `0, 0, 1, 1, 0, 0, 1, 1` of `1, …, 8`. -/
def col8 (n : ℕ) : Bool := (n - 1) / 2 % 2 == 1

lemma col8_dec (a d : ℕ) (hd : 0 < d) (ha : 1 ≤ a) (hle : a + 2 * d ≤ 8) :
    ¬ (col8 (a + d) = col8 a ∧ col8 (a + 2 * d) = col8 a) := by
  have ha6 : a ≤ 6 := by omega
  have hd3 : d ≤ 3 := by omega
  interval_cases a <;> interval_cases d <;> first | omega | decide

lemma good_col8 {k N : ℕ} (hk : 3 ≤ k) (hN : N ≤ 8) : Good k N col8 := by
  intro a d hd ha hle h
  have hm : 2 * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  rw [one_mul] at h1
  exact col8_dec a d hd ha (by omega) ⟨h1, h2⟩

/-- A good colouring `c` of `[1,N]` shows that `N` is not in the set defining `Erdos138.W`. -/
lemma not_mem_guarantee {k N : ℕ} (hk : 2 ≤ k) {c : ℕ → Bool} (hc : Good k N c) :
    N ∉ Erdos138.monoAP_guarantee_set 2 k := by
  intro hN
  obtain ⟨col, ap, hAP, hcol⟩ := hN (fun m => if c m.1 then 1 else 0)
  obtain ⟨a, d, hd, hmem⟩ := exists_of_isAPOfLength hk hAP
  have key : ∀ i < k, (1 ≤ a + i * d ∧ a + i * d ≤ N) ∧
      (if c (a + i * d) then (1 : Fin 2) else 0) = col := by
    intro i hi
    obtain ⟨m, hm, hme⟩ := hmem i hi
    have hmI := Finset.mem_Icc.1 m.2
    rw [← hme]
    exact ⟨hmI, hcol m hm⟩
  have hbool : ∀ b b' : Bool,
      ((if b then (1 : Fin 2) else 0) = if b' then (1 : Fin 2) else 0) → b = b' := by decide
  have h0 := key 0 (by omega)
  have hl := key (k - 1) (by omega)
  simp only [zero_mul, add_zero] at h0
  refine hc a d hd h0.1.1 hl.1.2 (fun i hi => hbool _ _ ?_)
  rw [(key i hi).2, h0.2]

/-- If `N` is not in the set defining `Erdos138.W`, then `[1,N]` has a good colouring. -/
lemma exists_good_of_not_mem {k N : ℕ} (hN : N ∉ Erdos138.monoAP_guarantee_set 2 k) :
    ∃ c : ℕ → Bool, Good k N c := by
  simp only [Erdos138.monoAP_guarantee_set, Set.mem_ofPred_eq, not_forall] at hN
  obtain ⟨col, hcol⟩ := hN
  let c : ℕ → Bool := fun n =>
    if h : n ∈ Finset.Icc 1 N then decide (col ⟨n, h⟩ = 1) else false
  refine ⟨c, fun a d hd ha hle hall => hcol ?_⟩
  have hI : ∀ i < k, a + i * d ∈ Finset.Icc 1 N := by
    intro i hi
    have : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have haI : a ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨ha, by omega⟩
  have hfin : ∀ p q : Fin 2, decide (p = 1) = decide (q = 1) → p = q := by decide
  refine ⟨col ⟨a, haI⟩, {m | ∃ i < k, m.1 = a + i * d}, ?_, ?_⟩
  · have himg : ((·.1) '' {m : (Finset.Icc 1 N : Set ℕ) | ∃ i < k, m.1 = a + i * d} : Set ℕ) =
        {a + n • d | (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞))} := by
      ext x
      constructor
      · rintro ⟨m, ⟨i, hi, hm⟩, rfl⟩
        exact ⟨i, by exact_mod_cast hi, by simp [hm, smul_eq_mul]⟩
      · rintro ⟨i, hi, rfl⟩
        have hi' : i < k := by exact_mod_cast hi
        exact ⟨⟨a + i * d, hI i hi'⟩, ⟨i, hi', rfl⟩, by simp [smul_eq_mul]⟩
    rw [himg]
    exact isAPOfLength_of_pos a d k hd
  · rintro ⟨m, hmI⟩ ⟨i, hi, hm⟩
    simp only at hm
    subst hm
    have h := hall i hi
    simp only [c, dif_pos (hI i hi), dif_pos haI] at h
    exact hfin _ _ h

/-- `W k = 0` (only if the defining set were empty) or `W k = N + 1` with `N ≥ 8` and a good
colouring of `[1,N]`. -/
lemma W_cases (k : ℕ) (hk : 3 ≤ k) :
    Erdos138.W k = 0 ∨ ∃ N, 8 ≤ N ∧ Erdos138.W k = N + 1 ∧ ∃ c, Good k N c := by
  have hW : Erdos138.W k = sInf (Erdos138.monoAP_guarantee_set 2 k) := rfl
  by_cases hne : (Erdos138.monoAP_guarantee_set 2 k).Nonempty
  · right
    have hmem : Erdos138.W k ∈ Erdos138.monoAP_guarantee_set 2 k := hW ▸ Nat.sInf_mem hne
    have h9 : 9 ≤ Erdos138.W k := by
      by_contra hlt
      exact not_mem_guarantee (by omega) (good_col8 hk (by omega)) hmem
    refine ⟨Erdos138.W k - 1, by omega, by omega, ?_⟩
    exact exists_good_of_not_mem (Nat.notMem_of_lt_sInf (by rw [← hW]; omega))
  · left
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hW, hne, Nat.sInf_empty]

/- ### `H_N > log (N + 1) + 1/2` for `N ≥ 8` -/

lemma Hr_eight : Hr 8 = 761 / 280 := by
  have h0 : Hr 0 = 0 := by simp [Hr]
  have := Hr_succ 7; have := Hr_succ 6; have := Hr_succ 5; have := Hr_succ 4
  have := Hr_succ 3; have := Hr_succ 2; have := Hr_succ 1; have := Hr_succ 0
  norm_num at *
  linarith

lemma log_nine_lt : Real.log 9 < 621 / 280 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have hq := Real.quadratic_le_exp_of_nonneg (x := 61 / 280) (by norm_num)
  have he : Real.exp (621 / 280) = Real.exp 1 * Real.exp 1 * Real.exp (61 / 280) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  rw [he]
  have hsq : (2.7182818283 : ℝ) * 2.7182818283 < Real.exp 1 * Real.exp 1 :=
    mul_lt_mul'' h1 h1 (by norm_num) (by norm_num)
  have hq0 : (0 : ℝ) < 1 + 61 / 280 + (61 / 280) ^ 2 / 2 := by norm_num
  nlinarith [mul_le_mul_of_nonneg_left hq (le_of_lt (lt_trans (by norm_num) hsq))]

/-- `H_N > log(N+1) + 1/2` for every `N ≥ 8`. -/
lemma Hr_gt_log (N : ℕ) (hN : 8 ≤ N) : Real.log ((N : ℝ) + 1) + 1 / 2 < Hr N := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [Hr_eight]
    have := log_nine_lt
    norm_num
    linarith
  | succ n hn ih =>
    rw [Hr_succ]
    have hl := Real.log_le_sub_one_of_pos (x := ((n : ℝ) + 2) / ((n : ℝ) + 1)) (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at hl
    have he : ((n : ℝ) + 2) / ((n : ℝ) + 1) - 1 = 1 / ((n : ℝ) + 1) := by
      field_simp; ring
    push_cast
    have : ((n : ℝ) + 1 + 1) = (n : ℝ) + 2 := by ring
    rw [this]
    linarith

lemma Hr_mono {M N : ℕ} (h : M ≤ N) : Hr M ≤ Hr N := by
  unfold Hr
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl h)
  intro i _ _; positivity

/- ### Main theorems -/

/-- If `W k = N + 1`, then `f(k) ≥ (2 H_N - 1)/3`. -/
theorem bound_H (k : ℕ) (hk : 3 ≤ k) (N : ℕ) (hW : Erdos138.W k = N + 1) :
    ENNReal.ofReal ((2 * Hr N - 1) / 3) ≤ f k := by
  rcases W_cases k hk with h0 | ⟨M, hM8, hWM, c, hc⟩
  · omega
  · have hMN : M = N := by omega
    subst hMN
    have hH8 : (2 : ℝ) ≤ Hr M := by
      have := Hr_mono hM8; rw [Hr_eight] at this; linarith
    exact le_trans (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
      (bound_of_good hk hc (by omega) hH8)

/-- **Erdős 169, variant.** For every `k ≥ 3`, `f(k) > (2/3) log W(k)`. -/
theorem erdos_169.variants.two_thirds (k : ℕ) (hk : 3 ≤ k) :
    ENNReal.ofReal (2 / 3 * Real.log (Erdos138.W k)) < f k := by
  have hf1 := f_ge_one (k := k) (by omega)
  rcases W_cases k hk with hW | ⟨N, hN8, hW, c, hc⟩
  · rw [hW]; simp only [Nat.cast_zero, Real.log_zero, mul_zero]
    exact lt_of_lt_of_le (by simp) hf1
  · have hH8 : (2 : ℝ) ≤ Hr N := by
      have := Hr_mono hN8; rw [Hr_eight] at this; linarith
    have hb := bound_of_good hk hc (by omega) hH8
    have hg := Hr_gt_log N hN8
    rw [hW]; push_cast
    refine lt_of_lt_of_le ?_ hb
    rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]
    linarith

/-- **Erdős 169, variant.** Some constant `c > 1/2` has `f(k) ≥ c log W(k)` for every `k ≥ 3`. -/
theorem erdos_169.variants.const_gt_half :
    ∃ c > (1 / 2 : ℝ), ∀ k ≥ 3, ENNReal.ofReal (c * Real.log (Erdos138.W k)) ≤ f k :=
  ⟨2 / 3, by norm_num, fun k hk => (erdos_169.variants.two_thirds k hk).le⟩

end ErdosLean.Erdos169
