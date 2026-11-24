import FormalConjectures.ErdosProblems.«177»

/-!
# Erdős Problem 177: `IsOptimalGrowth` cannot be satisfied

formal-conjectures PR #6756 (head `0b725ba8`) states Erdős Problem 177 as
`erdos_177 : IsOptimalGrowth (answer(sorry) : ℕ → ℝ)`, where `IsOptimalGrowth H` asks for an
admissible `h` with `h = O(H)` such that `H = O(h')` for every admissible `h'`. We prove
`not_isOptimalGrowth : ∀ H, ¬ Erdos177.IsOptimalGrowth H`, so that statement is false for every
choice of answer. The definitions are imported from the PR's own module, not copied.

The key step is `exists_admissible_not_isBigO`: for every admissible `h₁` there is an admissible
`h₂` with `¬ h₁ =O[atTop] h₂`. Let `f₁` witness `h₁`. Build a chain `M 0 = 1`,
`M (K+1) = 2 (K+1) · M K · e_K`, where `e_K ≥ 1` comes from van der Waerden
(`Combinatorics.exists_mono_homothetic_copy`) so that `f₁` is constant on a progression
`a, a + M (K+1), …, a + K · M (K+1)` with `a ≥ 1`. Hence `h₁ (M K) ≥ K`. The ratios
`M (K+1) / M K` are even, so the colouring `g = (-1)^(digit sum of n in the mixed radix given by
the chain)` satisfies `|∑_{i<N} g (a + i d)| ≤ 4 · M K / d` whenever `d ∣ M K`. Since
`d ∣ M d` for every `d ≥ 1`, `g` witnesses an admissible `h₂` with `h₂ (M K) = 4` for all `K`.
Then `h₁ = O(h₂)` would force `K ≤ 4 C` for all large `K`.

We also prove that no admissible `h` is `O(1)` along `atTop`, and that the set of exponents
`α` with some admissible `h = O(d ^ α)` is upward closed and contains only positive reals. This
supports restating the problem as a value question about `sInf admissibleExponents`.
-/

open Finset Filter Asymptotics Erdos177

namespace ErdosLean.Erdos177

/- ### Mixed-radix colourings with arbitrary even radices -/

/-- The radix at position `c`: `2 * (s c + 1)`, always even and at least `2`. -/
def R (s : ℕ → ℕ) (c : ℕ) : ℕ := 2 * (s c + 1)

lemma R_pos (s : ℕ → ℕ) (c : ℕ) : 0 < R s c := by unfold R; omega

lemma two_le_R (s : ℕ → ℕ) (c : ℕ) : 2 ≤ R s c := by unfold R; omega

/-- Digit sum of `n` in the mixed radix with bases `R s c, R s (c+1), …`. -/
def digitSum (s : ℕ → ℕ) (c n : ℕ) : ℕ :=
  if _h : n = 0 then 0 else n % R s c + digitSum s (c + 1) (n / R s c)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹_›) (two_le_R s c)

lemma digitSum_zero (s : ℕ → ℕ) (c : ℕ) : digitSum s c 0 = 0 := by
  rw [digitSum]; simp

lemma digitSum_eq (s : ℕ → ℕ) (c n : ℕ) :
    digitSum s c n = n % R s c + digitSum s (c + 1) (n / R s c) := by
  by_cases h : n = 0
  · subst h; simp [digitSum_zero]
  · rw [digitSum]; simp [h]

/-- `radix s c K = R s c * R s (c+1) * ⋯ * R s (c+K-1)`. -/
def radix (s : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 1
  | c, K + 1 => R s c * radix s (c + 1) K

lemma radix_pos (s : ℕ → ℕ) (c K : ℕ) : 0 < radix s c K := by
  induction K generalizing c with
  | zero => simp [radix]
  | succ K ih => simp only [radix]; exact Nat.mul_pos (R_pos s c) (ih _)

lemma radix_succ_right (s : ℕ → ℕ) (K : ℕ) : ∀ c, radix s c (K + 1) = radix s c K * R s (c + K) := by
  induction K with
  | zero => intro c; simp [radix]
  | succ K ih =>
    intro c
    rw [radix, ih (c + 1), radix, show c + 1 + K = c + (K + 1) by omega]
    ring

lemma digitSum_block (s : ℕ → ℕ) (K : ℕ) : ∀ c j x, x < radix s c K →
    digitSum s c (j * radix s c K + x) = digitSum s c x + digitSum s (c + K) j := by
  induction K with
  | zero => intro c j x hx; simp [radix] at hx; subst hx; simp [radix, digitSum_zero]
  | succ K ih =>
    intro c j x hx
    simp only [radix] at hx ⊢
    have hR := R_pos s c
    have hx' : x / R s c < radix s (c + 1) K := by
      rw [Nat.div_lt_iff_lt_mul hR]; linarith
    have e : j * (R s c * radix s (c + 1) K) + x
        = x % R s c + R s c * (j * radix s (c + 1) K + x / R s c) := by
      have := Nat.mod_add_div x (R s c); nlinarith
    rw [digitSum_eq s c (j * _ + x), digitSum_eq s c x, e, Nat.add_mul_mod_self_left,
      Nat.add_mul_div_left _ _ hR, Nat.mod_mod,
      Nat.div_eq_of_lt (Nat.mod_lt _ hR), zero_add, ih (c + 1) j _ hx',
      show c + 1 + K = c + (K + 1) by omega]
    ring

/-- The sign `(-1)^(digit sum)`. -/
def sgn (s : ℕ → ℕ) (c n : ℕ) : ℤ := (-1) ^ digitSum s c n

lemma sgn_sq (s : ℕ → ℕ) (c n : ℕ) : sgn s c n = 1 ∨ sgn s c n = -1 := by
  unfold sgn; exact neg_one_pow_eq_or ℤ _

lemma abs_sgn (s : ℕ → ℕ) (c n : ℕ) : |sgn s c n| = 1 := by
  rcases sgn_sq s c n with h | h <;> simp [h]

lemma sgn_block (s : ℕ → ℕ) (K c j x : ℕ) (hx : x < radix s c K) :
    sgn s c (j * radix s c K + x) = sgn s c x * sgn s (c + K) j := by
  unfold sgn; rw [digitSum_block s K c j x hx, pow_add]

/-- Because every radix is even, consecutive pairs `2m, 2m+1` get opposite signs. -/
lemma sgn_pair (s : ℕ → ℕ) (e m : ℕ) : sgn s e (2 * m + 1) = - sgn s e (2 * m) := by
  have hR : R s e = 2 * (s e + 1) := rfl
  set q := 2 * m / R s e
  set t := 2 * m % R s e
  have h1 : R s e * q + t = 2 * m := Nat.div_add_mod (2 * m) (R s e)
  have ht : t < R s e := Nat.mod_lt _ (by omega)
  have htev : t % 2 = 0 := by
    simp only [t]
    rw [Nat.mod_mod_of_dvd _ ⟨s e + 1, hR⟩]; omega
  have ht1 : t + 1 < R s e := by omega
  have e1 : 2 * m + 1 = (t + 1) + R s e * q := by linarith
  have e2 : 2 * m = t + R s e * q := by linarith
  have hRpos := R_pos s e
  unfold sgn
  rw [digitSum_eq _ _ (2 * m + 1), digitSum_eq _ _ (2 * m), e1, e2,
    Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ hRpos, Nat.add_mul_div_left _ _ hRpos,
    Nat.mod_eq_of_lt ht1, Nat.mod_eq_of_lt ht, Nat.div_eq_of_lt ht1, Nat.div_eq_of_lt ht]
  ring

lemma sum_sgn_bound (s : ℕ → ℕ) (e : ℕ) (n : ℕ) : |∑ i ∈ range n, sgn s e i| ≤ 1 := by
  have h2 : ∀ M, ∑ i ∈ range (2 * M), sgn s e i = 0 := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
        sgn_pair s e M]
      ring
  obtain ⟨M, rfl | rfl⟩ := Nat.even_or_odd' n
  · simp [h2]
  · rw [sum_range_succ, h2, zero_add, abs_sgn]

/- ### Progression sums -/

/-- Sum of `f` over the arithmetic progression `a, a + d, …, a + (N-1) d`. -/
def apSum (f : ℕ → ℤ) (a d N : ℕ) : ℤ := ∑ i ∈ range N, f (a + i * d)

lemma apSum_eq_sub (f : ℕ → ℤ) (a d N : ℕ) (hd : 0 < d) :
    apSum f a d N = ∑ n ∈ range (a + N * d), (if n % d = a % d then f n else 0)
      - ∑ n ∈ range a, (if n % d = a % d then f n else 0) := by
  rw [← Finset.sum_Ico_eq_sub _ (by omega)]
  induction N with
  | zero => simp [apSum]
  | succ N ih =>
    rw [apSum, sum_range_succ, ← apSum, ih, show a + (N + 1) * d = a + N * d + d by ring,
      ← Finset.sum_Ico_consecutive _ (show a ≤ a + N * d by omega)
        (show a + N * d ≤ a + N * d + d by omega)]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range, show a + N * d + d - (a + N * d) = d by omega,
      Finset.sum_eq_single 0]
    · simp [Nat.add_mul_mod_self_right]
    · intro k hk hk0
      refine ite_eq_right_iff.2 fun h => absurd h ?_
      intro h
      rw [show a + N * d + k = a + k + N * d by ring, Nat.add_mul_mod_self_right] at h
      have h' : k ≡ 0 [MOD d] := Nat.ModEq.add_left_cancel' a (by simpa [Nat.ModEq] using h)
      have := Nat.mod_eq_of_lt (Finset.mem_range.1 hk)
      simp [Nat.ModEq] at h'
      omega
    · intro h; exact absurd (Finset.mem_range.2 hd) h

section Partial

variable (s : ℕ → ℕ) (d K r : ℕ)

/-- The colouring `sgn s 0` restricted to one residue class mod `d`. -/
def resG (n : ℕ) : ℤ := if n % d = r % d then sgn s 0 n else 0

lemma resG_block (hdP : d ∣ radix s 0 K) (j y : ℕ) (hy : y < radix s 0 K) :
    resG s d r (j * radix s 0 K + y) = resG s d r y * sgn s K j := by
  obtain ⟨Q, hQ⟩ := hdP
  unfold resG
  have hm : (j * radix s 0 K + y) % d = y % d := by
    rw [hQ, show j * (d * Q) + y = y + d * (j * Q) by ring, Nat.add_mul_mod_self_left]
  rw [hm, sgn_block s K 0 j y hy, zero_add]
  split_ifs <;> simp

lemma resG_count (hd : 0 < d) (hdP : d ∣ radix s 0 K) (x : ℕ) (hx : x ≤ radix s 0 K) :
    |∑ y ∈ range x, resG s d r y| ≤ ((radix s 0 K / d : ℕ) : ℤ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∑ y ∈ range x, |resG s d r y|
      = ((Nat.count (fun y => y ≡ r [MOD d]) x : ℕ) : ℤ) := by
    rw [Nat.count_eq_card_filter_range, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold resG Nat.ModEq
    split_ifs <;> simp [*, abs_sgn]
  rw [h1, Nat.count_modEq_card x hd r]
  have : x / d + (if r % d < x % d then 1 else 0) ≤ radix s 0 K / d := by
    rcases hx.lt_or_eq with hx | rfl
    · have := Nat.div_lt_div_of_lt_of_dvd hdP hx
      split_ifs <;> omega
    · rw [Nat.mod_eq_zero_of_dvd hdP]; simp
  exact_mod_cast this

lemma resG_partial_bound (hd : 0 < d) (hdP : d ∣ radix s 0 K) (M : ℕ) :
    |∑ n ∈ range M, resG s d r n| ≤ 2 * ((radix s 0 K / d : ℕ) : ℤ) := by
  set P := radix s 0 K with hP
  have hPpos : 0 < P := radix_pos s 0 K
  set T := ∑ y ∈ range P, resG s d r y
  have hblocks : ∀ q, ∑ n ∈ range (q * P), resG s d r n = T * ∑ j ∈ range q, sgn s K j := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show (q + 1) * P = q * P + P by ring, sum_range_add, ih, sum_range_succ, mul_add]
      congr 1
      simp only [T, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [resG_block s d K r hdP q y (Finset.mem_range.1 hy)]
  have htail : ∀ q x, x ≤ P →
      ∑ y ∈ range x, resG s d r (q * P + y) = sgn s K q * ∑ y ∈ range x, resG s d r y := by
    intro q x hx
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [resG_block s d K r hdP q y (by have := Finset.mem_range.1 hy; omega)]
    ring
  have hM : M = M / P * P + M % P := by rw [Nat.div_add_mod']
  rw [hM, sum_range_add, hblocks, htail _ _ (Nat.mod_lt _ hPpos).le]
  have hT := resG_count s d K r hd hdP P le_rfl
  have hx := resG_count s d K r hd hdP (M % P) (Nat.mod_lt _ hPpos).le
  have hE := sum_sgn_bound s K (M / P)
  calc _ ≤ |T * ∑ j ∈ range (M / P), sgn s K j|
          + |sgn s K (M / P) * ∑ y ∈ range (M % P), resG s d r y| :=
        abs_add_le _ _
    _ = |T| * |∑ j ∈ range (M / P), sgn s K j| + |∑ y ∈ range (M % P), resG s d r y| := by
        rw [abs_mul, abs_mul, abs_sgn, one_mul]
    _ ≤ ((P / d : ℕ) : ℤ) * 1 + ((P / d : ℕ) : ℤ) := by
        gcongr
    _ = _ := by ring

end Partial

/-- **Key bound.** If every radix is even (built into `R`) and `d ∣ radix s 0 K`, every
progression of difference `d` has `|∑ sgn s 0| ≤ 4 · radix s 0 K / d`. -/
lemma sgn_apSum_bound (s : ℕ → ℕ) (d K a N : ℕ) (hd : 0 < d) (hdP : d ∣ radix s 0 K) :
    |apSum (sgn s 0) a d N| ≤ 4 * ((radix s 0 K / d : ℕ) : ℤ) := by
  rw [apSum_eq_sub _ _ _ _ hd]
  have h1 := resG_partial_bound s d K a hd hdP (a + N * d)
  have h2 := resG_partial_bound s d K a hd hdP a
  unfold resG at h1 h2
  calc _ ≤ _ := abs_sub _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/- ### The adaptive chain (van der Waerden step) -/

/-- Van der Waerden: for every `±1` function `f`, every `B` and every length `L`, there are
`e ≥ 1` and `a ≥ 1` with `f` constant on `a, a + B e, …, a + (L-1) B e`. -/
lemma exists_mono (f : ℕ → ℤ) (hf : ∀ n, f n = 1 ∨ f n = -1) (B L : ℕ) :
    ∃ e ≥ 1, ∃ a ≥ 1, ∀ i < L, f (a + i * (B * e)) = f a := by
  obtain ⟨e, he, b, col, hcol⟩ :=
    Combinatorics.exists_mono_homothetic_copy (range L) (fun n : ℕ => f (1 + B * n) = 1)
  refine ⟨e, he, 1 + B * b, by omega, fun i hi => ?_⟩
  have h1 := hcol i (Finset.mem_range.2 hi)
  have h0 := hcol 0 (Finset.mem_range.2 (by omega))
  simp only [smul_eq_mul, mul_zero, zero_add] at h1 h0
  rw [show 1 + B * b + i * (B * e) = 1 + B * (e * i + b) by ring]
  rcases hf (1 + B * (e * i + b)) with p | p <;> rcases hf (1 + B * b) with q | q <;>
    simp_all

open Classical in
/-- A choice of the multiplier `e` from `exists_mono` (default `1`). -/
noncomputable def eChoice (f : ℕ → ℤ) (B L : ℕ) : ℕ :=
  if h : ∃ e ≥ 1, ∃ a ≥ 1, ∀ i < L, f (a + i * (B * e)) = f a then h.choose else 1

lemma one_le_eChoice (f : ℕ → ℤ) (B L : ℕ) : 1 ≤ eChoice f B L := by
  unfold eChoice
  split_ifs with h
  · exact h.choose_spec.1
  · exact le_rfl

lemma eChoice_spec (f : ℕ → ℤ) (hf : ∀ n, f n = 1 ∨ f n = -1) (B L : ℕ) :
    ∃ a ≥ 1, ∀ i < L, f (a + i * (B * eChoice f B L)) = f a := by
  have h := exists_mono f hf B L
  unfold eChoice
  rw [dif_pos h]
  exact h.choose_spec.2

/-- The chain `M 0 = 1`, `M (K+1) = 2 (K+1) · M K · e_K`. -/
noncomputable def chainM (f : ℕ → ℤ) : ℕ → ℕ
  | 0 => 1
  | K + 1 => 2 * (K + 1) * chainM f K * eChoice f (2 * (K + 1) * chainM f K) (K + 1)

/-- The multiplier at step `K`. -/
noncomputable def eK (f : ℕ → ℤ) (K : ℕ) : ℕ := eChoice f (2 * (K + 1) * chainM f K) (K + 1)

lemma chainM_succ (f : ℕ → ℤ) (K : ℕ) :
    chainM f (K + 1) = 2 * (K + 1) * chainM f K * eK f K := rfl

/-- The radix sequence `s` with `R s K = 2 (K+1) e_K = M (K+1) / M K`. -/
noncomputable def sSeq (f : ℕ → ℤ) (K : ℕ) : ℕ := (K + 1) * eK f K - 1

lemma R_sSeq (f : ℕ → ℤ) (K : ℕ) : R (sSeq f) K = 2 * (K + 1) * eK f K := by
  have he : 1 ≤ eK f K := one_le_eChoice _ _ _
  have : 1 ≤ (K + 1) * eK f K := Nat.one_le_iff_ne_zero.2 (by positivity)
  unfold R sSeq
  rw [Nat.sub_add_cancel this]
  ring

lemma radix_sSeq (f : ℕ → ℤ) (K : ℕ) : radix (sSeq f) 0 K = chainM f K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [radix_succ_right, ih, zero_add, R_sSeq, chainM_succ]
    ring

lemma one_le_chainM (f : ℕ → ℤ) (K : ℕ) : 1 ≤ chainM f K := by
  induction K with
  | zero => exact le_rfl
  | succ K ih =>
    rw [chainM_succ]
    have := one_le_eChoice f (2 * (K + 1) * chainM f K) (K + 1)
    have h2 : 1 ≤ 2 * (K + 1) * chainM f K * eK f K := Nat.one_le_iff_ne_zero.2 (by
      unfold eK; positivity)
    exact h2

lemma self_le_chainM (f : ℕ → ℤ) (K : ℕ) : K ≤ chainM f K := by
  cases K with
  | zero => exact Nat.zero_le _
  | succ K =>
    rw [chainM_succ]
    have h1 := one_le_chainM f K
    have h2 : 1 ≤ eK f K := one_le_eChoice _ _ _
    have : 1 ≤ chainM f K * eK f K := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith

lemma dvd_chainM_self (f : ℕ → ℤ) (d : ℕ) (hd : 1 ≤ d) : d ∣ chainM f d := by
  obtain ⟨K, rfl⟩ : ∃ K, d = K + 1 := ⟨d - 1, by omega⟩
  rw [chainM_succ]
  exact Dvd.intro (2 * chainM f K * eK f K) (by ring)

/-- `f₁` has a monochromatic progression of length `K+1` and difference `M (K+1)`, starting at
some `a ≥ 1`. -/
lemma chainM_mono (f : ℕ → ℤ) (hf : ∀ n, f n = 1 ∨ f n = -1) (K : ℕ) :
    ∃ a ≥ 1, ∀ i < K + 1, f (a + i * chainM f (K + 1)) = f a :=
  eChoice_spec f hf (2 * (K + 1) * chainM f K) (K + 1)

/- ### The two admissible functions -/

/-- Any admissible `h₁` (with witness colouring `f₁`) is at least `K` at `M K`. -/
lemma le_h_chainM (h : ℕ → ℝ) (f : ℕ → ℤ) (hf : ∀ n, f n = 1 ∨ f n = -1)
    (hb : ∀ d ≥ 1, ∀ a ≥ 1, ∀ N : ℕ, |((∑ i ∈ range N, f (a + i * d) : ℤ) : ℝ)| ≤ h d)
    (K : ℕ) : (K : ℝ) ≤ h (chainM f K) := by
  cases K with
  | zero =>
    have := hb (chainM f 0) (one_le_chainM f 0) 1 le_rfl 0
    simpa using this
  | succ K =>
    obtain ⟨a, ha, hconst⟩ := chainM_mono f hf K
    have hsum : (∑ i ∈ range (K + 1), f (a + i * chainM f (K + 1)) : ℤ)
        = (K + 1 : ℤ) * f a := by
      rw [Finset.sum_congr rfl fun i hi => hconst i (Finset.mem_range.1 hi)]
      simp
    have := hb (chainM f (K + 1)) (one_le_chainM f _) a ha (K + 1)
    rw [hsum] at this
    have hfa : |(f a : ℝ)| = 1 := by rcases hf a with e | e <;> simp [e]
    push_cast at this ⊢
    rw [abs_mul, hfa, mul_one, abs_of_nonneg (by positivity)] at this
    exact this

open Classical in
/-- The admissible bound for the even-radix colouring built on the chain of `f`. -/
noncomputable def hChain (f : ℕ → ℤ) (d : ℕ) : ℝ :=
  if ∃ K, d = chainM f K then 4 else 4 * ((chainM f d / d : ℕ) : ℝ)

lemma hChain_chainM (f : ℕ → ℤ) (K : ℕ) : hChain f (chainM f K) = 4 := by
  unfold hChain
  rw [if_pos ⟨K, rfl⟩]

lemma isAdmissible_hChain (f : ℕ → ℤ) : IsAdmissible (hChain f) := by
  refine ⟨sgn (sSeq f) 0, fun n => sgn_sq _ 0 n, fun d hd a _ N => ?_⟩
  have key : ∀ K, d ∣ chainM f K →
      |((∑ i ∈ range N, sgn (sSeq f) 0 (a + i * d) : ℤ) : ℝ)|
        ≤ 4 * ((chainM f K / d : ℕ) : ℝ) := by
    intro K hdK
    have := sgn_apSum_bound (sSeq f) d K a N (by omega) (by rw [radix_sSeq]; exact hdK)
    rw [radix_sSeq] at this
    unfold apSum at this
    have h2 := (Int.cast_le (R := ℝ)).2 this
    push_cast at h2 ⊢
    exact h2
  unfold hChain
  split_ifs with hc
  · obtain ⟨K, rfl⟩ := hc
    have := key K dvd_rfl
    rwa [Nat.div_self (by omega), Nat.cast_one, mul_one] at this
  · exact key d (dvd_chainM_self f d hd)

/- ### Main theorems -/

/-- No admissible function is minimal up to constants: for every admissible `h₁` there is an
admissible `h₂` with `h₁ ≠ O(h₂)`. -/
theorem exists_admissible_not_isBigO (h₁ : ℕ → ℝ) (hh₁ : Erdos177.IsAdmissible h₁) :
    ∃ h₂, Erdos177.IsAdmissible h₂ ∧ ¬ h₁ =O[atTop] h₂ := by
  obtain ⟨f, hf, hb⟩ := hh₁
  refine ⟨hChain f, isAdmissible_hChain f, fun hO => ?_⟩
  obtain ⟨C, hC⟩ := hO.bound
  have hM : Tendsto (chainM f) atTop atTop :=
    tendsto_atTop_mono (self_le_chainM f) tendsto_id
  obtain ⟨K, hK1, hK2⟩ := ((hM.eventually hC).and (eventually_gt_atTop ⌈4 * C⌉₊)).exists
  rw [hChain_chainM, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at hK1
  have hlow := le_h_chainM h₁ f hf hb K
  have hn := Real.le_norm_self (h₁ (chainM f K))
  have hc := Nat.le_ceil (4 * C)
  have hK : ((⌈4 * C⌉₊ : ℕ) : ℝ) < K := by exact_mod_cast hK2
  linarith

/-- **`IsOptimalGrowth` from formal-conjectures PR #6756 is unsatisfiable.** Hence
`erdos_177 : IsOptimalGrowth (answer(sorry))` is false for every answer. -/
theorem not_isOptimalGrowth (H : ℕ → ℝ) : ¬ Erdos177.IsOptimalGrowth H := by
  rintro ⟨⟨h₁, hh₁, h₁H⟩, hall⟩
  obtain ⟨h₂, hh₂, hn⟩ := exists_admissible_not_isBigO h₁ hh₁
  exact hn (h₁H.trans (hall h₂ hh₂))

/-- The same statement with both PR definitions unfolded by hand. -/
theorem not_exists_isOptimalGrowth_unfolded :
    ¬ ∃ H : ℕ → ℝ,
      (∃ h : ℕ → ℝ, (∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
          ∀ d ≥ 1, ∀ a ≥ 1, ∀ N : ℕ, |((∑ i ∈ Finset.range N, f (a + i * d) : ℤ) : ℝ)| ≤ h d)
        ∧ h =O[atTop] H) ∧
      ∀ h : ℕ → ℝ, (∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
          ∀ d ≥ 1, ∀ a ≥ 1, ∀ N : ℕ, |((∑ i ∈ Finset.range N, f (a + i * d) : ℤ) : ℝ)| ≤ h d)
        → H =O[atTop] h :=
  fun ⟨H, hH⟩ => not_isOptimalGrowth H hH

/- ### Towards a corrected statement -/

/-- Every admissible `h` is unbounded along `atTop`: `h ≠ O(1)`. -/
theorem not_isBigO_one (h : ℕ → ℝ) (hh : Erdos177.IsAdmissible h) :
    ¬ h =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  obtain ⟨f, hf, hb⟩ := hh
  intro hO
  obtain ⟨C, hC⟩ := hO.bound
  have hM : Tendsto (chainM f) atTop atTop :=
    tendsto_atTop_mono (self_le_chainM f) tendsto_id
  obtain ⟨K, hK1, hK2⟩ := ((hM.eventually hC).and (eventually_gt_atTop ⌈C⌉₊)).exists
  rw [norm_one, mul_one] at hK1
  have hlow := le_h_chainM h f hf hb K
  have hn := Real.le_norm_self (h (chainM f K))
  have hc := Nat.le_ceil C
  have hK : ((⌈C⌉₊ : ℕ) : ℝ) < K := by exact_mod_cast hK2
  linarith

/-- The exponents `α` for which some admissible `h` is `O(d ^ α)`. -/
def admissibleExponents : Set ℝ :=
  {α | ∃ h, Erdos177.IsAdmissible h ∧ h =O[atTop] fun d : ℕ => (d : ℝ) ^ α}

/-- The set of admissible exponents is upward closed. -/
theorem mem_admissibleExponents_of_le {α β : ℝ} (hα : α ∈ admissibleExponents) (hab : α ≤ β) :
    β ∈ admissibleExponents := by
  obtain ⟨h, hh, hO⟩ := hα
  refine ⟨h, hh, hO.trans (IsBigO.of_bound 1 ?_)⟩
  filter_upwards [eventually_ge_atTop 1] with d hd
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _), one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hd' hab

/-- Every admissible exponent is positive. -/
theorem pos_of_mem_admissibleExponents {α : ℝ} (hα : α ∈ admissibleExponents) : 0 < α := by
  obtain ⟨h, hh, hO⟩ := hα
  refine not_le.mp fun hneg => ?_
  apply not_isBigO_one h hh
  refine hO.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop 1] with d hd
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _), norm_one, one_mul]
  exact Real.rpow_le_one_of_one_le_of_nonpos hd' hneg

end ErdosLean.Erdos177
