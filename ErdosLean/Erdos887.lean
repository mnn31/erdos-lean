import FormalConjectures.ErdosProblems.«887»

/-!
# Erdős Problem 887: divisors in `(√n, √n + C n^{1/4})`

1. `card_window_le_one` / `card_window_le_four`: for every `n`, the window with `C = 1` contains
   at most one divisor of `n`, and the window with `C = 2` contains at most four.
   A divisor `d` in the window has `2√n < d + n/d < 2√n + C²`, and `d ↦ d + n/d` is
   injective on divisors above `√n`. So five divisors need `C > 2`, and `C = 1` allows only one.

2. `five_divisors_infinite`: with `C = 7/2` there are infinitely many `n` with at least five
   divisors in the window. The family is `n = u(u+2)(u+3)(u+5)` where `(u+2)(u+3) = 3v(v+1)`
   (a Pell equation). Writing `v = w + 1`, also `n = 9 w (w+1) (w+2) (w+3)`, and the five
   divisors are `(u+2)(u+3)`, `3(w+1)(w+3)`, `(u+2)(u+5)`, `(u+3)(u+5)`, `3(w+2)(w+3)`.
   (Asymptotically every `C > 2√3 ≈ 3.464` works; `7/2` is a convenient rational.)

3. `erdos_887_rosenfeld_4_false`: the statement `Erdos887.erdos_887.variants.rosenfeld_4`, which
   asks that `4` be the greatest `K` such that for some `C > 0` infinitely many `n` have at least
   `K` divisors in the window, is false: `5` belongs to that set (with `C = 40`).
   The construction, posted on the erdosproblems.com forum for problem 887, is
   `n = (x² - 1)(x² - 4)(x² - 16)(x² - 49)` where `z² = 56 x² + 65`.
   Four divisors come from the balanced splits of `{±1, ±2, ±4, ±7}`, and the fifth is
   `x⁴ - 35x² + 56 + 2xz`, since `(x⁴ - 35x² + 56)² - n = (2xz)²`.
   We write `x = w + 7` so that every quantity is a polynomial in `w` with natural coefficients.
-/

open Filter Finset Real

namespace ErdosLean.Erdos887

/- ## Part 1: upper bound -/

/-- Key inequality: a divisor `d = n / e` with `√n < d < √n + C n^{1/4}` has `d + e < 2√n + C²`. -/
lemma sum_lt (d e : ℕ) (C : ℝ) (hC : 0 < C) (hpos : 0 < d * e)
    (hlo : √((d * e : ℕ) : ℝ) < d)
    (hhi : (d : ℝ) < √((d * e : ℕ) : ℝ) + C * ((d * e : ℕ) : ℝ) ^ ((1 : ℝ) / 4)) :
    ((d : ℝ) + e) < 2 * √((d * e : ℕ) : ℝ) + C ^ 2 := by
  have hd0 : (0 : ℝ) < d := by
    have : 0 < d := Nat.pos_of_mul_pos_right hpos
    exact_mod_cast this
  have he0 : (0 : ℝ) ≤ e := by positivity
  set s := √(d : ℝ) with hs
  set r := √(e : ℝ) with hr
  have hs2 : s ^ 2 = d := Real.sq_sqrt hd0.le
  have hr2 : r ^ 2 = e := Real.sq_sqrt he0
  have hspos : 0 < s := Real.sqrt_pos.mpr hd0
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hsq : √((d * e : ℕ) : ℝ) = s * r := by
    push_cast; exact Real.sqrt_mul hd0.le _
  set f := ((d * e : ℕ) : ℝ) ^ ((1 : ℝ) / 4) with hf
  have hf0 : 0 ≤ f := by positivity
  have hf2 : f ^ 2 = √((d * e : ℕ) : ℝ) := by
    rw [hf, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hsq] at hlo hhi hf2
  -- s > f since s² = d > √n = f²
  have hsf : f < s := by
    have : f ^ 2 < s ^ 2 := by rw [hf2, hs2]; exact hlo
    exact lt_of_pow_lt_pow_left₀ 2 hspos.le this
  -- (s - r) * s = d - √n < C f < C s
  have hsr : s - r < C := by
    have h1 : (s - r) * s = (d : ℝ) - s * r := by rw [← hs2]; ring
    have h2 : (d : ℝ) - s * r < C * s := by
      have : C * f < C * s := mul_lt_mul_of_pos_left hsf hC
      linarith
    have h3 : (s - r) * s < C * s := by rw [h1]; exact h2
    exact lt_of_mul_lt_mul_right h3 hspos.le
  have hrs : r < s := by
    have : s * r < s * s := by nlinarith [hs2]
    exact lt_of_mul_lt_mul_left this hspos.le
  have hsq' : (s - r) ^ 2 < C ^ 2 := by
    have : 0 ≤ s - r := by linarith
    exact pow_lt_pow_left₀ hsr this (by norm_num)
  have : (d : ℝ) + e = (s - r) ^ 2 + 2 * (s * r) := by rw [← hs2, ← hr2]; ring
  rw [this]; linarith

/-- Divisors above `√n` have strictly increasing `d + n/d`. -/
lemma sum_strictMono (n d d' : ℕ) (hd : d ∣ n) (hd' : d' ∣ n) (hlt : d < d')
    (h1 : n < d * d) (_h2 : n < d' * d') : d + n / d < d' + n / d' := by
  obtain ⟨e, he⟩ := hd
  obtain ⟨e', he'⟩ := hd'
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp at h1
    · exact h
  have hd'pos : 0 < d' := by omega
  have hq : n / d = e := by rw [he]; exact Nat.mul_div_cancel_left e hdpos
  have hq' : n / d' = e' := by rw [he']; exact Nat.mul_div_cancel_left e' hd'pos
  rw [hq, hq']
  have hdd : n < d * d' := lt_of_lt_of_le h1 (Nat.mul_le_mul_left _ hlt.le)
  zify at *
  nlinarith [mul_pos (show (0 : ℤ) < (d' : ℤ) - d by linarith)
    (show (0 : ℤ) < (d : ℤ) * d' - n by linarith)]

lemma mem_window_facts (n d : ℕ) (C : ℝ)
    (h : d ∈ ({d ∈ Ioo ⌊√(n : ℝ)⌋₊ ⌈√(n : ℝ) + C * (n : ℝ) ^ ((1 : ℝ) / 4)⌉₊ | d ∣ n} : Finset ℕ)) :
    d ∣ n ∧ √(n : ℝ) < d ∧ (d : ℝ) < √(n : ℝ) + C * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  rw [Finset.mem_filter, Finset.mem_Ioo] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h3, ?_, Nat.lt_ceil.mp h2⟩
  have := Nat.lt_floor_add_one (√(n : ℝ))
  have h1' : ((⌊√(n : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast h1
  push_cast at h1'
  linarith

/-- General counting: all values `d + n/d` for window divisors lie strictly between `⌊2√n⌋`
and `⌊2√n⌋ + 1 + C²`. -/
lemma card_window_le (n : ℕ) (C : ℝ) (hC : 0 < C) (m : ℕ) (hm : C ^ 2 ≤ (m : ℝ)) :
    #{d ∈ Ioo ⌊√(n : ℝ)⌋₊ ⌈√(n : ℝ) + C * (n : ℝ) ^ ((1 : ℝ) / 4)⌉₊ | d ∣ n} ≤ m := by
  set A := ({d ∈ Ioo ⌊√(n : ℝ)⌋₊ ⌈√(n : ℝ) + C * (n : ℝ) ^ ((1 : ℝ) / 4)⌉₊ | d ∣ n} : Finset ℕ)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- n = 0: the window is empty
    subst hn
    have : A = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro d hd
      obtain ⟨_, h2, h3⟩ := mem_window_facts 0 d C hd
      simp at h2 h3
      linarith
    rw [this]; simp
  set a := ⌊2 * √(n : ℝ)⌋₊ with ha
  have key : ∀ d ∈ A, d + n / d ∈ Ioo a (a + 1 + m) := by
    intro d hd
    obtain ⟨hdvd, hlo, hhi⟩ := mem_window_facts n d C hd
    obtain ⟨e, he⟩ := hdvd
    have hdpos : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h; simp at he; omega
      · exact h
    have hq : n / d = e := by rw [he]; exact Nat.mul_div_cancel_left e hdpos
    rw [hq]
    have hpos : 0 < d * e := by rw [← he]; exact hn
    rw [he] at hlo hhi
    have hs := sum_lt d e C hC hpos hlo hhi
    rw [← he] at hs hlo
    -- lower: d + e > 2√n
    have hlow : 2 * √(n : ℝ) < (d : ℝ) + e := by
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hdpos
      have hsn : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
      have hne : (n : ℝ) = d * e := by exact_mod_cast he
      have hsn0 : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
      -- (d - √n)^2 > 0 and d * e = n give d + e > 2 √n
      have h1 : (d : ℝ) * (d + e) > d * (2 * √(n : ℝ)) := by
        nlinarith [mul_pos (sub_pos.mpr hlo) (sub_pos.mpr hlo)]
      exact lt_of_mul_lt_mul_left h1 hd0.le
    rw [Finset.mem_Ioo]
    constructor
    · by_contra hc
      push Not at hc
      have : ((d + e : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hc
      have h2 : (a : ℝ) ≤ 2 * √(n : ℝ) := Nat.floor_le (by positivity)
      push_cast at this
      linarith
    · have h2 : 2 * √(n : ℝ) < (a : ℝ) + 1 := Nat.lt_floor_add_one _
      have : ((d + e : ℕ) : ℝ) < ((a + 1 + m : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  have hinj : Set.InjOn (fun d => d + n / d) (A : Set ℕ) := by
    intro d hd d' hd' heq
    simp only at heq
    obtain ⟨hdv, hlo, _⟩ := mem_window_facts n d C hd
    obtain ⟨hdv', hlo', _⟩ := mem_window_facts n d' C hd'
    have sqlt : ∀ x : ℕ, √(n : ℝ) < x → n < x * x := by
      intro x hx
      have h0 : (0 : ℝ) ≤ √(n : ℝ) := Real.sqrt_nonneg _
      have : (n : ℝ) < (x : ℝ) * x := by
        have := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
        nlinarith
      exact_mod_cast this
    rcases lt_trichotomy d d' with h | h | h
    · have := sum_strictMono n d d' hdv hdv' h (sqlt d hlo) (sqlt d' hlo'); omega
    · exact h
    · have := sum_strictMono n d' d hdv' hdv h (sqlt d' hlo') (sqlt d hlo); omega
  calc #A ≤ #(Ioo a (a + 1 + m)) := Finset.card_le_card_of_injOn _ (fun d hd => key d hd) hinj
    _ = m := by simp only [Nat.card_Ioo]; omega

/-- With `C = 1`, every `n` has at most ONE divisor in `(√n, √n + n^{1/4})`. -/
theorem card_window_le_one (n : ℕ) :
    #{d ∈ Ioo ⌊√(n : ℝ)⌋₊ ⌈√(n : ℝ) + 1 * (n : ℝ) ^ ((1 : ℝ) / 4)⌉₊ | d ∣ n} ≤ 1 :=
  card_window_le n 1 one_pos 1 (by norm_num)

/-- With `C = 2`, every `n` has at most FOUR divisors in `(√n, √n + 2 n^{1/4})`. -/
theorem card_window_le_four (n : ℕ) :
    #{d ∈ Ioo ⌊√(n : ℝ)⌋₊ ⌈√(n : ℝ) + 2 * (n : ℝ) ^ ((1 : ℝ) / 4)⌉₊ | d ∣ n} ≤ 4 :=
  card_window_le n 2 two_pos 4 (by norm_num)

/- ## Shared lemma: membership in the counted window -/

/-- A divisor `d` of `n` with `n < d²` and `d < √n + C n^{1/4}` lies in the counted set. -/
lemma mem_window (n d : ℕ) (B : ℝ) (hdvd : d ∣ n) (hlo : n < d ^ 2) (hhi : (d : ℝ) < B) :
    d ∈ ({d ∈ Ioo ⌊√(n : ℝ)⌋₊ ⌈B⌉₊ | d ∣ n} : Finset ℕ) := by
  rw [Finset.mem_filter, Finset.mem_Ioo]
  refine ⟨⟨?_, ?_⟩, hdvd⟩
  · rw [Nat.floor_lt (Real.sqrt_nonneg _)]
    have hd : (0 : ℝ) < d := by
      have : 0 < d := by
        rcases Nat.eq_zero_or_pos d with h | h
        · subst h; simp at hlo
        · exact h
      exact_mod_cast this
    rw [Real.sqrt_lt' hd]
    exact_mod_cast hlo
  · exact Nat.lt_ceil.mpr hhi

/- ## Five divisors with `C = 7/2`, infinitely often -/

namespace FiveDivisors

/-- `n = u (u+2) (u+3) (u+5)`. -/
def N (u : ℕ) : ℕ := u * (u + 2) * (u + 3) * (u + 5)

/-- Solutions of `(u+2)(u+3) = 3 (w+1)(w+2)` (that is, `(2u+5)² - 3(2w+3)² = -2`),
starting from `(u, w) = (1843, 1064)`. -/
def pell : ℕ → ℕ × ℕ
  | 0 => (1843, 1064)
  | k + 1 => (2 * (pell k).1 + 3 * (pell k).2 + 7, (pell k).1 + 2 * (pell k).2 + 4)

lemma pell_spec (k : ℕ) :
    ((pell k).1 + 2) * ((pell k).1 + 3) = 3 * ((pell k).2 + 1) * ((pell k).2 + 2) ∧
      1064 ≤ (pell k).2 := by
  induction k with
  | zero => simp [pell]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [pell]
    constructor
    · linear_combination h1
    · omega

lemma pell_strictMono : StrictMono (fun k => (pell k).1) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  simp only [pell]
  omega

lemma N_strictMono : StrictMono N := by
  refine strictMono_nat_of_lt_succ fun u => ?_
  unfold N
  have : u * (u + 2) < (u + 1) * (u + 1 + 2) := by nlinarith
  calc u * (u + 2) * (u + 3) * (u + 5) < (u + 1) * (u + 1 + 2) * (u + 3) * (u + 5) := by gcongr
    _ ≤ (u + 1) * (u + 1 + 2) * (u + 1 + 3) * (u + 1 + 5) := by gcongr <;> omega

lemma key (u w : ℕ) (hw : 1064 ≤ w) (h : (u + 2) * (u + 3) = 3 * (w + 1) * (w + 2)) :
    5 ≤ #{d ∈ Ioo ⌊√(N u : ℝ)⌋₊ ⌈√(N u : ℝ) + 7 / 2 * (N u : ℝ) ^ ((1 : ℝ) / 4)⌉₊ | d ∣ N u} := by
  -- u (u+5) = 3 w (w+3)
  have hu5 : u * (u + 5) = 3 * w * (w + 3) := by
    have : u * (u + 5) + 6 = (u + 2) * (u + 3) := by ring
    have : 3 * w * (w + 3) + 6 = 3 * (w + 1) * (w + 2) := by ring
    omega
  have hn9 : N u = 9 * (w * (w + 1) * (w + 2) * (w + 3)) := by
    have : N u = (u * (u + 5)) * ((u + 2) * (u + 3)) := by simp only [N]; ring
    rw [this, hu5, h]; ring
  have hnA : N u = (u + 2) * (u + 3) * (u * (u + 5)) := by simp only [N]; ring
  have hnB : N u = 3 * (w + 1) * (w + 3) * (3 * w * (w + 2)) := by rw [hn9]; ring
  have hnC : N u = (u + 2) * (u + 5) * (u * (u + 3)) := by simp only [N]; ring
  have hnD : N u = (u + 3) * (u + 5) * (u * (u + 2)) := by simp only [N]; ring
  have hnE : N u = 3 * (w + 2) * (w + 3) * (3 * w * (w + 1)) := by rw [hn9]; ring
  have hAB : 3 * (w + 1) * (w + 3) = (u + 2) * (u + 3) + 3 * (w + 1) := by rw [h]; ring
  have hAC : (u + 2) * (u + 5) = (u + 2) * (u + 3) + 2 * (u + 2) := by ring
  have hAD : (u + 3) * (u + 5) = (u + 2) * (u + 3) + 3 * (u + 3) := by ring
  have hAE : 3 * (w + 2) * (w + 3) = (u + 2) * (u + 3) + 6 * (w + 2) := by rw [h]; ring
  have hAe : (u + 2) * (u + 3) = u * (u + 5) + 6 := by ring
  have hc1 : 3 * (w + 1) < 2 * (u + 2) := by
    by_contra hc
    push Not at hc
    nlinarith
  have hc2 : u < 2 * w + 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have hApos : 0 < (u + 2) * (u + 3) := by positivity
  have hpoly : 16 * (6 * (w + 3)) ^ 4 < 2401 * N u := by
    rw [hn9]
    have h1 : 97 * (w + 3) ≤ 98 * w := by omega
    have h2 : (97 * (w + 3)) ^ 3 ≤ (98 * w) ^ 3 := Nat.pow_le_pow_left h1 3
    have h3 : w ^ 3 ≤ w * (w + 1) * (w + 2) := by
      have : w ^ 3 = w * w * w := by ring
      rw [this]; gcongr <;> omega
    have hw0 : 0 < w ^ 3 := by positivity
    have e1 : 16 * (6 * (w + 3)) ^ 4 = (w + 3) * (20736 * (w + 3) ^ 3) := by ring
    have e2 : 2401 * (9 * (w * (w + 1) * (w + 2) * (w + 3))) =
        (w + 3) * (21609 * (w * (w + 1) * (w + 2))) := by ring
    have e3 : (97 * (w + 3)) ^ 3 = 912673 * (w + 3) ^ 3 := by ring
    have e4 : (98 * w) ^ 3 = 941192 * w ^ 3 := by ring
    rw [e3, e4] at h2
    have key : 20736 * (w + 3) ^ 3 < 21609 * (w * (w + 1) * (w + 2)) := by
      generalize (w + 3) ^ 3 = X at *
      generalize w ^ 3 = Y at *
      generalize w * (w + 1) * (w + 2) = Z at *
      omega
    rw [e1, e2]
    exact Nat.mul_lt_mul_of_pos_left key (by omega)
  generalize N u = n at *
  generalize (u + 2) * (u + 3) = A at *
  generalize u * (u + 5) = e1 at *
  generalize 3 * (w + 1) * (w + 3) = B at *
  generalize (u + 2) * (u + 5) = D3 at *
  generalize (u + 3) * (u + 5) = D4 at *
  generalize 3 * (w + 2) * (w + 3) = E at *
  have o1 : A < B := by omega
  have o2 : B < D3 := by omega
  have o3 : D3 < D4 := by omega
  have o4 : D4 < E := by omega
  -- lower bound
  have hlo1 : n < A ^ 2 := by
    rw [hnA, sq]
    exact Nat.mul_lt_mul_of_pos_left (by omega) hApos
  have hlo : ∀ d, A ≤ d → n < d ^ 2 := fun d hd =>
    lt_of_lt_of_le hlo1 (Nat.pow_le_pow_left hd 2)
  -- upper bound: E = e1 + 6 (w + 3) < √n + (7/2) n^{1/4}
  have hEe : E = e1 + 6 * (w + 3) := by omega
  have hs : (e1 : ℝ) ≤ √(n : ℝ) := by
    have h1 : e1 ^ 2 ≤ n := by
      rw [hnA, sq]
      exact Nat.mul_le_mul_right _ (by omega)
    have h2 : √((e1 : ℝ) ^ 2) ≤ √(n : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast h1)
    rwa [Real.sqrt_sq (by positivity)] at h2
  have hq : ((6 * (w + 3) : ℕ) : ℝ) < 7 / 2 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have hx0 : (0 : ℝ) ≤ ((6 * (w + 3) : ℕ) : ℝ) := by positivity
    have h4 : ((6 * (w + 3) : ℕ) : ℝ) ^ 4 < (7 / 2 : ℝ) ^ 4 * (n : ℝ) := by
      have : ((16 * (6 * (w + 3)) ^ 4 : ℕ) : ℝ) < ((2401 * n : ℕ) : ℝ) := by exact_mod_cast hpoly
      push_cast at this ⊢
      nlinarith
    have h4' : (1 : ℝ) / 4 = ((4 : ℕ) : ℝ)⁻¹ := by norm_num
    calc ((6 * (w + 3) : ℕ) : ℝ)
        = (((6 * (w + 3) : ℕ) : ℝ) ^ 4) ^ ((4 : ℕ) : ℝ)⁻¹ := by
          rw [Real.pow_rpow_inv_natCast hx0 (by norm_num)]
      _ < ((7 / 2 : ℝ) ^ 4 * (n : ℝ)) ^ ((4 : ℕ) : ℝ)⁻¹ := by
          exact Real.rpow_lt_rpow (by positivity) h4 (by positivity)
      _ = 7 / 2 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
          rw [Real.mul_rpow (by positivity) (by positivity),
            Real.pow_rpow_inv_natCast (by norm_num) (by norm_num), h4']
  have hhi : ∀ d, d ≤ E → (d : ℝ) < √(n : ℝ) + 7 / 2 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
    intro d hd
    have h1 : d ≤ e1 + 6 * (w + 3) := by omega
    have h2 : (d : ℝ) ≤ (e1 : ℝ) + ((6 * (w + 3) : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  -- collect the five divisors
  have hsub : ({A, B, D3, D4, E} : Finset ℕ) ⊆
      {d ∈ Ioo ⌊√(n : ℝ)⌋₊ ⌈√(n : ℝ) + 7 / 2 * (n : ℝ) ^ ((1 : ℝ) / 4)⌉₊ | d ∣ n} := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact mem_window _ _ _ ⟨_, hnA⟩ (hlo _ le_rfl) (hhi _ (by omega))
    · exact mem_window _ _ _ ⟨_, hnB⟩ (hlo _ (by omega)) (hhi _ (by omega))
    · exact mem_window _ _ _ ⟨_, hnC⟩ (hlo _ (by omega)) (hhi _ (by omega))
    · exact mem_window _ _ _ ⟨_, hnD⟩ (hlo _ (by omega)) (hhi _ (by omega))
    · exact mem_window _ _ _ ⟨_, hnE⟩ (hlo _ (by omega)) (hhi _ le_rfl)
  have hcard : ({A, B, D3, D4, E} : Finset ℕ).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_pair (by omega)]
  calc 5 = ({A, B, D3, D4, E} : Finset ℕ).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

end FiveDivisors

open FiveDivisors in
/-- Infinitely many `n` have at least five divisors in `(√n, √n + (7/2) n^{1/4})`. -/
theorem five_divisors_infinite :
    Set.Infinite {n : ℕ | 5 ≤ #{d ∈ Ioo ⌊√(n : ℝ)⌋₊ ⌈√(n : ℝ) + 7 / 2 * (n : ℝ) ^ ((1 : ℝ) / 4)⌉₊ |
      d ∣ n}} := by
  refine Set.infinite_of_injective_forall_mem (f := fun k => N (pell k).1) ?_ ?_
  · intro a b hab
    exact pell_strictMono.injective (N_strictMono.injective hab)
  · intro k
    obtain ⟨h1, h2⟩ := pell_spec k
    exact key (pell k).1 (pell k).2 h2 h1

/- ## The variant `rosenfeld_4` is false -/

namespace Rosenfeld4

/-- `(x² - 1)(x² - 4)(x² - 16)(x² - 49)` with `x = w + 7`. -/
def N (w : ℕ) : ℕ := w * (w + 3) * (w + 5) * (w + 6) * (w + 8) * (w + 9) * (w + 11) * (w + 14)

/-- Solutions of `z² - 56 x² = 65`, starting from `(37, 277)`, as pairs `(x, z)`. -/
def pell : ℕ → ℕ × ℕ
  | 0 => (37, 277)
  | k + 1 => (15 * (pell k).1 + 2 * (pell k).2, 112 * (pell k).1 + 15 * (pell k).2)

lemma pell_spec (k : ℕ) :
    (pell k).2 ^ 2 = 56 * (pell k).1 ^ 2 + 65 ∧ 37 ≤ (pell k).1 := by
  induction k with
  | zero => simp [pell]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [pell]
    constructor
    · linear_combination h1
    · omega

lemma pell_strictMono : StrictMono (fun k => (pell k).1) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  have := (pell_spec k).2
  simp only [pell]
  omega

lemma N_strictMono : StrictMono N := by
  refine strictMono_nat_of_lt_succ fun w => ?_
  unfold N
  have h1 : w * (w + 3) < (w + 1) * (w + 1 + 3) := by nlinarith
  calc w * (w + 3) * (w + 5) * (w + 6) * (w + 8) * (w + 9) * (w + 11) * (w + 14)
      < (w + 1) * (w + 1 + 3) * (w + 5) * (w + 6) * (w + 8) * (w + 9) * (w + 11) * (w + 14) := by
        gcongr
    _ ≤ (w + 1) * (w + 1 + 3) * (w + 1 + 5) * (w + 1 + 6) * (w + 1 + 8) * (w + 1 + 9) *
          (w + 1 + 11) * (w + 1 + 14) := by
        gcongr <;> omega

lemma key (w z : ℕ) (hw : 30 ≤ w) (hz : z ^ 2 = 56 * (w + 7) ^ 2 + 65) :
    5 ≤ #{d ∈ Ioo ⌊√(N w : ℝ)⌋₊ ⌈√(N w : ℝ) + 40 * (N w : ℝ) ^ ((1 : ℝ) / 4)⌉₊ | d ∣ N w} := by
  set n := N w with hn
  set P : ℕ := w ^ 4 + 28 * w ^ 3 + 259 * w ^ 2 + 882 * w + 742 with hP
  set e1 : ℕ := w * (w + 8) * (w + 9) * (w + 11) with he1
  set d1 : ℕ := (w + 6) * (w + 5) * (w + 3) * (w + 14) with hd1
  set d2 : ℕ := (w + 5) * (w + 9) * (w + 3) * (w + 11) with hd2
  set d3 : ℕ := (w + 6) * (w + 8) * (w + 3) * (w + 11) with hd3
  set d4 : ℕ := (w + 6) * (w + 8) * (w + 5) * (w + 9) with hd4
  set d5 : ℕ := P + 2 * (w + 7) * z with hd5
  clear_value d5 d4 d3 d2 d1 e1 P n
  -- the four balanced splits
  have hn1 : n = d1 * e1 := by simp only [hn, N, hd1, he1]; ring
  have hn2 : n = d2 * ((w + 6) * (w + 8) * (w * (w + 14))) := by simp only [hn, N, hd2]; ring
  have hn3 : n = d3 * ((w + 5) * (w + 9) * (w * (w + 14))) := by simp only [hn, N, hd3]; ring
  have hn4 : n = d4 * ((w + 3) * (w + 11) * (w * (w + 14))) := by simp only [hn, N, hd4]; ring
  -- the Pell divisor
  have hsq : (2 * (w + 7) * z) ^ 2 + d2 = (15 * (w + 7) ^ 2 + 8) ^ 2 := by
    have : (2 * (w + 7) * z) ^ 2 = 4 * (w + 7) ^ 2 * z ^ 2 := by ring
    rw [this, hz, hd2]; ring
  have hd2pos : 0 < d2 := by rw [hd2]; positivity
  have hlt2 : 2 * (w + 7) * z < 15 * (w + 7) ^ 2 + 8 := by
    have : (2 * (w + 7) * z) ^ 2 < (15 * (w + 7) ^ 2 + 8) ^ 2 := by omega
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) this
  have hd2P : d2 = P + 15 * (w + 7) ^ 2 + 8 := by simp only [hd2, hP]; ring
  have hle : 2 * (w + 7) * z ≤ P := by
    have : 15 * (w + 7) ^ 2 + 8 ≤ P := by
      have e : P + 1 = 15 * (w + 7) ^ 2 + 8 + (w ^ 4 + 28 * w ^ 3 + 244 * w ^ 2 + 672 * w) := by
        simp only [hP]; ring
      have : 1 ≤ 672 * w := by omega
      have : 0 ≤ w ^ 4 + 28 * w ^ 3 + 244 * w ^ 2 := Nat.zero_le _
      omega
    omega
  have hn5 : n = d5 * (P - 2 * (w + 7) * z) := by
    zify [hle] at hz ⊢
    simp only [hn, N, hd5, hP]
    push_cast
    linear_combination (4 * ((w : ℤ) + 7) ^ 2) * hz
  -- ordering d1 < d5 < d2 < d3 < d4
  have he1d1 : d1 = e1 + 180 * (w + 7) := by simp only [hd1, he1]; ring
  have hd1P : d1 + 112 = P + 90 * (w + 7) := by simp only [hd1, hP]; ring
  have hz45 : 45 ≤ z := by
    by_contra hc
    have h1 : z ^ 2 ≤ 44 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : 37 ^ 2 ≤ (w + 7) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have h15 : d1 < d5 := by
    have : 90 * (w + 7) ≤ 2 * (w + 7) * z :=
      calc 90 * (w + 7) = 2 * (w + 7) * 45 := by ring
        _ ≤ 2 * (w + 7) * z := Nat.mul_le_mul_left _ hz45
    omega
  have h52 : d5 < d2 := by omega
  have h23 : d2 < d3 := by
    have : d3 = d2 + 3 * ((w + 3) * (w + 11)) := by simp only [hd2, hd3]; ring
    have : 0 < (w + 3) * (w + 11) := by positivity
    omega
  have h34 : d3 < d4 := by
    have : d4 = d3 + 12 * ((w + 6) * (w + 8)) := by simp only [hd3, hd4]; ring
    have : 0 < (w + 6) * (w + 8) := by positivity
    omega
  -- lower bound: every d_i exceeds √n
  have hlo1 : n < d1 ^ 2 := by
    rw [hn1, sq]
    have : 0 < d1 := by rw [hd1]; positivity
    exact Nat.mul_lt_mul_of_pos_left (by omega) this
  have hlo : ∀ d, d1 ≤ d → n < d ^ 2 := fun d hd =>
    lt_of_lt_of_le hlo1 (Nat.pow_le_pow_left hd 2)
  -- upper bound: d4 < e1 + 40 (w² + 14 w) ≤ √n + 40 n^{1/4}
  have hd4e1 : d4 + 10 * w ^ 2 + 50 * w = e1 + 40 * (w ^ 2 + 14 * w) + 2160 := by
    simp only [hd4, he1]; ring
  have hd4lt : d4 < e1 + 40 * (w ^ 2 + 14 * w) := by
    have : 30 * 30 ≤ w ^ 2 := by rw [sq]; exact Nat.mul_le_mul hw hw
    omega
  have hs : (e1 : ℝ) ≤ √(n : ℝ) := by
    have h1 : e1 ^ 2 ≤ n := by
      rw [hn1, sq]
      exact Nat.mul_le_mul_right _ (by omega)
    have h2 : √((e1 : ℝ) ^ 2) ≤ √(n : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast h1)
    rwa [Real.sqrt_sq (by positivity)] at h2
  have hq : ((w ^ 2 + 14 * w : ℕ) : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have hpow : (w ^ 2 + 14 * w) ^ 4 ≤ n := by
      have a1 : w ^ 2 + 14 * w ≤ (w + 3) * (w + 11) := by ring_nf; omega
      have a2 : w ^ 2 + 14 * w ≤ (w + 5) * (w + 9) := by ring_nf; omega
      have a3 : w ^ 2 + 14 * w ≤ (w + 6) * (w + 8) := by ring_nf; omega
      have hn' : n = (w * (w + 14)) * ((w + 3) * (w + 11)) * ((w + 5) * (w + 9)) *
          ((w + 6) * (w + 8)) := by simp only [hn, N]; ring
      have a0 : w ^ 2 + 14 * w = w * (w + 14) := by ring
      calc (w ^ 2 + 14 * w) ^ 4
          = (w ^ 2 + 14 * w) * (w ^ 2 + 14 * w) * (w ^ 2 + 14 * w) * (w ^ 2 + 14 * w) := by ring
        _ ≤ (w * (w + 14)) * ((w + 3) * (w + 11)) * ((w + 5) * (w + 9)) *
              ((w + 6) * (w + 8)) := by
            rw [← a0]; gcongr
        _ = n := hn'.symm
    have hpow' : ((w ^ 2 + 14 * w : ℕ) : ℝ) ^ 4 ≤ (n : ℝ) := by exact_mod_cast hpow
    have h4 : (1 : ℝ) / 4 = ((4 : ℕ) : ℝ)⁻¹ := by norm_num
    calc ((w ^ 2 + 14 * w : ℕ) : ℝ)
        = (((w ^ 2 + 14 * w : ℕ) : ℝ) ^ 4) ^ ((4 : ℕ) : ℝ)⁻¹ := by
          rw [Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
      _ ≤ (n : ℝ) ^ ((4 : ℕ) : ℝ)⁻¹ := by
          exact Real.rpow_le_rpow (by positivity) hpow' (by positivity)
      _ = (n : ℝ) ^ ((1 : ℝ) / 4) := by rw [h4]
  have hhi : ∀ d, d ≤ d4 → (d : ℝ) < √(n : ℝ) + 40 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
    intro d hd
    have h1 : d < e1 + 40 * (w ^ 2 + 14 * w) := lt_of_le_of_lt hd hd4lt
    have h2 : (d : ℝ) < (e1 : ℝ) + 40 * ((w ^ 2 + 14 * w : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  -- collect the five divisors
  have hsub : ({d1, d5, d2, d3, d4} : Finset ℕ) ⊆
      {d ∈ Ioo ⌊√(n : ℝ)⌋₊ ⌈√(n : ℝ) + 40 * (n : ℝ) ^ ((1 : ℝ) / 4)⌉₊ | d ∣ n} := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact mem_window _ _ _ ⟨_, hn1⟩ (hlo _ le_rfl) (hhi _ (by omega))
    · exact mem_window _ _ _ ⟨_, hn5⟩ (hlo _ (by omega)) (hhi _ (by omega))
    · exact mem_window _ _ _ ⟨_, hn2⟩ (hlo _ (by omega)) (hhi _ (by omega))
    · exact mem_window _ _ _ ⟨_, hn3⟩ (hlo _ (by omega)) (hhi _ (by omega))
    · exact mem_window _ _ _ ⟨_, hn4⟩ (hlo _ (by omega)) (hhi _ le_rfl)
  have hcard : ({d1, d5, d2, d3, d4} : Finset ℕ).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_pair (by omega)]
  calc 5 = ({d1, d5, d2, d3, d4} : Finset ℕ).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

end Rosenfeld4

open Rosenfeld4 in
/-- The repository statement `Erdos887.erdos_887.variants.rosenfeld_4` is false. -/
theorem erdos_887_rosenfeld_4_false :
    ¬ (type_of% @Erdos887.erdos_887.variants.rosenfeld_4) := by
  intro h
  have h5 : (5 : ℕ) ∈ {K : ℕ | ∃ C > (0 : ℝ),
      Infinite {n : ℕ | K ≤ #{ d ∈ Ioo ⌊√n⌋₊ ⌈√n + C * n^((1 : ℝ) / 4)⌉₊ | d ∣ n }}} := by
    refine ⟨40, by norm_num, ?_⟩
    rw [Set.infinite_coe_iff]
    refine Set.infinite_of_injective_forall_mem
      (f := fun k => N ((pell k).1 - 7)) ?_ ?_
    · intro a b hab
      have ha := (pell_spec a).2
      have hb := (pell_spec b).2
      have := N_strictMono.injective (show N ((pell a).1 - 7) = N ((pell b).1 - 7) from hab)
      exact pell_strictMono.injective (show (pell a).1 = (pell b).1 by omega)
    · intro k
      obtain ⟨hz, hx⟩ := pell_spec k
      have hx7 : (pell k).1 - 7 + 7 = (pell k).1 := by omega
      have := key ((pell k).1 - 7) (pell k).2 (by omega) (by rw [hx7]; exact hz)
      simpa using this
  have := h.2 h5
  omega

end ErdosLean.Erdos887
