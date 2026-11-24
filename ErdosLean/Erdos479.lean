import FormalConjectures.ErdosProblems.«479»

/-!
# Erdős Problem 479, the case `k = -2 ^ i`

We prove `erdos_479.variants.neg_two_pow`: for every `i ≥ 1` there are infinitely many `n` with
`2 ^ n ≡ -2 ^ i (mod n)`, that is, `n ∣ 2 ^ n + 2 ^ i`.

Start from `n = 2 ^ i`. Given `n ∣ 2 ^ n + 2 ^ i` with `n ≥ 2i`, put `X = n - i`. Bang's theorem
gives a prime `p` with `2` of order `2X` modulo `p`, so `p ∣ 2 ^ X + 1` and `p ≡ 1 (mod 2X)`.
Then `p > n` and `n p ∣ 2 ^ (n p) + 2 ^ i`. Modulo `p` this is Fermat's little theorem. Modulo
`n` it holds because `n ∣ 2 ^ i (2 ^ X + 1)` divides `2 ^ n (2 ^ (n (p - 1)) - 1)`, since
`2X ∣ p - 1`. Iterating gives an infinite increasing sequence.

Mathlib does not contain Bang's theorem, so `exists_prime_orderOf_two_eq` proves the base `2`
case from the cyclotomic polynomial `Φ_N`: a prime factor of `Φ_N(2)` that does not divide `N`
has the required order, and otherwise `Φ_N(2)` would be a single prime `p ∣ N`, which the bounds
`(q - 1) ^ φ(m) < Φ_m(q) ≤ (q + 1) ^ φ(m)` rule out unless `N = 6`.

Problem 479 has no variants in formal-conjectures at the pinned commit, so the statement is
copied verbatim from the proposed addition to `479.lean`.
-/

namespace ErdosLean.Erdos479

open Polynomial

/-- A prime dividing `Φ_n(2)` sees `2` as a root of the `n`-th cyclotomic polynomial. -/
lemma isRoot_two_of_dvd {n p : ℕ} (hp : p ∣ ((cyclotomic n ℤ).eval 2).natAbs) :
    (cyclotomic n (ZMod p)).IsRoot 2 := by
  have h : (((cyclotomic n ℤ).eval 2 : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 (Int.natCast_dvd.2 hp)
  rw [IsRoot.def, ← map_cyclotomic_int n (ZMod p), ← Int.cast_two, eval_intCast_map]
  simpa using h

/-- If `p` is prime, `2` is a root of `Φ_n` modulo `p` and `n = p ^ k * m` with `p ∤ m`, then
`2` has order `m` modulo `p`. -/
lemma orderOf_two_eq {n p k m : ℕ} [Fact p.Prime] (hroot : (cyclotomic n (ZMod p)).IsRoot 2)
    (hn : n = p ^ k * m) (hm : ¬p ∣ m) : orderOf (2 : ZMod p) = m := by
  subst hn
  have : NeZero (m : ZMod p) := ⟨fun h => hm ((ZMod.natCast_eq_zero_iff m p).1 h)⟩
  exact (isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp hroot).eq_orderOf.symm

/-- `Φ_{m p^{j+1}}(z) = Φ_{m p}(z^{p^j})`. -/
lemma eval_cyclotomic_mul_pow {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ∀ (j : ℕ) (z : ℤ), (cyclotomic (m * p ^ (j + 1)) ℤ).eval z =
      (cyclotomic (m * p) ℤ).eval (z ^ p ^ j)
  | 0, z => by simp
  | j + 1, z => by
    rw [pow_succ p (j + 1), ← mul_assoc, ← cyclotomic_expand_eq_cyclotomic hp
      (dvd_mul_of_dvd_right (dvd_pow_self p (Nat.succ_ne_zero j)) m), expand_eval,
      eval_cyclotomic_mul_pow hp m j, ← pow_mul, ← pow_succ']

lemma cyclotomic_eval_real (n : ℕ) (z : ℤ) :
    (cyclotomic n ℝ).eval (z : ℝ) = (((cyclotomic n ℤ).eval z : ℤ) : ℝ) := by
  rw [← map_cyclotomic_int n ℝ, eval_intCast_map]
  rfl

lemma size_aux {p x : ℕ} (hp : 5 ≤ p) (hx : 2 ≤ x) : p * (x + 1) + 1 ≤ x ^ p := by
  have h1 : 2 * p ≤ 2 ^ (p - 1) := by
    induction p, hp using Nat.le_induction with
    | base => norm_num
    | succ q hq ih =>
      rw [show q + 1 - 1 = (q - 1) + 1 by omega, pow_succ]
      omega
  have h2 : 2 ^ (p - 1) ≤ x ^ (p - 1) := Nat.pow_le_pow_left hx _
  have h3 : x ^ p = x ^ (p - 1) * x := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h3]
  nlinarith [Nat.mul_le_mul_right x (h1.trans h2)]

/-- Bang's theorem for base `2`: for `N ≥ 2`, `N ≠ 6`, some prime `p` has
`orderOf (2 : ZMod p) = N`. -/
theorem exists_prime_orderOf_two_eq {N : ℕ} (hN : 2 ≤ N) (h6 : N ≠ 6) :
    ∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = N := by
  set M := ((cyclotomic N ℤ).eval 2).natAbs with hM_def
  have hM : 1 < M := by
    have := sub_one_lt_natAbs_cyclotomic_eval (q := 2) (by omega : 1 < N) (by norm_num)
    simpa using this
  by_contra hcon
  push Not at hcon
  -- Every prime factor `q` of `M` divides `N`, and `2` has order `N / q ^ v_q(N)` modulo `q`.
  have key : ∀ q, q.Prime → q ∣ M → ∃ k m, ¬q ∣ m ∧ N = q ^ (k + 1) * m ∧
      orderOf (2 : ZMod q) = m ∧ 2 ≤ m ∧ m ∣ q - 1 := by
    intro q hq hqM
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨k, m, hm, hNkm⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (by omega : N ≠ 0) q hq.one_lt.ne'
    have hord := orderOf_two_eq (isRoot_two_of_dvd hqM) hNkm hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hNkm
      omega
    have h20 : (2 : ZMod q) ≠ 0 := by
      intro h
      have h1 := pow_orderOf_eq_one (2 : ZMod q)
      rw [hord, h, zero_pow hm0] at h1
      exact zero_ne_one h1
    have hm1 : m ≠ 1 := by
      rintro rfl
      rw [orderOf_eq_one_iff, ← one_add_one_eq_two, add_eq_left] at hord
      exact one_ne_zero hord
    obtain _ | k := k
    · exact absurd (by rw [hNkm, pow_zero, one_mul, hord]) (hcon q hq)
    exact ⟨k, m, hm, hNkm, hord, by omega, hord ▸ ZMod.orderOf_dvd_card_sub_one h20⟩
  have hp : M.minFac.Prime := Nat.minFac_prime (by omega)
  set p := M.minFac with hp_def
  obtain ⟨k, m, hm, hN', hord, hm2, hmp⟩ := key p hp (Nat.minFac_dvd M)
  have hp2 : p ≠ 2 := by
    rintro h
    rw [h] at hmp
    have := Nat.le_of_dvd one_pos hmp
    omega
  have hmlt : m < p := by
    have := Nat.le_of_dvd (by have := hp.two_le; omega) hmp
    omega
  -- `p` is the only prime factor of `M`.
  have huniq : ∀ {q}, q.Prime → q ∣ M → q = p := by
    intro q hq hqM
    by_contra hne
    obtain ⟨k', m', hm', hN'', -, hm'2, hm'q⟩ := key q hq hqM
    have hqm : q ∣ m := by
      have h : q ∣ N := hN'' ▸ dvd_mul_of_dvd_left (dvd_pow_self q (Nat.succ_ne_zero k')) m'
      rw [hN'] at h
      exact (Nat.Coprime.pow_right _ ((Nat.coprime_primes hq hp).2 hne)).dvd_of_dvd_mul_left h
    have hpm' : p ∣ m' := by
      have h : p ∣ N := hN' ▸ dvd_mul_of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero k)) m
      rw [hN''] at h
      exact (Nat.Coprime.pow_right _
        ((Nat.coprime_primes hp hq).2 (Ne.symm hne))).dvd_of_dvd_mul_left h
    have := Nat.le_of_dvd (by omega) hqm
    have := Nat.le_of_dvd (by omega) hpm'
    have := Nat.le_of_dvd (by have := hq.two_le; omega) hm'q
    omega
  have : Fact p.Prime := ⟨hp⟩
  -- `p ^ 2 ∤ M`, by lifting the exponent.
  have hsq : ¬p ^ 2 ∣ M := by
    intro h2
    set d := p ^ k * m with hd
    have hd0 : 0 < d := Nat.mul_pos (pow_pos hp.pos _) (by omega)
    have hNd : N = d * p := by rw [hN', hd]; ring
    have hdmem : d ∈ N.properDivisors := by
      rw [Nat.mem_properDivisors]
      exact ⟨⟨p, hNd⟩, hNd ▸ lt_mul_of_one_lt_right hd0 hp.one_lt⟩
    have hev : ((2 : ℤ) ^ d - 1) * (cyclotomic N ℤ).eval 2 ∣ (2 : ℤ) ^ N - 1 := by
      simpa using Polynomial.eval_dvd (x := (2 : ℤ))
        (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hdmem)
    have e1 : ((2 : ℤ) ^ d - 1) = ((2 ^ d - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
    have e2 : ((2 : ℤ) ^ N - 1) = ((2 ^ N - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
    have hnat : (2 ^ d - 1) * M ∣ 2 ^ N - 1 := by
      have := Int.natAbs_dvd_natAbs.mpr hev
      rwa [Int.natAbs_mul, e1, e2, Int.natAbs_natCast, Int.natAbs_natCast] at this
    have hpd : p ∣ 2 ^ d - 1 := by
      have h1 : (2 : ZMod p) ^ d = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, hord, hd]
        exact dvd_mul_left m _
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      rw [h1, sub_self]
    have hp2d : ¬p ∣ 2 ^ d := by
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    have hlte := padicValNat.pow_sub_pow (p := p) (hp.odd_of_ne_two hp2)
      (x := 2 ^ d) (y := 1) (Nat.one_lt_two_pow hd0.ne') (by simpa using hpd) hp2d
      hp.ne_zero
    rw [one_pow, ← pow_mul, ← hNd, padicValNat_self] at hlte
    have hdvd : p ^ (padicValNat p (2 ^ d - 1) + 2) ∣ 2 ^ N - 1 := by
      rw [pow_add]
      exact (Nat.mul_dvd_mul pow_padicValNat_dvd h2).trans hnat
    rw [padicValNat_dvd_iff_le (by
      have : 2 ≤ 2 ^ N := Nat.le_self_pow (by omega) 2
      omega), hlte] at hdvd
    omega
  have hMp : M = p := by
    have h := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : M ≠ 0) huniq
    generalize M.primeFactorsList.length = L at h
    rcases Nat.lt_or_ge L 2 with hL | hL
    · interval_cases L
      · simp at h; omega
      · simpa using h
    · exact absurd (h ▸ pow_dvd_pow p hL) hsq
  -- Size: `Φ_N(2) = Φ_{mp}(x)` with `x = 2 ^ p ^ k`, and `Φ_m(x ^ p) = Φ_{mp}(x) Φ_m(x)`.
  set x : ℕ := 2 ^ p ^ k with hx_def
  have hx2 : 2 ≤ x := Nat.le_self_pow (pow_ne_zero _ hp.ne_zero) 2
  have hΦ : (cyclotomic N ℤ).eval 2 = (cyclotomic (m * p) ℤ).eval (x : ℤ) := by
    rw [hN', mul_comm, eval_cyclotomic_mul_pow hp m k 2, hx_def]
    push_cast
    rfl
  have hexp : (cyclotomic m ℤ).eval ((x : ℤ) ^ p) =
      (cyclotomic (m * p) ℤ).eval (x : ℤ) * (cyclotomic m ℤ).eval (x : ℤ) := by
    rw [← expand_eval, cyclotomic_expand_eq_cyclotomic_mul hp hm, eval_mul]
  have hxR : (1 : ℝ) < x := by exact_mod_cast hx2
  have hφ : Nat.totient m ≠ 0 := (Nat.totient_pos.2 (by omega)).ne'
  have hlow := sub_one_pow_totient_lt_cyclotomic_eval hm2 (one_lt_pow₀ hxR hp.ne_zero)
  have hlow' := sub_one_pow_totient_lt_cyclotomic_eval hm2 hxR
  have hup := cyclotomic_eval_le_add_one_pow_totient hxR m
  have hA := cyclotomic_eval_real m (x : ℤ)
  have hB := cyclotomic_eval_real m ((x : ℤ) ^ p)
  have hC := cyclotomic_eval_real (m * p) (x : ℤ)
  push_cast at hA hB hC
  have hApos : 0 < (cyclotomic m ℝ).eval (x : ℝ) :=
    lt_of_le_of_lt (pow_nonneg (by linarith) _) hlow'
  have hBpos : 0 < (cyclotomic m ℝ).eval ((x : ℝ) ^ p) :=
    lt_of_le_of_lt (pow_nonneg (by nlinarith [one_lt_pow₀ hxR hp.ne_zero]) _) hlow
  have hBreal : (cyclotomic m ℝ).eval ((x : ℝ) ^ p) =
      (cyclotomic (m * p) ℝ).eval (x : ℝ) * (cyclotomic m ℝ).eval (x : ℝ) := by
    rw [hA, hB, hC, hexp]
    push_cast
    ring
  have hCpos : 0 < (cyclotomic (m * p) ℝ).eval (x : ℝ) := by
    rw [hBreal] at hBpos
    exact pos_of_mul_pos_left hBpos hApos.le
  have hCp : (cyclotomic (m * p) ℝ).eval (x : ℝ) = p := by
    have habs : ((cyclotomic (m * p) ℤ).eval (x : ℤ)).natAbs = p := by
      rw [← hΦ, ← hM_def, hMp]
    rw [hC] at hCpos ⊢
    have hCpos' : 0 < (cyclotomic (m * p) ℤ).eval (x : ℤ) := by exact_mod_cast hCpos
    rw [← Int.natAbs_of_nonneg hCpos'.le, habs]
    simp
  rw [hCp] at hBreal
  have hlt : (((x : ℝ) ^ p - 1)) ^ Nat.totient m < ((p : ℝ) * (x + 1)) ^ Nat.totient m := by
    calc ((x : ℝ) ^ p - 1) ^ Nat.totient m < (cyclotomic m ℝ).eval ((x : ℝ) ^ p) := hlow
      _ = p * (cyclotomic m ℝ).eval (x : ℝ) := hBreal
      _ ≤ p * ((x : ℝ) + 1) ^ Nat.totient m := by gcongr
      _ ≤ (p : ℝ) ^ Nat.totient m * ((x : ℝ) + 1) ^ Nat.totient m := by
          gcongr
          exact le_self_pow₀ (by exact_mod_cast hp.one_lt.le) hφ
      _ = ((p : ℝ) * (x + 1)) ^ Nat.totient m := (mul_pow _ _ _).symm
  have hlt' := lt_of_pow_lt_pow_left₀ _ (by positivity) hlt
  have hnat : x ^ p < p * (x + 1) + 1 := by
    have : (x : ℝ) ^ p < p * (x + 1) + 1 := by linarith
    exact_mod_cast this
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rcases Nat.lt_or_ge p 5 with hp5 | hp5
  · have hp3' : p = 3 := by
      interval_cases p
      · rfl
      · exact absurd hp (by norm_num)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : m = 2 := by
        have := Nat.le_of_dvd (by omega) hmp
        omega
      exact h6 (by rw [hN', this, hp3']; norm_num)
    · have hx8 : 8 ≤ x := by
        rw [hx_def, hp3']
        calc 8 = 2 ^ 3 ^ 1 := by norm_num
          _ ≤ 2 ^ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
      rw [hp3'] at hnat
      have h64 : 8 * 8 * x ≤ x * x * x := Nat.mul_le_mul (Nat.mul_le_mul hx8 hx8) le_rfl
      have : x ^ 3 = x * x * x := by ring
      linarith
  · have := size_aux hp5 hx2
    omega

/-- For `X ≥ 1` with `X ≠ 3`, some prime `p ≡ 1 (mod 2X)` divides `2 ^ X + 1`. -/
theorem exists_prime_dvd_two_pow_add_one {X : ℕ} (hX : 1 ≤ X) (h3 : X ≠ 3) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ 2 ^ X + 1 ∧ 2 * X ∣ p - 1 := by
  obtain ⟨p, hp, hord⟩ := exists_prime_orderOf_two_eq (N := 2 * X) (by omega) (by omega)
  have : Fact p.Prime := ⟨hp⟩
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h1 := pow_orderOf_eq_one (2 : ZMod p)
    rw [hord, h, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  refine ⟨p, hp, ?_, hord ▸ ZMod.orderOf_dvd_card_sub_one h20⟩
  have hsq : (2 : ZMod p) ^ X * (2 : ZMod p) ^ X = 1 := by
    rw [← pow_add, ← two_mul, ← hord, pow_orderOf_eq_one]
  have hne : (2 : ZMod p) ^ X ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have hneg : (2 : ZMod p) ^ X = -1 := (mul_self_eq_one_iff.mp hsq).resolve_left hne
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [hneg, neg_add_cancel]

/-- The lifting step: if `n ∣ 2 ^ n + 2 ^ i` with `n ≥ 2i`, and `p` is a prime dividing
`2 ^ (n - i) + 1` with `p ≡ 1 (mod 2 (n - i))`, then `n p ∣ 2 ^ (n p) + 2 ^ i`. -/
lemma lift {i n p : ℕ} (hn : (n : ℤ) ∣ 2 ^ n + 2 ^ i) (h2i : 2 * i ≤ n) (hn0 : 0 < n)
    (hp : p.Prime) (hpX : (p : ℤ) ∣ 2 ^ (n - i) + 1) (hX : 2 * (n - i) ∣ p - 1) :
    ((n * p : ℕ) : ℤ) ∣ 2 ^ (n * p) + 2 ^ i := by
  have : Fact p.Prime := ⟨hp⟩
  set X := n - i with hX_def
  have hnX : n = X + i := by omega
  have hpn : n < p := by
    have := Nat.le_of_dvd (by have := hp.two_le; omega) hX
    omega
  have hcop : IsCoprime (n : ℤ) (p : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2
      fun h => absurd (Nat.le_of_dvd hn0 h) (by omega))
  have e : (2 : ℤ) ^ n + 2 ^ i = 2 ^ i * (2 ^ X + 1) := by
    rw [hnX, pow_add]
    ring
  push_cast
  refine hcop.mul_dvd ?_ ?_
  · obtain ⟨t, ht⟩ := hX
    have h1 : (2 : ℤ) ^ X + 1 ∣ 2 ^ (2 * X) - 1 := ⟨2 ^ X - 1, by ring⟩
    have h2 : (2 : ℤ) ^ (2 * X) - 1 ∣ 2 ^ (n * (p - 1)) - 1 := by
      have := sub_dvd_pow_sub_pow ((2 : ℤ) ^ (2 * X)) 1 (n * t)
      rwa [one_pow, ← pow_mul, show 2 * X * (n * t) = n * (p - 1) by rw [ht]; ring] at this
    have h3 : (n : ℤ) ∣ 2 ^ n * (2 ^ (n * (p - 1)) - 1) :=
      (e ▸ hn).trans (mul_dvd_mul (pow_dvd_pow 2 (by omega)) (h1.trans h2))
    have hnp : n * p = n + n * (p - 1) := by
      have hle : n ≤ n * p := Nat.le_mul_of_pos_right n hp.pos
      rw [Nat.mul_sub_one]
      omega
    have e3 : (2 : ℤ) ^ (n + n * (p - 1)) + 2 ^ i =
        2 ^ n * (2 ^ (n * (p - 1)) - 1) + (2 ^ n + 2 ^ i) := by
      rw [pow_add]
      ring
    rw [hnp, e3]
    exact dvd_add h3 hn
  · have hpX' : (2 : ZMod p) ^ X + 1 = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hpX
      push_cast at this
      exact this
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [mul_comm, pow_mul, ZMod.pow_card, hnX, pow_add]
    linear_combination (2 : ZMod p) ^ i * hpX'

lemma two_pow_bounds (i : ℕ) : 2 * i ≤ 2 ^ i ∧ 2 ^ i ≠ i + 3 := by
  rcases Nat.lt_or_ge i 3 with h | h
  · interval_cases i <;> norm_num
  · have : 2 * i + 2 ≤ 2 ^ i := by
      induction i, h using Nat.le_induction with
      | base => norm_num
      | succ j hj ih =>
        rw [pow_succ]
        omega
    omega

/-- For every `i ≥ 1` there are infinitely many `n` with `2 ^ n ≡ -2 ^ i (mod n)`. -/
theorem erdos_479.variants.neg_two_pow :
    ∀ i ≥ 1, { n : ℕ | (2 : ℤ) ^ n ≡ -(2 ^ i) [ZMOD (n : ℤ)] }.Infinite := by
  intro i hi
  let good : ℕ → Prop := fun n => (n : ℤ) ∣ 2 ^ n + 2 ^ i ∧ 2 * i ≤ n ∧ 0 < n ∧ n ≠ i + 3
  have step : ∀ n, good n → ∃ n', good n' ∧ n < n' := by
    rintro n ⟨hn, h2i, hn0, hn3⟩
    obtain ⟨p, hp, hpX, hX⟩ :=
      exists_prime_dvd_two_pow_add_one (X := n - i) (by omega) (by omega)
    have hp3 : 3 ≤ p := by
      have := Nat.le_of_dvd (by have := hp.two_le; omega) hX
      omega
    have h3n : n * 3 ≤ n * p := Nat.mul_le_mul_left n hp3
    exact ⟨n * p, ⟨lift hn h2i hn0 hp hpX hX, by omega, by omega, by omega⟩, by omega⟩
  have seed : good (2 ^ i) := by
    obtain ⟨h1, h2⟩ := two_pow_bounds i
    refine ⟨?_, h1, by positivity, h2⟩
    push_cast
    exact dvd_add (pow_dvd_pow 2 Nat.lt_two_pow_self.le) dvd_rfl
  have hall : ∀ a, ∃ n, good n ∧ a < n := by
    intro a
    induction a with
    | zero => exact ⟨2 ^ i, seed, by positivity⟩
    | succ a ih =>
      obtain ⟨n, hn, han⟩ := ih
      obtain ⟨n', hn', hnn'⟩ := step n hn
      exact ⟨n', hn', by omega⟩
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨n, hn, han⟩ := hall a
  refine ⟨n, ?_, han⟩
  change (2 : ℤ) ^ n ≡ -(2 ^ i) [ZMOD (n : ℤ)]
  rw [Int.modEq_iff_dvd, show -(2 ^ i : ℤ) - 2 ^ n = -(2 ^ n + 2 ^ i) by ring, dvd_neg]
  exact hn.1

end ErdosLean.Erdos479
