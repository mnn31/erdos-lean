import FormalConjectures.ErdosProblems.«394»

/-!
# Erdős Problem 394: `limsup t_{n-3}(n!) / n = 2`

Let `t k N` (`Erdos394.t`) be the least `m ≥ 1` with `N ∣ m (m + 1) ⋯ (m + k - 1)`. Erdős and
Hall [ErHa78, p. 481] note that `t_{n-1}(n!) = 2` and `t_{n-2}(n!) = O(n)`, and ask what can be
said about `t_{n-3}(n!)`. We prove `erdos_394.variants.factorial_sub_three_limsup`:

  `limsup_{n → ∞} t_{n-3}(n!) / n = 2`.

The two halves are `tn3_upper` (for every `ε > 0`, eventually `t_{n-3}(n!) ≤ (2 + ε) n`) and
`tn3_lower` (`t_{n-3}(n!) ≥ 2 n` for infinitely many `n`, namely `n = 3 ^ y` with `y ≥ 2`).
This determines the limsup only; the open-ended question asks for more.

The statement is not in formal-conjectures at the commit pinned in `lakefile.toml`, so it is copied
verbatim from the proposed variant in `FormalConjectures/ErdosProblems/394.lean`. It uses only
`Erdos394.t`, whose definition is the same at the pinned commit.

Proof outline. Write `m = a + 1` and `b = n - 3`. The lemma numbers below are used in the file.
1. (Reduction) `n! ∣ (a + 1) ⋯ (a + n - 3)` iff `n (n - 1) (n - 2) ∣ C(a + b, b)`.
2. (Kummer, level form) `v_p C(a + b, b)` is at least the number of levels `i` with
   `a mod p^i + b mod p^i ≥ p^i`.
3. to 5. For `p ≥ 5` dividing `n (n - 1) (n - 2)`, `a mod p ≥ 3` gives enough carries. For
   `p = 2` and `p = 3` the conditions are `a ≡ 35 (mod 36)` together with
   `a mod 2α ≥ α + 3` and (when `n mod 9 ∈ {0, 3}`) `a mod 3β ≥ 2β + 3`, where `α` and `β` are
   the 2-part and 3-part of `n - j` for the relevant `j ≤ 3`.
   5A. (Admissibility) An `a` satisfying all of these has `t_{n-3}(n!) ≤ a + 1`.
6. to 8. Elementary lemmas on how the residue windows for `α` and `β` overlap.
9. (Sieve) Inclusion-exclusion with the Chinese remainder theorem: an interval of length
   `L > M 10^{|S|}` contains some `a` in a given class mod the 3-smooth modulus `M` with
   `a mod p ≥ 3` for every `p` in the set `S` of primes `p ≥ 5` dividing `n (n - 1) (n - 2)`.
10. `|S| = o(log n)`, so eventually `10^{|S|} ≤ n^{1/100}`.
   A case analysis on the sizes of `α` and `β` then gives, for each `K0 ≥ 1`, a window of `a`
   below `2 n + n / K0 + 3` meeting conditions 3 to 5 (`dispatch`), and Lemma 9 finds an
   admissible `a` in it (`upper`).
11. (Lower bound) For `n = 3^y`, `y ≥ 2`, we have `b = 3^y - 3` and `3^y ∥ n (n - 1) (n - 2)`.
   The base-3 digits of `b` force a carry at level `y + 1`, so `a ≥ 2 n + 3`.

[ErHa78] Erdős, P. and Hall, R. R., On some unconventional problems on the divisors of integers.
J. Austral. Math. Soc. Ser. A 25 (1978), 479-485.
-/

section Defs

/-
## Definitions

Conventions: for `n ≥ 6`, `a = m - 1`, `b = n - 3`.
* `j2 n = n % 4`, `alpha n = 2 ^ v₂(n - j2 n)`.
* `HasB n` iff `9 ∣ n - jB n` with `jB n ∈ {0, 3}`, i.e. `n % 9 ∈ {0, 3}`; then
  `beta n = 3 ^ v₃(n - jB n)` (with `v₃(n - jB n) ≥ 2`).
  Otherwise we put `beta n = 3` (the 3-adic condition is then implied by `a ≡ 8 (mod 9)`).
* `S n` = primes `p ≥ 5` dividing `n(n-1)(n-2)`.
* `GoodWindow n K0 Z`: an interval `[x, x+L)` and a 3-smooth modulus `M = 2^u 3^v` with
  `36 ∣ M`, `M * Z < L`, `x + L ≤ 2n + n/K0 + 3`, such that every `a` in the interval with
  `a ≡ -1 (mod M)` satisfies the 2-adic condition `alpha n + 3 ≤ a % (2 * alpha n)` and the 3-adic
  condition `HasB n → 2 * beta n + 3 ≤ a % (3 * beta n)` of Lemma 5A.
-/

open Finset

namespace ErdosLean.Erdos394Limsup

/-- The function of the problem (identical to `Erdos394.t`). -/
noncomputable abbrev t (k n : ℕ) : ℕ := Erdos394.t k n

/-- `j2 n = n mod 4`. -/
def j2 (n : ℕ) : ℕ := n % 4

/-- `alpha n = 2 ^ v_2 (n - n % 4)`. -/
def alpha (n : ℕ) : ℕ := 2 ^ padicValNat 2 (n - n % 4)

/-- `n % 9 ∈ {0, 3}`: exactly the case where the 3-adic condition is needed. -/
def HasB (n : ℕ) : Prop := n % 9 = 0 ∨ n % 9 = 3

instance (n : ℕ) : Decidable (HasB n) := by unfold HasB; infer_instance

/-- `jB n = 0` if `9 ∣ n`, else `3`. -/
def jB (n : ℕ) : ℕ := if n % 9 = 0 then 0 else 3

/-- `beta n = 3 ^ v_3 (n - jB n)` when `HasB n`, and `3` otherwise. -/
def beta (n : ℕ) : ℕ := if HasB n then 3 ^ padicValNat 3 (n - jB n) else 3

/-- The primes `p ≥ 5` dividing `n(n-1)(n-2)`. -/
def S (n : ℕ) : Finset ℕ := (n * (n - 1) * (n - 2)).primeFactors.filter (fun p => 5 ≤ p)

/-- A window for the upper bound (see module docstring). -/
def GoodWindow (n K0 Z : ℕ) : Prop :=
  ∃ x L u v : ℕ, 36 ∣ 2 ^ u * 3 ^ v ∧ 2 ^ u * 3 ^ v * Z < L ∧ x + L ≤ 2 * n + n / K0 + 3 ∧
    ∀ a, x ≤ a → a < x + L → a % (2 ^ u * 3 ^ v) = 2 ^ u * 3 ^ v - 1 →
      alpha n + 3 ≤ a % (2 * alpha n) ∧ (HasB n → 2 * beta n + 3 ≤ a % (3 * beta n))

/- ### Basic facts about `alpha`, `beta` -/

/-- `n - j2 = q2 * 2^x` with `q2` odd and `x ≥ 2`. -/
theorem alpha_spec {n : ℕ} (hn : 6 ≤ n) :
    ∃ x q : ℕ, alpha n = 2 ^ x ∧ 2 ≤ x ∧ n - n % 4 = q * 2 ^ x ∧ Odd q := by
  have hpos : n - n % 4 ≠ 0 := by omega
  have h4 : 4 ∣ n - n % 4 := by omega
  obtain ⟨e, q, hq, hnq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos 2 (by norm_num)
  have hv : padicValNat 2 (n - n % 4) = e := by
    rw [hnq, padicValNat.mul (by positivity) (by rintro rfl; simp at hq),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hq, add_zero]
  refine ⟨e, q, by rw [alpha, hv], ?_, by rw [hnq, mul_comm], Nat.odd_iff.2 (by omega)⟩
  have : 2 ^ 2 ∣ n - n % 4 := by simpa using h4
  rw [padicValNat_dvd_iff_le hpos, hv] at this
  exact this

/-- `beta n = 3 ^ y` with `y ≥ 1`; when `HasB n`, also `y ≥ 2` and
`n - jB n = q * 3 ^ y` with `3 ∤ q`. -/
theorem beta_spec {n : ℕ} (hn : 6 ≤ n) :
    ∃ y : ℕ, beta n = 3 ^ y ∧ 1 ≤ y ∧
      (HasB n → 2 ≤ y ∧ ∃ q : ℕ, n - jB n = q * 3 ^ y ∧ ¬ 3 ∣ q) := by
  by_cases hB : HasB n
  · have hj : jB n = if n % 9 = 0 then 0 else 3 := rfl
    have hpos : n - jB n ≠ 0 := by unfold HasB at hB; split_ifs at hj <;> omega
    have h9 : 9 ∣ n - jB n := by unfold HasB at hB; split_ifs at hj <;> omega
    obtain ⟨e, q, hq, hnq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos 3 (by norm_num)
    have hv : padicValNat 3 (n - jB n) = e := by
      rw [hnq, padicValNat.mul (by positivity) (by rintro rfl; simp at hq),
        padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hq, add_zero]
    have he : 2 ≤ e := by
      have : 3 ^ 2 ∣ n - jB n := by simpa using h9
      rw [padicValNat_dvd_iff_le hpos, hv] at this
      exact this
    refine ⟨e, by rw [beta, if_pos hB, hv], by omega, fun _ => ⟨he, q, by rw [hnq, mul_comm], hq⟩⟩
  · exact ⟨1, by rw [beta, if_neg hB]; norm_num, le_rfl, fun h => absurd h hB⟩

theorem four_le_alpha {n : ℕ} (hn : 6 ≤ n) : 4 ≤ alpha n := by
  obtain ⟨x, q, hx, h2, -, -⟩ := alpha_spec hn
  rw [hx]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) h2

theorem alpha_le {n : ℕ} (hn : 6 ≤ n) : alpha n ≤ n := by
  obtain ⟨x, q, hx, -, hq, hodd⟩ := alpha_spec hn
  have hq0 : 1 ≤ q := hodd.pos
  have : alpha n ≤ n - n % 4 := by rw [hq, hx]; exact Nat.le_mul_of_pos_left _ hq0
  omega

theorem three_le_beta {n : ℕ} (hn : 6 ≤ n) : 3 ≤ beta n := by
  obtain ⟨y, hy, h1, -⟩ := beta_spec hn
  rw [hy]
  calc 3 = 3 ^ 1 := by norm_num
    _ ≤ 3 ^ y := Nat.pow_le_pow_right (by norm_num) h1

theorem nine_le_beta {n : ℕ} (hn : 6 ≤ n) (hB : HasB n) : 9 ≤ beta n := by
  obtain ⟨y, hy, -, h2⟩ := beta_spec hn
  rw [hy]
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ 3 ^ y := Nat.pow_le_pow_right (by norm_num) (h2 hB).1

theorem jB_le (n : ℕ) : jB n ≤ 3 := by unfold jB; split_ifs <;> omega

theorem beta_le {n : ℕ} (hn : 6 ≤ n) : beta n ≤ n := by
  by_cases hB : HasB n
  · obtain ⟨y, hy, -, h2⟩ := beta_spec hn
    obtain ⟨-, q, hq, hq3⟩ := h2 hB
    have hq0 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · exact absurd (h ▸ dvd_zero 3) hq3
      · exact h
    have : beta n ≤ n - jB n := by rw [hq, hy]; exact Nat.le_mul_of_pos_left _ hq0
    omega
  · simp only [beta, hB, if_false]; omega

end ErdosLean.Erdos394Limsup

namespace ErdosLean.Erdos394Limsup

/-- If `a ≡ -1 (mod M)` and `d ∣ M` then `a ≡ -1 (mod d)`. -/
theorem mod_eq_pred_of_dvd {a M d : ℕ} (hd : d ∣ M) (hd0 : 0 < d) (hM : 0 < M)
    (h : a % M = M - 1) : a % d = d - 1 := by
  rw [← Nat.mod_mod_of_dvd a hd, h]
  obtain ⟨m, rfl⟩ := hd
  have hm : 1 ≤ m := Nat.pos_of_mul_pos_left hM
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have : d * (m' + 1) - 1 = (d - 1) + d * m' := by
    rw [Nat.mul_succ]; omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

end ErdosLean.Erdos394Limsup

end Defs

section Kummer

/-
## Reduction and Kummer-level lemmas (Lemmas 1-5, 5A and 11)
-/

open Finset Nat

namespace ErdosLean.Erdos394Limsup

/-- `(a+1)(a+2)…(a+k) = k! * C(a+k, k)`. -/
theorem prod_range_eq (a k : ℕ) : ∏ i ∈ range k, (a + 1 + i) = k ! * choose (a + k) k := by
  rw [← Nat.ascFactorial_eq_prod_range, Nat.ascFactorial_eq_factorial_mul_choose]

theorem factorial_eq_mul (n : ℕ) (hn : 3 ≤ n) : n ! = (n - 3)! * (n * (n - 1) * (n - 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [Nat.add_sub_cancel, show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    Nat.factorial_succ]
  ring

/-- Lemma 1 (reduction). -/
theorem reduction {n a : ℕ} (hn : 4 ≤ n) :
    n ! ∣ ∏ i ∈ range (n - 3), (a + 1 + i) ↔
      n * (n - 1) * (n - 2) ∣ choose (a + (n - 3)) (n - 3) := by
  rw [prod_range_eq, factorial_eq_mul n (by omega)]
  exact Nat.mul_dvd_mul_iff_left (Nat.factorial_pos _)

/-- Lemma 2 (Kummer, level form), as a lower bound: every level `i ∈ s` at which `a` and `b`
carry in base `p` contributes one to `v_p(C(a+b, b))`. -/
theorem card_le_padicValNat_choose {p a b : ℕ} (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ i ∈ s, 1 ≤ i ∧ p ^ i ≤ b % p ^ i + a % p ^ i) :
    s.card ≤ padicValNat p (choose (a + b) b) := by
  have := Fact.mk hp
  rw [padicValNat_choose' (b := Nat.log p (a + b) + 1) (Nat.lt_succ_self _)]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨h1, h2⟩ := hs i hi
  simp only [Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨h1, ?_⟩, h2⟩
  by_contra hlt
  have hlog : Nat.log p (a + b) < i := by omega
  have hpow : a + b < p ^ i := Nat.lt_pow_of_log_lt hp.one_lt hlog
  have hb : b % p ^ i ≤ b := Nat.mod_le _ _
  have ha : a % p ^ i ≤ a := Nat.mod_le _ _
  omega

theorem mod_le_mod_of_dvd' (a : ℕ) {d m : ℕ} (h : d ∣ m) : a % d ≤ a % m := by
  rw [← Nat.mod_mod_of_dvd a h]; exact Nat.mod_le _ _

/-- One carry level: if `m ∣ b + c` with `0 < c ≤ a % m`, then base-`m` addition carries. -/
theorem level_carry {m a b c : ℕ} (hc : 0 < c) (hd : m ∣ b + c)
    (ha : c ≤ a % m) : m ≤ b % m + a % m := by
  have h1 : m ∣ b % m + c := by
    have : b + c = b % m + c + m * (b / m) := by have := Nat.mod_add_div b m; omega
    rw [this] at hd
    exact (Nat.dvd_add_left (dvd_mul_right m _)).mp hd
  have := Nat.le_of_dvd (by omega) h1
  omega

/-- All levels `1..e` carry when `p^e ∣ b + c` and `0 < c ≤ a % p`. -/
theorem le_val_of_pow_dvd {p a b c e : ℕ} (hp : p.Prime) (hc : 0 < c) (hca : c ≤ a % p)
    (hd : p ^ e ∣ b + c) : e ≤ padicValNat p (choose (a + b) b) := by
  have := card_le_padicValNat_choose (a := a) (b := b) hp (Finset.Icc 1 e) ?_
  · simpa using this
  intro i hi
  rw [Finset.mem_Icc] at hi
  refine ⟨hi.1, level_carry hc ((pow_dvd_pow p hi.2).trans hd) ?_⟩
  exact hca.trans (mod_le_mod_of_dvd' a (dvd_pow_self p (by omega)))

theorem val_prod {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    padicValNat p (n * (n - 1) * (n - 2)) =
      padicValNat p n + padicValNat p (n - 1) + padicValNat p (n - 2) := by
  have := Fact.mk hp
  rw [padicValNat.mul (Nat.mul_ne_zero (by omega) (by omega)) (by omega),
    padicValNat.mul (by omega) (by omega)]

theorem val_mul_pow {p q x : ℕ} (hp : p.Prime) (hq : ¬ p ∣ q) : padicValNat p (q * p ^ x) = x := by
  have := Fact.mk hp
  rw [padicValNat.mul (by rintro rfl; simp at hq) (pow_ne_zero _ hp.ne_zero),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hq, zero_add]

theorem val_eq_one {p m : ℕ} (hp : p.Prime) (h : p ∣ m) (h2 : ¬ p ^ 2 ∣ m) :
    padicValNat p m = 1 := by
  obtain ⟨k, rfl⟩ := h
  have hk : ¬ p ∣ k := fun hk => h2 (by rw [sq]; exact Nat.mul_dvd_mul_left p hk)
  have := val_mul_pow (x := 1) hp hk
  rwa [pow_one, mul_comm] at this

theorem pow_succ_dvd_add {p q k y : ℕ} (h : p ∣ q + k) : p ^ (y + 1) ∣ q * p ^ y + k * p ^ y := by
  rw [← add_mul, pow_succ']; exact Nat.mul_dvd_mul h dvd_rfl

/-- Lemma 3 (`p ≥ 5`). If `p ∣ n(n-1)(n-2)` then `a mod p ≥ 3` gives enough carries;
if `p ∤ n(n-1)(n-2)` the left side is `0`. -/
theorem val_le_large {n a p : ℕ} (hn : 6 ≤ n) (hp : p.Prime) (hp5 : 5 ≤ p)
    (ha : p ∣ n * (n - 1) * (n - 2) → 3 ≤ a % p) :
    padicValNat p (n * (n - 1) * (n - 2)) ≤ padicValNat p (choose (a + (n - 3)) (n - 3)) := by
  have hfact := Fact.mk hp
  by_cases hN : p ∣ n * (n - 1) * (n - 2)
  swap
  · rw [padicValNat.eq_zero_of_not_dvd hN]; exact Nat.zero_le _
  have ha3 := ha hN
  have hndvd : ∀ u w d, p ∣ u → p ∣ w → u = w + d → 0 < d → d < p → False := by
    intro u w d hu hw he hd0 hdp
    rw [he] at hu
    have := Nat.le_of_dvd hd0 ((Nat.dvd_add_right hw).mp hu)
    omega
  rw [val_prod hp (by omega)]
  rcases (Nat.Prime.dvd_mul hp).1 hN with h01 | h2
  · rcases (Nat.Prime.dvd_mul hp).1 h01 with h0 | h1
    · have h1 : ¬ p ∣ n - 1 := fun h => hndvd n (n - 1) 1 h0 h (by omega) one_pos (by omega)
      have h2 : ¬ p ∣ n - 2 := fun h => hndvd n (n - 2) 2 h0 h (by omega) two_pos (by omega)
      rw [padicValNat.eq_zero_of_not_dvd h1, padicValNat.eq_zero_of_not_dvd h2, add_zero, add_zero]
      exact le_val_of_pow_dvd hp (c := 3) (by norm_num) ha3
        (by rw [show n - 3 + 3 = n by omega]; exact pow_padicValNat_dvd)
    · have h0 : ¬ p ∣ n := fun h => hndvd n (n - 1) 1 h h1 (by omega) one_pos (by omega)
      have h2 : ¬ p ∣ n - 2 := fun h => hndvd (n - 1) (n - 2) 1 h1 h (by omega) one_pos (by omega)
      rw [padicValNat.eq_zero_of_not_dvd h0, padicValNat.eq_zero_of_not_dvd h2, add_zero, zero_add]
      exact le_val_of_pow_dvd hp (c := 2) (by norm_num) (by omega)
        (by rw [show n - 3 + 2 = n - 1 by omega]; exact pow_padicValNat_dvd)
  · have h0 : ¬ p ∣ n := fun h => hndvd n (n - 2) 2 h h2 (by omega) two_pos (by omega)
    have h1 : ¬ p ∣ n - 1 := fun h => hndvd (n - 1) (n - 2) 1 h h2 (by omega) one_pos (by omega)
    rw [padicValNat.eq_zero_of_not_dvd h0, padicValNat.eq_zero_of_not_dvd h1, zero_add, zero_add]
    exact le_val_of_pow_dvd hp (c := 1) (by norm_num) (by omega)
      (by rw [show n - 3 + 1 = n - 2 by omega]; exact pow_padicValNat_dvd)

/-- Lemma 4 (`p = 2`). -/
theorem val_le_two {n a : ℕ} (hn : 6 ≤ n) (h4 : a % 4 = 3)
    (hA : alpha n + 3 ≤ a % (2 * alpha n)) :
    padicValNat 2 (n * (n - 1) * (n - 2)) ≤ padicValNat 2 (choose (a + (n - 3)) (n - 3)) := by
  obtain ⟨x, q, hx, hx2, hq, hodd⟩ := alpha_spec hn
  rw [hx, show 2 * 2 ^ x = 2 ^ (x + 1) by ring] at hA
  rw [val_prod Nat.prime_two (by omega)]
  have hq2 : ¬ 2 ∣ q := by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]
  have hqx : 2 ∣ q + 1 := by obtain ⟨k, rfl⟩ := hodd; exact ⟨k + 1, by ring⟩
  have h4x : 4 ≤ 2 ^ x := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hx2
  have hq4 : 4 ∣ q * 2 ^ x :=
    (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ (pow_dvd_pow 2 hx2).trans (dvd_mul_left _ _)
  have hdvx : ∀ i, i ≤ x → 2 ^ i ∣ q * 2 ^ x := fun i hi => (pow_dvd_pow 2 hi).trans (dvd_mul_left _ _)
  have ha4 : ∀ i, 2 ≤ i → 3 ≤ a % 2 ^ i := fun i hi => by
    have := mod_le_mod_of_dvd' a (show 4 ∣ 2 ^ i from
      (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ pow_dvd_pow 2 hi)
    omega
  have key : ∀ c lo, c ≤ 3 → n - 3 + c = q * 2 ^ x → 1 ≤ lo →
      (∀ i, lo ≤ i → i ≤ x → 2 ^ i ≤ (n - 3) % 2 ^ i + a % 2 ^ i) →
      x + 2 - lo ≤ padicValNat 2 (choose (a + (n - 3)) (n - 3)) := by
    intro c lo hc3 hbc hlo hmid
    have := card_le_padicValNat_choose (a := a) (b := n - 3) Nat.prime_two (Finset.Icc lo (x + 1)) ?_
    · rw [Nat.card_Icc] at this; omega
    intro i hi
    rw [Finset.mem_Icc] at hi
    refine ⟨by omega, ?_⟩
    rcases Nat.lt_or_ge x i with h | h
    · obtain rfl : i = x + 1 := by omega
      refine level_carry (c := c + 2 ^ x) (by positivity) ?_ (by omega)
      rw [← add_assoc, hbc]
      exact pow_succ_dvd_add (k := 1) (by simpa using hqx) |>.trans (by rw [one_mul])
    · exact hmid i hi.1 h
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with hj | hj | hj | hj
  · -- n = q 2^x, n - 2 ≡ 2 (mod 4)
    rw [show padicValNat 2 n = x by rw [show n = q * 2 ^ x by omega]; exact val_mul_pow Nat.prime_two hq2,
      padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ n - 1),
      val_eq_one Nat.prime_two (by omega) (by norm_num; omega)]
    have := key 3 1 le_rfl (by omega) le_rfl (fun i hi1 hix => by
      rcases Nat.lt_or_ge i 2 with h | h
      · obtain rfl : i = 1 := by omega
        simp only [pow_one]; omega
      · exact level_carry (c := 3) (by norm_num) (by rw [show n - 3 + 3 = q * 2 ^ x by omega]; exact hdvx i hix)
          (ha4 i h))
    omega
  · -- n - 1 = q 2^x
    rw [padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ n),
      show padicValNat 2 (n - 1) = x by rw [show n - 1 = q * 2 ^ x by omega]; exact val_mul_pow Nat.prime_two hq2,
      padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ n - 2)]
    have := key 2 2 (by norm_num) (by omega) (by norm_num) (fun i hi1 hix =>
      level_carry (c := 2) (by norm_num) (by rw [show n - 3 + 2 = q * 2 ^ x by omega]; exact hdvx i hix)
        (by have := ha4 i hi1; omega))
    omega
  · -- n - 2 = q 2^x, n ≡ 2 (mod 4)
    rw [val_eq_one Nat.prime_two (by omega) (by norm_num; omega),
      padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ n - 1),
      show padicValNat 2 (n - 2) = x by rw [show n - 2 = q * 2 ^ x by omega]; exact val_mul_pow Nat.prime_two hq2]
    have := key 1 1 (by norm_num) (by omega) le_rfl (fun i hi1 hix =>
      level_carry (c := 1) (by norm_num) (by rw [show n - 3 + 1 = q * 2 ^ x by omega]; exact hdvx i hix)
        (by have := mod_le_mod_of_dvd' a (dvd_pow_self 2 (by omega : i ≠ 0)); omega))
    omega
  · -- n - 3 = q 2^x, n - 1 ≡ 2 (mod 4)
    rw [padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ n),
      val_eq_one Nat.prime_two (by omega) (by norm_num; omega),
      padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ n - 2)]
    have := key 0 (x + 1) (by norm_num) (by omega) (by omega) (fun i hi1 hix => by omega)
    omega

/-- Lemma 5 (`p = 3`). -/
theorem val_le_three {n a : ℕ} (hn : 6 ≤ n) (h9 : a % 9 = 8)
    (hB : HasB n → 2 * beta n + 3 ≤ a % (3 * beta n)) :
    padicValNat 3 (n * (n - 1) * (n - 2)) ≤ padicValNat 3 (choose (a + (n - 3)) (n - 3)) := by
  have hfact := Fact.mk Nat.prime_three
  rw [val_prod Nat.prime_three (by omega)]
  rcases (by omega : n % 3 = 1 ∨ n % 3 = 2 ∨ n % 3 = 0) with h | h | h
  · rw [padicValNat.eq_zero_of_not_dvd (by omega : ¬ 3 ∣ n),
      padicValNat.eq_zero_of_not_dvd (by omega : ¬ 3 ∣ n - 2), zero_add, add_zero]
    exact le_val_of_pow_dvd Nat.prime_three (c := 2) (by norm_num) (by omega)
      (by rw [show n - 3 + 2 = n - 1 by omega]; exact pow_padicValNat_dvd)
  · rw [padicValNat.eq_zero_of_not_dvd (by omega : ¬ 3 ∣ n),
      padicValNat.eq_zero_of_not_dvd (by omega : ¬ 3 ∣ n - 1), zero_add, zero_add]
    exact le_val_of_pow_dvd Nat.prime_three (c := 1) (by norm_num) (by omega)
      (by rw [show n - 3 + 1 = n - 2 by omega]; exact pow_padicValNat_dvd)
  rw [padicValNat.eq_zero_of_not_dvd (by omega : ¬ 3 ∣ n - 1),
    padicValNat.eq_zero_of_not_dvd (by omega : ¬ 3 ∣ n - 2), add_zero, add_zero]
  -- top level helper
  have htop : ∀ q y : ℕ, ¬ 3 ∣ q → ∃ k, (k = 1 ∨ k = 2) ∧ 3 ^ (y + 1) ∣ q * 3 ^ y + k * 3 ^ y := by
    intro q y hq
    rcases (by omega : q % 3 = 1 ∨ q % 3 = 2) with hq1 | hq1
    · exact ⟨2, Or.inr rfl, pow_succ_dvd_add (by omega)⟩
    · exact ⟨1, Or.inl rfl, pow_succ_dvd_add (by omega)⟩
  rcases (by omega : n % 9 = 6 ∨ n % 9 = 0 ∨ n % 9 = 3) with h9' | h9' | h9'
  · rw [val_eq_one Nat.prime_three (by omega) (by norm_num; omega)]
    have := card_le_padicValNat_choose (a := a) (b := n - 3) Nat.prime_three {2} (by
      intro i hi
      rw [Finset.mem_singleton] at hi
      subst hi
      norm_num
      omega)
    simpa using this
  · have hB' : HasB n := Or.inl h9'
    obtain ⟨y, hy, -, hB2⟩ := beta_spec hn
    obtain ⟨hy2, q, hq, hq3⟩ := hB2 hB'
    have hj : jB n = 0 := by simp [jB, h9']
    rw [hj, Nat.sub_zero] at hq
    have hA := hB hB'
    rw [hy, show 3 * 3 ^ y = 3 ^ (y + 1) by ring] at hA
    rw [show padicValNat 3 n = y by rw [hq]; exact val_mul_pow Nat.prime_three hq3]
    obtain ⟨k, hk, hkd⟩ := htop q y hq3
    have h9y : 9 ≤ 3 ^ y := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ y := Nat.pow_le_pow_right (by norm_num) hy2
    have hk3 : k * 3 ^ y ≤ 2 * 3 ^ y := Nat.mul_le_mul_right _ (by omega)
    have := card_le_padicValNat_choose (a := a) (b := n - 3) Nat.prime_three
      (Finset.Icc 2 (y + 1)) ?_
    · rw [Nat.card_Icc] at this; omega
    intro i hi
    rw [Finset.mem_Icc] at hi
    refine ⟨by omega, ?_⟩
    rcases Nat.lt_or_ge y i with hiy | hiy
    · obtain rfl : i = y + 1 := by omega
      refine level_carry (c := k * 3 ^ y + 3) (by omega) ?_ (by omega)
      rw [← add_assoc, show n - 3 + k * 3 ^ y + 3 = q * 3 ^ y + k * 3 ^ y by omega]
      exact hkd
    · refine level_carry (c := 3) (by norm_num) ?_ ?_
      · rw [show n - 3 + 3 = q * 3 ^ y by omega]
        exact (pow_dvd_pow 3 hiy).trans (dvd_mul_left _ _)
      · have := mod_le_mod_of_dvd' a (show 9 ∣ 3 ^ i from
          (show (9 : ℕ) = 3 ^ 2 by norm_num) ▸ pow_dvd_pow 3 hi.1)
        omega
  · have hB' : HasB n := Or.inr h9'
    obtain ⟨y, hy, -, hB2⟩ := beta_spec hn
    obtain ⟨hy2, q, hq, hq3⟩ := hB2 hB'
    have hj : jB n = 3 := by simp [jB, h9']
    rw [hj] at hq
    have hA := hB hB'
    rw [hy, show 3 * 3 ^ y = 3 ^ (y + 1) by ring] at hA
    rw [val_eq_one Nat.prime_three (by omega) (by norm_num; omega)]
    obtain ⟨k, hk, hkd⟩ := htop q y hq3
    have hk3 : k * 3 ^ y ≤ 2 * 3 ^ y := Nat.mul_le_mul_right _ (by omega)
    have hk0 : 0 < k * 3 ^ y := Nat.mul_pos (by omega) (by positivity)
    have := card_le_padicValNat_choose (a := a) (b := n - 3) Nat.prime_three {y + 1} (by
      intro i hi
      rw [Finset.mem_singleton] at hi
      subst hi
      refine ⟨by omega, level_carry (c := k * 3 ^ y) hk0 ?_ (by omega)⟩
      rw [hq]; exact hkd)
    simpa using this

/-- Lemma 5A (admissibility). -/
theorem t_le_of_admissible {n a : ℕ} (hn : 6 ≤ n) (h36 : a % 36 = 35)
    (hA : alpha n + 3 ≤ a % (2 * alpha n)) (hB : HasB n → 2 * beta n + 3 ≤ a % (3 * beta n))
    (hS : ∀ p ∈ S n, 3 ≤ a % p) : t (n - 3) (n !) ≤ a + 1 := by
  have hdvd : n * (n - 1) * (n - 2) ∣ choose (a + (n - 3)) (n - 3) := by
    have hd0 : n * (n - 1) * (n - 2) ≠ 0 := by
      apply Nat.mul_ne_zero (Nat.mul_ne_zero _ _) _ <;> omega
    have hc0 : choose (a + (n - 3)) (n - 3) ≠ 0 := (Nat.choose_pos (by omega)).ne'
    rw [← Nat.factorization_prime_le_iff_dvd hd0 hc0]
    intro p hp
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    by_cases h2 : p = 2
    · subst h2; exact val_le_two hn (by omega) hA
    by_cases h3 : p = 3
    · subst h3; exact val_le_three hn (by omega) hB
    have h5 : 5 ≤ p := by
      have := hp.two_le
      rcases Nat.lt_or_ge p 5 with h | h
      · interval_cases p <;> simp_all (config := {decide := true})
      · exact h
    refine val_le_large hn hp h5 (fun hpd => hS p ?_)
    simp only [S, Finset.mem_filter, Nat.mem_primeFactors]
    exact ⟨⟨hp, hpd, hd0⟩, h5⟩
  refine Nat.sInf_le ⟨Nat.succ_pos a, ?_⟩
  exact (reduction (by omega)).2 hdvd

/-- Lemma 11 (carry form): for `n = 3^y`, `y ≥ 2`, the 3-adic condition forces `a ≥ 2n + 3`. -/
theorem lower_carry {y a : ℕ} (hy : 2 ≤ y)
    (h : 3 ^ y * (3 ^ y - 1) * (3 ^ y - 2) ∣ choose (a + (3 ^ y - 3)) (3 ^ y - 3)) :
    2 * 3 ^ y + 3 ≤ a := by
  have hfact := Fact.mk Nat.prime_three
  have h9 : 9 ≤ 3 ^ y := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ y := Nat.pow_le_pow_right (by norm_num) hy
  have h3y : 3 ∣ 3 ^ y := dvd_pow_self 3 (by omega)
  have hC : choose (a + (3 ^ y - 3)) (3 ^ y - 3) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hdv : 3 ^ y ∣ choose (a + (3 ^ y - 3)) (3 ^ y - 3) :=
    (dvd_mul_of_dvd_left (dvd_mul_right _ _) _).trans h
  have hle := (padicValNat_dvd_iff_le hC).1 hdv
  by_contra hlt
  rw [Nat.not_le] at hlt
  rw [padicValNat_choose' (b := Nat.log 3 (a + (3 ^ y - 3)) + 1) (Nat.lt_succ_self _)] at hle
  have hsub : (Finset.Ico 1 (Nat.log 3 (a + (3 ^ y - 3)) + 1)).filter
      (fun i => 3 ^ i ≤ (3 ^ y - 3) % 3 ^ i + a % 3 ^ i) ⊆ Finset.Ico 2 (y + 1) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_Ico] at hi ⊢
    obtain ⟨⟨h1, -⟩, h2⟩ := hi
    refine ⟨?_, ?_⟩
    · by_contra hi1
      obtain rfl : i = 1 := by omega
      simp only [pow_one] at h2
      omega
    · by_contra hi1
      have hpow : 3 ^ (y + 1) ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hy1 : 3 ^ (y + 1) = 3 * 3 ^ y := pow_succ' 3 y
      have hbm : (3 ^ y - 3) % 3 ^ i = 3 ^ y - 3 := Nat.mod_eq_of_lt (by omega)
      have : a % 3 ^ i ≤ a := Nat.mod_le _ _
      omega
  have := Finset.card_le_card hsub
  simp only [Nat.card_Ico] at this
  omega

/-- Lemma 11: `t_{n-3}(n!) ≥ 2n + 4` for `n = 3^y`, `y ≥ 2`. -/
theorem t_ge_pow_three {y : ℕ} (hy : 2 ≤ y) : 2 * 3 ^ y + 4 ≤ t (3 ^ y - 3) ((3 ^ y)!) := by
  have h9 : 9 ≤ 3 ^ y := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ y := Nat.pow_le_pow_right (by norm_num) hy
  set n := 3 ^ y with hn
  have hne : { m : ℕ | 0 < m ∧ n ! ∣ ∏ i ∈ range (n - 3), (m + i) }.Nonempty := by
    refine ⟨n !, Nat.factorial_pos _, ?_⟩
    have h0 : 0 ∈ range (n - 3) := Finset.mem_range.2 (by omega)
    simpa using Finset.dvd_prod_of_mem (fun i => n ! + i) h0
  obtain ⟨hpos, hd⟩ := Nat.sInf_mem hne
  change 0 < t (n - 3) (n !) at hpos
  change n ! ∣ ∏ i ∈ range (n - 3), (t (n - 3) (n !) + i) at hd
  obtain ⟨a, ha⟩ : ∃ a, t (n - 3) (n !) = a + 1 := ⟨t (n - 3) (n !) - 1, by omega⟩
  rw [ha] at hd ⊢
  have := lower_carry hy ((reduction (a := a) (by omega)).1 hd)
  omega

end ErdosLean.Erdos394Limsup

end Kummer

section Pattern

/-
## Overlap lemmas (Lemmas 6, 7, 8)
-/

namespace ErdosLean.Erdos394Limsup

/-- Lemma 7 (pattern lemma), discrete form: with `Q = q2 q3` and `u = c / Q`, the open interval
`(c/Q, (c+1)/Q)` lies in `((2i+1)/q2, (2i+2)/q2) ∩ ((3k+2)/q3, (3k+3)/q3)` and `(c+1)/Q ≤ 2`. -/
theorem pattern {q2 q3 : ℕ} (h2 : Odd q2) (h3 : 2 ≤ q3) (h3' : ¬ 3 ∣ q3) :
    ∃ c i k : ℕ, (2 * i + 1) * q3 ≤ c ∧ c + 1 ≤ (2 * i + 2) * q3 ∧
      (3 * k + 2) * q2 ≤ c ∧ c + 1 ≤ (3 * k + 3) * q2 ∧ c + 1 ≤ 2 * q2 * q3 := by
  obtain ⟨t, rfl⟩ := h2
  have hm : q3 % 3 = 1 ∨ q3 % 3 = 2 := by omega
  rcases hm with hm | hm
  · obtain ⟨r, hr⟩ : ∃ r, q3 = 3 * r + 1 := ⟨q3 / 3, by omega⟩
    rcases lt_trichotomy (2 * t + 1) q3 with hlt | heq | hgt
    · -- W2
      refine ⟨(2 * t + 1) * q3 + (2 * t + 1), t, r, ?_, ?_, ?_, ?_, ?_⟩ <;> subst hr <;>
        nlinarith
    · -- W3
      refine ⟨5 * q3, 2, 1, ?_, ?_, ?_, ?_, ?_⟩ <;> subst hr
      · omega
      · omega
      · omega
      · omega
      · have : 7 ≤ 3 * r + 1 := by omega
        nlinarith
    · -- W4
      have e3 : 3 * r + 2 = q3 + 1 := by omega
      have e4 : 3 * r + 3 = q3 + 2 := by omega
      set s := (q3 + 1) * (2 * t + 1) with hs
      set m := s / q3 with hmdef
      have hq3 : 0 < q3 := by omega
      have e1 : q3 * m + s % q3 = s := Nat.div_add_mod s q3
      have e2 : s % q3 < q3 := Nat.mod_lt _ hq3
      have hlo : m * q3 ≤ s := by rw [mul_comm]; omega
      have hhi : s < (m + 1) * q3 := by rw [add_mul, mul_comm]; omega
      have hhi' : (m + 1) * q3 ≤ s + q3 := by rw [add_mul, mul_comm]; omega
      rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
      · refine ⟨(m + 1) * q3, j, r, ?_, ?_, ?_, ?_, ?_⟩
        · rw [show 2 * j + 1 = m + 1 by omega]
        · rw [show 2 * j + 2 = m + 2 by omega, add_mul, add_mul]; omega
        · rw [e3]; omega
        · rw [e4]; rw [hs] at hhi'; nlinarith
        · rw [hs] at hhi'; nlinarith
      · refine ⟨s, j, r, ?_, ?_, ?_, ?_, ?_⟩
        · rw [← hj]; exact hlo
        · rw [show 2 * j + 2 = m + 1 by omega]; omega
        · rw [e3]
        · rw [e4, hs]; nlinarith
        · rw [hs]; nlinarith
  · obtain ⟨r, hr⟩ : ∃ r, q3 = 3 * r + 2 := ⟨q3 / 3, by omega⟩
    refine ⟨(2 * t + 1) * q3, t, r, le_refl _, ?_, ?_, ?_, ?_⟩
    · nlinarith
    · rw [← hr, mul_comm]
    · rw [show 3 * r + 3 = q3 + 1 by omega]; nlinarith
    · nlinarith

/-- Lemma 6 (phase-zero overlap), for positive integers. -/
theorem phase_zero {α β : ℕ} (hα : 0 < α) (hβ : 0 < β) :
    ∃ i k : ℕ,
      min α β ≤ 5 * (min ((2 * i + 2) * α) ((3 * k + 3) * β) -
        max ((2 * i + 1) * α) ((3 * k + 2) * β)) ∧
      min ((2 * i + 2) * α) ((3 * k + 3) * β) ≤ 27 * max α β := by
  rcases le_or_gt (3 * α) β with hb | hb
  · -- `β ≥ 3α`: `k = 0`, `[(2i+1)α, (2i+2)α) ⊆ [2β, 3β)`
    have e1 : α * (2 * β / α) + 2 * β % α = 2 * β := Nat.div_add_mod _ _
    have e2 : 2 * β % α < α := Nat.mod_lt _ hα
    rcases Nat.even_or_odd (2 * β / α) with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨j, 0, ?_, ?_⟩
      · rw [hj] at e1
        have : α * (j + j) = 2 * (j * α) := by ring
        have h1 : (2 * j + 2) * α = 2 * (j * α) + 2 * α := by ring
        have h2 : (2 * j + 1) * α = 2 * (j * α) + α := by ring
        rw [h1, h2]; omega
      · have : α * (j + j) = 2 * (j * α) := by ring
        have h1 : (2 * j + 2) * α = 2 * (j * α) + 2 * α := by ring
        rw [h1]; omega
    · refine ⟨j + 1, 0, ?_, ?_⟩
      · rw [hj] at e1
        have : α * (2 * j + 1) = 2 * (j * α) + α := by ring
        have h1 : (2 * (j + 1) + 2) * α = 2 * (j * α) + 4 * α := by ring
        have h2 : (2 * (j + 1) + 1) * α = 2 * (j * α) + 3 * α := by ring
        rw [h1, h2]; omega
      · rw [hj] at e1
        have : α * (2 * j + 1) = 2 * (j * α) + α := by ring
        have h1 : (2 * (j + 1) + 2) * α = 2 * (j * α) + 4 * α := by ring
        rw [h1]; omega
  rcases le_or_gt (4 * β) α with ha | ha
  · -- `α ≥ 4β`: `i = 0`, `[(3k+2)β, (3k+3)β) ⊆ [α, 2α)`
    have e1 : β * (α / β) + α % β = α := Nat.div_add_mod _ _
    have e2 : α % β < β := Nat.mod_lt _ hβ
    obtain ⟨j, hj⟩ : ∃ j, α / β = 3 * j ∨ α / β = 3 * j + 1 ∨ α / β = 3 * j + 2 :=
      ⟨α / β / 3, by omega⟩
    rcases hj with hj | hj | hj
    · refine ⟨0, j, ?_, ?_⟩ <;> rw [hj] at e1 <;>
        have : β * (3 * j) = 3 * (j * β) := by ring
      all_goals
        have h1 : (3 * j + 3) * β = 3 * (j * β) + 3 * β := by ring
        have h2 : (3 * j + 2) * β = 3 * (j * β) + 2 * β := by ring
        rw [h1]; try rw [h2]
        omega
    · refine ⟨0, j, ?_, ?_⟩ <;> rw [hj] at e1 <;>
        have : β * (3 * j + 1) = 3 * (j * β) + β := by ring
      all_goals
        have h1 : (3 * j + 3) * β = 3 * (j * β) + 3 * β := by ring
        have h2 : (3 * j + 2) * β = 3 * (j * β) + 2 * β := by ring
        rw [h1]; try rw [h2]
        omega
    · refine ⟨0, j + 1, ?_, ?_⟩ <;> rw [hj] at e1 <;>
        have : β * (3 * j + 2) = 3 * (j * β) + 2 * β := by ring
      all_goals
        have h1 : (3 * (j + 1) + 3) * β = 3 * (j * β) + 6 * β := by ring
        have h2 : (3 * (j + 1) + 2) * β = 3 * (j * β) + 5 * β := by ring
        rw [h1]; try rw [h2]
        omega
  -- finite table, `1/4 < β/α < 3` (rows from an exact-fraction search)
  rcases le_or_gt (13 * β) (5 * α) with h | h
  · exact ⟨0, 1, by omega, by omega⟩
  rcases le_or_gt (11 * β) (10 * α) with h' | h'
  · exact ⟨0, 0, by omega, by omega⟩
  rcases le_or_gt (25 * β) (29 * α) with h'' | h''
  · exact ⟨2, 1, by omega, by omega⟩
  rcases le_or_gt (10 * β) (19 * α) with h''' | h'''
  · exact ⟨1, 0, by omega, by omega⟩
  rcases le_or_gt (10 * β) (29 * α) with h'''' | h''''
  · exact ⟨2, 0, by omega, by omega⟩
  · exact ⟨3, 0, by omega, by omega⟩

theorem pat_three_pow_mod_eight (m : ℕ) : 3 ^ m % 8 = 1 ∨ 3 ^ m % 8 = 3 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h <;> rw [h] <;> norm_num

theorem pat_three_pow_odd_mod_eight {m : ℕ} (hm : Odd m) : 3 ^ m % 8 = 3 := by
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num

/-- `2^x ∣ 3^m + 1` forces `2^x ≤ 4`. -/
theorem pat_two_pow_le_of_dvd_three_pow_add_one {x m : ℕ} (h : 2 ^ x ∣ 3 ^ m + 1) :
    2 ^ x ≤ 4 := by
  by_contra hx
  have hx3 : 3 ≤ x := by
    by_contra hx'
    interval_cases x <;> simp_all
  have h8 : 2 ^ 3 ∣ 3 ^ m + 1 := (pow_dvd_pow 2 hx3).trans h
  have := pat_three_pow_mod_eight m
  omega

/-- `2^x ∣ 3^m - 1` with `m ≥ 1` forces `2^x ≤ 4m` (lifting the exponent). -/
theorem pat_two_pow_le_of_dvd_three_pow_sub_one {x m : ℕ} (hm : 1 ≤ m)
    (h : 2 ^ x ∣ 3 ^ m - 1) : 2 ^ x ≤ 4 * m := by
  rcases Nat.even_or_odd m with he | ho
  · have hv := padicValNat.pow_two_sub_one (x := 3) (n := m) (by norm_num) (by norm_num)
      (by omega) he
    have h4 : padicValNat 2 (3 + 1) = 2 := by
      rw [show (3 + 1 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    have h2 : padicValNat 2 (3 - 1) = 1 := by
      rw [show (3 - 1 : ℕ) = 2 by norm_num, padicValNat.self (by norm_num)]
    have hne : 3 ^ m - 1 ≠ 0 := by
      have : 3 ≤ 3 ^ m := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
    have hx : x ≤ padicValNat 2 (3 ^ m - 1) := (padicValNat_dvd_iff_le hne).1 h
    have hx' : x ≤ 2 + padicValNat 2 m := by omega
    calc 2 ^ x ≤ 2 ^ (2 + padicValNat 2 m) := Nat.pow_le_pow_right (by norm_num) hx'
      _ = 4 * 2 ^ padicValNat 2 m := by rw [pow_add]; norm_num
      _ ≤ 4 * m := Nat.mul_le_mul_left _ (Nat.le_of_dvd (by omega) pow_padicValNat_dvd)
  · have h3 := pat_three_pow_odd_mod_eight ho
    have hx : x ≤ 1 := by
      by_contra hx
      have h4 : 4 ∣ 3 ^ m - 1 := (pow_dvd_pow 2 (by omega : 2 ≤ x)).trans h
      have : 0 < 3 ^ m := by positivity
      omega
    calc 2 ^ x ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hx
      _ ≤ 4 * m := by omega

/-- Lemma 8 (`q3 = 1` forces a tiny 2-adic modulus). -/
theorem alpha_le_of_q3_eq_one {n : ℕ} (hn : 6 ≤ n) (hB : HasB n) (h1 : n - jB n = beta n) :
    alpha n ≤ 4 * Nat.log 3 n := by
  obtain ⟨y, hy, -, h2⟩ := beta_spec hn
  obtain ⟨hy2, -⟩ := h2 hB
  obtain ⟨x, q', hx, -, hq', -⟩ := alpha_spec hn
  have hdvd : 2 ^ x ∣ n - n % 4 := ⟨q', by rw [hq', mul_comm]⟩
  rw [hy] at h1
  have hjB := jB_le n
  have hylog : y ≤ Nat.log 3 n := Nat.le_log_of_pow_le (by norm_num) (by omega)
  rw [hx]
  suffices 2 ^ x ≤ 4 * y by omega
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  have hP : 3 ^ (y' + 1) = 3 * 3 ^ y' := by ring
  have hodd : 3 ^ y' % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
  have hcop : Nat.Coprime (2 ^ x) 3 := Nat.Coprime.pow_left _ (by norm_num)
  have hj : jB n = 0 ∨ jB n = 3 := by unfold jB; split_ifs <;> simp
  rw [hP] at h1
  have h4 : 3 ^ y' % 4 = 1 ∨ 3 ^ y' % 4 = 3 := by omega
  rcases hj with hj | hj <;> rcases h4 with h4 | h4
  · have e : n - n % 4 = (3 ^ y' - 1) * 3 := by omega
    rw [e] at hdvd
    have := pat_two_pow_le_of_dvd_three_pow_sub_one (by omega) (hcop.dvd_of_dvd_mul_right hdvd)
    omega
  · have e : n - n % 4 = 3 ^ (y' + 1) - 1 := by rw [hP]; omega
    rw [e] at hdvd
    exact pat_two_pow_le_of_dvd_three_pow_sub_one (by omega) hdvd
  · have e : n - n % 4 = 3 ^ (y' + 1) + 1 := by rw [hP]; omega
    rw [e] at hdvd
    have := pat_two_pow_le_of_dvd_three_pow_add_one hdvd
    omega
  · have e : n - n % 4 = (3 ^ y' + 1) * 3 := by omega
    rw [e] at hdvd
    have := pat_two_pow_le_of_dvd_three_pow_add_one (hcop.dvd_of_dvd_mul_right hdvd)
    omega

end ErdosLean.Erdos394Limsup

end Pattern

section Sieve

/-
## The CRT / Legendre sieve (Lemma 9)
-/

open Finset

namespace ErdosLean.Erdos394Limsup

theorem periodic_add_mul {M : ℕ} (P : ℕ → Prop) (hP : ∀ a, P (a + M) ↔ P a) (b k : ℕ) :
    P (b + M * k) ↔ P b := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← Nat.add_assoc, hP, ih]

theorem periodic_mod {M : ℕ} (P : ℕ → Prop) (hP : ∀ a, P (a + M) ↔ P a) (a : ℕ) :
    P a ↔ P (a % M) := by
  conv_lhs => rw [← Nat.mod_add_div a M]
  exact periodic_add_mul P hP _ _

theorem card_filter_Ico_eq_sum (P : ℕ → Prop) [DecidablePred P] (x L : ℕ) :
    #{a ∈ Ico x (x + L) | P a} = ∑ k ∈ range L, (if P (x + k) then 1 else 0) := by
  rw [card_filter, sum_Ico_eq_sum_range]
  simp

theorem sum_block {M : ℕ} (P : ℕ → Prop) [DecidablePred P] (hP : ∀ a, P (a + M) ↔ P a)
    (x : ℕ) :
    ∑ k ∈ range M, (if P (x + k) then 1 else 0) = #{a ∈ range M | P a} := by
  induction x with
  | zero => simp only [Nat.zero_add]; rw [card_filter]
  | succ x ih =>
    rw [← ih]
    have h1 := Finset.sum_range_succ (fun k => if P (x + k) then 1 else 0) M
    have h2 := Finset.sum_range_succ' (fun k => if P (x + k) then 1 else 0) M
    have h3 : (if P (x + M) then 1 else 0) = (if P (x + 0) then 1 else 0) := by
      simp [hP]
    have h4 : ∑ k ∈ range M, (if P (x + 1 + k) then 1 else 0) =
        ∑ k ∈ range M, (if P (x + (k + 1)) then 1 else 0) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show x + 1 + k = x + (k + 1) by omega]
    rw [h4]
    omega

theorem sum_partial_le {M : ℕ} (P : ℕ → Prop) [DecidablePred P] (hP : ∀ a, P (a + M) ↔ P a)
    (x r : ℕ) (hr : r ≤ M) :
    ∑ k ∈ range r, (if P (x + k) then 1 else 0) ≤ #{a ∈ range M | P a} := by
  rw [← sum_block P hP x]
  exact Finset.sum_le_sum_of_subset (range_subset_range.mpr hr)

theorem sum_mul_add {M : ℕ} (P : ℕ → Prop) [DecidablePred P] (hP : ∀ a, P (a + M) ↔ P a)
    (q r : ℕ) (hr : r ≤ M) : ∀ x : ℕ, ∃ s ≤ #{a ∈ range M | P a},
      ∑ k ∈ range (q * M + r), (if P (x + k) then 1 else 0) = q * #{a ∈ range M | P a} + s := by
  induction q with
  | zero => intro x; exact ⟨_, sum_partial_le P hP x r hr, by simp⟩
  | succ q ih =>
    intro x
    obtain ⟨s, hs, hsum⟩ := ih (x + M)
    refine ⟨s, hs, ?_⟩
    rw [show (q + 1) * M + r = M + (q * M + r) by ring, Finset.sum_range_add, sum_block P hP]
    have : ∀ k, x + (M + k) = x + M + k := fun k => by omega
    simp_rw [this]
    rw [hsum]
    ring

/-- A predicate periodic mod `M` with `c` residues per period has `c L / M ± c` members in any
interval of length `L`. -/
theorem count_periodic {M : ℕ} (hM : 0 < M) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ a, P (a + M) ↔ P a) (x L : ℕ) :
    |(#{a ∈ Ico x (x + L) | P a} : ℝ) - (#{a ∈ range M | P a} : ℝ) * L / M| ≤
      (#{a ∈ range M | P a} : ℝ) := by
  obtain ⟨s, hs, hsum⟩ := sum_mul_add P hP (L / M) (L % M) (Nat.mod_lt _ hM).le x
  have hL : L / M * M + L % M = L := Nat.div_add_mod' L M
  rw [card_filter_Ico_eq_sum, ← hL, hsum]
  set c := #{a ∈ range M | P a}
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hrM : ((L % M : ℕ) : ℝ) ≤ M := by exact_mod_cast (Nat.mod_lt _ hM).le
  have hsr : (s : ℝ) ≤ c := by exact_mod_cast hs
  have hmain : (c : ℝ) * ((L / M * M + L % M : ℕ) : ℝ) / M =
      ((L / M : ℕ) : ℝ) * c + c * ((L % M : ℕ) : ℝ) / M := by
    push_cast
    field_simp
  have h1 : (c : ℝ) * ((L % M : ℕ) : ℝ) / M ≤ c := by
    rw [div_le_iff₀ hMr]
    exact mul_le_mul_of_nonneg_left hrM (Nat.cast_nonneg _)
  have h2 : 0 ≤ (c : ℝ) * ((L % M : ℕ) : ℝ) / M := by positivity
  rw [hmain, abs_le]
  push_cast
  constructor <;> nlinarith [(Nat.cast_nonneg s : (0:ℝ) ≤ s)]

/-- CRT residue count: adding the condition `a mod p ∈ {0,1,2}` for a prime `p ≥ 3` coprime to
the period multiplies the residue count by `3` (period `M * p`). -/
theorem count_crt {M p : ℕ} (hM : 0 < M) (hp : p.Prime) (hp3 : 3 ≤ p) (hcop : Nat.Coprime p M)
    (P : ℕ → Prop) [DecidablePred P] (hP : ∀ a, P (a + M) ↔ P a) :
    #{a ∈ range (M * p) | P a ∧ a % p < 3} = 3 * #{a ∈ range M | P a} := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hM0 : M ≠ 0 := hM.ne'
  have hcop' : Nat.Coprime M p := hcop.symm
  rw [show 3 * #{a ∈ range M | P a} = #({a ∈ range M | P a} ×ˢ range 3) by
    rw [card_product, card_range]; ring]
  apply card_nbij (fun a => (a % M, a % p))
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ha ⊢
    exact ⟨⟨Nat.mod_lt _ hM, (periodic_mod P hP a).mp ha.2.1⟩, ha.2.2⟩
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Prod.mk.injEq] at ha hb hab
    have h1 : a ≡ b [MOD M * p] := (Nat.modEq_and_modEq_iff_modEq_mul hcop').mp hab
    have h2 : a % (M * p) = b % (M * p) := h1
    rwa [Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at h2
  · rintro ⟨r, t⟩ h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
    obtain ⟨⟨hr, hPr⟩, ht⟩ := h
    set k := Nat.chineseRemainder hcop' r t with hk
    have hkM : (k : ℕ) % M = r := by
      have := k.prop.1
      rw [Nat.ModEq, Nat.mod_eq_of_lt hr] at this
      exact this
    have hkp : (k : ℕ) % p = t := by
      have := k.prop.2
      rw [Nat.ModEq, Nat.mod_eq_of_lt (show t < p by omega)] at this
      exact this
    refine ⟨(k : ℕ), ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.chineseRemainder_lt_mul hcop' r t hM0 hp0, ?_, by omega⟩
      rw [periodic_mod P hP, hkM]
      exact hPr
    · simp [hkM, hkp]

/-- Lemma 9 (Legendre sieve with interval error `c 4^|S|`), by induction on `S`. -/
theorem sieve_count (S : Finset ℕ) : ∀ {M : ℕ} (_ : 0 < M) (P : ℕ → Prop) [DecidablePred P]
    (_ : ∀ a, P (a + M) ↔ P a) (_ : ∀ p ∈ S, p.Prime ∧ 5 ≤ p ∧ Nat.Coprime p M) (x L : ℕ),
    |(#{a ∈ Ico x (x + L) | P a ∧ ∀ p ∈ S, 3 ≤ a % p} : ℝ) -
        (#{a ∈ range M | P a} : ℝ) * L / M * ∏ p ∈ S, (1 - 3 / (p : ℝ))| ≤
      (#{a ∈ range M | P a} : ℝ) * 4 ^ S.card := by
  induction S using Finset.induction_on with
  | empty =>
    intro M hM P _ hP _ x L
    simpa using count_periodic hM P hP x L
  | insert p S hpS ih =>
    intro M hM P _ hP hS x L
    have hp := hS p (mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime ∧ 5 ≤ q ∧ Nat.Coprime q M :=
      fun q hq => hS q (mem_insert_of_mem hq)
    have hMp : 0 < M * p := Nat.mul_pos hM (by have := hp.2.1; omega)
    have hP' : ∀ a, (P (a + M * p) ∧ (a + M * p) % p < 3) ↔ (P a ∧ a % p < 3) := by
      intro a
      rw [periodic_add_mul P hP, Nat.add_mul_mod_self_right]
    have hS'' : ∀ q ∈ S, q.Prime ∧ 5 ≤ q ∧ Nat.Coprime q (M * p) := by
      intro q hq
      obtain ⟨hq1, hq2, hq3⟩ := hS' q hq
      refine ⟨hq1, hq2, Nat.Coprime.mul_right hq3 ((Nat.coprime_primes hq1 hp.1).mpr ?_)⟩
      rintro rfl
      exact hpS hq
    have hA := ih hM P hP hS' x L
    have hB := ih hMp (fun a => P a ∧ a % p < 3) hP' hS'' x L
    rw [count_crt hM hp.1 (by omega) hp.2.2 P hP] at hB
    have hsplit : (#{a ∈ Ico x (x + L) | P a ∧ ∀ q ∈ insert p S, 3 ≤ a % q} : ℝ) =
        (#{a ∈ Ico x (x + L) | P a ∧ ∀ q ∈ S, 3 ≤ a % q} : ℝ) -
        (#{a ∈ Ico x (x + L) | (P a ∧ a % p < 3) ∧ ∀ q ∈ S, 3 ≤ a % q} : ℝ) := by
      have key : #{a ∈ Ico x (x + L) | P a ∧ ∀ q ∈ insert p S, 3 ≤ a % q} +
          #{a ∈ Ico x (x + L) | (P a ∧ a % p < 3) ∧ ∀ q ∈ S, 3 ≤ a % q} =
          #{a ∈ Ico x (x + L) | P a ∧ ∀ q ∈ S, 3 ≤ a % q} := by
        rw [card_filter, card_filter, card_filter, ← sum_add_distrib]
        refine sum_congr rfl fun a _ => ?_
        simp only [forall_mem_insert, ← Nat.not_lt]
        split_ifs <;> first | rfl | (exfalso; tauto)
      rw [← key]
      push_cast
      ring
    rw [hsplit, prod_insert hpS, card_insert_of_notMem hpS]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.ne_zero
    have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    have hmain : (#{a ∈ range M | P a} : ℝ) * L / M * ((1 - 3 / (p : ℝ)) *
        ∏ q ∈ S, (1 - 3 / (q : ℝ))) =
        (#{a ∈ range M | P a} : ℝ) * L / M * ∏ q ∈ S, (1 - 3 / (q : ℝ)) -
        ((3 * #{a ∈ range M | P a} : ℕ) : ℝ) * L / ((M * p : ℕ) : ℝ) *
          ∏ q ∈ S, (1 - 3 / (q : ℝ)) := by
      push_cast
      field_simp
    rw [hmain, pow_succ]
    obtain ⟨a1, a2⟩ := abs_le.mp hA
    obtain ⟨b1, b2⟩ := abs_le.mp hB
    push_cast at b1 b2 ⊢
    rw [abs_le]
    constructor <;> linarith

/-- Lemma 9, existence form for a single residue class `r mod M`. -/
theorem sieve_exists {M : ℕ} (hM : 0 < M) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ 5 ≤ p ∧ Nat.Coprime p M) (x L r : ℕ) (hr : r < M)
    (hL : M * 10 ^ S.card < L) :
    ∃ a, x ≤ a ∧ a < x + L ∧ a % M = r ∧ ∀ p ∈ S, 3 ≤ a % p := by
  have hc : #{a ∈ range M | a % M = r} = 1 := by
    rw [card_eq_one]
    refine ⟨r, ?_⟩
    ext a
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨ha, h⟩
      rwa [Nat.mod_eq_of_lt ha] at h
    · rintro rfl
      exact ⟨hr, Nat.mod_eq_of_lt hr⟩
  have h := sieve_count S hM (fun a => a % M = r) (fun a => by simp) hS x L
  rw [hc] at h
  simp only [Nat.cast_one, one_mul] at h
  have hprod : ((2 : ℝ) / 5) ^ S.card ≤ ∏ p ∈ S, (1 - 3 / (p : ℝ)) := by
    rw [← prod_const]
    apply prod_le_prod
    · intros
      norm_num
    · intro p hp
      have h5 : (5 : ℝ) ≤ p := by exact_mod_cast (hS p hp).2.1
      have : 3 / (p : ℝ) ≤ 3 / 5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h5
      linarith
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hLM : (10 : ℝ) ^ S.card < L / M := by
    rw [lt_div_iff₀ hMr]
    have : ((M * 10 ^ S.card : ℕ) : ℝ) < L := by exact_mod_cast hL
    push_cast at this
    linarith
  have h4 : (10 : ℝ) ^ S.card * (2 / 5) ^ S.card = 4 ^ S.card := by
    rw [← mul_pow]
    norm_num
  have hpos : (0 : ℝ) < (2 / 5) ^ S.card := by positivity
  have hLM0 : (0 : ℝ) ≤ L / M := by positivity
  have hbig : (4 : ℝ) ^ S.card < L / M * ∏ p ∈ S, (1 - 3 / (p : ℝ)) := by
    calc (4 : ℝ) ^ S.card = 10 ^ S.card * (2 / 5) ^ S.card := h4.symm
      _ < L / M * (2 / 5) ^ S.card := mul_lt_mul_of_pos_right hLM hpos
      _ ≤ L / M * ∏ p ∈ S, (1 - 3 / (p : ℝ)) := mul_le_mul_of_nonneg_left hprod hLM0
  have hN : (0 : ℝ) < (#{a ∈ Ico x (x + L) | a % M = r ∧ ∀ p ∈ S, 3 ≤ a % p} : ℝ) := by
    have := (abs_le.mp h).1
    linarith
  have hN' : 0 < #{a ∈ Ico x (x + L) | a % M = r ∧ ∀ p ∈ S, 3 ≤ a % p} := by
    exact_mod_cast hN
  obtain ⟨a, ha⟩ := card_pos.mp hN'
  simp only [mem_filter, mem_Ico] at ha
  exact ⟨a, ha.1.1, ha.1.2, ha.2.1, ha.2.2⟩

end ErdosLean.Erdos394Limsup

end Sieve

section Omega

/-
## The omega bound (Lemma 10), ineffective form
-/

open Finset Filter

namespace ErdosLean.Erdos394Limsup

/-- `k!` is at most the product of any `k` distinct positive integers. -/
theorem factorial_card_le_prod (s : Finset ℕ) (hs : ∀ x ∈ s, 0 < x) :
    s.card.factorial ≤ ∏ x ∈ s, x := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hs' : ∀ x ∈ s, 0 < x := fun x hx => hs x (Finset.mem_insert_of_mem hx)
    have hcard : s.card + 1 ≤ a := by
      have hsub : s ⊆ Finset.Ioo 0 a := by
        intro x hx
        simp only [Finset.mem_Ioo]
        exact ⟨hs' x hx, ha x hx⟩
      have := Finset.card_le_card hsub
      simp only [Nat.card_Ioo] at this
      have ha0 : 0 < a := hs a (Finset.mem_insert_self a s)
      omega
    rw [Finset.card_insert_of_notMem has, Finset.prod_insert has, Nat.factorial_succ]
    exact Nat.mul_le_mul hcard (ih hs')

/-- `omega(x) = o(log x)`, in the form: for each `k`, eventually `10^(k ω(x)) ≤ x`. -/
theorem pow_card_primeFactors_le (k : ℕ) :
    ∀ᶠ x : ℕ in atTop, 10 ^ (k * x.primeFactors.card) ≤ x := by
  set C := 10 ^ (2 * k) with hC
  filter_upwards [eventually_ge_atTop (10 ^ (k * (2 * C)))] with x hx
  set w := x.primeFactors.card with hw
  have hx0 : 0 < x := lt_of_lt_of_le (Nat.pos_of_ne_zero (by positivity)) hx
  by_cases hwC : w < 2 * C
  · calc 10 ^ (k * w) ≤ 10 ^ (k * (2 * C)) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hwC.le)
      _ ≤ x := hx
  · push Not at hwC
    have hfact : w.factorial ≤ x := by
      calc w.factorial ≤ ∏ p ∈ x.primeFactors, p :=
            factorial_card_le_prod _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
        _ ≤ x := Nat.le_of_dvd hx0 (Nat.prod_primeFactors_dvd x)
    have h1 : C ^ (w - C) ≤ w.factorial := by
      have h := @Nat.factorial_mul_pow_le_factorial C (w - C)
      have hCw : C + (w - C) = w := by omega
      rw [hCw] at h
      calc C ^ (w - C) ≤ (C + 1) ^ (w - C) := Nat.pow_le_pow_left (Nat.le_succ _) _
        _ ≤ C.factorial * (C + 1) ^ (w - C) :=
            Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
        _ ≤ _ := h
    have h2 : 10 ^ (k * w) ≤ C ^ (w - C) := by
      rw [hC, ← pow_mul]
      apply Nat.pow_le_pow_right (by norm_num)
      have : w ≤ 2 * (w - C) := by omega
      calc k * w ≤ k * (2 * (w - C)) := Nat.mul_le_mul_left _ this
        _ = 2 * k * (w - C) := by ring
    exact h2.trans (h1.trans hfact)

theorem card_S_le (n : ℕ) :
    (S n).card ≤ n.primeFactors.card + (n - 1).primeFactors.card + (n - 2).primeFactors.card := by
  have hsub : S n ⊆ (n.primeFactors ∪ (n - 1).primeFactors) ∪ (n - 2).primeFactors := by
    intro p hp
    simp only [S, Finset.mem_filter, Nat.mem_primeFactors] at hp
    obtain ⟨⟨hpp, hd, h0⟩, -⟩ := hp
    have h1 : n ≠ 0 := fun h => h0 (by simp [h])
    have h2 : n - 1 ≠ 0 := fun h => h0 (by simp [h])
    have h3 : n - 2 ≠ 0 := fun h => h0 (by simp [h])
    simp only [Finset.mem_union, Nat.mem_primeFactors]
    rcases (Nat.Prime.dvd_mul hpp).1 hd with hd' | hd'
    · rcases (Nat.Prime.dvd_mul hpp).1 hd' with hd'' | hd''
      · exact Or.inl (Or.inl ⟨hpp, hd'', h1⟩)
      · exact Or.inl (Or.inr ⟨hpp, hd'', h2⟩)
    · exact Or.inr ⟨hpp, hd', h3⟩
  calc (S n).card ≤ ((n.primeFactors ∪ (n - 1).primeFactors) ∪ (n - 2).primeFactors).card :=
        Finset.card_le_card hsub
    _ ≤ (n.primeFactors ∪ (n - 1).primeFactors).card + (n - 2).primeFactors.card :=
        Finset.card_union_le _ _
    _ ≤ _ := by gcongr; exact Finset.card_union_le _ _

/-- Consequence of Lemma 10: `Z := 10^|S| ≤ n^(1/100)` eventually. -/
theorem Z_bound : ∀ᶠ n : ℕ in atTop, (10 ^ (S n).card) ^ 100 ≤ n := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (pow_card_primeFactors_le 300)
  filter_upwards [eventually_ge_atTop (N + 2)] with n hn
  have h0 := hN n (by omega)
  have h1 := hN (n - 1) (by omega)
  have h2 := hN (n - 2) (by omega)
  have h1' : 10 ^ (300 * (n - 1).primeFactors.card) ≤ n := h1.trans (Nat.sub_le _ _)
  have h2' : 10 ^ (300 * (n - 2).primeFactors.card) ≤ n := h2.trans (Nat.sub_le _ _)
  have hS := card_S_le n
  have key : ((10 ^ (S n).card) ^ 100) ^ 3 ≤ n ^ 3 := by
    calc ((10 ^ (S n).card) ^ 100) ^ 3 = 10 ^ (300 * (S n).card) := by
          rw [← pow_mul, ← pow_mul]; ring_nf
      _ ≤ 10 ^ (300 * (n.primeFactors.card + (n - 1).primeFactors.card +
            (n - 2).primeFactors.card)) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hS)
      _ = 10 ^ (300 * n.primeFactors.card) * 10 ^ (300 * (n - 1).primeFactors.card) *
            10 ^ (300 * (n - 2).primeFactors.card) := by
          rw [← pow_add, ← pow_add]; ring_nf
      _ ≤ n * n * n := Nat.mul_le_mul (Nat.mul_le_mul h0 h1') h2'
      _ = n ^ 3 := by ring
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 key

end ErdosLean.Erdos394Limsup

end Omega

section Windows

/-
## The case analysis of the upper bound, producing a `GoodWindow`
-/

open Filter

namespace ErdosLean.Erdos394Limsup

/-- Interval fact (A-intervals). -/
theorem mod_two_mul_of_mem {α a i : ℕ} (h1 : (2 * i + 1) * α + 3 ≤ a) (h2 : a < (2 * i + 2) * α) :
    α + 3 ≤ a % (2 * α) := by
  have e1 : (2 * i + 1) * α = 2 * α * i + α := by ring
  have e2 : (2 * i + 2) * α = 2 * α * i + 2 * α := by ring
  rw [e1] at h1
  rw [e2] at h2
  obtain ⟨r, rfl⟩ : ∃ r, a = r + 2 * α * i := ⟨a - 2 * α * i, by omega⟩
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Interval fact (B-intervals). -/
theorem mod_three_mul_of_mem {β a k : ℕ} (h1 : (3 * k + 2) * β + 3 ≤ a)
    (h2 : a < (3 * k + 3) * β) : 2 * β + 3 ≤ a % (3 * β) := by
  have e1 : (3 * k + 2) * β = 3 * β * k + 2 * β := by ring
  have e2 : (3 * k + 3) * β = 3 * β * k + 3 * β := by ring
  rw [e1] at h1
  rw [e2] at h2
  obtain ⟨r, rfl⟩ : ∃ r, a = r + 3 * β * k := ⟨a - 3 * β * k, by omega⟩
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Case (CC): residues for both conditions, `M = 2α · 3β`, `J = [0, n)`. -/
theorem win_CC {n K0 Z : ℕ} (hn : 6 ≤ n) (h : 6 * alpha n * beta n * Z < n) :
    GoodWindow n K0 Z := by
  obtain ⟨y, hy, hy1, -⟩ := beta_spec hn
  obtain ⟨x, q, hx, hx2, -, -⟩ := alpha_spec hn
  have hα4 := four_le_alpha hn
  have hM : 2 ^ (x + 1) * 3 ^ (y + 1) = 6 * alpha n * beta n := by
    rw [hy, hx, pow_succ, pow_succ]; ring
  have hMpos : 0 < 6 * alpha n * beta n := by
    have := three_le_beta hn; positivity
  refine ⟨0, n, x + 1, y + 1, ?_, ?_, ?_, ?_⟩
  · have h1 : 4 ∣ 2 ^ (x + 1) := (show 4 = 2 ^ 2 by norm_num) ▸ pow_dvd_pow 2 (by omega)
    have h2 : 9 ∣ 3 ^ (y + 1) := (show 9 = 3 ^ 2 by norm_num) ▸ pow_dvd_pow 3 (by omega)
    exact (show 36 = 4 * 9 by norm_num) ▸ Nat.mul_dvd_mul h1 h2
  · rw [hM]; exact h
  · have := Nat.zero_le (n / K0)
    omega
  · intro a _ _ haM
    rw [hM] at haM
    refine ⟨?_, fun hB => ?_⟩
    · have h3 : a % (2 * alpha n) = 2 * alpha n - 1 :=
        mod_eq_pred_of_dvd (Dvd.intro (3 * beta n) (by ring)) (by omega) hMpos haM
      omega
    · have hβ9 := nine_le_beta hn hB
      have h3 : a % (3 * beta n) = 3 * beta n - 1 :=
        mod_eq_pred_of_dvd (Dvd.intro (2 * alpha n) (by ring)) (by omega) hMpos haM
      omega

/-- Case (IC) (also covers `¬ HasB n` with large `alpha`): `M = 4 · 3β`, `J = [α+3, 2α)`. -/
theorem win_IC {n K0 Z : ℕ} (hn : 6 ≤ n) (h : 12 * beta n * Z < alpha n - 3) :
    GoodWindow n K0 Z := by
  obtain ⟨y, hy, hy1, hyB⟩ := beta_spec hn
  have hα4 := four_le_alpha hn
  have hαn := alpha_le hn
  have hβ3 := three_le_beta hn
  have hM : 2 ^ 2 * 3 ^ (y + 1) = 12 * beta n := by rw [hy, pow_succ]; ring
  refine ⟨alpha n + 3, alpha n - 3, 2, y + 1, ?_, ?_, ?_, ?_⟩
  · rw [hM, hy]
    exact (show 36 = 12 * 3 by norm_num) ▸ Nat.mul_dvd_mul_left 12 (dvd_pow_self 3 (by omega))
  · rw [hM]; exact h
  · have := Nat.zero_le (n / K0)
    omega
  · intro a h1 h2 haM
    refine ⟨?_, fun hB => ?_⟩
    · exact mod_two_mul_of_mem (i := 0) (by omega) (by omega)
    · have hβ9 := nine_le_beta hn hB
      have h3 : a % (3 * beta n) = 3 * beta n - 1 :=
        mod_eq_pred_of_dvd (by rw [hM]; exact Dvd.intro_left 4 (by ring)) (by omega)
          (by positivity) haM
      omega

/-- Case (CI): `M = 2α · 9`, `J = [2β+3, 2β+3+min(β-3, n/K0))`. -/
theorem win_CI {n K0 Z : ℕ} (hn : 6 ≤ n) (hB : HasB n) (h1 : 18 * alpha n * Z < beta n - 3)
    (h2 : 18 * alpha n * Z < n / K0) : GoodWindow n K0 Z := by
  obtain ⟨x, q, hx, hx2, -, -⟩ := alpha_spec hn
  have hα4 := four_le_alpha hn
  have hβ9 := nine_le_beta hn hB
  have hβn := beta_le hn
  have hM : 2 ^ (x + 1) * 3 ^ 2 = 18 * alpha n := by rw [hx, pow_succ]; ring
  refine ⟨2 * beta n + 3, min (beta n - 3) (n / K0), x + 1, 2, ?_, ?_, ?_, ?_⟩
  · have h1 : 4 ∣ 2 ^ (x + 1) := (show 4 = 2 ^ 2 by norm_num) ▸ pow_dvd_pow 2 (by omega)
    exact (show 36 = 4 * 3 ^ 2 by norm_num) ▸ Nat.mul_dvd_mul_right h1 _
  · rw [hM]; exact lt_min h1 h2
  · have := min_le_right (beta n - 3) (n / K0)
    omega
  · intro a ha1 ha2 haM
    rw [hM] at haM
    refine ⟨?_, fun _ => ?_⟩
    · have h3 : a % (2 * alpha n) = 2 * alpha n - 1 :=
        mod_eq_pred_of_dvd (Dvd.intro 9 (by ring)) (by omega) (by omega) haM
      omega
    · have := min_le_left (beta n - 3) (n / K0)
      exact mod_three_mul_of_mem (k := 0) (by omega) (by omega)

/-- Case (II-SS): Lemma 6, `M = 36`. -/
theorem win_SS {n K0 Z : ℕ} (hn : 6 ≤ n) (hB : HasB n) (h1 : 5 * (36 * Z + 4) ≤ alpha n)
    (h2 : 5 * (36 * Z + 4) ≤ beta n) (h3 : 27 * alpha n ≤ 2 * n) (h4 : 27 * beta n ≤ 2 * n) :
    GoodWindow n K0 Z := by
  have hα4 := four_le_alpha hn
  have hβ9 := nine_le_beta hn hB
  obtain ⟨i, k, hlen, hhi⟩ := phase_zero (α := alpha n) (β := beta n) (by omega) (by omega)
  set A1 := (2 * i + 1) * alpha n with hA1
  set A2 := (2 * i + 2) * alpha n with hA2
  set B1 := (3 * k + 2) * beta n with hB1
  set B2 := (3 * k + 3) * beta n with hB2
  have hm1 := min_le_left (alpha n) (beta n)
  have hm2 := min_le_right (alpha n) (beta n)
  have hlo1 := le_max_left A1 B1
  have hlo2 := le_max_right A1 B1
  have hhi1 := min_le_left A2 B2
  have hhi2 := min_le_right A2 B2
  have hmax : max (alpha n) (beta n) = alpha n ∨ max (alpha n) (beta n) = beta n := by
    rcases le_total (alpha n) (beta n) with h | h
    · right; exact max_eq_right h
    · left; exact max_eq_left h
  have hmin : min (alpha n) (beta n) = alpha n ∨ min (alpha n) (beta n) = beta n := by
    rcases le_total (alpha n) (beta n) with h | h
    · left; exact min_eq_left h
    · right; exact min_eq_right h
  refine ⟨max A1 B1 + 3, min A2 B2 - max A1 B1 - 3, 2, 2, by norm_num, ?_, ?_, ?_⟩
  · norm_num; omega
  · have := Nat.zero_le (n / K0)
    omega
  · intro a ha1 ha2 _
    refine ⟨mod_two_mul_of_mem (i := i) (by omega) (by omega),
      fun _ => mod_three_mul_of_mem (k := k) (by omega) (by omega)⟩

/-- Case (II-LS): a full A-interval inside `[2β+3, 2β+3+3α) ⊆ [2β+3, 3β)`, `M = 36`. -/
theorem win_LS {n K0 Z : ℕ} (hn : 6 ≤ n) (_hB : HasB n) (h1 : 3 * alpha n ≤ beta n - 3)
    (h2 : 3 * alpha n ≤ n / K0) (h3 : 36 * Z + 3 < alpha n) : GoodWindow n K0 Z := by
  have hα4 := four_le_alpha hn
  have hβn := beta_le hn
  unfold GoodWindow
  set α := alpha n with hα
  set β := beta n with hβ
  -- an A-interval `[(2i+1)α, (2i+2)α)` with `2β ≤ (2i+1)α` and `(2i+2)α ≤ 2β + 3α`
  obtain ⟨i, hi1, hi2⟩ : ∃ i, 2 * β ≤ (2 * i + 1) * α ∧ (2 * i + 2) * α ≤ 2 * β + 3 * α := by
    have e1 : α * (2 * β / α) + 2 * β % α = 2 * β := Nat.div_add_mod _ _
    have e2 : 2 * β % α < α := Nat.mod_lt _ (by omega)
    rcases Nat.even_or_odd (2 * β / α) with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨j, ?_, ?_⟩
      · rw [hj] at e1
        have : α * (j + j) = 2 * (j * α) := by ring
        have h1 : (2 * j + 1) * α = 2 * (j * α) + α := by ring
        rw [h1]; omega
      · rw [hj] at e1
        have : α * (j + j) = 2 * (j * α) := by ring
        have h1 : (2 * j + 2) * α = 2 * (j * α) + 2 * α := by ring
        rw [h1]; omega
    · refine ⟨j + 1, ?_, ?_⟩
      · rw [hj] at e1
        have : α * (2 * j + 1) = 2 * (j * α) + α := by ring
        have h2 : (2 * (j + 1) + 1) * α = 2 * (j * α) + 3 * α := by ring
        rw [h2]; omega
      · rw [hj] at e1
        have : α * (2 * j + 1) = 2 * (j * α) + α := by ring
        have h1 : (2 * (j + 1) + 2) * α = 2 * (j * α) + 4 * α := by ring
        rw [h1]; omega
  have e : (2 * i + 2) * α = (2 * i + 1) * α + α := by ring
  refine ⟨(2 * i + 1) * α + 3, α - 3, 2, 2, by norm_num, by norm_num; omega, ?_, ?_⟩
  · omega
  · intro a ha1 ha2 _
    refine ⟨mod_two_mul_of_mem (i := i) (by omega) (by omega),
      fun _ => mod_three_mul_of_mem (k := 0) (by omega) (by omega)⟩

/-- Case (II-SL): a full B-interval inside `[α+3, 2α)`, `M = 36`. -/
theorem win_SL {n K0 Z : ℕ} (hn : 6 ≤ n) (hB : HasB n) (h1 : 4 * beta n ≤ alpha n - 3)
    (h3 : 36 * Z + 3 < beta n) : GoodWindow n K0 Z := by
  have hαn := alpha_le hn
  have hβ9 := nine_le_beta hn hB
  unfold GoodWindow
  set α := alpha n with hα
  set β := beta n with hβ
  -- a B-interval `[(3k+2)β, (3k+3)β)` with `α ≤ (3k+2)β` and `(3k+3)β ≤ α + 4β`
  obtain ⟨k, hk1, hk2⟩ : ∃ k, α ≤ (3 * k + 2) * β ∧ (3 * k + 3) * β ≤ α + 4 * β := by
    have e1 : β * (α / β) + α % β = α := Nat.div_add_mod _ _
    have e2 : α % β < β := Nat.mod_lt _ (by omega)
    obtain ⟨j, hj⟩ : ∃ j, α / β = 3 * j ∨ α / β = 3 * j + 1 ∨ α / β = 3 * j + 2 :=
      ⟨α / β / 3, by omega⟩
    have h1 : (3 * j + 3) * β = 3 * (j * β) + 3 * β := by ring
    have h2 : (3 * j + 2) * β = 3 * (j * β) + 2 * β := by ring
    have h3 : (3 * (j + 1) + 3) * β = 3 * (j * β) + 6 * β := by ring
    have h4 : (3 * (j + 1) + 2) * β = 3 * (j * β) + 5 * β := by ring
    rcases hj with hj | hj | hj <;> rw [hj] at e1
    · have : β * (3 * j) = 3 * (j * β) := by ring
      exact ⟨j, by omega, by omega⟩
    · have : β * (3 * j + 1) = 3 * (j * β) + β := by ring
      exact ⟨j, by omega, by omega⟩
    · have : β * (3 * j + 2) = 3 * (j * β) + 2 * β := by ring
      exact ⟨j + 1, by omega, by omega⟩
  have e : (3 * k + 3) * β = (3 * k + 2) * β + β := by ring
  refine ⟨(3 * k + 2) * β + 3, β - 3, 2, 2, by norm_num, by norm_num; omega, ?_, ?_⟩
  · have := Nat.zero_le (n / K0)
    omega
  · intro a ha1 ha2 _
    refine ⟨mod_two_mul_of_mem (i := 0) (by omega) (by omega),
      fun _ => mod_three_mul_of_mem (k := k) (by omega) (by omega)⟩

/-- Case (II-LL): Lemma 7, `J = [c n / Q + 4, (c+1)(n-3)/Q)`, `M = 36`. -/
theorem win_LL {n K0 Z q2 q3 : ℕ} (hn : 6 ≤ n) (hB : HasB n) (hq2 : n - n % 4 = q2 * alpha n)
    (hodd : Odd q2) (hq3 : n - jB n = q3 * beta n) (h3 : 2 ≤ q3) (h3' : ¬ 3 ∣ q3)
    (h : q2 * q3 * (36 * Z + 12) ≤ n) : GoodWindow n K0 Z := by
  have hjB := jB_le n
  have hn4 : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  obtain ⟨c, i, k, hc1, hc2, hc3, hc4, hc5⟩ := pattern hodd h3 h3'
  have hq2pos : 1 ≤ q2 := hodd.pos
  unfold GoodWindow
  generalize alpha n = α at hq2 ⊢
  generalize beta n = β at hq3 ⊢
  obtain ⟨Q, hQ⟩ : ∃ Q, q2 * q3 = Q := ⟨_, rfl⟩
  rw [hQ] at h
  have hQ2 : 2 ≤ Q := by rw [← hQ]; nlinarith
  have hαn : q2 * α ≤ n := by omega
  have hαn' : n - 3 ≤ q2 * α := by omega
  have hβn : q3 * β ≤ n := by omega
  have hβn' : n - 3 ≤ q3 * β := by omega
  have hc5' : c + 1 ≤ 2 * Q := by rw [← hQ, ← mul_assoc]; exact hc5
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [Nat.add_sub_cancel] at hαn' hβn'
  have eD : Q * (c * (m + 3) / Q) + c * (m + 3) % Q = c * (m + 3) := Nat.div_add_mod _ _
  have hDlt : c * (m + 3) % Q < Q := Nat.mod_lt _ (by omega)
  have eE : Q * ((c + 1) * m / Q) + (c + 1) * m % Q = (c + 1) * m := Nat.div_add_mod _ _
  have hlen : c * (m + 3) / Q + 36 * Z + 5 ≤ (c + 1) * m / Q := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have : Q * (c * (m + 3) / Q) ≤ c * (m + 3) := by omega
    nlinarith
  have hEle : (c + 1) * m / Q ≤ 2 * m := by
    apply Nat.div_le_of_le_mul
    calc (c + 1) * m ≤ (2 * Q) * m := Nat.mul_le_mul_right _ hc5'
      _ = Q * (2 * m) := by ring
  generalize c * (m + 3) / Q = D at eD hlen
  generalize (c + 1) * m / Q = E at eE hlen hEle
  refine ⟨D + 4, E - (D + 4), 2, 2, by norm_num, by norm_num; omega, ?_, ?_⟩
  · have := Nat.zero_le ((m + 3) / K0)
    omega
  · intro a ha1 ha2 _
    have ha2' : a + 1 ≤ E := by omega
    have hQa : Q * (a + 1) ≤ (c + 1) * m := by
      have := Nat.mul_le_mul_left Q ha2'
      omega
    have hQa' : Q * (D + 4) ≤ Q * a := Nat.mul_le_mul_left _ ha1
    have hQa'' : Q * (D + 4) = Q * D + 4 * Q := by ring
    refine ⟨mod_two_mul_of_mem (i := i) ?_ ?_, fun _ => mod_three_mul_of_mem (k := k) ?_ ?_⟩
    · have m1 : (2 * i + 1) * q3 * (m + 3) ≤ c * (m + 3) := Nat.mul_le_mul_right _ hc1
      have m2 : (2 * i + 1) * q3 * (q2 * α) ≤ (2 * i + 1) * q3 * (m + 3) :=
        Nat.mul_le_mul_left _ hαn
      have : Q * ((2 * i + 1) * α + 3) < Q * a := by
        have e : Q * ((2 * i + 1) * α + 3) = (2 * i + 1) * q3 * (q2 * α) + 3 * Q := by
          rw [← hQ]; ring
        rw [e]; omega
      exact (Nat.lt_of_mul_lt_mul_left this).le
    · have m1 : (c + 1) * m ≤ (2 * i + 2) * q3 * m := Nat.mul_le_mul_right _ hc2
      have m2 : (2 * i + 2) * q3 * m ≤ (2 * i + 2) * q3 * (q2 * α) :=
        Nat.mul_le_mul_left _ hαn'
      have : Q * (a + 1) ≤ Q * ((2 * i + 2) * α) := by
        have e : Q * ((2 * i + 2) * α) = (2 * i + 2) * q3 * (q2 * α) := by rw [← hQ]; ring
        rw [e]; omega
      have := Nat.le_of_mul_le_mul_left this (by omega)
      omega
    · have m1 : (3 * k + 2) * q2 * (m + 3) ≤ c * (m + 3) := Nat.mul_le_mul_right _ hc3
      have m2 : (3 * k + 2) * q2 * (q3 * β) ≤ (3 * k + 2) * q2 * (m + 3) :=
        Nat.mul_le_mul_left _ hβn
      have : Q * ((3 * k + 2) * β + 3) < Q * a := by
        have e : Q * ((3 * k + 2) * β + 3) = (3 * k + 2) * q2 * (q3 * β) + 3 * Q := by
          rw [← hQ]; ring
        rw [e]; omega
      exact (Nat.lt_of_mul_lt_mul_left this).le
    · have m1 : (c + 1) * m ≤ (3 * k + 3) * q2 * m := Nat.mul_le_mul_right _ hc4
      have m2 : (3 * k + 3) * q2 * m ≤ (3 * k + 3) * q2 * (q3 * β) :=
        Nat.mul_le_mul_left _ hβn'
      have : Q * (a + 1) ≤ Q * ((3 * k + 3) * β) := by
        have e : Q * ((3 * k + 3) * β) = (3 * k + 3) * q2 * (q3 * β) := by rw [← hQ]; ring
        rw [e]; omega
      have := Nat.le_of_mul_le_mul_left this (by omega)
      omega

/- ### Size bounds from `Z ^ 100 ≤ n` -/

/-- `X ^ (k+1) ≤ C n ^ k` with `C < n` forces `X < n`. -/
theorem lt_of_pow_succ_le {X C n k : ℕ} (h : X ^ (k + 1) ≤ C * n ^ k) (hC : C < n) : X < n := by
  have hn : 0 < n ^ k := pow_pos (by omega) k
  have : X ^ (k + 1) < n ^ (k + 1) :=
    calc X ^ (k + 1) ≤ C * n ^ k := h
      _ < n * n ^ k := Nat.mul_lt_mul_of_pos_right hC hn
      _ = n ^ (k + 1) := by ring
  exact (Nat.pow_lt_pow_iff_left (by omega)).1 this

/-- `Z ≤ n^(1/100)` and `X ≥ n^(1/4)` give `180 Z + 20 < X`. -/
theorem small_Z {n Z X : ℕ} (hZ : Z ^ 100 ≤ n) (hX : n ≤ X ^ 4) (hn : 200 ^ 100 < n) :
    180 * Z + 20 < X := by
  suffices h : (180 * Z + 20) ^ 4 < n from
    (Nat.pow_lt_pow_iff_left (by norm_num)).1 (lt_of_lt_of_le h hX)
  rcases Nat.eq_zero_or_pos Z with rfl | hZ0
  · have : (180 * 0 + 20) ^ 4 ≤ 200 ^ 100 := by norm_num
    omega
  · have h1 : (180 * Z + 20) ^ 4 ≤ 200 ^ 4 * Z ^ 4 := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) 4
    have h2 : 200 ^ 4 * Z ^ 4 < n := by
      apply lt_of_pow_succ_le (k := 24) (C := 200 ^ 100) _ hn
      have hn1 : n ≤ n ^ 24 := Nat.le_self_pow (by norm_num) n
      calc (200 ^ 4 * Z ^ 4) ^ (24 + 1) = 200 ^ 100 * Z ^ 100 := by ring
        _ ≤ 200 ^ 100 * n ^ 24 := Nat.mul_le_mul_left _ (hZ.trans hn1)
    omega

/-- Size bound for case (II-LL). -/
theorem LL_size {n Z K : ℕ} (hZ : Z ^ 100 ≤ n) (hn : (48 * K ^ 2) ^ 100 < n) :
    K ^ 2 * (36 * Z + 12) ≤ n := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  have hK1 : 1 ≤ 48 * K ^ 2 := by have := pow_pos hK 2; omega
  rcases Nat.eq_zero_or_pos Z with rfl | hZ0
  · have : 48 * K ^ 2 ≤ (48 * K ^ 2) ^ 100 := Nat.le_self_pow (by norm_num) _
    have : K ^ 2 * (36 * 0 + 12) ≤ 48 * K ^ 2 := by omega
    omega
  · have h1 : K ^ 2 * (36 * Z + 12) ≤ 48 * K ^ 2 * Z := by
      have : 36 * Z + 12 ≤ 48 * Z := by omega
      calc K ^ 2 * (36 * Z + 12) ≤ K ^ 2 * (48 * Z) := Nat.mul_le_mul_left _ this
        _ = 48 * K ^ 2 * Z := by ring
    have h2 : 48 * K ^ 2 * Z < n := by
      apply lt_of_pow_succ_le (k := 99) (C := (48 * K ^ 2) ^ 100) _ hn
      have hn1 : n ≤ n ^ 99 := Nat.le_self_pow (by norm_num) n
      calc (48 * K ^ 2 * Z) ^ (99 + 1) = (48 * K ^ 2) ^ 100 * Z ^ 100 := by ring
        _ ≤ (48 * K ^ 2) ^ 100 * n ^ 99 := Nat.mul_le_mul_left _ (hZ.trans hn1)
    omega

/-- Size bounds for the top-level dispatcher, when `X ≤ n^(1/4)` and `Z ≤ n^(1/100)`. -/
theorem F_size {n X Z K0 : ℕ} (hX : X ^ 4 ≤ n) (hZ : Z ^ 100 ≤ n)
    (hn : (126 * K0 + 126) ^ 50 < n) (hK : K0 < n) :
    6 * X * Z * (18 * X * Z + 3) < n ∧ (18 * X * Z + 1) * K0 < n := by
  have e1 : 6 * X * Z * (18 * X * Z + 3) = 6 * (X * Z) * (18 * (X * Z) + 3) := by ring
  have e2 : (18 * X * Z + 1) * K0 = (18 * (X * Z) + 1) * K0 := by ring
  rw [e1, e2]
  have hY : (X * Z) ^ 100 ≤ n ^ 26 := by
    calc (X * Z) ^ 100 = (X ^ 4) ^ 25 * Z ^ 100 := by ring
      _ ≤ n ^ 25 * n := Nat.mul_le_mul (Nat.pow_le_pow_left hX 25) hZ
      _ = n ^ 26 := by ring
  generalize X * Z = Y at hY ⊢
  rcases Nat.eq_zero_or_pos Y with rfl | hY0
  · simp; omega
  set D := 126 * K0 + 126 with hD
  have hDY : D * Y ^ 2 < n := by
    apply lt_of_pow_succ_le (k := 49) (C := D ^ 50) _ hn
    have hn1 : n ^ 26 ≤ n ^ 49 := Nat.pow_le_pow_right (by omega) (by norm_num)
    calc (D * Y ^ 2) ^ (49 + 1) = D ^ 50 * Y ^ 100 := by ring
      _ ≤ D ^ 50 * n ^ 49 := Nat.mul_le_mul_left _ (hY.trans hn1)
  have hYY : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) Y
  constructor
  · have : 6 * Y * (18 * Y + 3) ≤ D * Y ^ 2 := by nlinarith
    omega
  · have : (18 * Y + 1) * K0 ≤ D * Y ^ 2 := by nlinarith
    omega

/-- `(4 log_3 n)^4 < n` once `n ≥ 3^20`. -/
theorem log_small {n : ℕ} (hn : 3 ^ 20 ≤ n) : (4 * Nat.log 3 n) ^ 4 < n := by
  have hL : 20 ≤ Nat.log 3 n := Nat.le_log_of_pow_le (by norm_num) hn
  have hpow : 3 ^ Nat.log 3 n ≤ n := Nat.pow_log_le_self 3 (by positivity)
  suffices h : ∀ L, 20 ≤ L → (4 * L) ^ 4 < 3 ^ L from (h _ hL).trans_le hpow
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    obtain ⟨t, rfl⟩ : ∃ t, L = t + 20 := ⟨L - 20, by omega⟩
    have e : 2 * (4 * (t + 20)) ^ 4 = (4 * (t + 20 + 1)) ^ 4 +
        256 * (t ^ 4 + 76 * t ^ 3 + 2154 * t ^ 2 + 26956 * t + 125519) := by ring
    have e' : 3 ^ (t + 20 + 1) = 3 ^ (t + 20) * 3 := pow_succ _ _
    omega

/-- Case (II) dispatcher: both moduli `≥ n^(1/4)`; split by `q2, q3` against `K1 = 14`,
`K2 = 70 K0` into SS / LS / SL / LL (LL uses Lemma 8 to get `q3 ≥ 2`). -/
theorem dispatch_II (K0 : ℕ) (hK0 : 1 ≤ K0) :
    ∀ᶠ n : ℕ in atTop, ∀ Z : ℕ, Z ^ 100 ≤ n → HasB n → n ≤ alpha n ^ 4 → n ≤ beta n ^ 4 →
      GoodWindow n K0 Z := by
  filter_upwards [eventually_gt_atTop (200 ^ 100), eventually_gt_atTop ((48 * (70 * K0) ^ 2) ^ 100),
    eventually_ge_atTop (3 ^ 20)] with n hn1 hn2 hn3 Z hZ hB hα hβ
  have hn6 : 6 ≤ n := le_trans (by norm_num) hn3
  have hn300 : 300 ≤ n := le_trans (by norm_num) hn3
  obtain ⟨x, q2, hx, -, hq2, hodd⟩ := alpha_spec hn6
  rw [← hx] at hq2
  obtain ⟨y, hy, -, hyB⟩ := beta_spec hn6
  obtain ⟨-, q3, hq3, hq3'⟩ := hyB hB
  rw [← hy] at hq3
  have hjB := jB_le n
  have hn4 : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hZα : 180 * Z + 20 < alpha n := small_Z hZ hα hn1
  have hZβ : 180 * Z + 20 < beta n := small_Z hZ hβ hn1
  have hq2α : q2 * alpha n ≤ n := by omega
  have hq2α' : n - 3 ≤ q2 * alpha n := by omega
  have hq3β : q3 * beta n ≤ n := by omega
  have hq3β' : n - 3 ≤ q3 * beta n := by omega
  have h3 : 2 ≤ q3 := by
    rcases Nat.lt_or_ge q3 2 with h | h
    · interval_cases q3
      · simp at hq3; omega
      · rw [one_mul] at hq3
        have h1 := alpha_le_of_q3_eq_one hn6 hB hq3
        have h2 := log_small hn3
        have h4 : alpha n ^ 4 ≤ (4 * Nat.log 3 n) ^ 4 := Nat.pow_le_pow_left h1 4
        omega
    · exact h
  have hK70 : 70 ≤ 70 * K0 := by omega
  by_cases hA : q2 ≤ 70 * K0
  · by_cases hB3 : q3 ≤ 70 * K0
    · -- (II-LL)
      apply win_LL hn6 hB hq2 hodd hq3 h3 hq3'
      have hs := LL_size (K := 70 * K0) hZ hn2
      calc q2 * q3 * (36 * Z + 12) ≤ (70 * K0) * (70 * K0) * (36 * Z + 12) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul hA hB3)
        _ = (70 * K0) ^ 2 * (36 * Z + 12) := by ring
        _ ≤ n := hs
    · by_cases h14 : q2 ≤ 14
      · -- (II-SL)
        have h1 : q2 * alpha n ≤ 14 * alpha n := Nat.mul_le_mul_right _ h14
        have h2 : 71 * beta n ≤ q3 * beta n := Nat.mul_le_mul_right _ (by omega)
        exact win_SL hn6 hB (by omega) (by omega)
      · -- (II-SS)
        have h1 : 15 * alpha n ≤ q2 * alpha n := Nat.mul_le_mul_right _ (by omega)
        have h2 : 15 * beta n ≤ q3 * beta n := Nat.mul_le_mul_right _ (by omega)
        exact win_SS hn6 hB (by omega) (by omega) (by omega) (by omega)
  · by_cases h14 : q3 ≤ 14
    · -- (II-LS)
      have h1 : q3 * beta n ≤ 14 * beta n := Nat.mul_le_mul_right _ h14
      have h2 : (70 * K0 + 1) * alpha n ≤ q2 * alpha n := Nat.mul_le_mul_right _ (by omega)
      have e : (70 * K0 + 1) * alpha n = 70 * (K0 * alpha n) + alpha n := by ring
      have h3 : alpha n ≤ K0 * alpha n := Nat.le_mul_of_pos_left _ (by omega)
      refine win_LS hn6 hB (by omega) ?_ (by omega)
      rw [Nat.le_div_iff_mul_le (by omega)]
      have e' : 3 * alpha n * K0 = 3 * (K0 * alpha n) := by ring
      omega
    · -- (II-SS)
      have h1 : 15 * alpha n ≤ q2 * alpha n := Nat.mul_le_mul_right _ (by omega)
      have h2 : 15 * beta n ≤ q3 * beta n := Nat.mul_le_mul_right _ (by omega)
      exact win_SS hn6 hB (by omega) (by omega) (by omega) (by omega)

/-- Top-level dispatcher: CC / IC / CI, otherwise both moduli are `≥ n^(1/4)` (case II). -/
theorem dispatch (K0 : ℕ) (hK0 : 1 ≤ K0) :
    ∀ᶠ n : ℕ in atTop, ∀ Z : ℕ, Z ^ 100 ≤ n → GoodWindow n K0 Z := by
  filter_upwards [dispatch_II K0 hK0, eventually_ge_atTop 82,
    eventually_gt_atTop ((126 * K0 + 126) ^ 50), eventually_gt_atTop K0] with n hII h82 hbig hK
  intro Z hZ
  have hn6 : 6 ≤ n := by omega
  by_cases hCC : 6 * alpha n * beta n * Z < n
  · exact win_CC hn6 hCC
  by_cases hIC : 12 * beta n * Z < alpha n - 3
  · exact win_IC hn6 hIC
  by_cases hCI : HasB n ∧ 18 * alpha n * Z < beta n - 3 ∧ 18 * alpha n * Z < n / K0
  · exact win_CI hn6 hCI.1 hCI.2.1 hCI.2.2
  push Not at hCC hIC
  have hβ4 : n ≤ beta n ^ 4 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨h1, -⟩ := F_size (X := beta n) hlt.le hZ hbig hK
    have e1 : 12 * beta n * Z = 12 * (beta n * Z) := by ring
    have e2 : 18 * beta n * Z = 18 * (beta n * Z) := by ring
    have hα' : alpha n ≤ 18 * beta n * Z + 3 := by omega
    have : 6 * alpha n * beta n * Z ≤ 6 * beta n * Z * (18 * beta n * Z + 3) :=
      calc 6 * alpha n * beta n * Z = 6 * beta n * Z * alpha n := by ring
        _ ≤ 6 * beta n * Z * (18 * beta n * Z + 3) := Nat.mul_le_mul_left _ hα'
    omega
  have hB : HasB n := by
    by_contra h
    have : beta n = 3 := by simp [beta, h]
    rw [this] at hβ4
    norm_num at hβ4
    omega
  have hα4 : n ≤ alpha n ^ 4 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨h1, h2⟩ := F_size (X := alpha n) hlt.le hZ hbig hK
    have h3 : 18 * alpha n * Z < n / K0 := by
      rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega)]
      exact h2.le
    have h4 : beta n ≤ 18 * alpha n * Z + 3 := by
      by_contra h5
      exact hCI ⟨hB, by omega, h3⟩
    have : 6 * alpha n * beta n * Z ≤ 6 * alpha n * Z * (18 * alpha n * Z + 3) :=
      calc 6 * alpha n * beta n * Z = 6 * alpha n * Z * beta n := by ring
        _ ≤ 6 * alpha n * Z * (18 * alpha n * Z + 3) := Nat.mul_le_mul_left _ h4
    omega
  exact hII Z hZ hB hα4 hβ4

end ErdosLean.Erdos394Limsup

end Windows

section Upper

/-
## Upper bound, ineffective form: `t_{n-3}(n!) ≤ 2n + n/K0 + 3` eventually
-/

open Filter Nat

namespace ErdosLean.Erdos394Limsup

theorem coprime_of_mem_S {n p u v : ℕ} (hp : p ∈ S n) :
    p.Prime ∧ 5 ≤ p ∧ Nat.Coprime p (2 ^ u * 3 ^ v) := by
  simp only [S, Finset.mem_filter, Nat.mem_primeFactors] at hp
  obtain ⟨⟨hpp, -, -⟩, h5⟩ := hp
  refine ⟨hpp, h5, Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ?_) (Nat.Coprime.pow_right _ ?_)⟩
  · exact (Nat.coprime_primes hpp Nat.prime_two).2 (by omega)
  · exact (Nat.coprime_primes hpp Nat.prime_three).2 (by omega)

theorem upper (K0 : ℕ) (hK0 : 1 ≤ K0) :
    ∀ᶠ n : ℕ in atTop, t (n - 3) (n !) ≤ 2 * n + n / K0 + 3 := by
  filter_upwards [dispatch K0 hK0, Z_bound, eventually_ge_atTop 6] with n hW hZ hn
  obtain ⟨x, L, u, v, h36, hML, hxL, hgood⟩ := hW _ hZ
  have hM0 : 0 < 2 ^ u * 3 ^ v := by positivity
  obtain ⟨a, hxa, hax, haM, haS⟩ :=
    sieve_exists hM0 (S n) (fun p hp => coprime_of_mem_S hp) x L (2 ^ u * 3 ^ v - 1)
      (by omega) hML
  obtain ⟨hA, hB⟩ := hgood a hxa hax haM
  have h36' : a % 36 = 35 := mod_eq_pred_of_dvd h36 (by norm_num) hM0 haM
  have := t_le_of_admissible hn h36' hA hB haS
  omega

end ErdosLean.Erdos394Limsup

end Upper

section Main

/-
## Main theorem: `limsup_{n → ∞} t_{n-3}(n!) / n = 2`
-/

open Filter Nat

namespace ErdosLean.Erdos394Limsup

/-- Upper half: for every `ε > 0`, eventually `t_{n-3}(n!) ≤ (2 + ε) n`. -/
theorem tn3_upper : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    (Erdos394.t (n - 3) (n !) : ℝ) ≤ (2 + ε) * n := by
  intro ε hε
  obtain ⟨K0, hK0⟩ := exists_nat_gt (2 / ε)
  have hK0pos : (0 : ℝ) < K0 := lt_trans (by positivity) hK0
  have hK1 : 1 ≤ K0 := by exact_mod_cast (show (0 : ℝ) < K0 from hK0pos)
  obtain ⟨N, hN⟩ := exists_nat_gt (6 / ε)
  filter_upwards [upper K0 hK1, eventually_ge_atTop N] with n hn hnN
  have h1 : ((2 * n + n / K0 + 3 : ℕ) : ℝ) ≤ 2 * n + n / K0 + 3 := by
    push_cast
    have : ((n / K0 : ℕ) : ℝ) ≤ (n : ℝ) / K0 := Nat.cast_div_le
    linarith
  have h2 : (n : ℝ) / K0 ≤ ε / 2 * n := by
    rw [div_le_iff₀ hK0pos]
    have hεK : 2 < ε * K0 := by rw [div_lt_iff₀ hε] at hK0; linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have h3 : (3 : ℝ) ≤ ε / 2 * n := by
    have : (6 / ε : ℝ) < n := lt_of_lt_of_le hN (by exact_mod_cast hnN)
    have : 6 / ε * ε = 6 := by field_simp
    nlinarith
  have h4 : (Erdos394.t (n - 3) (n !) : ℝ) ≤ ((2 * n + n / K0 + 3 : ℕ) : ℝ) := by
    exact_mod_cast hn
  nlinarith

/-- Lower half: `t_{n-3}(n!) ≥ 2n` for infinitely many `n` (namely `n = 3^y`, `y ≥ 2`). -/
theorem tn3_lower : ∃ᶠ n : ℕ in atTop, 2 * n ≤ Erdos394.t (n - 3) (n !) := by
  rw [Nat.frequently_atTop_iff_infinite]
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hlt : B + 2 < 3 ^ (B + 2) := Nat.lt_pow_self (by norm_num)
  have hmem : 3 ^ (B + 2) ∈ {n : ℕ | 2 * n ≤ Erdos394.t (n - 3) (n !)} := by
    have := t_ge_pow_three (y := B + 2) (by omega)
    simp only [Set.mem_ofPred_eq]
    exact le_trans (by omega) this
  have := hB hmem
  omega

/-- Both halves together. -/
theorem erdos_394_tn3_limsup :
    (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (Erdos394.t (n - 3) (n !) : ℝ) ≤ (2 + ε) * n) ∧
      (∃ᶠ n : ℕ in atTop, 2 * n ≤ Erdos394.t (n - 3) (n !)) :=
  ⟨tn3_upper, tn3_lower⟩

/-- **Main theorem.** `limsup_{n → ∞} t_{n-3}(n!) / n = 2`. This is the statement
`Erdos394.erdos_394.variants.factorial_sub_three_limsup` proposed for formal-conjectures. -/
theorem erdos_394.variants.factorial_sub_three_limsup :
    limsup (fun n : ℕ ↦ (Erdos394.t (n - 3) (n !) : ℝ) / n) atTop = 2 := by
  set f := fun n : ℕ => (Erdos394.t (n - 3) (n !) : ℝ) / n with hf
  have hup : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, f n ≤ 2 + ε := by
    intro ε hε
    filter_upwards [tn3_upper ε hε, eventually_ge_atTop 1] with n hn hn1
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    simp only [hf]
    rw [div_le_iff₀ this]
    exact hn
  have hlow : ∃ᶠ n : ℕ in atTop, 2 ≤ f n := by
    have := tn3_lower.and_eventually (eventually_ge_atTop 1)
    refine this.mono fun n ⟨hn, hn1⟩ => ?_
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    simp only [hf]
    rw [le_div_iff₀ this]
    have : ((2 * n : ℕ) : ℝ) ≤ (Erdos394.t (n - 3) (n !) : ℝ) := by exact_mod_cast hn
    push_cast at this
    linarith
  have hcob : IsCoboundedUnder (· ≤ ·) atTop f := by
    refine ⟨2, fun a ha => ?_⟩
    obtain ⟨n, hn1, hn2⟩ := (hlow.and_eventually ha).exists
    exact le_trans hn1 hn2
  have hbdd : IsBoundedUnder (· ≤ ·) atTop f :=
    isBoundedUnder_of_eventually_le ((hup 1 one_pos).mono fun n hn => (by linarith : f n ≤ 3))
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    exact limsup_le_of_le hcob (hup ε hε)
  · exact le_limsup_of_frequently_le hlow hbdd

end ErdosLean.Erdos394Limsup

end Main
