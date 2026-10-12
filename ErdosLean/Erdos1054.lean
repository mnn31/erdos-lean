import FormalConjectures.ErdosProblems.«1054»

/-!
# Erdős Problem 1054 (ii): a disproof of the formal statement

Let `f n` be the least `m` such that `n` is the sum of the `k` smallest divisors of `m` for some
`k ≥ 1` (with the junk value `0` when there is no such `m`). Part (ii) asks whether `f n = o(n)`
along a set of natural density one. It does not:

* (Tao's argument) For fixed `η, δ > 0` the number of `n < X` with `η X ≤ n`, `n` a prefix sum of
  divisors, and `f n ≤ δ n` is `O(δ² X / η)`. Indeed such an `n` equals `∑_{e ∣ m, e ≤ d} e` for
  some `m ≤ δ X` and `d ∣ m`, and `∑_{m ≤ y} ∑_{d ∣ m} ∑_{e ∣ m, e ≤ d} e = O(y²)`.
* For primes `p < q`, `1 + p + q` is the sum of the three smallest divisors of `p q`. The sums of
  two primes up to `Y` take `≫ Y` values: this follows from the additive-energy form of
  Cauchy–Schwarz, Chebyshev's bounds, the two-dimensional upper bound sieve for prime pairs
  `t, t + h`, and the bound `∑_{h ≤ Y} (h / φ(h))² = O(Y)`.

Hence the integers `n` with `f n > δ n` have positive upper density for small `δ`, which rules
out a density-one set on which `f n = o(n)`. The `answer(sorry)` of the repository statement
elaborates to `True`, so `erdos_1054_parts_ii_false` refutes it, and
`erdos_1054_parts_ii_solution` proves it with the answer `False`.

The Selberg sieve material (parts `AuxResults` to `TwoDim`) is vendored, essentially unchanged,
from the Apache-2.0 licensed developments it names in its own headers: Arend Mellendijk's Selberg
sieve as included in PrimeNumberTheoremAnd, and the two-dimensional sieve and Brun–Titchmarsh
modules of the EP1054 formalization (`antoshashakov/Principia-Math-Solutions`).
-/

/- ### Part `AuxResults` -/

section AuxResults
/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/

set_option autoImplicit false

/-
# Auxiliary results for the Selberg sieve

Ported from PrimeNumberTheoremAnd (PNT+, Kontorovich-Tao et al., Apache 2.0), file
`PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/AuxResults.lean` at commit
d963a6e694a05cd82e5f9b9ae7f4d94123e85393 (built there against Mathlib db127794; here against the
Mathlib v4.31.0 tag, whose `Mathlib/NumberTheory/SelbergSieve.lean` is byte-identical).
Port changes: this docstring and `set_option autoImplicit false` only. Declaration names and
namespaces are unchanged (`ArithmeticFunction.IsMultiplicative.prod_factors_of_mult`, `Aux.*`).
-/

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset

namespace ArithmeticFunction.IsMultiplicative

variable {R : Type*}

theorem prod_factors_of_mult (f : ArithmeticFunction ℝ)
    (h_mult : ArithmeticFunction.IsMultiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ a ∈ l.primeFactors, f a = f l := by
  rw [←IsMultiplicative.map_prod_of_subset_primeFactors h_mult l _ Finset.Subset.rfl,
    Nat.prod_primeFactors_of_squarefree hl]

end ArithmeticFunction.IsMultiplicative

namespace Aux
theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 :=
  by
  rw [←Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

theorem ite_sum_zero {p : Prop} [Decidable p] (s : Finset ℕ) (f : ℕ → ℝ) :
    (if p then (∑ x ∈ s, f x) else 0) = ∑ x ∈ s, if p then f x else 0 := by
  split_ifs <;> simp

theorem conv_lambda_sq_larger_sum (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors,
        ∑ d1 ∈ d.divisors,
          ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
      ∑ d ∈ n.divisors,
        ∑ d1 ∈ n.divisors,
          ∑ d2 ∈ n.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0 := by
  apply sum_congr rfl; intro d hd
  rw [mem_divisors] at hd
  simp_rw [←Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ←ite_and, ite_sum_zero,
    ←ite_and]
  congr with d1
  congr with d2
  congr
  rw [eq_iff_iff]
  refine ⟨fun ⟨_, _, h⟩ ↦ h, ?_⟩
  rintro rfl
  exact ⟨Nat.dvd_lcm_left d1 d2, Nat.dvd_lcm_right d1 d2, rfl⟩

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on
    {n | Squarefree n} (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]--
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ←isMultiplicative_moebius.map_mul_of_coprime,
        hmul]

      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw [if_neg hdl.symm, smul_zero]
    · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd)

theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) = if l = m then μ l else 0 := by
  rw [←moebius_inv_dvd_lower_bound _ _ (Squarefree.squarefree_of_dvd hm hP),
    sum_over_dvd_ite hP.ne_zero hm]
  simp_rw[ite_and, ←sum_filter, filter_comm]

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  norm_cast
  apply moebius_inv_dvd_lower_bound' hP l m hm

theorem multiplicative_zero_of_zero_dvd (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    {m n : ℕ} (h_sq : Squarefree n) (hmn : m ∣ n) (h_zero : f m = 0) : f n = 0 := by
  rcases hmn with ⟨k, rfl⟩
  simp only [MulZeroClass.zero_mul,
    h_mult.map_mul_of_coprime (coprime_of_squarefree_mul h_sq), h_zero]

theorem div_mult_of_dvd_squarefree (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    (l d : ℕ) (hdl : d ∣ l) (hl : Squarefree l) (hd : f d ≠ 0) : f l / f d = f (l / d) := by
  apply div_eq_of_eq_mul hd
  rw [← h_mult.right, Nat.div_mul_cancel hdl]
  apply coprime_of_squarefree_mul
  convert hl
  exact Nat.div_mul_cancel hdl

theorem inv_sub_antitoneOn_gt
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (c : R) :
    AntitoneOn (fun x:R ↦ (x-c)⁻¹) (Set.Ioi c) := by
  refine antitoneOn_iff_forall_lt.mpr ?_
  intro a ha b hb hab
  rw [Set.mem_Ioi] at ha hb
  gcongr

theorem inv_sub_antitoneOn_Icc
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c : R) (ha : c < a) :
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact inv_sub_antitoneOn_gt c |>.mono <| (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

theorem inv_antitoneOn_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    AntitoneOn (fun x:R ↦ x⁻¹) (Set.Ioi 0) := by
  convert inv_sub_antitoneOn_gt (R:=R) 0; ring

theorem inv_antitoneOn_Icc {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : R) (ha : 0 < a) :
    AntitoneOn (fun x ↦ x⁻¹) (Set.Icc a b) := by
  convert inv_sub_antitoneOn_Icc a b 0 ha; ring

theorem log_add_one_le_sum_inv (n : ℕ) :
    Real.log ↑(n+1) ≤ ∑ d ∈ Finset.Icc 1 n, (d:ℝ)⁻¹ := by
  calc _ = ∫ x in (1)..↑(n+1), x⁻¹ := ?_
       _ = ∫ x in (1:ℕ)..↑(n+1), x⁻¹ := ?_
       _ ≤ _ := ?_
  · rw[integral_inv (by simp[(show ¬ (1:ℝ) ≤ 0 by norm_num)] )]; congr; ring
  · congr; norm_num
  · apply AntitoneOn.integral_le_sum_Ico (by norm_num)
    apply inv_antitoneOn_Icc
    norm_num

theorem log_le_sum_inv (y : ℝ) (hy : 1 ≤ y) :
    Real.log y ≤ ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ := by
  calc _ ≤ Real.log ↑(Nat.floor y + 1) := ?_
       _ ≤ _ := ?_
  · gcongr
    apply (le_ceil y).trans
    norm_cast
    exact ceil_le_floor_add_one y
  · apply log_add_one_le_sum_inv

theorem sum_inv_le_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ ≤ 1 + Real.log ↑n :=
  by
  rw [← Finset.sum_erase_add (Icc 1 n) _ (by simp [hn] : 1 ∈ Icc 1 n), add_comm]
  gcongr
  · norm_num
  simp only [Icc_erase_left]
  calc
    ∑ d ∈ Ico 2 (n + 1), (d : ℝ)⁻¹ = ∑ d ∈ Ico 2 (n + 1), (↑(d + 1) - 1)⁻¹ := ?_
    _ ≤ ∫ x in (2).. ↑(n + 1), (x - 1)⁻¹  := ?_
    _ = Real.log ↑n := ?_
  · congr; norm_num;
  · apply @AntitoneOn.sum_le_integral_Ico 2 (n + 1) fun x : ℝ => (x - 1)⁻¹
    · linarith [hn]
    apply inv_sub_antitoneOn_Icc; norm_num
  rw [intervalIntegral.integral_comp_sub_right _ 1, integral_inv]
  · norm_num
  norm_num; simp[hn, show (0:ℝ) < 1 by norm_num]

theorem sum_inv_le_log_real (y : ℝ) (hy : 1 ≤ y) :
    ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ ≤ 1 + Real.log y := by
  trans (1 + Real.log (⌊y⌋₊))
  · apply sum_inv_le_log (⌊y⌋₊)
    apply le_floor; norm_cast
  gcongr
  · norm_cast; apply Nat.lt_of_succ_le; apply le_floor; norm_cast
  · apply floor_le; linarith

-- Lemma 3.1 in Heath-Brown's notes
theorem sum_pow_cardDistinctFactors_div_self_le_log_pow {P k : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if d ≤ x then (k:ℝ) ^ (ω d) / (d : ℝ) else (0 : ℝ))
    ≤ (1 + Real.log x) ^ k := by
  have hx_pos : 0 < x := by
    linarith
  calc
    _ = ∑ d ∈ P.divisors,
          ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
            if ∏ i, a i = d ∧ d ∣ P then if ↑d ≤ x then (d : ℝ)⁻¹ else 0 else 0 := ?_
    _ = ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ∏ i, a i ∣ P then if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 else 0 := ?_
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 := ?_ -- do we need this one?
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          ∏ i, if ↑(a i) ≤ x then (a i : ℝ)⁻¹ else 0 := ?_
    _ = ∏ _i : Fin k, ∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0 := by rw [prod_univ_sum]
    _ = (∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0) ^ k := by
      rw [prod_const, Finset.card_fin]
    _ ≤ (1 + Real.log x) ^ k := ?_

  · apply sum_congr rfl; intro d hd
    rw [mem_divisors] at hd
    simp_rw [ite_and];
    rw [← sum_filter, Finset.sum_const, ← finMulAntidiag_eq_piFinset_divisors_filter hd.1 hd.2,
      card_finMulAntidiag_of_squarefree <| hP.squarefree_of_dvd hd.1, if_pos hd.1]
    simp only [div_eq_mul_inv, nsmul_eq_mul, cast_pow, mul_ite, mul_zero]
  · rw [sum_comm]; apply sum_congr rfl; intro a _; rw [sum_eq_single (∏ i, a i)]
    · apply if_ctx_congr _ _ (fun _ => rfl)
      · rw [Iff.comm, iff_and_self]; exact fun _ => rfl
      · intro; rw [cast_prod, ← prod_inv_distrib]
    · exact fun d _ hd_ne ↦ if_neg fun h => hd_ne.symm h.1
    · exact fun h ↦ if_neg fun h' => h (mem_divisors.mpr ⟨h'.2, hP.ne_zero⟩)
  · apply sum_le_sum; intro a _
    by_cases h : (∏ i, a i ∣ P)
    · rw [if_pos h]
    rw [if_neg h]
    split_ifs with h'
    · apply prod_nonneg; intro i _; norm_num
    · rfl
  · apply sum_le_sum; intro a ha
    split_ifs with h
    · gcongr with i hi
      rw [if_pos]
      apply le_trans _ h
      norm_cast
      rw [←prod_erase_mul (a:=i) (h:= hi)]
      apply Nat.le_mul_of_pos_left
      rw [Fintype.mem_piFinset] at ha
      apply prod_pos; intro j _; apply pos_of_mem_divisors (ha j)
    · apply prod_nonneg; intro j _
      split_ifs
      · norm_num
      · rfl
  · rw [←sum_filter]
    gcongr
    trans (∑ d ∈ Icc 1 (floor x), (d:ℝ)⁻¹)
    · apply sum_le_sum_of_subset_of_nonneg
      · intro d; rw[mem_filter, mem_Icc]
        intro hd
        constructor
        · rw [Nat.succ_le_iff]; exact pos_of_mem_divisors hd.1
        · rw [le_floor_iff hx_pos.le]
          exact hd.2
      · norm_num
    apply sum_inv_le_log_real
    linarith

theorem sum_pow_cardDistinctFactors_le_self_mul_log_pow {P h : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if ↑d ≤ x then (h : ℝ) ^ ω d else (0 : ℝ)) ≤
      x * (1 + Real.log x) ^ h := by
  trans (∑ d ∈ P.divisors, x * if ↑d ≤ x then (h : ℝ) ^ ω d / d else (0 : ℝ))
  · simp_rw [mul_ite, mul_zero, ←sum_filter]
    gcongr with i hi
    rw [div_eq_mul_inv, mul_comm _ (i:ℝ)⁻¹, ←mul_assoc]
    trans (1*(h:ℝ)^ω i)
    · rw [one_mul]
    gcongr
    rw [mem_filter] at hi
    rw [←div_eq_mul_inv]
    apply one_le_div (by norm_cast; apply Nat.pos_of_mem_divisors hi.1) |>.mpr hi.2
  rw [←mul_sum];
  gcongr
  apply sum_pow_cardDistinctFactors_div_self_le_log_pow x hx hP

end Aux

end

end AuxResults

/- ### Part `Basic` -/

section Basic
/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module sieve
-/

set_option autoImplicit false

/-
# Upper bound sieves and Λ² sieves (Selberg sieve, basic layer)

Ported from PrimeNumberTheoremAnd (PNT+, Apache 2.0), file
`PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Basic.lean` at commit
d963a6e694a05cd82e5f9b9ae7f4d94123e85393. Port changes: this docstring,
`set_option autoImplicit false`, and the `AuxResults` import path. Names unchanged
(namespace `SelbergSieve`).
-/

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

open Finset Real Nat Aux BoundingSieve

namespace SelbergSieve

variable (s : BoundingSieve)
local notation3 "ν" => BoundingSieve.nu (self := s)
local notation3 "P" => BoundingSieve.prodPrimes (self := s)
local notation3 "a" => BoundingSieve.weights (self := s)
local notation3 "X" => BoundingSieve.totalMass (self := s)
local notation3 "A" => BoundingSieve.support (self := s)
local notation3 "𝒜" => BoundingSieve.multSum (s := s)
local notation3 "R" => BoundingSieve.rem (s := s)

-- S = ∑_{l|P, l≤√y} g(l)
-- Used in statement of the simple form of the selberg bound
def selbergTerms : ArithmeticFunction ℝ :=
  s.nu.pmul (.prodPrimeFactors fun p =>  1 / (1 - ν p))

local notation3 "g" => SelbergSieve.selbergTerms s

theorem selbergTerms_apply (d : ℕ) :
    g d = ν d * ∏ p ∈ d.primeFactors, 1/(1 - ν p) := by
  unfold selbergTerms
  by_cases h : d=0
  · rw [h]; simp
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.prodPrimeFactors_apply h]

section UpperBoundSieve

structure UpperBoundSieve where mk ::
  μPlus : ℕ → ℝ
  hμPlus : IsUpperMoebius μPlus

instance ubToμPlus : CoeFun UpperBoundSieve fun _ => ℕ → ℝ where coe ub := ub.μPlus

def IsLowerMoebius (μMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∑ d ∈ n.divisors, μMinus d ≤ (if n=1 then 1 else 0)

structure LowerBoundSieve where mk ::
  μMinus : ℕ → ℝ
  hμMinus : IsLowerMoebius μMinus

instance lbToμMinus : CoeFun LowerBoundSieve fun _ => ℕ → ℝ where coe lb := lb.μMinus

end UpperBoundSieve

section SieveLemmas

theorem nu_ne_zero_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors P) : ν d ≠ 0 := by
  apply _root_.ne_of_gt
  rw [mem_divisors] at hd
  apply nu_pos_of_dvd_prodPrimes hd.left

def delta (n : ℕ) : ℝ := if n=1 then 1 else 0

local notation "δ" => delta

theorem siftedSum_as_delta : siftedSum (s := s) = ∑ d ∈ s.support, a d * δ (Nat.gcd P d) :=
  by
  rw [siftedSum_eq_sum_support_mul_ite]
  simp only [delta]

-- Unused ?
theorem nu_lt_self_of_dvd_prodPrimes (d : ℕ) (hdP : d ∣ P) (hd_ne_one : d ≠ 1) : ν d < 1 :=
  nu_lt_one_of_dvd_prodPrimes hdP hd_ne_one

-- Facts about g
@[aesop safe]
theorem selbergTerms_pos (l : ℕ) (hl : l ∣ P) : 0 < g l := by
  rw [selbergTerms_apply]
  apply mul_pos
  · exact nu_pos_of_dvd_prodPrimes hl
  apply prod_pos
  intro p hp
  rw [one_div_pos]
  have hp_prime : p.Prime := prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ P := (Nat.dvd_of_mem_primeFactors hp).trans hl
  linarith only [s.nu_lt_one_of_prime p hp_prime hp_dvd]

theorem selbergTerms_mult : ArithmeticFunction.IsMultiplicative g := by
  unfold selbergTerms
  arith_mult

theorem one_div_selbergTerms_eq_conv_moebius_nu (l : ℕ) (hl : Squarefree l)
    (hnu_nonzero : ν l ≠ 0) : 1 / g l = ∑ d ∈ l.divisors, (μ <| l / d) * (ν d)⁻¹ :=
  by
  rw [selbergTerms_apply]
  simp only [one_div, prod_inv_distrib, mul_inv, inv_inv]
  rw [(s.nu_mult).prodPrimeFactors_one_sub_of_squarefree _ hl]
  rw [mul_sum]
  apply symm
  rw [← Nat.sum_divisorsAntidiagonal' fun d e : ℕ => ↑(μ d) * (ν e)⁻¹]
  rw [Nat.sum_divisorsAntidiagonal fun d e : ℕ => ↑(μ d) * (ν e)⁻¹]
  apply sum_congr rfl; intro d hd
  have hd_dvd : d ∣ l := dvd_of_mem_divisors hd
  rw [←div_mult_of_dvd_squarefree ν s.nu_mult l d (dvd_of_mem_divisors hd) hl, inv_div]
  · ring
  revert hnu_nonzero; contrapose!
  exact multiplicative_zero_of_zero_dvd ν s.nu_mult hl hd_dvd

theorem nu_eq_conv_one_div_selbergTerms (d : ℕ) (hdP : d ∣ P) :
    (ν d)⁻¹ = ∑ l ∈ divisors P, if l ∣ d then 1 / g l else 0 := by
  apply symm
  rw [←sum_filter, Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero hdP]
  have hd_pos : 0 < d := Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
  revert hdP; revert d
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on _ (fun _ _ => Nat.dvd_trans)).mpr
  intro l _ hlP
  rw [sum_divisorsAntidiagonal' (f:=fun x y => (μ <| x) * (ν y)⁻¹) (n:=l)]
  apply symm
  exact one_div_selbergTerms_eq_conv_moebius_nu _ l
    (Squarefree.squarefree_of_dvd hlP s.prodPrimes_squarefree)
    (_root_.ne_of_gt <| nu_pos_of_dvd_prodPrimes hlP)

theorem conv_selbergTerms_eq_selbergTerms_mul_nu {d : ℕ} (hd : d ∣ P) :
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) = g d * (ν d)⁻¹ := by
  calc
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) =
        ∑ l ∈ divisors P, if l ∣ d then g (d / l) else 0 := by
      rw [← sum_over_dvd_ite prodPrimes_ne_zero hd,
        ← Nat.sum_divisorsAntidiagonal fun x _ => g x,
        Nat.sum_divisorsAntidiagonal' fun x _ => g x, sum_over_dvd_ite prodPrimes_ne_zero hd]
    _ = g d * ∑ l ∈ divisors P, if l ∣ d then 1 / g l else 0 := by
      rw [mul_sum]; apply sum_congr rfl; intro l hl
      rw [mul_ite_zero]; apply if_ctx_congr Iff.rfl _ (fun _ => rfl); intro h
      rw [← div_mult_of_dvd_squarefree g (selbergTerms_mult s) d l h]
      · ring
      · apply Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree
      · apply _root_.ne_of_gt; rw [mem_divisors] at hl; apply selbergTerms_pos; exact hl.left
    _ = g d * (ν d)⁻¹ := by rw [← nu_eq_conv_one_div_selbergTerms s d hd]

theorem upper_bound_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    siftedSum (s := s) ≤ ∑ d ∈ divisors P, μPlus d * multSum (s := s) d :=
  siftedSum_le_sum_of_upperMoebius _ μPlus.hμPlus

theorem siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    siftedSum (s := s) ≤ X * mainSum (s := s) μPlus + errSum (s := s) μPlus := by
  apply siftedSum_le_mainSum_errSum_of_upperMoebius _ μPlus.hμPlus

end SieveLemmas

-- Results about Lambda Squared Sieves
section LambdaSquared

def lambdaSquared (weights : ℕ → ℝ) : ℕ → ℝ := fun d =>
  ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
    if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0

private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ (d : ℕ), ¬d ^ 2 ≤ y → w d = 0)
    {d : ℕ} (hd : ¬↑d ≤ y) (d1 : ℕ) (d2 : ℕ) (h : d = Nat.lcm d1 d2) (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2, mul_zero]
  by_contra hyp; apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ (d1.lcm d2) := by rw [h]
      _ ≤ (d1*d2) := Nat.div_le_self _ _
      _ ≤ _       := ?_
  · rw [sq]; gcongr

theorem lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬d ≤ y) :
    lambdaSquared w d = 0 := by
  dsimp only [lambdaSquared]
  by_cases hy : 0 ≤ y
  swap
  · push Not at hd hy
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw
      have : (0:ℝ) ≤ (d') ^ 2 := by norm_num
      linarith
    apply sum_eq_zero; intro d1 _
    apply sum_eq_zero; intro d2 _
    rw [this d1, this d2]
    simp only [mul_zero, ite_self]
  apply sum_eq_zero; intro d1 _
  apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw [mul_comm]
    apply lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1
      (Nat.lcm_comm d1 d2 ▸ h) hle

theorem upperMoebius_of_lambda_sq (weights : ℕ → ℝ) (hw : weights 1 = 1) :
    IsUpperMoebius <| lambdaSquared weights := by
  dsimp [IsUpperMoebius, lambdaSquared]
  intro n
  have h_sq :
    (∑ d ∈ n.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
      if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0) =
      (∑ d ∈ n.divisors, weights d) ^ 2 := by
    rw [sq, mul_sum, conv_lambda_sq_larger_sum _ n, sum_comm]
    apply sum_congr rfl; intro d1 hd1
    rw [sum_mul, sum_comm]
    apply sum_congr rfl; intro d2 hd2
    rw [sum_ite_eq_of_mem']
    · ring
    rw [mem_divisors, Nat.lcm_dvd_iff]
    exact ⟨⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩, (mem_divisors.mp hd1).2⟩
  rw [h_sq]
  split_ifs with hn
  · rw [hn]; simp [hw]
  · apply sq_nonneg

-- set_option quotPrecheck false
-- variable (s : Sieve)

-- local notation3 "ν" => Sieve.nu s
-- local notation3 "P" => Sieve.prodPrimes s
-- local notation3 "a" => Sieve.weights s
-- local notation3 "X" => Sieve.totalMass s
-- local notation3 "R" => Sieve.rem s
-- local notation3 "g" => Sieve.selbergTerms s

theorem lambdaSquared_mainSum_eq_quad_form (w : ℕ → ℝ) :
    mainSum (s := s) (lambdaSquared w) =
      ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
        ν d1 * w d1 * ν d2 * w d2 * (ν (d1.gcd d2))⁻¹ := by
  dsimp only [mainSum, lambdaSquared]
  trans (∑ d ∈ divisors P, ∑ d1 ∈ divisors d, ∑ d2 ∈ divisors d,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0)
  · rw [sum_congr rfl]; intro d _
    rw [sum_mul, sum_congr rfl]; intro d1 _
    rw [sum_mul, sum_congr rfl]; intro d2 _
    rw [ite_zero_mul]

  trans (∑ d ∈ divisors P, ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0)
  · apply conv_lambda_sq_larger_sum
  rw [sum_comm, sum_congr rfl]; intro d1 hd1
  rw [sum_comm, sum_congr rfl]; intro d2 hd2
  have h : d1.lcm d2 ∣ P :=
    Nat.lcm_dvd_iff.mpr ⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩
  rw [sum_ite_eq_of_mem' (divisors P) (d1.lcm d2) _ (mem_divisors.mpr ⟨h, prodPrimes_ne_zero⟩)]
  rw [s.nu_mult.map_lcm]
  · ring
  refine _root_.ne_of_gt (nu_pos_of_dvd_prodPrimes ?_)
  trans d1
  · exact Nat.gcd_dvd_left d1 d2
  · exact dvd_of_mem_divisors hd1

theorem lambdaSquared_mainSum_eq_diag_quad_form (w : ℕ → ℝ) :
    mainSum (s := s) (lambdaSquared w) =
      ∑ l ∈ divisors P,
        1 / g l * (∑ d ∈ divisors P, if l ∣ d then ν d * w d else 0) ^ 2 :=
  by
  rw [lambdaSquared_mainSum_eq_quad_form s w]
  trans (∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P, (∑ l ∈ divisors P,
          if l ∣ d1.gcd d2 then 1 / g l * (ν d1 * w d1) * (ν d2 * w d2) else 0))
  · apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 _
    have hgcd_dvd: d1.gcd d2 ∣ P := Trans.trans (Nat.gcd_dvd_left d1 d2) (dvd_of_mem_divisors hd1)
    rw [nu_eq_conv_one_div_selbergTerms s _ hgcd_dvd, mul_sum]
    apply sum_congr rfl; intro l _
    rw [mul_ite_zero]; apply if_congr Iff.rfl _ rfl
    ring
  trans (∑ l ∈ divisors P, ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
        if l ∣ Nat.gcd d1 d2 then 1 / selbergTerms s l * (ν d1 * w d1) * (ν d2 * w d2) else 0)
  · apply symm; rw [sum_comm, sum_congr rfl]; intro d1 _
    rw [sum_comm]
  apply sum_congr rfl; intro l _
  rw [sq, sum_mul, mul_sum, sum_congr rfl]; intro d1 _
  rw [mul_sum, mul_sum, sum_congr rfl]; intro d2 _
  rw [ite_zero_mul_ite_zero, mul_ite_zero]
  apply if_congr (Nat.dvd_gcd_iff) _ rfl;
  ring

end LambdaSquared

end SelbergSieve

end

end Basic

/- ### Part `Selberg` -/

section Selberg
/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module selberg
-/

set_option autoImplicit false

/-
# The Selberg Sieve

This file proves `selberg_bound_simple`, the main theorem of the Selberg.

Ported from PrimeNumberTheoremAnd (PNT+, Apache 2.0), file
`PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Selberg.lean` at commit
d963a6e694a05cd82e5f9b9ae7f4d94123e85393. Port changes: this paragraph,
`set_option autoImplicit false`, and the `Basic` import path. Names unchanged.
-/

set_option lang.lemmaCmd true

noncomputable section

open scoped BigOperators Classical SelbergSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat SelbergSieve.UpperBoundSieve ArithmeticFunction SelbergSieve BoundingSieve

namespace SelbergSieve
set_option quotPrecheck false

variable (s : SelbergSieve)
local notation3 "ν" => BoundingSieve.nu (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "P" => BoundingSieve.prodPrimes (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "a" => BoundingSieve.weights (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "X" => BoundingSieve.totalMass (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "A" => BoundingSieve.support (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "𝒜" => BoundingSieve.multSum (s := SelbergSieve.toBoundingSieve (self := s))
local notation3 "R" => BoundingSieve.rem (s := SelbergSieve.toBoundingSieve (self := s))
local notation3 "g" => SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))
local notation3 "y" => SelbergSieve.level (self := s)
local notation3 "hy" => SelbergSieve.one_le_level (self := s)

@[simp]
def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors P, if l ^ 2 ≤ y then g l else 0

set_option quotPrecheck false
local notation3 "S" => SelbergSieve.selbergBoundingSum s

theorem selbergBoundingSum_pos :
    0 < S := by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos;
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    · apply selbergTerms_pos _ _ (hl.1.1)
  · simp_rw [Finset.Nonempty, mem_filter]; use 1
    constructor
    · apply one_mem_divisors.mpr prodPrimes_ne_zero
    rw [cast_one, one_pow]
    exact s.one_le_level

theorem selbergBoundingSum_ne_zero : S ≠ 0 := by
  apply _root_.ne_of_gt
  exact s.selbergBoundingSum_pos

theorem selbergBoundingSum_nonneg : 0 ≤ S := _root_.le_of_lt s.selbergBoundingSum_pos

def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ P then
    (ν d)⁻¹ * g d * μ d * S⁻¹ *
      ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
  else 0

-- This notation traditionally uses λ, which is unavailable in lean
set_option quotPrecheck false
local notation3 "γ" => SelbergSieve.selbergWeights s

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ P) :
    γ d = 0 := by
  rw [selbergWeights, if_neg hd]

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬d ^ 2 ≤ y) :
    γ d = 0 := by
  dsimp only [selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right _]
    apply Finset.sum_eq_zero
    refine fun m hm => if_neg ?_
    intro hyp
    have : (d^2:ℝ) ≤ (d*m)^2 := by
      norm_cast;
      refine Nat.pow_le_pow_left ?h 2
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mem_divisors hm)
    linarith [hyp.1]
  · rfl

@[aesop safe]
theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ P) :
    0 ≤ γ d * μ d := by
  dsimp only [selbergWeights]
  rw [if_pos hdP, mul_assoc]
  trans ((μ d :ℝ)^2 * (ν d)⁻¹ * g d * S⁻¹ * ∑ m ∈ divisors P,
          if (d * m) ^ 2 ≤ y ∧ Coprime m d then g m else 0)
  swap
  · apply le_of_eq; ring
  refine mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_
  · apply sq_nonneg
  · rw [inv_nonneg]
    exact le_of_lt <| nu_pos_of_dvd_prodPrimes hdP
  · exact le_of_lt <| selbergTerms_pos _ d hdP
  · exact s.selbergBoundingSum_nonneg
  apply sum_nonneg; intro m hm
  split_ifs with h
  · exact le_of_lt <| selbergTerms_pos _ m (dvd_of_mem_divisors hm)
  · rfl

lemma sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
      ∑ l ∈ n.divisors, f l
    = ∑ m ∈ n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  by_cases hn: n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  swap
  · rw [sum_eq_zero, sum_eq_zero]
    · rintro m _
      rw [if_neg]
      rintro h
      apply hkn
      exact (Nat.dvd_mul_right k m).trans h
    · intro l hl; apply h l (dvd_of_mem_divisors hl)
      apply fun hkl => hkn <| hkl.trans (dvd_of_mem_divisors hl)
  trans (∑ l ∈ n.divisors, ∑ m ∈ n.divisors, if l=k*m then f l else 0)
  · rw [sum_congr rfl]; intro l hl
    by_cases hkl : k ∣ l
    swap
    · rw [h l (dvd_of_mem_divisors hl) hkl, sum_eq_zero];
      intro m _; rw [ite_id]
    rw [sum_eq_single (l/k)]
    · rw[if_pos]; rw [Nat.mul_div_cancel' hkl]
    · intro m _ hmlk
      apply if_neg; revert hmlk; contrapose!; intro hlkm
      rw [hlkm, mul_comm, Nat.mul_div_cancel];
      apply Nat.pos_of_dvd_of_pos hkn (Nat.pos_of_ne_zero hn)
    · contrapose!; intro _
      rw [mem_divisors]
      exact ⟨Trans.trans (Nat.div_dvd_of_dvd hkl) (dvd_of_mem_divisors hl), hn⟩
  · rw [sum_comm, sum_congr rfl]; intro m _
    split_ifs with hdvd
    · rw [sum_ite_eq_of_mem']
      simp only [mem_divisors, hdvd, ne_eq, hn, not_false_eq_true, and_self]
    · apply sum_eq_zero; intro l hl
      apply if_neg;
      rintro rfl
      simp only [mem_divisors, ne_eq] at hl
      exact hdvd hl.1

--Important facts about the selberg weights
theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    ν d * γ d =
      S⁻¹ * μ d *
        ∑ l ∈ divisors P, if d ∣ l ∧ l ^ 2 ≤ y then g l else 0 := by
  by_cases h_dvd : d ∣ P
  swap
  · dsimp only [selbergWeights]; rw [if_neg h_dvd]
    rw [sum_eq_zero]
    · ring
    intro l hl; rw [mem_divisors] at hl
    rw [if_neg]; push Not; intro h
    exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [selbergWeights]
  rw [if_pos h_dvd]
  repeat rw [mul_sum]
  -- change of variables l=m*d
  apply symm
  rw [sum_mul_subst d P]
  · apply sum_congr rfl
    intro m hm
    rw [mul_ite_zero, ←ite_and, mul_ite_zero, mul_ite_zero]
    apply if_ctx_congr _ _ fun _ => rfl
    · rw [coprime_comm]
      constructor
      · intro h
        push_cast at h
        exact ⟨h.2.2, coprime_of_squarefree_mul
          <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree⟩
      · intro h
        push_cast
        exact ⟨ Coprime.mul_dvd_of_dvd_of_dvd h.2 h_dvd (dvd_of_mem_divisors hm),
          Nat.dvd_mul_right d m, h.1⟩
    · intro h
      trans ((ν d)⁻¹ * (ν d) * g d * μ d / S * g m)
      · rw [inv_mul_cancel₀ (nu_ne_zero h_dvd),
          (selbergTerms_mult _).map_mul_of_coprime <| coprime_comm.mp h.2]
        ring
      ring
  · intro l _ hdl
    rw [if_neg, mul_zero]
    push Not; intro h; contradiction

theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors P) :
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
      if l ^ 2 ≤ y then g l * μ l * S⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
        ∑ d ∈ divisors P, ∑ k ∈ divisors P,
          if l ∣ d ∧ d ∣ k ∧ k ^ 2 ≤ y then g k * S⁻¹ * (μ d:ℝ) else 0 := by
      apply sum_congr rfl; intro d _
      rw [selbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl; intro k _
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl);
      intro _; ring
    _ = ∑ k ∈ divisors P, if k ^ 2 ≤ y then
            (∑ d ∈ divisors P, if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * g k * S⁻¹
          else 0 := by
      rw [sum_comm]; apply sum_congr rfl; intro k _
      apply symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum, sum_congr rfl]
      intro d _
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ←ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      · tauto
      intro _; ring
    _ = if l ^ 2 ≤ y then g l * μ l * S⁻¹ else 0 := by
      rw [← sum_ite_eq_of_mem' (divisors P) l (fun _ => if l^2 ≤ y then g l * μ l * S⁻¹ else 0) hl]
      apply sum_congr rfl; intro k hk
      rw [Aux.moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l _ (dvd_of_mem_divisors hk),
        ←ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]; apply and_congr_right
        intro heq; rw [heq]
      · intro h; rw [h.1]; ring

def selbergMuPlus : ℕ → ℝ :=
  lambdaSquared γ

set_option quotPrecheck false
local notation3 "μ⁺" => SelbergSieve.selbergMuPlus s

theorem weight_one_of_selberg : γ 1 = 1 := by
  dsimp only [selbergWeights]
  rw [if_pos (one_dvd P), s.nu_mult.left, (selbergTerms_mult _).map_one]
  simp only [inv_one, mul_one, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
    cardFactors_one, _root_.pow_zero, Int.cast_one, selbergBoundingSum, one_mul,
    coprime_one_right_eq_true, and_true, cast_one]
  rw [inv_mul_cancel₀]
  convert! s.selbergBoundingSum_ne_zero

theorem selbergμPlus_eq_zero (d : ℕ) (hd : ¬d ≤ y) : μ⁺ d = 0 := by
  apply lambdaSquared_eq_zero_of_support _ y _ d hd
  apply s.selbergWeights_eq_zero

def selbergUbSieve : UpperBoundSieve :=
  ⟨μ⁺, upperMoebius_of_lambda_sq γ (s.weight_one_of_selberg)⟩

-- proved for general lambda squared sieves
theorem mainSum_eq_diag_quad_form :
    mainSum (s := s.toBoundingSieve) μ⁺ =
      ∑ l ∈ divisors P,
        1 / g l *
          (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) ^ 2 :=
  by apply lambdaSquared_mainSum_eq_diag_quad_form

theorem selberg_bound_simple_mainSum :
    mainSum (s := s.toBoundingSieve) μ⁺ = S⁻¹ := by
  rw [mainSum_eq_diag_quad_form]
  trans (∑ l ∈ divisors P, (if l ^ 2 ≤ y then g l * (S⁻¹) ^ 2 else 0))
  · apply sum_congr rfl; intro l hl
    rw [s.selbergWeights_diagonalisation l hl, ite_pow, zero_pow two_ne_zero, mul_ite_zero]
    apply if_congr Iff.rfl _ rfl
    trans (1/g l * g l * g l * (μ l:ℝ)^2  * (S⁻¹) ^ 2)
    · ring
    norm_cast; rw [moebius_sq_eq_one_of_squarefree <| squarefree_of_mem_divisors_prodPrimes hl]
    rw [one_div_mul_cancel <| _root_.ne_of_gt <| selbergTerms_pos _ l <| dvd_of_mem_divisors hl]
    ring
  conv => {lhs; congr; {skip}; {ext i; rw [← ite_zero_mul]}}
  dsimp only [selbergBoundingSum]
  rw [←sum_mul, sq, ←mul_assoc, mul_inv_cancel₀]
  · ring
  · apply _root_.ne_of_gt; apply selbergBoundingSum_pos

lemma eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : Coprime m d) (hk : k ≠ 0) :
    k = d.gcd (k*m) := by
  obtain ⟨r, hr⟩ := hkd
  have hrdvd : r ∣ d := by use k; rw [mul_comm]; exact hr
  apply symm; rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  apply Coprime.coprime_dvd_right hrdvd hmd

private lemma _helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors P) (hm : m ∈ divisors P) :
    k * m ∣ P ∧ k = Nat.gcd d (k * m) ∧ (k * m) ^ 2 ≤ y ↔
    (k * m) ^ 2 ≤ y ∧ Coprime m d := by
  constructor
  · intro h
    constructor
    · exact h.2.2
    · obtain ⟨r, hr⟩ := hkd
      rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by rintro rfl; simp at hk ⊢)] at h
      rw [hr, coprime_comm]; apply Coprime.mul_left
      · apply coprime_of_squarefree_mul <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree
      · exact h.2.1
  · intro h
    constructor
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]; exact Coprime.coprime_dvd_right hkd h.2
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    constructor
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2 (by rintro rfl; simp at hk ⊢)
    · exact h.1

theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ P) :
    S ≥ γ d * ↑(μ d) * S := by
  calc
  _ = (∑ k ∈ divisors P, ∑ l ∈ divisors P, if k = d.gcd l ∧ l ^ 2 ≤ y then g l else 0) := by
    dsimp only [selbergBoundingSum]
    rw [sum_comm, sum_congr rfl]; intro l _
    simp_rw [ite_and]
    rw [sum_ite_eq_of_mem']
    · rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans (hdP), prodPrimes_ne_zero⟩
  _ = (∑ k ∈ divisors P,
          if k ∣ d then
            g k * ∑ m ∈ divisors P, if (k * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0) := by
    apply sum_congr rfl; intro k hk
    rw [mul_sum]
    split_ifs with hkd
    swap
    · rw [sum_eq_zero]; intro l _
      rw [if_neg]
      push Not; intro h; exfalso
      rw [h] at hkd
      exact hkd <| Nat.gcd_dvd_left d l
    rw [sum_mul_subst k P, sum_congr rfl]
    · intro m hm
      rw [mul_ite_zero, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · exact_mod_cast s._helper hkd hk hm
      · intro h
        apply (selbergTerms_mult _).map_mul_of_coprime
        rw [gcd_comm]; apply h.2.coprime_dvd_right hkd
    · intro l _ hkl; apply if_neg
      push Not; intro h; exfalso
      rw [h] at hkl; exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k ∈ divisors P, if k ∣ d
          then g k * ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0 ) := by
    apply sum_le_sum; intro k _
    split_ifs with hkd
    swap
    · rfl
    apply mul_le_mul le_rfl _ _ (le_of_lt <| selbergTerms_pos _ k <| hkd.trans hdP)
    · apply sum_le_sum; intro m hm
      split_ifs with h h' h'
      · rfl
      · exfalso; apply h'
        refine ⟨?_, h.2⟩
        · trans ((d*m)^2:ℝ)
          · norm_cast; gcongr
            refine Nat.le_of_dvd ?_ hkd
            apply Nat.pos_of_ne_zero; apply ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
          exact h.1
      · refine le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
      · rfl
    apply sum_nonneg; intro m hm
    split_ifs
    · apply le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
    · rfl
  _ = _ := by
    conv => enter [1, 2, k]; rw [← ite_zero_mul]
    rw [←sum_mul, conv_selbergTerms_eq_selbergTerms_mul_nu _ hdP]
    trans (S * S⁻¹ * (μ d:ℝ)^2 * (ν d)⁻¹ * g d * (∑ m ∈ divisors P, if (d*m) ^ 2 ≤ y ∧
      Coprime m d then g m else 0))
    · rw [mul_inv_cancel₀, ←Int.cast_pow, moebius_sq_eq_one_of_squarefree]
      · ring
      · exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
      · exact _root_.ne_of_gt <| s.selbergBoundingSum_pos
    dsimp only [selbergWeights]; rw [if_pos hdP]
    ring

theorem selberg_bound_weights (d : ℕ) : |γ d| ≤ 1 := by
  by_cases hdP : d ∣ P
  swap
  · rw [s.selbergWeights_eq_zero_of_not_dvd hdP]; simp only [zero_le_one, abs_zero]
  have : 1*S ≥ γ d * ↑(μ d) * S := by
    rw[one_mul]
    exact s.selbergBoundingSum_ge hdP
  replace this : γ d * μ d ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right this (s.selbergBoundingSum_pos)
  convert this using 1
  rw [← abs_of_nonneg <| s.selbergWeights_mul_mu_nonneg d hdP,
    abs_mul, ←Int.cast_abs, abs_moebius_eq_one_of_squarefree <|
    (s.prodPrimes_squarefree.squarefree_of_dvd hdP), Int.cast_one, mul_one]

theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors P) :
    |μ⁺ n| ≤ (3:ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z : ℕ => if n = x.lcm z then 1 else 0
  dsimp only [selbergMuPlus, lambdaSquared]
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then γ d1 * γ d2 else 0| ≤
        ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors, if n = d1.lcm d2 then γ d1 * γ d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, |if n = d1.lcm d2 then γ d1 * γ d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, f d1 d2 := ?_
    _ = (n.divisors ×ˢ n.divisors).sum fun p => f p.fst p.snd := ?_
    _ = Finset.card ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.fst.lcm p.snd) := ?_
    _ = (3:ℕ) ^ ω n := ?_
    _ = (3:ℝ) ^ ω n := ?_
  · apply abs_sum_le_sum_abs
  · gcongr; apply abs_sum_le_sum_abs
  · gcongr with d1 _ d2
    rw [apply_ite abs, abs_zero, abs_mul]
    simp only [f]
    by_cases h : n = d1.lcm d2
    · rw [if_pos h, if_pos h]
      apply mul_le_one₀ (s.selberg_bound_weights d1) (abs_nonneg <| γ d2)
        (s.selberg_bound_weights d2)
    rw [if_neg h, if_neg h]
  · rw [← Finset.sum_product']
  · rw [← sum_filter, Finset.sum_const, smul_one_eq_cast]
  · norm_cast
    simp [← card_pair_lcm_eq (squarefree_of_mem_divisors_prodPrimes hn), eq_comm]
  norm_num

theorem selberg_bound_simple_errSum :
    errSum (s := s.toBoundingSieve) μ⁺ ≤
      ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  dsimp only [errSum]
  gcongr with d hd
  split_ifs with h
  · apply mul_le_mul _ le_rfl (abs_nonneg <| R d) (pow_nonneg _ <| ω d)
    · apply s.selberg_bound_muPlus d hd
    · norm_num
  · rw [s.selbergμPlus_eq_zero d h, abs_zero, zero_mul]

theorem selberg_bound_simple :
    siftedSum (s := s.toBoundingSieve) ≤
      X / S +
        ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  let μPlus := s.selbergUbSieve
  calc
    siftedSum ≤ X * mainSum μPlus + errSum μPlus :=
      siftedSum_le_mainSum_errSum_of_UpperBoundSieve _ μPlus
    _ ≤ _ := ?_
  gcongr
  · erw [s.selberg_bound_simple_mainSum, div_eq_mul_inv]
  · apply s.selberg_bound_simple_errSum

end SelbergSieve

end

end Selberg

/- ### Part `SelbergBounds` -/

section SelbergBounds
/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

set_option autoImplicit false

/-
# Bounds for the Selberg sieve
This file proves a number of results to help bound `Sieve.selbergSum`

## Main Results
* `selbergBoundingSum_ge_sum_div`: If `ν` is completely multiplicative then `S ≥ ∑_{n ≤ √y}, ν n`
* `boundingSum_ge_log`: If `ν n = 1 / n` then `S ≥ log y / 2`
* `rem_sum_le_of_const`: If `R_d ≤ C` then the error term is at most `C * y * (1 + log y)^3`

Ported from PrimeNumberTheoremAnd (PNT+, Apache 2.0), file
`PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/SelbergBounds.lean` at commit
d963a6e694a05cd82e5f9b9ae7f4d94123e85393. Port changes: this paragraph,
`set_option autoImplicit false`, and the `Selberg` import path. Names unchanged.

## Principia additions (end of file, not in PNT+)
* `selbergBoundingSum_ge_sum_div_filter`: the generalisation proposed in the comment above
  `selbergBoundingSum_ge_sum_div` -- no hypothesis that every small prime divides `P`; the
  lower bound sums `ν m` only over those `m ≤ √y` all of whose prime factors divide `P`.
  This is what a sieve that omits the primes of a modulus (Brun-Titchmarsh in progressions)
  needs.
* `rem_sum_le_of_const_of_dvd`: `rem_sum_le_of_const` with the remainder bound required only
  at the divisors of `P`.
-/

set_option lang.lemmaCmd true

open scoped Nat ArithmeticFunction BigOperators Classical ArithmeticFunction.zeta
  ArithmeticFunction.omega
open BoundingSieve SelbergSieve

noncomputable section
namespace Sieve

lemma prodDistinctPrimes_squarefree (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  refine Iff.mpr Nat.squarefree_iff_prime_squarefree ?_
  intro p hp; by_contra h_dvd
  by_cases hps : p ∈ s
  · rw [←Finset.mul_prod_erase (a:=p) (h := hps), mul_dvd_mul_iff_left (Nat.Prime.ne_zero hp)]
      at h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd h_dvd
    rw [Finset.mem_erase] at hq
    exact hq.1.1 <| symm <| (Nat.prime_dvd_prime_iff_eq hp (h q hq.1.2)).mp hq.2
  · have : p ∣ ∏ p ∈ s, p := Trans.trans (dvd_mul_right p p) h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd this
    have heq : p = q := by
      rw [←Nat.prime_dvd_prime_iff_eq hp (h q hq.1)]
      exact hq.2
    rw [heq] at hps; exact hps hq.1

lemma primorial_squarefree (n : ℕ) : Squarefree (primorial n) := by
  apply prodDistinctPrimes_squarefree
  simp_rw [Finset.mem_filter];
  exact fun _ h => h.2

theorem zeta_pos_of_prime : ∀ (p : ℕ), Nat.Prime p → (0:ℝ) < (↑ζ:ArithmeticFunction ℝ) p := by
  intro p hp
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num

theorem zeta_lt_self_of_prime : ∀ (p : ℕ), Nat.Prime p → (↑ζ:ArithmeticFunction ℝ) p < (p:ℝ) := by
  intro p hp
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num;
  exact Nat.succ_le_iff.mp (Nat.Prime.two_le hp)

theorem prime_dvd_primorial_iff (n p : ℕ) (hp : p.Prime) :
    p ∣ primorial n ↔ p ≤ n := by
  unfold primorial
  constructor
  · intro h
    obtain ⟨q, hq⟩ : ∃ i, i ∈ Finset.filter Nat.Prime (Finset.range (n + 1)) ∧ p ∣ i :=
      hp.prime.exists_mem_finset_dvd h
    rw [Finset.mem_filter, Finset.mem_range] at hq
    rw [prime_dvd_prime_iff_eq (Nat.Prime.prime hp) (Nat.Prime.prime hq.1.2)] at hq
    rw [hq.2]
    exact Nat.lt_succ_iff.mp hq.1.1
  · intro h
    apply Finset.dvd_prod_of_mem
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_iff.mpr h, hp⟩

theorem siftedSum_eq (s : SelbergSieve) (hw : ∀ i ∈ s.support, s.weights i = 1) (z : ℝ)
    (hz : 1 ≤ z) (hP : s.prodPrimes = primorial (Nat.floor z)) :
    siftedSum (s := s.toBoundingSieve) =
    (s.support.filter (fun d => ∀ p:ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  dsimp only [siftedSum]
  rw [Finset.card_eq_sum_ones, ←Finset.sum_filter, Nat.cast_sum]
  apply Finset.sum_congr
  · rw [hP]
    ext d; constructor
    · intro hd
      rw [Finset.mem_filter] at *
      constructor
      · exact hd.1
      · intro p hpp hpy
        rw [←Nat.Prime.coprime_iff_not_dvd hpp]
        apply Nat.Coprime.coprime_dvd_left _ hd.2
        rw [prime_dvd_primorial_iff _ _ hpp]
        apply Nat.le_floor hpy
    · intro h
      rw [Finset.mem_filter] at *
      constructor
      · exact h.1
      refine Nat.coprime_of_dvd ?_
      intro p hp
      erw [prime_dvd_primorial_iff _ _ hp]
      intro hpy
      apply h.2 p hp
      trans ↑(Nat.floor z)
      · norm_cast
      · apply Nat.floor_le
        linarith only [hz]
  simp_rw [Nat.cast_one]
  intro x hx
  simp only [Finset.mem_filter] at hx
  apply hw x hx.1

def CompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
  f 1 = 1 ∧ ∀ a b, f (a*b) = f a * f b

namespace CompletelyMultiplicative
open ArithmeticFunction
theorem zeta : CompletelyMultiplicative ζ := by
  unfold CompletelyMultiplicative
  simp_rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, one_ne_zero, ite_false,
    mul_eq_zero, Nat.cast_ite, Nat.cast_one, CharP.cast_eq_zero, mul_ite, mul_zero, mul_one,
    true_and, ← ite_or, or_comm, implies_true]

theorem id : CompletelyMultiplicative ArithmeticFunction.id := by
    constructor <;> simp

theorem pmul (f g : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f)
    (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pmul f g) := by
  constructor
  · rw [pmul_apply, hf.1, hg.1, mul_one]
  intro a b
  simp_rw [pmul_apply, hf.2, hg.2]; ring

theorem pdiv {f g : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f)
    (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pdiv f g) := by
  constructor
  · rw [pdiv_apply, hf.1, hg.1, div_one]
  intro a b
  simp_rw [pdiv_apply, hf.2, hg.2]; ring

theorem isMultiplicative {f : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f) :
    ArithmeticFunction.IsMultiplicative f :=
  ⟨hf.1, fun _ => hf.2 _ _⟩

theorem apply_pow (f : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (a n : ℕ) :
    f (a^n) = f a ^ n := by
  induction n with
  | zero => simp_rw [pow_zero, hf.1]
  | succ n' ih => simp_rw [pow_succ, hf.2, ih]

end CompletelyMultiplicative

theorem prod_factors_one_div_compMult_ge (M : ℕ) (f : ArithmeticFunction ℝ)
    (hf : CompletelyMultiplicative f) (hf_nonneg : ∀ n, 0 ≤ f n) (d : ℕ) (hd : Squarefree d)
    (hf_size : ∀ n, n.Prime → n ∣ d → f n < 1) :
    f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p)
    ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n) := by
  calc f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p)
    = ∏ p ∈ d.primeFactors, f p / (1 - f p)                 := by
        conv => { lhs; congr; rw [←Nat.prod_primeFactors_of_squarefree hd] }
        rw [hf.isMultiplicative.map_prod_of_subset_primeFactors _ _ subset_rfl,
          ←Finset.prod_mul_distrib]
        simp_rw[one_div, div_eq_mul_inv]
  _ ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, (f p)^n  := by
    gcongr with p hp
    · exact fun p _ => Finset.sum_nonneg fun n _ => pow_nonneg (hf_nonneg p) n
    rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
    rw [← Finset.Ico_add_one_right_eq_Icc, geom_sum_Ico,
      ← mul_div_mul_left (c := (-1 : ℝ)) (f p ^ (M + 1) - f p ^ 1)]
    · gcongr
      · apply hf_nonneg
      · linarith [hf_size p hp.1 hp.2]
      · rw [pow_one]
        have : 0 ≤ f p ^ (M + 1) := by
          apply pow_nonneg
          apply hf_nonneg
        linarith only [this]
      · linarith only
    · norm_num
    · apply ne_of_lt <| hf_size p hp.1 hp.2
    · apply Nat.succ_le_iff.mpr (Nat.succ_pos _)

  _ = ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n)  := by
     simp_rw [hf.apply_pow]

theorem prod_factors_sum_pow_compMult (M : ℕ) (hM : M ≠ 0) (f : ArithmeticFunction ℝ)
    (hf : CompletelyMultiplicative f) (d : ℕ) (hd : Squarefree d) :
    ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n)
    = ∑ m ∈ (d^M).divisors.filter (d ∣ ·), f m := by
  rw [Finset.prod_sum]
  let i : (a:_) → (ha : a ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M) → ℕ :=
    fun a _ => ∏ p ∈ d.primeFactors.attach, p.1 ^ (a p p.2)
  have hfact_i : ∀ a ha,
      ∀ p , Nat.factorization (i a ha) p = if hp : p ∈ d.primeFactors then a p hp else 0 := by
    intro a ha p
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp, Nat.factorization_prod, Finset.sum_apply',
        Finset.sum_eq_single ⟨p, hp⟩, Nat.factorization_pow, Finsupp.smul_apply,
        Nat.Prime.factorization_self (Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp)]
      · ring
      · intro q _ hq
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_zero]; right
        apply Nat.factorization_eq_zero_of_not_dvd
        rw [Nat.Prime.dvd_iff_eq, ← exists_eq_subtype_mk_iff]
        · push Not
          exact fun _ => hq
        · exact Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp q.2
        · exact (Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp).ne_one
      · intro h
        exfalso
        exact h (Finset.mem_attach _ _)
      · exact fun q _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactorsList
          (List.mem_toFinset.mp q.2)))
    · rw [dif_neg hp]
      by_cases hpp : p.Prime
      swap
      · apply Nat.factorization_eq_zero_of_not_prime _ hpp
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hp_dvd
      obtain ⟨⟨q, hq⟩, _, hp_dvd_pow⟩ := Prime.exists_mem_finset_dvd hpp.prime hp_dvd
      apply hp
      rw [Nat.mem_primeFactors]
      constructor
      · exact hpp
      refine ⟨?_, hd.ne_zero⟩
      trans q
      · apply Nat.Prime.dvd_of_dvd_pow hpp hp_dvd_pow
      · apply Nat.dvd_of_mem_primeFactorsList <| List.mem_toFinset.mp hq

  have hi_ne_zero : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ≠ 0 := by
    intro a ha
    erw [Finset.prod_ne_zero_iff]
    exact fun p _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactorsList
      (List.mem_toFinset.mp p.property)))
  have hi : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ∈ (d^M).divisors.filter (d ∣ ·) := by
    intro a ha
    rw [Finset.mem_filter, Nat.mem_divisors, ←Nat.factorization_le_iff_dvd hd.ne_zero
      (hi_ne_zero a ha),← Nat.factorization_le_iff_dvd (hi_ne_zero a ha) (pow_ne_zero _ hd.ne_zero)]
    constructor; constructor
    · rw [Finsupp.le_iff]; intro p _
      rw [hfact_i a ha]
      by_cases hp : p ∈ d.primeFactors
      · rw [dif_pos hp]
        rw [Nat.factorization_pow, Finsupp.smul_apply]
        simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
        trans (M • 1)
        · norm_num
          exact (ha p hp).2
        · gcongr
          rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
          rw [←Nat.Prime.dvd_iff_one_le_factorization hp.1 hd.ne_zero]
          exact hp.2
      · rw [dif_neg hp]; norm_num
    · apply pow_ne_zero _ hd.ne_zero
    · rw [Finsupp.le_iff]; intro p hp
      rw [Nat.support_factorization] at hp
      rw [hfact_i a ha]
      rw [dif_pos hp]
      trans 1
      · exact hd.natFactorization_le_one p
      simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
      exact (ha p hp).1

  have h : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      ∏ p ∈ d.primeFactors.attach, f (p.1 ^ (a p p.2)) = f (i a ha) := by
    intro a ha
    apply symm
    apply hf.isMultiplicative.map_prod
    intro x _ y _ hxy
    simp_rw [Finset.mem_pi, Finset.mem_Icc, Nat.succ_le_iff] at ha
    apply (Nat.coprime_pow_left_iff (ha x x.2).1 ..).mpr
    apply (Nat.coprime_pow_right_iff (ha y y.2).1 ..).mpr
    have hxp := Nat.prime_of_mem_primeFactorsList (List.mem_toFinset.mp x.2)
    rw [Nat.Prime.coprime_iff_not_dvd hxp]
    rw [Nat.prime_dvd_prime_iff_eq hxp <| Nat.prime_of_mem_primeFactorsList
      (List.mem_toFinset.mp y.2)]
    exact fun hc => hxy (Subtype.ext hc)

  have i_inj : ∀ a ha b hb, i a ha = i b hb → a = b := by
    intro a ha b hb hiab
    apply_fun Nat.factorization at hiab
    ext p hp
    obtain hiabp := DFunLike.ext_iff.mp hiab p
    rw [hfact_i a ha, hfact_i b hb, dif_pos hp, dif_pos hp] at hiabp
    exact hiabp

  have i_surj : ∀ (b : ℕ), b ∈ (d^M).divisors.filter (d ∣ ·) → ∃ a ha, i a ha = b := by
    intro b hb
    have h : (fun p _ => b.factorization p) ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M := by
      rw [Finset.mem_pi]; intro p hp
      rw [Finset.mem_Icc]
      rw [Finset.mem_filter] at hb
      have hb_ne_zero : b ≠ 0 := ne_of_gt <| Nat.pos_of_mem_divisors hb.1
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      constructor
      · rw [←Nat.Prime.dvd_iff_one_le_factorization hpp hb_ne_zero]
        · exact Trans.trans (Nat.dvd_of_mem_primeFactors hp) hb.2
      · rw [Nat.mem_divisors] at hb
        trans Nat.factorization (d^M) p
        · exact (Nat.factorization_le_iff_dvd hb_ne_zero hb.left.right).mpr hb.left.left p
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        have : d.factorization p ≤ 1 := by
          apply hd.natFactorization_le_one
        exact (mul_le_iff_le_one_right (Nat.pos_of_ne_zero hM)).mpr this
    use (fun p _ => Nat.factorization b p)
    use h
    apply Nat.eq_of_factorization_eq
    · apply hi_ne_zero _ h
    · exact ne_of_gt <| Nat.pos_of_mem_divisors (Finset.mem_filter.mp hb).1
    intro p
    rw [hfact_i (fun p _ => (Nat.factorization b) p) h p]
    rw [Finset.mem_filter, Nat.mem_divisors] at hb
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp]
    · rw [dif_neg hp, eq_comm, Nat.factorization_eq_zero_iff, ←or_assoc]
      rw [Nat.mem_primeFactors] at hp
      left
      push Not at hp
      by_cases hpp : p.Prime
      · right; intro h
        apply absurd (hp hpp)
        push Not
        exact ⟨hpp.dvd_of_dvd_pow (h.trans hb.1.1), hd.ne_zero⟩
      · left; exact hpp

  exact Finset.sum_bij i hi i_inj i_surj h

theorem prod_primes_dvd_of_dvd (P : ℕ) {s : Finset ℕ} (h : ∀ p ∈ s, p ∣ P) (h' : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, p ∣ P := by
  simp_rw [Nat.prime_iff] at h'
  apply Finset.prod_primes_dvd _ h' h

lemma sqrt_le_self (x : ℝ) (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  refine Iff.mpr Real.sqrt_le_iff ?_
  constructor
  · linarith
  refine le_self_pow₀ hx ?right.h
  norm_num

lemma Nat.squarefree_dvd_pow (a b N : ℕ) (ha : Squarefree a) (hab : a ∣ b ^ N) : a ∣ b := by
  by_cases hN : N=0
  · rw [hN, pow_zero, Nat.dvd_one] at hab
    rw [hab]; simp
  rw [Squarefree.dvd_pow_iff_dvd ha hN] at hab
  exact hab

/-
Proposed generalisation :

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve)
    (hnu : CompletelyMultiplicative s.nuDivSelf) (hnu_nonneg : ∀ n, 0 ≤ s.nuDivSelf n)
    (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nuDivSelf p < 1):
    s.selbergBoundingSum ≥ ∑ m in
      (Finset.Icc 1 (Nat.floor <| Real.sqrt s.level)).filter (fun m => ∀ p, p.Prime → p ∣ m → p ∣ s.prodPrimes),
      s.nu m
-/

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve) (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes)
  (hnu : CompletelyMultiplicative s.nu) (hnu_nonneg : ∀ n, 0 ≤ s.nu n) (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p < 1):
    s.selbergBoundingSum ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), s.nu m := by
  unfold selbergBoundingSum
  calc ∑ l ∈ s.prodPrimes.divisors, (if l ^ 2 ≤ s.level then selbergTerms _ l else 0)
     ≥ ∑ l ∈ s.prodPrimes.divisors.filter (fun (l:ℕ) => l^2 ≤ s.level),
        ∑ m ∈ (l^(Nat.floor s.level)).divisors.filter (l ∣ ·), s.nu m         := ?_
   _ ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), s.nu m           := ?_
  · rw [←Finset.sum_filter]; apply Finset.sum_le_sum; intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p ∈ l.primeFactors, ∑ n ∈ Finset.Icc 1 (Nat.floor s.level), s.nu (p^n))
    · rw [prod_factors_sum_pow_compMult (Nat.floor s.level) _ s.nu]
      · exact hnu
      · exact hlsq
      · rw [ne_eq, Nat.floor_eq_zero, not_lt]
        exact s.one_le_level
    rw [selbergTerms_apply _ l]
    apply prod_factors_one_div_compMult_ge _ _ hnu _ _ hlsq
    · intro p hpp hpl
      apply hnu_lt p hpp (Trans.trans hpl hl.1.1)
    · exact hnu_nonneg

  rw [←Finset.sum_biUnion]
  · apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hnu_nonneg _)
    intro m hm
    have hprod_pos : 0 < (∏ p ∈ m.primeFactors, p) := by
      apply Finset.prod_pos;
      intro p hp; exact Nat.pos_of_mem_primeFactorsList <| List.mem_toFinset.mp hp
    have hprod_ne_zero :  (∏ p ∈ m.primeFactors, p) ^ ⌊s.level⌋₊ ≠ 0 := by
      apply pow_ne_zero; apply ne_of_gt; apply hprod_pos
    rw [Finset.mem_biUnion]; simp_rw [Finset.mem_filter, Nat.mem_divisors]
    rw [Finset.mem_Icc, Nat.le_floor_iff] at hm
    · have hm_ne_zero : m ≠ 0 := by
        exact ne_of_gt <| Nat.succ_le_iff.mp hm.1
      use ∏ p ∈ m.primeFactors, p
      constructor; constructor; constructor
      · apply prod_primes_dvd_of_dvd <;> intro p hp
        · apply hP p <| Nat.prime_of_mem_primeFactors hp
          trans (m:ℝ)
          · exact_mod_cast Nat.le_of_mem_primeFactors hp
          trans (Real.sqrt s.level)
          · exact hm.2
          apply sqrt_le_self s.level s.one_le_level
        exact Nat.prime_of_mem_primeFactors hp
      · exact prodPrimes_ne_zero
      · rw [←Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]), Real.sqrt_sq]
        · trans (m:ℝ)
          · norm_cast; apply Nat.le_of_dvd (Nat.succ_le_iff.mp hm.1)
            exact Nat.prod_primeFactors_dvd m
          exact hm.2
        apply le_of_lt; norm_cast
      constructor; constructor
      · rw [←Nat.factorization_le_iff_dvd _ hprod_ne_zero, Nat.factorization_pow]
        · intro p
          have hy_mul_prod_nonneg : 0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p ∈ m.primeFactors, p)) p := by
            apply mul_nonneg
            · apply Nat.le_floor; norm_cast; linarith only [s.one_le_level]
            · norm_num
          trans (Nat.factorization m) p * 1
          · rw [mul_one]
          rw [Finsupp.smul_apply, smul_eq_mul]
          by_cases hpp : p.Prime
          swap
          · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, zero_mul]; exact hy_mul_prod_nonneg
          by_cases hpdvd : p ∣ m
          swap
          · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]; exact hy_mul_prod_nonneg
          apply mul_le_mul
          · trans m
            · apply le_of_lt <| Nat.factorization_lt _ _
              apply hm_ne_zero
            apply Nat.le_floor
            refine le_trans hm.2 ?_
            apply sqrt_le_self _ s.one_le_level
          · rw [←Nat.Prime.pow_dvd_iff_le_factorization hpp <| ne_of_gt hprod_pos, pow_one]
            apply Finset.dvd_prod_of_mem
            rw [Nat.mem_primeFactors]
            exact ⟨hpp, hpdvd, hm_ne_zero⟩
          · norm_num
          · norm_num
        exact hm_ne_zero
      · exact hprod_ne_zero
      · exact Nat.prod_primeFactors_dvd m
    · apply Real.sqrt_nonneg
  · intro i hi j hj hij t hti htj x hx
    simp only [Finset.bot_eq_empty, Finset.notMem_empty]
    specialize hti hx
    specialize htj hx
    simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
    have h : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ x → x ∣ j ^ n → i ∣ j := by
      intro i j n hiP hix hij
      apply Nat.squarefree_dvd_pow i j n (squarefree_of_dvd_prodPrimes hiP)
      exact Trans.trans hix hij
    have hidvdj : i ∣ j := by
      apply h i j hi.1.1 hti.2 htj.1.1
    have hjdvdi : j ∣ i := by
      apply h j i hj.1.1 htj.2 hti.1.1
    exact hij <| Nat.dvd_antisymm hidvdj hjdvdi

theorem boundingSum_ge_sum (s : SelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
  (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes) :
    s.selbergBoundingSum ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), 1 / (m:ℝ) := by
  trans ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), (ζ : ArithmeticFunction ℝ).pdiv .id m
  · rw[←hnu]
    apply selbergBoundingSum_ge_sum_div
    · intro p hpp hple
      apply hP p hpp hple
    · rw[hnu]
      exact CompletelyMultiplicative.zeta.pdiv CompletelyMultiplicative.id
    · intro n
      rw[hnu]
      apply div_nonneg
      · by_cases h : n = 0 <;> simp[h]
      simp
    · intro p hpp _
      rw[hnu]
      simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one,
        ArithmeticFunction.id_apply]
      rw [if_neg, one_div]
      · apply inv_lt_one_of_one_lt₀; norm_cast
        exact hpp.one_lt
      exact hpp.ne_zero
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_Icc] at hm
  simp only [one_div, ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne (show m ≠ 0 by omega), Nat.cast_one,
    ArithmeticFunction.id_apply];

theorem boundingSum_ge_log (s : SelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
  (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes)  :
    s.selbergBoundingSum ≥ Real.log (s.level) / 2 := by
  trans (∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), 1 / (m:ℝ))
  · exact boundingSum_ge_sum s hnu hP
  trans (Real.log <| Real.sqrt s.level)
  · rw [ge_iff_le]; simp_rw[one_div]
    apply Aux.log_le_sum_inv (Real.sqrt s.level)
    rw [Real.le_sqrt] <;> linarith[s.one_le_level]
  · apply ge_of_eq
    refine Real.log_sqrt ?h.hx
    linarith[s.one_le_level]

open ArithmeticFunction

theorem rem_sum_le_of_const (s : SelbergSieve) (C : ℝ) (hrem : ∀ d > 0, |rem (s := s.toBoundingSieve) d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors, (if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |rem (s := s.toBoundingSieve) d| else 0)
      ≤ C * s.level * (1+Real.log s.level)^3 := by
  rw [←Finset.sum_filter]
  trans (∑ d ∈  Finset.filter (fun d:ℕ => ↑d ≤ s.level) (s.prodPrimes.divisors),  3 ^ ω d * C )
  · gcongr with d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    apply hrem d
    apply Nat.pos_of_ne_zero
    apply ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1
  rw [←Finset.sum_mul, mul_comm, mul_assoc]
  gcongr
  · linarith [abs_nonneg <| rem (s := s.toBoundingSieve) 1, hrem 1 (by norm_num)]
  rw [Finset.sum_filter]
  apply Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (hx := s.one_le_level)
  apply prodPrimes_squarefree

/- ## Principia additions (not in PNT+) -/

/-- Generalisation of `selbergBoundingSum_ge_sum_div` without the hypothesis that every prime
`p ≤ y` divides `P`: the lower bound sums `ν m` over those `m ≤ √y` all of whose prime factors
divide `P`. (This is the generalisation proposed in PNT+'s comment above
`selbergBoundingSum_ge_sum_div`.) -/
theorem selbergBoundingSum_ge_sum_div_filter (s : SelbergSieve)
    (hnu : CompletelyMultiplicative s.nu) (hnu_nonneg : ∀ n, 0 ≤ s.nu n)
    (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p < 1) :
    s.selbergBoundingSum ≥ ∑ m ∈ (Finset.Icc 1 (Nat.floor <| Real.sqrt s.level)).filter
      (fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ∣ s.prodPrimes), s.nu m := by
  unfold selbergBoundingSum
  calc ∑ l ∈ s.prodPrimes.divisors, (if l ^ 2 ≤ s.level then selbergTerms _ l else 0)
     ≥ ∑ l ∈ s.prodPrimes.divisors.filter (fun (l:ℕ) => l^2 ≤ s.level),
        ∑ m ∈ (l^(Nat.floor s.level)).divisors.filter (l ∣ ·), s.nu m         := ?_
   _ ≥ ∑ m ∈ (Finset.Icc 1 (Nat.floor <| Real.sqrt s.level)).filter
      (fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ∣ s.prodPrimes), s.nu m           := ?_
  · rw [←Finset.sum_filter]; apply Finset.sum_le_sum; intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p ∈ l.primeFactors, ∑ n ∈ Finset.Icc 1 (Nat.floor s.level), s.nu (p^n))
    · rw [prod_factors_sum_pow_compMult (Nat.floor s.level) _ s.nu]
      · exact hnu
      · exact hlsq
      · rw [ne_eq, Nat.floor_eq_zero, not_lt]
        exact s.one_le_level
    rw [selbergTerms_apply _ l]
    apply prod_factors_one_div_compMult_ge _ _ hnu _ _ hlsq
    · intro p hpp hpl
      apply hnu_lt p hpp (Trans.trans hpl hl.1.1)
    · exact hnu_nonneg
  rw [←Finset.sum_biUnion]
  · apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hnu_nonneg _)
    intro m hm'
    rw [Finset.mem_filter] at hm'
    obtain ⟨hm, hmP⟩ := hm'
    have hprod_pos : 0 < (∏ p ∈ m.primeFactors, p) := by
      apply Finset.prod_pos
      intro p hp; exact Nat.pos_of_mem_primeFactorsList <| List.mem_toFinset.mp hp
    have hprod_ne_zero :  (∏ p ∈ m.primeFactors, p) ^ ⌊s.level⌋₊ ≠ 0 := by
      apply pow_ne_zero; apply ne_of_gt; apply hprod_pos
    rw [Finset.mem_biUnion]; simp_rw [Finset.mem_filter, Nat.mem_divisors]
    rw [Finset.mem_Icc, Nat.le_floor_iff] at hm
    · have hm_ne_zero : m ≠ 0 := by
        exact ne_of_gt <| Nat.succ_le_iff.mp hm.1
      use ∏ p ∈ m.primeFactors, p
      constructor; constructor; constructor
      · apply prod_primes_dvd_of_dvd <;> intro p hp
        · exact hmP p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
        exact Nat.prime_of_mem_primeFactors hp
      · exact prodPrimes_ne_zero
      · rw [←Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]), Real.sqrt_sq]
        · trans (m:ℝ)
          · norm_cast; apply Nat.le_of_dvd (Nat.succ_le_iff.mp hm.1)
            exact Nat.prod_primeFactors_dvd m
          exact hm.2
        apply le_of_lt; norm_cast
      constructor; constructor
      · rw [←Nat.factorization_le_iff_dvd _ hprod_ne_zero, Nat.factorization_pow]
        · intro p
          have hy_mul_prod_nonneg :
              0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p ∈ m.primeFactors, p)) p := by
            apply mul_nonneg
            · apply Nat.le_floor; norm_cast; linarith only [s.one_le_level]
            · norm_num
          trans (Nat.factorization m) p * 1
          · rw [mul_one]
          rw [Finsupp.smul_apply, smul_eq_mul]
          by_cases hpp : p.Prime
          swap
          · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, zero_mul]; exact hy_mul_prod_nonneg
          by_cases hpdvd : p ∣ m
          swap
          · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]; exact hy_mul_prod_nonneg
          apply mul_le_mul
          · trans m
            · apply le_of_lt <| Nat.factorization_lt _ _
              apply hm_ne_zero
            apply Nat.le_floor
            refine le_trans hm.2 ?_
            apply sqrt_le_self _ s.one_le_level
          · rw [←Nat.Prime.pow_dvd_iff_le_factorization hpp <| ne_of_gt hprod_pos, pow_one]
            apply Finset.dvd_prod_of_mem
            rw [Nat.mem_primeFactors]
            exact ⟨hpp, hpdvd, hm_ne_zero⟩
          · norm_num
          · norm_num
        exact hm_ne_zero
      · exact hprod_ne_zero
      · exact Nat.prod_primeFactors_dvd m
    · apply Real.sqrt_nonneg
  · intro i hi j hj hij t hti htj x hx
    simp only [Finset.bot_eq_empty, Finset.notMem_empty]
    specialize hti hx
    specialize htj hx
    simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
    have h : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ x → x ∣ j ^ n → i ∣ j := by
      intro i j n hiP hix hij
      apply Nat.squarefree_dvd_pow i j n (squarefree_of_dvd_prodPrimes hiP)
      exact Trans.trans hix hij
    have hidvdj : i ∣ j := by
      apply h i j hi.1.1 hti.2 htj.1.1
    have hjdvdi : j ∣ i := by
      apply h j i hj.1.1 htj.2 hti.1.1
    exact hij <| Nat.dvd_antisymm hidvdj hjdvdi

open ArithmeticFunction in
/-- `rem_sum_le_of_const` with the remainder bound required only at the divisors of `P`. -/
theorem rem_sum_le_of_const_of_dvd (s : SelbergSieve) (C : ℝ)
    (hrem : ∀ d, d ∣ s.prodPrimes → |rem (s := s.toBoundingSieve) d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors,
        (if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |rem (s := s.toBoundingSieve) d| else 0)
      ≤ C * s.level * (1 + Real.log s.level) ^ 3 := by
  rw [←Finset.sum_filter]
  trans (∑ d ∈ Finset.filter (fun d:ℕ => ↑d ≤ s.level) (s.prodPrimes.divisors), 3 ^ ω d * C)
  · gcongr with d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    exact hrem d hd.1.1
  rw [←Finset.sum_mul, mul_comm, mul_assoc]
  gcongr
  · linarith [abs_nonneg <| rem (s := s.toBoundingSieve) 1, hrem 1 (one_dvd _)]
  rw [Finset.sum_filter]
  apply Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (hx := s.one_le_level)
  apply prodPrimes_squarefree

end Sieve
end

end SelbergBounds

/- ### Part `BrunTitchmarshAP` -/

section BrunTitchmarshAP
set_option autoImplicit false

/-
# The Brun–Titchmarsh inequality in arithmetic progressions

For every modulus `q ≥ 1`, every residue `a` and every real `x > q`,
`π(x; q, a) ≤ 2008 · x / (φ(q) · log (x / q))`
(`Principia.Common.BrunTitchmarshAP.brun_titchmarsh_ap`). The constant is not optimised
(Montgomery–Vaughan give `2`); no coprimality of `a` and `q` is needed for the upper bound.

## Route (Selberg's Λ² sieve, from the PNT+ port in this directory)

* `apSieve q a N z`: the progression `{n ≤ N : n ≡ a (mod q)}` sifted by the primes `p ≤ z`
  with `p ∤ q`, density `ν(d) = 1/d`, total mass `X = (N+1)/q`.
* Remainders: for `d ∣ P` we have `gcd(d, q) = 1`, so by the Chinese remainder theorem the
  multiples of `d` in the progression form one class mod `qd`, whose count in `[0, N]` is
  `⌊(N+1)/(qd)⌋ + (0 or 1)`; hence `|R_d| ≤ 1` (`abs_rem_le`).
* Main term: `Sieve.selbergBoundingSum_ge_sum_div_filter` (added to the port) bounds the Selberg
  sum below by `∑_{n ≤ √z, (n, q) = 1} 1/n`, and `harmAvoid_prod` gives
  `∑_{n ≤ T, (n,q)=1} 1/n ≥ (φ(q)/q) ∑_{n ≤ T} 1/n ≥ (φ(q)/q) log T` by removing the primes of
  `q` one at a time (`(1 - 1/p) H_Q ≤ H_{Q ∪ {p}}`).
* Choice `z = √(x/q)`: main term `≤ 8x/(φ(q) log(x/q))`, remainder and the unsifted primes
  `p ≤ z` together `≤ 2000 x/(φ(q) log(x/q))` (`log_poly_bound`).
-/

open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.omega
open BoundingSieve SelbergSieve

noncomputable section

namespace Principia.Common.BrunTitchmarshAP

/- ## Harmonic sums avoiding a finite set of primes -/

/-- `∑_{1 ≤ n ≤ T, q ∤ n for all q ∈ Q} 1/n`. -/
def harmAvoid (Q : Finset ℕ) (T : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n), (1 / (n : ℝ))

theorem harmAvoid_empty (T : ℕ) : harmAvoid ∅ T = ∑ n ∈ Finset.Icc 1 T, (1 / (n : ℝ)) := by
  unfold harmAvoid
  congr 1
  apply Finset.filter_true_of_mem
  intro n _ q hq
  simp at hq

/-- Removing one more prime `p` costs at most the factor `1 - 1/p`. -/
theorem harmAvoid_insert (Q : Finset ℕ) (p T : ℕ) (hp : p.Prime) :
    (1 - 1 / (p : ℝ)) * harmAvoid Q T ≤ harmAvoid (insert p Q) T := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)) (fun n => p ∣ n)
    (fun n => 1 / (n : ℝ))
  have hnot : ∑ n ∈ ((Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).filter
      (fun n => ¬ p ∣ n), (1 / (n : ℝ)) = harmAvoid (insert p Q) T := by
    unfold harmAvoid
    rw [Finset.filter_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    apply Finset.filter_congr
    intro n _
    simp only [Finset.mem_insert, forall_eq_or_imp]
    tauto
  have hsub : ((Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).filter (fun n => p ∣ n) ⊆
      ((Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).image (fun k => p * k) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨h1, hT⟩, hQ⟩, k, rfl⟩ := hn
    rw [Finset.mem_image]
    refine ⟨k, ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · rw [hk, Nat.mul_zero] at h1
        exact absurd h1 (by norm_num)
      · exact hk
    refine ⟨⟨hk, le_trans (Nat.le_mul_of_pos_left k hp.pos) hT⟩, ?_⟩
    intro q hq hqk
    exact hQ q hq (Dvd.dvd.mul_left hqk p)
  have hdvd : ∑ n ∈ ((Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).filter
      (fun n => p ∣ n), (1 / (n : ℝ)) ≤ (1 / (p : ℝ)) * harmAvoid Q T := by
    calc ∑ n ∈ ((Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).filter
          (fun n => p ∣ n), (1 / (n : ℝ))
        ≤ ∑ n ∈ ((Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).image (fun k => p * k),
            (1 / (n : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∑ k ∈ (Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n),
            (1 / (((p * k : ℕ)) : ℝ)) :=
          Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hp.pos hab)
      _ = (1 / (p : ℝ)) * harmAvoid Q T := by
          unfold harmAvoid
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [Nat.cast_mul, one_div_mul_one_div]
  have hH : harmAvoid Q T = ∑ n ∈ ((Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).filter
      (fun n => p ∣ n), (1 / (n : ℝ)) + ∑ n ∈ ((Finset.Icc 1 T).filter
        (fun n => ∀ q ∈ Q, ¬ q ∣ n)).filter (fun n => ¬ p ∣ n), (1 / (n : ℝ)) := by
    unfold harmAvoid
    exact hsplit.symm
  rw [sub_mul, one_mul]
  linarith

/-- Removing all the primes of `Q` costs at most `∏_{p ∈ Q} (1 - 1/p)`. -/
theorem harmAvoid_prod (T : ℕ) (Q : Finset ℕ) :
    (∀ p ∈ Q, p.Prime) → (∏ p ∈ Q, (1 - 1 / (p : ℝ))) * harmAvoid ∅ T ≤ harmAvoid Q T := by
  induction Q using Finset.induction_on with
  | empty => intro _; simp
  | insert p Q hpQ ih =>
    intro hQ
    have hp : p.Prime := hQ p (Finset.mem_insert_self p Q)
    have ih' := ih (fun q hq => hQ q (Finset.mem_insert_of_mem hq))
    have h1 : 0 ≤ 1 - 1 / (p : ℝ) := by
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
      have : 1 / (p : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]
        exact hp1
      linarith
    rw [Finset.prod_insert hpQ, mul_assoc]
    calc (1 - 1 / (p : ℝ)) * ((∏ q ∈ Q, (1 - 1 / (q : ℝ))) * harmAvoid ∅ T)
        ≤ (1 - 1 / (p : ℝ)) * harmAvoid Q T := mul_le_mul_of_nonneg_left ih' h1
      _ ≤ harmAvoid (insert p Q) T := harmAvoid_insert Q p T hp

/-- Euler's product for `φ(q)/q`, over `ℝ`. -/
theorem totient_div_eq_prod (q : ℕ) (hq : 0 < q) :
    (q.totient : ℝ) / q = ∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h := Nat.totient_eq_mul_prod_factors q
  have h' : (q.totient : ℝ) = q * ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have := congrArg (fun r : ℚ => (r : ℝ)) h
    push_cast at this
    exact this
  rw [h', mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hq.ne')]
  simp only [one_div]

/-- The coprime harmonic sum: `(φ(q)/q) log T ≤ ∑_{n ≤ T, (n, q) = 1} 1/n` for real `T ≥ 1`
(coprimality to `q` written as avoiding every prime factor of `q`). -/
theorem totient_mul_log_le_harmAvoid (q : ℕ) (hq : 0 < q) (T : ℝ) (hT : 1 ≤ T) :
    (q.totient : ℝ) / q * Real.log T ≤ harmAvoid q.primeFactors ⌊T⌋₊ := by
  have hlog : Real.log T ≤ harmAvoid ∅ ⌊T⌋₊ := by
    rw [harmAvoid_empty]
    simp only [one_div]
    exact Aux.log_le_sum_inv T hT
  have hnn : 0 ≤ (q.totient : ℝ) / q := by positivity
  calc (q.totient : ℝ) / q * Real.log T ≤ (q.totient : ℝ) / q * harmAvoid ∅ ⌊T⌋₊ :=
        mul_le_mul_of_nonneg_left hlog hnn
    _ = (∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ))) * harmAvoid ∅ ⌊T⌋₊ := by
        rw [totient_div_eq_prod q hq]
    _ ≤ harmAvoid q.primeFactors ⌊T⌋₊ :=
        harmAvoid_prod ⌊T⌋₊ q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)

/- ## The sieve on an arithmetic progression -/

/-- The sifting primes: `p ≤ z` prime with `p ∤ q`. -/
def siftPrimes (q : ℕ) (z : ℝ) : Finset ℕ :=
  (Finset.range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ q)

/-- Sifting the primes `p ≤ z`, `p ∤ q`, from the progression `{n ≤ N : n ≡ a (mod q)}`, with
density `ν(d) = 1/d` and total mass `(N+1)/q`. -/
def apSieve (q a N : ℕ) (z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := (Finset.range (N + 1)).filter (fun n => n % q = a % q)
  prodPrimes := ∏ p ∈ siftPrimes q z, p
  prodPrimes_squarefree := Sieve.prodDistinctPrimes_squarefree _
    (fun p hp => (Finset.mem_filter.mp hp).2.1)
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := ((N : ℝ) + 1) / q
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hp.ne_zero, ↓reduceIte, Nat.cast_one,
      ArithmeticFunction.id_apply, one_div]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp.one_lt
  level := z
  one_le_level := hz

section APSieve

variable (q a N : ℕ) (z : ℝ) (hz : 1 ≤ z)

theorem prime_dvd_prodPrimes_iff {p : ℕ} (hp : p.Prime) :
    p ∣ (apSieve q a N z hz).prodPrimes ↔ p ≤ ⌊z⌋₊ ∧ ¬ p ∣ q := by
  show p ∣ ∏ p ∈ siftPrimes q z, p ↔ _
  constructor
  · intro h
    obtain ⟨i, hi, hpi⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd h
    rw [siftPrimes, Finset.mem_filter, Finset.mem_range] at hi
    have hpi' : p = i := (Nat.prime_dvd_prime_iff_eq hp hi.2.1).mp hpi
    rw [← hpi'] at hi
    exact ⟨Nat.lt_succ_iff.mp hi.1, hi.2.2⟩
  · rintro ⟨h1, h2⟩
    exact Finset.dvd_prod_of_mem (fun p => p)
      (by rw [siftPrimes, Finset.mem_filter, Finset.mem_range]
          exact ⟨Nat.lt_succ_of_le h1, hp, h2⟩)

theorem coprime_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ (apSieve q a N z hz).prodPrimes) :
    Nat.Coprime q d := by
  apply Nat.coprime_of_dvd
  intro k hk hkq hkd
  exact ((prime_dvd_prodPrimes_iff q a N z hz hk).mp (hkd.trans hd)).2 hkq

theorem multSum_eq (d : ℕ) :
    multSum (s := (apSieve q a N z hz).toBoundingSieve) d =
      ((((Finset.range (N + 1)).filter (fun n => n % q = a % q)).filter
        (fun n => d ∣ n)).card : ℝ) := by
  show (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % q = a % q),
      if d ∣ n then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole]

/-- The multiples of `d` in the progression (`gcd(d, q) = 1`) form one class mod `qd`. -/
theorem card_filter_modEq_dvd {d : ℕ} (hd0 : 0 < d) (hq0 : 0 < q) (hcop : Nat.Coprime q d) :
    ∃ e : ℕ, e ≤ 1 ∧
      (((Finset.range (N + 1)).filter (fun n => n % q = a % q)).filter (fun n => d ∣ n)).card
        = (N + 1) / (q * d) + e := by
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder hcop a 0
  have hset : ((Finset.range (N + 1)).filter (fun n => n % q = a % q)).filter (fun n => d ∣ n)
      = (Finset.range (N + 1)).filter (fun n => n ≡ c [MOD q * d]) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro n _
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : n ≡ a [MOD q] := h1
      exact ⟨h1'.trans hc1.symm, (Nat.modEq_zero_iff_dvd.mpr h2).trans hc2.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(h1.trans hc1 : n ≡ a [MOD q]), Nat.modEq_zero_iff_dvd.mp (h2.trans hc2)⟩
  rw [hset, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ (Nat.mul_pos hq0 hd0)]
  refine ⟨if c % (q * d) < (N + 1) % (q * d) then 1 else 0, ?_, rfl⟩
  split_ifs <;> norm_num

/-- The sieve remainders are bounded by `1` at every divisor of `P`. -/
theorem abs_rem_le (hq0 : 0 < q) {d : ℕ} (hd : d ∣ (apSieve q a N z hz).prodPrimes) :
    |rem (s := (apSieve q a N z hz).toBoundingSieve) d| ≤ 1 := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hd)
  obtain ⟨e, he, hcard⟩ :=
    card_filter_modEq_dvd q a N hd0 hq0 (coprime_of_dvd_prodPrimes q a N z hz hd)
  have hnu : (apSieve q a N z hz).nu d = 1 / (d : ℝ) := by
    show ((ζ : ArithmeticFunction ℝ).pdiv .id) d = 1 / (d : ℝ)
    simp [ArithmeticFunction.pdiv_apply, hd0.ne']
  have hmain : (apSieve q a N z hz).nu d * (apSieve q a N z hz).totalMass
      = ((N + 1 : ℕ) : ℝ) / ((q * d : ℕ) : ℝ) := by
    rw [hnu]
    show 1 / (d : ℝ) * (((N : ℝ) + 1) / q) = _
    push_cast
    rw [div_mul_div_comm, one_mul, mul_comm (d : ℝ) (q : ℝ)]
  have hk1 : ((((N + 1) / (q * d) : ℕ)) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) / ((q * d : ℕ) : ℝ) :=
    Nat.cast_div_le
  have hk2 : ((N + 1 : ℕ) : ℝ) / ((q * d : ℕ) : ℝ) < ((((N + 1) / (q * d) : ℕ)) : ℝ) + 1 := by
    rw [← Nat.floor_div_eq_div (K := ℝ) (N + 1) (q * d)]
    exact Nat.lt_floor_add_one _
  have he' : (e : ℝ) ≤ 1 := by exact_mod_cast he
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  unfold rem
  rw [multSum_eq, hcard, hmain, Nat.cast_add ((N + 1) / (q * d)) e, abs_le]
  constructor <;> linarith

/-- The primes counted by `π(N; q, a)` are sifted, or at most `z`. -/
theorem card_primes_le :
    (((Finset.Iic N).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ) ≤
      siftedSum (s := (apSieve q a N z hz).toBoundingSieve) + (⌊z⌋₊ : ℝ) := by
  have hsift : siftedSum (s := (apSieve q a N z hz).toBoundingSieve) =
      ((((Finset.range (N + 1)).filter (fun n => n % q = a % q)).filter
        (fun n => Nat.Coprime (apSieve q a N z hz).prodPrimes n)).card : ℝ) := by
    show (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % q = a % q),
      if Nat.Coprime (apSieve q a N z hz).prodPrimes n then (1 : ℝ) else 0) = _
    rw [Finset.sum_boole]
  have hsub : (Finset.Iic N).filter (fun p => p.Prime ∧ p % q = a % q) ⊆
      ((Finset.range (N + 1)).filter (fun n => n % q = a % q)).filter
        (fun n => Nat.Coprime (apSieve q a N z hz).prodPrimes n) ∪ Finset.Icc 1 ⌊z⌋₊ := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Iic] at hp
    obtain ⟨hpN, hpp, hpa⟩ := hp
    rw [Finset.mem_union]
    by_cases hpz : p ≤ ⌊z⌋₊
    · right
      rw [Finset.mem_Icc]
      exact ⟨hpp.one_lt.le, hpz⟩
    · left
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨by omega, hpa⟩, ?_⟩
      apply Nat.Coprime.symm
      rw [Nat.Prime.coprime_iff_not_dvd hpp]
      intro hdvd
      exact hpz ((prime_dvd_prodPrimes_iff q a N z hz hpp).mp hdvd).1
  have hcard := Finset.card_union_le (((Finset.range (N + 1)).filter
      (fun n => n % q = a % q)).filter (fun n => Nat.Coprime (apSieve q a N z hz).prodPrimes n))
    (Finset.Icc 1 ⌊z⌋₊)
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
  rw [hsift]
  have h1 := Finset.card_le_card hsub
  have h2 : ((Finset.Iic N).filter (fun p => p.Prime ∧ p % q = a % q)).card ≤
      (((Finset.range (N + 1)).filter (fun n => n % q = a % q)).filter
        (fun n => Nat.Coprime (apSieve q a N z hz).prodPrimes n)).card + ⌊z⌋₊ :=
    h1.trans hcard
  exact_mod_cast h2

/-- The Selberg lower bound for the sieve's bounding sum: `S ≥ (φ(q)/q) log √z`. -/
theorem boundingSum_ge (hq0 : 0 < q) :
    (q.totient : ℝ) / q * Real.log (Real.sqrt z) ≤ (apSieve q a N z hz).selbergBoundingSum := by
  have hsqrt1 : 1 ≤ Real.sqrt z := Real.one_le_sqrt.mpr hz
  have hCM : Sieve.CompletelyMultiplicative (apSieve q a N z hz).nu :=
    Sieve.CompletelyMultiplicative.zeta.pdiv Sieve.CompletelyMultiplicative.id
  have hnn : ∀ n, 0 ≤ (apSieve q a N z hz).nu n := by
    intro n
    show 0 ≤ ((ζ : ArithmeticFunction ℝ).pdiv .id) n
    rw [ArithmeticFunction.pdiv_apply]
    apply div_nonneg
    · by_cases h : n = 0 <;> simp [h]
    · simp
  refine le_trans ?_ (Sieve.selbergBoundingSum_ge_sum_div_filter (apSieve q a N z hz) hCM hnn
    (apSieve q a N z hz).nu_lt_one_of_prime)
  refine le_trans (totient_mul_log_le_harmAvoid q hq0 (Real.sqrt z) hsqrt1) ?_
  unfold harmAvoid
  calc ∑ n ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter (fun n => ∀ r ∈ q.primeFactors, ¬ r ∣ n),
        (1 / (n : ℝ))
      = ∑ n ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter (fun n => ∀ r ∈ q.primeFactors, ¬ r ∣ n),
          (apSieve q a N z hz).nu n := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mem_filter, Finset.mem_Icc] at hn
        have hn0 : n ≠ 0 := by
          obtain ⟨⟨hn1, _⟩, _⟩ := hn
          omega
        show _ = ((ζ : ArithmeticFunction ℝ).pdiv .id) n
        simp [ArithmeticFunction.pdiv_apply, hn0]
    _ ≤ _ := by
        classical
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [Finset.mem_filter, Finset.mem_Icc] at hn
          obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hn
          refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hn2⟩, ?_⟩
          intro p hp hpn
          rw [prime_dvd_prodPrimes_iff q a N z hz hp]
          constructor
          · have hpn' : p ≤ n := Nat.le_of_dvd (by omega) hpn
            have hT : ⌊Real.sqrt z⌋₊ ≤ ⌊z⌋₊ := Nat.floor_mono (Sieve.sqrt_le_self z hz)
            omega
          · intro hpq
            exact hn3 p (Nat.mem_primeFactors.mpr ⟨hp, hpq, hq0.ne'⟩) hpn
        · intro i _ _
          exact hnn i

/-- The Selberg upper bound for the sifted progression. -/
theorem siftedSum_le (hq0 : 0 < q) (hz1 : 1 < z) :
    siftedSum (s := (apSieve q a N z hz).toBoundingSieve) ≤
      (((N : ℝ) + 1) / q) / ((q.totient : ℝ) / q * Real.log (Real.sqrt z)) +
        z * (1 + Real.log z) ^ 3 := by
  have hS := boundingSum_ge q a N z hz hq0
  have hpos : 0 < (q.totient : ℝ) / q * Real.log (Real.sqrt z) := by
    apply mul_pos
    · apply div_pos
      · exact_mod_cast Nat.totient_pos.mpr hq0
      · exact_mod_cast hq0
    · apply Real.log_pos
      exact Real.lt_sqrt_of_sq_lt (by norm_num; linarith)
  have herr := Sieve.rem_sum_le_of_const_of_dvd (apSieve q a N z hz) 1
    (fun d hd => abs_rem_le q a N z hz hq0 hd)
  have hX : 0 ≤ (apSieve q a N z hz).totalMass := by
    show 0 ≤ ((N : ℝ) + 1) / q
    positivity
  refine le_trans (SelbergSieve.selberg_bound_simple (apSieve q a N z hz)) ?_
  refine add_le_add (div_le_div_of_nonneg_left hX hpos hS) ?_
  refine le_trans herr (le_of_eq ?_)
  show 1 * z * (1 + Real.log z) ^ 3 = z * (1 + Real.log z) ^ 3
  rw [one_mul]

end APSieve

/- ## The final estimate -/

/-- `4 (1 + log z)^3 log z ≤ 2000 z` for `z ≥ 1` (via `log z ≤ 4 z^{1/4}`). -/
theorem log_poly_bound (z : ℝ) (hz : 1 ≤ z) :
    4 * (1 + Real.log z) ^ 3 * Real.log z ≤ 2000 * z := by
  have hz0 : 0 ≤ z := by linarith
  have hlog : Real.log z ≤ z ^ ((1 : ℝ) / 4) / ((1 : ℝ) / 4) :=
    Real.log_le_rpow_div hz0 (by norm_num)
  have hv1 : 1 ≤ z ^ ((1 : ℝ) / 4) := Real.one_le_rpow hz (by norm_num)
  have hv4 : (z ^ ((1 : ℝ) / 4)) ^ 4 = z := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz0]
    norm_num
  have hl0 : 0 ≤ Real.log z := Real.log_nonneg hz
  have hl : Real.log z ≤ 4 * z ^ ((1 : ℝ) / 4) := by
    have : z ^ ((1 : ℝ) / 4) / ((1 : ℝ) / 4) = 4 * z ^ ((1 : ℝ) / 4) := by ring
    linarith
  have h1 : 1 + Real.log z ≤ 5 * z ^ ((1 : ℝ) / 4) := by linarith
  have h1' : (1 + Real.log z) ^ 3 ≤ (5 * z ^ ((1 : ℝ) / 4)) ^ 3 :=
    pow_le_pow_left₀ (by linarith) h1 3
  have h2 : 4 * (1 + Real.log z) ^ 3 ≤ 4 * (5 * z ^ ((1 : ℝ) / 4)) ^ 3 :=
    mul_le_mul_of_nonneg_left h1' (by norm_num)
  have hc : 0 ≤ 4 * (5 * z ^ ((1 : ℝ) / 4)) ^ 3 :=
    mul_nonneg (by norm_num) (pow_nonneg (by linarith) 3)
  calc 4 * (1 + Real.log z) ^ 3 * Real.log z
      ≤ 4 * (5 * z ^ ((1 : ℝ) / 4)) ^ 3 * (4 * z ^ ((1 : ℝ) / 4)) :=
        mul_le_mul h2 hl hl0 hc
    _ = 2000 * (z ^ ((1 : ℝ) / 4)) ^ 4 := by ring
    _ = 2000 * z := by rw [hv4]

/-- **Brun–Titchmarsh in arithmetic progressions.** For every `q ≥ 1`, every `a` and every real
`x > q`, `π(x; q, a) ≤ 2008 x / (φ(q) log (x / q))`, where
`π(x; q, a) = #{p ≤ x prime : p ≡ a (mod q)}`. -/
theorem brun_titchmarsh_ap (q a : ℕ) (hq : 1 ≤ q) (x : ℝ) (hx : (q : ℝ) < x) :
    (((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ) ≤
      2008 * x / ((q.totient : ℝ) * Real.log (x / q)) := by
  have hq0 : 0 < q := hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hx1 : 1 < x := lt_of_le_of_lt hq1R hx
  have hy1 : 1 < x / q := by rw [one_lt_div hqR]; exact hx
  have hy0 : 0 ≤ x / q := by linarith
  have hz1 : 1 < Real.sqrt (x / q) := Real.lt_sqrt_of_sq_lt (by norm_num; linarith)
  have hz1' : 1 ≤ Real.sqrt (x / q) := hz1.le
  have hz0 : 0 ≤ Real.sqrt (x / q) := Real.sqrt_nonneg _
  have hmain := card_primes_le q a ⌊x⌋₊ (Real.sqrt (x / q)) hz1'
  have hsift := siftedSum_le q a ⌊x⌋₊ (Real.sqrt (x / q)) hz1' hq0 hz1
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hL : 0 < Real.log (x / q) := Real.log_pos hy1
  have hlogz : Real.log (Real.sqrt (x / q)) = Real.log (x / q) / 2 := Real.log_sqrt hy0
  have hlogsz : Real.log (Real.sqrt (Real.sqrt (x / q))) = Real.log (x / q) / 4 := by
    rw [Real.log_sqrt hz0, hlogz]
    ring
  have hzy : Real.sqrt (x / q) ^ 2 = x / q := Real.sq_sqrt hy0
  have hNx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
  -- the main term, multiplied out
  have ht1 : (((⌊x⌋₊ : ℝ) + 1) / q) / ((q.totient : ℝ) / q *
      Real.log (Real.sqrt (Real.sqrt (x / q)))) * ((q.totient : ℝ) * Real.log (x / q))
      = 4 * ((⌊x⌋₊ : ℝ) + 1) := by
    have hq' : (q : ℝ) ≠ 0 := hqR.ne'
    have hφ' : (q.totient : ℝ) ≠ 0 := hφ.ne'
    have hL' : Real.log (x / q) ≠ 0 := hL.ne'
    rw [hlogsz]
    field_simp
  -- the remainder and the unsifted small primes, multiplied out
  have hpoly := log_poly_bound (Real.sqrt (x / q)) hz1'
  have hfl : ((⌊Real.sqrt (x / q)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (x / q) := Nat.floor_le hz0
  have hlz0 : 0 ≤ Real.log (Real.sqrt (x / q)) := Real.log_nonneg hz1'
  have hone : 1 ≤ (1 + Real.log (Real.sqrt (x / q))) ^ 3 := one_le_pow₀ (by linarith)
  have hzle : Real.sqrt (x / q) ≤ Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 :=
    le_mul_of_one_le_right hz0 hone
  have ht2 : (Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 +
      ((⌊Real.sqrt (x / q)⌋₊ : ℕ) : ℝ)) * ((q.totient : ℝ) * Real.log (x / q)) ≤ 2000 * x := by
    have h2 : Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 +
        ((⌊Real.sqrt (x / q)⌋₊ : ℕ) : ℝ) ≤
          2 * Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 := by linarith
    have hA : 0 ≤ 2 * Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 := by
      positivity
    have hLz : Real.log (x / q) = 2 * Real.log (Real.sqrt (x / q)) := by linarith
    calc (Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 +
          ((⌊Real.sqrt (x / q)⌋₊ : ℕ) : ℝ)) * ((q.totient : ℝ) * Real.log (x / q))
        ≤ (2 * Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3) *
            ((q : ℝ) * Real.log (x / q)) :=
          mul_le_mul h2 (mul_le_mul_of_nonneg_right hφq hL.le) (by positivity) hA
      _ = Real.sqrt (x / q) * (4 * (1 + Real.log (Real.sqrt (x / q))) ^ 3 *
            Real.log (Real.sqrt (x / q))) * q := by
          rw [hLz]
          ring
      _ ≤ Real.sqrt (x / q) * (2000 * Real.sqrt (x / q)) * q :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hz0) hqR.le
      _ = 2000 * (Real.sqrt (x / q) ^ 2 * q) := by ring
      _ = 2000 * x := by
          rw [hzy, div_mul_cancel₀ x hqR.ne']
  have hπ : (((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ) ≤
      (((⌊x⌋₊ : ℝ) + 1) / q) / ((q.totient : ℝ) / q *
        Real.log (Real.sqrt (Real.sqrt (x / q)))) +
      (Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 +
        ((⌊Real.sqrt (x / q)⌋₊ : ℕ) : ℝ)) := by
    linarith
  rw [le_div_iff₀ (mul_pos hφ hL)]
  have hφL : 0 ≤ (q.totient : ℝ) * Real.log (x / q) := (mul_pos hφ hL).le
  calc (((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ) *
        ((q.totient : ℝ) * Real.log (x / q))
      ≤ ((((⌊x⌋₊ : ℝ) + 1) / q) / ((q.totient : ℝ) / q *
          Real.log (Real.sqrt (Real.sqrt (x / q)))) +
        (Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 +
          ((⌊Real.sqrt (x / q)⌋₊ : ℕ) : ℝ))) * ((q.totient : ℝ) * Real.log (x / q)) :=
        mul_le_mul_of_nonneg_right hπ hφL
    _ = (((⌊x⌋₊ : ℝ) + 1) / q) / ((q.totient : ℝ) / q *
          Real.log (Real.sqrt (Real.sqrt (x / q)))) * ((q.totient : ℝ) * Real.log (x / q)) +
        (Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 +
          ((⌊Real.sqrt (x / q)⌋₊ : ℕ) : ℝ)) * ((q.totient : ℝ) * Real.log (x / q)) := by ring
    _ ≤ 4 * ((⌊x⌋₊ : ℝ) + 1) + 2000 * x := by
        rw [ht1]
        linarith
    _ ≤ 2008 * x := by linarith

end Principia.Common.BrunTitchmarshAP

end

end BrunTitchmarshAP

/- ### Part `TwoDim` -/

section TwoDim
set_option autoImplicit false

/-
# The two-dimensional upper-bound sieve (Halberstam–Richert, Theorem 2.2 for two forms)

For coprime `a₁, a₂ ≥ 1` and `D = a₁ b₂ − a₂ b₁ ≠ 0`, every `u ∈ ℤ` and every real `T ≥ 2`,
`#{t ∈ [u, u + ⌊T⌋] : a₁ t + b₁ and a₂ t + b₂ both prime}
  ≤ 2^28 · T/(log T)^2 · a₁/φ(a₁) · a₂/φ(a₂) · |D|/φ(|D|)`
(`Principia.Common.TwoDimSieve.two_dim_sieve`). The constant is not optimised.

## Route (Selberg's Λ² sieve, from the PNT+ port in this directory)

* **Degenerate forms.** If `gcd(aᵢ, bᵢ) > 1`, the form `aᵢ t + bᵢ` takes at most one prime value
  (`card_prime_values_le_one`). Otherwise every prime `p` has `ρ(p) ∈ {1, 2}` roots of
  `F(t) = (a₁ t + b₁)(a₂ t + b₂)` modulo `p`: `ρ(p) = 1` if `p ∣ E = a₁ a₂ |D|`, else `2`
  (`rc_prime`, computed in the field `ZMod p`; `gcd(a₁, a₂) = 1` rules out `ρ(p) = 0`).
* **The sieve** `twoSieve`: the values `|F(t)|`, `t ∈ [u, u + L]`, weighted by multiplicity, sifted
  by the odd primes `p ≤ z`, with the completely multiplicative density `ν(p) = ρ(p)/p < 1` and
  total mass `L + 1`.
* **Remainders.** For squarefree `d ∣ P` the root count `ρ(d)` is multiplicative (Chinese
  remainder theorem, `rc_mul`), the multiples of `d` among the `F(t)` are `ρ(d)` residue classes
  of `t`, each of size `(L+1)/d + O(1)`, so `|R_d| ≤ ρ(d) ≤ 2^{ω(d)}` (`abs_rem_le`) and the Selberg
  error is `≤ z (1 + log z)^6` (`errSum_le`).
* **Main term.** `Sieve.selbergBoundingSum_ge_sum_div_filter` bounds the Selberg sum below by
  `∑_{m ≤ √z odd} ν(m)`; every pair `a, b ≤ z^{1/4}` with `a` odd and `b` prime to `2E` has
  `ab` in that range, and a divisor count (`card_divisors_avoid_le`) gives
  `∑ ν(m) ≥ (∑ 1/a)(∑ 1/b) ≥ (½ log z^{1/4}) (φ(2E)/(2E)) log z^{1/4}` (`boundingSum_ge`). This is
  the singular series to the **first** power; excluding the primes of `E` from the sieve instead
  would square it.
* **Parameters.** `z = √T` (`count_le_nondeg`, `err_bound`, `two_disc_le`, `two_dim_sieve`).
-/

noncomputable section

open scoped ArithmeticFunction ArithmeticFunction.omega
open BoundingSieve SelbergSieve

namespace Principia.Common.TwoDimSieve

/- ## Completely multiplicative functions from prime values -/

/-- The completely multiplicative function with value `c p` at each prime `p`:
`n ↦ ∏_{p^e ∥ n} c(p)^e`, and `0 ↦ 0`. -/
def cmOf (c : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod (fun p e => c p ^ e), by simp⟩

theorem cmOf_apply (c : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    cmOf c n = n.factorization.prod (fun p e => c p ^ e) := by
  change (if n = 0 then (0 : ℝ) else _) = _
  rw [if_neg hn]

theorem cmOf_zero (c : ℕ → ℝ) : cmOf c 0 = 0 :=
  ArithmeticFunction.map_zero

theorem cmOf_cm (c : ℕ → ℝ) : Sieve.CompletelyMultiplicative (cmOf c) := by
  constructor
  · rw [cmOf_apply c one_ne_zero, Nat.factorization_one, Finsupp.prod_zero_index]
  · intro a b
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      rw [zero_mul, cmOf_zero, zero_mul]
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      rw [mul_zero, cmOf_zero, mul_zero]
    rw [cmOf_apply c (Nat.mul_ne_zero ha.ne' hb.ne'), cmOf_apply c ha.ne', cmOf_apply c hb.ne',
      Nat.factorization_mul ha.ne' hb.ne']
    exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem cmOf_prime (c : ℕ → ℝ) {p : ℕ} (hp : p.Prime) : cmOf c p = c p := by
  rw [cmOf_apply c hp.ne_zero, hp.factorization,
    Finsupp.prod_single_index (h := fun p e => c p ^ e) (pow_zero (c p))]
  exact pow_one (c p)

theorem cmOf_squarefree (c : ℕ → ℝ) {d : ℕ} (hd : Squarefree d) :
    cmOf c d = ∏ p ∈ d.primeFactors, c p := by
  rw [← ArithmeticFunction.IsMultiplicative.prod_factors_of_mult (cmOf c)
    (cmOf_cm c).isMultiplicative hd]
  exact Finset.prod_congr rfl (fun p hp => cmOf_prime c (Nat.prime_of_mem_primeFactors hp))

theorem cmOf_nonneg (c : ℕ → ℝ) (hc : ∀ p, 0 ≤ c p) (n : ℕ) : 0 ≤ cmOf c n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn, cmOf_zero]
  · rw [cmOf_apply c hn.ne']
    unfold Finsupp.prod
    exact Finset.prod_nonneg (fun p _ => pow_nonneg (hc p) _)

/- ## The two linear forms and their local root counts -/

section Forms

variable (a₁ a₂ : ℕ) (b₁ b₂ : ℤ)

/-- The determinant `a₁ b₂ − a₂ b₁` of the two forms `a₁ t + b₁`, `a₂ t + b₂`. -/
def det : ℤ := (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁

/-- `E = a₁ a₂ |D|`. -/
def disc : ℕ := a₁ * a₂ * (det a₁ a₂ b₁ b₂).natAbs

/-- The local root count of `(a₁ t + b₁)(a₂ t + b₂)`: `1` at primes dividing `E`, `2` elsewhere
(under the non-degeneracy hypotheses of `rc_prime`). -/
def rho (p : ℕ) : ℝ := if p ∣ disc a₁ a₂ b₁ b₂ then 1 else 2

/-- The product of the two forms. -/
def F (t : ℤ) : ℤ := ((a₁ : ℤ) * t + b₁) * ((a₂ : ℤ) * t + b₂)

/-- The product of the two forms over `ZMod d`. -/
def Fz (d : ℕ) (r : ZMod d) : ZMod d :=
  ((a₁ : ZMod d) * r + (b₁ : ZMod d)) * ((a₂ : ZMod d) * r + (b₂ : ZMod d))

/-- The number of roots of the product of the two forms modulo `d`. -/
def rc (d : ℕ) : ℕ := Nat.card {r : ZMod d // Fz a₁ a₂ b₁ b₂ d r = 0}

theorem one_le_rho (p : ℕ) : 1 ≤ rho a₁ a₂ b₁ b₂ p := by
  unfold rho
  split_ifs <;> norm_num

theorem rho_le_two (p : ℕ) : rho a₁ a₂ b₁ b₂ p ≤ 2 := by
  unfold rho
  split_ifs <;> norm_num

theorem rho_nonneg (p : ℕ) : 0 ≤ rho a₁ a₂ b₁ b₂ p :=
  le_trans zero_le_one (one_le_rho a₁ a₂ b₁ b₂ p)

theorem lin_root {K : Type*} [Field K] {α β r : K} (hα : α ≠ 0) :
    α * r + β = 0 ↔ r = -β / α := by
  rw [eq_div_iff hα, add_eq_zero_iff_eq_neg, mul_comm]

theorem not_dvd_of_coprime {p a b : ℕ} (hp : p.Prime) (hab : Nat.Coprime a b) (ha : p ∣ a) :
    ¬ p ∣ b := by
  intro hb
  have h := Nat.dvd_gcd ha hb
  rw [hab.gcd_eq_one] at h
  exact hp.not_dvd_one h

/-- The root count at a prime. -/
theorem rc_prime (hcop : Nat.Coprime a₁ a₂) (hg₁ : Nat.Coprime a₁ b₁.natAbs)
    (hg₂ : Nat.Coprime a₂ b₂.natAbs) {p : ℕ} (hp : p.Prime) :
    (rc a₁ a₂ b₁ b₂ p : ℝ) = rho a₁ a₂ b₁ b₂ p := by
  have := Fact.mk hp
  classical
  have hcard : rc a₁ a₂ b₁ b₂ p =
      (Finset.univ.filter (fun r : ZMod p => Fz a₁ a₂ b₁ b₂ p r = 0)).card := by
    unfold rc
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hA : ∀ a : ℕ, (a : ZMod p) = 0 ↔ p ∣ a := fun a => ZMod.natCast_eq_zero_iff a p
  have hB : ∀ b : ℤ, (b : ZMod p) = 0 ↔ p ∣ b.natAbs := fun b => by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd]
  have hdet : ((a₁ : ZMod p) * b₂ - (a₂ : ZMod p) * b₁) = ((det a₁ a₂ b₁ b₂ : ℤ) : ZMod p) := by
    unfold det
    push_cast
    ring
  have hE : p ∣ disc a₁ a₂ b₁ b₂ ↔ p ∣ a₁ ∨ p ∣ a₂ ∨ p ∣ (det a₁ a₂ b₁ b₂).natAbs := by
    unfold disc
    rw [hp.dvd_mul, hp.dvd_mul, or_assoc]
  rw [hcard]
  unfold rho
  by_cases h1 : p ∣ a₁
  · have h2 : ¬ p ∣ a₂ := not_dvd_of_coprime hp hcop h1
    have hb1 : ¬ p ∣ b₁.natAbs := not_dvd_of_coprime hp hg₁ h1
    have hα₂ : (a₂ : ZMod p) ≠ 0 := fun h => h2 ((hA a₂).mp h)
    have hβ₁ : (b₁ : ZMod p) ≠ 0 := fun h => hb1 ((hB b₁).mp h)
    have hset : Finset.univ.filter (fun r : ZMod p => Fz a₁ a₂ b₁ b₂ p r = 0) =
        {-(b₂ : ZMod p) / (a₂ : ZMod p)} := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fz,
        mul_eq_zero]
      rw [(hA a₁).mpr h1, zero_mul, zero_add, lin_root hα₂]
      constructor
      · rintro (h | h)
        · exact absurd h hβ₁
        · exact h
      · intro h
        exact Or.inr h
    rw [hset, Finset.card_singleton, if_pos (hE.mpr (Or.inl h1))]
    norm_num
  · by_cases h2 : p ∣ a₂
    · have hb2 : ¬ p ∣ b₂.natAbs := not_dvd_of_coprime hp hg₂ h2
      have hα₁ : (a₁ : ZMod p) ≠ 0 := fun h => h1 ((hA a₁).mp h)
      have hβ₂ : (b₂ : ZMod p) ≠ 0 := fun h => hb2 ((hB b₂).mp h)
      have hset : Finset.univ.filter (fun r : ZMod p => Fz a₁ a₂ b₁ b₂ p r = 0) =
          {-(b₁ : ZMod p) / (a₁ : ZMod p)} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fz,
          mul_eq_zero]
        rw [(hA a₂).mpr h2, zero_mul, zero_add, lin_root hα₁]
        constructor
        · rintro (h | h)
          · exact h
          · exact absurd h hβ₂
        · intro h
          exact Or.inl h
      rw [hset, Finset.card_singleton, if_pos (hE.mpr (Or.inr (Or.inl h2)))]
      norm_num
    · have hα₁ : (a₁ : ZMod p) ≠ 0 := fun h => h1 ((hA a₁).mp h)
      have hα₂ : (a₂ : ZMod p) ≠ 0 := fun h => h2 ((hA a₂).mp h)
      have hset : Finset.univ.filter (fun r : ZMod p => Fz a₁ a₂ b₁ b₂ p r = 0) =
          {-(b₁ : ZMod p) / (a₁ : ZMod p), -(b₂ : ZMod p) / (a₂ : ZMod p)} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Fz, mul_eq_zero]
        rw [lin_root hα₁, lin_root hα₂]
      have hroots : -(b₁ : ZMod p) / (a₁ : ZMod p) = -(b₂ : ZMod p) / (a₂ : ZMod p) ↔
          p ∣ (det a₁ a₂ b₁ b₂).natAbs := by
        rw [← hB, ← hdet, div_eq_div_iff hα₁ hα₂]
        constructor
        · intro h
          linear_combination h
        · intro h
          linear_combination h
      rw [hset]
      by_cases h3 : p ∣ (det a₁ a₂ b₁ b₂).natAbs
      · rw [(hroots.mpr h3), Finset.insert_eq_of_mem (Finset.mem_singleton_self _),
          Finset.card_singleton, if_pos (hE.mpr (Or.inr (Or.inr h3)))]
        norm_num
      · have hne : -(b₁ : ZMod p) / (a₁ : ZMod p) ≠ -(b₂ : ZMod p) / (a₂ : ZMod p) :=
          fun h => h3 (hroots.mp h)
        have hnE : ¬ p ∣ disc a₁ a₂ b₁ b₂ := by
          rw [hE]
          rintro (h | h | h)
          · exact h1 h
          · exact h2 h
          · exact h3 h
        rw [Finset.card_pair hne, if_neg hnE]
        norm_num

/-- The root count is multiplicative (Chinese remainder theorem). -/
theorem rc_mul {m n : ℕ} (h : Nat.Coprime m n) :
    rc a₁ a₂ b₁ b₂ (m * n) = rc a₁ a₂ b₁ b₂ m * rc a₁ a₂ b₁ b₂ n := by
  unfold rc
  rw [← Nat.card_prod]
  apply Nat.card_congr
  let e := ZMod.chineseRemainder h
  have key : ∀ r : ZMod (m * n), e (Fz a₁ a₂ b₁ b₂ (m * n) r) =
      (Fz a₁ a₂ b₁ b₂ m (e r).1, Fz a₁ a₂ b₁ b₂ n (e r).2) := by
    intro r
    ext <;> simp [Fz]
  have hiff : ∀ r : ZMod (m * n), Fz a₁ a₂ b₁ b₂ (m * n) r = 0 ↔
      (Fz a₁ a₂ b₁ b₂ m (e.toEquiv r).1 = 0 ∧ Fz a₁ a₂ b₁ b₂ n (e.toEquiv r).2 = 0) := by
    intro r
    rw [← map_eq_zero_iff e e.injective, key, Prod.ext_iff]
    rfl
  exact (e.toEquiv.subtypeEquiv hiff).trans Equiv.subtypeProdEquivProd

/-- The root count on a product of distinct primes. -/
theorem rc_prod_primes (hcop : Nat.Coprime a₁ a₂) (hg₁ : Nat.Coprime a₁ b₁.natAbs)
    (hg₂ : Nat.Coprime a₂ b₂.natAbs) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (rc a₁ a₂ b₁ b₂ (∏ p ∈ S, p) : ℝ) = ∏ p ∈ S, rho a₁ a₂ b₁ b₂ p := by
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty]
    have : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
    have h1 : rc a₁ a₂ b₁ b₂ 1 = 1 := by
      unfold rc
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩,
        ⟨⟨0, Subsingleton.elim _ _⟩⟩⟩
    rw [h1, Nat.cast_one]
  | insert q S hq ih =>
    have hqp : q.Prime := hS q (Finset.mem_insert_self q S)
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hcopq : Nat.Coprime q (∏ p ∈ S, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      exact (Nat.coprime_primes hqp (hS' p hp)).mpr (fun h => hq (h ▸ hp))
    rw [Finset.prod_insert hq, Finset.prod_insert hq, rc_mul a₁ a₂ b₁ b₂ hcopq, Nat.cast_mul,
      rc_prime a₁ a₂ b₁ b₂ hcop hg₁ hg₂ hqp, ih hS']

/-- The root count at a squarefree modulus is `κ(d) = ∏_{p ∣ d} ρ(p)`. -/
theorem rc_squarefree (hcop : Nat.Coprime a₁ a₂) (hg₁ : Nat.Coprime a₁ b₁.natAbs)
    (hg₂ : Nat.Coprime a₂ b₂.natAbs) {d : ℕ} (hd : Squarefree d) :
    (rc a₁ a₂ b₁ b₂ d : ℝ) = cmOf (rho a₁ a₂ b₁ b₂) d := by
  rw [cmOf_squarefree _ hd]
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
  exact rc_prod_primes a₁ a₂ b₁ b₂ hcop hg₁ hg₂ d.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp)

end Forms

/- ## Counting an interval in a residue class -/

theorem natCast_zmod_eq_iff {d : ℕ} [NeZero d] (k : ℕ) (s : ZMod d) :
    (k : ZMod d) = s ↔ k ≡ s.val [MOD d] := by
  conv_lhs => rw [← ZMod.natCast_zmod_val s]
  exact ZMod.natCast_eq_natCast_iff k s.val d

/-- The class `r (mod d)` has `⌊(L+1)/d⌋` or `⌊(L+1)/d⌋ + 1` elements in `[u, u + L]`. -/
theorem card_Icc_filter_zmod (u : ℤ) (L d : ℕ) [NeZero d] (r : ZMod d) :
    ∃ e : ℕ, e ≤ 1 ∧
      ((Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ => (t : ZMod d) = r)).card =
        (L + 1) / d + e := by
  have hbij : ((Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ => (t : ZMod d) = r)).card =
      ((Finset.range (L + 1)).filter (fun k => k ≡ (r - (u : ZMod d)).val [MOD d])).card := by
    apply Finset.card_nbij' (fun t : ℤ => (t - u).toNat) (fun k : ℕ => u + (k : ℤ))
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ht
      obtain ⟨⟨h1, h2⟩, h3⟩ := ht
      have hcast : (((t - u).toNat : ℕ) : ℤ) = t - u := Int.toNat_of_nonneg (by omega)
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      rw [← natCast_zmod_eq_iff]
      refine ⟨by omega, ?_⟩
      rw [← Int.cast_natCast, hcast, Int.cast_sub, h3]
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hk1, hk2⟩ := hk
      rw [← natCast_zmod_eq_iff] at hk2
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [Int.cast_add, Int.cast_natCast, hk2]
      ring
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ht
      obtain ⟨⟨h1, _⟩, _⟩ := ht
      have h0 : 0 ≤ t - u := by omega
      change u + (((t - u).toNat : ℕ) : ℤ) = t
      rw [Int.toNat_of_nonneg h0]
      ring
    · intro k _
      change ((u + (k : ℤ)) - u).toNat = k
      simp
  rw [hbij, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ (NeZero.pos d)]
  refine ⟨_, ?_, rfl⟩
  split_ifs <;> norm_num

/-- Counting a finset through the fibres of a map into `ℕ`. -/
theorem sum_image_ite_card (s : Finset ℤ) (f : ℤ → ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    ∑ n ∈ s.image f, (if Q n then (((s.filter (fun t => f t = n)).card : ℕ) : ℝ) else 0) =
      (((s.filter (fun t => Q (f t))).card : ℕ) : ℝ) := by
  have hfib := Finset.card_eq_sum_card_fiberwise (f := f) (s := s.filter (fun t => Q (f t)))
    (t := s.image f) (fun t ht => Finset.mem_coe.mpr
      (Finset.mem_image_of_mem f (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).1))
  rw [hfib]
  push_cast
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.filter_filter]
  split_ifs with hQ
  · have hset : s.filter (fun t => Q (f t) ∧ f t = n) = s.filter (fun t => f t = n) := by
      apply Finset.filter_congr
      intro t _
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rw [h]
        exact hQ
    rw [hset]
  · have hset : s.filter (fun t => Q (f t) ∧ f t = n) = ∅ := by
      apply Finset.filter_false_of_mem
      intro t _ h
      apply hQ
      rw [← h.2]
      exact h.1
    rw [hset, Finset.card_empty, Nat.cast_zero]

/- ## The sieve -/

section TheSieve

variable (a₁ a₂ : ℕ) (b₁ b₂ : ℤ)

/-- The sifting density `ν(n) = κ(n)/n`, with `κ` completely multiplicative, `κ(p) = ρ(p)`. -/
def nu : ArithmeticFunction ℝ := (cmOf (rho a₁ a₂ b₁ b₂)).pdiv .id

theorem nu_cm : Sieve.CompletelyMultiplicative (nu a₁ a₂ b₁ b₂) :=
  Sieve.CompletelyMultiplicative.pdiv (cmOf_cm _) Sieve.CompletelyMultiplicative.id

theorem nu_apply (n : ℕ) : nu a₁ a₂ b₁ b₂ n = cmOf (rho a₁ a₂ b₁ b₂) n / n := by
  unfold nu
  simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.id_apply]

theorem nu_prime {p : ℕ} (hp : p.Prime) : nu a₁ a₂ b₁ b₂ p = rho a₁ a₂ b₁ b₂ p / p := by
  rw [nu_apply, cmOf_prime _ hp]

theorem nu_nonneg (n : ℕ) : 0 ≤ nu a₁ a₂ b₁ b₂ n := by
  rw [nu_apply]
  exact div_nonneg (cmOf_nonneg _ (rho_nonneg a₁ a₂ b₁ b₂) n) (Nat.cast_nonneg n)

theorem nu_pos_of_prime' {p : ℕ} (hp : p.Prime) : 0 < nu a₁ a₂ b₁ b₂ p := by
  rw [nu_prime a₁ a₂ b₁ b₂ hp]
  exact div_pos (lt_of_lt_of_le zero_lt_one (one_le_rho a₁ a₂ b₁ b₂ p))
    (by exact_mod_cast hp.pos)

theorem nu_lt_one_of_odd {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : nu a₁ a₂ b₁ b₂ p < 1 := by
  rw [nu_prime a₁ a₂ b₁ b₂ hp]
  have h3' : 3 ≤ p := lt_of_le_of_ne hp.two_le (Ne.symm h2)
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast h3'
  rw [div_lt_one (by linarith)]
  linarith [rho_le_two a₁ a₂ b₁ b₂ p]

/-- The sifting primes: the odd primes `p ≤ z`. -/
def oddPrimes (z : ℝ) : Finset ℕ :=
  (Finset.range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

theorem oddPrimes_squarefree (z : ℝ) : Squarefree (∏ p ∈ oddPrimes z, p) :=
  Sieve.prodDistinctPrimes_squarefree _ (fun _ hp => (Finset.mem_filter.mp hp).2.1)

theorem prime_dvd_prod_oddPrimes_iff (z : ℝ) {p : ℕ} (hp : p.Prime) :
    p ∣ ∏ q ∈ oddPrimes z, q ↔ p ≤ ⌊z⌋₊ ∧ p ≠ 2 := by
  constructor
  · intro h
    obtain ⟨i, hi, hpi⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd h
    rw [oddPrimes, Finset.mem_filter, Finset.mem_range] at hi
    have hpi' : p = i := (Nat.prime_dvd_prime_iff_eq hp hi.2.1).mp hpi
    rw [← hpi'] at hi
    exact ⟨Nat.lt_succ_iff.mp hi.1, hi.2.2⟩
  · rintro ⟨h1, h2⟩
    exact Finset.dvd_prod_of_mem (fun q => q)
      (by rw [oddPrimes, Finset.mem_filter, Finset.mem_range]
          exact ⟨Nat.lt_succ_of_le h1, hp, h2⟩)

/-- The two-dimensional sieve: the values `|F(t)|` for `t ∈ [u, u + L]` (weighted by
multiplicity), sifted by the odd primes `p ≤ z`, with density `ν` and total mass `L + 1`. -/
def twoSieve (u : ℤ) (L : ℕ) (z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := (Finset.Icc u (u + (L : ℤ))).image (fun t => (F a₁ a₂ b₁ b₂ t).natAbs)
  prodPrimes := ∏ p ∈ oddPrimes z, p
  prodPrimes_squarefree := oddPrimes_squarefree z
  weights := fun n =>
    (((Finset.Icc u (u + (L : ℤ))).filter (fun t => (F a₁ a₂ b₁ b₂ t).natAbs = n)).card : ℝ)
  weights_nonneg := fun _ => Nat.cast_nonneg _
  totalMass := (L : ℝ) + 1
  nu := nu a₁ a₂ b₁ b₂
  nu_mult := (nu_cm a₁ a₂ b₁ b₂).isMultiplicative
  nu_pos_of_prime := fun _ hp _ => nu_pos_of_prime' a₁ a₂ b₁ b₂ hp
  nu_lt_one_of_prime := fun _ hp hpP =>
    nu_lt_one_of_odd a₁ a₂ b₁ b₂ hp ((prime_dvd_prod_oddPrimes_iff z hp).mp hpP).2
  level := z
  one_le_level := hz

theorem multSum_eq (u : ℤ) (L : ℕ) (z : ℝ) (hz : 1 ≤ z) (d : ℕ) :
    multSum (s := (twoSieve a₁ a₂ b₁ b₂ u L z hz).toBoundingSieve) d =
      ((((Finset.Icc u (u + (L : ℤ))).filter
        (fun t => d ∣ (F a₁ a₂ b₁ b₂ t).natAbs)).card : ℕ) : ℝ) := by
  change (∑ n ∈ (Finset.Icc u (u + (L : ℤ))).image (fun t => (F a₁ a₂ b₁ b₂ t).natAbs),
      if d ∣ n then ((((Finset.Icc u (u + (L : ℤ))).filter
        (fun t => (F a₁ a₂ b₁ b₂ t).natAbs = n)).card : ℕ) : ℝ) else 0) = _
  exact sum_image_ite_card _ _ (fun n => d ∣ n)

theorem siftedSum_eq (u : ℤ) (L : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    siftedSum (s := (twoSieve a₁ a₂ b₁ b₂ u L z hz).toBoundingSieve) =
      ((((Finset.Icc u (u + (L : ℤ))).filter
        (fun t => Nat.Coprime (∏ p ∈ oddPrimes z, p) (F a₁ a₂ b₁ b₂ t).natAbs)).card : ℕ)
          : ℝ) := by
  change (∑ n ∈ (Finset.Icc u (u + (L : ℤ))).image (fun t => (F a₁ a₂ b₁ b₂ t).natAbs),
      if Nat.Coprime (∏ p ∈ oddPrimes z, p) n then ((((Finset.Icc u (u + (L : ℤ))).filter
        (fun t => (F a₁ a₂ b₁ b₂ t).natAbs = n)).card : ℕ) : ℝ) else 0) = _
  exact sum_image_ite_card _ _ (fun n => Nat.Coprime (∏ p ∈ oddPrimes z, p) n)

theorem kappa_le_two_pow {d : ℕ} (hd : Squarefree d) :
    cmOf (rho a₁ a₂ b₁ b₂) d ≤ (2 : ℝ) ^ ω d := by
  rw [cmOf_squarefree _ hd, ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
    Nat.toFinset_factors, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun p _ => rho_nonneg a₁ a₂ b₁ b₂ p)
    (fun p _ => rho_le_two a₁ a₂ b₁ b₂ p)

/-- The sieve remainders: `|R_d| ≤ κ(d)`, the number of root classes modulo `d`. -/
theorem abs_rem_le (hcop : Nat.Coprime a₁ a₂) (hg₁ : Nat.Coprime a₁ b₁.natAbs)
    (hg₂ : Nat.Coprime a₂ b₂.natAbs) (u : ℤ) (L : ℕ) (z : ℝ) (hz : 1 ≤ z) {d : ℕ}
    (hd : d ∣ ∏ p ∈ oddPrimes z, p) :
    |rem (s := (twoSieve a₁ a₂ b₁ b₂ u L z hz).toBoundingSieve) d| ≤
      cmOf (rho a₁ a₂ b₁ b₂) d := by
  classical
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (oddPrimes_squarefree z).ne_zero hd
  have : NeZero d := ⟨hd0⟩
  have hsq : Squarefree d := (oddPrimes_squarefree z).squarefree_of_dvd hd
  have hRcard : (((Finset.univ.filter (fun r : ZMod d => Fz a₁ a₂ b₁ b₂ d r = 0)).card : ℕ)
      : ℝ) = cmOf (rho a₁ a₂ b₁ b₂) d := by
    rw [← rc_squarefree a₁ a₂ b₁ b₂ hcop hg₁ hg₂ hsq]
    unfold rc
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcastF : ∀ t : ℤ, ((F a₁ a₂ b₁ b₂ t : ℤ) : ZMod d) = Fz a₁ a₂ b₁ b₂ d (t : ZMod d) := by
    intro t
    simp only [F, Fz, Int.cast_mul, Int.cast_add, Int.cast_natCast]
  have hmem : ∀ t : ℤ, d ∣ (F a₁ a₂ b₁ b₂ t).natAbs ↔ Fz a₁ a₂ b₁ b₂ d (t : ZMod d) = 0 := by
    intro t
    rw [← Int.natCast_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hcastF]
  have hdecomp : ((Finset.Icc u (u + (L : ℤ))).filter
      (fun t => d ∣ (F a₁ a₂ b₁ b₂ t).natAbs)).card =
      ∑ r ∈ Finset.univ.filter (fun r : ZMod d => Fz a₁ a₂ b₁ b₂ d r = 0),
        ((Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ => (t : ZMod d) = r)).card := by
    have hmaps : ∀ t ∈ (Finset.Icc u (u + (L : ℤ))).filter
        (fun t => d ∣ (F a₁ a₂ b₁ b₂ t).natAbs),
        (t : ZMod d) ∈ Finset.univ.filter (fun r : ZMod d => Fz a₁ a₂ b₁ b₂ d r = 0) := by
      intro t ht
      rw [Finset.mem_filter] at ht
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (hmem t).mp ht.2⟩
    have hfib := Finset.card_eq_sum_card_fiberwise (f := fun t : ℤ => (t : ZMod d))
      (s := (Finset.Icc u (u + (L : ℤ))).filter (fun t => d ∣ (F a₁ a₂ b₁ b₂ t).natAbs))
      (t := Finset.univ.filter (fun r : ZMod d => Fz a₁ a₂ b₁ b₂ d r = 0))
      (fun t ht => Finset.mem_coe.mpr (hmaps t (Finset.mem_coe.mp ht)))
    rw [hfib]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro t _
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [hmem, h]
      exact (Finset.mem_filter.mp hr).2
  have hnu : (twoSieve a₁ a₂ b₁ b₂ u L z hz).nu d * (twoSieve a₁ a₂ b₁ b₂ u L z hz).totalMass =
      ∑ r ∈ Finset.univ.filter (fun r : ZMod d => Fz a₁ a₂ b₁ b₂ d r = 0),
        (((L : ℝ) + 1) / d) := by
    change nu a₁ a₂ b₁ b₂ d * ((L : ℝ) + 1) = _
    rw [Finset.sum_const, nsmul_eq_mul, hRcard, nu_apply]
    ring
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have hbound : ∀ r : ZMod d,
      |((((Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ => (t : ZMod d) = r)).card : ℕ) : ℝ) -
        ((L : ℝ) + 1) / d| ≤ 1 := by
    intro r
    obtain ⟨e, he, hc⟩ := card_Icc_filter_zmod u L d r
    have hk1 : ((((L + 1) / d : ℕ)) : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / (d : ℝ) := Nat.cast_div_le
    have hk2 : ((L + 1 : ℕ) : ℝ) / (d : ℝ) < ((((L + 1) / d : ℕ)) : ℝ) + 1 := by
      rw [← Nat.floor_div_eq_div (K := ℝ) (L + 1) d]
      exact Nat.lt_floor_add_one _
    have he' : (e : ℝ) ≤ 1 := by exact_mod_cast he
    have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
    have hL1 : ((L + 1 : ℕ) : ℝ) = (L : ℝ) + 1 := by norm_num
    rw [hL1] at hk1 hk2
    rw [hc, Nat.cast_add, abs_le]
    constructor <;> linarith
  unfold rem
  rw [multSum_eq, hdecomp, hnu, Nat.cast_sum, ← Finset.sum_sub_distrib]
  calc |∑ r ∈ Finset.univ.filter (fun r : ZMod d => Fz a₁ a₂ b₁ b₂ d r = 0),
        (((((Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ => (t : ZMod d) = r)).card : ℕ)
          : ℝ) - ((L : ℝ) + 1) / d)|
      ≤ ∑ r ∈ Finset.univ.filter (fun r : ZMod d => Fz a₁ a₂ b₁ b₂ d r = 0), (1 : ℝ) :=
        le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun r _ => hbound r))
    _ = cmOf (rho a₁ a₂ b₁ b₂) d := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, hRcard]

/-- The Selberg error term: `∑_{d ∣ P, d ≤ z} 3^{ω(d)} |R_d| ≤ z (1 + log z)^6`. -/
theorem errSum_le (hcop : Nat.Coprime a₁ a₂) (hg₁ : Nat.Coprime a₁ b₁.natAbs)
    (hg₂ : Nat.Coprime a₂ b₂.natAbs) (u : ℤ) (L : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (∑ d ∈ (twoSieve a₁ a₂ b₁ b₂ u L z hz).prodPrimes.divisors,
      if (d : ℝ) ≤ (twoSieve a₁ a₂ b₁ b₂ u L z hz).level then
        (3 : ℝ) ^ ω d * |rem (s := (twoSieve a₁ a₂ b₁ b₂ u L z hz).toBoundingSieve) d|
      else 0) ≤ z * (1 + Real.log z) ^ 6 := by
  have h6 := Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow
    (P := ∏ p ∈ oddPrimes z, p) (h := 6) z hz (oddPrimes_squarefree z)
  change (∑ d ∈ (∏ p ∈ oddPrimes z, p).divisors,
      if (d : ℝ) ≤ z then
        (3 : ℝ) ^ ω d * |rem (s := (twoSieve a₁ a₂ b₁ b₂ u L z hz).toBoundingSieve) d|
      else 0) ≤ z * (1 + Real.log z) ^ 6
  refine le_trans (Finset.sum_le_sum ?_) h6
  intro d hd
  have hdP : d ∣ ∏ p ∈ oddPrimes z, p := Nat.dvd_of_mem_divisors hd
  split_ifs with hdz
  · have hsq : Squarefree d := (oddPrimes_squarefree z).squarefree_of_dvd hdP
    calc (3 : ℝ) ^ ω d * |rem (s := (twoSieve a₁ a₂ b₁ b₂ u L z hz).toBoundingSieve) d|
        ≤ (3 : ℝ) ^ ω d * (2 : ℝ) ^ ω d :=
          mul_le_mul_of_nonneg_left
            ((abs_rem_le a₁ a₂ b₁ b₂ hcop hg₁ hg₂ u L z hz hdP).trans
              (kappa_le_two_pow a₁ a₂ b₁ b₂ hsq)) (by positivity)
      _ = ((6 : ℕ) : ℝ) ^ ω d := by
          rw [← mul_pow]
          norm_num
  · exact le_refl 0

/- ## Values of a linear form that are small primes -/

theorem card_small_prime_values (a : ℕ) (b : ℤ) (ha : 0 < a) (s : Finset ℤ) (N : ℕ) :
    (s.filter (fun t => ((a : ℤ) * t + b).toNat.Prime ∧ ((a : ℤ) * t + b).toNat ≤ N)).card ≤
      N + 1 := by
  rw [← Finset.card_range (N + 1)]
  apply Finset.card_le_card_of_injOn (fun t => ((a : ℤ) * t + b).toNat)
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter] at ht
    simp only [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le ht.2.2
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
    have hx0 : 0 ≤ (a : ℤ) * x + b := by
      by_contra h
      push Not at h
      rw [Int.toNat_of_nonpos h.le] at hx
      exact Nat.not_prime_zero hx.2.1
    have hy0 : 0 ≤ (a : ℤ) * y + b := by
      by_contra h
      push Not at h
      rw [Int.toNat_of_nonpos h.le] at hy
      exact Nat.not_prime_zero hy.2.1
    have h1 : ((a : ℤ) * x + b).toNat = ((a : ℤ) * y + b).toNat := hxy
    have h2 : (((a : ℤ) * x + b).toNat : ℤ) = (((a : ℤ) * y + b).toNat : ℤ) := by rw [h1]
    rw [Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0] at h2
    have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
    exact mul_left_cancel₀ ha' (by linarith)

/-- A form `a t + b` with `gcd(a, b) > 1` takes at most one prime value. -/
theorem card_prime_values_le_one (a : ℕ) (b : ℤ) (ha : 0 < a) (h : ¬ Nat.Coprime a b.natAbs)
    (s : Finset ℤ) : (s.filter (fun t => ((a : ℤ) * t + b).toNat.Prime)).card ≤ 1 := by
  have key : ∀ t : ℤ, ((a : ℤ) * t + b).toNat.Prime →
      (a : ℤ) * t + b = ((Nat.gcd a b.natAbs : ℕ) : ℤ) := by
    intro t ht
    have hpos : 0 ≤ (a : ℤ) * t + b := by
      by_contra hneg
      push Not at hneg
      rw [Int.toNat_of_nonpos hneg.le] at ht
      exact Nat.not_prime_zero ht
    have hq : (((a : ℤ) * t + b).toNat : ℤ) = (a : ℤ) * t + b := Int.toNat_of_nonneg hpos
    have hg : Nat.gcd a b.natAbs ∣ ((a : ℤ) * t + b).toNat := by
      rw [← Int.natCast_dvd_natCast, hq]
      exact Dvd.dvd.add
        (Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)) t)
        (Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _))
    rcases Nat.Prime.eq_one_or_self_of_dvd ht _ hg with h1 | h1
    · exact absurd h1 h
    · rw [h1, hq]
  rw [Finset.card_le_one]
  intro x hx y hy
  rw [Finset.mem_filter] at hx hy
  have h1 := key x hx.2
  have h2 := key y hy.2
  have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  exact mul_left_cancel₀ ha' (by linarith)

/-- The prime pairs are sifted, or one of the two primes is at most `z`. -/
theorem card_prime_pairs_le_sifted (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (u : ℤ) (L : ℕ) (z : ℝ)
    (hz : 1 ≤ z) :
    ((((Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ =>
        ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime)).card : ℕ) : ℝ) ≤
      siftedSum (s := (twoSieve a₁ a₂ b₁ b₂ u L z hz).toBoundingSieve) +
        2 * ((⌊z⌋₊ : ℝ) + 1) := by
  classical
  rw [siftedSum_eq]
  have hcop1 : ∀ q : ℕ, q.Prime → ¬ q ≤ ⌊z⌋₊ → Nat.Coprime (∏ p ∈ oddPrimes z, p) q := by
    intro q hq hqz
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hq]
    intro hdvd
    exact hqz ((prime_dvd_prod_oddPrimes_iff z hq).mp hdvd).1
  have hnat : ∀ x : ℤ, x.toNat.Prime → x.natAbs = x.toNat := by
    intro x hx
    have hx0 : 0 ≤ x := by
      by_contra h
      push Not at h
      rw [Int.toNat_of_nonpos h.le] at hx
      exact Nat.not_prime_zero hx
    have e1 : (x.natAbs : ℤ) = x := Int.natAbs_of_nonneg hx0
    have e2 : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx0
    exact_mod_cast e1.trans e2.symm
  have hsub : (Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ =>
        ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime) ⊆
      ((Finset.Icc u (u + (L : ℤ))).filter
          (fun t => Nat.Coprime (∏ p ∈ oddPrimes z, p) (F a₁ a₂ b₁ b₂ t).natAbs) ∪
        (Finset.Icc u (u + (L : ℤ))).filter (fun t =>
          ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₁ : ℤ) * t + b₁).toNat ≤ ⌊z⌋₊)) ∪
        (Finset.Icc u (u + (L : ℤ))).filter (fun t =>
          ((a₂ : ℤ) * t + b₂).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat ≤ ⌊z⌋₊) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htI, hp1, hp2⟩ := ht
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_filter]
    by_cases h1 : ((a₁ : ℤ) * t + b₁).toNat ≤ ⌊z⌋₊
    · exact Or.inl (Or.inr ⟨htI, hp1, h1⟩)
    by_cases h2 : ((a₂ : ℤ) * t + b₂).toNat ≤ ⌊z⌋₊
    · exact Or.inr ⟨htI, hp2, h2⟩
    refine Or.inl (Or.inl ⟨htI, ?_⟩)
    unfold F
    rw [Int.natAbs_mul, hnat _ hp1, hnat _ hp2]
    exact Nat.Coprime.mul_right (hcop1 _ hp1 h1) (hcop1 _ hp2 h2)
  have hc1 := card_small_prime_values a₁ b₁ ha₁ (Finset.Icc u (u + (L : ℤ))) ⌊z⌋₊
  have hc2 := card_small_prime_values a₂ b₂ ha₂ (Finset.Icc u (u + (L : ℤ))) ⌊z⌋₊
  have hcard := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hnat' : ((Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ =>
        ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime)).card ≤
      ((Finset.Icc u (u + (L : ℤ))).filter
          (fun t => Nat.Coprime (∏ p ∈ oddPrimes z, p) (F a₁ a₂ b₁ b₂ t).natAbs)).card +
        (⌊z⌋₊ + 1) + (⌊z⌋₊ + 1) := by omega
  have hreal := (Nat.cast_le (α := ℝ)).mpr hnat'
  push_cast at hreal
  linarith

/- ## The main term: a lower bound for the Selberg bounding sum -/

/-- The divisors of `m` avoiding the primes of `Q` number at most `κ(m)`, when `κ ≥ 1` at every
prime and `κ ≥ 2` at primes outside `Q`. -/
theorem card_divisors_avoid_le (c : ℕ → ℝ) (Q : Finset ℕ) (hc0 : ∀ p, 0 ≤ c p)
    (hc1 : ∀ p, p.Prime → 1 ≤ c p) (hc2 : ∀ p, p.Prime → p ∉ Q → 2 ≤ c p) (m : ℕ) :
    (((m.divisors.filter (fun b => ∀ q ∈ Q, ¬ q ∣ b)).card : ℕ) : ℝ) ≤ cmOf c m := by
  induction m using Nat.recOnMul with
  | zero =>
    simp
  | one =>
    rw [(cmOf_cm c).1]
    have hsub : (Nat.divisors 1).filter (fun b => ∀ q ∈ Q, ¬ q ∣ b) ⊆ {1} := by
      rw [Nat.divisors_one]
      exact Finset.filter_subset _ _
    have h := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h
    exact_mod_cast h
  | prime p hp =>
    rw [cmOf_prime c hp]
    by_cases hpQ : p ∈ Q
    · have hsub : p.divisors.filter (fun b => ∀ q ∈ Q, ¬ q ∣ b) ⊆ {1} := by
        intro b hb
        rw [Finset.mem_filter, Nat.Prime.divisors hp, Finset.mem_insert,
          Finset.mem_singleton] at hb
        rcases hb.1 with h | h
        · rw [h]
          exact Finset.mem_singleton_self 1
        · exact (hb.2 p hpQ (dvd_of_eq h.symm)).elim
      have h := Finset.card_le_card hsub
      rw [Finset.card_singleton] at h
      calc ((((p.divisors.filter (fun b => ∀ q ∈ Q, ¬ q ∣ b)).card : ℕ) : ℝ)) ≤ 1 := by
            exact_mod_cast h
        _ ≤ c p := hc1 p hp
    · have h := Finset.card_filter_le p.divisors (fun b => ∀ q ∈ Q, ¬ q ∣ b)
      have h2 : p.divisors.card = 2 := by
        rw [Nat.Prime.divisors hp, Finset.card_pair hp.one_lt.ne]
      calc ((((p.divisors.filter (fun b => ∀ q ∈ Q, ¬ q ∣ b)).card : ℕ) : ℝ)) ≤ 2 := by
            exact_mod_cast h.trans h2.le
        _ ≤ c p := hc2 p hp hpQ
  | mul a b iha ihb =>
    rw [(cmOf_cm c).2]
    have hsub : ((a * b).divisors.filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)) ⊆
        ((a.divisors.filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)) ×ˢ
          (b.divisors.filter (fun n => ∀ q ∈ Q, ¬ q ∣ n))).image (fun x => x.1 * x.2) := by
      intro n hn
      rw [Finset.mem_filter, Nat.divisors_mul, Finset.mem_mul] at hn
      obtain ⟨⟨x, hx, y, hy, rfl⟩, hQ⟩ := hn
      rw [Finset.mem_image]
      refine ⟨(x, y), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hx, ?_⟩,
        Finset.mem_filter.mpr ⟨hy, ?_⟩⟩, rfl⟩
      · intro q hq hqx
        exact hQ q hq (Dvd.dvd.mul_right hqx y)
      · intro q hq hqy
        exact hQ q hq (Dvd.dvd.mul_left hqy x)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := (a.divisors.filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)) ×ˢ
          (b.divisors.filter (fun n => ∀ q ∈ Q, ¬ q ∣ n))) (f := fun x => x.1 * x.2)
    rw [Finset.card_product] at h2
    calc ((((a * b).divisors.filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).card : ℕ) : ℝ)
        ≤ ((((a.divisors.filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).card : ℕ) : ℝ)) *
          ((((b.divisors.filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).card : ℕ) : ℝ)) := by
          exact_mod_cast h1.trans h2
      _ ≤ cmOf c a * cmOf c b := mul_le_mul iha ihb (Nat.cast_nonneg _) (cmOf_nonneg c hc0 a)

/-- A product of two harmonic sums is dominated by `∑_{m ∈ M} κ(m)/m`. -/
theorem harm_mul_le (c : ℕ → ℝ) (Q : Finset ℕ) (hc0 : ∀ p, 0 ≤ c p)
    (hc1 : ∀ p, p.Prime → 1 ≤ c p) (hc2 : ∀ p, p.Prime → p ∉ Q → 2 ≤ c p)
    (A B M : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hB : ∀ b ∈ B, 0 < b ∧ ∀ q ∈ Q, ¬ q ∣ b)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ M) :
    (∑ a ∈ A, 1 / (a : ℝ)) * (∑ b ∈ B, 1 / (b : ℝ)) ≤ ∑ m ∈ M, cmOf c m / m := by
  classical
  have hprod : (∑ a ∈ A, 1 / (a : ℝ)) * (∑ b ∈ B, 1 / (b : ℝ)) =
      ∑ x ∈ A ×ˢ B, 1 / (x.1 : ℝ) * (1 / (x.2 : ℝ)) := by
    simp only [Finset.sum_mul_sum, Finset.sum_product]
  have hmaps : ∀ x ∈ A ×ˢ B, (fun x : ℕ × ℕ => x.1 * x.2) x ∈ M :=
    fun x hx => hAB x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2
  have hfw := Finset.sum_fiberwise_of_maps_to (s := A ×ˢ B) (t := M)
    (g := fun x : ℕ × ℕ => x.1 * x.2) hmaps (fun x => 1 / (x.1 : ℝ) * (1 / (x.2 : ℝ)))
  rw [hprod, ← hfw]
  apply Finset.sum_le_sum
  intro m _
  have hfib : ∀ x ∈ (A ×ˢ B).filter (fun x : ℕ × ℕ => x.1 * x.2 = m),
      1 / (x.1 : ℝ) * (1 / (x.2 : ℝ)) = 1 / (m : ℝ) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [one_div_mul_one_div, ← Nat.cast_mul, hx.2]
  have hsum_eq : ∑ x ∈ (A ×ˢ B).filter (fun x : ℕ × ℕ => x.1 * x.2 = m),
      1 / (x.1 : ℝ) * (1 / (x.2 : ℝ)) =
      ((((A ×ˢ B).filter (fun x : ℕ × ℕ => x.1 * x.2 = m)).card : ℕ) : ℝ) * (1 / (m : ℝ)) := by
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  refine le_trans (le_of_eq hsum_eq) ?_
  have hcard : ((A ×ˢ B).filter (fun x : ℕ × ℕ => x.1 * x.2 = m)).card ≤
      (m.divisors.filter (fun b => ∀ q ∈ Q, ¬ q ∣ b)).card := by
    apply Finset.card_le_card_of_injOn (fun x => x.2)
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx
      obtain ⟨⟨hxA, hxB⟩, hxm⟩ := hx
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors]
      have ha0 := hA x.1 hxA
      have hb0 := (hB x.2 hxB).1
      refine ⟨⟨Dvd.intro_left x.1 hxm, ?_⟩, (hB x.2 hxB).2⟩
      rw [← hxm]
      exact (Nat.mul_pos ha0 hb0).ne'
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx hy
      have hb0 := (hB x.2 hx.1.2).1
      have hxy' : x.2 = y.2 := hxy
      have h1 : x.1 * x.2 = y.1 * x.2 := by rw [hx.2, hxy', hy.2]
      exact Prod.ext (Nat.eq_of_mul_eq_mul_right hb0 h1) hxy'
  have hm0 : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  calc ((((A ×ˢ B).filter (fun x : ℕ × ℕ => x.1 * x.2 = m)).card : ℕ) : ℝ) * (1 / (m : ℝ))
      ≤ ((((m.divisors.filter (fun b => ∀ q ∈ Q, ¬ q ∣ b)).card : ℕ) : ℝ)) * (1 / (m : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hm0
    _ ≤ cmOf c m * (1 / (m : ℝ)) :=
        mul_le_mul_of_nonneg_right (card_divisors_avoid_le c Q hc0 hc1 hc2 m) hm0
    _ = cmOf c m / m := by rw [mul_one_div]

theorem disc_pos (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hD : det a₁ a₂ b₁ b₂ ≠ 0) :
    0 < disc a₁ a₂ b₁ b₂ := by
  unfold disc
  exact Nat.mul_pos (Nat.mul_pos ha₁ ha₂) (Int.natAbs_pos.mpr hD)

/-- The lower bound `G` for the Selberg bounding sum, `V = z^{1/4}`:
`G = (½ log V) · (φ(2E)/(2E) · log V)`. -/
def glb (z : ℝ) : ℝ :=
  (1 / 2 * Real.log (Real.sqrt (Real.sqrt z))) *
    (((2 * disc a₁ a₂ b₁ b₂).totient : ℝ) / ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ) *
      Real.log (Real.sqrt (Real.sqrt z)))

/-- **Main term.** `S ≥ (½ log z^{1/4}) (φ(2E)/(2E)) log z^{1/4}`. -/
theorem boundingSum_ge (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hD : det a₁ a₂ b₁ b₂ ≠ 0) (u : ℤ)
    (L : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    glb a₁ a₂ b₁ b₂ z ≤ (twoSieve a₁ a₂ b₁ b₂ u L z hz).selbergBoundingSum := by
  classical
  have hz0 : (0 : ℝ) ≤ z := by linarith
  have hsz1 : 1 ≤ Real.sqrt z := Real.one_le_sqrt.mpr hz
  have hV1 : 1 ≤ Real.sqrt (Real.sqrt z) := Real.one_le_sqrt.mpr hsz1
  have hV0 : 0 ≤ Real.sqrt (Real.sqrt z) := Real.sqrt_nonneg _
  have hq0 : 0 < 2 * disc a₁ a₂ b₁ b₂ := Nat.mul_pos two_pos (disc_pos a₁ a₂ b₁ b₂ ha₁ ha₂ hD)
  have hA := BrunTitchmarshAP.totient_mul_log_le_harmAvoid 2 two_pos _ hV1
  have hB := BrunTitchmarshAP.totient_mul_log_le_harmAvoid (2 * disc a₁ a₂ b₁ b₂) hq0 _ hV1
  rw [Nat.totient_two, Nat.cast_one] at hA
  have hlogV : 0 ≤ Real.log (Real.sqrt (Real.sqrt z)) := Real.log_nonneg hV1
  have hH0 : 0 ≤ BrunTitchmarshAP.harmAvoid (Nat.primeFactors 2) ⌊Real.sqrt (Real.sqrt z)⌋₊ := by
    unfold BrunTitchmarshAP.harmAvoid
    exact Finset.sum_nonneg (fun n _ => by positivity)
  have hprod : glb a₁ a₂ b₁ b₂ z ≤
      BrunTitchmarshAP.harmAvoid (Nat.primeFactors 2) ⌊Real.sqrt (Real.sqrt z)⌋₊ *
        BrunTitchmarshAP.harmAvoid (2 * disc a₁ a₂ b₁ b₂).primeFactors
          ⌊Real.sqrt (Real.sqrt z)⌋₊ := by
    unfold glb
    have hA' : 1 / 2 * Real.log (Real.sqrt (Real.sqrt z)) ≤
        BrunTitchmarshAP.harmAvoid (Nat.primeFactors 2) ⌊Real.sqrt (Real.sqrt z)⌋₊ := by
      have : ((2 : ℕ) : ℝ) = 2 := by norm_num
      rw [this] at hA
      exact hA
    exact mul_le_mul hA' hB
      (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hlogV) hH0
  refine le_trans hprod ?_
  refine le_trans ?_ (Sieve.selbergBoundingSum_ge_sum_div_filter (twoSieve a₁ a₂ b₁ b₂ u L z hz)
    (nu_cm a₁ a₂ b₁ b₂) (nu_nonneg a₁ a₂ b₁ b₂)
    (fun p hp hpP => (twoSieve a₁ a₂ b₁ b₂ u L z hz).nu_lt_one_of_prime p hp hpP))
  change _ ≤ ∑ m ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
      (fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ∣ ∏ q ∈ oddPrimes z, q), nu a₁ a₂ b₁ b₂ m
  rw [Finset.sum_congr rfl (fun m _ => nu_apply a₁ a₂ b₁ b₂ m)]
  unfold BrunTitchmarshAP.harmAvoid
  -- the size of the product ab
  have hWW : ⌊Real.sqrt (Real.sqrt z)⌋₊ * ⌊Real.sqrt (Real.sqrt z)⌋₊ ≤ ⌊Real.sqrt z⌋₊ := by
    apply Nat.le_floor
    have hW : ((⌊Real.sqrt (Real.sqrt z)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (Real.sqrt z) :=
      Nat.floor_le hV0
    push_cast
    calc ((⌊Real.sqrt (Real.sqrt z)⌋₊ : ℕ) : ℝ) * ((⌊Real.sqrt (Real.sqrt z)⌋₊ : ℕ) : ℝ)
        ≤ Real.sqrt (Real.sqrt z) * Real.sqrt (Real.sqrt z) :=
          mul_le_mul hW hW (Nat.cast_nonneg _) hV0
      _ = Real.sqrt z := Real.mul_self_sqrt (Real.sqrt_nonneg z)
  have hsqz : ⌊Real.sqrt z⌋₊ ≤ ⌊z⌋₊ := Nat.floor_mono (Sieve.sqrt_le_self z hz)
  have h2E : 2 ∈ (2 * disc a₁ a₂ b₁ b₂).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_mul_right 2 _, hq0.ne'⟩
  have h22 : 2 ∈ Nat.primeFactors 2 :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_refl 2, two_ne_zero⟩
  apply harm_mul_le (rho a₁ a₂ b₁ b₂) (2 * disc a₁ a₂ b₁ b₂).primeFactors
    (rho_nonneg a₁ a₂ b₁ b₂) (fun p _ => one_le_rho a₁ a₂ b₁ b₂ p)
  · intro p hp hpQ
    have hndvd : ¬ p ∣ disc a₁ a₂ b₁ b₂ := by
      intro h
      exact hpQ (Nat.mem_primeFactors.mpr ⟨hp, Dvd.dvd.mul_left h 2, hq0.ne'⟩)
    simp only [rho, if_neg hndvd, le_refl]
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_Icc] at ha
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one ha.1.1
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    exact ⟨Nat.lt_of_lt_of_le Nat.zero_lt_one hb.1.1, hb.2⟩
  · intro a ha b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at ha hb
    obtain ⟨⟨ha1, haW⟩, ha2⟩ := ha
    obtain ⟨⟨hb1, hbW⟩, hb2⟩ := hb
    have hab : a * b ≤ ⌊Real.sqrt z⌋₊ :=
      le_trans (Nat.mul_le_mul haW hbW) hWW
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.mul_pos ha1 hb1, hab⟩, ?_⟩
    intro p hp hpab
    rw [prime_dvd_prod_oddPrimes_iff z hp]
    constructor
    · exact le_trans (Nat.le_of_dvd (Nat.mul_pos ha1 hb1) hpab) (le_trans hab hsqz)
    · rintro rfl
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hpab with h | h
      · exact ha2 2 h22 h
      · exact hb2 2 h2E h

/-- **The sieve bound** (non-degenerate case), for `z > 1`. -/
theorem count_le_nondeg (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hcop : Nat.Coprime a₁ a₂)
    (hD : det a₁ a₂ b₁ b₂ ≠ 0) (hg₁ : Nat.Coprime a₁ b₁.natAbs)
    (hg₂ : Nat.Coprime a₂ b₂.natAbs) (u : ℤ) (L : ℕ) (z : ℝ) (hz : 1 < z) :
    ((((Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ =>
        ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime)).card : ℕ) : ℝ) ≤
      ((L : ℝ) + 1) / glb a₁ a₂ b₁ b₂ z +
        (z * (1 + Real.log z) ^ 6 + 2 * ((⌊z⌋₊ : ℝ) + 1)) := by
  have hz1 : 1 ≤ z := hz.le
  have h1 := card_prime_pairs_le_sifted a₁ a₂ b₁ b₂ ha₁ ha₂ u L z hz1
  have h2 := SelbergSieve.selberg_bound_simple (twoSieve a₁ a₂ b₁ b₂ u L z hz1)
  have h3 := errSum_le a₁ a₂ b₁ b₂ hcop hg₁ hg₂ u L z hz1
  have h4 := boundingSum_ge a₁ a₂ b₁ b₂ ha₁ ha₂ hD u L z hz1
  have hsz : 1 < Real.sqrt z := Real.lt_sqrt_of_sq_lt (by rw [one_pow]; exact hz)
  have hV : 1 < Real.sqrt (Real.sqrt z) := Real.lt_sqrt_of_sq_lt (by rw [one_pow]; exact hsz)
  have hlogV : 0 < Real.log (Real.sqrt (Real.sqrt z)) := Real.log_pos hV
  have hq0 : 0 < 2 * disc a₁ a₂ b₁ b₂ := Nat.mul_pos two_pos (disc_pos a₁ a₂ b₁ b₂ ha₁ ha₂ hD)
  have hφ : (0 : ℝ) < (2 * disc a₁ a₂ b₁ b₂).totient := by
    exact_mod_cast Nat.totient_pos.mpr hq0
  have hqR : (0 : ℝ) < ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ) := by exact_mod_cast hq0
  have hGpos : 0 < glb a₁ a₂ b₁ b₂ z := by
    unfold glb
    exact mul_pos (mul_pos (by norm_num) hlogV) (mul_pos (div_pos hφ hqR) hlogV)
  have hX : 0 ≤ (twoSieve a₁ a₂ b₁ b₂ u L z hz1).totalMass := by
    change (0 : ℝ) ≤ (L : ℝ) + 1
    positivity
  have h5 : (twoSieve a₁ a₂ b₁ b₂ u L z hz1).totalMass /
      (twoSieve a₁ a₂ b₁ b₂ u L z hz1).selbergBoundingSum ≤ ((L : ℝ) + 1) / glb a₁ a₂ b₁ b₂ z :=
    div_le_div_of_nonneg_left hX hGpos h4
  have h6 : siftedSum (s := (twoSieve a₁ a₂ b₁ b₂ u L z hz1).toBoundingSieve) ≤
      ((L : ℝ) + 1) / glb a₁ a₂ b₁ b₂ z + z * (1 + Real.log z) ^ 6 :=
    le_trans h2 (add_le_add h5 h3)
  linarith

/- ## Parameter choice `z = √T` -/

/-- `(√T (1 + log √T)^6 + 2(⌊√T⌋ + 1)) (log T)^2 ≤ 136049920 T` for `T ≥ 1`
(via `y = T^{1/16}`, `log T ≤ 16 y`). -/
theorem err_bound (T : ℝ) (hT : 1 ≤ T) :
    (Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 + 2 * ((⌊Real.sqrt T⌋₊ : ℝ) + 1)) *
      Real.log T ^ 2 ≤ 136049920 * T := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = T ^ ((1 : ℝ) / 16) := ⟨_, rfl⟩
  have hy1 : 1 ≤ y := by
    rw [hy]
    exact Real.one_le_rpow hT (by norm_num)
  have hy0' : 0 ≤ y := by linarith
  have hy16 : y ^ 16 = T := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hT0]
    norm_num
  have hsq : Real.sqrt T = y ^ 8 := by
    rw [← hy16, show (16 : ℕ) = 8 * 2 from rfl, pow_mul, Real.sqrt_sq (pow_nonneg hy0' 8)]
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlog : Real.log T ≤ 16 * y := by
    have h := Real.log_le_rpow_div hT0 (by norm_num : (0 : ℝ) < 1 / 16)
    rw [← hy] at h
    have e : y / (1 / 16) = 16 * y := by ring
    linarith
  have hlogs : Real.log (Real.sqrt T) = Real.log T / 2 := Real.log_sqrt hT0
  have hsq0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hfl : ((⌊Real.sqrt T⌋₊ : ℕ) : ℝ) ≤ y ^ 8 := (Nat.floor_le hsq0).trans (le_of_eq hsq)
  have h1 : 1 + Real.log (Real.sqrt T) ≤ 9 * y := by
    rw [hlogs]
    linarith
  have h1' : 0 ≤ 1 + Real.log (Real.sqrt T) := by
    rw [hlogs]
    linarith
  have h6 : (1 + Real.log (Real.sqrt T)) ^ 6 ≤ (9 * y) ^ 6 := pow_le_pow_left₀ h1' h1 6
  have h2 : Real.log T ^ 2 ≤ (16 * y) ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
  have hA : Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 ≤ y ^ 8 * (9 * y) ^ 6 := by
    calc Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 ≤ Real.sqrt T * (9 * y) ^ 6 :=
          mul_le_mul_of_nonneg_left h6 hsq0
      _ = y ^ 8 * (9 * y) ^ 6 := by rw [hsq]
  have hB : 2 * (((⌊Real.sqrt T⌋₊ : ℕ) : ℝ) + 1) ≤ 2 * (y ^ 8 + 1) := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hsum0 : 0 ≤ y ^ 8 * (9 * y) ^ 6 + 2 * (y ^ 8 + 1) := by positivity
  have hp2 : y ^ 2 ≤ y ^ 16 := pow_le_pow_right₀ hy1 (by norm_num)
  have hp10 : y ^ 10 ≤ y ^ 16 := pow_le_pow_right₀ hy1 (by norm_num)
  calc (Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 + 2 * ((⌊Real.sqrt T⌋₊ : ℝ) + 1)) *
        Real.log T ^ 2
      ≤ (y ^ 8 * (9 * y) ^ 6 + 2 * (y ^ 8 + 1)) * (16 * y) ^ 2 :=
        mul_le_mul (add_le_add hA hB) h2 (sq_nonneg _) hsum0
    _ = 136048896 * y ^ 16 + 512 * y ^ 10 + 512 * y ^ 2 := by ring
    _ ≤ 136048896 * y ^ 16 + 512 * y ^ 16 + 512 * y ^ 16 := by linarith
    _ = 136049920 * T := by
        rw [← hy16]
        ring

/-- `2E ≤ 2 · (a₁/φ(a₁)) (a₂/φ(a₂)) (|D|/φ(|D|)) · φ(2E)`. -/
theorem two_disc_le (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hD : det a₁ a₂ b₁ b₂ ≠ 0) :
    ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ) ≤
      2 * (((a₁ : ℝ) / (a₁.totient : ℝ)) * ((a₂ : ℝ) / (a₂.totient : ℝ)) *
        (((det a₁ a₂ b₁ b₂).natAbs : ℝ) / (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ))) *
        ((2 * disc a₁ a₂ b₁ b₂).totient : ℝ) := by
  have hD0 : 0 < (det a₁ a₂ b₁ b₂).natAbs := Int.natAbs_pos.mpr hD
  have hφ1 : (0 : ℝ) < a₁.totient := by exact_mod_cast Nat.totient_pos.mpr ha₁
  have hφ2 : (0 : ℝ) < a₂.totient := by exact_mod_cast Nat.totient_pos.mpr ha₂
  have hφD : (0 : ℝ) < ((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) := by
    exact_mod_cast Nat.totient_pos.mpr hD0
  have hn : a₁.totient * a₂.totient * (det a₁ a₂ b₁ b₂).natAbs.totient ≤
      (2 * disc a₁ a₂ b₁ b₂).totient := by
    calc a₁.totient * a₂.totient * (det a₁ a₂ b₁ b₂).natAbs.totient
        ≤ (a₁ * a₂).totient * (det a₁ a₂ b₁ b₂).natAbs.totient :=
          Nat.mul_le_mul_right _ (Nat.totient_super_multiplicative a₁ a₂)
      _ ≤ (disc a₁ a₂ b₁ b₂).totient := Nat.totient_super_multiplicative _ _
      _ = (2 : ℕ).totient * (disc a₁ a₂ b₁ b₂).totient := by rw [Nat.totient_two, one_mul]
      _ ≤ (2 * disc a₁ a₂ b₁ b₂).totient := Nat.totient_super_multiplicative _ _
  have e1 : (a₁ : ℝ) / (a₁.totient : ℝ) * (a₁.totient : ℝ) = a₁ := div_mul_cancel₀ _ hφ1.ne'
  have e2 : (a₂ : ℝ) / (a₂.totient : ℝ) * (a₂.totient : ℝ) = a₂ := div_mul_cancel₀ _ hφ2.ne'
  have e3 : ((det a₁ a₂ b₁ b₂).natAbs : ℝ) /
      (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ) *
      (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ) = (det a₁ a₂ b₁ b₂).natAbs :=
    div_mul_cancel₀ _ hφD.ne'
  have key : ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ) =
      2 * (((a₁ : ℝ) / (a₁.totient : ℝ)) * ((a₂ : ℝ) / (a₂.totient : ℝ)) *
        (((det a₁ a₂ b₁ b₂).natAbs : ℝ) / (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ))) *
        (((a₁.totient * a₂.totient * (det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ)) := by
    calc ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ)
        = 2 * ((a₁ : ℝ) * (a₂ : ℝ) * ((det a₁ a₂ b₁ b₂).natAbs : ℝ)) := by
          simp only [disc, Nat.cast_mul, Nat.cast_ofNat]
      _ = 2 * (((a₁ : ℝ) / (a₁.totient : ℝ) * (a₁.totient : ℝ)) *
            ((a₂ : ℝ) / (a₂.totient : ℝ) * (a₂.totient : ℝ)) *
            (((det a₁ a₂ b₁ b₂).natAbs : ℝ) / (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ) *
              (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ))) := by
          rw [e1, e2, e3]
      _ = _ := by
          push_cast
          ring
  rw [key]
  have hR0 : 0 ≤ 2 * (((a₁ : ℝ) / (a₁.totient : ℝ)) * ((a₂ : ℝ) / (a₂.totient : ℝ)) *
        (((det a₁ a₂ b₁ b₂).natAbs : ℝ) / (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ))) := by
    positivity
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn) hR0

end TheSieve

/-- **Two-dimensional upper-bound sieve** (Halberstam–Richert, *Sieve Methods*, Thm 2.2, the case
of two linear forms). For coprime `a₁, a₂ ≥ 1` and `D = a₁ b₂ − a₂ b₁ ≠ 0`, every integer `u` and
every real `T ≥ 2`, the number of `t ∈ [u, u + ⌊T⌋]` with `a₁ t + b₁` and `a₂ t + b₂` both prime is
at most `2^28 · T/(log T)^2 · a₁/φ(a₁) · a₂/φ(a₂) · |D|/φ(|D|)`. -/
theorem two_dim_sieve (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hcop : Nat.Coprime a₁ a₂) (hD : (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ ≠ 0) (u : ℤ) (T : ℝ)
    (hT : 2 ≤ T) :
    ((((Finset.Icc u (u + ⌊T⌋)).filter
          (fun t : ℤ =>
            ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime)).card : ℕ)
          : ℝ) ≤
        2 ^ 28 * T / (Real.log T) ^ 2 * ((a₁ : ℝ) / (a₁.totient : ℝ)) *
          ((a₂ : ℝ) / (a₂.totient : ℝ)) *
          ((((a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁).natAbs : ℝ) /
            ((((a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁).natAbs.totient : ℕ) : ℝ)) := by
  have hdet : det a₁ a₂ b₁ b₂ ≠ 0 := hD
  have hdet' : det a₁ a₂ b₁ b₂ = (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ := rfl
  rw [← hdet']
  have hD0 : 0 < (det a₁ a₂ b₁ b₂).natAbs := Int.natAbs_pos.mpr hdet
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hK : 0 < Real.log T ^ 2 := by positivity
  have hφ1 : (0 : ℝ) < a₁.totient := by exact_mod_cast Nat.totient_pos.mpr ha₁
  have hφ2 : (0 : ℝ) < a₂.totient := by exact_mod_cast Nat.totient_pos.mpr ha₂
  have hφD : (0 : ℝ) < ((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) := by
    exact_mod_cast Nat.totient_pos.mpr hD0
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ((a₁ : ℝ) / (a₁.totient : ℝ)) * ((a₂ : ℝ) / (a₂.totient : ℝ)) *
      (((det a₁ a₂ b₁ b₂).natAbs : ℝ) / (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ)) :=
    ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by
    have e1 : 1 ≤ (a₁ : ℝ) / (a₁.totient : ℝ) := by
      rw [one_le_div hφ1]
      exact_mod_cast Nat.totient_le a₁
    have e2 : 1 ≤ (a₂ : ℝ) / (a₂.totient : ℝ) := by
      rw [one_le_div hφ2]
      exact_mod_cast Nat.totient_le a₂
    have e3 : 1 ≤ ((det a₁ a₂ b₁ b₂).natAbs : ℝ) /
        (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ) := by
      rw [one_le_div hφD]
      exact_mod_cast Nat.totient_le _
    rw [hR]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le e1 e2) e3
  have hgoal : 2 ^ 28 * T / (Real.log T) ^ 2 * ((a₁ : ℝ) / (a₁.totient : ℝ)) *
      ((a₂ : ℝ) / (a₂.totient : ℝ)) *
      (((det a₁ a₂ b₁ b₂).natAbs : ℝ) / (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ)) =
      268435456 * T * R / Real.log T ^ 2 := by
    rw [hR]
    ring
  rw [hgoal, le_div_iff₀ hK]
  have hTR : T ≤ T * R := le_mul_of_one_le_right hT0 hR1
  have hTR0 : 0 ≤ T * R := mul_nonneg hT0 (by linarith)
  have herr := err_bound T hT1
  have hErr2 : 2 ≤ Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 +
      2 * ((⌊Real.sqrt T⌋₊ : ℝ) + 1) := by
    have hlogs : 0 ≤ Real.log (Real.sqrt T) :=
      Real.log_nonneg (Real.one_le_sqrt.mpr hT1)
    have : 0 ≤ Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 := by positivity
    have : (0 : ℝ) ≤ (⌊Real.sqrt T⌋₊ : ℝ) := Nat.cast_nonneg _
    linarith
  by_cases hnd : Nat.Coprime a₁ b₁.natAbs ∧ Nat.Coprime a₂ b₂.natAbs
  · obtain ⟨hg₁, hg₂⟩ := hnd
    have hfloor : ⌊T⌋ = ((⌊T⌋₊ : ℕ) : ℤ) := (Int.natCast_floor_eq_floor hT0).symm
    rw [hfloor]
    have hz : 1 < Real.sqrt T := Real.lt_sqrt_of_sq_lt (by rw [one_pow]; linarith)
    have hmain := count_le_nondeg a₁ a₂ b₁ b₂ ha₁ ha₂ hcop hdet hg₁ hg₂ u ⌊T⌋₊ (Real.sqrt T) hz
    have hV : Real.log (Real.sqrt (Real.sqrt (Real.sqrt T))) = Real.log T / 8 := by
      rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt (Real.sqrt_nonneg _),
        Real.log_sqrt hT0]
      ring
    have hq0 : 0 < 2 * disc a₁ a₂ b₁ b₂ := Nat.mul_pos two_pos (disc_pos a₁ a₂ b₁ b₂ ha₁ ha₂ hdet)
    have hφq : (0 : ℝ) < (2 * disc a₁ a₂ b₁ b₂).totient := by
      exact_mod_cast Nat.totient_pos.mpr hq0
    have hqR : (0 : ℝ) < ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ) := by exact_mod_cast hq0
    have hGlb : glb a₁ a₂ b₁ b₂ (Real.sqrt T) = Real.log T ^ 2 *
        (((2 * disc a₁ a₂ b₁ b₂).totient : ℝ) / ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ)) / 128 := by
      unfold glb
      rw [hV]
      ring
    have hRφ : 1 / 2 ≤ R * (((2 * disc a₁ a₂ b₁ b₂).totient : ℝ) /
        ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ)) := by
      have h := two_disc_le a₁ a₂ b₁ b₂ ha₁ ha₂ hdet
      rw [← hR] at h
      rw [← mul_div_assoc, le_div_iff₀ hqR]
      linarith
    have hL : ((⌊T⌋₊ : ℕ) : ℝ) + 1 ≤ 2 * T := by
      have := Nat.floor_le hT0
      linarith
    have hGpos : 0 < Real.log T ^ 2 *
        (((2 * disc a₁ a₂ b₁ b₂).totient : ℝ) / ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ)) / 128 :=
      div_pos (mul_pos hK (div_pos hφq hqR)) (by norm_num)
    have hMK : (((⌊T⌋₊ : ℕ) : ℝ) + 1) / glb a₁ a₂ b₁ b₂ (Real.sqrt T) * Real.log T ^ 2 ≤
        512 * T * R := by
      rw [hGlb, div_mul_eq_mul_div, div_le_iff₀ hGpos]
      calc (((⌊T⌋₊ : ℕ) : ℝ) + 1) * Real.log T ^ 2 ≤ 2 * T * Real.log T ^ 2 :=
            mul_le_mul_of_nonneg_right hL hK.le
        _ = 4 * T * Real.log T ^ 2 * (1 / 2) := by ring
        _ ≤ 4 * T * Real.log T ^ 2 * (R * (((2 * disc a₁ a₂ b₁ b₂).totient : ℝ) /
              ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hRφ (mul_nonneg (mul_nonneg (by norm_num) hT0) hK.le)
        _ = 512 * T * R * (Real.log T ^ 2 *
              (((2 * disc a₁ a₂ b₁ b₂).totient : ℝ) / ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ)) / 128) := by
            ring
    calc ((((Finset.Icc u (u + ((⌊T⌋₊ : ℕ) : ℤ))).filter (fun t : ℤ =>
            ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime)).card : ℕ) : ℝ) *
          Real.log T ^ 2
        ≤ ((((⌊T⌋₊ : ℕ) : ℝ) + 1) / glb a₁ a₂ b₁ b₂ (Real.sqrt T) +
            (Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 +
              2 * ((⌊Real.sqrt T⌋₊ : ℝ) + 1))) * Real.log T ^ 2 :=
          mul_le_mul_of_nonneg_right hmain hK.le
      _ = (((⌊T⌋₊ : ℕ) : ℝ) + 1) / glb a₁ a₂ b₁ b₂ (Real.sqrt T) * Real.log T ^ 2 +
            (Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 +
              2 * ((⌊Real.sqrt T⌋₊ : ℝ) + 1)) * Real.log T ^ 2 := by ring
      _ ≤ 512 * T * R + 136049920 * T := add_le_add hMK herr
      _ ≤ 268435456 * T * R := by linarith
  · -- a degenerate form takes at most one prime value
    have hc : ((Finset.Icc u (u + ⌊T⌋)).filter (fun t : ℤ =>
        ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime)).card ≤ 1 := by
      rcases not_and_or.mp hnd with h | h
      · refine le_trans (Finset.card_le_card ?_)
          (card_prime_values_le_one a₁ b₁ ha₁ h (Finset.Icc u (u + ⌊T⌋)))
        intro t ht
        rw [Finset.mem_filter] at ht ⊢
        exact ⟨ht.1, ht.2.1⟩
      · refine le_trans (Finset.card_le_card ?_)
          (card_prime_values_le_one a₂ b₂ ha₂ h (Finset.Icc u (u + ⌊T⌋)))
        intro t ht
        rw [Finset.mem_filter] at ht ⊢
        exact ⟨ht.1, ht.2.2⟩
    have hc' : ((((Finset.Icc u (u + ⌊T⌋)).filter (fun t : ℤ =>
        ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime)).card : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast hc
    have hK2 : 2 * Real.log T ^ 2 ≤ 136049920 * T := by
      calc 2 * Real.log T ^ 2 ≤ (Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 +
            2 * ((⌊Real.sqrt T⌋₊ : ℝ) + 1)) * Real.log T ^ 2 :=
            mul_le_mul_of_nonneg_right hErr2 hK.le
        _ ≤ 136049920 * T := herr
    calc ((((Finset.Icc u (u + ⌊T⌋)).filter (fun t : ℤ =>
            ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime)).card : ℕ) : ℝ) *
          Real.log T ^ 2
        ≤ 1 * Real.log T ^ 2 := mul_le_mul_of_nonneg_right hc' hK.le
      _ ≤ 268435456 * T * R := by linarith

end Principia.Common.TwoDimSieve

end

end TwoDim

/- ### Part `Prefix` -/

section Prefix
/-
# Prefix sums of divisors

A sum of the `k` smallest divisors of `m ≠ 0` is the sum of all divisors of `m` up to some divisor
`d` of `m`. We also record that `1 + p + q` is such a prefix sum for primes `p < q`.
-/

open Finset

open Erdos1054

namespace ErdosLean.Erdos1054

/-- The sum of the divisors of `m` that are at most `d`. -/
def S (m d : ℕ) : ℕ := ∑ e ∈ m.divisors with e ≤ d, e

/-- `n` is a prefix sum of divisors of some `m`, i.e. the condition defining `f`. -/
def Rep (n : ℕ) : Prop :=
  ∃ m : ℕ, ∃ k ≥ 1, n = ∑ i < k, Nat.nth (· ∈ m.divisors) i

lemma f_spec {n : ℕ} (h : Rep n) :
    ∃ k ≥ 1, n = ∑ i < k, Nat.nth (· ∈ (f n).divisors) i := by
  classical
  unfold Rep at h
  unfold f
  rw [dif_pos h]
  exact Nat.find_spec h

lemma f_eq_zero_of_not_rep {n : ℕ} (h : ¬ Rep n) : f n = 0 := by
  classical
  unfold Rep at h
  unfold f
  rw [dif_neg h]

lemma f_ne_zero_of_rep {n : ℕ} (hn : n ≠ 0) (h : Rep n) : f n ≠ 0 := by
  intro h0
  obtain ⟨k, -, hk⟩ := f_spec h
  rw [h0] at hk
  simp at hk
  exact hn hk

/-- The general shape of a prefix sum of divisors. -/
lemma sum_nth_divisors_eq (m k : ℕ) (hk : 1 ≤ k) (hkc : k ≤ #m.divisors) :
    Nat.nth (· ∈ m.divisors) (k - 1) ∈ m.divisors ∧
      ∑ i < k, Nat.nth (· ∈ m.divisors) i = S m (Nat.nth (· ∈ m.divisors) (k - 1)) := by
  classical
  set p : ℕ → Prop := (· ∈ m.divisors) with hp
  have hf : (Set.ofPred p).Finite := Set.finite_mem_finset m.divisors
  have hT : hf.toFinset = m.divisors := by
    ext x
    simp [p, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hjc : k - 1 < #hf.toFinset := by rw [hT]; omega
  refine ⟨by simpa [p] using Nat.nth_mem_of_lt_card hf hjc, ?_⟩
  have himg : (Finset.Iio k).image (Nat.nth p) = m.divisors.filter (· ≤ Nat.nth p (k - 1)) := by
    ext e
    simp only [Finset.mem_image, Finset.mem_Iio, Finset.mem_filter]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hic : i < #hf.toFinset := by omega
      refine ⟨by simpa [p] using Nat.nth_mem_of_lt_card hf hic, ?_⟩
      exact Nat.nth_le_nth_of_lt_card hf (by omega) hjc
    · rintro ⟨he, hle⟩
      obtain ⟨i, hi, rfl⟩ := Nat.exists_lt_card_finite_nth_eq hf (show p e from he)
      refine ⟨i, ?_, rfl⟩
      rcases lt_or_ge i k with h | h
      · exact h
      · have := Nat.nth_lt_nth_of_lt_card hf (show k - 1 < i by omega) hi
        omega
  have hinj : Set.InjOn (Nat.nth p) (Finset.Iio k : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_Iio, Set.mem_Iio] at ha hb
    exact (Nat.nth_strictMonoOn hf).injOn (Set.mem_Iio.mpr (by omega))
      (Set.mem_Iio.mpr (by omega)) hab
  unfold S
  rw [← himg, Finset.sum_image hinj]

/-- Every prefix sum of divisors of `m ≠ 0` is `S m d` for some divisor `d` of `m`. -/
lemma exists_S_eq (m k : ℕ) (hm : m ≠ 0) (hk : 1 ≤ k) :
    ∃ d ∈ m.divisors, ∑ i < k, Nat.nth (· ∈ m.divisors) i = S m d := by
  classical
  set c := #m.divisors with hc
  have hc1 : 1 ≤ c := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hm⟩
  set p : ℕ → Prop := (· ∈ m.divisors) with hp
  have hf : (Set.ofPred p).Finite := Set.finite_mem_finset m.divisors
  have hT : hf.toFinset = m.divisors := by
    ext x
    simp [p, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have key : ∑ i < k, Nat.nth p i = ∑ i < min k c, Nat.nth p i := by
    symm
    apply Finset.sum_subset
    · intro i hi
      simp only [Finset.mem_Iio] at hi ⊢
      omega
    · intro i hi hi'
      simp only [Finset.mem_Iio, not_lt] at hi hi'
      have hci : c ≤ i := by omega
      exact Nat.nth_of_card_le hf (by rw [hT]; exact hci)
  obtain ⟨h1, h2⟩ := sum_nth_divisors_eq m (min k c) (le_min hk hc1) (min_le_right _ _)
  exact ⟨_, h1, key.trans h2⟩

lemma divisors_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (p * q).divisors = {1, p, q, p * q} := by
  rw [Nat.divisors_mul, hp.divisors, hq.divisors]
  ext x
  simp only [Finset.mem_mul, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  · rintro (h | h | h | h) <;> rw [h]
    · exact ⟨1, Or.inl rfl, 1, Or.inl rfl, by simp⟩
    · exact ⟨p, Or.inr rfl, 1, Or.inl rfl, by simp⟩
    · exact ⟨1, Or.inl rfl, q, Or.inr rfl, by simp⟩
    · exact ⟨p, Or.inr rfl, q, Or.inr rfl, rfl⟩

/-- `1 + p + q` is the sum of the three smallest divisors of `p * q` when `p < q` are primes. -/
lemma rep_one_add_add {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Rep (1 + p + q) := by
  classical
  have hp1 := hp.one_lt
  have hq1 := hq.one_lt
  have hm : p * q ≠ 0 := Nat.mul_ne_zero hp.ne_zero hq.ne_zero
  have hpq' : q < p * q := by nlinarith
  have hD := divisors_mul_primes hp hq
  have hcard : #(p * q).divisors = 4 := by
    rw [hD]
    rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  -- the third smallest divisor is `q`
  have hnth : Nat.nth (· ∈ (p * q).divisors) 2 = q := by
    have hqmem : q ∈ (p * q).divisors := by rw [hD]; simp
    have hcount : Nat.count (· ∈ (p * q).divisors) q = 2 := by
      rw [Nat.count_eq_card_filter_range]
      have : (Finset.range q).filter (· ∈ (p * q).divisors) = {1, p} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, hD, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hx, h | h | h | h⟩ <;> omega
        · rintro (h | h) <;> refine ⟨by omega, by omega⟩
      rw [this, Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    rw [← hcount]
    exact Nat.nth_count hqmem
  refine ⟨p * q, 3, by norm_num, ?_⟩
  obtain ⟨-, h2⟩ := sum_nth_divisors_eq (p * q) 3 (by norm_num) (by omega)
  rw [h2, show 3 - 1 = 2 from rfl, hnth]
  unfold S
  rw [hD]
  have : ({1, p, q, p * q} : Finset ℕ).filter (· ≤ q) = {1, p, q} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h | h | h | h, hx⟩ <;> omega
    · rintro (h | h | h) <;> omega
  rw [this, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
    Finset.sum_singleton]
  ring

end ErdosLean.Erdos1054

end Prefix

/- ### Part `Tao` -/

section Tao
/-
# Tao's bound

Following Tao's argument (see the forum thread of Erdős problem 1054), the quantity
`T y = ∑_{m ≤ y} ∑_{d ∣ m} S m d` is `O(y²)`. By Markov's inequality this bounds the number of
`n ≤ X` with `ηX ≤ n` which are prefix sums of divisors of some `m ≤ δX` by `O(δ² X / η)`.
-/

open Finset Real

open Erdos1054

namespace ErdosLean.Erdos1054

/-- `T y = ∑_{m ∈ [1, y]} ∑_{d ∣ m} S m d`. -/
def T (y : ℕ) : ℕ := ∑ m ∈ Icc 1 y, ∑ d ∈ m.divisors, S m d

lemma divisors_eq_filter_Icc {m y : ℕ} (hm : m ∈ Icc 1 y) :
    m.divisors = (Icc 1 y).filter (· ∣ m) := by
  have h1 := (mem_Icc.1 hm).1
  have h2 := (mem_Icc.1 hm).2
  ext s
  simp only [Nat.mem_divisors, mem_filter, mem_Icc]
  constructor
  · rintro ⟨h, -⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), (Nat.le_of_dvd (by omega) h).trans h2⟩, h⟩
  · rintro ⟨-, h⟩
    exact ⟨h, by omega⟩

lemma le_of_div_le_div {m r s : ℕ} (hm : 0 < m) (hr : r ∣ m) (hs : s ∣ m)
    (h : m / r ≤ m / s) : s ≤ r := by
  by_contra hlt
  push Not at hlt
  have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hr hm
  have e1 : m / r * r = m := Nat.div_mul_cancel hr
  have e2 : m / s * s = m := Nat.div_mul_cancel hs
  have hpos : 0 < m / s := Nat.div_pos (Nat.le_of_dvd hm hs) (by omega)
  have : m / r * r ≤ m / s * r := Nat.mul_le_mul_right r h
  have : m / s * r < m / s * s := Nat.mul_lt_mul_of_pos_left hlt hpos
  omega

/-- The inner sum, rewritten through complementary divisors and bounded. -/
lemma inner_le (y m : ℕ) (hm : m ∈ Icc 1 y) :
    ((∑ d ∈ m.divisors, S m d : ℕ) : ℝ) ≤
      ∑ s ∈ Icc 1 y, ∑ r ∈ Icc 1 y,
        if s ∣ m ∧ r ∣ m ∧ s ≤ r then (y : ℝ) / r else 0 := by
  have hm1 := (mem_Icc.1 hm).1
  have hmy := (mem_Icc.1 hm).2
  have h1 : ∑ d ∈ m.divisors, S m d =
      ∑ s ∈ m.divisors, ∑ r ∈ m.divisors, if m / r ≤ m / s then m / r else 0 := by
    rw [← Nat.sum_div_divisors m (S m)]
    apply sum_congr rfl
    intro s _
    unfold S
    rw [sum_filter, ← Nat.sum_div_divisors m (fun e => if e ≤ m / s then e else 0)]
  rw [h1, divisors_eq_filter_Icc hm, sum_filter]
  push_cast
  apply sum_le_sum
  intro s hs
  split_ifs with hsm
  · rw [sum_filter]
    apply sum_le_sum
    intro r hr
    have hr1 := (mem_Icc.1 hr).1
    split_ifs with hrm hle hc hc
    · have hsr : s ≤ r := le_of_div_le_div (by omega) hrm hsm hle
      have hr0 : (r : ℝ) ≠ 0 := by positivity
      rw [Nat.cast_div hrm hr0]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hmy) (by positivity)
    · exact absurd ⟨hsm, hrm, le_of_div_le_div (by omega) hrm hsm hle⟩ hc
    · positivity
    · exact le_rfl
    · positivity
    · exact le_rfl
  · apply sum_nonneg
    intro r _
    split_ifs <;> positivity

lemma card_common_multiples (y s r : ℕ) :
    #((Icc 1 y).filter (fun m => s ∣ m ∧ r ∣ m)) = y / Nat.lcm s r := by
  have : (Icc 1 y).filter (fun m => s ∣ m ∧ r ∣ m) = (Ioc 0 y).filter (Nat.lcm s r ∣ ·) := by
    ext m
    simp only [mem_filter, mem_Icc, mem_Ioc, Nat.lcm_dvd_iff]
    omega
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]

/-- First reduction: `T y ≤ y² ∑_{s ≤ r ≤ y} gcd(s, r) / (r² s)`. -/
lemma T_le_gcd_sum (y : ℕ) :
    (T y : ℝ) ≤ (y : ℝ) ^ 2 * ∑ s ∈ Icc 1 y, ∑ r ∈ Icc 1 y,
      if s ≤ r then (Nat.gcd s r : ℝ) / ((r : ℝ) ^ 2 * s) else 0 := by
  unfold T
  rw [Nat.cast_sum]
  calc (∑ m ∈ Icc 1 y, ((∑ d ∈ m.divisors, S m d : ℕ) : ℝ))
      ≤ ∑ m ∈ Icc 1 y, ∑ s ∈ Icc 1 y, ∑ r ∈ Icc 1 y,
          if s ∣ m ∧ r ∣ m ∧ s ≤ r then (y : ℝ) / r else 0 :=
        sum_le_sum fun m hm => inner_le y m hm
    _ = ∑ s ∈ Icc 1 y, ∑ r ∈ Icc 1 y, ∑ m ∈ Icc 1 y,
          if s ∣ m ∧ r ∣ m ∧ s ≤ r then (y : ℝ) / r else 0 := by
        rw [sum_comm]
        apply sum_congr rfl
        intro s _
        rw [sum_comm]
    _ ≤ ∑ s ∈ Icc 1 y, ∑ r ∈ Icc 1 y,
          (y : ℝ) ^ 2 * if s ≤ r then (Nat.gcd s r : ℝ) / ((r : ℝ) ^ 2 * s) else 0 := by
        apply sum_le_sum
        intro s hs
        apply sum_le_sum
        intro r hr
        have hs1 := (mem_Icc.1 hs).1
        have hr1 := (mem_Icc.1 hr).1
        by_cases hsr : s ≤ r
        · simp only [hsr, and_true, if_true]
          rw [← sum_filter, sum_const, nsmul_eq_mul, card_common_multiples]
          have hL : (Nat.lcm s r : ℝ) * Nat.gcd s r = s * r := by
            have := Nat.gcd_mul_lcm s r
            rw [mul_comm]
            exact_mod_cast this
          have hL0 : (0 : ℝ) < Nat.lcm s r := by
            exact_mod_cast Nat.lcm_pos (by omega) (by omega)
          have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
          have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
          calc ((y / Nat.lcm s r : ℕ) : ℝ) * ((y : ℝ) / r)
              ≤ ((y : ℝ) / Nat.lcm s r) * ((y : ℝ) / r) := by
                gcongr
                exact Nat.cast_div_le
            _ = (y : ℝ) ^ 2 * ((Nat.gcd s r : ℝ) / ((r : ℝ) ^ 2 * s)) := by
                have hg : (Nat.gcd s r : ℝ) = s * r / Nat.lcm s r := by
                  rw [← hL]; field_simp
                rw [hg]
                field_simp
        · simp [hsr]
    _ = (y : ℝ) ^ 2 * ∑ s ∈ Icc 1 y, ∑ r ∈ Icc 1 y,
          if s ≤ r then (Nat.gcd s r : ℝ) / ((r : ℝ) ^ 2 * s) else 0 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro s _
        rw [mul_sum]

/-- The constant bounding the gcd sum. -/
noncomputable def K₀ : ℝ :=
  (∑' g : ℕ, ((g : ℝ) ^ 2)⁻¹) * (∑' u : ℕ, ((u : ℝ) ^ (3 / 2 : ℝ))⁻¹) ^ 2

lemma rpow_three_halves_mul_le {u v : ℝ} (hv : 0 < v) (hvu : v ≤ u) :
    u ^ (3 / 2 : ℝ) * v ^ (3 / 2 : ℝ) ≤ u ^ 2 * v := by
  have hu : 0 < u := hv.trans_le hvu
  have e : ∀ w : ℝ, 0 < w → w ^ (3 / 2 : ℝ) = w * w ^ (1 / 2 : ℝ) := by
    intro w hw
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hw, Real.rpow_one]
  have hsq : u ^ (1 / 2 : ℝ) * u ^ (1 / 2 : ℝ) = u := by
    rw [← Real.rpow_add hu]; norm_num
  have hvu' : v ^ (1 / 2 : ℝ) ≤ u ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hv.le hvu (by norm_num)
  rw [e u hu, e v hv]
  have h0 : 0 ≤ v ^ (1 / 2 : ℝ) := Real.rpow_nonneg hv.le _
  have h1 : 0 ≤ u ^ (1 / 2 : ℝ) := Real.rpow_nonneg hu.le _
  calc u * u ^ (1 / 2 : ℝ) * (v * v ^ (1 / 2 : ℝ))
      ≤ u * u ^ (1 / 2 : ℝ) * (v * u ^ (1 / 2 : ℝ)) := by gcongr
    _ = u * v * (u ^ (1 / 2 : ℝ) * u ^ (1 / 2 : ℝ)) := by ring
    _ = u ^ 2 * v := by rw [hsq]; ring

lemma gcd_sum_le (y : ℕ) :
    ∑ s ∈ Icc 1 y, ∑ r ∈ Icc 1 y,
      (if s ≤ r then (Nat.gcd s r : ℝ) / ((r : ℝ) ^ 2 * s) else 0) ≤ K₀ := by
  set a : ℕ → ℝ := fun g => ((g : ℝ) ^ 2)⁻¹ with ha
  set b : ℕ → ℝ := fun u => ((u : ℝ) ^ (3 / 2 : ℝ))⁻¹ with hb
  have ha0 : ∀ g, 0 ≤ a g := fun g => by positivity
  have hb0 : ∀ u, 0 ≤ b u := fun u => by positivity
  have hsa : Summable a := Real.summable_nat_pow_inv.mpr (by norm_num)
  have hsb : Summable b := Real.summable_nat_rpow_inv.mpr (by norm_num)
  set G : ℕ × ℕ × ℕ → ℝ := fun x => a x.1 * (b x.2.1 * b x.2.2) with hG
  set φ : ℕ × ℕ → ℕ × ℕ × ℕ := fun x => (Nat.gcd x.1 x.2, x.2 / Nat.gcd x.1 x.2,
    x.1 / Nat.gcd x.1 x.2) with hφ
  set P := (Icc 1 y ×ˢ Icc 1 y).filter (fun x : ℕ × ℕ => x.1 ≤ x.2) with hP
  set B := Icc 1 y ×ˢ Icc 1 y ×ˢ Icc 1 y with hB
  have step1 : ∑ s ∈ Icc 1 y, ∑ r ∈ Icc 1 y,
      (if s ≤ r then (Nat.gcd s r : ℝ) / ((r : ℝ) ^ 2 * s) else 0) =
      ∑ x ∈ P, (Nat.gcd x.1 x.2 : ℝ) / ((x.2 : ℝ) ^ 2 * x.1) := by
    rw [hP, sum_filter, sum_product]
  have hmem : ∀ x ∈ P, 1 ≤ x.1 ∧ x.1 ≤ y ∧ 1 ≤ x.2 ∧ x.2 ≤ y ∧ x.1 ≤ x.2 := by
    intro x hx
    simp only [hP, mem_filter, mem_product, mem_Icc] at hx
    omega
  have step2 : ∀ x ∈ P, (Nat.gcd x.1 x.2 : ℝ) / ((x.2 : ℝ) ^ 2 * x.1) ≤ G (φ x) := by
    intro x hx
    obtain ⟨h1, -, h3, -, h5⟩ := hmem x hx
    set g := Nat.gcd x.1 x.2 with hg
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
    obtain ⟨v, hv⟩ : g ∣ x.1 := Nat.gcd_dvd_left _ _
    obtain ⟨u, hu⟩ : g ∣ x.2 := Nat.gcd_dvd_right _ _
    have hv' : x.1 / g = v := by rw [hv, Nat.mul_div_cancel_left _ hg0]
    have hu' : x.2 / g = u := by rw [hu, Nat.mul_div_cancel_left _ hg0]
    have hv0 : 0 < v := by
      rcases Nat.eq_zero_or_pos v with h | h
      · rw [h, mul_zero] at hv; omega
      · exact h
    have hvu : v ≤ u := by
      rw [← hv', ← hu']; exact Nat.div_le_div_right h5
    simp only [hG, hφ, ha, hb]
    rw [← hg, hu', hv']
    rw [hv, hu]
    have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
    have hvR : (0 : ℝ) < v := by exact_mod_cast hv0
    have hvuR : (v : ℝ) ≤ u := by exact_mod_cast hvu
    have huR : (0 : ℝ) < u := hvR.trans_le hvuR
    have key := rpow_three_halves_mul_le hvR hvuR
    have hp1 : (0 : ℝ) < (u : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos huR _
    have hp2 : (0 : ℝ) < (v : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hvR _
    push_cast
    rw [show (g : ℝ) / ((g * u) ^ 2 * (g * v)) = 1 / (g ^ 2 * (u ^ 2 * v)) by
      field_simp]
    rw [show ((g : ℝ) ^ 2)⁻¹ * (((u : ℝ) ^ (3 / 2 : ℝ))⁻¹ * ((v : ℝ) ^ (3 / 2 : ℝ))⁻¹) =
      1 / (g ^ 2 * ((u : ℝ) ^ (3 / 2 : ℝ) * (v : ℝ) ^ (3 / 2 : ℝ))) by
      field_simp]
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have hinj : Set.InjOn φ P := by
    intro x hx x' hx' h
    simp only [hφ, Prod.mk.injEq] at h
    obtain ⟨hg, hu, hv⟩ := h
    obtain ⟨h1, -, h3, -, -⟩ := hmem x hx
    obtain ⟨h1', -, h3', -, -⟩ := hmem x' hx'
    have e1 : x.1 = Nat.gcd x.1 x.2 * (x.1 / Nat.gcd x.1 x.2) :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
    have e2 : x.2 = Nat.gcd x.1 x.2 * (x.2 / Nat.gcd x.1 x.2) :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
    have e1' : x'.1 = Nat.gcd x'.1 x'.2 * (x'.1 / Nat.gcd x'.1 x'.2) :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
    have e2' : x'.2 = Nat.gcd x'.1 x'.2 * (x'.2 / Nat.gcd x'.1 x'.2) :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
    ext
    · calc x.1 = Nat.gcd x.1 x.2 * (x.1 / Nat.gcd x.1 x.2) := e1
        _ = Nat.gcd x'.1 x'.2 * (x'.1 / Nat.gcd x'.1 x'.2) := by rw [hv, hg]
        _ = x'.1 := e1'.symm
    · calc x.2 = Nat.gcd x.1 x.2 * (x.2 / Nat.gcd x.1 x.2) := e2
        _ = Nat.gcd x'.1 x'.2 * (x'.2 / Nat.gcd x'.1 x'.2) := by rw [hu, hg]
        _ = x'.2 := e2'.symm
  have hmaps : ∀ x ∈ P, φ x ∈ B := by
    intro x hx
    obtain ⟨h1, h2, h3, h4, -⟩ := hmem x hx
    have hg0 : 0 < Nat.gcd x.1 x.2 := Nat.gcd_pos_of_pos_left _ (by omega)
    simp only [hφ, hB, mem_product, mem_Icc]
    refine ⟨⟨hg0, (Nat.gcd_le_left _ (by omega)).trans h2⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact Nat.div_pos (Nat.gcd_le_right _ (by omega)) hg0
    · exact (Nat.div_le_self _ _).trans h4
    · exact Nat.div_pos (Nat.gcd_le_left _ (by omega)) hg0
    · exact (Nat.div_le_self _ _).trans h2
  rw [step1]
  calc ∑ x ∈ P, (Nat.gcd x.1 x.2 : ℝ) / ((x.2 : ℝ) ^ 2 * x.1)
      ≤ ∑ x ∈ P, G (φ x) := sum_le_sum step2
    _ = ∑ z ∈ P.image φ, G z := (sum_image hinj).symm
    _ ≤ ∑ z ∈ B, G z := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro z hz
          obtain ⟨x, hx, rfl⟩ := mem_image.1 hz
          exact hmaps x hx
        · intro z _ _
          exact mul_nonneg (ha0 _) (mul_nonneg (hb0 _) (hb0 _))
    _ = (∑ g ∈ Icc 1 y, a g) * ((∑ u ∈ Icc 1 y, b u) * (∑ v ∈ Icc 1 y, b v)) := by
        rw [sum_mul_sum, sum_mul_sum, hB, sum_product]
        refine sum_congr rfl fun g _ => ?_
        rw [sum_product]
        refine sum_congr rfl fun u _ => ?_
        rw [mul_sum]
    _ ≤ K₀ := by
        have e1 : ∑ g ∈ Icc 1 y, a g ≤ ∑' g, a g := hsa.sum_le_tsum _ (fun g _ => ha0 g)
        have e2 : ∑ u ∈ Icc 1 y, b u ≤ ∑' u, b u := hsb.sum_le_tsum _ (fun u _ => hb0 u)
        have p1 : 0 ≤ ∑ g ∈ Icc 1 y, a g := sum_nonneg fun g _ => ha0 g
        have p2 : 0 ≤ ∑ u ∈ Icc 1 y, b u := sum_nonneg fun u _ => hb0 u
        unfold K₀
        rw [sq]
        gcongr

/-- **Tao's bound.** `T y ≤ K₀ y²`. -/
lemma T_le (y : ℕ) : (T y : ℝ) ≤ K₀ * (y : ℝ) ^ 2 := by
  calc (T y : ℝ) ≤ (y : ℝ) ^ 2 * _ := T_le_gcd_sum y
    _ ≤ (y : ℝ) ^ 2 * K₀ := by gcongr; exact gcd_sum_le y
    _ = K₀ * (y : ℝ) ^ 2 := mul_comm _ _

lemma K₀_nonneg : 0 ≤ K₀ := by
  unfold K₀
  apply mul_nonneg
  · exact tsum_nonneg fun g => by positivity
  · positivity

/-- The pairs `(m, d)` with `m ∈ [1, y]` and `d ∣ m`. -/
def pairs (y : ℕ) : Finset (Σ _ : ℕ, ℕ) := (Icc 1 y).sigma fun m => m.divisors

lemma sum_pairs (y : ℕ) : ∑ x ∈ pairs y, S x.1 x.2 = T y := by
  unfold pairs T
  rw [sum_sigma]

open Classical in
/-- **Counting the `n` with a small `f n`.** If `η, δ > 0`, then the number of `n < X` with
`η X ≤ n` which are prefix sums of divisors and satisfy `f n ≤ δ n` is at most `K₀ δ² X / η`. -/
lemma card_small_le (X : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    (#((range X).filter (fun n : ℕ => η * X ≤ (n : ℝ) ∧ Rep n ∧ (f n : ℝ) ≤ δ * n)) : ℝ) ≤
      K₀ * δ ^ 2 * X / η := by
  classical
  rcases Nat.eq_zero_or_pos X with hX | hX
  · subst hX; simp
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  set Y := ⌊δ * X⌋₊ with hY
  set Q := (pairs Y).filter (fun x => η * X ≤ (S x.1 x.2 : ℝ)) with hQ
  have hsub : (range X).filter (fun n : ℕ => η * X ≤ (n : ℝ) ∧ Rep n ∧ (f n : ℝ) ≤ δ * n) ⊆
      Q.image (fun x => S x.1 x.2) := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    obtain ⟨hnX, hηn, hrep, hfn⟩ := hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      have : (0 : ℝ) < η * X := mul_pos hη hXR
      push_cast at hηn
      linarith
    have hf0 := f_ne_zero_of_rep hn0 hrep
    obtain ⟨k, hk, hsum⟩ := f_spec hrep
    obtain ⟨d, hd, hS⟩ := exists_S_eq (f n) k hf0 hk
    have hSn : S (f n) d = n := (hsum.trans hS).symm
    rw [mem_image]
    refine ⟨⟨f n, d⟩, ?_, hSn⟩
    simp only [hQ, mem_filter, pairs, mem_sigma, mem_Icc]
    refine ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr hf0, ?_⟩, hd⟩, ?_⟩
    · rw [hY]
      apply Nat.le_floor
      calc (f n : ℝ) ≤ δ * n := hfn
        _ ≤ δ * X := by gcongr
    · show η * X ≤ (S (f n) d : ℝ)
      rw [hSn]; exact hηn
  have hcard : (#Q : ℝ) * (η * X) ≤ K₀ * δ ^ 2 * X ^ 2 := by
    have h1 : (#Q : ℝ) * (η * X) ≤ ∑ x ∈ Q, (S x.1 x.2 : ℝ) := by
      have := card_nsmul_le_sum Q (fun x => (S x.1 x.2 : ℝ)) (η * X)
        (fun x hx => (mem_filter.1 hx).2)
      rwa [nsmul_eq_mul] at this
    have h2 : ∑ x ∈ Q, (S x.1 x.2 : ℝ) ≤ ∑ x ∈ pairs Y, (S x.1 x.2 : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    have h3 : ∑ x ∈ pairs Y, (S x.1 x.2 : ℝ) = T Y := by
      rw [← sum_pairs]; push_cast; rfl
    have h4 : (Y : ℝ) ≤ δ * X := Nat.floor_le (by positivity)
    have h5 : (T Y : ℝ) ≤ K₀ * δ ^ 2 * X ^ 2 := by
      calc (T Y : ℝ) ≤ K₀ * (Y : ℝ) ^ 2 := T_le Y
        _ ≤ K₀ * (δ * X) ^ 2 := by
            gcongr
            · exact K₀_nonneg
        _ = K₀ * δ ^ 2 * X ^ 2 := by ring
    linarith
  have hQ' : (#Q : ℝ) ≤ K₀ * δ ^ 2 * X / η := by
    rw [le_div_iff₀ hη]
    have : (#Q : ℝ) * η * X ≤ K₀ * δ ^ 2 * X * X := by nlinarith
    nlinarith
  calc (#((range X).filter (fun n : ℕ => η * X ≤ (n : ℝ) ∧ Rep n ∧ (f n : ℝ) ≤ δ * n)) : ℝ)
      ≤ #(Q.image (fun x => S x.1 x.2)) := by exact_mod_cast card_le_card hsub
    _ ≤ #Q := by exact_mod_cast card_image_le
    _ ≤ K₀ * δ ^ 2 * X / η := hQ'

end ErdosLean.Erdos1054

end Tao

/- ### Part `Totient` -/

section Totient
/-
# The mean square of `h / φ(h)` is bounded

We show `∑_{h ≤ Y} (h / φ(h))² ≤ K₁ Y` for an absolute constant `K₁`.
-/

open Finset Real

open Erdos1054

namespace ErdosLean.Erdos1054

lemma ratio_totient_eq_prod {h : ℕ} (hh : h ≠ 0) :
    (h : ℝ) / h.totient = ∏ p ∈ h.primeFactors, ((p : ℝ) / (p - 1)) := by
  have key := Nat.totient_mul_prod_primeFactors h
  have hp1 : ∀ p ∈ h.primeFactors, (1 : ℝ) < p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have keyR : (h.totient : ℝ) * ∏ p ∈ h.primeFactors, (p : ℝ) =
      h * ∏ p ∈ h.primeFactors, ((p : ℝ) - 1) := by
    have : ((h.totient * ∏ p ∈ h.primeFactors, p : ℕ) : ℝ) =
        ((h * ∏ p ∈ h.primeFactors, (p - 1) : ℕ) : ℝ) := by rw [key]
    push_cast at this
    rw [this]
    congr 1
    apply prod_congr rfl
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).one_lt
    rw [Nat.cast_sub this.le]
    simp
  have hφ : (0 : ℝ) < h.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hh)
  have hpos : (0 : ℝ) < ∏ p ∈ h.primeFactors, ((p : ℝ) - 1) :=
    prod_pos fun p hp => by linarith [hp1 p hp]
  rw [prod_div_distrib, div_eq_div_iff hφ.ne' hpos.ne']
  linarith [keyR]

lemma sq_ratio_le {p : ℝ} (hp : 2 ≤ p) : (p / (p - 1)) ^ 2 ≤ 1 + 8 / p := by
  have h1 : 0 < p - 1 := by linarith
  have hp0 : 0 < p := by linarith
  have e : p / (p - 1) ≤ 1 + 2 / p := by
    rw [div_le_iff₀ h1]
    have : (1 + 2 / p) * (p - 1) = p + 1 - 2 / p := by field_simp; ring
    rw [this]
    have : 2 / p ≤ 1 := by rw [div_le_one hp0]; linarith
    linarith
  have e0 : 0 ≤ p / (p - 1) := by positivity
  calc (p / (p - 1)) ^ 2 ≤ (1 + 2 / p) ^ 2 := by gcongr
    _ = 1 + 4 / p + 4 / p * (1 / p) := by field_simp; ring
    _ ≤ 1 + 4 / p + 4 / p * 1 := by
        gcongr
        rw [div_le_one hp0]; linarith
    _ = 1 + 8 / p := by ring

/-- The constant in the mean-square bound for `h / φ(h)`. -/
noncomputable def K₁ : ℝ := Real.exp (8 * ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹)

lemma sum_sq_ratio_totient_le (Y : ℕ) :
    ∑ h ∈ Icc 1 Y, ((h : ℝ) / h.totient) ^ 2 ≤ K₁ * Y := by
  classical
  set PY := (range (Y + 1)).filter Nat.Prime with hPY
  set w : Finset ℕ → ℝ := fun D => ∏ p ∈ D, (8 / (p : ℝ)) with hw
  have hw0 : ∀ D, 0 ≤ w D := fun D => prod_nonneg fun p _ => by positivity
  have hpf : ∀ h ∈ Icc 1 Y, h.primeFactors ⊆ PY := by
    intro h hh p hp
    have hh' := mem_Icc.1 hh
    simp only [hPY, mem_filter, mem_range]
    exact ⟨Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactors hp).trans hh'.2),
      Nat.prime_of_mem_primeFactors hp⟩
  -- step 1: pointwise bound by a sum over subsets of prime factors
  have step1 : ∀ h ∈ Icc 1 Y, ((h : ℝ) / h.totient) ^ 2 ≤
      ∑ D ∈ PY.powerset, if D ⊆ h.primeFactors then w D else 0 := by
    intro h hh
    have h0 : h ≠ 0 := by have := (mem_Icc.1 hh).1; omega
    rw [ratio_totient_eq_prod h0, ← prod_pow]
    calc ∏ p ∈ h.primeFactors, ((p : ℝ) / (p - 1)) ^ 2
        ≤ ∏ p ∈ h.primeFactors, (1 + 8 / (p : ℝ)) := by
          apply prod_le_prod
          · intro p _; positivity
          · intro p hp
            exact sq_ratio_le (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)
      _ = ∑ D ∈ h.primeFactors.powerset, w D := prod_one_add _
      _ = ∑ D ∈ PY.powerset, if D ⊆ h.primeFactors then w D else 0 := by
          rw [← sum_filter]
          congr 1
          ext D
          simp only [mem_powerset, mem_filter]
          constructor
          · intro hD; exact ⟨hD.trans (hpf h hh), hD⟩
          · intro hD; exact hD.2
  -- step 2: count the multiples
  have step2 : ∀ D ∈ PY.powerset,
      ∑ h ∈ Icc 1 Y, (if D ⊆ h.primeFactors then w D else 0) ≤
        (Y : ℝ) * ∏ p ∈ D, (8 / (p : ℝ) ^ 2) := by
    intro D hD
    have hDP : ∀ p ∈ D, p.Prime := fun p hp => by
      have := mem_powerset.1 hD hp
      simp only [hPY, mem_filter] at this
      exact this.2
    set q := ∏ p ∈ D, p with hq
    have hq0 : 0 < q := prod_pos fun p hp => (hDP p hp).pos
    have hiff : ∀ h ∈ Icc 1 Y, D ⊆ h.primeFactors ↔ q ∣ h := by
      intro h hh
      have h0 : h ≠ 0 := by have := (mem_Icc.1 hh).1; omega
      constructor
      · intro hsub
        exact Finset.prod_primes_dvd h (fun p hp => (hDP p hp).prime)
          (fun p hp => Nat.dvd_of_mem_primeFactors (hsub hp))
      · intro hqd p hp
        rw [Nat.mem_primeFactors]
        exact ⟨hDP p hp, (dvd_prod_of_mem _ hp).trans hqd, h0⟩
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hcard : #((Icc 1 Y).filter (fun h => D ⊆ h.primeFactors)) = Y / q := by
      have : (Icc 1 Y).filter (fun h => D ⊆ h.primeFactors) = (Ioc 0 Y).filter (q ∣ ·) := by
        ext h
        simp only [mem_filter]
        constructor
        · rintro ⟨hh, hd⟩
          have hh' := mem_Icc.1 hh
          exact ⟨mem_Ioc.2 ⟨by omega, hh'.2⟩, (hiff h hh).1 hd⟩
        · rintro ⟨hh, hd⟩
          have hh'' := mem_Ioc.1 hh
          have hh' : h ∈ Icc 1 Y := mem_Icc.2 ⟨by omega, hh''.2⟩
          exact ⟨hh', (hiff h hh').2 hd⟩
      rw [this, Nat.Ioc_filter_dvd_card_eq_div]
    rw [hcard]
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
    calc ((Y / q : ℕ) : ℝ) * w D ≤ ((Y : ℝ) / q) * w D :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le (hw0 D)
      _ = (Y : ℝ) * ∏ p ∈ D, (8 / (p : ℝ) ^ 2) := by
          rw [hw, hq]
          push_cast
          rw [div_mul_eq_mul_div, mul_div_assoc, ← prod_div_distrib]
          congr 1
          apply prod_congr rfl
          intro p hp
          have : (p : ℝ) ≠ 0 := by exact_mod_cast (hDP p hp).ne_zero
          field_simp
  -- step 3: the Euler product
  have step3 : ∑ D ∈ PY.powerset, ∏ p ∈ D, (8 / (p : ℝ) ^ 2) ≤ K₁ := by
    rw [← prod_one_add]
    have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
    calc ∏ p ∈ PY, (1 + 8 / (p : ℝ) ^ 2) ≤ ∏ p ∈ PY, Real.exp (8 / (p : ℝ) ^ 2) := by
          apply prod_le_prod
          · intro p _; positivity
          · intro p _
            have := Real.add_one_le_exp (8 / (p : ℝ) ^ 2)
            linarith
      _ = Real.exp (∑ p ∈ PY, 8 / (p : ℝ) ^ 2) := (Real.exp_sum _ _).symm
      _ ≤ K₁ := by
          unfold K₁
          apply Real.exp_le_exp.mpr
          simp_rw [div_eq_mul_inv, ← mul_sum]
          gcongr
          exact hs.sum_le_tsum _ (fun n _ => by positivity)
  calc ∑ h ∈ Icc 1 Y, ((h : ℝ) / h.totient) ^ 2
      ≤ ∑ h ∈ Icc 1 Y, ∑ D ∈ PY.powerset, (if D ⊆ h.primeFactors then w D else 0) :=
        sum_le_sum step1
    _ = ∑ D ∈ PY.powerset, ∑ h ∈ Icc 1 Y, (if D ⊆ h.primeFactors then w D else 0) := sum_comm
    _ ≤ ∑ D ∈ PY.powerset, (Y : ℝ) * ∏ p ∈ D, (8 / (p : ℝ) ^ 2) := sum_le_sum step2
    _ = (Y : ℝ) * ∑ D ∈ PY.powerset, ∏ p ∈ D, (8 / (p : ℝ) ^ 2) := (mul_sum _ _ _).symm
    _ ≤ (Y : ℝ) * K₁ := by gcongr
    _ = K₁ * Y := mul_comm _ _

end ErdosLean.Erdos1054

end Totient

/- ### Part `Goldbach` -/

section Goldbach
/-
# A positive proportion of integers are prefix sums of divisors

For primes `p < q` the integer `1 + p + q` is the sum of the three smallest divisors of `p q`.
By the Cauchy–Schwarz inequality (in the form of additive energy) and the two-dimensional upper
bound sieve, the sums `p + q` of two primes up to `Y` take `≫ Y` distinct values.
-/

open Finset Real
open scoped Combinatorics.Additive Pointwise

open Erdos1054

namespace ErdosLean.Erdos1054

noncomputable instance : DecidablePred Rep := Classical.decPred _

/-- The primes up to `Y`. -/
def primesUpTo (Y : ℕ) : Finset ℕ := (range (Y + 1)).filter Nat.Prime

lemma mem_primesUpTo {Y p : ℕ} : p ∈ primesUpTo Y ↔ p ≤ Y ∧ p.Prime := by
  simp [primesUpTo]

lemma card_primesUpTo (Y : ℕ) : #(primesUpTo Y) = Nat.primeCounting Y := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rfl

/-- The primes `t ≤ Y` with `t + h` also a prime `≤ Y`. -/
def Q (Y h : ℕ) : Finset ℕ := (primesUpTo Y).filter (fun t => t + h ∈ primesUpTo Y)

/-- The additive energy of the primes is controlled by the prime pairs with a given difference. -/
lemma energy_le (Y : ℕ) :
    E[primesUpTo Y, primesUpTo Y] ≤
      #(primesUpTo Y) ^ 2 + 2 * ∑ h ∈ Icc 1 Y, #(Q Y h) ^ 2 := by
  classical
  set P := primesUpTo Y with hP
  set F := ((P ×ˢ P) ×ˢ P ×ˢ P).filter (fun x : (ℕ × ℕ) × ℕ × ℕ => x.1.1 + x.2.1 = x.1.2 + x.2.2)
    with hF
  have hE : E[P, P] = #F := rfl
  set S := (Icc 1 Y).sigma (fun h => Q Y h ×ˢ Q Y h) with hS
  have hcardS : #S = ∑ h ∈ Icc 1 Y, #(Q Y h) ^ 2 := by
    rw [hS, card_sigma]
    simp [card_product, sq]
  have memF : ∀ x ∈ F, (x.1.1 ≤ Y ∧ x.1.1.Prime) ∧ (x.1.2 ≤ Y ∧ x.1.2.Prime) ∧
      (x.2.1 ≤ Y ∧ x.2.1.Prime) ∧ (x.2.2 ≤ Y ∧ x.2.2.Prime) ∧ x.1.1 + x.2.1 = x.1.2 + x.2.2 := by
    intro x hx
    simp only [hF, hP, mem_filter, mem_product, mem_primesUpTo] at hx
    exact ⟨hx.1.1.1, hx.1.1.2, hx.1.2.1, hx.1.2.2, hx.2⟩
  -- the three cases `a₁ = a₂`, `a₂ < a₁`, `a₁ < a₂`
  have hA : #(F.filter (fun x => x.1.1 = x.1.2)) ≤ #P ^ 2 := by
    rw [sq, ← card_product]
    apply card_le_card_of_injOn (fun x => (x.1.1, x.2.1))
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx
      have := memF x hx.1
      simp only [mem_coe, mem_product, hP, mem_primesUpTo]
      exact ⟨this.1, this.2.2.1⟩
    · intro x hx y hy hxy
      simp only [coe_filter, Set.mem_ofPred_eq] at hx hy
      simp only [Prod.mk.injEq] at hxy
      have hx' := (memF x hx.1).2.2.2.2
      have hy' := (memF y hy.1).2.2.2.2
      ext <;> omega
  have hB : #(F.filter (fun x => x.1.2 < x.1.1)) ≤ #S := by
    apply card_le_card_of_injOn
      (fun x => (⟨x.1.1 - x.1.2, (x.1.2, x.2.1)⟩ : Σ _ : ℕ, ℕ × ℕ))
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx
      obtain ⟨⟨h11, p11⟩, ⟨h12, p12⟩, ⟨h21, p21⟩, ⟨h22, p22⟩, he⟩ := memF x hx.1
      have hlt := hx.2
      simp only [hS, mem_coe, mem_sigma, mem_Icc, mem_product, Q, mem_filter, mem_primesUpTo]
      refine ⟨⟨by omega, by omega⟩, ⟨⟨h12, p12⟩, ?_, ?_⟩, ⟨⟨h21, p21⟩, ?_, ?_⟩⟩
      · omega
      · rw [show x.1.2 + (x.1.1 - x.1.2) = x.1.1 by omega]; exact p11
      · omega
      · rw [show x.2.1 + (x.1.1 - x.1.2) = x.2.2 by omega]; exact p22
    · intro x hx y hy hxy
      simp only [coe_filter, Set.mem_ofPred_eq] at hx hy
      simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq] at hxy
      have hx' := (memF x hx.1).2.2.2.2
      have hy' := (memF y hy.1).2.2.2.2
      have := hx.2
      have := hy.2
      ext <;> omega
  have hC : #(F.filter (fun x => x.1.1 < x.1.2)) ≤ #S := by
    apply card_le_card_of_injOn
      (fun x => (⟨x.1.2 - x.1.1, (x.1.1, x.2.2)⟩ : Σ _ : ℕ, ℕ × ℕ))
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx
      obtain ⟨⟨h11, p11⟩, ⟨h12, p12⟩, ⟨h21, p21⟩, ⟨h22, p22⟩, he⟩ := memF x hx.1
      have hlt := hx.2
      simp only [hS, mem_coe, mem_sigma, mem_Icc, mem_product, Q, mem_filter, mem_primesUpTo]
      refine ⟨⟨by omega, by omega⟩, ⟨⟨h11, p11⟩, ?_, ?_⟩, ⟨⟨h22, p22⟩, ?_, ?_⟩⟩
      · omega
      · rw [show x.1.1 + (x.1.2 - x.1.1) = x.1.2 by omega]; exact p12
      · omega
      · rw [show x.2.2 + (x.1.2 - x.1.1) = x.2.1 by omega]; exact p21
    · intro x hx y hy hxy
      simp only [coe_filter, Set.mem_ofPred_eq] at hx hy
      simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq] at hxy
      have hx' := (memF x hx.1).2.2.2.2
      have hy' := (memF y hy.1).2.2.2.2
      have := hx.2
      have := hy.2
      ext <;> omega
  have hsplit : #F ≤ #(F.filter (fun x => x.1.1 = x.1.2)) +
      #(F.filter (fun x => x.1.2 < x.1.1)) + #(F.filter (fun x => x.1.1 < x.1.2)) := by
    have h1 := card_filter_add_card_filter_not (s := F) (fun x => x.1.1 = x.1.2)
    have h2 := card_filter_add_card_filter_not
      (s := F.filter (fun x => ¬ x.1.1 = x.1.2)) (fun x => x.1.2 < x.1.1)
    have h3 : #((F.filter (fun x => ¬ x.1.1 = x.1.2)).filter (fun x => x.1.2 < x.1.1)) ≤
        #(F.filter (fun x => x.1.2 < x.1.1)) :=
      card_le_card (fun x hx => by
        simp only [mem_filter] at hx ⊢; exact ⟨hx.1.1, hx.2⟩)
    have h4 : #((F.filter (fun x => ¬ x.1.1 = x.1.2)).filter (fun x => ¬ x.1.2 < x.1.1)) ≤
        #(F.filter (fun x => x.1.1 < x.1.2)) :=
      card_le_card (fun x hx => by
        simp only [mem_filter] at hx ⊢; exact ⟨hx.1.1, by omega⟩)
    omega
  rw [hE]
  omega

/-- The two-dimensional sieve bound for prime pairs with difference `h`. -/
lemma card_Q_le (Y h : ℕ) (hY : 2 ≤ Y) (hh : 1 ≤ h) :
    (#(Q Y h) : ℝ) ≤ 2 ^ 28 * Y / (Real.log Y) ^ 2 * ((h : ℝ) / h.totient) := by
  classical
  have key := Principia.Common.TwoDimSieve.two_dim_sieve 1 1 0 (h : ℤ) one_pos one_pos
    (Nat.coprime_one_left 1) (by simp; omega) 0 (Y : ℝ) (by exact_mod_cast hY)
  simp only [Nat.cast_one, one_mul, add_zero, mul_zero, sub_zero, Nat.totient_one,
    div_one, mul_one, Int.natAbs_natCast, zero_add, Int.floor_natCast] at key
  refine le_trans ?_ key
  have : #(Q Y h) ≤ #((Icc (0 : ℤ) Y).filter
      (fun t : ℤ => t.toNat.Prime ∧ (t + h).toNat.Prime)) := by
    apply card_le_card_of_injOn (fun t : ℕ => (t : ℤ))
    · intro t ht
      simp only [Q, coe_filter, Set.mem_ofPred_eq, mem_primesUpTo] at ht
      simp only [mem_coe, mem_filter, mem_Icc]
      refine ⟨⟨by positivity, by exact_mod_cast ht.1.1⟩, by simpa using ht.1.2, ?_⟩
      rw [show ((t : ℤ) + h) = ((t + h : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
      exact ht.2.2
    · intro a _ b _ hab
      simpa using hab
  exact_mod_cast this

lemma two_pow_ne : ((2 : ℝ) ^ 28) ≠ 0 := by positivity

/-- The energy bound in real form. -/
lemma energy_le_real (Y : ℕ) (hY : 2 ≤ Y) :
    (E[primesUpTo Y, primesUpTo Y] : ℝ) ≤
      (#(primesUpTo Y) : ℝ) ^ 2 + 2 ^ 57 * K₁ * (Y : ℝ) ^ 3 / (Real.log Y) ^ 4 := by
  have h1 := energy_le Y
  have hL : 0 < Real.log Y := Real.log_pos (by exact_mod_cast hY)
  have hsum : (∑ h ∈ Icc 1 Y, (#(Q Y h) : ℝ) ^ 2) ≤
      (2 ^ 28 * Y / (Real.log Y) ^ 2) ^ 2 * (K₁ * Y) := by
    calc (∑ h ∈ Icc 1 Y, (#(Q Y h) : ℝ) ^ 2)
        ≤ ∑ h ∈ Icc 1 Y, (2 ^ 28 * Y / (Real.log Y) ^ 2 * ((h : ℝ) / h.totient)) ^ 2 := by
          apply sum_le_sum
          intro h hh
          have := card_Q_le Y h hY (mem_Icc.1 hh).1
          gcongr
      _ = (2 ^ 28 * Y / (Real.log Y) ^ 2) ^ 2 * ∑ h ∈ Icc 1 Y, ((h : ℝ) / h.totient) ^ 2 := by
          rw [mul_sum]
          apply sum_congr rfl
          intro h _
          ring
      _ ≤ (2 ^ 28 * Y / (Real.log Y) ^ 2) ^ 2 * (K₁ * Y) := by
          gcongr
          exact sum_sq_ratio_totient_le Y
  have h1' : (E[primesUpTo Y, primesUpTo Y] : ℝ) ≤
      (#(primesUpTo Y) : ℝ) ^ 2 + 2 * ∑ h ∈ Icc 1 Y, (#(Q Y h) : ℝ) ^ 2 := by
    exact_mod_cast h1
  calc (E[primesUpTo Y, primesUpTo Y] : ℝ)
      ≤ (#(primesUpTo Y) : ℝ) ^ 2 + 2 * ∑ h ∈ Icc 1 Y, (#(Q Y h) : ℝ) ^ 2 := h1'
    _ ≤ (#(primesUpTo Y) : ℝ) ^ 2 + 2 * ((2 ^ 28 * Y / (Real.log Y) ^ 2) ^ 2 * (K₁ * Y)) := by
        gcongr
    _ = (#(primesUpTo Y) : ℝ) ^ 2 + 2 ^ 57 * K₁ * (Y : ℝ) ^ 3 / (Real.log Y) ^ 4 := by
        field_simp

/-- Sums of two distinct primes give prefix sums: `#(P + P) ≤ #{n ≤ 2Y : Rep n} + #P`. -/
lemma card_sumset_le (Y : ℕ) :
    #(primesUpTo Y + primesUpTo Y) ≤
      #((range (2 * Y + 1)).filter Rep) + #(primesUpTo Y) := by
  classical
  set P := primesUpTo Y
  have hsub : P + P ⊆ ((range (2 * Y + 1)).filter Rep).image (fun n => n - 1) ∪
      P.image (fun p => 2 * p) := by
    intro n hn
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hn
    rw [mem_primesUpTo] at ha hb
    rcases lt_trichotomy a b with hab | rfl | hab
    · apply mem_union_left
      rw [mem_image]
      refine ⟨1 + a + b, ?_, by omega⟩
      simp only [mem_filter, mem_range]
      exact ⟨by omega, rep_one_add_add ha.2 hb.2 hab⟩
    · apply mem_union_right
      rw [mem_image]
      exact ⟨a, mem_primesUpTo.2 ha, by ring⟩
    · apply mem_union_left
      rw [mem_image]
      refine ⟨1 + b + a, ?_, by omega⟩
      simp only [mem_filter, mem_range]
      exact ⟨by omega, rep_one_add_add hb.2 ha.2 hab⟩
  calc #(P + P) ≤ #(((range (2 * Y + 1)).filter Rep).image (fun n => n - 1) ∪
        P.image (fun p => 2 * p)) := card_le_card hsub
    _ ≤ #(((range (2 * Y + 1)).filter Rep).image (fun n => n - 1)) +
        #(P.image (fun p => 2 * p)) := card_union_le _ _
    _ ≤ #((range (2 * Y + 1)).filter Rep) + #P := add_le_add card_image_le card_image_le

/-- The main inequality, valid for every `Y ≥ 2`. -/
lemma main_ineq (Y : ℕ) (hY : 2 ≤ Y) :
    (#(primesUpTo Y) : ℝ) ^ 4 ≤
      ((#((range (2 * Y + 1)).filter Rep) : ℝ) + #(primesUpTo Y)) *
        ((#(primesUpTo Y) : ℝ) ^ 2 + 2 ^ 57 * K₁ * (Y : ℝ) ^ 3 / (Real.log Y) ^ 4) := by
  classical
  have h1 := le_card_add_mul_addEnergy (primesUpTo Y) (primesUpTo Y)
  have h1' : (#(primesUpTo Y) : ℝ) ^ 4 ≤
      (#(primesUpTo Y + primesUpTo Y) : ℝ) * E[primesUpTo Y, primesUpTo Y] := by
    have : (#(primesUpTo Y) : ℝ) ^ 2 * (#(primesUpTo Y) : ℝ) ^ 2 ≤
        (#(primesUpTo Y + primesUpTo Y) : ℝ) * E[primesUpTo Y, primesUpTo Y] := by
      exact_mod_cast h1
    calc (#(primesUpTo Y) : ℝ) ^ 4 = (#(primesUpTo Y) : ℝ) ^ 2 * (#(primesUpTo Y) : ℝ) ^ 2 := by
          ring
      _ ≤ _ := this
  have h2 : (#(primesUpTo Y + primesUpTo Y) : ℝ) ≤
      (#((range (2 * Y + 1)).filter Rep) : ℝ) + #(primesUpTo Y) := by
    exact_mod_cast card_sumset_le Y
  have h3 := energy_le_real Y hY
  calc (#(primesUpTo Y) : ℝ) ^ 4
      ≤ (#(primesUpTo Y + primesUpTo Y) : ℝ) * E[primesUpTo Y, primesUpTo Y] := h1'
    _ ≤ _ := by
        apply mul_le_mul h2 h3 (by positivity) (by positivity)

end ErdosLean.Erdos1054

end Goldbach

/- ### Part `Main` -/

section Main
/-
# Erdős Problem 1054 (ii) is false as formalised

The prefix sums of divisors have positive lower density (`rep_density`), while those `n` with
`f n ≤ δ n` have upper density `O(δ²)` (`card_small_le`). Hence no set of density one can satisfy
`f n = o(n)`.
-/

open Finset Real Filter Asymptotics

open Erdos1054

namespace ErdosLean.Erdos1054

lemma K₁_pos : 0 < K₁ := Real.exp_pos _

lemma eventually_log_succ_le {a : ℝ} (ha : 0 < a) :
    ∀ᶠ Y : ℕ in atTop, Real.log ((Y : ℝ) + 1) ≤ a * Y := by
  have h1 := (Real.isLittleO_log_id_atTop).def (show 0 < a / 2 by positivity)
  have h2 : Tendsto (fun Y : ℕ => (Y : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  filter_upwards [h2.eventually h1, eventually_ge_atTop 1] with Y hY hY1
  have hY1' : (1 : ℝ) ≤ Y := by exact_mod_cast hY1
  have hlog : Real.log ((Y : ℝ) + 1) ≤ ‖Real.log ((Y : ℝ) + 1)‖ := le_abs_self _
  have hn : ‖id ((Y : ℝ) + 1)‖ = (Y : ℝ) + 1 := by
    simp only [id, Real.norm_eq_abs]; exact abs_of_pos (by positivity)
  rw [hn] at hY
  nlinarith

lemma eventually_log_pow_le :
    ∀ᶠ Y : ℕ in atTop, Real.log (Y : ℝ) ^ 4 ≤ Y := by
  have h1 := (Real.isLittleO_pow_log_id_atTop (n := 4)).def (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h1] with Y hY
  have hn : ‖id (Y : ℝ)‖ = Y := by simp
  rw [hn, one_mul] at hY
  exact (le_abs_self _).trans hY

/-- The prefix sums of divisors have positive lower density. -/
lemma rep_density : ∃ c > 0, ∃ Y₀ : ℕ, ∀ Y ≥ Y₀,
    c * Y ≤ (#((range (2 * Y + 1)).filter Rep) : ℝ) := by
  set a : ℝ := Real.log 2 / 2 with ha
  have ha0 : 0 < a := by have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity
  set C₂ : ℝ := 1 + 2 ^ 57 * K₁ with hC₂
  have hC₂0 : 0 < C₂ := by have := K₁_pos; positivity
  set c : ℝ := a ^ 4 / (2 * C₂) with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c, hc0, ?_⟩
  have E1 := eventually_log_succ_le ha0
  have E3 := eventually_log_pow_le
  have E4a : ∀ᶠ Y : ℕ in atTop, 4 * Real.log 4 / c ≤ Real.log (Y : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have E4b : ∀ᶠ Y : ℕ in atTop, 4 / c ^ 2 ≤ (Y : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1
    (E1.and (E3.and (E4a.and (E4b.and (eventually_ge_atTop 3)))))
  refine ⟨Y₀, fun Y hY => ?_⟩
  obtain ⟨e1, e3, e4a, e4b, hY3⟩ := hY₀ Y hY
  have hYR : (3 : ℝ) ≤ Y := by exact_mod_cast hY3
  have hY0 : (0 : ℝ) < Y := by linarith
  have hL : 0 < Real.log (Y : ℝ) := Real.log_pos (by linarith)
  set L := Real.log (Y : ℝ) with hLdef
  set π' : ℝ := ((#(primesUpTo Y) : ℕ) : ℝ) with hπ'
  set R : ℝ := ((#((range (2 * Y + 1)).filter Rep) : ℕ) : ℝ) with hR
  have hπ0 : 0 ≤ π' := by positivity
  have hR0 : 0 ≤ R := by positivity
  -- Chebyshev's lower bound
  have hlow : a * Y / L ≤ π' := by
    have := Chebyshev.pi_ge Y
    rw [hπ', card_primesUpTo]
    refine le_trans ?_ this
    apply div_le_div_of_nonneg_right _ hL.le
    have : Real.log 2 * Y - a * Y = a * Y := by rw [ha]; ring
    nlinarith
  -- Chebyshev's upper bound
  have hup : π' ≤ c * Y := by
    have h := Chebyshev.pi_le_log4_mul_div (x := (Y : ℝ)) (by linarith)
    rw [Nat.floor_natCast] at h
    rw [hπ', card_primesUpTo]
    refine h.trans ?_
    have hs : Real.log (Real.sqrt Y) = L / 2 := by
      rw [Real.log_sqrt hY0.le]
    rw [hs]
    have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have t1 : Real.log 4 * Y / (L / 2) ≤ c / 2 * Y := by
      rw [div_le_iff₀ (by positivity)]
      have : 4 * Real.log 4 ≤ c * L := by
        have := e4a
        rw [div_le_iff₀ hc0] at this
        linarith
      nlinarith
    have t2 : Real.sqrt Y ≤ c / 2 * Y := by
      have hsq : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY0.le
      have hs0 : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
      have : 2 / c ≤ Real.sqrt Y := by
        rw [Real.le_sqrt (by positivity) hY0.le]
        rw [div_pow]
        calc (2 : ℝ) ^ 2 / c ^ 2 = 4 / c ^ 2 := by norm_num
          _ ≤ (Y : ℝ) := e4b
      have : 2 ≤ c * Real.sqrt Y := by
        rw [div_le_iff₀ hc0] at this; linarith
      nlinarith
    linarith
  -- the main inequality
  have hmain := main_ineq Y (by omega)
  rw [← hπ', ← hR, ← hLdef] at hmain
  have hL4 : 0 < L ^ 4 := by positivity
  have hY2 : π' ^ 2 ≤ (Y : ℝ) ^ 3 / L ^ 4 := by
    have hπY : π' ≤ Y := by
      have : #(primesUpTo Y) ≤ Y + 1 := by
        calc #(primesUpTo Y) ≤ #(range (Y + 1)) := card_filter_le _ _
          _ = Y + 1 := card_range _
      have hP1 : #(primesUpTo Y) ≤ Y := by
        have h0 : 0 ∉ primesUpTo Y := by simp [mem_primesUpTo, Nat.not_prime_zero]
        have : primesUpTo Y ⊆ (range (Y + 1)).erase 0 := by
          intro p hp
          exact mem_erase.2 ⟨fun h => h0 (h ▸ hp), by
            simp only [mem_range]; exact Nat.lt_succ_of_le (mem_primesUpTo.1 hp).1⟩
        calc #(primesUpTo Y) ≤ #((range (Y + 1)).erase 0) := card_le_card this
          _ = Y := by rw [card_erase_of_mem (by simp), card_range]; rfl
      rw [hπ']; exact_mod_cast hP1
    rw [le_div_iff₀ hL4]
    calc π' ^ 2 * L ^ 4 ≤ (Y : ℝ) ^ 2 * Y := by
          apply mul_le_mul (by gcongr) e3 hL4.le (by positivity)
      _ = (Y : ℝ) ^ 3 := by ring
  have hB : π' ^ 2 + 2 ^ 57 * K₁ * (Y : ℝ) ^ 3 / L ^ 4 ≤ C₂ * ((Y : ℝ) ^ 3 / L ^ 4) := by
    rw [hC₂]
    have : 2 ^ 57 * K₁ * (Y : ℝ) ^ 3 / L ^ 4 = 2 ^ 57 * K₁ * ((Y : ℝ) ^ 3 / L ^ 4) := by ring
    rw [this]
    linarith
  have hπ4 : (a * Y / L) ^ 4 ≤ π' ^ 4 := by
    gcongr
  have key : (a * Y / L) ^ 4 ≤ (R + π') * (C₂ * ((Y : ℝ) ^ 3 / L ^ 4)) :=
    hπ4.trans (hmain.trans (mul_le_mul_of_nonneg_left hB (by positivity)))
  have key' : a ^ 4 * Y ≤ (R + π') * C₂ := by
    have e : (a * Y / L) ^ 4 = a ^ 4 * Y * ((Y : ℝ) ^ 3 / L ^ 4) := by
      field_simp
    rw [e] at key
    have hpos : 0 < (Y : ℝ) ^ 3 / L ^ 4 := by positivity
    have : a ^ 4 * Y * ((Y : ℝ) ^ 3 / L ^ 4) ≤ (R + π') * C₂ * ((Y : ℝ) ^ 3 / L ^ 4) := by
      linarith [key]
    exact le_of_mul_le_mul_right this hpos
  have : 2 * c * Y ≤ R + π' := by
    rw [hc]
    rw [show 2 * (a ^ 4 / (2 * C₂)) * (Y : ℝ) = a ^ 4 * Y / C₂ by field_simp]
    rw [div_le_iff₀ hC₂0]
    linarith
  linarith

open Classical in
/-- The partial density of a set of naturals, as a finset count. -/
lemma partialDensity_eq (A : Set ℕ) (b : ℕ) :
    A.partialDensity Set.univ b = (#((range b).filter (· ∈ A)) : ℝ) / b := by
  classical
  unfold Set.partialDensity
  congr 1
  · congr 1
    rw [← Set.ncard_coe_finset]
    congr 1
    ext n
    simp [and_comm]
  · congr 1
    rw [Set.univ_inter, Set.ncard_eq_toFinset_card']
    simp

/-- **Erdős Problem 1054 (ii), as formalised, is false.** -/
theorem not_parts_ii : ¬ ∃ (A : Set ℕ), A.HasDensity 1 ∧
    (fun (n : A) ↦ (f ↑n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ)) := by
  classical
  rintro ⟨A, hA, ho⟩
  obtain ⟨c, hc, Y₀, hY₀⟩ := rep_density
  -- parameters
  set η : ℝ := c / 12 with hη
  have hη0 : 0 < η := by positivity
  have hK := K₀_nonneg
  set δ : ℝ := c / (12 * (K₀ + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hKδ : K₀ * δ ^ 2 / η ≤ c / 12 := by
    rw [div_le_iff₀ hη0, hδ, hη]
    have h1 : K₀ / (K₀ + 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have : K₀ * (c / (12 * (K₀ + 1))) ^ 2 = c ^ 2 / 144 * (K₀ / (K₀ + 1) ^ 2) := by
      field_simp; ring
    rw [this]
    have : c ^ 2 / 144 * (K₀ / (K₀ + 1) ^ 2) ≤ c ^ 2 / 144 * 1 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  -- `f n ≤ δ n` for all large `n ∈ A`
  have hne : Nonempty A := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have hA0 : A = ∅ := Set.eq_empty_of_isEmpty A
    unfold Set.HasDensity at hA
    rw [hA0] at hA
    have : (fun b : ℕ => (∅ : Set ℕ).partialDensity Set.univ b) = fun _ => 0 := by
      funext b; simp [Set.partialDensity]
    rw [this] at hA
    exact one_ne_zero (tendsto_nhds_unique hA tendsto_const_nhds)
  obtain ⟨a₀, ha₀⟩ := eventually_atTop.1 (ho.def hδ0)
  set N₀ : ℕ := a₀.1 with hN₀
  have hsmall : ∀ n ∈ A, N₀ ≤ n → (f n : ℝ) ≤ δ * n := by
    intro n hn hle
    have := ha₀ ⟨n, hn⟩ hle
    simpa [Real.norm_eq_abs, abs_of_nonneg] using this
  -- the density of `A` is eventually close to one
  have hdens : ∀ᶠ b : ℕ in atTop, 1 - c / 12 ≤ (#((range b).filter (· ∈ A)) : ℝ) / b := by
    have := (hA.eventually (Ioi_mem_nhds (show 1 - c / 12 < 1 by linarith)))
    filter_upwards [this] with b hb
    rw [← partialDensity_eq]; exact (Set.mem_Ioi.1 hb).le
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.1 hdens
  -- choose a large `Y`
  set Y : ℕ := max (max Y₀ B₀) ⌈24 * ((N₀ : ℝ) + 1) / c⌉₊ with hY
  set b : ℕ := 2 * Y + 1 with hb
  have hYY₀ : Y₀ ≤ Y := le_trans (le_max_left _ _) (le_max_left _ _)
  have hbB : B₀ ≤ b := by
    have : B₀ ≤ Y := le_trans (le_max_right _ _) (le_max_left _ _)
    omega
  have hYN : 24 * ((N₀ : ℝ) + 1) / c ≤ Y := by
    have : ⌈24 * ((N₀ : ℝ) + 1) / c⌉₊ ≤ Y := le_max_right _ _
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le (by positivity) hYN
  have hY1 : (1 : ℝ) ≤ Y := by
    have : 0 < Y := by exact_mod_cast hYpos
    exact_mod_cast this
  have hbR : (b : ℝ) = 2 * Y + 1 := by rw [hb]; push_cast; ring
  have hb0 : (0 : ℝ) < b := by rw [hbR]; positivity
  have hrep := hY₀ Y hYY₀
  have hd := hB₀ b hbB
  rw [le_div_iff₀ hb0] at hd
  -- split `A ∩ [0, b)`
  set S₁ := (range b).filter (fun n => n < N₀)
  set S₂ := (range b).filter (fun n : ℕ => (n : ℝ) < η * b)
  set S₃ := (range b).filter (fun n => ¬ Rep n)
  set S₄ := (range b).filter (fun n : ℕ => η * b ≤ (n : ℝ) ∧ Rep n ∧ (f n : ℝ) ≤ δ * n)
  have hsplit : (range b).filter (· ∈ A) ⊆ S₁ ∪ S₂ ∪ S₃ ∪ S₄ := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    simp only [S₁, S₂, S₃, S₄, mem_union, mem_filter, mem_range]
    by_cases h1 : n < N₀
    · exact Or.inl (Or.inl (Or.inl ⟨hn.1, h1⟩))
    by_cases h2 : (n : ℝ) < η * b
    · exact Or.inl (Or.inl (Or.inr ⟨hn.1, h2⟩))
    by_cases h3 : Rep n
    · exact Or.inr ⟨hn.1, not_lt.1 h2, h3, hsmall n hn.2 (not_lt.1 h1)⟩
    · exact Or.inl (Or.inr ⟨hn.1, h3⟩)
  have c1 : (#S₁ : ℝ) ≤ N₀ := by
    have : S₁ ⊆ range N₀ := fun n hn => by
      simp only [S₁, mem_filter, mem_range] at hn ⊢; exact hn.2
    exact_mod_cast (card_le_card this).trans (card_range _).le
  have c2 : (#S₂ : ℝ) ≤ η * b + 1 := by
    have : S₂ ⊆ range ⌈η * b⌉₊ := fun n hn => by
      simp only [S₂, mem_filter, mem_range] at hn ⊢
      exact Nat.lt_ceil.2 hn.2
    have h := card_le_card this
    rw [card_range] at h
    have h' : (⌈η * b⌉₊ : ℝ) < η * b + 1 := Nat.ceil_lt_add_one (by positivity)
    have : (#S₂ : ℝ) ≤ ⌈η * b⌉₊ := by exact_mod_cast h
    linarith
  have c3 : (#S₃ : ℝ) + #((range b).filter Rep) = b := by
    have := card_filter_add_card_filter_not (s := range b) Rep
    rw [card_range] at this
    have e : #S₃ = #((range b).filter fun n => ¬ Rep n) := rfl
    rw [e]
    exact_mod_cast (by omega : #((range b).filter fun n => ¬ Rep n) + #((range b).filter Rep) = b)
  have c4 : (#S₄ : ℝ) ≤ K₀ * δ ^ 2 * b / η := by
    have := card_small_le b hη0 hδ0
    convert this using 3
  have hrepb : c / 3 * b ≤ (#((range b).filter Rep) : ℝ) := by
    have : c * Y ≤ (#((range (2 * Y + 1)).filter Rep) : ℝ) := hrep
    rw [← hb] at this
    have : c / 3 * b ≤ c * Y := by
      rw [hbR]
      have : c / 3 * (2 * (Y : ℝ) + 1) ≤ c / 3 * (3 * Y) := by gcongr; linarith
      linarith
    linarith
  have hcard : (#((range b).filter (· ∈ A)) : ℝ) ≤ #S₁ + #S₂ + #S₃ + #S₄ := by
    have h := card_le_card hsplit
    have h' : #(S₁ ∪ S₂ ∪ S₃ ∪ S₄) ≤ #S₁ + #S₂ + #S₃ + #S₄ := by
      calc #(S₁ ∪ S₂ ∪ S₃ ∪ S₄) ≤ #(S₁ ∪ S₂ ∪ S₃) + #S₄ := card_union_le _ _
        _ ≤ #(S₁ ∪ S₂) + #S₃ + #S₄ := by gcongr; exact card_union_le _ _
        _ ≤ #S₁ + #S₂ + #S₃ + #S₄ := by gcongr; exact card_union_le _ _
    exact_mod_cast h.trans h'
  have hc4' : (#S₄ : ℝ) ≤ c / 12 * b := by
    calc (#S₄ : ℝ) ≤ K₀ * δ ^ 2 * b / η := c4
      _ = K₀ * δ ^ 2 / η * b := by ring
      _ ≤ c / 12 * b := by gcongr
  -- combine
  have hfin : c / 12 * b ≤ N₀ + 1 := by
    have e1 : (#S₃ : ℝ) ≤ b - c / 3 * b := by linarith
    have e2 : (1 - c / 12) * b ≤ N₀ + (η * b + 1) + (b - c / 3 * b) + c / 12 * b := by
      calc (1 - c / 12) * b ≤ (#((range b).filter (· ∈ A)) : ℝ) := hd
        _ ≤ #S₁ + #S₂ + #S₃ + #S₄ := hcard
        _ ≤ N₀ + (η * b + 1) + (b - c / 3 * b) + c / 12 * b := by
          gcongr
    rw [hη] at e2
    linarith
  have hbig : (N₀ : ℝ) + 1 < c / 12 * b := by
    have hN : (0 : ℝ) ≤ N₀ := by positivity
    have h2 : c / 6 * (24 * ((N₀ : ℝ) + 1) / c) = 4 * ((N₀ : ℝ) + 1) := by
      field_simp; ring
    have h3 : c / 6 * (24 * ((N₀ : ℝ) + 1) / c) ≤ c / 6 * Y := by gcongr
    have h4 : c / 6 * (Y : ℝ) ≤ c / 12 * b := by
      rw [hbR]; nlinarith
    linarith
  linarith

/-- The repository statement, with the answer `False` filled in. -/
theorem erdos_1054_parts_ii_answer : False ↔ ∃ (A : Set ℕ), A.HasDensity 1 ∧
    (fun (n : A) ↦ (f ↑n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ)) :=
  ⟨False.elim, fun h => not_parts_ii h⟩

end ErdosLean.Erdos1054

end Main

/- ### The repository statement -/

open Erdos1054

namespace ErdosLean.Erdos1054

open Filter Asymptotics

/-- The statement in the repository elaborates `answer(sorry)` to `True`; it is false. -/
theorem erdos_1054_parts_ii_false : ¬ (type_of% _root_.Erdos1054.erdos_1054.parts.ii) := by
  intro h
  exact not_parts_ii (h.mp trivial)

/-- The repository statement with the answer filled in as `False`. -/
theorem erdos_1054_parts_ii_solution : answer(False) ↔ ∃ (A : Set ℕ), A.HasDensity 1 ∧
    (fun (n : A) ↦ (f ↑n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ)) :=
  erdos_1054_parts_ii_answer

end ErdosLean.Erdos1054
