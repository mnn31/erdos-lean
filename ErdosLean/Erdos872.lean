import FormalConjectures.ErdosProblems.«872»

/-!
# Erdős Problem 872, prime variant

We prove `Erdos872.erdos_872.variants.prime_question`: every maximal primitive subset `A` of
`{2, ..., n}` has at least `π(n)` elements.

For a prime `q ≤ n` let `M q = q ^ Nat.log q n` be the largest power of `q` that is at most `n`.
Since `2 ≤ M q ≤ n`, maximality of `A` gives some `a ∈ A` with `a ∣ M q` or `M q ∣ a`. Sending `q`
to such an `a` is injective on the primes up to `n`:

* if `a ∣ M q`, every prime factor of `a` is `q`, which pins down `q`;
* if `M q ∣ a` and `M r ∣ a` for primes `q < r`, then `M q * M r ∣ a` by coprimality, but
  `M q * M r ≥ M q * (q + 1) > n ≥ a`, because `n < q * M q` and `q < r ≤ M r`.
-/

open Erdos872

namespace ErdosLean.Erdos872

/-- In a maximal primitive set, every `m ∈ {2, ..., n}` is comparable under divisibility with
some element of the set. -/
lemma exists_comparable {n : ℕ} {A : Finset ℕ} (hA : Maximal (IsPrimitive n) A) {m : ℕ}
    (hm : m ∈ Finset.Icc 2 n) : ∃ a ∈ A, a ∣ m ∨ m ∣ a := by
  by_cases hmA : m ∈ A
  · exact ⟨m, hmA, Or.inl dvd_rfl⟩
  by_contra h
  push Not at h
  have hP : IsPrimitive n (insert m A) := by
    refine ⟨Finset.insert_subset hm hA.1.1, ?_⟩
    intro a ha b hb hab
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact (h b hb).2
    · exact (h a ha).1
    · exact hA.1.2 a ha b hb hab
  exact hmA (hA.2 hP (Finset.subset_insert m A) (Finset.mem_insert_self m A))

/-- Every prime factor of a divisor of `q ^ k` is `q`. -/
lemma eq_of_dvd_of_dvd_pow {p q a k : ℕ} (hp : p.Prime) (hq : q.Prime) (hpa : p ∣ a)
    (ha : a ∣ q ^ k) : p = q :=
  (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow (hpa.trans ha))

/-- No `a ∈ {2, ..., n}` is comparable both with the largest power of `q` and with the largest
power of `r` not exceeding `n`, for distinct primes `q, r ≤ n`. -/
lemma not_comparable_both {n q r a : ℕ} (hq : q.Prime) (hr : r.Prime) (hqn : q ≤ n)
    (hrn : r ≤ n) (hqr : q ≠ r) (ha : 2 ≤ a) (han : a ≤ n)
    (hqa : a ∣ q ^ Nat.log q n ∨ q ^ Nat.log q n ∣ a)
    (hra : a ∣ r ^ Nat.log r n ∨ r ^ Nat.log r n ∣ a) : False := by
  have hq1 : 0 < Nat.log q n := Nat.log_pos hq.one_lt hqn
  have hr1 : 0 < Nat.log r n := Nat.log_pos hr.one_lt hrn
  have hqM : q ∣ q ^ Nat.log q n := dvd_pow_self q hq1.ne'
  have hrM : r ∣ r ^ Nat.log r n := dvd_pow_self r hr1.ne'
  have hpa : (Nat.minFac a).Prime := Nat.minFac_prime (by omega)
  rcases hqa with hqa | hqa <;> rcases hra with hra | hra
  · exact hqr ((eq_of_dvd_of_dvd_pow hpa hq (Nat.minFac_dvd a) hqa).symm.trans
      (eq_of_dvd_of_dvd_pow hpa hr (Nat.minFac_dvd a) hra))
  · exact hqr (eq_of_dvd_of_dvd_pow hr hq (hrM.trans hra) hqa).symm
  · exact hqr (eq_of_dvd_of_dvd_pow hq hr (hqM.trans hqa) hra)
  · -- Both prime powers divide `a`; they are coprime, so their product is at most `n`.
    have hcop : Nat.Coprime (q ^ Nat.log q n) (r ^ Nat.log r n) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hr).mpr hqr)
    have hprod : q ^ Nat.log q n * r ^ Nat.log r n ≤ n :=
      (Nat.le_of_dvd (by omega) (hcop.mul_dvd_of_dvd_of_dvd hqa hra)).trans han
    have hqbig : n < q ^ Nat.log q n * q := by
      have := Nat.lt_pow_succ_log_self hq.one_lt n
      rwa [pow_succ] at this
    have hrbig : n < r ^ Nat.log r n * r := by
      have := Nat.lt_pow_succ_log_self hr.one_lt n
      rwa [pow_succ] at this
    have hqle : q ≤ q ^ Nat.log q n := Nat.le_of_dvd (pow_pos hq.pos _) hqM
    have hrle : r ≤ r ^ Nat.log r n := Nat.le_of_dvd (pow_pos hr.pos _) hrM
    rcases lt_or_gt_of_ne hqr with h | h
    · have : q ^ Nat.log q n * q ≤ q ^ Nat.log q n * r ^ Nat.log r n :=
        Nat.mul_le_mul_left _ (h.le.trans hrle)
      omega
    · have : r ^ Nat.log r n * r ≤ q ^ Nat.log q n * r ^ Nat.log r n := by
        rw [mul_comm (q ^ Nat.log q n)]
        exact Nat.mul_le_mul_left _ (h.le.trans hqle)
      omega

/-- Every maximal primitive subset of `{2, ..., n}` has at least `π(n)` elements. -/
theorem card_primes_le {n : ℕ} {A : Finset ℕ} (hA : Maximal (IsPrimitive n) A) :
    ((Finset.Icc 2 n).filter Nat.Prime).card ≤ A.card := by
  have hw : ∀ q ∈ (Finset.Icc 2 n).filter Nat.Prime,
      ∃ a ∈ A, a ∣ q ^ Nat.log q n ∨ q ^ Nat.log q n ∣ a := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq2, hqn⟩, hqp⟩ := hq
    apply exists_comparable hA
    rw [Finset.mem_Icc]
    refine ⟨hq2.trans ?_, Nat.pow_log_le_self q (by omega)⟩
    exact Nat.le_of_dvd (pow_pos hqp.pos _) (dvd_pow_self q (Nat.log_pos hqp.one_lt hqn).ne')
  choose! f hfA hf using hw
  refine Finset.card_le_card_of_injOn f (by intro q hq; exact hfA q hq) ?_
  intro q hq r hr hfqr
  by_contra hqr
  have hq' : q ∈ (Finset.Icc 2 n).filter Nat.Prime := hq
  have hr' : r ∈ (Finset.Icc 2 n).filter Nat.Prime := hr
  have hfa := hA.1.1 (hfA q hq')
  simp only [Finset.mem_filter, Finset.mem_Icc] at hq' hr' hfa
  have hfr := hf r hr
  rw [← hfqr] at hfr
  exact not_comparable_both hq'.2 hr'.2 hq'.1.2 hr'.1.2 hqr hfa.1 hfa.2 (hf q hq) hfr

theorem prime_question : answer(True) ↔
    ∀ n ≥ 2, ∀ A : Finset ℕ, Maximal (IsPrimitive n) A →
      ((Finset.Icc 2 n).filter Nat.Prime).card ≤ A.card :=
  ⟨fun _ _ _ _ hA => card_primes_le hA, fun _ => trivial⟩

/-- The repository statement `Erdos872.erdos_872.variants.prime_question`, with its exact type. -/
theorem erdos_872_variants_prime_question :
    type_of% Erdos872.erdos_872.variants.prime_question :=
  prime_question

end ErdosLean.Erdos872
