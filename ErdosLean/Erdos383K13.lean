import FormalConjecturesForMathlib.Data.Nat.MaxPrimeFac
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Associated

/-!
# Erdős Problem 383: a witness for `k = 13`

Problem 383 asks whether for every `k` there are infinitely many primes `p` such that the largest
prime divisor of `∏_{i = 0}^{k} (p ^ 2 + i)` is `p`. We prove the finite instance with `k = 13`:
the set of such primes is nonempty (`erdos_383.variants.k_eq_13`). The witness is
`p = 169638367`. This says nothing about the infinitude asked for in the problem.

The statement is not in formal-conjectures at the commit pinned in `lakefile.toml`, so it is copied
verbatim from the proposed variant in `FormalConjectures/ErdosProblems/383.lean`. It uses only
`Nat.maxPrimeFac` from `FormalConjecturesForMathlib` at the pinned commit.

Proof. `p` is prime (`norm_num`). The `i = 0` factor `p ^ 2` gives `p ∣ ∏`, so the largest prime
divisor is at least `p`. For `i = 0, …, 13` the number `p ^ 2 + i` is written explicitly as a
product of integers in `[1, p]`, and each identity is checked by `norm_num`. A prime dividing a
product of such integers divides one of them, so it is at most `p`. Hence every prime divisor of
the whole product, in particular the largest one, is at most `p`.
-/

namespace ErdosLean.Erdos383K13

/-- A prime dividing the product of a list of integers in `[1, p]` is at most `p`. -/
lemma le_of_dvd_prod {p q : ℕ} (hq : q.Prime) :
    ∀ L : List ℕ, (∀ a ∈ L, 0 < a ∧ a ≤ p) → q ∣ L.prod → q ≤ p
  | [], _, h => absurd (Nat.dvd_one.mp (by simpa using h)) hq.ne_one
  | a :: L, hL, h => by
    rw [List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · exact (Nat.le_of_dvd (hL a (by simp)).1 h).trans (hL a (by simp)).2
    · exact le_of_dvd_prod hq L (fun b hb => hL b (by simp [hb])) h

/-- Every prime divisor of `169638367 ^ 2 + i`, `0 ≤ i ≤ 13`, is at most `169638367`, by an
explicit factorization of `169638367 ^ 2 + i` into integers in `[1, 169638367]`. -/
lemma le_of_dvd_sq_add {i q : ℕ} (hi : i ≤ 13) (hq : q.Prime) (h : q ∣ 169638367 ^ 2 + i) :
    q ≤ 169638367 := by
  interval_cases i
  · exact le_of_dvd_prod hq [169638367, 169638367] (by norm_num)
      (h.trans (dvd_of_eq (by norm_num)))
  · exact le_of_dvd_prod hq [2, 5, 461, 557, 19577, 572461] (by norm_num)
      (h.trans (dvd_of_eq (by norm_num)))
  · exact le_of_dvd_prod hq [3, 3, 11, 3169, 4787, 19161403] (by norm_num)
      (h.trans (dvd_of_eq (by norm_num)))
  · exact le_of_dvd_prod hq [2, 2, 43, 27919, 36997, 161977] (by norm_num)
      (h.trans (dvd_of_eq (by norm_num)))
  · exact le_of_dvd_prod hq [17, 31737197, 53337257] (by norm_num)
      (h.trans (dvd_of_eq (by norm_num)))
  · exact le_of_dvd_prod hq [2, 3, 7, 41, 5569, 9421, 318523] (by norm_num)
      (h.trans (dvd_of_eq (by norm_num)))
  · exact le_of_dvd_prod hq [5, 11717, 63773, 7702379] (by norm_num)
      (h.trans (dvd_of_eq (by norm_num)))
  · exact le_of_dvd_prod hq [2, 2, 2, 23, 1373, 1831, 62211613] (by norm_num)
      (h.trans (dvd_of_eq (by norm_num)))
  · exact le_of_dvd_prod hq [3, 137, 2652883, 26392969] (by norm_num)
      (h.trans (dvd_of_eq (by norm_num)))
  · exact le_of_dvd_prod hq [2, 13, 4153, 17977, 14825033] (by norm_num)
      (h.trans (dvd_of_eq (by norm_num)))
  · exact le_of_dvd_prod hq [9371, 20011, 153459379] (by norm_num)
      (h.trans (dvd_of_eq (by norm_num)))
  · exact le_of_dvd_prod hq [2, 2, 3, 3, 5, 5, 31, 37, 683, 2069, 19727] (by norm_num)
      (h.trans (dvd_of_eq (by norm_num)))
  · exact le_of_dvd_prod hq [7, 7, 331, 501427, 3538477] (by norm_num)
      (h.trans (dvd_of_eq (by norm_num)))
  · exact le_of_dvd_prod hq [2, 11, 29, 691129, 65263201] (by norm_num)
      (h.trans (dvd_of_eq (by norm_num)))

/-- The statement, copied verbatim from the proposed formal-conjectures variant. -/
theorem erdos_383.variants.k_eq_13 :
    {p : ℕ | p.Prime ∧ Nat.maxPrimeFac (∏ i ∈ Finset.Icc 0 13, (p ^ 2 + i)) = p}.Nonempty := by
  refine ⟨169638367, by norm_num, ?_⟩
  have hpos : 0 < ∏ i ∈ Finset.Icc 0 13, ((169638367 : ℕ) ^ 2 + i) :=
    Finset.prod_pos fun i _ => by positivity
  have hdvd : 169638367 ∣ ∏ i ∈ Finset.Icc 0 13, ((169638367 : ℕ) ^ 2 + i) :=
    (Dvd.intro 169638367 (by norm_num)).trans
      (Finset.dvd_prod_of_mem (fun i => (169638367 : ℕ) ^ 2 + i)
        (by simp : 0 ∈ Finset.Icc 0 13))
  have hone : 1 < ∏ i ∈ Finset.Icc 0 13, ((169638367 : ℕ) ^ 2 + i) :=
    lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd hpos hdvd)
  refine Nat.maxPrimeFac_eq_of_dvd_of_le _ _ hpos (by norm_num) hdvd ?_
  have hq := Nat.prime_maxPrimeFac_of_one_lt _ hone
  obtain ⟨i, hi, hqi⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp Nat.maxPrimeFac_dvd
  exact le_of_dvd_sq_add (Finset.mem_Icc.mp hi).2 hq hqi

end ErdosLean.Erdos383K13
