import FormalConjectures.ErdosProblems.«382»

/-!
# Erdős Problem 382, a bad interval with `v - u = 17`

We prove `erdos_382.variants.width_17`, that is,
`Erdos382.LargestPrimeRepeated 12339873448110272 12339873448110289`. The largest prime dividing
`∏ m ∈ [12339873448110272, 12339873448110289], m` is `p = 111084983`, and `p ^ 2` divides the
product, since `12339873448110289 = p ^ 2`.

The proof is a factorization certificate. Each of the 18 integers in the interval is written as a
product of primes that are at most `p`, and each of these primes is certified by `norm_num`. So
every prime factor of the product is at most `p`, and `p` divides the product, so `p` is its
largest prime factor. No `native_decide` is used.

The statement uses `Erdos382.LargestPrimeRepeated` from formal-conjectures at the pinned commit,
and its type is the type of the proposed formal-conjectures statement
`Erdos382.erdos_382.variants.width_17`, which is not in formal-conjectures at the pinned commit.
-/

namespace ErdosLean.Erdos382

/-- Every prime factor of `n` is at most `p`. -/
def Smooth (p n : ℕ) : Prop := ∀ q : ℕ, q.Prime → q ∣ n → q ≤ p

/-- A product of primes that are at most `p` is `p`-smooth. -/
lemma smooth_list_prod (p : ℕ) (l : List ℕ) (h : ∀ r ∈ l, r.Prime ∧ r ≤ p) :
    Smooth p l.prod := by
  induction l with
  | nil =>
    intro q hq hd
    exact absurd (Nat.dvd_one.1 (by simpa using hd)) hq.ne_one
  | cons a l ih =>
    intro q hq hd
    rw [List.prod_cons] at hd
    have ha : a.Prime ∧ a ≤ p := h a (by simp)
    rcases (Nat.Prime.dvd_mul hq).1 hd with h1 | h1
    · rw [(Nat.prime_dvd_prime_iff_eq hq ha.1).1 h1]
      exact ha.2
    · exact ih (fun r hr => h r (List.mem_cons_of_mem a hr)) q hq h1

/-- A factorization certificate: if `n` is a product of primes that are at most `p`, then `n` is
`p`-smooth. -/
lemma smooth_of_list_prod_eq {p n : ℕ} (l : List ℕ) (hl : l.prod = n)
    (h : ∀ r ∈ l, r.Prime ∧ r ≤ p) : Smooth p n :=
  hl ▸ smooth_list_prod p l h

/-- Every integer in `[12339873448110272, 12339873448110289]` is `111084983`-smooth. -/
lemma smooth_of_mem {m : ℕ} (hm : m ∈ Finset.Icc 12339873448110272 12339873448110289) :
    Smooth 111084983 m := by
  rw [Finset.mem_Icc] at hm
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < 18 ∧ m = 12339873448110272 + i :=
    ⟨m - 12339873448110272, by omega, by omega⟩
  interval_cases i
  · exact smooth_of_list_prod_eq [2, 2, 2, 2, 2, 2, 127, 414503, 3662683] (by norm_num) (by norm_num)
  · exact smooth_of_list_prod_eq [3, 13, 17, 53, 131, 1279, 2095943] (by norm_num) (by norm_num)
  · exact smooth_of_list_prod_eq [2, 11, 11, 478063, 106662119] (by norm_num) (by norm_num)
  · exact smooth_of_list_prod_eq [5, 5, 101, 5483, 16843, 52919] (by norm_num) (by norm_num)
  · exact smooth_of_list_prod_eq [2, 2, 3, 29, 4387367, 8082161] (by norm_num) (by norm_num)
  · exact smooth_of_list_prod_eq [13451, 298799, 3070273] (by norm_num) (by norm_num)
  · exact smooth_of_list_prod_eq [2, 7, 1451, 9377, 64781551] (by norm_num) (by norm_num)
  · exact smooth_of_list_prod_eq [3, 3, 31, 67, 107, 409, 15084281] (by norm_num) (by norm_num)
  · exact smooth_of_list_prod_eq [2, 2, 2, 5, 23, 1549, 1559, 5554249] (by norm_num) (by norm_num)
  · exact smooth_of_list_prod_eq [41, 743, 14489, 27957583] (by norm_num) (by norm_num)
  · exact smooth_of_list_prod_eq [2, 3, 59, 277, 22699, 5543971] (by norm_num) (by norm_num)
  · exact smooth_of_list_prod_eq [149, 3268103, 25341289] (by norm_num) (by norm_num)
  · exact smooth_of_list_prod_eq [2, 2, 44332831, 69586541] (by norm_num) (by norm_num)
  · exact smooth_of_list_prod_eq [3, 5, 7, 11, 79, 103, 19609, 66959] (by norm_num) (by norm_num)
  · exact smooth_of_list_prod_eq [2, 13, 1187, 21397, 18686749] (by norm_num) (by norm_num)
  · exact smooth_of_list_prod_eq [599, 195127, 105576319] (by norm_num) (by norm_num)
  · exact smooth_of_list_prod_eq [2, 2, 2, 2, 3, 3, 19, 97, 199, 7753, 30137] (by norm_num) (by norm_num)
  · exact smooth_of_list_prod_eq [111084983, 111084983] (by norm_num) (by norm_num)

/-- The interval `[12339873448110272, 12339873448110289]`, with `v - u = 17`, satisfies
`Erdos382.LargestPrimeRepeated`: its largest prime is `111084983`, and `111084983 ^ 2` is the
right endpoint. -/
theorem erdos_382.variants.width_17 :
    Erdos382.LargestPrimeRepeated 12339873448110272 12339873448110289 := by
  have hp : Nat.Prime 111084983 := by norm_num
  have hv : (111084983 : ℕ) ^ 2 = 12339873448110289 := by norm_num
  have hvmem : 12339873448110289 ∈ Finset.Icc 12339873448110272 12339873448110289 :=
    Finset.mem_Icc.2 ⟨by norm_num, le_rfl⟩
  have hvdvd : 12339873448110289 ∣ ∏ m ∈ Finset.Icc 12339873448110272 12339873448110289, m :=
    Finset.dvd_prod_of_mem _ hvmem
  have hN0 : ∏ m ∈ Finset.Icc 12339873448110272 12339873448110289, m ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun m hm => by
      have := (Finset.mem_Icc.1 hm).1
      omega
  have hpdvd : 111084983 ∣ ∏ m ∈ Finset.Icc 12339873448110272 12339873448110289, m :=
    (Dvd.intro_left _ (by rw [← hv, pow_two])).trans hvdvd
  have h1 : 1 < ∏ m ∈ Finset.Icc 12339873448110272 12339873448110289, m :=
    lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hpdvd)
  have hmax :
      Nat.maxPrimeFac (∏ m ∈ Finset.Icc 12339873448110272 12339873448110289, m) = 111084983 := by
    apply le_antisymm
    · have hq := Nat.prime_maxPrimeFac_of_one_lt _ h1
      obtain ⟨m, hm, hqm⟩ := (Prime.dvd_finsetProd_iff hq.prime _).1 Nat.maxPrimeFac_dvd
      exact smooth_of_mem hm _ hq hqm
    · exact Nat.le_maxPrimeFac hN0 hp hpdvd
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  rw [hmax, hv]
  exact hvdvd

end ErdosLean.Erdos382
