import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import FormalConjecturesForMathlib.Combinatorics.AP.Basic
import FormalConjectures.ErdosProblems.«3»

/-!
# Erdős Problems 3 and 169: the uniform tail question at a fixed length `k`

In [Er80, p. 92] Erdős asks (erdosproblems.com/169, last paragraph): for every `ε > 0` and
`k ≥ 3`, if `A` is a set of positive integers with no `k`-term arithmetic progression and `min A`
is large enough in terms of `ε` and `k`, is `∑_{n ∈ A} 1/n < ε`?

We prove `erdos_3.variants.uniform_tail_iff`: for each fixed `k ≥ 3`, this uniform tail property
at `k` is equivalent to Erdős Problem 3 at `k` (every set with divergent reciprocal sum contains a
`k`-term progression). This is known: Pal (arXiv:math/0703467, 2007, Lemma 5) proves that Problem 3
at `k` implies the tail property at `k`, and Gerver (Proc. AMS 62, 1977) proves the all-`k`
equivalence. The proof here is short and elementary. Write `r_k(n)` for the largest size of a
`k`-AP-free subset of `[1, n]`.

1. Translation: a `k`-AP-free subset of `n` consecutive integers has at most `r_k(n)` elements
   (`card_le_extremalNumber`, `card_le_mul_extremalNumber`).
2. Dyadic tail: a `k`-AP-free set `A` with `min A ≥ 4^J` has reciprocal sum at most
   `∑_{j ≥ J} 3 r_k(4^j) / 4^j` (`finite_sum_le_tail`). So if `∑_j r_k(4^j) / 4^j` converges, the
   tail property holds (`tailAt_of_dyadicAt`).
3. Windows: put an extremal `k`-AP-free set `S_j ⊆ [1, 4^j]` into the window
   `[2·4^j, 3·4^j - 1]`. Every 3-term progression of the union lies in one window
   (`triple_same_window`), so the union is `k`-AP-free for `k ≥ 3` (`winSet_apFree`), and its
   reciprocal sum is at least `∑_j r_k(4^j) / (3·4^j)` (`summable_card_of_summable_winSet`). So
   Problem 3 at `k` gives convergence of `∑_j r_k(4^j) / 4^j` (`dyadicAt_of_reciprocalAt`).
4. The tail property at `k` gives Problem 3 at `k`: the finitely many elements below the threshold
   add a finite amount (`reciprocalAt_of_tailAt`).

Two consequences are stated as conditional variants, as in formal-conjectures:
`erdos_3.variants.uniform_tail_three` takes `erdos_3.variants.kelley_meka` as a hypothesis (via
`type_of%`) and gives the tail property at `k = 3` through step 2 directly.
`erdos_3.variants.uniform_tail` takes the statement of `erdos_3` as a hypothesis and gives the
tail property for every `k ≥ 3`, which is the question of [Er80]. We also prove the converse,
`erdos_3_of_uniform_tail`.

The three statements are not in formal-conjectures at the commit pinned in `lakefile.toml`, so they
are copied verbatim from the proposed variants in `FormalConjectures/ErdosProblems/3.lean`. The
hypothesis of `uniform_tail` is the statement of `erdos_3` at formal-conjectures commit
`9097e2f9` (at the pinned commit it still carries `answer(True) ↔`), copied verbatim.

Internally we work with `HasAP`/`APFree` (a progression `a, a + d, …, a + (k-1) d` with `d > 0`)
and bridge to `Set.IsAPOfLength`/`Set.IsAPOfLengthFree` for `k ≥ 2`
(`isAPOfLengthFree_iff_apFree`).
-/

namespace ErdosLean.Erdos169Er80

open scoped BigOperators
open Finset Filter Topology Asymptotics

/- ### Definitions -/

/-- `A` contains `a, a + d, …, a + (k - 1) d` for some `d > 0`. -/
def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- `A` contains no `k`-term progression with positive difference. -/
def APFree (A : Set ℕ) (k : ℕ) : Prop := ¬ HasAP A k

/-- `r_k(N)`: the largest size of a `k`-AP-free subset of `[1, N]`. -/
noncomputable def extremalNumber (k N : ℕ) : ℕ := by
  classical
  exact (((Finset.Icc 1 N).powerset).filter fun S : Finset ℕ ↦ APFree (S : Set ℕ) k).sup
    Finset.card

/-- `1/n` if `n ∈ A`, else `0`. -/
noncomputable def reciprocalTerm (A : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact if n ∈ A then (n : ℝ)⁻¹ else 0

/- ### The three properties at a fixed `k` -/

/-- Erdős Problem 3 at length `k`. -/
def ReciprocalAt (k : ℕ) : Prop :=
  ∀ A : Set ℕ, APFree A k → Summable (reciprocalTerm A)

/-- Summability of `r_k(4^j)/4^j`. -/
def DyadicAt (k : ℕ) : Prop :=
  Summable (fun j : ℕ => (extremalNumber k (4 ^ j) : ℝ) / 4 ^ j)

/-- The [Er80] tail statement at length `k`. -/
def TailAt (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ A : Set ℕ, APFree A k → (∀ a ∈ A, N ≤ a) →
    Summable (reciprocalTerm A) ∧ ∑' n, reciprocalTerm A n < ε

/- ### Basic lemmas -/

lemma APFree.mono {A B : Set ℕ} {k : ℕ} (hBA : B ⊆ A) (h : APFree A k) : APFree B k := by
  rintro ⟨a, d, hd, hall⟩
  exact h ⟨a, d, hd, fun i hi => hBA (hall i hi)⟩

lemma reciprocalTerm_nonneg (A : Set ℕ) (n : ℕ) : 0 ≤ reciprocalTerm A n := by
  classical
  unfold reciprocalTerm
  split_ifs
  · positivity
  · exact le_rfl

lemma reciprocalTerm_of_mem {A : Set ℕ} {n : ℕ} (h : n ∈ A) :
    reciprocalTerm A n = (n : ℝ)⁻¹ := by
  classical
  unfold reciprocalTerm
  rw [if_pos h]

lemma reciprocalTerm_of_not_mem {A : Set ℕ} {n : ℕ} (h : n ∉ A) :
    reciprocalTerm A n = 0 := by
  classical
  unfold reciprocalTerm
  rw [if_neg h]

lemma extremalNumber_nonneg_real (k N : ℕ) : (0 : ℝ) ≤ extremalNumber k N := Nat.cast_nonneg _

/-- **Lemma 1 (translation).** A `k`-AP-free finite set inside the window `(b, b + n]` has at
most `r_k(n)` elements. -/
lemma card_le_extremalNumber {k b n : ℕ} {F : Finset ℕ}
    (hF : ∀ x ∈ F, b < x ∧ x ≤ b + n) (hfree : APFree (F : Set ℕ) k) :
    F.card ≤ extremalNumber k n := by
  classical
  set G := F.image (fun x => x - b) with hG
  have hinj : Set.InjOn (fun x => x - b) (F : Set ℕ) := by
    intro x hx y hy hxy
    have h1 := hF x hx
    have h2 := hF y hy
    simp only at hxy
    omega
  have hcard : G.card = F.card := Finset.card_image_of_injOn hinj
  have hsub : G ⊆ Finset.Icc 1 n := by
    intro y hy
    rw [hG, Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have := hF x hx
    rw [Finset.mem_Icc]
    omega
  have hGfree : APFree (G : Set ℕ) k := by
    rintro ⟨a, d, hd, hall⟩
    apply hfree
    refine ⟨a + b, d, hd, fun i hi => ?_⟩
    have hm := hall i hi
    rw [hG, Finset.coe_image] at hm
    obtain ⟨x, hx, hxe⟩ := hm
    have hb := hF x hx
    simp only at hxe
    have hx' : a + b + i * d = x := by omega
    rw [hx']
    exact hx
  rw [← hcard]
  unfold extremalNumber
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hsub, hGfree⟩)

/-- **Lemma 1' (several windows).** A `k`-AP-free finite set inside `(b, b + t n]` has at most
`t · r_k(n)` elements. -/
lemma card_le_mul_extremalNumber {k n : ℕ} : ∀ (t b : ℕ) (F : Finset ℕ),
    (∀ x ∈ F, b < x ∧ x ≤ b + t * n) → APFree (F : Set ℕ) k →
      F.card ≤ t * extremalNumber k n
  | 0, b, F, hF, _ => by
      have : F = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        have := hF x hx
        omega
      simp [this]
  | t + 1, b, F, hF, hfree => by
      classical
      set F1 := F.filter (fun x => x ≤ b + t * n) with hF1
      set F2 := F.filter (fun x => ¬ x ≤ b + t * n) with hF2
      have hsplit : F ⊆ F1 ∪ F2 := by
        intro x hx
        by_cases h : x ≤ b + t * n
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hx, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hx, h⟩)
      have h1 : F1.card ≤ t * extremalNumber k n := by
        apply card_le_mul_extremalNumber t b F1
        · intro x hx
          rw [hF1, Finset.mem_filter] at hx
          exact ⟨(hF x hx.1).1, hx.2⟩
        · exact hfree.mono (by
            intro x hx
            rw [hF1, Finset.coe_filter] at hx
            exact hx.1)
      have h2 : F2.card ≤ extremalNumber k n := by
        apply card_le_extremalNumber (b := b + t * n)
        · intro x hx
          rw [hF2, Finset.mem_filter] at hx
          have := (hF x hx.1).2
          constructor
          · omega
          · have : b + (t + 1) * n = b + t * n + n := by ring
            omega
        · exact hfree.mono (by
            intro x hx
            rw [hF2, Finset.coe_filter] at hx
            exact hx.1)
      calc F.card ≤ (F1 ∪ F2).card := Finset.card_le_card hsplit
        _ ≤ F1.card + F2.card := Finset.card_union_le _ _
        _ ≤ t * extremalNumber k n + extremalNumber k n := add_le_add h1 h2
        _ = (t + 1) * extremalNumber k n := by ring

/-- A `k`-AP-free finite set inside `[4^j, 4^{j+1})` has at most `3 r_k(4^j)` elements. -/
lemma card_block_le {k j : ℕ} {F : Finset ℕ}
    (hF : ∀ x ∈ F, 4 ^ j ≤ x ∧ x < 4 ^ (j + 1)) (hfree : APFree (F : Set ℕ) k) :
    F.card ≤ 3 * extremalNumber k (4 ^ j) := by
  apply card_le_mul_extremalNumber 3 (4 ^ j - 1) F _ hfree
  intro x hx
  have h := hF x hx
  have hp : 1 ≤ 4 ^ j := Nat.one_le_pow _ _ (by norm_num)
  have h4 : 4 ^ (j + 1) = 4 * 4 ^ j := by ring
  constructor <;> omega

/- ### Dyadic (4-adic) tail bound: `DyadicAt k → TailAt k` -/

/-- **Lemma 2 (block decomposition).** If `A` is `k`-AP-free with all elements `≥ 4^J`, then every
finite partial sum of its reciprocals is at most `∑_{j ≥ J} 3 r_k(4^j)/4^j`. -/
lemma finite_sum_le_tail {k J : ℕ} (hs : DyadicAt k) {A : Set ℕ} (hA : APFree A k)
    (hmin : ∀ a ∈ A, 4 ^ J ≤ a) (s : Finset ℕ) :
    ∑ n ∈ s, reciprocalTerm A n ≤
      ∑' i, 3 * ((extremalNumber k (4 ^ (i + J)) : ℝ) / 4 ^ (i + J)) := by
  classical
  set g : ℕ → ℝ := fun j => 3 * ((extremalNumber k (4 ^ j) : ℝ) / 4 ^ j) with hgdef
  have hg0 : ∀ j, 0 ≤ g j := fun j => by
    simp only [hgdef]
    positivity
  have hg : Summable g := hs.mul_left 3
  have hgJ : Summable (fun i => g (i + J)) := (summable_nat_add_iff J).2 hg
  set F := s.filter (· ∈ A) with hFdef
  have hpos : ∀ x ∈ F, x ≠ 0 := by
    intro x hx
    rw [hFdef, Finset.mem_filter] at hx
    have := hmin x hx.2
    have hp : 1 ≤ 4 ^ J := Nat.one_le_pow _ _ (by norm_num)
    omega
  -- reduce to F
  have hsF : ∑ n ∈ s, reciprocalTerm A n = ∑ n ∈ F, ((n : ℝ))⁻¹ := by
    rw [hFdef, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : n ∈ A
    · rw [if_pos h, reciprocalTerm_of_mem h]
    · rw [if_neg h, reciprocalTerm_of_not_mem h]
  rw [hsF]
  set K := F.sup (Nat.log 4) + 1 with hK
  have hmaps : ∀ x ∈ F, Nat.log 4 x ∈ Finset.Ico J K := by
    intro x hx
    rw [Finset.mem_Ico]
    constructor
    · have hxA : x ∈ A := (Finset.mem_filter.1 hx).2
      have := hmin x hxA
      exact Nat.le_log_of_pow_le (by norm_num) this
    · have := Finset.le_sup (f := Nat.log 4) hx
      omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hblock : ∀ j ∈ Finset.Ico J K,
      ∑ x ∈ F with Nat.log 4 x = j, ((x : ℝ))⁻¹ ≤ g j := by
    intro j _
    set Fj := F.filter (fun x => Nat.log 4 x = j) with hFj
    have hbounds : ∀ x ∈ Fj, 4 ^ j ≤ x ∧ x < 4 ^ (j + 1) := by
      intro x hx
      rw [hFj, Finset.mem_filter] at hx
      have hx0 := hpos x hx.1
      have h1 := Nat.pow_log_le_self 4 hx0
      have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) x
      rw [hx.2] at h1 h2
      exact ⟨h1, h2⟩
    have hfreej : APFree (Fj : Set ℕ) k := hA.mono (by
      intro x hx
      rw [hFj, Finset.coe_filter] at hx
      have := hx.1
      rw [hFdef, Finset.mem_filter] at this
      exact this.2)
    have hcard := card_block_le hbounds hfreej
    have hp : (0 : ℝ) < 4 ^ j := by positivity
    calc ∑ x ∈ Fj, ((x : ℝ))⁻¹ ≤ ∑ _x ∈ Fj, ((4 : ℝ) ^ j)⁻¹ := by
          apply Finset.sum_le_sum
          intro x hx
          have := (hbounds x hx).1
          have hx' : ((4 : ℝ) ^ j) ≤ (x : ℝ) := by exact_mod_cast this
          exact inv_anti₀ hp hx'
      _ = (Fj.card : ℝ) * ((4 : ℝ) ^ j)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((3 * extremalNumber k (4 ^ j) : ℕ) : ℝ) * ((4 : ℝ) ^ j)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcard
      _ = g j := by
          simp only [hgdef]
          push_cast
          ring
  calc ∑ j ∈ Finset.Ico J K, ∑ x ∈ F with Nat.log 4 x = j, ((x : ℝ))⁻¹
      ≤ ∑ j ∈ Finset.Ico J K, g j := Finset.sum_le_sum hblock
    _ = ∑ i ∈ Finset.range (K - J), g (J + i) := Finset.sum_Ico_eq_sum_range g J K
    _ = ∑ i ∈ Finset.range (K - J), g (i + J) := by
        apply Finset.sum_congr rfl; intro i _; rw [add_comm]
    _ ≤ ∑' i, g (i + J) := hgJ.sum_le_tsum _ (fun i _ => hg0 _)

/-- **Theorem A.** `DyadicAt k → TailAt k`. The threshold is `N = 4^J` for any `J` with
`∑_{j ≥ J} 3 r_k(4^j)/4^j < ε`. -/
theorem tailAt_of_dyadicAt {k : ℕ} (hs : DyadicAt k) : TailAt k := by
  intro ε hε
  set g : ℕ → ℝ := fun j => 3 * ((extremalNumber k (4 ^ j) : ℝ) / 4 ^ j) with hgdef
  have ht : Tendsto (fun J => ∑' i, g (i + J)) atTop (𝓝 0) := tendsto_sum_nat_add g
  obtain ⟨J, hJ⟩ : ∃ J, ∑' i, g (i + J) < ε :=
    (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨4 ^ J, fun A hA hmin => ?_⟩
  have key := finite_sum_le_tail (J := J) hs hA hmin
  have h0 : 0 ≤ reciprocalTerm A := fun n => reciprocalTerm_nonneg A n
  have hsum : Summable (reciprocalTerm A) := summable_of_sum_le h0 key
  exact ⟨hsum, lt_of_le_of_lt (hsum.tsum_le_of_sum_le key) hJ⟩

/- ### Window construction: `ReciprocalAt k → DyadicAt k` for `k ≥ 3` -/

/-- `x` lies in the `j`-th window, as the translate by `2·4^j - 1` of an element of `S j`. -/
def InWin (S : ℕ → Finset ℕ) (j x : ℕ) : Prop := ∃ s ∈ S j, x = s + (2 * 4 ^ j - 1)

/-- The window set `⋃_j (S j + (2·4^j - 1))`. -/
def winSet (S : ℕ → Finset ℕ) : Set ℕ := {x | ∃ j, InWin S j x}

lemma InWin.bounds {S : ℕ → Finset ℕ} (hS : ∀ j, S j ⊆ Finset.Icc 1 (4 ^ j)) {j x : ℕ}
    (h : InWin S j x) : 1 ≤ 4 ^ j ∧ 2 * 4 ^ j ≤ x ∧ x ≤ 3 * 4 ^ j - 1 := by
  obtain ⟨s, hs, rfl⟩ := h
  have := Finset.mem_Icc.1 (hS j hs)
  have hp : 1 ≤ 4 ^ j := Nat.one_le_pow _ _ (by norm_num)
  refine ⟨hp, ?_, ?_⟩ <;> omega

lemma four_pow_lt {i j : ℕ} (h : i < j) : 4 * 4 ^ i ≤ 4 ^ j := by
  have : 4 ^ (i + 1) ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) h
  calc 4 * 4 ^ i = 4 ^ (i + 1) := by ring
    _ ≤ 4 ^ j := this

/-- Windows are disjoint. -/
lemma InWin.unique {S : ℕ → Finset ℕ} (hS : ∀ j, S j ⊆ Finset.Icc 1 (4 ^ j)) {i j x : ℕ}
    (hi : InWin S i x) (hj : InWin S j x) : i = j := by
  have bi := hi.bounds hS
  have bj := hj.bounds hS
  rcases lt_trichotomy i j with h | h | h
  · have := four_pow_lt h
    omega
  · exact h
  · have := four_pow_lt h
    omega

/-- **Lemma 3 (window lemma).** A 3-term AP `x < y < z` (with `x + z = 2y`) inside the window set
lies in a single window. -/
lemma triple_same_window {S : ℕ → Finset ℕ} (hS : ∀ j, S j ⊆ Finset.Icc 1 (4 ^ j))
    {jx jy jz x y z : ℕ} (hx : InWin S jx x) (hy : InWin S jy y) (hz : InWin S jz z)
    (hxy : x < y) (hap : x + z = 2 * y) : jx = jy ∧ jy = jz := by
  have bx := hx.bounds hS
  have bY := hy.bounds hS
  have bz := hz.bounds hS
  have hyz : jy = jz := by
    rcases lt_trichotomy jy jz with h | h | h
    · have := four_pow_lt h
      omega
    · exact h
    · have := four_pow_lt h
      omega
  subst hyz
  refine ⟨?_, rfl⟩
  rcases lt_trichotomy jx jy with h | h | h
  · have := four_pow_lt h
    omega
  · exact h
  · have := four_pow_lt h
    omega

/-- **Lemma 4.** If every `S j ⊆ [1, 4^j]` is `k`-AP-free (`k ≥ 3`), so is the window set. -/
lemma winSet_apFree {S : ℕ → Finset ℕ} {k : ℕ} (hk : 3 ≤ k)
    (hS : ∀ j, S j ⊆ Finset.Icc 1 (4 ^ j)) (hfree : ∀ j, APFree (S j : Set ℕ) k) :
    APFree (winSet S) k := by
  rintro ⟨a, d, hd, hall⟩
  obtain ⟨j0, ha0⟩ := hall 0 (by omega)
  simp only [zero_mul, add_zero] at ha0
  -- every term lies in window j0
  have hterm : ∀ i, i < k → InWin S j0 (a + i * d) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases i with _ | _ | i
      · simpa using ha0
      · -- i = 1: use the triple (a, a+d, a+2d)
        obtain ⟨j1, h1⟩ := hall 1 (by omega)
        obtain ⟨j2, h2⟩ := hall 2 (by omega)
        have hx : InWin S j0 (a + 0 * d) := by simpa using ha0
        have ht := triple_same_window hS hx h1 h2 (by nlinarith) (by ring)
        rw [← ht.1] at h1
        exact h1
      · -- i + 2: use the triple (a + i d, a + (i+1) d, a + (i+2) d)
        have hA := ih i (by omega) (by omega)
        have hB := ih (i + 1) (by omega) (by omega)
        obtain ⟨jc, hC⟩ := hall (i + 2) hi
        have ht := triple_same_window hS hA hB hC (by nlinarith) (by ring)
        rw [← ht.2, ← ht.1] at hC
        exact hC
  -- so the AP is a translate of an AP in S j0
  obtain ⟨s0, hs0, hs0e⟩ := ha0
  apply hfree j0
  refine ⟨s0, d, hd, fun i hi => ?_⟩
  obtain ⟨s, hs, hse⟩ := hterm i hi
  have : s0 + i * d = s := by omega
  rw [this]
  exact hs

/-- **Lemma 5.** Reciprocal sums of the window set dominate `∑_j |S j| / (3·4^j)`. -/
lemma summable_card_of_summable_winSet {S : ℕ → Finset ℕ}
    (hS : ∀ j, S j ⊆ Finset.Icc 1 (4 ^ j)) (hsum : Summable (reciprocalTerm (winSet S))) :
    Summable (fun j => ((S j).card : ℝ) / (3 * 4 ^ j)) := by
  classical
  apply summable_of_sum_range_le (c := ∑' n, reciprocalTerm (winSet S) n)
  · intro j; positivity
  · intro J
    set T : ℕ → Finset ℕ := fun j => (S j).image (fun s => s + (2 * 4 ^ j - 1)) with hT
    have hdisj : ((Finset.range J : Finset ℕ) : Set ℕ).PairwiseDisjoint T := by
      intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      intro x hxi hxj
      rw [hT, Finset.mem_image] at hxi hxj
      obtain ⟨s, hs, hse⟩ := hxi
      obtain ⟨s', hs', hse'⟩ := hxj
      exact hij (InWin.unique hS ⟨s, hs, hse.symm⟩ ⟨s', hs', hse'.symm⟩)
    have hle : ∀ j ∈ Finset.range J,
        ((S j).card : ℝ) / (3 * 4 ^ j) ≤ ∑ x ∈ T j, reciprocalTerm (winSet S) x := by
      intro j _
      have hinj : Set.InjOn (fun s => s + (2 * 4 ^ j - 1)) (S j : Set ℕ) := by
        intro a _ b _ hab
        simp only at hab
        omega
      have hcard : (T j).card = (S j).card := Finset.card_image_of_injOn hinj
      have hp : (0 : ℝ) < 3 * 4 ^ j := by positivity
      calc ((S j).card : ℝ) / (3 * 4 ^ j) = ∑ _x ∈ T j, (3 * (4 : ℝ) ^ j)⁻¹ := by
            rw [Finset.sum_const, nsmul_eq_mul, hcard, div_eq_mul_inv]
        _ ≤ ∑ x ∈ T j, reciprocalTerm (winSet S) x := by
            apply Finset.sum_le_sum
            intro x hx
            rw [hT, Finset.mem_image] at hx
            obtain ⟨s, hs, hse⟩ := hx
            have hw : InWin S j x := ⟨s, hs, hse.symm⟩
            have hmem : x ∈ winSet S := ⟨j, hw⟩
            rw [reciprocalTerm_of_mem hmem]
            have b := hw.bounds hS
            have hx0 : (0 : ℝ) < x := by
              have : 0 < x := by
                have hp1 : 1 ≤ 4 ^ j := Nat.one_le_pow _ _ (by norm_num)
                omega
              exact_mod_cast this
            have hx3 : (x : ℝ) ≤ 3 * 4 ^ j := by
              have : x ≤ 3 * 4 ^ j := by omega
              exact_mod_cast this
            exact inv_anti₀ hx0 hx3
    calc ∑ j ∈ Finset.range J, ((S j).card : ℝ) / (3 * 4 ^ j)
        ≤ ∑ j ∈ Finset.range J, ∑ x ∈ T j, reciprocalTerm (winSet S) x := Finset.sum_le_sum hle
      _ = ∑ x ∈ (Finset.range J).biUnion T, reciprocalTerm (winSet S) x :=
          (Finset.sum_biUnion hdisj).symm
      _ ≤ ∑' n, reciprocalTerm (winSet S) n :=
          hsum.sum_le_tsum _ (fun i _ => reciprocalTerm_nonneg _ _)

/-- Extremal sets exist. -/
lemma exists_extremal (k N : ℕ) (hk : 1 ≤ k) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ APFree (S : Set ℕ) k ∧ S.card = extremalNumber k N := by
  classical
  have hne : (((Finset.Icc 1 N).powerset).filter
      fun S : Finset ℕ ↦ APFree (S : Set ℕ) k).Nonempty := by
    refine ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, ?_⟩⟩
    rintro ⟨a, d, _, hall⟩
    have := hall 0 (by omega)
    simp at this
  obtain ⟨S, hS, hSe⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  refine ⟨S, hS.1, hS.2, ?_⟩
  unfold extremalNumber
  convert hSe.symm

/-- **Theorem B.** `ReciprocalAt k → DyadicAt k` for `k ≥ 3`. -/
theorem dyadicAt_of_reciprocalAt {k : ℕ} (hk : 3 ≤ k) (h : ReciprocalAt k) : DyadicAt k := by
  choose S hS hfree hcard using fun j : ℕ => exists_extremal k (4 ^ j) (by omega)
  have hU : APFree (winSet S) k := winSet_apFree hk hS hfree
  have h3 := summable_card_of_summable_winSet hS (h _ hU)
  have h3' := h3.mul_left 3
  unfold DyadicAt
  refine h3'.congr (fun j => ?_)
  rw [hcard j]
  field_simp

/-- **Theorem C (trivial direction).** `TailAt k → ReciprocalAt k`. -/
theorem reciprocalAt_of_tailAt {k : ℕ} (h : TailAt k) : ReciprocalAt k := by
  classical
  intro A hA
  obtain ⟨N, hN⟩ := h 1 one_pos
  set B : Set ℕ := {n | n ∈ A ∧ N ≤ n} with hB
  have hBfree : APFree B k := hA.mono (fun n hn => hn.1)
  have hBsum := (hN B hBfree (fun a ha => ha.2)).1
  have hfin : Summable (fun n => if n < N then reciprocalTerm A n else 0) := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro n hn
    rw [Finset.mem_range] at hn
    rw [if_neg hn]
  refine (hBsum.add hfin).congr (fun n => ?_)
  by_cases hn : n < N
  · have : n ∉ B := fun hm => by have := hm.2; omega
    rw [reciprocalTerm_of_not_mem this, if_pos hn, zero_add]
  · rw [if_neg hn, add_zero]
    by_cases hA' : n ∈ A
    · have : n ∈ B := ⟨hA', by omega⟩
      rw [reciprocalTerm_of_mem this, reciprocalTerm_of_mem hA']
    · have : n ∉ B := fun hm => hA' hm.1
      rw [reciprocalTerm_of_not_mem this, reciprocalTerm_of_not_mem hA']

/-- **Main equivalence at fixed `k ≥ 3`.** -/
theorem tailAt_iff_reciprocalAt {k : ℕ} (hk : 3 ≤ k) : TailAt k ↔ ReciprocalAt k :=
  ⟨reciprocalAt_of_tailAt, fun h => tailAt_of_dyadicAt (dyadicAt_of_reciprocalAt hk h)⟩

theorem tailAt_iff_dyadicAt {k : ℕ} (hk : 3 ≤ k) : TailAt k ↔ DyadicAt k :=
  ⟨fun h => dyadicAt_of_reciprocalAt hk (reciprocalAt_of_tailAt h), tailAt_of_dyadicAt⟩

/- ### Bridge to the formal-conjectures vocabulary -/

/-- The uniform tail property at `k`, in the form of the formal-conjectures statements. -/
def UniformTail (k : ℕ) : Prop := ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ A : Set ℕ,
    A.IsAPOfLengthFree k → (∀ a ∈ A, N ≤ a) →
      (Summable fun a : A ↦ 1 / (a : ℝ)) ∧ ∑' a : A, 1 / (a : ℝ) < ε

/-- Problem 3 at `k`, in the form of `erdos_3.variants.three`. -/
def Erdos3At (k : ℕ) : Prop := ∀ A : Set ℕ,
    (¬ Summable fun a : A ↦ 1 / (a : ℝ)) → ∃ S ⊆ A, S.IsAPOfLength k

lemma reciprocalTerm_eq_indicator (A : Set ℕ) :
    reciprocalTerm A = A.indicator (fun n : ℕ => 1 / (n : ℝ)) := by
  classical
  funext n
  unfold reciprocalTerm Set.indicator
  split_ifs <;> simp

lemma summable_subtype_iff (A : Set ℕ) :
    (Summable fun a : A ↦ 1 / (a : ℝ)) ↔ Summable (reciprocalTerm A) := by
  rw [reciprocalTerm_eq_indicator]
  exact summable_subtype_iff_indicator (f := fun n : ℕ => 1 / (n : ℝ))

lemma tsum_subtype_eq (A : Set ℕ) :
    ∑' a : A, 1 / (a : ℝ) = ∑' n, reciprocalTerm A n := by
  rw [reciprocalTerm_eq_indicator]
  exact tsum_subtype A (fun n : ℕ => 1 / (n : ℝ))

/-- A formal-conjectures arithmetic progression of length `m ≥ 2` contains a `HasAP` of any
length `k ≤ m`. -/
lemma hasAP_of_isAPOfLength {S : Set ℕ} {m k : ℕ} (hS : S.IsAPOfLength m) (hm : 2 ≤ m)
    (hkm : k ≤ m) : HasAP S k := by
  obtain ⟨a, d, hcard, heq⟩ := hS
  rcases Nat.eq_zero_or_pos d with hd | hd
  · exfalso
    have hsub : S ⊆ {a} := by
      intro x hx
      rw [heq] at hx
      obtain ⟨n, _, rfl⟩ := hx
      simp [hd]
    have h1 : S.encard ≤ 1 := by
      calc S.encard ≤ ({a} : Set ℕ).encard := Set.encard_le_encard hsub
        _ = 1 := Set.encard_singleton a
    rw [← ENat.card_coe_set_eq, hcard] at h1
    have : m ≤ 1 := by exact_mod_cast h1
    omega
  · refine ⟨a, d, hd, fun i hi => ?_⟩
    rw [heq]
    refine ⟨i, ?_, by simp [smul_eq_mul]⟩
    exact_mod_cast (lt_of_lt_of_le hi hkm)

lemma HasAP.mono {A B : Set ℕ} {k : ℕ} (h : HasAP A k) (hAB : A ⊆ B) : HasAP B k := by
  obtain ⟨a, d, hd, hall⟩ := h
  exact ⟨a, d, hd, fun i hi => hAB (hall i hi)⟩

/-- A `HasAP` of length `k ≥ 2` gives a formal-conjectures arithmetic progression of length
`k`. -/
lemma not_isAPOfLengthFree_of_hasAP {A : Set ℕ} {k : ℕ} (hk : 2 ≤ k) (h : HasAP A k) :
    ¬ A.IsAPOfLengthFree k := by
  classical
  obtain ⟨a, d, hd, hall⟩ := h
  intro hfree
  set t : Set ℕ := {a + n • d | (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞))} with ht
  have hteq : t = ↑((Finset.range k).image (fun n => a + n * d)) := by
    ext x
    simp only [ht, Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_range, Set.mem_image,
      Set.mem_Iio, smul_eq_mul, Nat.cast_lt, exists_prop]
  have hinj : Function.Injective (fun n => a + n * d) := by
    intro x y hxy
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_right hd (by omega)
  have hcard : ENat.card t = k := by
    rw [ENat.card_coe_set_eq, hteq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hsub : t ⊆ A := by
    rw [hteq]
    intro x hx
    rw [Finset.coe_image, Finset.coe_range] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    exact hall n hn
  have hle := hfree t hsub ⟨a, d, hcard, ht⟩
  have : k ≤ 1 := by exact_mod_cast hle
  omega

/-- For `k ≥ 2` the two notions of `k`-AP-freeness agree. -/
lemma isAPOfLengthFree_iff_apFree {A : Set ℕ} {k : ℕ} (hk : 2 ≤ k) :
    A.IsAPOfLengthFree k ↔ APFree A k := by
  constructor
  · exact fun h hAP => not_isAPOfLengthFree_of_hasAP hk hAP h
  · intro h t ht htAP
    exfalso
    exact h (HasAP.mono (hasAP_of_isAPOfLength htAP hk le_rfl) ht)

/-- For `k ≥ 2`, `A` contains a progression of length `k` in the formal-conjectures sense if and
only if it contains one in the sense of `HasAP`. -/
lemma exists_isAPOfLength_iff_hasAP {A : Set ℕ} {k : ℕ} (hk : 2 ≤ k) :
    (∃ S ⊆ A, S.IsAPOfLength k) ↔ HasAP A k := by
  constructor
  · rintro ⟨S, hSA, hS⟩
    exact HasAP.mono (hasAP_of_isAPOfLength hS hk le_rfl) hSA
  · intro h
    by_contra hno
    refine not_isAPOfLengthFree_of_hasAP hk h ?_
    intro t ht htAP
    exact absurd ⟨t, ht, htAP⟩ hno

/-- `Erdos3At k` is the same as `ReciprocalAt k` (for `k ≥ 2`). -/
lemma erdos3At_iff_reciprocalAt {k : ℕ} (hk : 2 ≤ k) : Erdos3At k ↔ ReciprocalAt k := by
  constructor
  · intro h A hA
    by_contra hns
    rw [← summable_subtype_iff] at hns
    exact hA ((exists_isAPOfLength_iff_hasAP hk).1 (h A hns))
  · intro h A hns
    rw [summable_subtype_iff] at hns
    by_contra hno
    exact hns (h A fun hAP => hno ((exists_isAPOfLength_iff_hasAP hk).2 hAP))

/-- `UniformTail k` is the same as `TailAt k` (for `k ≥ 2`). -/
lemma uniformTail_iff_tailAt {k : ℕ} (hk : 2 ≤ k) : UniformTail k ↔ TailAt k := by
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun A hA hmin => ?_⟩
    obtain ⟨hs, hlt⟩ := hN A ((isAPOfLengthFree_iff_apFree hk).2 hA) hmin
    exact ⟨(summable_subtype_iff A).1 hs, by rwa [← tsum_subtype_eq]⟩
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun A hA hmin => ?_⟩
    obtain ⟨hs, hlt⟩ := hN A ((isAPOfLengthFree_iff_apFree hk).1 hA) hmin
    exact ⟨(summable_subtype_iff A).2 hs, by rwa [tsum_subtype_eq]⟩

/-- **Fixed-`k` equivalence**, in the formal-conjectures vocabulary. -/
lemma erdos3At_iff_uniformTail {k : ℕ} (hk : 3 ≤ k) : Erdos3At k ↔ UniformTail k := by
  rw [erdos3At_iff_reciprocalAt (by omega), uniformTail_iff_tailAt (by omega),
    tailAt_iff_reciprocalAt hk]

/- ### The dyadic route from the Kelley and Meka bound -/

/-- `extremalNumber k N` is at most formal-conjectures' `Set.IsAPOfLengthFree.maxCard k N`, for
`k ≥ 2`. -/
lemma extremalNumber_le_maxCard {k : ℕ} (hk : 2 ≤ k) (N : ℕ) :
    extremalNumber k N ≤ Set.IsAPOfLengthFree.maxCard k N := by
  classical
  unfold extremalNumber Set.IsAPOfLengthFree.maxCard
  apply Finset.sup_le
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro n ⟨T, hT, -, rfl⟩
    calc T.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hT
      _ = N := by simp
  · exact ⟨S, hS.1, (isAPOfLengthFree_iff_apFree hk).2 hS.2, rfl⟩

/-- `exp(-c (log 4^n)^β) ≤ 1/n^2` for all large `n`. -/
lemma eventually_exp_log_rpow_le {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-c * Real.log ((4 ^ n : ℕ) : ℝ) ^ β) ≤ (((n : ℝ)) ^ 2)⁻¹ := by
  have hlo := (isLittleO_log_rpow_atTop hβ).bound (show (0 : ℝ) < c / 2 by positivity)
  have hnat := tendsto_natCast_atTop_atTop.eventually hlo
  filter_upwards [hnat, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hl4 : 1 ≤ Real.log 4 := by
    have h := Real.log_two_gt_d9
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hL : Real.log ((4 ^ n : ℕ) : ℝ) = n * Real.log 4 := by
    push_cast; rw [Real.log_pow]
  rw [hL]
  have hlogn : Real.log (n : ℝ) ≤ c / 2 * (n : ℝ) ^ β := by
    have h0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (by positivity)] at hn
    exact hn
  have hmono : (n : ℝ) ^ β ≤ ((n : ℝ) * Real.log 4) ^ β :=
    Real.rpow_le_rpow hn0.le (by nlinarith) hβ.le
  have hkey : 2 * Real.log (n : ℝ) ≤ c * ((n : ℝ) * Real.log 4) ^ β := by
    have := mul_le_mul_of_nonneg_left hmono hc.le
    nlinarith
  have hexp : Real.exp (-(2 * Real.log (n : ℝ))) = (((n : ℝ)) ^ 2)⁻¹ := by
    rw [Real.exp_neg, show 2 * Real.log (n : ℝ) = Real.log (n : ℝ) + Real.log (n : ℝ) by ring,
      Real.exp_add, Real.exp_log hn0, sq]
  rw [← hexp]
  apply Real.exp_le_exp.2
  linarith

/-- A bound `maxCard k N ≪ N exp(-c (log N)^β)`, as in `erdos_3.variants.kelley_meka`, gives
`DyadicAt k`. -/
theorem dyadicAt_of_maxCard_isBigO {k : ℕ} (hk : 2 ≤ k) {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (hO : (fun N ↦ (Set.IsAPOfLengthFree.maxCard k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-c * Real.log N ^ β)) :
    DyadicAt k := by
  obtain ⟨C, hC⟩ := hO.bound
  have h4 : Tendsto (fun n : ℕ => 4 ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hC4 := h4.eventually hC
  unfold DyadicAt
  have hg : Summable (fun n : ℕ => |C| * (((n : ℝ)) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv.2 (by norm_num)).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  filter_upwards [hC4, eventually_exp_log_rpow_le hc hβ] with n hn he
  have hpos : (0 : ℝ) < 4 ^ n := by positivity
  set e := Real.exp (-c * Real.log ((4 ^ n : ℕ) : ℝ) ^ β) with hedef
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hm : (Set.IsAPOfLengthFree.maxCard k (4 ^ n) : ℝ) ≤ C * ((4 : ℝ) ^ n * e) := by
    have h0 : (0 : ℝ) ≤ ((4 ^ n : ℕ) : ℝ) * e := by positivity
    simp only [Real.norm_natCast] at hn
    rw [Real.norm_of_nonneg h0] at hn
    push_cast at hn ⊢
    exact hn
  have hx : (extremalNumber k (4 ^ n) : ℝ) ≤ Set.IsAPOfLengthFree.maxCard k (4 ^ n) := by
    exact_mod_cast extremalNumber_le_maxCard hk (4 ^ n)
  rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ hpos]
  calc (extremalNumber k (4 ^ n) : ℝ) ≤ C * ((4 : ℝ) ^ n * e) := hx.trans hm
    _ ≤ |C| * ((4 : ℝ) ^ n * e) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ = |C| * e * 4 ^ n := by ring
    _ ≤ |C| * (((n : ℝ)) ^ 2)⁻¹ * 4 ^ n := by
        apply mul_le_mul_of_nonneg_right _ hpos.le
        exact mul_le_mul_of_nonneg_left he (abs_nonneg C)


/- ### The statements of the proposed formal-conjectures variants -/

/-- `erdos_3.variants.uniform_tail_iff`, copied verbatim from the proposed variant in
`FormalConjectures/ErdosProblems/3.lean`: for fixed `k ≥ 3`, Problem 3 at `k` holds if and only if
the [Er80] uniform tail property holds at `k`. -/
theorem erdos_3.variants.uniform_tail_iff (k : ℕ) (hk : 3 ≤ k) :
    (∀ A : Set ℕ, (¬ Summable fun a : A ↦ 1 / (a : ℝ)) → ∃ S ⊆ A, S.IsAPOfLength k) ↔
      ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ A : Set ℕ, A.IsAPOfLengthFree k → (∀ a ∈ A, N ≤ a) →
        (Summable fun a : A ↦ 1 / (a : ℝ)) ∧ ∑' a : A, 1 / (a : ℝ) < ε :=
  erdos3At_iff_uniformTail hk

/-- `erdos_3.variants.uniform_tail_three`, copied verbatim from the proposed variant, proved from
the hypothesis `erdos_3.variants.kelley_meka` (the formal-conjectures statement itself, via
`type_of%`). The Kelley and Meka bound makes `∑_j r_3(4^j)/4^j` converge, and step 2 applies. -/
theorem erdos_3.variants.uniform_tail_three
    (h : type_of% Erdos3.erdos_3.variants.kelley_meka) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ A : Set ℕ, A.IsAPOfLengthFree 3 → (∀ a ∈ A, N ≤ a) →
      (Summable fun a : A ↦ 1 / (a : ℝ)) ∧ ∑' a : A, 1 / (a : ℝ) < ε := by
  obtain ⟨β, hβ, c, hc, hO⟩ := h
  have h3 : UniformTail 3 := (uniformTail_iff_tailAt (by norm_num)).2
    (tailAt_of_dyadicAt (dyadicAt_of_maxCard_isBigO (by norm_num) hβ hc hO))
  exact h3

/-- Problem 3 at every length gives Problem 3 at length `k`. -/
lemma erdos3At_of_erdos3 (h3 : ∀ A : Set ℕ, (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) {k : ℕ} (hk : 2 ≤ k) :
    Erdos3At k := by
  rw [erdos3At_iff_reciprocalAt hk]
  intro A hA
  by_contra hns
  rw [← summable_subtype_iff] at hns
  obtain ⟨m, hm, S, hSA, hS⟩ := Filter.frequently_atTop.1 (h3 A hns) k
  exact hA (HasAP.mono (hasAP_of_isAPOfLength hS (hk.trans hm) hm) hSA)

/-- `erdos_3.variants.uniform_tail`, copied verbatim from the proposed variant, proved from the
hypothesis given by the statement of `erdos_3` (copied verbatim from formal-conjectures commit
`9097e2f9`). This is the question of [Er80] for every `k ≥ 3`. -/
theorem erdos_3.variants.uniform_tail
    (h : ∀ A : Set ℕ, (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) :
    ∀ k : ℕ, 3 ≤ k → ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ A : Set ℕ, A.IsAPOfLengthFree k →
      (∀ a ∈ A, N ≤ a) → (Summable fun a : A ↦ 1 / (a : ℝ)) ∧ ∑' a : A, 1 / (a : ℝ) < ε :=
  fun k hk => (erdos3At_iff_uniformTail hk).1 (erdos3At_of_erdos3 h (by omega))

/-- The converse of `erdos_3.variants.uniform_tail`: the uniform tail property for every `k ≥ 3`
gives the statement of `erdos_3`. -/
theorem erdos_3_of_uniform_tail
    (h : ∀ k : ℕ, 3 ≤ k → ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ A : Set ℕ, A.IsAPOfLengthFree k →
      (∀ a ∈ A, N ≤ a) → (Summable fun a : A ↦ 1 / (a : ℝ)) ∧ ∑' a : A, 1 / (a : ℝ) < ε) :
    ∀ A : Set ℕ, (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k := by
  intro A hA
  rw [Filter.frequently_atTop]
  intro k0
  exact ⟨max k0 3, le_max_left _ _,
    (erdos3At_iff_uniformTail (le_max_right _ _)).2 (h _ (le_max_right _ _)) A hA⟩

end ErdosLean.Erdos169Er80
