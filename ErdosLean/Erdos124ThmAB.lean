import FormalConjectures.ErdosProblems.«124»

/-!
# Erdős Problem 124: one power block plus a part with `σ > 1`

Write `σ(X) = ∑_{x ∈ X} 1 / (x - 1)`. We prove
`erdos124.variants.ne_zero_of_power_block`: let `D` be a finite set of integers `≥ 3` and
`D = C ⊔ E`, where `C` is a nonempty set of powers `h ^ a` (`a ≥ 1`) of one integer `h` with
`2 σ(C) ≥ 1`, `σ(E) > 1`, and some `c ∈ E` is coprime to `h`. Then for every `k ≠ 0` every
sufficiently large integer is a sum of distinct powers `d ^ j` with `d ∈ D`, `j ≥ k`, using each
pair `(d, j)` at most once, i.e. it lies in `∑ d ∈ D, sumsOfDistinctPowers d k`.
The special case `C = {3}` is `erdos124.variants.ne_zero_of_three_mem`: the conclusion holds for
every `D` with `3 ∈ D`, `gcd D = 1` and `σ(D) > 3 / 2`.

This gives an infinite family of tuples for which `erdos124.ne_zero` holds. It says nothing about
tuples with `σ(D) ≤ 3 / 2`, and no member of the family is an inclusion-minimal admissible set.

Proof outline (coins are pairs `(d, j)` of value `d ^ j`):
* Lemma 1 (Brown's lemma, gap form; `gap_of_grow`): if every truncation of a set of coins
  satisfies `v ≤ (sum of the coins of value < v) + G`, its subset sums have gaps `≤ G`.
* Lemma 2 (`key`): if `d ^ g d ≥ τ > 1` for all `d ∈ E` and `σ(E) > 1`, then
  `∑ d ^ g d / (d - 1) ≥ σ(E) + τ` (the sum of the geometric sums is an integer `> ⌈τ⌉ - 1`).
* Lemmas 3 and 4 (`bound_one`, `bound_R`, `growB`): deleting from the coins of `E` with
  exponent `≥ k` the base-`c` coins `c ^ e` at `ε`-cluster values, each larger than the sum of
  the earlier ones divided by `ρ - 1`, keeps the gap bound `C_k(E) = ∑ d ^ k / (d - 1)`.
* Lemma 5 (`exists_cluster`): `ε`-cluster values `c ^ e` with `P ∣ e` exist and are arbitrarily
  large (simultaneous Dirichlet approximation, `sim_dirichlet`).
* Lemma 6 (`signed_rep`): with `2 σ(C) ≥ 1` every integer is a signed sum of distinct coins of
  `C`. This is the sufficiency half of Park's theorem on 2-complete partitions (S. K. Park,
  *The r-complete partitions*, Discrete Math. 183 (1998), Thm 2.2).
* Lemmas 7 and 8 (`exists_shift`, `gadget`): shifting a signed representation of
  `(c ^ e - 1) / h ^ K` by the block `h ^ K` gives disjoint `U ∋ (c, e)`, `V` with
  `∑ U - ∑ V = 1`, when `φ(h ^ K) ∣ e` (Euler's theorem).
* Assembly (`inv_step`): `G = ⌈C_k(E)⌉` disjoint unit gadgets plus the syndetic part.
  This scheme is Graham's (Complete sequences of polynomial values, Duke Math. J. 31 (1964),
  Lemmas 4 and 5); compare also Fan (arXiv:2607.14071 v6, Lemma 6.1 and, for sparse infinite
  deletions, Corollary 6.3).

The definition `sumsOfDistinctPowers` is the one of `FormalConjectures/ErdosProblems/124.lean`
(identical at the commit pinned in `lakefile.toml`). The two statements are copied verbatim from
the proposed variants of that file.
-/

open Filter Finset
open scoped Pointwise

namespace ErdosLean.Erdos124ThmAB

open _root_.Erdos124

/-- The value `d ^ j` of the coin `(d, j)`. -/
def val (p : ℕ × ℕ) : ℕ := p.1 ^ p.2

/-- The coins `(d, j)` with `d ∈ S`, satisfying `P`, of value `< t`. -/
def trunc (S : Finset ℕ) (P : ℕ × ℕ → Prop) [DecidablePred P] (t : ℕ) : Finset (ℕ × ℕ) :=
  (S ×ˢ range t).filter (fun p => P p ∧ val p < t)

lemma mem_trunc {S : Finset ℕ} {P : ℕ × ℕ → Prop} [DecidablePred P] {t : ℕ}
    (hS : ∀ d ∈ S, 2 ≤ d) {p : ℕ × ℕ} :
    p ∈ trunc S P t ↔ p.1 ∈ S ∧ P p ∧ val p < t := by
  unfold trunc
  simp only [mem_filter, mem_product, mem_range]
  constructor
  · rintro ⟨⟨h1, _⟩, h2, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, ?_⟩, h2, h3⟩
    calc p.2 < 2 ^ p.2 := Nat.lt_two_pow_self
      _ ≤ p.1 ^ p.2 := Nat.pow_le_pow_left (hS _ h1) _
      _ < t := h3

/-- Adding a finite set of coins, each of value at most `f` of the current sum. -/
lemma add_many {Q : Finset (ℕ × ℕ) → Prop} {f : ℕ → ℕ} (hf : Monotone f)
    (hstep : ∀ A b, b ∉ A → Q A → val b ≤ f (∑ a ∈ A, val a) → Q (insert b A))
    (A X : Finset (ℕ × ℕ)) (hX : ∀ b ∈ X, b ∉ A ∧ val b ≤ f (∑ a ∈ A, val a)) (hA : Q A) :
    Q (A ∪ X) := by
  induction X using Finset.induction_on with
  | empty => simpa using hA
  | insert b X hbX ih =>
    have hX' : ∀ c ∈ X, c ∉ A ∧ val c ≤ f (∑ a ∈ A, val a) :=
      fun c hc => hX c (mem_insert_of_mem hc)
    rw [union_insert]
    obtain ⟨hbA, hb⟩ := hX b (mem_insert_self _ _)
    refine hstep _ _ ?_ (ih hX') ?_
    · simp [hbA, hbX]
    · exact hb.trans (hf (sum_le_sum_of_subset subset_union_left))

/-- Threshold induction: a property preserved by adding a coin of value at most `f` of the
current sum holds for every truncation, if every truncation is large enough. -/
lemma threshold_induction (S : Finset ℕ) (hS : ∀ d ∈ S, 2 ≤ d) (P : ℕ × ℕ → Prop)
    [DecidablePred P] {Q : Finset (ℕ × ℕ) → Prop} {f : ℕ → ℕ} (hf : Monotone f) (h0 : Q ∅)
    (hstep : ∀ A b, b ∉ A → Q A → val b ≤ f (∑ a ∈ A, val a) → Q (insert b A))
    (hgrow : ∀ v, v ≤ f (∑ a ∈ trunc S P v, val a)) : ∀ t, Q (trunc S P t) := by
  intro t
  induction t with
  | zero =>
    convert h0
    ext p
    simp [mem_trunc hS]
  | succ t ih =>
    have hsplit : trunc S P (t + 1) =
        trunc S P t ∪ (trunc S P (t + 1)).filter (fun p => val p = t) := by
      ext p
      simp only [mem_union, mem_filter, mem_trunc hS]
      constructor
      · rintro ⟨h1, h2, h3⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h3 with h | h
        · exact Or.inl ⟨h1, h2, h⟩
        · exact Or.inr ⟨⟨h1, h2, h3⟩, h⟩
      · rintro (⟨h1, h2, h3⟩ | ⟨h, _⟩)
        · exact ⟨h1, h2, by omega⟩
        · exact h
    rw [hsplit]
    apply add_many hf hstep _ _ _ ih
    intro b hb
    rw [mem_filter, mem_trunc hS] at hb
    refine ⟨fun hb' => ?_, ?_⟩
    · rw [mem_trunc hS] at hb'
      omega
    · rw [hb.2]
      exact hgrow t

/-- Gap property of a finite set of coins: every `x` below the total plus `G` lies within
`G` above a subset sum. -/
def GapProp (G : ℕ) (A : Finset (ℕ × ℕ)) : Prop :=
  ∀ x, x < ∑ a ∈ A, val a + G → ∃ T ⊆ A, ∑ a ∈ T, val a ≤ x ∧ x < ∑ a ∈ T, val a + G

lemma gapProp_empty (G : ℕ) : GapProp G ∅ :=
  fun x hx => ⟨∅, subset_refl _, by simp, by simpa using hx⟩

lemma gapProp_insert (G : ℕ) (A : Finset (ℕ × ℕ)) (b : ℕ × ℕ) (hb : b ∉ A) (hA : GapProp G A)
    (hbv : val b ≤ ∑ a ∈ A, val a + G) : GapProp G (insert b A) := by
  intro x hx
  rw [sum_insert hb] at hx
  by_cases hx' : x < ∑ a ∈ A, val a + G
  · obtain ⟨T, hT, h1, h2⟩ := hA x hx'
    exact ⟨T, hT.trans (subset_insert _ _), h1, h2⟩
  · obtain ⟨T, hT, h1, h2⟩ := hA (x - val b) (by omega)
    have hbT : b ∉ T := fun h => hb (hT h)
    refine ⟨insert b T, insert_subset_insert _ hT, ?_, ?_⟩ <;> rw [sum_insert hbT] <;> omega

/-- Lemma 1 (Brown's lemma with gap `G`), in threshold form. -/
lemma gap_of_grow (S : Finset ℕ) (hS : ∀ d ∈ S, 2 ≤ d) (P : ℕ × ℕ → Prop) [DecidablePred P]
    (G : ℕ) (hgrow : ∀ v, v ≤ ∑ a ∈ trunc S P v, val a + G) (x : ℕ) :
    ∃ T : Finset (ℕ × ℕ), (∀ p ∈ T, p.1 ∈ S ∧ P p) ∧
      ∑ a ∈ T, val a ≤ x ∧ x < ∑ a ∈ T, val a + G := by
  have hQ := threshold_induction S hS P (Q := GapProp G) (f := fun s => s + G)
    (fun a b h => by simp only; omega) (gapProp_empty G)
    (fun A b hb hA hbv => gapProp_insert G A b hb hA hbv) hgrow (x + 1)
  obtain ⟨T, hT, h1, h2⟩ := hQ x (by have := hgrow (x + 1); omega)
  refine ⟨T, fun p hp => ?_, h1, h2⟩
  have := (mem_trunc hS).1 (hT hp)
  exact ⟨this.1, this.2.1⟩

/-- Signed property of a finite set of coins. -/
def SgnProp (A : Finset (ℕ × ℕ)) : Prop :=
  ∀ x : ℤ, |x| ≤ ∑ a ∈ A, (val a : ℤ) →
    ∃ U ⊆ A, ∃ V ⊆ A, Disjoint U V ∧ ∑ a ∈ U, (val a : ℤ) - ∑ a ∈ V, (val a : ℤ) = x

lemma sgnProp_empty : SgnProp ∅ := by
  intro x hx
  refine ⟨∅, subset_refl _, ∅, subset_refl _, disjoint_empty_left _, ?_⟩
  simp only [sum_empty, abs_nonpos_iff] at hx ⊢
  omega

lemma sgnProp_insert (A : Finset (ℕ × ℕ)) (b : ℕ × ℕ) (hb : b ∉ A) (hA : SgnProp A)
    (hbv : val b ≤ 2 * ∑ a ∈ A, val a + 1) : SgnProp (insert b A) := by
  intro x hx
  rw [sum_insert hb] at hx
  have hbv' : (val b : ℤ) ≤ 2 * ∑ a ∈ A, (val a : ℤ) + 1 := by exact_mod_cast hbv
  set s : ℤ := ∑ a ∈ A, (val a : ℤ) with hs
  rcases abs_le.mp hx with ⟨hx1, hx2⟩
  by_cases h1 : |x| ≤ s
  · obtain ⟨U, hU, V, hV, hUV, h⟩ := hA x h1
    exact ⟨U, hU.trans (subset_insert _ _), V, hV.trans (subset_insert _ _), hUV, h⟩
  · rw [abs_le, not_and_or] at h1
    simp only [not_le] at h1
    rcases h1 with h1 | h1
    · -- x < -s: put b into V
      obtain ⟨U, hU, V, hV, hUV, h⟩ := hA (x + val b) (abs_le.mpr ⟨by linarith, by linarith⟩)
      have hbV : b ∉ V := fun h => hb (hV h)
      have hbU : b ∉ U := fun h => hb (hU h)
      refine ⟨U, hU.trans (subset_insert _ _), insert b V, insert_subset_insert _ hV,
        disjoint_insert_right.mpr ⟨hbU, hUV⟩, ?_⟩
      rw [sum_insert hbV]
      linarith
    · -- x > s: put b into U
      obtain ⟨U, hU, V, hV, hUV, h⟩ := hA (x - val b) (abs_le.mpr ⟨by linarith, by linarith⟩)
      have hbV : b ∉ V := fun h => hb (hV h)
      have hbU : b ∉ U := fun h => hb (hU h)
      refine ⟨insert b U, insert_subset_insert _ hU, V, hV.trans (subset_insert _ _),
        disjoint_insert_left.mpr ⟨hbV, hUV⟩, ?_⟩
      rw [sum_insert hbU]
      linarith

/-- Lemma 6 in threshold form: every integer of absolute value at most the total of a
truncation is a signed sum of its coins. -/
lemma sgn_of_grow (S : Finset ℕ) (hS : ∀ d ∈ S, 2 ≤ d) (P : ℕ × ℕ → Prop) [DecidablePred P]
    (hgrow : ∀ v, v ≤ 2 * ∑ a ∈ trunc S P v, val a + 1) (x : ℤ) :
    ∃ U V : Finset (ℕ × ℕ), (∀ p ∈ U, p.1 ∈ S ∧ P p) ∧ (∀ p ∈ V, p.1 ∈ S ∧ P p) ∧
      Disjoint U V ∧ ∑ a ∈ U, (val a : ℤ) - ∑ a ∈ V, (val a : ℤ) = x := by
  have hQ := threshold_induction S hS P (Q := SgnProp) (f := fun s => 2 * s + 1)
    (fun a b h => by simp only; omega) sgnProp_empty
    (fun A b hb hA hbv => sgnProp_insert A b hb hA hbv) hgrow (2 * x.natAbs + 1)
  have hle : x.natAbs ≤ ∑ a ∈ trunc S P (2 * x.natAbs + 1), val a := by
    have := hgrow (2 * x.natAbs + 1)
    omega
  have hle' : |x| ≤ ∑ a ∈ trunc S P (2 * x.natAbs + 1), (val a : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hle
  obtain ⟨U, hU, V, hV, hUV, h⟩ := hQ x hle'
  refine ⟨U, V, fun p hp => ?_, fun p hp => ?_, hUV, h⟩
  · have := (mem_trunc hS).1 (hU hp)
    exact ⟨this.1, this.2.1⟩
  · have := (mem_trunc hS).1 (hV hp)
    exact ⟨this.1, this.2.1⟩

/-- A finite set of coins with bases in `D` and exponents `≥ k` sums to an element of the
sumset `∑ d ∈ D, sumsOfDistinctPowers d k`. -/
lemma sum_mem_sumset (D : Finset ℕ) (k : ℕ) (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ S, p.1 ∈ D ∧ k ≤ p.2) :
    ∑ p ∈ S, val p ∈ ∑ d ∈ D, sumsOfDistinctPowers d k := by
  rw [Set.mem_finsetSum]
  refine ⟨fun d => ∑ p ∈ S.filter (fun p => p.1 = d), val p, fun {d} hd => ?_, ?_⟩
  · refine ⟨(S.filter (fun p => p.1 = d)).image Prod.snd, ?_, ?_⟩
    · intro i hi
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hi
      exact (hS p (mem_filter.mp hp).1).2
    · rw [sum_image]
      · apply sum_congr rfl
        intro p hp
        rw [val, (mem_filter.mp hp).2]
      · intro p hp q hq hpq
        have h1 := (mem_filter.mp hp).2
        have h2 := (mem_filter.mp hq).2
        exact Prod.ext (h1.trans h2.symm) hpq
  · exact sum_fiberwise_of_maps_to (fun p hp => (hS p hp).1) _


/-- For each base `d ≥ 2` there is a first exponent `b ≥ k` with `v ≤ d ^ b`. -/
lemma exists_cover (d k v : ℕ) (hd : 2 ≤ d) :
    ∃ b, k ≤ b ∧ v ≤ d ^ b ∧ ∀ j, k ≤ j → j < b → d ^ j < v := by
  classical
  have hex : ∃ b, k ≤ b ∧ v ≤ d ^ b := by
    refine ⟨k + v, by omega, ?_⟩
    calc v ≤ 2 ^ v := (Nat.lt_two_pow_self).le
      _ ≤ d ^ v := Nat.pow_le_pow_left hd _
      _ ≤ d ^ (k + v) := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun j hj hjb => ?_⟩
  have := Nat.find_min hex hjb
  simp only [not_and, not_le] at this
  exact this hj

/-- `exists_cover` as a function of the base. -/
lemma cover_fun (k v : ℕ) :
    ∃ b : ℕ → ℕ, ∀ d, 2 ≤ d → k ≤ b d ∧ v ≤ d ^ b d ∧ ∀ j, k ≤ j → j < b d → d ^ j < v := by
  classical
  refine ⟨fun d => if h : 2 ≤ d then (exists_cover d k v h).choose else 0, fun d hd => ?_⟩
  simp only [dif_pos hd]
  exact (exists_cover d k v hd).choose_spec

lemma geom_Ico (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (hkb : k ≤ b) :
    ∑ j ∈ Ico k b, (d : ℝ) ^ j = (d : ℝ) ^ b / ((d : ℝ) - 1) - (d : ℝ) ^ k / ((d : ℝ) - 1) := by
  have h1 : (1 : ℝ) < d := by exact_mod_cast hd
  have h := geom_sum_Ico_mul (d : ℝ) hkb
  rw [← sub_div, eq_div_iff (by linarith : (d : ℝ) - 1 ≠ 0)]
  exact h

/-- The coins of exponent `≥ k` and value `< v` sum to at least
`∑ d, (d ^ b d - d ^ k) / (d - 1)` whenever every `d ^ j` with `k ≤ j < b d` is `< v`. -/
lemma sum_trunc_ge (E : Finset ℕ) (hE : ∀ d ∈ E, 2 ≤ d) (k v : ℕ) (b : ℕ → ℕ)
    (hb : ∀ d ∈ E, k ≤ b d ∧ ∀ j, k ≤ j → j < b d → d ^ j < v) :
    ∑ d ∈ E, (d : ℝ) ^ (b d) / ((d : ℝ) - 1) ≤
      (∑ p ∈ trunc E (fun p => k ≤ p.2) v, (val p : ℝ)) +
        ∑ d ∈ E, (d : ℝ) ^ k / ((d : ℝ) - 1) := by
  have hfib : ∑ p ∈ trunc E (fun p => k ≤ p.2) v, (val p : ℝ) =
      ∑ d ∈ E, ∑ p ∈ (trunc E (fun p => k ≤ p.2) v).filter (fun p => p.1 = d), (val p : ℝ) :=
    (sum_fiberwise_of_maps_to (fun p hp => ((mem_trunc hE).1 hp).1) _).symm
  rw [hfib, ← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  obtain ⟨hkb, hlt⟩ := hb d hd
  rw [← sub_le_iff_le_add, ← geom_Ico d (hE d hd) k (b d) hkb]
  have himg : ∑ j ∈ Ico k (b d), (d : ℝ) ^ j =
      ∑ p ∈ (Ico k (b d)).image (fun j => (d, j)), (val p : ℝ) := by
    rw [sum_image (fun x _ y _ h => by simpa using h)]
    simp [val]
  rw [himg]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hp
    rw [mem_Ico] at hj
    rw [mem_filter, mem_trunc hE]
    exact ⟨⟨hd, hj.1, hlt j hj.1 hj.2⟩, rfl⟩
  · intros
    positivity

/-- Lemma 2 (integrality): if `d ^ g d ≥ τ > 1` for all `d ∈ E` and `σ(E) > 1`, then
`∑ d ^ g d / (d - 1) ≥ σ(E) + τ`. -/
lemma key (E : Finset ℕ) (hE : ∀ d ∈ E, 2 ≤ d) (hσ : 1 < ∑ d ∈ E, 1 / ((d : ℝ) - 1)) (τ : ℝ)
    (hτ : 1 < τ) (g : ℕ → ℕ) (hg : ∀ d ∈ E, τ ≤ (d : ℝ) ^ (g d)) :
    (∑ d ∈ E, 1 / ((d : ℝ) - 1)) + τ ≤ ∑ d ∈ E, (d : ℝ) ^ (g d) / ((d : ℝ) - 1) := by
  have hn2 : 2 ≤ ⌈τ⌉₊ := by
    have : 1 < ⌈τ⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast hτ)
    omega
  have hτn : τ ≤ (⌈τ⌉₊ : ℝ) := Nat.le_ceil τ
  have hgeom : ∀ d ∈ E, (d : ℝ) ^ (g d) / ((d : ℝ) - 1) =
      1 / ((d : ℝ) - 1) + ((∑ i ∈ range (g d), d ^ i : ℕ) : ℝ) := by
    intro d hd
    have h1 : (1 : ℝ) < d := by exact_mod_cast hE d hd
    have h := geom_sum_mul (d : ℝ) (g d)
    have hne : (d : ℝ) - 1 ≠ 0 := by linarith
    push_cast
    field_simp
    linarith
  rw [sum_congr rfl hgeom, sum_add_distrib]
  have hlow : ∀ d ∈ E, ((⌈τ⌉₊ : ℝ) - 1) * (1 / ((d : ℝ) - 1)) ≤
      ((∑ i ∈ range (g d), d ^ i : ℕ) : ℝ) := by
    intro d hd
    have h1 : (1 : ℝ) < d := by exact_mod_cast hE d hd
    have h := geom_sum_mul (d : ℝ) (g d)
    have hng : (⌈τ⌉₊ : ℝ) ≤ (d : ℝ) ^ (g d) := by
      have : ⌈τ⌉₊ ≤ d ^ (g d) := Nat.ceil_le.mpr (by exact_mod_cast hg d hd)
      exact_mod_cast this
    rw [mul_one_div, div_le_iff₀ (by linarith)]
    push_cast
    linarith
  have hsum : (∑ d ∈ E, 1 / ((d : ℝ) - 1)) * ((⌈τ⌉₊ : ℝ) - 1) ≤
      ∑ d ∈ E, ((∑ i ∈ range (g d), d ^ i : ℕ) : ℝ) := by
    rw [mul_comm, mul_sum]
    exact sum_le_sum hlow
  have hn1 : (1 : ℝ) ≤ (⌈τ⌉₊ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ ⌈τ⌉₊ := by exact_mod_cast hn2
    linarith
  have hgt : (⌈τ⌉₊ : ℝ) - 1 < ∑ d ∈ E, ((∑ i ∈ range (g d), d ^ i : ℕ) : ℝ) := by
    nlinarith
  rw [← Nat.cast_sum] at hgt ⊢
  have h3 : ⌈τ⌉₊ < (∑ d ∈ E, ∑ i ∈ range (g d), d ^ i) + 1 := by
    have : (⌈τ⌉₊ : ℝ) < ((∑ d ∈ E, ∑ i ∈ range (g d), d ^ i : ℕ) : ℝ) + 1 := by linarith
    exact_mod_cast this
  have h4 : (⌈τ⌉₊ : ℝ) ≤ ((∑ d ∈ E, ∑ i ∈ range (g d), d ^ i : ℕ) : ℝ) := by
    exact_mod_cast (by omega : ⌈τ⌉₊ ≤ ∑ d ∈ E, ∑ i ∈ range (g d), d ^ i)
  linarith

/-- The constants of Lemma 4: `ρ = 1 + (σ - 1) / 2`. -/
noncomputable def rhoC (σ : ℝ) : ℝ := 1 + (σ - 1) / 2

/-- `L = ρ / (σ - 1)`. -/
noncomputable def LC (σ : ℝ) : ℝ := rhoC σ / (σ - 1)

/-- `ε = (σ - 1) / (4 (σ + 2 L + 1))`. -/
noncomputable def epsC (σ : ℝ) : ℝ := (σ - 1) / (4 * (σ + 2 * LC σ + 1))

lemma consts (σ : ℝ) (hσ : 1 < σ) :
    0 < epsC σ ∧ epsC σ ≤ 1 / 2 ∧ 4 * epsC σ ≤ σ - 1 ∧ (σ - 1) * LC σ = rhoC σ ∧
      rhoC σ ≤ (1 - epsC σ) * σ - 2 * epsC σ * LC σ ∧ 1 < rhoC σ ∧ 0 < LC σ := by
  have hs : 0 < σ - 1 := by linarith
  have hρ : 1 < rhoC σ := by unfold rhoC; linarith
  have hL : 0 < LC σ := by unfold LC; positivity
  have hLe : (σ - 1) * LC σ = rhoC σ := by unfold LC; field_simp
  have hD : 0 < σ + 2 * LC σ + 1 := by linarith
  have hε : epsC σ * (σ + 2 * LC σ + 1) = (σ - 1) / 4 := by unfold epsC; field_simp
  have hεpos : 0 < epsC σ := by unfold epsC; positivity
  refine ⟨hεpos, ?_, ?_, hLe, ?_, hρ, hL⟩
  · nlinarith
  · nlinarith
  · unfold rhoC at hρ ⊢
    nlinarith

/-- `y` is an `ε`-cluster value for `E`: every `d ∈ E` has a power within the factor `1 - ε`
of `y` on both sides. -/
def IsCluster (E : Finset ℕ) (ε : ℝ) (y : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, ∀ d ∈ E, (1 - ε) * (y : ℝ) ≤ (d : ℝ) ^ (f d) ∧ (1 - ε) * (d : ℝ) ^ (f d) ≤ y

/-- Lemma 3 and the case analysis of Lemma 4 at one deleted coin `y = c ^ e < v`. -/
lemma bound_one (E : Finset ℕ) (hE : ∀ d ∈ E, 2 ≤ d) (k c : ℕ) (hc : c ∈ E)
    (hσ : 1 < ∑ d ∈ E, 1 / ((d : ℝ) - 1)) (e : ℕ)
    (hcl : IsCluster E (epsC (∑ d ∈ E, 1 / ((d : ℝ) - 1))) (c ^ e)) (v : ℕ) (hv : c ^ e < v) :
    (v : ℝ) + rhoC (∑ d ∈ E, 1 / ((d : ℝ) - 1)) * (c : ℝ) ^ e ≤
      (∑ p ∈ trunc E (fun p => k ≤ p.2) v, (val p : ℝ)) +
        ∑ d ∈ E, (d : ℝ) ^ k / ((d : ℝ) - 1) := by
  set σ := ∑ d ∈ E, 1 / ((d : ℝ) - 1) with hσdef
  obtain ⟨hε0, hε1, hε2, hLe, hρL, hρ1, hL0⟩ := consts σ hσ
  set ε := epsC σ
  set ρ := rhoC σ
  set L := LC σ
  obtain ⟨b, hb⟩ := cover_fun k v
  have hT := sum_trunc_ge E hE k v b (fun d hd => ⟨(hb d (hE d hd)).1, (hb d (hE d hd)).2.2⟩)
  set T := (∑ p ∈ trunc E (fun p => k ≤ p.2) v, (val p : ℝ)) +
    ∑ d ∈ E, (d : ℝ) ^ k / ((d : ℝ) - 1)
  have hvb : ∀ d ∈ E, (v : ℝ) ≤ (d : ℝ) ^ (b d) := fun d hd => by
    exact_mod_cast (hb d (hE d hd)).2.1
  have hdpos : ∀ d ∈ E, (0 : ℝ) < (d : ℝ) - 1 := fun d hd => by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hE d hd
    linarith
  set y : ℝ := (c : ℝ) ^ e with hy
  have hyv : y < v := by rw [hy]; exact_mod_cast hv
  have hy0 : 0 < y := by
    rw [hy]; have : (2 : ℝ) ≤ c := by exact_mod_cast hE c hc
    positivity
  -- the generic bound σ v ≤ T
  have hgen : σ * v ≤ T := by
    refine le_trans ?_ hT
    rw [hσdef, sum_mul]
    apply sum_le_sum
    intro d hd
    rw [div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_right (hvb d hd) (hdpos d hd).le
  by_cases hA : L * y ≤ v
  · -- case (a): v ≥ L y
    have : (σ - 1) * (L * y) ≤ (σ - 1) * v := mul_le_mul_of_nonneg_left hA (by linarith)
    nlinarith
  by_cases hB : (1 - ε) * v ≤ y
  · -- case (b): v ≤ y / (1 - ε); use the next power of `c`
    have hc2 : (2 : ℝ) ≤ c := by exact_mod_cast hE c hc
    have hbc : e + 1 ≤ b c := by
      by_contra hcon
      have h1 : c ^ b c ≤ c ^ e :=
        Nat.pow_le_pow_right (by have := hE c hc; omega) (by omega)
      have h2 := (hb c (hE c hc)).2.1
      omega
    have hcb : (c : ℝ) * y ≤ (c : ℝ) ^ (b c) := by
      rw [hy, ← pow_succ']
      exact pow_le_pow_right₀ (by linarith) hbc
    set a : ℝ := 1 / ((c : ℝ) - 1) with ha
    have ha0 : 0 < a := by rw [ha]; have := hdpos c hc; positivity
    have ha1 : a ≤ 1 := by rw [ha, div_le_one (hdpos c hc)]; linarith
    have hca : (c : ℝ) * a = 1 + a := by
      have hne : (c : ℝ) - 1 ≠ 0 := (hdpos c hc).ne'
      rw [ha]; field_simp; ring
    have hsplit := add_sum_erase E (fun d => (d : ℝ) ^ (b d) / ((d : ℝ) - 1)) hc
    have hsplitσ := add_sum_erase E (fun d => 1 / ((d : ℝ) - 1)) hc
    have hrest : (σ - a) * v ≤
        ∑ d ∈ E.erase c, (d : ℝ) ^ (b d) / ((d : ℝ) - 1) := by
      have hσs : σ - a = ∑ d ∈ E.erase c, 1 / ((d : ℝ) - 1) := by rw [ha]; linarith [hsplitσ]
      rw [hσs, sum_mul]
      apply sum_le_sum
      intro d hd
      have hd' := mem_of_mem_erase hd
      rw [div_mul_eq_mul_div, one_mul]
      exact div_le_div_of_nonneg_right (hvb d hd') (hdpos d hd').le
    have hcterm : (1 + a) * y ≤ (c : ℝ) ^ (b c) / ((c : ℝ) - 1) := by
      rw [← hca, mul_comm (c : ℝ) a, mul_assoc, ha, one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right hcb (hdpos c hc).le
    have hv2 : (v : ℝ) ≤ 2 * y := by nlinarith
    have h1 : (σ - 1) * y ≤ (σ - 1) * v := mul_le_mul_of_nonneg_left hyv.le (by linarith)
    have h2 : a * ((v : ℝ) - y) ≤ a * (ε * v) := mul_le_mul_of_nonneg_left (by linarith) ha0.le
    have h3 : a * (ε * v) ≤ 1 * (ε * (2 * y)) :=
      mul_le_mul ha1 (mul_le_mul_of_nonneg_left hv2 hε0.le) (by positivity) (by norm_num)
    have hρσ : ρ = 1 + (σ - 1) / 2 := rfl
    nlinarith
  · -- case (c): the cluster case
    rw [not_le] at hA hB
    obtain ⟨f, hf0⟩ := hcl
    have hf : ∀ d ∈ E, (1 - ε) * y ≤ (d : ℝ) ^ (f d) ∧ (1 - ε) * (d : ℝ) ^ (f d) ≤ y := by
      intro d hd
      have := hf0 d hd
      push_cast at this
      exact this
    set τ : ℝ := (1 - ε) * v / y with hτ
    have hτ1 : 1 < τ := by rw [hτ, lt_div_iff₀ hy0]; linarith
    have hfv : ∀ d ∈ E, (d : ℝ) ^ (f d) * τ ≤ v := by
      intro d hd
      have h1 := (hf d hd).2
      have hv0 : (0 : ℝ) ≤ v := by positivity
      rw [hτ, show (d : ℝ) ^ (f d) * ((1 - ε) * v / y) = ((1 - ε) * (d : ℝ) ^ (f d)) * v / y by ring,
        div_le_iff₀ hy0]
      calc ((1 - ε) * (d : ℝ) ^ (f d)) * v ≤ y * v := mul_le_mul_of_nonneg_right h1 hv0
        _ = v * y := mul_comm _ _
    have hfpos : ∀ d ∈ E, (0 : ℝ) < (d : ℝ) ^ (f d) := fun d hd => by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hE d hd
      positivity
    have hfb : ∀ d ∈ E, f d < b d := by
      intro d hd
      by_contra hcon
      rw [not_lt] at hcon
      have h1 : (d : ℝ) ^ (b d) ≤ (d : ℝ) ^ (f d) :=
        pow_le_pow_right₀ (by have h2 : (2 : ℝ) ≤ d := (by exact_mod_cast hE d hd); linarith) hcon
      have := hvb d hd
      have := hfv d hd
      have := hfpos d hd
      nlinarith
    have hg : ∀ d ∈ E, τ ≤ (d : ℝ) ^ (b d - f d) := by
      intro d hd
      have hsplitp : (d : ℝ) ^ (b d) = (d : ℝ) ^ (f d) * (d : ℝ) ^ (b d - f d) := by
        rw [← pow_add]; congr 1; have := hfb d hd; omega
      have h1 := hvb d hd
      have h2 := hfv d hd
      have h3 := hfpos d hd
      rw [hsplitp] at h1
      nlinarith
    have hkey := key E hE hσ τ hτ1 (fun d => b d - f d) hg
    have hlow : (1 - ε) * y * ∑ d ∈ E, (d : ℝ) ^ (b d - f d) / ((d : ℝ) - 1) ≤
        ∑ d ∈ E, (d : ℝ) ^ (b d) / ((d : ℝ) - 1) := by
      rw [mul_sum]
      apply sum_le_sum
      intro d hd
      have hsplitp : (d : ℝ) ^ (b d) = (d : ℝ) ^ (f d) * (d : ℝ) ^ (b d - f d) := by
        rw [← pow_add]; congr 1; have := hfb d hd; omega
      rw [hsplitp, mul_div_assoc']
      apply div_le_div_of_nonneg_right _ (hdpos d hd).le
      exact mul_le_mul_of_nonneg_right (hf d hd).1 (by positivity)
    have hε' : 0 ≤ 1 - ε := by linarith
    have hm : (1 - ε) * y * (σ + τ) ≤ (1 - ε) * y * ∑ d ∈ E, (d : ℝ) ^ (b d - f d) / ((d : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    have hyτ : y * τ = (1 - ε) * v := by rw [hτ]; field_simp
    have hvL : (v : ℝ) ≤ L * y := hA.le
    have h4 : ε * v ≤ ε * (L * y) := mul_le_mul_of_nonneg_left hvL hε0.le
    have h5 : 0 ≤ ε * ε * v := by positivity
    nlinarith

/-- The generic bound `σ(E) v ≤ T(v) + C_k(E)`. -/
lemma bound_gen (E : Finset ℕ) (hE : ∀ d ∈ E, 2 ≤ d) (k v : ℕ) :
    (∑ d ∈ E, 1 / ((d : ℝ) - 1)) * v ≤
      (∑ p ∈ trunc E (fun p => k ≤ p.2) v, (val p : ℝ)) +
        ∑ d ∈ E, (d : ℝ) ^ k / ((d : ℝ) - 1) := by
  obtain ⟨b, hb⟩ := cover_fun k v
  have hT := sum_trunc_ge E hE k v b (fun d hd => ⟨(hb d (hE d hd)).1, (hb d (hE d hd)).2.2⟩)
  refine le_trans ?_ hT
  rw [sum_mul]
  apply sum_le_sum
  intro d hd
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hE d hd
  rw [div_mul_eq_mul_div, one_mul]
  exact div_le_div_of_nonneg_right (by exact_mod_cast (hb d (hE d hd)).2.1) (by linarith)

/-- Lemma 4 (deletion lemma), quantitative form: deleting the coins `c ^ e`, `e ∈ R`, of
`ε`-cluster values whose partial sums are at most `ρ` times their last term. -/
lemma bound_R (E : Finset ℕ) (hE : ∀ d ∈ E, 2 ≤ d) (k c : ℕ) (hc : c ∈ E)
    (hσ : 1 < ∑ d ∈ E, 1 / ((d : ℝ) - 1)) (R : Finset ℕ)
    (hR : ∀ e ∈ R, IsCluster E (epsC (∑ d ∈ E, 1 / ((d : ℝ) - 1))) (c ^ e))
    (hlac : ∀ e ∈ R, ∑ e' ∈ R.filter (· ≤ e), (c : ℝ) ^ e' ≤
      rhoC (∑ d ∈ E, 1 / ((d : ℝ) - 1)) * (c : ℝ) ^ e) (v : ℕ) :
    (v : ℝ) + ∑ e ∈ R.filter (fun e => c ^ e < v), (c : ℝ) ^ e ≤
      (∑ p ∈ trunc E (fun p => k ≤ p.2) v, (val p : ℝ)) +
        ∑ d ∈ E, (d : ℝ) ^ k / ((d : ℝ) - 1) := by
  have hc2 := hE c hc
  by_cases hne : (R.filter (fun e => c ^ e < v)).Nonempty
  · have he₀ := max'_mem _ hne
    set e₀ := (R.filter (fun e => c ^ e < v)).max' hne
    rw [mem_filter] at he₀
    have hfeq : R.filter (fun e => c ^ e < v) = R.filter (· ≤ e₀) := by
      ext e
      simp only [mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, le_max' _ _ (mem_filter.mpr ⟨h1, h2⟩)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) h2) he₀.2⟩
    rw [hfeq]
    have h1 := bound_one E hE k c hc hσ e₀ (hR e₀ he₀.1) v he₀.2
    have h2 := hlac e₀ he₀.1
    linarith
  · rw [not_nonempty_iff_eq_empty.mp hne, sum_empty, add_zero]
    have h1 := bound_gen E hE k v
    have hv : (0 : ℝ) ≤ v := by positivity
    nlinarith

/-- Lemma 4 in the form needed by Lemma 1: the coins of `E` with exponent `≥ k`, minus the
deleted coins `(c, e)`, `e ∈ R`, satisfy the growth condition with gap `G ≥ C_k(E)`. -/
lemma growB (E : Finset ℕ) (hE : ∀ d ∈ E, 2 ≤ d) (k c : ℕ) (hc : c ∈ E)
    (hσ : 1 < ∑ d ∈ E, 1 / ((d : ℝ) - 1)) (R : Finset ℕ)
    (hR : ∀ e ∈ R, IsCluster E (epsC (∑ d ∈ E, 1 / ((d : ℝ) - 1))) (c ^ e))
    (hlac : ∀ e ∈ R, ∑ e' ∈ R.filter (· ≤ e), (c : ℝ) ^ e' ≤
      rhoC (∑ d ∈ E, 1 / ((d : ℝ) - 1)) * (c : ℝ) ^ e) (G : ℕ)
    (hG : ∑ d ∈ E, (d : ℝ) ^ k / ((d : ℝ) - 1) ≤ G) (v : ℕ) :
    v ≤ ∑ a ∈ trunc E (fun p => k ≤ p.2 ∧ ¬ (p.1 = c ∧ p.2 ∈ R)) v, val a + G := by
  have hsplit := sum_filter_add_sum_filter_not (trunc E (fun p => k ≤ p.2) v)
    (fun p => ¬ (p.1 = c ∧ p.2 ∈ R)) (fun p => (val p : ℝ))
  have heq : trunc E (fun p => k ≤ p.2 ∧ ¬ (p.1 = c ∧ p.2 ∈ R)) v =
      (trunc E (fun p => k ≤ p.2) v).filter (fun p => ¬ (p.1 = c ∧ p.2 ∈ R)) := by
    ext p
    simp only [mem_filter, mem_trunc hE]
    tauto
  have hRle : ∑ p ∈ (trunc E (fun p => k ≤ p.2) v).filter (fun p => ¬¬ (p.1 = c ∧ p.2 ∈ R)),
      (val p : ℝ) ≤ ∑ e ∈ R.filter (fun e => c ^ e < v), (c : ℝ) ^ e := by
    rw [show ∑ e ∈ R.filter (fun e => c ^ e < v), (c : ℝ) ^ e =
        ∑ p ∈ (R.filter (fun e => c ^ e < v)).image (fun e => (c, e)), (val p : ℝ) by
      rw [sum_image (fun x _ y _ h => by simpa using h)]
      simp [val]]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [mem_filter, mem_trunc hE, not_not] at hp
      rw [mem_image]
      refine ⟨p.2, mem_filter.mpr ⟨hp.2.2, ?_⟩, ?_⟩
      · have := hp.1.2.2
        rw [val, hp.2.1] at this
        exact this
      · ext
        · simp [hp.2.1]
        · rfl
    · intros
      positivity
  have hb := bound_R E hE k c hc hσ R hR hlac v
  rw [heq]
  have : (v : ℝ) ≤ ∑ a ∈ (trunc E (fun p => k ≤ p.2) v).filter
      (fun p => ¬ (p.1 = c ∧ p.2 ∈ R)), (val a : ℝ) + G := by linarith
  exact_mod_cast this

/-- Simultaneous Dirichlet approximation, by induction from the one-dimensional theorem. -/
lemma sim_dirichlet (S : Finset ℕ) (α : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ q : ℕ, 0 < q ∧ ∀ i ∈ S, ∃ z : ℤ, |(q : ℝ) * α i - z| ≤ δ := by
  induction S using Finset.induction_on generalizing δ with
  | empty => exact ⟨1, one_pos, fun i hi => absurd hi (notMem_empty _)⟩
  | insert i₀ S hi₀ ih =>
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
    have hNpos : 0 < N := by
      have : (0 : ℝ) < N := lt_trans (by positivity) hN
      exact_mod_cast this
    have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
    obtain ⟨q', hq', hS⟩ := ih (δ / N) (by positivity)
    obtain ⟨m, hm0, hmN, hm⟩ := Real.exists_nat_abs_mul_sub_round_le ((q' : ℝ) * α i₀) hNpos
    refine ⟨m * q', Nat.mul_pos hm0 hq', fun i hi => ?_⟩
    rcases mem_insert.mp hi with rfl | hi
    · refine ⟨round ((m : ℝ) * ((q' : ℝ) * α i)), ?_⟩
      have h1 : 1 / ((N : ℝ) + 1) ≤ δ := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ hδ] at hN
        linarith
      push_cast
      rw [mul_assoc]
      linarith
    · obtain ⟨z, hz⟩ := hS i hi
      refine ⟨m * z, ?_⟩
      have hmr : (m : ℝ) ≤ N := by exact_mod_cast hmN
      have hm0r : (0 : ℝ) ≤ m := by positivity
      push_cast
      rw [show (m : ℝ) * q' * α i - m * z = m * (q' * α i - z) by ring, abs_mul,
        abs_of_nonneg hm0r]
      calc (m : ℝ) * |q' * α i - z| ≤ N * (δ / N) :=
            mul_le_mul hmr hz (abs_nonneg _) hNr.le
        _ = δ := by field_simp

lemma pow_eq_exp (x : ℝ) (n : ℕ) (hx : 0 < x) : x ^ n = Real.exp (n * Real.log x) := by
  rw [Real.exp_nat_mul, Real.exp_log hx]

/-- Lemma 5: `ε`-cluster values `c ^ e` with `P ∣ e` and `e` arbitrarily large. -/
lemma exists_cluster (E : Finset ℕ) (hE : ∀ d ∈ E, 2 ≤ d) (c : ℕ) (hc : 2 ≤ c) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (P X : ℕ) (hP : 0 < P) :
    ∃ e, P ∣ e ∧ X ≤ e ∧ IsCluster E ε (c ^ e) := by
  have hlogc : 0 < Real.log c := Real.log_pos (by exact_mod_cast hc)
  have hlogd : ∀ d ∈ E, 0 < Real.log d := fun d hd =>
    Real.log_pos (by exact_mod_cast (hE d hd))
  set Λ : ℝ := ∑ d ∈ E, Real.log d with hΛ
  have hΛ0 : 0 ≤ Λ := sum_nonneg (fun d hd => (hlogd d hd).le)
  set δ : ℝ := ε / (1 + Λ) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]
    linarith
  set M : ℕ := P * (X + 1) with hM
  obtain ⟨q, hq, hz⟩ := sim_dirichlet E (fun d => (M : ℝ) * Real.log c / Real.log d) δ hδ0
  refine ⟨q * M, ⟨q * (X + 1), by rw [hM]; ring⟩, ?_, ?_⟩
  · have : X + 1 ≤ q * M := by
      rw [hM]
      calc X + 1 ≤ P * (X + 1) := Nat.le_mul_of_pos_left _ hP
        _ ≤ q * (P * (X + 1)) := Nat.le_mul_of_pos_left _ hq
    omega
  obtain ⟨z, hz'⟩ : ∃ z : ℕ → ℤ, ∀ d ∈ E,
      |(q : ℝ) * ((M : ℝ) * Real.log c / Real.log d) - z d| ≤ δ :=
    ⟨fun d => if h : d ∈ E then (hz d h).choose else 0, fun d hd => by
      simp only [dif_pos hd]
      exact (hz d hd).choose_spec⟩
  refine ⟨fun d => (z d).toNat, fun d hd => ?_⟩
  have hzd := hz' d hd
  have hld := hlogd d hd
  set e : ℕ := q * M with he
  have heq : (q : ℝ) * ((M : ℝ) * Real.log c / Real.log d) * Real.log d = e * Real.log c := by
    rw [he]
    push_cast
    field_simp
  have hpos : 0 < (q : ℝ) * ((M : ℝ) * Real.log c / Real.log d) := by
    have : (0 : ℝ) < q := by exact_mod_cast hq
    have : (0 : ℝ) < M := by
      have : 0 < M := by rw [hM]; positivity
      exact_mod_cast this
    positivity
  have hz0 : 0 ≤ z d := by
    have h1 := (abs_le.mp hzd).2
    have : (-1 : ℝ) < z d := by linarith
    have : (-1 : ℤ) < z d := by exact_mod_cast this
    omega
  have hcast : (((z d).toNat : ℕ) : ℝ) = ((z d : ℤ) : ℝ) := by
    have := Int.toNat_of_nonneg hz0
    exact_mod_cast this
  -- the exponent gap
  set A : ℝ := (((z d).toNat : ℕ) : ℝ) * Real.log d with hA
  set B : ℝ := (e : ℝ) * Real.log c with hB
  have hAB : |A - B| ≤ ε := by
    have h1 : A - B = ((z d : ℝ) - (q : ℝ) * ((M : ℝ) * Real.log c / Real.log d)) *
        Real.log d := by
      rw [hA, hB, hcast]
      linear_combination heq
    rw [h1, abs_mul, abs_of_pos hld, abs_sub_comm]
    have h2 : Real.log d ≤ Λ := single_le_sum (fun d hd => (hlogd d hd).le) hd
    calc |(q : ℝ) * ((M : ℝ) * Real.log c / Real.log d) - z d| * Real.log d ≤ δ * Λ :=
          mul_le_mul hzd h2 hld.le hδ0.le
      _ ≤ ε := by
          rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  have hdA : ((d : ℝ)) ^ ((z d).toNat) = Real.exp A := by
    rw [hA, pow_eq_exp _ _ (by have := hE d hd; positivity)]
  have hcB : (((c ^ e : ℕ)) : ℝ) = Real.exp B := by
    push_cast
    rw [hB, pow_eq_exp _ _ (by positivity)]
  rw [hdA, hcB]
  have hexpA : Real.exp A = Real.exp B * Real.exp (A - B) := by
    rw [← Real.exp_add]; ring_nf
  have hexpB : Real.exp B = Real.exp A * Real.exp (B - A) := by
    rw [← Real.exp_add]; ring_nf
  have h1 := Real.add_one_le_exp (A - B)
  have h2 := Real.add_one_le_exp (B - A)
  have hpA := Real.exp_pos A
  have hpB := Real.exp_pos B
  have hab := abs_le.mp hAB
  constructor
  · rw [hexpA]
    nlinarith
  · rw [hexpB]
    nlinarith

/-- Lemma 6: with `2 σ(C) ≥ 1`, every integer is a signed sum of distinct coins of `C`
(cutoff `0`). -/
lemma signed_rep (C : Finset ℕ) (hC : ∀ d ∈ C, 2 ≤ d)
    (hσC : 1 ≤ 2 * ∑ d ∈ C, 1 / ((d : ℝ) - 1)) (x : ℤ) :
    ∃ U V : Finset (ℕ × ℕ), (∀ p ∈ U, p.1 ∈ C) ∧ (∀ p ∈ V, p.1 ∈ C) ∧ Disjoint U V ∧
      ∑ a ∈ U, (val a : ℤ) - ∑ a ∈ V, (val a : ℤ) = x := by
  have hgrow : ∀ v, v ≤ 2 * ∑ a ∈ trunc C (fun p => 0 ≤ p.2) v, val a + 1 := by
    intro v
    have h := bound_gen C hC 0 v
    simp only [pow_zero] at h
    have hT : (v : ℝ) ≤ 2 * (∑ a ∈ trunc C (fun p => 0 ≤ p.2) v, (val a : ℝ)) + 1 := by
      rcases Nat.eq_zero_or_pos v with hv | hv
      · have hv0 : (v : ℝ) = 0 := by exact_mod_cast hv
        have : (0 : ℝ) ≤ ∑ a ∈ trunc C (fun p => 0 ≤ p.2) v, (val a : ℝ) :=
          sum_nonneg (fun _ _ => by positivity)
        linarith
      · have hv1 : (1 : ℝ) ≤ v := by exact_mod_cast hv
        nlinarith
    exact_mod_cast hT
  obtain ⟨U, V, hU, hV, hUV, h⟩ := sgn_of_grow C hC (fun p => 0 ≤ p.2) hgrow x
  exact ⟨U, V, fun p hp => (hU p hp).1, fun p hp => (hV p hp).1, hUV, h⟩

/-- Lemma 7 (exponent shifts): for every `t` there are `K ≥ t` and shifts `s` with
`d ^ s d = h ^ K` and `s d ≥ t` for all `d ∈ C`. -/
lemma exists_shift (C : Finset ℕ) (h : ℕ) (hpow : ∀ x ∈ C, ∃ a ≥ 1, x = h ^ a) (t : ℕ) :
    ∃ K, t ≤ K ∧ ∃ s : ℕ → ℕ, ∀ d ∈ C, d ^ s d = h ^ K ∧ t ≤ s d := by
  induction C using Finset.induction_on with
  | empty => exact ⟨t, le_rfl, fun _ => 0, fun d hd => absurd hd (notMem_empty _)⟩
  | insert c₀ C hc₀ ih =>
    obtain ⟨K', hK', s', hs'⟩ := ih (fun x hx => hpow x (mem_insert_of_mem hx))
    obtain ⟨a₀, ha₀, hc₀a⟩ := hpow c₀ (mem_insert_self _ _)
    refine ⟨a₀ * K', le_trans hK' (Nat.le_mul_of_pos_left _ ha₀),
      fun d => if d = c₀ then K' else a₀ * s' d, fun d hd => ?_⟩
    by_cases hdc : d = c₀
    · simp only [hdc, if_true]
      refine ⟨?_, hK'⟩
      rw [hc₀a, ← pow_mul]
    · simp only [hdc, if_false]
      have hd' : d ∈ C := (mem_insert.mp hd).resolve_left hdc
      obtain ⟨h1, h2⟩ := hs' d hd'
      refine ⟨?_, le_trans h2 (Nat.le_mul_of_pos_left _ ha₀)⟩
      rw [mul_comm, pow_mul, h1, ← pow_mul, mul_comm]

/-- Lemma 8 (unit gadget): if `H = d ^ s d` for every `d ∈ C` with `s d ≥ k`, `c ∉ C` and
`H ∣ c ^ e - 1`, there are disjoint `U ∋ (c, e)` and `V` with `∑ U = ∑ V + 1`, all other coins
from `C`, with exponent `≥ k` and value `≥ H`. -/
lemma gadget (C : Finset ℕ) (hC : ∀ d ∈ C, 2 ≤ d)
    (hσC : 1 ≤ 2 * ∑ d ∈ C, 1 / ((d : ℝ) - 1)) (k H : ℕ) (s : ℕ → ℕ)
    (hs : ∀ d ∈ C, d ^ s d = H ∧ k ≤ s d) (c e : ℕ) (hcC : c ∉ C) (hdiv : H ∣ c ^ e - 1)
    (hce : 1 ≤ c ^ e) :
    ∃ U V : Finset (ℕ × ℕ), Disjoint U V ∧ (c, e) ∈ U ∧
      (∀ p ∈ U ∪ V, p = (c, e) ∨ (p.1 ∈ C ∧ k ≤ p.2 ∧ H ≤ val p)) ∧
      ∑ a ∈ V, val a + 1 = ∑ a ∈ U, val a := by
  obtain ⟨M, hM⟩ := hdiv
  obtain ⟨U₀, V₀, hU₀, hV₀, hUV₀, hsum⟩ := signed_rep C hC hσC M
  set φ : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.2 + s p.1) with hφ
  have hφinj : Function.Injective φ := by
    intro p q hpq
    simp only [hφ, Prod.mk.injEq] at hpq
    obtain ⟨h1, h2⟩ := hpq
    rw [h1] at h2
    exact Prod.ext h1 (by omega)
  have hval : ∀ p, p.1 ∈ C → val (φ p) = val p * H := by
    intro p hp
    simp only [hφ, val]
    rw [pow_add, (hs p.1 hp).1]
  have hsumφ : ∀ W : Finset (ℕ × ℕ), (∀ p ∈ W, p.1 ∈ C) →
      ∑ a ∈ W.image φ, val a = (∑ a ∈ W, val a) * H := by
    intro W hW
    rw [sum_image (fun x _ y _ h => hφinj h), sum_mul]
    exact sum_congr rfl (fun p hp => hval p (hW p hp))
  have hmemφ : ∀ W : Finset (ℕ × ℕ), (∀ p ∈ W, p.1 ∈ C) → ∀ p ∈ W.image φ,
      p.1 ∈ C ∧ k ≤ p.2 ∧ H ≤ val p := by
    intro W hW p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    refine ⟨hW q hq, le_trans (hs q.1 (hW q hq)).2 (by simp [hφ]), ?_⟩
    rw [hval q (hW q hq)]
    have : 1 ≤ val q := Nat.one_le_pow _ _ (by have := hC q.1 (hW q hq); omega)
    nlinarith
  have hceV : (c, e) ∉ V₀.image φ := fun h => hcC (hmemφ V₀ hV₀ _ h).1
  have hceU : (c, e) ∉ U₀.image φ := fun h => hcC (hmemφ U₀ hU₀ _ h).1
  refine ⟨insert (c, e) (V₀.image φ), U₀.image φ, ?_, mem_insert_self _ _, ?_, ?_⟩
  · rw [disjoint_insert_left]
    exact ⟨hceU, ((disjoint_image hφinj).mpr hUV₀).symm⟩
  · intro p hp
    rcases mem_union.mp hp with hp | hp
    · rcases mem_insert.mp hp with rfl | hp
      · exact Or.inl rfl
      · exact Or.inr (hmemφ V₀ hV₀ p hp)
    · exact Or.inr (hmemφ U₀ hU₀ p hp)
  · rw [sum_insert hceV, hsumφ U₀ hU₀, hsumφ V₀ hV₀]
    have hz : ((∑ a ∈ U₀, val a : ℕ) : ℤ) - ((∑ a ∈ V₀, val a : ℕ) : ℤ) = M := by
      push_cast
      exact hsum
    have hce' : ((c ^ e - 1 : ℕ) : ℤ) = (c : ℤ) ^ e - 1 := by
      rw [Nat.cast_sub hce]
      push_cast
      ring
    have hM' : (c : ℤ) ^ e - 1 = (H : ℤ) * M := by
      rw [← hce', hM]
      push_cast
      ring
    have : ((∑ a ∈ U₀, val a : ℕ) : ℤ) * H + 1 =
        ((c ^ e : ℕ) : ℤ) + ((∑ a ∈ V₀, val a : ℕ) : ℤ) * H := by
      have hcz : ((c ^ e : ℕ) : ℤ) = (c : ℤ) ^ e := by push_cast; ring
      rw [hcz]
      linear_combination (H : ℤ) * hz - hM'
    have h2 : (∑ a ∈ U₀, val a) * H + 1 = c ^ e + (∑ a ∈ V₀, val a) * H := by
      exact_mod_cast this
    exact h2

/-- One assembly step: given a block `A` of coins of `C` and deleted coins `(c, e)`, `e ∈ R`,
representing `u, u + 1, …, u + m`, add one unit gadget to represent `u', …, u' + m + 1`. -/
lemma inv_step (E C : Finset ℕ) (hE : ∀ d ∈ E, 2 ≤ d) (hC : ∀ d ∈ C, 2 ≤ d)
    (hσC : 1 ≤ 2 * ∑ d ∈ C, 1 / ((d : ℝ) - 1)) (h : ℕ) (hh : 2 ≤ h)
    (hpow : ∀ x ∈ C, ∃ a ≥ 1, x = h ^ a) (c : ℕ) (hcE : c ∈ E) (hcC : c ∉ C)
    (hcop : c.Coprime h) (k : ℕ) (ε ρ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 1 < ρ) (m : ℕ)
    (A : Finset (ℕ × ℕ)) (R : Finset ℕ) (u : ℕ)
    (hA : ∀ p ∈ A, (p.1 ∈ C ∧ k ≤ p.2) ∨ (p.1 = c ∧ p.2 ∈ R))
    (hR : ∀ e ∈ R, k ≤ e ∧ IsCluster E ε (c ^ e))
    (hlac : ∀ e ∈ R, ∑ e' ∈ R.filter (· ≤ e), (c : ℝ) ^ e' ≤ ρ * (c : ℝ) ^ e)
    (hrep : ∀ j ≤ m, ∃ S ⊆ A, ∑ a ∈ S, val a = u + j) :
    ∃ (A' : Finset (ℕ × ℕ)) (R' : Finset ℕ) (u' : ℕ),
      (∀ p ∈ A', (p.1 ∈ C ∧ k ≤ p.2) ∨ (p.1 = c ∧ p.2 ∈ R')) ∧
      (∀ e ∈ R', k ≤ e ∧ IsCluster E ε (c ^ e)) ∧
      (∀ e ∈ R', ∑ e' ∈ R'.filter (· ≤ e), (c : ℝ) ^ e' ≤ ρ * (c : ℝ) ^ e) ∧
      (∀ j ≤ m + 1, ∃ S ⊆ A', ∑ a ∈ S, val a = u' + j) := by
  have hc2 := hE c hcE
  set X : ℕ := ∑ p ∈ A, val p + ∑ e ∈ R, c ^ e with hX
  -- the block scale `H = h ^ K > X`
  obtain ⟨K, hK, s, hs⟩ := exists_shift C h hpow (X + k + 1)
  set H := h ^ K with hHdef
  have hXH : X < H := by
    calc X < K := by omega
      _ < 2 ^ K := Nat.lt_two_pow_self
      _ ≤ h ^ K := Nat.pow_le_pow_left hh _
  have hs' : ∀ d ∈ C, d ^ s d = H ∧ k ≤ s d := fun d hd => ⟨(hs d hd).1, by
    have := (hs d hd).2; omega⟩
  have hHpos : 0 < H := by omega
  have hP : 0 < Nat.totient H := Nat.totient_pos.mpr hHpos
  -- the base-`c` coin: a cluster value, exponent divisible by `φ(H)`, large
  set Rr : ℝ := ∑ e ∈ R, (c : ℝ) ^ e with hRr
  set N : ℕ := k + X + ⌈Rr / (ρ - 1)⌉₊ with hN
  obtain ⟨e, hPe, hNe, hcl⟩ := exists_cluster E hE c hc2 ε hε hε1 (Nat.totient H) N hP
  have hce : N < c ^ e := lt_of_le_of_lt hNe (Nat.lt_pow_self (by omega))
  have hdiv : H ∣ c ^ e - 1 := by
    have hcopH : c.Coprime H := Nat.Coprime.pow_right K hcop
    have h1 := Nat.ModEq.pow_totient hcopH
    obtain ⟨r, hr⟩ := hPe
    have h2 : c ^ e ≡ 1 [MOD H] := by
      rw [hr, pow_mul]
      simpa using h1.pow r
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp h2.symm
  obtain ⟨U, V, hUV, hceU, hUVmem, hUVsum⟩ :=
    gadget C hC hσC k H s hs' c e hcC hdiv (Nat.one_le_pow _ _ (by omega))
  -- every gadget coin has value `> X`
  have hbig : ∀ p ∈ U ∪ V, X < val p := by
    intro p hp
    rcases hUVmem p hp with rfl | ⟨_, _, hHp⟩
    · show X < c ^ e
      omega
    · omega
  have hAX : ∀ p ∈ A, val p ≤ X := fun p hp => by
    have := single_le_sum (f := val) (fun _ _ => Nat.zero_le _) hp
    omega
  have hdisjA : Disjoint A (U ∪ V) := by
    rw [disjoint_left]
    intro p hpA hpUV
    have := hAX p hpA
    have := hbig p hpUV
    omega
  have hRX : ∀ e' ∈ R, c ^ e' ≤ X := fun e' he' => by
    have := single_le_sum (f := fun e => c ^ e) (fun _ _ => Nat.zero_le _) he'
    omega
  have heR : ∀ e' ∈ R, e' < e := by
    intro e' he'
    by_contra hcon
    rw [not_lt] at hcon
    have := Nat.pow_le_pow_right (by omega : 1 ≤ c) hcon
    have := hRX e' he'
    omega
  have heRn : e ∉ R := fun he => lt_irrefl _ (heR e he)
  refine ⟨A ∪ (U ∪ V), insert e R, u + ∑ a ∈ V, val a, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases mem_union.mp hp with hp | hp
    · rcases hA p hp with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨h1.1, mem_insert_of_mem h1.2⟩
    · rcases hUVmem p hp with rfl | ⟨h1, h2, _⟩
      · exact Or.inr ⟨rfl, mem_insert_self _ _⟩
      · exact Or.inl ⟨h1, h2⟩
  · intro e' he'
    rcases mem_insert.mp he' with rfl | he'
    · exact ⟨by omega, hcl⟩
    · exact hR e' he'
  · intro e' he'
    rcases mem_insert.mp he' with rfl | he'
    · -- the new coin: the earlier deleted coins sum to at most `(ρ - 1) c ^ e`
      have hle : ∑ x ∈ (insert e' R).filter (· ≤ e'), (c : ℝ) ^ x ≤
          ∑ x ∈ insert e' R, (c : ℝ) ^ x :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
      rw [sum_insert heRn] at hle
      have hNr : Rr / (ρ - 1) ≤ (c : ℝ) ^ e' := by
        have h1 : Rr / (ρ - 1) ≤ (⌈Rr / (ρ - 1)⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : (⌈Rr / (ρ - 1)⌉₊ : ℝ) ≤ ((c ^ e' : ℕ) : ℝ) := by
          exact_mod_cast (show ⌈Rr / (ρ - 1)⌉₊ ≤ c ^ e' by omega)
        push_cast at h2
        linarith
      rw [div_le_iff₀ (by linarith)] at hNr
      have : Rr = ∑ x ∈ R, (c : ℝ) ^ x := rfl
      nlinarith
    · have hfeq : (insert e R).filter (· ≤ e') = R.filter (· ≤ e') := by
        rw [filter_insert]
        have : ¬ e ≤ e' := by have := heR e' he'; omega
        simp [this]
      rw [hfeq]
      exact hlac e' he'
  · intro j hj
    rcases Nat.lt_or_ge j (m + 1) with hj' | hj'
    · obtain ⟨S, hSA, hS⟩ := hrep j (by omega)
      have hdisj : Disjoint S V :=
        disjoint_of_subset_left hSA (disjoint_of_subset_right subset_union_right hdisjA)
      refine ⟨S ∪ V, union_subset_union hSA subset_union_right, ?_⟩
      rw [sum_union hdisj, hS]
      ring
    · obtain ⟨S, hSA, hS⟩ := hrep m le_rfl
      have hdisj : Disjoint S U :=
        disjoint_of_subset_left hSA (disjoint_of_subset_right subset_union_left hdisjA)
      refine ⟨S ∪ U, union_subset_union hSA subset_union_left, ?_⟩
      rw [sum_union hdisj, hS, ← hUVsum]
      omega

lemma cast_sigma (S : Finset ℕ) :
    ((∑ x ∈ S, (x - 1 : ℚ)⁻¹ : ℚ) : ℝ) = ∑ x ∈ S, 1 / ((x : ℝ) - 1) := by
  push_cast
  simp [one_div]

/-- **Theorem AB.** Let `D` be a finite set of integers `≥ 3` and `D = C ⊔ E`, where `C` is a
nonempty set of powers `h ^ a` (`a ≥ 1`) of one integer `h` with `2 σ(C) ≥ 1`, `σ(E) > 1`, and
some `c ∈ E` is coprime to `h`. Then for every `k ≠ 0` all sufficiently large integers lie in
`∑ d ∈ D, sumsOfDistinctPowers d k`. -/
theorem erdos124.variants.ne_zero_of_power_block :
    ∀ k ≠ 0, ∀ D C : Finset ℕ, ∀ h : ℕ, (∀ d ∈ D, 3 ≤ d) → C ⊆ D → C.Nonempty →
      (∀ x ∈ C, ∃ a ≥ 1, x = h ^ a) → 1 ≤ 2 * ∑ d ∈ C, (d - 1 : ℚ)⁻¹ →
      1 < ∑ d ∈ D \ C, (d - 1 : ℚ)⁻¹ → (∃ c ∈ D \ C, c.Coprime h) →
      ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d k := by
  intro k _ D C h hD hCD hC hpow hσC hσE hc
  set E := D \ C with hEdef
  have hE : ∀ d ∈ E, 2 ≤ d := fun d hd => by have := hD d (mem_sdiff.mp hd).1; omega
  have hC2 : ∀ d ∈ C, 2 ≤ d := fun d hd => by have := hD d (hCD hd); omega
  obtain ⟨c, hcE, hcop⟩ := hc
  have hcC : c ∉ C := (mem_sdiff.mp hcE).2
  have hh : 2 ≤ h := by
    obtain ⟨x, hx⟩ := hC
    obtain ⟨a, ha, rfl⟩ := hpow x hx
    have h3 := hD _ (hCD hx)
    rcases Nat.lt_or_ge h 2 with hlt | hge
    · have : h ^ a ≤ 1 := by
        interval_cases h
        · rw [zero_pow (by omega)]
          omega
        · rw [one_pow]
      omega
    · exact hge
  have hσC' : 1 ≤ 2 * ∑ d ∈ C, 1 / ((d : ℝ) - 1) := by
    rw [← cast_sigma]
    exact_mod_cast hσC
  have hσ : 1 < ∑ d ∈ E, 1 / ((d : ℝ) - 1) := by
    rw [← cast_sigma]
    exact_mod_cast hσE
  set σ := ∑ d ∈ E, 1 / ((d : ℝ) - 1) with hσdef
  obtain ⟨hε0, hε1, -, -, -, hρ1, -⟩ := consts σ hσ
  set G : ℕ := ⌈∑ d ∈ E, (d : ℝ) ^ k / ((d : ℝ) - 1)⌉₊ with hGdef
  have hG : ∑ d ∈ E, (d : ℝ) ^ k / ((d : ℝ) - 1) ≤ G := Nat.le_ceil _
  -- build `G` unit gadgets, one after the other
  have hinv : ∀ m, ∃ (A : Finset (ℕ × ℕ)) (R : Finset ℕ) (u : ℕ),
      (∀ p ∈ A, (p.1 ∈ C ∧ k ≤ p.2) ∨ (p.1 = c ∧ p.2 ∈ R)) ∧
      (∀ e ∈ R, k ≤ e ∧ IsCluster E (epsC σ) (c ^ e)) ∧
      (∀ e ∈ R, ∑ e' ∈ R.filter (· ≤ e), (c : ℝ) ^ e' ≤ rhoC σ * (c : ℝ) ^ e) ∧
      (∀ j ≤ m, ∃ S ⊆ A, ∑ a ∈ S, val a = u + j) := by
    intro m
    induction m with
    | zero =>
      refine ⟨∅, ∅, 0, by simp, by simp, by simp, fun j hj => ⟨∅, subset_refl _, ?_⟩⟩
      simp only [sum_empty]
      omega
    | succ m ih =>
      obtain ⟨A, R, u, hA, hR, hlac, hrep⟩ := ih
      exact inv_step E C hE hC2 hσC' h hh hpow c hcE hcC hcop k (epsC σ) (rhoC σ) hε0
        (by linarith) hρ1 m A R u hA hR hlac hrep
  obtain ⟨A, R, u, hA, hR, hlac, hrep⟩ := hinv G
  -- the syndetic part: coins of `E` with exponent `≥ k`, minus the deleted coins
  have hgrow := growB E hE k c hcE hσ R (fun e he => (hR e he).2) hlac G hG
  rw [eventually_atTop]
  refine ⟨u, fun n hn => ?_⟩
  obtain ⟨T, hT, hT1, hT2⟩ := gap_of_grow E hE _ G hgrow (n - u)
  obtain ⟨S, hSA, hS⟩ := hrep (n - u - ∑ a ∈ T, val a) (by omega)
  have hdisj : Disjoint T S := by
    rw [disjoint_left]
    intro p hpT hpS
    obtain ⟨hpE, -, hpR⟩ := hT p hpT
    rcases hA p (hSA hpS) with h1 | h1
    · exact (mem_sdiff.mp hpE).2 h1.1
    · exact hpR h1
  have hsum : ∑ a ∈ T ∪ S, val a = n := by
    rw [sum_union hdisj, hS]
    omega
  rw [← hsum]
  apply sum_mem_sumset
  intro p hp
  rcases mem_union.mp hp with hp | hp
  · obtain ⟨hpE, hpk, -⟩ := hT p hp
    exact ⟨(mem_sdiff.mp hpE).1, hpk⟩
  · rcases hA p (hSA hp) with h1 | h1
    · exact ⟨hCD h1.1, h1.2⟩
    · refine ⟨?_, (hR _ h1.2).1⟩
      rw [h1.1]
      exact (mem_sdiff.mp hcE).1

/-- **Corollary A′** (`C = {3}`). If `D` is a finite set of integers `≥ 3` with `3 ∈ D`,
`gcd D = 1` and `σ(D) > 3 / 2`, then for every `k ≠ 0` all sufficiently large integers lie in
`∑ d ∈ D, sumsOfDistinctPowers d k`. -/
theorem erdos124.variants.ne_zero_of_three_mem :
    ∀ k ≠ 0, ∀ D : Finset ℕ, (∀ d ∈ D, 3 ≤ d) → 3 ∈ D → 3 / 2 < ∑ d ∈ D, (d - 1 : ℚ)⁻¹ →
      D.gcd id = 1 → ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d k := by
  intro k hk D hD h3 hσ hgcd
  have hsub : ({3} : Finset ℕ) ⊆ D := singleton_subset_iff.mpr h3
  refine erdos124.variants.ne_zero_of_power_block k hk D {3} 3 hD hsub (singleton_nonempty 3)
    ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_singleton.mp hx]
    exact ⟨1, le_rfl, by norm_num⟩
  · norm_num
  · have := sum_sdiff hsub (f := fun x : ℕ => (x - 1 : ℚ)⁻¹)
    simp only [sum_singleton] at this
    norm_num at this
    linarith
  · by_contra hcon
    have hcon : ∀ c ∈ D \ {3}, ¬ c.Coprime 3 := fun c hc hcop => hcon ⟨c, hc, hcop⟩
    have hdvd : ∀ d ∈ D, 3 ∣ id d := by
      intro d hd
      by_cases hd3 : d = 3
      · simp [hd3]
      · have : ¬ d.Coprime 3 := hcon d (mem_sdiff.mpr ⟨hd, by simpa using hd3⟩)
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three, not_not] at this
        exact this
    have := Finset.dvd_gcd hdvd
    rw [hgcd] at this
    omega

end ErdosLean.Erdos124ThmAB
