import FormalConjectures.ErdosProblems.«836»

/-!
# Erdős Problem 836: intersecting non-2-colourable hypergraphs with small intersections

We prove `erdos_836.variants.r_le_two_mul_of_inter_le`. Let `t ≥ 2`. If `H` is a finite family
of `r`-element sets which is intersecting and not 2-colourable, and any two distinct edges share at
most `t` vertices, then `r ≤ 2 t`. Price showed `r ≤ 2 t + 1`, with equality for the Fano plane at
`t = 1`. This file shows that `t = 1` is the only case of equality.

The proof is Price's minimal blue class argument with an integrality step.
1. Pass to an edge-critical subfamily (`exists_critical`): the hypotheses pass to subfamilies.
2. Fix an edge `A`. Colour `H - A` properly, with `A` red, and take the blue class `B` as small
   as possible (`exists_min_blue`).
3. For `y ∈ A`, recolouring `y` blue creates a blue edge `F y ∋ y` with `F y ⊆ B ∪ {y}`
   (`exists_F`). For `b ∈ B`, recolouring `b` red creates a red edge `G b` with
   `G b ∩ B = {b}` (`exists_G`).
4. Put `T y = F y - {y}` and `c b = #{y ∈ A | b ∈ T y}`. Then `∑ c = r (r - 1)` and
   `∑ c ^ 2 ≤ (t + 1) r (r - 1)` (`count_bounds`), and `c b ≥ r - t` because every `y ∈ A`
   outside `G b` has `b ∈ T y` (`counts_of_critical`).
5. These counts give `r ≤ 2 t + 1`, and at `r = 2 t + 1` they force `(t + 1) |B| = 2 t (2 t + 1)`,
   so `t + 1 ∣ 2` (`le_two_mul_of_counts`).

The statement is not in formal-conjectures at the commit pinned in `lakefile.toml`, so it is copied
verbatim from the proposed variant in `FormalConjectures/ErdosProblems/836.lean`. It uses only
`Finset.IsUniform` and `Finset.HypergraphColorable` from
`FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite`, which is unchanged between the
pinned commit and the commit the variant was written against.
-/

namespace ErdosLean.Erdos836

open Finset

section Lemmas

variable {V : Type*} [DecidableEq V]

/-- The set `B` (the blue vertices) splits every edge of `H`: each edge has a vertex in `B` and a
vertex outside `B`. -/
def Splits (H : Finset (Finset V)) (B : Finset V) : Prop :=
  ∀ e ∈ H, (∃ x ∈ e, x ∈ B) ∧ ∃ x ∈ e, x ∉ B

/-- A splitting set gives a proper 2-colouring. -/
lemma colorable_of_splits {H : Finset (Finset V)} {B : Finset V} (h : Splits H B) :
    H.HypergraphColorable 2 := by
  refine ⟨fun v => if v ∈ B then 1 else 0, fun e he => ?_⟩
  obtain ⟨⟨x, hx, hxB⟩, ⟨y, hy, hyB⟩⟩ := h e he
  exact ⟨x, hx, y, hy, by simp [hxB, hyB]⟩

/-- Of three colours in `Fin 2`, if the first differs from the other two, those two agree. -/
lemma fin_two_aux : ∀ a b d : Fin 2, a ≠ b → a ≠ d → b = d := by decide

/-- If `H` is not 2-colourable but `H - A` is, then some set `B` disjoint from `A` splits every
edge other than `A`, and `B` is minimal: no `B - b` does. -/
lemma exists_min_blue {H : Finset (Finset V)} {A : Finset V} (hAne : A.Nonempty)
    (hC : ¬ H.HypergraphColorable 2) (hcol : (H.erase A).HypergraphColorable 2) :
    ∃ B : Finset V, Disjoint A B ∧ Splits (H.erase A) B ∧
      ∀ b ∈ B, ¬ Splits (H.erase A) (B.erase b) := by
  classical
  obtain ⟨c, hc⟩ := hcol
  obtain ⟨a₀, ha₀⟩ := hAne
  -- `A` is monochromatic under `c`
  have hmono : ∀ x ∈ A, c x = c a₀ := by
    intro x hx
    by_contra hne
    refine hC ⟨c, fun e he => ?_⟩
    by_cases heA : e = A
    · subst heA; exact ⟨x, hx, a₀, ha₀, hne⟩
    · exact hc e (mem_erase.mpr ⟨heA, he⟩)
  set W := H.biUnion id
  set B₀ := W.filter fun v => c v ≠ c a₀
  have hB₀ : Disjoint A B₀ ∧ Splits (H.erase A) B₀ := by
    refine ⟨disjoint_left.mpr fun x hx hxB => (mem_filter.mp hxB).2 (hmono x hx), ?_⟩
    intro e he
    have heH := (mem_erase.mp he).2
    have hsub : ∀ z ∈ e, z ∈ W := fun z hz => mem_biUnion.mpr ⟨e, heH, hz⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hc e he
    by_cases hxa : c x = c a₀
    · refine ⟨⟨y, hy, mem_filter.mpr ⟨hsub y hy, fun h => hxy (hxa.trans h.symm)⟩⟩,
        ⟨x, hx, fun h => (mem_filter.mp h).2 hxa⟩⟩
    · have hya : c y = c a₀ := fin_two_aux _ _ _ hxy hxa
      exact ⟨⟨x, hx, mem_filter.mpr ⟨hsub x hx, hxa⟩⟩, ⟨y, hy, fun h => (mem_filter.mp h).2 hya⟩⟩
  obtain ⟨B, hB, hmin⟩ := exists_min_image
    (W.powerset.filter fun B => Disjoint A B ∧ Splits (H.erase A) B) card
    ⟨B₀, mem_filter.mpr ⟨mem_powerset.mpr (filter_subset _ _), hB₀⟩⟩
  rw [mem_filter, mem_powerset] at hB
  refine ⟨B, hB.2.1, hB.2.2, fun b hb hspl => ?_⟩
  have := hmin (B.erase b) (mem_filter.mpr ⟨mem_powerset.mpr ((erase_subset b B).trans hB.1),
    disjoint_of_subset_right (erase_subset b B) hB.2.1, hspl⟩)
  have := card_erase_lt_of_mem hb
  omega

/-- Recolouring a vertex `y ∈ A` blue creates a blue edge `F ∋ y`, so `F ⊆ B ∪ {y}`. -/
lemma exists_F {H : Finset (Finset V)} {A B : Finset V} (hA2 : 1 < #A)
    (hC : ¬ H.HypergraphColorable 2) (hAB : Disjoint A B) (hB : Splits (H.erase A) B)
    {y : V} (hy : y ∈ A) : ∃ F ∈ H, F ≠ A ∧ y ∈ F ∧ F ⊆ insert y B := by
  by_contra hno
  refine hC (colorable_of_splits (B := insert y B) fun e he => ?_)
  by_cases heA : e = A
  · subst heA
    obtain ⟨x, hx, hxy⟩ := exists_mem_ne hA2 y
    refine ⟨⟨y, hy, mem_insert_self y B⟩, ⟨x, hx, fun h => ?_⟩⟩
    rcases mem_insert.mp h with h | h
    · exact hxy h
    · exact disjoint_left.mp hAB hx h
  · obtain ⟨⟨x, hx, hxB⟩, ⟨z, hz, hzB⟩⟩ := hB e (mem_erase.mpr ⟨heA, he⟩)
    refine ⟨⟨x, hx, mem_insert_of_mem hxB⟩, ?_⟩
    by_contra hall
    push Not at hall
    have hsub : e ⊆ insert y B := fun w hw => hall w hw
    have hye : y ∈ e := by
      have := hsub hz
      rcases mem_insert.mp this with h | h
      · exact h ▸ hz
      · exact absurd h hzB
    exact hno ⟨e, he, heA, hye, hsub⟩

/-- Recolouring a vertex `b ∈ B` red creates a red edge `G ∋ b`, so `G ∩ B = {b}`. -/
lemma exists_G {H : Finset (Finset V)} {A B : Finset V} (hB : Splits (H.erase A) B)
    (hmin : ∀ b ∈ B, ¬ Splits (H.erase A) (B.erase b)) {b : V} (hb : b ∈ B) :
    ∃ G ∈ H, G ≠ A ∧ b ∈ G ∧ ∀ z ∈ G, z ∈ B → z = b := by
  have h := hmin b hb
  simp only [Splits, not_forall] at h
  obtain ⟨e, he, hne⟩ := h
  obtain ⟨⟨x, hx, hxB⟩, ⟨z, hz, hzB⟩⟩ := hB e he
  have hout : ∃ w ∈ e, w ∉ B.erase b := ⟨z, hz, fun h => hzB (mem_of_mem_erase h)⟩
  have hin : ¬ ∃ w ∈ e, w ∈ B.erase b := fun h => hne ⟨h, hout⟩
  push Not at hin
  have honly : ∀ w ∈ e, w ∈ B → w = b := by
    intro w hw hwB
    by_contra hwb
    exact hin w hw (mem_erase.mpr ⟨hwb, hwB⟩)
  have hxb := honly x hx hxB
  obtain ⟨heA, heH⟩ := mem_erase.mp he
  exact ⟨e, heH, heA, hxb ▸ hx, honly⟩

/-- `c b` counts the sets `T y`, `y ∈ A`, that contain `b`. -/
lemma card_filter_eq_sum (A : Finset V) (T : V → Finset V) (b : V) :
    #{y ∈ A | b ∈ T y} = ∑ y ∈ A, if b ∈ T y then 1 else 0 := card_filter _ _

/-- First moment: `∑_b c b = ∑_y |T y|`. -/
lemma sum_count_eq (A B : Finset V) (T : V → Finset V) (hTB : ∀ y ∈ A, T y ⊆ B) :
    ∑ b ∈ B, #{y ∈ A | b ∈ T y} = ∑ y ∈ A, #(T y) := by
  simp_rw [card_filter_eq_sum]
  rw [sum_comm]
  refine sum_congr rfl fun y hy => ?_
  rw [← card_filter, filter_mem_eq_inter, inter_eq_right.mpr (hTB y hy)]

/-- Second moment: `∑_b (c b)^2 = ∑_{y, y'} |T y ∩ T y'|`. -/
lemma sum_count_sq_eq (A B : Finset V) (T : V → Finset V) (hTB : ∀ y ∈ A, T y ⊆ B) :
    ∑ b ∈ B, #{y ∈ A | b ∈ T y} ^ 2 = ∑ y ∈ A, ∑ y' ∈ A, #(T y ∩ T y') := by
  simp_rw [card_filter_eq_sum, sq, sum_mul_sum, ite_zero_mul_ite_zero, mul_one]
  rw [sum_comm]
  refine sum_congr rfl fun y hy => ?_
  rw [sum_comm]
  refine sum_congr rfl fun y' _ => ?_
  rw [← card_filter]
  congr 1
  ext b
  simp only [mem_filter, mem_inter]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro h; exact ⟨hTB y hy h.1, h⟩

/-- The two moment bounds used in Price's argument. -/
lemma count_bounds (A B : Finset V) (T : V → Finset V) (r t : ℕ) (hA : #A = r)
    (hTB : ∀ y ∈ A, T y ⊆ B) (hT : ∀ y ∈ A, #(T y) = r - 1)
    (hTT : ∀ y ∈ A, ∀ y' ∈ A, y ≠ y' → #(T y ∩ T y') ≤ t) :
    ∑ b ∈ B, #{y ∈ A | b ∈ T y} = r * (r - 1) ∧
      ∑ b ∈ B, #{y ∈ A | b ∈ T y} ^ 2 ≤ (t + 1) * (r * (r - 1)) := by
  constructor
  · rw [sum_count_eq A B T hTB, sum_congr rfl hT, sum_const, hA, smul_eq_mul]
  · rw [sum_count_sq_eq A B T hTB]
    have hrow : ∀ y ∈ A, ∑ y' ∈ A, #(T y ∩ T y') ≤ (r - 1) + (r - 1) * t := by
      intro y hy
      rw [← add_sum_erase A _ hy, inter_self, hT y hy]
      gcongr
      calc ∑ y' ∈ A.erase y, #(T y ∩ T y') ≤ #(A.erase y) • t :=
            sum_le_card_nsmul _ _ _ fun y' hy' =>
              hTT y hy y' (mem_of_mem_erase hy') (ne_of_mem_erase hy').symm
        _ = (r - 1) * t := by rw [card_erase_of_mem hy, hA, smul_eq_mul]
    calc ∑ y ∈ A, ∑ y' ∈ A, #(T y ∩ T y') ≤ #A • ((r - 1) + (r - 1) * t) :=
          sum_le_card_nsmul _ _ _ hrow
      _ = (t + 1) * (r * (r - 1)) := by rw [hA, smul_eq_mul]; ring

/-- The final count. If `∑ c = r (r - 1)`, `∑ c ^ 2 ≤ (t + 1) r (r - 1)` and every `c b ≥ r - t`,
then `r ≤ 2 t + 1`, and `r = 2 t + 1` forces every `c b = t + 1`, so `t + 1 ∣ 2 t (2 t + 1)`,
so `t + 1 ∣ 2`. With `t ≥ 2` this gives `r ≤ 2 t`. -/
lemma le_two_mul_of_counts {ι : Type*} (B : Finset ι) (c : ι → ℕ) (r t : ℕ) (ht : 2 ≤ t)
    (h1 : ∑ b ∈ B, c b = r * (r - 1))
    (h2 : ∑ b ∈ B, c b ^ 2 ≤ (t + 1) * (r * (r - 1)))
    (h3 : ∀ b ∈ B, r - t ≤ c b) : r ≤ 2 * t := by
  by_contra hr
  rw [not_le] at hr
  have hc : ∀ b ∈ B, t + 1 ≤ c b := fun b hb => by have := h3 b hb; omega
  -- every `c b` equals `t + 1`
  have hle : ∀ b ∈ B, c b ≤ t + 1 := by
    intro b hb
    by_contra hlt
    rw [not_le] at hlt
    have hstrict : ∑ x ∈ B, (t + 1) * c x < ∑ x ∈ B, c x ^ 2 := by
      apply Finset.sum_lt_sum
      · intro x hx
        rw [sq]
        exact Nat.mul_le_mul_right _ (hc x hx)
      · exact ⟨b, hb, by rw [sq]; exact Nat.mul_lt_mul_of_pos_right hlt (by omega)⟩
    rw [← Finset.mul_sum, h1] at hstrict
    omega
  have hceq : ∀ b ∈ B, c b = t + 1 := fun b hb => le_antisymm (hle b hb) (hc b hb)
  have hBne : B.Nonempty := by
    by_contra hB
    rw [Finset.not_nonempty_iff_eq_empty] at hB
    subst hB
    simp at h1
    rcases h1 with h1 | h1 <;> omega
  obtain ⟨b, hb⟩ := hBne
  have hr' : r = 2 * t + 1 := by have := h3 b hb; have := hceq b hb; omega
  rw [Finset.sum_congr rfl hceq, Finset.sum_const, smul_eq_mul, hr'] at h1
  -- `(t + 1) ∣ (2t + 1) 2t` forces `t + 1 ∣ 2`
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
  have hdvd : k + 3 ∣ 2 := by
    have e : (2 * (k + 2) + 1) * (2 * (k + 2) + 1 - 1) = (k + 3) * (4 * k + 6) + 2 := by
      rw [show 2 * (k + 2) + 1 - 1 = 2 * k + 4 by omega]; ring
    have : k + 3 ∣ (k + 3) * (4 * k + 6) + 2 := by
      rw [← e, ← h1]; exact Dvd.intro_left _ rfl
    exact (Nat.dvd_add_right (Dvd.intro _ rfl)).mp this
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- A non-2-colourable family contains an edge-critical non-2-colourable subfamily. -/
lemma exists_critical (H : Finset (Finset V)) (hC : ¬ H.HypergraphColorable 2) :
    ∃ H' ⊆ H, ¬ H'.HypergraphColorable 2 ∧
      ∀ A ∈ H', (H'.erase A).HypergraphColorable 2 := by
  classical
  obtain ⟨H', hH', hmin⟩ := Finset.exists_min_image
    (H.powerset.filter fun K => ¬ K.HypergraphColorable 2) Finset.card
    ⟨H, by simp [hC]⟩
  rw [mem_filter, mem_powerset] at hH'
  refine ⟨H', hH'.1, hH'.2, fun A hA => ?_⟩
  by_contra hcol
  have := hmin (H'.erase A) (by
    rw [mem_filter, mem_powerset]
    exact ⟨(erase_subset A H').trans hH'.1, hcol⟩)
  have := card_erase_lt_of_mem hA
  omega

/-- Price's set-up on an edge-critical family yields the counts `c b`. -/
lemma counts_of_critical (H : Finset (Finset V)) (r t : ℕ) (hr : 2 ≤ r)
    (hU : H.IsUniform r) (hI : (H : Set (Finset V)).Intersecting)
    (hT : (H : Set (Finset V)).Pairwise fun e f ↦ (e ∩ f).card ≤ t)
    (hC : ¬ H.HypergraphColorable 2) (hcrit : ∀ A ∈ H, (H.erase A).HypergraphColorable 2) :
    ∃ (B : Finset V) (c : V → ℕ), ∑ b ∈ B, c b = r * (r - 1) ∧
      ∑ b ∈ B, c b ^ 2 ≤ (t + 1) * (r * (r - 1)) ∧ ∀ b ∈ B, r - t ≤ c b := by
  -- `H` has an edge `A`
  obtain ⟨A, hA⟩ : H.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    exact hC ⟨fun _ => 0, fun e he => absurd he (notMem_empty e)⟩
  have hAr : #A = r := hU A hA
  have hA2 : 1 < #A := by omega
  obtain ⟨B, hAB, hB, hmin⟩ :=
    exists_min_blue (card_pos.mp (by omega)) hC (hcrit A hA)
  choose! F hFH hFA hyF hFsub using fun y (hy : y ∈ A) => exists_F hA2 hC hAB hB hy
  choose! G hGH hGA hbG hGB using fun b (hb : b ∈ B) => exists_G hB hmin hb
  set T : V → Finset V := fun y => (F y).erase y
  -- `F y` meets `A` only in `y`
  have hFAy : ∀ y ∈ A, ∀ z ∈ F y, z ∈ A → z = y := by
    intro y hy z hz hzA
    rcases mem_insert.mp (hFsub y hy hz) with h | h
    · exact h
    · exact absurd h (disjoint_left.mp hAB hzA)
  have hTB : ∀ y ∈ A, T y ⊆ B := by
    intro y hy z hz
    obtain ⟨hzy, hzF⟩ := mem_erase.mp hz
    rcases mem_insert.mp (hFsub y hy hzF) with h | h
    · exact absurd h hzy
    · exact h
  have hTcard : ∀ y ∈ A, #(T y) = r - 1 := by
    intro y hy
    rw [card_erase_of_mem (hyF y hy), hU _ (hFH y hy)]
  have hTT : ∀ y ∈ A, ∀ y' ∈ A, y ≠ y' → #(T y ∩ T y') ≤ t := by
    intro y hy y' hy' hne
    have hFne : F y ≠ F y' := by
      intro h
      exact hne (hFAy y hy y' (h ▸ hyF y' hy') hy').symm
    calc #(T y ∩ T y') ≤ #(F y ∩ F y') :=
          card_le_card (inter_subset_inter (erase_subset _ _) (erase_subset _ _))
      _ ≤ t := hT (mem_coe.mpr (hFH y hy)) (mem_coe.mpr (hFH y' hy')) hFne
  obtain ⟨h1, h2⟩ := count_bounds A B T r t hAr hTB hTcard hTT
  refine ⟨B, fun b => #{y ∈ A | b ∈ T y}, h1, h2, fun b hb => ?_⟩
  -- every `y ∈ A` outside `G b` has `b ∈ T y`
  have hsub : A \ G b ⊆ {y ∈ A | b ∈ T y} := by
    intro y hy
    obtain ⟨hyA, hyG⟩ := mem_sdiff.mp hy
    refine mem_filter.mpr ⟨hyA, ?_⟩
    obtain ⟨z, hzG, hzF⟩ := not_disjoint_iff.mp
      (hI (mem_coe.mpr (hGH b hb)) (mem_coe.mpr (hFH y hyA)))
    have hzy : z ≠ y := fun h => hyG (h ▸ hzG)
    have hzB : z ∈ B := by
      rcases mem_insert.mp (hFsub y hyA hzF) with h | h
      · exact absurd h hzy
      · exact h
    have hzb := hGB b hb z hzG hzB
    subst hzb
    exact mem_erase.mpr ⟨hzy, hzF⟩
  have hinter : #(A ∩ G b) ≤ t :=
    hT (mem_coe.mpr hA) (mem_coe.mpr (hGH b hb)) (hGA b hb).symm
  have := card_le_card hsub
  have := card_sdiff_add_card_inter A (G b)
  show r - t ≤ #{y ∈ A | b ∈ T y}
  omega

end Lemmas

/-- The statement, copied verbatim from the proposed formal-conjectures variant. -/
theorem erdos_836.variants.r_le_two_mul_of_inter_le {V : Type*} [DecidableEq V] (r t : ℕ)
    (ht : 2 ≤ t) (H : Finset (Finset V)) (hU : H.IsUniform r)
    (hI : (H : Set (Finset V)).Intersecting) (hC : ¬ H.HypergraphColorable 2)
    (hT : (H : Set (Finset V)).Pairwise fun e f ↦ (e ∩ f).card ≤ t) :
    r ≤ 2 * t := by
  by_contra hr
  obtain ⟨H', hH', hC', hcrit⟩ := exists_critical H hC
  obtain ⟨B, c, h1, h2, h3⟩ := counts_of_critical H' r t (by omega)
    (fun e he => hU e (hH' he)) (hI.mono (coe_subset.mpr hH'))
    (hT.mono (coe_subset.mpr hH')) hC' hcrit
  exact hr (le_two_mul_of_counts B c r t ht h1 h2 h3)

/- ## The hypothesis `t ≥ 2` is needed

The Fano plane is 3-uniform, intersecting, not 2-colourable and linear, so with `t = 1` it has
`r = 3 > 2 t`. -/

/-- The seven lines of the Fano plane. -/
def fano : Finset (Finset (Fin 7)) :=
  {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}

set_option maxRecDepth 100000 in
/-- The conclusion `r ≤ 2 t` fails for `t = 1`: the Fano plane satisfies every other hypothesis. -/
theorem fano_counterexample_t_eq_one :
    fano.IsUniform 3 ∧ (fano : Set (Finset (Fin 7))).Intersecting ∧
      ¬ fano.HypergraphColorable 2 ∧
      (fano : Set (Finset (Fin 7))).Pairwise (fun e f ↦ (e ∩ f).card ≤ 1) ∧ ¬ 3 ≤ 2 * 1 := by
  refine ⟨?_, ?_, ?_, ?_, by norm_num⟩
  · unfold Finset.IsUniform fano
    decide +kernel
  · intro a ha b hb
    simp only [Finset.mem_coe] at ha hb
    revert a b
    unfold fano
    decide +kernel
  · unfold Finset.HypergraphColorable Finset.IsProperHypergraphColoring fano
    decide +kernel
  · intro a ha b hb _
    simp only [Finset.mem_coe] at ha hb
    revert a b
    unfold fano
    decide +kernel

end ErdosLean.Erdos836
