import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Ackelsberg-Richter, Question 16.9

[AcRi26, Question 16.9] asks whether every $B \subseteq \mathbb{N}$ with $\overline{d}(B) = 1$ is
a $d$-essential component, meaning $\underline{d}(A + B) > d(A)$ for every $A \subseteq \mathbb{N}$
with $d(A) \in (0, 1)$. We prove that the answer is no
(`isDEssentialComponent_of_upperDensity_eq_one`).

The definition `IsDEssentialComponent` and the statement are not in formal-conjectures at the
commit pinned in `lakefile.toml`. They are copied verbatim from the proposed file
`FormalConjectures/Arxiv/2604.12864/EssentialComponent.lean`. They use `Set.HasDensity`,
`Set.lowerDensity` and `Set.upperDensity` from `FormalConjecturesForMathlib` at the pinned commit.

Construction.
* $A = \bigcup_{k \ge 1} [k^2, k^2 + k)$, written as $\{n : n < s^2 + s\}$ with
  $s = \lfloor\sqrt n\rfloor$. The number $c(b)$ of elements of $A$ below $b$ satisfies
  $b - \lfloor\sqrt b\rfloor \le 2c(b) \le b$ (`cntA_bounds`), so $d(A) = 1/2$ (`hasDensity_A`).
* $P_0 = 1$, $P_{s+1} = ((s+1) P_s)^4$ and $B = \bigcup_s (P_s, (s+1) P_s]$. The block
  $(P_s, (s+1) P_s]$ gives $\overline{d}(B) = 1$ (`upperDensity_B`).
* Put $N = (s+1) P_s$ and $M = P_{s+1} = N^4$. Every element of $B$ below $M$ is at most $N$
  (`le_of_mem_B`). Let $y = a + b < M$ with $a \in A$, $b \in B$ and $y \notin A$, and let
  $k = \lfloor\sqrt a\rfloor$. Then $y \in [k^2 + k, k^2 + k + N)$ and $k < N^2$. So
  $|(A + B) \cap [0, M)| \le c(M) + N^3$ (`ncard_add_le`), and
  $\underline{d}(A + B) \le 1/2 = d(A)$ (`lowerDensity_add_le`).

*Reference:* [AcRi26] E. Ackelsberg, F. K. Richter, *An inverse theorem for sumsets of sets of
positive density in the integers*, arXiv:2604.12864 (2026).
-/

open Filter Set
open scoped Pointwise

namespace ErdosLean.AcRiQuestion169

/- ## The statement, copied verbatim from the proposed formal-conjectures file -/

/--
A set $B \subseteq \mathbb{N}$ is a *$d$-essential component* if
$\underline{d}(A + B) > d(A)$ for every $A \subseteq \mathbb{N}$ whose density $d(A)$ exists and
lies in $(0, 1)$.

The paper's $\mathbb{N}$ starts at $1$, so `A` must avoid `0` here. Allowing $0 \in A$ would put
$B$ itself inside $A + B$. The densities on `Set ℕ` count the elements below `b`, including `0`.
For sets that avoid `0` they agree with the paper's densities, which count in
$[N] = \{1, \ldots, N\}$.
-/
def IsDEssentialComponent (B : Set ℕ) : Prop :=
  ∀ A : Set ℕ, 0 ∉ A → ∀ α ∈ Set.Ioo (0 : ℝ) 1, A.HasDensity α →
    α < (A + B).lowerDensity

/- ## The set `A` -/

/-- `A = ⋃ₖ [k², k² + k)`. -/
def A : Set ℕ := {n | n < n.sqrt * n.sqrt + n.sqrt}

instance : DecidablePred (· ∈ A) := fun n => inferInstanceAs (Decidable (n < _))

lemma zero_notMem_A : 0 ∉ A := by simp [A]

/-- The number of elements of `A` below `b`. -/
def cntA (b : ℕ) : ℕ := ((Finset.range b).filter (· ∈ A)).card

lemma cntA_formula (b : ℕ) :
    2 * cntA b = b.sqrt * b.sqrt - b.sqrt + 2 * min (b - b.sqrt * b.sqrt) b.sqrt := by
  induction b with
  | zero => simp [cntA]
  | succ b ih =>
    have hstep : cntA (b + 1) = cntA b + if b ∈ A then 1 else 0 := by
      unfold cntA
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
      · simp
    have h1 := Nat.sqrt_le b
    have h2 := Nat.lt_succ_sqrt b
    have h3 := Nat.sqrt_le (b + 1)
    have h5 : b.sqrt ≤ (b + 1).sqrt := Nat.sqrt_le_sqrt (Nat.le_succ b)
    have h6 : (b + 1).sqrt ≤ b.sqrt + 1 := Nat.sqrt_succ_le_succ_sqrt b
    obtain ⟨i, hi, hcase⟩ : ∃ i, cntA (b + 1) = cntA b + i ∧
        ((b < b.sqrt * b.sqrt + b.sqrt ∧ i = 1) ∨
          (¬ b < b.sqrt * b.sqrt + b.sqrt ∧ i = 0)) := by
      by_cases hb : b ∈ A
      · exact ⟨1, by rw [hstep, if_pos hb], Or.inl ⟨hb, rfl⟩⟩
      · exact ⟨0, by rw [hstep, if_neg hb], Or.inr ⟨hb, rfl⟩⟩
    clear hstep
    rw [Nat.succ_eq_add_one] at h2
    have e : (b.sqrt + 1) * (b.sqrt + 1) = b.sqrt * b.sqrt + 2 * b.sqrt + 1 := by ring
    rw [e] at h2
    have h7 := Nat.le_mul_self b.sqrt
    rcases Nat.eq_or_lt_of_le h5 with h | h
    · rw [← h] at h3 ⊢
      clear h5 h6 h e
      generalize b.sqrt = t at *
      generalize t * t = q at *
      omega
    · have h' : (b + 1).sqrt = b.sqrt + 1 := by omega
      rw [h'] at h3 ⊢
      rw [e] at h3 ⊢
      clear h5 h6 h h' e
      generalize b.sqrt = t at *
      generalize t * t = q at *
      omega

lemma cntA_bounds (b : ℕ) : 2 * cntA b ≤ b ∧ b ≤ 2 * cntA b + b.sqrt := by
  have h := cntA_formula b
  have h1 := Nat.sqrt_le b
  have h2 := Nat.lt_succ_sqrt b
  rw [Nat.succ_eq_add_one] at h2
  have e : (b.sqrt + 1) * (b.sqrt + 1) = b.sqrt * b.sqrt + 2 * b.sqrt + 1 := by ring
  rw [e] at h2
  have h7 := Nat.le_mul_self b.sqrt
  clear e
  generalize b.sqrt = t at *
  generalize t * t = q at *
  omega

lemma ncard_inter_Iio (S : Set ℕ) [DecidablePred (· ∈ S)] (b : ℕ) :
    (S ∩ Iio b).ncard = ((Finset.range b).filter (· ∈ S)).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp [and_comm]

lemma partialDensity_eq (S : Set ℕ) [DecidablePred (· ∈ S)] (b : ℕ) :
    S.partialDensity Set.univ b = (((Finset.range b).filter (· ∈ S)).card : ℝ) / b := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  rw [ncard_inter_Iio, Nat.ncard_Iio]

lemma partialDensity_A_le (b : ℕ) : A.partialDensity Set.univ b ≤ 1 / 2 := by
  rw [partialDensity_eq]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  have := (cntA_bounds b).1
  unfold cntA at this
  have : (2 * ((Finset.range b).filter (· ∈ A)).card : ℝ) ≤ b := by exact_mod_cast this
  linarith

lemma hasDensity_A : A.HasDensity (1 / 2) := by
  have hsqrt : Tendsto (fun b : ℕ => (b.sqrt : ℝ)) atTop atTop := by
    refine tendsto_natCast_atTop_atTop.comp ?_
    exact tendsto_atTop_atTop.2 fun x => ⟨x * x, fun b hb => Nat.le_sqrt.2 hb⟩
  have hlow : Tendsto (fun b : ℕ => 1 / 2 - 1 / (2 * (b.sqrt : ℝ))) atTop (nhds (1 / 2)) := by
    have : Tendsto (fun b : ℕ => 1 / (2 * (b.sqrt : ℝ))) atTop (nhds 0) := by
      have := (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 hsqrt
      exact this.inv_tendsto_atTop.congr fun b => by simp
    simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall partialDensity_A_le)
  filter_upwards [eventually_ge_atTop 1] with b hb
  rw [partialDensity_eq]
  have ht : 1 ≤ b.sqrt := Nat.le_sqrt.2 (by simpa using hb)
  have hq := Nat.sqrt_le b
  have hc := (cntA_bounds b).2
  unfold cntA at hc
  set c := ((Finset.range b).filter (· ∈ A)).card
  set t := b.sqrt
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hqR : (t : ℝ) * t ≤ b := by exact_mod_cast hq
  have hcR : (b : ℝ) ≤ 2 * c + t := by exact_mod_cast hc
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [le_div_iff₀ hbR]
  have : (b : ℝ) / (2 * t) ≥ t / 2 := by
    rw [ge_iff_le, le_div_iff₀ (by positivity)]
    nlinarith
  have e : (1 / 2 - 1 / (2 * (t : ℝ))) * b = b / 2 - b / (2 * t) := by
    field_simp
  rw [e]
  linarith

/- ## The set `B` -/

/-- The scales: `P 0 = 1` and `P (s + 1) = ((s + 1) * P s) ^ 4`. -/
def P : ℕ → ℕ
  | 0 => 1
  | s + 1 => ((s + 1) * P s) ^ 4

/-- `B = ⋃ₛ (P s, (s + 1) P s]`. -/
def B : Set ℕ := {n | ∃ s, P s < n ∧ n ≤ (s + 1) * P s}

lemma zero_notMem_B : 0 ∉ B := by simp [B]

lemma P_pos (s : ℕ) : 0 < P s := by
  induction s with
  | zero => simp [P]
  | succ s ih => exact pow_pos (Nat.mul_pos (Nat.succ_pos s) ih) 4

lemma le_P_succ (s : ℕ) : (s + 1) * P s ≤ P (s + 1) := by
  simp only [P]
  have : 1 ≤ (s + 1) * P s := Nat.mul_pos (Nat.succ_pos s) (P_pos s)
  calc (s + 1) * P s = ((s + 1) * P s) ^ 1 := (pow_one _).symm
    _ ≤ ((s + 1) * P s) ^ 4 := Nat.pow_le_pow_right this (by norm_num)

lemma P_mono : Monotone P := by
  refine monotone_nat_of_le_succ fun s => ?_
  calc P s ≤ (s + 1) * P s := Nat.le_mul_of_pos_left _ (Nat.succ_pos s)
    _ ≤ P (s + 1) := le_P_succ s

/-- The gap: every element of `B` below `P (s + 1)` is at most `(s + 1) * P s`. -/
lemma le_of_mem_B {s b : ℕ} (hb : b ∈ B) (hlt : b < P (s + 1)) : b ≤ (s + 1) * P s := by
  obtain ⟨t, ht1, ht2⟩ := hb
  rcases le_or_gt t s with h | h
  · calc b ≤ (t + 1) * P t := ht2
      _ ≤ (s + 1) * P s := Nat.mul_le_mul (by omega) (P_mono h)
  · have := P_mono (show s + 1 ≤ t by omega)
    omega

lemma partialDensity_nonneg (S : Set ℕ) (b : ℕ) : 0 ≤ S.partialDensity Set.univ b := by
  unfold Set.partialDensity
  positivity

lemma upperDensity_B : B.upperDensity = 1 := by
  classical
  have hb : atTop.IsBoundedUnder (· ≤ ·) fun b : ℕ => B.partialDensity Set.univ b :=
    isBoundedUnder_of ⟨1, fun b => Set.partialDensity_le_one _ _ _⟩
  have hc : atTop.IsCoboundedUnder (· ≤ ·) fun b : ℕ => B.partialDensity Set.univ b :=
    IsBoundedUnder.isCoboundedUnder_le
      (isBoundedUnder_of ⟨0, fun b => partialDensity_nonneg B b⟩ :
        atTop.IsBoundedUnder (· ≥ ·) fun b : ℕ => B.partialDensity Set.univ b)
  apply le_antisymm
  · exact limsup_le_of_le hc (Eventually.of_forall fun b => Set.partialDensity_le_one _ _ _)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have key : 1 - ε ≤ B.upperDensity := by
    refine le_limsup_of_frequently_le ?_ hb
    rw [frequently_atTop]
    intro a
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / ε)
    set s := a + n
    set p := P s
    have hp : 1 ≤ p := P_pos s
    refine ⟨(s + 1) * p + 1, ?_, ?_⟩
    · have : s + 1 ≤ (s + 1) * p := Nat.le_mul_of_pos_right _ hp
      omega
    have hsub : Finset.Ioc p ((s + 1) * p) ⊆
        (Finset.range ((s + 1) * p + 1)).filter (· ∈ B) := by
      intro x hx
      rw [Finset.mem_Ioc] at hx
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, s, hx.1, hx.2⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Ioc] at hcard
    rw [partialDensity_eq]
    have hsp : (s + 1) * p - p = s * p := by rw [add_mul, one_mul, Nat.add_sub_cancel]
    rw [hsp] at hcard
    set c := ((Finset.range ((s + 1) * p + 1)).filter (· ∈ B)).card
    have hcR : (s : ℝ) * p ≤ c := by exact_mod_cast hcard
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hnR : 2 / ε < s := by
      have : (n : ℝ) ≤ s := by exact_mod_cast Nat.le_add_left n a
      linarith
    have hεs : 2 ≤ ε * s := by
      rw [div_lt_iff₀ hε] at hnR
      linarith
    push_cast
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hεs (by linarith : (0 : ℝ) ≤ p)]
  linarith

/- ## The sumset `A + B` -/

lemma ncard_add_le (s : ℕ) :
    ((A + B) ∩ Iio (P (s + 1))).ncard ≤ cntA (P (s + 1)) + ((s + 1) * P s) ^ 3 := by
  set N := (s + 1) * P s with hN
  have hM : P (s + 1) = N * N * (N * N) := by simp only [P, hN]; ring
  let T : Finset ℕ := (Finset.range (P (s + 1))).filter (· ∈ A) ∪
    (Finset.range (N * N)).biUnion fun k => Finset.Ico (k * k + k) (k * k + k + N)
  have hsub : (A + B) ∩ Iio (P (s + 1)) ⊆ ↑T := by
    rintro y ⟨hy, hyM⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hy
    rw [Set.mem_Iio] at hyM
    rw [Finset.mem_coe, Finset.mem_union]
    by_cases hyA : a + b ∈ A
    · exact Or.inl (Finset.mem_filter.2 ⟨Finset.mem_range.2 hyM, hyA⟩)
    right
    have hbN : b ≤ N := le_of_mem_B hb (by omega)
    have hk1 := Nat.sqrt_le a
    have hak : a < a.sqrt * a.sqrt + a.sqrt := ha
    set k := a.sqrt
    have hy1 : k * k + k ≤ a + b := by
      by_contra hlt
      push Not at hlt
      apply hyA
      have hsq : (a + b).sqrt = k := by
        refine (Nat.eq_sqrt.2 ⟨by omega, ?_⟩).symm
        have e : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
        rw [e]
        omega
      show a + b < (a + b).sqrt * (a + b).sqrt + (a + b).sqrt
      rw [hsq]
      exact hlt
    have hkM : k < N * N := by
      have : k * k < (N * N) * (N * N) := by omega
      exact Nat.mul_self_lt_mul_self_iff.1 this
    rw [Finset.mem_biUnion]
    exact ⟨k, Finset.mem_range.2 hkM, Finset.mem_Ico.2 ⟨hy1, by omega⟩⟩
  calc ((A + B) ∩ Iio (P (s + 1))).ncard ≤ (T : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet T)
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ cntA (P (s + 1)) + N * N * N := by
        refine (Finset.card_union_le _ _).trans (add_le_add le_rfl ?_)
        refine Finset.card_biUnion_le.trans ?_
        simp
    _ = cntA (P (s + 1)) + N ^ 3 := by ring

lemma lowerDensity_add_le : (A + B).lowerDensity ≤ 1 / 2 := by
  have hb : atTop.IsBoundedUnder (· ≥ ·) fun b : ℕ => (A + B).partialDensity Set.univ b :=
    isBoundedUnder_of ⟨0, fun b => partialDensity_nonneg _ b⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  refine liminf_le_of_frequently_le ?_ hb
  rw [frequently_atTop]
  intro a
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  set s := a + n
  set N := (s + 1) * P s with hN
  have hNs : s + 1 ≤ N := Nat.le_mul_of_pos_right _ (P_pos s)
  have hNP := le_P_succ s
  refine ⟨P (s + 1), by omega, ?_⟩
  have hM : P (s + 1) = N ^ 4 := by simp only [P, hN]
  have hcnt := ncard_add_le s
  have hA := partialDensity_A_le (P (s + 1))
  rw [partialDensity_eq] at hA
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  have hMpos : (0 : ℝ) < P (s + 1) := by exact_mod_cast P_pos (s + 1)
  rw [div_le_iff₀ hMpos] at hA ⊢
  have hcR : (((A + B) ∩ Iio (P (s + 1))).ncard : ℝ) ≤ cntA (P (s + 1)) + (N : ℝ) ^ 3 := by
    exact_mod_cast hcnt
  have hNR : (1 / ε : ℝ) < N := by
    have : ((s + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hNs
    have : (n : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ s + 1)
    linarith
  have hεN : 1 ≤ ε * N := by
    rw [div_lt_iff₀ hε] at hNR
    linarith
  have hMR : ((P (s + 1) : ℕ) : ℝ) = (N : ℝ) ^ 4 := by rw [hM]; push_cast; ring
  have hN3 : (N : ℝ) ^ 3 ≤ ε * (N : ℝ) ^ 4 := by
    have := mul_le_mul_of_nonneg_right hεN (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 3)
    nlinarith
  unfold cntA at hcR
  rw [hMR] at hA ⊢
  nlinarith

/-- **[AcRi26, Question 16.9].** Not every set $B \subseteq \mathbb{N}$ with
$\overline{d}(B) = 1$ is a $d$-essential component. This is the statement
`Arxiv.«2604.12864».isDEssentialComponent_of_upperDensity_eq_one` of the proposed
formal-conjectures file, with the same type. -/
theorem isDEssentialComponent_of_upperDensity_eq_one :
    ¬ ∀ B : Set ℕ, 0 ∉ B → B.upperDensity = 1 → IsDEssentialComponent B := by
  intro h
  have := h B zero_notMem_B upperDensity_B A zero_notMem_A (1 / 2) ⟨by norm_num, by norm_num⟩
    hasDensity_A
  linarith [lowerDensity_add_le]

end ErdosLean.AcRiQuestion169
