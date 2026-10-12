import FormalConjectures.ErdosProblems.«1167»

/-!
# Erdős Problem 1167, finite targets

The repository statement `Erdos1167.erdos_1167.variants.finite_targets` is proved by
contraposition. If `λ ↛ (n_α)^r` is witnessed by a colouring, the colours that are actually
used all have targets `≥ r + 1`. If only finitely many such colours exist, the Erdős–Rado
tree argument (with finite branches) shows the ground set is finite, a contradiction.
Otherwise, with `μ` such colours, the same tree argument gives `λ ≤ exp_{r-1}(μ)`, and the
Erdős–Hajnal–Rado stepping-up construction (lexicographic order and first differences,
with the up/down pattern recorded in the colour) gives `exp_r(μ) ↛ (r + 2)^{r+1}_μ`,
which refutes the hypothesis `2^λ → (n_α + 1)^{r+1}`.
-/

open Cardinal

namespace ErdosLean.Erdos1167

universe u

/-- `H` is homogeneous of colour `α` for the `r`-uniform colouring `c`. -/
def Homog {X C : Type*} (r : ℕ) (c : Finset X → C) (α : C) (H : Finset X) : Prop :=
  ∀ s ⊆ H, s.card = r → c s = α

/-- `c` has no homogeneous set of size `n α` in colour `α`. -/
def Bad {X C : Type*} (r : ℕ) (c : Finset X → C) (n : C → ℕ) : Prop :=
  ∀ (α : C) (H : Finset X), H.card = n α → ¬ Homog r c α H

section Tree

variable {X : Type u} [LinearOrder X] [WellFoundedLT X] {C : Type u}

/-- The Erdős–Rado tree relation `x ◁ y`. -/
noncomputable def treeRel (r : ℕ) (c : Finset X → C) : X → X → Prop :=
  (wellFounded_lt (α := X)).fix (C := fun _ => X → Prop) (fun x IH y =>
    x < y ∧ (∀ z (hz : z < x), (IH z hz y ↔ IH z hz x)) ∧
    ∀ s : Finset X, (∀ z ∈ s, ∃ hz : z < x, IH z hz x) → s.card = r →
      c (insert x s) = c (insert y s))

variable {r : ℕ} {c : Finset X → C}

theorem treeRel_def (x y : X) :
    treeRel r c x y ↔ x < y ∧ (∀ z, z < x → (treeRel r c z y ↔ treeRel r c z x)) ∧
      ∀ s : Finset X, (∀ z ∈ s, z < x ∧ treeRel r c z x) → s.card = r →
        c (insert x s) = c (insert y s) := by
  unfold treeRel
  rw [WellFounded.fix_eq]
  simp only [exists_prop]

theorem treeRel_lt {x y : X} (h : treeRel r c x y) : x < y := ((treeRel_def x y).1 h).1

theorem treeRel_iff (x y : X) :
    treeRel r c x y ↔ x < y ∧ (∀ z, z < x → (treeRel r c z y ↔ treeRel r c z x)) ∧
      ∀ s : Finset X, (∀ z ∈ s, treeRel r c z x) → s.card = r →
        c (insert x s) = c (insert y s) := by
  rw [treeRel_def]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun s hs hc => h3 s (fun z hz => ⟨treeRel_lt (hs z hz), hs z hz⟩) hc⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun s hs hc => h3 s (fun z hz => (hs z hz).2) hc⟩

theorem treeRel_tree {x y z : X} (hxy : treeRel r c x y) (hzx : z < x) :
    treeRel r c z y ↔ treeRel r c z x :=
  ((treeRel_iff x y).1 hxy).2.1 z hzx

theorem treeRel_trans {x y z : X} (hxy : treeRel r c x y) (hzx : treeRel r c z x) :
    treeRel r c z y :=
  (treeRel_tree hxy (treeRel_lt hzx)).2 hzx

theorem treeRel_chain {x x' y : X} (hx : treeRel r c x y) (hx' : treeRel r c x' y)
    (h : x' < x) : treeRel r c x' x :=
  (treeRel_tree hx h).1 hx'

theorem treeRel_endhom {x y : X} (hxy : treeRel r c x y) (s : Finset X)
    (hs : ∀ z ∈ s, treeRel r c z x) (hc : s.card = r) : c (insert x s) = c (insert y s) :=
  ((treeRel_iff x y).1 hxy).2.2 s hs hc

theorem treeRel_inj_aux {x y : X} (hlt : x < y) (hP : ∀ z, treeRel r c z x ↔ treeRel r c z y)
    (hcol : ∀ s : Finset X, (∀ z ∈ s, treeRel r c z x) → s.card = r →
      c (insert x s) = c (insert y s)) : False := by
  have h : treeRel r c x y := (treeRel_iff x y).2 ⟨hlt, fun z _ => (hP z).symm, hcol⟩
  exact lt_irrefl _ (treeRel_lt ((hP x).2 h))

theorem treeRel_inj {x y : X} (hP : ∀ z, treeRel r c z x ↔ treeRel r c z y)
    (hcol : ∀ s : Finset X, (∀ z ∈ s, treeRel r c z x) → s.card = r →
      c (insert x s) = c (insert y s)) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · exact (treeRel_inj_aux h hP hcol).elim
  · exact h
  · exact (treeRel_inj_aux h (fun z => (hP z).symm)
      (fun s hs hc => (hcol s (fun z hz => (hP z).2 (hs z hz)) hc).symm)).elim

/-- The colouring induced on the branch below `y`. -/
noncomputable def branchCol (r : ℕ) (c : Finset X → C) (y : X) :
    Finset {x // treeRel r c x y} → C :=
  fun s => c (insert y (s.map (Function.Embedding.subtype _)))

theorem branchCol_bad (n : C → ℕ) (hc : Bad (r + 1) c n) (y : X) :
    Bad r (branchCol r c y) n := by
  classical
  intro α H hH hom
  apply hc α (H.map (Function.Embedding.subtype _)) (by simp [hH])
  intro t ht htc
  have tne : t.Nonempty := by
    rw [← Finset.card_pos, htc]; omega
  set m := t.max' tne with hm
  have hmt : m ∈ t := t.max'_mem tne
  have mem_branch : ∀ z ∈ t, treeRel r c z y := by
    intro z hz
    have := ht hz
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at this
    obtain ⟨w, _, rfl⟩ := this
    exact w.2
  set s := t.erase m with hs
  have hts : t = insert m s := (Finset.insert_erase hmt).symm
  have hscard : s.card = r := by
    rw [hs, Finset.card_erase_of_mem hmt, htc]; rfl
  have hsP : ∀ z ∈ s, treeRel r c z m := by
    intro z hz
    have hz' := Finset.mem_erase.1 hz
    have hle : z ≤ m := t.le_max' z hz'.2
    exact treeRel_chain (mem_branch m hmt) (mem_branch z hz'.2) (lt_of_le_of_ne hle hz'.1)
  have key : c t = c (insert y s) := by
    rw [hts]
    exact treeRel_endhom (mem_branch m hmt) s hsP hscard
  rw [key]
  have hsy : ∀ z ∈ s, treeRel r c z y := fun z hz => mem_branch z (Finset.mem_of_mem_erase hz)
  have := hom (s.subtype (fun z => treeRel r c z y)) ?_ ?_
  · rw [← this]
    unfold branchCol
    rw [Finset.subtype_map_of_mem hsy]
  · intro w hw
    rw [Finset.mem_subtype] at hw
    have := ht (Finset.mem_of_mem_erase hw)
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at this
    obtain ⟨w', hw', hww'⟩ := this
    have : w' = w := Subtype.ext hww'
    rw [← this]; exact hw'
  · have h1 := Finset.card_map (s := s.subtype (fun z => treeRel r c z y))
      (Function.Embedding.subtype (fun z => treeRel r c z y))
    rw [Finset.subtype_map_of_mem hsy] at h1
    rw [← h1, hscard]

end Tree

theorem exists_ps (Z W : Type u) [LinearOrder Z] [WellFoundedLT Z] [LinearOrder W]
    [WellFoundedLT W] (h : #Z < #W) :
    Nonempty (PrincipalSeg ((· < ·) : Z → Z → Prop) ((· < ·) : W → W → Prop)) := by
  rcases InitialSeg.total ((· < ·) : Z → Z → Prop) ((· < ·) : W → W → Prop) with f | f
  · rcases f.principalSumRelIso with g | g
    · exact ⟨g⟩
    · exact absurd (Cardinal.mk_congr g.toEquiv) h.ne
  · exact absurd (Cardinal.mk_le_of_injective f.injective) (not_le.2 h)

theorem image_eq_self {α : Type*} [DecidableEq α] {s : Finset α} {f : α → α}
    (h : ∀ z ∈ s, f z = z) : s.image f = s := by
  ext a
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rwa [h b hb]
  · intro ha
    exact ⟨a, ha, h a ha⟩

section Bound

variable {X : Type u} [LinearOrder X] [WellFoundedLT X] {C : Type u}

theorem tree_bound (r : ℕ) (n : C → ℕ) (B : Cardinal.{u})
    (hB : ∀ (Z : Type u) [LinearOrder Z] [WellFoundedLT Z] (c' : Finset Z → C),
      Bad r c' n → #Z ≤ B)
    (c : Finset X → C) (hc : Bad (r + 1) c n) :
    #X ≤ #(Σ i : (Order.succ B).ord.ToType, (Finset {w // w < i} → C)) := by
  classical
  set W := (Order.succ B).ord.ToType
  have hW : #W = Order.succ B := Cardinal.mk_ord_toType _
  have hP : ∀ y : X, #{x // treeRel r c x y} < #W := by
    intro y
    rw [hW]
    exact lt_of_le_of_lt (hB _ (branchCol r c y) (branchCol_bad n hc y)) (Order.lt_succ B)
  let ps : ∀ y : X, PrincipalSeg ((· < ·) : {x // treeRel r c x y} → _ → Prop)
      ((· < ·) : W → W → Prop) :=
    fun y => Classical.choice (exists_ps _ _ (hP y))
  let g : X → X → W := fun y x =>
    if h : treeRel r c x y then (ps y).toRelEmbedding ⟨x, h⟩ else (ps y).top
  let inv : X → W → X := fun y w =>
    if h : w < (ps y).top then ((ps y).subrelIso ⟨w, h⟩).1 else y
  have g_lt : ∀ {x y}, treeRel r c x y → g y x < (ps y).top := by
    intro x y h
    simp only [g, dif_pos h]
    exact (ps y).lt_top ⟨x, h⟩
  have inv_g : ∀ {x y}, treeRel r c x y → inv y (g y x) = x := by
    intro x y h
    simp only [inv, dif_pos (g_lt h)]
    simp only [g, dif_pos h]
    rw [PrincipalSeg.subrelIso_apply]
  have inv_mem : ∀ {y w}, w < (ps y).top → treeRel r c (inv y w) y := by
    intro y w h
    simp only [inv, dif_pos h]
    exact ((ps y).subrelIso ⟨w, h⟩).2
  have g_inv : ∀ {y w}, w < (ps y).top → g y (inv y w) = w := by
    intro y w h
    have hm := inv_mem h
    simp only [g, dif_pos hm]
    have : (⟨inv y w, hm⟩ : {x // treeRel r c x y}) = (ps y).subrelIso ⟨w, h⟩ := by
      apply Subtype.ext
      simp only [inv, dif_pos h]
    rw [this, PrincipalSeg.apply_subrelIso]
  have g_lt_iff : ∀ {x x' y}, treeRel r c x y → treeRel r c x' y →
      (g y x < g y x' ↔ x < x') := by
    intro x x' y h h'
    simp only [g, dif_pos h, dif_pos h']
    exact (ps y).toRelEmbedding.map_rel_iff
  let G : X → Finset W → C := fun y t => c (insert y (t.image (inv y)))
  let code : X → Σ i : W, (Finset {w // w < i} → C) :=
    fun y => ⟨(ps y).top, fun t => G y (t.map (Function.Embedding.subtype _))⟩
  let Φ : (Σ i : W, (Finset {w // w < i} → C)) → Finset W → Option C := fun p t =>
    if ht : ∀ w ∈ t, w < p.1 then some (p.2 (t.subtype (· < p.1))) else none
  have hΦ : ∀ y t, (∀ w ∈ t, w < (ps y).top) → Φ (code y) t = some (G y t) := by
    intro y t ht
    simp only [Φ, code]
    rw [dif_pos ht, Finset.subtype_map_of_mem ht]
  have hGimg : ∀ y y' (s : Finset X), (∀ z ∈ s, treeRel r c z y) →
      (∀ z ∈ s, inv y' (g y z) = z) → G y' (s.image (g y)) = c (insert y' s) := by
    intro y y' s _ h2
    simp only [G]
    rw [Finset.image_image]
    rw [image_eq_self (f := inv y' ∘ g y) (fun z hz => h2 z hz)]
  apply Cardinal.mk_le_of_injective (f := code)
  intro y y' hyy
  have htop : (ps y).top = (ps y').top := congrArg Sigma.fst hyy
  have hG : ∀ t : Finset W, (∀ w ∈ t, w < (ps y).top) → G y t = G y' t := by
    intro t ht
    have ht' : ∀ w ∈ t, w < (ps y').top := fun w hw => htop ▸ ht w hw
    have := congrArg (fun p => Φ p t) hyy
    rw [hΦ y t ht, hΦ y' t ht'] at this
    exact Option.some.inj this
  have step1 : ∀ x, treeRel r c x y → inv y' (g y x) = x := by
    intro x
    refine WellFoundedLT.induction (motive := fun x => treeRel r c x y → inv y' (g y x) = x) x ?_
    intro x IH hx
    have hgx : g y x < (ps y').top := htop ▸ g_lt hx
    set x' := inv y' (g y x) with hx'def
    have hx' : treeRel r c x' y' := inv_mem hgx
    have hgx' : g y' x' = g y x := g_inv hgx
    have agree : ∀ z, treeRel r c z y → z < x → treeRel r c z y' ∧ g y' z = g y z := by
      intro z hz hzx
      have e := IH z hzx hz
      have hgz : g y z < (ps y').top := htop ▸ g_lt hz
      refine ⟨e ▸ inv_mem hgz, ?_⟩
      have := g_inv hgz
      rwa [e] at this
    have hPx : ∀ z, treeRel r c z x ↔ treeRel r c z x' := by
      intro z
      constructor
      · intro hzx
        have hzy : treeRel r c z y := treeRel_trans hx hzx
        obtain ⟨hzy', hgz⟩ := agree z hzy (treeRel_lt hzx)
        apply treeRel_chain hx' hzy'
        rw [← g_lt_iff hzy' hx', hgz, hgx']
        exact (g_lt_iff hzy hx).2 (treeRel_lt hzx)
      · intro hzx'
        have hzy' : treeRel r c z y' := treeRel_trans hx' hzx'
        have hw : g y' z < (ps y).top := htop ▸ g_lt hzy'
        have hz0 : treeRel r c (inv y (g y' z)) y := inv_mem hw
        have hgz0 : g y (inv y (g y' z)) = g y' z := g_inv hw
        have hz0x : inv y (g y' z) < x := by
          rw [← g_lt_iff hz0 hx, hgz0, ← hgx']
          exact (g_lt_iff hzy' hx').2 (treeRel_lt hzx')
        have e := IH _ hz0x hz0
        rw [hgz0, inv_g hzy'] at e
        rw [e]
        exact treeRel_chain hx hz0 hz0x
    have hcol : ∀ s : Finset X, (∀ z ∈ s, treeRel r c z x) → s.card = r →
        c (insert x s) = c (insert x' s) := by
      intro s hs hsc
      rw [treeRel_endhom hx s hs hsc,
        treeRel_endhom hx' s (fun z hz => (hPx z).1 (hs z hz)) hsc]
      have hsy : ∀ z ∈ s, treeRel r c z y := fun z hz => treeRel_trans hx (hs z hz)
      have h1 := hGimg y y s hsy (fun z hz => inv_g (hsy z hz))
      have h2 := hGimg y y' s hsy (fun z hz => IH z (treeRel_lt (hs z hz)) (hsy z hz))
      rw [← h1, ← h2]
      apply hG
      intro w hw
      rw [Finset.mem_image] at hw
      obtain ⟨z, hz, rfl⟩ := hw
      exact g_lt (hsy z hz)
    exact (treeRel_inj hPx hcol).symm
  have hPy : ∀ z, treeRel r c z y ↔ treeRel r c z y' := by
    intro z
    constructor
    · intro hz
      rw [← step1 z hz]
      exact inv_mem (htop ▸ g_lt hz)
    · intro hz
      have hw : g y' z < (ps y).top := htop ▸ g_lt hz
      have hz0 : treeRel r c (inv y (g y' z)) y := inv_mem hw
      have e := step1 _ hz0
      rw [g_inv hw, inv_g hz] at e
      rw [e]
      exact hz0
  have hcol : ∀ s : Finset X, (∀ z ∈ s, treeRel r c z y) → s.card = r →
      c (insert y s) = c (insert y' s) := by
    intro s hs _
    have h1 := hGimg y y s hs (fun z hz => inv_g (hs z hz))
    have h2 := hGimg y y' s hs (fun z hz => step1 z (hs z hz))
    rw [← h1, ← h2]
    apply hG
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    exact g_lt (hs z hz)
  exact treeRel_inj hPy hcol

end Bound

theorem base_bound {X C : Type u} (n : C → ℕ) (c : Finset X → C) (hc : Bad 1 c n) :
    #X ≤ Cardinal.sum (fun α => (n α : Cardinal.{u})) := by
  classical
  have hfib : ∀ α, #{x // c {x} = α} < n α := by
    intro α
    by_contra hle
    push Not at hle
    obtain ⟨p, hp⟩ := Cardinal.le_mk_iff_exists_set.1 hle
    obtain ⟨t, -, htc⟩ := Cardinal.mk_set_eq_nat_iff_finset.1 hp
    apply hc α (t.map (Function.Embedding.subtype _)) (by simp [htc])
    intro s hs hsc
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 hsc
    have hx := hs (Finset.mem_singleton_self x)
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
    obtain ⟨w, -, rfl⟩ := hx
    exact w.2
  calc #X = #(Σ α, {x // c {x} = α}) :=
        Cardinal.mk_congr (Equiv.sigmaFiberEquiv (fun x => c {x})).symm
    _ = Cardinal.sum (fun α => #{x // c {x} = α}) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun α => (n α : Cardinal.{u})) :=
        Cardinal.sum_le_sum _ _ (fun α => (hfib α).le)

theorem pos_finite {C : Type u} [Finite C] (n : C → ℕ) : ∀ j : ℕ, ∃ B < ℵ₀,
    ∀ (Z : Type u) [LinearOrder Z] [WellFoundedLT Z] (c' : Finset Z → C),
      Bad (j + 1) c' n → #Z ≤ B := by
  intro j
  induction j with
  | zero =>
    refine ⟨Cardinal.sum (fun α => (n α : Cardinal.{u})), ?_, ?_⟩
    · have : (fun α => (n α : Cardinal.{u})) = fun α => #(ULift.{u} (Fin (n α))) := by
        funext α; simp
      rw [this, ← Cardinal.mk_sigma]
      exact Cardinal.lt_aleph0_of_finite _
    · intro Z _ _ c' hc'
      exact base_bound n c' hc'
  | succ j ih =>
    obtain ⟨B, hB0, hB⟩ := ih
    refine ⟨#(Σ i : (Order.succ B).ord.ToType, (Finset {w // w < i} → C)), ?_, ?_⟩
    · have hW : #((Order.succ B).ord.ToType) < ℵ₀ := by
        rw [Cardinal.mk_ord_toType]
        exact Cardinal.isSuccLimit_aleph0.succ_lt hB0
      have : Finite ((Order.succ B).ord.ToType) := Cardinal.lt_aleph0_iff_finite.1 hW
      exact Cardinal.lt_aleph0_of_finite _
    · intro Z _ _ c' hc'
      exact tree_bound (j + 1) n B hB c' hc'

/-- The tower `κ, 2^κ, 2^(2^κ), ...`. -/
noncomputable def tow (κ : Cardinal.{u}) : ℕ → Cardinal.{u}
  | 0 => κ
  | j + 1 => 2 ^ tow κ j

theorem le_tow (κ : Cardinal.{u}) : ∀ j, κ ≤ tow κ j
  | 0 => le_rfl
  | j + 1 => (le_tow κ j).trans (Cardinal.cantor _).le

theorem pos_infinite {C : Type u} (hC : ℵ₀ ≤ #C) (n : C → ℕ) : ∀ j : ℕ,
    ∀ (Z : Type u) [LinearOrder Z] [WellFoundedLT Z] (c' : Finset Z → C),
      Bad (j + 1) c' n → #Z ≤ tow #C j := by
  intro j
  induction j with
  | zero =>
    intro Z _ _ c' hc'
    refine (base_bound n c' hc').trans ?_
    refine (Cardinal.sum_le_mk_mul_iSup _).trans ?_
    calc #C * ⨆ α, (n α : Cardinal.{u}) ≤ #C * ℵ₀ := by
          gcongr
          exact ciSup_le' (fun α => Cardinal.natCast_lt_aleph0.le)
      _ = #C := Cardinal.mul_aleph0_eq hC
      _ = tow #C 0 := rfl
  | succ j ih =>
    intro Z _ _ c' hc'
    refine (tree_bound (j + 1) n (tow #C j) ih c' hc').trans ?_
    set B := tow #C j with hBdef
    have hCB : #C ≤ B := le_tow _ _
    have hB0 : ℵ₀ ≤ B := hC.trans hCB
    have h2B : ℵ₀ ≤ (2 : Cardinal.{u}) ^ B := hB0.trans (Cardinal.cantor _).le
    have hC0 : #C ≠ 0 := by
      intro h; rw [h] at hC; exact absurd hC (not_le.2 Cardinal.aleph0_pos)
    rw [Cardinal.mk_sigma]
    refine (Cardinal.sum_le_mk_mul_iSup _).trans ?_
    have hterm : ∀ i : (Order.succ B).ord.ToType,
        #(Finset {w // w < i} → C) ≤ (2 : Cardinal.{u}) ^ B := by
      intro i
      have hD : #{w // w < i} ≤ B := by
        have := Cardinal.mk_Iio_lt i (by rw [Cardinal.mk_ord_toType, Ordinal.type_toType])
        rw [Cardinal.mk_ord_toType] at this
        exact Order.lt_succ_iff.1 this
      have hFD : #(Finset {w // w < i}) ≤ B := by
        rcases finite_or_infinite {w // w < i} with hfin | hinf
        · exact (Cardinal.lt_aleph0_of_finite _).le.trans hB0
        · rw [Cardinal.mk_finset_of_infinite]; exact hD
      rw [← Cardinal.power_def]
      calc #C ^ #(Finset {w // w < i}) ≤ #C ^ B := Cardinal.power_le_power_left hC0 hFD
        _ ≤ ((2 : Cardinal.{u}) ^ B) ^ B :=
            Cardinal.power_le_power_right (hCB.trans (Cardinal.cantor _).le)
        _ = (2 : Cardinal.{u}) ^ (B * B) := Cardinal.power_mul.symm
        _ = (2 : Cardinal.{u}) ^ B := by rw [Cardinal.mul_eq_self hB0]
    calc #((Order.succ B).ord.ToType) * ⨆ i, #(Finset {w // w < i} → C)
        ≤ (2 : Cardinal.{u}) ^ B * (2 : Cardinal.{u}) ^ B := by
          gcongr
          · rw [Cardinal.mk_ord_toType]
            exact Order.succ_le_of_lt (Cardinal.cantor B)
          · exact ciSup_le' hterm
      _ = (2 : Cardinal.{u}) ^ B := Cardinal.mul_eq_self h2B
      _ = tow #C (j + 1) := rfl

section Enum

variable {α : Type*} [LinearOrder α] [Inhabited α]

/-- The `i`-th element of `T` in increasing order. -/
noncomputable def enum (T : Finset α) (i : ℕ) : α :=
  if h : i < T.card then T.orderEmbOfFin rfl ⟨i, h⟩ else default

theorem enum_mem {T : Finset α} {i : ℕ} (h : i < T.card) : enum T i ∈ T := by
  unfold enum
  rw [dif_pos h]
  exact T.orderEmbOfFin_mem rfl _

theorem enum_lt {T : Finset α} {i j : ℕ} (hij : i < j) (hj : j < T.card) :
    enum T i < enum T j := by
  unfold enum
  rw [dif_pos (hij.trans hj), dif_pos hj]
  exact (T.orderEmbOfFin rfl).strictMono (show (⟨i, _⟩ : Fin T.card) < ⟨j, hj⟩ from hij)

theorem enum_unique [DecidableEq α] {T : Finset α} {m : ℕ} (u : ℕ → α)
    (hu : ∀ i j, i < j → j < m → u i < u j) (hT : T = (Finset.range m).image u) :
    T.card = m ∧ ∀ i < m, enum T i = u i := by
  classical
  have hcard : T.card = m := by
    rw [hT, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hu i j h hj).ne hij
    · exact (hu j i h hi).ne hij.symm
  refine ⟨hcard, fun i hi => ?_⟩
  have key := Finset.orderEmbOfFin_unique (s := T) (k := T.card) rfl
    (f := fun x : Fin T.card => u x.1) ?_ ?_
  · unfold enum
    rw [dif_pos (hcard ▸ hi)]
    exact (congrFun key ⟨i, hcard ▸ hi⟩).symm
  · intro x
    have hx : u x.1 ∈ (Finset.range m).image u :=
      Finset.mem_image_of_mem _ (Finset.mem_range.2 (hcard ▸ x.2))
    rwa [← hT] at hx
  · intro x y hxy
    exact hu _ _ hxy (hcard ▸ y.2)

theorem enum_image [DecidableEq α] (T : Finset α) : (Finset.range T.card).image (enum T) = T := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact enum_mem (Finset.mem_range.1 hi)
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (enum_lt h hj).ne hij
    · exact (enum_lt h hi).ne hij.symm

end Enum

section Delta

variable {Y : Type u} [LinearOrder Y] [WellFoundedLT Y] [Inhabited Y]

open Classical in
/-- First point where two functions differ. -/
noncomputable def dlt (f g : Y → Bool) : Y :=
  if h : ∃ i, f i ≠ g i then (wellFounded_lt (α := Y)).min {i | f i ≠ g i} h else default

theorem dlt_eq {f g : Y → Bool} {i : Y} (hlt : ∀ j < i, f j = g j) (hi : f i ≠ g i) :
    dlt f g = i := by
  have h : ∃ i, f i ≠ g i := ⟨i, hi⟩
  unfold dlt
  rw [dif_pos h]
  have hmem := (wellFounded_lt (α := Y)).min_mem {i | f i ≠ g i} h
  have hnot : ¬ i < (wellFounded_lt (α := Y)).min {i | f i ≠ g i} h :=
    WellFounded.not_lt_min (wellFounded_lt (α := Y)) {i | f i ≠ g i} (x := i) hi
  rcases lt_trichotomy ((wellFounded_lt (α := Y)).min {i | f i ≠ g i} h) i with h1 | h1 | h1
  · exact absurd (hlt _ h1) hmem
  · exact h1
  · exact absurd h1 hnot

instance : Inhabited (Lex (Y → Bool)) := ⟨toLex (fun _ => false)⟩

/-- First difference of two elements of the lexicographic power. -/
noncomputable def D (f g : Lex (Y → Bool)) : Y := dlt (ofLex f) (ofLex g)

theorem lt_D {f g : Lex (Y → Bool)} (h : f < g) :
    (∀ j < D f g, ofLex f j = ofLex g j) ∧ ofLex f (D f g) = false ∧
      ofLex g (D f g) = true := by
  obtain ⟨i, hi, hfi⟩ := h
  have hfi' : ofLex f i = false ∧ ofLex g i = true := by
    revert hfi
    change ofLex f i < ofLex g i → _
    cases ofLex f i <;> cases ofLex g i <;> decide
  have hD : D f g = i := dlt_eq hi (by rw [hfi'.1, hfi'.2]; decide)
  rw [hD]
  exact ⟨hi, hfi'⟩

theorem D_tri {f g h : Lex (Y → Bool)} (hfg : f < g) (hgh : g < h) :
    D f g ≠ D g h ∧ D f h = min (D f g) (D g h) := by
  obtain ⟨a1, a2, a3⟩ := lt_D hfg
  obtain ⟨b1, b2, b3⟩ := lt_D hgh
  have hne : D f g ≠ D g h := by
    intro he
    rw [he] at a3
    rw [a3] at b2
    exact Bool.noConfusion b2
  refine ⟨hne, ?_⟩
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rw [min_eq_left hlt.le]
    apply dlt_eq
    · intro j hj
      rw [a1 j hj, b1 j (hj.trans hlt)]
    · rw [a2, ← b1 _ hlt, a3]; decide
  · rw [min_eq_right hlt.le]
    apply dlt_eq
    · intro j hj
      rw [a1 j (hj.trans hlt), b1 j hj]
    · rw [a1 _ hlt, b2, b3]; decide

/-- In an increasing chain whose consecutive differences increase, the first difference of
`h p` and `h q` is the `p`-th consecutive difference. -/
theorem D_inc (h : ℕ → Lex (Y → Bool)) (m : ℕ) (hh : ∀ i j, i < j → j ≤ m → h i < h j)
    (hd : ∀ i, i + 1 < m → D (h i) (h (i + 1)) < D (h (i + 1)) (h (i + 2))) :
    ∀ p q, p < q → q ≤ m → D (h p) (h q) = D (h p) (h (p + 1)) := by
  have mono : ∀ p q, p < q → q + 1 ≤ m → D (h p) (h (p + 1)) < D (h q) (h (q + 1)) := by
    intro p q hpq hq
    induction q with
    | zero => omega
    | succ q ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hpq with h1 | h1
      · exact (ih h1 (by omega)).trans (hd q (by omega))
      · subst h1; exact hd p (by omega)
  intro p q hpq hq
  induction q with
  | zero => omega
  | succ q ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hpq with h1 | h1
    · rw [(D_tri (hh p q h1 (by omega)) (hh q (q + 1) (by omega) hq)).2, ih h1 (by omega)]
      exact min_eq_left (mono p q h1 hq).le
    · subst h1; rfl

theorem D_dec (h : ℕ → Lex (Y → Bool)) (m : ℕ) (hh : ∀ i j, i < j → j ≤ m → h i < h j)
    (hd : ∀ i, i + 1 < m → D (h (i + 1)) (h (i + 2)) < D (h i) (h (i + 1))) :
    ∀ p q, p < q → q ≤ m → D (h p) (h (q + 1 - 1)) = D (h (q - 1)) (h q) := by
  intro p q hpq hq
  induction q with
  | zero => omega
  | succ q ih =>
    simp only [Nat.add_sub_cancel] at ih ⊢
    rcases Nat.lt_succ_iff_lt_or_eq.1 hpq with h1 | h1
    · rw [(D_tri (hh p q h1 (by omega)) (hh q (q + 1) (by omega) hq)).2, ih h1 (by omega)]
      apply min_eq_right
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      exact (hd q' (by omega)).le
    · subst h1; rfl

end Delta

theorem sub_enum {α : Type*} [LinearOrder α] [Inhabited α] [DecidableEq α] (H : Finset α) (m : ℕ)
    (u : ℕ → ℕ) (hu : ∀ a b, a < b → b < m → u a < u b) (huk : ∀ a < m, u a < H.card) :
    (Finset.range m).image (fun a => enum H (u a)) ⊆ H ∧
      ((Finset.range m).image (fun a => enum H (u a))).card = m ∧
      ∀ a < m, enum ((Finset.range m).image (fun a => enum H (u a))) a = enum H (u a) := by
  classical
  have key := enum_unique (T := (Finset.range m).image (fun a => enum H (u a)))
    (fun a => enum H (u a)) (fun a b hab hb => enum_lt (hu a b hab hb) (huk b hb)) rfl
  refine ⟨?_, key.1, key.2⟩
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact enum_mem (huk a (Finset.mem_range.1 ha))

theorem chain_lt {β : Type*} [LinearOrder β] (d : ℕ → β) (k : ℕ)
    (h : ∀ t, t + 1 < k → d t < d (t + 1)) : ∀ i j, i < j → j < k → d i < d j := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h1 | h1
    · exact (ih h1 (by omega)).trans (h j hj)
    · subst h1; exact h i hj

theorem chain_gt {β : Type*} [LinearOrder β] (d : ℕ → β) (k : ℕ)
    (h : ∀ t, t + 1 < k → d (t + 1) < d t) : ∀ i j, i < j → j < k → d j < d i := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h1 | h1
    · exact (h j hj).trans (ih h1 (by omega))
    · subst h1; exact h i hj

section Step

variable {Y : Type u} [LinearOrder Y] [WellFoundedLT Y] [Inhabited Y] {C : Type u}

/-- Consecutive first differences of a finite set. -/
noncomputable def dseq (T : Finset (Lex (Y → Bool))) (i : ℕ) : Y :=
  D (enum T i) (enum T (i + 1))

/-- The up/down pattern of consecutive first differences. -/
noncomputable def signs (T : Finset (Lex (Y → Bool))) : Finset ℕ :=
  (Finset.range (T.card - 2)).filter (fun i => dseq T i < dseq T (i + 1))

/-- The set of consecutive first differences. -/
noncomputable def dset (T : Finset (Lex (Y → Bool))) : Finset Y :=
  (Finset.range (T.card - 1)).image (dseq T)

/-- The stepped-up colouring. -/
noncomputable def upCol (c : Finset Y → C) (T : Finset (Lex (Y → Bool))) : Finset ℕ × C :=
  (signs T, c (dset T))

theorem stepUp (r k : ℕ) (hr : 2 ≤ r) (hk : r + 1 ≤ k) (c : Finset Y → C)
    (hc : ∀ (α : C) (H : Finset Y), H.card = k → ¬ Homog r c α H) :
    ∀ (β : Finset ℕ × C) (H : Finset (Lex (Y → Bool))), H.card = k + 1 →
      ¬ Homog (r + 1) (upCol c) β H := by
  classical
  rintro ⟨σ, α⟩ H hH hom
  have hh : ∀ i j, i < j → j ≤ k → enum H i < enum H j :=
    fun i j hij hj => enum_lt hij (by omega)
  set d : ℕ → Y := fun i => D (enum H i) (enum H (i + 1)) with hd
  -- colour of a sub-configuration with `r + 1` elements
  have colT : ∀ u : ℕ → ℕ, (∀ a b, a < b → b < r + 1 → u a < u b) → (∀ a < r + 1, u a ≤ k) →
      signs ((Finset.range (r + 1)).image (fun a => enum H (u a))) = σ ∧
      c (dset ((Finset.range (r + 1)).image (fun a => enum H (u a)))) = α := by
    intro u hu huk
    obtain ⟨hTH, hTc, -⟩ := sub_enum H (r + 1) u hu (fun a ha => by have := huk a ha; omega)
    have := hom _ hTH hTc
    simp only [upCol, Prod.mk.injEq] at this
    exact this
  have enumT : ∀ u : ℕ → ℕ, (∀ a b, a < b → b < r + 1 → u a < u b) → (∀ a < r + 1, u a ≤ k) →
      ∀ a, a + 1 < r + 1 →
        dseq ((Finset.range (r + 1)).image (fun a => enum H (u a))) a =
          D (enum H (u a)) (enum H (u (a + 1))) := by
    intro u hu huk a ha
    obtain ⟨-, -, hTe⟩ := sub_enum H (r + 1) u hu (fun a ha => by have := huk a ha; omega)
    unfold dseq
    rw [hTe a (by omega), hTe (a + 1) ha]
  have cardT : ∀ u : ℕ → ℕ, (∀ a b, a < b → b < r + 1 → u a < u b) → (∀ a < r + 1, u a ≤ k) →
      ((Finset.range (r + 1)).image (fun a => enum H (u a))).card = r + 1 := by
    intro u hu huk
    exact (sub_enum H (r + 1) u hu (fun a ha => by have := huk a ha; omega)).2.1
  -- windows
  have hwin : ∀ j, j + r ≤ k → ∀ a < r - 1, (a ∈ σ ↔ d (j + a) < d (j + a + 1)) := by
    intro j hj a ha
    have hu : ∀ a b, a < b → b < r + 1 → j + a < j + b := fun a b hab _ => by omega
    have huk : ∀ a < r + 1, j + a ≤ k := fun a ha => by omega
    rw [← (colT (fun a => j + a) hu huk).1]
    unfold signs
    rw [Finset.mem_filter, cardT _ hu huk, enumT _ hu huk a (by omega),
      enumT _ hu huk (a + 1) (by omega)]
    simp only [Finset.mem_range, hd]
    constructor
    · rintro ⟨-, h⟩
      rwa [show j + (a + 1) = j + a + 1 by omega] at h
    · intro h
      refine ⟨by omega, ?_⟩
      rwa [show j + (a + 1) = j + a + 1 by omega]
  have hσ : ∀ a, a < r - 1 → (a ∈ σ ↔ 0 ∈ σ) := by
    intro a
    induction a with
    | zero => intro _; exact Iff.rfl
    | succ a ih =>
      intro ha
      rw [← ih (by omega), hwin 0 (by omega) (a + 1) ha, hwin 1 (by omega) a (by omega)]
      rw [show 0 + (a + 1) = 1 + a by omega]
  have hdir : ∀ t, t + 2 ≤ k → (d t < d (t + 1) ↔ 0 ∈ σ) := by
    intro t ht
    by_cases htk : t + r ≤ k
    · have := hwin t htk 0 (by omega)
      simp only [Nat.add_zero] at this
      exact this.symm
    · have := hwin (k - r) (by omega) (t - (k - r)) (by omega)
      rw [show k - r + (t - (k - r)) = t by omega] at this
      rw [← this]
      exact hσ _ (by omega)
  have hne : ∀ t, t + 2 ≤ k → d t ≠ d (t + 1) := by
    intro t ht
    exact (D_tri (hh t (t + 1) (by omega) (by omega)) (hh (t + 1) (t + 2) (by omega) ht)).1
  -- realisation of an `r`-subset of the difference set
  have realize : ∀ u v : ℕ → ℕ, (∀ a b, a < b → b < r + 1 → u a < u b) →
      (∀ a < r + 1, u a ≤ k) → (∀ a < r, D (enum H (u a)) (enum H (u (a + 1))) = d (v a)) →
      c ((Finset.range r).image (fun a => d (v a))) = α := by
    intro u v hu huk huv
    rw [← (colT u hu huk).2]
    congr 1
    unfold dset
    rw [cardT u hu huk, Nat.add_sub_cancel]
    apply Finset.image_congr
    intro a ha
    simp only [Finset.coe_range, Set.mem_Iio] at ha
    simp only
    rw [enumT u hu huk a (by omega), huv a ha]
  -- strict monotonicity of `d`
  have hstrict : (∀ i j, i < j → j < k → d i < d j) ∨ (∀ i j, i < j → j < k → d j < d i) := by
    by_cases h0 : 0 ∈ σ
    · left
      exact chain_lt d k (fun t ht => (hdir t (by omega)).2 h0)
    · right
      refine chain_gt d k (fun t ht => ?_)
      have h1 : ¬ d t < d (t + 1) := fun h => h0 ((hdir t (by omega)).1 h)
      exact lt_of_le_of_ne (not_lt.1 h1) (hne t (by omega)).symm
  have hinj : Set.InjOn d ↑(Finset.range k) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · rcases hstrict with hs | hs
      · exact (hs i j h hj).ne hij
      · exact (hs i j h hj).ne hij.symm
    · rcases hstrict with hs | hs
      · exact (hs j i h hi).ne hij.symm
      · exact (hs j i h hi).ne hij
  apply hc α ((Finset.range k).image d) (by rw [Finset.card_image_of_injOn hinj, Finset.card_range])
  intro s hs hsc
  set I := (Finset.range k).filter (fun i => d i ∈ s) with hI
  have hIs : I.image d = s := by
    ext x
    simp only [Finset.mem_image, hI, Finset.mem_filter]
    constructor
    · rintro ⟨i, ⟨-, hi⟩, rfl⟩
      exact hi
    · intro hx
      have := hs hx
      rw [Finset.mem_image] at this
      obtain ⟨i, hi, rfl⟩ := this
      exact ⟨i, ⟨hi, hx⟩, rfl⟩
  have hIk : I ⊆ Finset.range k := Finset.filter_subset _ _
  have hIc : I.card = r := by
    rw [← hsc, ← hIs, Finset.card_image_of_injOn (hinj.mono (by exact_mod_cast hIk))]
  set v := enum I with hv
  have hvk : ∀ a < r, v a < k := fun a ha =>
    Finset.mem_range.1 (hIk (enum_mem (by omega)))
  have hvmono : ∀ a b, a < b → b < r → v a < v b := fun a b hab hb => enum_lt hab (by omega)
  have hvle : ∀ a b, a ≤ b → b < r → v a ≤ v b := by
    intro a b hab hb
    rcases eq_or_lt_of_le hab with h | h
    · rw [h]
    · exact (hvmono a b h hb).le
  have himg : (Finset.range r).image (fun a => d (v a)) = s := by
    rw [← hIs, ← hIc]
    conv_rhs => rw [← enum_image I]
    rw [Finset.image_image]
    rfl
  rw [← himg]
  rcases hstrict with hs' | hs'
  · -- increasing differences
    have hdinc : ∀ i, i + 1 < k → D (enum H i) (enum H (i + 1)) <
        D (enum H (i + 1)) (enum H (i + 2)) := fun i hi => hs' i (i + 1) (by omega) hi
    apply realize (fun a => if a < r then v a else v (r - 1) + 1) v
    · intro a b hab hb
      by_cases hbr : b < r
      · simp only [if_pos hbr, if_pos (hab.trans hbr)]
        exact hvmono a b hab hbr
      · simp only [if_neg hbr, if_pos (show a < r by omega)]
        exact Nat.lt_succ_of_le (hvle a (r - 1) (by omega) (by omega))
    · intro a ha
      by_cases har : a < r
      · simp only [if_pos har]; exact (hvk a har).le
      · simp only [if_neg har]; exact hvk (r - 1) (by omega)
    · intro a ha
      simp only [if_pos ha]
      by_cases ha1 : a + 1 < r
      · simp only [if_pos ha1]
        exact D_inc (enum H) k hh hdinc (v a) (v (a + 1)) (hvmono a (a + 1) (by omega) ha1)
          (hvk _ ha1).le
      · simp only [if_neg ha1]
        have : a = r - 1 := by omega
        subst this
        exact D_inc (enum H) k hh hdinc (v (r - 1)) (v (r - 1) + 1) (by omega)
          (hvk _ ha)
  · -- decreasing differences
    have hddec : ∀ i, i + 1 < k → D (enum H (i + 1)) (enum H (i + 2)) <
        D (enum H i) (enum H (i + 1)) := fun i hi => hs' i (i + 1) (by omega) hi
    apply realize (fun a => if a = 0 then v 0 else v (a - 1) + 1) v
    · intro a b hab hb
      have hb0 : b ≠ 0 := by omega
      simp only [if_neg hb0]
      by_cases ha0 : a = 0
      · simp only [if_pos ha0]
        exact Nat.lt_succ_of_le (hvle 0 (b - 1) (by omega) (by omega))
      · simp only [if_neg ha0]
        exact Nat.succ_lt_succ (hvmono (a - 1) (b - 1) (by omega) (by omega))
    · intro a ha
      by_cases ha0 : a = 0
      · simp only [if_pos ha0]; exact (hvk 0 (by omega)).le
      · simp only [if_neg ha0]; exact hvk (a - 1) (by omega)
    · intro a ha
      simp only [if_neg (show a + 1 ≠ 0 by omega), Nat.add_sub_cancel]
      have hpq : (if a = 0 then v 0 else v (a - 1) + 1) < v a + 1 := by
        by_cases ha0 : a = 0
        · simp only [if_pos ha0]; subst ha0; omega
        · simp only [if_neg ha0]
          exact Nat.succ_lt_succ (hvmono (a - 1) a (by omega) ha)
      have := D_dec (enum H) k hh hddec _ (v a + 1) hpq (hvk a ha)
      simp only [Nat.add_sub_cancel] at this
      exact this

end Step

/-- The base colouring of pairs by first difference. -/
theorem base_neg (S : Type u) [LinearOrder S] [WellFoundedLT S] [Inhabited S] :
    ∀ (β : S) (H : Finset (Lex (S → Bool))), H.card = 3 →
      ¬ Homog 2 (fun T => D (enum T 0) (enum T 1)) β H := by
  classical
  intro β H hH hom
  have h1 := sub_enum H 2 (fun a => a) (fun a b hab _ => hab) (fun a ha => by omega)
  have h2 := sub_enum H 2 (fun a => 1 + a) (fun a b hab _ => by omega) (fun a ha => by omega)
  have e1 := hom _ h1.1 h1.2.1
  have e2 := hom _ h2.1 h2.2.1
  simp only at e1 e2
  rw [h1.2.2 0 (by omega), h1.2.2 1 (by omega)] at e1
  rw [h2.2.2 0 (by omega), h2.2.2 1 (by omega)] at e2
  simp only [Nat.add_zero] at e2
  have := (D_tri (enum_lt (T := H) (i := 0) (j := 1) (by omega) (by omega))
    (enum_lt (T := H) (i := 1) (j := 2) (by omega) (by omega))).1
  exact this (e1.trans e2.symm)

/- Gluing the two halves together. -/

theorem mk_arrow_bool (α : Type u) : #(α → Bool) = 2 ^ #α := by
  simp

theorem mk_coe_coe_finset {A : Type u} (s : Finset A) : #(↑(↑s : Set A)) = s.card := by
  simp

/-- The tower of types `S, S → Bool, (S → Bool) → Bool, ...`. -/
def towT (S : Type u) : ℕ → Type u
  | 0 => S
  | j + 1 => towT S j → Bool

theorem mk_towT (S : Type u) : ∀ j, #(towT S j) = tow #S j
  | 0 => rfl
  | j + 1 => by
    show #(towT S j → Bool) = 2 ^ tow #S j
    rw [← mk_towT S j, mk_arrow_bool]

theorem neg_tower (S : Type u) [Infinite S] : ∀ j : ℕ, ∃ (C' : Type u), #C' ≤ #S ∧
    ∃ c : Finset (towT S (j + 1)) → C',
      ∀ (β : C') (H : Finset (towT S (j + 1))), H.card = j + 3 → ¬ Homog (j + 2) c β H := by
  intro j
  induction j with
  | zero =>
    obtain ⟨lo, wf⟩ := exists_wellFoundedLT S
    let _ := lo
    have : Inhabited S := ⟨Classical.arbitrary S⟩
    exact ⟨S, le_rfl, (fun T : Finset (Lex (S → Bool)) => D (enum T 0) (enum T 1)), base_neg S⟩
  | succ j ih =>
    obtain ⟨C', hC', c, hc⟩ := ih
    obtain ⟨lo, wf⟩ := exists_wellFoundedLT (towT S (j + 1))
    let _ := lo
    have : Inhabited (towT S (j + 1)) := ⟨show towT S j → Bool from fun _ => false⟩
    refine ⟨Finset ℕ × C', ?_, upCol c, ?_⟩
    · rw [Cardinal.mk_prod, Cardinal.lift_uzero, Cardinal.mk_finset_of_infinite, Cardinal.mk_nat,
        Cardinal.lift_aleph0]
      calc ℵ₀ * #C' ≤ ℵ₀ * #S := by gcongr
        _ = #S := Cardinal.aleph0_mul_eq (Cardinal.aleph0_le_mk S)
    · exact stepUp (j + 2) (j + 3) (by omega) (by omega) c hc

theorem main (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam)
    (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    Combinatorics.cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    Combinatorics.cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u})) := by
  classical
  intro hP
  by_contra hcon
  unfold Combinatorics.cardinalPartitionRel at hcon
  push Not at hcon
  obtain ⟨A, hA, col, hcol⟩ := hcon
  have : Infinite A := Cardinal.infinite_iff.2 (hA ▸ hlam)
  -- every target is at least `r`
  have hnr : ∀ i, r ≤ n i := by
    intro i
    by_contra h
    push Not at h
    have hle : (n i : Cardinal.{u}) ≤ #A :=
      (Cardinal.natCast_lt_aleph0.le).trans (hA ▸ hlam)
    obtain ⟨H, hH⟩ := Cardinal.le_mk_iff_exists_set.1 hle
    obtain ⟨s, hs, hsH, -⟩ := hcol i H hH
    have h1 : #(↑(↑s : Set A)) ≤ #H := Cardinal.mk_le_mk_of_subset hsH
    rw [mk_coe_coe_finset, hs, hH] at h1
    exact absurd (Nat.cast_le.1 h1) (not_le.2 h)
  -- every colour actually used has target at least `r + 1`
  have hS : ∀ s : {s : Finset A // s.card = r}, r + 1 ≤ n (col s) := by
    intro s
    by_contra h
    have hn : n (col s) = r := by have := hnr (col s); omega
    obtain ⟨t, ht, htH, hne⟩ := hcol (col s) (↑s.1 : Set A)
      (by rw [hn, mk_coe_coe_finset, s.2])
    have hts : t = s.1 := Finset.eq_of_subset_of_card_le (by exact_mod_cast htH)
      (by rw [ht, s.2])
    apply hne
    congr 1
    exact Subtype.ext hts
  obtain ⟨s0, hs0⟩ := Infinite.exists_subset_card_eq A r
  let S := {i : γ.ToType // r + 1 ≤ n i}
  let cS : Finset A → S := fun t =>
    if h : t.card = r then ⟨col ⟨t, h⟩, hS _⟩ else ⟨col ⟨s0, hs0⟩, hS _⟩
  let nS : S → ℕ := fun α => n α.1
  have hbad : Bad r cS nS := by
    intro α H hHc hom
    obtain ⟨s, hs, hsH, hne⟩ := hcol α.1 (↑H : Set A) (by rw [mk_coe_coe_finset, hHc])
    have := hom s (by exact_mod_cast hsH) hs
    simp only [cS, dif_pos hs] at this
    exact hne (congrArg Subtype.val this)
  obtain ⟨lo, wf⟩ := exists_wellFoundedLT A
  let _ := lo
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  rcases finite_or_infinite S with hfin | hinf
  · obtain ⟨B, hB0, hB⟩ := pos_finite nS (m + 1)
    have := hB A cS hbad
    rw [hA] at this
    exact absurd (this.trans_lt hB0) (not_lt.2 hlam)
  · have hS0 : ℵ₀ ≤ #S := Cardinal.aleph0_le_mk S
    have hAle : #A ≤ #(towT S (m + 1)) := by
      rw [mk_towT]; exact pos_infinite hS0 nS (m + 1) A cS hbad
    obtain ⟨C', hC', c, hc⟩ := neg_tower S (m + 1)
    have h2 : #(A → Bool) ≤ #(towT S (m + 2)) := by
      show #(A → Bool) ≤ #(towT S (m + 1) → Bool)
      rw [mk_arrow_bool, mk_arrow_bool]
      exact Cardinal.power_le_power_left two_ne_zero hAle
    obtain ⟨ι⟩ := (Cardinal.le_def _ _).1 h2
    obtain ⟨κ⟩ := (Cardinal.le_def _ _).1 hC'
    let col' : {s : Finset (A → Bool) // s.card = m + 2 + 1} → γ.ToType :=
      fun s => (κ (c (s.1.map ι))).1
    have hAB : #(A → Bool) = (2 : Cardinal.{u}) ^ lam := by
      rw [mk_arrow_bool, hA]
    obtain ⟨i, H, hH, hhom⟩ := hP (A → Bool) hAB col'
    have hH' : #H = ((n i + 1 : ℕ) : Cardinal.{u}) := by rw [hH]; push_cast; rfl
    obtain ⟨Hf, rfl, hHf⟩ := Cardinal.mk_set_eq_nat_iff_finset.1 hH'
    have hni := hnr i
    obtain ⟨t0, ht0, ht0c⟩ := Finset.exists_subset_card_eq (s := Hf) (n := m + 2 + 1)
      (by omega)
    have hi : col' ⟨t0, ht0c⟩ = i := hhom t0 ht0c (by exact_mod_cast ht0)
    have hni' : m + 2 + 1 ≤ n i := by
      rw [← hi]; exact (κ (c (t0.map ι))).2
    obtain ⟨H2, hH2, hH2c⟩ := Finset.exists_subset_card_eq (s := Hf) (n := m + 1 + 3)
      (by omega)
    apply hc (c (t0.map ι)) (H2.map ι) (by rw [Finset.card_map, hH2c])
    intro s hs hsc
    set s' := H2.filter (fun x => ι x ∈ s) with hs'
    have hs'map : s'.map ι = s := by
      ext y
      simp only [Finset.mem_map, hs', Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨-, hx⟩, rfl⟩
        exact hx
      · intro hy
        have := hs hy
        rw [Finset.mem_map] at this
        obtain ⟨x, hx, rfl⟩ := this
        exact ⟨x, ⟨hx, hy⟩, rfl⟩
    have hs'c : s'.card = m + 2 + 1 := by
      rw [← Finset.card_map ι, hs'map, hsc]
    have e1 : col' ⟨s', hs'c⟩ = i :=
      hhom s' hs'c (fun x hx => hH2 (Finset.filter_subset _ _ hx))
    have e2 : (κ (c (s'.map ι))).1 = (κ (c (t0.map ι))).1 := e1.trans hi.symm
    rw [hs'map] at e2
    exact κ.injective (Subtype.ext e2)

/-- The repository statement `Erdos1167.erdos_1167.variants.finite_targets`, with its exact type. -/
theorem erdos_1167_finite_targets :
    type_of% @Erdos1167.erdos_1167.variants.finite_targets.{u} := by
  intro r hr lam hlam γ _ n
  exact main r hr lam hlam γ n

end ErdosLean.Erdos1167
