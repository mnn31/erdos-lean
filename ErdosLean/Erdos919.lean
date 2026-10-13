import FormalConjectures.ErdosProblems.«918»

/-!
# Erdős Problem 919

Problem 919 asks for a graph on the ordinal `ω₂²` with chromatic number `ℵ₂` (or `ℵ₁`) such
that the subgraph spanned by any vertex set of order type `< ω₂²` is countably chromatic.

Problem 919 is not in formal-conjectures at the commit pinned in `lakefile.toml`, so the
statements below are copied verbatim from the problem file `FormalConjectures/ErdosProblems/919.lean`
proposed there. They mention the vertex type `(ω_ 2 ^ 2 : Ordinal.{u}).ToType` and
`SimpleGraph.chromaticCardinal` directly. `erdos_919.variants.iff_erdos_918_i` also matches the
right-hand side of `Erdos918.erdos_918.parts.i`, which is imported and checked below by `rfl`.

The proof models `ω₂` as `W := (ℵ₂).ord.ToType` and `ω₂²` as `W ×ₗ W`.

1. A graph `H` on `ω₂` is blown up to a graph on `ω₂ ×ₗ ω₂`: for rows `ξ < ξ'`, the vertices
   `(ξ, η)` and `(ξ', η')` are adjacent iff `ξ ~ ξ'` in `H` and `η ≥ ξ'`. This keeps the
   chromatic number when it is `ℵ₁` or `ℵ₂`, and if every subgraph of `H` on at most `ℵ₁`
   vertices is countably chromatic, then so is every subgraph of the blow-up on a vertex set of
   order type `< ω₂²` (`bigGraph_smallType`). Hence the `ℵ₂` question is equivalent to the
   existence of a graph of size `ℵ₂` with chromatic number `ℵ₂` all of whose `ℵ₁`-sized
   subgraphs are countably chromatic, which is Problem 918(i).
2. Taking the product with the complete graph on `ω₁` caps the chromatic number at `ℵ₁`, so the
   `ℵ₁` question is equivalent to the existence of a graph of size `ℵ₂` that is not countably
   chromatic although all its `ℵ₁`-sized subgraphs are.
3. Under CH the shift graph on `ω₂` is such a graph (Erdős and Hajnal).
-/

universe u

open Cardinal Ordinal Set SimpleGraph

namespace ErdosLean.Erdos919

noncomputable section

/- ## Colourability on a vertex set -/

/-- `G` restricted to `X` has a proper colouring with colours in `α`. -/
def ColorableOn {V : Type*} (G : SimpleGraph V) (X : Set V) (α : Type*) : Prop :=
  ∃ c : V → α, ∀ x ∈ X, ∀ y ∈ X, G.Adj x y → c x ≠ c y

/-- `ColorableOn` is the same as colourability of the induced subgraph. -/
theorem colorableOn_iff_induce {V : Type*} (G : SimpleGraph V) (X : Set V) (α : Type*)
    [Nonempty α] : ColorableOn G X α ↔ Nonempty ((G.induce X).Coloring α) := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨Coloring.mk (fun x => c x) (fun {x y} h => hc x x.2 y y.2 (by simpa using h))⟩
  · rintro ⟨c⟩
    refine ⟨fun v => if h : v ∈ X then c ⟨v, h⟩ else Classical.arbitrary α, ?_⟩
    intro x hx y hy hxy
    simp only [hx, hy, dite_true]
    exact c.valid (by simpa using hxy)

theorem ColorableOn.mono_set {V : Type*} {G : SimpleGraph V} {X Y : Set V} {α : Type*}
    (h : ColorableOn G Y α) (hXY : X ⊆ Y) : ColorableOn G X α := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun x hx y hy => hc x (hXY hx) y (hXY hy)⟩

theorem ColorableOn.of_injective {V : Type*} {G : SimpleGraph V} {X : Set V} {α β : Type*}
    (h : ColorableOn G X α) (f : α → β) (hf : Function.Injective f) : ColorableOn G X β := by
  obtain ⟨c, hc⟩ := h
  exact ⟨f ∘ c, fun x hx y hy hxy e => hc x hx y hy hxy (hf e)⟩

theorem ColorableOn.toNat {V : Type*} {G : SimpleGraph V} {X : Set V} {β : Type*}
    [Encodable β] (h : ColorableOn G X β) : ColorableOn G X ℕ :=
  h.of_injective _ Encodable.encode_injective

theorem ColorableOn.comap {A B : Type*} {G : SimpleGraph B} {Y : Set A} {α : Type*} (f : A → B)
    (h : ColorableOn G (f '' Y) α) : ColorableOn (G.comap f) Y α := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c ∘ f, fun a ha b hb hab => hc _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab⟩

/- ## The blow-up of a graph on `I` to a graph on `I × I` -/

section Blowup

variable {I : Type*} [LinearOrder I]

/-- Vertex `(ξ, η)` sits in row `ξ` at height `η`. Two vertices in rows `ξ < ξ'` are adjacent
iff `ξ ~ ξ'` in `H` and the vertex in the lower row has height `≥ ξ'`. -/
def blowup (H : SimpleGraph I) : SimpleGraph (I × I) where
  Adj p q := (p.1 < q.1 ∧ H.Adj p.1 q.1 ∧ q.1 ≤ p.2) ∨ (q.1 < p.1 ∧ H.Adj q.1 p.1 ∧ p.1 ≤ q.2)
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun p h => by rcases h with h | h <;> exact lt_irrefl _ h.1⟩

theorem blowup_adj {H : SimpleGraph I} {p q : I × I} : (blowup H).Adj p q ↔
    ((p.1 < q.1 ∧ H.Adj p.1 q.1 ∧ q.1 ≤ p.2) ∨ (q.1 < p.1 ∧ H.Adj q.1 p.1 ∧ p.1 ≤ q.2)) :=
  Iff.rfl

theorem blowup_adj_fst {H : SimpleGraph I} {p q : I × I} (h : (blowup H).Adj p q) :
    H.Adj p.1 q.1 := by
  rcases blowup_adj.1 h with h | h
  · exact h.2.1
  · exact h.2.1.symm

/-- Upper bound: `χ(blowup H) ≤ χ(H)`. -/
def blowupColoring {H : SimpleGraph I} {α : Type*} (c : H.Coloring α) :
    (blowup H).Coloring α :=
  Coloring.mk (fun p => c p.1) (fun h => c.valid (blowup_adj_fst h))

/-- Lower bound: if every `α`-colouring of a row has a colour class that is unbounded, then an
`α`-colouring of `blowup H` yields an `α`-colouring of `H`. -/
theorem blowup_lower {H : SimpleGraph I} {α : Type*}
    (hfib : ∀ d : I → α, ∃ a, ∀ x, ∃ y, x ≤ y ∧ d y = a)
    (c : (blowup H).Coloring α) : Nonempty (H.Coloring α) := by
  choose f hf using fun ξ : I => hfib (fun η => c (ξ, η))
  have key : ∀ ξ ξ', ξ < ξ' → H.Adj ξ ξ' → f ξ = f ξ' → False := by
    intro ξ ξ' hlt hadj heq
    obtain ⟨y, -, hy⟩ := hf ξ' ξ'
    obtain ⟨η, hη, hηc⟩ := hf ξ ξ'
    have hA : (blowup H).Adj (ξ, η) (ξ', y) := blowup_adj.2 (Or.inl ⟨hlt, hadj, hη⟩)
    have h1 : c (ξ, η) = f ξ := hηc
    have h2 : c (ξ', y) = f ξ' := hy
    exact c.valid hA (by rw [h1, h2, heq])
  refine ⟨Coloring.mk f ?_⟩
  intro ξ ξ' hadj heq
  rcases lt_trichotomy ξ ξ' with h | h | h
  · exact key _ _ h hadj heq
  · exact H.ne_of_adj hadj h
  · exact key _ _ h hadj.symm heq.symm

/-- Combinatorial core of the small-type case. -/
theorem blowup_small_core {H : SimpleGraph I} (X : Set (I × I)) (ξ₀ : I) (β : I → I)
    (hβ : ∀ p ∈ X, ξ₀ ≤ p.1 → p.2 < β p.1)
    (c₀ : I → ℕ) (hc₀ : ∀ ξ ξ', ξ < ξ₀ → ξ' < ξ₀ → H.Adj ξ ξ' → c₀ ξ ≠ c₀ ξ')
    (c₁ : I → ℕ) (hc₁ : ∀ ξ ξ', ξ < ξ' → H.Adj ξ ξ' → ξ' < β ξ → c₁ ξ ≠ c₁ ξ') :
    ColorableOn (blowup H) X (Bool × ℕ) := by
  classical
  let col : I × I → Bool × ℕ := fun p => if p.1 < ξ₀ then (false, c₀ p.1) else (true, c₁ p.1)
  have key : ∀ p ∈ X, ∀ q ∈ X, p.1 < q.1 → H.Adj p.1 q.1 → q.1 ≤ p.2 → col p ≠ col q := by
    intro p hp q hq hlt hadj hle h
    simp only [col] at h
    split_ifs at h with h1 h2 h2
    · exact hc₀ _ _ h1 h2 hadj (Prod.ext_iff.1 h).2
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact hc₁ _ _ hlt hadj (lt_of_le_of_lt hle (hβ p hp (not_lt.1 h1)))
        (Prod.ext_iff.1 h).2
  refine ⟨col, ?_⟩
  intro p hp q hq hpq
  rcases blowup_adj.1 hpq with ⟨hlt, hadj, hle⟩ | ⟨hlt, hadj, hle⟩
  · exact key p hp q hq hlt hadj hle
  · exact fun h => key q hq p hp hlt hadj hle h.symm

/-- Gluing countable colourings of the bounded blocks between consecutive closure points. -/
theorem Hbeta_colorable [WellFoundedLT I] {H : SimpleGraph I}
    (hinit : ∀ a : I, ∃ c : I → ℕ, ∀ ξ ξ', ξ < a → ξ' < a → H.Adj ξ ξ' → c ξ ≠ c ξ')
    (β : I → I) (hclub : ∀ a : I, ∃ δ, a < δ ∧ ∀ ζ < δ, β ζ ≤ δ) :
    ∃ c₁ : I → ℕ, ∀ ξ ξ', ξ < ξ' → H.Adj ξ ξ' → ξ' < β ξ → c₁ ξ ≠ c₁ ξ' := by
  classical
  let C : Set I := {δ | ∀ ζ < δ, β ζ ≤ δ}
  have hne : ∀ a, {δ | a < δ ∧ δ ∈ C}.Nonempty := fun a => by
    obtain ⟨δ, h1, h2⟩ := hclub a
    exact ⟨δ, h1, h2⟩
  let ν : I → I := fun a => WellFounded.min wellFounded_lt _ (hne a)
  have hν1 : ∀ a, a < ν a ∧ ν a ∈ C := fun a => WellFounded.min_mem _ _ (hne a)
  have hν2 : ∀ a δ, a < δ → δ ∈ C → ν a ≤ δ := fun a δ h1 h2 =>
    not_lt.1 (WellFounded.not_lt_min wellFounded_lt {δ | a < δ ∧ δ ∈ C} ⟨h1, h2⟩)
  choose c hc using hinit
  refine ⟨fun ξ => c (ν ξ) ξ, ?_⟩
  intro ξ ξ' hlt hadj hβ
  have h1 := hν1 ξ
  have hξ' : ξ' < ν ξ := lt_of_lt_of_le hβ (h1.2 ξ h1.1)
  have heq : ν ξ' = ν ξ :=
    le_antisymm (hν2 ξ' (ν ξ) hξ' h1.2) (hν2 ξ (ν ξ') (hlt.trans (hν1 ξ').1) (hν1 ξ').2)
  show c (ν ξ) ξ ≠ c (ν ξ') ξ'
  rw [heq]
  exact hc (ν ξ) ξ ξ' h1.1 hξ' hadj

end Blowup

/- ## Product with a complete graph: capping the chromatic number -/

section Tensor

/-- Categorical product of `H` with the complete graph on `T`. -/
def tensorTop {V : Type*} (H : SimpleGraph V) (T : Type*) : SimpleGraph (V × T) where
  Adj p q := H.Adj p.1 q.1 ∧ p.2 ≠ q.2
  symm := ⟨fun _ _ h => ⟨(And.left h).symm, (And.right h).symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

theorem tensorTop_adj {V T : Type*} {H : SimpleGraph V} {p q : V × T} :
    (tensorTop H T).Adj p q ↔ (H.Adj p.1 q.1 ∧ p.2 ≠ q.2) := Iff.rfl

theorem tensorTop_lower {V T α : Type*} (H : SimpleGraph V)
    (hT : ∀ d : T → α, ∃ t₁ t₂, t₁ ≠ t₂ ∧ d t₁ = d t₂)
    (c : (tensorTop H T).Coloring α) : Nonempty (H.Coloring α) := by
  choose t₁ t₂ hne hd using fun v : V => hT (fun t => c (v, t))
  refine ⟨Coloring.mk (fun v => c (v, t₁ v)) ?_⟩
  intro v w hvw heq
  have hd' : c (v, t₁ v) = c (v, t₂ v) := hd v
  by_cases h : t₁ v = t₁ w
  · exact c.valid (show (tensorTop H T).Adj (v, t₂ v) (w, t₁ w) from
      tensorTop_adj.2 ⟨hvw, fun e => hne v (h.trans e.symm)⟩) (hd'.symm.trans heq)
  · exact c.valid (show (tensorTop H T).Adj (v, t₁ v) (w, t₁ w) from tensorTop_adj.2 ⟨hvw, h⟩) heq

def tensorTopColoringT {V : Type*} (H : SimpleGraph V) (T : Type*) :
    (tensorTop H T).Coloring T :=
  Coloring.mk (fun p => p.2) (fun h => (tensorTop_adj.1 h).2)

theorem tensorTop_colorableOn {V T α : Type*} (H : SimpleGraph V) (X : Set (V × T))
    (h : ColorableOn H (Prod.fst '' X) α) : ColorableOn (tensorTop H T) X α := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun p => c p.1, fun x hx y hy hxy => hc _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ (tensorTop_adj.1 hxy).1⟩

end Tensor

/- ## The Erdős-Hajnal shift graph -/

section Shift

variable (I : Type*) [LinearOrder I]

/-- Vertices are pairs `a < b`; `(a, b) ~ (b, c)`. -/
def shift : SimpleGraph {p : I × I // p.1 < p.2} where
  Adj p q := p.1.2 = q.1.1 ∨ q.1.2 = p.1.1
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun p h => by rcases h with h | h <;> exact (ne_of_lt p.2) h.symm⟩

variable {I}

theorem shift_adj {p q : {p : I × I // p.1 < p.2}} :
    (shift I).Adj p q ↔ (p.1.2 = q.1.1 ∨ q.1.2 = p.1.1) := Iff.rfl

theorem shift_lower {α : Type*} (c : (shift I).Coloring α) : Function.Injective
    (fun b : I => {a : α | ∃ g : I, ∃ h : b < g, c ⟨(b, g), h⟩ = a}) := by
  have key : ∀ b b' : I, b < b' →
      {a : α | ∃ g : I, ∃ h : b < g, c ⟨(b, g), h⟩ = a} ≠
      {a : α | ∃ g : I, ∃ h : b' < g, c ⟨(b', g), h⟩ = a} := by
    intro b b' hlt hS
    have hmem : c ⟨(b, b'), hlt⟩ ∈ {a : α | ∃ g : I, ∃ h : b < g, c ⟨(b, g), h⟩ = a} :=
      ⟨b', hlt, rfl⟩
    rw [hS] at hmem
    obtain ⟨g, hg, hc⟩ := hmem
    exact c.valid (show (shift I).Adj ⟨(b, b'), hlt⟩ ⟨(b', g), hg⟩ from shift_adj.2 (Or.inl rfl)) hc.symm
  intro b b' hS
  rcases lt_trichotomy b b' with h | h | h
  · exact absurd hS (key _ _ h)
  · exact h
  · exact absurd hS.symm (key _ _ h)

/-- Colour of a pair of distinct `T`-indexed binary sequences: first difference and the bit. -/
noncomputable def diffColor {T : Type*} [LinearOrder T] [WellFoundedLT T] [Inhabited T]
    (x y : T → Bool) : T × Bool := by
  classical
  exact if h : ∃ t, x t ≠ y t then
    (WellFounded.min wellFounded_lt {t | x t ≠ y t} h,
      x (WellFounded.min wellFounded_lt {t | x t ≠ y t} h))
  else (default, false)

theorem diffColor_ne {T : Type*} [LinearOrder T] [WellFoundedLT T] [Inhabited T]
    {x y z : T → Bool} (hxy : x ≠ y) (hyz : y ≠ z) : diffColor x y ≠ diffColor y z := by
  classical
  have h1 : ∃ t, x t ≠ y t := Function.ne_iff.1 hxy
  have h2 : ∃ t, y t ≠ z t := Function.ne_iff.1 hyz
  unfold diffColor
  rw [dif_pos h1, dif_pos h2]
  intro h
  obtain ⟨ht, hb⟩ := Prod.ext_iff.1 h
  have hm := WellFounded.min_mem wellFounded_lt {t | x t ≠ y t} h1
  exact hm (hb.trans (congrArg y ht.symm))

theorem shift_colorableOn {T : Type*} [LinearOrder T] [WellFoundedLT T] [Inhabited T]
    (S : Set I) (f : I → T → Bool) (hf : Set.InjOn f S) :
    ColorableOn (shift I) {p | p.1.1 ∈ S ∧ p.1.2 ∈ S} (T × Bool) := by
  refine ⟨fun p => diffColor (f p.1.1) (f p.1.2), ?_⟩
  intro p hp q hq hpq
  have hne : ∀ r : {p : I × I // p.1 < p.2}, r.1.1 ∈ S → r.1.2 ∈ S → f r.1.1 ≠ f r.1.2 :=
    fun r h1 h2 e => (ne_of_lt r.2) (hf h1 h2 e)
  have e1 := hne p hp.1 hp.2
  have e2 := hne q hq.1 hq.2
  show diffColor (f p.1.1) (f p.1.2) ≠ diffColor (f q.1.1) (f q.1.2)
  rcases shift_adj.1 hpq with h | h
  · rw [h] at e1 ⊢
    exact diffColor_ne e1 e2
  · rw [← h] at e1 ⊢
    exact (diffColor_ne e2 e1).symm

end Shift

/- ## Transport along equivalences -/

section Transport

/-- All subgraphs on at most `ℵ₁` vertices are countably chromatic. -/
def SmallCardCC {V : Type u} (H : SimpleGraph V) : Prop :=
  ∀ X : Set V, #X ≤ ℵ₁ → ColorableOn H X ℕ

/-- `χ(G) > ℵ₁`, i.e. `χ(G) = ℵ₂` for a graph on `ℵ₂` vertices. -/
def ChiAleph2 {V : Type u} (G : SimpleGraph V) : Prop :=
  ∀ α : Type u, #α ≤ ℵ₁ → IsEmpty (G.Coloring α)

/-- `χ(G) = ℵ₁`. -/
def ChiAleph1 {V : Type u} (G : SimpleGraph V) : Prop :=
  (∃ α : Type u, #α ≤ ℵ₁ ∧ Nonempty (G.Coloring α)) ∧ IsEmpty (G.Coloring ℕ)

theorem smallCard_comap {V V' : Type u} (e : V ≃ V') {G : SimpleGraph V'}
    (hG : SmallCardCC G) : SmallCardCC (G.comap e) := by
  intro X hX
  obtain ⟨c, hc⟩ := hG (e '' X) (mk_image_le.trans hX)
  exact ⟨c ∘ e, fun x hx y hy hxy => hc _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy⟩

def coloringComap {V V' α : Type*} (f : V → V') {G : SimpleGraph V'} (c : G.Coloring α) :
    (G.comap f).Coloring α :=
  Coloring.mk (c ∘ f) (fun h => c.valid h)

def coloringOfComap {V V' α : Type*} (e : V ≃ V') {G : SimpleGraph V'}
    (c : (G.comap e).Coloring α) : G.Coloring α :=
  Coloring.mk (c ∘ e.symm) (fun {x y} h => c.valid (by simpa [comap_adj] using h))

/-- Lift the colours of a colouring to a higher universe. -/
def coloringULift {V α : Type*} {G : SimpleGraph V} (c : G.Coloring α) :
    G.Coloring (ULift.{u} α) :=
  Coloring.mk (fun v => ULift.up (c v)) (fun h e => c.valid h (congrArg ULift.down e))

/-- Lower the colours of a colouring from a higher universe. -/
def coloringDown {V α : Type*} {G : SimpleGraph V} (c : G.Coloring (ULift.{u} α)) :
    G.Coloring α :=
  Coloring.mk (fun v => (c v).down) (fun h e => c.valid h (ULift.ext _ _ e))

end Transport

/- ## The well-order `ω₂` -/

section Omega2

/-- The ordinal `ω₂` as a well-ordered type. -/
abbrev W : Type u := (ℵ_ 2 : Cardinal.{u}).ord.ToType

theorem mk_W : #W.{u} = ℵ_ 2 := mk_ord_toType _

theorem aleph2_eq_succ : (ℵ_ 2 : Cardinal.{u}) = Order.succ ℵ₁ := by
  rw [succ_aleph, one_add_one_eq_two]

theorem aleph1_lt_aleph2 : (ℵ₁ : Cardinal.{u}) < ℵ_ 2 := by
  rw [aleph2_eq_succ]; exact Order.lt_succ _

theorem le_aleph1_of_lt_aleph2 {c : Cardinal.{u}} (h : c < ℵ_ 2) : c ≤ ℵ₁ := by
  rw [aleph2_eq_succ] at h; exact Order.lt_succ_iff.1 h

theorem mk_Iio_W (x : W.{u}) : #(Iio x) ≤ ℵ₁ :=
  le_aleph1_of_lt_aleph2 (by simpa [mk_W] using mk_Iio_lt x (by rw [mk_W, type_toType]))

theorem mk_Iic_W (x : W.{u}) : #(Iic x) ≤ ℵ₁ := by
  rw [← Iio_insert]
  exact mk_insert_le.trans
    ((add_le_add (mk_Iio_W x) le_rfl).trans (add_one_eq (aleph0_le_aleph 1)).le)

theorem mk_ulift_nat_le_aleph1 : #(ULift.{u} ℕ) ≤ ℵ₁ := by
  rw [mk_uLift, mk_nat, lift_aleph0]; exact aleph0_le_aleph 1

/-- Regularity of `ω₂`: at most `ℵ₁` elements are bounded. -/
theorem exists_gt_of_small {J : Type u} (f : J → W.{u}) (hJ : #J ≤ ℵ₁) :
    ∃ u, ∀ j, f j < u := by
  by_contra h
  push Not at h
  have hsub : (univ : Set W) ⊆ ⋃ j, Iic (f j) := fun u _ => by
    obtain ⟨j, hj⟩ := h u
    exact mem_iUnion.2 ⟨j, hj⟩
  have h1 : #W.{u} ≤ ℵ₁ := by
    calc #W.{u} = #(univ : Set W) := mk_univ.symm
      _ ≤ #(⋃ j, Iic (f j)) := mk_le_mk_of_subset hsub
      _ ≤ #J * ⨆ j, #(Iic (f j)) := mk_iUnion_le _
      _ ≤ ℵ₁ * ℵ₁ := mul_le_mul' hJ (ciSup_le' fun j => mk_Iic_W (f j))
      _ = ℵ₁ := mul_eq_self (aleph0_le_aleph 1)
  rw [mk_W] at h1
  exact absurd h1 (not_le.2 aleph1_lt_aleph2)

/-- Every colouring of `ω₂` with at most `ℵ₁` colours has an unbounded colour class. -/
theorem exists_unbounded_fiber {α : Type u} (hα : #α ≤ ℵ₁) (d : W.{u} → α) :
    ∃ a, ∀ x, ∃ y, x ≤ y ∧ d y = a := by
  by_contra h
  push Not at h
  choose x hx using h
  obtain ⟨u, hu⟩ := exists_gt_of_small x hα
  exact hx (d u) u (hu (d u)).le rfl

/-- Closure points of any `β : ω₂ → ω₂` are unbounded. -/
theorem exists_closure_point (β : W.{u} → W.{u}) (a : W.{u}) :
    ∃ δ, a < δ ∧ ∀ ζ < δ, β ζ ≤ δ := by
  have hstep : ∀ x : W.{u}, ∃ y, x < y ∧ ∀ ζ < x, β ζ < y := by
    intro x
    obtain ⟨u, hu⟩ := exists_gt_of_small (J := Option (Iio x))
      (fun o => o.elim x (fun z => β z.1)) (by
        rw [mk_option]
        exact (add_le_add (mk_Iio_W x) le_rfl).trans (add_one_eq (aleph0_le_aleph 1)).le)
    exact ⟨u, hu none, fun ζ hζ => hu (some ⟨ζ, hζ⟩)⟩
  choose g hg1 hg2 using hstep
  let s : ℕ → W.{u} := fun n => g^[n] a
  obtain ⟨u, hu⟩ := exists_gt_of_small (fun n : ULift.{u} ℕ => s n.down) mk_ulift_nat_le_aleph1
  let U : Set W.{u} := {u | ∀ n, s n < u}
  have hUne : U.Nonempty := ⟨u, fun n => hu ⟨n⟩⟩
  have hsucc : ∀ n, s (n + 1) = g (s n) := fun n => Function.iterate_succ_apply' g n a
  refine ⟨WellFounded.min wellFounded_lt U hUne, (WellFounded.min_mem _ U hUne) 0, ?_⟩
  intro ζ hζ
  have hζU : ζ ∉ U := fun hmem => WellFounded.not_lt_min wellFounded_lt U hmem hζ
  simp only [U, mem_ofPred_eq, not_forall, not_lt] at hζU
  obtain ⟨n, hn⟩ := hζU
  have h1 : ζ < s (n + 1) := by rw [hsucc]; exact lt_of_le_of_lt hn (hg1 _)
  have h2 : β ζ < s (n + 1 + 1) := by rw [hsucc]; exact hg2 _ ζ h1
  exact (h2.trans ((WellFounded.min_mem _ U hUne) (n + 1 + 1))).le

/-- An unbounded subset of `ω₂` has order type `ω₂`. -/
theorem exists_embedding_of_unbounded (U : Set W.{u}) (hU : ∀ x, ∃ u ∈ U, x ≤ u) :
    Nonempty (W.{u} ↪o U) := by
  have hcard : ℵ_ 2 ≤ #U := by
    by_contra h
    push Not at h
    obtain ⟨v, hv⟩ := exists_gt_of_small (J := U) Subtype.val (le_aleph1_of_lt_aleph2 h)
    obtain ⟨u, hu, hvu⟩ := hU v
    exact absurd (hv ⟨u, hu⟩) (not_lt.2 hvu)
  have htype : typeLT W.{u} ≤ typeLT U := by
    rw [type_toType]
    calc (ℵ_ 2 : Cardinal.{u}).ord ≤ (#U).ord := ord_le_ord.2 hcard
      _ = (typeLT U).card.ord := by rw [card_type]
      _ ≤ typeLT U := ord_card_le _
  obtain ⟨f⟩ := type_le_iff'.1 htype
  exact ⟨OrderEmbedding.ofStrictMono f (fun a b h => f.map_rel_iff.2 h)⟩

/-- `W ×ₗ W` has order type `ω₂²`: it is (a copy of) the ordinal `ω₂²`. -/
theorem typeLT_lex : typeLT (W.{u} ×ₗ W.{u}) = ω_ 2 ^ 2 := by
  have : typeLT (W.{u} ×ₗ W.{u}) = (typeLT W.{u}) * (typeLT W.{u}) :=
    type_prod_lex (· < ·) (· < ·)
  rw [this, type_toType, ord_aleph, sq]

/-- If a set of order type `< ω₂²` is given, only boundedly many rows meet it unboundedly. -/
theorem rows_bounded (X : Set (W.{u} ×ₗ W.{u})) (hX : typeLT X < typeLT (W.{u} ×ₗ W.{u})) :
    ∃ ξ₀ : W.{u}, ∀ ξ, (∀ x, ∃ η, x ≤ η ∧ toLex (ξ, η) ∈ X) → ξ < ξ₀ := by
  by_contra hcon
  push Not at hcon
  let F : Set W.{u} := {ξ | ∀ x, ∃ η, x ≤ η ∧ toLex (ξ, η) ∈ X}
  obtain ⟨eF⟩ := exists_embedding_of_unbounded F (fun x => by
    obtain ⟨ξ, hξ, hx⟩ := hcon x
    exact ⟨ξ, hξ, hx⟩)
  have hrow : ∀ ξ : F, Nonempty (W.{u} ↪o {η : W.{u} | toLex (ξ.1, η) ∈ X}) := fun ξ =>
    exists_embedding_of_unbounded _ (fun x => by
      obtain ⟨η, h1, h2⟩ := ξ.2 x
      exact ⟨η, h2, h1⟩)
  let eR : ∀ ξ : F, W.{u} ↪o {η : W.{u} | toLex (ξ.1, η) ∈ X} :=
    fun ξ => Classical.choice (hrow ξ)
  let φ : W.{u} → W.{u} → X := fun i j => ⟨toLex ((eF i).1, (eR (eF i) j).1), (eR (eF i) j).2⟩
  have hφ : ∀ i j i' j', (i < i' ∨ i = i' ∧ j < j') → φ i j < φ i' j' := by
    intro i j i' j' h
    show toLex ((eF i).1, (eR (eF i) j).1) < toLex ((eF i').1, (eR (eF i') j').1)
    rw [Prod.Lex.toLex_lt_toLex]
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl (eF.strictMono h)
    · exact Or.inr ⟨rfl, (eR (eF i)).strictMono h⟩
  let Φ : W.{u} ×ₗ W.{u} → X := fun p => φ (ofLex p).1 (ofLex p).2
  have hΦ : StrictMono Φ := by
    intro p q hpq
    exact hφ _ _ _ _ (Prod.Lex.lt_iff.1 hpq)
  have hle : typeLT (W.{u} ×ₗ W.{u}) ≤ typeLT X :=
    type_le_iff'.2 ⟨(OrderEmbedding.ofStrictMono Φ hΦ).ltEmbedding⟩
  exact absurd hX (not_lt.2 hle)

theorem typeLT_W_le_lex : typeLT W.{u} ≤ typeLT (W.{u} ×ₗ W.{u}) :=
  type_le_iff'.2 ⟨(OrderEmbedding.ofStrictMono (fun i : W.{u} => toLex (i, i))
    (fun _ _ h => Prod.Lex.toLex_lt_toLex.2 (Or.inl h))).ltEmbedding⟩

theorem equiv_lex : Nonempty (W.{u} ≃ W.{u} ×ₗ W.{u}) := by
  apply Cardinal.eq.1
  rw [← mk_congr (toLex : W.{u} × W.{u} ≃ W.{u} ×ₗ W.{u}), mk_prod, Cardinal.lift_id, mk_W,
    mul_eq_self (aleph0_le_aleph 2)]

theorem mk_lex : #(W.{u} ×ₗ W.{u}) = ℵ_ 2 := by
  obtain ⟨e⟩ := equiv_lex.{u}
  rw [← mk_congr e, mk_W]

end Omega2

/- ## The reduction -/

/-- Every subgraph of `G` on a vertex set of order type `< ω₂²` is countably chromatic. -/
def SmallTypeCC (G : SimpleGraph (W.{u} ×ₗ W.{u})) : Prop :=
  ∀ X : Set (W.{u} ×ₗ W.{u}), typeLT X < ω_ 2 ^ 2 → ColorableOn G X ℕ

/-- The graph on `ω₂²` built from a graph `H` on `ω₂`. -/
def bigGraph (H : SimpleGraph W.{u}) : SimpleGraph (W.{u} ×ₗ W.{u}) := (blowup H).comap ofLex

theorem bigGraph_smallType (H : SimpleGraph W.{u}) (hH : SmallCardCC H) :
    SmallTypeCC (bigGraph H) := by
  intro X hX
  rw [← typeLT_lex] at hX
  obtain ⟨ξ₀, hξ₀⟩ := rows_bounded X hX
  have hb : ∀ ξ : W.{u}, ∃ b : W.{u}, ∀ η, ξ₀ ≤ ξ → b ≤ η → toLex (ξ, η) ∉ X := by
    intro ξ
    by_cases hF : ∀ x, ∃ η, x ≤ η ∧ toLex (ξ, η) ∈ X
    · exact ⟨ξ, fun _ h => absurd (hξ₀ ξ hF) (not_lt.2 h)⟩
    · push Not at hF
      obtain ⟨b, hb⟩ := hF
      exact ⟨b, fun η _ hη hmem => hb η hη hmem⟩
  choose β hβ using hb
  have hβ' : ∀ p ∈ ofLex '' X, ξ₀ ≤ p.1 → p.2 < β p.1 := by
    rintro _ ⟨q, hq, rfl⟩ h
    by_contra hlt
    exact hβ _ _ h (not_lt.1 hlt) (by simpa using hq)
  have hinit : ∀ a : W.{u}, ∃ c : W.{u} → ℕ,
      ∀ ξ ξ', ξ < a → ξ' < a → H.Adj ξ ξ' → c ξ ≠ c ξ' := by
    intro a
    obtain ⟨c, hc⟩ := hH (Iio a) (mk_Iio_W a)
    exact ⟨c, fun ξ ξ' h1 h2 hadj => hc ξ h1 ξ' h2 hadj⟩
  obtain ⟨c₀, hc₀⟩ := hinit ξ₀
  obtain ⟨c₁, hc₁⟩ := Hbeta_colorable hinit β (exists_closure_point β)
  obtain ⟨c, hc⟩ := (blowup_small_core (ofLex '' X) ξ₀ β hβ' c₀ hc₀ c₁ hc₁).toNat
  exact ⟨fun p => c (ofLex p), fun x hx y hy hxy => hc _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy⟩

theorem smallCard_of_smallType {G : SimpleGraph (W.{u} ×ₗ W.{u})} (hG : SmallTypeCC G) :
    SmallCardCC G := by
  intro X hX
  apply hG X
  rw [← typeLT_lex]
  calc typeLT X < (ℵ_ 2 : Cardinal.{u}).ord :=
        lt_ord.2 (by rw [card_type]; exact lt_of_le_of_lt hX aleph1_lt_aleph2)
    _ = typeLT W.{u} := (type_toType _).symm
    _ ≤ typeLT (W.{u} ×ₗ W.{u}) := typeLT_W_le_lex

theorem bigGraph_lower {H : SimpleGraph W.{u}} {α : Type u} (hα : #α ≤ ℵ₁)
    (c : (bigGraph H).Coloring α) : Nonempty (H.Coloring α) :=
  blowup_lower (exists_unbounded_fiber hα) (coloringOfComap ofLex c)

def bigGraphColoring {H : SimpleGraph W.{u}} {α : Type u} (c : H.Coloring α) :
    (bigGraph H).Coloring α :=
  coloringComap ofLex (blowupColoring c)

/-- The `ℵ₂` version is equivalent to the existence of an `(ℵ₀, ℵ₂)`-chromatic graph of size
`ℵ₂`. -/
theorem erdos919_aleph2_iff :
    (∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ ChiAleph2 G) ↔
      ∃ H : SimpleGraph W.{u}, SmallCardCC H ∧ ChiAleph2 H := by
  constructor
  · rintro ⟨G, hG, hχ⟩
    obtain ⟨e⟩ := equiv_lex.{u}
    exact ⟨G.comap e, smallCard_comap e (smallCard_of_smallType hG),
      fun α hα => ⟨fun c => (hχ α hα).false (coloringOfComap e c)⟩⟩
  · rintro ⟨H, hH, hχ⟩
    refine ⟨bigGraph H, bigGraph_smallType H hH, fun α hα => ⟨fun c => ?_⟩⟩
    obtain ⟨d⟩ := bigGraph_lower hα c
    exact (hχ α hα).false d

/-- The countable ordinals `ω₁` as a type. -/
abbrev T1 : Type u := (ℵ₁ : Cardinal.{u}).ord.ToType

theorem mk_T1 : #T1.{u} = ℵ₁ := mk_ord_toType _

theorem T1_not_inj (d : T1.{u} → ULift.{u} ℕ) : ∃ t₁ t₂, t₁ ≠ t₂ ∧ d t₁ = d t₂ := by
  by_contra h
  push Not at h
  have hinj : Function.Injective d := fun a b hab => by
    by_contra hne
    exact h a b hne hab
  have := mk_le_of_injective hinj
  rw [mk_T1, mk_uLift, mk_nat, lift_aleph0] at this
  exact absurd this (not_le.2 aleph0_lt_aleph_one)

/-- The `ℵ₁` version is equivalent to `ℵ₂` failing countable chromatic compactness. -/
theorem erdos919_aleph1_iff :
    (∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ ChiAleph1 G) ↔
      ∃ H : SimpleGraph W.{u}, SmallCardCC H ∧ IsEmpty (H.Coloring ℕ) := by
  constructor
  · rintro ⟨G, hG, -, hχ⟩
    obtain ⟨e⟩ := equiv_lex.{u}
    exact ⟨G.comap e, smallCard_comap e (smallCard_of_smallType hG),
      ⟨fun c => hχ.false (coloringOfComap e c)⟩⟩
  · rintro ⟨H, hH, hχ⟩
    let K := tensorTop H T1.{u}
    have hK : SmallCardCC K := by
      intro X hX
      exact tensorTop_colorableOn H X (hH _ (mk_image_le.trans hX))
    have hWT : Nonempty (W.{u} ≃ W.{u} × T1.{u}) := by
      apply Cardinal.eq.1
      rw [mk_prod, Cardinal.lift_id, Cardinal.lift_id, mk_W, mk_T1,
        mul_eq_left (aleph0_le_aleph 2) aleph1_lt_aleph2.le (aleph_pos 1).ne']
    obtain ⟨e⟩ := hWT
    let H' := K.comap e
    refine ⟨bigGraph H', bigGraph_smallType H' (smallCard_comap e hK), ?_, ?_⟩
    · exact ⟨T1, mk_T1.le, ⟨bigGraphColoring (coloringComap e (tensorTopColoringT H T1))⟩⟩
    · refine ⟨fun c => ?_⟩
      obtain ⟨d⟩ := bigGraph_lower mk_ulift_nat_le_aleph1 (coloringULift c)
      obtain ⟨d'⟩ := tensorTop_lower H T1_not_inj (coloringOfComap e d)
      exact hχ.false (coloringDown d')

/-- Under CH the `ℵ₁` version has a positive answer, via the Erdős-Hajnal shift graph. -/
theorem erdos919_aleph1_of_CH (hCH : (𝔠 : Cardinal.{0}) = ℵ₁) :
    ∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ ChiAleph1 G := by
  apply erdos919_aleph1_iff.2
  have hV : Nonempty (W.{u} ≃ {p : W.{u} × W.{u} // p.1 < p.2}) := by
    apply Cardinal.eq.1
    apply le_antisymm
    · have hnx : ∀ i : W.{u}, ∃ j, i < j := fun i => by
        obtain ⟨u, hu⟩ := exists_gt_of_small (J := PUnit) (fun _ => i)
          (by rw [mk_punit]; exact one_le_aleph0.trans (aleph0_le_aleph 1))
        exact ⟨u, hu PUnit.unit⟩
      choose nx hnx using hnx
      exact mk_le_of_injective
        (f := fun i => (⟨(i, nx i), hnx i⟩ : {p : W.{u} × W.{u} // p.1 < p.2}))
        (fun a b h => by simpa using congrArg (fun p : {p : W.{u} × W.{u} // p.1 < p.2} => p.1.1) h)
    · calc #{p : W.{u} × W.{u} // p.1 < p.2} ≤ #(W.{u} × W.{u}) := mk_subtype_le _
        _ = #W.{u} := by rw [mk_prod, Cardinal.lift_id, mk_W, mul_eq_self (aleph0_le_aleph 2)]
  obtain ⟨e⟩ := hV
  have hcont : #(ℕ → Bool) = 𝔠 := by rw [← power_def, mk_bool, mk_nat, two_power_aleph0]
  refine ⟨(shift W).comap e, smallCard_comap e ?_, ⟨fun c => ?_⟩⟩
  · intro X hX
    let S : Set W.{u} := (fun p : {p : W.{u} × W.{u} // p.1 < p.2} => p.1.1) '' X ∪
      (fun p : {p : W.{u} × W.{u} // p.1 < p.2} => p.1.2) '' X
    have hS : #S ≤ ℵ₁ :=
      calc #S ≤ #((fun p : {p : W.{u} × W.{u} // p.1 < p.2} => p.1.1) '' X) +
            #((fun p : {p : W.{u} × W.{u} // p.1 < p.2} => p.1.2) '' X) := mk_union_le _ _
        _ ≤ ℵ₁ + ℵ₁ := add_le_add (mk_image_le.trans hX) (mk_image_le.trans hX)
        _ = ℵ₁ := add_eq_self (aleph0_le_aleph 1)
    have hS' : Cardinal.lift.{0} #S ≤ Cardinal.lift.{u} #(ℕ → Bool) := by
      rw [Cardinal.lift_uzero, hcont, lift_continuum]
      exact hS.trans aleph_one_le_continuum
    obtain ⟨emb⟩ := lift_mk_le'.1 hS'
    classical
    let f : W.{u} → ℕ → Bool := fun x => if h : x ∈ S then emb ⟨x, h⟩ else fun _ => false
    have hf : Set.InjOn f S := by
      intro x hx y hy hxy
      simp only [f, hx, hy, dite_true] at hxy
      exact congrArg Subtype.val (emb.injective hxy)
    exact ((shift_colorableOn S f hf).mono_set
      (fun p hp => ⟨Or.inl ⟨p, hp, rfl⟩, Or.inr ⟨p, hp, rfl⟩⟩)).toNat
  · have hinj := shift_lower (coloringOfComap e c)
    have h1 := lift_mk_le_lift_mk_of_injective hinj
    rw [Cardinal.lift_uzero, mk_set, mk_nat, two_power_aleph0, hCH, mk_W] at h1
    simp only [lift_aleph, Ordinal.lift_one] at h1
    exact absurd h1 (not_le.2 aleph1_lt_aleph2)

/- ## Chromatic cardinals -/

section Chromatic

theorem chromaticCardinal_le_iff {V : Type u} (G : SimpleGraph V) (κ : Cardinal.{u}) :
    G.chromaticCardinal ≤ κ ↔ ∃ C : Type u, #C ≤ κ ∧ Nonempty (G.Coloring C) := by
  have hne : Set.Nonempty
      {κ : Cardinal.{u} | ∃ (C : Type u) (_ : #C = κ), Nonempty (G.Coloring C)} :=
    ⟨#V, show ∃ (C : Type u) (_ : #C = #V), Nonempty (G.Coloring C) from
      ⟨V, rfl, ⟨G.selfColoring⟩⟩⟩
  unfold SimpleGraph.chromaticCardinal
  constructor
  · intro h
    obtain ⟨C, hC, hc⟩ := csInf_mem hne
    exact ⟨C, hC.trans_le h, hc⟩
  · rintro ⟨C, hC, hc⟩
    refine le_trans (csInf_le' ?_) hC
    exact ⟨C, rfl, hc⟩

theorem chromaticCardinal_le_mk {V : Type u} (G : SimpleGraph V) : G.chromaticCardinal ≤ #V :=
  (chromaticCardinal_le_iff G _).2 ⟨V, le_rfl, ⟨G.selfColoring⟩⟩

theorem chromaticCardinal_le_aleph0_iff {V : Type u} (G : SimpleGraph V) :
    G.chromaticCardinal ≤ ℵ₀ ↔ Nonempty (G.Coloring ℕ) := by
  rw [chromaticCardinal_le_iff]
  constructor
  · rintro ⟨C, hC, ⟨c⟩⟩
    have : Countable C := mk_le_aleph0_iff.1 hC
    obtain ⟨f, hf⟩ := (countable_iff_exists_injective C).1 this
    exact ⟨Coloring.mk (f ∘ c) (fun h e => c.valid h (hf e))⟩
  · rintro ⟨c⟩
    exact ⟨ULift ℕ, by rw [mk_uLift, mk_nat, lift_aleph0], ⟨coloringULift c⟩⟩

theorem induce_le_aleph0_iff {V : Type u} (G : SimpleGraph V) (X : Set V) :
    (G.induce X).chromaticCardinal ≤ ℵ₀ ↔ ColorableOn G X ℕ := by
  rw [chromaticCardinal_le_aleph0_iff, colorableOn_iff_induce]

theorem aleph0_lt_chromaticCardinal_iff {V : Type u} (G : SimpleGraph V) :
    ℵ₀ < G.chromaticCardinal ↔ IsEmpty (G.Coloring ℕ) := by
  rw [← not_le, chromaticCardinal_le_aleph0_iff, not_nonempty_iff]

theorem chromaticCardinal_eq_aleph2_iff {V : Type u} (G : SimpleGraph V) (hV : #V = ℵ_ 2) :
    G.chromaticCardinal = ℵ_ 2 ↔ ChiAleph2 G := by
  have hle : G.chromaticCardinal ≤ Order.succ ℵ₁ := by
    rw [← aleph2_eq_succ, ← hV]; exact chromaticCardinal_le_mk G
  have key : G.chromaticCardinal ≤ ℵ₁ ↔ ¬ ChiAleph2 G := by
    rw [chromaticCardinal_le_iff]
    simp only [ChiAleph2, not_forall, not_isEmpty_iff, exists_prop]
  constructor
  · intro h
    by_contra hn
    have := key.2 hn
    rw [h] at this
    exact absurd this (not_le.2 aleph1_lt_aleph2)
  · intro h
    rcases Order.le_succ_iff_eq_or_le.1 hle with h1 | h1
    · rw [h1, aleph2_eq_succ]
    · exact absurd h (key.1 h1)

theorem chromaticCardinal_eq_aleph1_iff {V : Type u} (G : SimpleGraph V) :
    G.chromaticCardinal = ℵ₁ ↔ ChiAleph1 G := by
  unfold ChiAleph1
  rw [← chromaticCardinal_le_iff, ← aleph0_lt_chromaticCardinal_iff]
  constructor
  · intro h
    rw [h]
    exact ⟨le_rfl, aleph0_lt_aleph_one⟩
  · rintro ⟨h1, h2⟩
    apply le_antisymm h1
    rw [← succ_aleph0]
    exact Order.succ_le_of_lt h2

theorem chromaticCardinal_comap_equiv {A B : Type u} (e : A ≃ B) (G : SimpleGraph B) :
    (G.comap e).chromaticCardinal = G.chromaticCardinal := by
  have h : ∀ κ, (G.comap e).chromaticCardinal ≤ κ ↔ G.chromaticCardinal ≤ κ := fun κ => by
    rw [chromaticCardinal_le_iff, chromaticCardinal_le_iff]
    exact ⟨fun ⟨C, hC, ⟨c⟩⟩ => ⟨C, hC, ⟨coloringOfComap e c⟩⟩,
      fun ⟨C, hC, ⟨c⟩⟩ => ⟨C, hC, ⟨coloringComap e c⟩⟩⟩
  exact le_antisymm ((h _).2 le_rfl) ((h _).1 le_rfl)

end Chromatic

/- ## The vertex type of the problem -/

section Vertices

/-- The vertex type `ω₂²` used in the problem statement. -/
abbrev V9 : Type u := (ω_ 2 ^ 2 : Ordinal.{u}).ToType

theorem typeLT_image_le {A B : Type u} [LinearOrder A] [WellFoundedLT A] [LinearOrder B]
    [WellFoundedLT B] (e : A ≃o B) (X : Set A) : typeLT (e '' X) ≤ typeLT X := by
  have hmem : ∀ y : e '' X, e.symm y.1 ∈ X := by
    rintro ⟨_, x, hx, rfl⟩
    simpa using hx
  exact type_le_iff'.2 ⟨(OrderEmbedding.ofStrictMono
    (fun y : e '' X => (⟨e.symm y.1, hmem y⟩ : X)) (fun _ _ h => e.symm.strictMono h)).ltEmbedding⟩

theorem typeLT_image {A B : Type u} [LinearOrder A] [WellFoundedLT A] [LinearOrder B]
    [WellFoundedLT B] (e : A ≃o B) (X : Set A) : typeLT (e '' X) = typeLT X := by
  refine le_antisymm (typeLT_image_le e X) ?_
  have := typeLT_image_le e.symm (e '' X)
  rwa [e.symm_image_image] at this

theorem smallType_comap {A B : Type u} [LinearOrder A] [WellFoundedLT A] [LinearOrder B]
    [WellFoundedLT B] (e : A ≃o B) {G : SimpleGraph B} {o : Ordinal.{u}}
    (h : ∀ X : Set B, typeLT X < o → ColorableOn G X ℕ) :
    ∀ Y : Set A, typeLT Y < o → ColorableOn (G.comap e) Y ℕ :=
  fun Y hY => ColorableOn.comap e (h _ (by rwa [typeLT_image]))

theorem typeLT_V9 : typeLT V9.{u} = typeLT (W.{u} ×ₗ W.{u}) := by
  rw [type_toType, typeLT_lex]

/-- `ω₂²` is order isomorphic to `ω₂ ×ₗ ω₂`. -/
def isoV9 : V9.{u} ≃o W.{u} ×ₗ W.{u} :=
  OrderIso.ofRelIsoLT (Classical.choice (type_eq.1 typeLT_V9))

/-- The property asked for in the problem, for a chromatic cardinal `κ`. -/
def Q (κ : Cardinal.{u}) : Prop :=
  ∃ G : SimpleGraph V9.{u}, G.chromaticCardinal = κ ∧
    ∀ X : Set V9.{u}, typeLT X < ω_ 2 ^ 2 → (G.induce X).chromaticCardinal ≤ ℵ₀

theorem Q_iff (κ : Cardinal.{u}) :
    Q κ ↔ ∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ G.chromaticCardinal = κ := by
  constructor
  · rintro ⟨G, hχ, hX⟩
    exact ⟨G.comap isoV9.symm,
      smallType_comap isoV9.symm (fun X hXo => (induce_le_aleph0_iff G X).1 (hX X hXo)),
      (chromaticCardinal_comap_equiv isoV9.symm.toEquiv G).trans hχ⟩
  · rintro ⟨G, hG, hχ⟩
    exact ⟨G.comap isoV9, (chromaticCardinal_comap_equiv isoV9.toEquiv G).trans hχ,
      fun X hXo => (induce_le_aleph0_iff _ X).2 (smallType_comap isoV9 hG X hXo)⟩

theorem Q_aleph2_iff :
    Q.{u} (ℵ_ 2) ↔ ∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ ChiAleph2 G := by
  rw [Q_iff]
  refine exists_congr fun G => ?_
  rw [chromaticCardinal_eq_aleph2_iff G mk_lex]

theorem Q_aleph1_iff :
    Q.{u} ℵ₁ ↔ ∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ ChiAleph1 G := by
  rw [Q_iff]
  refine exists_congr fun G => ?_
  rw [chromaticCardinal_eq_aleph1_iff G]

end Vertices

/- ## Graphs of size `ℵ₂` -/

section Size

theorem exists_superset_aleph1 {V : Type u} (hV : ℵ₁ ≤ #V) (X : Set V) (hX : #X ≤ ℵ₁) :
    ∃ Y : Set V, X ⊆ Y ∧ #Y = ℵ₁ := by
  obtain ⟨Z, hZ⟩ := le_mk_iff_exists_set.1 hV
  refine ⟨X ∪ Z, subset_union_left, le_antisymm ?_ ?_⟩
  · calc #(X ∪ Z : Set V) ≤ #X + #Z := mk_union_le _ _
      _ ≤ ℵ₁ + ℵ₁ := add_le_add hX hZ.le
      _ = ℵ₁ := add_eq_self (aleph0_le_aleph 1)
  · rw [← hZ]
    exact mk_le_mk_of_subset subset_union_right

theorem smallCard_iff {V : Type u} (hV : #V = ℵ_ 2) (G : SimpleGraph V) :
    SmallCardCC G ↔ ∀ (X : Set V) (_ : #X = ℵ₁), (G.induce X).chromaticCardinal ≤ ℵ₀ := by
  constructor
  · intro h X hX
    exact (induce_le_aleph0_iff G X).2 (h X hX.le)
  · intro h X hX
    obtain ⟨Y, hXY, hY⟩ := exists_superset_aleph1 (by rw [hV]; exact aleph1_lt_aleph2.le) X hX
    exact ((induce_le_aleph0_iff G Y).1 (h Y hY)).mono_set hXY

/-- Graphs of size `ℵ₂` can be moved to `W`. -/
theorem size_iff (P : ∀ {V : Type u}, SimpleGraph V → Prop)
    (hP : ∀ {A B : Type u} (e : A ≃ B) (G : SimpleGraph B), P (G.comap e) ↔ P G) :
    (∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ P G ∧
      ∀ (X : Set V) (_ : #X = ℵ₁), (G.induce X).chromaticCardinal ≤ ℵ₀) ↔
    ∃ H : SimpleGraph W.{u}, SmallCardCC H ∧ P H := by
  constructor
  · rintro ⟨V, G, hV, hPG, hX⟩
    obtain ⟨e⟩ := Cardinal.eq.1 (hV.trans mk_W.symm)
    exact ⟨G.comap e.symm, smallCard_comap e.symm ((smallCard_iff hV G).2 hX),
      (hP e.symm G).2 hPG⟩
  · rintro ⟨H, hH, hPH⟩
    exact ⟨W, H, mk_W, hPH, (smallCard_iff mk_W H).1 hH⟩

theorem e918_iff :
    (∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀) ↔
    ∃ H : SimpleGraph W.{u}, SmallCardCC H ∧ ChiAleph2 H := by
  rw [size_iff (fun G => G.chromaticCardinal = ℵ_ 2)
    (fun e G => by rw [chromaticCardinal_comap_equiv])]
  refine exists_congr fun H => ?_
  rw [chromaticCardinal_eq_aleph2_iff H mk_W]

theorem inc_iff :
    (∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ ℵ₀ < G.chromaticCardinal ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀) ↔
    ∃ H : SimpleGraph W.{u}, SmallCardCC H ∧ IsEmpty (H.Coloring ℕ) := by
  rw [size_iff (fun G => ℵ₀ < G.chromaticCardinal)
    (fun e G => by rw [chromaticCardinal_comap_equiv])]
  refine exists_congr fun H => ?_
  rw [aleph0_lt_chromaticCardinal_iff H]

/-- CH does not depend on the universe. -/
theorem continuum_eq_aleph1_zero.{v} (h : (𝔠 : Cardinal.{v}) = ℵ₁) :
    (𝔠 : Cardinal.{0}) = ℵ₁ := by
  have h' : Cardinal.lift.{v} (𝔠 : Cardinal.{0}) = Cardinal.lift.{v} (ℵ₁ : Cardinal.{0}) := by
    simpa using h
  exact Cardinal.lift_inj.1 h'

end Size

end

/- ## The statements of Problem 919 -/

/-- `erdos_919.variants.iff_erdos_918_i`: the `ℵ₂` version of Problem 919 is equivalent to
Problem 918(i). -/
theorem erdos_919.variants.iff_erdos_918_i :
    (∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ_ 2 ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀) ↔
    ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀ :=
  (Q_aleph2_iff.trans erdos919_aleph2_iff).trans e918_iff.symm

/-- `erdos_919.variants.aleph_1_iff`: the `ℵ₁` version of Problem 919 is equivalent to the
existence of a graph on `ℵ₂` vertices that is not countably chromatic although every subgraph
on `ℵ₁` vertices is. -/
theorem erdos_919.variants.aleph_1_iff :
    (∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ₁ ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀) ↔
    ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ ℵ₀ < G.chromaticCardinal ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀ :=
  (Q_aleph1_iff.trans erdos919_aleph1_iff).trans inc_iff.symm

/-- `erdos_919.variants.aleph_2_imp_aleph_1`: a positive answer to the `ℵ₂` version gives a
positive answer to the `ℵ₁` version. -/
theorem erdos_919.variants.aleph_2_imp_aleph_1 :
    (∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ_ 2 ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀) →
    ∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ₁ ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀ := by
  intro h
  obtain ⟨H, hH, hχ⟩ := erdos919_aleph2_iff.1 (Q_aleph2_iff.1 h)
  exact Q_aleph1_iff.2 (erdos919_aleph1_iff.2
    ⟨H, hH, ⟨fun c => (hχ _ mk_ulift_nat_le_aleph1).false (coloringULift c)⟩⟩)

/-- `erdos_919.variants.aleph_1_of_CH`: under the continuum hypothesis the `ℵ₁` version has a
positive answer. -/
theorem erdos_919.variants.aleph_1_of_CH (hCH : 𝔠 = ℵ₁) :
    ∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ₁ ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀ := by
  exact Q_aleph1_iff.2 (erdos919_aleph1_of_CH (continuum_eq_aleph1_zero hCH))

/-- The right-hand side of `erdos_919.variants.iff_erdos_918_i` is the statement of
`Erdos918.erdos_918.parts.i`. -/
example : (type_of% @Erdos918.erdos_918.parts.i.{u}) =
    (True ↔ ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀) :=
  rfl

end ErdosLean.Erdos919
