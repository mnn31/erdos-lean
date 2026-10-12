import FormalConjectures.ErdosProblems.«36»

/-!
# Erdős 36, variant `upper`: `limsup M(N)/N ≤ 0.380924`

The statement `Erdos36.erdos_36.variants.upper` asks for a constant `c < 0.380926853433087`
(Haugland's 2022 bound) with `limsup M(N)/N ≤ c`.  We prove it with `c = 0.380924`.

Construction.  Take the 95-step function `f` of AlphaEvolve (2025), whose continuous overlap
`max_x ∫ f(t) (1 - f(t + x)) dt` is `0.3809230…`.  Cut `{1, …, 2n}` into `K = 95` blocks of
length `L = ⌊2n / K⌋`; block `i` keeps the integers `t` with `t % p i < a i`, where
`a i / p i ≈ f i` and the moduli `p i` are distinct primes (or `1` for an empty block).
By the Chinese remainder theorem, inside any window of `p i * p j` consecutive integers the
pattern of block `i` and the shifted complement pattern of block `j` meet exactly
`a i * (p j - a j)` times, so the overlap between two blocks is governed by
`(a i / p i) (1 - a j / p j)`.  Inside a single block the pattern is periodic and the bound is
`min (a i) (p i - a i) / p i` instead.  A few elements are then moved to make the two halves
equal in size; each moved element changes every overlap count by at most one.

All the numerical work reduces to finitely many integer inequalities (checked by `decide`):
the diagonal sums of the matrix `T i j ≈ D² (a i / p i) (1 - a j / p j)` are at most `Wb`,
and `(2 Wb + D sig) / (K D²) < 0.380924`.
-/

open Filter Finset

set_option linter.constructorNameAsVariable false

open Erdos36

namespace ErdosLean.Erdos36

/- ## Certificate data -/

/-- Moduli of the blocks (distinct primes, or `1`). -/
def pL : List ℕ :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 100003, 100019, 100043, 100049, 100057, 100069, 1, 100103,
   100109, 100129, 100151, 100153, 100169, 100183, 100189, 100193, 100207, 100213, 100237,
   100267, 100271, 100279, 100291, 100297, 100313, 100333, 100343, 100357, 100361, 100363,
   100379, 100391, 100393, 100403, 100411, 100417, 100447, 100459, 100469, 100483, 100493,
   100501, 100511, 100517, 100519, 100523, 100537, 100547, 100549, 100559, 100591, 100609,
   100613, 100621, 100649, 100669, 100673, 100693, 100699, 100703, 100733, 100741, 100747,
   100769, 100787, 100799, 1, 100801, 100811, 100823, 100829, 100847, 100853, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1]

/-- Block `i` keeps `t` when `t % p i < a i`. -/
def aL : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50609, 63217, 67962, 88863, 88972, 67870, 0, 9486, 1441,
   42448, 59898, 80514, 68425, 31533, 40482, 86010, 79815, 59169, 41154, 27166, 61505, 71148,
   58226, 80592, 71750, 82535, 81121, 68597, 64805, 89265, 94697, 84483, 79763, 94574, 96618,
   96528, 99685, 96568, 96674, 94649, 79842, 84575, 94821, 89402, 64907, 68711, 81278, 82711,
   71919, 80803, 58400, 71382, 61714, 27262, 41323, 59438, 80186, 86439, 40688, 31696, 68811,
   80987, 60254, 42719, 1451, 9552, 0, 68366, 89643, 89550, 68496, 63740, 51039, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0]

/-- Upper bounds for `D * a i / p i`. -/
def uL : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 506074818, 632049911, 679327890, 888194785, 889213149,
   678232020, 0, 94762395, 14394311, 423933127, 598076904, 803910018, 683095569, 314754001,
   404056334, 858443205, 796501243, 590432380, 410566957, 270936600, 613387720, 709500494,
   580570540, 803533506, 715261233, 822610707, 808437061, 683529799, 645718955, 889421401,
   943394535, 841539581, 794507586, 941943966, 962225255, 961271498, 992413910, 961267781,
   962227155, 941940428, 794503100, 841533916, 943389281, 889421690, 645718720, 683535112,
   808438685, 822610322, 715263206, 803538222, 580568839, 709499151, 613379981, 270937479,
   410565431, 590430024, 796499558, 858441004, 404055651, 314747327, 683102857, 803913005,
   598072400, 423929979, 14396698, 94762845, 0, 678227399, 889218439, 888190195, 679328368,
   632046566, 506073196, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Upper bounds for `D * (p i - a i) / p i`. -/
def vL : List ℕ :=
  [1000000000, 1000000000, 1000000000, 1000000000, 1000000000, 1000000000, 1000000000,
   1000000000, 1000000000, 1000000000, 1000000000, 493925183, 367950090, 320672111, 111805216,
   110786852, 321767981, 1000000000, 905237606, 985605690, 576066874, 401923097, 196089983,
   316904432, 685246000, 595943667, 141556796, 203498758, 409567621, 589433044, 729063401,
   386612281, 290499507, 419429461, 196466495, 284738768, 177389294, 191562940, 316470202,
   354281046, 110578600, 56605466, 158460420, 205492415, 58056035, 37774746, 38728503, 7586091,
   38732220, 37772846, 58059573, 205496901, 158466085, 56610720, 110578311, 354281281, 316464889,
   191561316, 177389679, 284736795, 196461779, 419431162, 290500850, 386620020, 729062522,
   589434570, 409569977, 203500443, 141558997, 595944350, 685252674, 316897144, 196086996,
   401927601, 576070022, 985603303, 905237156, 1000000000, 321772602, 110781562, 111809806,
   320671633, 367953435, 493926805, 1000000000, 1000000000, 1000000000, 1000000000, 1000000000,
   1000000000, 1000000000, 1000000000, 1000000000, 1000000000, 1000000000]

/-- Upper bounds for `D * min (a i) (p i - a i) / p i`. -/
def mL : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 493925183, 367950090, 320672111, 111805216, 110786852,
   321767981, 0, 94762395, 14394311, 423933127, 401923097, 196089983, 316904432, 314754001,
   404056334, 141556796, 203498758, 409567621, 410566957, 270936600, 386612281, 290499507,
   419429461, 196466495, 284738768, 177389294, 191562940, 316470202, 354281046, 110578600,
   56605466, 158460420, 205492415, 58056035, 37774746, 38728503, 7586091, 38732220, 37772846,
   58059573, 205496901, 158466085, 56610720, 110578311, 354281281, 316464889, 191561316,
   177389679, 284736795, 196461779, 419431162, 290500850, 386620020, 270937479, 410565431,
   409569977, 203500443, 141558997, 404055651, 314747327, 316897144, 196086996, 401927601,
   423929979, 14396698, 94762845, 0, 321772602, 110781562, 111809806, 320671633, 367953435,
   493926805, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Bound for every diagonal sum of `T`. -/
def Wb : ℕ := 18093872078032173895

/-- Slack in the density of the construction. -/
def sig : ℕ := 5394

/-- Number of blocks.  Irreducible, so that the elaborator never expands `range K`. -/
@[irreducible] def K : ℕ := 95

/-- Common denominator of the fixed-point bounds `u`, `v`, `m`. -/
def D : ℕ := 1000000000

def p (i : ℕ) : ℕ := pL.getD i 1
def a (i : ℕ) : ℕ := aL.getD i 0
def u (i : ℕ) : ℕ := uL.getD i 0
def v (i : ℕ) : ℕ := vL.getD i 0
def m (i : ℕ) : ℕ := mL.getD i 0

/-- `T i j / D²` bounds the density of overlaps between block `i` of `A` and block `j` of `B`. -/
def T (i j : ℕ) : ℕ := if i = j then D * m i else u i * v j

/-- Number of hits in one period. -/
def Cc (i j : ℕ) : ℕ := if i = j then min (a i) (p i - a i) else a i * (p j - a j)

/-- The period. -/
def Pp (i j : ℕ) : ℕ := if i = j then p i else p i * p j

/- ### The finite checks -/

lemma p_pos : ∀ i < K, 0 < p i := by decide +kernel

lemma a_le : ∀ i < K, a i ≤ p i := by decide +kernel

lemma p_coprime : ∀ i < K, ∀ j < K, i ≠ j → Nat.Coprime (p i) (p j) := by decide +kernel

lemma hu : ∀ i < K, D * a i ≤ u i * p i := by decide +kernel

lemma hv : ∀ i < K, D * (p i - a i) ≤ v i * p i := by decide +kernel

lemma hm : ∀ i < K, D * min (a i) (p i - a i) ≤ m i * p i := by decide +kernel

/-- Sum of the `T i j` with `i - j = e`, written as a single sum over `i`. -/
def wrow (e : ℤ) (i : ℕ) : ℕ :=
  if 0 ≤ (i : ℤ) - e ∧ (i : ℤ) - e < K then T i ((i : ℤ) - e).toNat else 0

/-- `∑ i < n, wrow e i` as a plain recursion, for the kernel. -/
def wdiag (e : ℤ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => wdiag e n + wrow e n

lemma wdiag_check : ∀ e < 2 * K - 1, wdiag ((e : ℤ) - (K - 1)) K ≤ Wb := by decide +kernel

lemma sum_u : 2 * ∑ i ∈ range K, u i ≤ D * K + sig := by decide +kernel

lemma sum_v : 2 * ∑ i ∈ range K, v i ≤ D * K + sig := by decide +kernel

/-- The final numerical gap: `(2 Wb + D sig) / (K D²) < 0.380924`. -/
lemma gap : 1000000 * (2 * Wb + D * sig) < 380924 * (K * D ^ 2) := by decide +kernel

/- ### Diagonal sums -/

/-- The sum of `T i j` over the diagonal `i - j = e`. -/
def Wd (e : ℤ) : ℕ := ∑ i ∈ range K, ∑ j ∈ range K, if (i : ℤ) - j = e then T i j else 0

lemma inner_sum (e : ℤ) (i : ℕ) :
    (∑ j ∈ range K, if (i : ℤ) - j = e then T i j else 0) = wrow e i := by
  unfold wrow
  split_ifs with h
  · rw [sum_eq_single ((i : ℤ) - e).toNat]
    · rw [if_pos (by omega)]
    · intro j _ hj
      rw [if_neg (by omega)]
    · intro hj
      exact absurd (Finset.mem_range.mpr (by omega)) hj
  · refine sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [if_neg (by omega)]

lemma wdiag_eq (e : ℤ) (n : ℕ) : wdiag e n = ∑ i ∈ range n, wrow e i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wdiag, ih, sum_range_succ]

lemma Wd_le (e : ℤ) : Wd e ≤ Wb := by
  have h : Wd e = wdiag e K := by
    rw [wdiag_eq, Wd]
    exact sum_congr rfl fun i _ => inner_sum e i
  rw [h]
  by_cases he : -(K : ℤ) < e ∧ e < K
  · have := wdiag_check (e + (K - 1)).toNat (by unfold K at he ⊢; omega)
    rwa [show (((e + (K - 1)).toNat : ℕ) : ℤ) - (K - 1) = e by unfold K at he ⊢; omega] at this
  · rw [wdiag_eq, sum_eq_zero fun i hi => ?_]
    · exact Nat.zero_le _
    · rw [Finset.mem_range] at hi
      unfold wrow
      rw [if_neg (by omega)]

/- ## Counting in windows -/

/-- On `p` consecutive integers, `t ↦ (t - k) % p` is injective. -/
lemma card_window_mod (p : ℕ) (k x : ℤ) (S : Finset ℤ) :
    ((Ico x (x + p)).filter fun t => (t - k) % p ∈ S).card ≤ S.card := by
  refine card_le_card_of_injOn (fun t => (t - k) % p) (fun t ht => (Finset.mem_filter.mp ht).2) ?_
  intro t ht t' ht' h
  simp only [coe_filter, Finset.mem_Ico, Set.mem_ofPred_eq] at ht ht'
  have h1 : (p : ℤ) ∣ (t' - k) - (t - k) := Int.ModEq.dvd h
  rw [show (t' - k) - (t - k) = t' - t by ring] at h1
  have h2 := Int.eq_zero_of_abs_lt_dvd h1 (by rw [abs_lt]; constructor <;> omega)
  omega

/-- On `p * q` consecutive integers (`p`, `q` coprime), `t ↦ (t % p, (t - k) % q)` is
injective: the Chinese remainder theorem. -/
lemma card_window_pair (p q : ℕ) (hpq : Nat.Coprime p q) (k x : ℤ) (S S' : Finset ℤ) :
    ((Ico x (x + (p * q : ℕ))).filter fun t : ℤ => t % (p : ℤ) ∈ S ∧ (t - k) % (q : ℤ) ∈ S').card ≤
      S.card * S'.card := by
  rw [← card_product]
  refine card_le_card_of_injOn (fun t : ℤ => (t % (p : ℤ), (t - k) % (q : ℤ))) (fun t ht => ?_) ?_
  · obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_product.mpr ⟨h1, h2⟩
  · intro t ht t' ht' h
    simp only [coe_filter, Finset.mem_Ico, Set.mem_ofPred_eq] at ht ht'
    simp only [Prod.mk.injEq] at h
    have h1 : (p : ℤ) ∣ t' - t := Int.ModEq.dvd h.1
    have h2 : (q : ℤ) ∣ (t' - k) - (t - k) := Int.ModEq.dvd h.2
    rw [show (t' - k) - (t - k) = t' - t by ring] at h2
    have hcop : IsCoprime (p : ℤ) q := Nat.isCoprime_iff_coprime.mpr hpq
    have h3 : ((p * q : ℕ) : ℤ) ∣ t' - t := by push_cast; exact hcop.mul_dvd h1 h2
    have h4 := Int.eq_zero_of_abs_lt_dvd h3 (by rw [abs_lt]; constructor <;> omega)
    omega

/-- If every window of length `P` contains at most `C` points of `g`, then an interval of
length `ℓ` contains at most `(ℓ / P + 1) * C` of them. -/
lemma card_filter_Ico_le {g : ℤ → Prop} [DecidablePred g] (P C : ℕ) (hP : 0 < P)
    (hw : ∀ x : ℤ, ((Ico x (x + P)).filter g).card ≤ C) (ℓ : ℕ) (x : ℤ) :
    ((Ico x (x + ℓ)).filter g).card ≤ (ℓ / P + 1) * C := by
  induction ℓ using Nat.strong_induction_on generalizing x with
  | _ ℓ ih =>
    by_cases h : ℓ < P
    · rw [Nat.div_eq_of_lt h, zero_add, one_mul]
      exact (card_le_card (filter_subset_filter _ (Ico_subset_Ico_right (by omega)))).trans
        (hw x)
    · rw [not_lt] at h
      have hsplit : Ico x (x + ℓ) = Ico x (x + P) ∪ Ico (x + P) (x + P + (ℓ - P : ℕ)) := by
        rw [Ico_union_Ico_eq_Ico (by omega) (by omega)]
        congr 1
        omega
      rw [hsplit, filter_union]
      refine (card_union_le _ _).trans ?_
      have h1 := ih (ℓ - P) (by omega) (x + P)
      have h2 := hw x
      rw [Nat.div_eq_sub_div hP h]
      calc _ ≤ C + ((ℓ - P) / P + 1) * C := add_le_add h2 h1
        _ = _ := by ring

/-- `|[c + 1, c + L] ∩ [e + 1, e + L]|`. -/
def tent (L : ℕ) (c e : ℤ) : ℕ := if c ≤ e then (c + L - e).toNat else (e + L - c).toNat

lemma card_inter_le {g : ℤ → Prop} [DecidablePred g] (P C L : ℕ) (hP : 0 < P)
    (hw : ∀ x : ℤ, ((Ico x (x + P)).filter g).card ≤ C) (c e : ℤ) :
    ((Ico (c + 1) (c + 1 + L)).filter fun x => e + 1 ≤ x ∧ x < e + 1 + L ∧ g x).card ≤
      (tent L c e / P + 1) * C := by
  unfold tent
  split_ifs with hce
  · refine le_trans (card_le_card ?_) (card_filter_Ico_le P C hP hw _ (e + 1))
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx ⊢
    exact ⟨⟨by omega, by omega⟩, hx.2.2.2⟩
  · refine le_trans (card_le_card ?_) (card_filter_Ico_le P C hP hw _ (c + 1))
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx ⊢
    exact ⟨⟨by omega, by omega⟩, hx.2.2.2⟩

/-- `X (ℓ / P + 1) C ≤ ℓ T + X C` as soon as `X C ≤ T P`. -/
lemma scale_bound (X ℓ P C T : ℕ) (h : X * C ≤ T * P) :
    X * ((ℓ / P + 1) * C) ≤ ℓ * T + X * C := by
  have : ℓ / P * (X * C) ≤ ℓ * T := calc
      ℓ / P * (X * C) ≤ ℓ / P * (T * P) := Nat.mul_le_mul_left _ h
      _ = (ℓ / P * P) * T := by ring
      _ ≤ ℓ * T := Nat.mul_le_mul_right _ (Nat.div_mul_le_self ℓ P)
  calc X * ((ℓ / P + 1) * C) = ℓ / P * (X * C) + X * C := by ring
    _ ≤ _ := Nat.add_le_add_right this _

lemma T_bound {i j : ℕ} (hi : i < K) (hj : j < K) : D ^ 2 * Cc i j ≤ T i j * Pp i j := by
  unfold T Cc Pp
  split_ifs with h
  · subst h
    calc D ^ 2 * min (a i) (p i - a i) = D * (D * min (a i) (p i - a i)) := by ring
      _ ≤ D * (m i * p i) := Nat.mul_le_mul_left _ (hm i hi)
      _ = D * m i * p i := by ring
  · calc D ^ 2 * (a i * (p j - a j)) = (D * a i) * (D * (p j - a j)) := by ring
      _ ≤ (u i * p i) * (v j * p j) := Nat.mul_le_mul (hu i hi) (hv j hj)
      _ = u i * v j * (p i * p j) := by ring

/- ## The construction -/

/-- Block `i`: the integers `i L + 1, …, i L + L`. -/
def blk (L i : ℕ) : Finset ℤ := Ico ((i : ℤ) * L + 1) ((i : ℤ) * L + 1 + L)

/-- The set before balancing. -/
@[irreducible] def A0 (L : ℕ) : Finset ℤ :=
  (range K).biUnion fun i => (blk L i).filter fun x => x % (p i : ℤ) < a i

lemma mem_A0 {L : ℕ} {x : ℤ} :
    x ∈ A0 L ↔ ∃ i < K, x ∈ blk L i ∧ x % (p i : ℤ) < a i := by
  unfold A0
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]

lemma A0_card_le (L : ℕ) :
    (A0 L).card ≤ ∑ i ∈ range K, ((blk L i).filter fun x => x % (p i : ℤ) < a i).card := by
  unfold A0
  exact card_biUnion_le

/-- Points of block `i` of `A0` whose shift by `-k` lands in block `j` outside `A0`. -/
def pairSet (L i j : ℕ) (k : ℤ) : Finset ℤ :=
  (blk L i).filter fun x => x - k ∈ blk L j ∧ x % (p i : ℤ) < a i ∧ ¬ (x - k) % (p j : ℤ) < a j

lemma pairSet_card (L : ℕ) {i j : ℕ} (hi : i < K) (hj : j < K) (k : ℤ) :
    (pairSet L i j k).card ≤ (tent L ((i : ℤ) * L) ((j : ℤ) * L + k) / Pp i j + 1) * Cc i j := by
  have hpi := p_pos i hi
  have hpj := p_pos j hj
  have hsub : pairSet L i j k ⊆ (Ico ((i : ℤ) * L + 1) ((i : ℤ) * L + 1 + L)).filter fun x =>
      ((j : ℤ) * L + k) + 1 ≤ x ∧ x < ((j : ℤ) * L + k) + 1 + L ∧
        (x % (p i : ℤ) ∈ Ico (0 : ℤ) (a i) ∧ (x - k) % (p j : ℤ) ∈ Ico (a j : ℤ) (p j)) := by
    intro x hx
    simp only [pairSet, blk, Finset.mem_filter, Finset.mem_Ico] at hx ⊢
    have h0 : 0 ≤ x % (p i : ℤ) := Int.emod_nonneg _ (by omega)
    have h1 : (x - k) % (p j : ℤ) < p j := Int.emod_lt_of_pos _ (by omega)
    omega
  refine (card_le_card hsub).trans ?_
  have hai := a_le i hi
  have haj := a_le j hj
  by_cases hij : i = j
  · subst hij
    simp only [Pp, Cc, if_true]
    refine card_inter_le _ _ _ hpi (fun x => le_min ?_ ?_) _ _
    · refine (card_le_card fun t ht => ?_).trans
        ((card_window_mod (p i) 0 x (Ico 0 (a i))).trans (by simp))
      simp only [Finset.mem_filter] at ht ⊢
      exact ⟨ht.1, by simpa using ht.2.1⟩
    · refine (card_le_card fun t ht => ?_).trans
        ((card_window_mod (p i) k x (Ico (a i) (p i))).trans (by simp))
      simp only [Finset.mem_filter] at ht ⊢
      exact ⟨ht.1, ht.2.2⟩
  · simp only [Pp, Cc, if_neg hij]
    refine card_inter_le _ _ _ (Nat.mul_pos hpi hpj) (fun x => ?_) _ _
    refine (card_window_pair (p i) (p j) (p_coprime i hi j hj hij) k x _ _).trans
      (le_of_eq ?_)
    have h1 : ((p j : ℤ) - a j).toNat = p j - a j := by omega
    rw [Int.card_Ico, Int.card_Ico, sub_zero, Int.toNat_natCast, h1]

lemma tent_le (L : ℕ) (hL : 0 < L) (i j : ℕ) (k : ℤ) :
    tent L ((i : ℤ) * L) ((j : ℤ) * L + k) ≤
      (if (i : ℤ) - j = k / L then L - (k % L).toNat else 0) +
        (if (i : ℤ) - j = k / L + 1 then (k % L).toNat else 0) := by
  have hk : (L : ℤ) * (k / L) + k % L = k := Int.mul_ediv_add_emod k L
  have hr0 : 0 ≤ k % L := Int.emod_nonneg _ (by omega)
  have hr1 : k % L < L := Int.emod_lt_of_pos _ (by omega)
  have hdiff : (i : ℤ) * L - ((j : ℤ) * L + k) = ((i : ℤ) - j - k / L) * L - k % L := by
    linear_combination hk
  have key : ((i : ℤ) - j - k / L = 0 ∧ ((i : ℤ) - j - k / L) * L = 0) ∨
      ((i : ℤ) - j - k / L = 1 ∧ ((i : ℤ) - j - k / L) * L = L) ∨
      (2 ≤ (i : ℤ) - j - k / L ∧ 2 * (L : ℤ) ≤ ((i : ℤ) - j - k / L) * L) ∨
      ((i : ℤ) - j - k / L ≤ -1 ∧ ((i : ℤ) - j - k / L) * L ≤ -L) := by
    rcases (by omega : (i : ℤ) - j - k / L = 0 ∨ (i : ℤ) - j - k / L = 1 ∨
        2 ≤ (i : ℤ) - j - k / L ∨ (i : ℤ) - j - k / L ≤ -1) with h | h | h | h
    · left; rw [h]; simp
    · right; left; rw [h]; simp
    · right; right; left; exact ⟨h, by nlinarith⟩
    · right; right; right; exact ⟨h, by nlinarith⟩
  unfold tent
  split_ifs <;> omega

lemma sum_tent_le (L : ℕ) (hL : 0 < L) (k : ℤ) :
    ∑ i ∈ range K, ∑ j ∈ range K, tent L ((i : ℤ) * L) ((j : ℤ) * L + k) * T i j ≤ L * Wb := by
  have hr : (k % L).toNat ≤ L := by
    have := Int.emod_lt_of_pos k (by omega : (0 : ℤ) < L); omega
  calc _ ≤ ∑ i ∈ range K, ∑ j ∈ range K,
        ((L - (k % L).toNat) * (if (i : ℤ) - j = k / L then T i j else 0) +
          (k % L).toNat * (if (i : ℤ) - j = k / L + 1 then T i j else 0)) := by
        refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
        refine (Nat.mul_le_mul_right _ (tent_le L hL i j k)).trans (le_of_eq ?_)
        split_ifs <;> ring
    _ = (L - (k % L).toNat) * Wd (k / L) + (k % L).toNat * Wd (k / L + 1) := by
        simp only [Wd, mul_sum, ← sum_add_distrib]
    _ ≤ (L - (k % L).toNat) * Wb + (k % L).toNat * Wb :=
        add_le_add (Nat.mul_le_mul_left _ (Wd_le _)) (Nat.mul_le_mul_left _ (Wd_le _))
    _ = L * Wb := by rw [← add_mul, Nat.sub_add_cancel hr]

lemma blk_filter_lt_card (L i : ℕ) (hi : i < K) :
    D * ((blk L i).filter fun x => x % (p i : ℤ) < a i).card ≤ L * u i + D * a i := by
  have hp := p_pos i hi
  refine le_trans (Nat.mul_le_mul_left _ ?_) (scale_bound D L (p i) (a i) (u i) (hu i hi))
  refine card_filter_Ico_le (p i) (a i) hp (fun x => ?_) L _
  refine (card_le_card fun t ht => ?_).trans
    ((card_window_mod (p i) 0 x (Ico 0 (a i))).trans (by simp))
  simp only [Finset.mem_filter, Finset.mem_Ico, sub_zero] at ht ⊢
  exact ⟨ht.1, Int.emod_nonneg _ (by omega), ht.2⟩

lemma blk_filter_ge_card (L i : ℕ) (hi : i < K) :
    D * ((blk L i).filter fun x => ¬ x % (p i : ℤ) < a i).card ≤ L * v i + D * (p i - a i) := by
  have hp := p_pos i hi
  have ha := a_le i hi
  refine le_trans (Nat.mul_le_mul_left _ ?_) (scale_bound D L (p i) _ (v i) (hv i hi))
  refine card_filter_Ico_le (p i) _ hp (fun x => ?_) L _
  refine (card_le_card fun t ht => ?_).trans
    ((card_window_mod (p i) 0 x (Ico (a i) (p i))).trans (by simp))
  simp only [Finset.mem_filter, Finset.mem_Ico, sub_zero] at ht ⊢
  exact ⟨ht.1, by omega, Int.emod_lt_of_pos _ (by omega)⟩

lemma exists_blk (L : ℕ) (hL : 0 < L) (y : ℤ) (h1 : 1 ≤ y) (h2 : y ≤ K * L) :
    ∃ j < K, y ∈ blk L j := by
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  have hq0 : 0 ≤ (y - 1) / L := Int.ediv_nonneg (by omega) hL'.le
  have hq1 : (y - 1) / L * L ≤ y - 1 := Int.ediv_mul_le _ hL'.ne'
  have hq2 : y - 1 < ((y - 1) / L + 1) * L := Int.lt_ediv_add_one_mul_self _ hL'
  have hqK : (y - 1) / L < K := by
    by_contra hc
    rw [not_lt] at hc
    have : (K : ℤ) * L ≤ (y - 1) / L * L := mul_le_mul_of_nonneg_right hc hL'.le
    omega
  refine ⟨((y - 1) / L).toNat, by omega, ?_⟩
  simp only [blk, Finset.mem_Ico]
  rw [Int.toNat_of_nonneg hq0]
  constructor <;> linarith

lemma A0_subset (n L : ℕ) (hKL : K * L ≤ 2 * n) : A0 L ⊆ Icc (1 : ℤ) (2 * n) := by
  intro x hx
  obtain ⟨i, hi, hxi, -⟩ := mem_A0.mp hx
  simp only [blk, Finset.mem_Ico] at hxi
  obtain ⟨h1, h2⟩ := hxi
  have : ((i : ℤ) + 1) * L ≤ K * L :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hi) (by positivity)
  have hKL' : ((K * L : ℕ) : ℤ) ≤ 2 * n := by exact_mod_cast hKL
  push_cast at hKL'
  have : (0 : ℤ) ≤ (i : ℤ) * L := by positivity
  rw [Finset.mem_Icc]
  constructor <;> nlinarith

/-- `A0` has roughly the right size. -/
lemma A0_card_upper (L : ℕ) :
    D * (A0 L).card ≤ L * ∑ i ∈ range K, u i + D * ∑ i ∈ range K, a i := by
  calc D * (A0 L).card
      ≤ D * ∑ i ∈ range K, ((blk L i).filter fun x => x % (p i : ℤ) < a i).card :=
        Nat.mul_le_mul_left _ (A0_card_le L)
    _ = ∑ i ∈ range K, D * ((blk L i).filter fun x => x % (p i : ℤ) < a i).card := by
        rw [mul_sum]
    _ ≤ ∑ i ∈ range K, (L * u i + D * a i) :=
        sum_le_sum fun i hi => blk_filter_lt_card L i (Finset.mem_range.mp hi)
    _ = _ := by rw [sum_add_distrib, mul_sum, mul_sum]

lemma A0_card_lower (L : ℕ) (hL : 0 < L) :
    D * (K * L) ≤ D * (A0 L).card + (L * ∑ i ∈ range K, v i +
      D * ∑ i ∈ range K, (p i - a i)) := by
  have hcov : Icc (1 : ℤ) (K * L) ⊆ A0 L ∪
      (range K).biUnion fun j => (blk L j).filter fun x => ¬ x % (p j : ℤ) < a j := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    obtain ⟨j, hj, hyj⟩ := exists_blk L hL y hy.1 hy.2
    rw [Finset.mem_union]
    by_cases hc : y % (p j : ℤ) < a j
    · left
      exact mem_A0.mpr ⟨j, hj, hyj, hc⟩
    · right
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, Finset.mem_filter.mpr ⟨hyj, hc⟩⟩
  have hc1 : K * L ≤ (A0 L).card +
      ∑ j ∈ range K, ((blk L j).filter fun x => ¬ x % (p j : ℤ) < a j).card := by
    have h1 := (card_le_card hcov).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left card_biUnion_le _))
    have h2 : (Icc (1 : ℤ) (K * L)).card = K * L := by
      rw [Int.card_Icc, add_sub_cancel_right, ← Nat.cast_mul, Int.toNat_natCast]
    rwa [h2] at h1
  calc D * (K * L) ≤ D * ((A0 L).card +
        ∑ j ∈ range K, ((blk L j).filter fun x => ¬ x % (p j : ℤ) < a j).card) :=
        Nat.mul_le_mul_left _ hc1
    _ = D * (A0 L).card +
        ∑ j ∈ range K, D * ((blk L j).filter fun x => ¬ x % (p j : ℤ) < a j).card := by
        rw [mul_add, mul_sum]
    _ ≤ D * (A0 L).card + ∑ j ∈ range K, (L * v j + D * (p j - a j)) :=
        Nat.add_le_add_left (sum_le_sum fun j hj => blk_filter_ge_card L j (Finset.mem_range.mp hj)) _
    _ = _ := by rw [sum_add_distrib, mul_sum, mul_sum]

/-- The overlap of `A0` with its complement, for one shift. -/
lemma A0_overlap (n L : ℕ) (hL : 0 < L) (h2n : 2 * n < K * L + K)
    (k : ℤ) :
    D ^ 2 * ((A0 L).filter fun x => x - k ∈ Icc (1 : ℤ) (2 * n) \ A0 L).card ≤
      L * Wb + D ^ 2 * ((∑ i ∈ range K, ∑ j ∈ range K, Cc i j) + K) := by
  have hsub : ((A0 L).filter fun x => x - k ∈ Icc (1 : ℤ) (2 * n) \ A0 L) ⊆
      ((range K ×ˢ range K).biUnion fun ij => pairSet L ij.1 ij.2 k) ∪
        Icc ((K * L : ℕ) + 1 + k : ℤ) (2 * n + k) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc] at hx
    obtain ⟨hxA, ⟨hy1, hy2⟩, hyA⟩ := hx
    obtain ⟨i, hi, hxi⟩ := mem_A0.mp hxA
    rw [Finset.mem_union]
    by_cases hy : x - k ≤ K * L
    · left
      obtain ⟨j, hj, hyj⟩ := exists_blk L hL (x - k) hy1 (by exact_mod_cast hy)
      refine Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨hxi.1, hyj, hxi.2, fun hc => hyA (mem_A0.mpr ⟨j, hj, hyj, hc⟩)⟩
    · right
      rw [Finset.mem_Icc]
      push_cast
      omega
  have hR : (Icc ((K * L : ℕ) + 1 + k : ℤ) (2 * n + k)).card ≤ K := by
    rw [Int.card_Icc]; omega
  have hpairs : D ^ 2 * ∑ ij ∈ range K ×ˢ range K, (pairSet L ij.1 ij.2 k).card ≤
      L * Wb + D ^ 2 * ∑ i ∈ range K, ∑ j ∈ range K, Cc i j := by
    rw [sum_product, mul_sum]
    calc ∑ i ∈ range K, D ^ 2 * ∑ j ∈ range K, (pairSet L i j k).card
        = ∑ i ∈ range K, ∑ j ∈ range K, D ^ 2 * (pairSet L i j k).card := by
          simp only [mul_sum]
      _ ≤ ∑ i ∈ range K, ∑ j ∈ range K,
          (tent L ((i : ℤ) * L) ((j : ℤ) * L + k) * T i j + D ^ 2 * Cc i j) := by
          refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
          rw [Finset.mem_range] at hi hj
          exact (Nat.mul_le_mul_left _ (pairSet_card L hi hj k)).trans
            (scale_bound _ _ _ _ _ (T_bound hi hj))
      _ = ∑ i ∈ range K, ∑ j ∈ range K, tent L ((i : ℤ) * L) ((j : ℤ) * L + k) * T i j +
          D ^ 2 * ∑ i ∈ range K, ∑ j ∈ range K, Cc i j := by
          simp only [sum_add_distrib, mul_sum]
      _ ≤ _ := Nat.add_le_add_right (sum_tent_le L hL k) _
  calc D ^ 2 * ((A0 L).filter fun x => x - k ∈ Icc (1 : ℤ) (2 * n) \ A0 L).card
      ≤ D ^ 2 * (∑ ij ∈ range K ×ˢ range K, (pairSet L ij.1 ij.2 k).card + K) := by
        refine Nat.mul_le_mul_left _ ((card_le_card hsub).trans ((card_union_le _ _).trans ?_))
        exact add_le_add card_biUnion_le hR
    _ ≤ _ := by linarith [hpairs]

/- ## Overlaps -/

lemma overlap_le (A B : Finset ℤ) (k : ℤ) :
    Overlap A B k ≤ (A.filter fun x => x - k ∈ B).card := by
  unfold Overlap
  rw [Finset.product_eq_sprod]
  refine card_le_card_of_injOn Prod.fst ?_ ?_
  · rintro ⟨a, b⟩ hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hq.1.1, ?_⟩)
    rw [show a - k = b by omega]
    exact hq.1.2
  · rintro ⟨a, b⟩ hq ⟨a', b'⟩ hq' h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq hq'
    simp only at h
    subst h
    ext <;> simp; omega

/-- Moving elements between the two halves: each moved element changes each count by at most
one. -/
lemma filter_card_le_of_change (A B A' B' : Finset ℤ) (k : ℤ) :
    (A'.filter fun x => x - k ∈ B').card ≤
      (A.filter fun x => x - k ∈ B).card + (A' \ A).card + (B' \ B).card := by
  calc (A'.filter fun x => x - k ∈ B').card
      ≤ ((A.filter fun x => x - k ∈ B) ∪ (A' \ A) ∪ (B' \ B).image (· + k)).card := by
        refine card_le_card fun x hx => ?_
        simp only [Finset.mem_filter] at hx
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_image]
        by_cases hA : x ∈ A
        · by_cases hB : x - k ∈ B
          · exact Or.inl (Or.inl ⟨hA, hB⟩)
          · exact Or.inr ⟨x - k, ⟨hx.2, hB⟩, by ring⟩
        · exact Or.inl (Or.inr ⟨hx.1, hA⟩)
    _ ≤ _ := (card_union_le _ _).trans (add_le_add (card_union_le _ _) card_image_le)

/- ## The bound for each `n` -/

/-- Constant error term. -/
def E2 : ℕ := 2 * ((∑ i ∈ range K, ∑ j ∈ range K, Cc i j) + K) +
  (K + 2 * ∑ i ∈ range K, a i + 2 * ∑ i ∈ range K, (p i - a i))

lemma main_bound (n : ℕ) (hn : K ≤ 2 * n) :
    2 * K * D ^ 2 * M n ≤ 2 * n * (2 * Wb + D * sig) + K * D ^ 2 * E2 := by
  obtain ⟨L, hLdef⟩ : ∃ L, L = 2 * n / K := ⟨_, rfl⟩
  have hK : 0 < K := by unfold K; decide
  have hL : 0 < L := hLdef ▸ Nat.div_pos hn hK
  have hKL : K * L ≤ 2 * n := hLdef ▸ Nat.mul_div_le _ _
  have h2n : 2 * n < K * L + K := by
    have := Nat.div_add_mod (2 * n) K
    have := Nat.mod_lt (2 * n) hK
    rw [← hLdef] at *
    omega
  obtain ⟨U, hU⟩ : ∃ U, U = Icc (1 : ℤ) (2 * n) := ⟨_, rfl⟩
  have hUc : U.card = 2 * n := by rw [hU, Int.card_Icc]; omega
  have hA0U := A0_subset n L hKL
  rw [← hU] at hA0U
  obtain ⟨s, hs⟩ : ∃ s, s = (A0 L).card := ⟨_, rfl⟩
  have hup := A0_card_upper L
  have hlo := A0_card_lower L hL
  rw [← hs] at hup hlo
  have hsu := sum_u
  have hsv := sum_v
  -- pick a balanced `A` close to `A0`
  obtain ⟨A, hAU, hAc, hdev⟩ : ∃ A : Finset ℤ, A ⊆ U ∧ A.card = n ∧
      2 * D * ((A \ A0 L).card + ((U \ A) \ (U \ A0 L)).card) ≤
        L * sig + D * (K + 2 * ∑ i ∈ range K, a i + 2 * ∑ i ∈ range K, (p i - a i)) := by
    rcases le_total s n with hsn | hsn
    · obtain ⟨A, h1, h2, h3⟩ := exists_subsuperset_card_eq (n := n) hA0U (hs ▸ hsn) (by rw [hUc]; omega)
      refine ⟨A, h2, h3, ?_⟩
      have e1 : (A \ A0 L).card = n - s := by rw [card_sdiff_of_subset h1, h3, hs]
      have e2 : (U \ A) \ (U \ A0 L) = ∅ := by
        rw [sdiff_eq_empty_iff_subset]; exact sdiff_subset_sdiff le_rfl h1
      rw [e1, e2, card_empty, add_zero]
      have h1' : L * (2 * ∑ i ∈ range K, v i) ≤ L * (D * K + sig) := Nat.mul_le_mul_left _ hsv
      have ht : n - s + s = n := Nat.sub_add_cancel hsn
      generalize n - s = t at *
      generalize (∑ i ∈ range K, u i) = Su at *
      generalize (∑ i ∈ range K, v i) = Sv at *
      generalize (∑ i ∈ range K, a i) = Sa at *
      generalize (∑ i ∈ range K, (p i - a i)) = Spa at *
      generalize sig = sg at *
      unfold D K at *
      linarith only [hlo, h2n, h1', ht]
    · obtain ⟨A, h1, h2, h3⟩ := exists_subsuperset_card_eq (empty_subset _)
        (by simp : (∅ : Finset ℤ).card ≤ n) (hs ▸ hsn)
      refine ⟨A, h2.trans hA0U, h3, ?_⟩
      have e1 : A \ A0 L = ∅ := sdiff_eq_empty_iff_subset.mpr h2
      have e2 : ((U \ A) \ (U \ A0 L)).card ≤ s - n := by
        rw [hs, ← h3, ← card_sdiff_of_subset h2]
        refine card_le_card fun x hx => ?_
        simp only [Finset.mem_sdiff] at hx ⊢
        exact ⟨by by_contra hc; exact hx.2 ⟨hx.1.1, hc⟩, hx.1.2⟩
      rw [e1, card_empty, zero_add]
      have h1' : L * (2 * ∑ i ∈ range K, u i) ≤ L * (D * K + sig) := Nat.mul_le_mul_left _ hsu
      have e2' := Nat.mul_le_mul_left (2 * D) e2
      have ht : s - n + n = s := Nat.sub_add_cancel hsn
      generalize s - n = t at *
      generalize ((U \ A) \ (U \ A0 L)).card = c at *
      generalize (∑ i ∈ range K, u i) = Su at *
      generalize (∑ i ∈ range K, v i) = Sv at *
      generalize (∑ i ∈ range K, a i) = Sa at *
      generalize (∑ i ∈ range K, (p i - a i)) = Spa at *
      generalize sig = sg at *
      unfold D K at *
      linarith only [hKL, hup, h1', e2', ht]
  obtain ⟨B, hB⟩ : ∃ B, B = U \ A := ⟨_, rfl⟩
  rw [← hB] at hdev
  -- every overlap is small
  have hov : ∀ k, 2 * K * D ^ 2 * Overlap A B k ≤ 2 * n * (2 * Wb + D * sig) + K * D ^ 2 * E2 := by
    intro k
    have h1 := overlap_le A B k
    have h2 := filter_card_le_of_change (A0 L) (U \ A0 L) A B k
    have h3 := A0_overlap n L hL h2n k
    rw [← hU] at h3
    have hKL' : K * (L * (2 * Wb + D * sig)) ≤ 2 * n * (2 * Wb + D * sig) := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_right _ hKL
    unfold E2
    unfold D K at *
    linarith
  have hM : M n ≤ MaxOverlap A B := by
    refine Nat.sInf_le ⟨A, B, hB ▸ disjoint_sdiff, ?_, ?_, rfl⟩
    · rw [hB, union_sdiff_of_subset hAU, hU]
    · rw [hB, card_sdiff_of_subset hAU, hUc, hAc]
      omega
  have hmax : 2 * K * D ^ 2 * MaxOverlap A B ≤
      2 * n * (2 * Wb + D * sig) + K * D ^ 2 * E2 := by
    have hpos : 0 < 2 * K * D ^ 2 := by unfold K D; decide
    have : MaxOverlap A B ≤ (2 * n * (2 * Wb + D * sig) + K * D ^ 2 * E2) / (2 * K * D ^ 2) :=
      ciSup_le fun k => (Nat.le_div_iff_mul_le hpos).mpr (by rw [mul_comm]; exact hov k)
    calc _ ≤ 2 * K * D ^ 2 *
          ((2 * n * (2 * Wb + D * sig) + K * D ^ 2 * E2) / (2 * K * D ^ 2)) :=
          Nat.mul_le_mul_left _ this
      _ ≤ _ := Nat.mul_div_le _ _
  exact (Nat.mul_le_mul_left _ hM).trans hmax

/- ## The limsup -/

theorem limsup_le : atTop.limsup MinOverlapQuotient ≤ (0.380924 : ℝ) := by
  refine limsup_le_of_le (isCoboundedUnder_le_of_le atTop (x := 0) fun N => ?_) ?_
  · unfold MinOverlapQuotient; positivity
  · rw [eventually_atTop]
    refine ⟨K * D ^ 2 * E2 * 1000000 + K, fun n hn => ?_⟩
    have hKn : K ≤ n := le_trans (Nat.le_add_left _ _) hn
    have hb := main_bound n (by clear hn; omega)
    have hg := gap
    have hnat : 1000000 * M n ≤ 380924 * n := by
      have hg' := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hg)
      have : 2 * K * D ^ 2 * (1000000 * M n) ≤ 2 * K * D ^ 2 * (380924 * n) := by
        unfold D K at *
        rw [Nat.mul_succ] at hg'
        linarith
      exact Nat.le_of_mul_le_mul_left this (by unfold K D; decide)
    have hnpos : (0 : ℝ) < n := by
      have : 0 < n := by unfold K at hn; omega
      exact_mod_cast this
    unfold MinOverlapQuotient
    rw [div_le_iff₀ hnpos]
    have : (1000000 : ℝ) * M n ≤ 380924 * n := by exact_mod_cast hnat
    norm_num
    linarith

/-- The repository statement, with the answer `0.380924`. -/
theorem erdos_36_variants_upper :
    ∃ (c : ℝ), c < 0.380926853433087 ∧ atTop.limsup MinOverlapQuotient ≤ c ∧
      c = answer(0.380924) :=
  ⟨0.380924, by norm_num, limsup_le, rfl⟩

/-- The bound also gives `Erdos36.minimum_overlap.variants.upper.haugland_2022`, with its exact
type. -/
theorem haugland_2022 : type_of% _root_.Erdos36.minimum_overlap.variants.upper.haugland_2022 :=
  le_trans limsup_le (by norm_num)

end ErdosLean.Erdos36
