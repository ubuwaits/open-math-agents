import Mathlib
import OMAReductions.R_Erdos101_erdos_101_R1

-- Credit: @ubuwaits

/-!
# Incidence rank and common four-term sums

A dense family of real-plane four-point lines contains an induced core with
bounded rational dimension for every vector-valued common-sum labeling.
The integer construction at the end supplies dense abstract families with
all pair sums distinct, for arbitrarily large numbers of vertices.
-/

/- The dimension of common-sum labelings on dense linear four-uniform hypergraphs. -/

noncomputable section

open scoped BigOperators
open Finset Module

namespace Erdos101IncidenceRank

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Two distinct vertices determine at most one edge. -/
def LinearEdges (E : Finset (Finset α)) : Prop :=
  ∀ ⦃e⦄, e ∈ E → ∀ ⦃f⦄, f ∈ E → ∀ ⦃p q : α⦄, p ∈ e → p ∈ f → q ∈ e → q ∈ f → p ≠ q → e = f

def restricted (E : Finset (Finset α)) (U : Finset α) : Finset (Finset α) :=
  E.filter (· ⊆ U)

def star (E : Finset (Finset α)) (p : α) := E.filter (p ∈ ·)

def neighbors (E : Finset (Finset α)) (p : α) := (star E p).biUnion (·.erase p)

def labelSpace (U : Finset α) (E : Finset (Finset α)) : Submodule ℝ (EuclideanSpace ℝ α) where
  carrier := {x | (∀ p ∉ U, x p = 0) ∧ ∀ e ∈ E, ∑ p ∈ e, x p = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨fun p hp => by simp [hx p hp, hy p hp],
      fun e he => by simp [Finset.sum_add_distrib, hx' e he, hy' e he]⟩
  smul_mem' := by
    rintro r x ⟨hx, hx'⟩
    exact ⟨fun p hp => by simp [hx p hp],
      fun e he => by simp [← Finset.mul_sum, hx' e he]⟩

omit [DecidableEq α] in
/-- Bessel's inequality bounds dimension by the total squared lengths of recovery vectors. -/
theorem finrank_of_recovery (V : Submodule ℝ (EuclideanSpace ℝ α))
    (w : α → EuclideanSpace ℝ α)
    (recover : ∀ (x : V) (p : α), (x : EuclideanSpace ℝ α) p =
      inner ℝ (x : EuclideanSpace ℝ α) (w p)) :
    (finrank ℝ V : ℝ) ≤ ∑ p, ‖w p‖ ^ 2 := by
  let b := stdOrthonormalBasis ℝ V
  let v (i : Fin (finrank ℝ V)) := (b i : EuclideanSpace ℝ α)
  have ho : Orthonormal ℝ v := (V.subtypeₗᵢ.orthonormal_comp_iff).2 b.orthonormal
  calc
    (finrank ℝ V : ℝ) = ∑ i, ‖v i‖ ^ 2 := by
      have unit (i) : ‖v i‖ = 1 := ho.1 i
      simp [unit]
    _ = ∑ p, ∑ i, (v i p) ^ 2 := by
      simp_rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.sum_comm
    _ ≤ ∑ p, ‖w p‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      have h := ho.sum_inner_products_le (s := Finset.univ) (w p)
      have ev (i) : inner ℝ (v i) (w p) = v i p := (recover (b i) p).symm
      simpa only [ev, Real.norm_eq_abs, sq_abs] using h

omit [Fintype α] in
private theorem disjoint_star {E : Finset (Finset α)} (lin : LinearEdges E) (p : α) :
    (↑(star E p) : Set (Finset α)).PairwiseDisjoint (fun e => e.erase p) := by
  intro e he f hf ne
  apply Finset.disjoint_left.mpr
  intro q hq hq'
  obtain ⟨hem, hpe⟩ := Finset.mem_filter.mp he
  obtain ⟨hfm, hpf⟩ := Finset.mem_filter.mp hf
  exact ne (lin hem hfm hpe hpf (Finset.mem_erase.mp hq).2 (Finset.mem_erase.mp hq').2
    (Finset.mem_erase.mp hq).1.symm)

omit [Fintype α] in
private theorem neighbors_card {E : Finset (Finset α)} (four : ∀ e ∈ E, e.card = 4)
    (lin : LinearEdges E) (p : α) : (neighbors E p).card = 3 * (star E p).card := by
  rw [neighbors, Finset.card_biUnion (disjoint_star lin p)]
  trans ∑ _e ∈ star E p, 3
  · refine Finset.sum_congr rfl fun e he => ?_
    obtain ⟨hem, hpe⟩ := Finset.mem_filter.mp he
    simp [Finset.card_erase_of_mem hpe, four e hem]
  · simp [Nat.mul_comm]

omit [Fintype α] in
private theorem neighbors_sum {E : Finset (Finset α)} (lin : LinearEdges E) (p : α)
    {x : EuclideanSpace ℝ α} (hx : ∀ e ∈ E, ∑ q ∈ e, x q = 0) :
    ∑ q ∈ neighbors E p, x q = -((star E p).card : ℝ) * x p := by
  rw [neighbors, Finset.sum_biUnion (disjoint_star lin p)]
  trans ∑ _e ∈ star E p, -(x p)
  · refine Finset.sum_congr rfl fun e he => ?_
    obtain ⟨hem, hpe⟩ := Finset.mem_filter.mp he
    have h := Finset.sum_erase_add e (fun q => x q) hpe
    rw [hx e hem] at h
    linarith
  · simp

omit [Fintype α] in
private theorem not_neighbor (E : Finset (Finset α)) (p : α) : p ∉ neighbors E p := by
  simp [neighbors]

/-- The leverage of coordinate p is at most 3/(degree(p)+3). -/
theorem label_dimension (U : Finset α) (E : Finset (Finset α))
    (four : ∀ e ∈ E, e.card = 4) (lin : LinearEdges E) :
    (finrank ℝ (labelSpace U E) : ℝ) ≤ ∑ p ∈ U, 3 / ((star E p).card + 3 : ℝ) := by
  classical
  let d (p : α) : ℝ := (star E p).card
  let raw (p : α) : EuclideanSpace ℝ α := WithLp.toLp 2
    (fun q => (if q = p then (3 : ℝ) else 0) - (if q ∈ neighbors E p then 1 else 0))
  let w (p : α) : EuclideanSpace ℝ α := if p ∈ U then (d p + 3)⁻¹ • raw p else 0
  have hp (p : α) : 0 < d p + 3 := by dsimp [d]; positivity
  have recover (x : labelSpace U E) (p : α) :
      (x : EuclideanSpace ℝ α) p = inner ℝ (x : EuclideanSpace ℝ α) (w p) := by
    by_cases hu : p ∈ U
    · rw [show w p = (d p + 3)⁻¹ • raw p by simp [w, hu], real_inner_smul_right]
      have dot : inner ℝ (x : EuclideanSpace ℝ α) (raw p) =
          3 * (x : EuclideanSpace ℝ α) p - ∑ q ∈ neighbors E p, (x : EuclideanSpace ℝ α) q := by
        rw [PiLp.inner_apply]
        simp only [Real.inner_apply]
        change (∑ q, (x : EuclideanSpace ℝ α) q *
            ((if q = p then (3 : ℝ) else 0) - (if q ∈ neighbors E p then 1 else 0))) = _
        simp only [mul_sub, mul_ite, mul_zero, mul_one, Finset.sum_sub_distrib]
        simp [mul_comm]
      rw [dot, neighbors_sum lin p x.property.2]
      change _ = (d p + 3)⁻¹ * (3 * _ - -(d p) * _)
      field_simp [(hp p).ne']
      ring
    · simp [w, hu, x.property.1 p hu]
  have norm_w (p : α) (hu : p ∈ U) : ‖w p‖ ^ 2 = 3 / (d p + 3) := by
    have cells (q : α) : ((raw p) q) ^ 2 =
        (if q = p then (9 : ℝ) else 0) + (if q ∈ neighbors E p then 1 else 0) := by
      by_cases h : q = p
      · subst q; norm_num [raw, not_neighbor]
      · by_cases h' : q ∈ neighbors E p <;> simp [raw, h, h']
    have norm_raw : ‖raw p‖ ^ 2 = 9 + 3 * d p := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp_rw [cells]
      simp [Finset.sum_add_distrib, neighbors_card four lin, d]
    rw [show w p = (d p + 3)⁻¹ • raw p by simp [w, hu], norm_smul, mul_pow, norm_raw]
    rw [Real.norm_eq_abs, sq_abs]
    field_simp [(hp p).ne']
    ring
  refine (finrank_of_recovery _ w recover).trans_eq ?_
  calc
    (∑ p, ‖w p‖ ^ 2) = ∑ p ∈ U, ‖w p‖ ^ 2 := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) fun p _ hu => by simp [w, hu]
    _ = _ := Finset.sum_congr rfl fun p hu => norm_w p hu


omit [Fintype α] in
private theorem restricted_erase (E : Finset (Finset α)) (U : Finset α) (p : α) :
    restricted E (U.erase p) = (restricted E U).filter (p ∉ ·) := by
  ext e
  simp only [restricted, Finset.mem_filter]
  constructor
  · rintro ⟨he, h⟩
    exact ⟨⟨he, h.trans (Finset.erase_subset _ _)⟩, fun hp => Finset.notMem_erase p U (h hp)⟩
  · rintro ⟨⟨he, h⟩, hp⟩
    exact ⟨he, fun q hq => Finset.mem_erase.mpr ⟨fun eq => hp (eq ▸ hq), h hq⟩⟩

/-- A family of at least n²/s edges retains half its edges after passing to an
induced subfamily of minimum degree n/(2s). No regularity assumption is needed. -/
theorem dense_core (E : Finset (Finset α)) (s : ℕ) (pos : 0 < s)
    (density : (Fintype.card α)^2 ≤ s * E.card) :
    ∃ U : Finset α, E.card ≤ 2*(restricted E U).card ∧
      ∀ p ∈ U, Fintype.card α ≤ 2*s*(star (restricted E U) p).card := by
  classical
  let n := Fintype.card α
  let score (U : Finset α) : ℤ :=
    2*(s : ℤ)*((restricted E U).card : ℤ) - (n : ℤ)*(U.card : ℤ)
  obtain ⟨U, _, best⟩ := Finset.univ.exists_max_image score (Finset.univ_nonempty)
  have top := best Finset.univ (Finset.mem_univ _)
  have full : restricted E Finset.univ = E := by simp [restricted]
  have dense : (n : ℤ)^2 ≤ (s : ℤ)*(E.card : ℤ) := by exact_mod_cast density
  have hs : (0 : ℤ) < s := by exact_mod_cast pos
  have hu : 0 ≤ (n : ℤ)*(U.card : ℤ) := by positivity
  dsimp only [score] at top
  rw [full, Finset.card_univ] at top
  change 2*(s : ℤ)*E.card - (n : ℤ)*n ≤ _ at top
  refine ⟨U, ?_, ?_⟩
  · have ineq : (s : ℤ)*(E.card : ℤ) ≤ (s : ℤ)*(2*((restricted E U).card : ℤ)) := by
      nlinarith only [dense, top, hu]
    exact_mod_cast (le_of_mul_le_mul_left ineq hs)
  · intro p hp
    have drop := best (U.erase p) (Finset.mem_univ _)
    have edge_counts : (star (restricted E U) p).card + (restricted E (U.erase p)).card =
        (restricted E U).card := by
      rw [restricted_erase]
      exact Finset.card_filter_add_card_filter_not ..
    have de : ((star (restricted E U) p).card : ℤ) + (restricted E (U.erase p)).card =
        (restricted E U).card := by exact_mod_cast edge_counts
    have du : ((U.erase p).card : ℤ) + 1 = U.card := by
      exact_mod_cast Finset.card_erase_add_one hp
    dsimp only [score] at drop
    rw [← de, ← du] at drop
    have conclusion : (n : ℤ) ≤ 2*(s : ℤ)*(star (restricted E U) p).card := by
      nlinarith only [drop]
    exact_mod_cast conclusion

/-- An arbitrary dense linear four-uniform hypergraph has an induced core supporting
at least half its edges and at most 6s independent real-valued zero-sum labelings. -/
theorem dense_core_label_dimension (E : Finset (Finset α)) (s : ℕ) (pos : 0 < s)
    (density : (Fintype.card α)^2 ≤ s * E.card)
    (four : ∀ e ∈ E, e.card = 4) (lin : LinearEdges E) :
    ∃ U : Finset α, E.card ≤ 2*(restricted E U).card ∧
      (∀ p ∈ U, Fintype.card α ≤ 2*s*(star (restricted E U) p).card) ∧
      finrank ℝ (labelSpace U (restricted E U)) ≤ 6*s := by
  obtain ⟨U, count, deg⟩ := dense_core E s pos density
  refine ⟨U, count, deg, ?_⟩
  have sub := Finset.filter_subset (· ⊆ U) E
  have four' (e) (he : e ∈ restricted E U) := four e (sub he)
  have lin' : LinearEdges (restricted E U) :=
    fun _ he _ hf => lin (sub he) (sub hf)
  have h := label_dimension U (restricted E U) four' lin'
  by_cases h0 : Fintype.card α = 0
  · have u0 : U = ∅ := Finset.card_eq_zero.mp (by
      have := Finset.card_le_univ U; omega)
    rw [u0] at h ⊢
    simp only [Finset.sum_empty] at h
    exact_mod_cast h.trans (show (0 : ℝ) ≤ 6*(s : ℝ) by positivity)
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Nat.pos_of_ne_zero h0
  have uc : (U.card : ℝ) ≤ Fintype.card α := by exact_mod_cast Finset.card_le_univ U
  have terms (p) (hp : p ∈ U) : (3 : ℝ) / ((star (restricted E U) p).card + 3) ≤
      (6*(s : ℝ))/(Fintype.card α : ℝ) := by
    have d : (Fintype.card α : ℝ) ≤ 2*(s : ℝ)*(star (restricted E U) p).card := by
      exact_mod_cast deg p hp
    apply (div_le_div_iff₀ (by positivity) hn).2
    nlinarith only [d, (show (0 : ℝ) ≤ s by positivity)]
  have bound : ∑ p ∈ U, 3 / ((star (restricted E U) p).card + 3 : ℝ) ≤ 6 * (s : ℝ) := by
    calc
      _ ≤ ∑ _p ∈ U, (6*(s : ℝ))/(Fintype.card α : ℝ) := Finset.sum_le_sum terms
      _ = (U.card : ℝ) * ((6*(s : ℝ))/(Fintype.card α : ℝ)) := by simp
      _ ≤ (Fintype.card α : ℝ) * ((6*(s : ℝ))/(Fintype.card α : ℝ)) :=
        mul_le_mul_of_nonneg_right uc (by positivity)
      _ = _ := by field_simp
  exact_mod_cast h.trans bound

/-- Rational scalar solutions to the same equations, including the support constraint. -/
def rationalLabels (U : Finset α) (E : Finset (Finset α)) : Submodule ℚ (α → ℚ) where
  carrier := {f | (∀ p ∉ U, f p = 0) ∧ ∀ e ∈ E, ∑ p ∈ e, f p = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hf,hf'⟩ ⟨hg,hg'⟩
    exact ⟨fun p hp => by simp [hf p hp,hg p hp],
      fun e he => by simp [Finset.sum_add_distrib,hf' e he,hg' e he]⟩
  smul_mem' := by
    rintro t f ⟨hf,hf'⟩
    exact ⟨fun p hp => by simp [hf p hp],
      fun e he => by simp [← Finset.mul_sum,hf' e he]⟩

omit [DecidableEq α] in
theorem rational_dimension_le (U : Finset α) (E : Finset (Finset α)) :
    finrank ℚ (rationalLabels U E) ≤ finrank ℝ (labelSpace U E) := by
  let V := rationalLabels U E
  let b := Module.finBasis ℚ V
  let v (i : Fin (finrank ℚ V)) : α → ℚ := b i
  have hq : LinearIndependent ℚ v := b.linearIndependent.map' V.subtype V.ker_subtype
  let t := (WithLp.linearEquiv 2 ℝ (α → ℝ)).symm
  have hr := (linearIndependent_algebraMap_comp_iff (S := ℝ)).2 hq
  let y (i : Fin (finrank ℚ V)) : labelSpace U E :=
    ⟨t (algebraMap ℚ ℝ ∘ v i), by
      constructor
      · intro p hp
        change algebraMap ℚ ℝ ((b i : V).val p) = 0
        rw [(b i).property.1 p hp, map_zero]
      · intro e he
        change ∑ p ∈ e, algebraMap ℚ ℝ ((b i : V).val p) = 0
        rw [← map_sum, (b i).property.2 e he, map_zero]⟩
  have hy : LinearIndependent ℝ y := LinearIndependent.of_comp (labelSpace U E).subtype
    (hr.map' t.toLinearMap t.ker)
  simpa using hy.fintype_card_le_finrank

omit [DecidableEq α] in
/-- The values of a vector-valued zero-sum labeling span at most the scalar nullity
over the rationals. The target vector space may have arbitrary dimension. -/
theorem rational_span_le {V : Type*} [AddCommGroup V] [Module ℚ V]
    (U : Finset α) (E : Finset (Finset α)) (x : α → V)
    (support : ∀ p ∉ U, x p = 0) (zero : ∀ e ∈ E, ∑ p ∈ e, x p = 0) :
    finrank ℚ (Submodule.span ℚ (Set.range x)) ≤ finrank ℝ (labelSpace U E) := by
  let W := Submodule.span ℚ (Set.range x)
  let : Module.Finite ℚ W := Module.Finite.span_of_finite ℚ (Set.finite_range x)
  let g (p : α) : W := ⟨x p, Submodule.subset_span (Set.mem_range_self _)⟩
  have span : Submodule.span ℚ (Set.range g) = ⊤ := by
    apply Submodule.map_injective_of_injective W.subtype_injective
    rw [Submodule.map_top, Submodule.range_subtype, LinearMap.map_span, ← Set.range_comp]
    rfl
  let pull : Module.Dual ℚ W →ₗ[ℚ] rationalLabels U E :=
    { toFun := fun f => ⟨fun p => f (g p), by
        constructor
        · intro p hp
          have h : g p = 0 := Subtype.ext (support p hp)
          change f (g p) = 0
          rw [h, map_zero]
        · intro e he
          have h : ∑ p ∈ e, g p = 0 := by
            apply Subtype.ext
            simpa [g] using zero e he
          rw [← map_sum, h, map_zero]⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have inj : Function.Injective pull := by
    intro f h eq
    apply LinearMap.ext_on span
    rintro _ ⟨p,rfl⟩
    exact congrArg (fun k : rationalLabels U E => k.val p) eq
  have h := pull.finrank_le_finrank_of_injective inj
  rw [Subspace.dual_finrank_eq] at h
  exact h.trans (rational_dimension_le U E)

/-- On the dense core, all labels with a common four-term sum lie in a translate
of a rational subspace whose dimension is independent of the number of points. -/
theorem common_sum_span {V : Type*} [AddCommGroup V] [Module ℚ V]
    (U : Finset α) (E : Finset (Finset α)) (x : α → V) (c : V)
    (inside : ∀ e ∈ E, e ⊆ U) (four : ∀ e ∈ E, e.card = 4)
    (common : ∀ e ∈ E, ∑ p ∈ e, x p = c) :
    ∃ W : Submodule ℚ V, Module.Finite ℚ W ∧ finrank ℚ W ≤ finrank ℝ (labelSpace U E) ∧
      ∀ p ∈ U, x p - (1/4 : ℚ) • c ∈ W := by
  classical
  let z (p : α) := if p ∈ U then x p - (1/4 : ℚ) • c else 0
  have zero (e) (he : e ∈ E) : ∑ p ∈ e, z p = 0 := by
    calc
      _ = ∑ p ∈ e, (x p - (1/4 : ℚ) • c) := Finset.sum_congr rfl (fun p hp => by simp [z, inside e he hp])
      _ = 0 := by
        rw [Finset.sum_sub_distrib, common e he, Finset.sum_const, four e he]
        norm_num [← Nat.cast_smul_eq_nsmul ℚ 4, smul_smul]
  exact ⟨_, Module.Finite.span_of_finite ℚ (Set.finite_range z),
    rational_span_le U E z (fun p hp => by simp [z, hp]) zero,
    fun p hp => by simpa [z, hp] using (Submodule.subset_span (R := ℚ) (Set.mem_range_self (f := z) p))⟩

/-- A common-sum model with bounded intersections with low-rank rational affine
subspaces has four-edge density below 1/s once n exceeds 2sB/3. -/
theorem finite_rank_obstruction {V : Type*} [AddCommGroup V] [Module ℚ V]
    (E : Finset (Finset α)) (x : α → V) (c : V) (s B : ℕ) (pos : 0 < s)
    (density : (Fintype.card α)^2 ≤ s*E.card)
    (four : ∀ e ∈ E, e.card = 4) (lin : LinearEdges E) (common : ∀ e ∈ E, ∑ p ∈ e, x p = c)
    (bounded : ∀ (W : Submodule ℚ V), Module.Finite ℚ W → finrank ℚ W ≤ 6*s →
      ∀ T : Finset α, (∀ p ∈ T, x p - (1/4 : ℚ) • c ∈ W) → T.card ≤ B) :
    3*Fintype.card α ≤ 2*s*B := by
  obtain ⟨U, count, degrees, rank⟩ := dense_core_label_dimension E s pos density four lin
  let R := restricted E U
  have inside (e) (he : e ∈ R) : e ⊆ U := (Finset.mem_filter.mp he).2
  have sub : R ⊆ E := Finset.filter_subset _ _
  have each (e) (he : e ∈ R) := four e (sub he)
  have linear : LinearEdges R := fun _ he _ hf => lin (sub he) (sub hf)
  obtain ⟨W, finite, dim, contains⟩ :=
    common_sum_span U R x c inside each (fun e he => common e (sub he))
  have size := bounded W finite (dim.trans rank) U contains
  by_cases hU : U.Nonempty
  · obtain ⟨p,hp⟩ := hU
    have incl : neighbors R p ⊆ U := by
      intro q hq
      obtain ⟨e,he,h⟩ := Finset.mem_biUnion.mp hq
      exact inside e (Finset.mem_filter.mp he).1 (Finset.mem_erase.mp h).2
    have cells := (Finset.card_le_card incl).trans size
    rw [neighbors_card each linear] at cells
    calc
      3*Fintype.card α ≤ 3*(2*s*(star R p).card) := Nat.mul_le_mul_left _ (degrees p hp)
      _ = 2*s*(3*(star R p).card) := by ring
      _ ≤ 2*s*B := Nat.mul_le_mul_left _ cells
  · have h0 := Finset.not_nonempty_iff_eq_empty.mp hU
    have re : R = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have em := Finset.subset_empty.mp (h0 ▸ inside e he)
      simpa [em] using each e he
    change E.card ≤ 2*R.card at count
    rw [re, Finset.card_empty, Nat.mul_zero] at count
    have e0 := Nat.eq_zero_of_le_zero count
    rw [e0, Nat.mul_zero] at density
    have n0 : Fintype.card α = 0 := by nlinarith only [density]
    simp [n0]

section Plane

open EuclideanGeometry OMA.R_Erdos101_erdos_101_R1
open scoped Classical

abbrev Line := AffineSubspace ℝ ℝ²

def trace (S : Finset ℝ²) (L : Line) : Finset S :=
  Finset.univ.filter (fun p : S => p.val ∈ L)

private theorem trace_card {S : Finset ℝ²} {L : Line}
    (four : L ∈ linesWithPointsFor 4 (S : Set ℝ²)) : (trace S L).card = 4 := by
  rw [← four_points four]
  apply Finset.card_bij (fun (p : S) _ => (p : ℝ²))
  · intro p hp
    exact Finset.mem_filter.mpr ⟨p.property, (Finset.mem_filter.mp hp).2⟩
  · intro p _ q _ eq
    exact Subtype.ext eq
  · intro q hq
    obtain ⟨hs, hl⟩ := Finset.mem_filter.mp hq
    exact ⟨⟨q, hs⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩, rfl⟩

private theorem trace_equal {S : Finset ℝ²} {L M : Line}
    (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²)) (hM : M ∈ linesWithPointsFor 4 (S : Set ℝ²))
    {p q : S} (hp : p ∈ trace S L) (hp' : p ∈ trace S M)
    (hq : q ∈ trace S L) (hq' : q ∈ trace S M) (different : p ≠ q) : L = M := by
  have ne : p.val ≠ q.val := fun h => different (Subtype.ext h)
  exact (line_through hL (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 ne).symm.trans
    (line_through hM (Finset.mem_filter.mp hp').2 (Finset.mem_filter.mp hq').2 ne)

/-- Application to the original four-point lines with no algebraic restriction on the points. -/
theorem plane_core (S : Finset ℝ²) (A : Finset Line)
    (four : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²))
    (s : ℕ) (pos : 0 < s) (density : S.card ^ 2 ≤ s*A.card) :
    ∃ U : Finset S, A.card ≤ 2*(restricted (A.image (trace S)) U).card ∧
      (∀ p ∈ U, S.card ≤ 2*s*(star (restricted (A.image (trace S)) U) p).card) ∧
      finrank ℝ (labelSpace U (restricted (A.image (trace S)) U)) ≤ 6*s := by
  have inj : (A : Set Line).InjOn (trace S) := by
    intro L hL M hM eq
    have many := trace_card (four L hL)
    obtain ⟨p, q, hp, hq, ne⟩ := Finset.one_lt_card_iff.mp (show 1 < (trace S L).card by omega)
    exact trace_equal (four L hL) (four M hM) hp (eq ▸ hp) hq (eq ▸ hq) ne
  have count := Finset.card_image_of_injOn inj
  have size (e) (he : e ∈ A.image (trace S)) : e.card = 4 := by
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp he
    exact trace_card (four L hL)
  have lin : LinearEdges (A.image (trace S)) := by
    intro e he f hf p q hp hp' hq hq' ne
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hf
    exact congrArg (trace S) (trace_equal (four L hL) (four M hM) hp hp' hq hq' ne)
  simpa only [Fintype.card_coe, count] using
    dense_core_label_dimension (A.image (trace S)) s pos (by simpa only [Fintype.card_coe, count] using density) size lin

end Plane

end Erdos101IncidenceRank

/- Integer Sidon sets support dense linear four-uniform families of one common sum.
This is a counterexample to dropping real-plane realizability from the geometric question. -/

noncomputable section

namespace Erdos101SidonObstruction

open Finset Erdos101IncidenceRank

/-- The classical Erdős–Turán modular-parabola encoding. -/
def code (p : ℕ) (a : ZMod p) : ℕ := 2*p*a.val + (a^2).val

private theorem pair_moments {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {a b c d : K}
    (hs : a+b = c+d) (hq : a^2+b^2 = c^2+d^2) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have prod : a*b = c*d := by
    apply mul_left_cancel₀ h2
    calc
      2*(a*b) = (a+b)^2 - (a^2+b^2) := by ring
      _ = 2*(c*d) := by rw [hs, hq]; ring
  have zero : (a-c)*(a-d) = 0 := by
    calc
      _ = a^2 - (c+d)*a + c*d := by ring
      _ = 0 := by rw [← hs, ← prod]; ring
  rcases mul_eq_zero.mp zero with h | h
  · have eq := sub_eq_zero.mp h
    exact Or.inl ⟨eq, add_left_cancel (eq ▸ hs)⟩
  · have eq := sub_eq_zero.mp h
    rw [add_comm c d] at hs
    exact Or.inr ⟨eq, add_left_cancel (eq ▸ hs)⟩

/-- All unordered integer pair sums are distinct, including doubles. -/
theorem code_sidon (p : ℕ) [Fact p.Prime] (large : 3 ≤ p) {a b c d : ZMod p}
    (hs : code p a + code p b = code p c + code p d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have radix : 0 < 2*p := by omega
  have low (u v : ZMod p) : (u^2).val + (v^2).val < 2*p := by
    have := (u^2).val_lt; have := (v^2).val_lt; omega
  have split (u v : ZMod p) :
      code p u + code p v = (u^2).val+(v^2).val + (u.val+v.val)*(2*p) := by
    unfold code
    ring
  rw [split, split] at hs
  have high := congrArg (fun n : ℕ => n / (2*p)) hs
  simp only [Nat.add_mul_div_right _ _ radix, Nat.div_eq_of_lt (low _ _), zero_add] at high
  have lowEq : (a^2).val+(b^2).val = (c^2).val+(d^2).val := by
    rw [high] at hs
    exact Nat.add_right_cancel hs
  have reduce (u v : ZMod p) : ((u.val+v.val : ℕ) : ZMod p) = u+v := by simp
  have fieldSum := congrArg (fun n : ℕ => (n : ZMod p)) high
  have fieldSquare := congrArg (fun n : ℕ => (n : ZMod p)) lowEq
  have h2 : (2 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using
      (show ((2 : ℕ) : ZMod p) ≠ 0 from
        fun h => Nat.not_dvd_of_pos_of_lt (by decide) (by omega : 2 < p)
          ((ZMod.natCast_eq_zero_iff _ _).mp h))
  exact pair_moments h2 (by simpa only [reduce] using fieldSum)
    (by simpa only [reduce] using fieldSquare)

private theorem fiber_linear {α : Type*} [DecidableEq α] (f : α → ℕ)
    (sidon : ∀ {a b c d}, f a+f b=f c+f d → (a=c ∧ b=d) ∨ (a=d ∧ b=c))
    (E : Finset (Finset α)) (k : ℕ) (four : ∀ e ∈ E, e.card=4)
    (total : ∀ e ∈ E, ∑ a ∈ e, f a = k) : LinearEdges E := by
  intro e he g hg p q hpe hpg hqe hqg ne
  have split (t : Finset α) (ht : t ∈ E) (hp : p ∈ t) (hq : q ∈ t) :
      ∃ a b, t = insert q (insert p {a,b}) ∧ a ≠ b ∧ f a+f b + f p + f q = k := by
    have hp' : p ∈ t.erase q := Finset.mem_erase.mpr ⟨ne, hp⟩
    have nt : ((t.erase q).erase p).card = 2 := by
      simp [Finset.card_erase_of_mem hp', Finset.card_erase_of_mem hq, four t ht]
    obtain ⟨a,b,hab,hrest⟩ := Finset.card_eq_two.mp nt
    refine ⟨a,b,?_,hab,?_⟩
    · rw [← hrest, Finset.insert_erase hp', Finset.insert_erase hq]
    · have h₁ := Finset.sum_erase_add (t.erase q) f hp'
      have h₂ := Finset.sum_erase_add t f hq
      rw [hrest, Finset.sum_pair hab] at h₁
      rw [total t ht] at h₂
      omega
  obtain ⟨a,b,he',_,heq⟩ := split e he hpe hqe
  obtain ⟨c,d,hg',_,hgq⟩ := split g hg hpg hqg
  rcases sidon (show f a+f b = f c+f d by omega) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact he'.trans hg'.symm
  · rw [he', hg', Finset.pair_comm a b]

private theorem choose_bound {p : ℕ} (large : 6 ≤ p) : p^4 ≤ 192 * p.choose 4 := by
  have form := Nat.descFactorial_eq_factorial_mul_choose p 4
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, mul_one] at form
  norm_num at form
  have b1 : p ≤ 2*(p-1) := by omega
  have b2 : p ≤ 2*(p-2) := by omega
  have b3 : p ≤ 2*(p-3) := by omega
  have bound := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (le_refl p) b1) b2) b3
  nlinarith only [form, bound]

/-- For every sufficiently large prime p, at least p²/1728 four-subsets of a
p-element integer Sidon set have the same sum. -/
theorem dense_integer_model (p : ℕ) [Fact p.Prime] (large : 7 ≤ p) :
    ∃ (E : Finset (Finset (ZMod p))) (k : ℕ),
      p^2 ≤ 1728*E.card ∧ (∀ e ∈ E, e.card=4) ∧ LinearEdges E ∧
      (∀ e ∈ E, ∑ a ∈ e, code p a = k) ∧ Function.Injective (code p) := by
  classical
  let Q := (Finset.univ : Finset (ZMod p)).powersetCard 4
  let weight (e : Finset (ZMod p)) := ∑ a ∈ e, code p a
  let B := Finset.range (8*p^2+1)
  have size (a : ZMod p) : code p a ≤ 2*p^2 := by
    have hi : a.val+1 ≤ p := a.val_lt
    have lo : (a^2).val < p := (a^2).val_lt
    have h := Nat.mul_le_mul_left (2*p) hi
    dsimp only [code]
    nlinarith only [h, lo]
  have maps : Set.MapsTo weight (Q : Set (Finset (ZMod p))) (B : Set ℕ) := by
    intro e he
    have hc := (Finset.mem_powersetCard.mp he).2
    have h := Finset.sum_le_sum (s:=e) (fun a _ => size a)
    simp only [Finset.sum_const, smul_eq_mul, hc] at h
    change weight e ∈ Finset.range _
    rw [Finset.mem_range]
    change (∑ a ∈ e, code p a) < _
    nlinarith only [h]
  let fiber (k : ℕ) := Q.filter (weight · = k)
  obtain ⟨k, _, hk⟩ := B.exists_max_image (fun k => (fiber k).card)
    (by exact ⟨0, Finset.mem_range.mpr (by omega)⟩)
  have count : p.choose 4 ≤ (8*p^2+1)*(fiber k).card := calc
    p.choose 4 = Q.card := by simp [Q, Finset.card_powersetCard, ZMod.card]
    _ = ∑ t ∈ B, (fiber t).card := Finset.card_eq_sum_card_fiberwise maps
    _ ≤ ∑ _t ∈ B, (fiber k).card := Finset.sum_le_sum hk
    _ = _ := by simp [B]
  have ppos : 0 < p^2 := by positivity
  have slack : 8*p^2+1 ≤ 9*p^2 := by omega
  have count' := count.trans (Nat.mul_le_mul_right (fiber k).card slack)
  have product : p^2*p^2 ≤ p^2*(1728*(fiber k).card) := by
    nlinarith only [choose_bound (by omega : 6 ≤ p), Nat.mul_le_mul_left 192 count']
  have density := Nat.le_of_mul_le_mul_left product ppos
  have four (e) (he : e ∈ fiber k) := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
  have common (e) (he : e ∈ fiber k) := (Finset.mem_filter.mp he).2
  have sidon := @code_sidon p _ (by omega)
  refine ⟨fiber k, k, density, four, fiber_linear _ (fun h => sidon h) _ _ four common,
    common, ?_⟩
  intro a b h
  rcases sidon (show code p a+code p a=code p b+code p b by rw [h]) with hab | hab
  all_goals exact hab.1

theorem arbitrarily_large (N : ℕ) :
    ∃ (p : ℕ) (_ : Fact p.Prime), N ≤ p ∧
      ∃ (E : Finset (Finset (ZMod p))) (k : ℕ), p^2 ≤ 1728*E.card ∧
        (∀ e ∈ E, e.card=4) ∧ LinearEdges E ∧ (∀ e ∈ E, ∑ a ∈ e, code p a = k) ∧
        Function.Injective (code p) := by
  obtain ⟨p,hp,prime⟩ := Nat.exists_infinite_primes (max N 7)
  let : Fact p.Prime := ⟨prime⟩
  exact ⟨p, inferInstance, (le_max_left ..).trans hp, dense_integer_model p ((le_max_right ..).trans hp)⟩

end Erdos101SidonObstruction
