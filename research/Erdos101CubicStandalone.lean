import FormalConjectures.ErdosProblems.«101»
import Mathlib

/-! Four-point lines using three configuration points on y = x³. The final
theorem is Erdos101CubicLines.sparse_cubic_lines. The absolute bound holds
uniformly over all other real points. Adam McKenna's graph BSG proof and its
Apache license are retained below. Formalization of the cubic case: @ubuwaits. -/

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


/-
# Graph Balog–Szemerédi–Gowers theorem

The ten lemma declarations below are selected from Adam McKenna’s
LeanFormalizations.Combinatorics.Additive.BalogSzemerediGowers at commit
db02244c25aecd74eb96d9186c922387824c1258. The other declarations have been
omitted. The original license text follows the proof.

https://github.com/mysticflounder/lean-formalizations/blob/db02244c25aecd74eb96d9186c922387824c1258/lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean
-/

namespace Finset

open scoped Pointwise

/--
**Length-3 path count is dominated by a triple-rep count in `S × S × S`.**

For a bipartite graph `E ⊆ A ×ˢ B` over an additive commutative group, fix a
restricted sumset `S` containing all sums `p.1 + p.2` for `p ∈ E`. For any
`a, b ∈ G`, the number of length-3 paths `a — b₁ — a₁ — b` in `E` is at most
the number of triples `(s₁, s₂, s₃) ∈ S × S × S` with `s₁ - s₂ + s₃ = a + b`.

Proof: the map `(b₁, a₁) ↦ (a + b₁, a₁ + b₁, a₁ + b)` sends each path to a
triple in `S × S × S` (because each edge `(x, y) ∈ E` has `x + y ∈ S`) summing
to `a + b` under `s₁ - s₂ + s₃`. It is injective: `b₁` is recovered from
`(a + b₁) - a` (or equivalently from the first coordinate minus the constant `a`),
and `a₁` is recovered from the third coordinate as `(a₁ + b) - b`.

Used by `graph_balogSzemerediGowers_restricted_sumset` to bridge the pointwise
length-3 path count (supplied by `dense_bipartite_has_path3_rectangle` via
dependent random choice) to the triple-rep multiplicity hypothesis of
`restricted_sumset_via_multiplicity`. Tao-Vu, *Additive Combinatorics*, §6.4
(Cor. 6.20).
-/
lemma path3_count_le_triple_rep_count {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B S : Finset G) (E : Finset (G × G)) (hSdef : ∀ p ∈ E, p.1 + p.2 ∈ S)
    (a b : G) :
    (((B ×ˢ A).filter fun q : G × G ↦
        (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℕ)
    ≤ ((S ×ˢ S ×ˢ S).filter
        fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card := by
  -- Define the map (b₁, a₁) ↦ (a + b₁, a₁ + b₁, a₁ + b).
  set f : G × G → G × G × G := fun q ↦ (a + q.1, q.2 + q.1, q.2 + b) with hf_def
  set src : Finset (G × G) :=
    (B ×ˢ A).filter (fun q : G × G ↦
      (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E) with hsrc_def
  set tgt : Finset (G × G × G) :=
    (S ×ˢ S ×ˢ S).filter (fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b)
    with htgt_def
  apply Finset.card_le_card_of_injOn f
  · -- MapsTo: f sends src into tgt.
    intro q hq
    simp only [hsrc_def, Finset.coe_filter, Set.mem_ofPred_eq,
      Finset.mem_product] at hq
    obtain ⟨⟨_hq1B, _hq2A⟩, hEab1, hEa1b1, hEa1b⟩ := hq
    have hs1 : a + q.1 ∈ S := hSdef (a, q.1) hEab1
    have hs2 : q.2 + q.1 ∈ S := hSdef (q.2, q.1) hEa1b1
    have hs3 : q.2 + b ∈ S := hSdef (q.2, b) hEa1b
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, ?_⟩)
    · exact Finset.mem_product.mpr ⟨hs1, Finset.mem_product.mpr ⟨hs2, hs3⟩⟩
    · -- (a + b₁) - (a₁ + b₁) + (a₁ + b) = a + b.
      show (a + q.1) - (q.2 + q.1) + (q.2 + b) = a + b
      abel
  · -- InjOn: f is injective on src.
    intro q₁ _hq₁ q₂ _hq₂ hfeq
    -- f q₁ = f q₂ means (a + q₁.1, q₁.2 + q₁.1, q₁.2 + b) = (a + q₂.1, …, q₂.2 + b).
    -- Project out the first and third coordinates of the triple equality.
    have h1 : a + q₁.1 = a + q₂.1 := by
      have := congrArg Prod.fst hfeq
      simpa [hf_def] using this
    have h3 : q₁.2 + b = q₂.2 + b := by
      have := congrArg (fun p : G × G × G ↦ p.2.2) hfeq
      simpa [hf_def] using this
    have hq1eq : q₁.1 = q₂.1 := add_left_cancel h1
    have hq2eq : q₁.2 = q₂.2 := add_right_cancel h3
    exact Prod.ext hq1eq hq2eq

/--
**Restricted sumset upper bound via difference-set multiplicity.**

Let `A, B, S ⊆ G`. If every `(a, b) ∈ A × B` admits at least `M` triples
`(s₁, s₂, s₃) ∈ S × S × S` with `s₁ - s₂ + s₃ = a + b`, then
`M · |A + B| ≤ |S|³`.

Proof: the disjoint fibers `T_v := { (s₁, s₂, s₃) ∈ S × S × S : s₁ - s₂ + s₃ = v }`
indexed by `v ∈ A + B` each contain ≥ M triples and embed into `S × S × S`,
so `M · |A + B| ≤ ∑_{v ∈ A + B} |T_v| ≤ |S|³`.

This is the standard sumset bound used in the Tao-Vu / Petridis path-counting
proof of Balog-Szemerédi-Gowers: the triple-counting step inside the proof of
Tao-Vu, *Additive Combinatorics*, Theorem 2.29 (§6.4) — `#triples ≤ |A+B|³` —
not a separately numbered lemma.
-/
lemma restricted_sumset_via_multiplicity {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B S : Finset G) (M : ℕ) :
    (∀ a ∈ A, ∀ b ∈ B,
        M ≤ ((S ×ˢ S ×ˢ S).filter
          (fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b)).card) →
    M * (A + B).card ≤ S.card ^ 3 := by
  intro hcover
  -- Build the disjoint sets T_v = { (s₁,s₂,s₃) ∈ S × S × S : s₁ - s₂ + s₃ = v }.
  set T : G → Finset (G × G × G) :=
    fun v ↦ (S ×ˢ S ×ˢ S).filter (fun p ↦ p.1 - p.2.1 + p.2.2 = v) with hT_def
  -- Each fiber T_v contributes at least M to the sum over A + B.
  have hMle : ∀ v ∈ A + B, M ≤ (T v).card := by
    intro v hv
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hv
    -- Substitute a + b = v in the multiplicity hypothesis.
    have hM_at := hcover a ha b hb
    -- The triple subset T(a,b) has card ≥ M, and lies inside T v.
    set T_ab : Finset (G × G × G) :=
      (S ×ˢ S ×ˢ S).filter
        (fun p ↦ p.1 - p.2.1 + p.2.2 = a + b) with hTab_def
    have hT_ab_eq : T_ab = T v := by
      apply Finset.filter_congr
      intro p _
      constructor
      · intro h; rw [h, hab]
      · intro h; rw [h, ← hab]
    have : M ≤ T_ab.card := hM_at
    rw [hT_ab_eq] at this
    exact this
  -- The fibers cover disjointly inside S × S × S.
  -- Sum over v ∈ A + B of |T_v| ≤ |S × S × S| = |S|^3.
  have hdisj : ((A + B : Finset G) : Set G).PairwiseDisjoint T := by
    intro v _ w _ hvw
    refine Finset.disjoint_filter.mpr ?_
    intro p _ hpv hpw
    exact hvw (hpv ▸ hpw)
  have hSubset : ∀ v ∈ A + B, T v ⊆ S ×ˢ S ×ˢ S := by
    intro v _ p hp
    exact (Finset.mem_filter.mp hp).1
  -- Σ_v |T_v| = | ⋃_v T_v | ≤ |S × S × S|.
  have hSumCard :
      ∑ v ∈ A + B, (T v).card = ((A + B).biUnion T).card := by
    rw [Finset.card_biUnion]
    intro v hv w hw hvw
    have hpw : ((A + B : Finset G) : Set G).PairwiseDisjoint T := hdisj
    have hv' : v ∈ ((A + B : Finset G) : Set G) := hv
    have hw' : w ∈ ((A + B : Finset G) : Set G) := hw
    exact hpw hv' hw' hvw
  have hSumLeS3 : ∑ v ∈ A + B, (T v).card ≤ (S ×ˢ S ×ˢ S).card := by
    rw [hSumCard]
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨v, hv, hpv⟩ := hp
    exact hSubset v hv hpv
  -- Σ_v M ≤ Σ_v |T_v|.
  have hML : M * (A + B).card ≤ ∑ v ∈ A + B, (T v).card := by
    have hsum_le : ∑ _v ∈ A + B, M ≤ ∑ v ∈ A + B, (T v).card :=
      Finset.sum_le_sum (fun v hv ↦ hMle v hv)
    have hconst : ∑ _v ∈ A + B, M = (A + B).card * M := by
      rw [Finset.sum_const, smul_eq_mul]
    rw [hconst, mul_comm] at hsum_le
    exact hsum_le
  -- Combine.
  have hCard_S3 : (S ×ˢ S ×ˢ S).card = S.card ^ 3 := by
    rw [Finset.card_product, Finset.card_product, pow_succ, pow_succ, pow_one]
    ring
  calc M * (A + B).card
      ≤ ∑ v ∈ A + B, (T v).card := hML
    _ ≤ (S ×ˢ S ×ˢ S).card := hSumLeS3
    _ = S.card ^ 3 := hCard_S3

/--
**DRC step (Fox-Sudakov Lemma 5.1, "pair DRC").** For a bipartite graph
`F ⊆ X × Y` of density `c := |F| / (|X| · |Y|)` and any `0 < ε ≤ 1`, there
exists `U ⊆ X` such that
* `(c / 2) |X| ≤ |U|`, AND
* the number of ordered pairs `(x, x') ∈ U × U` with codegree
  `|N(x) ∩ N(x')| < (ε c² / 2) |Y|` is at most `ε |U|²`.

Proof (random choice): pick `v ∈ Y` uniformly and set `U := N(v) ⊆ X`. The
indicator `|U|² = (Σ_x [v ∈ N(x)])²` has expectation `≥ (E|U|)² = c² |X|²` by
Cauchy-Schwarz. For "bad" ordered pairs `(x, x')` with codegree
`< (ε c² / 2) |Y|`, the probability `P(v ∈ N(x) ∩ N(x'))` is `< ε c² / 2`, so
the expected number `Z` of bad pairs inside `U² ` is `< (ε c² / 2) |X|²`.
Hence `E[|U|² − Z/ε] ≥ (c² / 2) |X|²`, and there is a choice of `v` realizing
`|U|² ≥ (c² / 2) |X|²` (so `|U| ≥ (c / √2) |X| ≥ (c/2)|X|`) and
`Z ≤ ε |U|²`. Reference: Fox-Sudakov 2011, Lemma 5.1.
-/
lemma graph_pair_dependentRandomChoice {G : Type*} [DecidableEq G]
    (X Y : Finset G) (hX : X.Nonempty) (hY : Y.Nonempty)
    (F : Finset (G × G)) (hF_sub : F ⊆ X ×ˢ Y)
    (c : ℝ) (hc_pos : 0 < c) (_hc_le : c ≤ 1)
    (hF_dense : c * (X.card : ℝ) * (Y.card : ℝ) ≤ (F.card : ℝ))
    (ε : ℝ) (hε_pos : 0 < ε) (_hε_le : ε ≤ 1) :
    ∃ U : Finset G, U ⊆ X ∧
      (c / 2) * (X.card : ℝ) ≤ (U.card : ℝ) ∧
      (((U ×ˢ U).filter fun p : G × G ↦
        (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
          (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) <
        (ε * c ^ 2 / 2) * (Y.card : ℝ)).card : ℝ) ≤
      ε * (U.card : ℝ) ^ 2 := by
  have hX_real_pos : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast hX.card_pos
  have hY_real_pos : (0 : ℝ) < (Y.card : ℝ) := by exact_mod_cast hY.card_pos
  have hX_nn : (0 : ℝ) ≤ (X.card : ℝ) := le_of_lt hX_real_pos
  have hY_nn : (0 : ℝ) ≤ (Y.card : ℝ) := le_of_lt hY_real_pos
  -- `U(v) := { x ∈ X : (x, v) ∈ F }`.
  set U : G → Finset G := fun v ↦ X.filter (fun x ↦ (x, v) ∈ F) with hU_def
  -- "Bad" ordered pairs in `X × X` (independent of `v`).
  set Bad : Finset (G × G) := (X ×ˢ X).filter fun p : G × G ↦
    (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
      (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) <
    (ε * c ^ 2 / 2) * (Y.card : ℝ) with hBad_def
  -- The bad-in-U(v) finset is the restriction of `Bad` to `U(v) × U(v)`.
  set BadInV : G → Finset (G × G) := fun v ↦
    (U v ×ˢ U v).filter fun p : G × G ↦
      (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
        (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) <
      (ε * c ^ 2 / 2) * (Y.card : ℝ) with hBadInV_def
  -- Step 1: Σ_v |U(v)| = |F|.
  have hSum_U_card : ∑ v ∈ Y, ((U v).card : ℝ) = (F.card : ℝ) := by
    have hF_filter : F = (X ×ˢ Y).filter (fun p : G × G ↦ p ∈ F) := by
      ext p
      refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
      · exact Finset.mem_filter.mpr ⟨hF_sub hp, hp⟩
      · exact (Finset.mem_filter.mp hp).2
    have hF_card_eq : (F.card : ℝ) = ∑ v ∈ Y, ((U v).card : ℝ) := by
      conv_lhs => rw [hF_filter]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product_right]
      push_cast
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      simp only [U, Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast
      rfl
    linarith
  -- Step 2: Σ_v |U(v)|² = Σ_{(x,x') ∈ X × X} codeg(x, x').
  set codeg : G × G → ℝ := fun p : G × G ↦
    (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
      (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) with hcodeg_def
  have hcodeg_nn : ∀ p, 0 ≤ codeg p := fun p ↦ Nat.cast_nonneg _
  have hSum_U_sq : ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 = ∑ p ∈ X ×ˢ X, codeg p := by
    have hStep : ∀ v ∈ Y,
        ((U v).card : ℝ) ^ 2 = ((U v ×ˢ U v).card : ℝ) := by
      intro v _
      rw [Finset.card_product]
      push_cast; ring
    rw [Finset.sum_congr rfl hStep]
    -- Σ_v |U(v) × U(v)| = Σ_v #{(x, x') ∈ X × X : (x, v) ∈ F ∧ (x', v) ∈ F}.
    have hStep2 : ∀ v ∈ Y, ((U v ×ˢ U v).card : ℝ) =
        (((X ×ˢ X).filter (fun p : G × G ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F)).card : ℝ) := by
      intro v _
      have hSet : U v ×ˢ U v =
          (X ×ˢ X).filter (fun p : G × G ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F) := by
        ext p
        simp only [Finset.mem_product, Finset.mem_filter, U]
        tauto
      rw [hSet]
    rw [Finset.sum_congr rfl hStep2]
    -- Swap sums: Σ_v #{(x,x'): (x,v)∈F ∧ (x',v)∈F} = Σ_{(x,x')} codeg(x,x').
    rw [show (∑ v ∈ Y,
        (((X ×ˢ X).filter (fun p : G × G ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F)).card : ℝ)) =
        ∑ v ∈ Y, ∑ p ∈ X ×ˢ X,
          (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) from by
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast; rfl]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    -- codeg(p) = #{v ∈ Y : (p.1, v) ∈ F ∧ (p.2, v) ∈ F}.
    have hcodeg_eq : codeg p =
        ∑ v ∈ Y, (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) := by
      simp only [codeg]
      rw [show (Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩ (Y.filter (fun y ↦ (p.2, y) ∈ F))
          = Y.filter (fun y ↦ (p.1, y) ∈ F ∧ (p.2, y) ∈ F) from by
        ext y; simp only [Finset.mem_inter, Finset.mem_filter]; tauto]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast; rfl
    rw [hcodeg_eq]
  -- Step 3: Cauchy-Schwarz: |F|² ≤ |Y| · Σ_v |U(v)|².
  have hCS : (F.card : ℝ) ^ 2 ≤ (Y.card : ℝ) * ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Y (fun _ : G ↦ (1 : ℝ))
      (fun v ↦ ((U v).card : ℝ))
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    rw [hSum_U_card] at h
    exact h
  -- Step 4: c²|X|²|Y| ≤ Σ_v |U(v)|².
  have hSum_U_sq_lb : c ^ 2 * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ≤
      ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 := by
    have hc_nn : 0 ≤ c := le_of_lt hc_pos
    have hF_dense_nn : 0 ≤ c * (X.card : ℝ) * (Y.card : ℝ) :=
      mul_nonneg (mul_nonneg hc_nn hX_nn) hY_nn
    have hF_sq : (c * (X.card : ℝ) * (Y.card : ℝ)) ^ 2 ≤ (F.card : ℝ) ^ 2 :=
      pow_le_pow_left₀ hF_dense_nn hF_dense 2
    have hY_pos : 0 < (Y.card : ℝ) := hY_real_pos
    have h := le_trans hF_sq hCS
    have hrw : (c * (X.card : ℝ) * (Y.card : ℝ)) ^ 2 =
        (Y.card : ℝ) * (c ^ 2 * (X.card : ℝ) ^ 2 * (Y.card : ℝ)) := by ring
    rw [hrw] at h
    exact le_of_mul_le_mul_left h hY_pos
  -- Step 5: Σ_v |BadInV(v)| ≤ (ε c² / 2) |X|² |Y|.
  -- For each bad pair (x, x'), the number of v ∈ Y with x, x' ∈ U(v) equals
  -- codeg(x, x') ≤ (ε c² / 2)|Y|.
  have hSum_BadInV_le : ∑ v ∈ Y, ((BadInV v).card : ℝ) ≤
      (ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) := by
    -- Σ_v |BadInV(v)| = Σ_{p ∈ Bad} codeg(p).
    have hSwap : ∑ v ∈ Y, ((BadInV v).card : ℝ) = ∑ p ∈ Bad, codeg p := by
      -- Σ_v #{(x,x') ∈ U(v)² : p ∈ Bad}.
      have hStep : ∀ v ∈ Y, ((BadInV v).card : ℝ) =
          ∑ p ∈ Bad, (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) := by
        intro v _
        -- BadInV(v) = Bad.filter (p ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F).
        have hBadInV_eq : BadInV v =
            Bad.filter (fun p ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F) := by
          ext p
          simp only [BadInV, Bad, Finset.mem_filter, Finset.mem_product, U,
            Finset.mem_filter]
          tauto
        rw [hBadInV_eq, Finset.card_eq_sum_ones, Finset.sum_filter]
        push_cast; rfl
      rw [Finset.sum_congr rfl hStep]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      have hcodeg_eq : codeg p =
          ∑ v ∈ Y, (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) := by
        simp only [codeg]
        rw [show (Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩ (Y.filter (fun y ↦ (p.2, y) ∈ F))
            = Y.filter (fun y ↦ (p.1, y) ∈ F ∧ (p.2, y) ∈ F) from by
          ext y; simp only [Finset.mem_inter, Finset.mem_filter]; tauto]
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        push_cast; rfl
      rw [hcodeg_eq]
    rw [hSwap]
    -- Σ_{p ∈ Bad} codeg(p) ≤ |Bad| · (εc²/2)|Y| ≤ |X|² · (εc²/2)|Y|.
    have hBad_sub : Bad ⊆ X ×ˢ X := Finset.filter_subset _ _
    have hBad_card_le : (Bad.card : ℝ) ≤ ((X ×ˢ X).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hBad_sub
    have hXX_card : ((X ×ˢ X).card : ℝ) = (X.card : ℝ) ^ 2 := by
      rw [Finset.card_product]; push_cast; ring
    have hBad_card_le_X_sq : (Bad.card : ℝ) ≤ (X.card : ℝ) ^ 2 := by
      rw [← hXX_card]; exact hBad_card_le
    have hτ_nn : 0 ≤ (ε * c ^ 2 / 2) * (Y.card : ℝ) := by positivity
    have hPointwise : ∀ p ∈ Bad, codeg p ≤ (ε * c ^ 2 / 2) * (Y.card : ℝ) := by
      intro p hp
      simp only [Bad, Finset.mem_filter] at hp
      exact le_of_lt hp.2
    calc ∑ p ∈ Bad, codeg p
        ≤ ∑ _p ∈ Bad, (ε * c ^ 2 / 2) * (Y.card : ℝ) :=
          Finset.sum_le_sum hPointwise
      _ = (Bad.card : ℝ) * ((ε * c ^ 2 / 2) * (Y.card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (X.card : ℝ) ^ 2 * ((ε * c ^ 2 / 2) * (Y.card : ℝ)) :=
          mul_le_mul_of_nonneg_right hBad_card_le_X_sq hτ_nn
      _ = (ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) := by ring
  -- Step 6: Σ_v Φ(v) ≥ (c² / 2) |X|² |Y|, where Φ(v) = |U(v)|² − (1/ε) |BadInV(v)|.
  set Φ : G → ℝ := fun v ↦
    ((U v).card : ℝ) ^ 2 - (1 / ε) * ((BadInV v).card : ℝ) with hΦ_def
  have hε_inv_pos : (0 : ℝ) < 1 / ε := one_div_pos.mpr hε_pos
  have hε_inv_nn : (0 : ℝ) ≤ 1 / ε := le_of_lt hε_inv_pos
  have hSum_Φ_lb : (c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ≤ ∑ v ∈ Y, Φ v := by
    have hSplit : ∑ v ∈ Y, Φ v =
        (∑ v ∈ Y, ((U v).card : ℝ) ^ 2) - (1 / ε) * ∑ v ∈ Y, ((BadInV v).card : ℝ) := by
      simp only [Φ]
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hSplit]
    have h1 : c ^ 2 * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ≤ ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 :=
      hSum_U_sq_lb
    have h2 : (1 / ε) * ∑ v ∈ Y, ((BadInV v).card : ℝ) ≤
        (1 / ε) * ((ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hSum_BadInV_le hε_inv_nn
    have h2' : (1 / ε) * ((ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ)) =
        (c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) := by
      field_simp
    rw [h2'] at h2
    linarith
  -- Step 7: Extract a `v` with Φ(v) ≥ (c²/2)|X|².
  have hSum_Φ_const : (c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) =
      ∑ _v ∈ Y, (c ^ 2 / 2) * (X.card : ℝ) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hSum_Φ_const] at hSum_Φ_lb
  obtain ⟨v, _hvY, hΦv⟩ := Finset.exists_le_of_sum_le hY hSum_Φ_lb
  -- Step 8: For this `v`, derive |U(v)| ≥ (c/2)|X| and |BadInV(v)| ≤ ε|U(v)|².
  -- From hΦv : (c²/2)|X|² ≤ |U(v)|² - (1/ε)|BadInV(v)|.
  -- Since |BadInV(v)| ≥ 0, |U(v)|² ≥ (c²/2)|X|² ≥ (c/2)²|X|² (because c ≤ 1).
  have hU_card_nn : (0 : ℝ) ≤ ((U v).card : ℝ) := Nat.cast_nonneg _
  have hBadInV_nn : (0 : ℝ) ≤ ((BadInV v).card : ℝ) := Nat.cast_nonneg _
  have hU_sq_lb : (c ^ 2 / 2) * (X.card : ℝ) ^ 2 ≤ ((U v).card : ℝ) ^ 2 := by
    have h1 : (1 / ε) * ((BadInV v).card : ℝ) ≥ 0 :=
      mul_nonneg hε_inv_nn hBadInV_nn
    linarith
  have hc_sq_half_ge_c_half_sq : (c / 2) ^ 2 ≤ c ^ 2 / 2 := by
    have hc_nn : 0 ≤ c := le_of_lt hc_pos
    have : (c / 2) ^ 2 = c ^ 2 / 4 := by ring
    rw [this]
    -- c²/4 ≤ c²/2 ↔ c² ≥ 0.
    nlinarith [sq_nonneg c]
  have hU_card_lb : (c / 2) * (X.card : ℝ) ≤ ((U v).card : ℝ) := by
    have hc_half_X_nn : (0 : ℝ) ≤ (c / 2) * (X.card : ℝ) :=
      mul_nonneg (by linarith) hX_nn
    have hsq_chain : ((c / 2) * (X.card : ℝ)) ^ 2 ≤ ((U v).card : ℝ) ^ 2 := by
      calc ((c / 2) * (X.card : ℝ)) ^ 2
          = (c / 2) ^ 2 * (X.card : ℝ) ^ 2 := by ring
        _ ≤ (c ^ 2 / 2) * (X.card : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hc_sq_half_ge_c_half_sq (sq_nonneg _)
        _ ≤ ((U v).card : ℝ) ^ 2 := hU_sq_lb
    have hsqrt := Real.sqrt_le_sqrt hsq_chain
    rwa [Real.sqrt_sq hc_half_X_nn, Real.sqrt_sq hU_card_nn] at hsqrt
  -- |BadInV(v)| ≤ ε |U(v)|².
  have hBadInV_le : ((BadInV v).card : ℝ) ≤ ε * ((U v).card : ℝ) ^ 2 := by
    -- From hΦv: (c²/2)|X|² ≤ |U(v)|² − (1/ε)|BadInV(v)|.
    -- So (1/ε)|BadInV(v)| ≤ |U(v)|² − (c²/2)|X|² ≤ |U(v)|².
    have h1 : (1 / ε) * ((BadInV v).card : ℝ) ≤ ((U v).card : ℝ) ^ 2 := by
      have hX_sq_nn : 0 ≤ (c ^ 2 / 2) * (X.card : ℝ) ^ 2 := by positivity
      linarith
    have h2 : ((BadInV v).card : ℝ) ≤ ε * ((U v).card : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (le_of_lt hε_pos)
      have heq : ε * ((1 / ε) * ((BadInV v).card : ℝ)) = ((BadInV v).card : ℝ) := by
        field_simp
      rw [heq] at this
      exact this
    exact h2
  -- Step 9: Package the witness.
  refine ⟨U v, ?_, hU_card_lb, ?_⟩
  · simp only [U]; exact Finset.filter_subset _ _
  · exact hBadInV_le

/--
**High-degree subset density.** For `E ⊆ A ×ˢ B` with `|A| = |B| = n` and
`δ n² ≤ |E|`, the subset `A₁ := { a ∈ A : (δ/2) n ≤ |Nb(a)| }` has
`(δ/2) n ≤ |A₁|` and `e(A₁, B) ≥ (δ/2) n²` (where `e(A₁, B) := |E ∩ (A₁ ×ˢ B)|`).

Standard rare/popular split: rows with `|Nb(a)| < (δ/2) n` contribute
`< (δ/2) n²` edges, so the popular rows in `A₁` contribute `≥ (δ/2) n²`.
Combined with the pointwise bound `|Nb(a)| ≤ n` on `A₁`, this gives
`|A₁| · n ≥ (δ/2) n²`, i.e. `|A₁| ≥ (δ/2) n`.
-/
lemma graph_high_degree_subset_lb {G : Type*} [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (_hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    (δ / 2) * (A.card : ℝ) ≤
      ((A.filter (fun a ↦
        (δ / 2) * (B.card : ℝ) ≤
          ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ))).card : ℝ) ∧
    (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤
      ((E.filter (fun p : G × G ↦
        (δ / 2) * (B.card : ℝ) ≤
          ((B.filter (fun b ↦ (p.1, b) ∈ E)).card : ℝ))).card : ℝ) := by
  classical
  set rowDeg : G → ℕ := fun a ↦ (B.filter (fun b ↦ (a, b) ∈ E)).card with hrowDeg_def
  set Apop : Finset G := A.filter (fun a ↦ (δ / 2) * (B.card : ℝ) ≤ (rowDeg a : ℝ))
    with hApop_def
  set Epop : Finset (G × G) := E.filter (fun p : G × G ↦
    (δ / 2) * (B.card : ℝ) ≤ ((B.filter (fun b ↦ (p.1, b) ∈ E)).card : ℝ))
    with hEpop_def
  have hApop_sub : Apop ⊆ A := Finset.filter_subset _ _
  have hEpop_sub : Epop ⊆ E := Finset.filter_subset _ _
  have hA_pos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hA_nn : (0 : ℝ) ≤ (A.card : ℝ) := le_of_lt hA_pos
  have hBcard_eq : (B.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hAB.symm
  have hB_pos : (0 : ℝ) < (B.card : ℝ) := by rw [hBcard_eq]; exact hA_pos
  have hB_nn : (0 : ℝ) ≤ (B.card : ℝ) := le_of_lt hB_pos
  have hrowDeg_le : ∀ a, rowDeg a ≤ B.card := fun a ↦
    Finset.card_le_card (Finset.filter_subset _ _)
  have hrowDeg_le_R : ∀ a, (rowDeg a : ℝ) ≤ (B.card : ℝ) := fun a ↦ by
    exact_mod_cast hrowDeg_le a
  have hSumRow : ∑ a ∈ A, (rowDeg a : ℕ) = E.card := by
    have step1 : ∀ a, rowDeg a = ∑ b ∈ B, (if (a, b) ∈ E then 1 else 0) := fun a ↦ by
      simp only [rowDeg, Finset.card_eq_sum_ones, Finset.sum_filter]
    have step2 : ∑ a ∈ A, rowDeg a = ∑ p ∈ A ×ˢ B, (if p ∈ E then 1 else 0) := by
      simp_rw [step1, Finset.sum_product]
    have step3 :
        ∑ p ∈ A ×ˢ B, (if p ∈ E then 1 else 0) = ((A ×ˢ B).filter (· ∈ E)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have step4 : (A ×ˢ B).filter (· ∈ E) = E := by
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hE_sub h, h⟩⟩
    rw [step2, step3, step4]
  have hSumRow_real : ∑ a ∈ A, (rowDeg a : ℝ) = (E.card : ℝ) := by
    have h := hSumRow
    have hcast : ((∑ a ∈ A, rowDeg a : ℕ) : ℝ) = (E.card : ℝ) := by exact_mod_cast h
    push_cast at hcast; exact hcast
  have hsplit_A : ∑ a ∈ A, (rowDeg a : ℝ) =
      (∑ a ∈ Apop, (rowDeg a : ℝ)) + ∑ a ∈ A \ Apop, (rowDeg a : ℝ) := by
    rw [← Finset.sum_sdiff hApop_sub]; ring
  have hrare : ∑ a ∈ A \ Apop, (rowDeg a : ℝ) ≤
      ((A \ Apop).card : ℝ) * ((δ / 2) * (B.card : ℝ)) := by
    rw [show ((A \ Apop).card : ℝ) * ((δ / 2) * (B.card : ℝ)) =
              ∑ _a ∈ A \ Apop, ((δ / 2) * (B.card : ℝ)) by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a ha ↦ ?_
    rw [Finset.mem_sdiff, hApop_def, Finset.mem_filter] at ha
    have hnot := ha.2
    by_contra hgt
    push Not at hgt
    exact hnot ⟨ha.1, le_of_lt hgt⟩
  have hAdiff_le_A : ((A \ Apop).card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := A) (t := Apop))
  have hδ2B_nn : 0 ≤ (δ / 2) * (B.card : ℝ) := by positivity
  have hrare' : ∑ a ∈ A \ Apop, (rowDeg a : ℝ) ≤ (A.card : ℝ) * ((δ / 2) * (B.card : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hAdiff_le_A hδ2B_nn
    linarith [hrare]
  have hSumApop : ∑ a ∈ Apop, (rowDeg a : ℕ) = Epop.card := by
    have step1 : ∀ a, rowDeg a = ∑ b ∈ B, (if (a, b) ∈ E then 1 else 0) := fun a ↦ by
      simp only [rowDeg, Finset.card_eq_sum_ones, Finset.sum_filter]
    have step2 : ∑ a ∈ Apop, rowDeg a = ∑ p ∈ Apop ×ˢ B, (if p ∈ E then 1 else 0) := by
      simp_rw [step1, Finset.sum_product]
    have step3 : ∑ p ∈ Apop ×ˢ B, (if p ∈ E then 1 else 0) =
        ((Apop ×ˢ B).filter (· ∈ E)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have step4 : (Apop ×ˢ B).filter (· ∈ E) = Epop := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, hEpop_def, hApop_def, hrowDeg_def]
      constructor
      · rintro ⟨⟨⟨hp1A, hp1pop⟩, _hp2⟩, hpE⟩
        exact ⟨hpE, hp1pop⟩
      · rintro ⟨hpE, hpop⟩
        have hpAB := hE_sub hpE
        rw [Finset.mem_product] at hpAB
        exact ⟨⟨⟨hpAB.1, hpop⟩, hpAB.2⟩, hpE⟩
    rw [step2, step3, step4]
  have hSumApop_real : ∑ a ∈ Apop, (rowDeg a : ℝ) = (Epop.card : ℝ) := by
    have h := hSumApop
    have hcast : ((∑ a ∈ Apop, rowDeg a : ℕ) : ℝ) = (Epop.card : ℝ) := by exact_mod_cast h
    push_cast at hcast; exact hcast
  have hE_dense' : δ * (A.card : ℝ) * (B.card : ℝ) ≤ ∑ a ∈ A, (rowDeg a : ℝ) := by
    rw [hSumRow_real]; exact hE_dense
  have hEpop_lb : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ (Epop.card : ℝ) := by
    have : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ ∑ a ∈ Apop, (rowDeg a : ℝ) := by
      have hδ_split : δ * (A.card : ℝ) * (B.card : ℝ) =
          (δ / 2) * (A.card : ℝ) * (B.card : ℝ) + (A.card : ℝ) * ((δ / 2) * (B.card : ℝ)) := by
        ring
      linarith [hE_dense', hsplit_A, hrare', hδ_split]
    linarith [this, hSumApop_real]
  have hApop_sum_ub : ∑ a ∈ Apop, (rowDeg a : ℝ) ≤ (Apop.card : ℝ) * (B.card : ℝ) := by
    rw [show (Apop.card : ℝ) * (B.card : ℝ) = ∑ _a ∈ Apop, (B.card : ℝ) by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a _ ↦ hrowDeg_le_R a
  have hApop_lb : (δ / 2) * (A.card : ℝ) ≤ (Apop.card : ℝ) := by
    have h1 : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ (Apop.card : ℝ) * (B.card : ℝ) := by
      calc (δ / 2) * (A.card : ℝ) * (B.card : ℝ)
          ≤ (Epop.card : ℝ) := hEpop_lb
        _ = ∑ a ∈ Apop, (rowDeg a : ℝ) := hSumApop_real.symm
        _ ≤ (Apop.card : ℝ) * (B.card : ℝ) := hApop_sum_ub
    exact le_of_mul_le_mul_right h1 hB_pos
  exact ⟨hApop_lb, hEpop_lb⟩

/--
**Markov refinement helper.** Given `U` and a bad-pair count bound
`#{(a, a') ∈ U×U : codeg_E(a, a') < τ} ≤ κ · |U|²`, produce
`A' ⊆ U` with `|A'| ≥ |U|/2` (when `κ ≤ 1/4`) such that for every
`a ∈ A'` the bad-partner count `#{a' ∈ U : codeg_E(a, a') < τ}` is
`≤ 2κ · |U|`.  Used inside `graph_dependentRandomChoice_payoff_pointwise_witness` with
`κ := δ/16`, giving `2κ = δ/8`.
-/
private lemma graph_dependentRandomChoice_markov_refinement {G : Type*} [DecidableEq G]
    (B U : Finset G) (E : Finset (G × G)) (τ : ℝ) (κ : ℝ)
    (hκ_pos : 0 < κ) (hUpos : (0 : ℝ) < (U.card : ℝ))
    (hbadCount : (((U ×ˢ U).filter fun p : G × G ↦
        ((B.filter fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
      ≤ κ * (U.card : ℝ) ^ 2) :
    ∃ A' : Finset G, A' ⊆ U ∧
      (1 - 1 / 2) * (U.card : ℝ) ≤ (A'.card : ℝ) ∧
      (∀ a ∈ A',
        ((U.filter fun a₁ ↦
          ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
          ≤ 2 * κ * (U.card : ℝ)) := by
  classical
  -- Bad partners of `a` in U.
  set badPartner : G → Finset G := fun a ↦
    U.filter (fun a₁ ↦
      ((B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card : ℝ) < τ)
    with hbadPartner_def
  set A' : Finset G := U.filter (fun a ↦
    ((badPartner a).card : ℝ) ≤ 2 * κ * (U.card : ℝ)) with hA'_def
  have hA'_sub : A' ⊆ U := Finset.filter_subset _ _
  -- Sum of bad-partner cards equals bad-pair count (fiber over first coord).
  set badPairs : Finset (G × G) := (U ×ˢ U).filter (fun p : G × G ↦
    ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ)
    with hbadPairs_def
  have hbadSum : (badPairs.card : ℝ) = ∑ a ∈ U, ((badPartner a).card : ℝ) := by
    have hN : badPairs.card = ∑ a ∈ U, (badPartner a).card := by
      rw [hbadPairs_def, hbadPartner_def]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have hcast : ((∑ a ∈ U, (badPartner a).card : ℕ) : ℝ) = (badPairs.card : ℝ) := by
      exact_mod_cast hN.symm
    push_cast at hcast; linarith
  -- Markov lower bound on Σ over U \ A'.
  have hsum_split :
      ∑ a ∈ U, ((badPartner a).card : ℝ) =
        (∑ a ∈ A', ((badPartner a).card : ℝ)) +
        ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := by
    rw [← Finset.sum_sdiff hA'_sub]; ring
  have hsum_diff_ge :
      ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) ≤
        ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := by
    rw [show ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) =
            ∑ _a ∈ U \ A', (2 * κ * (U.card : ℝ)) from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a ha ↦ ?_
    rw [Finset.mem_sdiff, hA'_def, Finset.mem_filter] at ha
    have hnot := ha.2
    by_contra hge
    push Not at hge
    exact hnot ⟨ha.1, le_of_lt hge⟩
  have hpartner_nn : ∀ a, 0 ≤ ((badPartner a).card : ℝ) := fun a ↦ Nat.cast_nonneg _
  have hsum_A'_nn : 0 ≤ ∑ a ∈ A', ((badPartner a).card : ℝ) :=
    Finset.sum_nonneg fun a _ ↦ hpartner_nn a
  -- Combine: |U\A'| · 2κ|U| ≤ Σ over U ≤ |badPairs| ≤ κ|U|².  Hence |U\A'| ≤ |U|/2.
  have hdiff_card_le : ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) ≤
      κ * (U.card : ℝ) ^ 2 := by
    calc ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ))
        ≤ ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := hsum_diff_ge
      _ ≤ ∑ a ∈ U, ((badPartner a).card : ℝ) := by linarith
      _ = (badPairs.card : ℝ) := hbadSum.symm
      _ ≤ κ * (U.card : ℝ) ^ 2 := hbadCount
  have hcoeff_pos : 0 < 2 * κ * (U.card : ℝ) := by positivity
  have hdiff_le_half : ((U \ A').card : ℝ) ≤ (U.card : ℝ) / 2 := by
    have heq : κ * (U.card : ℝ) ^ 2 = ((U.card : ℝ) / 2) * (2 * κ * (U.card : ℝ)) := by ring
    rw [heq] at hdiff_card_le
    exact le_of_mul_le_mul_right hdiff_card_le hcoeff_pos
  have hA'_card_real : ((U \ A').card : ℝ) + (A'.card : ℝ) = (U.card : ℝ) := by
    have h : (U \ A').card + A'.card = U.card := Finset.card_sdiff_add_card_eq_card hA'_sub
    exact_mod_cast h
  have hA'_lb : (U.card : ℝ) / 2 ≤ (A'.card : ℝ) := by linarith
  refine ⟨A', hA'_sub, ?_, ?_⟩
  · linarith
  · intro a ha
    rw [hA'_def, Finset.mem_filter] at ha
    exact ha.2

/--
**Popular columns helper.** For `U ⊆ A` with row degree `≥ ρ · |B|` for every
`a ∈ U` (in the sense of `|{b ∈ B : (a, b) ∈ E}| ≥ ρ · |B|`), the rare/popular
split on columns produces `B' ⊆ B` of cardinality `≥ (ρ/2) · |B|` such that
every `b ∈ B'` has `|{a ∈ U : (a, b) ∈ E}| ≥ (ρ/2) · |U|`.
-/
private lemma graph_dependentRandomChoice_popular_columns {G : Type*} [DecidableEq G]
    (A B : Finset G) (hAB : A.card = B.card)
    (E : Finset (G × G)) (_hE_sub : E ⊆ A ×ˢ B)
    (U : Finset G) (hU_sub : U ⊆ A)
    (hU_pos : (0 : ℝ) < (U.card : ℝ))
    (ρ : ℝ) (hρ_pos : 0 < ρ) (_hρ_le_one : ρ ≤ 1)
    (hrowDeg_lb : ∀ a ∈ U, ρ * (B.card : ℝ) ≤
      ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ)) :
    ∃ B' : Finset G, B' ⊆ B ∧
      (ρ / 2) * (B.card : ℝ) ≤ (B'.card : ℝ) ∧
      (∀ b ∈ B', (ρ / 2) * (U.card : ℝ) ≤
        ((U.filter fun a ↦ (a, b) ∈ E).card : ℝ)) := by
  classical
  -- |B| > 0 since |B| = |A| and U ⊆ A nonempty.
  have hBcard_nat : B.card = A.card := hAB.symm
  have hUcard_le_A : (U.card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hU_sub
  have hA_pos : (0 : ℝ) < (A.card : ℝ) := lt_of_lt_of_le hU_pos hUcard_le_A
  have hB_pos : (0 : ℝ) < (B.card : ℝ) := by
    have : (B.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hBcard_nat
    rw [this]; exact hA_pos
  -- Column count.
  set colCount : G → ℕ := fun b ↦ (U.filter (fun a ↦ (a, b) ∈ E)).card with hcolCount_def
  set B' : Finset G := B.filter (fun b ↦ (ρ / 2) * (U.card : ℝ) ≤ (colCount b : ℝ)) with hB'_def
  have hB'_sub : B' ⊆ B := Finset.filter_subset _ _
  -- Edge count from U: Σ_a∈U rowDeg(a) ≥ ρ|U||B|.  Also = Σ_b colCount b.
  set rowDeg : G → ℕ := fun a ↦ (B.filter (fun b ↦ (a, b) ∈ E)).card with hrowDeg_def
  -- Σ over U of rowDeg = Σ over B of colCount: both count {(a, b) ∈ U × B : (a, b) ∈ E}.
  have hSwap : ∑ a ∈ U, (rowDeg a : ℕ) = ∑ b ∈ B, (colCount b : ℕ) := by
    have hrowDeg_eq : ∀ a, rowDeg a = ∑ b ∈ B, (if (a, b) ∈ E then 1 else 0) := fun a ↦ by
      simp only [rowDeg, Finset.card_eq_sum_ones, Finset.sum_filter]
    have hcolCount_eq : ∀ b, colCount b = ∑ a ∈ U, (if (a, b) ∈ E then 1 else 0) := fun b ↦ by
      simp only [colCount, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp_rw [hrowDeg_eq, hcolCount_eq]
    rw [Finset.sum_comm]
  have hSwap_real :
      ∑ a ∈ U, (rowDeg a : ℝ) = ∑ b ∈ B, (colCount b : ℝ) := by
    have : ((∑ a ∈ U, rowDeg a : ℕ) : ℝ) = ((∑ b ∈ B, colCount b : ℕ) : ℝ) := by
      exact_mod_cast hSwap
    push_cast at this; exact this
  -- Σ_{a ∈ U} rowDeg(a) ≥ ρ|U||B|.
  have hrow_sum_lb : ρ * (U.card : ℝ) * (B.card : ℝ) ≤ ∑ a ∈ U, (rowDeg a : ℝ) := by
    have hsum : ∑ _a ∈ U, ρ * (B.card : ℝ) ≤ ∑ a ∈ U, (rowDeg a : ℝ) :=
      Finset.sum_le_sum fun a haU ↦ hrowDeg_lb a haU
    have hconst : ∑ _a ∈ U, ρ * (B.card : ℝ) = (U.card : ℝ) * (ρ * (B.card : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst] at hsum
    linarith
  have hcol_sum_lb : ρ * (U.card : ℝ) * (B.card : ℝ) ≤ ∑ b ∈ B, (colCount b : ℝ) := by
    rw [← hSwap_real]; exact hrow_sum_lb
  -- Rare columns contribute < (ρ/2)|U| each.
  have hrare_col : ∑ b ∈ B \ B', (colCount b : ℝ) ≤
      ((B \ B').card : ℝ) * ((ρ / 2) * (U.card : ℝ)) := by
    rw [show ((B \ B').card : ℝ) * ((ρ / 2) * (U.card : ℝ)) =
            ∑ _b ∈ B \ B', ((ρ / 2) * (U.card : ℝ)) from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun b hb ↦ ?_
    rw [Finset.mem_sdiff, hB'_def, Finset.mem_filter] at hb
    have hnot := hb.2
    by_contra hgt
    push Not at hgt
    exact hnot ⟨hb.1, le_of_lt hgt⟩
  have hrare_col' : ∑ b ∈ B \ B', (colCount b : ℝ) ≤
      (B.card : ℝ) * ((ρ / 2) * (U.card : ℝ)) := by
    have h : ((B \ B').card : ℝ) ≤ (B.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := B) (t := B'))
    have hnn : 0 ≤ (ρ / 2) * (U.card : ℝ) := by
      have : 0 ≤ ρ / 2 := by linarith
      exact mul_nonneg this (le_of_lt hU_pos)
    have := mul_le_mul_of_nonneg_right h hnn
    linarith
  -- Split column-sum.
  have hcol_split : ∑ b ∈ B, (colCount b : ℝ) =
      (∑ b ∈ B', (colCount b : ℝ)) + ∑ b ∈ B \ B', (colCount b : ℝ) := by
    rw [← Finset.sum_sdiff hB'_sub]; ring
  have hpop_col_lb : (ρ / 2) * (U.card : ℝ) * (B.card : ℝ) ≤
      ∑ b ∈ B', (colCount b : ℝ) := by
    nlinarith [hcol_split, hcol_sum_lb, hrare_col']
  -- Σ over B' of colCount ≤ |B'| · |U|.
  have hcolCount_le : ∀ b, (colCount b : ℝ) ≤ (U.card : ℝ) := fun b ↦ by
    have h : (colCount b : ℕ) ≤ U.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    exact_mod_cast h
  have hpop_col_ub : ∑ b ∈ B', (colCount b : ℝ) ≤ (B'.card : ℝ) * (U.card : ℝ) := by
    rw [show (B'.card : ℝ) * (U.card : ℝ) = ∑ _b ∈ B', (U.card : ℝ) from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    exact Finset.sum_le_sum fun b _ ↦ hcolCount_le b
  -- Divide through by |U|.
  have hB'_lb : (ρ / 2) * (B.card : ℝ) ≤ (B'.card : ℝ) := by
    have hchain : (ρ / 2) * (U.card : ℝ) * (B.card : ℝ) ≤
        (B'.card : ℝ) * (U.card : ℝ) := le_trans hpop_col_lb hpop_col_ub
    have hrew : (ρ / 2) * (U.card : ℝ) * (B.card : ℝ) =
        ((ρ / 2) * (B.card : ℝ)) * (U.card : ℝ) := by ring
    rw [hrew] at hchain
    exact le_of_mul_le_mul_right hchain hU_pos
  have hpop_col_prop : ∀ b ∈ B', (ρ / 2) * (U.card : ℝ) ≤ (colCount b : ℝ) := by
    intro b hb
    rw [hB'_def, Finset.mem_filter] at hb
    exact hb.2
  exact ⟨B', hB'_sub, hB'_lb, hpop_col_prop⟩

/--
**Witness for the DRC pointwise payoff (steps 1-4).** Internal helper.
Composes `graph_high_degree_subset_lb` (rare/popular row split) with
`graph_pair_dependentRandomChoice` (Fox-Sudakov 5.1 pair-DRC) and a Markov + rare/popular
column split.  Returns the four pieces needed by the pointwise count
step: a "core" set `U ⊆ A`, the "non-bad" refinement `A' ⊆ U`, the
"popular column" refinement `B' ⊆ B`, and the codegree threshold
`τ ≥ 0` that interpolates the bad-partner bound for `a ∈ A'` and the
final `(δ⁵/2¹²)|A|²` count.

The arithmetic identity `(δ⁵/2¹²)|A|² ≤ (δ/8)|U| · τ` is established
here (using `m := |Apop|`-relative density and `|U| · τ`-style
cancellation) so the count helper need not redo it.
-/
private lemma graph_dependentRandomChoice_payoff_pointwise_witness {G : Type*} [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ U A' B' : Finset G, ∃ τ : ℝ,
      U ⊆ A ∧ A' ⊆ U ∧ B' ⊆ B ∧
      0 ≤ τ ∧
      (δ / 4) * (A.card : ℝ) ≤ (U.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤ (δ / 8) * (U.card : ℝ) * τ ∧
      (∀ a ∈ A',
        ((U.filter fun a₁ ↦
          ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
          ≤ (δ / 8) * (U.card : ℝ)) ∧
      (∀ b ∈ B',
        (δ / 4) * (U.card : ℝ) ≤
          ((U.filter fun a₁ ↦ (a₁, b) ∈ E).card : ℝ)) := by
  classical
  -- Cardinality positivity.
  have hApos : 0 < A.card := hA.card_pos
  have hA_real_pos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hApos
  have hA_nn : (0 : ℝ) ≤ (A.card : ℝ) := le_of_lt hA_real_pos
  have hBcard_nat : B.card = A.card := hAB.symm
  have hB_real_eq : (B.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hBcard_nat
  have hB_real_pos : (0 : ℝ) < (B.card : ℝ) := by rw [hB_real_eq]; exact hA_real_pos
  have hB : B.Nonempty := by
    rw [← Finset.card_pos]; rw [hBcard_nat]; exact hApos
  -- δ bounds.
  have hδ_nn : 0 ≤ δ := le_of_lt hδ_pos
  -- Step 1: apply rare/popular row split.
  obtain ⟨hApop_lb, hEpop_lb⟩ :=
    graph_high_degree_subset_lb δ hδ_pos hδ_le A B hA hAB E hE_sub hE_dense
  -- Define A₁ (popular rows) and E₁ (edges with popular first coord).
  set A₁ : Finset G := A.filter (fun a ↦
    (δ / 2) * (B.card : ℝ) ≤ ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ)) with hA₁_def
  have hA₁_sub : A₁ ⊆ A := Finset.filter_subset _ _
  -- |A₁| ≥ (δ/2)|A| > 0, so A₁ is nonempty.
  have hA₁_card_pos : (0 : ℝ) < (A₁.card : ℝ) := by
    have : 0 < (δ / 2) * (A.card : ℝ) := by positivity
    linarith
  have hA₁_card_pos_nat : 0 < A₁.card := by exact_mod_cast hA₁_card_pos
  have hA₁_ne : A₁.Nonempty := Finset.card_pos.mp hA₁_card_pos_nat
  set E₁ : Finset (G × G) := E.filter (fun p ↦ p.1 ∈ A₁) with hE₁_def
  have hE₁_sub_E : E₁ ⊆ E := Finset.filter_subset _ _
  -- E₁ characterisation: edges with first coord in A₁.
  have hE₁_iff : ∀ p, p ∈ E₁ ↔ p ∈ E ∧ p.1 ∈ A₁ := fun p ↦ by
    simp [E₁, Finset.mem_filter]
  -- E₁ ⊆ A₁ ×ˢ B.
  have hE₁_sub : E₁ ⊆ A₁ ×ˢ B := by
    intro p hp
    rw [hE₁_iff] at hp
    obtain ⟨hpE, hpA₁⟩ := hp
    have hpAB := hE_sub hpE
    rw [Finset.mem_product] at hpAB ⊢
    exact ⟨hpA₁, hpAB.2⟩
  -- The edge count for E₁: this matches the popular-edge form of `graph_high_degree_subset_lb`.
  -- |E₁| = |E.filter (popular first coord)| ≥ (δ/2)·|A|·|B|.
  have hE₁_card_lb : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ (E₁.card : ℝ) := by
    -- The popular-edge filter from `graph_high_degree_subset_lb` matches E₁:
    --   E.filter (popular p.1) = E.filter (p.1 ∈ A₁)
    have hfilter_eq :
        E.filter (fun p : G × G ↦
          (δ / 2) * (B.card : ℝ) ≤ ((B.filter (fun b ↦ (p.1, b) ∈ E)).card : ℝ)) = E₁ := by
      ext p
      simp only [E₁, Finset.mem_filter, hA₁_def]
      constructor
      · rintro ⟨hpE, hpop⟩
        have hpAB := hE_sub hpE
        rw [Finset.mem_product] at hpAB
        exact ⟨hpE, hpAB.1, hpop⟩
      · rintro ⟨hpE, _, hpop⟩
        exact ⟨hpE, hpop⟩
    rw [← hfilter_eq]; exact hEpop_lb
  -- Step 2: invoke graph_pair_dependentRandomChoice on (A₁, B, E₁) with density c₀ = (δ/2)|A|/|A₁|.
  set m : ℝ := (A₁.card : ℝ) with hm_def
  have hm_pos : 0 < m := hA₁_card_pos
  have hm_le_A : m ≤ (A.card : ℝ) := by
    have : (A₁.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card hA₁_sub
    exact this
  -- Density c₀ for pair-DRC: c₀ * m * |B| = (δ/2) * |A| * |B|.
  set c₀ : ℝ := (δ / 2) * (A.card : ℝ) / m with hc₀_def
  have hc₀_pos : 0 < c₀ := by
    have hnum : 0 < (δ / 2) * (A.card : ℝ) := by positivity
    exact div_pos hnum hm_pos
  -- c₀ ≤ 1, because (δ/2)|A| ≤ m (= |A₁|).
  have hc₀_le_one : c₀ ≤ 1 := by
    rw [hc₀_def]
    rw [div_le_one hm_pos]
    exact hApop_lb
  -- c₀ * |A₁| = (δ/2) * |A|.
  have hc₀_mul_m : c₀ * m = (δ / 2) * (A.card : ℝ) := by
    rw [hc₀_def]; field_simp
  -- Density hypothesis for graph_pair_dependentRandomChoice.
  have hF_dense_drc : c₀ * (A₁.card : ℝ) * (B.card : ℝ) ≤ (E₁.card : ℝ) := by
    have : c₀ * (A₁.card : ℝ) * (B.card : ℝ) = (δ / 2) * (A.card : ℝ) * (B.card : ℝ) := by
      rw [show (A₁.card : ℝ) = m from rfl]; rw [hc₀_mul_m]
    rw [this]; exact hE₁_card_lb
  -- ε = δ/16.
  set ε : ℝ := δ / 16 with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; positivity
  have hε_le_one : ε ≤ 1 := by
    rw [hε_def]; linarith
  -- Invoke graph_pair_dependentRandomChoice.
  obtain ⟨U, hU_sub_A₁, hU_card_lb_drc, hbad_card_le⟩ :=
    graph_pair_dependentRandomChoice A₁ B hA₁_ne hB E₁ hE₁_sub c₀ hc₀_pos hc₀_le_one hF_dense_drc
      ε hε_pos hε_le_one
  have hU_sub : U ⊆ A := hU_sub_A₁.trans hA₁_sub
  -- (c₀/2) * |A₁| = (δ/4) * |A|.
  have hU_card_lb : (δ / 4) * (A.card : ℝ) ≤ (U.card : ℝ) := by
    have heq : c₀ / 2 * (A₁.card : ℝ) = (δ / 4) * (A.card : ℝ) := by
      have := hc₀_mul_m
      rw [show (A₁.card : ℝ) = m from rfl]
      linarith
    linarith [hU_card_lb_drc, heq]
  have hU_card_pos : (0 : ℝ) < (U.card : ℝ) := by
    have : 0 < (δ / 4) * (A.card : ℝ) := by positivity
    linarith
  have hU_card_pos_nat : 0 < U.card := by exact_mod_cast hU_card_pos
  have hU_ne : U.Nonempty := Finset.card_pos.mp hU_card_pos_nat
  -- τ_drc = (ε * c₀²/2) * |B|.  Goal `τ := τ_drc`.
  set τ : ℝ := (ε * c₀ ^ 2 / 2) * (B.card : ℝ) with hτ_def
  have hτ_nn : 0 ≤ τ := by
    rw [hτ_def]
    have h1 : 0 ≤ ε * c₀ ^ 2 / 2 := by positivity
    have h2 : (0 : ℝ) ≤ (B.card : ℝ) := le_of_lt hB_real_pos
    exact mul_nonneg h1 h2
  -- The arithmetic identity: (δ⁵/2¹²)|A|² ≤ (δ/8) · |U| · τ.
  -- We use: (δ/8)|U| ≥ (δ/8)(δ/4)|A| = δ²/32 · |A|, and τ ≥ ?
  -- Key: τ = (δ/16)·c₀²/2·|B| = (δ/32)·c₀²·|A|.
  -- And c₀² · |A₁|² = (δ/2)² · |A|², so c₀² = δ²|A|²/(4·m²).
  -- Hence τ · m² = (δ/32) · (δ²/4) · |A|³ = δ³|A|³/128.
  -- Want: (δ/8)|U| · τ ≥ (δ⁵/2¹²)|A|².
  -- Using |U| ≥ (δ/4)|A| and τ ≥ (δ³/2⁷)|A| (since m ≤ |A|, so |A|³/m² ≥ |A|).
  have hτ_lb : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) ≤ τ := by
    -- τ = (δ/16) · c₀² / 2 · |B| = (δ/32) · c₀² · |A|.
    -- c₀ · m = (δ/2)|A|, so c₀² · m² = δ²|A|²/4.
    -- τ · m² = (δ/32) · δ²|A|²/4 · |A| = δ³|A|³/128.
    -- τ = δ³|A|³ / (128 m²).  Since m ≤ |A|: τ ≥ δ³|A|/128.
    have hc₀sq : c₀ ^ 2 * m ^ 2 = ((δ / 2) * (A.card : ℝ)) ^ 2 := by
      have h := hc₀_mul_m
      calc c₀ ^ 2 * m ^ 2 = (c₀ * m) ^ 2 := by ring
        _ = ((δ / 2) * (A.card : ℝ)) ^ 2 := by rw [h]
    have hm_sq_pos : 0 < m ^ 2 := by positivity
    have hm_sq_le : m ^ 2 ≤ (A.card : ℝ) ^ 2 := by
      have hm_nn : 0 ≤ m := le_of_lt hm_pos
      exact pow_le_pow_left₀ hm_nn hm_le_A 2
    -- τ * m² = (ε * c₀²/2) * |B| * m² = (ε / 2) * (c₀² · m²) * |B|
    --        = (δ / 32) * ((δ/2)|A|)² * |A| = δ³|A|³/128.
    have hτ_m_sq : τ * m ^ 2 = δ ^ 3 / 128 * (A.card : ℝ) ^ 3 := by
      have : τ = (ε * c₀ ^ 2 / 2) * (B.card : ℝ) := hτ_def
      rw [this, hB_real_eq, hε_def]
      have : (δ / 16 * c₀ ^ 2 / 2) * (A.card : ℝ) * m ^ 2
          = (δ / 32) * (c₀ ^ 2 * m ^ 2) * (A.card : ℝ) := by ring
      rw [this, hc₀sq]
      ring
    -- (δ³/2⁷)|A| · m² ≤ τ · m² ↔ (δ³/2⁷)|A| ≤ τ if m² > 0.
    -- Use (δ³/2⁷)|A| · m² ≤ (δ³/2⁷)|A| · |A|² = (δ³/128)|A|³ = τ · m².
    have hineq : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * m ^ 2 ≤ τ * m ^ 2 := by
      rw [hτ_m_sq]
      have : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * m ^ 2 ≤
            (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * (A.card : ℝ) ^ 2 := by
        have hLcoeff_nn : 0 ≤ (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left hm_sq_le hLcoeff_nn
      have heq2 : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * (A.card : ℝ) ^ 2 =
          δ ^ 3 / 128 * (A.card : ℝ) ^ 3 := by ring
      linarith
    exact le_of_mul_le_mul_right hineq hm_sq_pos
  -- Now establish the bound (δ⁵/2¹²)|A|² ≤ (δ/8)|U| · τ via
  -- (δ/8)|U| ≥ (δ/8)(δ/4)|A| = δ²/32 · |A| and τ ≥ δ³/128 · |A|, product ≥ δ⁵|A|²/2¹².
  have hUτ_bound : (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤ (δ / 8) * (U.card : ℝ) * τ := by
    have h1 : (δ / 8) * ((δ / 4) * (A.card : ℝ)) ≤ (δ / 8) * (U.card : ℝ) := by
      have h8 : (0 : ℝ) ≤ δ / 8 := by linarith
      exact mul_le_mul_of_nonneg_left hU_card_lb h8
    have h2 : (δ / 8) * ((δ / 4) * (A.card : ℝ)) * ((δ ^ 3 / 2 ^ 7) * (A.card : ℝ)) ≤
        (δ / 8) * (U.card : ℝ) * τ := by
      have hLHS_nn : 0 ≤ (δ / 8) * ((δ / 4) * (A.card : ℝ)) := by positivity
      have hLHS_nn' : 0 ≤ (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) := by positivity
      exact mul_le_mul h1 hτ_lb hLHS_nn' (le_trans hLHS_nn h1)
    have hrew : (δ / 8) * ((δ / 4) * (A.card : ℝ)) * ((δ ^ 3 / 2 ^ 7) * (A.card : ℝ)) =
        (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 := by ring
    linarith
  -- Bad-pair count in U using the E-codegree.  It is bounded by the E₁-bad count from
  -- graph_pair_dependentRandomChoice, since codeg_E ≥ codeg_{E₁}.
  have hbadCountE : (((U ×ˢ U).filter fun p : G × G ↦
      ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ).card : ℝ)
    ≤ ε * (U.card : ℝ) ^ 2 := by
    -- Pointwise: codeg_E(p) < τ ⟹ codeg_{E₁}(p) ≤ codeg_E(p) < τ.
    have hbadE_sub : ((U ×ˢ U).filter fun p : G × G ↦
          ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ) ⊆
        ((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) < τ) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      refine ⟨hp.1, ?_⟩
      have hsub : (B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
                  (B.filter (fun y ↦ (p.2, y) ∈ E₁)) ⊆
                  B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E) := by
        intro y hy
        simp only [Finset.mem_inter, Finset.mem_filter] at hy
        simp only [Finset.mem_filter]
        exact ⟨hy.1.1, hE₁_sub_E hy.1.2, hE₁_sub_E hy.2.2⟩
      have hcard : (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
          (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) ≤
          ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      linarith [hp.2]
    have h := Finset.card_le_card hbadE_sub
    have hreal : (((U ×ˢ U).filter fun p : G × G ↦
          ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ).card : ℝ) ≤
        (((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) < τ).card : ℝ) := by
      exact_mod_cast h
    -- `τ = (ε * c₀ ^ 2 / 2) * (B.card : ℝ)` by definition; substitute.
    have hfilter_eq :
        ((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) < τ) =
        ((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) <
          (ε * c₀ ^ 2 / 2) * (B.card : ℝ)) := by rfl
    rw [hfilter_eq] at hreal
    linarith
  -- Apply Markov refinement helper.
  obtain ⟨A', hA'_sub_U, hA'_half, hA'_prop⟩ :=
    graph_dependentRandomChoice_markov_refinement (G := G) B U E τ ε hε_pos hU_card_pos hbadCountE
  -- `hA'_half`: (1 - 1/2) * |U| ≤ |A'|, i.e. |U|/2 ≤ |A'|.
  -- `hA'_prop`: ∀ a ∈ A', ((badPartner a).card : ℝ) ≤ 2ε|U| = (δ/8)|U|.
  -- So we get the (δ/8)|U| bound directly: 2 * (δ/16) = δ/8.
  have htwo_eps : (2 : ℝ) * ε = δ / 8 := by rw [hε_def]; ring
  have hA'_prop_clean : ∀ a ∈ A',
      ((U.filter fun a₁ ↦
        ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
        ≤ (δ / 8) * (U.card : ℝ) := by
    intro a ha
    have h := hA'_prop a ha
    have hrew : (2 * ε * (U.card : ℝ)) = (δ / 8) * (U.card : ℝ) := by
      rw [show (2 * ε * (U.card : ℝ)) = 2 * ε * (U.card : ℝ) from rfl, htwo_eps]
    linarith [hrew]
  -- |A'| ≥ |U|/2 ≥ (δ/8)|A|.
  have hA'_card_lb : (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) := by
    have h1 : (δ / 8) * (A.card : ℝ) ≤ (U.card : ℝ) / 2 := by linarith [hU_card_lb]
    have : (1 - 1 / 2) * (U.card : ℝ) = (U.card : ℝ) / 2 := by ring
    linarith [hA'_half, this]
  -- Step 4: popular columns via `graph_dependentRandomChoice_popular_columns`.
  -- Row-degree lower bound for a ∈ U (which is ⊆ A₁): rowDeg_E(a) ≥ (δ/2)|B|.
  have hrowDeg_lb : ∀ a ∈ U, (δ / 2) * (B.card : ℝ) ≤
      ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ) := by
    intro a haU
    have haA₁ : a ∈ A₁ := hU_sub_A₁ haU
    rw [hA₁_def, Finset.mem_filter] at haA₁
    exact haA₁.2
  -- δ/2 > 0 and ≤ 1 since δ ≤ 1.
  have hρ_pos : (0 : ℝ) < δ / 2 := by positivity
  have hρ_le : δ / 2 ≤ 1 := by linarith
  obtain ⟨B', hB'_sub, hB'_lb_drc, hpopCol⟩ :=
    graph_dependentRandomChoice_popular_columns (G := G) A B hAB E hE_sub U hU_sub hU_card_pos
      (δ / 2) hρ_pos hρ_le hrowDeg_lb
  -- (δ/2)/2 = δ/4. So |B'| ≥ (δ/4)|B| = (δ/4)|A| ≥ (δ/8)|A|.
  have hB'_card_lb : (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) := by
    have h3 : (δ / 8) * (A.card : ℝ) ≤ (δ / 4) * (A.card : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hA_nn
    have hquarter_eq : (δ / 2) / 2 * (B.card : ℝ) = (δ / 4) * (A.card : ℝ) := by
      rw [hB_real_eq]; ring
    linarith [hB'_lb_drc, hquarter_eq]
  -- Popular-column property: for b ∈ B', (δ/4)|U| ≤ |{a ∈ U : (a, b) ∈ E}|.
  have hpopCol_clean : ∀ b ∈ B', (δ / 4) * (U.card : ℝ) ≤
      ((U.filter fun a ↦ (a, b) ∈ E).card : ℝ) := by
    intro b hb
    have h := hpopCol b hb
    have hrew : (δ / 2) / 2 * (U.card : ℝ) = (δ / 4) * (U.card : ℝ) := by ring
    linarith [hrew]
  refine ⟨U, A', B', τ, hU_sub, hA'_sub_U, hB'_sub, hτ_nn, hU_card_lb,
    hA'_card_lb, hB'_card_lb, hUτ_bound, hA'_prop_clean, hpopCol_clean⟩

/--
**Pointwise count helper (step 5).** Given the witness from
`graph_dependentRandomChoice_payoff_pointwise_witness`, partition the path-3 Finset
`(B ×ˢ A).filter ((a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E)` by the
second coordinate `q.2 = a₁ ∈ U`. For `a₁` that is a popular neighbour of
`b` and a non-bad partner of `a`, the corresponding fiber has cardinality
`≥ τ`. There are at least `(δ/8)|U|` such `a₁`, giving the final bound
`(δ/8)|U| · τ ≥ (δ⁵/2¹²)|A|²`.
-/
private lemma graph_dependentRandomChoice_payoff_pointwise_count {G : Type*} [DecidableEq G]
    (δ : ℝ) (A B : Finset G) (E : Finset (G × G)) (U A' B' : Finset G) (τ : ℝ)
    (hU_sub : U ⊆ A) (_hA'_sub_U : A' ⊆ U) (_hB'_sub : B' ⊆ B)
    (hτ_nn : 0 ≤ τ)
    (hUτ_bound : (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤ (δ / 8) * (U.card : ℝ) * τ)
    (hbadPartner : ∀ a ∈ A',
      ((U.filter fun a₁ ↦
        ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
        ≤ (δ / 8) * (U.card : ℝ))
    (hpopCol : ∀ b ∈ B',
      (δ / 4) * (U.card : ℝ) ≤
        ((U.filter fun a₁ ↦ (a₁, b) ∈ E).card : ℝ))
    (a : G) (ha : a ∈ A') (b : G) (hb : b ∈ B') :
    (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤
      (((B ×ˢ A).filter fun q : G × G ↦
        (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
  classical
  -- "Popular neighbours of b in U" and "non-bad partners of a in U".
  set Nb : Finset G := U.filter (fun a₁ ↦ (a₁, b) ∈ E) with hNb_def
  set Bad : Finset G := U.filter (fun a₁ ↦
    ((B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card : ℝ) < τ) with hBad_def
  have hNb_lb : (δ / 4) * (U.card : ℝ) ≤ (Nb.card : ℝ) := hpopCol b hb
  have hBad_ub : (Bad.card : ℝ) ≤ (δ / 8) * (U.card : ℝ) := hbadPartner a ha
  -- Good := Nb \ Bad.  |Good| ≥ |Nb| - |Bad| ≥ (δ/8)|U|.
  set Good : Finset G := Nb \ Bad with hGood_def
  have hGood_sub_Nb : Good ⊆ Nb := Finset.sdiff_subset
  have hNb_sub_U : Nb ⊆ U := Finset.filter_subset _ _
  have hGood_sub_U : Good ⊆ U := hGood_sub_Nb.trans hNb_sub_U
  have hGood_card_lb : (δ / 8) * (U.card : ℝ) ≤ (Good.card : ℝ) := by
    -- |Nb \ Bad| ≥ |Nb| - |Bad|, via Nb ⊆ (Nb \ Bad) ∪ Bad.
    have hUnion : Nb ⊆ (Nb \ Bad) ∪ Bad := by
      intro x hx
      by_cases hxBad : x ∈ Bad
      · exact Finset.mem_union_right _ hxBad
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxBad⟩)
    have h1 : Nb.card ≤ ((Nb \ Bad) ∪ Bad).card := Finset.card_le_card hUnion
    have h2 : ((Nb \ Bad) ∪ Bad).card ≤ (Nb \ Bad).card + Bad.card :=
      Finset.card_union_le _ _
    have hreal : (Nb.card : ℝ) ≤ ((Nb \ Bad).card : ℝ) + (Bad.card : ℝ) := by
      have : (Nb.card : ℕ) ≤ (Nb \ Bad).card + Bad.card := le_trans h1 h2
      exact_mod_cast this
    have hGood_card_eq : ((Nb \ Bad).card : ℝ) = (Good.card : ℝ) := by
      rw [hGood_def]
    linarith [hreal, hNb_lb, hBad_ub, hGood_card_eq]
  -- For each a₁ ∈ Good: (a₁, b) ∈ E and codeg_E(a, a₁) ≥ τ.
  have hGood_codeg : ∀ a₁ ∈ Good,
      τ ≤ ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) ∧ (a₁, b) ∈ E := by
    intro a₁ ha₁
    rw [hGood_def, Finset.mem_sdiff, hNb_def, Finset.mem_filter, hBad_def,
      Finset.mem_filter] at ha₁
    obtain ⟨⟨ha₁U, ha₁bE⟩, hnotBad⟩ := ha₁
    refine ⟨?_, ha₁bE⟩
    by_contra hlt
    push Not at hlt
    exact hnotBad ⟨ha₁U, hlt⟩
  -- Path Finset of interest.
  set paths : Finset (G × G) := (B ×ˢ A).filter fun q : G × G ↦
    (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E with hpaths_def
  -- Fiber over the second coordinate: for each a₁, witness pairs (b₁, a₁).
  set fiber : G → Finset (G × G) := fun a₁ ↦
    (B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).image (fun b₁ ↦ (b₁, a₁))
    with hfiber_def
  -- fiber a₁ has the same cardinality as the inner filter (image of an injection).
  have hfiber_card : ∀ a₁,
      (fiber a₁).card = (B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card := by
    intro a₁
    rw [hfiber_def]
    apply Finset.card_image_of_injective
    intro x y hxy
    exact (Prod.mk.injEq _ _ _ _).mp hxy |>.1
  -- For a₁ ∈ Good, fiber a₁ ⊆ paths.
  have hfiber_sub : ∀ a₁ ∈ Good, fiber a₁ ⊆ paths := by
    intro a₁ ha₁ p hp
    rw [hfiber_def, Finset.mem_image] at hp
    obtain ⟨b₁, hb₁, hpeq⟩ := hp
    rw [Finset.mem_filter] at hb₁
    obtain ⟨hb₁B, habE, ha₁b₁E⟩ := hb₁
    have ha₁U : a₁ ∈ U := hGood_sub_U ha₁
    have ha₁A : a₁ ∈ A := hU_sub ha₁U
    obtain ⟨_, ha₁bE⟩ := hGood_codeg a₁ ha₁
    rw [hpaths_def, Finset.mem_filter, Finset.mem_product]
    rw [← hpeq]
    exact ⟨⟨hb₁B, ha₁A⟩, habE, ha₁b₁E, ha₁bE⟩
  -- Pairwise disjointness of fibers (different a₁ → different second coord).
  have hfiber_disjoint : (Good : Set G).PairwiseDisjoint fiber := by
    intro x _ y _ hxy
    refine Finset.disjoint_left.mpr ?_
    intro p hpx hpy
    rw [hfiber_def, Finset.mem_image] at hpx hpy
    obtain ⟨bx, _, hpx_eq⟩ := hpx
    obtain ⟨by_, _, hpy_eq⟩ := hpy
    have hsnd : p.2 = x := by rw [← hpx_eq]
    have hsnd' : p.2 = y := by rw [← hpy_eq]
    exact hxy (hsnd.symm.trans hsnd')
  -- |⋃_{a₁ ∈ Good} fiber a₁| = Σ_{a₁ ∈ Good} |fiber a₁|.
  have hbiUnion_card : (Good.biUnion fiber).card = ∑ a₁ ∈ Good, (fiber a₁).card := by
    exact Finset.card_biUnion (fun x hx y hy hxy ↦ hfiber_disjoint hx hy hxy)
  -- The biUnion is contained in paths.
  have hbiUnion_sub : Good.biUnion fiber ⊆ paths := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨a₁, ha₁, hp⟩ := hp
    exact hfiber_sub a₁ ha₁ hp
  have hcard_path_lb : (∑ a₁ ∈ Good, (fiber a₁).card : ℕ) ≤ paths.card := by
    calc (∑ a₁ ∈ Good, (fiber a₁).card : ℕ)
        = (Good.biUnion fiber).card := hbiUnion_card.symm
      _ ≤ paths.card := Finset.card_le_card hbiUnion_sub
  have hcard_path_lb_real : (∑ a₁ ∈ Good, ((fiber a₁).card : ℝ)) ≤ (paths.card : ℝ) := by
    have h : ((∑ a₁ ∈ Good, (fiber a₁).card : ℕ) : ℝ) ≤ (paths.card : ℝ) := by
      exact_mod_cast hcard_path_lb
    push_cast at h; exact h
  -- Σ_{a₁ ∈ Good} |fiber a₁| ≥ |Good| · τ.
  have hsum_lb : (Good.card : ℝ) * τ ≤ ∑ a₁ ∈ Good, ((fiber a₁).card : ℝ) := by
    rw [show (Good.card : ℝ) * τ = ∑ _a₁ ∈ Good, τ from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a₁ ha₁ ↦ ?_
    have hcard := hfiber_card a₁
    have hcodeg := (hGood_codeg a₁ ha₁).1
    have : ((fiber a₁).card : ℝ) =
        ((B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card : ℝ) := by
      exact_mod_cast hcard
    rw [this]
    exact hcodeg
  -- Combine: paths ≥ |Good| · τ ≥ (δ/8)|U| · τ ≥ (δ⁵/2¹²)|A|².
  have hGood_τ : (δ / 8) * (U.card : ℝ) * τ ≤ (Good.card : ℝ) * τ :=
    mul_le_mul_of_nonneg_right hGood_card_lb hτ_nn
  linarith [hUτ_bound, hGood_τ, hsum_lb, hcard_path_lb_real]

/--
**DRC payoff: pointwise path-3 count.** Given the pair-DRC witness `U ⊆ A`
(from `graph_pair_dependentRandomChoice`), define the "non-bad" set
`A' := { a ∈ U : few a' ∈ U with codegree < (δ³/2⁷) n }` and the "popular"
set `B' := { b ∈ B : (δ/4) |U| ≤ |N_U(b)| }`. For `a ∈ A'`, `b ∈ B'`, the
length-3 path count `P(a, b) ≥ (δ⁵ / 2¹²) n²`.

Proof: of the `(δ/4)|U|` vertices in `U ∩ N(b)`, at most `(δ/8)|U|` are bad
partners of `a`, leaving `≥ (δ/8)|U|` non-bad partners `a₁`. Each non-bad
partner has `|N(a) ∩ N(a₁)| ≥ (δ³/2⁷) n` choices of `b₁`. Total:
`P(a, b) ≥ (δ/8)|U| · (δ³/2⁷) n ≥ (δ/8)(δ/4)n · (δ³/128) n = (δ⁵/2¹²) n²`.
-/
lemma graph_dependentRandomChoice_payoff_pointwise {G : Type*} [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      ∀ a ∈ A', ∀ b ∈ B',
        (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
  classical
  obtain ⟨U, A', B', τ, hU_sub, hA'_sub_U, hB'_sub, hτ_nn, _hU_card, hA'_card,
    hB'_card, hUτ_bound, hbadPartner, hpopCol⟩ :=
    graph_dependentRandomChoice_payoff_pointwise_witness δ hδ_pos hδ_le A B hA hAB E hE_sub hE_dense
  refine ⟨A', B', hA'_sub_U.trans hU_sub, hB'_sub, hA'_card, hB'_card, ?_⟩
  intro a ha b hb
  exact graph_dependentRandomChoice_payoff_pointwise_count δ A B E U A' B' τ hU_sub hA'_sub_U hB'_sub
    hτ_nn hUτ_bound hbadPartner hpopCol a ha b hb

/--
**Dense bipartite graph has a pointwise length-3 path rectangle (Fox-Sudakov
Lemma 5.2 / Tao-Vu Cor. 6.20).** Given a bipartite graph `E ⊆ A ×ˢ B` of density
`≥ δ` (with `|A| = |B|`), there exist subsets `A' ⊆ A`, `B' ⊆ B` of cardinality
`≥ (δ / 8) · |A|` such that *every* pair `(a, b) ∈ A' × B'` admits at least
`(δ^5 / 2^12) · |A|^2` length-3 paths `a — b₁ — a₁ — b` in `E`. The path
multiplicity is **pointwise**, not averaged — this is what makes the bound
linear when fed into the triple-rep count.

Proof: dependent random choice (as implemented). (1) Restrict to the popular
rows `A₁ := {a : deg_E(a) ≥ (δ/2)|B|}` and edges `E₁` out of them; `E₁` still
has density `≥ δ/2`. (2) Pair-DRC (Fox-Sudakov 5.1): pick a *column* vertex
`v ∈ B` uniformly and set the core `U := N_{E₁}(v) ⊆ A₁ ⊆ A`; by Cauchy-Schwarz
a positive fraction of `v` give both `|U| ≥ (δ/4)|A|` and few "bad" ordered
pairs `(a, a') ∈ U × U` of low codegree `|N(a) ∩ N(a')| < τ`. (3) `A' ⊆ U` is
the Markov refinement to vertices with `≤ (δ/8)|U|` bad partners in `U`; (4)
`B' ⊆ B` is the popular columns, those with `≥ (δ/4)|U|` neighbors inside `U`.
The high pointwise codegree on `A'` combined with `B'`'s density in `U` forces
`≥ (δ⁵/2¹²)|A|²` length-3 paths through every `(a, b) ∈ A' × B'`. References:
Fox-Sudakov, *Dependent Random Choice* (2011), Lemma 5.2; Tao-Vu, *Additive
Combinatorics*, §6.4, Cor. 6.20.
-/
lemma dense_bipartite_has_path3_rectangle {G : Type*} [AddCommGroup G] [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      ∀ a ∈ A', ∀ b ∈ B',
        (δ^5 / 2^12) * (A.card : ℝ)^2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
  classical
  -- The Fox-Sudakov DRC payload is packaged in `graph_dependentRandomChoice_payoff_pointwise`,
  -- which assembles `graph_pair_dependentRandomChoice`, `graph_high_degree_subset_lb`, and the
  -- final pointwise path-3 count step (see those lemmas for the breakdown).
  exact graph_dependentRandomChoice_payoff_pointwise δ hδ_pos hδ_le A B hA hAB E hE_sub hE_dense

end Finset

/-
Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/

/-
# Rich monotone graphs on a finite ordered grid

Divide each coordinate range into blocks of fixed length. A monotone graph
meets few blocks, so a rich graph has many blocks containing any prescribed
fixed number of its points. A bound on the number of graphs through those
points gives a linear bound for the family. For a fractional linear map
two monotone pieces and three-point multiplicity suffice.
-/

namespace Erdos101OrderedGrid

open scoped Classical

abbrev Pos := ℕ × ℕ

def grid (n : ℕ) : Finset Pos := Finset.range n ×ˢ Finset.range n
def block (k : ℕ) (p : Pos) : Pos := (p.1/k,p.2/k)
def fiber (G : Finset Pos) (k : ℕ) (c : Pos) := G.filter (fun p => block k p = c)
def occupied (G : Finset Pos) (k : ℕ) := G.image (block k)
def good (G : Finset Pos) (k r : ℕ) := (occupied G k).filter (fun c => r ≤ (fiber G k c).card)

/-- Increasing coordinate pairs when `up` is true, decreasing pairs otherwise. -/
def aligned (up : Bool) (p q : Pos) : Prop :=
  p.1 ≤ q.1 ∧ (if up then p.2 ≤ q.2 else q.2 ≤ p.2)

def chain (up : Bool) (G : Finset Pos) : Prop :=
  ∀ p ∈ G, ∀ q ∈ G, aligned up p q ∨ aligned up q p

def twoChains (G : Finset Pos) : Prop :=
  ∃ B C : Finset Pos, ∃ b c : Bool, G = B ∪ C ∧ chain b B ∧ chain c C

lemma fiber_card_le (G : Finset Pos) {k : ℕ} (hk : 0 < k) (c : Pos) :
    (fiber G k c).card ≤ k^2 := by
  let rem : Pos → Pos := fun p => (p.1%k,p.2%k)
  have hinj : Set.InjOn rem (fiber G k c : Finset Pos) := by
    intro p hp q hq he
    have h := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    change p.1/k = q.1/k at hx
    change p.2/k = q.2/k at hy
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    change p.1%k = q.1%k at h₁
    change p.2%k = q.2%k at h₂
    apply Prod.ext
    · rw [← Nat.mod_add_div p.1 k,h₁,hx,Nat.mod_add_div]
    · rw [← Nat.mod_add_div p.2 k,h₂,hy,Nat.mod_add_div]
  have hsub : (fiber G k c).image rem ⊆ grid k := by
    intro p hp
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hk),
      Finset.mem_range.mpr (Nat.mod_lt _ hk)⟩
  rw [← Finset.card_image_of_injOn hinj]
  simpa [grid,pow_two] using Finset.card_le_card hsub

lemma occupied_chain {G : Finset Pos} {b : Bool} (h : chain b G) (k : ℕ) :
    chain b (occupied G k) := by
  have mono {p q : Pos} (hp : aligned b p q) : aligned b (block k p) (block k q) := by
    cases b <;> simp [aligned,block] at hp ⊢ <;>
      exact ⟨Nat.div_le_div_right hp.1,Nat.div_le_div_right hp.2⟩
  intro p hp q hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
  exact (h x hx y hy).imp mono mono

lemma occupied_subset {G : Finset Pos} {n : ℕ} (h : G ⊆ grid n) (k : ℕ) :
    occupied G k ⊆ grid (n/k+1) := by
  intro p hp
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp (h hx)
  exact Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_range.mp ha).le)),
     Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_range.mp hb).le))⟩

lemma chain_card {G : Finset Pos} {m : ℕ} (hgrid : G ⊆ grid (m+1)) {b : Bool}
    (hchain : chain b G) : G.card ≤ 2*(m+1) := by
  let code (p : Pos) := p.1 + (if b then p.2 else m-p.2)
  have coords {p : Pos} (hp : p ∈ G) : p.1 ≤ m ∧ p.2 ≤ m :=
    ⟨Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp (hgrid hp)).1),
     Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp (hgrid hp)).2)⟩
  have equal {p q : Pos} (hp : p ∈ G) (hq : q ∈ G) (ha : aligned b p q)
      (he : code p = code q) : p = q := by
    obtain ⟨px,py⟩ := coords hp
    obtain ⟨qx,qy⟩ := coords hq
    cases b <;> simp [aligned,code] at ha he <;> apply Prod.ext <;> omega
  have hinj : Set.InjOn code (G : Set Pos) := by
    intro p hp q hq he
    rcases hchain p hp q hq with h | h
    · exact equal hp hq h he
    · exact (equal hq hp h he.symm).symm
  have hsub : G.image code ⊆ Finset.range (2*(m+1)) := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨px,py⟩ := coords hp
    apply Finset.mem_range.mpr
    cases b <;> simp [code] <;> omega
  rw [← Finset.card_image_of_injOn hinj]
  simpa using Finset.card_le_card hsub

lemma occupied_count {G : Finset Pos} {n : ℕ} (hgrid : G ⊆ grid n) (h : twoChains G) (k : ℕ) :
    (occupied G k).card ≤ 4*(n/k+1) := by
  obtain ⟨B,C,b,c,rfl,hB,hC⟩ := h
  have h₁ := chain_card (occupied_subset (Finset.subset_union_left.trans hgrid) k) (occupied_chain hB k)
  have h₂ := chain_card (occupied_subset (Finset.subset_union_right.trans hgrid) k) (occupied_chain hC k)
  change ((B ∪ C).image (block k)).card ≤ _
  rw [Finset.image_union]
  exact (Finset.card_union_le ..).trans (by change (occupied B k).card + (occupied C k).card ≤ _; omega)

lemma graph_count {G : Finset Pos} {k r : ℕ} (hk : 0 < k) :
    G.card ≤ (occupied G k).card*r + (good G k r).card*k^2 := by
  have hfib (c : Pos) :
      (fiber G k c).card ≤ r + (if r ≤ (fiber G k c).card then k^2 else 0) := by
    split_ifs
    · exact (fiber_card_le G hk c).trans (by omega)
    · omega
  calc
    G.card = ∑ c ∈ occupied G k, (fiber G k c).card := Finset.card_eq_sum_card_image .. 
    _ ≤ ∑ c ∈ occupied G k, (r + (if r ≤ (fiber G k c).card then k^2 else 0)) :=
      Finset.sum_le_sum (fun c _ => hfib c)
    _ = (occupied G k).card*r + (good G k r).card*k^2 := by
      simp [Finset.sum_add_distrib,← Finset.sum_filter,good]

lemma good_per_graph {G : Finset Pos} {n t k r b : ℕ} (hk : 0 < k) (hn : k ≤ n)
    (large : 4*t*r*b ≤ k) (occ : (occupied G k).card ≤ b*(n/k+1)) (hrich : n ≤ t*G.card) :
    n ≤ 2*t*k^2*(good G k r).card := by
  have hd : 1 ≤ n/k := (Nat.le_div_iff_mul_le hk).mpr (by simpa using hn)
  have hm : 2*(t*((occupied G k).card*r)) ≤ n := calc
    _ ≤ 2*(t*((b*(n/k+1))*r)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ occ))
    _ = (2*t*r*b)*(n/k+1) := by ring
    _ ≤ (2*t*r*b)*(n/k+n/k) := Nat.mul_le_mul_left _ (Nat.add_le_add_left hd _)
    _ = (4*t*r*b)*(n/k) := by ring
    _ ≤ k*(n/k) := Nat.mul_le_mul_right _ large
    _ = (n/k)*k := Nat.mul_comm ..
    _ ≤ n := Nat.div_mul_le_self n k
  have bound := Nat.mul_le_mul_left t (graph_count (G := G) (r := r) hk)
  nlinarith only [hrich,bound,hm]

lemma good_per_cell {ι : Type*} (A : Finset ι) (graphs : ι → Finset Pos) {n k r M : ℕ}
    (hk : 0 < k) (hg : ∀ i ∈ A, graphs i ⊆ grid n)
    (hm : ∀ T : Finset Pos, T.card = r → (A.filter (fun i => T ⊆ graphs i)).card ≤ M) (c : Pos) :
    (A.filter (fun i => c ∈ good (graphs i) k r)).card ≤ k^(2*r)*M := by
  classical
  let P := fiber (grid n) k c
  let samples := P.powersetCard r
  have hsub : A.filter (fun i => c ∈ good (graphs i) k r) ⊆
      samples.biUnion (fun T => A.filter (fun i => T ⊆ graphs i)) := by
    intro i hi
    obtain ⟨hiA,hgood⟩ := Finset.mem_filter.mp hi
    obtain ⟨T,hT,hsize⟩ := Finset.exists_subset_card_eq (Finset.mem_filter.mp hgood).2
    have hTP : T ⊆ P := hT.trans (Finset.filter_subset_filter _ (hg i hiA))
    exact Finset.mem_biUnion.mpr ⟨T,Finset.mem_powersetCard.mpr ⟨hTP,hsize⟩,
      Finset.mem_filter.mpr ⟨hiA,hT.trans (Finset.filter_subset ..)⟩⟩
  have hnum : samples.card ≤ k^(2*r) := calc
    samples.card = P.card.choose r := Finset.card_powersetCard ..
    _ ≤ P.card^r := Nat.choose_le_pow ..
    _ ≤ (k^2)^r := Nat.pow_le_pow_left (fiber_card_le _ hk _) r
    _ = _ := (pow_mul ..).symm
  calc
    _ ≤ _ := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ _T ∈ samples, M := Finset.sum_le_sum (fun T hT => hm T (Finset.mem_powersetCard.mp hT).2)
    _ = samples.card*M := by simp
    _ ≤ _ := Nat.mul_le_mul_right M hnum

/-- A rich family of bounded block occupancy has linear size when prescribed
r-point sets lie on at most M family members. -/
theorem rich_components (A : Finset ι) (graphs : ι → Finset Pos) {n t k r b M : ℕ}
    (hk : 0 < k) (hn : k ≤ n) (large : 4*t*r*b ≤ k) (hg : ∀ i ∈ A, graphs i ⊆ grid n)
    (hc : ∀ i ∈ A, (occupied (graphs i) k).card ≤ b*(n/k+1)) (hr : ∀ i ∈ A, n ≤ t*(graphs i).card)
    (hm : ∀ T : Finset Pos, T.card = r → (A.filter (fun i => T ⊆ graphs i)).card ≤ M) :
    A.card ≤ 8*t*k^(2+2*r)*M*n := by
  classical
  let cells := grid (n/k+1)
  have hn' : 0 < n := by omega
  have cellsub {i : ι} (hi : i ∈ A) : good (graphs i) k r ⊆ cells :=
    (Finset.filter_subset ..).trans (occupied_subset (hg i hi) k)
  have decomp {i : ι} (hi : i ∈ A) :
      cells.filter (fun c => c ∈ good (graphs i) k r) = good (graphs i) k r := by
    ext c
    exact Finset.mem_filter.trans (and_iff_right_of_imp (fun h => cellsub hi h))
  have hsum : ∑ i ∈ A, (good (graphs i) k r).card ≤ cells.card*(k^(2*r)*M) := calc
    _ = ∑ i ∈ A, (cells.filter (fun c => c ∈ good (graphs i) k r)).card :=
      Finset.sum_congr rfl (fun i hi => by rw [decomp hi])
    _ = ∑ c ∈ cells, (A.filter (fun i => c ∈ good (graphs i) k r)).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow ..
    _ ≤ ∑ _c ∈ cells, k^(2*r)*M := Finset.sum_le_sum (fun c _ => good_per_cell A graphs hk hg hm c)
    _ = _ := by simp
  have bound : cells.card ≤ 4*n^2 := by
    have hd := Nat.div_le_self n k
    calc
      cells.card = (n/k+1)^2 := by simp [cells,grid,pow_two]
      _ ≤ (2*n)^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  have htotal : A.card*n ≤ (8*t*k^(2+2*r)*M*n)*n := calc
    _ = ∑ _i ∈ A, n := by simp
    _ ≤ ∑ i ∈ A, (2*t*k^2)*(good (graphs i) k r).card :=
      Finset.sum_le_sum (fun i hi => good_per_graph hk hn large (hc i hi) (hr i hi))
    _ = (2*t*k^2)*∑ i ∈ A, (good (graphs i) k r).card := (Finset.mul_sum ..).symm
    _ ≤ (2*t*k^2)*(cells.card*(k^(2*r)*M)) := Nat.mul_le_mul_left _ hsum
    _ ≤ (2*t*k^2)*((4*n^2)*(k^(2*r)*M)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ bound)
    _ = _ := by rw [pow_add]; ring
  exact Nat.le_of_mul_le_mul_right htotal hn'

/-- For a two-piece graph, triple multiplicity suffices. -/
theorem rich_graphs (A : Finset ι) (graphs : ι → Finset Pos) {n t M : ℕ}
    (ht : 0 < t) (hn : 64*t ≤ n) (hg : ∀ i ∈ A, graphs i ⊆ grid n)
    (hc : ∀ i ∈ A, twoChains (graphs i)) (hr : ∀ i ∈ A, n ≤ t*(graphs i).card)
    (hm : ∀ T : Finset Pos, T.card = 3 → (A.filter (fun i => T ⊆ graphs i)).card ≤ M) :
    A.card ≤ 8*t*(64*t)^8*M*n :=
  rich_components A graphs (by omega) hn (b := 4) (r := 3) (by omega) hg
    (fun i hi => occupied_count (hg i hi) (hc i hi) _) hr hm

end Erdos101OrderedGrid

noncomputable section
namespace Erdos101Parabola
open Erdos101OrderedGrid
open scoped Classical
def rank (X : Finset ℝ) (x : ℝ) := (X.filter (· < x)).card
def ranks (X : Finset ℝ) (p : ℝ × ℝ) : Pos := (rank X p.1,rank X p.2)
lemma rank_mono (X : Finset ℝ) : Monotone (rank X) := by
  intro x y h
  apply Finset.card_le_card
  intro z hz
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2.trans_le h⟩

lemma rank_strict (X : Finset ℝ) {x y : ℝ} (hx : x ∈ X) (h : x < y) : rank X x < rank X y := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
  · intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2.trans h⟩
  · intro he
    have hm : x ∈ X.filter (· < y) := Finset.mem_filter.mpr ⟨hx,h⟩
    rw [← he] at hm
    exact (lt_irrefl x) (Finset.mem_filter.mp hm).2

lemma rank_lt_card (X : Finset ℝ) {x : ℝ} (hx : x ∈ X) : rank X x < X.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset ..,?_⟩
  intro he
  have hm : x ∈ X.filter (· < x) := by rw [he]; exact hx
  exact (lt_irrefl x) (Finset.mem_filter.mp hm).2

lemma ranks_inj (X : Finset ℝ) : Set.InjOn (ranks X) (↑(X ×ˢ X) : Set (ℝ × ℝ)) := by
  have inj {x y : ℝ} (hx : x ∈ X) (hy : y ∈ X) (he : rank X x = rank X y) : x = y := by
    rcases lt_trichotomy x y with h|h|h
    · exact False.elim ((rank_strict X hx h).ne he)
    · exact h
    · exact False.elim ((rank_strict X hy h).ne he.symm)
  intro p hp q hq h
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
  obtain ⟨hz,hw⟩ := Finset.mem_product.mp hq
  exact Prod.ext (inj hx hz (congrArg Prod.fst h)) (inj hy hw (congrArg Prod.snd h))
end Erdos101Parabola
end

noncomputable section
namespace OMA.R_Erdos101_erdos_101_R1
open EuclideanGeometry
open scoped Classical
lemma four_points {S : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²)) :
    (S.filter (fun p => p ∈ L)).card = 4 := by
  have he : ((S.filter (fun p => p ∈ L) : Finset ℝ²) : Set ℝ²) = (L : Set ℝ²) ∩ S := by
    ext p
    simp [and_comm]
  rw [← Set.ncard_coe_finset, he]
  exact hL.2

lemma line_through {S : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²)) {p q : ℝ²}
    (hp : p ∈ L) (hq : q ∈ L) (hne : p ≠ q) : line[ℝ, p, q] = L := by
  obtain ⟨⟨a, _, b, _, _, rfl⟩, _⟩ := hL
  exact affineSpan_pair_eq_of_mem_of_mem_of_ne hp hq hne
end OMA.R_Erdos101_erdos_101_R1
end

/- On the secants of the real cubic `(x,x³)`, the same rational function
describes both projected weight tables, up to a constant sign. -/

noncomputable section

namespace Erdos101RectangleCubic

/-- The other two parameters on a secant to the cubic satisfy `z = -x-y`. -/
def weight (x y : ℝ) := (x+2*y)/(2*x+y)

theorem cubic_weights {x y z : ℝ} (sum : x+y+z = 0) (xy : x ≠ y) (xz : x ≠ z) :
    let t := (z-x)/(y-x)
    (1-t)/t = -weight x y ∧ 1-t = weight x z := by
  have zval : z = -(x+y) := by linarith
  have d : y-x ≠ 0 := sub_ne_zero.mpr xy.symm
  have h : 2*x+y ≠ 0 := fun eq => xz (by linarith)
  have h' : 2*x+z ≠ 0 := fun eq => xy (by linarith)
  have diff : 1-(z-x)/(y-x) = (y-z)/(y-x) := by
    apply (eq_div_iff d).mpr
    rw [sub_mul,div_mul_cancel₀ _ d,one_mul]; ring
  dsimp only [weight]
  rw [diff,div_div_div_cancel_right₀ d]
  constructor
  · rw [← neg_div,div_eq_div_iff (sub_ne_zero.mpr xz.symm) h,zval]; ring
  · rw [div_eq_div_iff d h',zval]; ring

private lemma slope {x a q y z : ℝ} (ne : y ≠ z)
    (hy : (x+2*y)*(2*a+y)=q*((2*x+y)*(a+2*y)))
    (hz : (x+2*z)*(2*a+z)=q*((2*x+z)*(a+2*z))) :
    (2-2*q)*(y+z) + (x+4*a-q*(4*x+a)) = 0 := by
  apply (mul_eq_zero.mp (show (y-z)*((2-2*q)*(y+z) + (x+4*a-q*(4*x+a)))=0 by
    linear_combination hy-hz)).resolve_left (sub_ne_zero.mpr ne)

/-- For two distinct rows, a fixed relative value occurs in at most two
columns, even if the set of columns is chosen after the rows. -/
theorem two_columns (Y : Finset ℝ) {x a : ℝ} (xa : x ≠ a) (q : ℝ) :
    (Y.filter (fun y => (x+2*y)*(2*a+y) = q*((2*x+y)*(a+2*y)))).card ≤ 2 := by
  classical
  by_contra! many
  obtain ⟨y,z,w,hy,hz,hw,yz,yw,zw⟩ := Finset.two_lt_card_iff.mp many
  have h₁ := slope yz (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2
  have h₂ := slope yw (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hw).2
  have h₃ : (2-2*q)*(z-w) = 0 := by linear_combination h₁-h₂
  have h₄ := (mul_eq_zero.mp h₃).resolve_right (sub_ne_zero.mpr zw)
  have one : q = 1 := by linarith only [h₄]
  rw [one] at h₁
  exact xa (by linarith only [h₁])

/-- A normalized anchored value of either table is a fixed relative row value. -/
theorem anchored_columns (Y : Finset ℝ) {x a b : ℝ} (xa : x ≠ a)
    (ab : weight a b ≠ 0) (xb : weight x b ≠ 0)
    (valid : ∀ y ∈ Y, 2*x+y ≠ 0 ∧ 2*a+y ≠ 0 ∧ a+2*y ≠ 0) (r : ℝ) :
    (Y.filter (fun y => weight x y*weight a b/(weight x b*weight a y)=r)).card ≤ 2 := by
  classical
  let q := r*weight x b/weight a b
  apply le_trans _ (two_columns Y xa q)
  apply Finset.card_le_card
  intro y hy
  obtain ⟨hy,hr⟩ := Finset.mem_filter.mp hy
  obtain ⟨hx,ha,hay⟩ := valid y hy
  have why : weight a y ≠ 0 := div_ne_zero hay ha
  have h := (div_eq_iff (mul_ne_zero xb why)).mp hr
  have w : weight x y = q*weight a y := by
    dsimp [q]
    field_simp [ab]
    linear_combination h
  change (x+2*y)/(2*x+y) = q*((a+2*y)/(2*a+y)) at w
  rw [← mul_div_assoc,div_eq_div_iff hx ha] at w
  exact Finset.mem_filter.mpr ⟨hy,by linear_combination w⟩

/-- A fourth point off the cubic forces a fixed, nonzero product of the three
translated parameters. Its nonzero value is independent of the slope. -/
theorem fourth_point_product {x y z u v m d : ℝ} (xy : x ≠ y) (sum : x+y+z = 0)
    (hx : x^3=m*x+d) (hy : y^3=m*y+d) (p : v=m*u+d) :
    (x-u)*(y-u)*(z-u) = v-u^3 := by
  have slope := (mul_eq_zero.mp (show (x-y)*(x^2+x*y+y^2-m) = 0 by
    linear_combination hx-hy)).resolve_left (sub_ne_zero.mpr xy)
  have sz : z = -(x+y) := by linarith
  rw [sz,p]
  linear_combination hx+(u-x)*slope

end Erdos101RectangleCubic

end

/- A dense graph with few edge sums retains quadratically many of its own
edges on rows and columns with small sumsets against large translation sets.
This allows the external point attached to each original secant to be kept. -/

noncomputable section

namespace Erdos101CubicSumsets

open scoped Pointwise Classical

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The row set has many incident original edges, and there are many shifts
which together put all its translates into a set of linear size. -/
theorem keep_rows (δ : ℝ) (hδ : 0 < δ) (unit : δ ≤ 1)
    (A : Finset G) (nonempty : A.Nonempty) (E : Finset (G × G)) (sub : E ⊆ A ×ˢ A)
    (dense : δ*(A.card : ℝ)^2 ≤ E.card) (few : (E.image (fun p => p.1+p.2)).card ≤ A.card) :
    let c := δ/8
    let t := δ^5/2^12
    ∃ U ⊆ A, ∃ V ⊆ A, c*(A.card : ℝ) ≤ V.card ∧ ((U+V).card : ℝ) ≤ A.card/t ∧
      c*t*(A.card : ℝ)^2 ≤ (E.filter (fun p => p.1 ∈ U)).card := by
  classical
  let n : ℝ := A.card
  let c := δ/8
  let t := δ^5/2^12
  have hn : 0 < n := Nat.cast_pos.mpr (Finset.card_pos.mpr nonempty)
  have hc : 0 < c := by dsimp [c]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨U,V,su,sv,hu,hv,paths⟩ := Finset.dense_bipartite_has_path3_rectangle δ hδ unit A A nonempty rfl
    E sub (by simpa only [pow_two,mul_assoc] using dense)
  change c*n ≤ (U.card : ℝ) at hu
  change c*n ≤ (V.card : ℝ) at hv
  let S := E.image (fun p => p.1+p.2)
  let M := ⌈t*n^2⌉₊
  have fib (a : G) (ha : a ∈ U) (b : G) (hb : b ∈ V) :
      M ≤ ((S ×ˢ S ×ˢ S).filter (fun p => p.1-p.2.1+p.2.2=a+b)).card := by
    apply Nat.ceil_le.mpr
    refine (paths a ha b hb).trans (Nat.cast_le.mpr ?_)
    exact Finset.path3_count_le_triple_rep_count A A S E (fun p hp => Finset.mem_image_of_mem _ hp) a b
  have product := (Finset.restricted_sumset_via_multiplicity U V S M fib).trans (Nat.pow_le_pow_left few 3)
  have pre : (M : ℝ)*((U+V).card : ℝ) ≤ n^3 := by dsimp only [n]; exact_mod_cast product
  have main : t*n^2*((U+V).card : ℝ) ≤ n^3 :=
    (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _)).trans pre
  have sumsize : ((U+V).card : ℝ) ≤ n/t := by
    apply (le_div_iff₀ ht).mpr
    apply le_of_mul_le_mul_left (a := n^2) _ (sq_pos_of_pos hn)
    nlinarith only [main]
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (Nat.cast_pos.mp ((mul_pos hc hn).trans_le hv))
  let row (a : G) := E.filter (fun p => p.1=a)
  have rich (a : G) (ha : a ∈ U) : t*n ≤ ((row a).card : ℝ) := by
    let D := A.filter (fun y => (a,y) ∈ E)
    have td : D.card ≤ (row a).card := by
      apply Finset.card_le_card_of_injOn (fun y => (a,y))
      · intro y hy
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).2,rfl⟩
      · exact (Prod.mk_right_injective a).injOn
    have incl : (A ×ˢ A).filter (fun q : G × G =>
        (a,q.1) ∈ E ∧ (q.2,q.1) ∈ E ∧ (q.2,b) ∈ E) ⊆ D ×ˢ A := by
      intro q hq
      obtain ⟨hin,he,_⟩ := Finset.mem_filter.mp hq
      obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hin
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨h₁,he⟩,h₂⟩
    have up := Finset.card_le_card incl
    rw [Finset.card_product] at up
    have total : t*n^2 ≤ ((row a).card : ℝ)*n := (paths a ha b hb).trans
      (by dsimp only [n]; exact_mod_cast up.trans (Nat.mul_le_mul_right _ td))
    apply le_of_mul_le_mul_right (a := n) _ hn
    nlinarith only [total]
  refine ⟨U,su,V,sv,hv,sumsize,?_⟩
  calc
    c*t*n^2 = (c*n)*(t*n) := by ring
    _ ≤ (U.card : ℝ)*(t*n) := mul_le_mul_of_nonneg_right hu (mul_pos ht hn).le
    _ = ∑ _a ∈ U, t*n := by simp
    _ ≤ ∑ a ∈ U, ((row a).card : ℝ) := Finset.sum_le_sum rich
    _ = _ := by exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter E U Prod.fst

/-- The two coordinate restrictions select the same original records. -/
theorem keep_both (δ : ℝ) (hδ : 0 < δ) (unit : δ ≤ 1) :
    ∃ η K : ℝ, 0 < η ∧ 0 < K ∧ ∀ (A : Finset G), A.Nonempty → ∀ E : Finset (G × G),
      E ⊆ A ×ˢ A → δ*(A.card : ℝ)^2 ≤ E.card → (E.image (fun p => p.1+p.2)).card ≤ A.card →
      ∃ U ⊆ A, ∃ V ⊆ A, ∃ X ⊆ A, ∃ Y ⊆ A,
        η*(A.card : ℝ) ≤ X.card ∧ η*(A.card : ℝ) ≤ Y.card ∧
        ((U+X).card : ℝ) ≤ K*A.card ∧ ((V+Y).card : ℝ) ≤ K*A.card ∧
        η*(A.card : ℝ)^2 ≤ (E.filter (fun p => p.1 ∈ U ∧ p.2 ∈ V)).card := by
  classical
  let c := δ/8
  let t := δ^5/2^12
  let d := c*t
  have hc : 0 < c := by dsimp [c]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hd : 0 < d := mul_pos hc ht
  have hδ₅ := pow_le_pow_left₀ hδ.le unit 5
  have hdu : d ≤ 1 := by dsimp [d,c,t]; norm_num at hδ₅ ⊢; nlinarith only [hδ₅,unit,hδ.le,mul_nonneg (sub_nonneg.mpr unit) (pow_nonneg hδ.le 5)]
  let c' := d/8
  let t' := d^5/2^12
  have hc' : 0 < c' := by dsimp [c']; positivity
  have ht' : 0 < t' := by dsimp [t']; positivity
  let η := min c (min c' (c'*t'))
  let K := max (1/t) (1/t')
  refine ⟨η,K,lt_min hc (lt_min hc' (mul_pos hc' ht')),(one_div_pos.mpr ht).trans_le (le_max_left ..),?_⟩
  intro A hn E sub size few
  obtain ⟨U,su,X,sx,xsize,ux,rows⟩ := keep_rows δ hδ unit A hn E sub size few
  let R := E.filter (fun p => p.1 ∈ U)
  let F := R.image Prod.swap
  have swapInj : Function.Injective (Prod.swap (α := G) (β := G)) := Prod.swap_injective
  have fs : F ⊆ A ×ˢ A := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have w := Finset.mem_product.mp (sub (Finset.mem_filter.mp hq).1)
    exact Finset.mem_product.mpr ⟨w.2,w.1⟩
  have ff : F.image (fun p => p.1+p.2) ⊆ E.image (fun p => p.1+p.2) := by
    intro w hw
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨p,(Finset.mem_filter.mp hp).1,add_comm ..⟩
  have fsize : d*(A.card : ℝ)^2 ≤ F.card := by simpa [F,R,Finset.card_image_of_injective _ swapInj] using rows
  obtain ⟨V,sv,Y,sy,ysize,vy,cols⟩ := keep_rows d hd hdu A hn F fs fsize ((Finset.card_le_card ff).trans few)
  have ff' : F.filter (fun p => p.1 ∈ V) = (E.filter (fun p => p.1 ∈ U ∧ p.2 ∈ V)).image Prod.swap := by
    ext p
    constructor
    · intro hp
      obtain ⟨inF,hv⟩ := Finset.mem_filter.mp hp
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp inF
      obtain ⟨inE,hu⟩ := Finset.mem_filter.mp he
      exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨inE,hu,hv⟩,rfl⟩
    · intro hp
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨inE,hu,hv⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨inE,hu⟩),hv⟩
  rw [ff',Finset.card_image_of_injective _ swapInj] at cols
  have nonneg := Nat.cast_nonneg (α := ℝ) A.card
  refine ⟨U,su,V,sv,X,sx,Y,sy,(mul_le_mul_of_nonneg_right (min_le_left ..) nonneg).trans xsize,
    (mul_le_mul_of_nonneg_right ((min_le_right ..).trans (min_le_left ..)) nonneg).trans ysize,?_,?_,
    (mul_le_mul_of_nonneg_right ((min_le_right ..).trans (min_le_right ..)) (sq_nonneg _)).trans cols⟩
  · calc
      _ ≤ (1/t)*(A.card : ℝ) := by rw [one_div,mul_comm,← div_eq_mul_inv]; exact ux
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left ..) nonneg
  · calc
      _ ≤ (1/t')*(A.card : ℝ) := by rw [one_div,mul_comm,← div_eq_mul_inv]; exact vy
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) nonneg

end Erdos101CubicSumsets

end

/- A nonzero product of three translated cubic parameters, with their sum
fixed, has finitely many monotone branches. On each branch a supporting
line separates each point strictly from every other point. -/

noncomputable section

namespace Erdos101CubicBranches

abbrev Pt := ℝ × ℝ

def a (u : ℝ) (p : Pt) := p.1-u
def b (u : ℝ) (p : Pt) := p.2-u
def c (u : ℝ) (p : Pt) := -p.1-p.2-u
def product (u : ℝ) (p : Pt) := a u p*b u p*c u p
def gx (u : ℝ) (p : Pt) := 1/a u p-1/c u p
def gy (u : ℝ) (p : Pt) := 1/b u p-1/c u p

def code (u : ℝ) (p : Pt) : Fin 5 → Bool :=
  ![decide (0<a u p),decide (0<b u p),decide (0<c u p),decide (0<gx u p),decide (0<gy u p)]

private lemma same_truth {p q : Prop} [Decidable p] [Decidable q] (eq : decide p = decide q) : p ↔ q := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

private lemma same_sign {f g : ℝ} (hf : f ≠ 0) (hg : g ≠ 0) (same : decide (0<f) = decide (0<g)) :
    0 < g/f := by
  by_cases h : 0 < f
  · have : 0 < g := by simpa [h] using same.symm
    exact div_pos this h
  · have : ¬ 0 < g := by simpa [h] using same.symm
    exact div_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.mp this) hg) (lt_of_le_of_ne (not_lt.mp h) hf)

private lemma strict_sum {r s t : ℝ} (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (prod : r*s*t=1)
    (diff : r ≠ 1 ∨ s ≠ 1) : 3 < r+s+t := by
  have sumlog : Real.log r+Real.log s+Real.log t=0 := by
    rw [← Real.log_mul hr.ne' hs.ne',← Real.log_mul (mul_pos hr hs).ne' ht.ne',prod,Real.log_one]
  have h₃ := Real.log_le_sub_one_of_pos ht
  rcases diff with h|h
  · linarith only [sumlog,Real.log_lt_sub_one_of_pos hr h,Real.log_le_sub_one_of_pos hs,h₃]
  · linarith only [sumlog,Real.log_le_sub_one_of_pos hr,Real.log_lt_sub_one_of_pos hs h,h₃]

/-- Strict supporting half-plane at a point on a branch. -/
theorem tangent {u : ℝ} {p q : Pt} (nz : product u p ≠ 0) (same : product u q = product u p)
    (branch : code u p = code u q) (ne : p ≠ q) :
    0 < gx u p*(q.1-p.1)+gy u p*(q.2-p.2) := by
  have parts {w : Pt} (h : product u w ≠ 0) : a u w ≠ 0 ∧ b u w ≠ 0 ∧ c u w ≠ 0 := by
    simpa only [product,mul_ne_zero_iff,and_assoc] using h
  obtain ⟨pa,pb,pc⟩ := parts nz
  obtain ⟨qa,qb,qc⟩ := parts (same ▸ nz)
  have ra : 0 < a u q/a u p := same_sign pa qa (congrFun branch 0)
  have rb : 0 < b u q/b u p := same_sign pb qb (congrFun branch 1)
  have rc : 0 < c u q/c u p := same_sign pc qc (congrFun branch 2)
  have prod : (a u q/a u p)*(b u q/b u p)*(c u q/c u p) = 1 := by
    rw [div_mul_div_comm,div_mul_div_comm,div_eq_one_iff_eq (mul_ne_zero (mul_ne_zero pa pb) pc)]
    exact same
  have diff : a u q/a u p ≠ 1 ∨ b u q/b u p ≠ 1 := by
    by_contra! h
    have hx := (div_eq_one_iff_eq pa).mp h.1
    have hy := (div_eq_one_iff_eq pb).mp h.2
    exact ne (Prod.ext ((sub_left_inj.mp hx).symm) ((sub_left_inj.mp hy).symm))
  have positive := strict_sum ra rb rc prod diff
  have eq : gx u p*(q.1-p.1)+gy u p*(q.2-p.2) = a u q/a u p+b u q/b u p+c u q/c u p-3 := by
    have hx : a u q = a u p+(q.1-p.1) := by dsimp [a]; ring
    have hy : b u q = b u p+(q.2-p.2) := by dsimp [b]; ring
    have hz : c u q = c u p-(q.1-p.1)-(q.2-p.2) := by dsimp [c]; ring
    rw [gx,gy,hx,hy,hz]
    field_simp [pa,pb,pc]; ring
  rw [eq]
  linarith only [positive]

def orient (up : Bool) (z : ℝ) := if up then z else -z

def Supports (D : Finset Pt) (up : Bool) : Prop :=
  ∀ p ∈ D, ∃ m : ℝ, ∀ q ∈ D, p ≠ q → orient up p.2 + m*(q.1-p.1) < orient up q.2

def Ordered (D : Finset Pt) (up : Bool) : Prop :=
  ∀ p ∈ D, ∀ q ∈ D, p.1 ≤ q.1 → if up then p.2 ≤ q.2 else q.2 ≤ p.2

private theorem ordered_of_tangents {u : ℝ} {D : Finset Pt} (p₀ : Pt)
    (branch : ∀ p ∈ D, code u p = code u p₀)
    (tang : ∀ p ∈ D, ∀ q ∈ D, p ≠ q → 0 < gx u p*(q.1-p.1)+gy u p*(q.2-p.2)) :
    Ordered D (decide ((0 < gx u p₀) ↔ ¬ 0 < gy u p₀)) := by
  intro p hp q hq h
  by_cases eq : p = q
  · subst q; split <;> exact le_rfl
  have hp' := tang p hp q hq eq
  have hq' := tang q hq p hp (Ne.symm eq)
  have sx (w) (hw : w ∈ D) : (0 < gx u w) ↔ 0 < gx u p₀ := by
    exact same_truth (congrFun (branch w hw) 3)
  have sy (w) (hw : w ∈ D) : (0 < gy u w) ↔ 0 < gy u p₀ := by
    exact same_truth (congrFun (branch w hw) 4)
  by_cases hx : 0 < gx u p₀ <;> by_cases hy : 0 < gy u p₀
  all_goals simp [hx,hy]
  · by_contra! y
    have m := mul_nonpos_of_nonneg_of_nonpos ((sx q hq).mpr hx).le (sub_nonpos.mpr h)
    have v := mul_nonpos_of_nonneg_of_nonpos ((sy q hq).mpr hy).le (sub_nonpos.mpr y.le)
    linarith only [m,v,hq']
  · by_contra! y
    have m := mul_nonpos_of_nonneg_of_nonpos ((sx q hq).mpr hx).le (sub_nonpos.mpr h)
    have v := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp (hy ∘ (sy q hq).mp)) (sub_nonneg.mpr y.le)
    linarith only [m,v,hq']
  · by_contra! y
    have m := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp (hx ∘ (sx p hp).mp)) (sub_nonneg.mpr h)
    have v := mul_nonpos_of_nonneg_of_nonpos ((sy p hp).mpr hy).le (sub_nonpos.mpr y.le)
    linarith only [m,v,hp']
  · by_contra! y
    have m := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp (hx ∘ (sx p hp).mp)) (sub_nonneg.mpr h)
    have v := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp (hy ∘ (sy p hp).mp)) (sub_nonneg.mpr y.le)
    linarith only [m,v,hp']

/-- One of 32 parts is both a monotone graph and strictly supported from
one side. The same part works for all its pairs. -/
theorem large_branch (u d : ℝ) (nz : d ≠ 0) (D : Finset Pt) (nonempty : D.Nonempty)
    (hits : ∀ p ∈ D, product u p = d ∧ gy u p ≠ 0) :
    ∃ B ⊆ D, D.card ≤ 32*B.card ∧ ∃ up sign : Bool, Ordered B up ∧ Supports B sign := by
  classical
  let fiber (i : Fin 5 → Bool) := D.filter (fun p => code u p = i)
  obtain ⟨i,_,maximal⟩ := (Finset.univ : Finset (Fin 5 → Bool)).exists_max_image
    (fun i => (fiber i).card) Finset.univ_nonempty
  have size : D.card ≤ 32*(fiber i).card := calc
    _ = ∑ j : Fin 5 → Bool, (fiber j).card := Finset.card_eq_sum_card_fiberwise (by simp)
    _ ≤ ∑ _j : Fin 5 → Bool, (fiber i).card := Finset.sum_le_sum (fun j hj => maximal j hj)
    _ = _ := by simp
  obtain ⟨p₀,h₀⟩ := Finset.card_pos.mp (show 0 < (fiber i).card by have := Finset.card_pos.mpr nonempty; omega)
  let B := fiber i
  have incl : B ⊆ D := Finset.filter_subset ..
  have branch (p) (hp : p ∈ B) : code u p = code u p₀ :=
    (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp h₀).2.symm
  have tang (p) (hp : p ∈ B) (q) (hq : q ∈ B) (ne : p ≠ q) :=
    tangent ((hits p (incl hp)).1 ▸ nz) ((hits q (incl hq)).1.trans (hits p (incl hp)).1.symm)
      ((branch p hp).trans (branch q hq).symm) ne
  refine ⟨B,incl,size,_,decide (0 < gy u p₀),ordered_of_tangents p₀ branch tang,?_⟩
  intro p hp
  have sy : (0 < gy u p) ↔ 0 < gy u p₀ := same_truth (congrFun (branch p hp) 4)
  by_cases up : 0 < gy u p₀
  · refine ⟨-gx u p/gy u p,?_⟩
    intro q hq ne
    simp only [up,decide_true,orient,if_true]
    have e := tang p hp q hq ne
    have pos := sy.mpr up
    rw [div_mul_eq_mul_div,← lt_sub_iff_add_lt',div_lt_iff₀ pos]
    linarith only [e]
  · refine ⟨gx u p/gy u p,?_⟩
    intro q hq ne
    simp only [up,decide_false,orient,Bool.false_eq_true,if_false]
    have e := tang p hp q hq ne
    have neg := lt_of_le_of_ne (not_lt.mp (up ∘ sy.mp)) (hits p (incl hp)).2
    rw [div_mul_eq_mul_div,← lt_sub_iff_add_lt',div_lt_iff_of_neg neg]
    linarith only [e]

end Erdos101CubicBranches

end

/- Bounds on translated copies of a strictly supported finite graph in an
ordered Cartesian product. Two fixed points specify at most one translation. -/

noncomputable section

namespace Erdos101CubicTranslations

open Erdos101CubicBranches Erdos101OrderedGrid Erdos101Parabola
open scoped Classical Pointwise

private theorem first_inj {D : Finset Pt} {s : Bool} (supports : Supports D s) :
    (D : Set Pt).InjOn Prod.fst := by
  intro p hp q hq eq
  by_contra ne
  obtain ⟨m,hm⟩ := supports p hp
  obtain ⟨k,hk⟩ := supports q hq
  have a := hm q hq ne
  have b := hk p hp (Ne.symm ne)
  simp only [eq,sub_self,mul_zero,add_zero] at a b
  exact (lt_asymm a b)

private theorem chord {D : Finset Pt} {s : Bool} (supp : Supports D s) {p z q : Pt}
    (hp : p ∈ D) (hz : z ∈ D) (hq : q ∈ D) (pz : p.1 < z.1) (zq : z.1 < q.1) :
    (q.1-p.1)*orient s z.2 < (q.1-z.1)*orient s p.2+(z.1-p.1)*orient s q.2 := by
  obtain ⟨m,hm⟩ := supp z hz
  have a := mul_lt_mul_of_pos_left (hm p hp (fun e => pz.ne (congrArg Prod.fst e.symm))) (sub_pos.mpr zq)
  have b := mul_lt_mul_of_pos_left (hm q hq (fun e => zq.ne (congrArg Prod.fst e))) (sub_pos.mpr pz)
  nlinarith only [a,b]

private theorem no_parallel {D : Finset Pt} {s : Bool} (supp : Supports D s) {p q v : Pt}
    (hp : p ∈ D) (hq : q ∈ D) (hp' : p+v ∈ D) (hq' : q+v ∈ D) (order : p.1 < q.1) (pos : 0 < v.1) : False := by
  have h₁ := chord supp hp hq hq' order (by change q.1 < q.1+v.1; linarith)
  have h₂ := chord supp hp hp' hq' (by change p.1 < p.1+v.1; linarith) (by change p.1+v.1 < q.1+v.1; linarith)
  cases s <;> simp only [orient,Bool.false_eq_true,if_false,if_true,Prod.fst_add,Prod.snd_add] at h₁ h₂ <;> nlinarith only [h₁,h₂]

private theorem unique_start_pos {D : Finset Pt} {s : Bool} (supp : Supports D s) {p q v : Pt}
    (hp : p ∈ D) (hq : q ∈ D) (hp' : p+v ∈ D) (hq' : q+v ∈ D) (pos : 0 < v.1) : p = q := by
  rcases lt_trichotomy p.1 q.1 with h|h|h
  · exact False.elim (no_parallel supp hp hq hp' hq' h pos)
  · exact first_inj supp hp hq h
  · exact False.elim (no_parallel supp hq hp hq' hp' h pos)

/-- On one side of a strictly supported graph each directed displacement
has at most one starting point. -/
theorem unique_start {D : Finset Pt} {s : Bool} (supp : Supports D s) {p q v : Pt}
    (hp : p ∈ D) (hq : q ∈ D) (hp' : p+v ∈ D) (hq' : q+v ∈ D) (ne : v ≠ 0) : p = q := by
  rcases lt_trichotomy 0 v.1 with h|h|h
  · exact unique_start_pos supp hp hq hp' hq' h
  · have eq := first_inj supp hp hp' (by change p.1 = p.1+v.1; rw [← h,add_zero])
    exact False.elim (ne (((add_right_inj p).mp ((add_zero p).trans eq)).symm))
  · have eq : p+v = q+v := unique_start_pos (v := -v) supp hp' hq' (by simpa) (by simpa)
      (by simpa using neg_pos.mpr h)
    exact add_right_cancel eq

/-- If every translate contains a fixed positive proportion of a side
length, the number of available translations grows only linearly. -/
theorem translate_count (D : Finset Pt) (U V X Y : Finset ℝ) {n t : ℕ} (ht : 0 < t)
    (big : 32*t ≤ n) (box : ((U+X) ∪ (V+Y)).card ≤ n) (rich : n ≤ t*D.card)
    (inside : D ⊆ U ×ˢ V) {up sign : Bool} (ordered : Ordered D up) (supports : Supports D sign) :
    X.card*Y.card ≤ 8*t*(32*t)^6*n := by
  classical
  let W := (U+X) ∪ (V+Y)
  let I := X ×ˢ Y
  let view (s : Pt) (p : Pt) := ranks W (p+s)
  let graph (s : Pt) := D.image (view s)
  have actual {s p : Pt} (hs : s ∈ I) (hp : p ∈ D) : p+s ∈ W ×ˢ W := by
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hs
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp (inside hp)
    exact Finset.mem_product.mpr ⟨Finset.mem_union_left _ (Finset.add_mem_add hu hx),
      Finset.mem_union_right _ (Finset.add_mem_add hv hy)⟩
  have v_inj {s : Pt} (hs : s ∈ I) : (D : Set Pt).InjOn (view s) := fun _ hp _ hq eq =>
    add_right_cancel (ranks_inj W (actual hs hp) (actual hs hq) eq)
  have grid_sub (s) (hs : s ∈ I) : graph s ⊆ grid n := by
    intro w hw
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hw
    have h := Finset.mem_product.mp (actual hs hp)
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr ((rank_lt_card W h.1).trans_le box),
      Finset.mem_range.mpr ((rank_lt_card W h.2).trans_le box)⟩
  have mono (s : Pt) : chain up (graph s) := by
    have forward {p q : Pt} (hp : p ∈ D) (hq : q ∈ D) (x : p.1 ≤ q.1) : aligned up (view s p) (view s q) := by
      refine ⟨rank_mono W (add_le_add_left x _),?_⟩
      have y := ordered p hp q hq x
      cases up <;> exact rank_mono W (add_le_add_left y _)
    intro i hi j hj
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hj
    exact (le_total p.1 q.1).imp (forward hp hq) (forward hq hp)
  have cell (s) (hs : s ∈ I) : (occupied (graph s) (32*t)).card ≤ 4*(n/(32*t)+1) :=
    occupied_count (grid_sub s hs) ⟨graph s,∅,up,true,by simp,mono s,by simp [chain]⟩ _
  have multiplicity (T : Finset Pos) (size : T.card=2) : (I.filter (fun s => T ⊆ graph s)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro s hs r hr
    obtain ⟨si,st⟩ := Finset.mem_filter.mp hs
    obtain ⟨ri,rt⟩ := Finset.mem_filter.mp hr
    obtain ⟨i,hi,j,hj,ne⟩ := Finset.one_lt_card.mp (show 1 < T.card by omega)
    obtain ⟨p,hp,pi⟩ := Finset.mem_image.mp (st hi)
    obtain ⟨q,hq,qi⟩ := Finset.mem_image.mp (rt hi)
    obtain ⟨p',hp',pj⟩ := Finset.mem_image.mp (st hj)
    obtain ⟨q',hq',qj⟩ := Finset.mem_image.mp (rt hj)
    have e : p+s = q+r := ranks_inj W (actual si hp) (actual ri hq) (pi.trans qi.symm)
    have e' : p'+s = q'+r := ranks_inj W (actual si hp') (actual ri hq') (pj.trans qj.symm)
    have delta : q+(p'-p) = q' := by linear_combination e'-e
    have nz : p'-p ≠ 0 := fun z => ne (pi.symm.trans ((sub_eq_zero.mp z) ▸ pj))
    have pq := unique_start (v := p'-p) supports hp hq (by simpa [add_comm] using hp') (delta ▸ hq') nz
    exact add_left_cancel (pq ▸ e)
  have result := rich_components I graph (t := t) (k := 32*t) (r := 2) (M := 1) (b := 4) (by omega) big
    (by omega) grid_sub cell (fun s hs => by simpa only [graph,Finset.card_image_of_injOn (v_inj hs)] using rich) multiplicity
  simpa only [I,Finset.card_product,mul_one] using result

end Erdos101CubicTranslations

end

/- There are subquadratically many distinct secants that join three members
of a real cubic parameter set and contain a fourth point from a given set of
comparable size off the cubic. The exterior point can vary with every pair. -/

noncomputable section

namespace Erdos101CubicCompletion

open Erdos101CubicBranches Erdos101CubicTranslations Erdos101CubicSumsets
open scoped Classical Pointwise

/-- In an additive graph with at most n edge sums, a nonzero product from
a prescribed fourth point cannot be realized on a dense set of edges. -/
theorem sparse_products (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ A : Finset ℝ, N ≤ A.card →
    ∀ Q E : Finset Pt, Q.card ≤ A.card → E ⊆ A ×ˢ A → (E.image (fun p => p.1+p.2)).card ≤ A.card →
    ∀ f : Pt → Pt, (∀ p ∈ E, f p ∈ Q ∧ (f p).2-(f p).1^3 ≠ 0 ∧
      product (f p).1 p = (f p).2-(f p).1^3 ∧ gy (f p).1 p ≠ 0) →
    (E.card : ℝ) < ε*(A.card : ℝ)^2 := by
  classical
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε zero_lt_one
  obtain ⟨η,K,hη,hK,extract⟩ := keep_both (G := ℝ) δ hδ (min_le_right ..)
  let H := ⌈2*K⌉₊+1
  have hH : 2*K ≤ (H : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)
  have hHn : 1 ≤ H := by dsimp [H]; omega
  obtain ⟨t,ht⟩ := exists_nat_gt (32*(H : ℝ)/η)
  have htR : 32*(H : ℝ) < t*η := (div_lt_iff₀ hη).mp ht
  have htpos : 0 < t := Nat.cast_pos.mp ((div_nonneg (by positivity) hη.le).trans_lt ht)
  let M := 8*t*(32*t)^6
  obtain ⟨N,hN⟩ := exists_nat_gt ((M : ℝ)*H/η^2)
  refine ⟨max N (32*t),?_⟩
  intro A hn Q E cq sub sums f hits
  by_contra! dense
  let n := A.card
  have hn1 : 32*t ≤ n := (le_max_right ..).trans hn
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  obtain ⟨U,_,V,_,X,_,Y,_,xsize,ysize,ux,vy,retained⟩ := extract A (Finset.card_pos.mp hn0) E sub
    ((mul_le_mul_of_nonneg_right (min_le_left ..) (sq_nonneg _)).trans dense) sums
  let F := E.filter (fun p => p.1 ∈ U ∧ p.2 ∈ V)
  have fs : F ⊆ E := Finset.filter_subset ..
  have into (p) (hp : p ∈ F) : f p ∈ Q := (hits p (fs hp)).1
  have fpos : 0 < F.card := Nat.cast_pos.mp ((mul_pos hη (sq_pos_of_pos hnR)).trans_le retained)
  obtain ⟨w,hw⟩ := Finset.card_pos.mp fpos
  let D (q : Pt) := F.filter (fun p => f p = q)
  obtain ⟨q,hq,maximal⟩ := Q.exists_max_image (fun q => (D q).card) ⟨f w,into w hw⟩
  have split : F.card ≤ Q.card*(D q).card := calc
    _ = ∑ q ∈ Q, (D q).card := Finset.card_eq_sum_card_fiberwise into
    _ ≤ ∑ _j ∈ Q, (D q).card := Finset.sum_le_sum maximal
    _ = _ := by simp
  have mass : η*(n : ℝ) ≤ (D q).card := by
    have total : η*(n : ℝ)^2 ≤ (n : ℝ)*(D q).card := retained.trans
      (by exact_mod_cast split.trans (Nat.mul_le_mul_right _ cq))
    apply le_of_mul_le_mul_left (a := (n : ℝ)) _ hnR
    nlinarith only [total]
  have hd : (D q).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp ((mul_pos hη hnR).trans_le mass))
  have values (p) (hp : p ∈ D q) : q.2-q.1^3 ≠ 0 ∧ product q.1 p = q.2-q.1^3 ∧ gy q.1 p ≠ 0 :=
    (Finset.mem_filter.mp hp).2 ▸ (hits p (fs (Finset.mem_filter.mp hp).1)).2
  obtain ⟨p,hp⟩ := hd
  obtain ⟨B,bd,size,up,sign,ordered,supports⟩ := large_branch q.1 _ (values p hp).1 (D q) ⟨p,hp⟩
    (fun z hz => (values z hz).2)
  have base : B ⊆ U ×ˢ V := fun z hz => Finset.mem_product.mpr (Finset.mem_filter.mp
    (Finset.mem_filter.mp (bd hz)).1).2
  have side : ((U+X) ∪ (V+Y)).card ≤ H*n := by
    have lower : (((U+X) ∪ (V+Y)).card : ℝ) ≤ (((U+X).card+(V+Y).card : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Finset.card_union_le (U+X) (V+Y))
    push_cast at lower
    have upper := mul_le_mul_of_nonneg_right hH hnR.le
    exact_mod_cast (show (((U+X) ∪ (V+Y)).card : ℝ) ≤ (H : ℝ)*n by linarith only [lower,ux,vy,upper])
  have density : H*n ≤ t*B.card := by
    have cols : η*(n : ℝ) ≤ 32*(B.card : ℝ) := mass.trans (by exact_mod_cast size)
    have a := mul_le_mul_of_nonneg_left cols (Nat.cast_nonneg (α := ℝ) t)
    have b := mul_le_mul_of_nonneg_right htR.le hnR.le
    exact_mod_cast (show (H : ℝ)*n ≤ (t : ℝ)*B.card by nlinarith only [a,b])
  have bound := translate_count B U V X Y htpos
    (hn1.trans (by simpa using Nat.mul_le_mul_right n hHn)) side density base ordered supports
  have ub : (X.card : ℝ)*Y.card ≤ (M : ℝ)*((H : ℝ)*n) := by exact_mod_cast bound
  have lower := mul_le_mul xsize ysize (mul_pos hη hnR).le (Nat.cast_nonneg (α := ℝ) X.card)
  have endbound : η^2*(n : ℝ) ≤ (M : ℝ)*H := by
    apply le_of_mul_le_mul_right (a := (n : ℝ)) _ hnR
    nlinarith only [lower,ub]
  have hn' : (N : ℝ) ≤ n := Nat.cast_le.mpr ((le_max_left ..).trans hn)
  have lo := (div_lt_iff₀ (sq_pos_of_pos hη)).mp (hN.trans_le hn')
  nlinarith only [lo,endbound]

/-- The exterior points in this statement are arbitrary. Only the original
three cubic parameters are drawn from the finite one-dimensional set. -/
theorem sparse_completed_secants (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ A : Finset ℝ, N ≤ A.card →
    ∀ Q E : Finset Pt, Q.card ≤ A.card → E ⊆ A ×ˢ A →
      (∀ p ∈ E, ∃ z ∈ A, ∃ q ∈ Q, ∃ m d : ℝ, p.1 ≠ p.2 ∧ p.2 ≠ z ∧ p.1+p.2+z=0 ∧
        p.1^3=m*p.1+d ∧ p.2^3=m*p.2+d ∧ q.2=m*q.1+d ∧ q.2 ≠ q.1^3) →
      (E.card : ℝ) < ε*(A.card : ℝ)^2 := by
  classical
  obtain ⟨N,estimate⟩ := sparse_products ε hε
  refine ⟨N,?_⟩
  intro A hn Q E cq sub marks
  have sums : E.image (fun p => p.1+p.2) ⊆ A.image Neg.neg := by
    intro w hw
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨z,hz,q,hq,m,d,_,_,sum,_⟩ := marks p hp
    exact Finset.mem_image.mpr ⟨z,hz,by linarith only [sum]⟩
  have eligible (p : Pt) (hp : p ∈ E) : ∃ q ∈ Q, q.2-q.1^3 ≠ 0 ∧ product q.1 p=q.2-q.1^3 ∧ gy q.1 p ≠ 0 := by
    obtain ⟨z,hz,q,hq,m,d,xy,yz,sum,xm,ym,qm,off⟩ := marks p hp
    have zeq : -p.1-p.2=z := by linarith only [sum]
    have prod : product q.1 p = q.2-q.1^3 := by
      simpa only [product,a,b,c,zeq] using Erdos101RectangleCubic.fourth_point_product xy sum xm ym qm
    have nz : product q.1 p ≠ 0 := prod ▸ sub_ne_zero.mpr off
    have parts : a q.1 p ≠ 0 ∧ b q.1 p ≠ 0 ∧ c q.1 p ≠ 0 := by simpa only [product,mul_ne_zero_iff,and_assoc] using nz
    refine ⟨q,hq,sub_ne_zero.mpr off,prod,?_⟩
    intro zero
    have hh := (div_eq_div_iff parts.2.1 parts.2.2).mp (sub_eq_zero.mp zero : (1 : ℝ)/b q.1 p = 1/c q.1 p)
    exact yz (sub_left_inj.mp (by simpa only [one_mul,b,c,zeq] using hh.symm : p.2-q.1=z-q.1))
  let f (p : Pt) : Pt := if h : p ∈ E then (eligible p h).choose else 0
  apply estimate A hn Q E cq sub ((Finset.card_le_card sums).trans Finset.card_image_le) f
  intro p hp
  simpa [f,hp] using (eligible p hp).choose_spec

end Erdos101CubicCompletion

end

/- Four-point lines through three configuration points on `y = x³` are
subquadratic. All remaining configuration points are arbitrary. -/

noncomputable section

namespace Erdos101CubicLines

open EuclideanGeometry Erdos101CubicBranches Erdos101CubicCompletion
open scoped Classical

def curve (x : ℝ) : ℝ² := !₂[x,x^3]
def slope (x y : ℝ) := x^2+x*y+y^2
def intercept (x y : ℝ) := -x*y*(x+y)

private theorem from_coord {p : ℝ²} (h : p 1=(p 0)^3) : p = curve (p 0) := by
  ext i; fin_cases i
  · rfl
  · exact h

private theorem secant {p : ℝ²} {x y : ℝ} (hp : p ∈ line[ℝ,curve x,curve y]) :
    p 1 = slope x y * p 0 + intercept x y := by
  obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hp
  have h0 := congrArg (fun v : ℝ² => v 0) ht
  have h1 := congrArg (fun v : ℝ² => v 1) ht
  simp [curve,AffineMap.lineMap_apply_module] at h0 h1
  dsimp [slope,intercept]
  linear_combination (x^2+x*y+y^2)*h0-h1

private theorem roots {x y z : ℝ} (h : z^3=slope x y*z+intercept x y) : z=x ∨ z=y ∨ z=-(x+y) := by
  have f : (z-x)*(z-y)*(z+x+y)=0 := by dsimp [slope,intercept] at h; linear_combination h
  rcases (mul_eq_zero.mp f) with k|k
  · exact ((mul_eq_zero.mp k).imp sub_eq_zero.mp sub_eq_zero.mp).elim Or.inl (Or.inr ∘ Or.inl)
  · right; right; linarith only [k]

private structure Mark (S : Finset ℝ²) (L : AffineSubspace ℝ ℝ²) where
  x : ℝ
  y : ℝ
  z : ℝ
  q : ℝ²
  xs : curve x ∈ S
  ys : curve y ∈ S
  zs : curve z ∈ S
  qs : q ∈ S
  line_eq : line[ℝ,curve x,curve y] = L
  xy : x ≠ y
  yz : y ≠ z
  sum : x+y+z=0
  qline : q 1=slope x y*q 0+intercept x y
  off : q 1≠(q 0)^3

private theorem has_mark (S : Finset ℝ²) (L : AffineSubspace ℝ ℝ²)
    (four : L ∈ linesWithPointsFor 4 (S : Set ℝ²))
    (three : 3 ≤ (S.filter (fun p => p ∈ L ∧ p 1 = (p 0)^3)).card) : Nonempty (Mark S L) := by
  classical
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp three
  obtain ⟨as,al,ac⟩ := Finset.mem_filter.mp ha
  obtain ⟨bs,bl,bc⟩ := Finset.mem_filter.mp hb
  obtain ⟨cs,cl,cc⟩ := Finset.mem_filter.mp hc
  have form : line[ℝ,curve (a 0),curve (b 0)] = L := by
    rw [← from_coord ac,← from_coord bc]
    exact OMA.R_Erdos101_erdos_101_R1.line_through four al bl hab
  have neq (p r : ℝ²) (pC : p 1=(p 0)^3) (rC : r 1=(r 0)^3) (ne : p ≠ r) : p 0 ≠ r 0 :=
    fun e => ne ((from_coord pC).trans ((congrArg curve e).trans (from_coord rC).symm))
  have xy := neq a b ac bc hab
  have xz := neq a c ac cc hac
  have yz := neq b c bc cc hbc
  have rootC := roots (cc ▸ secant (form ▸ cl))
  have z : c 0 = -(a 0+b 0) := (rootC.resolve_left xz.symm).resolve_left yz.symm
  have count : ({a,b,c} : Finset ℝ²).card < (S.filter (fun p => p ∈ L)).card := by
    rw [OMA.R_Erdos101_erdos_101_R1.four_points four]
    have bound : ({a,b,c} : Finset ℝ²).card ≤ 3 := Finset.card_le_three
    omega
  obtain ⟨q,hq⟩ := Finset.sdiff_nonempty_of_card_lt_card count
  obtain ⟨qmem,qavoid⟩ := Finset.mem_sdiff.mp hq
  obtain ⟨qs,ql⟩ := Finset.mem_filter.mp qmem
  have qline := secant (form ▸ ql)
  have off : q 1 ≠ (q 0)^3 := by
    intro qC
    rcases roots (qC ▸ qline) with eq|eq|eq
    · exact qavoid (Finset.mem_insert.mpr (Or.inl ((from_coord qC).trans ((congrArg curve eq).trans (from_coord ac).symm))))
    · exact qavoid (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl
        ((from_coord qC).trans ((congrArg curve eq).trans (from_coord bc).symm)))))
    · have e : q=c := (from_coord qC).trans ((congrArg curve (eq.trans z.symm)).trans (from_coord cc).symm)
      exact qavoid (by simp [e])
  exact ⟨⟨a 0,b 0,c 0,q,from_coord ac ▸ as,from_coord bc ▸ bs,from_coord cc ▸ cs,qs,form,xy,yz,
    by linarith only [z],qline,off⟩⟩

/-- Uniformly in the entire configuration, the number of four-point lines
containing three of its points on the cuspidal cubic is little-o of n². -/
theorem sparse_cubic_lines (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ S : Finset ℝ², N ≤ S.card → ∀ F : Finset (AffineSubspace ℝ ℝ²),
      (∀ L ∈ F, L ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧
        3 ≤ (S.filter (fun p => p ∈ L ∧ p 1 = (p 0)^3)).card) → (F.card : ℝ) < ε*(S.card : ℝ)^2 := by
  classical
  obtain ⟨N,bound⟩ := sparse_completed_secants ε hε
  refine ⟨N,?_⟩
  intro S hn F lines
  let mark (L : F) := Classical.choice (has_mark S L.val (lines L L.property).1 (lines L L.property).2)
  let key (L : F) := ((mark L).x,(mark L).y)
  let E := F.attach.image key
  have inj : Function.Injective key := by
    intro L M e
    apply Subtype.ext
    exact (mark L).line_eq.symm.trans ((congrArg (fun p : Pt => line[ℝ,curve p.1,curve p.2]) e).trans (mark M).line_eq)
  have size : E.card = F.card := (Finset.card_image_of_injective _ inj).trans Finset.card_attach
  let Q := S.image (fun p : ℝ² => (p 0,p 1))
  obtain ⟨A,larger,card⟩ := Infinite.exists_superset_card_eq (S.image (fun p : ℝ² => p 0)) S.card Finset.card_image_le
  have inc {x : ℝ} (hx : curve x ∈ S) : x ∈ A := larger (Finset.mem_image.mpr ⟨curve x,hx,rfl⟩)
  have pairs : E ⊆ A ×ˢ A := by
    intro p hp
    obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨inc (mark L).xs,inc (mark L).ys⟩
  rw [← size,← card]
  apply bound A (card ▸ hn) Q E (Finset.card_image_le.trans card.ge) pairs
  intro p hp
  obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp hp
  let m := mark L
  refine ⟨m.z,inc m.zs,(m.q 0,m.q 1),Finset.mem_image_of_mem _ m.qs,slope m.x m.y,intercept m.x m.y,
    m.xy,m.yz,m.sum,?_,?_,m.qline,m.off⟩
  · change m.x^3 = slope m.x m.y*m.x+intercept m.x m.y
    dsimp [slope,intercept]; ring
  · change m.y^3 = slope m.x m.y*m.y+intercept m.x m.y
    dsimp [slope,intercept]; ring

end Erdos101CubicLines

end
