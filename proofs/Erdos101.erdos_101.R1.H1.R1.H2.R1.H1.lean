import OMAReductions.R_Erdos101_erdos_101_R1_H1_R1_H2_R1
import Mathlib

/-! A shared matching of external secants to an arbitrary real plane curve.

Theorem `Erdos101RichSecantSamples.sample_from_four_lines` states the result
in terms of the original four-point lines of a finite Euclidean configuration.
At any fixed positive density of external centers and of four-point lines
through each center meeting the curve twice, a matching of any prescribed
size at least 25 is realized at a positive fraction of the centers.
Each realization comes with a partner center and all its actual pivots.

The proof uses derivative signs to pull a cut back through algebraic
correspondences, bounds the number of occupied rank boxes, and counts
repeated endpoint samples. Degree, density, and sample size determine the
constants. Formalization by @ubuwaits. -/

namespace Erdos101OrderedGrid

open scoped Classical

abbrev Pos := ℕ × ℕ

def grid (n : ℕ) : Finset Pos := Finset.range n ×ˢ Finset.range n
def block (k : ℕ) (p : Pos) : Pos := (p.1/k,p.2/k)
def fiber (G : Finset Pos) (k : ℕ) (c : Pos) := G.filter (fun p => block k p = c)
def occupied (G : Finset Pos) (k : ℕ) := G.image (block k)
def good (G : Finset Pos) (k r : ℕ) := (occupied G k).filter (fun c => r ≤ (fiber G k c).card)

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

lemma occupied_subset {G : Finset Pos} {n : ℕ} (h : G ⊆ grid n) (k : ℕ) :
    occupied G k ⊆ grid (n/k+1) := by
  intro p hp
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp (h hx)
  exact Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_range.mp ha).le)),
     Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_range.mp hb).le))⟩

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

end Erdos101OrderedGrid

noncomputable section
namespace Erdos101Parabola
open EuclideanGeometry Erdos101OrderedGrid
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
def richPairs (T : Finset ℝ²) (Y : ℝ² → Finset ℝ) (n t : ℕ) :=
  (T ×ˢ T).filter (fun e => e.1 ≠ e.2 ∧ n ≤ t*(Y e.1 ∩ Y e.2).card)

/-- Dense rows in a bipartite incidence relation force many pairs of rows
with a large common neighborhood. The diagonal contributes only linearly
many pairs. -/
lemma density_bound (T : Finset ℝ²) (X : Finset ℝ) (Y : ℝ² → Finset ℝ) {n s K : ℕ}
    (hn : 0 < n) (hX : X.card ≤ n) (hT : T.card ≤ n) (hY : ∀ p ∈ T, Y p ⊆ X)
    (many : n ≤ s*T.card) (rows : ∀ p ∈ T, n ≤ s*(Y p).card)
    (few : (richPairs T Y n (2*s^4)).card ≤ K*n) : n ≤ (2*s^4)*(1+K) := by
  let t := 2*s^4
  let D := T ×ˢ T
  let A := richPairs T Y n t
  let V := fun y => T.filter (fun p => y ∈ Y p)
  let O := fun e : ℝ² × ℝ² => (Y e.1 ∩ Y e.2).card
  let I := ∑ y ∈ X, (V y).card
  let Z := ∑ e ∈ D, O e
  have roweq {p : ℝ²} (hp : p ∈ T) : X.filter (fun y => y ∈ Y p) = Y p := by
    ext y
    exact Finset.mem_filter.trans (and_iff_right_of_imp (fun h => hY p hp h))
  have inc : ∑ p ∈ T, (Y p).card = I := calc
    _ = ∑ p ∈ T, (X.filter (fun y => y ∈ Y p)).card := Finset.sum_congr rfl (fun p hp => by rw [roweq hp])
    _ = I := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun p y => y ∈ Y p)
  have rn : T.card*n ≤ s*I := calc
    _ = ∑ _p ∈ T, n := by simp
    _ ≤ ∑ p ∈ T, s*(Y p).card := Finset.sum_le_sum rows
    _ = _ := by rw [← Finset.mul_sum,inc]
  have dense : n^2 ≤ s^2*I := calc
    _ ≤ (s*T.card)*n := by simpa [pow_two] using Nat.mul_le_mul_right n many
    _ = s*(T.card*n) := Nat.mul_assoc ..
    _ ≤ s*(s*I) := Nat.mul_le_mul_left s rn
    _ = _ := by ring
  have squares : ∑ y ∈ X, (V y).card^2 = Z := by
    have byY (y : ℝ) : (V y).card^2 = (D.filter (fun e => y ∈ Y e.1 ∧ y ∈ Y e.2)).card := by
      have eq : (V y ×ˢ V y) = D.filter (fun e => y ∈ Y e.1 ∧ y ∈ Y e.2) := by
        ext e
        simp only [D,V,Finset.mem_product,Finset.mem_filter]
        tauto
      rw [← eq,Finset.card_product,pow_two]
    have byE (e : ℝ² × ℝ²) (he : e ∈ D) :
        X.filter (fun y => y ∈ Y e.1 ∧ y ∈ Y e.2) = Y e.1 ∩ Y e.2 := by
      ext y
      simp only [Finset.mem_filter,Finset.mem_inter]
      exact and_iff_right_of_imp (fun h => hY e.1 (Finset.mem_product.mp he).1 h.1)
    calc
      _ = ∑ y ∈ X, (D.filter (fun e => y ∈ Y e.1 ∧ y ∈ Y e.2)).card :=
        Finset.sum_congr rfl (fun y _ => byY y)
      _ = ∑ e ∈ D, (X.filter (fun y => y ∈ Y e.1 ∧ y ∈ Y e.2)).card :=
        Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun y (e : ℝ² × ℝ²) => y ∈ Y e.1 ∧ y ∈ Y e.2)
      _ = _ := Finset.sum_congr rfl (fun e he => congrArg Finset.card (byE e he))
  have cs : I^2 ≤ X.card*Z := by
    have := Finset.sum_mul_sq_le_sq_mul_sq X (fun _ => (1 : ℕ)) (fun y => (V y).card)
    simpa [squares,I] using this
  have moment : n^3*n ≤ (s^4*Z)*n := calc
    _ = (n^2)^2 := by ring
    _ ≤ (s^2*I)^2 := Nat.pow_le_pow_left dense 2
    _ = s^4*I^2 := by ring
    _ ≤ s^4*(X.card*Z) := Nat.mul_le_mul_left _ cs
    _ ≤ s^4*(n*Z) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hX)
    _ = _ := by ring
  have lower : 2*n^3 ≤ t*Z := by
    change 2*n^3 ≤ (2*s^4)*Z
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.le_of_mul_le_mul_right moment hn)
  have heach (e : ℝ² × ℝ²) (he : e ∈ D) :
      t*O e ≤ n + (if e.1 = e.2 then t*n else 0) + (if e ∈ A then t*n else 0) := by
    have bound : t*O e ≤ t*n := Nat.mul_le_mul_left _ ((Finset.card_le_card
      ((Finset.inter_subset_left).trans (hY e.1 (Finset.mem_product.mp he).1))).trans hX)
    by_cases h₁ : e.1 = e.2
    · simp [h₁]
      omega
    · by_cases h₂ : e ∈ A
      · simp [h₁,h₂]
        omega
      · have lt : ¬ n ≤ t*O e := fun hh => h₂ (Finset.mem_filter.mpr ⟨he,h₁,hh⟩)
        simp [h₁,h₂]
        omega
  have hdiag : D.filter (fun e => e.1 = e.2) = T.diag := (Finset.diag_eq_filter ..).symm
  have hA : D ∩ A = A := Finset.inter_eq_right.mpr (Finset.filter_subset ..)
  have small : D.card ≤ n^2 := by
    simpa [D,pow_two] using Nat.mul_le_mul hT hT
  have upper : t*Z ≤ n^3 + t*n^2 + K*t*n^2 := calc
    _ = ∑ e ∈ D, t*O e := Finset.mul_sum ..
    _ ≤ ∑ e ∈ D, (n + (if e.1 = e.2 then t*n else 0) + (if e ∈ A then t*n else 0)) :=
      Finset.sum_le_sum heach
    _ = D.card*n + T.card*(t*n) + A.card*(t*n) := by
      simp [Finset.sum_add_distrib,← Finset.sum_filter,hdiag,hA]
    _ ≤ n^2*n + n*(t*n) + (K*n)*(t*n) := Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul_right _ small) (Nat.mul_le_mul_right _ hT)) (Nat.mul_le_mul_right _ few)
    _ = _ := by ring
  have finalBound : n*n^2 ≤ (t*(1+K))*n^2 := by nlinarith only [lower,upper]
  exact Nat.le_of_mul_le_mul_right finalBound (pow_pos hn _)
end Erdos101Parabola
end

/-
# A bound on the number of partners of one external secant center

Three noncollinear target endpoints suffice. The proof works over every
field, including the complex field used for generic samples on a curve.
-/

noncomputable section

namespace Erdos101SecantFibers

open MvPolynomial
open scoped Classical

variable {k : Type*} [Field k]

/-- Three pencils with noncollinear centers have at most one common point
for each ordered choice of one line from each pencil. -/
theorem three_pencils {V P : Type*} [AddCommGroup V] [Module k V] [AddTorsor V P]
    (Q A B C : Finset P) (a b c : P) (hn : ¬ Collinear k ({a,b,c} : Set P))
    (hQ : ∀ q ∈ Q, ∃ x ∈ A, ∃ y ∈ B, ∃ z ∈ C,
      q ∈ line[k,a,x] ∧ q ∈ line[k,b,y] ∧ q ∈ line[k,c,z]) :
    Q.card ≤ A.card*B.card*C.card := by
  classical
  choose x hx y hy z hz h using hQ
  let f (q : P) := if hq : q ∈ Q then ((x q hq,y q hq),z q hq) else ((a,b),c)
  have count : Q.card ≤ ((A ×ˢ B) ×ˢ C).card := by
    apply Finset.card_le_card_of_injOn f
    · intro q hq
      change q ∈ Q at hq
      change f q ∈ (A ×ˢ B) ×ˢ C
      simp only [f,dif_pos hq,Finset.mem_product]
      exact ⟨⟨hx q hq,hy q hq⟩,hz q hq⟩
    · intro q hq r hr he
      change q ∈ Q at hq
      change r ∈ Q at hr
      obtain ⟨⟨ex,ey⟩,ez⟩ : (x q hq = x r hr ∧ y q hq = y r hr) ∧ z q hq = z r hr := by
        simpa only [f,dif_pos hq,dif_pos hr,Prod.mk.injEq] using he
      obtain ⟨qa,qb,qc⟩ := h q hq
      obtain ⟨ra,rb,rc⟩ := h r hr
      rw [← ex] at ra
      rw [← ey] at rb
      rw [← ez] at rc
      by_contra qr
      have center {u v : P} (hq' : q ∈ line[k,u,v]) (hr' : r ∈ line[k,u,v]) : u ∈ line[k,q,r] := by
        rw [affineSpan_pair_eq_of_mem_of_mem_of_ne hq' hr' qr]
        exact left_mem_affineSpan_pair .. 
      exact hn (collinear_triple_of_mem_affineSpan_pair (center qa ra) (center qb rb) (center qc rc))
  simpa using count

private lemma affine_substitution_degree {σ : Type*} (F : MvPolynomial σ k) (u : σ → Polynomial k)
    (hu : ∀ i, (u i).natDegree ≤ 1) : ((eval₂Hom Polynomial.C u) F).natDegree ≤ F.totalDegree := by
  let φ := eval₂Hom Polynomial.C u
  have he : φ F = ∑ v ∈ F.support, φ (monomial v (coeff v F)) := by
    simpa only [map_sum] using congrArg φ F.as_sum
  change (φ F).natDegree ≤ _
  rw [he]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro v hv
  change ((eval₂Hom Polynomial.C u) (monomial v (coeff v F))).natDegree ≤ _
  rw [eval₂Hom_monomial]
  calc
    _ ≤ (Polynomial.C (coeff v F)).natDegree + (v.prod (fun i e => (u i)^e)).natDegree :=
      Polynomial.natDegree_mul_le
    _ = (v.prod (fun i e => (u i)^e)).natDegree := by rw [Polynomial.natDegree_C,zero_add]
    _ ≤ ∑ i ∈ v.support, ((u i)^(v i)).natDegree := Polynomial.natDegree_prod_le ..
    _ ≤ ∑ i ∈ v.support, v i := Finset.sum_le_sum (fun i _ =>
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (v i) (hu i)))
    _ ≤ F.totalDegree := le_totalDegree hv

/-- A line through a point outside a hypersurface has at most its degree
many distinct intersections in any finite set. -/
theorem line_section {σ : Type*} (F : MvPolynomial σ k) (p x : σ → k)
    (hp : eval p F ≠ 0) (Y : Finset (σ → k))
    (hY : ∀ y ∈ Y, y ∈ line[k,p,x] ∧ eval y F = 0) : Y.card ≤ F.totalDegree := by
  classical
  let u (i : σ) : Polynomial k := Polynomial.C (p i)+Polynomial.C (x i-p i)*Polynomial.X
  let g := (eval₂Hom Polynomial.C u) F
  have hv (t : k) : g.eval t = eval ((AffineMap.lineMap p x) t) F := by
    have comp : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id k := by ext; simp
    change (eval₂ Polynomial.C u F).eval t = _
    rw [polynomial_eval_eval₂,comp,eval₂_id]
    apply congrArg (fun v : σ → k => eval v F)
    funext i
    simp [u,AffineMap.lineMap_apply_module]
    ring
  have hn : g ≠ 0 := by
    intro hz
    apply hp
    simpa [hz] using (hv 0).symm
  have hsub : Y ⊆ g.roots.toFinset.image (fun t => (AffineMap.lineMap p x) t) := by
    intro y hy
    obtain ⟨hline,hzero⟩ := hY y hy
    obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hline
    exact Finset.mem_image.mpr ⟨t,Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hn).mpr
      (by change g.eval t = 0; rw [hv,ht,hzero])),ht⟩
  have hu (i : σ) : (u i).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_add_le ..).trans (max_le (by simp)
      (Polynomial.natDegree_mul_le.trans (by simp)))
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans
    ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' g).trans (affine_substitution_degree F u hu))))

/-- Each of three fixed source endpoints gives a line through the same
external center p. Every possible partner q must join each target endpoint
to a curve intersection on its corresponding source line. -/
theorem three_sample_fiber (F : MvPolynomial (Fin 2) k)
    (p x₁ x₂ x₃ z₁ z₂ z₃ : Fin 2 → k) (hp : eval p F ≠ 0)
    (hn : ¬ Collinear k ({z₁,z₂,z₃} : Set (Fin 2 → k)))
    (Q : Finset (Fin 2 → k))
    (hq : ∀ q ∈ Q, ∃ a b c : Fin 2 → k, eval a F = 0 ∧ eval b F = 0 ∧ eval c F = 0 ∧
      a ∈ line[k,p,x₁] ∧ b ∈ line[k,p,x₂] ∧ c ∈ line[k,p,x₃] ∧
      q ∈ line[k,z₁,a] ∧ q ∈ line[k,z₂,b] ∧ q ∈ line[k,z₃,c]) :
    Q.card ≤ F.totalDegree^3 := by
  classical
  choose a b c ha hb hc la lb lc qa qb qc using hq
  let A := Q.attach.image (fun q => a q.val q.property)
  let B := Q.attach.image (fun q => b q.val q.property)
  let C := Q.attach.image (fun q => c q.val q.property)
  have ha' := line_section F p x₁ hp A (by
    intro v hv
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨la _ q.property,ha _ q.property⟩)
  have hb' := line_section F p x₂ hp B (by
    intro v hv
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨lb _ q.property,hb _ q.property⟩)
  have hc' := line_section F p x₃ hp C (by
    intro v hv
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨lc _ q.property,hc _ q.property⟩)
  have hcount := three_pencils Q A B C z₁ z₂ z₃ hn (by
    intro q h
    exact ⟨_,Finset.mem_image.mpr ⟨⟨q,h⟩,Finset.mem_attach ..,rfl⟩,
      _,Finset.mem_image.mpr ⟨⟨q,h⟩,Finset.mem_attach ..,rfl⟩,
      _,Finset.mem_image.mpr ⟨⟨q,h⟩,Finset.mem_attach ..,rfl⟩,qa q h,qb q h,qc q h⟩)
  exact hcount.trans ((Nat.mul_le_mul (Nat.mul_le_mul ha' hb') hc').trans_eq (by ring))


end Erdos101SecantFibers
end

noncomputable section

namespace Erdos101SecantSamples

open EuclideanGeometry Erdos101OrderedGrid
open scoped Classical
/-- Some fixed sample attains the multiplicity needed by the ordered-grid count. -/
theorem repeated_sample (A : Finset ι) (graphs : ι → Finset Pos) {n t k r b : ℕ}
    (hk : 0 < k) (hn : k ≤ n) (large : 4*t*r*b ≤ k) (space : r ≤ (grid n).card)
    (hg : ∀ i ∈ A, graphs i ⊆ grid n)
    (hc : ∀ i ∈ A, (occupied (graphs i) k).card ≤ b*(n/k+1))
    (hr : ∀ i ∈ A, n ≤ t*(graphs i).card) :
    ∃ T ⊆ grid n, T.card=r ∧ A.card ≤ 8*t*k^(2+2*r)*(A.filter (fun i => T ⊆ graphs i)).card*n := by
  classical
  let m (T : Finset Pos) := (A.filter (fun i => T ⊆ graphs i)).card
  obtain ⟨T₀,hs₀,hn₀⟩ := Finset.exists_subset_card_eq space
  obtain ⟨T,hT,hmax⟩ := ((grid n).powersetCard r).exists_max_image m
    ⟨T₀,Finset.mem_powersetCard.mpr ⟨hs₀,hn₀⟩⟩
  obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hT
  refine ⟨T,hsub,hcard,rich_components A graphs hk hn large hg hc hr ?_⟩
  intro B hB
  by_cases h : B ⊆ grid n
  · exact hmax B (Finset.mem_powersetCard.mpr ⟨h,hB⟩)
  · have he : A.filter (fun i => B ⊆ graphs i) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun i hi hs => h (hs.trans (hg i hi)))
    simp [he]

private lemma line_card (S : Finset ℝ²) (hcap : NonCollinearFor 5 (S : Set ℝ²)) (a b : ℝ²) :
    (S.filter (fun p => p ∈ line[ℝ,a,b])).card ≤ 4 := by
  by_contra! h
  obtain ⟨U,hs,hn⟩ := Finset.exists_subset_card_eq (show 5 ≤ _ from h)
  apply hcap (U : Set ℝ²) (Finset.coe_subset.mpr (hs.trans (Finset.filter_subset ..))) U.finite_toSet (by simpa using hn)
  apply (collinear_iff_exists_forall_eq_smul_vadd _).mpr
  refine ⟨a,b -ᵥ a,?_⟩
  intro p hp
  obtain ⟨u,hu⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp (Finset.mem_filter.mp (hs hp)).2
  exact ⟨u,hu.symm⟩

private lemma avoid_pairs (E : Finset ι) (S : Finset ℝ²) (left right : ι → ℝ²)
    (hs : ∀ i ∈ E, left i ∈ S ∧ right i ∈ S) (hcap : NonCollinearFor 5 (S : Set ℝ²))
    (hl : Set.InjOn left E) (hr : Set.InjOn right E) (P : Finset (ι × ι)) (hN : 8*P.card < E.card) :
    ∃ c ∈ E, ∀ z ∈ P, left c ∉ line[ℝ,left z.1,left z.2] ∧ right c ∉ line[ℝ,right z.1,right z.2] := by
  classical
  let hit (f : ι → ℝ²) (z : ι × ι) := E.filter (fun i => f i ∈ line[ℝ,f z.1,f z.2])
  have hcount (f : ι → ℝ²) (hinj : Set.InjOn f E) (hf : ∀ i ∈ E, f i ∈ S) (z) :
      (hit f z).card ≤ 4 := by
    apply le_trans _ (line_card S hcap (f z.1) (f z.2))
    apply Finset.card_le_card_of_injOn f
    · intro i hi
      exact Finset.mem_filter.mpr ⟨hf i (Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2⟩
    · exact hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset ..))
  let B := P.biUnion (fun z => hit left z ∪ hit right z)
  have hB : B.card ≤ 8*P.card := calc
    _ ≤ ∑ z ∈ P, (hit left z ∪ hit right z).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ P, 8 := Finset.sum_le_sum (fun z _ => (Finset.card_union_le ..).trans
      (Nat.add_le_add (hcount left hl (fun i hi => (hs i hi).1) z)
        (hcount right hr (fun i hi => (hs i hi).2) z)))
    _ = _ := by simp [mul_comm]
  obtain ⟨c,hc⟩ := Finset.sdiff_nonempty_of_card_lt_card (hB.trans_lt hN)
  obtain ⟨hcE,hout⟩ := Finset.mem_sdiff.mp hc
  refine ⟨c,hcE,fun z hz => ⟨fun h => hout ?_,fun h => hout ?_⟩⟩
  · exact Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hcE,h⟩)⟩
  · exact Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hcE,h⟩)⟩

def independentTriple (left right : ι → ℝ²) (a b c : ι) : Prop :=
  (¬ Collinear ℝ ({left a,left b,left c} : Set ℝ²)) ∧
  (¬ Collinear ℝ ({right a,right b,right c} : Set ℝ²))

def frame (left right : ι → ℝ²) (a b c d : ι) : Prop :=
  independentTriple left right a b c ∧ independentTriple left right a b d ∧
  independentTriple left right a c d ∧ independentTriple left right b c d

/-- Every specified pair in a matching of size at least 25 can be the first
member of a projective frame on both sides. -/
theorem frame_with_first (E : Finset ι) (S : Finset ℝ²) (left right : ι → ℝ²)
    (hs : ∀ i ∈ E, left i ∈ S ∧ right i ∈ S) (hcap : NonCollinearFor 5 (S : Set ℝ²))
    (hl : Set.InjOn left E) (hr : Set.InjOn right E) (hN : 25 ≤ E.card) {a : ι} (ha : a ∈ E) :
    ∃ b ∈ E, ∃ c ∈ E, ∃ d ∈ E, frame left right a b c d := by
  classical
  have noncol {p q r : ℝ²} (hpq : p ≠ q) (hn : r ∉ line[ℝ,p,q]) :
      ¬ Collinear ℝ ({p,q,r} : Set ℝ²) := fun h =>
    hn (h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hpq)
  have make {i j v} (hi : i ∈ E) (hj : j ∈ E) (hne : i ≠ j)
      (h : left v ∉ line[ℝ,left i,left j] ∧ right v ∉ line[ℝ,right i,right j]) :
      independentTriple left right i j v :=
    ⟨noncol (fun e => hne (hl hi hj e)) h.1,noncol (fun e => hne (hr hi hj e)) h.2⟩
  obtain ⟨b,hb,hba⟩ := Finset.exists_mem_ne (s := E) (show 1 < E.card by omega) a
  have hab := Ne.symm hba
  obtain ⟨c,hc,off⟩ := avoid_pairs E S left right hs hcap hl hr {(a,b)} (by simp; omega)
  have abc := make ha hb hab (off (a,b) (by simp))
  have hac : a ≠ c := fun e => ne₁₃_of_not_collinear abc.1 (congrArg left e)
  have hbc : b ≠ c := fun e => ne₂₃_of_not_collinear abc.1 (congrArg left e)
  let P : Finset (ι × ι) := {(a,b),(a,c),(b,c)}
  have hP : P.card ≤ 3 := Finset.card_le_three
  obtain ⟨d,hd,off'⟩ := avoid_pairs E S left right hs hcap hl hr P (by omega)
  exact ⟨b,hb,c,hc,d,hd,abc,make ha hb hab (off' (a,b) (by simp [P])),
    make ha hc hac (off' (a,c) (by simp [P])),make hb hc hbc (off' (b,c) (by simp [P]))⟩

/-- Four matched pairs, in general position on both sides. -/
theorem simultaneous_frames (E : Finset ι) (S : Finset ℝ²) (left right : ι → ℝ²)
    (hs : ∀ i ∈ E, left i ∈ S ∧ right i ∈ S) (hcap : NonCollinearFor 5 (S : Set ℝ²))
    (hl : Set.InjOn left E) (hr : Set.InjOn right E) (hN : 25 ≤ E.card) :
    ∃ a ∈ E, ∃ b ∈ E, ∃ c ∈ E, ∃ d ∈ E,
      independentTriple left right a b c ∧ independentTriple left right a b d ∧
      independentTriple left right a c d ∧ independentTriple left right b c d := by
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < E.card by omega)
  exact ⟨a,ha,frame_with_first E S left right hs hcap hl hr hN ha⟩
abbrev Poly := MvPolynomial (Fin 2) ℝ
/-- One pivot on the curve witnesses an ordered endpoint pair for these centers. -/
def hasPivot (F : Poly) (p q x z : ℝ²) : Prop :=
  ∃ y : ℝ², MvPolynomial.eval (fun i => y i) F=0 ∧ y ∈ line[ℝ,p,x] ∧ q ∈ line[ℝ,z,y]

private def coord := WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)

private lemma coord_line {p x y : ℝ²} (h : y ∈ line[ℝ,p,x]) :
    coord y ∈ line[ℝ,coord p,coord x] := by
  obtain ⟨s,hs⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp h
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  refine ⟨s,?_⟩
  rw [← hs]
  simp [AffineMap.lineMap_apply_module]

private lemma coord_noncol {x y z : ℝ²} (h : ¬ Collinear ℝ ({x,y,z} : Set ℝ²)) :
    ¬ Collinear ℝ ({coord x,coord y,coord z} : Set (Fin 2 → ℝ)) := by
  intro h'
  obtain ⟨b,v,hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp h'
  apply h ((collinear_iff_exists_forall_eq_smul_vadd _).mpr ?_)
  refine ⟨coord.symm b,coord.symm v,?_⟩
  intro a ha
  have hm : coord a ∈ ({coord x,coord y,coord z} : Set (Fin 2 → ℝ)) := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl <;> simp
  obtain ⟨s,hs⟩ := hv _ hm
  refine ⟨s,?_⟩
  apply coord.injective
  simpa [vadd_eq_add] using hs

/-- Count distinct first centers of realizations, accounting for repeated partners. -/
theorem sample_first_centers (F : Poly) (A : Finset (ℝ² × ℝ²)) (left right : ι → ℝ²)
    (a b c : ι) (hn : ¬ Collinear ℝ ({right a,right b,right c} : Set ℝ²))
    (outside : ∀ e ∈ A, MvPolynomial.eval (fun i => e.1 i) F ≠ 0)
    (hits : ∀ e ∈ A, hasPivot F e.1 e.2 (left a) (right a) ∧
      hasPivot F e.1 e.2 (left b) (right b) ∧ hasPivot F e.1 e.2 (left c) (right c)) :
    A.card ≤ F.totalDegree^3*(A.image Prod.fst).card := by
  classical
  apply Finset.card_le_mul_card_image
  intro p hp
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
  let fiber := A.filter (fun w => w.1=e.1)
  let endpoint (w : ℝ² × ℝ²) := coord w.2
  have hinj : Set.InjOn endpoint fiber := by
    intro w hw s hs h
    exact Prod.ext ((Finset.mem_filter.mp hw).2.trans (Finset.mem_filter.mp hs).2.symm)
      (coord.injective h)
  change fiber.card ≤ _
  rw [← Finset.card_image_of_injOn hinj]
  apply Erdos101SecantFibers.three_sample_fiber F (coord e.1) (coord (left a)) (coord (left b))
    (coord (left c)) (coord (right a)) (coord (right b)) (coord (right c)) (outside e he) (coord_noncol hn)
  intro q hq
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hwA,hp'⟩ := Finset.mem_filter.mp hw
  obtain ⟨⟨y,hy,ly,ry⟩,⟨u,hu,lu,ru⟩,⟨v,hv,lv,rv⟩⟩ := hits w hwA
  rw [hp'] at ly lu lv
  exact ⟨coord y,coord u,coord v,hy,hu,hv,coord_line ly,coord_line lu,coord_line lv,
    coord_line ry,coord_line ru,coord_line rv⟩
end Erdos101SecantSamples
end

/- Finite derivative-sign tests for comparing the endpoints of algebraic
secant correspondences. The univariate facts are Thom's lemma and the
order on Thom encodings. They apply to different specialized polynomials
of the same bounded degree. -/

noncomputable section
namespace Erdos101SecantOrder

open Polynomial Set
open scoped Classical

/-- The i-th formal derivative, starting with the polynomial itself. -/
def diff : ℕ → ℝ[X] → ℝ[X]
  | 0, f => f
  | i+1, f => diff i f.derivative

def code (d : ℕ) (f : ℝ[X]) (x : ℝ) (i : Fin (d+1)) : SignType :=
  SignType.sign ((diff i.val f).eval x)

private lemma head {d : ℕ} {f g : ℝ[X]} {x y : ℝ} (h : code d f x = code d g y) :
    SignType.sign (f.eval x) = SignType.sign (g.eval y) := congrFun h 0

private lemma tail {d : ℕ} {f g : ℝ[X]} {x y : ℝ} (h : code (d+1) f x = code (d+1) g y) :
    code d f.derivative x = code d g.derivative y := funext (fun i => congrFun h i.succ)

private lemma combine {d : ℕ} {f g : ℝ[X]} {x y : ℝ}
    (h : SignType.sign (f.eval x) = SignType.sign (g.eval y))
    (t : code d f.derivative x = code d g.derivative y) : code (d+1) f x = code (d+1) g y := by
  funext i; refine Fin.cases h (fun j => congrFun t j) i

private lemma derivative_degree {f : ℝ[X]} {d : ℕ} (h : f.natDegree ≤ d+1) : f.derivative.natDegree ≤ d :=
  (Polynomial.natDegree_derivative_le _).trans (by omega)

private lemma constant_code {f : ℝ[X]} (deg : f.natDegree ≤ 0) (a b : ℝ) : code 0 f a = code 0 f b := by
  funext i; fin_cases i; change SignType.sign (f.eval a) = SignType.sign (f.eval b)
  rw [Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero deg)]; simp

private lemma sign_nonneg {x y : ℝ} (same : SignType.sign x = SignType.sign y) (hy : 0 ≤ y) : 0 ≤ x := by
  by_contra! hx
  exact (not_lt_of_ge hy) (sign_eq_neg_one_iff.mp (same.symm.trans (sign_neg hx)))

private lemma sign_nonpos {x y : ℝ} (same : SignType.sign x = SignType.sign y) (hy : y ≤ 0) : x ≤ 0 := by
  by_contra! hx
  exact (not_lt_of_ge hy) (sign_eq_one_iff.mp (same.symm.trans (sign_pos hx)))

private lemma directions {f : ℝ[X]} {a b : ℝ}
    (constant : ∀ z ∈ Icc a b, SignType.sign (f.derivative.eval z) = SignType.sign (f.derivative.eval a)) :
    (0 ≤ f.derivative.eval a → MonotoneOn f.eval (Icc a b)) ∧
    (f.derivative.eval a ≤ 0 → AntitoneOn f.eval (Icc a b)) := by
  constructor <;> intro h
  · apply monotoneOn_of_deriv_nonneg (convex_Icc ..) f.continuous.continuousOn f.differentiable.differentiableOn
    intro x hx; rw [f.deriv]; exact sign_nonneg (constant _ (interior_subset hx)) h
  · apply antitoneOn_of_deriv_nonpos (convex_Icc ..) f.continuous.continuousOn f.differentiable.differentiableOn
    intro x hx; rw [f.deriv]; exact sign_nonpos (constant _ (interior_subset hx)) h

/-- Each complete sign condition on a polynomial and all its derivatives
holds throughout the interval between any two points realizing it. -/
theorem interval_code (d : ℕ) {f : ℝ[X]} (deg : f.natDegree ≤ d) {a b : ℝ}
    (same : code d f a = code d f b) {z : ℝ} (hz : z ∈ Icc a b) : code d f a = code d f z := by
  induction d generalizing f a b z with
  | zero => exact constant_code deg a z
  | succ d ih =>
    have t := tail same
    have within (x : ℝ) (hx : x ∈ Icc a b) := ih (derivative_degree deg) t hx
    apply combine _ (within z hz)
    have dir := directions (fun x hx => (head (within x hx)).symm)
    have ab := hz.1.trans hz.2
    obtain pos | neg := le_total 0 (f.derivative.eval a)
    · have mono := dir.1 pos
      have left := SignType.sign.monotone (mono (left_mem_Icc.mpr ab) hz hz.1)
      have right := SignType.sign.monotone (mono hz (right_mem_Icc.mpr ab) hz.2)
      exact le_antisymm left (right.trans (head same).symm.le)
    · have anti := dir.2 neg
      have left := SignType.sign.monotone (anti (left_mem_Icc.mpr ab) hz hz.1)
      have right := SignType.sign.monotone (anti hz (right_mem_Icc.mpr ab) hz.2)
      exact le_antisymm ((head same).le.trans right) left

/-- If matching sign codes occur in opposite orders for two polynomials,
the two endpoint codes must be identical. -/
theorem reverse_codes (d : ℕ) {f g : ℝ[X]} (df : f.natDegree ≤ d) (dg : g.natDegree ≤ d)
    {a b c e : ℝ} (ab : a ≤ b) (ec : e ≤ c) (ac : code d f a = code d g c)
    (be : code d f b = code d g e) : code d f a = code d f b := by
  induction d generalizing f g with
  | zero => exact constant_code df a b
  | succ d ih =>
    have df' := derivative_degree df
    have dg' := derivative_degree dg
    have t := ih df' dg' (tail ac) (tail be)
    have tg := (tail be).symm.trans (t.symm.trans (tail ac))
    have fdir := directions (fun x hx => (head (interval_code d df' t hx)).symm)
    have gdir := directions (fun x hx => (head (interval_code d dg' tg hx)).symm)
    have sg := head ((tail be).symm.trans t.symm)
    apply combine _ t
    obtain pos | neg := le_total 0 (f.derivative.eval a)
    · have h := SignType.sign.monotone (fdir.1 pos (left_mem_Icc.mpr ab) (right_mem_Icc.mpr ab) ab)
      have k := SignType.sign.monotone (gdir.1 (sign_nonneg sg pos) (left_mem_Icc.mpr ec) (right_mem_Icc.mpr ec) ec)
      exact le_antisymm h ((head be).le.trans (k.trans (head ac).symm.le))
    · have h := SignType.sign.monotone (fdir.2 neg (left_mem_Icc.mpr ab) (right_mem_Icc.mpr ab) ab)
      have k := SignType.sign.monotone (gdir.2 (sign_nonpos sg neg) (left_mem_Icc.mpr ec) (right_mem_Icc.mpr ec) ec)
      exact le_antisymm ((head ac).le.trans (k.trans (head be).symm.le)) h

private lemma different_from_root {d : ℕ} {f : ℝ[X]} (df : f.natDegree ≤ d) (nonzero : f ≠ 0)
    {a b : ℝ} (ab : a < b) (ra : f.eval a = 0) : code d f a ≠ code d f b := by
  intro same
  apply nonzero
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (Set.Icc_infinite ab).mono
  intro z hz
  have eq := head (interval_code d df same hz)
  exact sign_eq_zero_iff.mp (eq.symm.trans (ra ▸ sign_zero))

/-- For roots with a fixed code, the sign codes at a threshold determine
on which side of that threshold the root lies. -/
theorem cut_iff {d : ℕ} {f g : ℝ[X]} (df : f.natDegree ≤ d) (dg : g.natDegree ≤ d)
    (nf : f ≠ 0) (ng : g ≠ 0) {u v t : ℝ} (fu : f.eval u = 0) (gv : g.eval v = 0)
    (roots : code d f u = code d g v) (cuts : code d f t = code d g t) : u < t ↔ v < t := by
  constructor
  · intro h; by_contra! bad
    exact different_from_root df nf h fu (reverse_codes d df dg h.le bad roots cuts)
  · intro h; by_contra! bad
    exact different_from_root dg ng h gv (reverse_codes d dg df h.le bad roots.symm cuts.symm)

end Erdos101SecantOrder
end

/- For a fixed Thom encoding, a horizontal threshold on the roots of a
polynomial relation pulls back to finitely many cuts on its input axis.
These cut counts multiply when relations are composed. -/

noncomputable section
namespace Erdos101SecantCuts

open Polynomial Set Erdos101SecantOrder
open scoped Classical

/-- Two numbers occupy the same side of t, with equality distinguished. -/
def SameSide (a b t : ℝ) : Prop := (a<t ↔ b<t) ∧ (a=t ↔ b=t)

def SameCell (B : Finset ℝ) (a b : ℝ) : Prop := ∀ t ∈ B, SameSide a b t

private lemma sameCell_symm {B : Finset ℝ} {a b : ℝ} (same : SameCell B a b) : SameCell B b a :=
  fun t ht => ⟨(same t ht).1.symm,(same t ht).2.symm⟩

private lemma no_cut {B : Finset ℝ} {a b : ℝ} (ab : a<b) (same : SameCell B a b)
    {t : ℝ} (ht : t ∈ B) : t ∉ Icc a b := by
  intro mem
  rcases mem.1.eq_or_lt with eq | lt
  · exact ab.ne (eq.trans (((same t ht).2.mp eq).symm))
  · exact (not_lt_of_ge mem.2) ((same t ht).1.mp lt)

private lemma constant_sign_forward (f : ℝ[X]) {a b : ℝ} (ab : a<b)
    (same : SameCell f.roots.toFinset a b) : SignType.sign (f.eval a) = SignType.sign (f.eval b) := by
  by_cases hz : f=0
  · simp [hz]
  have away (z : ℝ) (mem : z ∈ Icc a b) (zero : f.eval z=0) : False :=
    no_cut ab same (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hz).mpr zero)) mem
  rcases lt_or_gt_of_ne (away a (left_mem_Icc.mpr ab.le)) with neg|pos
  · have last : f.eval b < 0 := by
      by_contra! bad
      obtain ⟨z,mem,hz⟩ := intermediate_value_Icc ab.le f.continuous.continuousOn (show (0:ℝ) ∈ Icc (f.eval a) (f.eval b) from ⟨neg.le,bad⟩)
      exact away z mem hz
    rw [sign_neg neg, sign_neg last]
  · have last : 0 < f.eval b := by
      by_contra! bad
      obtain ⟨z,mem,hz⟩ := intermediate_value_Icc' ab.le f.continuous.continuousOn (show (0:ℝ) ∈ Icc (f.eval b) (f.eval a) from ⟨bad,pos.le⟩)
      exact away z mem hz
    rw [sign_pos pos,sign_pos last]

private lemma constant_sign (f : ℝ[X]) {a b : ℝ} (same : SameCell f.roots.toFinset a b) :
    SignType.sign (f.eval a) = SignType.sign (f.eval b) := by
  rcases lt_trichotomy a b with lt|eq|gt
  · exact constant_sign_forward f lt same
  · rw [eq]
  · exact (constant_sign_forward f gt (sameCell_symm same)).symm

private lemma root_unique {d : ℕ} {f : ℝ[X]} (deg : f.natDegree ≤ d) (nonzero : f ≠ 0)
    {u t : ℝ} (root : f.eval u=0) (same : code d f u=code d f t) : u=t := by
  have sub (a b : ℝ) (lt : a<b) (ra : f.eval a=0) (eq : code d f a=code d f b) : False := by
    apply nonzero (f.eq_zero_of_infinite_isRoot ((Set.Icc_infinite lt).mono ?_))
    intro z hz
    have h := congrFun (interval_code d deg eq hz) 0
    change SignType.sign (f.eval a) = SignType.sign (f.eval z) at h
    exact sign_eq_zero_iff.mp (h.symm.trans (ra ▸ sign_zero))
  rcases lt_trichotomy u t with h|h|h
  · exact False.elim (sub u t h root same)
  · exact h
  · have hh := congrFun same 0
    change SignType.sign (f.eval u) = SignType.sign (f.eval t) at hh
    exact False.elim (sub t u h (sign_eq_zero_iff.mp (hh.symm.trans (root ▸ sign_zero))) same.symm)

private lemma root_position {d : ℕ} {f g : ℝ[X]} (df : f.natDegree ≤ d) (dg : g.natDegree ≤ d)
    (nf : f ≠ 0) (ng : g ≠ 0) {u v t : ℝ} (fu : f.eval u=0) (gv : g.eval v=0)
    (rs : code d f u=code d g v) (cs : code d f t=code d g t) : SameSide u v t := by
  refine ⟨cut_iff df dg nf ng fu gv rs cs,?_⟩
  constructor
  · rintro rfl; exact root_unique dg ng gv (rs.symm.trans cs)
  · rintro rfl; exact root_unique df nf fu (rs.trans cs.symm)

/-- Each output threshold needs at most K input cuts, independently of the
number of data points and of the value of that threshold. -/
def Pulls (R : ℝ → ℝ → Prop) (K : ℕ) : Prop :=
  ∀ t : ℝ, ∃ B : Finset ℝ, B.card ≤ K ∧ ∀ {x x' y y' : ℝ}, R x y → R x' y' →
    SameCell B x x' → SameSide y y' t

def Branch (f : ℝ → ℝ[X]) (d : ℕ) (σ : Fin (d+1) → SignType) (x y : ℝ) : Prop :=
  f x ≠ 0 ∧ (f x).eval y=0 ∧ code d (f x) y=σ

/-- For bounded bidegree (e,d), a branch requires at most (d+1)e cuts
per threshold. Pairs may be on unrelated real components of the curve. -/
theorem branch_pulls (f : ℝ → ℝ[X]) (d e : ℕ) (degree : ∀ x, (f x).natDegree ≤ d)
    (profiles : ∀ t : ℝ, ∀ i : Fin (d+1), ∃ P : ℝ[X], P.natDegree ≤ e ∧
      ∀ x : ℝ, (diff i.val (f x)).eval t = P.eval x) (σ : Fin (d+1) → SignType) :
    Pulls (Branch f d σ) ((d+1)*e) := by
  classical
  intro t
  choose P deg val using profiles t
  let B := Finset.univ.biUnion (fun i => (P i).roots.toFinset)
  have bound : B.card ≤ (d+1)*e := calc
    _ ≤ ∑ i : Fin (d+1), (P i).roots.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin (d+1), e := Finset.sum_le_sum (fun i _ => (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans (deg i)))
    _ = _ := by simp
  refine ⟨B,bound,?_⟩
  intro x x' y y' h h' same
  refine root_position (degree x) (degree x') h.1 h'.1 h.2.1 h'.2.1 (h.2.2.trans h'.2.2.symm) ?_
  funext i
  simp only [code,val]
  apply constant_sign
  exact fun u hu => same u (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hu⟩)

/-- Successive algebraic correspondences pull back the same threshold
through their actual shared intermediate value. -/
theorem compose {R T : ℝ → ℝ → Prop} {k l : ℕ} (first : Pulls R k) (second : Pulls T l) :
    Pulls (fun x z => ∃ y, R x y ∧ T y z) (l*k) := by
  classical
  intro t
  obtain ⟨C,size,after⟩ := second t
  choose B bd before using first
  refine ⟨C.biUnion B,?_,?_⟩
  · calc
      _ ≤ ∑ v ∈ C, (B v).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ C, k := Finset.sum_le_sum (fun v _ => bd v)
      _ ≤ _ := by simpa using Nat.mul_le_mul_right k size
  · intro x x' z z' h h' same
    obtain ⟨y,xy,yz⟩ := h
    obtain ⟨y',xy',yz'⟩ := h'
    apply after yz yz'
    intro c hc
    apply before c xy xy'
    exact fun b hb => same b (Finset.mem_biUnion.mpr ⟨c,hc,hb⟩)

end Erdos101SecantCuts
end

/- A bounded number of one-dimensional cuts per threshold gives a linear
bound for the number of occupied boxes of any ranked Cartesian grid. -/

noncomputable section
namespace Erdos101SecantBlocks

open Erdos101SecantCuts Erdos101Parabola Erdos101OrderedGrid
open scoped Classical

private def key (B : Finset ℝ) (x : ℝ) := (rank B x,decide (x ∈ B))

private lemma key_controls {B : Finset ℝ} {a b : ℝ} (eq : key B a=key B b) : SameCell B a b := by
  have r : rank B a = rank B b := congrArg Prod.fst eq
  have e : (a ∈ B) ↔ b ∈ B := by simpa only [key,decide_eq_decide] using congrArg Prod.snd eq
  have eqIf {x y : ℝ} (rk : rank B x=rank B y) (hx : x∈B) (hy : y∈B) : x=y := by
    rcases lt_trichotomy x y with lt|h|gt
    · exact False.elim ((rank_strict B hx lt).ne rk)
    · exact h
    · exact False.elim ((rank_strict B hy gt).ne rk.symm)
  intro z hz
  have threshold {x y : ℝ} (rk : rank B x=rank B y) (mem : x∈B ↔ y∈B) (h : x<z) : y<z := by
    by_contra! bad
    rcases bad.eq_or_lt with gz|lt
    · exact h.ne ((eqIf rk (mem.mpr (gz ▸ hz)) (gz ▸ hz)).trans gz.symm)
    · exact ((rank_mono B h.le).trans_lt (rank_strict B hz lt)).ne rk
  refine ⟨⟨threshold r e,threshold r.symm e.symm⟩,?_⟩
  constructor
  · rintro rfl; exact (eqIf r hz (e.mp hz)).symm
  · rintro rfl; exact eqIf r (e.mpr hz) hz

private lemma bucket_cuts (X : Finset ℝ) (g : ℝ → ℕ) (m : ℕ) (mono : Monotone g)
    (bounded : ∀ x∈X, g x < m) : ∃ V : Finset ℝ, V.card ≤ m ∧
      ∀ x ∈ X, ∀ y ∈ X, SameCell V x y → g x = g y := by
  classical
  let J := X.image g
  let fiber (j : J) := X.filter (fun x => g x=j.val)
  have active (j : J) : (fiber j).Nonempty := by
    obtain ⟨x,hx,e⟩ := Finset.mem_image.mp j.property
    exact ⟨x,Finset.mem_filter.mpr ⟨hx,e⟩⟩
  let start (j : J) := (fiber j).min' (active j)
  let V := J.attach.image start
  have bound : J ⊆ Finset.range m := by
    intro v hv; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_range.mpr (bounded x hx)
  have small : V.card ≤ m := calc
    _ ≤ J.attach.card := Finset.card_image_le
    _ = J.card := Finset.card_attach
    _ ≤ (Finset.range m).card := Finset.card_le_card bound
    _ = _ := Finset.card_range _
  refine ⟨V,small,?_⟩
  intro x hx y hy cells
  have forbid {a b : ℝ} (hb : b ∈ X) (cuts : ∀ z ∈ V, a<z ↔ b<z) (lt : g a<g b) : False := by
    let j : J := ⟨g b,Finset.mem_image_of_mem g hb⟩
    have hm : start j ∈ fiber j := Finset.min'_mem _ _
    have value : g (start j)=g b := (Finset.mem_filter.mp hm).2
    have top : start j ≤ b := Finset.min'_le (fiber j) b (show b ∈ fiber j from Finset.mem_filter.mpr ⟨hb,rfl⟩)
    have bottom : a<start j := by
      by_contra! other; exact (not_lt_of_ge (value ▸ mono other)) lt
    have included : start j ∈ V := Finset.mem_image_of_mem _ (Finset.mem_attach _ _)
    exact (not_lt_of_ge top) ((cuts _ included).mp bottom)
  exact le_antisymm (le_of_not_gt (forbid hx (fun z h => (cells z h).1.symm)))
    (le_of_not_gt (forbid hy (fun z h => (cells z h).1)))

/-- For a relation admitting K input cuts per output cut, any records
inside X×X occupy at most 2(K+2)(|X|/k+1) boxes of side k ranks. -/
theorem occupied_le {R : ℝ → ℝ → Prop} {K : ℕ} (pull : Pulls R K) (X : Finset ℝ)
    (P : Finset (ℝ × ℝ)) (inside : P ⊆ X ×ˢ X) (hits : ∀ p∈P, R p.1 p.2) (k : ℕ) :
    (occupied (P.image (ranks X)) k).card ≤ 2*(K+2)*(X.card/k+1) := by
  classical
  let m := X.card/k+1
  let g (a : ℝ) := rank X a/k
  have mono : Monotone g := fun _ _ h => Nat.div_le_div_right (rank_mono X h)
  have bounded (x : ℝ) (hx : x∈X) : g x < m := Nat.lt_succ_of_le (Nat.div_le_div_right (rank_lt_card X hx).le)
  obtain ⟨V,small,controls⟩ := bucket_cuts X g m mono bounded
  choose B size pulls using pull
  let C := V ∪ V.biUnion B
  have cb : C.card ≤ m + m*K := calc
    _ ≤ V.card+(V.biUnion B).card := Finset.card_union_le ..
    _ ≤ V.card+∑ t ∈ V, (B t).card := Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ V.card+∑ _ ∈ V, K := Nat.add_le_add_left (Finset.sum_le_sum (fun t _ => size t)) _
    _ ≤ _ := by simpa using Nat.add_le_add small (Nat.mul_le_mul_right K small)
  let cells := occupied (P.image (ranks X)) k
  have found (b : cells) : ∃ p ∈ P, block k (ranks X p) = b.val := by
    obtain ⟨w,hw,eq⟩ := Finset.mem_image.mp b.property
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hw
    exact ⟨p,hp,eq⟩
  choose pt mem blockEq using found
  let index (j : cells) := key C (pt j).1
  have inj : Function.Injective index := by
    intro i j eq
    have h := key_controls eq
    have si := Finset.mem_product.mp (inside (mem i))
    have sj := Finset.mem_product.mp (inside (mem j))
    have inX : SameCell V (pt i).1 (pt j).1 := fun t ht => h t (Finset.mem_union_left _ ht)
    have inY : SameCell V (pt i).2 (pt j).2 := by
      intro t ht
      apply pulls t (hits _ (mem i)) (hits _ (mem j))
      exact fun z hz => h z (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨t,ht,hz⟩))
    apply Subtype.ext
    rw [← blockEq i,← blockEq j]
    exact Prod.ext (controls _ si.1 _ sj.1 inX) (controls _ si.2 _ sj.2 inY)
  have bounds : cells.attach.image index ⊆ Finset.range (C.card+1) ×ˢ (Finset.univ : Finset Bool) := by
    intro q hq; obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_filter_le ..)),Finset.mem_univ _⟩
  have cm := Finset.card_le_card bounds
  rw [Finset.card_image_of_injective _ inj,Finset.card_attach,Finset.card_product,Finset.card_range] at cm
  change cells.card ≤ 2*(K+2)*m
  have mpos : 1 ≤ m := Nat.le_add_left 1 _
  simp only [Finset.card_univ,Fintype.card_bool] at cm
  nlinarith only [cm,cb,mpos]

/-- The bounds for finitely many branches add, allowing a different
branch, or several witnesses, for every individual record. -/
theorem colored_occupied {ι : Type*} [Fintype ι] (R : ι → ℝ → ℝ → Prop) {K : ℕ}
    (pull : ∀ i, Pulls (R i) K) (X : Finset ℝ) (P : Finset (ℝ × ℝ))
    (inside : P ⊆ X ×ˢ X) (hits : ∀ p∈P, ∃ i, R i p.1 p.2) (k : ℕ) :
    (occupied (P.image (ranks X)) k).card ≤ (Fintype.card ι*(2*(K+2)))*(X.card/k+1) := by
  classical
  let part (i : ι) := P.filter (fun p => R i p.1 p.2)
  let boxes (i : ι) := occupied ((part i).image (ranks X)) k
  have cover : occupied (P.image (ranks X)) k ⊆ Finset.univ.biUnion boxes := by
    intro b hb
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨i,hi⟩ := hits p hp
    apply Finset.mem_biUnion.mpr
    exact ⟨i,Finset.mem_univ _,Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hp,hi⟩ : p ∈ part i))⟩
  have bound (i : ι) : (boxes i).card ≤ 2*(K+2)*(X.card/k+1) :=
    occupied_le (pull i) X (part i) ((Finset.filter_subset ..).trans inside) (fun _ hp => (Finset.mem_filter.mp hp).2) k
  calc
    _ ≤ (Finset.univ.biUnion boxes).card := Finset.card_le_card cover
    _ ≤ ∑ i : ι, (boxes i).card := Finset.card_biUnion_le
    _ ≤ ∑ _ : ι, 2*(K+2)*(X.card/k+1) := Finset.sum_le_sum (fun i _ => bound i)
    _ = _ := by simp [Nat.mul_assoc]

end Erdos101SecantBlocks
end

/- Bivariate polynomial input for the cut estimate. The two degrees are
bounded by the same integer. The resulting bound is uniform in the real
coefficients of the polynomial and in the chosen threshold. -/

noncomputable section
namespace Erdos101SecantPolynomials

open Polynomial Erdos101SecantOrder Erdos101SecantCuts
open scoped Classical

abbrev Bi := Polynomial (Polynomial ℝ)

def specialize (P : Bi) (x : ℝ) : ℝ[X] := P.map (evalRingHom x)

def evalAt (x y : ℝ) : Bi →+* ℝ := (evalRingHom y).comp (mapRingHom (evalRingHom x))

def scalar (a : ℝ) : Bi := C (C a)
def input : Bi := C X
def output : Bi := X

@[simp] lemma eval_scalar (x y a : ℝ) : evalAt x y (scalar a)=a := by simp [evalAt,scalar]
@[simp] lemma eval_input (x y : ℝ) : evalAt x y input=x := by simp [evalAt,input]
@[simp] lemma eval_output (x y : ℝ) : evalAt x y output=y := by simp [evalAt,output]

/-- Every monomial has both individual exponents at most d. -/
def Box (d : ℕ) (P : Bi) : Prop := P.natDegree ≤ d ∧ ∀ i, (P.coeff i).natDegree ≤ d

lemma Box.mono {P : Bi} {d e : ℕ} (Pbd : Box d P) (de : d ≤ e) : Box e P :=
  ⟨Pbd.1.trans de,fun i => (Pbd.2 i).trans de⟩

lemma box_scalar (a : ℝ) : Box 0 (scalar a) := by
  refine ⟨by simp [scalar],?_⟩
  intro i; rw [scalar,coeff_C]; split <;> simp

lemma box_input : Box 1 input := by
  refine ⟨by simp [input],?_⟩
  intro i; rw [input,coeff_C]; split <;> simp

lemma box_output : Box 1 output := by
  refine ⟨by simp [output],?_⟩
  intro i; rw [output,coeff_X]; split <;> simp

lemma Box.add {P Q : Bi} {d : ℕ} (h : Box d P) (k : Box d Q) : Box d (P+Q) := by
  refine ⟨(natDegree_add_le ..).trans (max_le h.1 k.1),?_⟩
  intro i; rw [coeff_add]; exact (natDegree_add_le ..).trans (max_le (h.2 i) (k.2 i))

lemma Box.sub {P Q : Bi} {d : ℕ} (h : Box d P) (k : Box d Q) : Box d (P-Q) := by
  refine ⟨(natDegree_sub_le ..).trans (max_le h.1 k.1),?_⟩
  intro i; rw [coeff_sub]; exact (natDegree_sub_le ..).trans (max_le (h.2 i) (k.2 i))

lemma Box.mul {P Q : Bi} {d e : ℕ} (h : Box d P) (k : Box e Q) : Box (d+e) (P*Q) := by
  refine ⟨natDegree_mul_le.trans (Nat.add_le_add h.1 k.1),?_⟩
  intro i; rw [coeff_mul]; apply Polynomial.natDegree_sum_le_of_forall_le
  intro u _; exact natDegree_mul_le.trans (Nat.add_le_add (h.2 u.1) (k.2 u.2))

lemma Box.pow {P : Bi} {d : ℕ} (h : Box d P) (n : ℕ) : Box (d*n) (P^n) := by
  induction n with
  | zero => simpa [scalar] using box_scalar 1
  | succ n ih => simpa only [Nat.mul_succ,pow_succ] using ih.mul h

lemma box_sum {α : Type*} (A : Finset α) {P : α → Bi} {d : ℕ} (bd : ∀ a∈A, Box d (P a)) :
    Box d (∑ a∈A, P a) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa [scalar] using (box_scalar 0).mono (Nat.zero_le d)
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    exact (bd a (Finset.mem_insert_self ..)).add (ih (fun j hj => bd j (Finset.mem_insert_of_mem hj)))

private def outerDiff : ℕ → Bi → Bi
  | 0, P => P
  | i+1, P => outerDiff i P.derivative

private lemma diff_specialize (i : ℕ) (P : Bi) (x : ℝ) : diff i (specialize P x) = specialize (outerDiff i P) x := by
  induction i generalizing P with
  | zero => rfl
  | succ i ih => simpa only [diff,outerDiff,specialize,derivative_map] using ih P.derivative

private lemma diff_bound (i : ℕ) (P : Bi) {d : ℕ} (bd : ∀ n, (P.coeff n).natDegree ≤ d) :
    ∀ n, ((outerDiff i P).coeff n).natDegree ≤ d := by
  induction i generalizing P with
  | zero => exact bd
  | succ i ih =>
    apply ih P.derivative
    intro n; rw [coeff_derivative]
    have e : (n : ℝ[X])+1=C ((n : ℝ)+1) := by simp
    rw [e]; exact (natDegree_mul_C_le ..).trans (bd _)

private lemma horizontal (P : Bi) {d : ℕ} (bd : ∀ n, (P.coeff n).natDegree ≤ d) (t : ℝ) :
    (P.eval (C t)).natDegree ≤ d := by
  rw [eval_eq_sum_range]; apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _; rw [← map_pow]; exact (natDegree_mul_C_le ..).trans (bd i)

/-- Each fixed derivative-sign branch of a bivariate polynomial of bounded
degree has a uniform number of input cuts at every output threshold. -/
theorem polynomial_pulls (P : Bi) {d : ℕ} (bound : Box d P) (σ : Fin (d+1) → SignType) :
    Pulls (Branch (specialize P) d σ) ((d+1)*d) := by
  apply branch_pulls
  · intro x; exact natDegree_map_le.trans bound.1
  · intro t i
    let Q := outerDiff i.val P
    refine ⟨Q.eval (C t),horizontal Q (diff_bound i.val _ bound.2) t,?_⟩
    intro x; rw [diff_specialize]
    have h := Polynomial.eval_map_apply (p := Q) (f := evalRingHom x) (C t)
    simpa [Q,specialize] using h

end Erdos101SecantPolynomials
end

/- Explicit equations for the three plane algebraic relations connecting
two companion endpoints through a common pivot on a curve. Their degrees
are bounded before specializing either external center. -/

noncomputable section
namespace Erdos101SecantCoordinates

open Erdos101SecantPolynomials Polynomial
open scoped Classical

abbrev Point := ℝ × ℝ
abbrev PlanePoly := MvPolynomial (Fin 2) ℝ

def value (F : PlanePoly) (p : Point) := MvPolynomial.eval ![p.1,p.2] F

def subst (F : PlanePoly) (d : ℕ) (A B D : Bi) : Bi :=
  ∑ m ∈ F.support, scalar (F.coeff m)*A^(m 0)*B^(m 1)*D^(d-(m 0+m 1))

private lemma exponent_bound {F : PlanePoly} {d : ℕ} (deg : F.totalDegree ≤ d)
    {m : Fin 2 →₀ ℕ} (hm : m ∈ F.support) : m 0 + m 1 ≤ d := by
  have h := (MvPolynomial.le_totalDegree hm).trans deg
  have exp : (m.sum fun _ e => e) = m 0 + m 1 := by
    rw [Finsupp.sum_fintype _ _ (by simp),Fin.sum_univ_two]
  exact exp ▸ h

private lemma expansion (F : PlanePoly) (p : Point) :
    value F p = ∑ m ∈ F.support, F.coeff m*p.1^(m 0)*p.2^(m 1) := by
  change MvPolynomial.eval ![p.1,p.2] F = _
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.eval_monomial,Finsupp.prod_fintype _ _ (by simp),Fin.prod_univ_two]
  simp [mul_assoc]

lemma subst_box {F : PlanePoly} {d e : ℕ} (deg : F.totalDegree ≤ d) {A B D : Bi}
    (ha : Box e A) (hb : Box e B) (hd : Box e D) : Box (e*d) (subst F d A B D) := by
  apply box_sum
  intro m hm
  have total := exponent_bound deg hm
  have ex : m 0 + m 1 + (d-(m 0+m 1)) = d := by omega
  have sum : 0+e*(m 0)+e*(m 1)+e*(d-(m 0+m 1)) = e*d := by
    rw [zero_add,← Nat.mul_add,← Nat.mul_add,ex]
  rw [← sum]
  exact (((box_scalar _).mul (ha.pow _)).mul (hb.pow _)).mul (hd.pow _)

lemma subst_value {F : PlanePoly} {d : ℕ} (deg : F.totalDegree ≤ d) (x y u : ℝ) (p : Point)
    (A B D : Bi) (ha : evalAt x y A=u*p.1) (hb : evalAt x y B=u*p.2) (hd : evalAt x y D=u) :
    evalAt x y (subst F d A B D) = u^d*value F p := by
  rw [subst,map_sum,expansion,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have total := exponent_bound deg hm
  have powers : u^(m 0)*u^(m 1)*u^(d-(m 0+m 1))=u^d := by
    rw [← pow_add,← pow_add]; congr 1; omega
  simp only [map_mul,map_pow,eval_scalar,ha,hb,hd,mul_pow]
  linear_combination (F.coeff m*p.1^(m 0)*p.2^(m 1))*powers

private lemma scale {d : ℕ} {P : Bi} (bd : Box d P) (c : ℝ) : Box d (P*scalar c) := by
  simpa using bd.mul (box_scalar c)

def pencil (F : PlanePoly) (d : ℕ) (p : Point) (s a : Bi) :=
  subst F d a (scalar p.2+s*(a-scalar p.1)) (scalar 1)

lemma pencil_box {F : PlanePoly} {d : ℕ} (deg : F.totalDegree ≤ d) (p : Point)
    {s a : Bi} (hs : Box 1 s) (ha : Box 1 a) : Box (2*d) (pencil F d p s a) := by
  apply subst_box deg (ha.mono (by decide)) _ ((box_scalar _).mono (by decide))
  exact ((box_scalar _).mono (by decide)).add (hs.mul (ha.sub ((box_scalar _).mono (by decide))))

def Along (p w : Point) (s : ℝ) : Prop := w.2=p.2+s*(w.1-p.1)

lemma pencil_value {F : PlanePoly} {d : ℕ} (deg : F.totalDegree ≤ d) (p w : Point)
    (x y : ℝ) (s a : Bi) (hx : evalAt x y a=w.1) (line : Along p w (evalAt x y s)) :
    evalAt x y (pencil F d p s a)=value F w := by
  have h := subst_value deg x y 1 w a (scalar p.2+s*(a-scalar p.1)) (scalar 1)
    (by simpa only [one_mul] using hx) (by simpa only [map_add,map_sub,map_mul,eval_scalar,hx,one_mul] using line.symm) (by simp)
  simpa only [one_pow,one_mul,pencil] using h

def junction (F : PlanePoly) (d : ℕ) (p q : Point) : Bi :=
  subst F d (scalar q.2-scalar p.2+input*scalar p.1-output*scalar q.1)
    (input*scalar q.2-output*scalar p.2+(input*output)*scalar (p.1-q.1)) (input-output)

lemma junction_box {F : PlanePoly} {d : ℕ} (deg : F.totalDegree ≤ d) (p q : Point) : Box (2*d) (junction F d p q) := by
  apply subst_box deg
  · exact (((((box_scalar _).sub (box_scalar _)).mono (by decide : 0 ≤ 1)).add (scale box_input _)).sub (scale box_output _)).mono (by decide)
  · exact (((scale box_input _).sub (scale box_output _)).mono (by decide : 1 ≤ 2)).add (scale (box_input.mul box_output) _)
  · exact (box_input.sub box_output).mono (by decide)

lemma junction_value {F : PlanePoly} {d : ℕ} (deg : F.totalDegree ≤ d) (p q w : Point) (s t : ℝ)
    (ps : Along p w s) (qt : Along q w t) : evalAt s t (junction F d p q)=(s-t)^d*value F w := by
  change w.2 = p.2+s*(w.1-p.1) at ps
  change w.2 = q.2+t*(w.1-q.1) at qt
  apply subst_value deg s t (s-t) w
  · simp only [map_add,map_mul,map_sub,eval_scalar,eval_input,eval_output]
    linear_combination ps-qt
  · simp only [map_add,map_mul,map_sub,eval_scalar,eval_input,eval_output]
    linear_combination t*ps-s*qt
  · simp

/-- A nonvertical line through p and w in these coordinates. -/
def gradient (p w : Point) := (w.2-p.2)/(w.1-p.1)

lemma through (p w : Point) (ne : w.1 ≠ p.1) : Along p w (gradient p w) := by
  unfold Along gradient; field_simp [sub_ne_zero.mpr ne]; ring

/-- A projected endpoint x at which the original polynomial does not
contain the entire vertical line. -/
def VerticalRegular (F : PlanePoly) (x : ℝ) : Prop := ∃ v : ℝ, value F (x,v) ≠ 0

lemma start_nonzero {F : PlanePoly} {d : ℕ} (deg : F.totalDegree ≤ d) (p : Point) (x : ℝ)
    (ne : x ≠ p.1) (regular : VerticalRegular F x) : specialize (pencil F d p output input) x ≠ 0 := by
  obtain ⟨v,hv⟩ := regular
  let s := gradient p (x,v)
  have h := pencil_value deg p (x,v) x s output input (by simp) (by simpa only [eval_output] using through p (x,v) ne)
  intro hz; apply hv; rw [← h]; change (specialize _ x).eval s=0; rw [hz]; simp

lemma junction_nonzero {F : PlanePoly} {d : ℕ} (deg : F.totalDegree ≤ d) (p q : Point) (s : ℝ)
    (outside : value F p ≠ 0) (diffX : p.1 ≠ q.1) (valid : s ≠ gradient q p) :
    specialize (junction F d p q) s ≠ 0 := by
  let t := gradient q p
  have h := junction_value deg p q p s t (by simp [Along]) (through q p diffX)
  intro hz
  apply (mul_ne_zero (pow_ne_zero d (sub_ne_zero.mpr valid)) outside)
  rw [← h]; change (specialize _ s).eval t=0; rw [hz]; simp

lemma end_nonzero {F : PlanePoly} {d : ℕ} (deg : F.totalDegree ≤ d) (q : Point) (t : ℝ)
    (outside : value F q ≠ 0) : specialize (pencil F d q input output) t ≠ 0 := by
  have h := pencil_value deg q q t q.1 input output (by simp) (by simp [Along])
  intro hz; apply outside; rw [← h]; change (specialize _ t).eval q.1=0; rw [hz]; simp

end Erdos101SecantCoordinates
end

/- Endpoint pairs arising from two external centers and a shared point
on a fixed real plane curve occupy only linearly many rank boxes. -/

noncomputable section
namespace Erdos101PairedSecants

open Erdos101SecantOrder Erdos101SecantCuts Erdos101SecantPolynomials Erdos101SecantCoordinates
open Erdos101SecantBlocks Erdos101Parabola Erdos101OrderedGrid
open scoped Classical

private abbrev Sig (b : ℕ) := Fin (b+1) → SignType
private abbrev Tags (b : ℕ) := Sig b × Sig b × Sig b

/-- The bound depends only on the degree of the input curve. -/
def boxConstant (d : ℕ) :=
  let b := 2*d
  let k := (b+1)*b
  (3^(b+1))^3*(2*(k*(k*k)+2))

/-- Projected endpoints on two pencils with a common curve point. -/
def RegularRecord (F : PlanePoly) (p q : Point) (a b : ℝ) : Prop :=
  ∃ u v w : Point, ∃ s t : ℝ, u.1=a ∧ v.1=b ∧ value F u=0 ∧ value F v=0 ∧ value F w=0 ∧
    Along p u s ∧ Along p w s ∧ Along q w t ∧ Along q v t ∧
    a ≠ p.1 ∧ VerticalRegular F a ∧ s ≠ gradient q p

theorem regular_blocks {F : PlanePoly} {d : ℕ} (degree : F.totalDegree ≤ d) (p q : Point)
    (outside : value F p ≠ 0) (outside' : value F q ≠ 0) (diffX : p.1 ≠ q.1)
    (X : Finset ℝ) (P : Finset (ℝ × ℝ)) (inside : P ⊆ X ×ˢ X)
    (records : ∀ e ∈ P, RegularRecord F p q e.1 e.2) (k : ℕ) :
    (occupied (P.image (ranks X)) k).card ≤ boxConstant d*(X.card/k+1) := by
  classical
  let b := 2*d
  let K := (b+1)*b
  let A := pencil F d p output input
  let B := junction F d p q
  let C := pencil F d q input output
  let link (P : Bi) (c : Sig b) := Branch (specialize P) b c
  let chain (c : Tags b) (a z : ℝ) := ∃ t, (∃ s, link A c.1 a s ∧ link B c.2.1 s t) ∧ link C c.2.2 t z
  have pulls (c : Tags b) : Pulls (chain c) (K*(K*K)) := compose
    (compose (polynomial_pulls A (pencil_box degree p box_output box_input) c.1)
      (polynomial_pulls B (junction_box degree p q) c.2.1))
    (polynomial_pulls C (pencil_box degree q box_input box_output) c.2.2)
  have hits (e : ℝ × ℝ) (he : e ∈ P) : ∃ c, chain c e.1 e.2 := by
    obtain ⟨u,v,w,s,t,ua,vb,uf,vf,wf,pu,pw,qw,qv,px,regular,pq⟩ := records e he
    have ra : (specialize A e.1).eval s=0 := by
      change evalAt e.1 s A=0
      exact (pencil_value degree p u e.1 s output input (by simpa using ua.symm) (by simpa using pu)).trans uf
    have rb : (specialize B s).eval t=0 := by
      change evalAt s t B=0
      rw [show evalAt s t B=(s-t)^d*value F w from junction_value degree p q w s t pw qw,wf,mul_zero]
    have rc : (specialize C t).eval e.2=0 := by
      change evalAt t e.2 C=0
      exact (pencil_value degree q v t e.2 input output (by simpa using vb.symm) (by simpa using qv)).trans vf
    refine ⟨(code b (specialize A e.1) s,code b (specialize B s) t,code b (specialize C t) e.2),t,?_,?_⟩
    · exact ⟨s,⟨start_nonzero degree p e.1 px regular,ra,rfl⟩,⟨junction_nonzero degree p q s outside diffX pq,rb,rfl⟩⟩
    · exact ⟨end_nonzero degree q t outside',rc,rfl⟩
  have result := colored_occupied chain pulls X P inside hits k
  have tags : Fintype.card (Tags b)=(3^(b+1))^3 := by
    have signs : Fintype.card SignType=3 := by decide
    simp only [Tags,Sig,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,signs]
    ring
  simpa only [tags,boxConstant,b,K] using result

/-- Three curve points, with the middle point on both secants. -/
def Paired (F : PlanePoly) (p q : Point) (a b : ℝ) : Prop :=
  ∃ u v w : Point, u.1=a ∧ v.1=b ∧ value F u=0 ∧ value F v=0 ∧ value F w=0 ∧
    w ∈ line[ℝ,p,u] ∧ w ∈ line[ℝ,q,v]

private lemma along_line (p u w : Point) (xu : u.1 ≠ p.1) (onLine : w ∈ line[ℝ,p,u]) :
    Along p w (gradient p u) := by
  have det : (w.2-p.2)*(u.1-p.1)=(u.2-p.2)*(w.1-p.1) := by
    obtain ⟨z,eq⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp onLine
    rw [← eq]; simp only [AffineMap.lineMap_apply_module,Prod.snd_add,Prod.fst_add,Prod.smul_snd,Prod.smul_fst,smul_eq_mul]; ring
  unfold Along Erdos101SecantCoordinates.gradient
  field_simp [sub_ne_zero.mpr xu]; nlinarith only [det]

private lemma remove_strips {F : PlanePoly} {d : ℕ} (degree : F.totalDegree ≤ d) (p q : Point)
    (outside : value F p ≠ 0) : ∃ Z : Finset ℝ, Z.card ≤ 4*d+1 ∧
    ∀ {a b : ℝ}, Paired F p q a b → a ∈ Z ∨ b=q.1 ∨ RegularRecord F p q a b := by
  classical
  let f := fun s => specialize (pencil F d p input output) s
  let t := gradient q p
  have degreeF (s : ℝ) : (f s).natDegree ≤ 2*d := Polynomial.natDegree_map_le.trans (pencil_box degree p box_input box_output).1
  have lim (s : ℝ) : (f s).roots.toFinset.card ≤ 2*d :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans (degreeF s))
  let Z := insert p.1 ((f 0).roots.toFinset ∪ (f t).roots.toFinset)
  have bound : Z.card ≤ 4*d+1 := calc
    _ ≤ ((f 0).roots.toFinset ∪ (f t).roots.toFinset).card+1 := Finset.card_insert_le ..
    _ ≤ ((f 0).roots.toFinset.card+(f t).roots.toFinset.card)+1 := Nat.add_le_add_right (Finset.card_union_le ..) _
    _ ≤ _ := by have a := lim 0; have b := lim t; omega
  refine ⟨Z,bound,?_⟩
  intro a b paired
  by_cases bad : a ∈ Z
  · exact Or.inl bad
  by_cases right : b=q.1
  · exact Or.inr (Or.inl right)
  right; right
  obtain ⟨u,v,w,ua,vb,uf,vf,wf,pu,qv⟩ := paired
  have px : a ≠ p.1 := fun e => bad (e ▸ Finset.mem_insert_self ..)
  have xu : u.1 ≠ p.1 := ua ▸ px
  have xv : v.1 ≠ q.1 := vb ▸ right
  have avoids₀ : (f 0).eval a ≠ 0 := by
    intro h
    exact bad (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (end_nonzero degree p 0 outside)).mpr h))))
  have avoids : (f t).eval a ≠ 0 := by
    intro h
    exact bad (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (end_nonzero degree p t outside)).mpr h))))
  have regular : VerticalRegular F a := by
    refine ⟨p.2,?_⟩
    have he := pencil_value degree p (a,p.2) 0 a input output (by simp) (by simp [Along])
    exact he ▸ avoids₀
  let s := gradient p u
  have actual := through p u xu
  have distinct : s ≠ t := by
    intro eq; apply avoids
    have he := pencil_value degree p u t a input output (by simpa using ua.symm) (by
      simpa only [eval_input,← eq] using actual)
    exact he.trans uf
  exact ⟨u,v,w,s,gradient q v,ua,vb,uf,vf,wf,actual,along_line p u w xu pu,
    along_line q v w xv qv,through q v xv,px,regular,distinct⟩

/-- Uniform occupancy for actual shared-pivot secants on any plane curve.
Vertical components and the line joining the centers are counted as strips. -/
theorem paired_secant_blocks {F : PlanePoly} {d : ℕ} (degree : F.totalDegree ≤ d) (p q : Point)
    (outside : value F p ≠ 0) (outside' : value F q ≠ 0) (diffX : p.1 ≠ q.1)
    (X : Finset ℝ) (P : Finset (ℝ × ℝ)) (inside : P ⊆ X ×ˢ X)
    (records : ∀ e ∈ P, Paired F p q e.1 e.2) (k : ℕ) :
    (occupied (P.image (ranks X)) k).card ≤ (boxConstant d+4*d+2)*(X.card/k+1) := by
  classical
  obtain ⟨Z,zsmall,classify⟩ := remove_strips degree p q outside
  let good := P.filter (fun e => RegularRecord F p q e.1 e.2)
  let G := occupied (good.image (ranks X)) k
  have goodCount : G.card ≤ boxConstant d*(X.card/k+1) := regular_blocks degree p q outside outside' diffX X good
    ((Finset.filter_subset ..).trans inside) (fun _ h => (Finset.mem_filter.mp h).2) k
  let side := Finset.range (X.card/k+1)
  let bucket (x : ℝ) := rank X x/k
  have onSide (x : ℝ) (hx : x∈X) : bucket x ∈ side :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (rank_lt_card X hx).le))
  let cols := Z.image bucket
  let leftStrip := cols ×ˢ side
  let rightStrip := side ×ˢ {bucket q.1}
  have cover : occupied (P.image (ranks X)) k ⊆ (G ∪ leftStrip) ∪ rightStrip := by
    intro b hb
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hw
    have ends := Finset.mem_product.mp (inside he)
    rcases classify (records e he) with hz | eq | regular
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hz,onSide _ ends.2⟩))
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨onSide _ ends.1,Finset.mem_singleton.mpr (congrArg bucket eq)⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨he,regular⟩ : e∈good))))
  have leftCount : leftStrip.card ≤ (4*d+1)*(X.card/k+1) := by
    dsimp only [leftStrip,side]; rw [Finset.card_product,Finset.card_range]
    exact Nat.mul_le_mul_right _ (Finset.card_image_le.trans zsmall)
  have rightCount : rightStrip.card=X.card/k+1 := by simp [rightStrip,side]
  have union := (Finset.card_le_card cover).trans ((Finset.card_union_le ..).trans
    (Nat.add_le_add_right (Finset.card_union_le G leftStrip) rightStrip.card))
  rw [rightCount] at union
  nlinarith only [union,leftCount,goodCount]

end Erdos101PairedSecants
end

/- One affine coordinate order suffices for every pair of external
centers in a finite plane configuration. The shear preserves degree and
all the actual secants that are counted. -/

noncomputable section
namespace Erdos101SecantShear

open EuclideanGeometry MvPolynomial Erdos101SecantCoordinates Erdos101PairedSecants Erdos101Parabola Erdos101OrderedGrid
open scoped Classical

def shear (r : ℝ) (p : ℝ²) : Point := (p 0+r*p 1,p 1)

theorem separating (S : Finset ℝ²) : ∃ r : ℝ, (S : Set ℝ²).InjOn (fun p => (shear r p).1) := by
  classical
  let slope (e : ℝ² × ℝ²) := (e.2 0-e.1 0)/(e.1 1-e.2 1)
  obtain ⟨r,avoid⟩ := Infinite.exists_notMem_finset (S.offDiag.image slope)
  refine ⟨r,?_⟩
  intro a ha b hb eq
  change a 0+r*a 1=b 0+r*b 1 at eq
  by_cases second : a 1=b 1
  · have first : a 0=b 0 := by rw [second] at eq; linarith
    ext i; fin_cases i
    · exact first
    · exact second
  · exfalso; apply avoid
    have ne : a ≠ b := fun e => second (e ▸ rfl)
    refine Finset.mem_image.mpr ⟨(a,b),Finset.mem_offDiag.mpr ⟨ha,hb,ne⟩,?_⟩
    apply (div_eq_iff (sub_ne_zero.mpr second)).mpr
    nlinarith only [eq]

def transformed (F : PlanePoly) (r : ℝ) : PlanePoly :=
  ∑ m ∈ F.support, C (F.coeff m)*(X 0 + C (-r)*X 1)^(m 0)*(X 1)^(m 1)

theorem transformed_degree (F : PlanePoly) (r : ℝ) : (transformed F r).totalDegree ≤ F.totalDegree := by
  have left : (X 0 + C (-r)*X 1 : PlanePoly).totalDegree ≤ 1 := by
    apply (totalDegree_add ..).trans (max_le (by simp) _)
    exact (totalDegree_mul ..).trans (by simp)
  apply totalDegree_finsetSum_le
  intro m hm
  have ex : (m.sum fun _ e => e) = m 0 + m 1 := by rw [Finsupp.sum_fintype _ _ (by simp),Fin.sum_univ_two]
  have a := (totalDegree_pow (X 0 + C (-r)*X 1 : PlanePoly) (m 0)).trans (Nat.mul_le_mul_left _ left)
  have b := totalDegree_pow (X 1 : PlanePoly) (m 1)
  have e := (totalDegree_mul (C (F.coeff m)*(X 0+C (-r)*X 1)^(m 0)) ((X 1)^(m 1))).trans
    (Nat.add_le_add (totalDegree_mul ..) b)
  simp only [totalDegree_C,zero_add,totalDegree_X,Nat.mul_one] at a e
  exact e.trans ((Nat.add_le_add_right a _).trans (ex ▸ le_totalDegree hm))

theorem transformed_value (F : PlanePoly) (r : ℝ) (p : ℝ²) : value (transformed F r) (shear r p) = eval (fun i => p i) F := by
  have expanded := congrArg (eval (fun i => p i)) F.as_sum
  rw [expanded,value,transformed,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [eval_monomial,Finsupp.prod_fintype _ _ (by simp),Fin.prod_univ_two]
  simp only [map_mul,map_add,map_pow,eval_C,eval_X,Matrix.cons_val_zero,Matrix.cons_val_one,
    shear,neg_mul]
  ring

lemma shear_line {x y z : ℝ²} (r : ℝ) (onLine : z ∈ line[ℝ,x,y]) : shear r z ∈ line[ℝ,shear r x,shear r y] := by
  obtain ⟨s,hs⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp onLine
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  refine ⟨s,?_⟩
  rw [← hs]
  ext <;> simp [shear,AffineMap.lineMap_apply_module]
  ring

/-- The curve points x and z have a common curve pivot on the indicated
pair of secants. All witnesses live in the original plane. -/
def Shared (F : PlanePoly) (p q x z : ℝ²) : Prop :=
  eval (fun i => x i) F = 0 ∧ eval (fun i => z i) F = 0 ∧
  ∃ w : ℝ², eval (fun i => w i) F = 0 ∧ w ∈ line[ℝ,p,x] ∧ w ∈ line[ℝ,q,z]

def records (r : ℝ) (E : Finset (ℝ² × ℝ²)) := E.image (fun e => ((shear r e.1).1,(shear r e.2).1))

/-- The common real projection is chosen using S alone. It works for all
curves, all distinct external centers in S, all endpoint records and all
choices of block size. -/
theorem configuration_blocks (S : Finset ℝ²) : ∃ r : ℝ,
    (S : Set ℝ²).InjOn (fun p => (shear r p).1) ∧ ∀ (F : PlanePoly) (d : ℕ), F.totalDegree ≤ d →
    ∀ p∈S, ∀ q∈S, p ≠ q → eval (fun i => p i) F ≠ 0 → eval (fun i => q i) F ≠ 0 →
    ∀ E : Finset (ℝ² × ℝ²), E ⊆ S ×ˢ S → (∀ e∈E, Shared F p q e.1 e.2) → ∀ k : ℕ,
      (occupied ((records r E).image (ranks (S.image (fun p => (shear r p).1)))) k).card ≤
        (boxConstant d+4*d+2)*(S.card/k+1) := by
  classical
  obtain ⟨r,sep⟩ := separating S
  refine ⟨r,sep,?_⟩
  intro F d deg p hp q hq ne op oq E inside data k
  let X := S.image (fun p => (shear r p).1)
  have card : X.card=S.card := Finset.card_image_of_injOn sep
  have subset : records r E ⊆ X ×ˢ X := by
    intro a ha
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp ha
    have ends := Finset.mem_product.mp (inside he)
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ ends.1,Finset.mem_image_of_mem _ ends.2⟩
  rw [← card]
  apply paired_secant_blocks ((transformed_degree F r).trans deg) (shear r p) (shear r q)
    ((transformed_value F r p).trans_ne op) ((transformed_value F r q).trans_ne oq) (fun h => ne (sep hp hq h)) X _ subset
  intro a ha
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨left,right,w,curve,first,second⟩ := data e he
  exact ⟨shear r e.1,shear r e.2,shear r w,rfl,rfl,(transformed_value ..).trans left,
    (transformed_value ..).trans right,(transformed_value ..).trans curve,shear_line r first,shear_line r second⟩

end Erdos101SecantShear
end

/- The common coordinate order converts a family of actual paired secants
into a fixed sample of any prescribed size at least 25. The frame and witnesses below
are stated in the original Euclidean coordinates. -/

noncomputable section
namespace Erdos101SecantFrame

open EuclideanGeometry MvPolynomial Erdos101SecantCoordinates Erdos101SecantShear Erdos101PairedSecants
open Erdos101Parabola Erdos101OrderedGrid Erdos101SecantSamples
open scoped Classical

abbrev Pair := ℝ² × ℝ²

def Proper (F : PlanePoly) (e v : Pair) : Prop :=
  eval (fun i => v.1 i) F = 0 ∧ eval (fun i => v.2 i) F = 0 ∧ ∃ w : ℝ²,
    eval (fun i => w i) F=0 ∧ w ≠ v.1 ∧ w ≠ v.2 ∧ w ∉ line[ℝ,e.1,e.2] ∧
    w ∈ line[ℝ,e.1,v.1] ∧ w ∈ line[ℝ,e.2,v.2]

private lemma shared_of_proper {F : PlanePoly} {e v : Pair} (h : Proper F e v) : Shared F e.1 e.2 v.1 v.2 := by
  obtain ⟨x,z,w,y,_,_,_,a,b⟩ := h
  exact ⟨x,z,w,y,a,b⟩

private lemma pivot_of_proper {F : PlanePoly} {e v : Pair} (h : Proper F e v) : hasPivot F e.1 e.2 v.1 v.2 := by
  obtain ⟨_,_,w,hit,_,distinct,_,first,second⟩ := h
  have eq : line[ℝ,v.2,w] = line[ℝ,e.2,v.2] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne (right_mem_affineSpan_pair ..) second distinct.symm
  exact ⟨w,hit,first,eq ▸ left_mem_affineSpan_pair ..⟩

def FrameIn (W : Finset Pair) : Prop :=
  ∃ a ∈ W, ∃ b ∈ W, ∃ c ∈ W, ∃ d ∈ W,
    independentTriple Prod.fst Prod.snd a b c ∧ independentTriple Prod.fst Prod.snd a b d ∧
    independentTriple Prod.fst Prod.snd a c d ∧ independentTriple Prod.fst Prod.snd b c d

/-- A rich family of paired external-center matchings shares a single
sample of any prescribed size at least 25, including a two-sided frame,
at many distinct first centers. -/
theorem shared_frame (S : Finset ℝ²) (F : PlanePoly) {d : ℕ} (degree : F.totalDegree ≤ d)
    (cap : NonCollinearFor 5 (S : Set ℝ²)) (A : Finset Pair) (active : A.Nonempty)
    (E : Pair → Finset Pair) (centers : ∀ e ∈ A, e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 ≠ e.2 ∧
      eval (fun i => e.1 i) F ≠ 0 ∧ eval (fun i => e.2 i) F ≠ 0)
    (inside : ∀ e∈A, E e ⊆ S ×ˢ S) (data : ∀ e∈A, ∀ v∈E e, Proper F e v)
    (matching : ∀ e∈A, Set.InjOn Prod.fst (E e : Set Pair) ∧ Set.InjOn Prod.snd (E e : Set Pair))
    {t k m : ℕ} (sample : 25 ≤ m) (hk : 0 < k) (size : k ≤ S.card) (enough : 4*t*m*(boxConstant d+4*d+2) ≤ k)
    (space : m ≤ (grid S.card).card) (rich : ∀ e∈A, S.card ≤ t*(E e).card) :
    ∃ W : Finset Pair, ∃ J ⊆ A, W ⊆ S ×ˢ S ∧ W.card=m ∧ FrameIn W ∧
      Set.InjOn Prod.fst (W : Set Pair) ∧ Set.InjOn Prod.snd (W : Set Pair) ∧
      (∀ e∈J, W ⊆ E e) ∧ A.card ≤ 8*t*k^(2+2*m)*d^3*(J.image Prod.fst).card*S.card := by
  classical
  obtain ⟨r,inj,box⟩ := configuration_blocks S
  let X := S.image (fun p => (shear r p).1)
  let view (v : Pair) := ((shear r v.1).1,(shear r v.2).1)
  let key (v : Pair) := ranks X (view v)
  let G (e : Pair) := (E e).image key
  have xc : X.card=S.card := Finset.card_image_of_injOn inj
  have viewIn {v : Pair} (hi : v ∈ S ×ˢ S) : view v ∈ X ×ˢ X := by
    have mem := Finset.mem_product.mp hi
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ mem.1,Finset.mem_image_of_mem _ mem.2⟩
  have unique : Set.InjOn key (↑(S ×ˢ S) : Set Pair) := by
    intro u hu v hv eq
    have same := ranks_inj X (viewIn hu) (viewIn hv) eq
    have us := Finset.mem_product.mp hu
    have vs := Finset.mem_product.mp hv
    change ((shear r u.1).1,(shear r u.2).1)=((shear r v.1).1,(shear r v.2).1) at same
    obtain ⟨a,b⟩ := Prod.mk.inj same
    exact Prod.ext (inj us.1 vs.1 a) (inj us.2 vs.2 b)
  have gd (e : Pair) (he : e∈A) : G e ⊆ grid S.card := by
    intro w hw; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    have vv := Finset.mem_product.mp (viewIn (inside e he hv))
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr ((rank_lt_card X vv.1).trans_le xc.le),
      Finset.mem_range.mpr ((rank_lt_card X vv.2).trans_le xc.le)⟩
  have small (e : Pair) (he : e∈A) : (occupied (G e) k).card ≤ (boxConstant d+4*d+2)*(S.card/k+1) := by
    obtain ⟨ps,qs,ne,op,oq⟩ := centers e he
    have bound := box F d degree _ ps _ qs ne op oq (E e) (inside e he) (fun v hv => shared_of_proper (data e he v hv)) k
    simpa only [G,key,view,X,records,Finset.image_image,Function.comp_def] using bound
  have many (e : Pair) (he : e∈A) : S.card ≤ t*(G e).card := by
    rw [show (G e).card=(E e).card from Finset.card_image_of_injOn (unique.mono (Finset.coe_subset.mpr (inside e he)))]
    exact rich e he
  obtain ⟨T,_,sz,count⟩ := repeated_sample A G hk size enough space gd small many
  let J := A.filter (fun e => T ⊆ G e)
  have jp : J.Nonempty := by
    by_contra! empty
    have z : J.card=0 := Finset.card_eq_zero.mpr empty
    change A.card ≤ 8*t*k^(2+2*m)*J.card*S.card at count
    rw [z,mul_zero,zero_mul] at count
    exact (not_lt_of_ge count) (Finset.card_pos.mpr active)
  obtain ⟨e₀,h₀⟩ := jp
  have inA := (Finset.mem_filter.mp h₀).1
  let W := (E e₀).filter (fun v => key v ∈ T)
  have sub : W ⊆ E e₀ := Finset.filter_subset ..
  have gridW : W.image key=T := by
    ext w
    constructor
    · rintro hw; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw; exact (Finset.mem_filter.mp hv).2
    · intro hw; obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp ((Finset.mem_filter.mp h₀).2 hw)
      exact Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,eq ▸ hw⟩,eq⟩
  have inS := sub.trans (inside e₀ inA)
  have ws : W.card=m := by
    rw [← Finset.card_image_of_injOn (s := W) (unique.mono (Finset.coe_subset.mpr inS)),gridW,sz]
  have common (e : Pair) (he : e∈J) : W ⊆ E e := by
    intro v hv
    have hev := Finset.mem_filter.mp he
    obtain ⟨u,hu,eq⟩ := Finset.mem_image.mp (hev.2 (Finset.mem_filter.mp hv).2)
    exact (unique (inside e hev.1 hu) (inS hv) eq) ▸ hu
  have frame : FrameIn W := simultaneous_frames W S Prod.fst Prod.snd (fun v hv => Finset.mem_product.mp (inS hv))
    cap ((matching e₀ inA).1.mono (Finset.coe_subset.mpr sub)) ((matching e₀ inA).2.mono (Finset.coe_subset.mpr sub)) (sample.trans ws.ge)
  have hasFrame := frame
  obtain ⟨a,ha,b,hb,c,hc,u,hu,abc,_,_,_⟩ := frame
  have fiber := sample_first_centers F J Prod.fst Prod.snd a b c abc.2
    (fun e he => (centers e (Finset.mem_filter.mp he).1).2.2.2.1) (fun e he =>
      ⟨pivot_of_proper (data _ (Finset.mem_filter.mp he).1 _ (common e he ha)),
       pivot_of_proper (data _ (Finset.mem_filter.mp he).1 _ (common e he hb)),
       pivot_of_proper (data _ (Finset.mem_filter.mp he).1 _ (common e he hc))⟩)
  refine ⟨W,J,Finset.filter_subset ..,inS,ws,hasFrame,(matching e₀ inA).1.mono (Finset.coe_subset.mpr sub),
    (matching e₀ inA).2.mono (Finset.coe_subset.mpr sub),common,?_⟩
  have total := fiber.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left degree 3))
  calc
    _ ≤ 8*t*k^(2+2*m)*J.card*S.card := count
    _ ≤ (8*t*k^(2+2*m))*(d^3*(J.image Prod.fst).card)*S.card := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ total)
    _ = _ := by ring

end Erdos101SecantFrame
end

/- Selecting distinct curve points on actual four-point lines produces
matchings from each external center. The common pivots on the line of
two centers are removed using the original no-five assumption. -/

noncomputable section
namespace Erdos101SecantPencils

open EuclideanGeometry MvPolynomial Erdos101SecantCoordinates Erdos101SecantFrame
open scoped Classical

def Row (S : Finset ℝ²) (F : PlanePoly) (p : ℝ²) (D : Finset ℝ²) (c : ℝ² → ℝ²) : Prop :=
  D ⊆ S ∧ Set.InjOn c D ∧ ∀ w∈D, c w ∈ S ∧ eval (fun i => w i) F=0 ∧
    eval (fun i => c w i) F=0 ∧ w ≠ c w ∧ w ∈ line[ℝ,p,c w] ∧
    line[ℝ,p,c w] ∈ linesWithPointsFor 4 (S : Set ℝ²)

/-- The pivot and its companion both identify the original four-point line. -/
theorem row_of_lines (S : Finset ℝ²) (F : PlanePoly) (p : ℝ²) (outside : eval (fun i => p i) F ≠ 0)
    (A : Finset (AffineSubspace ℝ ℝ²))
    (lines : ∀ L∈A, p∈L ∧ L∈linesWithPointsFor 4 (S : Set ℝ²) ∧
      2 ≤ (S.filter (fun x => x∈L ∧ eval (fun i => x i) F=0)).card) :
    ∃ D : Finset ℝ², ∃ c : ℝ² → ℝ², D.card=A.card ∧ Row S F p D c := by
  classical
  have endpoints (L : A) : ∃ w∈S, ∃ u∈S, eval (fun i => w i) F=0 ∧ eval (fun i => u i) F=0 ∧
      w ≠ u ∧ w ∈ L.val ∧ u ∈ L.val := by
    obtain ⟨w,hw,u,hu,ne⟩ := Finset.one_lt_card.mp (lines L L.property).2.2
    obtain ⟨sw,lw,fw⟩ := Finset.mem_filter.mp hw
    obtain ⟨su,lu,fu⟩ := Finset.mem_filter.mp hu
    exact ⟨w,sw,u,su,fw,fu,ne,lw,lu⟩
  choose w ws u us fw fu distinct wl ul using endpoints
  have identify (L : A) {x : ℝ²} (mem : x∈L.val) (zero : eval (fun i => x i) F=0) : line[ℝ,p,x]=L.val := by
    obtain ⟨pl,four,_⟩ := lines L L.property
    have ne : p ≠ x := by rintro rfl; exact outside zero
    obtain ⟨⟨a,_,b,_,_,eq⟩,_⟩ := four
    rw [← eq] at pl mem ⊢
    exact affineSpan_pair_eq_of_mem_of_mem_of_ne pl mem ne
  have wi : Function.Injective w := fun L M eq => Subtype.ext <| (identify L (wl L) (fw L)).symm.trans
    ((congrArg (fun x => line[ℝ,p,x]) eq).trans (identify M (wl M) (fw M)))
  have ui : Function.Injective u := fun L M eq => Subtype.ext <| (identify L (ul L) (fu L)).symm.trans
    ((congrArg (fun x => line[ℝ,p,x]) eq).trans (identify M (ul M) (fu M)))
  let D := A.attach.image w
  let c := Function.extend w u (fun _ => p)
  have cv (L : A) : c (w L)=u L := wi.extend_apply ..
  refine ⟨D,c,(Finset.card_image_of_injective _ wi).trans Finset.card_attach,?_,?_,?_⟩
  · intro v hv; obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp hv; exact ws L
  · intro a ha b hb eq
    obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨M,_,rfl⟩ := Finset.mem_image.mp hb
    rw [cv,cv] at eq; exact congrArg w (ui eq)
  · intro v hv; obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp hv
    rw [cv,identify L (ul L) (fu L)]
    exact ⟨us L,fw L,fu L,distinct L,wl L,(lines L L.property).2.1⟩

def pivots (e : Pair) (D : ℝ² → Finset ℝ²) := (D e.1 ∩ D e.2).filter (fun w => w ∉ line[ℝ,e.1,e.2])
def pairs (e : Pair) (D : ℝ² → Finset ℝ²) (c : ℝ² → ℝ² → ℝ²) :=
  (pivots e D).image (fun w => (c e.1 w,c e.2 w))

/-- Both secants are genuine four-point lines, with a common pivot in the
original configuration away from the line joining the centers. -/
def Realized (S : Finset ℝ²) (F : PlanePoly) (e v : Pair) : Prop :=
  eval (fun i => v.1 i) F=0 ∧ eval (fun i => v.2 i) F=0 ∧
  ∃ w∈S, eval (fun i => w i) F=0 ∧ w ≠ v.1 ∧ w ≠ v.2 ∧ w ∉ line[ℝ,e.1,e.2] ∧
    w ∈ line[ℝ,e.1,v.1] ∧ w ∈ line[ℝ,e.2,v.2] ∧
    line[ℝ,e.1,v.1] ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧
    line[ℝ,e.2,v.2] ∈ linesWithPointsFor 4 (S : Set ℝ²)

lemma realized_proper {S F e v} (h : Realized S F e v) : Proper F e v := by
  obtain ⟨af,bf,w,_,wf,wa,wb,off,onP,onQ,_,_⟩ := h
  exact ⟨af,bf,w,wf,wa,wb,off,onP,onQ⟩

lemma pairs_from_rows {e : Pair} {S : Finset ℝ²} {F : PlanePoly} {D : ℝ² → Finset ℝ²} {c : ℝ² → ℝ² → ℝ²}
    (p : Row S F e.1 (D e.1) (c e.1)) (q : Row S F e.2 (D e.2) (c e.2)) :
    let E := pairs e D c
    E.card=(pivots e D).card ∧ E ⊆ S ×ˢ S ∧ (∀ v∈E, Realized S F e v) ∧
      Set.InjOn Prod.fst (E : Set Pair) ∧ Set.InjOn Prod.snd (E : Set Pair) := by
  classical
  let z (w : ℝ²) := (c e.1 w,c e.2 w)
  have both {w} (h : w ∈ pivots e D) := Finset.mem_inter.mp (Finset.mem_filter.mp h).1
  have inj : Set.InjOn z (pivots e D) := fun _ ha _ hb eq => p.2.1 (both ha).1 (both hb).1 (congrArg Prod.fst eq)
  refine ⟨Finset.card_image_of_injOn inj,?_,?_,?_,?_⟩
  · intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_product.mpr ⟨(p.2.2 w (both hw).1).1,(q.2.2 w (both hw).2).1⟩
  · intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨_,wf,af,wa,pa,fp⟩ := p.2.2 w (both hw).1
    obtain ⟨_,_,bf,wb,qb,fq⟩ := q.2.2 w (both hw).2
    exact ⟨af,bf,w,p.1 (both hw).1,wf,wa,wb,(Finset.mem_filter.mp hw).2,pa,qb,fp,fq⟩
  · intro a ha b hb eq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
    exact congrArg z (p.2.1 (both hi).1 (both hj).1 eq)
  · intro a ha b hb eq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
    exact congrArg z (q.2.1 (both hi).2 (both hj).2 eq)

private lemma line_cap (S : Finset ℝ²) (cap : NonCollinearFor 5 (S : Set ℝ²)) (a b : ℝ²) :
    (S.filter (fun p => p ∈ line[ℝ,a,b])).card ≤ 4 := by
  by_contra! h
  obtain ⟨U,hs,hn⟩ := Finset.exists_subset_card_eq (show 5 ≤ _ from h)
  apply cap (U : Set ℝ²) (Finset.coe_subset.mpr (hs.trans (Finset.filter_subset ..))) U.finite_toSet (by simpa using hn)
  apply (collinear_iff_exists_forall_eq_smul_vadd _).mpr
  refine ⟨a,b -ᵥ a,?_⟩
  intro p hp
  obtain ⟨u,hu⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp (Finset.mem_filter.mp (hs hp)).2
  exact ⟨u,hu.symm⟩

lemma discard_base_line {S : Finset ℝ²} (cap : NonCollinearFor 5 (S : Set ℝ²)) (e : Pair) (D : ℝ² → Finset ℝ²)
    (sub : D e.1 ⊆ S) : (D e.1 ∩ D e.2).card ≤ (pivots e D).card+4 := by
  classical
  let U := D e.1 ∩ D e.2
  let L := line[ℝ,e.1,e.2]
  have incl : U.filter (fun w => w∈L) ⊆ S.filter (fun w => w∈L) := by
    intro w hw; obtain ⟨mem,onLine⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨sub (Finset.mem_inter.mp mem).1,onLine⟩
  have atMost := (Finset.card_le_card incl).trans (line_cap S cap e.1 e.2)
  have sum := Finset.card_filter_add_card_filter_not (s := U) (fun w => w∈L)
  change U.card ≤ (U.filter (fun w => w∉L)).card+4
  omega

end Erdos101SecantPencils
end

/- A fixed matching of curve secants is shared by a positive fraction of
the external centers in the hypotheses of the curve-capture step. -/

noncomputable section
namespace Erdos101RichSecantSamples

open EuclideanGeometry MvPolynomial Erdos101SecantCoordinates Erdos101SecantShear
open Erdos101PairedSecants Erdos101SecantFrame Erdos101SecantPencils Erdos101Parabola Erdos101OrderedGrid
open scoped Classical

/-- Every center in U has a distinct partner in T that realizes every pair
in the same matching W on actual four-point lines. -/
def Pattern (S T U : Finset ℝ²) (F : PlanePoly) (W : Finset Pair) (m : ℕ) : Prop :=
  U ⊆ T ∧ W ⊆ S ×ˢ S ∧ W.card=m ∧ FrameIn W ∧ Set.InjOn Prod.fst (W : Set Pair) ∧
  Set.InjOn Prod.snd (W : Set Pair) ∧ ∀ p∈U, ∃ q∈T, p ≠ q ∧ ∀ v∈W, Realized S F (p,q) v

private theorem shared_rows {d s m : ℕ} (hs : 0 < s) (largeSample : 25 ≤ m) :
    ∃ C : ℕ, 0 < C ∧ ∃ N : ℕ, ∀ S T : Finset ℝ², N ≤ S.card → T ⊆ S →
    NonCollinearFor 5 (S : Set ℝ²) → ∀ F : PlanePoly, F.totalDegree ≤ d →
    (∀ p∈T, eval (fun i => p i) F ≠ 0) → S.card ≤ s*T.card →
    ∀ (D : ℝ² → Finset ℝ²) (c : ℝ² → ℝ² → ℝ²),
      (∀ p∈T, Row S F p (D p) (c p) ∧ S.card ≤ s*(D p).card) →
      ∃ W U, Pattern S T U F W m ∧ S.card ≤ C*U.card := by
  classical
  let t := 2*s^4
  have ht : 0 < t := by dsimp [t]; positivity
  let b := boxConstant d+4*d+2
  have hb : 0 < b := by dsimp [b]; omega
  let k := 4*(2*t)*m*b
  have hm : 0 < m := by omega
  have hk : 0 < k := by dsimp [k]; positivity
  let L := 8*(2*t)*k^(2+2*m)*d^3
  refine ⟨t*(1+L),Nat.mul_pos ht (by omega),max (max k m) (8*t+1),?_⟩
  intro S T size sub cap F degree outside dense D c rows
  let n := S.card
  have hkN : k ≤ n := (le_max_left k m).trans ((le_max_left ..).trans size)
  have hmN : m ≤ n := (le_max_right k m).trans ((le_max_left ..).trans size)
  have cut : 8*t+1 ≤ n := (le_max_right ..).trans size
  have pos : 0 < n := by omega
  obtain ⟨r,sep⟩ := separating S
  let h (p : ℝ²) := (shear r p).1
  let X := S.image h
  let Y (p : ℝ²) := (D p).image h
  have inside (p : ℝ²) (hp : p∈T) : D p ⊆ S := (rows p hp).1.1
  have xc : X.card=n := Finset.card_image_of_injOn sep
  have yc (p : ℝ²) (hp : p∈T) : (Y p).card=(D p).card :=
    Finset.card_image_of_injOn (sep.mono (Finset.coe_subset.mpr (inside p hp)))
  have common (p q : ℝ²) (hp : p∈T) (hq : q∈T) : (Y p ∩ Y q).card=(D p ∩ D q).card := by
    have both := Finset.union_subset (inside p hp) (inside q hq)
    have overlap := Finset.image_inter_of_injOn (D p) (D q) (sep.mono (by simpa using (Finset.coe_subset.mpr both)))
    change ((D p).image h ∩ (D q).image h).card=_
    rw [← overlap]
    exact Finset.card_image_of_injOn (sep.mono (Finset.coe_subset.mpr (Finset.inter_subset_left.trans (inside p hp))))
  let A := richPairs T Y n t
  have density {K : ℕ} (few : A.card ≤ K*n) : n ≤ t*(1+K) :=
    density_bound T X Y pos xc.le (Finset.card_le_card sub) (fun p hp => Finset.image_subset_image (inside p hp))
      dense (fun p hp => (yc p hp).symm ▸ (rows p hp).2) few
  have active : A.Nonempty := by
    by_contra! empty
    have zero : A.card=0 := Finset.card_eq_zero.mpr empty
    have hn := density (K := 0) (by simp [zero])
    simp at hn; omega
  have ends (e : Pair) (he : e∈A) := Finset.mem_product.mp (Finset.mem_filter.mp he).1
  have ne (e : Pair) (he : e∈A) : e.1 ≠ e.2 := (Finset.mem_filter.mp he).2.1
  let E (e : Pair) := pairs e D c
  have points (e : Pair) (he : e∈A) := pairs_from_rows (rows _ (ends e he).1).1 (rows _ (ends e he).2).1
  have rich (e : Pair) (he : e∈A) : n ≤ (2*t)*(E e).card := by
    obtain ⟨hp,hq⟩ := ends e he
    have first : n ≤ t*(Y e.1 ∩ Y e.2).card := (Finset.mem_filter.mp he).2.2
    rw [common _ _ hp hq] at first
    have loss := Nat.mul_le_mul_left t (discard_base_line cap e D (inside _ hp))
    have count : (E e).card=(pivots e D).card := (points e he).1
    rw [count]
    nlinarith only [first,loss,cut]
  have space : m ≤ (grid n).card := by
    simp only [grid,Finset.card_product,Finset.card_range]
    exact hmN.trans (Nat.le_mul_of_pos_right _ pos)
  obtain ⟨W,J,JA,subW,count,frame,first,last,shared,bound⟩ := shared_frame S F degree cap A active E
    (fun e he => ⟨sub (ends e he).1,sub (ends e he).2,ne e he,outside _ (ends e he).1,outside _ (ends e he).2⟩)
    (fun e he => (points e he).2.1) (fun e he v hv => realized_proper ((points e he).2.2.1 v hv))
    (fun e he => (points e he).2.2.2) largeSample hk hkN le_rfl space rich
  let U := J.image Prod.fst
  have upper : n ≤ t*(1+L*U.card) := density bound
  have upos : 0 < U.card := by
    by_contra! zero
    rw [Nat.eq_zero_of_le_zero zero] at upper
    simp at upper; omega
  refine ⟨W,U,⟨?_,subW,count,frame,first,last,?_⟩,?_⟩
  · intro p hp; obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
    exact (ends e (JA he)).1
  · intro p hp; obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨e.2,(ends e (JA he)).2,ne e (JA he),fun v hv => (points e (JA he)).2.2.1 v (shared e he hv)⟩
  · exact upper.trans (by
      calc
        t*(1+L*U.card) ≤ t*(U.card+L*U.card) := Nat.mul_le_mul_left _ (Nat.add_le_add_right upos _)
        _ = t*(1+L)*U.card := by ring)

/-- For each fixed degree, positive density, and prescribed sample size
at least 25, linearly many distinct external centers admit the same
two-sided endpoint frame and every other pair in the sample. -/
theorem sample_from_four_lines (d m : ℕ) (largeSample : 25 ≤ m) (τ : ℝ) (positive : 0 < τ) :
    ∃ C : ℕ, 0 < C ∧ ∃ N : ℕ, ∀ S T : Finset ℝ², N ≤ S.card → T ⊆ S →
    NonCollinearFor 5 (S : Set ℝ²) → ∀ F : PlanePoly, F.totalDegree ≤ d →
    (∀ p∈T, eval (fun i => p i) F ≠ 0) → τ*S.card ≤ T.card →
    (∀ p∈T, ∃ A : Finset (AffineSubspace ℝ ℝ²), τ*S.card ≤ A.card ∧
      ∀ L∈A, p∈L ∧ L∈linesWithPointsFor 4 (S : Set ℝ²) ∧
        2 ≤ (S.filter (fun x => x∈L ∧ eval (fun i => x i) F=0)).card) →
    ∃ W U, Pattern S T U F W m ∧ S.card ≤ C*U.card := by
  classical
  obtain ⟨s,hs⟩ := exists_nat_gt (1/τ)
  have sp : 0 < s := by exact_mod_cast (lt_trans (one_div_pos.mpr positive) hs)
  have scale : 1 ≤ (s : ℝ)*τ := (div_le_iff₀ positive).mp hs.le
  have natbound {n a : ℕ} (h : τ*n ≤ a) : n ≤ s*a := by
    exact_mod_cast (show (n : ℝ) ≤ (s : ℝ)*a from calc
      (n : ℝ) = 1*n := by ring
      _ ≤ ((s : ℝ)*τ)*n := mul_le_mul_of_nonneg_right scale (Nat.cast_nonneg n)
      _ = (s : ℝ)*(τ*n) := mul_assoc ..
      _ ≤ _ := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg s))
  obtain ⟨C,cp,N,result⟩ := shared_rows (d := d) sp largeSample
  refine ⟨C,cp,N,?_⟩
  intro S T sn sub cap F deg outside many rich
  have chooseRow (p : ℝ²) (hp : p∈T) : ∃ D : Finset ℝ², ∃ c : ℝ² → ℝ²,
      Row S F p D c ∧ S.card ≤ s*D.card := by
    obtain ⟨A,amount,valid⟩ := rich p hp
    obtain ⟨D,c,sz,row⟩ := row_of_lines S F p (outside p hp) A valid
    exact ⟨D,c,row,sz ▸ natbound amount⟩
  choose! D c rows using chooseRow
  exact result S T sn sub cap F deg outside (natbound many) D c rows

end Erdos101RichSecantSamples
end

open EuclideanGeometry MvPolynomial

theorem OMA.solution : OMA.R_Erdos101_erdos_101_R1_H1_R1_H2_R1.H1 := by
  intro d m largeSample τ pos
  obtain ⟨C,cp,N,extract⟩ := Erdos101RichSecantSamples.sample_from_four_lines d m largeSample τ pos
  refine ⟨C,cp,N,?_⟩
  intro S T n sub cap F deg outside many rich
  obtain ⟨W,U,pattern,bound⟩ := extract S T n sub cap F deg outside many rich
  obtain ⟨ut,ws,sz,_,left,right,hits⟩ := pattern
  exact ⟨W,U,ut,bound,ws,sz,left,right,hits⟩
