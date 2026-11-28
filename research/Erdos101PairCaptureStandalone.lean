import OMAReductions.R_Erdos101_erdos_101_R1_H1_R1
import Mathlib

/-!
# Two-point curve capture and overlapping grids in Erdős problem 101

A dense family of four-point lines with two points per line on a bounded-degree
curve has a dense subfamily with all four points on a bounded-degree curve.
The original conjecture follows from forcing the first pair and the published
bounded-degree quadruple-line theorem, represented here as an explicit premise.

The final sections give a finite criterion for forcing the first curve. For
n points and at least n³/k overlapping five-by-ten additive grids with the
stated multiplicities, one irreducible cubic contains three points on at
least n²/(2k³) distinct four-point lines when n ≥ 18k². The extraction
of that many grids from unrestricted four-point lines remains open.

Credit: @ubuwaits.
-/

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
/-- Count a shared pivot twice by its two centers. The estimate requires only
the total number of assigned pivots across the centers. -/
theorem common_pivots (centers : Finset ι) (U : Finset α) (D : ι → Finset α)
    [DecidableEq α] (hD : ∀ p ∈ centers, D p ⊆ U) :
    (∑ p ∈ centers, (D p).card)^2 ≤ U.card *
      ∑ e ∈ centers ×ˢ centers, (D e.1 ∩ D e.2).card := by
  classical
  let T (y : α) := centers.filter (fun p => y ∈ D p)
  have hsingle (p : ι) (hp : p ∈ centers) : U.filter (fun y => y ∈ D p) = D p := by
    ext y
    exact Finset.mem_filter.trans (and_iff_right_of_imp (fun hy => hD p hp hy))
  have hmass : ∑ p ∈ centers, (D p).card = ∑ y ∈ U, (T y).card := calc
    _ = ∑ p ∈ centers, (U.filter (fun y => y ∈ D p)).card :=
      Finset.sum_congr rfl (fun p hp => by rw [hsingle p hp])
    _ = _ := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow ..
  have hpairs (y : α) : (centers ×ˢ centers).filter
      (fun e => y ∈ D e.1 ∩ D e.2) = T y ×ˢ T y := by
    ext ⟨p,q⟩
    simp [T,and_assoc,and_left_comm]
  have hinter (e : ι × ι) (he : e ∈ centers ×ˢ centers) :
      U.filter (fun y => y ∈ D e.1 ∩ D e.2) = D e.1 ∩ D e.2 := by
    ext y
    exact Finset.mem_filter.trans (and_iff_right_of_imp (fun h =>
      hD _ (Finset.mem_product.mp he).1 (Finset.mem_inter.mp h).1))
  have second : ∑ e ∈ centers ×ˢ centers, (D e.1 ∩ D e.2).card = ∑ y ∈ U, (T y).card^2 := calc
    _ = ∑ e ∈ centers ×ˢ centers, (U.filter (fun y => y ∈ D e.1 ∩ D e.2)).card :=
      Finset.sum_congr rfl (fun e he => by rw [hinter e he])
    _ = ∑ y ∈ U, ((centers ×ˢ centers).filter (fun e => y ∈ D e.1 ∩ D e.2)).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow ..
    _ = _ := Finset.sum_congr rfl (fun y _ => by rw [hpairs,Finset.card_product,pow_two])
  rw [hmass,second]
  exact sq_sum_le_card_mul_sum_sq

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

namespace Erdos101SecantComponents
open EuclideanGeometry MvPolynomial
open scoped Classical Pointwise

lemma irreducible_degree_pos {F : MvPolynomial (Fin 2) ℝ} (h : Irreducible F) :
    0 < F.totalDegree := by
  by_contra! hdeg
  have he := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hdeg)
  have hc : F.coeff 0 ≠ 0 := by
    intro hz
    rw [hz, map_zero] at he
    exact h.ne_zero he
  exact h.not_isUnit (he ▸ (isUnit_iff_ne_zero.mpr hc).map C)

lemma count_factors_le_degree (s : Multiset (MvPolynomial (Fin 2) ℝ))
    (hs : ∀ F ∈ s, Irreducible F) : s.card ≤ s.prod.totalDegree := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons F s ih =>
    have hF := hs F (by simp)
    have hr : ∀ G ∈ s, Irreducible G := fun G hG => hs G (by simp [hG])
    have hn : s.prod ≠ 0 := fun he => (hr 0 (Multiset.prod_eq_zero_iff.mp he)).ne_zero rfl
    rw [Multiset.card_cons, Multiset.prod_cons, totalDegree_mul_of_isDomain hF.ne_zero hn]
    have := irreducible_degree_pos hF
    have := ih hr
    omega

/-- The zero set of a nonzero polynomial of degree d is covered by at most
d irreducible factors. Their degrees and their number are controlled even
when the input has repeated factors. -/
lemma component_cover {F : MvPolynomial (Fin 2) ℝ} (hF : F ≠ 0) :
    ∃ C : Finset (MvPolynomial (Fin 2) ℝ), C.card ≤ F.totalDegree ∧
      (∀ G ∈ C, Irreducible G ∧ G.totalDegree ≤ F.totalDegree) ∧
      ∀ p : ℝ², eval (fun i => p i) F = 0 → ∃ G ∈ C, eval (fun i => p i) G = 0 := by
  classical
  obtain ⟨s, hprime, hassoc⟩ := UniqueFactorizationMonoid.exists_prime_factors F hF
  have hirr : ∀ G ∈ s, Irreducible G := fun G hG => (hprime G hG).irreducible
  refine ⟨s.toFinset, (Multiset.toFinset_card_le _).trans ((count_factors_le_degree s hirr).trans
    (totalDegree_le_of_dvd_of_isDomain hassoc.dvd hF)), ?_, ?_⟩
  · intro G hG
    have hm := Multiset.mem_toFinset.mp hG
    exact ⟨hirr G hm,
      totalDegree_le_of_dvd_of_isDomain ((Multiset.dvd_prod hm).trans hassoc.dvd) hF⟩
  · intro p hp
    let e := eval (fun i => p i)
    have hz : e s.prod = 0 := (Associated.map e hassoc).eq_zero_iff.mpr hp
    rw [← Multiset.prod_hom s e] at hz
    obtain ⟨G, hG, he⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hz)
    exact ⟨G, Multiset.mem_toFinset.mpr hG, he⟩

lemma affine_polynomial_form {F : MvPolynomial (Fin 2) ℝ} (hd : F.totalDegree ≤ 1) :
    ∃ a b c : ℝ, F = C c + C a * X 0 + C b * X 1 := by
  classical
  let u : Fin 2 →₀ ℕ := Finsupp.single 0 1
  let v : Fin 2 →₀ ℕ := Finsupp.single 1 1
  have hu : u ≠ 0 := by simp [u]
  have hv : v ≠ 0 := by simp [v]
  have huv : u ≠ v := by
    intro he
    have := DFunLike.congr_fun he 0
    simp [u,v] at this
  refine ⟨F.coeff u, F.coeff v, F.coeff 0, ?_⟩
  apply MvPolynomial.ext
  intro w
  rw [C_mul_X_eq_monomial, C_mul_X_eq_monomial]
  simp only [C_apply, coeff_add, coeff_monomial]
  change F.coeff w = (if 0 = w then F.coeff 0 else 0) +
    (if u = w then F.coeff u else 0) + (if v = w then F.coeff v else 0)
  by_cases h0 : w = 0
  · simp [h0, hu, hv]
  by_cases h1 : w = u
  · simp [h1,hu.symm,huv.symm]
  by_cases h2 : w = v
  · simp [h2,hv.symm,huv]
  simp only [if_neg (Ne.symm h0), if_neg (Ne.symm h1), if_neg (Ne.symm h2), add_zero]
  by_contra hne
  have he := (le_totalDegree (mem_support_iff.mpr hne)).trans hd
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at he
  have hcases : (w 0 = 0 ∧ w 1 = 0) ∨ (w 0 = 1 ∧ w 1 = 0) ∨ (w 0 = 0 ∧ w 1 = 1) := by omega
  rcases hcases with h | h | h
  · apply h0
    ext i
    fin_cases i <;> simp [h]
  · apply h1
    ext i
    fin_cases i <;> simp [u,h]
  · apply h2
    ext i
    fin_cases i <;> simp [v,h]

/-- The points on a single linear factor form a collinear set, including
the case of a horizontal or vertical component. -/
lemma linear_zeros_collinear {F : MvPolynomial (Fin 2) ℝ} (hF : F ≠ 0)
    (hd : F.totalDegree ≤ 1) :
    Collinear ℝ {p : ℝ² | eval (fun i => p i) F = 0} := by
  obtain ⟨a,b,c,rfl⟩ := affine_polynomial_form hd
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      have hc : c ≠ 0 := by rintro rfl; simp at hF
      exact ⟨0, 0, fun p hp => False.elim (hc (by simpa using hp))⟩
    refine ⟨!₂[0,-c/b], !₂[1,0], ?_⟩
    intro p hp
    have h : c + b*p 1 = 0 := by simpa using hp
    refine ⟨p 0, ?_⟩
    ext i
    fin_cases i
    · simp
    · simp
      exact (eq_div_iff hb).mpr (by linarith)
  · refine ⟨!₂[-c/a,0], !₂[-b/a,1], ?_⟩
    intro p hp
    have h : c + a * p 0 + b * p 1 = 0 := by simpa using hp
    refine ⟨p 1, ?_⟩
    ext i
    fin_cases i
    · simp
      field_simp
      linarith
    · simp

lemma linear_component_card {F : MvPolynomial (Fin 2) ℝ} (hF : F ≠ 0)
    (hd : F.totalDegree ≤ 1) {S : Finset ℝ²} (hcap : NonCollinearFor 5 (S : Set ℝ²)) :
    (S.filter (fun p => eval (fun i => p i) F = 0)).card ≤ 4 := by
  by_contra! h
  obtain ⟨T, hT, hsize⟩ := Finset.exists_subset_card_eq
    (show 5 ≤ (S.filter (fun p => eval (fun i => p i) F = 0)).card by omega)
  apply hcap (T : Set ℝ²) (Finset.coe_subset.mpr (hT.trans (Finset.filter_subset ..)))
    T.finite_toSet (by simpa using hsize)
  exact Collinear.subset (fun p hp => (Finset.mem_filter.mp (hT hp)).2) (linear_zeros_collinear hF hd)

end Erdos101SecantComponents

noncomputable section

namespace Erdos101CurveIntersections

open EuclideanGeometry MvPolynomial
open scoped Classical

private abbrev Poly := MvPolynomial (Fin 2) ℝ
private abbrev V (n : ℕ) := restrictTotalDegree (Fin 2) ℝ n

private lemma exponent_sum (m : Fin 2 →₀ ℕ) :
    (m.sum fun _ e => e) = m 0 + m 1 := by
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]

private def exponentEquiv (t : ℕ) :
    {m : Fin 2 →₀ ℕ // (m.sum fun _ e => e) ≤ t} ≃
      (Σ k : Fin (t+1), Fin (k.val+1)) where
  toFun m :=
    ⟨⟨m.val 0 + m.val 1, by have := m.property; rw [exponent_sum] at this; omega⟩,
     ⟨m.val 0, by dsimp; omega⟩⟩
  invFun p :=
    ⟨Finsupp.equivFunOnFinite.symm ![p.2.val,p.1.val-p.2.val], by
      rw [exponent_sum]
      change p.2.val + (p.1.val - p.2.val) ≤ t
      have := p.2.isLt
      have := p.1.isLt
      omega⟩
  left_inv m := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · change m.val 0 + m.val 1 - m.val 0 = m.val 1
      omega
  right_inv p := by
    rcases p with ⟨⟨k,hk⟩,⟨j,hj⟩⟩
    change j < k+1 at hj
    have he : j + (k-j) = k := by omega
    apply Sigma.ext
    · exact Fin.ext he
    · exact (Fin.heq_ext_iff (congrArg (· + 1) he)).2 rfl

lemma twice_dimension (t : ℕ) :
    2 * Module.finrank ℝ (V t) = (t+1)*(t+2) := by
  classical
  change 2 * Module.finrank ℝ (restrictSupport ℝ {m : Fin 2 →₀ ℕ | (m.sum fun _ e => e) ≤ t}) = _
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport ℝ _)]
  change 2 * Nat.card {m : Fin 2 →₀ ℕ // (m.sum fun _ e => e) ≤ t} = _
  rw [Nat.card_congr (exponentEquiv t), Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  induction t with
  | zero => decide
  | succ t ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    nlinarith only [ih]

private lemma pair_indicator {p q : ℝ²} (hne : p ≠ q) :
    ∃ F : Poly, eval (fun i => p i) F = 1 ∧ eval (fun i => q i) F = 0 := by
  obtain ⟨i,hi⟩ : ∃ i, p i ≠ q i := by
    by_contra! h
    exact hne (by ext i; exact h i)
  exact ⟨C ((p i-q i)⁻¹) * (X i - C (q i)), by simp [sub_ne_zero.mpr hi], by simp⟩

private lemma indicator (S : Finset ℝ²) (p : S) :
    ∃ F : Poly, ∀ q : S, eval (fun i => q.val i) F = if p = q then 1 else 0 := by
  classical
  have factors (q : {q : S // q ≠ p}) :=
    pair_indicator (p := p.val) (q := q.val.val) (fun h => q.property (Subtype.ext h.symm))
  let L := fun q => (factors q).choose
  refine ⟨∏ q, L q, ?_⟩
  intro q
  rw [map_prod]
  by_cases he : p = q
  · subst q
    simp [show ∀ q, eval (fun i => p.val i) (L q) = 1 from fun q => (factors q).choose_spec.1]
  · rw [if_neg he]
    let j : {r : S // r ≠ p} := ⟨q, Ne.symm he⟩
    have hz : eval (fun i => q.val i) (L j) = 0 := (factors j).choose_spec.2
    exact Finset.prod_eq_zero (f := fun r => eval (fun i => q.val i) (L r)) (Finset.mem_univ j) hz

private def evaluation (S : Finset ℝ²) (n : ℕ) : V n →ₗ[ℝ] (S → ℝ) :=
  LinearMap.pi (fun p => (aeval (fun i => p.val i) : Poly →ₐ[ℝ] ℝ).toLinearMap.comp (V n).subtype)

private lemma interpolation (S : Finset ℝ²) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → Function.Surjective (evaluation S n) := by
  classical
  choose Q hQ using indicator S
  refine ⟨Finset.univ.sup (fun p => (Q p).totalDegree),?_⟩
  intro n hn f
  let P (p : S) : V n := ⟨Q p, (mem_restrictTotalDegree _ _ _).mpr
    ((Finset.le_sup (f := fun p => (Q p).totalDegree) (Finset.mem_univ p)).trans hn)⟩
  have hP (p q : S) : evaluation S n (P p) q = if p = q then 1 else 0 := hQ p q
  refine ⟨∑ p : S, f p • P p, ?_⟩
  ext q
  simp [map_sum,Finset.sum_apply,hP]

def multiples (F : Poly) (s n : ℕ) (h : F.totalDegree + s ≤ n) : V s →ₗ[ℝ] V n :=
  (((Algebra.lmul ℝ Poly) F).comp (V s).subtype).codRestrict (V n) (fun Q =>
    (mem_restrictTotalDegree _ _ _).mpr ((totalDegree_mul F Q.val).trans
      ((Nat.add_le_add_left ((mem_restrictTotalDegree _ _ _).mp Q.property) _).trans h)))

private lemma multiples_injective (F : Poly) (hF : F ≠ 0) (s n : ℕ) (h : F.totalDegree + s ≤ n) :
    Function.Injective (multiples F s n h) := by
  intro A B he
  exact Subtype.ext (mul_left_cancel₀ hF (congrArg Subtype.val he))

private lemma multiples_vanish (S : Finset ℝ²) (F : Poly)
    (hzero : ∀ p ∈ S, eval (fun i => p i) F = 0)
    (s n : ℕ) (h : F.totalDegree + s ≤ n) :
    LinearMap.range (multiples F s n h) ≤ LinearMap.ker (evaluation S n) := by
  rintro _ ⟨Q,rfl⟩
  apply LinearMap.mem_ker.mpr
  funext p
  change eval (fun i => p.val i) (F * Q.val) = 0
  simp [hzero p p.property]

/-- The affine Bézout bound on distinct real points. The first polynomial
is irreducible and does not divide the second. No general-position or
smoothness assumptions on the points are required. -/
theorem card_common_zeros_le (S : Finset ℝ²) (F G : MvPolynomial (Fin 2) ℝ)
    (hF : Irreducible F) (hdiv : ¬ F ∣ G)
    (hzF : ∀ p ∈ S, eval (fun i => p i) F = 0)
    (hzG : ∀ p ∈ S, eval (fun i => p i) G = 0) :
    S.card ≤ F.totalDegree * G.totalDegree := by
  classical
  obtain ⟨k,hk⟩ := interpolation S
  let d := F.totalDegree
  let e := G.totalDegree
  let t := d+e+k
  have hG : G ≠ 0 := by rintro rfl; exact hdiv (dvd_zero _)
  have hp : (F*G).totalDegree + k ≤ t := by
    rw [totalDegree_mul_of_isDomain hF.ne_zero hG]
  let f := multiples F (e+k) t (by dsimp [t,d]; omega)
  let g := multiples G (d+k) t (by dsimp [t,e]; omega)
  let j := multiples (F*G) k t hp
  have hinter : LinearMap.range f ⊓ LinearMap.range g ≤ LinearMap.range j := by
    rintro P ⟨⟨A,hA⟩,⟨B,hB⟩⟩
    have hAB : F * A.val = G * B.val := congrArg Subtype.val (hA.trans hB.symm)
    have hFB : F ∣ G * B.val := ⟨A.val,hAB.symm⟩
    obtain ⟨R,hR⟩ := ((UniqueFactorizationMonoid.irreducible_iff_prime.mp hF).dvd_mul.mp hFB).resolve_left hdiv
    have hdegR : R.totalDegree ≤ k := by
      by_cases hR0 : R = 0
      · simp [hR0]
      have hdegB := (mem_restrictTotalDegree _ _ _).mp B.property
      rw [hR,totalDegree_mul_of_isDomain hF.ne_zero hR0] at hdegB
      exact Nat.le_of_add_le_add_left hdegB
    refine ⟨⟨R,(mem_restrictTotalDegree _ _ _).mpr hdegR⟩,Subtype.ext ?_⟩
    change (F*G)*R = P.val
    calc
      _ = G * B.val := by rw [hR]; ring
      _ = _ := congrArg Subtype.val hB
  have hker : LinearMap.range f ⊔ LinearMap.range g ≤ LinearMap.ker (evaluation S t) :=
    sup_le (multiples_vanish S F hzF ..) (multiples_vanish S G hzG ..)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range f) (LinearMap.range g)
  have hf : Function.Injective f := multiples_injective F hF.ne_zero ..
  have hg : Function.Injective g := multiples_injective G hG ..
  rw [LinearMap.finrank_range_of_inj hf, LinearMap.finrank_range_of_inj hg] at hsum
  have heval := (evaluation S t).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (hk t (by dsimp [t]; omega)), finrank_top,
    Module.finrank_pi, Fintype.card_coe] at heval
  have hint := (Submodule.finrank_mono hinter).trans (LinearMap.finrank_range_le j)
  have hsub := Submodule.finrank_mono hker
  have hdim : S.card + Module.finrank ℝ (V (e+k)) + Module.finrank ℝ (V (d+k)) ≤
      Module.finrank ℝ (V t) + Module.finrank ℝ (V k) := by omega
  change S.card ≤ d*e
  dsimp [t] at hdim
  nlinarith only [hdim,twice_dimension (e+k),twice_dimension (d+k),twice_dimension (d+e+k),
    twice_dimension k]
end Erdos101CurveIntersections
end

/-
# Chords under a projectivity

If M is the inverse matrix of a projectivity and Y=(x,y,1), then
Y × M Y is a triple of quadratics. For a pencil with center a, the conic
a·(Y × M Y)=0 contains the intersection of a line of the pencil with its
image. A fixed irreducible nonlinear curve can share more than 2 deg F
such intersections for centers on at most one line.
-/

noncomputable section

namespace Erdos101PencilConics

open EuclideanGeometry MvPolynomial
open scoped Classical

abbrev Poly := MvPolynomial (Fin 2) ℝ

def affineForm (a b c : ℝ) : Poly := C a*X 0 + C b*X 1 + C c

lemma affineForm_degree (a b c : ℝ) : (affineForm a b c).totalDegree ≤ 1 := by
  apply (totalDegree_add ..).trans
  apply max_le
  · apply (totalDegree_add ..).trans
    exact max_le ((totalDegree_mul ..).trans (by simp)) ((totalDegree_mul ..).trans (by simp))
  · simp

lemma affineForm_eq_zero {a b c : ℝ} (h : affineForm a b c=0) : a=0 ∧ b=0 ∧ c=0 := by
  have h0 := congrArg (eval (![0,0] : Fin 2 → ℝ)) h
  have h1 := congrArg (eval (![1,0] : Fin 2 → ℝ)) h
  have h2 := congrArg (eval (![0,1] : Fin 2 → ℝ)) h
  simp [affineForm] at h0 h1 h2
  exact ⟨by linarith,by linarith,h0⟩

def conic (G : Fin 3 → Poly) (a : ℝ²) : Poly := a 0 • G 0 + a 1 • G 1 + G 2

lemma conic_degree (G : Fin 3 → Poly) (hG : ∀ j, (G j).totalDegree ≤ 2) (a : ℝ²) :
    (conic G a).totalDegree ≤ 2 := by
  apply (totalDegree_add ..).trans
  refine max_le ((totalDegree_add ..).trans (max_le ?_ ?_)) (hG 2)
  · rw [← C_mul']
    exact (totalDegree_mul ..).trans (by simpa using hG 0)
  · rw [← C_mul']
    exact (totalDegree_mul ..).trans (by simpa using hG 1)

private lemma scalar_multiple {F P : Poly} (hF : F ≠ 0) (hdeg : 2 ≤ F.totalDegree)
    (hP : P.totalDegree ≤ 2) (hdiv : F ∣ P) : P ∈ Submodule.span ℝ ({F} : Set Poly) := by
  obtain ⟨Q,rfl⟩ := hdiv
  by_cases h0 : Q=0
  · simp [h0]
  rw [totalDegree_mul_of_isDomain hF h0] at hP
  have he := totalDegree_eq_zero_iff_eq_C.mp (show Q.totalDegree=0 by omega)
  apply Submodule.mem_span_singleton.mpr
  refine ⟨Q.coeff 0,?_⟩
  rw [← C_mul',mul_comm,← he]

theorem pencil_centers_on_line (F : Poly) (hF : Irreducible F) (hdeg : 2 ≤ F.totalDegree)
    (G : Fin 3 → Poly) (hG : ∀ j, (G j).totalDegree ≤ 2)
    (hcross : X 0*G 0+X 1*G 1+G 2=0) (hn : ∃ j, G j ≠ 0) :
    ∃ L : Poly, L ≠ 0 ∧ L.totalDegree ≤ 1 ∧ ∀ a : ℝ²,
      (∃ Y : Finset ℝ², 2*F.totalDegree < Y.card ∧
        ∀ p ∈ Y, eval (fun i => p i) F=0 ∧ eval (fun i => p i) (conic G a)=0) →
      eval (fun i => a i) L=0 := by
  classical
  let V := Submodule.span ℝ ({F} : Set Poly)
  have hsome : ∃ j, G j ∉ V := by
    by_contra! hall
    choose c hc using fun j => Submodule.mem_span_singleton.mp (hall j)
    have hh : F*affineForm (c 0) (c 1) (c 2)=0 := by
      simp only [← hc,← C_mul'] at hcross
      unfold affineForm
      linear_combination hcross
    obtain ⟨h0,h1,h2⟩ := affineForm_eq_zero ((mul_eq_zero.mp hh).resolve_left hF.ne_zero)
    obtain ⟨j,hj⟩ := hn
    fin_cases j <;> apply hj <;> rw [← hc] <;> simp [h0,h1,h2]
  obtain ⟨j,hj⟩ := hsome
  obtain ⟨f,hf,hker⟩ := Submodule.exists_le_ker_of_notMem hj
  let L := affineForm (f (G 0)) (f (G 1)) (f (G 2))
  refine ⟨L,?_,affineForm_degree ..,?_⟩
  · intro h
    obtain ⟨h0,h1,h2⟩ := affineForm_eq_zero h
    fin_cases j <;> contradiction
  · rintro a ⟨Y,hY,hz⟩
    have hdiv : F ∣ conic G a := by
      by_contra h
      have hb := Erdos101CurveIntersections.card_common_zeros_le Y F (conic G a) hF h
        (fun p hp => (hz p hp).1) (fun p hp => (hz p hp).2)
      have hd := Nat.mul_le_mul_left F.totalDegree (conic_degree G hG a)
      rw [mul_comm 2] at hY
      omega
    have hv := LinearMap.mem_ker.mp (hker (scalar_multiple hF.ne_zero hdeg (conic_degree G hG a) hdiv))
    simpa [L,conic,affineForm,mul_comm] using hv

theorem at_most_four_centers (S A : Finset ℝ²) (hAS : A ⊆ S) (hcap : NonCollinearFor 5 (S : Set ℝ²))
    (F : Poly) (hF : Irreducible F) (hdeg : 2 ≤ F.totalDegree)
    (G : Fin 3 → Poly) (hG : ∀ j, (G j).totalDegree ≤ 2)
    (hcross : X 0*G 0+X 1*G 1+G 2=0) (hn : ∃ j, G j ≠ 0)
    (hA : ∀ a ∈ A, ∃ Y : Finset ℝ², 2*F.totalDegree < Y.card ∧
        ∀ p ∈ Y, eval (fun i => p i) F=0 ∧ eval (fun i => p i) (conic G a)=0) :
    A.card ≤ 4 := by
  obtain ⟨L,hL,hd,hl⟩ := pencil_centers_on_line F hF hdeg G hG hcross hn
  have hs : A ⊆ S.filter (fun p => eval (fun i => p i) L=0) := fun p hp =>
    Finset.mem_filter.mpr ⟨hAS hp,hl p (hA p hp)⟩
  exact (Finset.card_le_card hs).trans
    (Erdos101SecantComponents.linear_component_card hL hd hcap)

def crossForms (P Q R : Poly) : Fin 3 → Poly :=
  ![X 1*R-Q,P-X 0*R,X 0*Q-X 1*P]

lemma crossForms_syzygy (P Q R : Poly) :
    X 0*crossForms P Q R 0 + X 1*crossForms P Q R 1 + crossForms P Q R 2=0 := by
  dsimp [crossForms]
  ring

lemma crossForms_degree {P Q R : Poly} (hP : P.totalDegree ≤ 1) (hQ : Q.totalDegree ≤ 1)
    (hR : R.totalDegree ≤ 1) (i : Fin 3) : (crossForms P Q R i).totalDegree ≤ 2 := by
  have prod_bound (j : Fin 2) (A : Poly) (h : A.totalDegree ≤ 1) :
      (X j*A).totalDegree ≤ 2 := (totalDegree_mul ..).trans (by rw [totalDegree_X]; omega)
  have sub_bound (A B : Poly) (ha : A.totalDegree ≤ 2) (hb : B.totalDegree ≤ 2) :
      (A-B).totalDegree ≤ 2 := (totalDegree_sub ..).trans (max_le ha hb)
  fin_cases i
  · exact sub_bound _ _ (prod_bound 1 R hR) (by omega)
  · exact sub_bound _ _ (by omega) (prod_bound 0 R hR)
  · exact sub_bound _ _ (prod_bound 0 Q hQ) (prod_bound 1 P hP)

end Erdos101PencilConics
end

namespace Erdos101HarmonicAxes
open EuclideanGeometry
open scoped Classical
theorem line_pair_bound (S : Finset ℝ²) (hcap : NonCollinearFor 5 (S : Set ℝ²)) (p q : ℝ²) :
    (S.filter (fun z => z ∈ line[ℝ,p,q])).offDiag.card ≤ 12 := by
  let T := S.filter (fun z => z ∈ line[ℝ,p,q])
  have ht : T.card ≤ 4 := by
    by_contra! hc
    obtain ⟨B,hB,h5⟩ := Finset.exists_subset_card_eq (show 5 ≤ _ from hc)
    apply hcap (B : Set ℝ²) (Finset.coe_subset.mpr (hB.trans (Finset.filter_subset ..)))
      B.finite_toSet (by simpa using h5)
    apply (collinear_iff_exists_forall_eq_smul_vadd _).mpr
    refine ⟨p,q -ᵥ p,?_⟩
    intro z hz
    obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp (Finset.mem_filter.mp (hB hz)).2
    exact ⟨t,ht.symm⟩
  change T.offDiag.card ≤ 12
  rw [Finset.offDiag_card]
  interval_cases k : T.card <;> decide
end Erdos101HarmonicAxes

/- A fixed projective correspondence admits only boundedly many external
centers realizing a large matched sample on a curve of arbitrary degree.
The proof counts exceptional anchors separately on each irreducible factor. -/

noncomputable section
namespace Erdos101ProjectiveSecantCap

open EuclideanGeometry MvPolynomial Erdos101PencilConics
open Erdos101SecantComponents
open scoped Classical

private lemma line_bound (S : Finset ℝ²) (cap : NonCollinearFor 5 (S : Set ℝ²)) (a b : ℝ²) :
    (S.filter (fun p => p ∈ line[ℝ,a,b])).card ≤ 4 := by
  have h := Erdos101HarmonicAxes.line_pair_bound S cap a b
  rw [Finset.offDiag_card] at h
  by_contra! more
  have prod := Nat.mul_le_mul_right (S.filter (fun p => p ∈ line[ℝ,a,b])).card more
  omega

/-- A nonzero pencil of quadratic chord equations with its projective
syzygy leaves at most a bounded number of first centers. All pivots belong
to the same no-five-collinear configuration as the centers and anchors. -/
theorem centers_bound (S A U : Finset ℝ²) (anchors : A ⊆ S) (centers : U ⊆ S)
    (cap : NonCollinearFor 5 (S : Set ℝ²)) (F : Poly) (nonzero : F ≠ 0)
    (d : ℕ) (degree : F.totalDegree ≤ d) (large : 4*d < A.card)
    (G : Fin 3 → Poly) (quadratic : ∀ j, (G j).totalDegree ≤ 2)
    (syzygy : X 0*G 0+X 1*G 1+G 2=0) (nontrivial : ∃ j, G j ≠ 0)
    (hits : ∀ a∈A, ∀ p∈U, ∃ y∈S, p∈line[ℝ,a,y] ∧ eval (fun i => y i) F=0 ∧
      eval (fun i => y i) (conic G a)=0) : U.card ≤ 4*d*(4+2*d) := by
  classical
  obtain ⟨C,cc,factors,cover⟩ := component_cover nonzero
  let Y (H : Poly) (a : ℝ²) := S.filter (fun y => eval (fun i => y i) H=0 ∧ eval (fun i => y i) (conic G a)=0)
  let bad (H : Poly) := A.filter (fun a => 2 ≤ H.totalDegree ∧ 2*H.totalDegree < (Y H a).card)
  have few (H : Poly) (hc : H∈C) : (bad H).card ≤ 4 := by
    by_cases high : 2 ≤ H.totalDegree
    · apply at_most_four_centers S (bad H) ((Finset.filter_subset ..).trans anchors) cap H
        (factors H hc).1 high G quadratic syzygy nontrivial
      intro a ha
      exact ⟨Y H a,(Finset.mem_filter.mp ha).2.2,fun y hy => (Finset.mem_filter.mp hy).2⟩
    · have empty : bad H=∅ := Finset.filter_eq_empty_iff.mpr (fun _ _ h => high h.1)
      simp [empty]
  have count : (C.biUnion bad).card ≤ 4*d := calc
    _ ≤ ∑ H∈C, (bad H).card := Finset.card_biUnion_le
    _ ≤ ∑ _H∈C, 4 := Finset.sum_le_sum few
    _ = 4*C.card := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left 4 (cc.trans degree)
  obtain ⟨a,ha,good⟩ := Finset.not_subset.mp (show ¬ A ⊆ C.biUnion bad from
    fun sub => (not_le_of_gt large) ((Finset.card_le_card sub).trans count))
  have per (H : Poly) (hc : H∈C) : (Y H a).card ≤ 4+2*d := by
    by_cases high : 2 ≤ H.totalDegree
    · have bound : (Y H a).card ≤ 2*H.totalDegree := by
        by_contra! tooMany
        exact good (Finset.mem_biUnion.mpr ⟨H,hc,Finset.mem_filter.mpr ⟨ha,high,tooMany⟩⟩)
      have hd := (factors H hc).2.trans degree
      omega
    · have incl : Y H a ⊆ S.filter (fun y => eval (fun i => y i) H=0) := by
        intro y hy
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hy).2.1⟩
      have bound := linear_component_card (factors H hc).1.ne_zero (by omega : H.totalDegree ≤ 1) cap
      exact ((Finset.card_le_card incl).trans bound).trans (by omega)
  let V := C.biUnion (fun H => Y H a)
  have vc : V.card ≤ d*(4+2*d) := calc
    _ ≤ ∑ H∈C, (Y H a).card := Finset.card_biUnion_le
    _ ≤ ∑ _H∈C, (4+2*d) := Finset.sum_le_sum per
    _ = C.card*(4+2*d) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (cc.trans degree)
  let pencil (y : ℝ²) := S.filter (fun p => p∈line[ℝ,a,y])
  have inside : U ⊆ V.biUnion pencil := by
    intro p hp
    obtain ⟨y,ys,line,fy,gy⟩ := hits a ha p hp
    obtain ⟨H,hc,hy⟩ := cover y fy
    exact Finset.mem_biUnion.mpr ⟨y,Finset.mem_biUnion.mpr ⟨H,hc,Finset.mem_filter.mpr ⟨ys,hy,gy⟩⟩,
      Finset.mem_filter.mpr ⟨centers hp,line⟩⟩
  calc
    _ ≤ (V.biUnion pencil).card := Finset.card_le_card inside
    _ ≤ ∑ y∈V, (pencil y).card := Finset.card_biUnion_le
    _ ≤ ∑ _y∈V, 4 := Finset.sum_le_sum (fun y _ => line_bound S cap a y)
    _ = 4*V.card := by simp [Nat.mul_comm]
    _ ≤ 4*(d*(4+2*d)) := Nat.mul_le_mul_left _ vc
    _ = _ := by ring

end Erdos101ProjectiveSecantCap
end

/- Once one projective matrix carries each partner back to its first
center and each target anchor back to its matched source anchor, there
are only boundedly many original first centers. -/

noncomputable section
namespace Erdos101MatchedProjectivity

open EuclideanGeometry MvPolynomial Matrix Erdos101PencilConics Erdos101SecantFrame Erdos101SecantPencils
open scoped Classical Matrix

abbrev Vec := Fin 3 → ℝ
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

def lift (p : ℝ²) : Vec := ![p 0,p 1,1]
def row (M : Mat) (i : Fin 3) := affineForm (M i 0) (M i 1) (M i 2)
def forms (M : Mat) := crossForms (row M 0) (row M 1) (row M 2)

private lemma eval_row (M : Mat) (w : ℝ²) (i : Fin 3) :
    eval (fun j => w j) (row M i) = (M *ᵥ lift w) i := by
  simp [row,affineForm,mulVec,dotProduct,Fin.sum_univ_three,lift]

private def volume (a b c : Vec) :=
  a 0*(b 1*c 2-b 2*c 1)+a 1*(b 2*c 0-b 0*c 2)+a 2*(b 0*c 1-b 1*c 0)

private lemma value (M : Mat) (a w : ℝ²) :
    eval (fun i => w i) (conic (forms M) a)=volume (lift a) (lift w) (M *ᵥ lift w) := by
  simp [conic,forms,crossForms,volume,lift,eval_row,smul_eq_C_mul]

private lemma nontrivial {M : Mat} {p q : ℝ²} {r : ℝ}
    (pq : p ≠ q) (nz : r ≠ 0) (image : M *ᵥ lift q=r • lift p) : ∃ i, forms M i ≠ 0 := by
  by_contra! all
  have a := congrArg (eval (fun i => q i)) (all 0)
  have b := congrArg (eval (fun i => q i)) (all 1)
  simp [forms,crossForms,eval_row] at a b
  rw [image] at a b
  simp [lift] at a b
  apply pq
  ext i
  fin_cases i
  · change p 0=q 0
    apply mul_left_cancel₀ nz
    linear_combination b
  · change p 1=q 1
    apply mul_left_cancel₀ nz
    linear_combination -a

private lemma line_combination {p a w : ℝ²} (line : w∈line[ℝ,p,a]) :
    ∃ s t : ℝ, lift w=s • lift p+t • lift a := by
  obtain ⟨r,hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp line
  refine ⟨1-r,r,?_⟩
  rw [← hr]
  funext i
  fin_cases i <;> simp [lift,AffineMap.lineMap_apply_module]

private lemma on_conic {M : Mat} {p q a b w : ℝ²} {r s : ℝ}
    (center : M *ᵥ lift q = r • lift p) (anchor : M *ᵥ lift b = s • lift a)
    (first : w∈line[ℝ,p,a]) (second : w∈line[ℝ,q,b]) :
    eval (fun i => w i) (conic (forms M) a)=0 := by
  obtain ⟨i,j,first'⟩ := line_combination first
  obtain ⟨k,l,second'⟩ := line_combination second
  have image : M *ᵥ lift w = k • (r • lift p)+l • (s • lift a) := by
    rw [second',Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,center,anchor]
  rw [value,image,first']
  simp [volume]
  ring

/-- A projectively related subfamily of a fixed matching has at most
4d(4+2d) distinct first centers as soon as it uses more than 4d
different source anchors. -/
theorem matched_bound (S U : Finset ℝ²) (sub : U ⊆ S) (cap : NonCollinearFor 5 (S : Set ℝ²))
    (F : Poly) (nz : F ≠ 0) {d : ℕ} (degree : F.totalDegree ≤ d) (W : Finset Pair)
    (inside : W ⊆ S ×ˢ S) (many : 4*d < (W.image Prod.fst).card) (M : Mat)
    (anchors : ∀ v∈W, ∃ s : ℝ, M *ᵥ lift v.2=s • lift v.1)
    (partners : ∀ p∈U, ∃ q : ℝ², p ≠ q ∧ (∃ r : ℝ, r ≠ 0 ∧ M *ᵥ lift q=r • lift p) ∧
      ∀ v∈W, Realized S F (p,q) v) : U.card ≤ 4*d*(4+2*d) := by
  classical
  by_cases populated : U.Nonempty
  · obtain ⟨p₀,h₀⟩ := populated
    obtain ⟨q₀,ne,⟨r,hr,hm⟩,_⟩ := partners p₀ h₀
    have contained : W.image Prod.fst ⊆ S := by
      intro a ha; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_product.mp (inside hv)).1
    apply Erdos101ProjectiveSecantCap.centers_bound S (W.image Prod.fst) U contained sub cap F nz d degree many (forms M)
        (crossForms_degree (affineForm_degree ..) (affineForm_degree ..) (affineForm_degree ..))
        (crossForms_syzygy ..) (nontrivial ne hr hm)
    · intro a ha p hp
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨q,_,⟨t,_,pq⟩,hits⟩ := partners p hp
      obtain ⟨_,_,w,ws,wf,wa,_,_,pa,qb,_,_⟩ := hits v hv
      obtain ⟨s,vs⟩ := anchors v hv
      have line : line[ℝ,v.1,w] = line[ℝ,p,v.1] :=
        affineSpan_pair_eq_of_mem_of_mem_of_ne (right_mem_affineSpan_pair ..) pa wa.symm
      exact ⟨w,ws,line ▸ left_mem_affineSpan_pair ..,wf,on_conic pq vs pa qb⟩
  · simp [Finset.not_nonempty_iff_eq_empty.mp populated]

end Erdos101MatchedProjectivity
end

/- Detecting a generic center in a sequence of finite plane configurations.
If the centers in the n-th configuration escape every nonzero polynomial
of degree at most n, one ultrafilter simultaneously avoids every varying
polynomial test of bounded degree. -/

noncomputable section
namespace Erdos101GenericCenters

open Filter MvPolynomial
open scoped Classical Filter

abbrev Poly := MvPolynomial (Fin 2) ℝ

private structure Test where
  start : ℕ
  degree : ℕ
  poly : ℕ → Poly
  nonzero : ∀ n, poly n ≠ 0
  bounded : ∀ n, (poly n).totalDegree ≤ degree

private def Test.unit (k : ℕ) : Test := ⟨k,0,fun _ => 1,fun _ => one_ne_zero,fun _ => by simp⟩

private def Test.combine (a b : Test) : Test :=
  ⟨max a.start b.start,a.degree+b.degree,fun n => a.poly n*b.poly n,
    fun n => mul_ne_zero (a.nonzero n) (b.nonzero n),
    fun n => (totalDegree_mul ..).trans (Nat.add_le_add (a.bounded n) (b.bounded n))⟩

/-- Failing containment in any curve of uniformly bounded degree gives an
ultrafilter that avoids all polynomial tests, even when their coefficients
vary between configurations. -/
theorem avoiding_filter {β : Type*} (index : β → ℕ) (point : β → Fin 2 → ℝ)
    (escape : ∀ j : ℕ, ∀ F : Poly, F ≠ 0 → F.totalDegree ≤ j →
      ∃ z : β, index z=j ∧ eval (point z) F ≠ 0) :
    ∃ u : Ultrafilter β, Tendsto index (u : Filter β) atTop ∧
      ∀ (f : ℕ → Poly) (D : ℕ), (∀ j, f j ≠ 0) → (∀ j, (f j).totalDegree ≤ D) →
      ∀ᶠ z in u, eval (point z) (f (index z)) ≠ 0 := by
  let cell (a : Test) : Set β := {z | a.start ≤ index z ∧ eval (point z) (a.poly (index z)) ≠ 0}
  let B : FilterBasis β := {
    sets := Set.range cell
    nonempty := ⟨cell (.unit 0),Set.mem_range_self _⟩
    inter_sets := by
      rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩
      refine ⟨cell (a.combine b),Set.mem_range_self _,?_⟩
      intro z hz
      obtain ⟨large,nz⟩ := hz
      have nz' : eval (point z) (a.poly (index z))*eval (point z) (b.poly (index z)) ≠ 0 := by
        simpa [Test.combine] using nz
      exact ⟨⟨(le_max_left ..).trans large,left_ne_zero_of_mul nz'⟩,
        ⟨(le_max_right ..).trans large,right_ne_zero_of_mul nz'⟩⟩ }
  have : NeBot B.filter := B.hasBasis.neBot_iff.mpr (by
    rintro _ ⟨a,rfl⟩
    let j := max a.start a.degree
    obtain ⟨z,idx,nonzero⟩ := escape j (a.poly j) (a.nonzero j) ((a.bounded j).trans (le_max_right ..))
    exact ⟨z,idx.symm ▸ le_max_left a.start a.degree,by simpa [idx] using nonzero⟩)
  let u := Ultrafilter.of B.filter
  have member (a : Test) : ∀ᶠ z in u, z ∈ cell a := Ultrafilter.of_le B.filter (B.mem_filter_of_mem (Set.mem_range_self a))
  refine ⟨u,tendsto_atTop.mpr (fun j => (member (.unit j)).mono (fun _ h => h.1)),?_⟩
  intro f D nz bd
  exact (member ⟨0,D,f,nz,bd⟩).mono (fun _ h => h.2)

abbrev Limit {β : Type*} (u : Ultrafilter β) := Germ (u : Filter β) ℝ
abbrev Base {β : Type*} (u : Ultrafilter β) (index : β → ℕ) := Limit (u.map index)

/-- Coefficients may vary with the configuration but are fixed across the
points of each individual configuration. -/
def pull {β : Type*} (u : Ultrafilter β) (index : β → ℕ) : Base u index →+* Limit u where
  toFun f := f.compTendsto index (by rw [Ultrafilter.coe_map]; exact tendsto_map)
  map_one' := rfl
  map_zero' := rfl
  map_add' a b := Germ.inductionOn₂ a b (fun _ _ => rfl)
  map_mul' a b := Germ.inductionOn₂ a b (fun _ _ => rfl)

def position {β : Type*} (u : Ultrafilter β) (point : β → Fin 2 → ℝ) (i : Fin 2) : Limit u :=
  Germ.ofFun (fun z => point z i)

lemma eval_lift {β : Type*} (u : Ultrafilter β) (index : β → ℕ) (point : β → Fin 2 → ℝ)
    (P : MvPolynomial (Fin 2) (ℕ → ℝ)) :
    eval₂Hom (pull u index) (position u point) (map (Germ.coeRingHom (u.map index : Filter ℕ)) P) =
      (Germ.coeRingHom (u : Filter β)) (fun z => eval (point z) (map (Pi.evalRingHom (fun _ : ℕ => ℝ) (index z)) P)) := by
  let L := (eval₂Hom (pull u index) (position u point)).comp (map (Germ.coeRingHom (u.map index : Filter ℕ)))
  let R := (Germ.coeRingHom (u : Filter β)).comp (RingHom.pi (fun z => (eval (point z)).comp
    (map (Pi.evalRingHom (fun _ : ℕ => ℝ) (index z)))))
  have eq : L = R := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change eval₂Hom (pull u index) (position u point)
        (map (Germ.coeRingHom (u.map index : Filter ℕ)) (C c)) =
        (Germ.coeRingHom (u : Filter β)) (fun z => eval (point z)
          (map (Pi.evalRingHom (fun _ : ℕ => ℝ) (index z)) (C c)))
      simp only [MvPolynomial.map_C,eval₂Hom_C,eval_C]
      rfl
    · intro i
      change eval₂Hom (pull u index) (position u point)
        (map (Germ.coeRingHom (u.map index : Filter ℕ)) (X i)) =
        (Germ.coeRingHom (u : Filter β)) (fun z => eval (point z)
          (map (Pi.evalRingHom (fun _ : ℕ => ℝ) (index z)) (X i)))
      simp only [MvPolynomial.map_X,eval₂Hom_X',eval_X]
      rfl
  exact DFunLike.congr_fun eq P

/-- A single limiting center has two algebraically independent coordinates
over the field of all configuration-dependent coefficients. This gives the
generic point needed for a uniform bounded-degree curve assertion. -/
theorem independent_center {β : Type*} (index : β → ℕ) (point : β → Fin 2 → ℝ)
    (escape : ∀ j : ℕ, ∀ F : Poly, F ≠ 0 → F.totalDegree ≤ j →
      ∃ z : β, index z=j ∧ eval (point z) F ≠ 0) :
    ∃ u : Ultrafilter β, Tendsto index (u : Filter β) atTop ∧
      (∀ (f : ℕ → Poly) (D : ℕ), (∀ j, f j ≠ 0) → (∀ j, (f j).totalDegree ≤ D) →
        ∀ᶠ z in u, eval (point z) (f (index z)) ≠ 0) ∧
      let _ : Algebra (Base u index) (Limit u) := (pull u index).toAlgebra
      AlgebraicIndependent (Base u index) (position u point) := by
  classical
  obtain ⟨u,large,avoid⟩ := avoiding_filter index point escape
  refine ⟨u,large,avoid,?_⟩
  let _ : Algebra (Base u index) (Limit u) := (pull u index).toAlgebra
  apply algebraicIndependent_iff.mpr
  intro Q vanishes
  by_contra nz
  let v := u.map index
  let π := Germ.coeRingHom (v : Filter ℕ) (R := ℝ)
  have surj : Function.Surjective π := Quot.mk_surjective
  obtain ⟨P,rep⟩ := MvPolynomial.map_surjective π surj Q
  obtain ⟨m,coeffNz⟩ := exists_coeff_ne_zero nz
  rw [← rep,coeff_map] at coeffNz
  let f (j : ℕ) := map (Pi.evalRingHom (fun _ : ℕ => ℝ) j) P
  have projected : ∀ᶠ j in v, f j ≠ 0 := by
    have someCoeff : ∀ᶠ j in v, (P.coeff m) j ≠ 0 := Ultrafilter.eventually_not.mpr
      (fun hh => coeffNz (Germ.coe_eq.mpr hh))
    filter_upwards [someCoeff] with j hj
    intro zero
    apply hj
    simpa [f,coeff_map] using congrArg (coeff m) zero
  have nzAt : ∀ᶠ z in u, f (index z) ≠ 0 := projected
  let g (j : ℕ) := if f j = 0 then 1 else f j
  have gn (j : ℕ) : g j ≠ 0 := by simp [g]; split_ifs <;> simp_all
  have gd (j : ℕ) : (g j).totalDegree ≤ P.totalDegree := by
    dsimp only [g]
    split_ifs
    · simp
    · exact Finset.sup_mono (support_map_subset _ P)
  have misses : ∀ᶠ z in u, eval (point z) (f (index z)) ≠ 0 := by
    filter_upwards [avoid g P.totalDegree gn gd,nzAt] with z hz hz'
    simpa [g,hz'] using hz
  have must : ∀ᶠ z in u, eval (point z) (f (index z))=0 := by
    apply Germ.coe_eq.mp
    have eq := eval_lift u index point P
    rw [← rep] at vanishes
    exact eq.symm.trans vanishes
  exact (Ultrafilter.eventually_not.mp misses) must

/-- Polynomials with varying real coefficients but one degree bound are
specializations of a single polynomial over the ring of coefficient sequences. -/
theorem lift_bounded (f : ℕ → Poly) (d : ℕ) (degree : ∀ j, (f j).totalDegree ≤ d) :
    ∃ P : MvPolynomial (Fin 2) (ℕ → ℝ), ∀ j,
      map (Pi.evalRingHom (fun _ : ℕ => ℝ) j) P=f j := by
  classical
  let exponent (v : ℕ × ℕ) := Finsupp.single (0 : Fin 2) v.1 + Finsupp.single 1 v.2
  let B := (Finset.range (d+1) ×ˢ Finset.range (d+1)).image exponent
  have sub (j : ℕ) : (f j).support ⊆ B := by
    intro m hm
    have bound := (le_totalDegree hm).trans (degree j)
    rw [Finsupp.sum_fintype _ _ (by simp),Fin.sum_univ_two] at bound
    apply Finset.mem_image.mpr
    refine ⟨(m 0,m 1),Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,?_⟩
    ext i; fin_cases i <;> simp [exponent]
  let P := ∑ m∈B, monomial m (fun j => (f j).coeff m)
  refine ⟨P,fun j => ?_⟩
  change map _ (∑ m∈B, monomial m (fun j => (f j).coeff m))=f j
  rw [map_sum]
  simp only [map_monomial,Pi.evalRingHom_apply]
  conv_rhs => rw [(f j).as_sum]
  symm
  exact Finset.sum_subset (sub j) (fun m _ hm => by
    rw [notMem_support_iff.mp hm]; simp)

/-- Every evaluation of a bounded-degree family commutes with passage
to the limiting fields, including at the varying center or a pivot. -/
theorem transfer_curve {β : Type*} (u : Ultrafilter β) (index : β → ℕ)
    (f : ℕ → Poly) (d : ℕ) (degree : ∀ j, (f j).totalDegree ≤ d) :
    ∃ Q : MvPolynomial (Fin 2) (Base u index), ∀ point : β → Fin 2 → ℝ,
      eval₂Hom (pull u index) (position u point) Q =
        Germ.coeRingHom (u : Filter β) (fun z => eval (point z) (f (index z))) := by
  obtain ⟨P,rep⟩ := lift_bounded f d degree
  refine ⟨map (Germ.coeRingHom (u.map index : Filter ℕ)) P,fun point => ?_⟩
  simpa only [rep] using eval_lift u index point P

end Erdos101GenericCenters
end

/-
# Four projective pencils in characteristic zero

In a projective frame the four pencils have parameters x, y, y/x and
(y−1)/(x−1). On a two-dimensional algebraic correspondence, a target
parameter algebraic over the corresponding source parameter is constant
along that pencil. The four resulting identities determine both target
coordinates. This is the function-field calculation for the finite
anchor argument in the external-secant case of Erdős 101.
-/

noncomputable section

namespace Erdos101FourPencils

open IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

def constants (D : Derivation k K K) : IntermediateField k K where
  carrier := {x | D x = 0}
  zero_mem' := D.map_zero
  one_mem' := D.map_one_eq_zero
  add_mem' ha hb := by change D (_+_) = 0; rw [map_add,ha,hb,add_zero]
  mul_mem' ha hb := by change D (_*_) = 0; rw [D.leibniz,ha,hb,smul_zero,smul_zero,add_zero]
  inv_mem' a ha := by change D a⁻¹ = 0; rw [D.leibniz_inv,ha,smul_zero]
  algebraMap_mem' := D.map_algebraMap

/-- A derivation that kills a parameter also kills every element algebraic
over the one-generated field. Separability is used at the minimal polynomial. -/
theorem algebraic_constant [CharZero K] (D : Derivation k K K) {a b : K}
    (ha : D a = 0) (hb : IsAlgebraic k⟮a⟯ b) : D b = 0 := by
  let E := k⟮a⟯
  have hE : E ≤ constants D := IntermediateField.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr ha)
  let d : Derivation E K K := {
    toLinearMap := {
      toFun := D
      map_add' := D.map_add
      map_smul' := fun z x => by
        change D ((z : K)*x) = (z : K)*D x
        have hz : D (z : K) = 0 := hE z.property
        simp [hz] }
    map_one_eq_zero' := D.map_one_eq_zero
    leibniz' := D.leibniz }
  have hn := (minpoly.irreducible hb.isIntegral).separable.aeval_derivative_ne_zero
    (minpoly.aeval E b)
  have h := d.map_aeval (minpoly E b) b
  rw [minpoly.aeval,map_zero,smul_eq_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hn

private lemma radial_identity [CharZero K] (Dx Dy : Derivation k K K) {x y u v : K}
    (hx : Dx x=1) (hy : Dy y=1) (hxy : Dx y=0) (hyx : Dy x=0)
    (hu : Dy u=0) (hv : Dx v=0) (hu0 : u ≠ 0)
    (hs : IsAlgebraic k⟮y/x⟯ (v/u)) : x*Dx u*v = y*Dy v*u := by
  let D := x • Dx + y • Dy
  have ex : D x = x := by simp [D,hx,hyx]
  have ey : D y = y := by simp [D,hy,hxy]
  have eu : D u = x*Dx u := by simp [D,hu]
  have ev : D v = y*Dy v := by simp [D,hv]
  have h0 : D (y/x) = 0 := by rw [D.leibniz_div,ex,ey]; simp [mul_comm]
  have ht := algebraic_constant D h0 hs
  rw [D.leibniz_div,eu,ev] at ht
  have hz := (mul_eq_zero.mp ht).resolve_left (pow_ne_zero _ (inv_ne_zero hu0))
  linear_combination -hz

private def ratio (a b : K) := ((b-1)*a)/(b*(a-1))

private lemma derivative_of_ratio (D : Derivation k K K) (x u c : K)
    (hx : D x=1) (hc : D c=0) (he : c*(u*(x-1))=(u-1)*x) :
    x^2*D u=c*u^2 := by
  have hd := congrArg D he
  simp only [D.leibniz,map_sub,D.map_one_eq_zero,hx,hc,smul_eq_mul] at hd
  linear_combination (x*D u+u)*he-x*u*hd

/-- After choosing separate frames on source and target, four algebraic
pencil correspondences force the same coordinates. The first pencil must
also vary in the target, expressed by algebraicity in the reverse direction. -/
theorem normalized_four_pencils [CharZero K] (Dx Dy : Derivation k K K) (x y u v : K)
    (hx : Dx x=1) (hy : Dy y=1) (hxy : Dx y=0) (hyx : Dy x=0)
    (hu : IsAlgebraic k⟮x⟯ u) (hxu : IsAlgebraic k⟮u⟯ x)
    (hv : IsAlgebraic k⟮y⟯ v) (hyv : IsAlgebraic k⟮v⟯ y)
    (h₀ : IsAlgebraic k⟮y/x⟯ (v/u))
    (h₁ : IsAlgebraic k⟮(y-1)/(x-1)⟯ ((v-1)/(u-1))) : u=x ∧ v=y := by
  have huY := algebraic_constant Dy hyx hu
  have hvX := algebraic_constant Dx hxy hv
  have hdu : Dx u ≠ 0 := fun h => one_ne_zero (hx.symm.trans (algebraic_constant Dx h hxu))
  have hdv : Dy v ≠ 0 := fun h => one_ne_zero (hy.symm.trans (algebraic_constant Dy h hyv))
  have x0 : x ≠ 0 := fun h => one_ne_zero (hx.symm.trans (h ▸ Dx.map_zero))
  have y0 : y ≠ 0 := fun h => one_ne_zero (hy.symm.trans (h ▸ Dy.map_zero))
  have x1 : x-1 ≠ 0 := fun h => one_ne_zero (hx.symm.trans ((sub_eq_zero.mp h) ▸ Dx.map_one_eq_zero))
  have y1 : y-1 ≠ 0 := fun h => one_ne_zero (hy.symm.trans ((sub_eq_zero.mp h) ▸ Dy.map_one_eq_zero))
  have u0 : u ≠ 0 := fun h => hdu (h ▸ Dx.map_zero)
  have v0 : v ≠ 0 := fun h => hdv (h ▸ Dy.map_zero)
  have u1 : u-1 ≠ 0 := fun h => hdu ((sub_eq_zero.mp h) ▸ Dx.map_one_eq_zero)
  have xy : x-y ≠ 0 := fun h => one_ne_zero (hx.symm.trans ((sub_eq_zero.mp h) ▸ hxy))
  have hA := radial_identity Dx Dy hx hy hxy hyx huY hvX u0 h₀
  have hB : (x-1)*Dx u*(v-1)=(y-1)*Dy v*(u-1) := by
    simpa using radial_identity Dx Dy (x := x-1) (y := y-1) (u := u-1) (v := v-1)
      (by simp [hx]) (by simp [hy]) (by simp [hxy]) (by simp [hyx])
      (by simp [huY]) (by simp [hvX]) u1 h₁
  let c := ratio x u
  have hc : c=ratio y v := by
    apply (div_eq_div_iff (mul_ne_zero u0 x1) (mul_ne_zero v0 y1)).mpr
    apply mul_left_cancel₀ hdu
    linear_combination (y-1)*(u-1)*hA - (y*u)*hB
  have cx : c*(u*(x-1))=(u-1)*x := div_mul_cancel₀ _ (mul_ne_zero u0 x1)
  have cy : c*(v*(y-1))=(v-1)*y := by rw [hc]; exact div_mul_cancel₀ _ (mul_ne_zero v0 y1)
  have cn : c ≠ 0 := div_ne_zero (mul_ne_zero u1 x0) (mul_ne_zero u0 x1)
  have dcx : Dx c=0 := by rw [hc]; simp [ratio,Derivation.leibniz_div,hxy,hvX]
  have dcy : Dy c=0 := by simp [c,ratio,Derivation.leibniz_div,hyx,huY]
  have ux := derivative_of_ratio Dx x u c hx dcx cx
  have vy := derivative_of_ratio Dy y v c hy dcy cy
  have huv : u*y=v*x := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero cn u0) v0)
    linear_combination x*y*hA - y*v*ux + x*u*vy
  let r := u/x
  have rx : r*x=u := div_mul_cancel₀ _ x0
  have ry : r*y=v := by dsimp [r]; field_simp; linear_combination huv
  rw [← rx] at cx
  rw [← ry] at cy
  have cxx : c*r*(x-1)=r*x-1 := by
    apply mul_right_cancel₀ x0
    linear_combination cx
  have cyy : c*r*(y-1)=r*y-1 := by
    apply mul_right_cancel₀ y0
    linear_combination cy
  have rr : (r-1)*(x-y) = 0 := by linear_combination (y-1)*cxx-(x-1)*cyy
  have r1 := sub_eq_zero.mp ((mul_eq_zero.mp rr).resolve_right xy)
  exact ⟨by simpa [r1] using rx.symm,by simpa [r1] using ry.symm⟩

private lemma curve_rank_le_one (F : MvPolynomial (Fin 2) k) (hF : F ≠ 0) (w : Fin 2 → K)
    (hw : MvPolynomial.aeval w F=0) : (AlgebraicIndependent.matroid k K).eRk (Set.range w) ≤ 1 := by
  classical
  have hpair : Set.range w = ({w 0,w 1} : Set K) := by
    ext a
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | ha)
      · exact Set.mem_range_self 0
      · rw [Set.mem_singleton_iff.mp ha]
        exact Set.mem_range_self 1
  by_cases he : w 0 = w 1
  · simp [hpair,he]
  have inj : Function.Injective w := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  have hdep : (AlgebraicIndependent.matroid k K).Dep (Set.range w) := by
    apply (Matroid.not_indep_iff (by simp)).mp
    intro hind
    have hr : AlgebraicIndependent k ((↑) : Set.range w → K) := AlgebraicIndependent.matroid_indep_iff.mp hind
    exact hF (((algebraicIndependent_subtype_range inj).mp hr).eq_zero_of_aeval_eq_zero F hw)
  have ht := Matroid.eRk_lt_encard_of_dep_of_finite (Set.finite_range w) hdep
  rw [hpair,Set.encard_pair he] at ht
  exact ENat.lt_two_iff.mp (by simpa only [hpair] using ht)

private lemma mem_matroid_closure {U : Set K} {a : K} :
    a ∈ (AlgebraicIndependent.matroid k K).closure U ↔ IsAlgebraic (adjoin k U) a := by
  rw [AlgebraicIndependent.matroid_closure_eq,IntermediateField.isAlgebraic_adjoin_iff]
  rfl

/-- Two rational parameters of a point on a plane curve are dependent. Either
parameter, if transcendental, is enough to make the other one algebraic. -/
theorem curve_parameter (F : MvPolynomial (Fin 2) k) (hF : F ≠ 0) (w : Fin 2 → K)
    (hw : MvPolynomial.aeval w F=0) (s t : K) (hs : s ∈ adjoin k (Set.range w))
    (ht : t ∈ adjoin k (Set.range w)) (htr : Transcendental k s) : IsAlgebraic k⟮s⟯ t := by
  let M := AlgebraicIndependent.matroid k K
  let C := M.closure (Set.range w)
  have incl (a : K) (ha : a ∈ adjoin k (Set.range w)) : a ∈ C := by
    exact mem_matroid_closure.mpr (isAlgebraic_algebraMap (⟨a,ha⟩ : adjoin k (Set.range w)))
  have hi : M.Indep {s} := by
    apply AlgebraicIndependent.matroid_indep_iff.mpr
    exact (algebraicIndependent_singleton_iff (⟨s,Set.mem_singleton s⟩ : ({s} : Set K))).mpr htr
  have hR : M.eRk C ≤ M.eRk {s} := by
    rw [hi.eRk_eq_encard,Set.encard_singleton,M.eRk_closure_eq]
    exact curve_rank_le_one F hF w hw
  have hb := hi.isBasis_of_eRk_ge (Set.finite_singleton s) (Set.singleton_subset_iff.mpr (incl s hs)) hR
    (by simp [M])
  exact mem_matroid_closure.mp (hb.subset_closure (incl t ht))

def pencilParameters (a b : K) : Fin 4 → K := ![a,b,b/a,(b-1)/(a-1)]

/-- The input relations for four-pencil rigidity follow from a curve equation
at the four pivots and rational dependence of the two pencil coordinates on
each pivot. The pivots may differ from one pencil to the next. -/
theorem four_curve_pencils [CharZero K] (Dx Dy : Derivation k K K) (x y u v : K)
    (hx : Dx x=1) (hy : Dy y=1) (hxy : Dx y=0) (hyx : Dy x=0)
    (F : MvPolynomial (Fin 2) k) (hF : F ≠ 0) (w : Fin 4 → Fin 2 → K)
    (hw : ∀ i, MvPolynomial.aeval (w i) F=0)
    (hmem : ∀ i, pencilParameters x y i ∈ adjoin k (Set.range (w i)) ∧
      pencilParameters u v i ∈ adjoin k (Set.range (w i)))
    (hs : ∀ i, Transcendental k (pencilParameters x y i))
    (hu : Transcendental k u) (hv : Transcendental k v) : u=x ∧ v=y := by
  have forward (i : Fin 4) := curve_parameter F hF (w i) (hw i) _ _ (hmem i).1 (hmem i).2 (hs i)
  apply normalized_four_pencils Dx Dy x y u v hx hy hxy hyx (forward 0) ?_ (forward 1) ?_ (forward 2) (forward 3)
  · exact curve_parameter F hF (w 0) (hw 0) u x (hmem 0).2 (hmem 0).1 hu
  · exact curve_parameter F hF (w 1) (hw 1) v y (hmem 1).2 (hmem 1).1 hv

end Erdos101FourPencils
end

/- Coordinate derivations at a generic external center. A transcendence
basis supplies the formal partial derivatives, including in an arbitrary
characteristic-zero extension field. -/

noncomputable section
namespace Erdos101GenericPencils

open KaehlerDifferential MvPolynomial
open scoped Classical TensorProduct IntermediateField.algebraAdjoinAdjoin

private theorem extend_etale (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Algebra.FormallyEtale S T]
    (d : Derivation R S S) : ∃ E : Derivation R T T, ∀ s : S, E (algebraMap S T s)=algebraMap S T (d s) := by
  let f := (Algebra.linearMap S T).comp d.liftKaehlerDifferential
  let e := tensorKaehlerEquivOfFormallyEtale R S T
  let g := (f.liftBaseChange T).comp e.symm.toLinearMap
  refine ⟨g.compDer (D R T),?_⟩
  intro s
  change f.liftBaseChange T (e.symm (D R T (algebraMap S T s)))=_
  rw [tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,LinearMap.liftBaseChange_tmul,one_smul]
  exact congrArg (algebraMap S T) (d.liftKaehlerDifferential_comp_D s)

private def transport {R A S : Type*} [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
    (e : A ≃ₐ[R] S) (d : Derivation R A A) : Derivation R S S where
  toLinearMap := e.toLinearMap.comp (d.toLinearMap.comp e.symm.toLinearMap)
  map_one_eq_zero' := by simp
  leibniz' a b := by simp [d.leibniz,smul_eq_mul]

/-- Prescribe the values of a derivation on an entire transcendence basis. -/
theorem basis_derivation {k K ι : Type*} [Field k] [Field K] [Algebra k K] [CharZero K] {v : ι → K}
    (basis : IsTranscendenceBasis k v) (increments : ι → k) :
    ∃ d : Derivation k K K, ∀ i, d (v i)=algebraMap k K (increments i) := by
  let S := Algebra.adjoin k (Set.range v)
  let L := IntermediateField.adjoin k (Set.range v)
  have : Algebra.IsAlgebraic L K := basis.isAlgebraic_field
  have : Algebra.FormallyEtale L K := Algebra.FormallyEtale.of_isSeparable L K
  have : Algebra.FormallyEtale S L := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors S)
  have : IsScalarTower S L K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  have : Algebra.FormallyEtale S K := Algebra.FormallyEtale.comp S L K
  let e := basis.1.aevalEquiv
  let δ := MvPolynomial.mkDerivation k (fun i => (C (increments i) : MvPolynomial ι k))
  obtain ⟨d,h⟩ := extend_etale k S K (transport e δ)
  refine ⟨d,?_⟩
  intro i
  have coordinate : algebraMap S K (e (X i))=v i := by
    rw [basis.1.algebraMap_aevalEquiv,aeval_X]
  rw [← coordinate,h]
  change algebraMap S K (e (δ (e.symm (e (X i)))))=_
  rw [e.symm_apply_apply,MvPolynomial.mkDerivation_X,basis.1.algebraMap_aevalEquiv,aeval_C]

/-- A generic pair has two independent coordinate derivatives. -/
theorem coordinate_partials {k K : Type*} [Field k] [Field K] [Algebra k K] [CharZero K]
    (x : Fin 2 → K) (independent : AlgebraicIndependent k x) :
    ∃ dx dy : Derivation k K K, dx (x 0)=1 ∧ dy (x 1)=1 ∧ dx (x 1)=0 ∧ dy (x 0)=0 := by
  classical
  obtain ⟨b,extend,basis⟩ := exists_isTranscendenceBasis_superset independent.to_subtype_range
  let p (i : Fin 2) : b := ⟨x i,extend (Set.mem_range_self _)⟩
  have diff : x 0 ≠ x 1 := independent.injective.ne (by decide)
  obtain ⟨dx,hx⟩ := basis_derivation basis (fun a => if a.1=x 0 then 1 else 0)
  obtain ⟨dy,hy⟩ := basis_derivation basis (fun a => if a.1=x 1 then 1 else 0)
  exact ⟨dx,dy,by simpa [p] using hx (p 0),by simpa [p] using hy (p 1),
    by simpa [p,diff.symm] using hx (p 1),by simpa [p,diff] using hy (p 0)⟩

end Erdos101GenericPencils
end

/- Projective changes of coordinates preserve a generic plane point over
a coefficient field. A nonzero homogeneous linear form cannot vanish on
the affine lift of that point. -/

noncomputable section
namespace Erdos101ProjectiveChart

open IntermediateField Matrix MvPolynomial
open scoped Classical Matrix

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

abbrev Vec (k : Type*) := Fin 3 → k
abbrev Mat (k : Type*) := Matrix (Fin 3) (Fin 3) k

def lift (x : Fin 2 → K) : Vec K := ![x 0,x 1,1]
def normalize (v : Vec K) : Fin 2 → K := ![v 0/v 2,v 1/v 2]
def image (M : Mat k) (v : Vec K) : Vec K := (M.map (algebraMap k K)) *ᵥ v

lemma lift_normalize {v : Vec K} (nonzero : v 2 ≠ 0) : lift (normalize v)=(v 2)⁻¹ • v := by
  funext i; fin_cases i <;> simp [lift,normalize,div_eq_inv_mul,nonzero]

omit [Field K] in
private lemma range_two (x : Fin 2 → K) : Set.range x={x 0,x 1} := by
  ext z
  constructor
  · rintro ⟨i,rfl⟩; fin_cases i <;> simp
  · rintro (rfl|h)
    · exact Set.mem_range_self _
    · exact (Set.mem_singleton_iff.mp h) ▸ Set.mem_range_self 1

/-- Two coordinates that generate a field containing a generic pair must
themselves be algebraically independent. -/
theorem independent_of_generates {x y : Fin 2 → K} (hx : AlgebraicIndependent k x)
    (contains : ∀ i, x i ∈ adjoin k (Set.range y)) : AlgebraicIndependent k y := by
  let M := AlgebraicIndependent.matroid k K
  have subset : Set.range x ⊆ M.closure (Set.range y) := by
    rintro _ ⟨i,rfl⟩
    have equiv : x i ∈ M.closure (Set.range y) ↔ IsAlgebraic (adjoin k (Set.range y)) (x i) := by
      rw [AlgebraicIndependent.matroid_closure_eq,IntermediateField.isAlgebraic_adjoin_iff]
      rfl
    exact equiv.mpr (isAlgebraic_algebraMap (⟨x i,contains i⟩ : adjoin k (Set.range y)))
  have xi : M.Indep (Set.range x) := AlgebraicIndependent.matroid_indep_iff.mpr hx.to_subtype_range
  have xne : x 0 ≠ x 1 := hx.injective.ne (by decide)
  have lower : 2 ≤ M.eRk (Set.range y) := by
    have b := M.eRk_mono subset
    rwa [xi.eRk_eq_encard,range_two x,Set.encard_pair xne,M.eRk_closure_eq] at b
  have yne : y 0 ≠ y 1 := by
    intro eq
    have small := M.eRk_le_encard (Set.range y)
    rw [range_two y,eq,Set.pair_eq_singleton,Set.encard_singleton] at small
    rw [range_two y,eq,Set.pair_eq_singleton] at lower
    exact (by decide : ¬(2:ℕ∞) ≤ 1) (lower.trans small)
  have yi : Function.Injective y := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  have indep : M.Indep (Set.range y) := (M.indep_iff_eRk_eq_encard_of_finite (Set.finite_range y)).mpr
    (le_antisymm (M.eRk_le_encard _) (by simpa only [range_two y,Set.encard_pair yne] using lower))
  exact (algebraicIndependent_subtype_range yi).mp (AlgebraicIndependent.matroid_indep_iff.mp indep)

private def form (c : Vec k) : MvPolynomial (Fin 2) k := C (c 0)*X 0+C (c 1)*X 1+C (c 2)

private lemma form_ne {c : Vec k} (nz : c ≠ 0) : form c ≠ 0 := by
  intro zero; apply nz
  have h0 := congrArg (eval (![0,0] : Fin 2 → k)) zero
  have h1 := congrArg (eval (![1,0] : Fin 2 → k)) zero
  have h2 := congrArg (eval (![0,1] : Fin 2 → k)) zero
  simp [form] at h0 h1 h2
  funext i; fin_cases i
  · change c 0=0; simpa [h0] using h1
  · change c 1=0; simpa [h0] using h2
  · exact h0

lemma nonzero_row {x : Fin 2 → K} (hx : AlgebraicIndependent k x) {M : Mat k} {i : Fin 3}
    (row : M i ≠ 0) : image M (lift x) i ≠ 0 := by
  refine fun h => form_ne row (hx.eq_zero_of_aeval_eq_zero _ ?_)
  simpa [form,image,Matrix.mulVec,dotProduct,Fin.sum_univ_three,lift] using h

lemma apply_inverse (M N : Mat k) (inverse : N*M=1) (v : Vec K) : image N (image M v)=v := by
  dsimp [image]
  rw [Matrix.mulVec_mulVec,← Matrix.map_mul, inverse,Matrix.map_one _ (map_zero _) (map_one _),Matrix.one_mulVec]

private lemma ratio_mem (M : Mat k) (y : Fin 2 → K) (i : Fin 3) :
    image M (lift y) i ∈ adjoin k (Set.range y) := by
  let L := adjoin k (Set.range y)
  have c (j : Fin 3) : algebraMap k K (M i j) ∈ L := L.algebraMap_mem _
  have b (j : Fin 2) : y j ∈ L := subset_adjoin _ _ (Set.mem_range_self _)
  simpa [image,Matrix.mulVec,dotProduct,Fin.sum_univ_three,lift] using
    L.add_mem (L.add_mem (L.mul_mem (c 0) (b 0)) (L.mul_mem (c 1) (b 1))) (c 2)

/-- Normalize an invertible change of projective coordinates at a point
outside its pole line. The resulting coordinates have full transcendence degree. -/
theorem independent_chart (M N : Mat k) (inverse : N*M=1) {x : Fin 2 → K} (hx : AlgebraicIndependent k x)
    (den : image M (lift x) 2 ≠ 0) : AlgebraicIndependent k (normalize (image M (lift x))) := by
  let w := image M (lift x)
  let y := normalize w
  let L := adjoin k (Set.range y)
  have back : image N (lift y) = (w 2)⁻¹ • lift x := by
    rw [show lift y=(w 2)⁻¹ • w from lift_normalize den]
    change (N.map (algebraMap k K)) *ᵥ ((w 2)⁻¹ • w)=_
    rw [Matrix.mulVec_smul]
    exact congrArg (fun z => (w 2)⁻¹ • z) (apply_inverse M N inverse _)
  apply independent_of_generates hx
  have m (i : Fin 3) : (w 2)⁻¹ * lift x i ∈ L := by
    have v := ratio_mem N y i
    rw [back] at v; exact v
  have scale : (w 2)⁻¹ ∈ L := by simpa [lift] using m 2
  have coord (i : Fin 3) : lift x i ∈ L := by
    have cancel : (w 2)⁻¹ * lift x i / (w 2)⁻¹=lift x i := by field_simp [show w 2 ≠ 0 from den]
    exact cancel ▸ L.div_mem (m i) scale
  intro i; fin_cases i
  · exact coord 0
  · exact coord 1

end Erdos101ProjectiveChart
end

/- If a point of a plane curve is on a line defined over the algebraic
closure of the coefficient field, its coordinates are algebraic unless the
whole line belongs to the curve. A second, external point rules this out. -/

noncomputable section
namespace Erdos101AlgebraicLine

open MvPolynomial
open scoped Classical Polynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

private lemma evaluate_param (F : MvPolynomial (Fin 2) k) (g : Fin 2 → k[X]) (s : K) :
    Polynomial.aeval s (eval₂Hom Polynomial.C g F)=aeval (fun i => Polynomial.aeval s (g i)) F := by
  let A := (Polynomial.aeval (R := k) s).toRingHom.comp (eval₂Hom Polynomial.C g)
  let B := (aeval (fun i => Polynomial.aeval s (g i)) : MvPolynomial (Fin 2) k →ₐ[k] K).toRingHom
  have eq : A=B := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change Polynomial.aeval s (eval₂Hom Polynomial.C g (C c))=aeval (fun i => Polynomial.aeval s (g i)) (C c)
      simp only [eval₂Hom_C,Polynomial.aeval_C,aeval_C]
    · intro i
      change Polynomial.aeval s (eval₂Hom Polynomial.C g (X i))=aeval (fun i => Polynomial.aeval s (g i)) (X i)
      simp only [eval₂Hom_X',aeval_X]
  exact DFunLike.congr_fun eq F

private lemma coords_of_param (F : MvPolynomial (Fin 2) k) (g : Fin 2 → k[X])
    (s t : K) (q w : Fin 2 → K)
    (qs : ∀ i, Polynomial.aeval s (g i)=q i) (wt : ∀ i, Polynomial.aeval t (g i)=w i)
    (fq : aeval q F ≠ 0) (fw : aeval w F = 0) : ∀ i, IsAlgebraic k (w i) := by
  let P := eval₂Hom Polynomial.C g F
  have nz : P ≠ 0 := by
    intro zero; apply fq
    rw [← show (fun i => Polynomial.aeval s (g i))=q from funext qs,← evaluate_param]
    change Polynomial.aeval s P=0; simp [zero]
  have root : Polynomial.aeval t P=0 := by
    rw [show Polynomial.aeval t P=aeval (fun i => Polynomial.aeval t (g i)) F from evaluate_param F g t,funext wt]
    exact fw
  let E := algebraicClosure k K
  have ht : t ∈ E := mem_algebraicClosure_iff.mpr (⟨P,nz,root⟩ : IsAlgebraic k t)
  intro i
  let z : E := Polynomial.aeval (⟨t,ht⟩ : E) (g i)
  have val : (z : K) = w i := by
    change (E.val : E →ₐ[k] K) (Polynomial.aeval (⟨t,ht⟩ : E) (g i))=_
    exact (Polynomial.aeval_algHom_apply E.val (⟨t,ht⟩ : E) (g i)).symm.trans (wt i)
  exact mem_algebraicClosure_iff.mp (val ▸ z.property)

private def solveCoord (a b c : k) : k[X] := -(Polynomial.C a*Polynomial.X + Polynomial.C c)*Polynomial.C b⁻¹

private lemma solveCoord_eq {a b c : k} (nonzero : b ≠ 0) (x y : K)
    (eq : algebraMap k K a*x+algebraMap k K b*y+algebraMap k K c=0) :
    Polynomial.aeval x (solveCoord a b c)=y := by
  have n : algebraMap k K b ≠ 0 := (map_ne_zero_iff _ (algebraMap k K).injective).mpr nonzero
  simp [solveCoord]
  field_simp [n]
  linear_combination -eq

/-- All coordinates of w are algebraic when a line over k contains both
w on the curve and q outside it. -/
theorem on_line {F : MvPolynomial (Fin 2) k} {w q : Fin 2 → K}
    (fw : aeval w F=0) (fq : aeval q F ≠ 0) (a b c : k) (normal : a ≠ 0 ∨ b ≠ 0)
    (qw : algebraMap k K a*q 0+algebraMap k K b*q 1+algebraMap k K c=0)
    (ww : algebraMap k K a*w 0+algebraMap k K b*w 1+algebraMap k K c=0) :
    ∀ i, IsAlgebraic k (w i) := by
  rcases normal with ha|hb
  · let g : Fin 2 → k[X] := ![solveCoord b a c,Polynomial.X]
    apply coords_of_param F g (q 1) (w 1) q w _ _ fq fw
    · intro i; fin_cases i
      · exact solveCoord_eq (c := c) ha (q 1) (q 0) (by simpa only [add_comm (algebraMap k K a*q 0)] using qw)
      · simp [g]
    · intro i; fin_cases i
      · exact solveCoord_eq (c := c) ha (w 1) (w 0) (by simpa only [add_comm (algebraMap k K a*w 0)] using ww)
      · simp [g]
  · let g : Fin 2 → k[X] := ![Polynomial.X,solveCoord a b c]
    apply coords_of_param F g (q 0) (w 0) q w _ _ fq fw
    · intro i; fin_cases i
      · simp [g]
      · exact solveCoord_eq hb _ _ qw
    · intro i; fin_cases i
      · simp [g]
      · exact solveCoord_eq hb _ _ ww

/-- The same conclusion holds when the line coefficients are algebraic
over the base field. -/
theorem on_algebraic_line {F : MvPolynomial (Fin 2) k} {w q : Fin 2 → K}
    (fw : aeval w F=0) (fq : aeval q F ≠ 0) (a b c : K)
    (ha : IsAlgebraic k a) (hb : IsAlgebraic k b) (hc : IsAlgebraic k c)
    (normal : a ≠ 0 ∨ b ≠ 0) (qw : a*q 0+b*q 1+c=0) (ww : a*w 0+b*w 1+c=0) :
    ∀ i, IsAlgebraic k (w i) := by
  let E := algebraicClosure k K
  let lift (x : K) (h : IsAlgebraic k x) : E := ⟨x,mem_algebraicClosure_iff.mpr h⟩
  let H := map (algebraMap k E) F
  have val (p : Fin 2 → K) : aeval p H=aeval p F := by
    change eval₂ (algebraMap E K) p (map (algebraMap k E) F)=_
    rw [eval₂_map,← IsScalarTower.algebraMap_eq k E K]
    rfl
  have nr : lift a ha ≠ 0 ∨ lift b hb ≠ 0 := normal.imp (fun hn eq => hn (congrArg Subtype.val eq))
    (fun hn eq => hn (congrArg Subtype.val eq))
  have result := on_line (F := H) ((val w).trans fw) (fun h => fq ((val q).symm.trans h))
    (lift a ha) (lift b hb) (lift c hc) nr qw ww
  intro i
  exact (result i).restrictScalars k

end Erdos101AlgebraicLine
end

/- A curve pivot transfers transcendence of a pencil parameter to the
partner pencil. Finiteness of a line section rules out both poles and
algebraic target directions. -/

noncomputable section
namespace Erdos101PencilParameters

open IntermediateField MvPolynomial Erdos101ProjectiveChart
open scoped Classical

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

def coeff (A : Vec k) : Vec K := fun i => algebraMap k K (A i)
def lineValue (A : Vec K) (p : Fin 2 → K) := A 0*p 0 + A 1*p 1 + A 2

private lemma difference (A B : Vec K) (c : K) (p : Fin 2 → K) :
    lineValue (A-c • B) p=lineValue A p-c*lineValue B p := by simp [lineValue]; ring

private lemma alg_diff (A B : Vec k) {c : K} (hc : IsAlgebraic k c) (i : Fin 3) :
    IsAlgebraic k (((coeff A : Vec K)-c • (coeff B : Vec K)) i) := by
  let E := algebraicClosure k K
  apply mem_algebraicClosure_iff.mp
  exact E.sub_mem (E.algebraMap_mem _) (E.mul_mem (mem_algebraicClosure_iff.mpr hc) (E.algebraMap_mem _))

lemma lineValue_mem (A : Vec k) (w : Fin 2 → K) : lineValue (coeff A) w ∈ adjoin k (Set.range w) := by
  let L := adjoin k (Set.range w)
  have v (i : Fin 2) : w i ∈ L := subset_adjoin _ _ (Set.mem_range_self i)
  exact L.add_mem (L.add_mem (L.mul_mem (L.algebraMap_mem _) (v 0)) (L.mul_mem (L.algebraMap_mem _) (v 1)))
    (L.algebraMap_mem _)

lemma generic_line {p : Fin 2 → K} (generic : AlgebraicIndependent k p) {A : Vec K}
    (algebraic : ∀ i, IsAlgebraic k (A i)) (zero : lineValue A p=0) : A=0 := by
  let E := algebraicClosure k K
  let C (i : Fin 3) : E := ⟨A i,mem_algebraicClosure_iff.mpr (algebraic i)⟩
  have all : C=0 := by
    by_contra nz
    have notZero := nonzero_row (generic.extendScalars E) (M := fun (_ : Fin 3) => C) (i := 0) nz
    apply notZero
    change (∑ j : Fin 3, A j * Erdos101ProjectiveChart.lift p j)=0
    simpa [Fin.sum_univ_three,Erdos101ProjectiveChart.lift,lineValue] using zero
  funext i
  exact congrArg Subtype.val (congrFun all i)

private lemma curve_line {F : MvPolynomial (Fin 2) k} {q w : Fin 2 → K}
    (outside : aeval q F ≠ 0) (onCurve : aeval w F=0) (varies : ¬ ∀ i, IsAlgebraic k (w i))
    {A : Vec K} (algebraic : ∀ i, IsAlgebraic k (A i)) (zw : lineValue A w=0) (zq : lineValue A q=0) : A=0 := by
  by_cases normal : A 0 ≠ 0 ∨ A 1 ≠ 0
  · exact (varies (Erdos101AlgebraicLine.on_algebraic_line onCurve outside _ _ _ (algebraic 0) (algebraic 1)
      (algebraic 2) normal zq zw)).elim
  push Not at normal
  have last : A 2=0 := by simpa [lineValue,normal.1,normal.2] using zq
  funext i; fin_cases i
  · exact normal.1
  · exact normal.2
  · exact last

private lemma ratio_mem (A B : Vec k) (q w : Fin 2 → K) {s : K} (sne : s ≠ 0)
    (top : lineValue (coeff A) w=s*lineValue (coeff A) q)
    (bottom : lineValue (coeff B) w=s*lineValue (coeff B) q) :
    lineValue (coeff A) q/lineValue (coeff B) q ∈ adjoin k (Set.range w) := by
  have valid := (adjoin k (Set.range w)).div_mem (lineValue_mem A w) (lineValue_mem B w)
  rwa [top,bottom,mul_div_mul_left _ _ sne] at valid

/-- At a generic center every nondegenerate pencil coordinate is transcendental;
its value at any proper pivot belongs to the pivot's coordinate field. -/
theorem source (A B : Vec k) {p w : Fin 2 → K} (generic : AlgebraicIndependent k p)
    (bn : (coeff B : Vec K) ≠ 0) (independent : ∀ r : K, (coeff A : Vec K) ≠ r • (coeff B : Vec K))
    {s : K} (sne : s ≠ 0) (top : lineValue (coeff A) w=s*lineValue (coeff A) p)
    (bottom : lineValue (coeff B) w=s*lineValue (coeff B) p) :
    lineValue (coeff B) p ≠ 0 ∧ Transcendental k (lineValue (coeff A) p/lineValue (coeff B) p) ∧
      lineValue (coeff A) p/lineValue (coeff B) p ∈ adjoin k (Set.range w) ∧ ¬ ∀ i, IsAlgebraic k (w i) := by
  have den : lineValue (coeff B) p ≠ 0 := fun h => bn (generic_line generic (fun i => isAlgebraic_algebraMap (B i)) h)
  let r := lineValue (coeff A) p/lineValue (coeff B) p
  have trans : Transcendental k r := by
    intro alg
    apply independent r
    apply sub_eq_zero.mp (generic_line generic (alg_diff A B alg) ?_)
    rw [difference,div_mul_cancel₀ _ den,sub_self]
  have mem := ratio_mem A B p w sne top bottom
  refine ⟨den,trans,mem,?_⟩
  intro all
  have incl : adjoin k (Set.range w) ≤ algebraicClosure k K := adjoin_le_iff.mpr (by
    rintro _ ⟨i,rfl⟩; exact mem_algebraicClosure_iff.mpr (all i))
  exact trans (mem_algebraicClosure_iff.mp (incl mem))

/-- The target center has a finite, transcendental coordinate on each
paired pencil, even before its own genericity has been proved. -/
theorem target (A B : Vec k) {F : MvPolynomial (Fin 2) k} {q w : Fin 2 → K}
    (outside : aeval q F ≠ 0) (onCurve : aeval w F=0) (varies : ¬ ∀ i, IsAlgebraic k (w i))
    (bn : (coeff B : Vec K) ≠ 0) (independent : ∀ r : K, (coeff A : Vec K) ≠ r • (coeff B : Vec K))
    {s : K} (sne : s ≠ 0) (top : lineValue (coeff A) w=s*lineValue (coeff A) q)
    (bottom : lineValue (coeff B) w=s*lineValue (coeff B) q) :
    lineValue (coeff B) q ≠ 0 ∧ Transcendental k (lineValue (coeff A) q/lineValue (coeff B) q) ∧
    lineValue (coeff A) q/lineValue (coeff B) q ∈ adjoin k (Set.range w) := by
  have den : lineValue (coeff B) q ≠ 0 := by
    intro z; exact bn (curve_line outside onCurve varies (fun i => isAlgebraic_algebraMap (B i)) (by rw [bottom,z,mul_zero]) z)
  refine ⟨den,?_,ratio_mem A B q w sne top bottom⟩
  let r := lineValue (coeff A) q/lineValue (coeff B) q
  intro alg
  apply independent r
  have van : lineValue (coeff A-r • coeff B) q=0 := by rw [difference,div_mul_cancel₀ _ den,sub_self]
  apply sub_eq_zero.mp (curve_line outside onCurve varies (alg_diff A B alg) ?_ van)
  rw [difference] at van ⊢
  rw [top,bottom]
  linear_combination s*van

end Erdos101PencilParameters
end

/- Four matched curve pivots determine the image of a generic pair of
centers, in separate source and target projective frames. -/

noncomputable section
namespace Erdos101NormalizedSecants

open Matrix Erdos101PencilParameters Erdos101ProjectiveChart Erdos101FourPencils
open MvPolynomial (aeval)
open scoped Classical Matrix

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

def num (R : Type*) [Ring R] : Fin 4 → Vec R :=
  ![![1,0,0],![0,1,0],![0,1,0],![0,1,-1]]
def den (R : Type*) [Ring R] : Fin 4 → Vec R :=
  ![![0,0,1],![0,0,1],![1,0,0],![1,0,-1]]

def topRow (M : Mat k) (i : Fin 4) := num k i ᵥ* M
def botRow (M : Mat k) (i : Fin 4) := den k i ᵥ* M

private lemma num_map (i : Fin 4) : (algebraMap k K) ∘ num k i = num K i := by
  funext j; fin_cases i <;> fin_cases j <;> simp [num]
private lemma den_map (i : Fin 4) : (algebraMap k K) ∘ den k i = den K i := by
  funext j; fin_cases i <;> fin_cases j <;> simp [den]

private lemma top_map (M : Mat k) (i : Fin 4) :
    (coeff (topRow M i) : Vec K) = num K i ᵥ* M.map (algebraMap k K) := by
  funext j; simpa [coeff,topRow,num_map] using (algebraMap k K).map_vecMul M (num k i) j

private lemma bot_map (M : Mat k) (i : Fin 4) :
    (coeff (botRow M i) : Vec K) = den K i ᵥ* M.map (algebraMap k K) := by
  funext j; simpa [coeff,botRow,den_map] using (algebraMap k K).map_vecMul M (den k i) j

private lemma row_cancel (M N : Mat k) (inv : M*N=1) : Function.Injective (fun v : Vec K => v ᵥ* M.map (algebraMap k K)) := by
  intro a b eq
  have product : M.map (algebraMap k K)*N.map (algebraMap k K)=1 := by
    rw [← Matrix.map_mul,inv,Matrix.map_one _ (map_zero _) (map_one _)]
  have back := congrArg (fun v => v ᵥ* N.map (algebraMap k K)) eq
  simpa only [Matrix.vecMul_vecMul,product,Matrix.vecMul_one] using back

private lemma good_rows (M N : Mat k) (inv : M*N=1) (i : Fin 4) :
    (coeff (botRow M i) : Vec K) ≠ 0 ∧ ∀ r : K, (coeff (topRow M i) : Vec K) ≠ r • coeff (botRow M i) := by
  rw [bot_map,top_map]
  have inj := row_cancel (K := K) M N inv
  constructor
  · intro eq
    have z := inj (eq.trans (Matrix.zero_vecMul _).symm)
    fin_cases i
    · have := congrFun z 2; simp [den] at this
    · have := congrFun z 2; simp [den] at this
    · have := congrFun z 0; simp [den] at this
    · have := congrFun z 0; simp [den] at this
  · intro r eq
    rw [← Matrix.smul_vecMul] at eq
    have z := inj eq
    fin_cases i
    · have := congrFun z 0; simp [num,den] at this
    · have := congrFun z 1; simp [num,den] at this
    · have := congrFun z 1; simp [num,den] at this
    · have := congrFun z 1; simp [num,den] at this

private lemma value_dot (A : Vec K) (p : Fin 2 → K) : lineValue A p=A ⬝ᵥ lift p := by
  simp [lineValue,dotProduct,Fin.sum_univ_three,lift]

private lemma top_value (M : Mat k) (i : Fin 4) (p : Fin 2 → K) :
    lineValue (coeff (topRow M i)) p=num K i ⬝ᵥ image M (lift p) := by
  rw [value_dot,top_map]; exact (Matrix.dotProduct_mulVec ..).symm

private lemma bot_value (M : Mat k) (i : Fin 4) (p : Fin 2 → K) :
    lineValue (coeff (botRow M i)) p=den K i ⬝ᵥ image M (lift p) := by
  rw [value_dot,bot_map]; exact (Matrix.dotProduct_mulVec ..).symm

private lemma canonical (v : Vec K) (regular : ∀ i, den K i ⬝ᵥ v ≠ 0) (i : Fin 4) :
    num K i ⬝ᵥ v / (den K i ⬝ᵥ v)=pencilParameters (normalize v 0) (normalize v 1) i := by
  have h2 : v 2 ≠ 0 := by simpa [den,dotProduct,Fin.sum_univ_three] using regular 0
  have h0 : v 0 ≠ 0 := by simpa [den,dotProduct,Fin.sum_univ_three] using regular 2
  have hd : v 0-v 2 ≠ 0 := by simpa [den,dotProduct,Fin.sum_univ_three,sub_eq_add_neg] using regular 3
  fin_cases i <;> simp [num,den,dotProduct,Fin.sum_univ_three,pencilParameters,Erdos101ProjectiveChart.normalize,sub_eq_add_neg]
  all_goals field_simp [h0,h2,hd]

/-- Each pencil has a numerator and denominator that vanish at its standard
anchor. An off-anchor pivot has both evaluations scaled by the same nonzero factor. -/
def Direction (M : Mat k) (i : Fin 4) (p w : Fin 2 → K) : Prop :=
  ∃ s : K, s ≠ 0 ∧ lineValue (coeff (topRow M i)) w=s*lineValue (coeff (topRow M i)) p ∧
    lineValue (coeff (botRow M i)) w=s*lineValue (coeff (botRow M i)) p

lemma direction_dot (M : Mat k) (i : Fin 4) (p w : Fin 2 → K) : Direction M i p w ↔
    ∃ s : K, s ≠ 0 ∧ num K i ⬝ᵥ image M (lift w)=s*(num K i ⬝ᵥ image M (lift p)) ∧
      den K i ⬝ᵥ image M (lift w)=s*(den K i ⬝ᵥ image M (lift p)) := by
  simp only [Direction,top_value,bot_value]

/-- A generic first center, its external partner, and four proper pivots on
one curve determine the same normalized coordinates on both sides. -/
theorem rigid [CharZero K] (M N V Z : Mat k) (mi : M*N=1) (im : N*M=1) (vi : V*Z=1)
    (p q : Fin 2 → K) (generic : AlgebraicIndependent k p)
    (F : MvPolynomial (Fin 2) k) (outside : aeval q F ≠ 0) (w : Fin 4 → Fin 2 → K)
    (hits : ∀ i, aeval (w i) F=0) (ab : ∀ i, Direction M i p (w i)) (cd : ∀ i, Direction V i q (w i)) :
    normalize (image M (lift p))=normalize (image V (lift q)) ∧
      image M (lift p) 2 ≠ 0 ∧ image V (lift q) 2 ≠ 0 := by
  let x := normalize (image M (lift p))
  let y := normalize (image V (lift q))
  let raw (L : Mat k) (z : Fin 2 → K) (i : Fin 4) := lineValue (coeff (topRow L i)) z/lineValue (coeff (botRow L i)) z
  have left (i : Fin 4) : lineValue (coeff (botRow M i)) p ≠ 0 ∧ Transcendental k (raw M p i) ∧
      raw M p i ∈ IntermediateField.adjoin k (Set.range (w i)) ∧ ¬ ∀ j, IsAlgebraic k (w i j) := by
    obtain ⟨s,sn,a,b⟩ := ab i
    exact source _ _ generic (good_rows M N mi i).1 (good_rows M N mi i).2 sn a b
  have right (i : Fin 4) : lineValue (coeff (botRow V i)) q ≠ 0 ∧ Transcendental k (raw V q i) ∧
      raw V q i ∈ IntermediateField.adjoin k (Set.range (w i)) := by
    obtain ⟨s,sn,a,b⟩ := cd i
    exact target _ _ outside (hits i) (left i).2.2.2 (good_rows V Z vi i).1 (good_rows V Z vi i).2 sn a b
  have regularM (i : Fin 4) : den K i ⬝ᵥ image M (lift p) ≠ 0 := (bot_value M i p) ▸ (left i).1
  have regularV (i : Fin 4) : den K i ⬝ᵥ image V (lift q) ≠ 0 := (bot_value V i q) ▸ (right i).1
  have lm (i : Fin 4) : raw M p i=pencilParameters (x 0) (x 1) i := by
    dsimp only [raw]; rw [top_value,bot_value]; exact canonical _ regularM i
  have rv (i : Fin 4) : raw V q i=pencilParameters (y 0) (y 1) i := by
    dsimp only [raw]; rw [top_value,bot_value]; exact canonical _ regularV i
  have pd : image M (lift p) 2 ≠ 0 := by simpa [den,dotProduct,Fin.sum_univ_three] using regularM 0
  have qd : image V (lift q) 2 ≠ 0 := by simpa [den,dotProduct,Fin.sum_univ_three] using regularV 0
  have independent : AlgebraicIndependent k x := independent_chart M N im generic pd
  obtain ⟨dx,dy,xx,yy,xy,yx⟩ := Erdos101GenericPencils.coordinate_partials x independent
  have nz : F ≠ 0 := fun z => outside (by simp [z])
  have yt (i : Fin 4) : Transcendental k (pencilParameters (y 0) (y 1) i) :=
    rv i ▸ (right i).2.1
  obtain ⟨eq₀,eq₁⟩ := four_curve_pencils dx dy (x 0) (x 1) (y 0) (y 1) xx yy xy yx F nz w hits
    (fun i => ⟨lm i ▸ (left i).2.2.1,rv i ▸ (right i).2.2⟩)
    (fun i => lm i ▸ (left i).2.1) (yt 0) (yt 1)
  refine ⟨?_,pd,qd⟩
  funext i; fin_cases i
  · exact eq₀.symm
  · exact eq₁.symm

end Erdos101NormalizedSecants
end

/- Explicit projective coordinates for four real points in general position.
The three side equations of the first triangle are scaled to take value one
at the fourth point. -/

noncomputable section
namespace Erdos101SecantFrameCharts

open EuclideanGeometry MvPolynomial Matrix Erdos101ProjectiveChart
open scoped Classical Matrix

def standard (R : Type*) [Ring R] : Fin 4 → Vec R :=
  ![![0,1,0],![1,0,0],![0,0,1],![1,1,1]]

def pt (a : ℝ²) : Vec ℝ := ![a 0,a 1,1]
private def side (a b : ℝ²) : Vec ℝ := ![a 1-b 1,b 0-a 0,a 0*b 1-a 1*b 0]
private def area (a b c : ℝ²) := side a b ⬝ᵥ pt c

private lemma left (a b : ℝ²) : area a b a=0 := by simp [area,side,pt,dotProduct,Fin.sum_univ_three]; ring
private lemma right (a b : ℝ²) : area a b b=0 := by simp [area,side,pt,dotProduct,Fin.sum_univ_three]; ring

private lemma area_ne {a b c : ℝ²} (tri : ¬ Collinear ℝ ({a,b,c} : Set ℝ²)) : area a b c ≠ 0 := by
  intro zero; apply tri
  by_cases same : a=b
  · subst b; simpa using collinear_pair ℝ a c
  let v := side a b
  let F := Erdos101PencilConics.affineForm (v 0) (v 1) (v 2)
  have fn : F ≠ 0 := by
    intro bad
    obtain ⟨first,second,_⟩ := Erdos101PencilConics.affineForm_eq_zero bad
    apply same
    ext i; fin_cases i
    · exact (sub_eq_zero.mp second).symm
    · exact sub_eq_zero.mp first
  apply (Erdos101SecantComponents.linear_zeros_collinear fn (Erdos101PencilConics.affineForm_degree ..)).subset
  have val (p : ℝ²) : eval (fun i => p i) F=area a b p := by
    simp [F,Erdos101PencilConics.affineForm,area,v,pt,dotProduct,Fin.sum_univ_three]
  rintro p (ha|hb|h)
  · rw [ha]; exact (val a).trans (left a b)
  · rw [hb]; exact (val b).trans (right a b)
  · rw [Set.mem_singleton_iff.mp h]; exact (val c).trans zero

private def scaled (a b e : ℝ²) : Vec ℝ := (area a b e)⁻¹ • side a b

private lemma scaled_val (a b e p : ℝ²) : scaled a b e ⬝ᵥ pt p = (area a b e)⁻¹ * area a b p :=
  smul_dotProduct .. 

/-- The indices 0 and 1 are sent to the vertical and horizontal points at
infinity. The other two go to the origin and the affine point (1,1). -/
theorem chart (a b c e : ℝ²) (abc : ¬ Collinear ℝ ({a,b,c} : Set ℝ²))
    (abe : ¬ Collinear ℝ ({a,b,e} : Set ℝ²)) (ace : ¬ Collinear ℝ ({a,c,e} : Set ℝ²))
    (bce : ¬ Collinear ℝ ({b,c,e} : Set ℝ²)) :
    ∃ M N : Mat ℝ, M*N=1 ∧ N*M=1 ∧ ∃ r : Fin 4 → ℝ, ∀ i, r i ≠ 0 ∧
      M *ᵥ pt (![a,b,c,e] i)=r i • standard ℝ i := by
  let M : Mat ℝ := ![scaled a c e,scaled b c e,scaled a b e]
  let r : Fin 4 → ℝ := ![(area b c e)⁻¹*area b c a,(area a c e)⁻¹*area a c b,
    (area a b e)⁻¹*area a b c,1]
  have xx := area_ne ace
  have yy := area_ne bce
  have zz := area_ne abe
  have r0 : area b c a ≠ 0 := area_ne (by
    have eq : ({b,c,a} : Set ℝ²)={a,b,c} := by ext; simp [or_left_comm,or_comm]
    rwa [eq])
  have r1 : area a c b ≠ 0 := area_ne (by simpa only [Set.pair_comm] using abc)
  have nz (i : Fin 4) : r i ≠ 0 := by fin_cases i <;> simp [r,xx,yy,zz,r0,r1,area_ne abc]
  have hits (i : Fin 4) : M *ᵥ pt (![a,b,c,e] i)=r i • standard ℝ i := by
    funext j
    fin_cases i <;> fin_cases j <;> simp [M,Matrix.mulVec,scaled_val,r,standard,left,right,xx,yy,zz]
  let columns : Fin 3 → Vec ℝ := ![(r 1)⁻¹ • pt b,(r 0)⁻¹ • pt a,(r 2)⁻¹ • pt c]
  let N : Mat ℝ := fun i j => columns j i
  have col (i j : Fin 3) : (M*N) i j=(M *ᵥ columns j) i := rfl
  have inv : M*N=1 := by
    ext i j; rw [col]
    fin_cases j
    · change (M *ᵥ ((r 1)⁻¹ • pt b)) i=_
      rw [Matrix.mulVec_smul,show M *ᵥ pt b=r 1 • standard ℝ 1 from hits 1,smul_smul,inv_mul_cancel₀ (nz 1),one_smul]
      fin_cases i <;> rfl
    · change (M *ᵥ ((r 0)⁻¹ • pt a)) i=_
      rw [Matrix.mulVec_smul,show M *ᵥ pt a=r 0 • standard ℝ 0 from hits 0,smul_smul,inv_mul_cancel₀ (nz 0),one_smul]
      fin_cases i <;> rfl
    · change (M *ᵥ ((r 2)⁻¹ • pt c)) i=_
      rw [Matrix.mulVec_smul,show M *ᵥ pt c=r 2 • standard ℝ 2 from hits 2,smul_smul,inv_mul_cancel₀ (nz 2),one_smul]
      fin_cases i <;> rfl
  exact ⟨M,N,inv,mul_eq_one_comm.mp inv,r,fun i => ⟨nz i,hits i⟩⟩

end Erdos101SecantFrameCharts
end

/- Two projective maps agreeing at a generic plane point agree at every
point. This lets different four-point subframes share one matrix. -/

noncomputable section
namespace Erdos101ProjectiveAgreement

open Matrix MvPolynomial Erdos101ProjectiveChart
open scoped Classical Matrix

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

def Parallel (x y : Vec K) : Prop := ∀ i j, x i*y j=x j*y i

lemma parallel_of_scalar {x y : Vec K} {s : K} (h : x=s • y) : Parallel x y := by
  rw [h]; intro i j; simp; ring

lemma scalar_of_parallel {x y : Vec K} (h : Parallel x y) (hy : y ≠ 0) : ∃ s : K, x=s • y := by
  obtain ⟨j,hj⟩ : ∃ j, y j ≠ 0 := by by_contra! no; exact hy (funext no)
  refine ⟨x j/y j,?_⟩
  funext i; change x i=(x j/y j)*y i
  field_simp; exact h i j

private def rowPoly (M : Mat k) (i : Fin 3) : MvPolynomial (Fin 2) k := C (M i 0)*X 0+C (M i 1)*X 1+C (M i 2)

private lemma rowValue (M : Mat k) (i : Fin 3) (z : Fin 2 → K) :
    aeval z (rowPoly M i)=image M (lift z) i := by
  simp [rowPoly,image,Matrix.mulVec,dotProduct,Fin.sum_univ_three,lift]

theorem agree_everywhere {p : Fin 2 → K} (generic : AlgebraicIndependent k p) (M N : Mat k)
    (same : Parallel (image M (lift p)) (image N (lift p))) (z : Fin 2 → K) :
    Parallel (image M (lift z)) (image N (lift z)) := by
  intro i j
  let F := rowPoly M i*rowPoly N j-rowPoly M j*rowPoly N i
  have van : aeval p F=0 := by simp only [F,map_sub,map_mul,rowValue,sub_eq_zero]; exact same i j
  have ident := generic.eq_zero_of_aeval_eq_zero _ van
  have other := congrArg (aeval z) ident
  simpa only [F,map_sub,map_mul,rowValue,map_zero,sub_eq_zero] using other

lemma image_product (M N : Mat k) (z : Vec K) : image (M*N) z=image M (image N z) := by
  dsimp [image]; rw [Matrix.mulVec_mulVec,Matrix.map_mul]

lemma normalized_scalar {x y : Vec K} (hx : x 2 ≠ 0) (hy : y 2 ≠ 0)
    (same : Erdos101ProjectiveChart.normalize x=Erdos101ProjectiveChart.normalize y) :
    ∃ r : K, r ≠ 0 ∧ y=r • x := by
  let r := y 2 / x 2
  refine ⟨r,div_ne_zero hy hx,?_⟩
  have eq := congrArg (fun z => y 2 • lift z) same
  rw [lift_normalize hx,lift_normalize hy,smul_smul,smul_smul,mul_inv_cancel₀ hy,one_smul] at eq
  simpa only [r,div_eq_mul_inv] using eq.symm

/-- Recover the homogeneous image in the original coordinates from
agreement of two normalized points. -/
theorem matrix_from_normalized (M N V : Mat k) (inv : N*M=1) {p q : Fin 2 → K}
    (agree : Erdos101ProjectiveChart.normalize (image M (lift p))=Erdos101ProjectiveChart.normalize (image V (lift q)))
    (hp : image M (lift p) 2 ≠ 0) (hq : image V (lift q) 2 ≠ 0) :
    ∃ r : K, r ≠ 0 ∧ image (N*V) (lift q)=r • lift p := by
  obtain ⟨r,nz,rv⟩ := normalized_scalar hp hq agree
  refine ⟨r,nz,?_⟩
  rw [image_product,rv]
  change N.map (algebraMap k K) *ᵥ (r • image M (lift p))=_
  rw [Matrix.mulVec_smul]
  exact congrArg (fun z => r • z) (apply_inverse M N inv _)

/-- If two maps take the same generic point to the same image, an
anchor correspondence of the second map also holds for the first inverse. -/
theorem transfer_anchor {p q x y : Fin 2 → K} (generic : AlgebraicIndependent k p)
    (M N B : Mat k) (inv : N*M=1) {s t v : K} (vn : v ≠ 0)
    (first : image M (lift p)=s • lift q) (second : image B (lift p)=t • lift q)
    (anchor : image B (lift x)=v • lift y) :
    ∃ c : K, c ≠ 0 ∧ image N (lift y)=c • lift x := by
  have par : Parallel (image M (lift p)) (image B (lift p)) := by
    rw [first,second]; intro i j; simp; ring
  have atX := agree_everywhere generic M B par x
  rw [anchor] at atX
  have parY : Parallel (image M (lift x)) (lift y) := by
    intro i j; have h := atX i j
    change _*(v * _)=_*(v * _) at h
    apply mul_left_cancel₀ vn; linear_combination h
  have lift_ne : lift y ≠ 0 := by
    intro eq; have atTwo := congrFun eq 2; simp [lift] at atTwo
  obtain ⟨c,fc⟩ := scalar_of_parallel parY lift_ne
  have back : lift x=c • image N (lift y) := by
    calc
      lift x=image N (image M (lift x)) := (apply_inverse M N inv _).symm
      _ = c • image N (lift y) := by rw [fc]; exact Matrix.mulVec_smul ..
  have cn : c ≠ 0 := by
    rintro rfl; have h := congrFun back 2; simp [lift] at h
  exact ⟨c⁻¹,inv_ne_zero cn,by rw [back,smul_smul,inv_mul_cancel₀ cn,one_smul]⟩

end Erdos101ProjectiveAgreement
end

/- Passage of finite projective frames and proper secant pivots to
the field of germs of real plane configurations. -/

noncomputable section
namespace Erdos101SecantLimits

open Filter Matrix EuclideanGeometry Erdos101GenericCenters Erdos101ProjectiveChart
open Erdos101NormalizedSecants Erdos101SecantFrameCharts Erdos101ProjectiveAgreement
open scoped Classical Filter Matrix

variable {β : Type*}

abbrev g (u : Ultrafilter β) (f : β → ℝ) : Limit u := Germ.ofFun f
abbrev seqVec (u : Ultrafilter β) (x : β → Vec ℝ) : Vec (Limit u) := fun i => g u (fun z => x z i)
abbrev seqMat (u : Ultrafilter β) (M : β → Mat ℝ) : Mat (Limit u) := fun i j => g u (fun z => M z i j)
abbrev xy (u : Ultrafilter β) (x : β → ℝ²) := position u (fun z i => x z i)

lemma germ_nonzero (u : Ultrafilter β) {f : β → ℝ} : g u f ≠ 0 ↔ ∀ᶠ z in u, f z ≠ 0 := by
  change ¬ g u f=g u (fun _ => 0) ↔ _
  rw [Germ.coe_eq]
  exact Ultrafilter.eventually_not.symm

lemma vector_eq (u : Ultrafilter β) (a b : β → Vec ℝ) :
    seqVec u a=seqVec u b ↔ ∀ᶠ z in u, a z=b z := by
  constructor
  · intro h
    have each (i : Fin 3) : ∀ᶠ z in u, a z i=b z i := Germ.coe_eq.mp (congrFun h i)
    exact (Filter.eventually_all.mpr each).mono (fun _ hz => funext hz)
  · intro h; funext i; exact Germ.coe_eq.mpr (h.mono (fun _ hz => congrFun hz i))

lemma vec_smul (u : Ultrafilter β) (r : β → ℝ) (v : β → Vec ℝ) :
    seqVec u (fun z => r z • v z)=g u r • seqVec u v := rfl

lemma point_lift (u : Ultrafilter β) (x : β → ℝ²) : lift (xy u x)=seqVec u (fun z => pt (x z)) := by
  funext i; fin_cases i <;> rfl

lemma mat_mul (u : Ultrafilter β) (M N : β → Mat ℝ) :
    seqMat u (fun z => M z*N z)=seqMat u M*seqMat u N := by
  ext i j; simp only [seqMat,Matrix.mul_apply,Fin.sum_univ_three]; rfl

lemma mat_one (u : Ultrafilter β) : seqMat u (fun _ => (1 : Mat ℝ))=1 := by
  ext i j
  by_cases h : i=j
  · subst j; simp [seqMat]; rfl
  · simp [seqMat,h]; rfl

lemma mat_inverse (u : Ultrafilter β) (M N : β → Mat ℝ) (h : ∀ z, M z*N z=1) :
    seqMat u M*seqMat u N=1 := by rw [← mat_mul,show (fun z => M z*N z)=_ from funext h,mat_one]

abbrev baseAlgebra (u : Ultrafilter β) (J : β → ℕ) : Algebra (Base u J) (Limit u) := (pull u J).toAlgebra
local instance (u : Ultrafilter β) (J : β → ℕ) : Algebra (Base u J) (Limit u) := baseAlgebra u J

lemma action (u : Ultrafilter β) (J : β → ℕ) (M : ℕ → Mat ℝ) (v : β → Vec ℝ) :
    image (seqMat (u.map J) M) (seqVec u v)=seqVec u (fun z => M (J z) *ᵥ v z) := by
  funext i
  simp only [image,seqMat,seqVec,Matrix.map_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  rfl

lemma num_dot (u : Ultrafilter β) (i : Fin 4) (v : β → Vec ℝ) :
    num (Limit u) i ⬝ᵥ seqVec u v=g u (fun z => num ℝ i ⬝ᵥ v z) := by
  fin_cases i <;> simp [num,dotProduct,Fin.sum_univ_three,seqVec]
  rfl

lemma den_dot (u : Ultrafilter β) (i : Fin 4) (v : β → Vec ℝ) :
    den (Limit u) i ⬝ᵥ seqVec u v=g u (fun z => den ℝ i ⬝ᵥ v z) := by
  fin_cases i <;> simp [den,dotProduct,Fin.sum_univ_three,seqVec]
  rfl

private lemma standard_zeros (i : Fin 4) :
    num ℝ i ⬝ᵥ standard ℝ i=0 ∧ den ℝ i ⬝ᵥ standard ℝ i=0 := by
  fin_cases i <;> simp [num,den,standard,dotProduct,Fin.sum_univ_three]

private lemma real_direction (M : Mat ℝ) (i : Fin 4) (a p w : ℝ²) (r : ℝ)
    (anchor : M *ᵥ pt a = r • standard ℝ i) (different : w ≠ a) (line : w∈line[ℝ,p,a]) :
    ∃ s : ℝ, s ≠ 0 ∧ num ℝ i ⬝ᵥ (M *ᵥ pt w)=s*(num ℝ i ⬝ᵥ (M *ᵥ pt p)) ∧
      den ℝ i ⬝ᵥ (M *ᵥ pt w)=s*(den ℝ i ⬝ᵥ (M *ᵥ pt p)) := by
  obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp line
  have tn : 1-t ≠ 0 := by
    intro h; have := sub_eq_zero.mp h; subst t; apply different; simpa using ht.symm
  have combo : pt w=(1-t) • pt p+t • pt a := by
    rw [← ht]; funext j; fin_cases j <;> simp [pt,AffineMap.lineMap_apply_module]
  have evalRow (b : Vec ℝ) (zero : b ⬝ᵥ standard ℝ i=0) :
      b ⬝ᵥ (M *ᵥ pt w)=(1-t)*(b ⬝ᵥ (M *ᵥ pt p)) := by
    rw [combo,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,anchor,dotProduct_add]
    simp only [dotProduct_smul,smul_eq_mul,zero,mul_zero,add_zero]
  exact ⟨1-t,tn,evalRow _ (standard_zeros i).1,evalRow _ (standard_zeros i).2⟩

theorem pivot_direction (u : Ultrafilter β) (J : β → ℕ) (M : ℕ → Mat ℝ) (i : Fin 4)
    (a : ℕ → ℝ²) (p w : β → ℝ²) (r : ℕ → ℝ) (anchor : ∀ n, M n *ᵥ pt (a n)=r n • standard ℝ i)
    (different : ∀ z, w z ≠ a (J z)) (line : ∀ z, w z∈line[ℝ,p z,a (J z)]) :
    Direction (seqMat (u.map J) M) i (xy u p) (xy u w) := by
  choose s nz top bot using fun z => real_direction (M (J z)) i (a (J z)) (p z) (w z) (r (J z))
    (anchor (J z)) (different z) (line z)
  rw [direction_dot]
  refine ⟨g u s,germ_nonzero u |>.mpr (.of_forall nz),?_,?_⟩
  · rw [point_lift,point_lift,action,action,num_dot,num_dot]
    exact Germ.coe_eq.mpr (.of_forall top)
  · rw [point_lift,point_lift,action,action,den_dot,den_dot]
    exact Germ.coe_eq.mpr (.of_forall bot)

end Erdos101SecantLimits
end

/- Choosing compatible ordinary projective charts through any
designated pair of a finite matching. -/

noncomputable section
namespace Erdos101MatchedFrames

open Matrix EuclideanGeometry Erdos101ProjectiveChart Erdos101SecantFrameCharts
open scoped Classical Matrix

abbrev Pair := ℝ² × ℝ²

structure Frame where
  v : Fin 4 → Pair
  M : Mat ℝ
  N : Mat ℝ
  V : Mat ℝ
  Z : Mat ℝ
  mn : M*N=1
  nm : N*M=1
  vz : V*Z=1
  zv : Z*V=1
  l : Fin 4 → ℝ
  r : Fin 4 → ℝ
  left : ∀ i, l i ≠ 0 ∧ M *ᵥ pt (v i).1=l i • standard ℝ i
  right : ∀ i, r i ≠ 0 ∧ V *ᵥ pt (v i).2=r i • standard ℝ i

theorem frameAt (W : Finset Pair) (S : Finset ℝ²) (inside : W ⊆ S ×ˢ S)
    (cap : NonCollinearFor 5 (S : Set ℝ²)) (left : Set.InjOn Prod.fst (W : Set Pair))
    (right : Set.InjOn Prod.snd (W : Set Pair)) (many : 25 ≤ W.card) (a : Pair) (ha : a ∈ W) :
    ∃ f : Frame, f.v 0=a ∧ ∀ i, f.v i ∈ W := by
  obtain ⟨b,hb,c,hc,d,hd,abc,abd,acd,bcd⟩ := Erdos101SecantSamples.frame_with_first W S Prod.fst Prod.snd
    (fun p h => Finset.mem_product.mp (inside h)) cap left right many ha
  obtain ⟨M,N,mn,nm,l,hl⟩ := chart _ _ _ _ abc.1 abd.1 acd.1 bcd.1
  obtain ⟨V,Z,vz,zv,r,hr⟩ := chart _ _ _ _ abc.2 abd.2 acd.2 bcd.2
  let v : Fin 4 → Pair := ![a,b,c,d]
  have L (i : Fin 4) : l i ≠ 0 ∧ M *ᵥ pt (v i).1=l i • standard ℝ i := by fin_cases i <;> apply hl
  have R (i : Fin 4) : r i ≠ 0 ∧ V *ᵥ pt (v i).2=r i • standard ℝ i := by fin_cases i <;> apply hr
  refine ⟨⟨v,M,N,V,Z,mn,nm,vz,zv,l,r,L,R⟩,rfl,?_⟩
  intro i; fin_cases i <;> first | exact ha | exact hb | exact hc | exact hd

def Frame.forward (f : Frame) := f.Z*f.M
def Frame.backward (f : Frame) := f.N*f.V

theorem Frame.inverse (f : Frame) : f.backward*f.forward=1 := by
  calc
    (f.N*f.V)*(f.Z*f.M)=f.N*((f.V*f.Z)*f.M) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [f.vz,one_mul,f.nm]

theorem Frame.anchor (f : Frame) (i : Fin 4) :
    f.forward *ᵥ pt (f.v i).1=(f.l i/f.r i) • pt (f.v i).2 := by
  have back := congrArg (fun x => f.Z *ᵥ x) (f.right i).2
  simp only [Matrix.mulVec_mulVec,f.zv,Matrix.one_mulVec,Matrix.mulVec_smul] at back
  rw [Frame.forward,← Matrix.mulVec_mulVec,(f.left i).2,Matrix.mulVec_smul,back,smul_smul,div_mul_cancel₀ _ (f.right i).1]

end Erdos101MatchedFrames
end

/- A matched frame of four real secants and an algebraically generic
first center determine a common projective map in the limiting fields. -/

noncomputable section
namespace Erdos101FrameGerms

open Filter Matrix EuclideanGeometry Erdos101GenericCenters Erdos101ProjectiveChart
open Erdos101NormalizedSecants Erdos101SecantFrameCharts Erdos101ProjectiveAgreement
open Erdos101SecantLimits Erdos101MatchedFrames
open scoped Classical Filter Matrix

variable {β : Type*}
local instance (u : Ultrafilter β) (J : β → ℕ) : Algebra (Base u J) (Limit u) := baseAlgebra u J

private theorem limitCharZero (u : Ultrafilter β) : CharZero (Limit u) :=
  charZero_of_injective_ringHom ((Germ.coeRingHom (u : Filter β)).comp (Pi.constRingHom β ℝ)).injective

def MapsAt (u : Ultrafilter β) (J : β → ℕ) (M : ℕ → Mat ℝ) (p q : β → ℝ²) : Prop :=
  ∃ r : Limit u, r ≠ 0 ∧ image (seqMat (u.map J) M) (lift (xy u p))=r • lift (xy u q)

theorem maps_eventually (u : Ultrafilter β) (J : β → ℕ) {M : ℕ → Mat ℝ} {p q : β → ℝ²}
    (h : MapsAt u J M p q) :
    ∀ᶠ z in u, ∃ r : ℝ, r ≠ 0 ∧ M (J z) *ᵥ pt (p z)=r • pt (q z) := by
  obtain ⟨r,nz,eq⟩ := h
  obtain ⟨s,hs⟩ : ∃ s : β → ℝ, g u s=r := Quot.mk_surjective r
  rw [← hs] at nz eq
  rw [point_lift,point_lift,action,← vec_smul,vector_eq] at eq
  filter_upwards [(germ_nonzero u).mp nz,eq] with z hz hv
  exact ⟨s z,hz,hv⟩

theorem maps_of_real (u : Ultrafilter β) (J : β → ℕ) {M : ℕ → Mat ℝ} {p q : β → ℝ²}
    (s : β → ℝ) (sn : ∀ z, s z ≠ 0) (eq : ∀ z, M (J z) *ᵥ pt (p z)=s z • pt (q z)) :
    MapsAt u J M p q := by
  refine ⟨g u s,(germ_nonzero u).mpr (.of_forall sn),?_⟩
  rw [point_lift,point_lift,action,← vec_smul,vector_eq]
  exact .of_forall eq

def Pivots (uFrame : Frame) (F : Poly) (p q : ℝ²) : Prop :=
  ∀ i, ∃ w : ℝ², MvPolynomial.eval (fun j => w j) F=0 ∧ w ≠ (uFrame.v i).1 ∧ w ≠ (uFrame.v i).2 ∧
    w∈line[ℝ,p,(uFrame.v i).1] ∧ w∈line[ℝ,q,(uFrame.v i).2]

theorem frame_maps (u : Ultrafilter β) (J : β → ℕ) (f : ℕ → Frame) (p q : β → ℝ²)
    (generic : AlgebraicIndependent (Base u J) (xy u p)) (F : ℕ → Poly) (d : ℕ)
    (degree : ∀ n, (F n).totalDegree ≤ d) (outside : ∀ z, MvPolynomial.eval (fun i => q z i) (F (J z)) ≠ 0)
    (pivot : ∀ z, Pivots (f (J z)) (F (J z)) (p z) (q z)) :
    MapsAt u J (fun n => (f n).forward) p q ∧ MapsAt u J (fun n => (f n).backward) q p := by
  let _ : CharZero (Limit u) := limitCharZero u
  let v := u.map J
  let M := seqMat v (fun n => (f n).M)
  let N := seqMat v (fun n => (f n).N)
  let V := seqMat v (fun n => (f n).V)
  let Z := seqMat v (fun n => (f n).Z)
  have mn : M*N=1 := mat_inverse v _ _ (fun n => (f n).mn)
  have nm : N*M=1 := mat_inverse v _ _ (fun n => (f n).nm)
  have vz : V*Z=1 := mat_inverse v _ _ (fun n => (f n).vz)
  have zv : Z*V=1 := mat_inverse v _ _ (fun n => (f n).zv)
  obtain ⟨P,evalP⟩ := transfer_curve u J F d degree
  choose w hit wl wr lp lq using fun (i : Fin 4) z => pivot z i
  have nonzero : MvPolynomial.aeval (xy u q) P ≠ 0 := by
    change MvPolynomial.eval₂Hom (pull u J) _ P ≠ 0
    rw [evalP]; exact (germ_nonzero u).mpr (.of_forall outside)
  have hits (i : Fin 4) : MvPolynomial.aeval (xy u (w i)) P=0 := by
    change MvPolynomial.eval₂Hom (pull u J) _ P=0
    rw [evalP]; exact Germ.coe_eq.mpr (.of_forall (hit i))
  have left (i : Fin 4) : Direction M i (xy u p) (xy u (w i)) :=
    pivot_direction u J _ i _ _ _ _ (fun n => ((f n).left i).2) (wl i) (lp i)
  have right (i : Fin 4) : Direction V i (xy u q) (xy u (w i)) :=
    pivot_direction u J _ i _ _ _ _ (fun n => ((f n).right i).2) (wr i) (lq i)
  obtain ⟨eq,mp,vq⟩ := rigid M N V Z mn nm vz (xy u p) (xy u q) generic P nonzero _ hits left right
  constructor
  · unfold MapsAt; change ∃ r : Limit u, r ≠ 0 ∧ image (seqMat v (fun n => (f n).Z*(f n).M)) _=_
    rw [mat_mul]; exact matrix_from_normalized V Z M zv eq.symm vq mp
  · unfold MapsAt; change ∃ r : Limit u, r ≠ 0 ∧ image (seqMat v (fun n => (f n).N*(f n).V)) _=_
    rw [mat_mul]; exact matrix_from_normalized M N V nm eq mp vq

/-- Different choices of subframe give a single projectivity at every
matched anchor, since all of them have the same generic center and partner. -/
theorem common_anchor (u : Ultrafilter β) (J : β → ℕ) (f b : ℕ → Frame) (p q : β → ℝ²)
    (generic : AlgebraicIndependent (Base u J) (xy u p))
    (first : MapsAt u J (fun n => (f n).forward) p q) (second : MapsAt u J (fun n => (b n).forward) p q)
    (i : Fin 4) : MapsAt u J (fun n => (f n).backward)
      (fun z => ((b (J z)).v i).2) (fun z => ((b (J z)).v i).1) := by
  have special := maps_of_real u J (M := fun n => (b n).forward)
    (p := fun z => ((b (J z)).v i).1) (q := fun z => ((b (J z)).v i).2)
    (fun z => (b (J z)).l i/(b (J z)).r i)
    (fun z => div_ne_zero ((b (J z)).left i).1 ((b (J z)).right i).1) (fun z => (b (J z)).anchor i)
  obtain ⟨s,_,fs⟩ := first
  obtain ⟨t,_,bs⟩ := second
  obtain ⟨c,cn,bc⟩ := special
  exact transfer_anchor generic _ _ _ (mat_inverse (u.map J) _ _ (fun n => (f n).inverse)) cn fs bs bc

end Erdos101FrameGerms
end

/- All first centers realizing a sufficiently large fixed matching lie
on one curve of uniformly bounded degree. The degree depends only on
the original curve degree and is obtained by compactness. -/

noncomputable section
namespace Erdos101FixedSecantLocus

open EuclideanGeometry Filter MvPolynomial Matrix Erdos101GenericCenters
open Erdos101ProjectiveChart Erdos101SecantFrameCharts Erdos101SecantLimits
open Erdos101MatchedFrames Erdos101FrameGerms
open Erdos101SecantPencils (Realized)
open scoped Classical Filter Matrix

local instance {β : Type*} (u : Ultrafilter β) (J : β → ℕ) : Algebra (Base u J) (Limit u) := baseAlgebra u J

structure Configuration (d : ℕ) where
  S : Finset ℝ²
  U : Finset ℝ²
  W : Finset Pair
  F : Poly
  nonzero : F ≠ 0
  degree : F.totalDegree ≤ d
  centers : U ⊆ S
  cap : NonCollinearFor 5 (S : Set ℝ²)
  inside : W ⊆ S ×ˢ S
  first : Set.InjOn Prod.fst (W : Set Pair)
  second : Set.InjOn Prod.snd (W : Set Pair)
  size : 25 ≤ W.card
  distinct : 4*d < (W.image Prod.fst).card
  partners : ∀ p∈U, ∃ q : ℝ², p ≠ q ∧ eval (fun i => q i) F ≠ 0 ∧ ∀ v∈W, Realized S F (p,q) v

private theorem through_finite (U : Finset ℝ²) : ∃ F : Poly, F ≠ 0 ∧ F.totalDegree ≤ U.card ∧
    ∀ p∈U, eval (fun i => p i) F=0 := by
  let l (p : ℝ²) : Poly := X 0-C (p 0)
  have nz (p : ℝ²) : l p ≠ 0 := by
    intro eq
    have h := congrArg (eval (![p 0+1,0] : Fin 2 → ℝ)) eq
    simp [l] at h
  have degree (p : ℝ²) : (l p).totalDegree ≤ 1 := (totalDegree_sub ..).trans (by simp)
  refine ⟨∏ p∈U, l p,Finset.prod_ne_zero_iff.mpr (fun p _ => nz p),
    (totalDegree_finsetProd U l).trans ((Finset.sum_le_sum (fun p (_ : p∈U) => degree p)).trans_eq (by simp)),?_⟩
  intro p hp; rw [map_prod]; exact Finset.prod_eq_zero hp (by simp [l])

/-- Along any escaping sequence the same matrix works, at once, for all
anchors and for the selected centers in a uniformly bounded subset. -/
private theorem bounded_subfamily {d : ℕ} (A : ℕ → Configuration d)
    {β : Type*} (u : Ultrafilter β) (J : β → ℕ) (p : β → ℝ²) (hp : ∀ z, p z∈(A (J z)).U)
    (generic : AlgebraicIndependent (Base u J) (xy u p)) :
    ∃ B : ℕ → Finset ℝ², (∀ n, (B n).card ≤ 4*d*(4+2*d)) ∧ ∀ᶠ z in u, p z∈B (J z) := by
  classical
  choose q unequal outside realized using fun z => (A (J z)).partners (p z) (hp z)
  have nonempty (n : ℕ) : (A n).W.Nonempty := Finset.card_pos.mp (by have := (A n).size; omega)
  have frameFor (n : ℕ) (a : Pair) (ha : a∈(A n).W) := frameAt (A n).W (A n).S (A n).inside
    (A n).cap (A n).first (A n).second (A n).size a ha
  have usable (f : ℕ → Frame) (inW : ∀ n i, (f n).v i ∈ (A n).W) :
      MapsAt u J (fun n => (f n).forward) p q ∧ MapsAt u J (fun n => (f n).backward) q p := by
    apply frame_maps u J f p q generic (fun n => (A n).F) d (fun n => (A n).degree) outside
    intro z i
    obtain ⟨_,_,w,_,wf,wa,wb,_,lp,lq,_,_⟩ := realized z _ (inW (J z) i)
    exact ⟨w,wf,wa,wb,lp,lq⟩
  choose a ha using nonempty
  choose f _ inW using fun n => frameFor n (a n) (ha n)
  let M (n : ℕ) := (f n).backward
  obtain ⟨forward,backward⟩ := usable f inW
  have forCenters := maps_eventually u J backward
  let anchor (n : ℕ) (v : Pair) := ∃ s : ℝ, M n *ᵥ pt v.2=s • pt v.1
  have test (n : ℕ) : ∃ a∈(A n).W, anchor n a → ∀ v∈(A n).W, anchor n v := by
    by_cases all : ∀ v∈(A n).W, anchor n v
    · exact ⟨a n,ha n,fun _ => all⟩
    · push Not at all
      obtain ⟨b,hb,fail⟩ := all; exact ⟨b,hb,fun yes => (fail yes).elim⟩
  choose b hb detect using test
  choose f' starts inW' using fun n => frameFor n (b n) (hb n)
  have selected := maps_eventually u J (common_anchor u J f f' p q generic forward (usable f' inW').1 0)
  have anchors : ∀ᶠ z in u, ∀ v∈(A (J z)).W, anchor (J z) v := by
    filter_upwards [selected] with z hz
    obtain ⟨s,_,eq⟩ := hz
    exact detect (J z) ⟨s,by simpa only [starts] using eq⟩
  let works (n : ℕ) (v : ℝ²) := ∃ q' : ℝ², v ≠ q' ∧
    (∃ r : ℝ, r ≠ 0 ∧ M n *ᵥ pt q'=r • pt v) ∧ ∀ h∈(A n).W, Realized (A n).S (A n).F (v,q') h
  let B (n : ℕ) := if ∀ v∈(A n).W, anchor n v then (A n).U.filter (works n) else ∅
  refine ⟨B,?_,?_⟩
  · intro n; dsimp only [B]; split_ifs with h
    · exact Erdos101MatchedProjectivity.matched_bound (A n).S _ ((Finset.filter_subset ..).trans (A n).centers)
        (A n).cap (A n).F (A n).nonzero (A n).degree (A n).W (A n).inside (A n).distinct (M n) h
        (fun v hv => (Finset.mem_filter.mp hv).2)
    · simp
  · filter_upwards [anchors,forCenters] with z hz center
    rw [show B (J z)=(A (J z)).U.filter (works (J z)) from if_pos hz]
    exact Finset.mem_filter.mpr ⟨hp z,q z,unequal z,center,realized z⟩

/-- All first centers in a configuration realizing the same sufficiently
large matching lie on one nonzero curve. Its degree depends only on d. -/
theorem uniform_locus (d : ℕ) : ∃ D : ℕ, ∀ A : Configuration d, ∃ F : Poly,
    F ≠ 0 ∧ F.totalDegree ≤ D ∧ ∀ p∈A.U, eval (fun i => p i) F=0 := by
  classical
  by_contra! fail
  choose A avoid using fail
  let β := (n : ℕ) × ↥(A n).U
  let J (z : β) := z.1
  let p (z : β) : ℝ² := z.2.val
  have escape (j : ℕ) (F : Poly) (nz : F ≠ 0) (bound : F.totalDegree ≤ j) :
      ∃ z : β, J z=j ∧ eval (fun i => p z i) F ≠ 0 := by
    obtain ⟨v,hv,h⟩ := avoid j F nz bound
    exact ⟨⟨j,⟨v,hv⟩⟩,rfl,h⟩
  obtain ⟨u,_,miss,generic⟩ := independent_center J (fun z i => p z i) escape
  obtain ⟨B,size,belongs⟩ := bounded_subfamily A u J p (fun z => z.2.property) generic
  choose G nonzero degree hits using fun n => through_finite (B n)
  have outside := miss G (4*d*(4+2*d)) nonzero (fun n => (degree n).trans (size n))
  exact (Ultrafilter.eventually_not.mp outside) (belongs.mono (fun z h => hits (J z) (p z) h))

/-- Quantitative density is inherited from the sampled first centers.
The degree in the conclusion is independent of this density. -/
theorem fraction_locus (d : ℕ) : ∃ D : ℕ, ∀ C : ℕ, 0 < C →
    ∀ S T U : Finset ℝ², T ⊆ S → U ⊆ T → NonCollinearFor 5 (S : Set ℝ²) →
    ∀ F : Poly, F ≠ 0 → F.totalDegree ≤ d → (∀ p∈T, eval (fun i => p i) F ≠ 0) →
    S.card ≤ C*U.card → ∀ W : Finset Pair, W ⊆ S ×ˢ S → max 25 (4*d+1) ≤ W.card →
    Set.InjOn Prod.fst (W : Set Pair) → Set.InjOn Prod.snd (W : Set Pair) →
    (∀ p∈U, ∃ q∈T, p ≠ q ∧ ∀ v∈W, Realized S F (p,q) v) →
    ∃ G : Poly, G ≠ 0 ∧ G.totalDegree ≤ D ∧
      (1/(C : ℝ))*S.card ≤ (T.filter (fun p => eval (fun i => p i) G=0)).card := by
  obtain ⟨D,locus⟩ := uniform_locus d
  refine ⟨D,?_⟩
  intro C cp S T U ts ut cap F nz degree outside many W ws size first second partners
  have large : 4*d < (W.image Prod.fst).card := by rw [Finset.card_image_of_injOn first]; omega
  let A : Configuration d := ⟨S,U,W,F,nz,degree,ut.trans ts,cap,ws,first,second,
    (le_max_left ..).trans size,large,fun p hp => by
      obtain ⟨q,hq,different,r⟩ := partners p hp
      exact ⟨q,different,outside q hq,r⟩⟩
  obtain ⟨G,gn,gd,all⟩ := locus A
  have sub : U ⊆ T.filter (fun p => eval (fun i => p i) G=0) := fun p hp =>
    Finset.mem_filter.mpr ⟨ut hp,all p hp⟩
  have pos : (0 : ℝ) < C := by exact_mod_cast cp
  refine ⟨G,gn,gd,?_⟩
  calc
    (1/(C : ℝ))*S.card=(S.card : ℝ)/C := by ring
    _ ≤ U.card := (div_le_iff₀ pos).mpr (by exact_mod_cast (show S.card ≤ U.card*C by simpa [Nat.mul_comm] using many))
    _ ≤ _ := by exact_mod_cast Finset.card_le_card sub

end Erdos101FixedSecantLocus
end

namespace Erdos101ExternalSecantCapture

open EuclideanGeometry MvPolynomial
open scoped Classical

theorem main : OMA.R_Erdos101_erdos_101_R1_H1_R1.H2 := by
  intro d τ positive
  let m := max 25 (4*d+1)
  obtain ⟨D,fixed⟩ := Erdos101FixedSecantLocus.fraction_locus d
  obtain ⟨C,cp,N,sample⟩ := Erdos101RichSecantSamples.sample_from_four_lines d m (le_max_left ..) τ positive
  refine ⟨D,1/(C : ℝ),one_div_pos.mpr (by exact_mod_cast cp),N,?_⟩
  intro S T size ts cap F nz degree outside many rich
  obtain ⟨W,U,pattern,dense⟩ := sample S T size ts cap F degree outside many rich
  obtain ⟨ut,ws,card,_,first,second,partners⟩ := pattern
  exact fixed C cp S T U ts ut cap F nz degree outside dense W ws card.ge first second partners
end Erdos101ExternalSecantCapture

noncomputable section
namespace Erdos101TwoMarkedSecants

open EuclideanGeometry MvPolynomial
open OMA.R_Erdos101_erdos_101_R1
open scoped Classical

abbrev Line := AffineSubspace ℝ ℝ²
abbrev Poly := MvPolynomial (Fin 2) ℝ

def Two (S : Finset ℝ²) (F : Poly) (L : Line) : Prop :=
  2 ≤ (S.filter (fun p => p∈L ∧ eval (fun i => p i) F=0)).card

/-- Dense designated incidences have linearly many points of linear degree. -/
private theorem hot_marks {S : Finset ℝ²} {A : Finset Line} (mark : Line → ℝ²) {δ : ℝ}
    (positive : 0 < δ) (size : 0 < S.card) (four : ∀ L∈A, L∈linesWithPointsFor 4 (S : Set ℝ²))
    (onLine : ∀ L∈A, mark L∈S ∧ mark L∈L) (dense : δ*(S.card : ℝ)^2 ≤ A.card) :
    let T := S.filter (fun p => δ/2*S.card ≤ ((A.filter (fun L => mark L=p)).card : ℝ))
    δ/2*S.card ≤ (T.card : ℝ) := by
  let w (p : ℝ²) := ((A.filter (fun L => mark L=p)).card : ℝ)
  let T := S.filter (fun p => δ/2*S.card ≤ w p)
  change δ/2*S.card ≤ (T.card : ℝ)
  have npos : 0 < (S.card : ℝ) := by exact_mod_cast size
  have total : ∑ p∈S, w p=(A.card : ℝ) := by
    dsimp only [w]
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise
      (show Set.MapsTo mark (A : Set Line) (S : Set ℝ²) from fun L h => (onLine L h).1)).symm
  have each (p : ℝ²) (hp : p∈S) : w p ≤ S.card := by
    have sub : A.filter (fun L => mark L=p) ⊆ A.filter (fun L => p∈L) := by
      intro L h; obtain ⟨ha,hm⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨ha,hm ▸ (onLine L ha).2⟩
    have le := Finset.card_le_card sub
    have cap := pencil_bound four hp
    change 3*(A.filter (fun L => p∈L)).card ≤ S.card-1 at cap
    dsimp only [w]; exact_mod_cast (show (A.filter (fun L => mark L=p)).card ≤ S.card by omega)
  have hot : ∑ p∈T, w p ≤ (T.card : ℝ)*S.card := calc
    _ ≤ ∑ _p∈T, (S.card : ℝ) := Finset.sum_le_sum (fun p hp => each p (Finset.mem_filter.mp hp).1)
    _ = _ := by simp
  have cold : ∑ p∈S \ T, w p ≤ (S.card : ℝ)*(δ/2*S.card) := calc
    _ ≤ ∑ _p∈S \ T, δ/2*(S.card : ℝ) := Finset.sum_le_sum (fun p hp =>
      le_of_not_ge (fun h => (Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hp).1,h⟩)))
    _ = ((S \ T).card : ℝ)*(δ/2*S.card) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
      (Finset.card_le_card (Finset.sdiff_subset (s := S) (t := T)))) (by positivity)
  have sum := Finset.sum_sdiff (Finset.filter_subset _ S : T ⊆ S) (f := w)
  rw [total] at sum
  apply le_of_mul_le_mul_right (a := (S.card : ℝ)) _ npos
  nlinarith only [dense,hot,cold,sum]

theorem capture_mark (d : ℕ) (δ : ℝ) (positive : 0 < δ) :
    ∃ D : ℕ, ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, ∀ (S : Finset ℝ²) (A : Finset Line) (F : Poly) (mark : Line → ℝ²),
    N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) → F ≠ 0 → F.totalDegree ≤ d →
    (∀ L∈A, L∈linesWithPointsFor 4 (S : Set ℝ²) ∧ Two S F L) → (∀ L∈A, mark L∈S ∧ mark L∈L) →
    δ*(S.card : ℝ)^2 ≤ A.card → ∃ G : Poly, G ≠ 0 ∧ G.totalDegree ≤ D ∧ ∃ B ⊆ A,
      η*(S.card : ℝ)^2 ≤ B.card ∧ ∀ L∈B, eval (fun i => mark L i) G=0 := by
  let τ := δ/4
  have tp : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨e,c,cp,N,external⟩ := Erdos101ExternalSecantCapture.main d τ tp
  refine ⟨max d e,min τ c*(δ/2),mul_pos (lt_min tp cp) (half_pos positive),max 1 N,?_⟩
  intro S A F mark size cap nonzero degree lines onLine dense
  let row (p : ℝ²) := A.filter (fun L => mark L=p)
  let T := S.filter (fun p => δ/2*S.card ≤ ((row p).card : ℝ))
  have tsub : T ⊆ S := Finset.filter_subset ..
  have hot : δ/2*(S.card : ℝ) ≤ T.card := hot_marks mark positive (by omega) (fun L h => (lines L h).1) onLine dense
  have finish (G : Poly) (gn : G ≠ 0) (gd : G.totalDegree ≤ max d e) (R : Finset ℝ²) (inside : R ⊆ T)
      (many : min τ c*(S.card : ℝ) ≤ R.card) (van : ∀ p∈R, eval (fun i => p i) G=0) :
      ∃ G : Poly, G ≠ 0 ∧ G.totalDegree ≤ max d e ∧ ∃ B ⊆ A,
        min τ c*(δ/2)*(S.card : ℝ)^2 ≤ B.card ∧ ∀ L∈B, eval (fun i => mark L i) G=0 := by
    let B := A.filter (fun L => mark L ∈ R)
    have total : ∑ p∈R, ((row p).card : ℝ)=(B.card : ℝ) := by
      dsimp only [row,B]; exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter A R mark
    refine ⟨G,gn,gd,B,Finset.filter_subset ..,?_,fun L h => van _ (Finset.mem_filter.mp h).2⟩
    calc
      _ = (min τ c*S.card)*(δ/2*S.card) := by ring
      _ ≤ (R.card : ℝ)*(δ/2*S.card) := mul_le_mul_of_nonneg_right many (by positivity)
      _ = ∑ _p∈R, δ/2*(S.card : ℝ) := by simp
      _ ≤ ∑ p∈R, ((row p).card : ℝ) := Finset.sum_le_sum (fun p hp => (Finset.mem_filter.mp (inside hp)).2)
      _ = _ := total
  let onC := T.filter (fun p => eval (fun i => p i) F=0)
  let offC := T.filter (fun p => eval (fun i => p i) F ≠ 0)
  by_cases enough : τ*(S.card : ℝ) ≤ onC.card
  · exact finish F nonzero (degree.trans (le_max_left ..)) onC (Finset.filter_subset ..)
      ((mul_le_mul_of_nonneg_right (min_le_left ..) (Nat.cast_nonneg _)).trans enough)
      (fun _ h => (Finset.mem_filter.mp h).2)
  have split : (onC.card : ℝ)+offC.card=T.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := T) (fun p => eval (fun i => p i) F=0)
  have large : τ*(S.card : ℝ) ≤ offC.card := by dsimp [τ] at enough ⊢; linarith
  have offSub : offC ⊆ T := Finset.filter_subset ..
  obtain ⟨G,gn,gd,many⟩ := external S offC ((le_max_right ..).trans size) (offSub.trans tsub) cap F nonzero degree
    (fun _ h => (Finset.mem_filter.mp h).2) large (by
      intro p hp
      have hotp := (Finset.mem_filter.mp (offSub hp)).2
      refine ⟨row p,(mul_le_mul_of_nonneg_right (show τ ≤ δ/2 by dsimp [τ]; linarith) (Nat.cast_nonneg _)).trans hotp,?_⟩
      intro L h; obtain ⟨inA,atP⟩ := Finset.mem_filter.mp h
      exact ⟨atP ▸ (onLine L inA).2,lines L inA⟩)
  exact finish G gn (gd.trans (le_max_right ..)) _ ((Finset.filter_subset ..).trans offSub)
    ((mul_le_mul_of_nonneg_right (min_le_right ..) (Nat.cast_nonneg _)).trans many)
    (fun _ h => (Finset.mem_filter.mp h).2)

private theorem other_two (S : Finset ℝ²) (A : Finset Line) (F : Poly)
    (lines : ∀ L∈A, L∈linesWithPointsFor 4 (S : Set ℝ²) ∧ Two S F L) :
    ∃ mark : Fin 2 → Line → ℝ², (∀ i L, L∈A → mark i L∈S ∧ mark i L∈L) ∧
      ∀ L∈A, ∀ p∈S, p∈L → eval (fun i => p i) F=0 ∨ ∃ i, mark i L=p := by
  have pick (L : Line) (hL : L∈A) : ∃ x : Fin 2 → ℝ², (∀ i, x i∈S ∧ x i∈L) ∧
      ∀ p∈S, p∈L → eval (fun i => p i) F=0 ∨ ∃ i, x i=p := by
    let all := S.filter (fun p => p∈L)
    obtain ⟨B,hB,bc⟩ := Finset.exists_subset_card_eq (lines L hL).2
    have sub : B ⊆ all := fun p hp => Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (hB hp)).1,(Finset.mem_filter.mp (hB hp)).2.1⟩
    have count : (all \ B).card=2 := by
      rw [Finset.card_sdiff_of_subset sub,bc,show all.card=4 from four_points (lines L hL).1]
    let e := (Finset.equivFinOfCardEq (s := all \ B) count).symm
    refine ⟨fun i => (e i).val,fun i => Finset.mem_filter.mp (Finset.mem_sdiff.mp (e i).property).1,?_⟩
    intro p hp pl
    by_cases hb : p∈B
    · exact Or.inl (Finset.mem_filter.mp (hB hb)).2.2
    · let v : ↥(all \ B) := ⟨p,Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hp,pl⟩,hb⟩⟩
      exact Or.inr ⟨e.symm v,congrArg Subtype.val (e.apply_symm_apply v)⟩
  let mark (i : Fin 2) (L : Line) := if h : L∈A then (pick L h).choose i else 0
  refine ⟨mark,fun i L h => by simpa only [mark,dif_pos h] using (pick L h).choose_spec.1 i,?_⟩
  intro L h p hp pl; simpa only [mark,dif_pos h] using (pick L h).choose_spec.2 p hp pl

/-- If a curve contains two points on every line of a dense four-point
family, a bounded-degree curve contains all four points on a dense subfamily. -/
theorem all_four (d : ℕ) (δ : ℝ) (positive : 0 < δ) :
    ∃ D : ℕ, ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, ∀ (S : Finset ℝ²) (A : Finset Line) (F : Poly),
    N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) → F ≠ 0 → F.totalDegree ≤ d →
    (∀ L∈A, L∈linesWithPointsFor 4 (S : Set ℝ²) ∧ Two S F L) → δ*(S.card : ℝ)^2 ≤ A.card →
    ∃ G : Poly, G ≠ 0 ∧ G.totalDegree ≤ D ∧ ∃ B ⊆ A, η*(S.card : ℝ)^2 ≤ B.card ∧
      ∀ L∈B, ∀ p∈S, p∈L → eval (fun i => p i) G=0 := by
  obtain ⟨e,γ,gp,N,first⟩ := capture_mark d δ positive
  obtain ⟨f,η,ep,M,second⟩ := capture_mark d γ gp
  refine ⟨d+e+f,η,ep,max N M,?_⟩
  intro S A F size cap nz deg lines dense
  obtain ⟨mark,ok,cover⟩ := other_two S A F lines
  obtain ⟨G,gn,gd,B,ba,big,atG⟩ := first S A F (mark 0) ((le_max_left ..).trans size)
    cap nz deg lines (ok 0) dense
  obtain ⟨H,hn,hd,C,cb,more,atH⟩ := second S B F (mark 1) ((le_max_right ..).trans size)
    cap nz deg (fun L h => lines L (ba h)) (fun L h => ok 1 L (ba h)) big
  refine ⟨F*G*H,mul_ne_zero (mul_ne_zero nz gn) hn,(totalDegree_mul ..).trans
    (Nat.add_le_add ((totalDegree_mul ..).trans (Nat.add_le_add deg gd)) hd),C,cb.trans ba,more,?_⟩
  intro L h p hp pl
  rcases cover L (ba (cb h)) p hp pl with hit | ⟨i,eq⟩
  · simp [hit]
  · fin_cases i
    · rw [← eq]; simp [atG L (cb h)]
    · rw [← eq]; simp [atH L h]

/-- For two already marked points, only the all-points-on-a-curve case
of the conjecture is needed to get the little-o incidence estimate. -/
theorem sparse_if_bounded_curve (bounded : OMA.R_Erdos101_erdos_101_R1.H2) (d : ℕ) (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ (S : Finset ℝ²) (A : Finset Line) (F : Poly), N ≤ S.card →
    NonCollinearFor 5 (S : Set ℝ²) → F ≠ 0 → F.totalDegree ≤ d →
    (∀ L∈A, L∈linesWithPointsFor 4 (S : Set ℝ²) ∧ Two S F L) → (A.card : ℝ) < ε*(S.card : ℝ)^2 := by
  obtain ⟨D,η,ep,N,concentrate⟩ := all_four d ε positive
  obtain ⟨M,upper⟩ := all_degrees_bound bounded D (η/2) (half_pos ep)
  refine ⟨max 1 (max N M),?_⟩
  intro S A F size cap nz deg lines
  by_contra! dense
  have large := (le_max_right 1 (max N M)).trans size
  obtain ⟨G,gn,gd,B,ba,many,hits⟩ := concentrate S A F ((le_max_left ..).trans large) cap nz deg lines dense
  let T := S.filter (fun p => eval (fun i => p i) G=0)
  have sub : T ⊆ S := Finset.filter_subset ..
  have transferred : B ⊆ (four_lines_finite T).toFinset := by
    intro L hl; apply (four_lines_finite T).mem_toFinset.mpr
    exact mem_after_restriction sub (lines L (ba hl)).1 (fun p hp pl => Finset.mem_filter.mpr ⟨hp,hits L hl p hp pl⟩)
  have small := upper S.card ((le_max_right ..).trans large) T (Finset.card_le_card sub) (cap.subset sub)
    G gn gd (fun _ h => (Finset.mem_filter.mp h).2)
  rw [Set.ncard_eq_toFinset_card _ (four_lines_finite T)] at small
  have npos : 0 < (S.card : ℝ) := by exact_mod_cast (show 0 < S.card by omega)
  exact (not_le_of_gt (mul_lt_mul_of_pos_right (half_lt_self ep) (sq_pos_of_pos npos)))
    (many.trans ((Nat.cast_le.mpr (Finset.card_le_card transferred)).trans small))

end Erdos101TwoMarkedSecants
end

noncomputable section
namespace Erdos101PairCapture

open EuclideanGeometry MvPolynomial Asymptotics Filter
open OMA.R_Erdos101_erdos_101_R1 Erdos101TwoMarkedSecants
open scoped Classical

/-- At each fixed positive four-line density, detect two endpoints on
a common bounded-degree curve for a positive proportion of all pairs. -/
def PairCapture : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ d : ℕ, ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, ∀ S : Finset ℝ²,
    N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
    δ*(S.card : ℝ)^2 ≤ (linesWithPointsFor 4 (S : Set ℝ²)).ncard →
    ∃ F : Poly, F ≠ 0 ∧ F.totalDegree ≤ d ∧ ∃ A : Finset Line,
      η*(S.card : ℝ)^2 ≤ A.card ∧ ∀ L∈A, L∈linesWithPointsFor 4 (S : Set ℝ²) ∧ Two S F L

theorem full_of_pair_capture (detect : PairCapture) (bounded : OMA.R_Erdos101_erdos_101_R1.H2) :
    type_of% @Erdos101.erdos_101 := by
  apply IsLittleO.of_bound
  intro ε positive
  obtain ⟨d,η,ep,N,extract⟩ := detect ε positive
  obtain ⟨M,sparse⟩ := sparse_if_bounded_curve bounded d η ep
  filter_upwards [eventually_ge_atTop (max N M)] with n size
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (sq_nonneg _)]
  have max_bound : Erdos101.numLinesWithFourPointMax n ≤ ⌊ε*(n : ℝ)^2⌋₊ := by
    apply csSup_le'
    rintro _ ⟨U,uc,finite,cap,rfl⟩
    let S := finite.toFinset
    have he : (S : Set ℝ²)=U := finite.coe_toFinset
    have card : S.card=n := (Set.ncard_eq_toFinset_card U finite).symm.trans uc
    apply Nat.le_floor
    by_contra! many
    obtain ⟨F,fn,fd,A,count,lines⟩ := extract S (card ▸ (le_max_left ..).trans size) (he ▸ cap)
      (by simpa only [he,card] using many.le)
    exact (not_lt_of_ge count) (sparse S A F (card ▸ (le_max_right ..).trans size) (he ▸ cap) fn fd lines)
  exact (Nat.cast_le.mpr max_bound).trans (Nat.floor_le (mul_nonneg positive.le (sq_nonneg _)))

/-- The marked-point inverse problem needs only its unmarked hypothesis,
now that external center capture is proved. -/
theorem marked_iff_unmarked : OMA.R_Erdos101_erdos_101_R1.H1 ↔ OMA.R_Erdos101_erdos_101_R1_H1_R1.H1 :=
  ⟨fun h => (OMA.R_Erdos101_erdos_101_R1_H1_R1.cases_of_marked_capture h).1,
    fun h => OMA.R_Erdos101_erdos_101_R1_H1_R1.main h Erdos101ExternalSecantCapture.main⟩

end Erdos101PairCapture
end

noncomputable section
namespace Erdos101CubicGrid

open EuclideanGeometry MvPolynomial
open scoped Classical

abbrev PlanePoly := MvPolynomial (Fin 2) ℝ

abbrev atPoint (p : ℝ²) : PlanePoly →+* ℝ := eval (fun i => p i)

lemma irreducible_linear {L : PlanePoly} (hd : L.totalDegree = 1) :
    Irreducible L := by
  apply irreducible_of_totalDegree_eq_one hd
  intro x hx
  apply isUnit_iff_ne_zero.mpr
  rintro rfl
  have hL : L = 0 := by
    ext i
    simpa using hx i
  simp [hL] at hd

lemma section_dvd {ι : Type*} [DecidableEq ι] (p : ι ↪ ℝ²) (s : Finset ι)
    (L F : PlanePoly) (hd : L.totalDegree = 1) (hcard : F.totalDegree < s.card)
    (hL : ∀ a ∈ s, atPoint (p a) L = 0) (hF : ∀ a ∈ s, atPoint (p a) F = 0) :
    L ∣ F := by
  by_contra hn
  have h := Erdos101CurveIntersections.card_common_zeros_le (s.map p) L F
    (irreducible_linear hd) hn (by simpa using hL) (by simpa using hF)
  simp [hd] at h
  omega

lemma factor_degree {F L : PlanePoly} {d : ℕ} (hd : F.totalDegree ≤ d+1)
    (hL : L.totalDegree = 1) (hdiv : L ∣ F) :
    ∃ Q, F = L*Q ∧ Q.totalDegree ≤ d := by
  obtain ⟨Q,hQ⟩ := hdiv
  refine ⟨Q,hQ,?_⟩
  by_cases hq : Q = 0
  · simp [hq]
  have hl : L ≠ 0 := (irreducible_linear hL).ne_zero
  rw [hQ,totalDegree_mul_of_isDomain hl hq,hL] at hd
  omega

/-- Three full rows of a nine-point grid, each a line. The union of the three columns
is encoded by a polynomial of degree at most three. A test point on the first row
outside the columns fixes the member of the cubic pencil. -/
theorem chasles {ι : Type*} [DecidableEq ι] (p : ι ↪ ℝ²) (row : Fin 3 → Finset ι)
    (R : Fin 3 → PlanePoly) (G F : PlanePoly) (miss extra : ι)
    (hr : ∀ i, (row i).card = 3) (hrd : ∀ i, (R i).totalDegree = 1)
    (hrow : ∀ i a, a ∈ row i → atPoint (p a) (R i) = 0)
    (hoff : ∀ i j, i ≠ j → ∀ a ∈ row j, atPoint (p a) (R i) ≠ 0)
    (hm : miss ∈ row 2) (he : extra ∉ row 0) (heR : atPoint (p extra) (R 0) = 0)
    (heG : atPoint (p extra) G ≠ 0)
    (hG : ∀ i a, a ∈ row i → atPoint (p a) G = 0)
    (hGd : G.totalDegree ≤ 3) (hFd : F.totalDegree ≤ 3)
    (hF : ∀ i a, a ∈ row i → a ≠ miss → atPoint (p a) F = 0) :
    atPoint (p miss) F = 0 := by
  let c := atPoint (p extra) F / atPoint (p extra) G
  let H := F - C c * G
  have hH : H.totalDegree ≤ 3 :=
    (totalDegree_sub _ _).trans (max_le hFd ((totalDegree_mul _ _).trans (by simpa using hGd)))
  have hHe : atPoint (p extra) H = 0 := by simp [H,c,heG,atPoint]
  have hHr (i) (a) (ha : a ∈ row i) (ham : a ≠ miss) : atPoint (p a) H = 0 := by
    simp only [H,map_sub,map_mul,hG i a ha,hF i a ha ham,mul_zero,sub_zero]
  have hnm (i : Fin 3) (hi : i ≠ 2) (a) (ha : a ∈ row i) : a ≠ miss := by
    rintro rfl
    exact hoff i 2 hi _ hm (hrow i _ ha)
  obtain ⟨Q,hQ,hQd⟩ := factor_degree (d := 2) hH (hrd 0)
    (section_dvd p (insert extra (row 0)) _ _ (hrd 0) (by simp [he,hr]; omega)
      (by simpa using And.intro heR (hrow 0))
      (by simpa using And.intro hHe (fun a ha => hHr 0 a ha (hnm 0 (by decide) a ha))))
  have hQr (i : Fin 3) (hi : (0 : Fin 3) ≠ i) (a) (ha : a ∈ row i) (ham : a ≠ miss) :
      atPoint (p a) Q = 0 := by
    have hz := hHr i a ha ham
    rw [hQ,map_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left (hoff 0 i hi a ha)
  obtain ⟨T,hT,hTd⟩ := factor_degree (d := 1) hQd (hrd 1)
    (section_dvd p (row 1) _ _ (hrd 1) (by rw [hr]; omega) (hrow 1)
      (fun a ha => hQr 1 (by decide) a ha (hnm 1 (by decide) a ha)))
  have hdiv := section_dvd p ((row 2).erase miss) (R 2) T (hrd 2)
    (by rw [Finset.card_erase_of_mem hm,hr]; omega)
    (fun a ha => hrow 2 a (Finset.mem_erase.mp ha).2) (by
      intro a ha
      obtain ⟨ham,hmem⟩ := Finset.mem_erase.mp ha
      have hz := hQr 2 (by decide) a hmem ham
      rw [hT,map_mul] at hz
      exact (mul_eq_zero.mp hz).resolve_left (hoff 1 2 (by decide) a hmem))
  obtain ⟨U,hU⟩ := hdiv
  have hz : atPoint (p miss) H = 0 := by
    rw [hQ,hT,hU]
    simp [atPoint,show eval (fun i => p miss i) (R 2) = 0 from hrow 2 miss hm]
  simpa only [H,map_sub,map_mul,hG 2 miss hm,mul_zero,sub_zero] using hz

lemma linear_through (s : Finset ℝ²) (hs : Collinear ℝ (s : Set ℝ²)) :
    ∃ F : PlanePoly, F ≠ 0 ∧ F.totalDegree ≤ 1 ∧ ∀ p ∈ s, atPoint p F = 0 := by
  obtain ⟨o,v,h⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp hs
  by_cases hv : v 1 = 0
  · let F : PlanePoly := X 1 - C (o 1)
    have htest : atPoint !₂[0,o 1+1] F = 1 := by simp [F,atPoint]
    refine ⟨F,by intro he; simp [he] at htest,
      (totalDegree_sub _ _).trans (by simp),?_⟩
    intro p hp
    obtain ⟨t,rfl⟩ := h p hp
    simp [F,atPoint,hv]
  · let m := v 0 / v 1
    let b := o 0 - m * o 1
    let F : PlanePoly := X 0 - (C m * X 1 + C b)
    have htest : atPoint !₂[b+1,0] F = 1 := by simp [F,atPoint]
    have hmx : (C m * X (1 : Fin 2) : PlanePoly).totalDegree ≤ 1 :=
      (totalDegree_mul _ _).trans (by simp)
    refine ⟨F,by intro he; simp [he] at htest,
      (totalDegree_sub _ _).trans (max_le (by simp)
        ((totalDegree_add _ _).trans (max_le hmx (by simp)))),?_⟩
    intro p hp
    obtain ⟨t,rfl⟩ := h p hp
    simp [F,atPoint,b,m]
    field_simp [hv]
    ring

end Erdos101CubicGrid
end

noncomputable section
namespace Erdos101AdditiveGrid

open EuclideanGeometry MvPolynomial
open Erdos101CubicGrid (PlanePoly atPoint chasles irreducible_linear section_dvd factor_degree)
open scoped Classical

abbrev Label := Fin 19
abbrev Cell := Fin 5 × Fin 5

/-- Labels 0–4 are the rows, 5–9 the columns and 10–18 the sums. -/
def cell (ij : Cell) : Finset Label :=
  let i := ij.1.val
  let j := ij.2.val
  {⟨i, by have := ij.1.isLt; omega⟩, ⟨5+j, by have := ij.2.isLt; omega⟩,
    ⟨10+i+j, by have := ij.1.isLt; have := ij.2.isLt; omega⟩}

structure Grid where
  point : Label ↪ ℝ²
  line : Cell → PlanePoly
  fourth : Cell → ℝ²
  degree : ∀ ij, (line ij).totalDegree = 1
  incident : ∀ ij a, atPoint (point a) (line ij) = 0 ↔ a ∈ cell ij
  fourth_on : ∀ ij, atPoint (fourth ij) (line ij) = 0
  fourth_fresh : ∀ ij a, fourth ij ≠ point a

private def hits (u : Fin 3 → Cell) := cell (u 0) ∪ cell (u 1) ∪ cell (u 2)

private def product (X : Grid) (u : Fin 3 → Cell) := X.line (u 0) * X.line (u 1) * X.line (u 2)

private lemma product_at (X : Grid) (u : Fin 3 → Cell) (a : Label) :
    atPoint (X.point a) (product X u) = 0 ↔ a ∈ hits u := by
  simp only [product,map_mul,mul_eq_zero,X.incident,hits,Finset.mem_union]

private lemma product_degree (X : Grid) (u : Fin 3 → Cell) : (product X u).totalDegree ≤ 3 := by
  exact (totalDegree_mul _ _).trans ((Nat.add_le_add (totalDegree_mul _ _) le_rfl).trans
    (by simp [X.degree]))

private def withTest (X : Grid) (v : Cell) : Option Label ↪ ℝ² where
  toFun := fun a => a.elim (X.fourth v) X.point
  inj' := by
    intro a b h
    cases a <;> cases b
    · rfl
    · exact False.elim (X.fourth_fresh v _ h)
    · exact False.elim (X.fourth_fresh v _ h.symm)
    · exact congrArg some (X.point.injective h)

private abbrev someLabel : Label ↪ Option Label := ⟨some,Option.some_injective _⟩

/-- Three distinct intersections of a line with a union of three other
lines exhaust its intersections with this cubic. -/
private lemma fourth_off (X : Grid) (v : Cell) (u : Fin 3 → Cell)
    (hc : (cell v ∩ hits u).card = 3)
    (hn : ∀ k, ¬ cell v ⊆ cell (u k)) : atPoint (X.fourth v) (product X u) ≠ 0 := by
  intro hz
  let row := cell v ∩ hits u
  let points := insert (X.fourth v) (row.map X.point)
  have fresh : X.fourth v ∉ row.map X.point := by
    rintro h
    obtain ⟨a,_,he⟩ := Finset.mem_map.mp h
    exact X.fourth_fresh v a he.symm
  have card : points.card = 4 := by simp [points,fresh,row,hc]
  have divides := section_dvd (Function.Embedding.refl ℝ²) points (X.line v) (product X u)
    (X.degree v) (by have := product_degree X u; omega)
    (by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | h
      · exact X.fourth_on v
      · obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp h
        exact (X.incident v a).2 (Finset.mem_inter.mp ha).1)
    (by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | h
      · exact hz
      · obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp h
        exact (product_at X u a).2 (Finset.mem_inter.mp ha).2)
  have prime := (irreducible_linear (X.degree v)).prime
  have bad (k : Fin 3) : ¬ X.line v ∣ X.line (u k) := by
    rintro ⟨Q,hQ⟩
    apply hn k
    intro a ha
    apply (X.incident _ _).1
    rw [hQ,map_mul,(X.incident v a).2 ha,zero_mul]
  rcases prime.dvd_mul.mp divides with h | h
  · exact (prime.dvd_mul.mp h).elim (bad 0) (bad 1)
  · exact bad 2 h

private structure Step where
  red : Fin 3 → Cell
  blue : Fin 3 → Cell
  miss : Label

private def Step.row (s : Step) (i : Fin 3) := cell (s.red i) ∩ hits s.blue

private def Step.Valid (s : Step) (known : Finset Label) : Prop :=
  (∀ i, (s.row i).card = 3) ∧
  (∀ i j : Fin 3, i ≠ j → Disjoint (cell (s.red i)) (s.row j)) ∧
  s.miss ∈ s.row 2 ∧ (∀ k, ¬ cell (s.red 0) ⊆ cell (s.blue k)) ∧
  (∀ i, (s.row i).erase s.miss ⊆ known)

private instance (s : Step) (known : Finset Label) : Decidable (s.Valid known) := by
  unfold Step.Valid
  infer_instance

private lemma Step.extend (s : Step) (X : Grid) (F : PlanePoly) (hd : F.totalDegree ≤ 3)
    (known : Finset Label) (h : s.Valid known) (hz : ∀ a ∈ known, atPoint (X.point a) F = 0) :
    ∀ a ∈ insert s.miss known, atPoint (X.point a) F = 0 := by
  obtain ⟨hcard,hdj,hm,hdist,hknown⟩ := h
  rw [Finset.forall_mem_insert]
  refine ⟨?_,hz⟩
  apply chasles (withTest X (s.red 0)) (fun i => (s.row i).map someLabel)
    (fun i => X.line (s.red i)) (product X s.blue) F (some s.miss) none
  · simpa using hcard
  · exact fun i => X.degree _
  · intro i a ha
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
    exact (X.incident _ _).2 (Finset.mem_inter.mp hx).1
  · intro i j hij a ha
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
    exact fun hh => Finset.disjoint_left.mp (hdj i j hij) ((X.incident _ _).1 hh) hx
  · exact Finset.mem_map.mpr ⟨_,hm,rfl⟩
  · rintro hh
    obtain ⟨_,_,he⟩ := Finset.mem_map.mp hh
    cases he
  · exact X.fourth_on _
  · exact fourth_off X _ _ (hcard 0) hdist
  · intro i a ha
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
    exact (product_at ..).2 (Finset.mem_inter.mp hx).2
  · exact product_degree .. 
  · exact hd
  · intro i a ha ham
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
    exact hz _ (hknown i (Finset.mem_erase.mpr ⟨fun hh => ham (congrArg some hh),hx⟩))

private def firstRed : Fin 3 → Cell := ![(0,1),(1,2),(2,0)]
private def firstBlue : Fin 3 → Cell := ![(0,2),(1,0),(2,1)]
private def seed : Finset Label := insert 3 (hits firstRed ∩ hits firstBlue)

private lemma seed_cubic (X : Grid) :
    ∃ F : PlanePoly, F ≠ 0 ∧ F.totalDegree ≤ 3 ∧ ∀ a ∈ seed, atPoint (X.point a) F = 0 := by
  let R := product X firstRed
  let B := product X firstBlue
  let r := atPoint (X.point 3) R
  let b := atPoint (X.point 3) B
  let F := C b * R - C r * B
  have hrd : R.totalDegree ≤ 3 := product_degree ..
  have hbd : B.totalDegree ≤ 3 := product_degree ..
  have hrat : r ≠ 0 := fun h => (by decide : (3 : Label) ∉ hits firstRed) ((product_at ..).1 h)
  let test := X.fourth (firstRed 0)
  have htestR : atPoint test R = 0 := by
    change atPoint test (X.line (firstRed 0) * _ * _) = 0
    simp only [map_mul,X.fourth_on,test,zero_mul]
  have htestB : atPoint test B ≠ 0 := fourth_off X _ _ (by decide) (by decide)
  have hcalc (p : ℝ²) : atPoint p F = b * atPoint p R - r * atPoint p B := by simp [F,atPoint]
  refine ⟨F,?_,(totalDegree_sub _ _).trans (max_le
    ((totalDegree_mul _ _).trans (by simpa using hrd))
    ((totalDegree_mul _ _).trans (by simpa using hbd))),?_⟩
  · intro he
    have hh : atPoint test F = 0 := by simp [he]
    rw [hcalc,htestR] at hh
    exact (mul_ne_zero hrat htestB) (by simpa using hh)
  · simp only [seed,Finset.forall_mem_insert]
    refine ⟨by rw [hcalc]; change b*r-r*b = 0; ring,?_⟩
    intro a ha
    obtain ⟨hr,hb⟩ := Finset.mem_inter.mp ha
    rw [hcalc,(product_at ..).2 hr,(product_at ..).2 hb]
    ring

private def steps : List Step :=
  [⟨![(1,1),(3,0),(2,2)], ![(1,2),(2,0),(3,1)], 14⟩,
   ⟨![(0,2),(2,1),(1,3)], ![(0,3),(1,1),(2,2)], 8⟩,
   ⟨![(1,2),(3,1),(2,3)], ![(1,3),(2,1),(3,2)], 15⟩,
   ⟨![(2,1),(3,2),(4,0)], ![(2,2),(3,0),(4,1)], 4⟩,
   ⟨![(0,3),(2,2),(1,4)], ![(0,4),(1,2),(2,3)], 9⟩,
   ⟨![(2,2),(4,1),(3,3)], ![(2,3),(3,1),(4,2)], 16⟩]

private def validate (known : Finset Label) : List Step → Bool
  | [] => true
  | s :: ss => decide (s.Valid known) && validate (insert s.miss known) ss

private def endSet (known : Finset Label) : List Step → Finset Label
  | [] => known
  | s :: ss => endSet (insert s.miss known) ss

private lemma propagate (X : Grid) (F : PlanePoly) (hd : F.totalDegree ≤ 3)
    (known : Finset Label) (ss : List Step) (h : validate known ss = true)
    (hz : ∀ a ∈ known, atPoint (X.point a) F = 0) :
    ∀ a ∈ endSet known ss, atPoint (X.point a) F = 0 := by
  induction ss generalizing known with
  | nil => exact hz
  | cons s ss ih =>
    obtain ⟨hv,ht⟩ := Bool.and_eq_true_iff.mp h
    exact ih _ ht (s.extend X F hd _ (of_decide_eq_true hv) hz)

private def covered : Finset Label := {0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16}

private lemma cubic (X : Grid) :
    ∃ F : PlanePoly, F ≠ 0 ∧ F.totalDegree ≤ 3 ∧ ∀ a ∈ covered, atPoint (X.point a) F = 0 := by
  obtain ⟨F,hn,hd,hz⟩ := seed_cubic X
  have hv : validate seed steps = true := by decide
  have he : covered = endSet seed steps := by decide
  exact ⟨F,hn,hd,he ▸ propagate X F hd seed steps hv hz⟩

private def tripleCell (i : Fin 5) : Cell := (i, i+2)

private def triple (i : Fin 5) := cell (tripleCell i)

private lemma clean_triple (bad : Finset Label) (hbad : bad.card ≤ 4) :
    ∃ i, Disjoint (triple i) bad := by
  by_contra! h
  choose a ha using fun i => Finset.not_disjoint_iff.mp (h i)
  have hd : ∀ i j : Fin 5, i ≠ j → Disjoint (triple i) (triple j) := by decide
  have hi : Function.Injective a := by
    intro i j he
    by_contra hne
    exact Finset.disjoint_left.mp (hd i j hne) (ha i).1 (he ▸ (ha j).1)
  have hcount := Finset.card_le_card_of_injOn (s := Finset.univ) (t := bad) a
    (fun i _ => (ha i).2) hi.injOn
  simp at hcount
  omega

private def zeros (X : Grid) (F : PlanePoly) :=
  Finset.univ.filter (fun a => atPoint (X.point a) F = 0)

private lemma linear_bound (X : Grid)
    (hn : NonCollinearFor 5 ((Finset.univ.map X.point : Finset ℝ²) : Set ℝ²))
    (F : PlanePoly) (hF : F ≠ 0) (hd : F.totalDegree ≤ 1) : (zeros X F).card ≤ 4 := by
  have he : (zeros X F).map X.point =
      (Finset.univ.map X.point).filter (fun p => atPoint p F = 0) := by
    ext p
    simp [zeros]
    aesop
  have h := Erdos101SecantComponents.linear_component_card hF hd hn
  change ((Finset.univ.map X.point).filter (fun p => atPoint p F = 0)).card ≤ 4 at h
  simpa only [← he,Finset.card_map] using h

private lemma rigid_cubic (X : Grid)
    (hn : NonCollinearFor 5 ((Finset.univ.map X.point : Finset ℝ²) : Set ℝ²))
    (F : PlanePoly) (hF : F ≠ 0) (hd : F.totalDegree ≤ 3)
    (hz : ∀ a ∈ covered, atPoint (X.point a) F = 0) :
    Irreducible F ∧ F.totalDegree = 3 := by
  have ht : ∀ i, (triple i).card = 3 := by decide
  have hc : ∀ i, triple i ⊆ covered := by decide
  have hsection (i : Fin 5) (P : PlanePoly) (hp : P.totalDegree ≤ 2)
      (hzero : ∀ a ∈ triple i, atPoint (X.point a) P = 0) : X.line (tripleCell i) ∣ P :=
    section_dvd X.point (triple i) _ _ (X.degree _) (by rw [ht]; omega)
      (fun a ha => (X.incident _ _).2 ha) hzero
  have hfree (L : PlanePoly) (hl : L.totalDegree = 1) : ¬ L ∣ F := by
    intro hdiv
    have hl0 := (irreducible_linear hl).ne_zero
    obtain ⟨Q,hQ,hQd⟩ := factor_degree (d := 2) hd hl hdiv
    have hQ0 : Q ≠ 0 := by rintro rfl; simp [hQ] at hF
    have hsmall := linear_bound X hn L hl0 hl.le
    obtain ⟨i,hi⟩ := clean_triple (zeros X L) hsmall
    have hw : X.line (tripleCell i) ∣ Q := hsection i Q hQd fun a ha => by
      have hnot : atPoint (X.point a) L ≠ 0 := fun h =>
        Finset.disjoint_left.mp hi ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      have haF := hz a (hc i ha)
      rw [hQ,map_mul] at haF
      exact (mul_eq_zero.mp haF).resolve_left hnot
    obtain ⟨M,hM,hMd⟩ := factor_degree (d := 1) hQd (X.degree _) hw
    have hM0 : M ≠ 0 := by rintro rfl; simp [hM] at hQ0
    have hsub : covered ⊆ (zeros X L ∪ zeros X (X.line (tripleCell i))) ∪ zeros X M := by
      intro a ha
      have h := hz a ha
      rw [hQ,hM,map_mul,map_mul,mul_eq_zero,mul_eq_zero] at h
      simpa [zeros,or_assoc] using h
    have hs := Finset.card_le_card hsub
    have h₁ := Finset.card_union_le (zeros X L) (zeros X (X.line (tripleCell i)))
    have h₂ := Finset.card_union_le (zeros X L ∪ zeros X (X.line (tripleCell i))) (zeros X M)
    have h₃ := linear_bound X hn (X.line (tripleCell i)) (irreducible_linear (X.degree _)).ne_zero
      (X.degree _).le
    have h₄ := linear_bound X hn M hM0 hMd
    have hsize : covered.card = 16 := by decide
    omega
  have hdeg : F.totalDegree = 3 := by
    by_contra h
    exact hfree _ (X.degree _) (hsection 0 F (by omega) (fun a ha => hz _ (hc 0 ha)))
  refine ⟨⟨?_,?_⟩,hdeg⟩
  · intro hu
    have h := hu.map (atPoint (X.point 0))
    rw [hz 0 (by decide)] at h
    exact not_isUnit_zero h
  · intro U V he
    have hnU : U ≠ 0 := by rintro rfl; simp [he] at hF
    have hnV : V ≠ 0 := by rintro rfl; simp [he] at hF
    have hdUV := hdeg
    rw [he,totalDegree_mul_of_isDomain hnU hnV] at hdUV
    have unit (P : PlanePoly) (hp : P ≠ 0) (hp' : P.totalDegree = 0) : IsUnit P := by
      have hC := totalDegree_eq_zero_iff_eq_C.mp hp'
      have hnC : P.coeff 0 ≠ 0 := by intro h; rw [h,map_zero] at hC; exact hp hC
      exact hC ▸ (isUnit_iff_ne_zero.mpr hnC).map C
    by_cases hU : U.totalDegree = 0
    · exact Or.inl (unit U hnU hU)
    by_cases hV : V.totalDegree = 0
    · exact Or.inr (unit V hnV hV)
    rcases (show U.totalDegree = 1 ∨ V.totalDegree = 1 by omega) with h | h
    · exact False.elim (hfree U h ⟨V,he⟩)
    · exact False.elim (hfree V h ⟨U,he.trans (mul_comm _ _)⟩)


/-- All five rows, five columns and the six sums numbered one through six
lie on a single irreducible cubic. -/
theorem five_by_five_cubic (X : Grid)
    (hn : NonCollinearFor 5 ((Finset.univ.map X.point : Finset ℝ²) : Set ℝ²)) :
    ∃ F : PlanePoly, Irreducible F ∧ F.totalDegree = 3 ∧
      ∀ a : Label, (a.val ≤ 9 ∨ 11 ≤ a.val ∧ a.val ≤ 16) → atPoint (X.point a) F = 0 := by
  obtain ⟨F,hF,hd,hz⟩ := cubic X
  obtain ⟨hirr,hdeg⟩ := rigid_cubic X hn F hF hd hz
  have index : ∀ a : Label, (a.val ≤ 9 ∨ 11 ≤ a.val ∧ a.val ≤ 16) → a ∈ covered := by decide
  exact ⟨F,hirr,hdeg,fun a ha => hz a (index a ha)⟩

/-- Form the grid directly from a point set, the collinear triples indexed
by row, column and sum, and any fourth point on each selected line. -/
theorem cubic_of_collinear_cells (S : Finset ℝ²) (p : Label ↪ ℝ²) (e : Cell → ℝ²)
    (hn : NonCollinearFor 5 (S : Set ℝ²)) (hp : Finset.univ.map p ⊆ S)
    (he : ∀ v, e v ∈ S) (hf : ∀ v a, e v ≠ p a)
    (h : ∀ v, Collinear ℝ ((insert (e v) ((cell v).map p) : Finset ℝ²) : Set ℝ²)) :
    ∃ F : PlanePoly, Irreducible F ∧ F.totalDegree = 3 ∧
      ∀ a : Label, (a.val ≤ 9 ∨ 11 ≤ a.val ∧ a.val ≤ 16) → atPoint (p a) F = 0 := by
  let T v := insert (e v) ((cell v).map p)
  have hmem (a : Label) : p a ∈ S := hp (Finset.mem_map.mpr ⟨a,Finset.mem_univ _,rfl⟩)
  have hcore (v) : e v ∉ (cell v).map p := by
    intro ha
    obtain ⟨a,_,hh⟩ := Finset.mem_map.mp ha
    exact hf v a hh.symm
  have hct : ∀ v : Cell, (cell v).card = 3 := by decide
  have hsize (v) : (T v).card = 4 := by simp [T,hcore,hct]
  have eqn (v : Cell) : ∃ L : PlanePoly, L.totalDegree = 1 ∧ atPoint (e v) L = 0 ∧
      ∀ a, atPoint (p a) L = 0 ↔ a ∈ cell v := by
    obtain ⟨L,hL,hd,hz⟩ := Erdos101CubicGrid.linear_through (T v) (h v)
    have hv : atPoint (e v) L = 0 := hz _ (Finset.mem_insert_self ..)
    have hdeg : L.totalDegree = 1 := by
      by_contra hh
      have hc := totalDegree_eq_zero_iff_eq_C.mp (show L.totalDegree = 0 by omega)
      rw [hc,eval_C] at hv
      rw [hv,map_zero] at hc
      exact hL hc
    let z := S.filter (fun x => atPoint x L = 0)
    have hsmall : z.card ≤ 4 :=
      Erdos101SecantComponents.linear_component_card hL hd hn
    have sub : T v ⊆ z := by
      intro x hx
      refine Finset.mem_filter.mpr ⟨?_,hz _ hx⟩
      rcases Finset.mem_insert.mp hx with rfl | hh
      · exact he v
      · exact hp (Finset.map_subset_map.mpr (Finset.subset_univ _) hh)
    have same : T v = z := Finset.eq_of_subset_of_card_le sub (by rw [hsize]; exact hsmall)
    refine ⟨L,hdeg,hv,fun a => ?_⟩
    have hh := Finset.ext_iff.mp same (p a)
    simpa [T,z,hmem,Ne.symm (hf v a)] using hh.symm
  choose L hd hl hi using eqn
  exact five_by_five_cubic ⟨p,L,e,hd,hi,hl,hf⟩
    (NonCollinearFor.subset (Finset.coe_subset.mpr hp) hn)

/-- Ten common real zeros identify the zero sets of irreducible cubics. -/
theorem cubic_uniqueness (F G : PlanePoly) (hF : Irreducible F) (hG : Irreducible G)
    (dF : F.totalDegree = 3) (dG : G.totalDegree = 3) (T : Finset ℝ²) (hT : 10 ≤ T.card)
    (zF : ∀ p ∈ T, atPoint p F = 0) (zG : ∀ p ∈ T, atPoint p G = 0) :
    ∀ p : ℝ², atPoint p F = 0 ↔ atPoint p G = 0 := by
  have hdvd : F ∣ G := by
    by_contra hh
    have hc := Erdos101CurveIntersections.card_common_zeros_le T F G hF hh zF zG
    rw [dF,dG] at hc
    omega
  have assoc := hF.associated_of_dvd hG hdvd
  intro p
  exact ⟨fun h => (zero_dvd_iff.mp (h ▸ map_dvd (atPoint p) hdvd)),
    fun h => (zero_dvd_iff.mp (h ▸ map_dvd (atPoint p) assoc.symm.dvd))⟩

/-- Global labels 0–4 denote the rows, 5–14 the columns and 15–28 the sums. -/
abbrev LongLabel := Fin 29
abbrev LongCell := Fin 5 × Fin 10

def longCell (ij : LongCell) : Finset LongLabel :=
  let i := ij.1.val
  let j := ij.2.val
  {⟨i, by have := ij.1.isLt; omega⟩, ⟨5+j, by have := ij.2.isLt; omega⟩,
    ⟨15+i+j, by have := ij.1.isLt; have := ij.2.isLt; omega⟩}

private def windowIndex (b : Fin 6) (a : Label) : LongLabel :=
  if a.val < 5 then ⟨a.val,by omega⟩ else
  if a.val < 10 then ⟨a.val+b.val,by omega⟩ else ⟨a.val+5+b.val,by omega⟩

private def window (b : Fin 6) : Label ↪ LongLabel :=
  ⟨windowIndex b,(by decide : ∀ b : Fin 6, Function.Injective (windowIndex b)) b⟩

private def windowCell (b : Fin 6) (ij : Cell) : LongCell :=
  (ij.1,⟨ij.2.val+b.val,by have := ij.2.isLt; omega⟩)

private def reached (b : Fin 6) : Finset LongLabel := covered.map (window b)

private theorem glue_windows (p : LongLabel ↪ ℝ²)
    (localCubic : ∀ b : Fin 6, ∃ F : PlanePoly, Irreducible F ∧ F.totalDegree = 3 ∧
      ∀ a ∈ reached b, atPoint (p a) F = 0) :
    ∃ F : PlanePoly, Irreducible F ∧ F.totalDegree = 3 ∧
      ∀ a : LongLabel, (a.val ≤ 14 ∨ 16 ≤ a.val ∧ a.val ≤ 26) → atPoint (p a) F = 0 := by
  choose F hirr hdeg hz using localCubic
  have adjacent (i : Fin 5) : ∀ x : ℝ², atPoint x (F i.castSucc) = 0 ↔
      atPoint x (F i.succ) = 0 := by
    let T := reached i.castSucc ∩ reached i.succ
    have hs : 10 ≤ T.card :=
      (by decide : ∀ i : Fin 5, 10 ≤ (reached i.castSucc ∩ reached i.succ).card) i
    exact cubic_uniqueness _ _ (hirr _) (hirr _) (hdeg _) (hdeg _) (T.map p)
      (by simpa using hs)
      (by intro x hx; obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx; exact hz _ _ (Finset.mem_inter.mp ha).1)
      (by intro x hx; obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx; exact hz _ _ (Finset.mem_inter.mp ha).2)
  have chain (b : Fin 6) (x : ℝ²) : atPoint x (F b) = 0 ↔ atPoint x (F 0) = 0 := by
    induction b using Fin.induction with
    | zero => rfl
    | succ i ih => exact (adjacent i x).symm.trans ih
  refine ⟨F 0,hirr 0,hdeg 0,?_⟩
  intro a ha
  have index : ∀ a : LongLabel, (a.val ≤ 14 ∨ 16 ≤ a.val ∧ a.val ≤ 26) →
      ∃ b : Fin 6, a ∈ reached b := by decide
  obtain ⟨b,hb⟩ := index a ha
  exact (chain b _).1 (hz b a hb)

/-- Every five-by-ten grid of these collinear quadruples puts all five rows,
all ten columns and the eleven interior sums numbered one through eleven on
a single irreducible cubic. No relation among the fourth points is assumed. -/
theorem five_by_ten_cubic (S : Finset ℝ²) (p : LongLabel ↪ ℝ²) (e : LongCell → ℝ²)
    (hn : NonCollinearFor 5 (S : Set ℝ²)) (hp : Finset.univ.map p ⊆ S)
    (he : ∀ v, e v ∈ S) (hf : ∀ v a, e v ≠ p a)
    (h : ∀ v, Collinear ℝ ((insert (e v) ((longCell v).map p) : Finset ℝ²) : Set ℝ²)) :
    ∃ F : PlanePoly, Irreducible F ∧ F.totalDegree = 3 ∧
      ∀ a : LongLabel, (a.val ≤ 14 ∨ 16 ≤ a.val ∧ a.val ≤ 26) → atPoint (p a) F = 0 := by
  have hc : ∀ b v, (cell v).map (window b) = longCell (windowCell b v) := by decide
  have localCubic (b : Fin 6) : ∃ F : PlanePoly, Irreducible F ∧ F.totalDegree = 3 ∧
      ∀ a ∈ reached b, atPoint (p a) F = 0 := by
    obtain ⟨F,hirr,hdeg,hz⟩ := cubic_of_collinear_cells S ((window b).trans p)
      (fun v => e (windowCell b v)) hn (by
        rw [← Finset.map_map]
        exact (Finset.map_subset_map.mpr (Finset.subset_univ _)).trans hp)
      (fun v => he _) (fun v a => hf _ _) (by
        intro v
        rw [← Finset.map_map,hc]
        exact h _)
    refine ⟨F,hirr,hdeg,?_⟩
    intro a ha
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
    exact hz x ((by decide : ∀ a ∈ covered, a.val ≤ 9 ∨ 11 ≤ a.val ∧ a.val ≤ 16) x hx)
  exact glue_windows p localCubic

end Erdos101AdditiveGrid
end

noncomputable section
namespace Erdos101OverlappingGrids

open EuclideanGeometry MvPolynomial
open Erdos101CubicGrid (PlanePoly atPoint)
open Erdos101AdditiveGrid (LongLabel LongCell longCell)
open scoped Classical

lemma no_four_on_irreducible_cubic (T : Finset ℝ²) (hT : 4 ≤ T.card)
    (hc : Collinear ℝ (T : Set ℝ²)) (F : PlanePoly) (hF : Irreducible F)
    (dF : F.totalDegree = 3) (hzero : ∀ p ∈ T, atPoint p F = 0) : False := by
  obtain ⟨G, hG, dG, zG⟩ := Erdos101CubicGrid.linear_through T hc
  have hnd : ¬ F ∣ G := by
    rintro ⟨Q, hQ⟩
    have hn : Q ≠ 0 := by
      rintro rfl
      simp [hQ] at hG
    rw [hQ, totalDegree_mul_of_isDomain hF.ne_zero hn, dF] at dG
    omega
  have hsize := Erdos101CurveIntersections.card_common_zeros_le T F G hF hnd hzero zG
  rw [dF] at hsize
  omega

/-- The four ranges of labels are 0–8, 9–18, 19–36 and 37–63. -/
abbrev Label := Fin 64

def active (i : Fin 9) : Prop := i.val < 5 ∨ i.val % 2 = 0
instance (i : Fin 9) : Decidable (active i) := by unfold active; infer_instance

def cell (i : Fin 9) (j : Fin 10) : Finset Label :=
  {⟨i.val, by omega⟩, ⟨9 + j.val, by omega⟩,
   ⟨19 + i.val + j.val, by omega⟩, ⟨37 + i.val + 2*j.val, by omega⟩}

private def firstIndex (a : LongLabel) : Label :=
  if a.val < 5 then ⟨a.val, by omega⟩
  else if a.val < 15 then ⟨9 + (a.val - 5), by omega⟩
  else ⟨19 + (a.val - 15), by omega⟩

private def secondIndex (a : LongLabel) : Label :=
  if a.val < 5 then ⟨2*a.val, by omega⟩
  else if a.val < 15 then ⟨9 + (a.val - 5), by omega⟩
  else ⟨37 + 2*(a.val - 15), by omega⟩

private def first : LongLabel ↪ Label := ⟨firstIndex, by decide⟩
private def second : LongLabel ↪ Label := ⟨secondIndex, by decide⟩
private def firstRow (i : Fin 5) : Fin 9 := ⟨i.val, by omega⟩
private def secondRow (i : Fin 5) : Fin 9 := ⟨2*i.val, by omega⟩
private def firstExtra (v : LongCell) : Label := ⟨37 + v.1.val + 2*v.2.val, by omega⟩
private def secondExtra (v : LongCell) : Label := ⟨19 + 2*v.1.val + v.2.val, by omega⟩

private lemma cubic_from_window (S : Finset ℝ²) (p : Label ↪ ℝ²)
    (hn : NonCollinearFor 5 (S : Set ℝ²))
    (inside : ∀ i j, active i → ∀ a ∈ cell i j, p a ∈ S)
    (col : ∀ i j, active i → Collinear ℝ (((cell i j).map p : Finset ℝ²) : Set ℝ²))
    (f : LongLabel ↪ Label) (row : Fin 5 → Fin 9) (extra : LongCell → Label)
    (ha : ∀ i, active (row i))
    (fresh : ∀ v a, extra v ≠ f a)
    (cells : ∀ v : LongCell, insert (extra v) ((longCell v).map f) = cell (row v.1) v.2) :
    ∃ F : PlanePoly, Irreducible F ∧ F.totalDegree = 3 ∧
      ∀ a : LongLabel, (a.val ≤ 14 ∨ 16 ≤ a.val ∧ a.val ≤ 26) → atPoint (p (f a)) F = 0 := by
  apply Erdos101AdditiveGrid.five_by_ten_cubic S (f.trans p) (fun v => p (extra v)) hn
  · intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v, hv⟩ := (by decide : ∀ a : LongLabel, ∃ v : LongCell, a ∈ longCell v) a
    apply inside (row v.1) v.2 (ha _)
    rw [← cells v]
    exact Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨a, hv, rfl⟩)
  · intro v
    apply inside (row v.1) v.2 (ha _)
    rw [← cells v]
    exact Finset.mem_insert_self ..
  · exact fun v a heq => fresh v a (p.injective heq)
  · intro v
    rw [← Finset.map_map, ← Finset.map_insert, cells v]
    exact col _ _ (ha _)

private def column (j : Fin 10) : Label := ⟨9 + j.val, by omega⟩
private def columnEmb : Fin 10 ↪ Label := ⟨column, by decide⟩
private def longColumn (j : Fin 10) : LongLabel := ⟨5 + j.val, by omega⟩

/-- No configuration without five collinear points can realize the labels
`i, j, i+j, i+2j` in four disjoint families on the selected seven rows
and all ten columns. Only points actually occurring on these lines need
belong to the configuration. -/
theorem impossible (S : Finset ℝ²) (p : Label ↪ ℝ²)
    (hn : NonCollinearFor 5 (S : Set ℝ²))
    (inside : ∀ i j, active i → ∀ a ∈ cell i j, p a ∈ S)
    (col : ∀ i j, active i → Collinear ℝ (((cell i j).map p : Finset ℝ²) : Set ℝ²)) :
    False := by
  obtain ⟨F, hF, dF, zF⟩ := cubic_from_window S p hn inside col first firstRow firstExtra
    (by decide) (by decide) (by decide)
  obtain ⟨G, hG, dG, zG⟩ := cubic_from_window S p hn inside col second secondRow secondExtra
    (by decide) (by decide) (by decide)
  let B := Finset.univ.map (columnEmb.trans p)
  have onB (f : LongLabel ↪ Label) (P : PlanePoly)
      (zP : ∀ a : LongLabel, (a.val ≤ 14 ∨ 16 ≤ a.val ∧ a.val ≤ 26) → atPoint (p (f a)) P = 0)
      (cols : ∀ j, f (longColumn j) = column j) : ∀ x ∈ B, atPoint x P = 0 := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
    change atPoint (p (column j)) P = 0
    rw [← cols j]
    apply zP
    left
    change 5 + j.val ≤ 14
    omega
  have agree := Erdos101AdditiveGrid.cubic_uniqueness F G hF hG dF dG B
    (by simp [B]) (onB first F zF (by decide)) (onB second G zG (by decide))
  apply no_four_on_irreducible_cubic ((cell 0 1).map p) _ (col 0 1 (by decide)) F hF dF
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    have cases : a = first 0 ∨ a = first 6 ∨ a = first 16 ∨ a = second 16 :=
      (by decide : ∀ a ∈ cell 0 1,
        a = first 0 ∨ a = first 6 ∨ a = first 16 ∨ a = second 16) a ha
    rcases cases with rfl | rfl | rfl | rfl
    · exact zF 0 (by decide)
    · exact zF 6 (by decide)
    · exact zF 16 (by decide)
    · exact (agree _).mpr (zG 16 (by decide))
  · rw [Finset.card_map]
    decide

end Erdos101OverlappingGrids
end

noncomputable section
namespace Erdos101GridConcentration

open EuclideanGeometry MvPolynomial
open Erdos101CubicGrid (PlanePoly atPoint)
open Erdos101AdditiveGrid (LongLabel LongCell longCell)
open scoped Classical

private theorem fiber_moment {ι κ α : Type*} [DecidableEq κ] [DecidableEq α]
    (G : Finset ι) (B : Finset κ) (f : ι → κ) (x : ι → α) (R : ι → Finset α)
    (keys : ∀ i ∈ G, f i ∈ B) (inj : Set.InjOn (fun i => (f i,x i)) (G : Set ι))
    (inRow : ∀ i ∈ G, ∀ j ∈ G, f j = f i → x j ∈ R i) :
    G.card^2 ≤ B.card * ∑ i ∈ G, (R i).card := by
  classical
  let fiber (b : κ) := G.filter (fun i => f i = b)
  have size (i : ι) (hi : i ∈ G) : (fiber (f i)).card ≤ (R i).card := by
    apply Finset.card_le_card_of_injOn x
    · intro j hj
      exact inRow i hi j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
    · intro j hj k hk h
      exact inj (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hk).1
        (Prod.ext ((Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hk).2.symm) h)
  have mass : ∑ b ∈ B, (fiber b).card = G.card := (Finset.card_eq_sum_card_fiberwise keys).symm
  have sq : ∑ b ∈ B, (fiber b).card^2 = ∑ i ∈ G, (fiber (f i)).card := by
    simpa only [fiber, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, ← pow_two] using
      (Finset.sum_fiberwise_of_maps_to' (s := G) (t := B) keys (fun b => (fiber b).card))
  calc
    _ = (∑ b ∈ B, (fiber b).card)^2 := by rw [mass]
    _ ≤ B.card * ∑ b ∈ B, (fiber b).card^2 := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := by rw [sq]; exact Nat.mul_le_mul_left _ (Finset.sum_le_sum size)

/-- The largest class of identical traces controls the fourth moment
of the number of grids. Distinct traces intersect at most b times. -/
private theorem pool {ι κ α : Type*} [DecidableEq κ] [DecidableEq α]
    (G : Finset ι) (occurs : G.Nonempty) (B : Finset κ) (S : Finset α)
    (f : ι → κ) (x : ι → α) (R : ι → Finset α) (b : ℕ)
    (keys : ∀ i ∈ G, f i ∈ B) (inj : Set.InjOn (fun i => (f i,x i)) (G : Set ι))
    (sub : ∀ i ∈ G, R i ⊆ S) (inRow : ∀ i ∈ G, ∀ j ∈ G, f j = f i → x j ∈ R i)
    (apart : ∀ i ∈ G, ∀ j ∈ G, R j ≠ R i → (R i ∩ R j).card ≤ b) :
    ∃ i ∈ G, G.card^4 ≤ B.card^2 * S.card * G.card *
      (b*G.card + S.card*(G.filter (fun j => R j = R i)).card) := by
  classical
  let count (i : ι) := (G.filter (fun j => R j = R i)).card
  obtain ⟨k,hk,maximal⟩ := G.exists_max_image count occurs
  have row (i : ι) (hi : i ∈ G) :
      ∑ j ∈ G, (R i ∩ R j).card ≤ b*G.card + S.card*count k := calc
    _ ≤ ∑ j ∈ G, (b + if R j = R i then S.card else 0) := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs with h
      · exact (Finset.card_le_card (Finset.inter_subset_left.trans (sub i hi))).trans (by omega)
      · simpa using apart i hi j hj h
    _ = b*G.card + S.card*count i := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [count,Nat.mul_comm]
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ (maximal _ hi)) _
  have pairs : (∑ e ∈ G ×ˢ G, (R e.1 ∩ R e.2).card) ≤
      G.card*(b*G.card + S.card*count k) := by
    rw [Finset.sum_product]
    calc
      _ ≤ ∑ _i ∈ G, (b*G.card + S.card*count k) := Finset.sum_le_sum row
      _ = _ := by simp
  have m₁ := fiber_moment G B f x R keys inj inRow
  have m₂ := Erdos101SecantSamples.common_pivots G S R sub
  refine ⟨k,hk,?_⟩
  calc
    G.card^4 = (G.card^2)^2 := by ring
    _ ≤ (B.card * ∑ i ∈ G, (R i).card)^2 := Nat.pow_le_pow_left m₁ 2
    _ = B.card^2 * (∑ i ∈ G, (R i).card)^2 := mul_pow ..
    _ ≤ B.card^2 * (S.card * (G.card*(b*G.card+S.card*count k))) :=
      Nat.mul_le_mul_left _ (m₂.trans (Nat.mul_le_mul_left _ pairs))
    _ = _ := by dsimp only [count]; ring

def colIndex (j : Fin 10) : LongLabel := ⟨5+j.val,by omega⟩
private def colEmb : Fin 10 ↪ LongLabel := ⟨colIndex, by decide⟩

/-- Data of one five-by-ten window. Its fourth points may be arbitrary,
and the window may share points or lines with other windows. -/
structure Window (S : Finset ℝ²) where
  point : LongLabel ↪ ℝ²
  extra : LongCell → ℝ²
  core_mem : Finset.univ.map point ⊆ S
  extra_mem : ∀ v, extra v ∈ S
  fresh : ∀ v a, extra v ≠ point a
  collinear : ∀ v, Collinear ℝ ((insert (extra v) ((longCell v).map point) : Finset ℝ²) : Set ℝ²)

private def covered (a : LongLabel) := a.val ≤ 14 ∨ 16 ≤ a.val ∧ a.val ≤ 26

/-- A common column key identifies the ten column labels pointwise.
The row-zero points distinguish windows with the same key. -/
theorem many_shared_grids {ι κ : Type*} [DecidableEq κ]
    (S : Finset ℝ²) (hn : NonCollinearFor 5 (S : Set ℝ²))
    (G : Finset ι) (occurs : G.Nonempty) (B : Finset κ) (key : ι → κ)
    (W : ι → Window S) (keys : ∀ i ∈ G, key i ∈ B)
    (rows : Set.InjOn (fun i => (key i,(W i).point 0)) (G : Set ι))
    (cols : ∀ i ∈ G, ∀ j ∈ G, key j = key i → ∀ h : Fin 10,
      (W j).point (colIndex h) = (W i).point (colIndex h)) :
    ∃ F : PlanePoly, Irreducible F ∧ F.totalDegree = 3 ∧ ∃ H ⊆ G,
      (∀ i ∈ H, ∀ a : LongLabel, (a.val ≤ 14 ∨ 16 ≤ a.val ∧ a.val ≤ 26) →
         atPoint ((W i).point a) F = 0) ∧
      G.card^4 ≤ B.card^2*S.card*G.card*(9*G.card + S.card*H.card) := by
  classical
  choose P irr deg van using fun i => Erdos101AdditiveGrid.five_by_ten_cubic S (W i).point
    (W i).extra hn (W i).core_mem (W i).extra_mem (W i).fresh (W i).collinear
  let R (i : ι) := S.filter (fun p => atPoint p (P i) = 0)
  have contains (i : ι) (a : LongLabel) (ha : covered a) : (W i).point a ∈ R i :=
    Finset.mem_filter.mpr ⟨(W i).core_mem (Finset.mem_map.mpr ⟨a,Finset.mem_univ _,rfl⟩),van i a ha⟩
  have transfer (i j : ι) (T : Finset ℝ²) (ht : 10 ≤ T.card)
      (ti : T ⊆ R i) (tj : T ⊆ R j) : R i = R j := by
    have agree := Erdos101AdditiveGrid.cubic_uniqueness (P i) (P j) (irr i) (irr j)
      (deg i) (deg j) T ht (fun x hx => (Finset.mem_filter.mp (ti hx)).2)
      (fun x hx => (Finset.mem_filter.mp (tj hx)).2)
    ext x
    simp only [R, Finset.mem_filter, agree]
  have same (i : ι) (hi : i ∈ G) (j : ι) (hj : j ∈ G) (eq : key j = key i) : R j = R i := by
    let T := Finset.univ.map (colEmb.trans (W j).point)
    have inc (h : Fin 10) : covered (colIndex h) := Or.inl (by change 5+h.val ≤ 14; omega)
    apply transfer j i T (by simp [T])
    · intro x hx
      obtain ⟨h,_,rfl⟩ := Finset.mem_map.mp hx
      exact contains _ _ (inc h)
    · intro x hx
      obtain ⟨h,_,rfl⟩ := Finset.mem_map.mp hx
      change (W j).point (colIndex h) ∈ R i
      rw [cols i hi j hj eq h]
      exact contains _ _ (inc h)
  have apart (i : ι) (_ : i ∈ G) (j : ι) (_ : j ∈ G) (ne : R j ≠ R i) :
      (R i ∩ R j).card ≤ 9 := by
    by_contra! hm
    exact ne (transfer i j _ hm Finset.inter_subset_left Finset.inter_subset_right).symm
  obtain ⟨k,_,bound⟩ := pool G occurs B S key (fun i => (W i).point 0) R 9 keys rows
    (fun _ _ => Finset.filter_subset ..)
    (fun i hi j hj eq => same i hi j hj eq ▸ contains j 0 (Or.inl (by decide))) apart
  refine ⟨P k,irr k,deg k,_,Finset.filter_subset ..,?_,bound⟩
  intro i hi a ha
  obtain ⟨_,eq⟩ := Finset.mem_filter.mp hi
  exact (Finset.mem_filter.mp (eq ▸ contains i a ha : (W i).point a ∈ R k)).2

/-- The row-zero, column-one line has a sum label covered by the cubic. -/
def distinguished {S : Finset ℝ²} (W : Window S) : AffineSubspace ℝ ℝ² :=
  line[ℝ,W.point 0,W.point 6]

private theorem distinguished_points {S : Finset ℝ²} (hn : NonCollinearFor 5 (S : Set ℝ²))
    (W : Window S) (F : PlanePoly)
    (covered_zero : ∀ a : LongLabel, covered a → atPoint (W.point a) F = 0) :
    distinguished W ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧
    3 ≤ (S.filter (fun p => p ∈ distinguished W ∧ atPoint p F = 0)).card := by
  let v : LongCell := (0,1)
  let U := (longCell v).map W.point
  let T := insert (W.extra v) U
  have inS (a : LongLabel) : W.point a ∈ S := W.core_mem (Finset.mem_map.mpr ⟨a,Finset.mem_univ _,rfl⟩)
  have distinct : W.point 0 ≠ W.point 6 := W.point.injective.ne (by decide)
  have incore (a : LongLabel) (ha : a ∈ longCell v) : W.point a ∈ T :=
    Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨a,ha,rfl⟩)
  have line (p : ℝ²) (hp : p ∈ T) : p ∈ distinguished W :=
    (W.collinear v).mem_affineSpan_of_mem_of_ne (incore 0 (by decide)) (incore 6 (by decide)) hp distinct
  have source : T ⊆ S := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl|h
    · exact W.extra_mem v
    · obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp h
      exact inS a
  have cardU : U.card = 3 := (Finset.card_map ..).trans (by decide)
  have off : W.extra v ∉ U := by
    intro h
    obtain ⟨a,_,eq⟩ := Finset.mem_map.mp h
    exact W.fresh v a eq.symm
  have cardT : T.card = 4 := by simp [T,off,cardU]
  let actual := S.filter (fun p => p ∈ distinguished W)
  have subset : T ⊆ actual := fun p hp => Finset.mem_filter.mpr ⟨source hp,line p hp⟩
  have size : actual.card = 4 := by
    apply Nat.le_antisymm _ (cardT ▸ Finset.card_le_card subset)
    by_contra! many
    obtain ⟨Q,sub,five⟩ := Finset.exists_subset_card_eq (show 5 ≤ actual.card by omega)
    apply hn (Q : Set ℝ²) (Finset.coe_subset.mpr (sub.trans (Finset.filter_subset ..)))
      Q.finite_toSet (by simpa using five)
    apply (collinear_iff_exists_forall_eq_smul_vadd _).mpr
    refine ⟨W.point 0,W.point 6 -ᵥ W.point 0,?_⟩
    intro p hp
    obtain ⟨u,eq⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp (Finset.mem_filter.mp (sub hp)).2
    exact ⟨u,eq.symm⟩
  constructor
  · refine ⟨⟨_,inS 0,_,inS 6,distinct,rfl⟩,?_⟩
    have he : ((distinguished W : Set ℝ²) ∩ S) = (actual : Set ℝ²) := by ext p; simp [actual,and_comm]
    simpa only [he,Set.ncard_coe_finset] using size
  · rw [← cardU]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hp
    exact Finset.mem_filter.mpr ⟨inS a,line _ (incore _ ha),
      covered_zero a ((by decide : ∀ a ∈ longCell (0,1), a.val ≤ 14 ∨ 16 ≤ a.val ∧ a.val ≤ 26) a ha)⟩

private theorem density_arithmetic {n g b h f k : ℕ} (ng : 0 < n) (gg : 0 < g) (kk : 0 < k)
    (large : 18*k^2 ≤ n) (many : n^3 ≤ k*g) (keys : b ≤ n^2) (fib : h ≤ n*f)
    (bound : g^4 ≤ b^2*n*g*(9*g+n*h)) : n^2 ≤ 2*k^3*f := by
  have core : g^3 ≤ 9*g*n^5 + n^7*f := by
    apply Nat.le_of_mul_le_mul_left (c := g) _ gg
    calc
      g*g^3 = g^4 := by ring
      _ ≤ _ := bound
      _ ≤ (n^2)^2*n*g*(9*g+n*(n*f)) := by gcongr
      _ = _ := by ring
  have gap : 18*n^5 ≤ g^2 := by
    apply Nat.le_of_mul_le_mul_left (c := k^2) _ (pow_pos kk _)
    calc
      k^2*(18*n^5) = (18*k^2)*n^5 := by ring
      _ ≤ n*n^5 := Nat.mul_le_mul_right _ large
      _ = (n^3)^2 := by ring
      _ ≤ (k*g)^2 := Nat.pow_le_pow_left many 2
      _ = _ := by ring
  have major : 18*g*n^5 ≤ g^3 := by
    calc
      _ = g*(18*n^5) := by ring
      _ ≤ g*g^2 := Nat.mul_le_mul_left _ gap
      _ = _ := by ring
  have endBound : g^3 ≤ 2*n^7*f := by
    have eq : 18*g*n^5 = 2*(9*g*n^5) := by ring
    rw [eq] at major
    rw [Nat.mul_assoc]
    omega
  apply Nat.le_of_mul_le_mul_left (c := n^7) _ (pow_pos ng _)
  calc
    n^7*n^2 = (n^3)^3 := by ring
    _ ≤ (k*g)^3 := Nat.pow_le_pow_left many 3
    _ = k^3*g^3 := mul_pow ..
    _ ≤ k^3*(2*n^7*f) := Nat.mul_le_mul_left _ endBound
    _ = _ := by ring

/-- If at least n³/k grids occur and at most n grids distinguish the same
line, one irreducible cubic contains three points on at least n²/(2k³)
distinct genuine four-point lines. -/
theorem cubic_lines_of_grids {ι κ : Type*} [DecidableEq κ]
    (S : Finset ℝ²) (hn : NonCollinearFor 5 (S : Set ℝ²))
    (G : Finset ι) (B : Finset κ) (key : ι → κ) (W : ι → Window S)
    (keys : ∀ i ∈ G, key i ∈ B)
    (rows : Set.InjOn (fun i => (key i,(W i).point 0)) (G : Set ι))
    (cols : ∀ i ∈ G, ∀ j ∈ G, key j = key i → ∀ h : Fin 10,
      (W j).point (colIndex h) = (W i).point (colIndex h))
    (k : ℕ) (positive : 0 < k) (large : 18*k^2 ≤ S.card)
    (many : S.card^3 ≤ k*G.card) (bounds : B.card ≤ S.card^2)
    (multiplicity : ∀ L, (G.filter (fun i => distinguished (W i) = L)).card ≤ S.card) :
    ∃ F : PlanePoly, Irreducible F ∧ F.totalDegree = 3 ∧ ∃ A : Finset (AffineSubspace ℝ ℝ²),
      S.card^2 ≤ 2*k^3*A.card ∧ ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧
        3 ≤ (S.filter (fun p => p ∈ L ∧ atPoint p F = 0)).card := by
  classical
  have sp : 0 < S.card := (by positivity : 0 < 18*k^2).trans_le large
  have gp : 0 < G.card := by
    by_contra! h
    have z := Nat.eq_zero_of_le_zero h
    simp [z,sp.ne'] at many
  obtain ⟨F,irr,deg,H,hg,zeros,size⟩ := many_shared_grids S hn G (Finset.card_pos.mp gp) B key W keys rows cols
  let ℓ (i : ι) := distinguished (W i)
  let A := H.image ℓ
  have lines : H.card ≤ S.card*A.card := calc
    _ = ∑ L ∈ A, (H.filter (fun i => ℓ i = L)).card :=
      Finset.card_eq_sum_card_fiberwise (fun i hi => Finset.mem_image_of_mem ℓ hi)
    _ ≤ ∑ _L ∈ A, S.card := Finset.sum_le_sum (fun L _ =>
      (Finset.card_le_card (Finset.filter_subset_filter _ hg)).trans (multiplicity L))
    _ = _ := by simp [Nat.mul_comm]
  refine ⟨F,irr,deg,A,density_arithmetic sp gp positive large many bounds lines size,?_⟩
  intro L hL
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hL
  exact distinguished_points hn (W i) F (zeros i hi)

end Erdos101GridConcentration
end

noncomputable section
namespace Erdos101GridSparsity

open EuclideanGeometry Erdos101GridConcentration Erdos101CubicGrid
open scoped Classical

/-- For the stated window multiplicities, the number of windows is o(n³),
using the bounded-degree quadruple-line theorem as a separate premise. -/
theorem sparse_grids (bounded : OMA.R_Erdos101_erdos_101_R1.H2) (k : ℕ) (positive : 0 < k) :
    ∃ N : ℕ, ∀ {ι κ : Type} [DecidableEq κ] (S : Finset ℝ²),
    N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
    ∀ (G : Finset ι) (B : Finset κ) (key : ι → κ) (W : ι → Window S),
    (∀ i ∈ G, key i ∈ B) →
    Set.InjOn (fun i => (key i,(W i).point 0)) (G : Set ι) →
    (∀ i ∈ G, ∀ j ∈ G, key j = key i → ∀ h : Fin 10,
      (W j).point (colIndex h) = (W i).point (colIndex h)) →
    B.card ≤ S.card^2 →
    (∀ L, (G.filter (fun i => distinguished (W i) = L)).card ≤ S.card) →
    k*G.card < S.card^3 := by
  let δ : ℝ := 1/(2*(k : ℝ)^3)
  have kp : 0 < (k : ℝ) := by exact_mod_cast positive
  have dp : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N,sparse⟩ := Erdos101TwoMarkedSecants.sparse_if_bounded_curve bounded 3 δ dp
  refine ⟨max N (18*k^2),?_⟩
  intro ι κ _ S size cap G B key W keys rows cols bound mult
  by_contra! many
  obtain ⟨F,irr,deg,A,dense,three⟩ := cubic_lines_of_grids S cap G B key W keys rows cols k positive
    ((le_max_right ..).trans size) many bound mult
  have small := sparse S A F ((le_max_left ..).trans size) cap irr.ne_zero deg.le
    (fun L h => ⟨(three L h).1,(by decide : 2 ≤ 3).trans (three L h).2⟩)
  have lower : (S.card : ℝ)^2 ≤ (2*(k : ℝ)^3)*A.card := by exact_mod_cast dense
  have dp' : 0 < 2*(k : ℝ)^3 := by positivity
  dsimp only [δ] at small
  rw [one_div_mul_eq_div,lt_div_iff₀ dp'] at small
  linarith only [small,lower]

end Erdos101GridSparsity
end
