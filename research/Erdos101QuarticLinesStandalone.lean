import Mathlib
import OMAReductions.R_Erdos101_erdos_101_R1

-- Credit: @ubuwaits

/-!
# Three points on a real quartic polynomial graph

Uniformly over the coefficients, the number of triple lines on n graph
points is O(n^(11/6)). The same estimate controls four-point lines of
an ambient configuration with three graph points. If s points lie off an
affine image of the graph, at most choose(s,2) further lines are needed.

The proof uses the quartic divided-difference equation, real univariate
root bounds, and incidence counting on an ordered Cartesian grid. Related
general results are due to Elekes and Szabó (doi:10.1007/s00454-023-00556-3)
and to Raz, Sharir and de Zeeuw (arXiv:1504.05012).
-/

namespace Erdos101OrderedGrid

open scoped Classical

abbrev Pos := ℕ × ℕ

def grid (n : ℕ) : Finset Pos := Finset.range n ×ˢ Finset.range n
def block (k : ℕ) (p : Pos) : Pos := (p.1/k,p.2/k)
def fiber (G : Finset Pos) (k : ℕ) (c : Pos) := G.filter (fun p => block k p = c)
def occupied (G : Finset Pos) (k : ℕ) := G.image (block k)

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

/- Dual multiplicity for triples on a depressed quartic polynomial graph.
The two-moment equation is symmetric in its three parameters. Elimination
for two paired pencils gives a quadratic in the sum of the two coordinates;
its difference parameter has at most fourteen possible values for two
distinct nonexceptional sample points. -/

noncomputable section
namespace Erdos101QuarticPairs
open Polynomial
open scoped Classical

def moment (V a x c : ℝ) := a^2+x^2+c^2+a*x+a*c+x*c-V/2

def hit (V : ℝ) (p q : ℝ × ℝ) : Prop :=
  ∃ a : ℝ, moment V a p.1 q.1 = 0 ∧ moment V a p.2 q.2 = 0

def regular (p : ℝ × ℝ) : Prop := p.1 ≠ p.2 ∧ p.1 + p.2 ≠ 0

def A {R : Type*} [CommRing R] (d u : R) := d^2 + 3*d*u + 3*u^2
def B {R : Type*} [CommRing R] (d s u : R) := 2*s*(d^2 + 3*d*u + u^2)
def Cc {R : Type*} [CommRing R] (V d s u : R) :=
  d^4 + 3*d^3*u + 3*d^2*s^2 - 2*d^2*V + 4*d^2*u^2 + 3*d*s^2*u -
    4*d*V*u + 3*d*u^3 + s^2*u^2 - 2*V*u^2 + u^4

def eqn (V d s u v : ℝ) := A d u*v^2 + B d s u*v + Cc V d s u

private def ell (c d x y : ℝ) := x+c-y-d
private def m (c d x y : ℝ) := x^2+c*x+c^2-y^2-d*y-d^2

private theorem identity (V c d x y : ℝ) :
    eqn V (c-d) (c+d) (x-y) (x+y) = 4*((m c d x y)^2 -
      (x+c)*m c d x y*ell c d x y + (x^2+c*x+c^2-V/2)*(ell c d x y)^2) := by
  unfold eqn A B Cc m ell
  ring

theorem hit_eqn {V : ℝ} {p q : ℝ × ℝ} (h : hit V p q) :
    eqn V (p.1-p.2) (p.1+p.2) (q.1-q.2) (q.1+q.2) = 0 := by
  obtain ⟨a,hx,hy⟩ := h
  obtain ⟨c,d⟩ := p
  obtain ⟨x,y⟩ := q
  change moment V a c x = 0 at hx
  change moment V a d y = 0 at hy
  change eqn V (c-d) (c+d) (x-y) (x+y) = 0
  have linear : m c d x y = -a*ell c d x y := by
    unfold moment at hx hy
    unfold m ell
    linear_combination hx - hy
  rw [identity, linear]
  unfold moment at hx
  linear_combination 4*(ell c d x y)^2*hx

/-- Any real root off the exceptional difference lifts to a pair of simultaneous
moments, so its difference lies in a bounded interval. -/
private theorem bound_difference {V c d u v : ℝ} (away : u+(c-d) ≠ 0)
    (root : eqn V (c-d) (c+d) u v=0) : u^2 ≤ 4*V := by
  let x := (v+u)/2
  let y := (v-u)/2
  have sub : x-y=u := by dsimp [x,y]; ring
  have add : x+y=v := by dsimp [x,y]; ring
  have el : ell c d x y ≠ 0 := by
    change x+c-y-d ≠ 0
    convert away using 1
    dsimp [x,y]
    ring
  rw [← sub, ← add, identity] at root
  let a := -(m c d x y)/(ell c d x y)
  have hx : moment V a x c=0 := by
    dsimp [a, moment]
    field_simp [el]
    linear_combination root / 2
  have linear : a * ell c d x y = -m c d x y := by dsimp [a]; field_simp
  have hy : moment V a y d=0 := by
    unfold moment at hx ⊢
    unfold ell m at linear
    linear_combination hx - linear
  unfold moment at hx hy
  rw [← sub]
  nlinarith only [hx,hy,sq_nonneg (a+x+c),sq_nonneg (a+y+d),sq_nonneg a,sq_nonneg c,
    sq_nonneg d,sq_nonneg (x+y)]

private def pa (d : ℝ) : ℝ[X] := A (C d) X
private def pb (d s : ℝ) : ℝ[X] := B (C d) (C s) X
private def pc (V d s : ℝ) : ℝ[X] := Cc (C V) (C d) (C s) X

private def j (d s d' s' : ℝ) := pa d*pb d' s' - pa d'*pb d s
private def k (V d s d' s' : ℝ) := pa d*pc V d' s' - pa d'*pc V d s
private def eliminant (V d s d' s' : ℝ) :=
  pa d*(k V d s d' s')^2 - pb d s*k V d s d' s'*j d s d' s' +
    pc V d s*(j d s d' s')^2

@[simp] private lemma eval_pa (u d : ℝ) : (pa d).eval u = A d u := by simp [pa,A]
@[simp] private lemma eval_pb (u d s : ℝ) : (pb d s).eval u = B d s u := by simp [pb,B]
@[simp] private lemma eval_pc (u V d s : ℝ) : (pc V d s).eval u = Cc V d s u := by simp [pc,Cc]

private lemma Apos {d : ℝ} (hd : d ≠ 0) (u : ℝ) : 0 < A d u := by
  unfold A
  nlinarith only [sq_nonneg (2*u+d),sq_pos_of_ne_zero hd]

private lemma j_nonzero {d s d' s' : ℝ} (hd : d ≠ 0) (hd' : d' ≠ 0)
    (hs : s ≠ 0) (different : d ≠ d' ∨ s ≠ s') : j d s d' s' ≠ 0 := by
  intro eq
  have van (u : ℝ) : A d u*B d' s' u - A d' u*B d s u=0 := by
    simpa [j] using congrArg (Polynomial.eval u) eq
  have h0 := van 0
  simp only [A,B,mul_zero,add_zero] at h0
  have fact : 2*(d^2*d'^2)*(s'-s)=0 := by linear_combination h0
  have ss : s'=s := sub_eq_zero.mp ((mul_eq_zero.mp fact).resolve_left (by positivity))
  subst s'
  have hdd : d' ≠ d := fun h => different.elim (fun n => n h.symm) (fun n => n rfl)
  have f (u : ℝ) : 4*s*u^2*(d'-d)*(3*u+d+d')=0 := by
    have h := van u
    unfold A B at h
    linear_combination h
  have z1 : 3*1+d+d'=0 := (mul_eq_zero.mp (f 1)).resolve_left (by positivity)
  have z2 : 3*2+d+d'=0 := (mul_eq_zero.mp (f 2)).resolve_left (by positivity)
  linarith

private lemma eliminant_zero {V d s d' s' u v : ℝ}
    (h : eqn V d s u v=0) (h' : eqn V d' s' u v=0) :
    (eliminant V d s d' s').eval u=0 := by
  let J := (j d s d' s').eval u
  let K := (k V d s d' s').eval u
  have linear : K = -J*v := by
    dsimp [J,K,j,k]
    simp only [eval_sub, eval_mul, eval_pa, eval_pb, eval_pc]
    unfold eqn at h h'
    linear_combination A d u*h' - A d' u*h
  change (pa d*(k V d s d' s')^2 - pb d s*k V d s d' s'*j d s d' s' +
    pc V d s*(j d s d' s')^2).eval u = 0
  simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_pa, eval_pb, eval_pc]
  change A d u*K^2 - B d s u*K*J + Cc V d s u*J^2 = 0
  rw [linear]
  unfold eqn at h
  linear_combination J^2*h

private lemma eliminant_ne {V c e c' e' : ℝ} (hc : c ≠ e) (hc' : c' ≠ e')
    (hs : c+e ≠ 0) (diff : (c,e) ≠ (c',e')) :
    eliminant V (c-e) (c+e) (c'-e') (c'+e') ≠ 0 := by
  let d := c-e
  let s := c+e
  let d' := c'-e'
  let s' := c'+e'
  have different : d ≠ d' ∨ s ≠ s' := by
    by_contra! eq
    exact diff (Prod.ext (by dsimp [d,s,d',s'] at eq; linarith [eq.1,eq.2])
      (by dsimp [d,s,d',s'] at eq; linarith [eq.1,eq.2]))
  have nj := j_nonzero (sub_ne_zero.mpr hc) (sub_ne_zero.mpr hc') hs different
  let M := |c-e| + 4*|V| + 2
  obtain ⟨u,gt,nonroot⟩ : ∃ u > M, (j d s d' s').eval u ≠ 0 := by
    by_contra! no
    exact nj ((j d s d' s').eq_zero_of_infinite_isRoot (Set.Ioi_infinite M |>.mono fun u hu => no u hu))
  have pos : 0 < u := by dsimp [M] at gt; linarith [abs_nonneg (c-e),abs_nonneg V]
  have away : u+(c-e) ≠ 0 := by dsimp [M] at gt; linarith [neg_abs_le (c-e),abs_nonneg V]
  have big : 4*V < u^2 := by
    dsimp [M] at gt
    have above : 1 < u := by linarith [abs_nonneg (c-e),abs_nonneg V]
    nlinarith only [gt,abs_nonneg (c-e),le_abs_self V,mul_pos pos (sub_pos.mpr above)]
  intro null
  have ev := congrArg (Polynomial.eval u) null
  change (eliminant V d s d' s').eval u = (0 : ℝ[X]).eval u at ev
  simp only [eliminant, eval_add, eval_sub, eval_mul, eval_pow, eval_pa, eval_pb, eval_pc, eval_zero] at ev
  let J := (j d s d' s').eval u
  let K := (k V d s d' s').eval u
  have solution : eqn V d s u (-K/J)=0 := by
    unfold eqn
    field_simp [show J ≠ 0 from nonroot]
    linear_combination ev
  exact (not_le_of_gt big) (bound_difference away solution)

private lemma eliminant_degree (V d s d' s' : ℝ) : (eliminant V d s d' s').natDegree ≤ 14 := by
  dsimp [eliminant,k,j,pa,pb,pc,A,B,Cc]
  compute_degree

private lemma two_sum_roots {D S u V : ℝ} (different : D ≠ 0) :
    ∃ f : ℝ[X], f ≠ 0 ∧ f.natDegree ≤ 2 ∧ ∀ v, eqn V D S u v=0 → f.eval v=0 := by
  let f : ℝ[X] := C (A D u)*X^2+C (B D S u)*X+C (Cc V D S u)
  have coeff : f.coeff 2 = A D u := by simp [f,Polynomial.coeff_C_mul]
  exact ⟨f, fun hz => (Apos different u).ne' (by simpa [hz] using coeff.symm),
    by dsimp [f]; compute_degree, fun v h => by simpa [f,eqn] using h⟩

/-- Two distinct sample points off the diagonal and anti-diagonal determine
at most 28 pairs admitting a common intermediate for each sample. -/
theorem two_point_bound (T : Finset (ℝ × ℝ)) {p q : ℝ × ℝ}
    (hp : regular p) (hq : regular q) (different : p ≠ q)
    (first : ∀ t ∈ T, hit V p t) (second : ∀ t ∈ T, hit V q t) : T.card ≤ 28 := by
  let P := eliminant V (p.1-p.2) (p.1+p.2) (q.1-q.2) (q.1+q.2)
  have nz : P ≠ 0 := eliminant_ne hp.1 hq.1 hp.2 different
  let delta (t : ℝ × ℝ) := t.1-t.2
  have maps (t) (ht : t ∈ T) : delta t ∈ P.roots.toFinset := by
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots nz).mpr
      (eliminant_zero (hit_eqn (first t ht)) (hit_eqn (second t ht))))
  have fibers (u : ℝ) (_ : u ∈ P.roots.toFinset) : (T.filter (fun t => delta t=u)).card ≤ 2 := by
    let H := T.filter (fun t => delta t=u)
    let sig (t : ℝ × ℝ) := t.1+t.2
    obtain ⟨f,nf,deg,root⟩ := two_sum_roots (V := V) (S := p.1+p.2) (u := u) (sub_ne_zero.mpr hp.1)
    have inj : (H : Set (ℝ × ℝ)).InjOn sig := by
      intro a ha b hb eq
      have aa : a.1-a.2=u := (Finset.mem_filter.mp ha).2
      have bb : b.1-b.2=u := (Finset.mem_filter.mp hb).2
      change a.1+a.2=b.1+b.2 at eq
      exact Prod.ext (by linarith) (by linarith)
    have image : H.image sig ⊆ f.roots.toFinset := by
      intro v hv; obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨mem,dif⟩ := Finset.mem_filter.mp ht
      have h := hit_eqn (first t mem)
      change t.1-t.2 = u at dif
      rw [dif] at h
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots nf).mpr (root _ h))
    change H.card ≤ _
    rw [← Finset.card_image_of_injOn inj]
    exact (Finset.card_le_card image).trans ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans deg))
  have total := Finset.card_le_mul_card_image_of_maps_to maps 2 fibers
  have count : P.roots.toFinset.card ≤ 14 :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans (eliminant_degree ..))
  nlinarith only [total,count]

end Erdos101QuarticPairs

/- Cartesian grid incidence bound for the dual quartic correspondences. -/
noncomputable section
namespace Erdos101QuarticGrid

open Finset Polynomial Erdos101OrderedGrid Erdos101Parabola Erdos101SecantCuts
open Erdos101SecantOrder Erdos101SecantBlocks Erdos101QuarticPairs
open scoped Classical

theorem count_by_point {ι β : Type*} [DecidableEq β] (I : Finset ι) (T : Finset β) (D : ι → Finset β)
    (sub : ∀ i ∈ I, D i ⊆ T) :
    (∑ i ∈ I, (D i).card) = ∑ p ∈ T, (I.filter (fun i => p ∈ D i)).card := by
  classical
  trans ∑ i ∈ I, (T.filter (fun p => p ∈ D i)).card
  · refine Finset.sum_congr rfl fun i hi => congrArg Finset.card ?_
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun hp => ⟨sub i hi hp,hp⟩, fun hp => hp.2⟩
  · exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow ..

set_option maxHeartbeats 1200000 in
/-- Every occupied box pays for its first point. Additional points are covered
by distinct ordered pairs of points lying in that box. -/
theorem incidence_bound {ι : Type*} (I : Finset ι) (G : ι → Finset Pos) {n k b M : ℕ}
    (hk : 0 < k) (gridset : ∀ i ∈ I, G i ⊆ grid n)
    (thin : ∀ i ∈ I, (occupied (G i) k).card ≤ b*(n/k+1))
    (pair : ∀ p q : Pos, p ≠ q → (I.filter (fun i => p ∈ G i ∧ q ∈ G i)).card ≤ M) :
    ∑ i ∈ I, (G i).card ≤ I.card*b*(n/k+1) + (n/k+1)^2*k^4*M := by
  classical
  let boxes := grid (n/k+1)
  let F (i : ι) (c : Pos) := fiber (G i) k c
  let pairs (i : ι) (c : Pos) := (F i c).offDiag
  have fsum (i) (hi : i ∈ I) :
      (G i).card ≤ (occupied (G i) k).card + ∑ c ∈ boxes, (pairs i c).card := by
    have base (c) (hc : c ∈ occupied (G i) k) :
        (F i c).card ≤ 1 + (pairs i c).card := by
      dsimp only [pairs]
      rw [Finset.offDiag_card]
      have h : 0 < (F i c).card := by
        obtain ⟨p,hp,eq⟩ := Finset.mem_image.mp hc
        exact Finset.card_pos.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,eq⟩⟩
      generalize (F i c).card = m at h ⊢
      obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
      simp [Nat.succ_mul, Nat.mul_succ]
      omega
    calc
      (G i).card = ∑ c ∈ occupied (G i) k, (F i c).card := Finset.card_eq_sum_card_image ..
      _ ≤ ∑ c ∈ occupied (G i) k, (1 + (pairs i c).card) := Finset.sum_le_sum base
      _ = (occupied (G i) k).card + ∑ c ∈ occupied (G i) k, (pairs i c).card := by simp [Finset.sum_add_distrib]
      _ ≤ _ := Nat.add_le_add_left (Finset.sum_le_sum_of_subset_of_nonneg
        (occupied_subset (gridset i hi) k) (by intros; omega)) _
  have perbox (c : Pos) : (∑ i ∈ I, (pairs i c).card) ≤ k^4*M := by
    let P := fiber (grid n) k c
    have sub (i) (hi : i ∈ I) : pairs i c ⊆ P.offDiag := by
      intro pq hp
      obtain ⟨ha,hb,ne⟩ := Finset.mem_offDiag.mp hp
      have inc : F i c ⊆ P := Finset.filter_subset_filter _ (gridset i hi)
      exact Finset.mem_offDiag.mpr ⟨inc ha,inc hb,ne⟩
    have bound (pq) (hp : pq ∈ P.offDiag) :
        (I.filter (fun i => pq ∈ pairs i c)).card ≤ M := by
      refine (Finset.card_le_card ?_).trans (pair pq.1 pq.2 (Finset.mem_offDiag.mp hp).2.2)
      intro i hi
      obtain ⟨mem,h⟩ := Finset.mem_filter.mp hi
      obtain ⟨ha,hb,_⟩ := Finset.mem_offDiag.mp h
      exact Finset.mem_filter.mpr ⟨mem,(Finset.mem_filter.mp ha).1,(Finset.mem_filter.mp hb).1⟩
    have cardP := fiber_card_le (grid n) hk c
    have card2 : P.offDiag.card ≤ k^4 := by
      rw [Finset.offDiag_card]
      calc
        _ ≤ P.card*P.card := Nat.sub_le .. 
        _ ≤ k^2*k^2 := Nat.mul_le_mul cardP cardP
        _ = _ := by ring
    calc
      _ = ∑ pq ∈ P.offDiag, (I.filter (fun i => pq ∈ pairs i c)).card := count_by_point I _ _ sub
      _ ≤ ∑ _pq ∈ P.offDiag, M := Finset.sum_le_sum bound
      _ = P.offDiag.card*M := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ card2
  have sumocc := Finset.sum_le_sum thin
  calc
    _ ≤ ∑ i ∈ I, ((occupied (G i) k).card + ∑ c ∈ boxes, (pairs i c).card) := Finset.sum_le_sum fsum
    _ = (∑ i ∈ I, (occupied (G i) k).card) + ∑ c ∈ boxes, ∑ i ∈ I, (pairs i c).card := by
      rw [Finset.sum_add_distrib, Finset.sum_comm (s := I) (t := boxes)]
    _ ≤ (∑ _i ∈ I, b*(n/k+1)) + ∑ _c ∈ boxes, k^4*M :=
      Nat.add_le_add sumocc (Finset.sum_le_sum (fun c _ => perbox c))
    _ = _ := by simp [boxes,grid,pow_two,Nat.mul_assoc]

def pencil (V c x : ℝ) : ℝ[X] :=
  X^2 + C (x+c)*X + C (x^2+c^2+x*c-V/2)

@[simp] theorem eval_pencil (V c x y : ℝ) : (pencil V c x).eval y = moment V y x c := by
  simp [pencil,moment]; ring

theorem pencil_ne (V c x : ℝ) : pencil V c x ≠ 0 := by
  intro h
  have top : (pencil V c x).natDegree = 2 := by dsimp [pencil]; compute_degree <;> norm_num
  simp [h] at top

private theorem branch_bound (V c : ℝ) (σ : Fin 3 → SignType) :
    Pulls (Branch (pencil V c) 2 σ) 6 := by
  apply branch_pulls (pencil V c) 2 2 (fun x => by dsimp [pencil]; compute_degree)
  intro t i
  fin_cases i
  · refine ⟨pencil V c t, by dsimp [pencil]; compute_degree, ?_⟩
    intro x; simp [diff,moment]; ring
  · refine ⟨X+C (2*t+c), by compute_degree; decide, ?_⟩
    intro x; simp [diff,pencil,Polynomial.derivative_pow]; ring
  · refine ⟨C 2, by simp, ?_⟩
    intro x; norm_num [diff,pencil,Polynomial.derivative_pow]

abbrev Pair := ℝ × ℝ

def edges (V : ℝ) (T : Finset ℝ) (t : Pair) : Finset Pair :=
  (T ×ˢ T).filter (fun p => regular p ∧ hit V p t)

def boxConstant := 55404

private theorem occupancy (V : ℝ) (T : Finset ℝ) (t : Pair) (k : ℕ) :
    (occupied ((edges V T t).image (ranks T)) k).card ≤ boxConstant*(T.card/k+1) := by
  let R (i : (Fin 3 → SignType) × (Fin 3 → SignType)) (x y : ℝ) :=
    ∃ a, Branch (pencil V t.1) 2 i.1 x a ∧ Branch (pencil V t.2) 2 i.2 a y
  have pull (i) : Pulls (R i) 36 := Erdos101SecantCuts.compose (branch_bound V t.1 i.1) (branch_bound V t.2 i.2)
  have hits (p) (hp : p ∈ edges V T t) : ∃ i, R i p.1 p.2 := by
    obtain ⟨a,hx,hy⟩ := (Finset.mem_filter.mp hp).2.2
    refine ⟨(code 2 (pencil V t.1 p.1) a, code 2 (pencil V t.2 a) p.2),a,
      ⟨pencil_ne V t.1 p.1, ?_, rfl⟩,⟨pencil_ne V t.2 a, ?_, rfl⟩⟩
    · simpa only [eval_pencil] using hx
    · rw [eval_pencil]
      unfold moment at hy ⊢
      linear_combination hy
  have b := colored_occupied R pull T (edges V T t) (Finset.filter_subset ..) hits k
  have cardSign : Fintype.card SignType = 3 := by decide
  simpa [boxConstant, Fintype.card_fun, Fintype.card_prod, cardSign] using b

theorem quartic_incidences (V : ℝ) (T : Finset ℝ) {k : ℕ} (hk : 0 < k) :
    ∑ t ∈ T ×ˢ T, (edges V T t).card ≤
      T.card^2*boxConstant*(T.card/k+1) + (T.card/k+1)^2*k^4*28 := by
  let G (t : Pair) := (edges V T t).image (ranks T)
  have inc (t : Pair) : edges V T t ⊆ T ×ˢ T := Finset.filter_subset .. 
  have size (t : Pair) : (G t).card = (edges V T t).card :=
    Finset.card_image_of_injOn ((ranks_inj T).mono (Finset.coe_subset.mpr (inc t)))
  have bounds (t : Pair) : G t ⊆ grid T.card := by
    intro z hz; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a,b⟩ := Finset.mem_product.mp (inc t hp)
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (rank_lt_card T a), Finset.mem_range.mpr (rank_lt_card T b)⟩
  have pair (p q : Pos) (ne : p ≠ q) :
      ((T ×ˢ T).filter (fun t => p ∈ G t ∧ q ∈ G t)).card ≤ 28 := by
    let H := (T ×ˢ T).filter (fun t => p ∈ G t ∧ q ∈ G t)
    by_cases some : H.Nonempty
    · obtain ⟨t,ht⟩ := some
      obtain ⟨_,hp,hq⟩ := Finset.mem_filter.mp ht
      obtain ⟨x,hx,px⟩ := Finset.mem_image.mp hp
      obtain ⟨y,hy,qy⟩ := Finset.mem_image.mp hq
      have liftHit (z : Pair) (hz : z ∈ edges V T t) (v : Pair) (hv : ranks T z ∈ G v) : hit V z v := by
        obtain ⟨z',hz',eq⟩ := Finset.mem_image.mp hv
        have same := ranks_inj T (inc v hz') (inc t hz) eq
        exact same ▸ (Finset.mem_filter.mp hz').2.2
      apply two_point_bound H (V := V) (Finset.mem_filter.mp hx).2.1 (Finset.mem_filter.mp hy).2.1
        (fun eq => ne (px.symm.trans ((congrArg (ranks T) eq).trans qy)))
      · intro v hv
        exact liftHit x hx v (px ▸ (Finset.mem_filter.mp hv).2.1)
      · intro v hv
        exact liftHit y hy v (qy ▸ (Finset.mem_filter.mp hv).2.2)
    · change H.card ≤ 28
      simp [Finset.not_nonempty_iff_eq_empty.mp some]
  have ans := incidence_bound (T ×ˢ T) G hk (fun t _ => bounds t)
    (fun t _ => occupancy V T t k) pair
  simpa only [size,Finset.card_product,pow_two] using ans

end Erdos101QuarticGrid

/- Uniform power saving for the real three-variable quartic collinearity equation. -/

noncomputable section
namespace Erdos101QuarticMoments

open Finset Polynomial Erdos101QuarticPairs Erdos101QuarticGrid
open scoped Classical

def rows (V : ℝ) (T : Finset ℝ) (a : ℝ) :=
  (T ×ˢ T).filter (fun p => moment V a p.1 p.2 = 0)

def triples (V : ℝ) (T : Finset ℝ) := ∑ a ∈ T, (rows V T a).card

private theorem fiber_two (V a x : ℝ) (T : Finset ℝ) :
    (T.filter (fun c => moment V a x c=0)).card ≤ 2 := by
  let f := pencil V x a
  have hdeg : f.natDegree ≤ 2 := by dsimp [f,pencil]; compute_degree
  have incl : T.filter (fun c => moment V a x c=0) ⊆ f.roots.toFinset := by
    intro c hc
    obtain ⟨_,h⟩ := Finset.mem_filter.mp hc
    apply Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (pencil_ne V x a)).mpr ?_)
    change (pencil V x a).eval c = 0
    rw [eval_pencil]
    unfold moment at h ⊢
    linear_combination h
  exact (Finset.card_le_card incl).trans ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans hdeg))

private theorem small_bad (T : Finset ℝ) : ((T ×ˢ T).filter (fun p => ¬ regular p)).card ≤ 2*T.card := by
  apply Finset.card_le_mul_card_image_of_maps_to (f := Prod.fst)
    (fun p hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1) 2
  intro x hx
  let W := ((T ×ˢ T).filter (fun p => ¬ regular p)).filter (fun p => p.1=x)
  have incl : W ⊆ {(x,x),(x,-x)} := by
    intro p hp
    obtain ⟨⟨_,hn⟩,eq⟩ := Finset.mem_filter.mp hp |>.imp_left Finset.mem_filter.mp
    change p.1=x at eq
    change ¬ (p.1 ≠ p.2 ∧ p.1+p.2 ≠ 0) at hn
    by_cases d : p.1=p.2
    · rw [show p=(x,x) from Prod.ext eq (d.symm.trans eq)]
      exact Finset.mem_insert_self ..
    · have h : p.1+p.2=0 := by by_contra z; exact hn ⟨d,z⟩
      have e : p=(x,-x) := Prod.ext eq (by linarith)
      simp [e]
  exact (Finset.card_le_card incl).trans (Finset.card_le_two)

private def swap (r : Pair × Pair) : Pair × Pair :=
  ((r.1.2,r.2.2),(r.1.1,r.2.1))

private theorem inject_swap : Function.Injective swap := by
  rintro ⟨⟨a,b⟩,⟨c,d⟩⟩ ⟨⟨w,x⟩,⟨y,z⟩⟩ h
  simpa [swap,and_left_comm,and_comm,and_assoc] using h

theorem second_moment (V : ℝ) (T : Finset ℝ) :
    (triples V T)^2 ≤ T.card*(8*T.card^2+2*∑ t ∈ T ×ˢ T, (edges V T t).card) := by
  let U := T ×ˢ T
  let E (a : ℝ) := ((rows V T a) ×ˢ (rows V T a)).image swap
  let H (a : ℝ) := (E a).filter (fun r => regular r.2)
  let D (a : ℝ) := (E a).filter (fun r => ¬regular r.2)
  have sz (a) : (rows V T a).card^2 = (E a).card := by
    simp [E,Finset.card_image_of_injective _ inject_swap,pow_two]
  have info {a r} (hr : r ∈ E a) :
      r.1 ∈ U ∧ r.2 ∈ U ∧ moment V a r.2.1 r.1.1=0 ∧ moment V a r.2.2 r.1.2=0 := by
    obtain ⟨⟨⟨x,c⟩,⟨y,d⟩⟩,hw,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hw
    obtain ⟨xc,xa⟩ := Finset.mem_filter.mp h₁
    obtain ⟨yd,ya⟩ := Finset.mem_filter.mp h₂
    exact ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp xc).2,(Finset.mem_product.mp yd).2⟩,
      Finset.mem_product.mpr ⟨(Finset.mem_product.mp xc).1,(Finset.mem_product.mp yd).1⟩,xa,ya⟩
  have bad (a : ℝ) : (D a).card ≤ 8*T.card := by
    have maps (r) (hr : r ∈ D a) : r.2 ∈ U.filter (fun p => ¬regular p) :=
      Finset.mem_filter.mpr ⟨(info (Finset.mem_filter.mp hr).1).2.1,(Finset.mem_filter.mp hr).2⟩
    have cell (p : Pair) (_ : p ∈ U.filter (fun p => ¬regular p)) :
        ((D a).filter (fun r => r.2=p)).card ≤ 4 := by
      let I := (D a).filter (fun r => r.2=p)
      let L := T.filter (fun c => moment V a p.1 c=0)
      let R := T.filter (fun d => moment V a p.2 d=0)
      have inc : I ⊆ (L ×ˢ R) ×ˢ {p} := by
        intro r hr
        obtain ⟨hd,e⟩ := Finset.mem_filter.mp hr
        obtain ⟨ht,_,first,last⟩ := info (Finset.mem_filter.mp hd).1
        rw [show r.2=p from e] at first last
        exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨(Finset.mem_product.mp ht).1,first⟩,
           Finset.mem_filter.mpr ⟨(Finset.mem_product.mp ht).2,last⟩⟩,Finset.mem_singleton.mpr e⟩
      have mult := Nat.mul_le_mul (fiber_two V a p.1 T) (fiber_two V a p.2 T)
      exact (Finset.card_le_card inc).trans (by simpa [L,R] using mult)
    exact (Finset.card_le_mul_card_image_of_maps_to maps 4 cell).trans
      ((Nat.mul_le_mul_left 4 (small_bad T)).trans_eq (by ring))
  let all := U.biUnion (fun t => ({t} : Finset Pair) ×ˢ edges V T t)
  have acard : all.card = ∑ t ∈ U, (edges V T t).card := by
    rw [Finset.card_biUnion]
    · simp
    · intro t _ t' _ ne
      refine Finset.disjoint_left.mpr fun r hr hr' => ne ?_
      exact (Finset.mem_singleton.mp (Finset.mem_product.mp hr).1).symm.trans
        (Finset.mem_singleton.mp (Finset.mem_product.mp hr').1)
  have incl (a) (_ : a ∈ T) : H a ⊆ all := by
    intro r hr
    obtain ⟨he,reg⟩ := Finset.mem_filter.mp hr
    obtain ⟨ht,hp,first,last⟩ := info he
    exact Finset.mem_biUnion.mpr ⟨r.1,ht,Finset.mem_product.mpr
      ⟨Finset.mem_singleton_self _,Finset.mem_filter.mpr ⟨hp,reg,a,first,last⟩⟩⟩
  have fixed (r : Pair × Pair) (_ : r ∈ all) : (T.filter (fun a => r ∈ H a)).card ≤ 2 := by
    apply (Finset.card_le_card ?_).trans (fiber_two V r.2.1 r.1.1 T)
    intro a ha
    obtain ⟨mem,h⟩ := Finset.mem_filter.mp ha
    have z := (info (Finset.mem_filter.mp h).1).2.2.1
    refine Finset.mem_filter.mpr ⟨mem,?_⟩
    unfold moment at z ⊢
    linear_combination z
  have total : ∑ a ∈ T, (H a).card ≤ 2*all.card := calc
    _ = ∑ r ∈ all, (T.filter (fun a => r ∈ H a)).card := count_by_point T all H incl
    _ ≤ ∑ _r ∈ all, 2 := Finset.sum_le_sum fixed
    _ = _ := by simp [Nat.mul_comm]
  have both : ∑ a ∈ T, (rows V T a).card^2 ≤ 8*T.card^2+2*all.card := by
    have eq (a) : (E a).card=(D a).card+(H a).card := by
      rw [Nat.add_comm]; exact (Finset.card_filter_add_card_filter_not ..).symm
    simp_rw [sz,eq]
    rw [Finset.sum_add_distrib]
    have small := Finset.sum_le_sum (s:=T) (fun a _ => bad a)
    simp only [Finset.sum_const,smul_eq_mul] at small
    nlinarith only [small,total]
  rw [acard] at both
  exact (sq_sum_le_card_mul_sum_sq (s := T) (f := fun a => (rows V T a).card)).trans
    (Nat.mul_le_mul_left _ both)

def powerConstant : ℕ := (4*boxConstant+232)^3*8^11

/-- For n real parameters the ordered triple count is uniformly O(n^(11/6)). -/
theorem power_triples (V : ℝ) (T : Finset ℝ) :
    (triples V T)^6 ≤ powerConstant*T.card^11 := by
  by_cases hn : T.card=0
  · have empty := Finset.card_eq_zero.mp hn
    simp [empty, triples]
  let n := T.card
  let r := Nat.nthRoot 3 n
  let k := r+1
  have hk : 0 < k := by dsimp [k]; omega
  have hr : 1 ≤ r := (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr (by dsimp [n]; omega)
  have upper : n ≤ k^3 := (Nat.lt_pow_nthRoot_add_one (by decide : 3 ≠ 0) n).le
  have lower : r^3 ≤ n := Nat.pow_nthRoot_le_iff.mpr (Or.inl (by decide))
  have cube : k^3 ≤ 8*n := calc
    _ ≤ (2*r)^3 := Nat.pow_le_pow_left (by dsimp [k]; omega) _
    _ = 8*r^3 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ lower
  have quotient : n/k ≤ k^2 := by
    apply Nat.le_of_mul_le_mul_right (c := k)
    · exact (Nat.div_mul_le_self n k).trans (upper.trans_eq (by ring))
    · exact hk
  have ksq : 1 ≤ k^2 := Nat.one_le_pow _ _ hk
  have count := quartic_incidences V T hk
  change (∑ t ∈ T ×ˢ T, (edges V T t).card) ≤ n^2*boxConstant*(n/k+1)+(n/k+1)^2*k^4*28 at count
  have cuts : n/k+1 ≤ 2*k^2 := by omega
  have I : ∑ t ∈ T ×ˢ T, (edges V T t).card ≤ (2*boxConstant+112)*k^8 := by
    apply count.trans
    calc
      _ ≤ (k^3)^2*boxConstant*(2*k^2) + (2*k^2)^2*k^4*28 :=
        Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left upper _)) cuts)
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left cuts _)))
      _ = _ := by ring
  have m := second_moment V T
  change (triples V T)^2 ≤ n*(8*n^2+2*∑ t ∈ T ×ˢ T, (edges V T t).card) at m
  have ksmall : k^6 ≤ k^8 := Nat.pow_le_pow_right hk (by decide)
  have step : (triples V T)^2 ≤ (4*boxConstant+232)*k^11 := by
    apply m.trans
    calc
      _ ≤ k^3*(8*k^8+2*((2*boxConstant+112)*k^8)) := Nat.mul_le_mul upper (Nat.add_le_add
        (Nat.mul_le_mul_left 8 ((Nat.pow_le_pow_left upper 2).trans ((by ring : (k^3)^2=k^6) ▸ ksmall)))
        (Nat.mul_le_mul_left _ I))
      _ = _ := by ring
  calc
    _ = ((triples V T)^2)^3 := by ring
    _ ≤ ((4*boxConstant+232)*k^11)^3 := Nat.pow_le_pow_left step _
    _ = (4*boxConstant+232)^3*(k^3)^11 := by ring
    _ ≤ (4*boxConstant+232)^3*(8*n)^11 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left cube _)
    _ = _ := by unfold powerConstant; ring

end Erdos101QuarticMoments

/- Uniformly over real quartic polynomial graphs, n planar points determine
O(n^(11/6)) lines containing three points of the configuration on the graph.
Any other points of the configuration may be placed arbitrarily. -/

noncomputable section
namespace Erdos101QuarticLines

open EuclideanGeometry Finset Erdos101QuarticPairs Erdos101QuarticGrid Erdos101QuarticMoments
open scoped Classical

structure Quartic where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ
  lead : a ≠ 0

def Quartic.value (f : Quartic) (x : ℝ) := f.a*x^4+f.b*x^3+f.c*x^2+f.d*x+f.e
def Quartic.point (f : Quartic) (x : ℝ) : ℝ² := !₂[x,f.value x]
def Quartic.shift (f : Quartic) := f.b/(4*f.a)
def Quartic.level (f : Quartic) := 2*(6*f.shift^2-f.c/f.a)

private theorem from_coord (f : Quartic) {p : ℝ²} (h : p 1=f.value (p 0)) :
    p=f.point (p 0) := by
  ext i; fin_cases i <;> simp [Quartic.point,h]

theorem collinear_moment (f : Quartic) {x y z : ℝ} (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z)
    (hz : f.point z ∈ line[ℝ,f.point x,f.point y]) :
    moment f.level (x+f.shift) (y+f.shift) (z+f.shift) = 0 := by
  obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hz
  rw [AffineMap.lineMap_apply_module] at ht
  have h₀ := congrArg (fun p : ℝ² => p 0) ht
  have h₁ := congrArg (fun p : ℝ² => p 1) ht
  change (1-t)*x+t*y=z at h₀
  change (1-t)*f.value x+t*f.value y=f.value z at h₁
  have determinant : (y-x)*(f.value z-f.value x)-(z-x)*(f.value y-f.value x)=0 := by
    linear_combination (f.value y-f.value x)*h₀ - (y-x)*h₁
  have fact : ((y-x)*(z-x)*(z-y))*
      (f.a*(x^2+y^2+z^2+x*y+x*z+y*z)+f.b*(x+y+z)+f.c) = 0 := by
    unfold Quartic.value at determinant
    linear_combination determinant
  have normal := (mul_eq_zero.mp fact).resolve_left
    (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr xy.symm) (sub_ne_zero.mpr xz.symm)) (sub_ne_zero.mpr yz.symm))
  dsimp [moment,Quartic.level,Quartic.shift]
  field_simp [f.lead]
  linear_combination 16*f.a*normal

abbrev Line := AffineSubspace ℝ ℝ²

/-- A proper line with three distinct parameters on the quartic graph. -/
def threeOn (f : Quartic) (T : Finset ℝ) (L : Line) : Prop :=
  ∃ x ∈ T, ∃ y ∈ T, ∃ z ∈ T, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ line[ℝ,f.point x,f.point y]=L ∧ f.point z ∈ L

theorem triple_line_power (f : Quartic) (T : Finset ℝ) (F : Finset Line)
    (lines : ∀ L ∈ F, threeOn f T L) : F.card^6 ≤ powerConstant*T.card^11 := by
  classical
  choose x xm y ym z zm xy xz yz lineEq zmem using fun L : F => lines L.val L.property
  let X := T.image (fun t => t+f.shift)
  let key (L : F) : ℝ × Pair := (x L+f.shift,(y L+f.shift,z L+f.shift))
  let all := X.biUnion (fun a => ({a} : Finset ℝ) ×ˢ (rows f.level X a))
  have inj : Function.Injective key := by
    intro L M same
    have hx : x L+f.shift=x M+f.shift := congrArg Prod.fst same
    have hy : y L+f.shift=y M+f.shift := congrArg (fun p : ℝ × Pair => p.2.1) same
    apply Subtype.ext
    rw [← lineEq L,← lineEq M,add_right_cancel hx,add_right_cancel hy]
  have inc : F.attach.image key ⊆ all := by
    intro w hw
    obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp hw
    have mem (t) (ht : t ∈ T) : t+f.shift ∈ X := Finset.mem_image_of_mem _ ht
    have moment := collinear_moment f (xy L) (xz L) (yz L) ((lineEq L).symm ▸ zmem L)
    exact Finset.mem_biUnion.mpr ⟨_,mem _ (xm L),Finset.mem_product.mpr ⟨Finset.mem_singleton_self _,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨mem _ (ym L),mem _ (zm L)⟩,moment⟩⟩⟩
  have acard : all.card = triples f.level X := by
    rw [Finset.card_biUnion]
    · simp [triples]
    · intro t _ u _ ne
      refine Finset.disjoint_left.mpr fun w hw hw' => ne ?_
      exact (Finset.mem_singleton.mp (Finset.mem_product.mp hw).1).symm.trans
        (Finset.mem_singleton.mp (Finset.mem_product.mp hw').1)
  have bound := Finset.card_le_card inc
  rw [Finset.card_image_of_injective _ inj,Finset.card_attach,acard] at bound
  have cardX : X.card=T.card := Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)
  exact (Nat.pow_le_pow_left bound 6).trans ((power_triples f.level X).trans_eq (by rw [cardX]))

/-- Each counted line has three points on the graph and may have its fourth
point anywhere in the ambient finite configuration. -/
theorem four_lines_with_three_on_graph (f : Quartic) (S : Finset ℝ²) (F : Finset Line)
    (lines : ∀ L ∈ F, L ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧
      3 ≤ (S.filter (fun p => p ∈ L ∧ p 1=f.value (p 0))).card) :
    F.card^6 ≤ powerConstant*S.card^11 := by
  let T := S.image (fun p : ℝ² => p 0)
  refine (triple_line_power f T F ?_).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left Finset.card_image_le _))
  intro L hL
  obtain ⟨four,three⟩ := lines L hL
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := Finset.two_lt_card_iff.mp three
  obtain ⟨as,al,af⟩ := Finset.mem_filter.mp ha
  obtain ⟨bs,bl,bf⟩ := Finset.mem_filter.mp hb
  obtain ⟨cs,cl,cf⟩ := Finset.mem_filter.mp hc
  have av := from_coord f af
  have bv := from_coord f bf
  have cv := from_coord f cf
  have distinct {u v : ℝ²} (hu : u=f.point (u 0)) (hv : v=f.point (v 0)) (ne : u ≠ v) : u 0 ≠ v 0 :=
    fun eq => ne (hu.trans ((congrArg f.point eq).trans hv.symm))
  refine ⟨a 0,Finset.mem_image_of_mem _ as,b 0,Finset.mem_image_of_mem _ bs,c 0,Finset.mem_image_of_mem _ cs,
    distinct av bv ab,distinct av cv ac,distinct bv cv bc,?_,cv ▸ cl⟩
  rw [← av,← bv]
  exact OMA.R_Erdos101_erdos_101_R1.line_through four al bl ab

theorem affine_four_lines (f : Quartic) (e : ℝ² ≃ᵃ[ℝ] ℝ²) (S : Finset ℝ²) (F : Finset (AffineSubspace ℝ ℝ²))
    (lines : ∀ L ∈ F, L ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧
      3 ≤ (S.filter (fun p => p ∈ L ∧ e p 1 = f.value (e p 0))).card) :
    F.card^6 ≤ powerConstant*S.card^11 := by
  classical
  let imageLine (L : AffineSubspace ℝ ℝ²) := L.map e.toAffineMap
  have onLine (L : AffineSubspace ℝ ℝ²) (p : ℝ²) : e p ∈ imageLine L ↔ p ∈ L :=
    AffineSubspace.mem_map_iff_mem_of_injective (f := e.toAffineMap) e.injective
  have linj : Function.Injective imageLine := by
    intro L M eq
    ext p
    rw [← onLine L p,← onLine M p,eq]
  rw [← Finset.card_image_of_injective F linj,← Finset.card_image_of_injective S e.injective]
  apply four_lines_with_three_on_graph f
  intro T hT
  obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp hT
  obtain ⟨four,three⟩ := lines L hL
  obtain ⟨⟨a,ha,b,hb,ne,eq⟩,card⟩ := four
  refine ⟨⟨⟨e a,Finset.mem_image_of_mem _ ha,e b,Finset.mem_image_of_mem _ hb,e.injective.ne ne,?_⟩,?_⟩,?_⟩
  · rw [← eq]; dsimp only [imageLine]; rw [AffineSubspace.map_span,Set.image_pair]; rfl
  · change ((L.map e.toAffineMap : Set ℝ²) ∩ (S.image e : Set ℝ²)).ncard=4
    rw [AffineSubspace.coe_map,Finset.coe_image]
    change (e '' (L : Set ℝ²) ∩ e '' (S : Set ℝ²)).ncard=4
    rwa [← Set.image_inter e.injective,Set.ncard_image_of_injective _ e.injective]
  · rw [Finset.filter_image,Finset.card_image_of_injective _ e.injective]
    simpa only [onLine] using three

/-- If s points miss the transformed quartic, at most choose(s,2) additional
four-point lines need to be added to the preceding power bound. -/
theorem near_quartic (f : Quartic) (e : ℝ² ≃ᵃ[ℝ] ℝ²) (S : Finset ℝ²) :
    let off := S.filter (fun p => e p 1 ≠ f.value (e p 0))
    ((linesWithPointsFor 4 (S : Set ℝ²)).ncard - off.card.choose 2)^6 ≤ powerConstant*S.card^11 := by
  classical
  let off := S.filter (fun p => e p 1 ≠ f.value (e p 0))
  let A := (OMA.R_Erdos101_erdos_101_R1.four_lines_finite S).toFinset
  let P (L : Line) := 3 ≤ (S.filter (fun p => p ∈ L ∧ e p 1=f.value (e p 0))).card
  let good := A.filter P
  let bad := A.filter (fun L => ¬P L)
  have four {L} (h : L ∈ A) := (OMA.R_Erdos101_erdos_101_R1.four_lines_finite S).mem_toFinset.mp h
  have small (L : bad) : ∃ q : Finset ℝ², q ⊆ off ∧ q.card=2 ∧ ∀ p ∈ q, p ∈ L.val := by
    obtain ⟨mem,avoid⟩ := Finset.mem_filter.mp L.property
    let B := S.filter (fun p => p ∈ L.val)
    let C := B.filter (fun p => e p 1=f.value (e p 0))
    let D := B.filter (fun p => e p 1≠f.value (e p 0))
    have count : C.card+D.card=B.card := Finset.card_filter_add_card_filter_not ..
    have total : B.card=4 := OMA.R_Erdos101_erdos_101_R1.four_points (four mem)
    have cap : C.card < 3 := by
      apply Nat.lt_of_not_ge
      simpa [P,C,B,Finset.filter_filter] using avoid
    obtain ⟨q,sub,size⟩ := Finset.exists_subset_card_eq (show 2 ≤ D.card by omega)
    have on (p) (hp : p ∈ q) := Finset.mem_filter.mp (sub hp)
    exact ⟨q,fun p hp => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (on p hp).1).1,(on p hp).2⟩,
      size,fun p hp => (Finset.mem_filter.mp (on p hp).1).2⟩
  choose key incl size on using small
  have inj : Function.Injective key := by
    intro L M eq
    obtain ⟨p,q,hp,hq,ne⟩ := Finset.one_lt_card_iff.mp (show 1 < (key L).card by rw [size]; decide)
    have left := OMA.R_Erdos101_erdos_101_R1.line_through (four (Finset.mem_filter.mp L.property).1)
      (on L p hp) (on L q hq) ne
    have right := OMA.R_Erdos101_erdos_101_R1.line_through (four (Finset.mem_filter.mp M.property).1)
      (on M p (eq ▸ hp)) (on M q (eq ▸ hq)) ne
    exact Subtype.ext (left.symm.trans right)
  have keysub : bad.attach.image key ⊆ off.powersetCard 2 := by
    intro q hq
    obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_powersetCard.mpr ⟨incl L,size L⟩
  have count := Finset.card_le_card keysub
  rw [Finset.card_image_of_injective _ inj,Finset.card_attach,Finset.card_powersetCard] at count
  have sum : good.card+bad.card=A.card := Finset.card_filter_add_card_filter_not ..
  have pow := affine_four_lines f e S good (fun L h => ⟨four (Finset.mem_filter.mp h).1,(Finset.mem_filter.mp h).2⟩)
  change ((linesWithPointsFor 4 (S : Set ℝ²)).ncard - off.card.choose 2)^6 ≤ _
  rw [Set.ncard_eq_toFinset_card _ (OMA.R_Erdos101_erdos_101_R1.four_lines_finite S)]
  change (A.card-off.card.choose 2)^6 ≤ _
  exact (Nat.pow_le_pow_left (show A.card-off.card.choose 2 ≤ good.card by omega) 6).trans pow

open Filter Asymptotics

/-- The Erdős little-o conclusion for configurations with a sublinear number
of exceptions. The graph and affine coordinate system can change at every n. -/
theorem littleO_near_quartics (S : ℕ → Finset ℝ²) (f : ℕ → Quartic) (e : ℕ → ℝ² ≃ᵃ[ℝ] ℝ²)
    (size : ∀ n, (S n).card ≤ n)
    (exceptions : (fun n => (((S n).filter (fun p => e n p 1 ≠ (f n).value (e n p 0))).card : ℝ))
      =o[atTop] (fun n => (n : ℝ))) :
    (fun n => ((linesWithPointsFor 4 (S n : Set ℝ²)).ncard : ℝ))
      =o[atTop] (fun n => (n : ℝ)^2) := by
  apply IsLittleO.of_bound
  intro ε positive
  let r := ε/2
  have rp : 0 < r := by dsimp [r]; positivity
  obtain ⟨N,hN⟩ := exists_nat_gt ((powerConstant : ℝ)/r^6)
  filter_upwards [eventually_ge_atTop N, exceptions.bound rp] with n hn hs
  let s := ((S n).filter (fun p => e n p 1 ≠ (f n).value (e n p 0))).card
  let q := (linesWithPointsFor 4 (S n : Set ℝ²)).ncard
  change ‖(s : ℝ)‖ ≤ r*‖(n : ℝ)‖ at hs
  change ‖(q : ℝ)‖ ≤ ε*‖(n : ℝ)^2‖
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (Nat.cast_nonneg _)] at hs
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (sq_nonneg _)]
  have sn : s ≤ n := (Finset.card_filter_le ..).trans (size n)
  have small : (s.choose 2 : ℝ) ≤ r*(n : ℝ)^2 := calc
    (s.choose 2 : ℝ) ≤ (s : ℝ)^2 := by exact_mod_cast Nat.choose_le_pow s 2
    _ ≤ (r*(n : ℝ))*n := by
      have h := mul_le_mul hs (show (s : ℝ) ≤ n by exact_mod_cast sn) (Nat.cast_nonneg s) (by positivity)
      simpa only [pow_two] using h
    _ = _ := by ring
  have coeff : (powerConstant : ℝ) ≤ r^6*(n : ℝ) := by
    have a := (div_lt_iff₀ (pow_pos rp 6)).mp hN
    have b : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith only [a, mul_le_mul_of_nonneg_left b (pow_nonneg rp.le 6)]
  have localBound : (q-s.choose 2)^6 ≤ powerConstant*n^11 :=
    (near_quartic (f n) (e n) (S n)).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (size n) _))
  let d := q-s.choose 2
  have dsmall : (d : ℝ) ≤ r*(n : ℝ)^2 := by
    apply le_of_not_gt
    intro fail
    have up := pow_lt_pow_left₀ fail (by positivity) (by decide : 6 ≠ 0)
    have down : (d : ℝ)^6 ≤ (powerConstant : ℝ)*(n : ℝ)^11 := by exact_mod_cast localBound
    nlinarith only [up,down,mul_le_mul_of_nonneg_right coeff (show 0 ≤ (n : ℝ)^11 by positivity)]
  have add : q ≤ d+s.choose 2 := by dsimp [d]; omega
  have total : (q : ℝ) ≤ d+(s.choose 2 : ℝ) := by exact_mod_cast add
  dsimp only [r] at dsmall small
  linarith only [total,dsmall,small]

end Erdos101QuarticLines
