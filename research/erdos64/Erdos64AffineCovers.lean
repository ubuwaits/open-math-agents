import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic

/-!
# Short cycles in affine covers of the tetrahedron

Each vertex of the tetrahedron has copies indexed by an arbitrary abelian
group. The three edges from vertex zero preserve the index. On each remaining
edge a sheet may be translated or negated and translated. Bits 0, 1 and 2 of
the mask select negation on edges 12, 23 and 31, respectively.

The certificate follows projected cycles starting on sheet zero. A repeated
vertex gives an integer relation among the three shifts, which leads to a
new case. All implications between relations use explicit integer linear
combinations and therefore also hold in groups with torsion. The last section
allows all nonzero scalar multipliers over a division ring and, more
generally, affine actions with invertible differences from the identity.
-/

namespace Erdos64AffineCovers

open SimpleGraph Function

abbrev Color := Fin 4
abbrev Voltage := ℤ × ℤ × ℤ
abbrev Position := Color × Voltage

private def flipped (mask : Fin 8) (i j : Color) : Bool :=
  match i.val, j.val with
  | 1, 2 | 2, 1 => mask.val.testBit 0
  | 2, 3 | 3, 2 => mask.val.testBit 1
  | 3, 1 | 1, 3 => mask.val.testBit 2
  | _, _ => false

/-- Negate a sheet coordinate exactly when the edge reverses its sign. -/
def orient {B : Type*} [Neg B] (flip : Bool) (x : B) : B :=
  if flip then -x else x

private def displacement (mask : Fin 8) (i j : Color) : Voltage :=
  match i.val, j.val with
  | 1, 2 => (1,0,0)
  | 2, 3 => (0,1,0)
  | 3, 1 => (0,0,1)
  | 2, 1 => orient (flipped mask i j) (-1,0,0)
  | 3, 2 => orient (flipped mask i j) (0,-1,0)
  | 1, 3 => orient (flipped mask i j) (0,0,-1)
  | _, _ => 0

variable {A : Type*} [AddCommGroup A]

private def normalGraph (mask : Fin 8) (φ : Voltage →+ A) : SimpleGraph (Color × A) :=
  SimpleGraph.fromRel fun u v : Color × A =>
    u.1 ≠ v.1 ∧ v.2 = orient (flipped mask u.1 v.1) u.2 + φ (displacement mask u.1 v.1)

def HasShortCycle {X : Type*} (G : SimpleGraph X) : Prop :=
  cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G

private def Vanishes (φ : Voltage →+ A) (rows : List Voltage) : Prop :=
  ∀ v ∈ rows, φ v = 0

private theorem addRelation {φ : Voltage →+ A} {rows : List Voltage} {d : Voltage}
    (hd : φ d = 0) (h : Vanishes φ rows) : Vanishes φ (d :: rows) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hm
  · exact hd
  · exact h v hm

private def combination : List Voltage → List ℤ → Voltage
  | v :: vs, c :: cs => c • v + combination vs cs
  | _, _ => 0

private theorem consequence {φ : Voltage →+ A} {rows : List Voltage} (h : Vanishes φ rows)
    (coeff : List ℤ) {v : Voltage} (eq : combination rows coeff = v) : φ v = 0 := by
  subst v
  induction rows generalizing coeff with
  | nil => simp [combination]
  | cons r rs ih =>
    cases coeff with
    | nil => simp [combination]
    | cons c cs =>
      have hr : φ r = 0 := h r (by simp)
      have ht : Vanishes φ rs := fun x hx => h x (by simp [hx])
      simp only [combination, map_add, map_zsmul, hr, zsmul_zero, ih ht cs, add_zero]

private theorem consequences {φ : Voltage →+ A} {rows next : List Voltage}
    (h : Vanishes φ rows) (matrix : List (List ℤ))
    (eq : matrix.map (combination rows) = next) : Vanishes φ next := by
  subst next
  intro v hv
  obtain ⟨c, _, hc⟩ := List.mem_map.mp hv
  exact consequence h c hc

private def traceFrom (mask : Fin 8) (u : Color) (p : Voltage) : List Color → List Position
  | [] => [(u,p)]
  | v :: vs =>
      (u,p) :: traceFrom mask v (orient (flipped mask u v) p + displacement mask u v) vs

private def points (mask : Fin 8) {n : ℕ} (word : List Color) (i : Fin n) : Position :=
  let visits := match word with
    | [] => []
    | u :: vs => traceFrom mask u 0 vs
  visits[i.val]?.getD (0,0)

private def residue (mask : Fin 8) (x y : Position) : Voltage :=
  orient (flipped mask x.1 y.1) x.2 + displacement mask x.1 y.1 - y.2

private def distanceVector (x y : Position) : Voltage := y.2 - x.2

private theorem template (mask : Fin 8) {n : ℕ} [NeZero n] (allowed : n = 4 ∨ n = 8 ∨ n = 16)
    (φ : Voltage →+ A) (p : Fin n → Position) (total : Voltage) (collisions : List Voltage)
    (edges : ∀ i, (p i).1 ≠ (p (i + 1)).1 ∧
      (residue mask (p i) (p (i + 1)) = 0 ∨ residue mask (p i) (p (i + 1)) = total))
    (pairs : ∀ i j, i ≠ j → (p i).1 = (p j).1 →
      distanceVector (p i) (p j) ∈ collisions ∨ -distanceVector (p i) (p j) ∈ collisions)
    (closed : φ total = 0)
    (next : ∀ d ∈ collisions, φ d = 0 → HasShortCycle (normalGraph mask φ)) :
    HasShortCycle (normalGraph mask φ) := by
  classical
  let label (i : Fin n) : Color × A := ((p i).1, φ (p i).2)
  by_cases injective : Injective label
  · have edge (i : Fin n) : (normalGraph mask φ).Adj (label i) (label (i + 1)) := by
      obtain ⟨distinct, hz⟩ := edges i
      have h : φ (residue mask (p i) (p (i + 1))) = 0 := by
        rcases hz with hz | hz <;> simp [hz, closed]
      refine ⟨fun eq => distinct (congrArg (fun z : Color × A => z.1) eq),
        Or.inl ⟨distinct, ?_⟩⟩
      have ev (b : Bool) (v : Voltage) : φ (orient b v) = orient b (φ v) := by
        cases b <;> simp [orient]
      exact (sub_eq_zero.mp (by simpa only [residue, map_sub, map_add, ev] using h)).symm
    have contains : cycleGraph n ⊑ normalGraph mask φ := by
      refine ⟨⟨⟨label, ?_⟩, injective⟩⟩
      intro i j hij
      have h1 : 1 < n := by omega
      have h : i-j = 1 ∨ j-i = 1 := by
        simpa only [Fin.ext_iff, Fin.val_one', Nat.mod_eq_of_lt h1] using cycleGraph_adj'.mp hij
      rcases h with h | h
      · have eq : i = j+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h
        simpa only [eq] using (edge j).symm
      · have eq : j = i+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h
        simpa only [eq] using edge i
    rcases allowed with rfl | rfl | rfl
    · exact Or.inl contains
    · exact Or.inr (Or.inl contains)
    · exact Or.inr (Or.inr contains)
  · obtain ⟨i, j, same, ne⟩ := Function.not_injective_iff.mp injective
    have sameColor : (p i).1 = (p j).1 := congrArg (fun z : Color × A => z.1) same
    have samePoint : φ (p i).2 = φ (p j).2 := congrArg (fun z : Color × A => z.2) same
    have dz : φ (distanceVector (p i) (p j)) = 0 := by
      simpa only [distanceVector, map_sub, sub_eq_zero] using samePoint.symm
    rcases pairs i j ne sameColor with h | h
    · exact next _ h dz
    · exact next _ h (by simp [dz])


private theorem mask0 (φ : Voltage →+ A) : HasShortCycle (normalGraph 0 φ) := by
  have case0 (h : Vanishes φ [(0, 1, 0), (0, 0, 1)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 4) (by decide) φ
      (points 0 [0, 1, 3, 2]) (0, -1, -1) []
      (by decide) (by decide) (consequence h [-1, -1] (by decide))
    intro d hd hz
    simp at hd
  have case1 (h : Vanishes φ [(1, 0, 0), (0, 1, 0), (0, 0, 1)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 4) (by decide) φ
      (points 0 [0, 1, 2, 3]) (1, 1, 0) []
      (by decide) (by decide) (consequence h [1, 1, 0] (by decide))
    intro d hd hz
    simp at hd
  have case2 (h : Vanishes φ [(1, -1, 0), (0, 0, 1)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 8) (by decide) φ
      (points 0 [0, 1, 3, 2, 0, 3, 1, 2]) (1, -1, 0) [(0, 1, 0), (0, 1, 1), (1, 0, 1)]
      (by decide) (by decide) (consequence h [1, 0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case1 (consequences (addRelation hz h) [[1, 1, 0], [1, 0, 0], [0, 0, 1]] (by decide))
    · exact case1 (consequences (addRelation hz h) [[1, 1, -1], [1, 0, -1], [0, 0, 1]] (by decide))
    · exact case1 (consequences (addRelation hz h) [[1, 0, -1], [1, -1, -1], [0, 0, 1]] (by decide))
  have case3 (h : Vanishes φ [(1, 0, 0), (0, 0, 1)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 4) (by decide) φ
      (points 0 [0, 2, 1, 3]) (-1, 0, -1) []
      (by decide) (by decide) (consequence h [-1, -1] (by decide))
    intro d hd hz
    simp at hd
  have case4 (h : Vanishes φ [(1, 1, 0), (0, 0, 1)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 4) (by decide) φ
      (points 0 [0, 1, 2, 3]) (1, 1, 0) []
      (by decide) (by decide) (consequence h [1, 0] (by decide))
    intro d hd hz
    simp at hd
  have case5 (h : Vanishes φ [(2, 0, 0), (0, 0, 1)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 8) (by decide) φ
      (points 0 [0, 2, 1, 3, 0, 2, 1, 3]) (-2, 0, -2) [(1, 0, 1)]
      (by decide) (by decide) (consequence h [-1, -2] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case3 (consequences (addRelation hz h) [[1, 0, -1], [0, 0, 1]] (by decide))
  have case6 (h : Vanishes φ [(2, 1, 0), (0, 0, 1)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 8) (by decide) φ
      (points 0 [0, 1, 2, 0, 3, 1, 2, 3]) (2, 1, 1) [(1, 0, 0), (1, 0, 1), (1, 1, 1)]
      (by decide) (by decide) (consequence h [1, 1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case1 (consequences (addRelation hz h) [[1, 0, 0], [-2, 1, 0], [0, 0, 1]] (by decide))
    · exact case1 (consequences (addRelation hz h) [[1, 0, -1], [-2, 1, 2], [0, 0, 1]] (by decide))
    · exact case1 (consequences (addRelation hz h) [[-1, 1, 1], [2, -1, -2], [0, 0, 1]] (by decide))
  have case7 (h : Vanishes φ [(0, 0, 1)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 16) (by decide) φ
      (points 0 [0, 1, 2, 0, 1, 2, 0, 3, 2, 1, 0, 2, 1, 0, 2, 3]) (0, 0, 0) [(0, 1, 0), (1, -1, 0), (1, 0, 0), (1, 1, 0), (2, 0, 0), (2, 1, 0)]
      (by decide) (by decide) (consequence h [0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact case0 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
    · exact case2 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
    · exact case3 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
    · exact case4 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
    · exact case5 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
    · exact case6 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
  have case8 (h : Vanishes φ [(1, 0, -1), (0, 1, 1)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 4) (by decide) φ
      (points 0 [0, 1, 2, 3]) (1, 1, 0) []
      (by decide) (by decide) (consequence h [1, 1] (by decide))
    intro d hd hz
    simp at hd
  have case9 (h : Vanishes φ [(1, 0, -1)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 8) (by decide) φ
      (points 0 [0, 1, 2, 3, 0, 1, 3, 2]) (1, 0, -1) [(0, 0, 1), (1, 1, 0)]
      (by decide) (by decide) (consequence h [1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact case3 (consequences (addRelation hz h) [[1, 1], [1, 0]] (by decide))
    · exact case8 (consequences (addRelation hz h) [[0, 1], [1, -1]] (by decide))
  have case10 (h : Vanishes φ [(1, 0, 0), (0, 0, 2)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 8) (by decide) φ
      (points 0 [0, 2, 1, 3, 0, 2, 1, 3]) (-2, 0, -2) [(1, 0, 1)]
      (by decide) (by decide) (consequence h [-2, -1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case3 (consequences (addRelation hz h) [[0, 1, 0], [1, -1, 0]] (by decide))
  have case11 (h : Vanishes φ [(1, 0, 0), (0, 1, -1)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 8) (by decide) φ
      (points 0 [0, 1, 2, 3, 0, 2, 1, 3]) (0, 1, -1) [(0, 1, 0), (1, 0, 1), (1, 1, 0)]
      (by decide) (by decide) (consequence h [0, 1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case1 (consequences (addRelation hz h) [[0, 1, 0], [1, 0, 0], [1, 0, -1]] (by decide))
    · exact case1 (consequences (addRelation hz h) [[0, 1, 0], [1, -1, 1], [1, -1, 0]] (by decide))
    · exact case1 (consequences (addRelation hz h) [[0, 1, 0], [1, -1, 0], [1, -1, -1]] (by decide))
  have case12 (h : Vanishes φ [(1, 0, 0), (0, 1, 0)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 4) (by decide) φ
      (points 0 [0, 1, 2, 3]) (1, 1, 0) []
      (by decide) (by decide) (consequence h [1, 1] (by decide))
    intro d hd hz
    simp at hd
  have case13 (h : Vanishes φ [(1, 0, 0), (0, 1, 1)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 4) (by decide) φ
      (points 0 [0, 1, 3, 2]) (0, -1, -1) []
      (by decide) (by decide) (consequence h [0, -1] (by decide))
    intro d hd hz
    simp at hd
  have case14 (h : Vanishes φ [(1, 0, 0), (0, 1, 2)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 8) (by decide) φ
      (points 0 [0, 1, 3, 0, 2, 1, 3, 2]) (-1, -1, -2) [(0, 0, 1), (1, 0, 1), (1, 1, 1)]
      (by decide) (by decide) (consequence h [-1, -1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case1 (consequences (addRelation hz h) [[0, 1, 0], [-2, 0, 1], [1, 0, 0]] (by decide))
    · exact case1 (consequences (addRelation hz h) [[0, 1, 0], [-2, 2, 1], [1, -1, 0]] (by decide))
    · exact case1 (consequences (addRelation hz h) [[0, 1, 0], [2, -2, -1], [-1, 1, 1]] (by decide))
  have case15 (h : Vanishes φ [(1, 0, 0)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 16) (by decide) φ
      (points 0 [0, 1, 2, 3, 1, 0, 3, 1, 0, 3, 2, 1, 3, 0, 1, 3]) (0, 0, 0) [(0, 0, 1), (0, 0, 2), (1, 1, -1), (1, 1, 0), (1, 1, 1), (1, 1, 2)]
      (by decide) (by decide) (consequence h [0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact case3 (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
    · exact case10 (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
    · exact case11 (consequences (addRelation hz h) [[0, 1], [1, -1]] (by decide))
    · exact case12 (consequences (addRelation hz h) [[0, 1], [1, -1]] (by decide))
    · exact case13 (consequences (addRelation hz h) [[0, 1], [1, -1]] (by decide))
    · exact case14 (consequences (addRelation hz h) [[0, 1], [1, -1]] (by decide))
  have case16 (h : Vanishes φ [(1, 0, 1)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 4) (by decide) φ
      (points 0 [0, 2, 1, 3]) (-1, 0, -1) []
      (by decide) (by decide) (consequence h [-1] (by decide))
    intro d hd hz
    simp at hd
  have case17 (h : Vanishes φ [(1, 0, 1), (0, 0, 2)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 4) (by decide) φ
      (points 0 [0, 2, 1, 3]) (-1, 0, -1) []
      (by decide) (by decide) (consequence h [-1, 0] (by decide))
    intro d hd hz
    simp at hd
  have case18 (h : Vanishes φ [(2, 0, 0), (0, 0, 2)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 8) (by decide) φ
      (points 0 [0, 2, 1, 3, 0, 2, 1, 3]) (-2, 0, -2) [(1, 0, 1)]
      (by decide) (by decide) (consequence h [-1, -1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case17 (consequences (addRelation hz h) [[1, 0, 0], [2, -1, 0]] (by decide))
  have case19 (h : Vanishes φ [(1, 0, 2), (0, 0, 4)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 16) (by decide) φ
      (points 0 [0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 1, 3]) (-4, 0, -4) [(1, 0, 1), (2, 0, 2), (3, 0, 3)]
      (by decide) (by decide) (consequence h [-4, 1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case3 (consequences (addRelation hz h) [[2, -1, 0], [-1, 1, 0]] (by decide))
    · exact case10 (consequences (addRelation hz h) [[1, -1, 0], [-1, 2, 0]] (by decide))
    · exact case3 (consequences (addRelation hz h) [[-2, 7, -2], [1, -3, 1]] (by decide))
  have case20 (h : Vanishes φ [(2, 0, 0)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 16) (by decide) φ
      (points 0 [0, 1, 2, 0, 3, 1, 0, 3, 1, 0, 2, 1, 3, 0, 1, 3]) (0, 0, 0) [(0, 0, 1), (0, 0, 2), (1, 0, -1), (1, 0, 0), (1, 0, 1), (1, 0, 2)]
      (by decide) (by decide) (consequence h [0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact case5 (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
    · exact case18 (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
    · exact case17 (consequences (addRelation hz h) [[-1, 1], [-2, 1]] (by decide))
    · exact case15 (consequences (addRelation hz h) [[1, 0]] (by decide))
    · exact case17 (consequences (addRelation hz h) [[1, 0], [2, -1]] (by decide))
    · exact case19 (consequences (addRelation hz h) [[1, 0], [2, -1]] (by decide))
  have case21 (h : Vanishes φ [(2, 0, 1), (0, 0, 2)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 16) (by decide) φ
      (points 0 [0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 1, 3]) (-4, 0, -4) [(1, 0, 1), (2, 0, 2), (3, 0, 3)]
      (by decide) (by decide) (consequence h [-2, -1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case3 (consequences (addRelation hz h) [[-1, 1, 0], [2, -1, 0]] (by decide))
    · exact case5 (consequences (addRelation hz h) [[-1, 2, 0], [1, -1, 0]] (by decide))
    · exact case3 (consequences (addRelation hz h) [[5, -7, -4], [-2, 3, 2]] (by decide))
  have case22 (h : Vanishes φ [(1, 0, 2), (0, 1, 1), (0, 0, 3)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 4) (by decide) φ
      (points 0 [0, 1, 2, 3]) (1, 1, 0) []
      (by decide) (by decide) (consequence h [1, 1, -1] (by decide))
    intro d hd hz
    simp at hd
  have case23 (h : Vanishes φ [(1, 0, 2), (0, 0, 3)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 8) (by decide) φ
      (points 0 [0, 1, 2, 3, 0, 1, 3, 2]) (1, 0, -1) [(0, 0, 1), (1, 1, 0)]
      (by decide) (by decide) (consequence h [1, -1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact case3 (consequences (addRelation hz h) [[-2, 1, 0], [1, 0, 0]] (by decide))
    · exact case22 (consequences (addRelation hz h) [[0, 1, 0], [1, -1, 1], [0, 0, 1]] (by decide))
  have case24 (h : Vanishes φ [(2, 0, 1)]) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 16) (by decide) φ
      (points 0 [0, 1, 2, 0, 3, 1, 0, 3, 1, 0, 2, 1, 3, 0, 1, 3]) (0, 0, 0) [(0, 0, 1), (0, 0, 2), (1, 0, -1), (1, 0, 0), (1, 0, 1), (1, 0, 2)]
      (by decide) (by decide) (consequence h [0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact case5 (consequences (addRelation hz h) [[-1, 1], [1, 0]] (by decide))
    · exact case21 (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
    · exact case23 (consequences (addRelation hz h) [[-1, 1], [-2, 1]] (by decide))
    · exact case3 (consequences (addRelation hz h) [[1, 0], [-2, 1]] (by decide))
    · exact case3 (consequences (addRelation hz h) [[-1, 1], [2, -1]] (by decide))
    · exact case23 (consequences (addRelation hz h) [[1, 0], [2, -1]] (by decide))
  have case25 (h : Vanishes φ []) : HasShortCycle (normalGraph 0 φ) := by
    apply template 0 (n := 16) (by decide) φ
      (points 0 [0, 1, 2, 0, 1, 2, 0, 3, 1, 0, 2, 1, 0, 2, 1, 3]) (0, 0, 0) [(0, 0, 1), (1, 0, -1), (1, 0, 0), (1, 0, 1), (2, 0, 0), (2, 0, 1)]
      (by decide) (by decide) (consequence h [] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact case7 (consequences (addRelation hz h) [[1]] (by decide))
    · exact case9 (consequences (addRelation hz h) [[1]] (by decide))
    · exact case15 (consequences (addRelation hz h) [[1]] (by decide))
    · exact case16 (consequences (addRelation hz h) [[1]] (by decide))
    · exact case20 (consequences (addRelation hz h) [[1]] (by decide))
    · exact case24 (consequences (addRelation hz h) [[1]] (by decide))
  exact case25 (by simp [Vanishes])

private theorem mask1 (φ : Voltage →+ A) : HasShortCycle (normalGraph 1 φ) := by
  have case0 (h : Vanishes φ [(1, 1, 0)]) : HasShortCycle (normalGraph 1 φ) := by
    apply template 1 (n := 4) (by decide) φ
      (points 1 [0, 1, 2, 3]) (1, 1, 0) []
      (by decide) (by decide) (consequence h [1] (by decide))
    intro d hd hz
    simp at hd
  have case1 (h : Vanishes φ []) : HasShortCycle (normalGraph 1 φ) := by
    apply template 1 (n := 8) (by decide) φ
      (points 1 [0, 1, 2, 3, 0, 1, 2, 3]) (0, 0, 0) [(1, 1, 0)]
      (by decide) (by decide) (consequence h [] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case0 (consequences (addRelation hz h) [[1]] (by decide))
  exact case1 (by simp [Vanishes])

private theorem mask2 (φ : Voltage →+ A) : HasShortCycle (normalGraph 2 φ) := by
  have case0 (h : Vanishes φ [(1, -1, 0)]) : HasShortCycle (normalGraph 2 φ) := by
    apply template 2 (n := 4) (by decide) φ
      (points 2 [0, 1, 2, 3]) (-1, 1, 0) []
      (by decide) (by decide) (consequence h [-1] (by decide))
    intro d hd hz
    simp at hd
  have case1 (h : Vanishes φ []) : HasShortCycle (normalGraph 2 φ) := by
    apply template 2 (n := 8) (by decide) φ
      (points 2 [0, 1, 2, 3, 0, 1, 2, 3]) (0, 0, 0) [(1, -1, 0)]
      (by decide) (by decide) (consequence h [] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case0 (consequences (addRelation hz h) [[1]] (by decide))
  exact case1 (by simp [Vanishes])

private theorem mask3 (φ : Voltage →+ A) : HasShortCycle (normalGraph 3 φ) := by
  have case0 (h : Vanishes φ [(0, 1, 1)]) : HasShortCycle (normalGraph 3 φ) := by
    apply template 3 (n := 4) (by decide) φ
      (points 3 [0, 1, 3, 2]) (0, 1, 1) []
      (by decide) (by decide) (consequence h [1] (by decide))
    intro d hd hz
    simp at hd
  have case1 (h : Vanishes φ []) : HasShortCycle (normalGraph 3 φ) := by
    apply template 3 (n := 8) (by decide) φ
      (points 3 [0, 1, 3, 2, 0, 1, 3, 2]) (0, 0, 0) [(0, 1, 1)]
      (by decide) (by decide) (consequence h [] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case0 (consequences (addRelation hz h) [[1]] (by decide))
  exact case1 (by simp [Vanishes])

private theorem mask4 (φ : Voltage →+ A) : HasShortCycle (normalGraph 4 φ) := by
  have case0 (h : Vanishes φ [(0, 1, -1)]) : HasShortCycle (normalGraph 4 φ) := by
    apply template 4 (n := 4) (by decide) φ
      (points 4 [0, 1, 3, 2]) (0, -1, 1) []
      (by decide) (by decide) (consequence h [-1] (by decide))
    intro d hd hz
    simp at hd
  have case1 (h : Vanishes φ []) : HasShortCycle (normalGraph 4 φ) := by
    apply template 4 (n := 8) (by decide) φ
      (points 4 [0, 1, 3, 2, 0, 1, 3, 2]) (0, 0, 0) [(0, 1, -1)]
      (by decide) (by decide) (consequence h [] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case0 (consequences (addRelation hz h) [[1]] (by decide))
  exact case1 (by simp [Vanishes])

private theorem mask5 (φ : Voltage →+ A) : HasShortCycle (normalGraph 5 φ) := by
  have case0 (h : Vanishes φ [(1, 1, 0)]) : HasShortCycle (normalGraph 5 φ) := by
    apply template 5 (n := 4) (by decide) φ
      (points 5 [0, 1, 2, 3]) (1, 1, 0) []
      (by decide) (by decide) (consequence h [1] (by decide))
    intro d hd hz
    simp at hd
  have case1 (h : Vanishes φ []) : HasShortCycle (normalGraph 5 φ) := by
    apply template 5 (n := 8) (by decide) φ
      (points 5 [0, 1, 2, 3, 0, 1, 2, 3]) (0, 0, 0) [(1, 1, 0)]
      (by decide) (by decide) (consequence h [] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case0 (consequences (addRelation hz h) [[1]] (by decide))
  exact case1 (by simp [Vanishes])

private theorem mask6 (φ : Voltage →+ A) : HasShortCycle (normalGraph 6 φ) := by
  have case0 (h : Vanishes φ [(1, -1, 0)]) : HasShortCycle (normalGraph 6 φ) := by
    apply template 6 (n := 4) (by decide) φ
      (points 6 [0, 1, 2, 3]) (-1, 1, 0) []
      (by decide) (by decide) (consequence h [-1] (by decide))
    intro d hd hz
    simp at hd
  have case1 (h : Vanishes φ []) : HasShortCycle (normalGraph 6 φ) := by
    apply template 6 (n := 8) (by decide) φ
      (points 6 [0, 1, 2, 3, 0, 1, 2, 3]) (0, 0, 0) [(1, -1, 0)]
      (by decide) (by decide) (consequence h [] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case0 (consequences (addRelation hz h) [[1]] (by decide))
  exact case1 (by simp [Vanishes])

private theorem mask7 (φ : Voltage →+ A) : HasShortCycle (normalGraph 7 φ) := by
  have case0 (h : Vanishes φ [(0, 1, 0), (0, 0, 1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 4) (by decide) φ
      (points 7 [0, 1, 3, 2]) (0, 1, -1) []
      (by decide) (by decide) (consequence h [1, -1] (by decide))
    intro d hd hz
    simp at hd
  have case1 (h : Vanishes φ [(0, 2, 0), (0, 0, 1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 8) (by decide) φ
      (points 7 [0, 1, 3, 2, 0, 1, 3, 2]) (0, 2, -2) [(0, 1, -1)]
      (by decide) (by decide) (consequence h [1, -2] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case0 (consequences (addRelation hz h) [[1, 0, 1], [0, 0, 1]] (by decide))
  have case2 (h : Vanishes φ [(1, 0, 0), (0, 1, 0), (0, 0, 1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 4) (by decide) φ
      (points 7 [0, 1, 2, 3]) (-1, 1, 0) []
      (by decide) (by decide) (consequence h [-1, 1, 0] (by decide))
    intro d hd hz
    simp at hd
  have case3 (h : Vanishes φ [(1, -2, 0), (0, 0, 1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 8) (by decide) φ
      (points 7 [0, 1, 2, 3, 1, 0, 2, 3]) (-1, 2, -1) [(0, 1, -1), (1, -1, 1)]
      (by decide) (by decide) (consequence h [-1, -1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact case2 (consequences (addRelation hz h) [[2, 1, 2], [1, 0, 1], [0, 0, 1]] (by decide))
    · exact case2 (consequences (addRelation hz h) [[2, -1, -2], [1, -1, -1], [0, 0, 1]] (by decide))
  have case4 (h : Vanishes φ [(1, -1, 0), (0, 0, 1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 4) (by decide) φ
      (points 7 [0, 1, 2, 3]) (-1, 1, 0) []
      (by decide) (by decide) (consequence h [-1, 0] (by decide))
    intro d hd hz
    simp at hd
  have case5 (h : Vanishes φ [(1, 0, 0), (0, 0, 1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 4) (by decide) φ
      (points 7 [0, 2, 1, 3]) (-1, 0, 1) []
      (by decide) (by decide) (consequence h [-1, 1] (by decide))
    intro d hd hz
    simp at hd
  have case6 (h : Vanishes φ [(1, 1, 0), (0, 0, 1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 8) (by decide) φ
      (points 7 [0, 1, 3, 2, 0, 3, 1, 2]) (1, 1, -2) [(0, 1, -2), (0, 1, -1), (1, 0, -1)]
      (by decide) (by decide) (consequence h [1, -2] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case2 (consequences (addRelation hz h) [[-1, 1, -2], [1, 0, 2], [0, 0, 1]] (by decide))
    · exact case2 (consequences (addRelation hz h) [[-1, 1, -1], [1, 0, 1], [0, 0, 1]] (by decide))
    · exact case2 (consequences (addRelation hz h) [[1, 0, 1], [-1, 1, -1], [0, 0, 1]] (by decide))
  have case7 (h : Vanishes φ [(0, 0, 1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 16) (by decide) φ
      (points 7 [0, 1, 2, 0, 1, 2, 3, 1, 0, 3, 1, 2, 0, 1, 2, 3]) (0, 0, 0) [(0, 1, -1), (0, 1, 0), (0, 2, -1), (1, -2, 0), (1, -1, 0), (1, 0, -1), (1, 0, 0), (1, 1, -1)]
      (by decide) (by decide) (consequence h [0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact case0 (consequences (addRelation hz h) [[1, 1], [0, 1]] (by decide))
    · exact case0 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
    · exact case1 (consequences (addRelation hz h) [[1, 1], [0, 1]] (by decide))
    · exact case3 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
    · exact case4 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
    · exact case5 (consequences (addRelation hz h) [[1, 1], [0, 1]] (by decide))
    · exact case5 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
    · exact case6 (consequences (addRelation hz h) [[1, 1], [0, 1]] (by decide))
  have case8 (h : Vanishes φ [(0, 1, -1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 4) (by decide) φ
      (points 7 [0, 1, 3, 2]) (0, 1, -1) []
      (by decide) (by decide) (consequence h [1] (by decide))
    intro d hd hz
    simp at hd
  have case9 (h : Vanishes φ [(1, 0, 0), (0, 1, 0)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 4) (by decide) φ
      (points 7 [0, 1, 2, 3]) (-1, 1, 0) []
      (by decide) (by decide) (consequence h [-1, 1] (by decide))
    intro d hd hz
    simp at hd
  have case10 (h : Vanishes φ [(1, 0, -1), (0, 1, 0)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 4) (by decide) φ
      (points 7 [0, 2, 1, 3]) (-1, 0, 1) []
      (by decide) (by decide) (consequence h [-1, 0] (by decide))
    intro d hd hz
    simp at hd
  have case11 (h : Vanishes φ [(1, 0, -2), (0, 1, 0)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 8) (by decide) φ
      (points 7 [0, 1, 3, 0, 2, 1, 3, 2]) (1, 1, -2) [(0, 0, 1), (1, 0, -1), (1, 1, -3)]
      (by decide) (by decide) (consequence h [1, 1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case2 (consequences (addRelation hz h) [[2, 1, 0], [0, 0, 1], [1, 0, 0]] (by decide))
    · exact case2 (consequences (addRelation hz h) [[2, -1, 0], [0, 0, 1], [1, -1, 0]] (by decide))
    · exact case2 (consequences (addRelation hz h) [[-2, 3, 2], [0, 0, 1], [-1, 1, 1]] (by decide))
  have case12 (h : Vanishes φ [(2, 0, -1), (0, 1, 0)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 8) (by decide) φ
      (points 7 [0, 1, 2, 0, 3, 1, 2, 3]) (-2, 1, 1) [(1, 0, -1), (1, 0, 0), (3, -1, -1)]
      (by decide) (by decide) (consequence h [-1, 1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case2 (consequences (addRelation hz h) [[-1, 1, 0], [0, 0, 1], [-2, 1, 0]] (by decide))
    · exact case2 (consequences (addRelation hz h) [[1, 0, 0], [0, 0, 1], [2, -1, 0]] (by decide))
    · exact case2 (consequences (addRelation hz h) [[1, -1, 1], [0, 0, 1], [2, -3, 2]] (by decide))
  have case13 (h : Vanishes φ [(2, 0, -2), (0, 1, 0)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 8) (by decide) φ
      (points 7 [0, 2, 1, 3, 0, 2, 1, 3]) (-2, 0, 2) [(1, 0, -1)]
      (by decide) (by decide) (consequence h [-1, 0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case10 (consequences (addRelation hz h) [[1, 0, 0], [0, 0, 1]] (by decide))
  have case14 (h : Vanishes φ [(0, 1, 0)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 16) (by decide) φ
      (points 7 [0, 1, 2, 0, 1, 3, 0, 2, 3, 0, 1, 2, 0, 1, 3, 2]) (0, 0, 0) [(0, 1, -1), (1, -1, 0), (1, 0, -1), (1, 0, 0), (1, 1, -1), (1, 2, -2), (2, 0, -1), (2, 1, -2)]
      (by decide) (by decide) (consequence h [0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact case0 (consequences (addRelation hz h) [[0, 1], [-1, 1]] (by decide))
    · exact case9 (consequences (addRelation hz h) [[1, 1], [0, 1]] (by decide))
    · exact case10 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
    · exact case9 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
    · exact case10 (consequences (addRelation hz h) [[1, -1], [0, 1]] (by decide))
    · exact case11 (consequences (addRelation hz h) [[1, -2], [0, 1]] (by decide))
    · exact case12 (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
    · exact case13 (consequences (addRelation hz h) [[1, -1], [0, 1]] (by decide))
  have case15 (h : Vanishes φ [(1, 0, -2), (0, 1, -1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 4) (by decide) φ
      (points 7 [0, 1, 3, 2]) (0, 1, -1) []
      (by decide) (by decide) (consequence h [0, 1] (by decide))
    intro d hd hz
    simp at hd
  have case16 (h : Vanishes φ [(1, 0, -1), (0, 2, -1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 4) (by decide) φ
      (points 7 [0, 2, 1, 3]) (-1, 0, 1) []
      (by decide) (by decide) (consequence h [-1, 0] (by decide))
    intro d hd hz
    simp at hd
  have case17 (h : Vanishes φ [(1, 0, 0), (0, 2, 0)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 8) (by decide) φ
      (points 7 [0, 1, 2, 3, 0, 1, 2, 3]) (-2, 2, 0) [(1, -1, 0)]
      (by decide) (by decide) (consequence h [-2, 1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case9 (consequences (addRelation hz h) [[0, 1, 0], [-1, 1, 0]] (by decide))
  have case18 (h : Vanishes φ [(1, 0, 0), (0, 1, 1), (0, 0, 2)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 4) (by decide) φ
      (points 7 [0, 1, 3, 2]) (0, 1, -1) []
      (by decide) (by decide) (consequence h [0, 1, -1] (by decide))
    intro d hd hz
    simp at hd
  have case19 (h : Vanishes φ [(1, 1, -1), (0, 3, -1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 8) (by decide) φ
      (points 7 [0, 1, 2, 0, 3, 1, 2, 3]) (-2, 1, 1) [(1, 0, -1), (1, 0, 0), (3, -1, -1)]
      (by decide) (by decide) (consequence h [-2, 1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case2 (consequences (addRelation hz h) [[-2, 3, -1], [-1, 1, 0], [-3, 3, -1]] (by decide))
    · exact case18 (consequences (addRelation hz h) [[1, 0, 0], [2, -2, 1], [3, -3, 1]] (by decide))
    · exact case18 (consequences (addRelation hz h) [[1, -2, 1], [2, -6, 3], [3, -9, 4]] (by decide))
  have case20 (h : Vanishes φ [(1, 2, -2), (0, 4, -2)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 8) (by decide) φ
      (points 7 [0, 2, 1, 3, 0, 2, 1, 3]) (-2, 0, 2) [(1, 0, -1)]
      (by decide) (by decide) (consequence h [-2, 1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case16 (consequences (addRelation hz h) [[1, 0, 0], [-1, 1, 0]] (by decide))
  have case21 (h : Vanishes φ [(1, -2, 0)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 16) (by decide) φ
      (points 7 [0, 1, 2, 0, 1, 3, 2, 0, 1, 2, 0, 3, 1, 0, 2, 3]) (0, 0, 0) [(0, 1, -1), (0, 1, 0), (0, 2, -1), (1, -1, 0), (1, 0, -1), (1, 0, 0), (1, 1, -1), (1, 2, -2)]
      (by decide) (by decide) (consequence h [0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact case15 (consequences (addRelation hz h) [[2, 1], [1, 0]] (by decide))
    · exact case9 (consequences (addRelation hz h) [[2, 1], [1, 0]] (by decide))
    · exact case16 (consequences (addRelation hz h) [[1, 1], [1, 0]] (by decide))
    · exact case9 (consequences (addRelation hz h) [[2, -1], [1, -1]] (by decide))
    · exact case16 (consequences (addRelation hz h) [[1, 0], [1, -1]] (by decide))
    · exact case17 (consequences (addRelation hz h) [[1, 0], [1, -1]] (by decide))
    · exact case19 (consequences (addRelation hz h) [[1, 0], [1, -1]] (by decide))
    · exact case20 (consequences (addRelation hz h) [[1, 0], [1, -1]] (by decide))
  have case22 (h : Vanishes φ [(1, 1, 0), (0, 2, 0), (0, 0, 1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 4) (by decide) φ
      (points 7 [0, 1, 2, 3]) (-1, 1, 0) []
      (by decide) (by decide) (consequence h [-1, 1, 0] (by decide))
    intro d hd hz
    simp at hd
  have case23 (h : Vanishes φ [(1, 1, -2), (0, 2, -1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 8) (by decide) φ
      (points 7 [0, 1, 3, 0, 2, 1, 3, 2]) (1, 1, -2) [(0, 0, 1), (1, 0, -1), (1, 1, -3)]
      (by decide) (by decide) (consequence h [1, 0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case22 (consequences (addRelation hz h) [[2, 1, 0], [1, 0, 1], [1, 0, 0]] (by decide))
    · exact case2 (consequences (addRelation hz h) [[3, -2, 1], [1, -1, 1], [2, -2, 1]] (by decide))
    · exact case22 (consequences (addRelation hz h) [[-2, 3, 0], [-1, 1, 1], [-1, 1, 0]] (by decide))
  have case24 (h : Vanishes φ [(1, 0, 0), (0, 1, 1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 8) (by decide) φ
      (points 7 [0, 1, 2, 3, 0, 2, 1, 3]) (-2, 1, 1) [(1, -1, 0), (1, 0, -1), (2, -1, 0)]
      (by decide) (by decide) (consequence h [-2, 1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case2 (consequences (addRelation hz h) [[0, 1, 0], [-1, 1, 0], [1, -1, 1]] (by decide))
    · exact case2 (consequences (addRelation hz h) [[0, 1, 0], [1, -1, 1], [-1, 1, 0]] (by decide))
    · exact case2 (consequences (addRelation hz h) [[0, 1, 0], [-1, 2, 0], [1, -2, 1]] (by decide))
  have case25 (h : Vanishes φ [(1, 1, -1), (0, 2, 0)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 8) (by decide) φ
      (points 7 [0, 2, 1, 3, 0, 2, 1, 3]) (-2, 0, 2) [(1, 0, -1)]
      (by decide) (by decide) (consequence h [-2, 1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case10 (consequences (addRelation hz h) [[1, 0, 0], [-1, 1, 0]] (by decide))
  have case26 (h : Vanishes φ [(1, -1, -1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 16) (by decide) φ
      (points 7 [0, 1, 2, 0, 1, 2, 3, 1, 0, 3, 1, 2, 0, 1, 2, 3]) (0, 0, 0) [(0, 1, -1), (0, 1, 0), (0, 2, -1), (1, -2, 0), (1, -1, 0), (1, 0, -1), (1, 0, 0), (1, 1, -1)]
      (by decide) (by decide) (consequence h [0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact case15 (consequences (addRelation hz h) [[1, 1], [1, 0]] (by decide))
    · exact case10 (consequences (addRelation hz h) [[1, 1], [1, 0]] (by decide))
    · exact case23 (consequences (addRelation hz h) [[1, 1], [1, 0]] (by decide))
    · exact case15 (consequences (addRelation hz h) [[-1, 2], [-1, 1]] (by decide))
    · exact case4 (consequences (addRelation hz h) [[1, 0], [1, -1]] (by decide))
    · exact case10 (consequences (addRelation hz h) [[1, 0], [1, -1]] (by decide))
    · exact case24 (consequences (addRelation hz h) [[1, 0], [1, -1]] (by decide))
    · exact case25 (consequences (addRelation hz h) [[1, 0], [1, -1]] (by decide))
  have case27 (h : Vanishes φ [(1, -1, 0)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 4) (by decide) φ
      (points 7 [0, 1, 2, 3]) (-1, 1, 0) []
      (by decide) (by decide) (consequence h [-1] (by decide))
    intro d hd hz
    simp at hd
  have case28 (h : Vanishes φ [(1, 0, -1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 4) (by decide) φ
      (points 7 [0, 2, 1, 3]) (-1, 0, 1) []
      (by decide) (by decide) (consequence h [-1] (by decide))
    intro d hd hz
    simp at hd
  have case29 (h : Vanishes φ [(1, 0, 0), (0, 1, -2)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 8) (by decide) φ
      (points 7 [0, 1, 3, 0, 2, 1, 3, 2]) (1, 1, -2) [(0, 0, 1), (1, 0, -1), (1, 1, -3)]
      (by decide) (by decide) (consequence h [1, 1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact case2 (consequences (addRelation hz h) [[0, 1, 0], [2, 0, 1], [1, 0, 0]] (by decide))
    · exact case2 (consequences (addRelation hz h) [[0, 1, 0], [-2, 2, 1], [-1, 1, 0]] (by decide))
    · exact case2 (consequences (addRelation hz h) [[0, 1, 0], [-2, 2, 3], [-1, 1, 1]] (by decide))
  have case30 (h : Vanishes φ [(1, 0, 0), (0, 1, -1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 4) (by decide) φ
      (points 7 [0, 1, 3, 2]) (0, 1, -1) []
      (by decide) (by decide) (consequence h [0, 1] (by decide))
    intro d hd hz
    simp at hd
  have case31 (h : Vanishes φ [(1, 0, 0), (0, 2, 0), (0, 0, 1)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 4) (by decide) φ
      (points 7 [0, 2, 1, 3]) (-1, 0, 1) []
      (by decide) (by decide) (consequence h [-1, 0, 1] (by decide))
    intro d hd hz
    simp at hd
  have case32 (h : Vanishes φ [(1, 0, 0), (0, 1, 0), (0, 0, 3)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 4) (by decide) φ
      (points 7 [0, 1, 2, 3]) (-1, 1, 0) []
      (by decide) (by decide) (consequence h [-1, 1, 0] (by decide))
    intro d hd hz
    simp at hd
  have case33 (h : Vanishes φ [(1, 0, 0), (0, 2, 1), (0, 0, 2)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 8) (by decide) φ
      (points 7 [0, 2, 1, 3, 0, 2, 1, 3]) (-2, 0, 2) [(1, 0, -1)]
      (by decide) (by decide) (consequence h [-2, 0, 1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case31 (consequences (addRelation hz h) [[0, 1, 0, 0], [1, -1, 1, 0], [-1, 1, 0, 0]] (by decide))
  have case34 (h : Vanishes φ [(1, 0, 0), (0, 2, -3)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 16) (by decide) φ
      (points 7 [0, 1, 2, 3, 1, 2, 0, 3, 1, 2, 3, 1, 0, 2, 1, 3]) (0, 0, 0) [(0, 0, 1), (0, 1, -2), (0, 1, -1), (1, -1, 0), (1, -1, 1), (1, 0, -2), (1, 0, -1), (1, 1, -3)]
      (by decide) (by decide) (consequence h [0, 0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact case31 (consequences (addRelation hz h) [[0, 1, 0], [3, 0, 1], [1, 0, 0]] (by decide))
    · exact case2 (consequences (addRelation hz h) [[0, 1, 0], [-3, 0, 2], [-2, 0, 1]] (by decide))
    · exact case2 (consequences (addRelation hz h) [[0, 1, 0], [3, 0, -1], [2, 0, -1]] (by decide))
    · exact case32 (consequences (addRelation hz h) [[0, 1, 0], [-1, 1, 0], [-2, 2, -1]] (by decide))
    · exact case2 (consequences (addRelation hz h) [[0, 1, 0], [-3, 3, -1], [-2, 2, -1]] (by decide))
    · exact case33 (consequences (addRelation hz h) [[0, 1, 0], [-2, 2, 1], [-1, 1, 0]] (by decide))
    · exact case31 (consequences (addRelation hz h) [[0, 1, 0], [-3, 3, 1], [-1, 1, 0]] (by decide))
    · exact case32 (consequences (addRelation hz h) [[0, 1, 0], [-1, 1, 1], [-2, 2, 1]] (by decide))
  have case35 (h : Vanishes φ [(1, 0, 0), (0, 2, -2)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 8) (by decide) φ
      (points 7 [0, 1, 3, 2, 0, 1, 3, 2]) (0, 2, -2) [(0, 1, -1)]
      (by decide) (by decide) (consequence h [0, 1] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    exact case30 (consequences (addRelation hz h) [[0, 1, 0], [1, 0, 0]] (by decide))
  have case36 (h : Vanishes φ [(1, 0, 0)]) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 16) (by decide) φ
      (points 7 [0, 1, 2, 3, 1, 0, 2, 1, 3, 0, 1, 3, 2, 0, 1, 3]) (0, 0, 0) [(0, 0, 1), (0, 1, -2), (0, 1, -1), (0, 2, -3), (1, -2, 2), (1, -1, 0), (1, -1, 1), (1, 0, -1)]
      (by decide) (by decide) (consequence h [0] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact case5 (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
    · exact case29 (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
    · exact case30 (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
    · exact case34 (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
    · exact case35 (consequences (addRelation hz h) [[0, 1], [-1, 1]] (by decide))
    · exact case9 (consequences (addRelation hz h) [[0, 1], [-1, 1]] (by decide))
    · exact case30 (consequences (addRelation hz h) [[0, 1], [-1, 1]] (by decide))
    · exact case5 (consequences (addRelation hz h) [[0, 1], [-1, 1]] (by decide))
  have case37 (h : Vanishes φ []) : HasShortCycle (normalGraph 7 φ) := by
    apply template 7 (n := 16) (by decide) φ
      (points 7 [0, 1, 2, 0, 1, 2, 3, 0, 1, 2, 0, 1, 3, 2, 1, 3]) (0, 0, 0) [(0, 0, 1), (0, 1, -1), (0, 1, 0), (1, -2, 0), (1, -1, -1), (1, -1, 0), (1, 0, -1), (1, 0, 0)]
      (by decide) (by decide) (consequence h [] (by decide))
    intro d hd hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact case7 (consequences (addRelation hz h) [[1]] (by decide))
    · exact case8 (consequences (addRelation hz h) [[1]] (by decide))
    · exact case14 (consequences (addRelation hz h) [[1]] (by decide))
    · exact case21 (consequences (addRelation hz h) [[1]] (by decide))
    · exact case26 (consequences (addRelation hz h) [[1]] (by decide))
    · exact case27 (consequences (addRelation hz h) [[1]] (by decide))
    · exact case28 (consequences (addRelation hz h) [[1]] (by decide))
    · exact case36 (consequences (addRelation hz h) [[1]] (by decide))
  exact case37 (by simp [Vanishes])

private def evaluate (a b c : A) : Voltage →+ A where
  toFun z := z.1 • a + z.2.1 • b + z.2.2 • c
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, add_zsmul]; abel


/-- A tetrahedral cover with translations or reflected translations on the three
oriented chords. The reverse of every chord carries the inverse affine map. -/
def affineCover (mask : Fin 8) (a b c : A) : SimpleGraph (Color × A) :=
  normalGraph mask (evaluate a b c)

private theorem undirected (mask : Fin 8) (φ : Voltage →+ A) (i j : Color) (x : A) :
    orient (flipped mask j i)
        (orient (flipped mask i j) x + φ (displacement mask i j)) +
      φ (displacement mask j i) = x := by
  have same : ∀ (m : Fin 8) (u v : Color), flipped m v u = flipped m u v := by decide
  have inverse : ∀ (m : Fin 8) (u v : Color), displacement m v u =
      -orient (flipped m u v) (displacement m u v) := by decide
  rw [same mask i j, inverse mask i j]
  cases flipped mask i j <;> simp [orient]

private theorem normal_adj (mask : Fin 8) (φ : Voltage →+ A) (u v : Color × A) :
    (normalGraph mask φ).Adj u v ↔
      u.1 ≠ v.1 ∧ v.2 = orient (flipped mask u.1 v.1) u.2 + φ (displacement mask u.1 v.1) := by
  constructor
  · rintro ⟨_,h | h⟩
    · exact h
    · refine ⟨h.1.symm, ?_⟩
      rw [h.2, undirected]
  · intro h
    exact ⟨fun eq => h.1 (congrArg Prod.fst eq), Or.inl h⟩

/-- Uniform even for infinite abelian sheet groups and noncommuting edge maps. -/
theorem affine_cover_short (mask : Fin 8) (a b c : A) :
    HasShortCycle (affineCover mask a b c) := by
  unfold affineCover
  fin_cases mask
  · exact mask0 _
  · exact mask1 _
  · exact mask2 _
  · exact mask3 _
  · exact mask4 _
  · exact mask5 _
  · exact mask6 _
  · exact mask7 _

/-- A graph containing the four fibers and six prescribed matchings already
contains a short cycle, even when it has additional edges or vertices. -/
theorem affine_subgraph_short {V : Type*} (G : SimpleGraph V) (e : Color × A ↪ V)
    (s t u : Bool) (a b c : A)
    (star : ∀ i : Color, i ≠ 0 → ∀ x, G.Adj (e (0,x)) (e (i,x)))
    (oneTwo : ∀ x, G.Adj (e (1,x)) (e (2,orient s x + a)))
    (twoThree : ∀ x, G.Adj (e (2,x)) (e (3,orient t x + b)))
    (threeOne : ∀ x, G.Adj (e (3,x)) (e (1,orient u x + c))) : HasShortCycle G := by
  have bits : ∃ m : Fin 8, m.val.testBit 0 = s ∧ m.val.testBit 1 = t ∧ m.val.testBit 2 = u := by
    cases s <;> cases t <;> cases u <;> decide
  obtain ⟨m, hs, ht, hu⟩ := bits
  let φ := evaluate a b c
  let N := normalGraph m φ
  have starEdge (i : Color) (hi : i ≠ 0) (x y : A) (h : N.Adj (0,x) (i,y)) :
      G.Adj (e (0,x)) (e (i,y)) := by
    have eq := ((normal_adj m φ _ _).mp h).2
    have yx : y = x := by fin_cases i <;> simpa [flipped, orient, displacement] using eq
    exact yx ▸ star i hi x
  have edge12 (x y : A) (h : N.Adj (1,x) (2,y)) : G.Adj (e (1,x)) (e (2,y)) := by
    have eq : y = orient s x + a := by
      simpa [φ, evaluate, flipped, displacement, hs] using ((normal_adj m φ _ _).mp h).2
    exact eq ▸ oneTwo x
  have edge23 (x y : A) (h : N.Adj (2,x) (3,y)) : G.Adj (e (2,x)) (e (3,y)) := by
    have eq : y = orient t x + b := by
      simpa [φ, evaluate, flipped, displacement, ht] using ((normal_adj m φ _ _).mp h).2
    exact eq ▸ twoThree x
  have edge31 (x y : A) (h : N.Adj (3,x) (1,y)) : G.Adj (e (3,x)) (e (1,y)) := by
    have eq : y = orient u x + c := by
      simpa [φ, evaluate, flipped, displacement, hu] using ((normal_adj m φ _ _).mp h).2
    exact eq ▸ threeOne x
  have copy : N ⊑ G := by
    refine ⟨⟨⟨e, ?_⟩, e.injective⟩⟩
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    fin_cases i <;> fin_cases j <;> first
    | exact (((normal_adj m φ _ _).mp h).1 rfl).elim
    | exact starEdge _ (by decide) x y h
    | exact (starEdge _ (by decide) y x h.symm).symm
    | exact edge12 x y h
    | exact edge23 x y h
    | exact edge31 x y h
    | exact (edge12 y x h.symm).symm
    | exact (edge23 y x h.symm).symm
    | exact (edge31 y x h.symm).symm
  rcases affine_cover_short m a b c with h | h | h
  · exact Or.inl (h.trans copy)
  · exact Or.inr (Or.inl (h.trans copy))
  · exact Or.inr (Or.inr (h.trans copy))

/-- A translation or the composition of negation with a translation. -/
def SignedAffine (f : Equiv.Perm A) : Prop :=
  ∃ (s : Bool) (a : A), ∀ x, f x = orient s x + a

private theorem signedInverse {f : Equiv.Perm A} (h : SignedAffine f) :
    SignedAffine f.symm := by
  obtain ⟨s,a,ha⟩ := h
  cases s
  · refine ⟨false,-a,fun x => f.injective ?_⟩
    rw [f.apply_symm_apply, ha]
    simp [orient]
  · refine ⟨true,a,fun x => f.injective ?_⟩
    rw [f.apply_symm_apply, ha]
    simp [orient]

private theorem signedTrans {f g : Equiv.Perm A} (hf : SignedAffine f) (hg : SignedAffine g) :
    SignedAffine (f.trans g) := by
  obtain ⟨s,a,ha⟩ := hf
  obtain ⟨t,b,hb⟩ := hg
  refine ⟨s.xor t,orient t a + b,fun x => ?_⟩
  change g (f x) = _
  rw [hb, ha]
  cases s <;> cases t <;> simp [orient, add_assoc, add_left_comm, add_comm]

/-- The six original edge matchings may all translate or negate and translate
in arbitrary coordinates. Relabel the three outer fibers by the star
matchings and apply the normalized certificate. -/
theorem signed_matchings_short {V : Type*} (G : SimpleGraph V) (e : Color × A ↪ V)
    (star : Color → Equiv.Perm A) (p q r : Equiv.Perm A)
    (signedStar : ∀ i : Color, i ≠ 0 → SignedAffine (star i))
    (hp : SignedAffine p) (hq : SignedAffine q) (hr : SignedAffine r)
    (atZero : ∀ i : Color, i ≠ 0 → ∀ x, G.Adj (e (0,x)) (e (i,star i x)))
    (oneTwo : ∀ x, G.Adj (e (1,x)) (e (2,p x)))
    (twoThree : ∀ x, G.Adj (e (2,x)) (e (3,q x)))
    (threeOne : ∀ x, G.Adj (e (3,x)) (e (1,r x))) : HasShortCycle G := by
  let frame (i : Color) : Equiv.Perm A := if i = 0 then Equiv.refl A else star i
  let chord (i j : Color) (v : Equiv.Perm A) := ((frame i).trans v).trans (frame j).symm
  have signedChord {i j : Color} (hi : i ≠ 0) (hj : j ≠ 0) (v : Equiv.Perm A)
      (hv : SignedAffine v) : SignedAffine (chord i j v) := by
    simpa [chord, frame, hi, hj] using signedTrans (signedTrans (signedStar i hi) hv)
      (signedInverse (signedStar j hj))
  obtain ⟨s,a,sa⟩ := signedChord (by decide : (1 : Color) ≠ 0) (by decide : (2 : Color) ≠ 0) p hp
  obtain ⟨t,b,tb⟩ := signedChord (by decide : (2 : Color) ≠ 0) (by decide : (3 : Color) ≠ 0) q hq
  obtain ⟨u,c,uc⟩ := signedChord (by decide : (3 : Color) ≠ 0) (by decide : (1 : Color) ≠ 0) r hr
  let label : Color × A ↪ V :=
    ⟨fun z => e (z.1,frame z.1 z.2), by
      rintro ⟨i,x⟩ ⟨j,y⟩ h
      have eq := e.injective h
      have ij : i = j := congrArg Prod.fst eq
      subst j
      exact Prod.ext rfl ((frame i).injective (congrArg Prod.snd eq))⟩
  have label_apply (i : Color) (x : A) : label (i,x) = e (i,frame i x) := rfl
  apply affine_subgraph_short G label s t u a b c
  · intro i hi x
    simpa [label_apply, frame, hi] using atZero i hi x
  · intro x
    rw [← sa x]
    simpa [label_apply, chord] using oneTwo (frame 1 x)
  · intro x
    rw [← tb x]
    simpa [label_apply, chord] using twoThree (frame 2 x)
  · intro x
    rw [← uc x]
    simpa [label_apply, chord] using threeOne (frame 3 x)

/-! ## Affine matchings with a fixed-point-free linear action -/

private theorem hamiltonSquare {A V : Type*} (G : SimpleGraph V) (e : Color × A ↪ V)
    (i j k : Color) (colors : Injective (![0,i,j,k] : Fin 4 → Color)) (x y : A)
    (h₀ : G.Adj (e (0,x)) (e (i,x))) (h₁ : G.Adj (e (i,x)) (e (j,y)))
    (h₂ : G.Adj (e (j,y)) (e (k,x))) (h₃ : G.Adj (e (k,x)) (e (0,x))) :
    cycleGraph 4 ⊑ G := by
  let v : Fin 4 → Color × A := ![(0,x),(i,x),(j,y),(k,x)]
  have projection (t : Fin 4) : (v t).1 = (![0,i,j,k] : Fin 4 → Color) t := by
    fin_cases t <;> rfl
  refine ⟨⟨⟨fun t => e (v t), ?_⟩, ?_⟩⟩
  · intro s t edge
    fin_cases s <;> fin_cases t <;> first
      | exact h₀ | exact h₁ | exact h₂ | exact h₃
      | exact h₀.symm | exact h₁.symm | exact h₂.symm | exact h₃.symm
      | exact absurd edge (by decide)
  · intro s t eq
    apply colors
    rw [← projection, ← projection]
    exact congrArg Prod.fst (e.injective eq)

/-- A group acts additively on the sheets. If every nonidentity linear part
has invertible difference from the identity, three arbitrary affine chords
still force a 4-, 8-, or 16-cycle. -/
theorem fixed_point_free_affine_short {A S V : Type*} [AddCommGroup A] [Group S]
    [DistribMulAction S A] (G : SimpleGraph V) (e : Color × A ↪ V)
    (regular : ∀ g : S, g ≠ 1 → Bijective (fun x : A => x - g • x))
    (p q r : S) (a b c : A)
    (star : ∀ i : Color, i ≠ 0 → ∀ x, G.Adj (e (0,x)) (e (i,x)))
    (oneTwo : ∀ x, G.Adj (e (1,x)) (e (2,p • x + a)))
    (twoThree : ∀ x, G.Adj (e (2,x)) (e (3,q • x + b)))
    (threeOne : ∀ x, G.Adj (e (3,x)) (e (1,r • x + c))) : HasShortCycle G := by
  have fixed (s t : S) (u v : A) (ne : t*s ≠ 1) :
      ∃ x : A, t • (s • x + u) + v = x := by
    obtain ⟨x,hx⟩ := (regular _ ne).surjective (t • u + v)
    refine ⟨x,?_⟩
    change x - (t*s) • x = t • u + v at hx
    rw [sub_eq_iff_eq_add] at hx
    rw [smul_add, ← mul_smul]
    calc
      (t*s) • x + t • u + v = t • u + v + (t*s) • x := by abel
      _ = x := hx.symm
  by_cases qp : q*p = 1
  swap
  · obtain ⟨x,h⟩ := fixed p q a b qp
    exact Or.inl (hamiltonSquare G e 1 2 3 (by decide) x (p • x + a)
      (star 1 (by decide) x) (oneTwo x) (by simpa only [h] using twoThree (p • x + a)) (star 3 (by decide) x).symm)
  by_cases rq : r*q = 1
  swap
  · obtain ⟨x,h⟩ := fixed q r b c rq
    exact Or.inl (hamiltonSquare G e 2 3 1 (by decide) x (q • x + b)
      (star 2 (by decide) x) (twoThree x) (by simpa only [h] using threeOne (q • x + b)) (star 1 (by decide) x).symm)
  by_cases pr : p*r = 1
  swap
  · obtain ⟨x,h⟩ := fixed r p c a pr
    exact Or.inl (hamiltonSquare G e 3 1 2 (by decide) x (r • x + c)
      (star 3 (by decide) x) (threeOne x) (by simpa only [h] using oneTwo (r • x + c)) (star 2 (by decide) x).symm)
  have same : r = p := by
    calc r = r*1 := (mul_one r).symm
         _ = r*(q*p) := by rw [qp]
         _ = p := by rw [← mul_assoc,rq,one_mul]
  subst r
  have same : q = p := mul_right_cancel (qp.trans pr.symm)
  subst q
  by_cases trivial : p = 1
  · subst p
    apply affine_subgraph_short G e false false false a b c star
    · simpa [orient] using oneTwo
    · simpa [orient] using twoThree
    · simpa [orient] using threeOne
  · have neg (x : A) : p • x = -x := by
      have invol : p • (p • x) = x := by rw [← mul_smul,pr,one_smul]
      have fixedSum : p • (x + p • x) = x + p • x := by rw [smul_add,invol,add_comm]
      have equal : x + p • x = 0 := (regular p trivial).injective (by
        rw [fixedSum,smul_zero,sub_self,sub_self])
      exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using equal)
    apply affine_subgraph_short G e true true true a b c star
    · simpa [orient,neg] using oneTwo
    · simpa [orient,neg] using twoThree
    · simpa [orient,neg] using threeOne

/-- Change the sheet coordinates independently in the three outer fibers.
This allows all six edge matchings to have arbitrary affine parts. -/
theorem affine_six_matchings_short {A S V : Type*} [AddCommGroup A] [Group S]
    [DistribMulAction S A] (G : SimpleGraph V) (e : Color × A ↪ V)
    (regular : ∀ g : S, g ≠ 1 → Bijective (fun x : A => x - g • x))
    (st : Color → S) (d : Color → A) (p q r : S) (a b c : A)
    (star : ∀ i : Color, i ≠ 0 → ∀ x, G.Adj (e (0,x)) (e (i,st i • x + d i)))
    (oneTwo : ∀ x, G.Adj (e (1,x)) (e (2,p • x + a)))
    (twoThree : ∀ x, G.Adj (e (2,x)) (e (3,q • x + b)))
    (threeOne : ∀ x, G.Adj (e (3,x)) (e (1,r • x + c))) : HasShortCycle G := by
  let frame (i : Color) (x : A) := if i = 0 then x else st i • x + d i
  let label : Color × A ↪ V := ⟨fun z => e (z.1,frame z.1 z.2), by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have h' := e.injective h
    have ij : i = j := congrArg Prod.fst h'
    subst j
    have eq : frame i x = frame i y := congrArg Prod.snd h'
    apply congrArg (fun z : A => (i,z))
    by_cases zero : i = 0
    · simpa only [frame,if_pos zero] using eq
    · simp only [frame,if_neg zero,add_left_inj] at eq
      exact (MulAction.bijective (st i)).injective eq⟩
  let linear (i j : Color) (g : S) := (st j)⁻¹ * (g * st i)
  let bias (i j : Color) (g : S) (z : A) := (st j)⁻¹ • (g • d i + z - d j)
  have chord (i j : Color) (hi : i ≠ 0) (hj : j ≠ 0) (g : S) (z : A)
      (edge : ∀ x, G.Adj (e (i,x)) (e (j,g • x + z))) (x : A) :
      G.Adj (label (i,x)) (label (j,linear i j g • x + bias i j g z)) := by
    change G.Adj (e (i,frame i x)) (e (j,frame j _))
    simp only [frame, if_neg hi, if_neg hj]
    have norm : st j • (linear i j g • x + bias i j g z) + d j =
        g • (st i • x + d i) + z := by
      simp only [linear,bias,smul_add,mul_smul,smul_inv_smul]
      abel
    rw [norm]
    exact edge _
  apply fixed_point_free_affine_short G label regular (linear 1 2 p) (linear 2 3 q) (linear 3 1 r)
    (bias 1 2 p a) (bias 2 3 q b) (bias 3 1 r c)
  · intro i hi x
    change G.Adj (e (0,frame 0 x)) (e (i,frame i x))
    simpa only [frame,if_pos rfl,if_neg hi] using star i hi x
  · exact chord 1 2 (by decide) (by decide) p a oneTwo
  · exact chord 2 3 (by decide) (by decide) q b twoThree
  · exact chord 3 1 (by decide) (by decide) r c threeOne

/-- On finite sheets it suffices that every nonidentity element fixes only zero. -/
theorem finite_frobenius_short {A S V : Type*} [AddCommGroup A] [Finite A] [Group S]
    [DistribMulAction S A] (G : SimpleGraph V) (e : Color × A ↪ V)
    (free : ∀ g : S, g ≠ 1 → ∀ x : A, g • x = x → x = 0)
    (st : Color → S) (d : Color → A) (p q r : S) (a b c : A)
    (star : ∀ i : Color, i ≠ 0 → ∀ x, G.Adj (e (0,x)) (e (i,st i • x + d i)))
    (oneTwo : ∀ x, G.Adj (e (1,x)) (e (2,p • x + a)))
    (twoThree : ∀ x, G.Adj (e (2,x)) (e (3,q • x + b)))
    (threeOne : ∀ x, G.Adj (e (3,x)) (e (1,r • x + c))) : HasShortCycle G := by
  apply affine_six_matchings_short G e _ st d p q r a b c star oneTwo twoThree threeOne
  intro g ng
  apply Finite.injective_iff_bijective.mp
  intro x y equal
  change x - g • x = y - g • y at equal
  apply sub_eq_zero.mp
  apply free g ng
  rw [smul_sub]
  calc g • x - g • y = (x-y) - ((x-g • x)-(y-g • y)) := by abel
       _ = x-y := by rw [equal,sub_self,sub_zero]

/-- Scalar affine matchings of an arbitrary vector space over a division
ring satisfy the same short-cycle bound as signed translations. -/
theorem scalar_affine_short {K A V : Type*} [DivisionRing K] [AddCommGroup A]
    [Module K A] (G : SimpleGraph V) (e : Color × A ↪ V)
    (st : Color → Kˣ) (d : Color → A) (p q r : Kˣ) (a b c : A)
    (star : ∀ i : Color, i ≠ 0 → ∀ x, G.Adj (e (0,x)) (e (i,(st i:K) • x + d i)))
    (oneTwo : ∀ x, G.Adj (e (1,x)) (e (2,(p:K) • x + a)))
    (twoThree : ∀ x, G.Adj (e (2,x)) (e (3,(q:K) • x + b)))
    (threeOne : ∀ x, G.Adj (e (3,x)) (e (1,(r:K) • x + c))) : HasShortCycle G := by
  apply affine_six_matchings_short G e (S := Kˣ) _ st d p q r a b c star oneTwo twoThree threeOne
  intro g ne
  have nonzero : (1:K) - (g:K) ≠ 0 := sub_ne_zero.mpr <| fun h => ne (Units.ext h.symm)
  let u := Units.mk0 ((1:K)-(g:K)) nonzero
  have action (x : A) : u • x = x - g • x := by
    change ((1:K)-(g:K)) • x = x - (g:K) • x
    rw [sub_smul,one_smul]
  rw [← funext action]
  exact MulAction.bijective u

/-! ## Solvable groups on a prime number of sheets -/

open MulAction

private theorem abelianNormal {G : Type*} [Group G] [Group.IsSolvable G] [Nontrivial G] :
    ∃ N : Subgroup G, N ≠ ⊥ ∧ N.Normal ∧ IsMulCommutative N := by
  classical
  have terminating : ∃ n : ℕ, derivedSeries G n = ⊥ := Group.IsSolvable.solvable
  let m := Nat.find terminating
  have last : derivedSeries G m = ⊥ := Nat.find_spec terminating
  have pos : m ≠ 0 := by
    intro z
    rw [z,derivedSeries_zero] at last
    exact top_ne_bot last
  obtain ⟨k,hk⟩ : ∃ k, m = k+1 := ⟨m-1,by omega⟩
  refine ⟨derivedSeries G k, ?_, derivedSeries_normal G k, ?_⟩
  · intro trivial
    have le : m ≤ k := Nat.find_min' terminating trivial
    omega
  · rw [hk,derivedSeries_succ] at last
    exact Subgroup.commutator_self_eq_bot_iff.mp last

private theorem automorphism_fixed {N : Type*} [Group N] (prime : (Nat.card N).Prime)
    (u : MulAut N) (ne : u ≠ 1) (x : N) (hx : u x = x) : x = 1 := by
  classical
  by_contra nx
  let : Fact (Nat.card N).Prime := ⟨prime⟩
  apply ne
  ext y
  obtain ⟨k,rfl⟩ := mem_zpowers_of_prime_card (p := Nat.card N) rfl nx (g' := y)
  simp only [map_zpow, hx, MulAut.one_apply]

/-- A faithful transitive solvable permutation group on a prime number of
sheets gives a tetrahedral cover with a simple 4-, 8-, or 16-cycle. -/
theorem prime_solvable_short {G X V : Type*} [Group G] [Group.IsSolvable G]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X] [Finite X]
    (prime : (Nat.card X).Prime) (graph : SimpleGraph V) (e : Color × X ↪ V)
    (p q r : G)
    (star : ∀ i : Color, i ≠ 0 → ∀ x, graph.Adj (e (0,x)) (e (i,x)))
    (oneTwo : ∀ x, graph.Adj (e (1,x)) (e (2,p • x)))
    (twoThree : ∀ x, graph.Adj (e (2,x)) (e (3,q • x)))
    (threeOne : ∀ x, graph.Adj (e (3,x)) (e (1,r • x))) : HasShortCycle graph := by
  classical
  let : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp prime.one_lt
  obtain ⟨origin,y,xy⟩ := exists_pair_ne X
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G origin y
  let : Nontrivial G := ⟨⟨g,1,fun he => xy (by simpa only [he,one_smul] using hg)⟩⟩
  obtain ⟨N,nn,normal,comm⟩ := abelianNormal (G := G)
  let : N.Normal := normal
  let : IsMulCommutative N := comm
  let : CommGroup N := { (inferInstance : Group N) with mul_comm := mul_comm' }
  let : IsPreprimitive G X := IsPreprimitive.of_prime_card prime
  have nonfixed : fixedPoints N X ≠ Set.univ := by
    intro allFixed
    apply nn
    apply eq_bot_iff.mpr
    intro n hn
    change n = 1
    apply eq_of_smul_eq_smul (α := X)
    intro x
    have fixed : x ∈ fixedPoints N X := allFixed ▸ Set.mem_univ x
    simpa only [Subgroup.smul_def,one_smul] using (mem_fixedPoints.mp fixed (⟨n,hn⟩ : N))
  let : IsPretransitive N X := IsQuasiPreprimitive.isPretransitive_of_normal nonfixed
  let coords : N ≃ X := Equiv.ofBijective (fun n : N => n • origin) ⟨by
    intro n m same
    apply Subtype.ext
    apply eq_of_smul_eq_smul (α := X)
    intro x
    obtain ⟨h,rfl⟩ := MulAction.exists_smul_eq N origin x
    change n • (h • origin) = m • (h • origin)
    simpa only [smul_comm n h,smul_comm m h] using congrArg (fun z : X => h • z) same,
    fun x => MulAction.exists_smul_eq N origin x⟩
  have card : (Nat.card N).Prime := (Nat.card_congr coords).symm ▸ prime
  let : Finite N := Finite.of_equiv X coords.symm
  let : DistribMulAction (MulAut N) (Additive N) := {
    smul u x := Additive.ofMul (u x.toMul)
    one_smul x := rfl
    mul_smul u v x := rfl
    smul_zero u := u.map_one
    smul_add u x y := u.map_mul _ _ }
  let shift (h : G) : Additive N := Additive.ofMul (coords.symm (h • origin))
  let linear (h : G) : MulAut N := MulAut.conjNormal h
  let label : Color × Additive N ↪ V :=
    ((Equiv.refl Color).prodCongr (Additive.toMul.trans coords)).toEmbedding.trans e
  have affine (h : G) (x : Additive N) :
      coords ((linear h • x + shift h).toMul) = h • coords x.toMul := by
    change ((MulAut.conjNormal h x.toMul) * coords.symm (h • origin)) • origin =
      h • (x.toMul • origin)
    rw [mul_smul]
    have base : coords.symm (h • origin) • origin = h • origin := coords.apply_symm_apply _
    rw [base]
    change ((MulAut.conjNormal h x.toMul : N) : G) • (h • origin) =
      h • ((x.toMul : G) • origin)
    simp only [MulAut.conjNormal_apply, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
  apply finite_frobenius_short graph label (S := MulAut N) _ (fun _ => 1) (fun _ => 0)
    (linear p) (linear q) (linear r) (shift p) (shift q) (shift r)
  · intro i hi x
    change graph.Adj (e (0,coords x.toMul)) (e (i,coords (((1 : MulAut N) • x + 0).toMul)))
    simpa only [one_smul,add_zero] using star i hi (coords x.toMul)
  · intro x
    change graph.Adj (e (1,coords x.toMul)) (e (2,coords ((linear p • x + shift p).toMul)))
    rw [affine]
    exact oneTwo _
  · intro x
    change graph.Adj (e (2,coords x.toMul)) (e (3,coords ((linear q • x + shift q).toMul)))
    rw [affine]
    exact twoThree _
  · intro x
    change graph.Adj (e (3,coords x.toMul)) (e (1,coords ((linear r • x + shift r).toMul)))
    rw [affine]
    exact threeOne _
  · intro u nu x hx
    exact automorphism_fixed card u nu x.toMul hx

/-- The standard four-fiber graph with its three star matchings normalized. -/
def permutationCover {X : Type*} (p q r : Equiv.Perm X) : SimpleGraph (Color × X) :=
  SimpleGraph.fromRel fun u v =>
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨
    (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨
    (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2)

/-- A connected prime-sheeted tetrahedral cover whose chord permutations
generate a solvable group contains a cycle of length 4, 8, or 16. -/
theorem prime_solvable_cover_short {X : Type*} [Finite X] (p q r : Equiv.Perm X)
    (prime : (Nat.card X).Prime) (solvable : Group.IsSolvable (Subgroup.closure ({p,q,r} : Set _)))
    (connected : (permutationCover p q r).Connected) : HasShortCycle (permutationCover p q r) := by
  classical
  let M := Subgroup.closure ({p,q,r} : Set (Equiv.Perm X))
  let : Group.IsSolvable M := solvable
  let P : M := ⟨p,Subgroup.subset_closure (by simp)⟩
  let Q : M := ⟨q,Subgroup.subset_closure (by simp)⟩
  let R : M := ⟨r,Subgroup.subset_closure (by simp)⟩
  let rel (u v : Color × X) : Prop :=
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨ (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨ (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2)
  have directed {u v : Color × X} (h : rel u v) : ∃ g : M, g • u.2 = v.2 := by
    rcases h with h | h | h | h
    · exact ⟨1,(one_smul M _).trans h.2.2.symm⟩
    · exact ⟨P,h.2.2.symm⟩
    · exact ⟨Q,h.2.2.symm⟩
    · exact ⟨R,h.2.2.symm⟩
  have adjacent {u v : Color × X} (h : (permutationCover p q r).Adj u v) :
      ∃ g : M, g • u.2 = v.2 := by
    rcases h.2 with h | h
    · exact directed h
    · obtain ⟨g,hg⟩ := directed h
      exact ⟨g⁻¹,by rw [← hg,inv_smul_smul]⟩
  have path {u v : Color × X} (w : (permutationCover p q r).Walk u v) :
      ∃ g : M, g • u.2 = v.2 := by
    induction w with
    | nil => exact ⟨1,one_smul M _⟩
    | cons edge tail ih =>
      obtain ⟨g,hg⟩ := adjacent edge
      obtain ⟨h,hh⟩ := ih
      exact ⟨h*g,by rw [mul_smul,hg,hh]⟩
  let : IsPretransitive M X := ⟨fun x y => by
    obtain ⟨w⟩ := connected.preconnected (0,x) (0,y)
    exact path w⟩
  apply prime_solvable_short (G := M) prime _ (Function.Embedding.refl _) P Q R
  · intro i hi x
    simp [permutationCover, hi, Ne.symm hi]
  · intro x
    simp [permutationCover, P]
  · intro x
    simp [permutationCover, Q]
  · intro x
    simp [permutationCover, R]

end Erdos64AffineCovers
