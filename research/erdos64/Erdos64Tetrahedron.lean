import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Tactic

/-!
# Power-of-two cycles in abelian covers of the tetrahedron

A voltage on an oriented edge translates the sheet by a fixed element of an
abelian group. Normalizing the three edges out of vertex 0 to zero leaves
the three independent voltages on 12, 23 and 31. The finite certificate below
either embeds a 4-, 8- or 16-cycle or uses an identification of two vertices
to pass to a smaller quotient of the free abelian group on the voltages.
-/

namespace Erdos64Tetrahedron

open SimpleGraph Function

abbrev Color := Fin 4
abbrev Voltage := ℤ × ℤ × ℤ
abbrev Position := Color × Voltage

private def edgeVector (i j : Color) : Voltage :=
  match i.val, j.val with
  | 1, 2 => (1, 0, 0)
  | 2, 3 => (0, 1, 0)
  | 3, 1 => (0, 0, 1)
  | 2, 1 => (-1, 0, 0)
  | 3, 2 => (0, -1, 0)
  | 1, 3 => (0, 0, -1)
  | _, _ => 0

variable {A : Type*} [AddCommGroup A]

/-- The cover of the complete graph on four vertices defined by edge voltages. -/
def coverGraph (ω : Color → Color → A) (reverse : ∀ i j, ω j i = -ω i j) :
    SimpleGraph (Color × A) where
  Adj u v := u.1 ≠ v.1 ∧ v.2 = u.2 + ω u.1 v.1
  symm := ⟨by
    rintro u v ⟨hne, heq⟩
    exact ⟨hne.symm, by rw [reverse u.1 v.1, heq]; abel⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private def normalGraph (φ : Voltage →+ A) : SimpleGraph (Color × A) :=
  coverGraph (fun i j => φ (edgeVector i j)) (by
    have rev : ∀ i j, edgeVector j i = -edgeVector i j := by decide
    intro i j
    rw [rev i j, map_neg])

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

private def traceFrom (u : Color) (p : Voltage) : List Color → List Position
  | [] => [(u, p)]
  | v :: vs => (u, p) :: traceFrom v (p + edgeVector u v) vs

private def points {n : ℕ} (word : List Color) (i : Fin n) : Position :=
  let visits := match word with
    | [] => []
    | u :: vs => traceFrom u 0 vs
  visits[i.val]?.getD (0, 0)

private def residue (x y : Position) : Voltage := x.2 + edgeVector x.1 y.1 - y.2
private def distanceVector (x y : Position) : Voltage := y.2 - x.2

private theorem template {n : ℕ} [NeZero n] (allowed : n = 4 ∨ n = 8 ∨ n = 16)
    (φ : Voltage →+ A) (p : Fin n → Position) (total : Voltage) (collisions : List Voltage)
    (edges : ∀ i, (p i).1 ≠ (p (i + 1)).1 ∧
      (residue (p i) (p (i + 1)) = 0 ∨ residue (p i) (p (i + 1)) = total))
    (pairs : ∀ i j, i ≠ j → (p i).1 = (p j).1 →
      distanceVector (p i) (p j) ∈ collisions ∨ -distanceVector (p i) (p j) ∈ collisions)
    (closed : φ total = 0)
    (next : ∀ d ∈ collisions, φ d = 0 → HasShortCycle (normalGraph φ)) :
    HasShortCycle (normalGraph φ) := by
  classical
  let label (i : Fin n) : Color × A := ((p i).1, φ (p i).2)
  by_cases injective : Injective label
  · have edge (i : Fin n) : (normalGraph φ).Adj (label i) (label (i + 1)) := by
      obtain ⟨distinct, hz⟩ := edges i
      have h : φ (residue (p i) (p (i + 1))) = 0 := by
        rcases hz with hz | hz <;> simp [hz, closed]
      refine ⟨distinct, ?_⟩
      exact (sub_eq_zero.mp (by simpa [residue] using h)).symm
    have contains : cycleGraph n ⊑ normalGraph φ := by
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

-- The rows of each case are integer relations on the three chord voltages.
-- The color words specify the projected cycles. Each row of a transition
-- matrix expresses one relation of a later case in terms of the collision
-- and the relations already known.

private theorem case0 (φ : Voltage →+ A)
    (h : Vanishes φ [(0, 1, 0), (0, 0, 1)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 4) (by decide) φ
    (points [0, 1, 3, 2]) (0, -1, -1)
    [] (by decide) (by decide)
    (consequence h [-1, -1] (by decide))
  intro d hd hz
  simp at hd

private theorem case1 (φ : Voltage →+ A)
    (h : Vanishes φ [(1, 0, 0), (0, 1, 0), (0, 0, 1)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 4) (by decide) φ
    (points [0, 1, 2, 3]) (1, 1, 0)
    [] (by decide) (by decide)
    (consequence h [1, 1, 0] (by decide))
  intro d hd hz
  simp at hd

private theorem case2 (φ : Voltage →+ A)
    (h : Vanishes φ [(1, -1, 0), (0, 0, 1)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 8) (by decide) φ
    (points [0, 1, 3, 2, 0, 3, 1, 2]) (1, -1, 0)
    [(0, 1, 0), (0, 1, 1), (1, 0, 1)] (by decide) (by decide)
    (consequence h [1, 0] (by decide))
  intro d hd hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact case1 φ (consequences (addRelation hz h) [[1, 1, 0], [1, 0, 0], [0, 0, 1]] (by decide))
  · exact case1 φ (consequences (addRelation hz h) [[1, 1, -1], [1, 0, -1], [0, 0, 1]] (by decide))
  · exact case1 φ (consequences (addRelation hz h) [[1, 0, -1], [1, -1, -1], [0, 0, 1]] (by decide))

private theorem case3 (φ : Voltage →+ A)
    (h : Vanishes φ [(1, 0, 0), (0, 0, 1)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 4) (by decide) φ
    (points [0, 2, 1, 3]) (-1, 0, -1)
    [] (by decide) (by decide)
    (consequence h [-1, -1] (by decide))
  intro d hd hz
  simp at hd

private theorem case4 (φ : Voltage →+ A)
    (h : Vanishes φ [(1, 1, 0), (0, 0, 1)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 4) (by decide) φ
    (points [0, 1, 2, 3]) (1, 1, 0)
    [] (by decide) (by decide)
    (consequence h [1, 0] (by decide))
  intro d hd hz
  simp at hd

private theorem case5 (φ : Voltage →+ A)
    (h : Vanishes φ [(2, 0, 0), (0, 0, 1)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 8) (by decide) φ
    (points [0, 2, 1, 3, 0, 2, 1, 3]) (-2, 0, -2)
    [(1, 0, 1)] (by decide) (by decide)
    (consequence h [-1, -2] (by decide))
  intro d hd hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst d
  exact case3 φ (consequences (addRelation hz h) [[1, 0, -1], [0, 0, 1]] (by decide))

private theorem case6 (φ : Voltage →+ A)
    (h : Vanishes φ [(2, 1, 0), (0, 0, 1)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 8) (by decide) φ
    (points [0, 1, 2, 0, 3, 1, 2, 3]) (2, 1, 1)
    [(1, 0, 0), (1, 0, 1), (1, 1, 1)] (by decide) (by decide)
    (consequence h [1, 1] (by decide))
  intro d hd hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact case1 φ (consequences (addRelation hz h) [[1, 0, 0], [-2, 1, 0], [0, 0, 1]] (by decide))
  · exact case1 φ (consequences (addRelation hz h) [[1, 0, -1], [-2, 1, 2], [0, 0, 1]] (by decide))
  · exact case1 φ (consequences (addRelation hz h) [[-1, 1, 1], [2, -1, -2], [0, 0, 1]] (by decide))

private theorem case7 (φ : Voltage →+ A)
    (h : Vanishes φ [(0, 0, 1)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 16) (by decide) φ
    (points [0, 1, 2, 0, 1, 2, 0, 3, 2, 1, 0, 2, 1, 0, 2, 3]) (0, 0, 0)
    [(0, 1, 0), (1, -1, 0), (1, 0, 0), (1, 1, 0), (2, 0, 0), (2, 1, 0)] (by decide) (by decide)
    (consequence h [0] (by decide))
  intro d hd hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact case0 φ (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
  · exact case2 φ (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
  · exact case3 φ (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
  · exact case4 φ (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
  · exact case5 φ (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))
  · exact case6 φ (consequences (addRelation hz h) [[1, 0], [0, 1]] (by decide))

private theorem case8 (φ : Voltage →+ A)
    (h : Vanishes φ [(1, 0, -1), (0, 1, 1)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 4) (by decide) φ
    (points [0, 1, 2, 3]) (1, 1, 0)
    [] (by decide) (by decide)
    (consequence h [1, 1] (by decide))
  intro d hd hz
  simp at hd

private theorem case9 (φ : Voltage →+ A)
    (h : Vanishes φ [(1, 0, -1)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 8) (by decide) φ
    (points [0, 1, 2, 3, 0, 1, 3, 2]) (1, 0, -1)
    [(0, 0, 1), (1, 1, 0)] (by decide) (by decide)
    (consequence h [1] (by decide))
  intro d hd hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact case3 φ (consequences (addRelation hz h) [[1, 1], [1, 0]] (by decide))
  · exact case8 φ (consequences (addRelation hz h) [[0, 1], [1, -1]] (by decide))

private theorem case10 (φ : Voltage →+ A)
    (h : Vanishes φ [(1, 0, 0), (0, 0, 2)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 8) (by decide) φ
    (points [0, 2, 1, 3, 0, 2, 1, 3]) (-2, 0, -2)
    [(1, 0, 1)] (by decide) (by decide)
    (consequence h [-2, -1] (by decide))
  intro d hd hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst d
  exact case3 φ (consequences (addRelation hz h) [[0, 1, 0], [1, -1, 0]] (by decide))

private theorem case11 (φ : Voltage →+ A)
    (h : Vanishes φ [(1, 0, 0), (0, 1, -1)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 8) (by decide) φ
    (points [0, 1, 2, 3, 0, 2, 1, 3]) (0, 1, -1)
    [(0, 1, 0), (1, 0, 1), (1, 1, 0)] (by decide) (by decide)
    (consequence h [0, 1] (by decide))
  intro d hd hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact case1 φ (consequences (addRelation hz h) [[0, 1, 0], [1, 0, 0], [1, 0, -1]] (by decide))
  · exact case1 φ (consequences (addRelation hz h) [[0, 1, 0], [1, -1, 1], [1, -1, 0]] (by decide))
  · exact case1 φ (consequences (addRelation hz h) [[0, 1, 0], [1, -1, 0], [1, -1, -1]] (by decide))

private theorem case12 (φ : Voltage →+ A)
    (h : Vanishes φ [(1, 0, 0), (0, 1, 0)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 4) (by decide) φ
    (points [0, 1, 2, 3]) (1, 1, 0)
    [] (by decide) (by decide)
    (consequence h [1, 1] (by decide))
  intro d hd hz
  simp at hd

private theorem case13 (φ : Voltage →+ A)
    (h : Vanishes φ [(1, 0, 0), (0, 1, 1)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 4) (by decide) φ
    (points [0, 1, 3, 2]) (0, -1, -1)
    [] (by decide) (by decide)
    (consequence h [0, -1] (by decide))
  intro d hd hz
  simp at hd

private theorem case14 (φ : Voltage →+ A)
    (h : Vanishes φ [(1, 0, 0), (0, 1, 2)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 8) (by decide) φ
    (points [0, 1, 3, 0, 2, 1, 3, 2]) (-1, -1, -2)
    [(0, 0, 1), (1, 0, 1), (1, 1, 1)] (by decide) (by decide)
    (consequence h [-1, -1] (by decide))
  intro d hd hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact case1 φ (consequences (addRelation hz h) [[0, 1, 0], [-2, 0, 1], [1, 0, 0]] (by decide))
  · exact case1 φ (consequences (addRelation hz h) [[0, 1, 0], [-2, 2, 1], [1, -1, 0]] (by decide))
  · exact case1 φ (consequences (addRelation hz h) [[0, 1, 0], [2, -2, -1], [-1, 1, 1]] (by decide))

private theorem case15 (φ : Voltage →+ A)
    (h : Vanishes φ [(1, 0, 0)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 16) (by decide) φ
    (points [0, 1, 2, 3, 1, 0, 3, 1, 0, 3, 2, 1, 3, 0, 1, 3]) (0, 0, 0)
    [(0, 0, 1), (0, 0, 2), (1, 1, -1), (1, 1, 0), (1, 1, 1), (1, 1, 2)] (by decide) (by decide)
    (consequence h [0] (by decide))
  intro d hd hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact case3 φ (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
  · exact case10 φ (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
  · exact case11 φ (consequences (addRelation hz h) [[0, 1], [1, -1]] (by decide))
  · exact case12 φ (consequences (addRelation hz h) [[0, 1], [1, -1]] (by decide))
  · exact case13 φ (consequences (addRelation hz h) [[0, 1], [1, -1]] (by decide))
  · exact case14 φ (consequences (addRelation hz h) [[0, 1], [1, -1]] (by decide))

private theorem case16 (φ : Voltage →+ A)
    (h : Vanishes φ [(1, 0, 1)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 4) (by decide) φ
    (points [0, 2, 1, 3]) (-1, 0, -1)
    [] (by decide) (by decide)
    (consequence h [-1] (by decide))
  intro d hd hz
  simp at hd

private theorem case17 (φ : Voltage →+ A)
    (h : Vanishes φ [(1, 0, 1), (0, 0, 2)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 4) (by decide) φ
    (points [0, 2, 1, 3]) (-1, 0, -1)
    [] (by decide) (by decide)
    (consequence h [-1, 0] (by decide))
  intro d hd hz
  simp at hd

private theorem case18 (φ : Voltage →+ A)
    (h : Vanishes φ [(2, 0, 0), (0, 0, 2)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 8) (by decide) φ
    (points [0, 2, 1, 3, 0, 2, 1, 3]) (-2, 0, -2)
    [(1, 0, 1)] (by decide) (by decide)
    (consequence h [-1, -1] (by decide))
  intro d hd hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst d
  exact case17 φ (consequences (addRelation hz h) [[1, 0, 0], [2, -1, 0]] (by decide))

private theorem case19 (φ : Voltage →+ A)
    (h : Vanishes φ [(1, 0, 2), (0, 0, 4)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 16) (by decide) φ
    (points [0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 1, 3]) (-4, 0, -4)
    [(1, 0, 1), (2, 0, 2), (3, 0, 3)] (by decide) (by decide)
    (consequence h [-4, 1] (by decide))
  intro d hd hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact case3 φ (consequences (addRelation hz h) [[2, -1, 0], [-1, 1, 0]] (by decide))
  · exact case10 φ (consequences (addRelation hz h) [[1, -1, 0], [-1, 2, 0]] (by decide))
  · exact case3 φ (consequences (addRelation hz h) [[-2, 7, -2], [1, -3, 1]] (by decide))

private theorem case20 (φ : Voltage →+ A)
    (h : Vanishes φ [(2, 0, 0)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 16) (by decide) φ
    (points [0, 1, 2, 0, 3, 1, 0, 3, 1, 0, 2, 1, 3, 0, 1, 3]) (0, 0, 0)
    [(0, 0, 1), (0, 0, 2), (1, 0, -1), (1, 0, 0), (1, 0, 1), (1, 0, 2)] (by decide) (by decide)
    (consequence h [0] (by decide))
  intro d hd hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact case5 φ (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
  · exact case18 φ (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
  · exact case17 φ (consequences (addRelation hz h) [[-1, 1], [-2, 1]] (by decide))
  · exact case15 φ (consequences (addRelation hz h) [[1, 0]] (by decide))
  · exact case17 φ (consequences (addRelation hz h) [[1, 0], [2, -1]] (by decide))
  · exact case19 φ (consequences (addRelation hz h) [[1, 0], [2, -1]] (by decide))

private theorem case21 (φ : Voltage →+ A)
    (h : Vanishes φ [(2, 0, 1), (0, 0, 2)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 16) (by decide) φ
    (points [0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 1, 3]) (-4, 0, -4)
    [(1, 0, 1), (2, 0, 2), (3, 0, 3)] (by decide) (by decide)
    (consequence h [-2, -1] (by decide))
  intro d hd hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact case3 φ (consequences (addRelation hz h) [[-1, 1, 0], [2, -1, 0]] (by decide))
  · exact case5 φ (consequences (addRelation hz h) [[-1, 2, 0], [1, -1, 0]] (by decide))
  · exact case3 φ (consequences (addRelation hz h) [[5, -7, -4], [-2, 3, 2]] (by decide))

private theorem case22 (φ : Voltage →+ A)
    (h : Vanishes φ [(1, 0, 2), (0, 1, 1), (0, 0, 3)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 4) (by decide) φ
    (points [0, 1, 2, 3]) (1, 1, 0)
    [] (by decide) (by decide)
    (consequence h [1, 1, -1] (by decide))
  intro d hd hz
  simp at hd

private theorem case23 (φ : Voltage →+ A)
    (h : Vanishes φ [(1, 0, 2), (0, 0, 3)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 8) (by decide) φ
    (points [0, 1, 2, 3, 0, 1, 3, 2]) (1, 0, -1)
    [(0, 0, 1), (1, 1, 0)] (by decide) (by decide)
    (consequence h [1, -1] (by decide))
  intro d hd hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact case3 φ (consequences (addRelation hz h) [[-2, 1, 0], [1, 0, 0]] (by decide))
  · exact case22 φ (consequences (addRelation hz h) [[0, 1, 0], [1, -1, 1], [0, 0, 1]] (by decide))

private theorem case24 (φ : Voltage →+ A)
    (h : Vanishes φ [(2, 0, 1)]) : HasShortCycle (normalGraph φ) := by
  apply template (n := 16) (by decide) φ
    (points [0, 1, 2, 0, 3, 1, 0, 3, 1, 0, 2, 1, 3, 0, 1, 3]) (0, 0, 0)
    [(0, 0, 1), (0, 0, 2), (1, 0, -1), (1, 0, 0), (1, 0, 1), (1, 0, 2)] (by decide) (by decide)
    (consequence h [0] (by decide))
  intro d hd hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact case5 φ (consequences (addRelation hz h) [[-1, 1], [1, 0]] (by decide))
  · exact case21 φ (consequences (addRelation hz h) [[0, 1], [1, 0]] (by decide))
  · exact case23 φ (consequences (addRelation hz h) [[-1, 1], [-2, 1]] (by decide))
  · exact case3 φ (consequences (addRelation hz h) [[1, 0], [-2, 1]] (by decide))
  · exact case3 φ (consequences (addRelation hz h) [[-1, 1], [2, -1]] (by decide))
  · exact case23 φ (consequences (addRelation hz h) [[1, 0], [2, -1]] (by decide))

private theorem case25 (φ : Voltage →+ A)
    (h : Vanishes φ []) : HasShortCycle (normalGraph φ) := by
  apply template (n := 16) (by decide) φ
    (points [0, 1, 2, 0, 1, 2, 0, 3, 1, 0, 2, 1, 0, 2, 1, 3]) (0, 0, 0)
    [(0, 0, 1), (1, 0, -1), (1, 0, 0), (1, 0, 1), (2, 0, 0), (2, 0, 1)] (by decide) (by decide)
    (consequence h [] (by decide))
  intro d hd hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact case7 φ (consequences (addRelation hz h) [[1]] (by decide))
  · exact case9 φ (consequences (addRelation hz h) [[1]] (by decide))
  · exact case15 φ (consequences (addRelation hz h) [[1]] (by decide))
  · exact case16 φ (consequences (addRelation hz h) [[1]] (by decide))
  · exact case20 φ (consequences (addRelation hz h) [[1]] (by decide))
  · exact case24 φ (consequences (addRelation hz h) [[1]] (by decide))

theorem normal_short (φ : Voltage →+ A) : HasShortCycle (normalGraph φ) :=
  case25 φ (by simp [Vanishes])

private def evaluate (a b c : A) : Voltage →+ A where
  toFun z := z.1 • a + z.2.1 • b + z.2.2 • c
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, add_zsmul]; abel

/-- Every abelian voltage cover of the tetrahedron, with arbitrary voltages
on all six edges, contains a simple cycle of length 4, 8 or 16. -/
theorem abelian_cover_short (ω : Color → Color → A) (rev : ∀ i j, ω j i = -ω i j) :
    HasShortCycle (coverGraph ω rev) := by
  let offset (i : Color) : A := if i = 0 then 0 else ω 0 i
  let chord (i j : Color) := offset i + ω i j - offset j
  let φ := evaluate (chord 1 2) (chord 2 3) (chord 3 1)
  have shift (i j : Color) (hne : i ≠ j) :
      φ (edgeVector i j) + offset j = offset i + ω i j := by
    fin_cases i <;> fin_cases j <;> first
    | exact (hne rfl).elim
    | simp [φ, evaluate, edgeVector, chord, offset, rev 0 1, rev 0 2, rev 0 3,
            rev 1 2, rev 2 3, rev 3 1] <;> abel
  let f (u : Color × A) : Color × A := (u.1, u.2 + offset u.1)
  have injective : Injective f := by
    rintro ⟨i, x⟩ ⟨j, y⟩ eq
    have ij : i = j := congrArg Prod.fst eq
    subst j
    exact Prod.ext rfl (add_right_cancel (congrArg Prod.snd eq))
  have copy : normalGraph φ ⊑ coverGraph ω rev := by
    refine ⟨⟨⟨f, ?_⟩, injective⟩⟩
    intro u v huv
    obtain ⟨hne, hv⟩ := huv
    refine ⟨hne, ?_⟩
    change v.2 + offset v.1 = u.2 + offset u.1 + ω u.1 v.1
    rw [hv, add_assoc, shift u.1 v.1 hne, add_assoc]
  rcases normal_short φ with h | h | h
  · exact Or.inl (h.trans copy)
  · exact Or.inr (Or.inl (h.trans copy))
  · exact Or.inr (Or.inr (h.trans copy))

section Sharpness
open Fin.NatCast

private def routes {V : Type*} [DecidableEq V] (nb : V → List V) (root : V) :
    ℕ → V → List V → Bool
  | 0, u, _ => (nb u).contains root
  | steps + 1, u, seen => (nb u).any fun v =>
      !(seen.contains v) && routes nb root steps v (v :: seen)

private theorem route_of_copy {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (nb : V → List V) (complete : ∀ {u v}, G.Adj u v → v ∈ nb u)
    {n : ℕ} (hn : 3 ≤ n) (copy : cycleGraph n ⊑ G) :
    ∃ root, routes nb root (n - 1) root [root] = true := by
  obtain ⟨c⟩ := copy
  let : NeZero n := ⟨by omega⟩
  let seq (i : ℕ) : V := c (i : Fin n)
  have closed : seq n = seq 0 := by simp [seq]
  have side (i : ℕ) : seq (i + 1) ∈ nb (seq i) := by
    apply complete
    apply c.toHom.map_rel'
    apply cycleGraph_adj'.mpr
    right
    simp [Nat.mod_eq_of_lt (show 1 < n by omega)]
  have distinct {i j : ℕ} (hi : i < n) (hj : j < n) (h : seq i = seq j) : i = j := by
    simpa only [Fin.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
      using congrArg Fin.val (c.injective h)
  have follow (r i : ℕ) (seen : List V) (endAt : i + r + 1 = n)
      (earlier : ∀ z ∈ seen, ∃ j ≤ i, seq j = z) :
      routes nb (seq 0) r (seq i) seen = true := by
    induction r generalizing i seen with
    | zero =>
      have last : i + 1 = n := by omega
      simpa [routes, last, closed] using side i
    | succ r ih =>
      apply List.any_eq_true.mpr
      refine ⟨seq (i + 1), side i, ?_⟩
      have fresh : seq (i + 1) ∉ seen := by
        intro mem
        obtain ⟨j, hj, eq⟩ := earlier _ mem
        have := distinct (by omega) (by omega) eq
        omega
      have rest := ih (i + 1) (seq (i + 1) :: seen) (by omega) (by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | mem
        · exact ⟨i + 1, le_rfl, rfl⟩
        · obtain ⟨j, hj, eq⟩ := earlier z mem
          exact ⟨j, by omega, eq⟩)
      simp [fresh, rest]
  exact ⟨seq 0, follow _ 0 _ (by omega) (by simp)⟩

/-- On seven sheets assign voltages 0, 1 and 2 to 12, 23 and 31, respectively. -/
private def sevenVoltage (i j : Color) : ZMod 7 :=
  let v := edgeVector i j
  (v.2.1 : ZMod 7) + 2 * (v.2.2 : ZMod 7)

private theorem sevenReverse : ∀ i j, sevenVoltage j i = -sevenVoltage i j := by decide

def sevenCover := coverGraph sevenVoltage sevenReverse

private def sevenNeighbors (u : Color × ZMod 7) : List (Color × ZMod 7) :=
  ((List.finRange 4).filter (· ≠ u.1)).map (fun v => (v, u.2 + sevenVoltage u.1 v))

private theorem seven_complete {u v : Color × ZMod 7} (h : sevenCover.Adj u v) :
    v ∈ sevenNeighbors u := by
  obtain ⟨hne, heq⟩ := h
  apply List.mem_map.mpr
  refine ⟨v.1, ?_, Prod.ext rfl heq.symm⟩
  simp [hne.symm]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem seven_check :
    ∀ u, routes sevenNeighbors u 3 u [u] = false ∧
         routes sevenNeighbors u 7 u [u] = false := by decide

/-- The bound 16 is attained by a 28-vertex cyclic cover. -/
theorem seven_sharp :
    ¬ cycleGraph 4 ⊑ sevenCover ∧ ¬ cycleGraph 8 ⊑ sevenCover ∧ cycleGraph 16 ⊑ sevenCover := by
  have no4 : ¬ cycleGraph 4 ⊑ sevenCover := by
    intro copy
    obtain ⟨u, h⟩ := route_of_copy sevenNeighbors seven_complete (by decide : 3 ≤ 4) copy
    exact Bool.noConfusion (h.symm.trans (seven_check u).1)
  have no8 : ¬ cycleGraph 8 ⊑ sevenCover := by
    intro copy
    obtain ⟨u, h⟩ := route_of_copy sevenNeighbors seven_complete (by decide : 3 ≤ 8) copy
    exact Bool.noConfusion (h.symm.trans (seven_check u).2)
  refine ⟨no4, no8, ?_⟩
  exact ((abelian_cover_short sevenVoltage sevenReverse).resolve_left no4).resolve_left no8

end Sharpness

end Erdos64Tetrahedron
