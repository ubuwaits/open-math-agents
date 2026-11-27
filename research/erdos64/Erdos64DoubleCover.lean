import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Tactic

/-!
# Projecting eight-cycles from the bipartite double cover

Alternating vertices of a simple eight-cycle remain pairwise distinct on
each sheet. The only possible identifications occur between the two sheets.
This file describes exactly what can be seen downstairs in a square-free
simple graph. Containment throughout means an ordinary subgraph.
-/

namespace Erdos64DoubleCover

open Function SimpleGraph

private def listed {n : ℕ} (edges : List (Fin n × Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => (i,j) ∈ edges

private instance {n : ℕ} (edges : List (Fin n × Fin n)) : DecidableRel (listed edges).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ ((_ , _) ∈ edges ∨ (_, _) ∈ edges)))

/-- Three internally disjoint paths of lengths 1, 2 and 4 between 0 and 1. -/
def theta124 : SimpleGraph (Fin 6) :=
  listed [(0,1),(0,2),(2,1),(0,3),(3,4),(4,5),(5,1)]

/-- Two vertex-disjoint triangles joined by a single edge. -/
def joinedTriangles : SimpleGraph (Fin 6) :=
  listed [(0,1),(1,2),(2,0),(3,4),(4,5),(5,3),(2,3)]

/-- A triangle and a pentagon meeting at exactly one vertex. -/
def trianglePentagon : SimpleGraph (Fin 7) :=
  listed [(0,1),(1,2),(2,0),(0,3),(3,4),(4,5),(5,6),(6,0)]

private instance : DecidableRel trianglePentagon.Adj := by unfold trianglePentagon; infer_instance

private inductive Shape | square | octagon | theta | joined | wedge
  deriving DecidableEq

private def count : Shape → ℕ
  | .square => 4 | .octagon => 8 | .theta | .joined => 6 | .wedge => 7

private def graph : (t : Shape) → SimpleGraph (Fin (count t))
  | .square => cycleGraph 4 | .octagon => cycleGraph 8 | .theta => theta124
  | .joined => joinedTriangles | .wedge => trianglePentagon

private instance shapeAdj : (t : Shape) → DecidableRel (graph t).Adj
  | .square => inferInstanceAs (DecidableRel (cycleGraph 4).Adj)
  | .octagon => inferInstanceAs (DecidableRel (cycleGraph 8).Adj)
  | .theta => inferInstanceAs (DecidableRel (listed (n := 6) _).Adj)
  | .joined => inferInstanceAs (DecidableRel (listed (n := 6) _).Adj)
  | .wedge => inferInstanceAs (DecidableRel (listed (n := 7) _).Adj)

private abbrev Pos := Fin 4 ⊕ Fin 4

private def ring : Fin 8 → Pos :=
  ![.inl 0,.inr 0,.inl 1,.inr 1,.inl 2,.inr 2,.inl 3,.inr 3]

private def ringIndex : Pos → Fin 8 :=
  Sum.elim ![0,2,4,6] ![1,3,5,7]

private def name (overlap : Fin 4 → Option (Fin 4)) : Pos → Pos
  | .inl k => .inl k
  | .inr k => match overlap k with | some j => .inl j | none => .inr k

private theorem encode {V : Type*} (ev od : Fin 4 → V) (he : Injective ev) (ho : Injective od) :
    ∃ f : Fin 4 → Option (Fin 4), ∀ i j : Pos,
      name f i = name f j ↔ Sum.elim ev od i = Sum.elim ev od j := by
  classical
  let f (k : Fin 4) : Option (Fin 4) :=
    if h : ∃ j, ev j = od k then some h.choose else none
  have isSome (k j : Fin 4) : f k = some j ↔ ev j = od k := by
    dsimp only [f]
    split
    next h =>
      simp only [Option.some.injEq]
      exact ⟨fun h' => h' ▸ h.choose_spec, fun h' => he (h.choose_spec.trans h'.symm)⟩
    next h => exact ⟨by simp, fun eq => (h ⟨j,eq⟩).elim⟩
  have eval (i : Pos) : Sum.elim ev od (name f i) = Sum.elim ev od i := by
    cases i with
    | inl j => rfl
    | inr k =>
      cases h : f k with
      | none => simp [name, h]
      | some j => simpa [name, h] using (isSome k j).mp h
  refine ⟨f, fun i j => ⟨fun eq => (eval i).symm.trans ((congrArg (Sum.elim ev od) eq).trans (eval j)), ?_⟩⟩
  cases i with
  | inl a =>
    cases j with
    | inl b => intro eq; exact congrArg Sum.inl (he eq)
    | inr b => intro eq; simp [name, (isSome b a).mpr eq]
  | inr a =>
    cases j with
    | inl b => intro eq; simp [name, (isSome a b).mpr eq.symm]
    | inr b => intro eq; rw [ho eq]

private def valid (f : Fin 4 → Option (Fin 4)) : Prop :=
  Injective (fun i => name f (.inr i)) ∧ ∀ i : Fin 8, name f (ring i) ≠ name f (ring (i+1))

private instance (f : Fin 4 → Option (Fin 4)) : Decidable (valid f) := by unfold valid; infer_instance

private structure Witness where
  shape : Shape
  vertex : Fin (count shape) → Fin 8


/-- For each admissible identification pattern, list the eight-cycle positions
which exhibit one of the five subgraphs. The proof below checks every entry. -/
private def witness (f : Fin 4 → Option (Fin 4)) : Witness :=
  match f 0, f 1, f 2, f 3 with
  | none, none, none, none => ⟨.octagon, ![0,1,2,3,4,5,6,7]⟩
  | none, none, none, some 1 => ⟨.wedge, ![2,0,1,6,5,4,3]⟩
  | none, none, none, some 2 => ⟨.wedge, ![4,6,5,0,1,2,3]⟩
  | none, none, some 0, none => ⟨.wedge, ![0,6,7,4,3,2,1]⟩
  | none, none, some 0, some 1 => ⟨.square, ![0,2,3,4]⟩
  | none, none, some 0, some 2 => ⟨.theta, ![0,4,6,1,2,3]⟩
  | none, none, some 1, none => ⟨.wedge, ![2,4,3,6,7,0,1]⟩
  | none, none, some 1, some 2 => ⟨.square, ![0,4,2,1]⟩
  | none, some 3, none, none => ⟨.wedge, ![3,4,5,2,1,0,7]⟩
  | none, some 3, none, some 1 => ⟨.joined, ![0,1,2,3,4,5]⟩
  | none, some 3, none, some 2 => ⟨.theta, ![4,3,5,0,1,2]⟩
  | none, some 3, some 0, none => ⟨.square, ![0,4,3,7]⟩
  | none, some 3, some 0, some 1 => ⟨.square, ![0,2,3,4]⟩
  | none, some 3, some 0, some 2 => ⟨.square, ![0,3,2,1]⟩
  | none, some 3, some 1, none => ⟨.theta, ![2,3,4,1,0,7]⟩
  | none, some 3, some 1, some 2 => ⟨.square, ![0,4,2,1]⟩
  | none, some 0, none, none => ⟨.wedge, ![0,2,1,4,5,6,7]⟩
  | none, some 0, none, some 1 => ⟨.theta, ![0,2,1,4,5,6]⟩
  | none, some 0, none, some 2 => ⟨.joined, ![2,1,0,4,6,5]⟩
  | none, some 0, some 1, none => ⟨.square, ![0,2,6,7]⟩
  | none, some 0, some 1, some 2 => ⟨.square, ![0,2,6,4]⟩
  | some 2, none, none, none => ⟨.wedge, ![1,2,3,0,7,6,5]⟩
  | some 2, none, none, some 1 => ⟨.square, ![0,2,3,1]⟩
  | some 2, none, some 0, none => ⟨.joined, ![2,3,1,0,6,7]⟩
  | some 2, none, some 0, some 1 => ⟨.square, ![0,2,3,1]⟩
  | some 2, none, some 1, none => ⟨.theta, ![2,1,3,6,7,0]⟩
  | some 2, some 3, none, none => ⟨.square, ![0,1,3,7]⟩
  | some 2, some 3, none, some 1 => ⟨.square, ![0,2,3,1]⟩
  | some 2, some 3, some 0, none => ⟨.square, ![0,1,2,3]⟩
  | some 2, some 3, some 0, some 1 => ⟨.square, ![0,2,1,3]⟩
  | some 2, some 3, some 1, none => ⟨.square, ![0,1,3,7]⟩
  | some 2, some 0, none, none => ⟨.theta, ![0,1,2,7,6,5]⟩
  | some 2, some 0, none, some 1 => ⟨.square, ![2,1,5,6]⟩
  | some 2, some 0, some 1, none => ⟨.square, ![0,2,6,7]⟩
  | some 3, none, none, none => ⟨.wedge, ![1,0,7,2,3,4,5]⟩
  | some 3, none, none, some 1 => ⟨.theta, ![2,1,0,3,4,5]⟩
  | some 3, none, none, some 2 => ⟨.square, ![0,4,5,1]⟩
  | some 3, none, some 0, none => ⟨.theta, ![0,1,7,4,3,2]⟩
  | some 3, none, some 0, some 1 => ⟨.square, ![0,2,3,4]⟩
  | some 3, none, some 0, some 2 => ⟨.square, ![2,1,4,3]⟩
  | some 3, none, some 1, none => ⟨.joined, ![0,7,1,2,4,3]⟩
  | some 3, none, some 1, some 2 => ⟨.square, ![0,4,2,1]⟩
  | some 3, some 0, none, none => ⟨.square, ![0,2,1,7]⟩
  | some 3, some 0, none, some 1 => ⟨.square, ![0,4,5,1]⟩
  | some 3, some 0, none, some 2 => ⟨.square, ![0,2,1,4]⟩
  | some 3, some 0, some 1, none => ⟨.square, ![0,2,1,7]⟩
  | some 3, some 0, some 1, some 2 => ⟨.square, ![0,2,4,1]⟩
  | _, _, _, _ => ⟨.square, ![0,1,2,3]⟩

private def imageEdge (f : Fin 4 → Option (Fin 4)) (a b : Pos) : Prop :=
  ∃ k : Fin 8, let u := name f (ring k); let v := name f (ring (k+1))
    (u = a ∧ v = b) ∨ (u = b ∧ v = a)

private instance (f : Fin 4 → Option (Fin 4)) (a b : Pos) : Decidable (imageEdge f a b) := by
  unfold imageEdge; infer_instance

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem certificate : ∀ f : Fin 4 → Option (Fin 4), valid f →
    let w := witness f
    let v := fun i => name f (ring (w.vertex i))
    Injective v ∧ ∀ i j, (graph w.shape).Adj i j → imageEdge f (v i) (v j) := by
  decide

private def project {V : Type*} : V ⊕ V → V := Sum.elim id id

private theorem project_ext {V : Type*} {x y : V ⊕ V}
    (s : x.isLeft = y.isLeft) (hp : project x = project y) : x = y := by
  cases x <;> cases y <;> simp_all [project]

private theorem projected_edge {V : Type*} {G : SimpleGraph V} {x y : V ⊕ V}
    (h : G.bipartiteDoubleCover.Adj x y) : G.Adj (project x) (project y) ∧ x.isLeft ≠ y.isLeft := by
  cases x <;> cases y <;> simp_all [project]

set_option maxRecDepth 8192 in
private theorem constantSheets : ∀ sheet : Fin 8 → Bool, (∀ i, sheet i ≠ sheet (i+1)) →
    (∀ i j, sheet (ringIndex (.inl i)) = sheet (ringIndex (.inl j))) ∧
    (∀ i j, sheet (ringIndex (.inr i)) = sheet (ringIndex (.inr j))) := by decide

private theorem shape_below {V : Type*} (G : SimpleGraph V) (h : cycleGraph 8 ⊑ G.bipartiteDoubleCover) :
    ∃ t : Shape, graph t ⊑ G := by
  obtain ⟨c⟩ := h
  have nextEdge : ∀ i : Fin 8, (cycleGraph 8).Adj i (i+1) := by decide
  let point (i : Fin 8) := project (c i)
  let sheet (i : Fin 8) := (c i).isLeft
  have adj (i : Fin 8) := projected_edge (c.toHom.map_rel' (nextEdge i))
  have sh := constantSheets sheet (fun i => (adj i).2)
  let ev (i : Fin 4) := point (ringIndex (.inl i))
  let od (i : Fin 4) := point (ringIndex (.inr i))
  have he : Injective ev := by
    intro i j eq
    have inj : Injective (fun k : Fin 4 => ringIndex (.inl k)) := by decide
    exact inj (c.injective (project_ext (sh.1 i j) eq))
  have ho : Injective od := by
    intro i j eq
    have inj : Injective (fun k : Fin 4 => ringIndex (.inr k)) := by decide
    exact inj (c.injective (project_ext (sh.2 i j) eq))
  obtain ⟨f,rep⟩ := encode ev od he ho
  let value := Sum.elim ev od
  have val_pos (z : Pos) : value z = point (ringIndex z) := by cases z <;> rfl
  have index_ring : ∀ k : Fin 8, ringIndex (ring k) = k := by decide
  have edge (k : Fin 8) : G.Adj (value (ring k)) (value (ring (k+1))) := by
    simp only [val_pos, index_ring]
    exact (adj k).1
  have validf : valid f := by
    refine ⟨fun i j eq => ho ((rep _ _).mp eq), fun k eq => (edge k).ne ((rep _ _).mp eq)⟩
  let w := witness f
  obtain ⟨inj,sides⟩ := certificate f validf
  let label (i : Fin (count w.shape)) := value (ring (w.vertex i))
  refine ⟨w.shape, ⟨⟨⟨label, ?_⟩, fun _ _ eq => inj ((rep _ _).mpr eq)⟩⟩⟩
  intro i j hij
  obtain ⟨k,h | h⟩ := sides i j hij
  · have a : value (ring k) = label i := (rep _ _).mp h.1
    have b : value (ring (k+1)) = label j := (rep _ _).mp h.2
    change G.Adj (label i) (label j)
    rw [← a, ← b]
    exact edge k
  · have a : value (ring (k+1)) = label i := (rep _ _).mp h.2
    have b : value (ring k) = label j := (rep _ _).mp h.1
    change G.Adj (label i) (label j)
    rw [← a, ← b]
    exact (edge k).symm

private def projectedWord : (t : Shape) → Fin 8 → Fin (count t)
  | .square => (![0,1,2,3,0,1,2,3] : Fin 8 → Fin 4)
  | .octagon => (![0,1,2,3,4,5,6,7] : Fin 8 → Fin 8)
  | .theta => (![0,1,2,0,1,5,4,3] : Fin 8 → Fin 6)
  | .joined => (![0,1,2,3,4,5,3,2] : Fin 8 → Fin 6)
  | .wedge => (![0,1,2,0,3,4,5,6] : Fin 8 → Fin 7)

private def liftedWord (t : Shape) (i : Fin 8) : Fin (count t) ⊕ Fin (count t) :=
  if i.val % 2 = 0 then .inl (projectedWord t i) else .inr (projectedWord t i)

private theorem lifts (t : Shape) (h : t ≠ .square) : cycleGraph 8 ⊑ (graph t).bipartiteDoubleCover := by
  have inj : ∀ s : Shape, s ≠ .square → Injective (liftedWord s) := by intro s; cases s <;> decide
  have adj : ∀ s : Shape, s ≠ .square → ∀ i j, (cycleGraph 8).Adj i j →
      (graph s).bipartiteDoubleCover.Adj (liftedWord s i) (liftedWord s j) := by
    intro s; cases s <;> decide
  exact ⟨⟨⟨liftedWord t, fun e => adj t h _ _ e⟩, inj t h⟩⟩

private theorem double_mono {U V : Type*} {H : SimpleGraph U} {G : SimpleGraph V}
    (sub : H ⊑ G) : H.bipartiteDoubleCover ⊑ G.bipartiteDoubleCover := by
  obtain ⟨e⟩ := sub
  refine ⟨⟨⟨Sum.map e e, ?_⟩, Sum.map_injective.mpr ⟨e.injective,e.injective⟩⟩⟩
  rintro (i | i) (j | j) h <;> first | exact h.elim | exact e.toHom.map_rel' h

/-- Exact alternatives in any square-free simple graph. -/
theorem eight_iff {V : Type*} (G : SimpleGraph V) (no4 : ¬ cycleGraph 4 ⊑ G) :
    cycleGraph 8 ⊑ G.bipartiteDoubleCover ↔
      cycleGraph 8 ⊑ G ∨ theta124 ⊑ G ∨ joinedTriangles ⊑ G ∨ trianglePentagon ⊑ G := by
  constructor
  · intro h
    obtain ⟨t,sub⟩ := shape_below G h
    cases t with
    | square => exact (no4 sub).elim
    | octagon => exact Or.inl sub
    | theta => exact Or.inr (Or.inl sub)
    | joined => exact Or.inr (Or.inr (Or.inl sub))
    | wedge => exact Or.inr (Or.inr (Or.inr sub))
  · rintro (h | h | h | h)
    · exact (lifts .octagon (by decide)).trans (double_mono h)
    · exact (lifts .theta (by decide)).trans (double_mono h)
    · exact (lifts .joined (by decide)).trans (double_mono h)
    · exact (lifts .wedge (by decide)).trans (double_mono h)

/-- In a subcubic graph the triangle and pentagon cannot meet only at one
vertex, because that vertex would have four distinct neighbors. -/
theorem subcubic_eight_iff {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (subcubic : ∀ v, G.degree v ≤ 3) (no4 : ¬ cycleGraph 4 ⊑ G) :
    cycleGraph 8 ⊑ G.bipartiteDoubleCover ↔ cycleGraph 8 ⊑ G ∨ theta124 ⊑ G ∨ joinedTriangles ⊑ G := by
  rw [eight_iff G no4]
  have four : trianglePentagon.degree 0 = 4 := by decide
  have exclude : ¬ trianglePentagon ⊑ G := by
    rintro ⟨c⟩
    have impossible := (c.degree_le 0).trans (subcubic (c 0))
    rw [four] at impossible
    omega
  tauto

end Erdos64DoubleCover
