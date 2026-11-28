import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1
import Mathlib

/-!
# A triangle-contraction reduction for the bridgeless cubic case of Erdős–Gyárfás

Contract a triangle and find a power-of-two cycle in the smaller cubic graph.
A cycle avoiding the contracted vertex survives unchanged. Traversing its
triangle adds one or two edges. This leaves a rooted cycle-length problem and
the square-free, octagon-free triangle-free case. The interval argument
is adapted from Daniel Garcia, arXiv:2609.04686, Lemma 3.2.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R2

open SimpleGraph Function Fin.NatCast

/-- The triangle-free case. A square or an octagon already settles the target. -/
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.Connected → (∀ v, G.degree v = 3) →
    (∀ ⦃a b⦄, G.Adj a b → ¬G.IsBridge s(a,b)) →
    (¬∃ e : Fin 3 ↪ V, ∀ i j, i ≠ j → G.Adj (e i) (e j)) →
    (¬cycleGraph 4 ⊑ G) → (¬cycleGraph 8 ⊑ G) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G

/-- Every power-of-two cycle visits the designated vertex and at least one exists.
Find a cycle through that vertex one or two edges short of a power of two. -/
def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (r : V),
    G.Connected → (∀ v, G.degree v = 3) →
    (∀ ⦃a b⦄, G.Adj a b → ¬G.IsBridge s(a,b)) →
    (∀ c : (cycleGraph 3).Copy G, r ∉ Set.range c) →
    (∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G) →
    (∀ (k : ℕ), 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G, r ∈ Set.range c) →
    ∃ (n k : ℕ) (c : (cycleGraph n).Copy G),
      3 ≤ n ∧ 2 ≤ k ∧ r ∈ Set.range c ∧ (n+1=2^k ∨ n+2=2^k)

theorem cycle_of_ring {V : Type*} (G : SimpleGraph V) (l : List V)
    (large : 3 ≤ l.length) (distinct : l.Nodup) (path : l.IsChain G.Adj)
    (close : ∀ h : l ≠ [], G.Adj (l.getLast h) (l.head h)) : cycleGraph l.length ⊑ G := by
  let : NeZero l.length := ⟨by omega⟩
  have pos : 1 < l.length := by omega
  have next (i : Fin l.length) : G.Adj (l.get i) (l.get (i+1)) := by
    have val : (i+1 : Fin l.length).val = (i.val+1) % l.length := by
      rw [Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt pos]
    by_cases inside : i.val+1 < l.length
    · have eq : (i+1 : Fin l.length).val = i.val+1 := val.trans (Nat.mod_eq_of_lt inside)
      simpa only [List.get_eq_getElem,eq] using path.getElem i.val inside
    · have last : i.val=l.length-1 := by omega
      have start : (i+1 : Fin l.length).val = 0 := by rw [val,show i.val+1=l.length by omega,Nat.mod_self]
      have h := close (List.length_pos_iff.mp (by omega))
      simpa only [List.get_eq_getElem,last,start,List.head_eq_getElem,List.getLast_eq_getElem] using h
  refine ⟨⟨⟨l.get,?_⟩,distinct.injective_get⟩⟩
  intro i j adj
  have diff : i-j=1 ∨ j-i=1 := by
    simpa only [Fin.ext_iff,Fin.val_one',Nat.mod_eq_of_lt pos] using cycleGraph_adj'.mp adj
  rcases diff with h | h
  · have eq : i=j+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h
    simpa only [eq] using (next j).symm
  · have eq : j=i+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h
    simpa only [eq] using next i

/-- Four cyclically adjacent vertices with distinct opposite pairs form a square. -/
theorem square_of_four {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (da : G.Adj d a)
    (ac : a ≠ c) (bd : b ≠ d) : cycleGraph 4 ⊑ G := by
  have cut := cycle_of_ring G [a,b,c,d] (by simp)
    (by simp [ab.ne,ac,da.ne.symm,bc.ne,bd,cd.ne])
    (by simp [ab,bc,cd]) (by simpa using da)
  exact cut

/-- Concatenating mutually disjoint nonempty paths around a ring gives a
simple cycle with as many vertices as the sum of the path vertex counts. -/
theorem cycle_of_chunks {V : Type*} (G : SimpleGraph V) {n : ℕ} [NeZero n]
    (chunk : Fin n → List V) (nonempty : ∀ i, chunk i ≠ [])
    (distinct : ∀ i, (chunk i).Nodup) (apart : ∀ i j, i ≠ j → (chunk i).Disjoint (chunk j))
    (path : ∀ i, (chunk i).IsChain G.Adj)
    (link : ∀ i, G.Adj ((chunk i).getLast (nonempty i)) ((chunk (i+1)).head (nonempty _)))
    (large : 3 ≤ (List.ofFn chunk).flatten.length) :
    cycleGraph (List.ofFn chunk).flatten.length ⊑ G := by
  let blocks := List.ofFn chunk
  have noEmpty : [] ∉ blocks := by
    intro h
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
    exact nonempty i hi
  have blocksNe : blocks ≠ [] := by simp [blocks,NeZero.ne n]
  have firstNonempty : blocks.head blocksNe ≠ [] := fun h => noEmpty (h ▸ List.head_mem blocksNe)
  have lastNonempty : blocks.getLast blocksNe ≠ [] := fun h => noEmpty (h ▸ List.getLast_mem blocksNe)
  apply cycle_of_ring G blocks.flatten large
  · apply List.nodup_flatten.mpr
    constructor
    · intro row mem
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
      exact distinct i
    · exact List.pairwise_ofFn.mpr (fun {_ _} lt => apart _ _ (ne_of_lt lt))
  · apply (List.isChain_flatten noEmpty).mpr
    constructor
    · intro row mem
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
      exact path i
    · apply List.isChain_ofFn.mpr
      intro j hj x hx y hy
      let i : Fin n := ⟨j,by omega⟩
      have follow : i+1 = (⟨j+1,hj⟩ : Fin n) := by
        apply Fin.ext
        simp only [Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt (show 1<n by omega)]
        exact Nat.mod_eq_of_lt hj
      have h := link i
      rw [follow] at h
      simp only [List.getLast?_eq_some_getLast (nonempty _),Option.mem_some_iff] at hx
      simp only [List.head?_eq_some_head (nonempty _),Option.mem_some_iff] at hy
      subst x
      subst y
      exact h
  · intro ne
    rw [List.head_flatten_eq_head_head ne firstNonempty,List.getLast_flatten_eq_getLast_getLast ne lastNonempty]
    let last : Fin n := ⟨n-1,by have := NeZero.pos n; omega⟩
    have restart : last+1 = (0 : Fin n) := by
      by_cases one : n = 1
      · subst n; exact Subsingleton.elim _ _
      have pos := NeZero.pos n
      have big : 1 < n := by omega
      apply Fin.ext
      simp only [last,Fin.val_add,Fin.val_one',Fin.val_zero,Nat.mod_eq_of_lt big,
        show n-1+1=n by omega,Nat.mod_self]
    have h := link last
    rw [restart] at h
    have zero : (0 : Fin n) = ⟨0,NeZero.pos n⟩ := Fin.ext (Fin.val_zero n)
    simpa only [blocks,List.head_ofFn,List.getLast_ofFn,last,zero] using h

/-- If a base cycle has n vertices and encounters s replaced vertices, every
length from n+s through n+2s occurs upstairs. -/
theorem triangle_lengths {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (expanded : Set V)
    (project : W → V)
    (point : V → Fin 3 → W)
    (project_point : ∀ v i, project (point v i) = v)
    (port : V → V → Fin 3)
    (separate : ∀ v ∈ expanded, ∀ x y, G.Adj v x → G.Adj v y → x ≠ y → port v x ≠ port v y)
    (injective : ∀ v ∈ expanded, Injective (point v))
    (internal : ∀ v ∈ expanded, ∀ i j, i ≠ j → H.Adj (point v i) (point v j))
    (single : ∀ v ∉ expanded, ∀ i j, point v i = point v j)
    (external : ∀ v w, G.Adj v w → H.Adj (point v (port v w)) (point w (port w v))) {n : ℕ} (big : 3 ≤ n) (c : (cycleGraph n).Copy G)
    (visits : Finset (Fin n)) (selected : ∀ i, i ∈ visits ↔ c i ∈ expanded)
    (t : ℕ) (ht : t ≤ visits.card) : cycleGraph (n + visits.card + t) ⊑ H := by
  classical
  let : NeZero n := ⟨by omega⟩
  obtain ⟨long,subset,card⟩ := Finset.exists_subset_card_eq ht
  let incoming (i : Fin n) := port (c i) (c (i-1))
  let outgoing (i : Fin n) := port (c i) (c (i+1))
  let middle (i : Fin n) := -(incoming i + outgoing i)
  let entry (i : Fin n) := point (c i) (incoming i)
  let extra (i : Fin n) := point (c i) (middle i)
  let exit (i : Fin n) := point (c i) (outgoing i)
  let chunk (i : Fin n) := if i ∈ long then [entry i,extra i,exit i] else
    if i ∈ visits then [entry i,exit i] else [entry i]
  have edge (i : Fin n) : G.Adj (c i) (c (i+1)) := by
    apply c.toHom.map_rel'
    apply cycleGraph_adj'.mpr
    right
    simp [Nat.mod_eq_of_lt (show 1<n by omega)]
  have marks (i : Fin n) (hi : i∈visits) : incoming i ≠ outgoing i := by
    refine separate (c i) ((selected i).mp hi) _ _ ?_ (edge i) ?_
    · simpa only [sub_add_cancel] using (edge (i-1)).symm
    · intro h
      have add := congrArg (· + (1 : Fin n)) (c.injective h)
      have zero : (0 : Fin n) = 1+1 := add_left_cancel (a := i) (by simpa [add_assoc] using add)
      have invalid := congrArg Fin.val zero
      simp [Fin.val_add,Nat.mod_eq_of_lt (show 1<n by omega),
        Nat.mod_eq_of_lt (show 2<n by omega)] at invalid
  have third : ∀ a b : Fin 3, a ≠ b → a ≠ -(a+b) ∧ -(a+b) ≠ b := by decide
  have live (i : Fin n) : chunk i ≠ [] := by dsimp [chunk]; split_ifs <;> simp
  have nodup (i : Fin n) : (chunk i).Nodup := by
    by_cases hi : i ∈ visits
    · have inj := injective (c i) ((selected i).mp hi)
      have neq := marks i hi
      have others : incoming i ≠ middle i ∧ middle i ≠ outgoing i := third _ _ neq
      by_cases keep : i∈long <;> simp [chunk,keep,hi,entry,extra,exit,inj.eq_iff,neq,others.1,others.2]
    · have h : i∉long := fun mem => hi (subset mem)
      simp [chunk,h,hi]
  have projecting (i : Fin n) (w : W) (mem : w ∈ chunk i) : project w=c i := by
    dsimp [chunk] at mem
    split_ifs at mem <;> simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    · rcases mem with rfl | rfl | rfl <;> exact project_point _ _
    · rcases mem with rfl | rfl <;> exact project_point _ _
    · subst w; exact project_point _ _
  have apart (i j : Fin n) (diff : i ≠ j) : (chunk i).Disjoint (chunk j) := by
    intro w hi hj
    exact diff (c.injective ((projecting i w hi).symm.trans (projecting j w hj)))
  have chain (i : Fin n) : (chunk i).IsChain H.Adj := by
    by_cases hi : i ∈ visits
    · have edges := internal (c i) ((selected i).mp hi)
      have neq := marks i hi
      have others : incoming i ≠ middle i ∧ middle i ≠ outgoing i := third _ _ neq
      by_cases keep : i∈long <;> simp [chunk,keep,hi,entry,extra,exit,
        edges _ _ neq,edges _ _ others.1,edges _ _ others.2]
    · have h : i∉long := fun mem => hi (subset mem)
      simp [chunk,h,hi]
  have first (i : Fin n) : (chunk i).head (live i) = entry i := by
    dsimp [chunk]; split_ifs <;> rfl
  have last (i : Fin n) : (chunk i).getLast (live i) = exit i := by
    dsimp [chunk]; split_ifs with a b
    · rfl
    · rfl
    · exact single _ (fun h => b ((selected i).mpr h)) _ _
  have link (i : Fin n) : H.Adj ((chunk i).getLast (live i)) ((chunk (i+1)).head (live _)) := by
    rw [last,first]
    simpa only [exit,entry,incoming,outgoing,add_sub_cancel_right] using external _ _ (edge i)
  have count (i : Fin n) : (chunk i).length = 1 + (if i∈visits then 1 else 0) +
      (if i∈long then 1 else 0) := by
    by_cases a : i∈long
    · simp [chunk,a,subset a]
    · by_cases b : i∈visits <;> simp [chunk,a,b]
  have size : (List.ofFn chunk).flatten.length = n + visits.card + t := by
    simp only [List.length_flatten,List.map_ofFn,Fin.sum_ofFn,comp_apply,count,Finset.sum_add_distrib]
    simp [card]
  rw [← size]
  exact cycle_of_chunks H chunk live nodup apart chain link (by rw [size]; omega)

/-- For one expanded vertex, an avoiding cycle keeps its length. A cycle
through that vertex lifts to both of the next two lengths. -/
theorem single_vertex_lengths {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (expanded : Set V)
    (project : W → V)
    (point : V → Fin 3 → W)
    (project_point : ∀ v i, project (point v i) = v)
    (port : V → V → Fin 3)
    (separate : ∀ v ∈ expanded, ∀ x y, G.Adj v x → G.Adj v y → x ≠ y → port v x ≠ port v y)
    (injective : ∀ v ∈ expanded, Injective (point v))
    (internal : ∀ v ∈ expanded, ∀ i j, i ≠ j → H.Adj (point v i) (point v j))
    (single : ∀ v ∉ expanded, ∀ i j, point v i = point v j)
    (external : ∀ v w, G.Adj v w → H.Adj (point v (port v w)) (point w (port w v))) (r : V) (one : expanded={r})
    {n : ℕ} (big : 3 ≤ n) (c : (cycleGraph n).Copy G) :
    (r ∉ Set.range c → cycleGraph n ⊑ H) ∧
    (r ∈ Set.range c → cycleGraph (n+1) ⊑ H ∧ cycleGraph (n+2) ⊑ H) := by
  classical
  constructor
  · intro misses
    have spec (i : Fin n) : i ∈ (∅ : Finset (Fin n)) ↔ c i∈expanded := by
      simp [one,show c i≠r from fun eq => misses ⟨i,eq⟩]
    simpa using triangle_lengths expanded project point project_point port separate injective internal single external big c ∅ spec 0 (by simp)
  · rintro ⟨i,rfl⟩
    have spec (j : Fin n) : j ∈ ({i} : Finset (Fin n)) ↔ c j∈expanded := by
      simp only [one, Finset.mem_singleton, Set.mem_singleton_iff]
      exact ⟨fun h => congrArg c h, fun h => c.injective h⟩
    have move (m d : ℕ) (eq : n + ({i} : Finset (Fin n)).card + m = d)
        (w : cycleGraph (n + ({i} : Finset (Fin n)).card + m) ⊑ H) : cycleGraph d ⊑ H :=
      eq ▸ w
    constructor
    · exact move 0 (n+1) (by simp) (triangle_lengths expanded project point project_point port separate injective internal single external big c {i} spec 0 (by simp))
    · exact move 1 (n+2) (by simp [Nat.add_assoc]) (triangle_lengths expanded project point project_point port separate injective internal single external big c {i} spec 1 (by simp))

/-- Project a walk when an edge may collapse to one vertex. -/
theorem project_reachable {V W : Type*} {G : SimpleGraph V} {B : SimpleGraph W}
    (p : V → W) (step : ∀ x y, G.Adj x y → B.Reachable (p x) (p y))
    {a b : V} (reach : G.Reachable a b) : B.Reachable (p a) (p b) := by
  obtain ⟨w⟩ := reach
  induction w with
  | nil => exact .refl _
  | cons adj tail ih => exact (step _ _ adj).trans ih

/-- A projection with a unique lift of each surviving edge preserves bridgelessness. -/
theorem bridges_project {V W : Type*} (G : SimpleGraph V) (p : V → W)
    (bridgeless : ∀ ⦃x y⦄, G.Adj x y → ¬G.IsBridge s(x,y))
    (unique : ∀ ⦃a b x y⦄, G.Adj a b → G.Adj x y → p a ≠ p b →
      p a = p x → p b = p y → a = x ∧ b = y) :
    ∀ ⦃u v⦄, (G.map p).Adj u v → ¬(G.map p).IsBridge s(u,v) := by
  classical
  intro u v h
  obtain ⟨diff,a,b,ab,rfl,rfl⟩ := (map_adj' p G _ _).mp h
  apply fun bridge => (isBridge_iff.mp bridge) ?_
  have bypass : (G.deleteEdges {s(a,b)}).Reachable a b := by
    by_contra missing
    exact bridgeless ab (isBridge_iff.mpr missing)
  apply project_reachable p _ bypass
  intro x y hxy
  obtain ⟨xy, keep⟩ := deleteEdges_adj.mp hxy
  by_cases eq : p x = p y
  · exact eq ▸ Reachable.refl _
  apply Adj.reachable
  apply deleteEdges_adj.mpr
  refine ⟨(map_adj' p G _ _).mpr ⟨eq,x,y,xy,rfl,rfl⟩,?_⟩
  intro removed
  apply keep
  apply Set.mem_singleton_iff.mpr
  rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp removed) with h | h
  · exact Sym2.eq_iff.mpr (Or.inl (unique xy ab eq h.1 h.2))
  · exact Sym2.eq_iff.mpr (Or.inr (unique xy ab.symm eq h.1 h.2))

/-- In a square-free cubic graph the three edges leaving a triangle end
at three distinct outside vertices, one for each triangle vertex. -/
theorem triangle_exits {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (cubic : ∀ x, G.degree x = 3) (nosq : ¬cycleGraph 4 ⊑ G)
    (e : Fin 3 ↪ V) (triangle : ∀ i j, i ≠ j → G.Adj (e i) (e j)) :
    ∃ out : Fin 3 ↪ V, (∀ i, out i ∉ Set.range e) ∧
      (∀ i, G.Adj (e i) (out i)) ∧
      (∀ i x, x ∉ Set.range e → G.Adj (e i) x → out i = x) := by
  classical
  let T := Finset.univ.map e
  have member (x : V) : x ∈ T ↔ x ∈ Set.range e := by simp [T,Set.mem_range]
  have sizeT : T.card = 3 := by simp [T]
  have inside (i : Fin 3) : e i ∈ T := (member _).mpr ⟨i,rfl⟩
  have boundary (i : Fin 3) : G.neighborFinset (e i) ∩ T = T.erase (e i) := by
    ext x
    simp only [Finset.mem_inter,mem_neighborFinset,Finset.mem_erase]
    constructor
    · rintro ⟨adj,hmem⟩
      exact ⟨adj.ne.symm,hmem⟩
    · rintro ⟨diff,hmem⟩
      obtain ⟨j,rfl⟩ := (member _).mp hmem
      exact ⟨triangle i j (fun h => diff (congrArg e h.symm)),hmem⟩
  have one (i : Fin 3) : ∃ y, (G.neighborFinset (e i) \ T) = {y} := by
    apply Finset.card_eq_one.mp
    have count := Finset.card_sdiff_add_card_inter (G.neighborFinset (e i)) T
    rw [boundary,Finset.card_erase_of_mem (inside i),sizeT,card_neighborFinset_eq_degree,cubic] at count
    omega
  choose f hf using one
  have spec (i : Fin 3) (x : V) : G.Adj (e i) x ∧ x ∉ Set.range e ↔ x = f i := by
    rw [←Finset.mem_singleton,←hf]
    simp [member]
  have outside (i : Fin 3) := ((spec i (f i)).mpr rfl).2
  have adjacent (i : Fin 3) := ((spec i (f i)).mpr rfl).1
  have inj : Injective f := by
    intro i j same
    by_contra diff
    have other : ∀ a b : Fin 3, a ≠ b → a ≠ -(a+b) ∧ -(a+b) ≠ b := by decide
    let k := -(i+j)
    obtain ⟨ik,kj⟩ := other i j diff
    have close : G.Adj (e j) (f i) := same.symm ▸ adjacent j
    exact nosq (square_of_four (adjacent i).symm (triangle i k ik) (triangle k j kj) close
      (fun h => outside i ⟨k,h.symm⟩) (fun h => diff (e.injective h)))
  exact ⟨⟨f,inj⟩,outside,adjacent,fun i x off adj => ((spec i x).mp ⟨adj,off⟩).symm⟩


/-- Contracting one triangle in a square-free connected bridgeless cubic graph
produces a strictly smaller graph with all three properties. The projection
also records exactly the two cycle lifts needed at its distinguished vertex. -/
theorem contract_triangle {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (connected : G.Connected) (cubic : ∀ x, G.degree x = 3)
    (bridgeless : ∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a,b))
    (nosq : ¬cycleGraph 4 ⊑ G) (e : Fin 3 ↪ V)
    (triangle : ∀ i j, i ≠ j → G.Adj (e i) (e j)) :
    ∃ (W : Type) (_ : Fintype W) (B : SimpleGraph W) (_ : DecidableRel B.Adj) (root : W),
      Fintype.card W < Fintype.card V ∧ B.Connected ∧ (∀ w, B.degree w = 3) ∧
      (∀ ⦃a b⦄, B.Adj a b → ¬ B.IsBridge s(a,b)) ∧
      ∀ (n : ℕ), 3 ≤ n → ∀ c : (cycleGraph n).Copy B,
        (root ∉ Set.range c → cycleGraph n ⊑ G) ∧
        (root ∈ Set.range c → cycleGraph (n+1) ⊑ G ∧ cycleGraph (n+2) ⊑ G) := by
  classical
  obtain ⟨out,outside,edge,only⟩ := triangle_exits G cubic nosq e triangle
  let Off := {x : V // x ∉ Set.range e}
  let W := Option Off
  let p (x : V) : W := if h : x ∈ Set.range e then none else some ⟨x,h⟩
  let B := G.map p
  have atTriangle (i : Fin 3) : p (e i) = none := dif_pos ⟨i,rfl⟩
  have off (x : Off) : p x.val = some x := dif_neg x.property
  have pn (x : V) : p x = none ↔ x ∈ Set.range e := by
    by_cases h : x ∈ Set.range e
    · exact ⟨fun _ => h,fun _ => dif_pos h⟩
    · refine ⟨?_,fun mem => (h mem).elim⟩
      intro eq
      have impossible : some (⟨x,h⟩ : Off) = none := (off ⟨x,h⟩).symm.trans eq
      cases impossible
  have ps (x : V) (y : Off) : p x = some y ↔ x = y.val := by
    constructor
    · intro h
      by_cases mem : x ∈ Set.range e
      · rw [(pn x).mpr mem] at h
        contradiction
      · have eq := (off ⟨x,mem⟩).symm.trans h
        exact congrArg Subtype.val (Option.some.inj eq)
    · rintro rfl
      exact off y
  have onto : Surjective p := by
    rintro (_ | x)
    · exact ⟨e 0,atTriangle 0⟩
    · exact ⟨x.val,off x⟩
  have shrink : Fintype.card W < Fintype.card V := by
    apply Fintype.card_lt_of_surjective_not_injective p onto
    intro inj
    exact (by decide : (0:Fin 3) ≠ 1) (e.injective (inj ((atTriangle 0).trans (atTriangle 1).symm)))
  have projects {a b : V} (h : G.Adj a b) (diff : p a ≠ p b) : B.Adj (p a) (p b) :=
    (map_adj' p G _ _).mpr ⟨diff,a,b,h,rfl,rfl⟩
  have conn : B.Connected := by
    refine ⟨?_⟩
    intro u v
    obtain ⟨a,rfl⟩ := onto u
    obtain ⟨b,rfl⟩ := onto v
    apply project_reachable p _ (connected a b)
    intro x y xy
    by_cases eq : p x = p y
    · exact eq ▸ Reachable.refl _
    · exact (projects xy eq).reachable
  have sameNeighbor (z : Off) {x y : V} (zx : G.Adj z.val x) (zy : G.Adj z.val y)
      (eq : p x = p y) : x = y := by
    cases which : p x with
    | some w => exact ((ps x w).mp which).trans (((ps y w).mp (eq.symm.trans which)).symm)
    | none =>
      obtain ⟨i,rfl⟩ := (pn x).mp which
      obtain ⟨j,rfl⟩ := (pn y).mp (eq.symm.trans which)
      exact congrArg e (out.injective ((only i z.val z.property zx.symm).trans
        (only j z.val z.property zy.symm).symm))
  have unique ⦃a b x y : V⦄ (ab : G.Adj a b) (xy : G.Adj x y)
      (diff : p a ≠ p b) (ax : p a = p x) (by' : p b = p y) : a=x ∧ b=y := by
    cases ha : p a with
    | some w =>
      have aw := (ps a w).mp ha
      have xw := (ps x w).mp (ax.symm.trans ha)
      exact ⟨aw.trans xw.symm,sameNeighbor w (aw ▸ ab) (xw ▸ xy) by'⟩
    | none =>
      cases hb : p b with
      | none => exact (diff (ha.trans hb.symm)).elim
      | some w =>
        have bw := (ps b w).mp hb
        have yw := (ps y w).mp (by'.symm.trans hb)
        exact ⟨sameNeighbor w (bw ▸ ab.symm) (yw ▸ xy.symm) ax,bw.trans yw.symm⟩
  have noBridge : ∀ ⦃a b⦄, B.Adj a b → ¬B.IsBridge s(a,b) := bridges_project G p bridgeless unique
  let exit (i : Fin 3) : Off := ⟨out i,outside i⟩
  have exitInj : Injective exit := fun _ _ h => out.injective (congrArg Subtype.val h)
  have rootAdj (x : Off) : B.Adj none (some x) ↔ x ∈ Set.range exit := by
    constructor
    · intro h
      obtain ⟨_,a,b,ab,ha,hb⟩ := (map_adj' p G _ _).mp h
      obtain ⟨i,rfl⟩ := (pn a).mp ha
      obtain rfl := (ps b x).mp hb
      exact ⟨i,Subtype.ext (only i _ x.property ab)⟩
    · rintro ⟨i,rfl⟩
      exact (map_adj' p G _ _).mpr ⟨by simp,e i,out i,edge i,atTriangle i,off (exit i)⟩
  have leafAdj (a b : Off) : B.Adj (some a) (some b) ↔ G.Adj a.val b.val := by
    constructor
    · intro h
      obtain ⟨_,x,y,xy,hx,hy⟩ := (map_adj' p G _ _).mp h
      rwa [(ps x a).mp hx,(ps y b).mp hy] at xy
    · intro h
      exact (map_adj' p G _ _).mpr ⟨fun eq => h.ne (congrArg Subtype.val (Option.some.inj eq)),
        a.val,b.val,h,off a,off b⟩
  have deg : ∀ w, B.degree w=3 := by
    rintro (_ | x)
    · let ends (i : Fin 3) : W := some (exit i)
      have rootNbr : B.neighborFinset none = Finset.univ.image ends := by
        ext w
        cases w with
        | none => simp [ends]
        | some x =>
          rw [mem_neighborFinset,rootAdj,Finset.mem_image]
          exact ⟨fun ⟨i,hi⟩ => ⟨i,Finset.mem_univ _,congrArg some hi⟩,
            fun ⟨i,_,hi⟩ => ⟨i,Option.some.inj hi⟩⟩
      rw [←card_neighborFinset_eq_degree,rootNbr,
        Finset.card_image_of_injective _ (fun _ _ h => exitInj (Option.some.inj h))]
      simp
    · have nbr : B.neighborFinset (some x) = (G.neighborFinset x.val).image p := by
        ext w
        simp only [mem_neighborFinset,Finset.mem_image]
        constructor
        · intro h
          obtain ⟨_,a,b,ab,ha,hb⟩ := (map_adj' p G _ _).mp h
          exact ⟨b,(ps a x).mp ha ▸ ab,hb⟩
        · rintro ⟨b,h,rfl⟩
          have diff : some x ≠ p b := fun eq => h.ne (((ps b x).mp eq.symm).symm)
          exact (map_adj' p G _ _).mpr ⟨diff,x.val,b,h,off x,rfl⟩
      rw [←card_neighborFinset_eq_degree,nbr,Finset.card_image_of_injOn,
        card_neighborFinset_eq_degree,cubic]
      exact fun _ hx _ hy eq => sameNeighbor x ((mem_neighborFinset _ _ _).mp hx)
        ((mem_neighborFinset _ _ _).mp hy) eq
  let point : W → Fin 3 → V
    | none,i => e i
    | some x,_ => x.val
  let port : W → W → Fin 3
    | none,some x => invFun exit x
    | _,_ => 0
  have atExit (i : Fin 3) : invFun exit (exit i)=i := leftInverse_invFun exitInj i
  have designation : ∀ (v : W) (i : Fin 3), p (point v i)=v := by
    rintro (_ | x) i
    · exact atTriangle i
    · exact off x
  have separate : ∀ v ∈ ({none} : Set W), ∀ x y, B.Adj v x → B.Adj v y → x≠y →
      port v x≠port v y := by
    rintro v hv x y hx hy diff
    obtain rfl : v=none := hv
    cases x with
    | none => exact (hx.ne rfl).elim
    | some a =>
      cases y with
      | none => exact (hy.ne rfl).elim
      | some b =>
        obtain ⟨i,rfl⟩ := (rootAdj a).mp hx
        obtain ⟨j,rfl⟩ := (rootAdj b).mp hy
        change invFun exit (exit i) ≠ invFun exit (exit j)
        rw [atExit,atExit]
        exact fun h => diff (congrArg (fun t => some (exit t)) h)
  have internal : ∀ v ∈ ({none} : Set W), ∀ i j, i≠j → G.Adj (point v i) (point v j) := by
    rintro v hv
    obtain rfl : v=none := hv
    exact triangle
  have inject : ∀ v ∈ ({none} : Set W), Injective (point v) := by
    rintro v hv
    obtain rfl : v=none := hv
    exact e.injective
  have single : ∀ v ∉ ({none} : Set W), ∀ i j, point v i=point v j := by
    rintro (_ | x) h i j
    · exact (h rfl).elim
    · rfl
  have external : ∀ v w, B.Adj v w → G.Adj (point v (port v w)) (point w (port w v)) := by
    rintro (_ | a) (_ | b) h
    · exact (h.ne rfl).elim
    · obtain ⟨i,rfl⟩ := (rootAdj b).mp h
      change G.Adj (e (invFun exit (exit i))) (out i)
      rw [atExit]
      exact edge i
    · obtain ⟨i,rfl⟩ := (rootAdj a).mp h.symm
      change G.Adj (out i) (e (invFun exit (exit i)))
      rw [atExit]
      exact (edge i).symm
    · exact (leafAdj a b).mp h
  refine ⟨W,inferInstance,B,inferInstance,none,shrink,conn,deg,noBridge,?_⟩
  intro n large c
  exact single_vertex_lengths
    {none} p point designation port separate inject internal single external none rfl large c

/-- Strong induction on the order allows the rooted case to assume a
power-of-two cycle already exists in the contracted graph. -/
theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1.H1 := by
  classical
  intro free rooted
  have solve (m : ℕ) : ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V = m → G.Connected → (∀ v, G.degree v = 3) →
      (∀ ⦃a b⦄, G.Adj a b → ¬G.IsBridge s(a,b)) →
      ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro V G _ _ card connected cubic bridgeless
      by_contra fail
      have no4 : ¬cycleGraph 4 ⊑ G := fun h => fail ⟨2,by decide,h⟩
      have no8 : ¬cycleGraph 8 ⊑ G := fun h => fail ⟨3,by decide,h⟩
      by_cases tri : ∃ e : Fin 3 ↪ V, ∀ i j, i ≠ j → G.Adj (e i) (e j)
      · obtain ⟨e,edges⟩ := tri
        obtain ⟨W,fw,B,db,r,smaller,conn,deg,bridges,lift⟩ :=
          contract_triangle G connected cubic bridgeless no4 e edges
        let : Fintype W := fw
        let : DecidableRel B.Adj := db
        have existsDyadic := ih (Fintype.card W) (smaller.trans_eq card) W B rfl conn deg bridges
        have noTriangle (c : (cycleGraph 3).Copy B) (hit : r ∈ Set.range c) : False :=
          no4 (((lift 3 (by decide) c).2 hit).1)
        have allHit (k : ℕ) (hk : 2 ≤ k) (c : (cycleGraph (2^k)).Copy B) : r ∈ Set.range c := by
          by_contra misses
          have four : 4 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
          exact fail ⟨k,hk,(lift _ (by omega) c).1 misses⟩
        obtain ⟨n,k,c,large,hk,hit,close⟩ :=
          rooted W B r conn deg bridges noTriangle existsDyadic allHit
        obtain ⟨short,long⟩ := (lift n large c).2 hit
        exact fail ⟨k,hk,close.elim (fun eq => eq ▸ short) (fun eq => eq ▸ long)⟩
      · exact fail (free V G connected cubic bridgeless tri no4 no8)
  intro V G _ _ connected cubic bridgeless
  obtain ⟨k,hk,w⟩ := solve (Fintype.card V) V G rfl connected cubic bridgeless
  have four : 4 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  obtain ⟨v,c,cycle,len⟩ := (cycleGraph_isContained_iff (by omega)).mp w
  exact ⟨k,v,c,hk,cycle,len⟩

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R2
