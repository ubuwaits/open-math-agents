import Mathlib

/-!
# Lifting cycles through disjoint vertex replacements

Chad Mazzola (@ubuwaits), using Codex. The construction uses the port-path
argument of Daniel Garcia, Lemma 3.2 of arXiv:2609.04686, and specializes it
to triangles on one or both shores of a cubic graph.
-/

namespace Erdos64TriangleExpansion

open SimpleGraph Function Fin.NatCast

private theorem cycle_of_ring {V : Type*} (G : SimpleGraph V) (l : List V)
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

/-- A vertex designated for expansion has a triangle with three distinct attachment
ports. Each other vertex has a single image. An original edge joins the two
specified attachments. The projection keeps different vertex replacements disjoint. -/
structure Replacement {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) where
  expanded : Set V
  project : W → V
  point : V → Fin 3 → W
  project_point : ∀ v i, project (point v i) = v
  port : V → V → Fin 3
  separate : ∀ v ∈ expanded, ∀ x y, G.Adj v x → G.Adj v y → x ≠ y → port v x ≠ port v y
  injective : ∀ v ∈ expanded, Injective (point v)
  internal : ∀ v ∈ expanded, ∀ i j, i ≠ j → H.Adj (point v i) (point v j)
  single : ∀ v ∉ expanded, ∀ i j, point v i = point v j
  external : ∀ v w, G.Adj v w → H.Adj (point v (port v w)) (point w (port w v))

/-- If a base cycle has n vertices and encounters s replaced vertices, every
length from n+s through n+2s occurs upstairs. -/
theorem triangle_lengths {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (R : Replacement G H) {n : ℕ} (big : 3 ≤ n) (c : (cycleGraph n).Copy G)
    (visits : Finset (Fin n)) (selected : ∀ i, i ∈ visits ↔ c i ∈ R.expanded)
    (t : ℕ) (ht : t ≤ visits.card) : cycleGraph (n + visits.card + t) ⊑ H := by
  classical
  let : NeZero n := ⟨by omega⟩
  obtain ⟨long,subset,card⟩ := Finset.exists_subset_card_eq ht
  let incoming (i : Fin n) := R.port (c i) (c (i-1))
  let outgoing (i : Fin n) := R.port (c i) (c (i+1))
  let middle (i : Fin n) := -(incoming i + outgoing i)
  let entry (i : Fin n) := R.point (c i) (incoming i)
  let extra (i : Fin n) := R.point (c i) (middle i)
  let exit (i : Fin n) := R.point (c i) (outgoing i)
  let chunk (i : Fin n) := if i ∈ long then [entry i,extra i,exit i] else
    if i ∈ visits then [entry i,exit i] else [entry i]
  have edge (i : Fin n) : G.Adj (c i) (c (i+1)) := by
    apply c.toHom.map_rel'
    apply cycleGraph_adj'.mpr
    right
    simp [Nat.mod_eq_of_lt (show 1<n by omega)]
  have marks (i : Fin n) (hi : i∈visits) : incoming i ≠ outgoing i := by
    refine R.separate (c i) ((selected i).mp hi) _ _ ?_ (edge i) ?_
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
    · have inj := R.injective (c i) ((selected i).mp hi)
      have neq := marks i hi
      have others : incoming i ≠ middle i ∧ middle i ≠ outgoing i := third _ _ neq
      by_cases keep : i∈long <;> simp [chunk,keep,hi,entry,extra,exit,inj.eq_iff,neq,others.1,others.2]
    · have h : i∉long := fun mem => hi (subset mem)
      simp [chunk,h,hi]
  have projecting (i : Fin n) (w : W) (mem : w ∈ chunk i) : R.project w=c i := by
    dsimp [chunk] at mem
    split_ifs at mem <;> simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    · rcases mem with rfl | rfl | rfl <;> exact R.project_point _ _
    · rcases mem with rfl | rfl <;> exact R.project_point _ _
    · subst w; exact R.project_point _ _
  have apart (i j : Fin n) (diff : i ≠ j) : (chunk i).Disjoint (chunk j) := by
    intro w hi hj
    exact diff (c.injective ((projecting i w hi).symm.trans (projecting j w hj)))
  have chain (i : Fin n) : (chunk i).IsChain H.Adj := by
    by_cases hi : i ∈ visits
    · have edges := R.internal (c i) ((selected i).mp hi)
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
    · exact R.single _ (fun h => b ((selected i).mpr h)) _ _
  have link (i : Fin n) : H.Adj ((chunk i).getLast (live i)) ((chunk (i+1)).head (live _)) := by
    rw [last,first]
    simpa only [exit,entry,incoming,outgoing,add_sub_cancel_right] using R.external _ _ (edge i)
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

/-- A base cycle doubles whenever at least half of its vertices were replaced. -/
theorem double_of_half {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (R : Replacement G H) {n : ℕ} (big : 3 ≤ n) (c : (cycleGraph n).Copy G)
    (visits : Finset (Fin n)) (selected : ∀ i, i ∈ visits ↔ c i ∈ R.expanded)
    (half : n ≤ 2 * visits.card) : cycleGraph (2*n) ⊑ H := by
  have bound : visits.card ≤ n := by simpa using Finset.card_le_univ visits
  have h := triangle_lengths R big c visits selected (n-visits.card) (by omega)
  rwa [show n+visits.card+(n-visits.card)=2*n by omega] at h

/-- If the replaced vertices meet every base edge, every simple base cycle
lifts to a simple cycle of twice its length. -/
theorem vertex_cover_doubles {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (R : Replacement G H) (cover : ∀ u v, G.Adj u v → u∈R.expanded ∨ v∈R.expanded)
    {n : ℕ} (big : 3 ≤ n) (cycle : cycleGraph n ⊑ G) : cycleGraph (2*n) ⊑ H := by
  classical
  let : NeZero n := ⟨by omega⟩
  obtain ⟨c⟩ := cycle
  let visits := Finset.univ.filter (fun i : Fin n => c i∈R.expanded)
  have selected (i : Fin n) : i∈visits ↔ c i∈R.expanded := by simp [visits]
  apply double_of_half R big c visits selected
  have maps : Set.MapsTo (fun i : Fin n => i+1) (↑(visitsᶜ)) (↑visits) := by
    intro i hi
    have outside : i∉visits := Finset.mem_compl.mp hi
    apply (selected _).mpr
    apply (cover _ _ (c.toHom.map_rel' (b := i+1) ?_)).resolve_left (fun h => outside ((selected i).mpr h))
    apply cycleGraph_adj'.mpr
    right
    simp [Nat.mod_eq_of_lt (show 1<n by omega)]
  have hk := Finset.card_le_card_of_injOn _ maps (fun _ _ _ _ eq => add_right_cancel eq)
  rw [Finset.card_compl,Fintype.card_fin] at hk
  omega

/-- For one expanded vertex, an avoiding cycle keeps its length. A cycle
through that vertex lifts to both of the next two lengths. -/
theorem single_vertex_lengths {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (R : Replacement G H) (r : V) (one : R.expanded={r})
    {n : ℕ} (big : 3 ≤ n) (c : (cycleGraph n).Copy G) :
    (r ∉ Set.range c → cycleGraph n ⊑ H) ∧
    (r ∈ Set.range c → cycleGraph (n+1) ⊑ H ∧ cycleGraph (n+2) ⊑ H) := by
  classical
  constructor
  · intro misses
    have spec (i : Fin n) : i ∈ (∅ : Finset (Fin n)) ↔ c i∈R.expanded := by
      simp [one,show c i≠r from fun eq => misses ⟨i,eq⟩]
    simpa using triangle_lengths R big c ∅ spec 0 (by simp)
  · rintro ⟨i,rfl⟩
    have spec (j : Fin n) : j ∈ ({i} : Finset (Fin n)) ↔ c j∈R.expanded := by
      simp only [one, Finset.mem_singleton, Set.mem_singleton_iff]
      exact ⟨fun h => congrArg c h, fun h => c.injective h⟩
    have move (m d : ℕ) (eq : n + ({i} : Finset (Fin n)).card + m = d)
        (w : cycleGraph (n + ({i} : Finset (Fin n)).card + m) ⊑ H) : cycleGraph d ⊑ H :=
      eq ▸ w
    constructor
    · exact move 0 (n+1) (by simp) (triangle_lengths R big c {i} spec 0 (by simp))
    · exact move 1 (n+2) (by simp [Nat.add_assoc]) (triangle_lengths R big c {i} spec 1 (by simp))

end Erdos64TriangleExpansion
