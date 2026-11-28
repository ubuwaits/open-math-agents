import Erdos64TriangleExpansion

/-!
# Vertex symmetry and two-sheeted cycle lifts

An orbit of a vertex that hits every dyadic cycle must lie on every dyadic
cycle. The second argument controls cycle lengths in two-sheeted coverings.
-/

namespace Erdos64SymmetricCycles

open SimpleGraph Function Fin.NatCast

/-- If every copy of a cycle uses r, then every automorphic image of r
lies in every copy, without a transitivity assumption. -/
theorem orbit_on_cycle {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (r : V) (hit : ∀ c : (cycleGraph n).Copy G, r ∈ Set.range c)
    (c : (cycleGraph n).Copy G) (g : G ≃g G) : g r ∈ Set.range c := by
  obtain ⟨i,hi⟩ := hit (g.symm.toCopy.comp c)
  refine ⟨i,?_⟩
  change g.symm (c i) = r at hi
  simpa using congrArg g hi

/-- In a vertex-transitive graph, a length whose every cycle visits one
vertex can only be the full graph order. -/
theorem transitive_cycle_spans {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (r : V) (transitive : ∀ x, ∃ g : G ≃g G, g r = x)
    (hit : ∀ c : (cycleGraph n).Copy G, r ∈ Set.range c)
    (c : (cycleGraph n).Copy G) : n = Fintype.card V := by
  have onto : Surjective c := by
    intro x
    obtain ⟨g,rfl⟩ := transitive x
    exact orbit_on_cycle r hit c g
  simpa using Fintype.card_congr (Equiv.ofBijective c ⟨fun _ _ h => c.injective h,onto⟩)

/-- A vertex-transitive graph of order other than a power of two has a
dyadic cycle avoiding any specified vertex as soon as one such cycle exists. -/
theorem avoiding_cycle {V : Type*} [Fintype V] {G : SimpleGraph V}
    (r : V) (transitive : ∀ x, ∃ g : G ≃g G, g r = x)
    {k : ℕ} (proper : 2^k ≠ Fintype.card V) (someCycle : cycleGraph (2^k) ⊑ G) :
    ∃ c : (cycleGraph (2^k)).Copy G, r ∉ Set.range c := by
  classical
  by_contra! hit
  exact proper (transitive_cycle_spans r transitive hit someCycle.some)

private theorem cycle_of_period {U Z : Type*} {H : SimpleGraph U} (f : Z → Z)
    (label : Z ↪ U) (adj : ∀ z, H.Adj (label z) (label (f z))) (z : Z)
    (large : 3 ≤ minimalPeriod f z) : cycleGraph (minimalPeriod f z) ⊑ H := by
  let t := minimalPeriod f z
  let : NeZero t := ⟨by change 3 ≤ t at large; omega⟩
  let v (i : Fin t) := label (f^[i.val] z)
  have inj : Injective v := by
    intro i j eq
    exact Fin.ext ((iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp
      (label.injective eq))
  have step (i : Fin t) : H.Adj (v i) (v (i + 1)) := by
    have h1 : 1 < t := by change 3 ≤ t at large; omega
    have hi : (i + 1 : Fin t).val = (i.val + 1) % t := by
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt h1]
    change H.Adj (label (f^[i.val] z)) (label (f^[(i + 1 : Fin t).val] z))
    rw [hi, iterate_mod_minimalPeriod_eq, iterate_succ_apply']
    exact adj _
  change cycleGraph t ⊑ H
  refine ⟨⟨⟨v, ?_⟩, inj⟩⟩
  intro i j h
  have h1 : 1 < t := by change 3 ≤ t at large; omega
  have h' : i - j = 1 ∨ j - i = 1 := by
    simpa only [Fin.ext_iff, Fin.val_one', Nat.mod_eq_of_lt h1] using cycleGraph_adj'.mp h
  rcases h' with h' | h'
  · have eq : i = j + 1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h'
    simpa only [eq] using (step j).symm
  · have eq : j = i + 1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h'
    simpa only [eq] using step i

/-- A graph covering with fibers of size at most two lifts a simple n-cycle
to a simple n-cycle or 2n-cycle. Local bijectivity is only needed along
the edges of the base cycle. -/
theorem lift_two {U V : Type*} [Fintype U] {G : SimpleGraph U} {B : SimpleGraph V}
    (q : U → V) (onto : Surjective q)
    (small : ∀ v, Nat.card {u : U // q u=v} ≤ 2) {n : ℕ} (large : 3≤n)
    (c : (cycleGraph n).Copy B)
    (liftEdge : ∀ (u : U) (v : V), B.Adj (q u) v → ∃! w : U, G.Adj u w ∧ q w = v) :
    cycleGraph n ⊑ G ∨ cycleGraph (2*n) ⊑ G := by
  classical
  let : NeZero n := ⟨by omega⟩
  have edge (i : Fin n) : B.Adj (c i) (c (i+1)) := by
    apply c.toHom.map_rel'
    apply cycleGraph_adj'.mpr
    right
    simp [Nat.mod_eq_of_lt (show 1<n by omega)]
  let Fiber (i : Fin n) := {u : U // q u=c i}
  let D := Σ i : Fin n, Fiber i
  have next (z : D) : ∃! w : U, G.Adj z.2.val w ∧ q w=c (z.1+1) := by
    apply liftEdge
    rw [z.2.property]
    exact edge z.1
  let f (z : D) : D := ⟨z.1+1,(next z).choose,(next z).choose_spec.1.2⟩
  let label : D ↪ U := ⟨fun z => z.2.val,by
    rintro ⟨i,a,ha⟩ ⟨j,b,hb⟩ (rfl : a=b)
    obtain rfl := c.injective (ha.symm.trans hb)
    rfl⟩
  have adj (z : D) : G.Adj (label z) (label (f z)) := (next z).choose_spec.1.1
  have inject : Injective f := by
    intro x y h
    have phase : x.1=y.1 := add_right_cancel (congrArg Sigma.fst h : x.1+1=y.1+1)
    have eq : label (f x)=label (f y) := congrArg label h
    apply label.injective
    have same : q (label (f x))=c (x.1+1) := (f x).2.property
    have choices := liftEdge (label (f x)) (c x.1) (same ▸ (edge x.1).symm)
    apply choices.unique
    · exact ⟨(adj x).symm,x.2.property⟩
    · exact ⟨eq ▸ (adj y).symm,y.2.property.trans (congrArg c phase.symm)⟩
  obtain ⟨a,ha⟩ := onto (c 0)
  let start : D := ⟨0,a,ha⟩
  let t := minimalPeriod f start
  have pos : 0<t := by
    apply minimalPeriod_pos_of_mem_periodicPts
    exact inject.mem_periodicPts _
  have tick (m : ℕ) : (f^[m] start).1=(m : Fin n) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [iterate_succ_apply']
      change (f^[m] start).1+1 = _
      rw [ih,Nat.cast_succ]
  have period : n ∣ t := by
    apply Fin.natCast_eq_zero.mp
    exact (tick t).symm.trans (congrArg Sigma.fst (iterate_minimalPeriod (f := f) (x := start)))
  have bound : t ≤ 2*n := by
    apply (minimalPeriod_le_card (f := f) (x := start)).trans
    change Fintype.card (Σ i : Fin n, Fiber i) ≤ 2*n
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _i : Fin n, 2 := Finset.sum_le_sum (fun i _ => by
        simpa only [Nat.card_eq_fintype_card,Fiber] using small (c i))
      _ = _ := by simp [mul_comm]
  obtain ⟨m,hm⟩ := period
  have choices : t=n ∨ t=2*n := by
    by_cases two : 3 ≤ m
    · have low : n*3 ≤ n*m := Nat.mul_le_mul_left n two
      omega
    · interval_cases m <;> simp_all [Nat.mul_comm]
  have lift := cycle_of_period f label adj start (show 3≤t by rcases choices with h|h <;> omega)
  exact choices.elim (fun h => Or.inl (h ▸ lift)) (fun h => Or.inr (h ▸ lift))

end Erdos64SymmetricCycles
