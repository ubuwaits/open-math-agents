import FormalConjectures.ErdosProblems.«64»
import Mathlib

/-!
# Power-of-two and twice-prime orders in vertex-transitive graphs

Graphs on N = 2^(m+3) vertices with minimum degree three admit a simple
power-of-two cycle of length at most N/2 whenever the automorphism group
is vertex transitive. A transitive Sylow two-subgroup supplies a central free
involution. Either there is a square or its pairs define a two-sheeted cover
that preserves every local degree. A binary cover of the tetrahedron always
has a square. Strong induction proves the bound.

If the order is twice a prime, Cauchy's theorem provides a prime-order
automorphism. One moving orbit forces a square. Two moving orbits form
an abelian two-layer graph and force a 4-, 8-, or 16-cycle. The bound 16
is attained by the cyclic Haar graph with shifts 0, 1, 8 modulo 19.

The reduction also uses the degree-three edge and neighborhood conditions
proved by @JamesSlash in reduction R1, PR #466. Related Cayley-graph results
appear in Michael C. Burkhart, arXiv:2611.05060.
-/

namespace OMA.R_Erdos64_erdos_64_R4

open SimpleGraph Function Fin.NatCast MulAction

/-- The connected case with more than one vertex orbit, after the elementary
degree reductions and removal of squares and octagons. -/
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.Connected → (∀ x, 3 ≤ G.degree x) →
    (¬∀ x y, ∃ g : G ≃g G, g x=y) →
    (∀ ⦃a b⦄, G.Adj a b → G.degree a=3 ∨ G.degree b=3) →
    (∀ a, ∃ b, G.Adj a b ∧ G.degree b=3) →
    (¬cycleGraph 4 ⊑ G) → (¬cycleGraph 8 ⊑ G) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G

/-- The remaining transitive case is cubic. Its order excludes powers of two and twice a prime. -/
def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.Connected → (∀ x, G.degree x=3) →
    (∀ x y, ∃ g : G ≃g G, g x=y) →
    (∀ k : ℕ, Fintype.card V ≠ 2^k) →
    (∀ p : ℕ, p.Prime → Fintype.card V ≠ 2*p) →
    (¬cycleGraph 4 ⊑ G) → (¬cycleGraph 8 ⊑ G) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G

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

/-- Three signed edges on the leaves of a claw force a square in a binary cover
of a tetrahedron. At one leaf, the two incident signs agree. -/
theorem claw_square {V : Type*} {G : SimpleGraph V} (t : V → V) {v a b c : V}
    (va : G.Adj v a) (vb : G.Adj v b) (vc : G.Adj v c)
    (ab : a≠b) (bc : b≠c) (ca : c≠a)
    (na : v≠t a) (nb : v≠t b) (nc : v≠t c)
    (dab : G.Adj a b ∨ (G.Adj a (t b) ∧ G.Adj (t a) b))
    (dbc : G.Adj b c ∨ (G.Adj b (t c) ∧ G.Adj (t b) c))
    (dca : G.Adj c a ∨ (G.Adj c (t a) ∧ G.Adj (t c) a)) : cycleGraph 4 ⊑ G := by
  rcases dab with u|u <;> rcases dbc with w|w <;> rcases dca with z|z
  · exact square_of_four va u w vc.symm vb.ne ca.symm
  · exact square_of_four va u w vc.symm vb.ne ca.symm
  · exact square_of_four vc z u vb.symm va.ne bc.symm
  · exact square_of_four vb w.1 z.2 va.symm nc ab.symm
  · exact square_of_four vb w z va.symm vc.ne ab.symm
  · exact square_of_four vc z.1 u.2 vb.symm na bc.symm
  · exact square_of_four va u.1 w.2 vc.symm nb ca.symm
  · exact square_of_four va u.1 w.2 vc.symm nb ca.symm

/-- Every two-sheeted cover of K4 contains a square. -/
theorem square_over_four {V W : Type*} [Fintype W] {G : SimpleGraph V} {B : SimpleGraph W}
    [DecidableRel B.Adj] (order : Fintype.card W=4) (cubic : ∀ w, B.degree w=3)
    (t : V → V) (twice : ∀ x,t (t x)=x) (sym : ∀ a b,G.Adj a b → G.Adj (t a) (t b))
    (q : V → W) (onto : Surjective q) (pair : ∀ x y, q x=q y ↔ x=y ∨ x=t y)
    (lift : ∀ x y, B.Adj (q x) y → ∃ w, G.Adj x w ∧ q w=y) : cycleGraph 4 ⊑ G := by
  classical
  let E := (Fintype.equivFinOfCardEq order).symm
  have allAdj (i j : Fin 4) (diff : i ≠ j) : B.Adj (E i) (E j) :=
    ((B.degree_eq_card_sub_one (E i)).mp (by rw [cubic,order]))
      (fun h => diff (E.injective h))
  obtain ⟨v,hv⟩ := onto (E 0)
  have leaves (i : Fin 4) (h : i≠0) : ∃ a, G.Adj v a ∧ q a=E i := by
    apply lift
    rw [hv]
    exact allAdj _ _ h.symm
  obtain ⟨a,va,ha⟩ := leaves 1 (by decide)
  obtain ⟨b,vb,hb⟩ := leaves 2 (by decide)
  obtain ⟨c,vc,hc⟩ := leaves 3 (by decide)
  have qt (x : V) : q (t x)=q x := (pair _ _).mpr (Or.inr rfl)
  have different {x y : V} {i j : Fin 4} (hx : q x=E i) (hy : q y=E j) (diff : i≠j) :
      x≠y ∧ x≠t y := by
    have neq : q x≠q y := fun h => diff (E.injective (hx.symm.trans (h.trans hy)))
    exact ⟨fun h => neq (congrArg q h),fun h => neq ((congrArg q h).trans (qt y))⟩
  have signs {x y : V} {i j : Fin 4} (hx : q x=E i) (hy : q y=E j) (diff : i≠j) :
      G.Adj x y ∨ (G.Adj x (t y) ∧ G.Adj (t x) y) := by
    obtain ⟨w,adj,hw⟩ := lift x (q y) (by rw [hx,hy]; exact allAdj i j diff)
    rcases (pair w y).mp hw with rfl | rfl
    · exact Or.inl adj
    · exact Or.inr ⟨adj,(twice y) ▸ sym _ _ adj⟩
  exact claw_square t va vb vc (different ha hb (by decide)).1 (different hb hc (by decide)).1
    (different hc ha (by decide)).1 (different hv ha (by decide)).2 (different hv hb (by decide)).2
    (different hv hc (by decide)).2 (signs ha hb (by decide)) (signs hb hc (by decide))
    (signs hc ha (by decide))

/-- For a free involution, its pairs are the fibers of a two-to-one map. -/
theorem pair_projection {V : Type} [Fintype V] (t : V → V) (twice : ∀ x, t (t x)=x)
    (free : ∀ x, t x ≠ x) :
    ∃ (W : Type) (_ : Fintype W) (q : V → W), Surjective q ∧
      (∀ x y, q x=q y ↔ x=y ∨ x=t y) ∧ Fintype.card V = Fintype.card W * 2 ∧
      (∀ w, Nat.card {x : V // q x=w}=2) := by
  classical
  let block (x : V) : Set V := {x,t x}
  let W := Set.range block
  let q (x : V) : W := ⟨block x,⟨x,rfl⟩⟩
  have onto : Surjective q := by rintro ⟨_,x,rfl⟩; exact ⟨x,rfl⟩
  have pair (x y : V) : q x=q y ↔ x=y ∨ x=t y := by
    constructor
    · intro h
      have s : x∈block x := Set.mem_insert _ _
      rw [show block x=block y from congrArg Subtype.val h] at s
      exact s
    · rintro (rfl | rfl)
      · rfl
      · apply Subtype.ext
        change ({t y,t (t y)} : Set V)={y,t y}
        rw [twice]
        exact Set.pair_comm _ _
  let : Finite W := Finite.of_surjective q onto
  let : Fintype W := Fintype.ofFinite W
  have fiber (w : W) : Nat.card {x : V // q x=w}=2 := by
    obtain ⟨x,rfl⟩ := onto w
    let f (b : Bool) : {z : V // q z=q x} := if b then
      ⟨t x,(pair _ _).mpr (Or.inr rfl)⟩ else ⟨x,rfl⟩
    have inj : Injective f := by
      intro i j same
      have eq := congrArg Subtype.val same
      cases i <;> cases j <;> simp_all [f,free x,(free x).symm]
    have sur : Surjective f := by
      rintro ⟨z,hz⟩
      rcases (pair z x).mp hz with rfl | rfl
      · exact ⟨false,rfl⟩
      · exact ⟨true,rfl⟩
    exact (Nat.card_congr (Equiv.ofBijective f ⟨inj,sur⟩)).symm.trans (by simp [Nat.card_eq_fintype_card])
  refine ⟨W,inferInstance,q,onto,pair,?_,fiber⟩
  rw [←Fintype.card_congr (Equiv.sigmaFiberEquiv q),Fintype.card_sigma]
  have size (w : W) : Fintype.card {x : V // q x=w}=2 := by
    simpa only [Nat.card_eq_fintype_card] using fiber w
  simp [size]

/-- If the number of points is a power of two, every Sylow 2-subgroup of a
finite transitive group is still transitive on those points. -/
theorem sylow_transitive {A V : Type*} [Group A] [Finite A] [Finite V] [MulAction A V]
    [IsPretransitive A V] (S : Sylow 2 A) {k : ℕ} (card : Nat.card V=2^k) :
    IsPretransitive S V := by
  classical
  constructor
  intro x y
  let H := stabilizer A x
  have eq : H.index=2^k := (index_stabilizer_of_transitive A x).trans card
  have hd : 2^k ∣ H.relIndex S.1 * S.1.index := by
    rw [← Subgroup.inf_relIndex_right,Subgroup.relIndex_mul_index (show H ⊓ S.1 ≤ S.1 from inf_le_right),←eq]
    exact Subgroup.index_dvd_of_le (show H ⊓ S.1 ≤ H from inf_le_left)
  have d : 2^k ∣ H.relIndex S.1 :=
    (Nat.prime_two.coprime_pow_of_not_dvd S.not_dvd_index).symm.dvd_of_dvd_mul_right hd
  have idx : H.relIndex S.1 = (stabilizer S x).index := rfl
  have count : Nat.card V ≤ (orbit S x).ncard := by
    rw [card,←index_stabilizer S x,←idx]
    apply Nat.le_of_dvd _ d
    rw [idx,index_stabilizer S x]
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨x,1,one_smul _ _⟩
  have full : orbit S x=Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    simpa using count
  have mem : y ∈ orbit S x := full ▸ Set.mem_univ y
  exact mem

/-- A nontrivial faithful transitive permutation 2-group contains a central
involution which moves every point. -/
theorem central_pair {V : Type*} [Finite V] (A : Subgroup (Equiv.Perm V))
    [Nontrivial A] (two : IsPGroup 2 A) (transitive : ∀ x y, ∃ g : A, g.val x=y) :
    ∃ t : A, (∀ v, t.val (t.val v)=v) ∧ (∀ v,t.val v≠v) ∧
      (∀ (g : A) v, g.val (t.val v)=t.val (g.val v)) := by
  classical
  let Z := Subgroup.center A
  let : Nontrivial Z := two.center_nontrivial
  obtain ⟨j,pj,card⟩ := (two.to_subgroup Z).nontrivial_iff_card.mp (inferInstance : Nontrivial Z)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (card ▸ dvd_pow_self 2 pj.ne')
  have commute (g : A) (v : V) : g.val (z.val.val v) = z.val.val (g.val v) :=
    congrArg (fun h : A => h.val v) (Subgroup.mem_center_iff.mp z.property g)
  have sq : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have invol (v : V) : z.val.val (z.val.val v)=v := congrArg (fun g : Z => g.val.val v)
    (show z*z=1 by simpa [pow_two] using sq)
  refine ⟨z.val,invol,?_,commute⟩
  intro x fixed
  have ident : z=1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro y
    obtain ⟨g,rfl⟩ := transitive x y
    exact (commute g x).symm.trans (congrArg g.val fixed)
  simp [ident] at hz

/-- An invariant partition gives a quotient action that is again a transitive
permutation 2-group. The only required compatibility is equality of fibers. -/
theorem descend {V W : Type*} (A : Subgroup (Equiv.Perm V)) (two : IsPGroup 2 A)
    (transitive : ∀ x y, ∃ g : A, g.val x=y)
    (q : V → W) (onto : Surjective q) (respects : ∀ (g : A) x y, q x=q y → q (g.val x)=q (g.val y)) :
    ∃ D : Subgroup (Equiv.Perm W), IsPGroup 2 D ∧ (∀ x y, ∃ g : D,g.val x=y) ∧
      ∀ d : D, ∃ g : A, ∀ x, d.val (q x)=q (g.val x) := by
  classical
  let s := surjInv onto
  have qs := rightInverse_surjInv onto
  let f (g : A) (w : W) := q (g.val (s w))
  have equiv (g : A) (v : V) : f g (q v)=q (g.val v) := respects _ _ _ (qs _)
  have mul (g h : A) (w : W) : f g (f h w)=f (g*h) w := by
    obtain ⟨x,rfl⟩ := onto w
    exact (congrArg (f g) (equiv h x)).trans
      ((equiv g (h.val x)).trans (equiv (g*h) x).symm)
  have one (w : W) : f 1 w=w := qs _
  let perm (g : A) : Equiv.Perm W :=
    ⟨f g,f g⁻¹,fun w => (mul _ _ w).trans (by rw [inv_mul_cancel]; exact one w),
      fun w => (mul _ _ w).trans (by rw [mul_inv_cancel]; exact one w)⟩
  let hom : A →* Equiv.Perm W :=
    ⟨⟨perm,Equiv.ext one⟩,fun g h => Equiv.ext (fun w => (mul g h w).symm)⟩
  refine ⟨hom.range,two.of_surjective hom.rangeRestrict hom.rangeRestrict_surjective,?_,?_⟩
  · intro x y
    obtain ⟨a,rfl⟩ := onto x
    obtain ⟨b,rfl⟩ := onto y
    obtain ⟨g,hg⟩ := transitive a b
    exact ⟨hom.rangeRestrict g,(equiv g a).trans (congrArg q hg)⟩
  · rintro ⟨_,g,rfl⟩
    exact ⟨g,equiv g⟩

/-- In a square-free graph of minimum degree three a central free involution
of a transitive group gives a two-sheeted cover preserving the minimum degree. -/
theorem binary_quotient {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (degree : ∀ v, 3 ≤ G.degree v) (nosq : ¬cycleGraph 4 ⊑ G)
    (P : Subgroup (Equiv.Perm V)) [Nontrivial P] (two : IsPGroup 2 P)
    (transitive : ∀ x y, ∃ g : P, g.val x=y)
    (auto : ∀ (g : P) x y, G.Adj x y → G.Adj (g.val x) (g.val y)) :
    ∃ (W : Type) (_ : Fintype W) (B : SimpleGraph W) (_ : DecidableRel B.Adj)
      (D : Subgroup (Equiv.Perm W)), Fintype.card V=Fintype.card W*2 ∧
      (∀ w, 3 ≤ B.degree w) ∧ IsPGroup 2 D ∧ (∀ x y, ∃ d : D, d.val x=y) ∧
      (∀ (d : D) x y, B.Adj x y → B.Adj (d.val x) (d.val y)) ∧
      Fintype.card W ≠ 4 ∧
      ∀ n : ℕ, 3 ≤ n → cycleGraph n ⊑ B → cycleGraph n ⊑ G ∨ cycleGraph (2*n) ⊑ G := by
  classical
  obtain ⟨h,twice,free,commuting⟩ := central_pair P two transitive
  let t : V → V := h.val
  have sym (x y : V) : G.Adj x y → G.Adj (t x) (t y) := auto h x y
  obtain ⟨W,fw,q,onto,pair,card,fib⟩ := pair_projection t twice free
  let : Fintype W := fw
  have fixed (x : V) : q (t x)=q x := (pair _ _).mpr (Or.inr rfl)
  have noLoops (x : V) : ¬ G.Adj x (t x) := by
    intro loop
    have loops (y : V) : G.Adj y (t y) := by
      obtain ⟨g,rfl⟩ := transitive x y
      change G.Adj (g.val x) (h.val (g.val x))
      rw [←commuting g x]
      exact auto g x (t x) loop
    have other : ∃ y, G.Adj x y ∧ y≠t x := by
      by_contra! only
      have incl : G.neighborFinset x ⊆ {t x} := fun z hz =>
        Finset.mem_singleton.mpr (only z ((G.mem_neighborFinset _ _).mp hz))
      have bound := Finset.card_le_card incl
      rw [card_neighborFinset_eq_degree,Finset.card_singleton] at bound
      have := degree x
      omega
    obtain ⟨y,xy,neq⟩ := other
    have diff : x≠t y := fun eq => neq ((twice y).symm.trans (congrArg t eq.symm))
    exact nosq (square_of_four xy (loops y) (sym x y xy).symm loop.symm diff neq)
  have edgesDistinct {x y : V} (xy : G.Adj x y) : q x≠q y := by
    intro eq
    rcases (pair _ _).mp eq with rfl|rfl
    · exact xy.ne rfl
    · exact noLoops y xy.symm
  have neighborInj {x y z : V} (xy : G.Adj x y) (xz : G.Adj x z) (eq : q y=q z) : y=z := by
    rcases (pair _ _).mp eq with done|rfl
    · exact done
    · have across : G.Adj z (t x) := (show G.Adj (t x) z from (twice z) ▸ sym _ _ xy).symm
      exact (nosq (square_of_four xz across (sym _ _ xz) xy.symm (free x).symm (free z).symm)).elim
  let B := G.map q
  have lift (x : V) (w : W) (edge : B.Adj (q x) w) :
      ∃! y, G.Adj x y ∧ q y=w := by
    obtain ⟨_,a,b,ab,ha,hb⟩ := (map_adj' q G _ _).mp edge
    have existsLift : ∃ y, G.Adj x y ∧ q y=w := by
      rcases (pair _ _).mp ha with rfl|rfl
      · exact ⟨b,ab,hb⟩
      · exact ⟨t b,(twice x) ▸ sym _ _ ab,(fixed b).trans hb⟩
    obtain ⟨y,xy,hy⟩ := existsLift
    exact ⟨y,⟨xy,hy⟩,fun z hz => neighborInj hz.1 xy (hz.2.trans hy.symm)⟩
  have deg (w : W) : 3 ≤ B.degree w := by
    obtain ⟨v,rfl⟩ := onto w
    have nbr : B.neighborFinset (q v)=(G.neighborFinset v).image q := by
      ext y
      simp only [mem_neighborFinset,Finset.mem_image]
      constructor
      · intro adj
        exact (lift v y adj).exists
      · rintro ⟨u,vu,rfl⟩
        exact (map_adj' q G _ _).mpr ⟨edgesDistinct vu,v,u,vu,rfl,rfl⟩
    suffices inj : Set.InjOn q (G.neighborFinset v) by
      rw [←card_neighborFinset_eq_degree,nbr,Finset.card_image_of_injOn inj,card_neighborFinset_eq_degree]
      exact degree v
    exact fun _ hx _ hy eq => neighborInj ((mem_neighborFinset _ _ _).mp hx)
      ((mem_neighborFinset _ _ _).mp hy) eq
  have respects (g : P) (x y : V) (eq : q x=q y) : q (g.val x)=q (g.val y) := by
    apply (pair _ _).mpr
    rcases (pair _ _).mp eq with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr (commuting g y)
  obtain ⟨D,twoD,transD,desc⟩ := descend P two transitive q onto respects
  have autoD (d : D) (x y : W) (xy : B.Adj x y) : B.Adj (d.val x) (d.val y) := by
    obtain ⟨g,act⟩ := desc d
    obtain ⟨neq,a,b,ab,rfl,rfl⟩ := (map_adj' q G _ _).mp xy
    exact (map_adj' q G _ _).mpr ⟨fun eq => neq (d.val.injective eq),
      g.val a,g.val b,auto g _ _ ab,(act _).symm,(act _).symm⟩
  have notFour (size : Fintype.card W=4) : False := by
    have exactDeg (w : W) : B.degree w=3 := by
      have upper := B.degree_lt_card_verts w
      have lower := deg w
      omega
    exact nosq (square_over_four (G := G) (B := B) size exactDeg t twice sym q onto pair
      (fun x y e => (lift x y e).exists))
  refine ⟨W,fw,B,inferInstance,D,card,deg,twoD,transD,autoD,notFour,?_⟩
  rintro n large ⟨c⟩
  exact lift_two q onto (fun w => (fib w).le) large c lift


/-- At order 2^(m+3) a transitive 2-group guarantees a dyadic cycle on at
most half of the vertices, assuming only minimum degree three. -/
theorem short_of_two (m : ℕ) : ∀ (V : Type) [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj], Fintype.card V=2^(m+3) → (∀ v, 3 ≤ G.degree v) →
    ∀ P : Subgroup (Equiv.Perm V), IsPGroup 2 P → (∀ x y, ∃ g : P, g.val x=y) →
    (∀ (g : P) x y, G.Adj x y → G.Adj (g.val x) (g.val y)) →
    ∃ d : ℕ, 2 ≤ d ∧ 2^d ≤ 2^(m+2) ∧ cycleGraph (2^d) ⊑ G := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro V _ G _ order degree P two transitive auto
    have four : 4 ≤ 2^(m+2) := Nat.pow_le_pow_right (by decide : 0<2) (show 2 ≤ m+2 by omega)
    by_cases square : cycleGraph 4 ⊑ G
    · exact ⟨2,by decide,four,square⟩
    classical
    have large : 8 ≤ Fintype.card V := order ▸
      Nat.pow_le_pow_right (by decide : 0<2) (show 3 ≤ m+3 by omega)
    let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨x,y,distinct⟩ := exists_pair_ne V
    obtain ⟨g,move⟩ := transitive x y
    let : Nontrivial P := ⟨g,1,fun eq => distinct (by simpa [eq] using move)⟩
    obtain ⟨W,fw,B,db,D,cards,degreeB,twoD,transD,autoD,notFour,lifts⟩ :=
      binary_quotient degree square P two transitive auto
    let : Fintype W := fw
    let : DecidableRel B.Adj := db
    have next : Fintype.card W=2^(m+2) := by
      rw [order,show m+3=m+2+1 by omega,pow_succ] at cards
      omega
    cases m with
    | zero => exact (notFour next).elim
    | succ j =>
      obtain ⟨d,hd,small,cycle⟩ := ih j (by omega) W B next degreeB D twoD transD autoD
      have low : 4 ≤ 2^d := Nat.pow_le_pow_right (by decide : 0<2) hd
      have upper : 2^(j.succ+2)=2^(j+2)*2 := pow_succ 2 (j+2)
      rcases lifts _ (by omega) cycle with c|c
      · exact ⟨d,hd,by rw [upper]; omega,c⟩
      · refine ⟨d+1,by omega,by rw [upper,pow_succ]; omega,?_⟩
        rwa [pow_succ'] 

/-- Form the full permutation group of graph automorphisms and take a
transitive Sylow subgroup on a power-of-two number of vertices. -/
theorem short_of_transitive {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (degree : ∀ v, 3 ≤ G.degree v) (transitive : ∀ x y, ∃ g : G ≃g G, g x=y)
    {m : ℕ} (order : Fintype.card V=2^(m+3)) :
    ∃ d : ℕ, 2 ≤ d ∧ 2^d ≤ 2^(m+2) ∧ cycleGraph (2^d) ⊑ G := by
  classical
  let A : Subgroup (Equiv.Perm V) :=
    { carrier := {g | ∀ u v, G.Adj (g u) (g v) ↔ G.Adj u v}
      mul_mem' := fun hg hh u v => (hg _ _).trans (hh u v)
      one_mem' := fun _ _ => Iff.rfl
      inv_mem' := fun {g} hg u v => by simpa using (hg (g.symm u) (g.symm v)).symm }
  let : MulAction.IsPretransitive A V := ⟨fun u v => by
    obtain ⟨g,h⟩ := transitive u v
    exact ⟨⟨g.toEquiv,fun _ _ => g.map_rel_iff⟩,h⟩⟩
  let S : Sylow 2 A := Classical.choice inferInstance
  have strans := sylow_transitive (V := V) S (k := m+3) (by simpa [Nat.card_eq_fintype_card] using order)
  let P := S.1.map A.subtype
  have twoP : IsPGroup 2 P := S.2.map A.subtype
  have transP (u v : V) : ∃ g : P, g.val u=v := by
    obtain ⟨s,hs⟩ := strans.exists_smul_eq u v
    exact ⟨⟨s.val.val,s.val,s.property,rfl⟩,hs⟩
  apply short_of_two m V G order degree P twoP transP
  rintro ⟨_,g,_,rfl⟩ u v uv
  exact (g.property u v).mpr uv

/-- If a vertex-transitive graph of minimum degree three has order greater
than four and has any dyadic cycle, each vertex can be avoided by one. -/
theorem avoids_each_vertex {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (degree : ∀ v, 3 ≤ G.degree v) (transitive : ∀ x y, ∃ g : G ≃g G, g x=y)
    (big : 4 < Fintype.card V) (has : ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G)
    (r : V) : ∃ (k : ℕ) (c : (cycleGraph (2^k)).Copy G), 2 ≤ k ∧ r ∉ Set.range c := by
  obtain ⟨k,hk,w⟩ := has
  by_cases spanning : 2^k=Fintype.card V
  · have three : 3 ≤ k := by
      by_contra! small
      have : k=2 := by omega
      subst k
      omega
    obtain ⟨m,rfl⟩ : ∃ m, k=m+3 := ⟨k-3,by omega⟩
    obtain ⟨d,hd,small,cycle⟩ := short_of_transitive G degree transitive spanning.symm
    have proper : 2^d≠Fintype.card V := by
      rw [←spanning,show m+3=m+2+1 by omega,pow_succ]
      have positive : 0<2^(m+2) := by positivity
      omega
    obtain ⟨c,avoid⟩ := avoiding_cycle r (transitive r) proper cycle
    exact ⟨d,c,hd,avoid⟩
  · obtain ⟨c,avoid⟩ := avoiding_cycle r (transitive r) spanning w
    exact ⟨k,c,hk,avoid⟩

/-- In the rooted triangle-contraction branch, vertex transitivity is
impossible. At order four the unique degree-three graph is complete. -/
theorem rooted_obstruction_asymmetric {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (degree : ∀ v, 3 ≤ G.degree v) (r : V)
    (noneThrough : ∀ c : (cycleGraph 3).Copy G, r ∉ Set.range c)
    (has : ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G)
    (hit : ∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G, r ∈ Set.range c) :
    ¬∀ x y, ∃ g : G ≃g G, g x=y := by
  intro sym
  by_cases big : 4 < Fintype.card V
  · obtain ⟨k,c,hk,avoid⟩ := avoids_each_vertex G degree sym big has r
    exact avoid (hit k hk c)
  · have lower := degree r
    have upper := G.degree_lt_card_verts r
    have four : Fintype.card V=4 := by omega
    let e := (Fin.castSuccEmb : Fin 3 ↪ Fin 4).trans (Fintype.equivFinOfCardEq four).symm.toEmbedding
    have universal (u : V) : G.IsUniversal u := by
      apply (G.degree_eq_card_sub_one u).mp
      have := degree u
      have := G.degree_lt_card_verts u
      omega
    let c : (cycleGraph 3).Copy G :=
      ⟨⟨e,fun h => universal _ (fun eq => h.ne (e.injective eq))⟩,e.injective⟩
    obtain ⟨g,hg⟩ := sym (c 0) r
    exact noneThrough (g.toCopy.comp c) ⟨0,hg⟩

/-- Square at order four. -/
theorem square_at_four {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (four : Fintype.card V=4) (degree : ∀ x, 3 ≤ G.degree x) : cycleGraph 4 ⊑ G := by
  classical
  let e := (Fintype.equivFinOfCardEq four).symm
  refine ⟨⟨⟨e,?_⟩,e.injective⟩⟩
  intro u v uv
  have precise : G.degree (e u)=Fintype.card V-1 := by
    have := degree (e u)
    have := G.degree_lt_card_verts (e u)
    omega
  exact ((G.degree_eq_card_sub_one _).mp precise) (fun h => uv.ne (e.injective h))

/- The three-matching certificate below is by José Mejias (@mejiasd3v),
reused from the merged reduction in PR 5246. Root submissions can import only
the target module and Mathlib. -/


namespace LocalCommutation
open SimpleGraph
lemma route {X : Type*} (G : SimpleGraph (Bool × X)) (x : (Fin 10) → X)
    {n : ℕ} (hn : n=4 ∨ n=8 ∨ n=16) (w : Fin n → Bool × (Fin 10))
    (edges collisions : List (Fin 10 × Fin 10))
    (hwalk : ∀ i j, (cycleGraph n).Adj i j → (if (w i).1 == (w j).1 then false else if (w i).1 then edges.contains ((w j).2,(w i).2) else edges.contains ((w i).2,(w j).2)))
    (hpair : ∀ i j, i<j → (w i).1=(w j).1 →
      ((w i).2,(w j).2) ∈ collisions ∨ ((w j).2,(w i).2) ∈ collisions)
    (adj : ∀ e ∈ edges, G.Adj (false,x e.1) (true,x e.2))
    (recur : ∀ e ∈ collisions, x e.1 = x e.2 → (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G)) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  let f (i : Fin n) : Bool × X := ((w i).1,x (w i).2)
  have edge {a b : Bool × (Fin 10)} (h : (if a.1 == b.1 then false else if a.1 then edges.contains (b.2,a.2) else edges.contains (a.2,b.2))) : G.Adj (a.1,x a.2) (b.1,x b.2) := by
    obtain ⟨i,a⟩ := a; obtain ⟨j,b⟩ := b
    cases i <;> cases j <;> simp at h
    · exact adj _ h
    · exact (adj _ h).symm
  let g : cycleGraph n →g G := ⟨f, fun h => edge (hwalk _ _ h)⟩
  by_cases hi : Function.Injective g
  · have hs : cycleGraph n ⊑ G := ⟨g.toCopy hi⟩
    rcases hn with rfl|rfl|rfl
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr hs)
  · obtain ⟨i,j,h,hn'⟩ := Function.not_injective_iff.mp hi
    have bad (a b : Fin n) (lt : a<b) (e : g a = g b) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
      have s := congrArg Prod.fst e
      have r : x (w a).2 = x (w b).2 := congrArg Prod.snd e
      rcases hpair a b lt s with h | h
      · exact recur _ h r
      · exact recur _ h r.symm
    rcases lt_or_gt_of_ne hn' with hlt|hlt
    · exact bad i j hlt h
    · exact bad j i hlt h.symm

/-- Ten vertices of four oriented squares. A node identifies vertices whose labels
coincide. Identity, horizontal and vertical edges give an explicit closed walk;
if it repeats a vertex, congruence or injectivity forces a smaller quotient. -/
theorem shape0 {X : Type*} (G : SimpleGraph (Bool × X)) (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idAdj : ∀ u, G.Adj (false,u) (true,u))
    (pAdj : ∀ u, G.Adj (false,u) (true,p u))
    (qAdj : ∀ u, G.Adj (false,u) (true,q u)) (x : (Fin 10) → X)
    (edge0 : p (x 0) = x 4)
    (edge1 : q (x 0) = x 1)
    (edge2 : p (x 1) = x 5)
    (edge3 : q (x 1) = x 2)
    (edge4 : p (x 2) = x 6)
    (edge5 : q (x 2) = x 3)
    (edge6 : p (x 3) = x 7)
    (edge7 : q (x 4) = x 5)
    (edge8 : p (x 5) = x 8)
    (edge9 : q (x 5) = x 6)
    (edge10 : p (x 6) = x 9)
    (edge11 : q (x 6) = x 7)
    (edge12 : q (x 8) = x 9)
    : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  have node0 (eq1 : x 1 = x 0) (eq2 : x 2 = x 0) (eq3 : x 3 = x 0) (eq4 : x 4 = x 0) (eq5 : x 5 = x 0) (eq6 : x 6 = x 0) (eq7 : x 7 = x 0) (eq8 : x 8 = x 0) (eq9 : x 9 = x 0) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : id (x 0) = x 0 := rfl
    have hy : p (x 0) = x 0 := (edge0.trans eq4)
    exact False.elim ((sep (x 0)).1 (hy.trans hx.symm))
  have node1 (eq2 : x 2 = x 0) (eq3 : x 3 = x 1) (eq4 : x 4 = x 0) (eq5 : x 5 = x 1) (eq6 : x 6 = x 0) (eq7 : x 7 = x 1) (eq8 : x 8 = x 1) (eq9 : x 9 = x 0) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : id (x 0) = x 0 := rfl
    have hy : p (x 0) = x 0 := (edge0.trans eq4)
    exact False.elim ((sep (x 0)).1 (hy.trans hx.symm))
  have node2 (eq1 : x 1 = x 0) (eq2 : x 2 = x 0) (eq3 : x 3 = x 0) (eq5 : x 5 = x 4) (eq6 : x 6 = x 4) (eq7 : x 7 = x 4) (eq8 : x 8 = x 0) (eq9 : x 9 = x 0) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : id (x 0) = x 0 := rfl
    have hy : q (x 0) = x 0 := (edge1.trans eq1)
    exact False.elim ((sep (x 0)).2.1 (hy.trans hx.symm))
  have node3 (eq2 : x 2 = x 0) (eq3 : x 3 = x 1) (eq4 : x 4 = x 1) (eq5 : x 5 = x 0) (eq6 : x 6 = x 1) (eq7 : x 7 = x 0) (eq8 : x 8 = x 1) (eq9 : x 9 = x 0) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : p (x 0) = x 1 := (edge0.trans eq4)
    have hy : q (x 0) = x 1 := edge1
    exact False.elim ((sep (x 0)).2.2 (hx.trans hy.symm))
  have node4 (eq1 : x 1 = x 0) (eq2 : x 2 = x 0) (eq3 : x 3 = x 0) (eq5 : x 5 = x 4) (eq6 : x 6 = x 4) (eq7 : x 7 = x 4) (eq9 : x 9 = x 8) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : id (x 0) = x 0 := rfl
    have hy : q (x 0) = x 0 := (edge1.trans eq1)
    exact False.elim ((sep (x 0)).2.1 (hy.trans hx.symm))
  have node5 (eq3 : x 3 = x 0) (eq4 : x 4 = x 0) (eq5 : x 5 = x 1) (eq6 : x 6 = x 2) (eq7 : x 7 = x 0) (eq8 : x 8 = x 1) (eq9 : x 9 = x 2) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : id (x 0) = x 0 := rfl
    have hy : p (x 0) = x 0 := (edge0.trans eq4)
    exact False.elim ((sep (x 0)).1 (hy.trans hx.symm))
  have node6 (eq3 : x 3 = x 0) (eq4 : x 4 = x 2) (eq5 : x 5 = x 0) (eq6 : x 6 = x 1) (eq7 : x 7 = x 2) (eq8 : x 8 = x 2) (eq9 : x 9 = x 0) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,0), (true,0), (false,1), (true,1)]
      [(0,0), (1,0), (1,1), (0,1)] [(0,1)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : p (x 1) = x 0 := (edge2.trans eq5)
        exact e ▸ pAdj (x 1)
      · exact idAdj _
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl
      have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
      exact node0 hit.symm ((eq4.symm.trans t0).trans eq5) eq3 (t0.trans eq5) eq5 (eq6.trans hit.symm) (((eq7.trans eq4.symm).trans t0).trans eq5) (((eq8.trans eq4.symm).trans t0).trans eq5) eq9
  have node7 (eq3 : x 3 = x 0) (eq4 : x 4 = x 1) (eq5 : x 5 = x 2) (eq6 : x 6 = x 0) (eq7 : x 7 = x 1) (eq8 : x 8 = x 0) (eq9 : x 9 = x 1) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : p (x 0) = x 1 := (edge0.trans eq4)
    have hy : q (x 0) = x 1 := edge1
    exact False.elim ((sep (x 0)).2.2 (hx.trans hy.symm))
  have node8 (eq4 : x 4 = x 2) (eq5 : x 5 = x 3) (eq6 : x 6 = x 0) (eq7 : x 7 = x 1) (eq8 : x 8 = x 1) (eq9 : x 9 = x 2) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,0), (true,0), (false,2), (true,2)]
      [(0,0), (2,0), (2,2), (0,2)] [(0,2)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : p (x 2) = x 0 := (edge4.trans eq6)
        exact e ▸ pAdj (x 2)
      · exact idAdj _
      · have e : p (x 0) = x 2 := (edge0.trans eq4)
        exact e ▸ pAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl
      have t0 : x 1 = x 3 := (edge1.symm.trans ((congrArg q hit).trans edge5))
      exact node1 hit.symm t0.symm (eq4.trans hit.symm) (eq5.trans t0.symm) eq6 eq7 eq8 (eq9.trans hit.symm)
  have node9 (eq2 : x 2 = x 0) (eq3 : x 3 = x 1) (eq6 : x 6 = x 4) (eq7 : x 7 = x 5) (eq8 : x 8 = x 0) (eq9 : x 9 = x 1) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,0), (true,0), (false,1), (true,1)]
      [(0,0), (1,0), (1,1), (0,1)] [(0,1)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : q (x 1) = x 0 := (edge3.trans eq2)
        exact e ▸ qAdj (x 1)
      · exact idAdj _
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl
      have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
      exact node2 hit.symm eq2 (eq3.trans hit.symm) t0.symm eq6 (eq7.trans t0.symm) eq8 (eq9.trans hit.symm)
  have node10 (eq4 : x 4 = x 0) (eq5 : x 5 = x 1) (eq6 : x 6 = x 2) (eq7 : x 7 = x 3) (eq8 : x 8 = x 1) (eq9 : x 9 = x 2) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : id (x 0) = x 0 := rfl
    have hy : p (x 0) = x 0 := (edge0.trans eq4)
    exact False.elim ((sep (x 0)).1 (hy.trans hx.symm))
  have node11 (eq4 : x 4 = x 3) (eq5 : x 5 = x 0) (eq6 : x 6 = x 1) (eq7 : x 7 = x 2) (eq8 : x 8 = x 3) (eq9 : x 9 = x 0) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,0), (true,0), (false,1), (true,1)]
      [(0,0), (1,0), (1,1), (0,1)] [(0,1)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : p (x 1) = x 0 := (edge2.trans eq5)
        exact e ▸ pAdj (x 1)
      · exact idAdj _
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl
      have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
      have t1 : x 0 = x 2 := (p.injective (edge0.trans ((((t0.trans eq5).trans hit).trans eq6.symm).trans edge4.symm)))
      exact node0 hit.symm t1.symm ((eq4.symm.trans t0).trans eq5) (t0.trans eq5) eq5 (eq6.trans hit.symm) (eq7.trans t1.symm) (((eq8.trans eq4.symm).trans t0).trans eq5) eq9
  have node12 (eq5 : x 5 = x 0) (eq6 : x 6 = x 1) (eq7 : x 7 = x 2) (eq8 : x 8 = x 4) (eq9 : x 9 = x 0) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,0), (true,0), (false,1), (true,1)]
      [(0,0), (1,0), (1,1), (0,1)] [(0,1)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : p (x 1) = x 0 := (edge2.trans eq5)
        exact e ▸ pAdj (x 1)
      · exact idAdj _
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl
      have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
      have t1 : x 0 = x 2 := (p.injective (edge0.trans ((((t0.trans eq5).trans hit).trans eq6.symm).trans edge4.symm)))
      have t2 : x 0 = x 3 := (p.injective (edge0.trans ((((t0.trans eq5).trans t1).trans eq7.symm).trans edge6.symm)))
      exact node0 hit.symm t1.symm t2.symm (t0.trans eq5) eq5 (eq6.trans hit.symm) (eq7.trans t1.symm) ((eq8.trans t0).trans eq5) eq9
  have node13 (eq4 : x 4 = x 1) (eq5 : x 5 = x 2) (eq6 : x 6 = x 3) (eq8 : x 8 = x 3) (eq9 : x 9 = x 7) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : p (x 0) = x 1 := (edge0.trans eq4)
    have hy : q (x 0) = x 1 := edge1
    exact False.elim ((sep (x 0)).2.2 (hx.trans hy.symm))
  have node14 (eq2 : x 2 = x 0) (eq3 : x 3 = x 1) (eq6 : x 6 = x 4) (eq7 : x 7 = x 5) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,0), (true,0), (false,1), (true,1)]
      [(0,0), (1,0), (1,1), (0,1)] [(0,1)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : q (x 1) = x 0 := (edge3.trans eq2)
        exact e ▸ qAdj (x 1)
      · exact idAdj _
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl
      have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
      have t1 : x 8 = x 9 := (edge8.symm.trans ((congrArg p (t0.symm.trans eq6.symm)).trans edge10))
      exact node4 hit.symm eq2 (eq3.trans hit.symm) t0.symm eq6 (eq7.trans t0.symm) t1.symm
  have node15 (eq6 : x 6 = x 0) (eq7 : x 7 = x 1) (eq9 : x 9 = x 4) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=8) (by decide) ![(false,0), (true,0), (false,2), (true,2), (false,1), (true,5), (false,4), (true,4)]
      [(0,0), (2,0), (2,2), (1,2), (1,5), (4,5), (4,4), (0,4)] [(0,1), (0,2), (0,4), (0,5), (1,2), (1,4), (2,4), (2,5), (4,5)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : p (x 2) = x 0 := (edge4.trans eq6)
        exact e ▸ pAdj (x 2)
      · exact idAdj _
      · have e : q (x 1) = x 2 := edge3
        exact e ▸ qAdj (x 1)
      · have e : p (x 1) = x 5 := edge2
        exact e ▸ pAdj (x 1)
      · have e : q (x 4) = x 5 := edge7
        exact e ▸ qAdj (x 4)
      · exact idAdj _
      · have e : p (x 0) = x 4 := edge0
        exact e ▸ pAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q hit).trans edge3))
        have t2 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (hit.trans t1)).trans edge5))
        have t3 : x 0 = x 5 := (q.injective (edge1.trans ((hit.symm.trans eq6.symm).trans edge9.symm)))
        have t4 : x 0 = x 8 := (q.injective (edge1.trans ((((hit.symm.trans t3).trans t0.symm).trans eq9.symm).trans edge12.symm)))
        exact node0 hit.symm (t1.symm.trans hit.symm) (t2.symm.trans hit.symm) (t0.trans t3.symm) t3.symm eq6 (eq7.trans hit.symm) t4.symm ((eq9.trans t0).trans t3.symm)
      · have t0 : x 4 = x 6 := (edge0.symm.trans ((congrArg p hit).trans edge4))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q hit).trans edge5))
        have t2 : x 1 = x 5 := (edge1.symm.trans ((congrArg q (eq6.symm.trans t0.symm)).trans edge7))
        have t3 : x 5 = x 8 := (edge2.symm.trans ((congrArg p t2).trans edge8))
        exact node1 hit.symm t1.symm (t0.trans eq6) t2.symm eq6 eq7 (t3.symm.trans t2.symm) ((eq9.trans t0).trans eq6)
      · have t0 : x 0 = x 2 := (p.injective (edge0.trans ((hit.symm.trans eq6.symm).trans edge4.symm)))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q t0).trans edge5))
        have t2 : x 1 = x 5 := (edge1.symm.trans ((congrArg q hit).trans edge7))
        have t3 : x 5 = x 8 := (edge2.symm.trans ((congrArg p t2).trans edge8))
        exact node1 t0.symm t1.symm hit.symm t2.symm eq6 eq7 (t3.symm.trans t2.symm) (eq9.trans hit.symm)
      · have t0 : x 4 = x 8 := (edge0.symm.trans ((congrArg p hit).trans edge8))
        have t1 : x 1 = x 6 := (edge1.symm.trans ((congrArg q hit).trans edge9))
        have t2 : x 1 = x 2 := (p.injective (edge2.trans ((hit.symm.trans eq6.symm).trans edge4.symm)))
        have t3 : x 1 = x 3 := (p.injective (edge2.trans ((((hit.symm.trans eq6.symm).trans t1.symm).trans eq7.symm).trans edge6.symm)))
        have t4 : x 5 = x 8 := (edge2.symm.trans ((congrArg p ((t1.trans eq6).trans hit)).trans edge8))
        exact node0 (t1.trans eq6) ((t2.symm.trans t1).trans eq6) ((t3.symm.trans t1).trans eq6) ((t0.trans t4.symm).trans hit.symm) hit.symm eq6 ((eq7.trans t1).trans eq6) (t4.symm.trans hit.symm) (((eq9.trans t0).trans t4.symm).trans hit.symm)
      · have t0 : x 0 = x 1 := (q.injective (edge1.trans (hit.trans edge3.symm)))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (t0.trans hit)).trans edge5))
        have t2 : x 0 = x 5 := (q.injective (edge1.trans ((t0.symm.trans eq6.symm).trans edge9.symm)))
        have t3 : x 5 = x 8 := (edge2.symm.trans ((congrArg p (t0.symm.trans t2)).trans edge8))
        have t4 : x 5 = x 9 := (edge2.symm.trans ((congrArg p (t0.symm.trans eq6.symm)).trans edge10))
        exact node0 t0.symm (hit.symm.trans t0.symm) (t1.symm.trans t0.symm) ((eq9.symm.trans t4.symm).trans t2.symm) t2.symm eq6 (eq7.trans t0.symm) (t3.symm.trans t2.symm) (t4.symm.trans t2.symm)
      · have t0 : x 0 = x 3 := (p.injective (edge0.trans ((hit.symm.trans eq7.symm).trans edge6.symm)))
        have t1 : x 0 = x 8 := (q.injective (edge1.trans ((hit.trans eq9.symm).trans edge12.symm)))
        have t2 : x 2 = x 5 := (edge3.symm.trans ((congrArg q hit).trans edge7))
        exact node7 t0.symm hit.symm t2.symm eq6 eq7 t1.symm (eq9.trans hit.symm)
      · have t0 : x 1 = x 8 := (q.injective (edge3.trans ((hit.trans eq9.symm).trans edge12.symm)))
        have t1 : x 3 = x 5 := (edge5.symm.trans ((congrArg q hit).trans edge7))
        exact node8 hit.symm t1.symm eq6 eq7 t0.symm (eq9.trans hit.symm)
      · have t0 : x 1 = x 4 := (q.injective (edge3.trans (hit.trans edge7.symm)))
        have t1 : x 6 = x 8 := (edge4.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 3 = x 6 := (edge5.symm.trans ((congrArg q hit).trans edge9))
        exact node7 (t2.trans eq6) t0.symm hit.symm eq6 eq7 (t1.symm.trans eq6) (eq9.trans t0.symm)
      · have t0 : x 0 = x 1 := (p.injective (edge0.trans (hit.trans edge2.symm)))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q t0).trans edge3))
        have t2 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (t0.trans t1)).trans edge5))
        have t3 : x 0 = x 5 := (q.injective (edge1.trans ((t0.symm.trans eq6.symm).trans edge9.symm)))
        have t4 : x 0 = x 8 := (q.injective (edge1.trans ((((t0.symm.trans t3).trans hit.symm).trans eq9.symm).trans edge12.symm)))
        exact node0 t0.symm (t1.symm.trans t0.symm) (t2.symm.trans t0.symm) (hit.trans t3.symm) t3.symm eq6 (eq7.trans t0.symm) t4.symm ((eq9.trans hit).trans t3.symm)
  have node16 (eq4 : x 4 = x 2) (eq5 : x 5 = x 3) (eq8 : x 8 = x 7) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,0), (true,1), (false,1), (true,2)]
      [(0,1), (1,1), (1,2), (0,2)] [(0,1), (1,2)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
      · exact idAdj _
      · have e : q (x 1) = x 2 := edge3
        exact e ▸ qAdj (x 1)
      · have e : p (x 0) = x 2 := (edge0.trans eq4)
        exact e ▸ pAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q hit).trans edge3))
        have t2 : x 1 = x 6 := (edge1.symm.trans ((congrArg q (((hit.trans t1).trans eq4.symm).trans t0)).trans edge9))
        have t3 : x 1 = x 7 := (edge1.symm.trans ((congrArg q (hit.trans t2)).trans edge11))
        have t4 : x 1 = x 9 := (edge1.symm.trans ((congrArg q ((hit.trans t3).trans eq8.symm)).trans edge12))
        exact node0 hit.symm (t1.symm.trans hit.symm) ((((eq5.symm.trans t0.symm).trans eq4).trans t1.symm).trans hit.symm) ((eq4.trans t1.symm).trans hit.symm) (((t0.symm.trans eq4).trans t1.symm).trans hit.symm) (t2.symm.trans hit.symm) (t3.symm.trans hit.symm) ((eq8.trans t3.symm).trans hit.symm) (t4.symm.trans hit.symm)
      · have t0 : x 0 = x 1 := (q.injective (edge1.trans (hit.trans edge3.symm)))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (t0.trans hit)).trans edge5))
        have t2 : x 1 = x 6 := (edge1.symm.trans ((congrArg q ((t0.trans t1).trans eq5.symm)).trans edge9))
        have t3 : x 1 = x 7 := (edge1.symm.trans ((congrArg q (t0.trans t2)).trans edge11))
        have t4 : x 1 = x 9 := (edge1.symm.trans ((congrArg q ((t0.trans t3).trans eq8.symm)).trans edge12))
        exact node0 t0.symm (hit.symm.trans t0.symm) (t1.symm.trans t0.symm) ((eq4.trans hit.symm).trans t0.symm) ((eq5.trans t1.symm).trans t0.symm) (t2.symm.trans t0.symm) (t3.symm.trans t0.symm) ((eq8.trans t3.symm).trans t0.symm) (t4.symm.trans t0.symm)
  have node17 (eq3 : x 3 = x 0) (eq7 : x 7 = x 4) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=8) (by decide) ![(false,0), (true,0), (false,2), (true,2), (false,1), (true,5), (false,4), (true,4)]
      [(0,0), (2,0), (2,2), (1,2), (1,5), (4,5), (4,4), (0,4)] [(0,1), (0,2), (0,4), (0,5), (1,2), (1,4), (2,4), (2,5), (4,5)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : q (x 2) = x 0 := (edge5.trans eq3)
        exact e ▸ qAdj (x 2)
      · exact idAdj _
      · have e : q (x 1) = x 2 := edge3
        exact e ▸ qAdj (x 1)
      · have e : p (x 1) = x 5 := edge2
        exact e ▸ pAdj (x 1)
      · have e : q (x 4) = x 5 := edge7
        exact e ▸ qAdj (x 4)
      · exact idAdj _
      · have e : p (x 0) = x 4 := edge0
        exact e ▸ pAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q hit).trans edge3))
        have t2 : x 5 = x 6 := (edge2.symm.trans ((congrArg p t1).trans edge4))
        have t3 : x 8 = x 9 := (edge8.symm.trans ((congrArg p t2).trans edge10))
        exact node4 hit.symm (t1.symm.trans hit.symm) eq3 t0.symm (t2.symm.trans t0.symm) eq7 t3.symm
      · have t0 : x 4 = x 6 := (edge0.symm.trans ((congrArg p hit).trans edge4))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q hit).trans edge5))
        have t2 : x 5 = x 6 := (edge2.symm.trans ((congrArg p ((t1.trans eq3).trans hit)).trans edge4))
        have t3 : x 8 = x 9 := (edge8.symm.trans ((congrArg p t2).trans edge10))
        exact node4 (t1.trans eq3) hit.symm eq3 (t2.trans t0.symm) t0.symm eq7 t3.symm
      · have t0 : x 1 = x 5 := (edge1.symm.trans ((congrArg q hit).trans edge7))
        have t1 : x 5 = x 8 := (edge2.symm.trans ((congrArg p t0).trans edge8))
        have t2 : x 2 = x 6 := (edge3.symm.trans ((congrArg q t0).trans edge9))
        have t3 : x 2 = x 9 := (edge3.symm.trans ((congrArg q (t0.trans t1)).trans edge12))
        exact node5 eq3 hit.symm t0.symm t2.symm (eq7.trans hit.symm) (t1.symm.trans t0.symm) t3.symm
      · have t0 : x 4 = x 8 := (edge0.symm.trans ((congrArg p hit).trans edge8))
        have t1 : x 1 = x 6 := (edge1.symm.trans ((congrArg q hit).trans edge9))
        have t2 : x 5 = x 9 := (edge2.symm.trans ((congrArg p t1).trans edge10))
        have t3 : x 2 = x 7 := (edge3.symm.trans ((congrArg q t1).trans edge11))
        exact node6 eq3 (eq7.symm.trans t3.symm) hit.symm t1.symm t3.symm ((t0.symm.trans eq7.symm).trans t3.symm) (t2.symm.trans hit.symm)
      · have t0 : x 0 = x 1 := (q.injective (edge1.trans (hit.trans edge3.symm)))
        have t1 : x 5 = x 6 := (edge2.symm.trans ((congrArg p hit).trans edge4))
        have t2 : x 5 = x 7 := (edge2.symm.trans ((congrArg p (t0.symm.trans eq3.symm)).trans edge6))
        have t3 : x 8 = x 9 := (edge8.symm.trans ((congrArg p t1).trans edge10))
        exact node4 t0.symm (hit.symm.trans t0.symm) eq3 (t2.trans eq7) ((t1.symm.trans t2).trans eq7) eq7 t3.symm
      · have t0 : x 0 = x 6 := (q.injective (edge1.trans ((hit.trans eq7.symm).trans edge11.symm)))
        have t1 : x 2 = x 5 := (edge3.symm.trans ((congrArg q hit).trans edge7))
        have t2 : x 6 = x 8 := (edge4.symm.trans ((congrArg p t1).trans edge8))
        have t3 : x 7 = x 9 := (edge6.symm.trans ((congrArg p (eq3.trans t0)).trans edge10))
        exact node7 eq3 hit.symm t1.symm t0.symm (eq7.trans hit.symm) (t2.symm.trans t0.symm) ((t3.symm.trans eq7).trans hit.symm)
      · have t0 : x 1 = x 6 := (q.injective (edge3.trans ((hit.trans eq7.symm).trans edge11.symm)))
        have t1 : x 3 = x 5 := (edge5.symm.trans ((congrArg q hit).trans edge7))
        have t2 : x 7 = x 8 := (edge6.symm.trans ((congrArg p t1).trans edge8))
        have t3 : x 5 = x 9 := (edge7.symm.trans ((congrArg q (eq7.symm.trans t2)).trans edge12))
        exact node6 eq3 hit.symm (t1.symm.trans eq3) t0.symm (eq7.trans hit.symm) ((t2.symm.trans eq7).trans hit.symm) ((t3.symm.trans t1.symm).trans eq3)
      · have t0 : x 1 = x 4 := (q.injective (edge3.trans (hit.trans edge7.symm)))
        have t1 : x 6 = x 8 := (edge4.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 3 = x 6 := (edge5.symm.trans ((congrArg q hit).trans edge9))
        have t3 : x 7 = x 9 := (edge6.symm.trans ((congrArg p t2).trans edge10))
        exact node7 eq3 t0.symm hit.symm (t2.symm.trans eq3) (eq7.trans t0.symm) ((t1.symm.trans t2.symm).trans eq3) ((t3.symm.trans eq7).trans t0.symm)
      · have t0 : x 0 = x 1 := (p.injective (edge0.trans (hit.trans edge2.symm)))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q t0).trans edge3))
        have t2 : x 5 = x 6 := (edge2.symm.trans ((congrArg p t1).trans edge4))
        have t3 : x 8 = x 9 := (edge8.symm.trans ((congrArg p t2).trans edge10))
        exact node4 t0.symm (t1.symm.trans t0.symm) eq3 hit.symm (t2.symm.trans hit.symm) eq7 t3.symm
  have node18 (eq8 : x 8 = x 0) (eq9 : x 9 = x 1) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=8) (by decide) ![(false,0), (true,0), (false,5), (true,6), (false,2), (true,2), (false,1), (true,1)]
      [(0,0), (5,0), (5,6), (2,6), (2,2), (1,2), (1,1), (0,1)] [(0,1), (0,2), (0,5), (0,6), (1,2), (1,5), (1,6), (2,5), (2,6)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : p (x 5) = x 0 := (edge8.trans eq8)
        exact e ▸ pAdj (x 5)
      · have e : q (x 5) = x 6 := edge9
        exact e ▸ qAdj (x 5)
      · have e : p (x 2) = x 6 := edge4
        exact e ▸ pAdj (x 2)
      · exact idAdj _
      · have e : q (x 1) = x 2 := edge3
        exact e ▸ qAdj (x 1)
      · exact idAdj _
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q hit).trans edge3))
        have t2 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (hit.trans t1)).trans edge5))
        have t3 : x 5 = x 6 := (edge2.symm.trans ((congrArg p t1).trans edge4))
        have t4 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t2).trans edge6))
        exact node2 hit.symm (t1.symm.trans hit.symm) (t2.symm.trans hit.symm) t0.symm (t3.symm.trans t0.symm) (t4.symm.trans t0.symm) eq8 (eq9.trans hit.symm)
      · have t0 : x 4 = x 6 := (edge0.symm.trans ((congrArg p hit).trans edge4))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q hit).trans edge5))
        have t2 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t1).trans edge6))
        exact node9 hit.symm t1.symm t0.symm t2.symm eq8 eq9
      · have t0 : x 4 = x 8 := (edge0.symm.trans ((congrArg p hit).trans edge8))
        have t1 : x 1 = x 5 := (edge1.symm.trans ((congrArg q (eq8.symm.trans t0.symm)).trans edge7))
        have t2 : x 1 = x 6 := (edge1.symm.trans ((congrArg q hit).trans edge9))
        have t3 : x 1 = x 7 := (edge1.symm.trans ((congrArg q ((hit.trans t1.symm).trans t2)).trans edge11))
        have t4 : x 1 = x 2 := (p.injective (edge2.trans ((t1.symm.trans t2).trans edge4.symm)))
        have t5 : x 1 = x 3 := (p.injective (edge2.trans ((t1.symm.trans t3).trans edge6.symm)))
        exact node0 (t1.trans hit.symm) ((t4.symm.trans t1).trans hit.symm) ((t5.symm.trans t1).trans hit.symm) (t0.trans eq8) hit.symm ((t2.symm.trans t1).trans hit.symm) ((t3.symm.trans t1).trans hit.symm) eq8 ((eq9.trans t1).trans hit.symm)
      · have t0 : x 4 = x 9 := (edge0.symm.trans ((congrArg p hit).trans edge10))
        have t1 : x 1 = x 7 := (edge1.symm.trans ((congrArg q hit).trans edge11))
        have t2 : x 2 = x 5 := (edge3.symm.trans ((congrArg q (eq9.symm.trans t0.symm)).trans edge7))
        have t3 : x 3 = x 6 := (edge5.symm.trans ((congrArg q t2).trans edge9))
        exact node7 (t3.trans hit.symm) (t0.trans eq9) t2.symm hit.symm t1.symm eq8 eq9
      · have t0 : x 0 = x 1 := (q.injective (edge1.trans (hit.trans edge3.symm)))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (t0.trans hit)).trans edge5))
        have t2 : x 5 = x 6 := (edge2.symm.trans ((congrArg p hit).trans edge4))
        have t3 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t1).trans edge6))
        have t4 : x 4 = x 5 := (q.injective (edge7.trans (t2.trans edge9.symm)))
        exact node2 t0.symm (hit.symm.trans t0.symm) (t1.symm.trans t0.symm) t4.symm (t2.symm.trans t4.symm) (t3.symm.trans t4.symm) eq8 (eq9.trans t0.symm)
      · have t0 : x 0 = x 4 := (q.injective (edge1.trans (hit.trans edge7.symm)))
        have t1 : x 5 = x 8 := (edge2.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 1 = x 6 := (p.injective (edge2.trans ((hit.symm.trans eq9.symm).trans edge10.symm)))
        have t3 : x 2 = x 5 := (edge3.symm.trans ((congrArg q (((hit.trans t1).trans eq8).trans t0)).trans edge7))
        have t4 : x 2 = x 7 := (edge3.symm.trans ((congrArg q t2).trans edge11))
        have t5 : x 2 = x 3 := (p.injective (edge4.trans ((((t2.symm.trans hit).trans t3.symm).trans t4).trans edge6.symm)))
        exact node0 ((hit.trans t1).trans eq8) ((t3.trans t1).trans eq8) (((t5.symm.trans t3).trans t1).trans eq8) t0.symm (t1.trans eq8) (((t2.symm.trans hit).trans t1).trans eq8) (((t4.symm.trans t3).trans t1).trans eq8) eq8 (((eq9.trans hit).trans t1).trans eq8)
      · have t0 : x 0 = x 5 := (q.injective (edge1.trans (hit.trans edge9.symm)))
        have t1 : x 1 = x 5 := (p.injective (edge2.trans ((t0.symm.trans eq8.symm).trans edge8.symm)))
        have t2 : x 2 = x 6 := (edge3.symm.trans ((congrArg q t1).trans edge9))
        have t3 : x 2 = x 7 := (edge3.symm.trans ((congrArg q hit).trans edge11))
        have t4 : x 2 = x 3 := (p.injective (edge4.trans ((t2.symm.trans t3).trans edge6.symm)))
        have t5 : x 2 = x 4 := (q.injective (edge5.trans ((((t4.symm.trans t2).trans hit.symm).trans t1).trans edge7.symm)))
        exact node0 (t1.trans t0.symm) (((t2.trans hit.symm).trans t1).trans t0.symm) ((((t4.symm.trans t2).trans hit.symm).trans t1).trans t0.symm) ((((t5.symm.trans t2).trans hit.symm).trans t1).trans t0.symm) t0.symm ((hit.symm.trans t1).trans t0.symm) ((((t3.symm.trans t2).trans hit.symm).trans t1).trans t0.symm) eq8 ((eq9.trans t1).trans t0.symm)
      · have t0 : x 1 = x 4 := (q.injective (edge3.trans (hit.trans edge7.symm)))
        have t1 : x 6 = x 8 := (edge4.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 3 = x 6 := (edge5.symm.trans ((congrArg q hit).trans edge9))
        have t3 : x 7 = x 9 := (edge6.symm.trans ((congrArg p t2).trans edge10))
        exact node7 ((t2.trans t1).trans eq8) t0.symm hit.symm (t1.trans eq8) (t3.trans eq9) eq8 eq9
      · have t0 : x 1 = x 5 := (q.injective (edge3.trans (hit.trans edge9.symm)))
        have t1 : x 6 = x 9 := (edge4.symm.trans ((congrArg p hit).trans edge10))
        have t2 : x 3 = x 6 := (edge5.symm.trans ((congrArg q (((hit.trans t1).trans eq9).trans t0)).trans edge9))
        have t3 : x 3 = x 7 := (edge5.symm.trans ((congrArg q hit).trans edge11))
        have t4 : x 2 = x 8 := (q.injective (edge5.trans ((t2.trans t1).trans edge12.symm)))
        have t5 : x 4 = x 5 := (q.injective (edge7.trans (((t0.symm.trans eq9.symm).trans t1.symm).trans edge9.symm)))
        exact node0 ((((eq9.symm.trans t1.symm).trans hit.symm).trans t4).trans eq8) (t4.trans eq8) (((t2.trans hit.symm).trans t4).trans eq8) ((((((t5.trans t0.symm).trans eq9.symm).trans t1.symm).trans hit.symm).trans t4).trans eq8) (((((t0.symm.trans eq9.symm).trans t1.symm).trans hit.symm).trans t4).trans eq8) ((hit.symm.trans t4).trans eq8) ((((t3.symm.trans t2).trans hit.symm).trans t4).trans eq8) eq8 (((t1.symm.trans hit.symm).trans t4).trans eq8)
  have node19 (eq8 : x 8 = x 1) (eq9 : x 9 = x 2) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,1), (true,1), (false,5), (true,5)]
      [(1,1), (5,1), (5,5), (1,5)] [(1,5)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : p (x 5) = x 1 := (edge8.trans eq8)
        exact e ▸ pAdj (x 5)
      · exact idAdj _
      · have e : p (x 1) = x 5 := edge2
        exact e ▸ pAdj (x 1)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl
      have t0 : x 0 = x 4 := (q.injective (edge1.trans (hit.trans edge7.symm)))
      have t1 : x 2 = x 6 := (edge3.symm.trans ((congrArg q hit).trans edge9))
      have t2 : x 3 = x 7 := (edge5.symm.trans ((congrArg q t1).trans edge11))
      exact node10 t0.symm hit.symm t1.symm t2.symm eq8 eq9
  have node20 (eq8 : x 8 = x 2) (eq9 : x 9 = x 3) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,1), (true,2), (false,5), (true,5)]
      [(1,2), (5,2), (5,5), (1,5)] [(1,5), (2,5)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · have e : q (x 1) = x 2 := edge3
        exact e ▸ qAdj (x 1)
      · have e : p (x 5) = x 2 := (edge8.trans eq8)
        exact e ▸ pAdj (x 5)
      · exact idAdj _
      · have e : p (x 1) = x 5 := edge2
        exact e ▸ pAdj (x 1)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · have t0 : x 0 = x 4 := (q.injective (edge1.trans (hit.trans edge7.symm)))
        have t1 : x 5 = x 8 := (edge2.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 2 = x 3 := (edge3.symm.trans ((congrArg q ((hit.trans t1).trans eq8)).trans edge5))
        have t3 : x 1 = x 4 := (q.injective (edge3.trans ((eq8.symm.trans t1.symm).trans edge7.symm)))
        have t4 : x 2 = x 6 := (edge3.symm.trans ((congrArg q hit).trans edge9))
        have t5 : x 2 = x 7 := (edge3.symm.trans ((congrArg q (((hit.trans t1).trans eq8).trans t4)).trans edge11))
        exact node0 (t3.trans t0.symm) ((((eq8.symm.trans t1.symm).trans hit.symm).trans t3).trans t0.symm) (((((t2.symm.trans eq8.symm).trans t1.symm).trans hit.symm).trans t3).trans t0.symm) t0.symm ((hit.symm.trans t3).trans t0.symm) (((((t4.symm.trans eq8.symm).trans t1.symm).trans hit.symm).trans t3).trans t0.symm) (((((t5.symm.trans eq8.symm).trans t1.symm).trans hit.symm).trans t3).trans t0.symm) (((t1.symm.trans hit.symm).trans t3).trans t0.symm) ((((((eq9.trans t2.symm).trans eq8.symm).trans t1.symm).trans hit.symm).trans t3).trans t0.symm)
      · have t0 : x 1 = x 5 := (p.injective (edge2.trans ((hit.symm.trans eq8.symm).trans edge8.symm)))
        have t1 : x 2 = x 3 := (edge3.symm.trans ((congrArg q (t0.trans hit.symm)).trans edge5))
        have t2 : x 1 = x 4 := (q.injective (edge3.trans (hit.trans edge7.symm)))
        have t3 : x 2 = x 6 := (edge3.symm.trans ((congrArg q t0).trans edge9))
        have t4 : x 2 = x 7 := (edge3.symm.trans ((congrArg q ((t0.trans hit.symm).trans t3)).trans edge11))
        have t5 : x 0 = x 1 := (p.injective (edge0.trans ((t2.symm.trans t0).trans edge2.symm)))
        exact node0 t5.symm ((hit.trans t0.symm).trans t5.symm) (((t1.symm.trans hit).trans t0.symm).trans t5.symm) (t2.symm.trans t5.symm) (t0.symm.trans t5.symm) (((t3.symm.trans hit).trans t0.symm).trans t5.symm) (((t4.symm.trans hit).trans t0.symm).trans t5.symm) (((eq8.trans hit).trans t0.symm).trans t5.symm) ((((eq9.trans t1.symm).trans hit).trans t0.symm).trans t5.symm)
  have node21 (eq8 : x 8 = x 3) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,2), (true,3), (false,5), (true,6)]
      [(2,3), (5,3), (5,6), (2,6)] [(2,5), (3,6)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · have e : q (x 2) = x 3 := edge5
        exact e ▸ qAdj (x 2)
      · have e : p (x 5) = x 3 := (edge8.trans eq8)
        exact e ▸ pAdj (x 5)
      · have e : q (x 5) = x 6 := edge9
        exact e ▸ qAdj (x 5)
      · have e : p (x 2) = x 6 := edge4
        exact e ▸ pAdj (x 2)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · have t0 : x 1 = x 4 := (q.injective (edge3.trans (hit.trans edge7.symm)))
        have t1 : x 6 = x 8 := (edge4.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 7 = x 9 := (edge6.symm.trans ((congrArg p (eq8.symm.trans t1.symm)).trans edge10))
        exact node13 t0.symm hit.symm (t1.trans eq8) eq8 t2.symm
      · have t0 : x 2 = x 5 := (p.injective (edge4.trans ((hit.symm.trans eq8.symm).trans edge8.symm)))
        have t1 : x 7 = x 9 := (edge6.symm.trans ((congrArg p hit).trans edge10))
        have t2 : x 1 = x 4 := (q.injective (edge3.trans (t0.trans edge7.symm)))
        exact node13 t2.symm t0.symm hit.symm eq8 t1.symm
  have node22 (eq4 : x 4 = x 3) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=8) (by decide) ![(false,0), (true,1), (false,1), (true,5), (false,5), (true,6), (false,2), (true,3)]
      [(0,1), (1,1), (1,5), (5,5), (5,6), (2,6), (2,3), (0,3)] [(0,1), (0,2), (0,5), (1,2), (1,3), (1,5), (1,6), (2,5), (3,5), (3,6), (5,6)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
      · exact idAdj _
      · have e : p (x 1) = x 5 := edge2
        exact e ▸ pAdj (x 1)
      · exact idAdj _
      · have e : q (x 5) = x 6 := edge9
        exact e ▸ qAdj (x 5)
      · have e : p (x 2) = x 6 := edge4
        exact e ▸ pAdj (x 2)
      · have e : q (x 2) = x 3 := edge5
        exact e ▸ qAdj (x 2)
      · have e : p (x 0) = x 3 := (edge0.trans eq4)
        exact e ▸ pAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q hit).trans edge3))
        have t2 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (hit.trans t1)).trans edge5))
        have t3 : x 1 = x 6 := (edge1.symm.trans ((congrArg q (((hit.trans t2).trans eq4.symm).trans t0)).trans edge9))
        have t4 : x 1 = x 7 := (edge1.symm.trans ((congrArg q (hit.trans t3)).trans edge11))
        have t5 : x 5 = x 8 := (edge2.symm.trans ((congrArg p ((t2.trans eq4.symm).trans t0)).trans edge8))
        have t6 : x 5 = x 9 := (edge2.symm.trans ((congrArg p t3).trans edge10))
        exact node0 hit.symm (t1.symm.trans hit.symm) (t2.symm.trans hit.symm) ((eq4.trans t2.symm).trans hit.symm) (((t0.symm.trans eq4).trans t2.symm).trans hit.symm) (t3.symm.trans hit.symm) (t4.symm.trans hit.symm) ((((t5.symm.trans t0.symm).trans eq4).trans t2.symm).trans hit.symm) ((((t6.symm.trans t0.symm).trans eq4).trans t2.symm).trans hit.symm)
      · have t0 : x 4 = x 6 := (edge0.symm.trans ((congrArg p hit).trans edge4))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q hit).trans edge5))
        have t2 : x 0 = x 5 := (q.injective (edge1.trans (((t1.trans eq4.symm).trans t0).trans edge9.symm)))
        have t3 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t1).trans edge6))
        have t4 : x 5 = x 9 := (edge2.symm.trans ((congrArg p ((t1.trans eq4.symm).trans t0)).trans edge10))
        have t5 : x 1 = x 8 := (q.injective (edge3.trans (((hit.symm.trans t2).trans t4).trans edge12.symm)))
        exact node3 hit.symm t1.symm (eq4.trans t1.symm) t2.symm ((t0.symm.trans eq4).trans t1.symm) (t3.symm.trans t2.symm) t5.symm (t4.symm.trans t2.symm)
      · have t0 : x 4 = x 8 := (edge0.symm.trans ((congrArg p hit).trans edge8))
        have t1 : x 1 = x 6 := (edge1.symm.trans ((congrArg q hit).trans edge9))
        have t2 : x 5 = x 9 := (edge2.symm.trans ((congrArg p t1).trans edge10))
        have t3 : x 2 = x 7 := (edge3.symm.trans ((congrArg q t1).trans edge11))
        exact node11 eq4 hit.symm t1.symm t3.symm (t0.symm.trans eq4) (t2.symm.trans hit.symm)
      · have t0 : x 0 = x 1 := (q.injective (edge1.trans (hit.trans edge3.symm)))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (t0.trans hit)).trans edge5))
        have t2 : x 1 = x 5 := (edge1.symm.trans ((congrArg q ((t0.trans t1).trans eq4.symm)).trans edge7))
        have t3 : x 1 = x 6 := (edge1.symm.trans ((congrArg q (t0.trans t2)).trans edge9))
        have t4 : x 1 = x 7 := (edge1.symm.trans ((congrArg q (t0.trans t3)).trans edge11))
        have t5 : x 5 = x 8 := (edge2.symm.trans ((congrArg p t2).trans edge8))
        have t6 : x 5 = x 9 := (edge2.symm.trans ((congrArg p t3).trans edge10))
        exact node0 t0.symm (hit.symm.trans t0.symm) (t1.symm.trans t0.symm) ((eq4.trans t1.symm).trans t0.symm) (t2.symm.trans t0.symm) (t3.symm.trans t0.symm) (t4.symm.trans t0.symm) ((t5.symm.trans t2.symm).trans t0.symm) ((t6.symm.trans t2.symm).trans t0.symm)
      · have t0 : x 0 = x 2 := (q.injective (edge1.trans (hit.trans edge5.symm)))
        have t1 : x 5 = x 7 := (edge2.symm.trans ((congrArg p hit).trans edge6))
        have t2 : x 2 = x 5 := (edge3.symm.trans ((congrArg q (hit.trans eq4.symm)).trans edge7))
        have t3 : x 1 = x 6 := (q.injective (edge3.trans ((t2.trans t1).trans edge11.symm)))
        have t4 : x 6 = x 8 := (edge4.symm.trans ((congrArg p t2).trans edge8))
        have t5 : x 7 = x 9 := (edge6.symm.trans ((congrArg p (hit.symm.trans t3)).trans edge10))
        exact node3 t0.symm hit.symm (eq4.trans hit.symm) (t2.symm.trans t0.symm) t3.symm ((t1.symm.trans t2.symm).trans t0.symm) (t4.symm.trans t3.symm) (((t5.symm.trans t1.symm).trans t2.symm).trans t0.symm)
      · have t0 : x 0 = x 4 := (q.injective (edge1.trans (hit.trans edge7.symm)))
        have t1 : x 5 = x 8 := (edge2.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 2 = x 6 := (edge3.symm.trans ((congrArg q hit).trans edge9))
        have t3 : x 2 = x 9 := (edge3.symm.trans ((congrArg q (hit.trans t1)).trans edge12))
        have t4 : x 3 = x 7 := (edge5.symm.trans ((congrArg q t2).trans edge11))
        exact node5 (eq4.symm.trans t0.symm) t0.symm hit.symm t2.symm ((t4.symm.trans eq4.symm).trans t0.symm) (t1.symm.trans hit.symm) t3.symm
      · have t0 : x 0 = x 5 := (q.injective (edge1.trans (hit.trans edge9.symm)))
        have t1 : x 5 = x 9 := (edge2.symm.trans ((congrArg p hit).trans edge10))
        have t2 : x 2 = x 7 := (edge3.symm.trans ((congrArg q hit).trans edge11))
        have t3 : x 4 = x 8 := (q.injective (edge7.trans (t1.trans edge12.symm)))
        exact node11 eq4 t0.symm hit.symm t2.symm (t3.symm.trans eq4) (t1.symm.trans t0.symm)
      · have t0 : x 1 = x 4 := (q.injective (edge3.trans (hit.trans edge7.symm)))
        have t1 : x 6 = x 8 := (edge4.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 3 = x 6 := (edge5.symm.trans ((congrArg q hit).trans edge9))
        have t3 : x 7 = x 9 := (edge6.symm.trans ((congrArg p t2).trans edge10))
        have t4 : x 5 = x 7 := (edge7.symm.trans ((congrArg q (eq4.trans t2)).trans edge11))
        have t5 : x 0 = x 2 := (p.injective (edge0.trans ((eq4.trans t2).trans edge4.symm)))
        exact node3 t5.symm (eq4.symm.trans t0.symm) t0.symm (hit.symm.trans t5.symm) ((t2.symm.trans eq4.symm).trans t0.symm) ((t4.symm.trans hit.symm).trans t5.symm) (((t1.symm.trans t2.symm).trans eq4.symm).trans t0.symm) (((t3.symm.trans t4.symm).trans hit.symm).trans t5.symm)
      · have t0 : x 0 = x 1 := (p.injective (edge0.trans ((eq4.trans hit).trans edge2.symm)))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q t0).trans edge3))
        have t2 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (t0.trans t1)).trans edge5))
        have t3 : x 1 = x 6 := (edge1.symm.trans ((congrArg q ((t0.trans t2).trans hit)).trans edge9))
        have t4 : x 1 = x 7 := (edge1.symm.trans ((congrArg q (t0.trans t3)).trans edge11))
        have t5 : x 5 = x 8 := (edge2.symm.trans ((congrArg p (t2.trans hit)).trans edge8))
        have t6 : x 5 = x 9 := (edge2.symm.trans ((congrArg p t3).trans edge10))
        exact node0 t0.symm (t1.symm.trans t0.symm) (t2.symm.trans t0.symm) ((eq4.trans t2.symm).trans t0.symm) ((hit.symm.trans t2.symm).trans t0.symm) (t3.symm.trans t0.symm) (t4.symm.trans t0.symm) (((t5.symm.trans hit.symm).trans t2.symm).trans t0.symm) (((t6.symm.trans hit.symm).trans t2.symm).trans t0.symm)
      · have t0 : x 0 = x 2 := (p.injective (edge0.trans ((eq4.trans hit).trans edge4.symm)))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q t0).trans edge5))
        have t2 : x 0 = x 5 := (q.injective (edge1.trans ((t1.trans hit).trans edge9.symm)))
        have t3 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t1).trans edge6))
        have t4 : x 5 = x 9 := (edge2.symm.trans ((congrArg p (t1.trans hit)).trans edge10))
        have t5 : x 1 = x 8 := (q.injective (edge3.trans (((t0.symm.trans t2).trans t4).trans edge12.symm)))
        exact node3 t0.symm t1.symm (eq4.trans t1.symm) t2.symm (hit.symm.trans t1.symm) (t3.symm.trans t2.symm) t5.symm (t4.symm.trans t2.symm)
      · have t0 : x 1 = x 2 := (p.injective (edge2.trans (hit.trans edge4.symm)))
        have t1 : x 2 = x 3 := (edge3.symm.trans ((congrArg q t0).trans edge5))
        have t2 : x 2 = x 5 := (edge3.symm.trans ((congrArg q ((t0.trans t1).trans eq4.symm)).trans edge7))
        have t3 : x 2 = x 7 := (edge3.symm.trans ((congrArg q ((t0.trans t2).trans hit)).trans edge11))
        have t4 : x 6 = x 8 := (edge4.symm.trans ((congrArg p t2).trans edge8))
        have t5 : x 6 = x 9 := (edge4.symm.trans ((congrArg p (t2.trans hit)).trans edge10))
        have t6 : x 0 = x 1 := (p.injective (edge0.trans (((eq4.trans t1.symm).trans t2).trans edge2.symm)))
        exact node0 t6.symm (t0.symm.trans t6.symm) ((t1.symm.trans t0.symm).trans t6.symm) (((eq4.trans t1.symm).trans t0.symm).trans t6.symm) ((t2.symm.trans t0.symm).trans t6.symm) (((hit.symm.trans t2.symm).trans t0.symm).trans t6.symm) ((t3.symm.trans t0.symm).trans t6.symm) ((((t4.symm.trans hit.symm).trans t2.symm).trans t0.symm).trans t6.symm) ((((t5.symm.trans hit.symm).trans t2.symm).trans t0.symm).trans t6.symm)
  have node23 : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=16) (by decide) ![(false,0), (true,1), (false,1), (true,2), (false,2), (true,3), (false,3), (true,7), (false,6), (true,9), (false,8), (true,8), (false,5), (true,5), (false,4), (true,4)]
      [(0,1), (1,1), (1,2), (2,2), (2,3), (3,3), (3,7), (6,7), (6,9), (8,9), (8,8), (5,8), (5,5), (4,5), (4,4), (0,4)] [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,8), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (1,8), (1,9), (2,3), (2,4), (2,5), (2,6), (2,7), (2,8), (2,9), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), (4,5), (4,6), (4,7), (4,8), (4,9), (5,6), (5,7), (5,8), (5,9), (6,8), (7,8), (7,9), (8,9)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
      · exact idAdj _
      · have e : q (x 1) = x 2 := edge3
        exact e ▸ qAdj (x 1)
      · exact idAdj _
      · have e : q (x 2) = x 3 := edge5
        exact e ▸ qAdj (x 2)
      · exact idAdj _
      · have e : p (x 3) = x 7 := edge6
        exact e ▸ pAdj (x 3)
      · have e : q (x 6) = x 7 := edge11
        exact e ▸ qAdj (x 6)
      · have e : p (x 6) = x 9 := edge10
        exact e ▸ pAdj (x 6)
      · have e : q (x 8) = x 9 := edge12
        exact e ▸ qAdj (x 8)
      · exact idAdj _
      · have e : p (x 5) = x 8 := edge8
        exact e ▸ pAdj (x 5)
      · exact idAdj _
      · have e : q (x 4) = x 5 := edge7
        exact e ▸ qAdj (x 4)
      · exact idAdj _
      · have e : p (x 0) = x 4 := edge0
        exact e ▸ pAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q hit).trans edge3))
        have t2 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (hit.trans t1)).trans edge5))
        have t3 : x 5 = x 6 := (edge2.symm.trans ((congrArg p t1).trans edge4))
        have t4 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t2).trans edge6))
        have t5 : x 8 = x 9 := (edge8.symm.trans ((congrArg p t3).trans edge10))
        exact node4 hit.symm (t1.symm.trans hit.symm) (t2.symm.trans hit.symm) t0.symm (t3.symm.trans t0.symm) (t4.symm.trans t0.symm) t5.symm
      · have t0 : x 4 = x 6 := (edge0.symm.trans ((congrArg p hit).trans edge4))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q hit).trans edge5))
        have t2 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t1).trans edge6))
        exact node14 hit.symm t1.symm t0.symm t2.symm
      · have t0 : x 4 = x 7 := (edge0.symm.trans ((congrArg p hit).trans edge6))
        exact node17 hit.symm t0.symm
      · have t0 : x 1 = x 5 := (edge1.symm.trans ((congrArg q hit).trans edge7))
        have t1 : x 5 = x 8 := (edge2.symm.trans ((congrArg p t0).trans edge8))
        have t2 : x 2 = x 6 := (edge3.symm.trans ((congrArg q t0).trans edge9))
        have t3 : x 2 = x 9 := (edge3.symm.trans ((congrArg q (t0.trans t1)).trans edge12))
        have t4 : x 3 = x 7 := (edge5.symm.trans ((congrArg q t2).trans edge11))
        exact node10 hit.symm t0.symm t2.symm t4.symm (t1.symm.trans t0.symm) t3.symm
      · have t0 : x 4 = x 8 := (edge0.symm.trans ((congrArg p hit).trans edge8))
        have t1 : x 1 = x 6 := (edge1.symm.trans ((congrArg q hit).trans edge9))
        have t2 : x 5 = x 9 := (edge2.symm.trans ((congrArg p t1).trans edge10))
        have t3 : x 2 = x 7 := (edge3.symm.trans ((congrArg q t1).trans edge11))
        exact node12 hit.symm t1.symm t3.symm t0.symm (t2.symm.trans hit.symm)
      · have t0 : x 4 = x 9 := (edge0.symm.trans ((congrArg p hit).trans edge10))
        have t1 : x 1 = x 7 := (edge1.symm.trans ((congrArg q hit).trans edge11))
        exact node15 hit.symm t1.symm t0.symm
      · have t0 : x 1 = x 9 := (edge1.symm.trans ((congrArg q hit).trans edge12))
        exact node18 hit.symm t0.symm
      · have t0 : x 0 = x 1 := (q.injective (edge1.trans (hit.trans edge3.symm)))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (t0.trans hit)).trans edge5))
        have t2 : x 5 = x 6 := (edge2.symm.trans ((congrArg p hit).trans edge4))
        have t3 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t1).trans edge6))
        have t4 : x 4 = x 5 := (q.injective (edge7.trans (t2.trans edge9.symm)))
        have t5 : x 8 = x 9 := (edge8.symm.trans ((congrArg p t2).trans edge10))
        exact node4 t0.symm (hit.symm.trans t0.symm) (t1.symm.trans t0.symm) t4.symm (t2.symm.trans t4.symm) (t3.symm.trans t4.symm) t5.symm
      · have t0 : x 0 = x 2 := (q.injective (edge1.trans (hit.trans edge5.symm)))
        have t1 : x 5 = x 7 := (edge2.symm.trans ((congrArg p hit).trans edge6))
        have t2 : x 4 = x 6 := (q.injective (edge7.trans (t1.trans edge11.symm)))
        exact node14 t0.symm hit.symm t2.symm t1.symm
      · have t0 : x 2 = x 5 := (edge3.symm.trans ((congrArg q hit).trans edge7))
        have t1 : x 6 = x 8 := (edge4.symm.trans ((congrArg p t0).trans edge8))
        have t2 : x 3 = x 6 := (edge5.symm.trans ((congrArg q t0).trans edge9))
        have t3 : x 7 = x 9 := (edge6.symm.trans ((congrArg p t2).trans edge10))
        exact node13 hit.symm t0.symm t2.symm (t1.symm.trans t2.symm) t3.symm
      · have t0 : x 0 = x 4 := (q.injective (edge1.trans (hit.trans edge7.symm)))
        have t1 : x 5 = x 8 := (edge2.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 2 = x 6 := (edge3.symm.trans ((congrArg q hit).trans edge9))
        have t3 : x 2 = x 9 := (edge3.symm.trans ((congrArg q (hit.trans t1)).trans edge12))
        have t4 : x 3 = x 7 := (edge5.symm.trans ((congrArg q t2).trans edge11))
        exact node10 t0.symm hit.symm t2.symm t4.symm (t1.symm.trans hit.symm) t3.symm
      · have t0 : x 0 = x 5 := (q.injective (edge1.trans (hit.trans edge9.symm)))
        have t1 : x 5 = x 9 := (edge2.symm.trans ((congrArg p hit).trans edge10))
        have t2 : x 2 = x 7 := (edge3.symm.trans ((congrArg q hit).trans edge11))
        have t3 : x 4 = x 8 := (q.injective (edge7.trans (t1.trans edge12.symm)))
        exact node12 t0.symm hit.symm t2.symm t3.symm (t1.symm.trans t0.symm)
      · have t0 : x 0 = x 6 := (q.injective (edge1.trans (hit.trans edge11.symm)))
        have t1 : x 4 = x 9 := (edge0.symm.trans ((congrArg p t0).trans edge10))
        exact node15 t0.symm hit.symm t1.symm
      · have t0 : x 2 = x 9 := (edge3.symm.trans ((congrArg q hit).trans edge12))
        exact node19 hit.symm t0.symm
      · have t0 : x 0 = x 8 := (q.injective (edge1.trans (hit.trans edge12.symm)))
        exact node18 t0.symm hit.symm
      · have t0 : x 1 = x 2 := (q.injective (edge3.trans (hit.trans edge5.symm)))
        have t1 : x 6 = x 7 := (edge4.symm.trans ((congrArg p hit).trans edge6))
        have t2 : x 5 = x 6 := (q.injective (edge9.trans (t1.trans edge11.symm)))
        have t3 : x 0 = x 1 := (q.injective (edge1.trans (t0.trans edge3.symm)))
        have t4 : x 4 = x 5 := (q.injective (edge7.trans (t2.trans edge9.symm)))
        have t5 : x 8 = x 9 := (edge8.symm.trans ((congrArg p t2).trans edge10))
        exact node4 t3.symm (t0.symm.trans t3.symm) ((hit.symm.trans t0.symm).trans t3.symm) t4.symm (t2.symm.trans t4.symm) ((t1.symm.trans t2.symm).trans t4.symm) t5.symm
      · have t0 : x 3 = x 5 := (edge5.symm.trans ((congrArg q hit).trans edge7))
        have t1 : x 7 = x 8 := (edge6.symm.trans ((congrArg p t0).trans edge8))
        exact node16 hit.symm t0.symm t1.symm
      · have t0 : x 1 = x 4 := (q.injective (edge3.trans (hit.trans edge7.symm)))
        have t1 : x 6 = x 8 := (edge4.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 3 = x 6 := (edge5.symm.trans ((congrArg q hit).trans edge9))
        have t3 : x 7 = x 9 := (edge6.symm.trans ((congrArg p t2).trans edge10))
        exact node13 t0.symm hit.symm t2.symm (t1.symm.trans t2.symm) t3.symm
      · have t0 : x 1 = x 5 := (q.injective (edge3.trans (hit.trans edge9.symm)))
        have t1 : x 6 = x 9 := (edge4.symm.trans ((congrArg p hit).trans edge10))
        have t2 : x 3 = x 7 := (edge5.symm.trans ((congrArg q hit).trans edge11))
        have t3 : x 5 = x 8 := (q.injective (edge9.trans (t1.trans edge12.symm)))
        have t4 : x 0 = x 4 := (q.injective (edge1.trans (t0.trans edge7.symm)))
        exact node10 t4.symm t0.symm hit.symm t2.symm (t3.symm.trans t0.symm) (t1.symm.trans hit.symm)
      · have t0 : x 1 = x 6 := (q.injective (edge3.trans (hit.trans edge11.symm)))
        have t1 : x 0 = x 5 := (q.injective (edge1.trans (t0.trans edge9.symm)))
        have t2 : x 5 = x 9 := (edge2.symm.trans ((congrArg p t0).trans edge10))
        have t3 : x 4 = x 8 := (q.injective (edge7.trans (t2.trans edge12.symm)))
        exact node12 t1.symm t0.symm hit.symm t3.symm (t2.symm.trans t1.symm)
      · have t0 : x 3 = x 9 := (edge5.symm.trans ((congrArg q hit).trans edge12))
        exact node20 hit.symm t0.symm
      · have t0 : x 1 = x 8 := (q.injective (edge3.trans (hit.trans edge12.symm)))
        exact node19 t0.symm hit.symm
      · exact node22 hit.symm
      · have t0 : x 2 = x 4 := (q.injective (edge5.trans (hit.trans edge7.symm)))
        have t1 : x 7 = x 8 := (edge6.symm.trans ((congrArg p hit).trans edge8))
        exact node16 t0.symm hit.symm t1.symm
      · have t0 : x 2 = x 5 := (q.injective (edge5.trans (hit.trans edge9.symm)))
        have t1 : x 7 = x 9 := (edge6.symm.trans ((congrArg p hit).trans edge10))
        have t2 : x 6 = x 8 := (q.injective (edge11.trans (t1.trans edge12.symm)))
        have t3 : x 1 = x 4 := (q.injective (edge3.trans (t0.trans edge7.symm)))
        exact node13 t3.symm t0.symm hit.symm (t2.symm.trans hit.symm) t1.symm
      · have t0 : x 2 = x 6 := (q.injective (edge5.trans (hit.trans edge11.symm)))
        have t1 : x 1 = x 5 := (q.injective (edge3.trans (t0.trans edge9.symm)))
        have t2 : x 6 = x 9 := (edge4.symm.trans ((congrArg p t0).trans edge10))
        have t3 : x 5 = x 8 := (q.injective (edge9.trans (t2.trans edge12.symm)))
        have t4 : x 0 = x 4 := (q.injective (edge1.trans (t1.trans edge7.symm)))
        exact node10 t4.symm t1.symm t0.symm hit.symm (t3.symm.trans t1.symm) (t2.symm.trans t0.symm)
      · exact node21 hit.symm
      · have t0 : x 2 = x 8 := (q.injective (edge5.trans (hit.trans edge12.symm)))
        exact node20 t0.symm hit.symm
      · have t0 : x 0 = x 1 := (p.injective (edge0.trans (hit.trans edge2.symm)))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q t0).trans edge3))
        have t2 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (t0.trans t1)).trans edge5))
        have t3 : x 5 = x 6 := (edge2.symm.trans ((congrArg p t1).trans edge4))
        have t4 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t2).trans edge6))
        have t5 : x 8 = x 9 := (edge8.symm.trans ((congrArg p t3).trans edge10))
        exact node4 t0.symm (t1.symm.trans t0.symm) (t2.symm.trans t0.symm) hit.symm (t3.symm.trans hit.symm) (t4.symm.trans hit.symm) t5.symm
      · have t0 : x 0 = x 2 := (p.injective (edge0.trans (hit.trans edge4.symm)))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q t0).trans edge5))
        have t2 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t1).trans edge6))
        exact node14 t0.symm t1.symm hit.symm t2.symm
      · have t0 : x 0 = x 3 := (p.injective (edge0.trans (hit.trans edge6.symm)))
        exact node17 t0.symm hit.symm
      · have t0 : x 0 = x 5 := (p.injective (edge0.trans (hit.trans edge8.symm)))
        have t1 : x 1 = x 6 := (edge1.symm.trans ((congrArg q t0).trans edge9))
        have t2 : x 5 = x 9 := (edge2.symm.trans ((congrArg p t1).trans edge10))
        have t3 : x 2 = x 7 := (edge3.symm.trans ((congrArg q t1).trans edge11))
        exact node12 t0.symm t1.symm t3.symm hit.symm (t2.symm.trans t0.symm)
      · have t0 : x 0 = x 6 := (p.injective (edge0.trans (hit.trans edge10.symm)))
        have t1 : x 1 = x 7 := (edge1.symm.trans ((congrArg q t0).trans edge11))
        exact node15 t0.symm t1.symm hit.symm
      · have t0 : x 1 = x 2 := (p.injective (edge2.trans (hit.trans edge4.symm)))
        have t1 : x 2 = x 3 := (edge3.symm.trans ((congrArg q t0).trans edge5))
        have t2 : x 6 = x 7 := (edge4.symm.trans ((congrArg p t1).trans edge6))
        have t3 : x 4 = x 5 := (q.injective (edge7.trans (hit.trans edge9.symm)))
        have t4 : x 8 = x 9 := (edge8.symm.trans ((congrArg p hit).trans edge10))
        have t5 : x 0 = x 1 := (p.injective (edge0.trans (t3.trans edge2.symm)))
        exact node4 t5.symm (t0.symm.trans t5.symm) ((t1.symm.trans t0.symm).trans t5.symm) t3.symm (hit.symm.trans t3.symm) ((t2.symm.trans hit.symm).trans t3.symm) t4.symm
      · have t0 : x 1 = x 3 := (p.injective (edge2.trans (hit.trans edge6.symm)))
        have t1 : x 4 = x 6 := (q.injective (edge7.trans (hit.trans edge11.symm)))
        have t2 : x 0 = x 2 := (p.injective (edge0.trans (t1.trans edge4.symm)))
        exact node14 t2.symm t0.symm t1.symm hit.symm
      · have t0 : x 1 = x 5 := (p.injective (edge2.trans (hit.trans edge8.symm)))
        have t1 : x 2 = x 6 := (edge3.symm.trans ((congrArg q t0).trans edge9))
        have t2 : x 2 = x 9 := (edge3.symm.trans ((congrArg q (t0.trans hit)).trans edge12))
        have t3 : x 3 = x 7 := (edge5.symm.trans ((congrArg q t1).trans edge11))
        have t4 : x 0 = x 4 := (q.injective (edge1.trans (t0.trans edge7.symm)))
        exact node10 t4.symm t0.symm t1.symm t3.symm (hit.symm.trans t0.symm) t2.symm
      · have t0 : x 1 = x 6 := (p.injective (edge2.trans (hit.trans edge10.symm)))
        have t1 : x 2 = x 7 := (edge3.symm.trans ((congrArg q t0).trans edge11))
        have t2 : x 4 = x 8 := (q.injective (edge7.trans (hit.trans edge12.symm)))
        have t3 : x 0 = x 5 := (p.injective (edge0.trans (t2.trans edge8.symm)))
        exact node12 t3.symm t0.symm t1.symm t2.symm (hit.symm.trans t3.symm)
      · have t0 : x 2 = x 5 := (p.injective (edge4.trans (hit.trans edge8.symm)))
        have t1 : x 3 = x 6 := (edge5.symm.trans ((congrArg q t0).trans edge9))
        have t2 : x 7 = x 9 := (edge6.symm.trans ((congrArg p t1).trans edge10))
        have t3 : x 1 = x 4 := (q.injective (edge3.trans (t0.trans edge7.symm)))
        exact node13 t3.symm t0.symm t1.symm (hit.symm.trans t1.symm) t2.symm
      · have t0 : x 3 = x 5 := (p.injective (edge6.trans (hit.trans edge8.symm)))
        have t1 : x 2 = x 4 := (q.injective (edge5.trans (t0.trans edge7.symm)))
        exact node16 t1.symm t0.symm hit.symm
      · have t0 : x 3 = x 6 := (p.injective (edge6.trans (hit.trans edge10.symm)))
        have t1 : x 6 = x 8 := (q.injective (edge11.trans (hit.trans edge12.symm)))
        have t2 : x 2 = x 5 := (p.injective (edge4.trans (t1.trans edge8.symm)))
        have t3 : x 1 = x 4 := (q.injective (edge3.trans (t2.trans edge7.symm)))
        exact node13 t3.symm t2.symm t0.symm (t1.symm.trans t0.symm) hit.symm
      · have t0 : x 5 = x 6 := (p.injective (edge8.trans (hit.trans edge10.symm)))
        have t1 : x 6 = x 7 := (edge9.symm.trans ((congrArg q t0).trans edge11))
        have t2 : x 1 = x 2 := (p.injective (edge2.trans (t0.trans edge4.symm)))
        have t3 : x 1 = x 3 := (p.injective (edge2.trans ((t0.trans t1).trans edge6.symm)))
        have t4 : x 4 = x 5 := (q.injective (edge7.trans (t0.trans edge9.symm)))
        have t5 : x 0 = x 1 := (p.injective (edge0.trans (t4.trans edge2.symm)))
        exact node4 t5.symm (t2.symm.trans t5.symm) (t3.symm.trans t5.symm) t4.symm (t0.symm.trans t4.symm) ((t1.symm.trans t0.symm).trans t4.symm) hit.symm
  exact node23

/-- Exchanging sides reverses every matching edge. -/

theorem near0 {X : Type*} (G : SimpleGraph (Bool × X)) (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idAdj : ∀ u, G.Adj (false,u) (true,u))
    (pAdj : ∀ u, G.Adj (false,u) (true,p u))
    (qAdj : ∀ u, G.Adj (false,u) (true,q u)) (z : X)
    (center : p (q (z)) = q (p (z)))
    (c1 : p (q (p z)) = q (p (p z)))
    (c2 : p (q (q.symm z)) = q (p (q.symm z)))
    (c3 : p (q (q z)) = q (p (q z)))
    : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  let labels : (Fin 10) → X := ![q.symm z, z, q (z), q (q z), p (q.symm z), p (z), p (q (z)), p (q (q z)), p (p z), p (q (p z))]
  apply shape0 G p q sep idAdj pAdj qAdj labels
  · rfl
  · exact q.apply_symm_apply z
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact c2.symm.trans (congrArg p (q.apply_symm_apply z))
  · rfl
  · exact center.symm
  · exact congrArg p center
  · exact c3.symm
  · exact c1.symm

end LocalCommutation

namespace HaarShort
open SimpleGraph
variable {A : Type*} [AddCommGroup A]

/-- An abelian Haar graph with three distinct shifts contains a 4-, 8-, or
16-cycle. Translate the right part to normalize one of the shifts to zero. -/
theorem haar_short_cycle (G : SimpleGraph (Bool × A)) (u v : A)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (h0 : ∀ x, G.Adj (false, x) (true, x))
    (h1 : ∀ x, G.Adj (false, x) (true, x + u))
    (h2 : ∀ x, G.Adj (false, x) (true, x + v)) :
    SimpleGraph.cycleGraph 4 ⊑ G ∨ SimpleGraph.cycleGraph 8 ⊑ G ∨ SimpleGraph.cycleGraph 16 ⊑ G := by
  let p : Equiv.Perm A := Equiv.addRight u
  let q : Equiv.Perm A := Equiv.addRight v
  have sep (x : A) : p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x := by simpa [p,q] using And.intro hu (And.intro hv huv)
  have comm (x : A) : p (q x) = q (p x) := by change x+v+u=x+u+v; abel
  exact LocalCommutation.near0 G p q sep h0 h1 h2 0 (comm _) (comm _) (comm _) (comm _)

end HaarShort

namespace Erdos64TwoOrbits
open SimpleGraph Function

theorem short_map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : G ⊑ H) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) → (cycleGraph 4 ⊑ H ∨ cycleGraph 8 ⊑ H ∨ cycleGraph 16 ⊑ H) := by
  rintro (c|c|c)
  · exact Or.inl (c.trans h)
  · exact Or.inr (Or.inl (c.trans h))
  · exact Or.inr (Or.inr (c.trans h))

variable {A : Type*} [AddCommGroup A]
variable {V : Type*} {G : SimpleGraph V}

/-- Two different, nonopposite internal steps and the matching between the
rows trace the eight corners of a rectangle. Coincident steps give a square. -/
theorem matched_steps (l r : A ↪ V) (apart : ∀ x y, l x ≠ r y)
    (s t : A) (hs : s ≠ 0) (ht : t ≠ 0)
    (left : ∀ x, G.Adj (l x) (l (x+s))) (right : ∀ x, G.Adj (r x) (r (x+t)))
    (rung : ∀ x, G.Adj (l x) (r x)) : cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G := by
  have ls : G.Adj (l 0) (l s) := by simpa using left 0
  have rt : G.Adj (r 0) (r t) := by simpa using right 0
  have sq (edge : G.Adj (r 0) (r s)) : cycleGraph 4 ⊑ G :=
    square_of_four ls (rung _) edge.symm (rung _).symm (apart _ _) (apart _ _)
  by_cases eq : s=t
  · exact Or.inl (sq (eq ▸ rt))
  by_cases cancel : s+t=0
  · exact Or.inl (sq (by simpa [cancel] using (right s).symm))
  have ss : s ≠ s+t := by simpa using ht
  have tt : t ≠ s+t := by simpa using hs
  have reduced (x y : A) : r x ≠ l y := (apart y x).symm
  apply Or.inr
  let seq := [l 0,l s,r s,r (s+t),l (s+t),l t,r t,r 0]
  have nd : seq.Nodup := by
    simp [seq,apart,reduced,hs,hs.symm,ht,ht.symm,eq,cancel,Ne.symm cancel,
      ss,tt.symm]
  have back : G.Adj (l (s+t)) (l t) := by simpa [add_comm] using (left t).symm
  have chain : seq.IsChain G.Adj := by
    simp [seq,ls,rung, right s,(rung (s+t)).symm,back,rt.symm]
  exact cycle_of_ring G seq (by simp [seq]) nd chain (by simpa [seq] using (rung 0).symm)

/-- A layer with three distinct internal neighbours contains a square. -/
theorem internal_square (f : A ↪ V) (a b c : A) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (edge : ∀ x u, u=a ∨ u=b ∨ u=c → G.Adj (f x) (f (x+u))) : cycleGraph 4 ⊑ G := by
  have make (u : A) (au : a≠u) (sum : a+u≠0) (mem : u=b ∨ u=c) : cycleGraph 4 ⊑ G := by
    have h1 : G.Adj (f 0) (f a) := by simpa using edge 0 a (Or.inl rfl)
    have h2 := edge a u (Or.inr mem)
    have h3 : G.Adj (f (a+u)) (f u) := by simpa [add_comm] using (edge u a (Or.inl rfl)).symm
    have h4 : G.Adj (f u) (f 0) := by simpa using (edge 0 u (Or.inr mem)).symm
    exact square_of_four h1 h2 h3 h4 (fun h => sum (f.injective h).symm)
      (fun h => au (f.injective h))
  by_cases zero : a+b=0
  · exact make c ac (fun h => bc (add_left_cancel (zero.trans h.symm))) (Or.inr rfl)
  · exact make b ab zero (Or.inl rfl)

variable (K : SimpleGraph (Bool × A))

theorem three_cross (inv : (∀ (d : A) {i j : Bool} {x y : A}, K.Adj (i,x) (j,y) → K.Adj (i,d+x) (j,d+y))) (b : Bool) (c u v : A)
    (cu : c≠u) (cv : c≠v) (uv : u≠v) (h0 : K.Adj (b,0) (!b,c))
    (h1 : K.Adj (b,0) (!b,u)) (h2 : K.Adj (b,0) (!b,v)) : (cycleGraph 4 ⊑ K ∨ cycleGraph 8 ⊑ K ∨ cycleGraph 16 ⊑ K) := by
  let e : (Bool × A) ≃ (Bool × A) :=
    { toFun := fun | (false,x) => (b,x) | (true,x) => (!b,x+c)
      invFun := fun (i,x) => if i=b then (false,x) else (true,x-c)
      left_inv := by rintro ⟨i,x⟩; cases i <;> cases b <;> simp
      right_inv := by rintro ⟨i,x⟩; cases i <;> cases b <;> simp }
  let J := K.comap e
  have sub : J ⊑ K := isContained_iff_exists_le_comap.mpr ⟨e.toEmbedding,le_rfl⟩
  apply short_map sub
  apply HaarShort.haar_short_cycle J (u-c) (v-c)
      (sub_ne_zero.mpr cu.symm) (sub_ne_zero.mpr cv.symm) (fun h => uv (sub_left_inj.mp h))
  · intro x; simpa [J,e] using inv x h0
  · intro x; simpa [J,e,add_assoc] using inv x h1
  · intro x; simpa [J,e,add_assoc] using inv x h2

variable [Fintype A] [DecidableRel K.Adj]

private theorem neighbours_in_row (degree : ∀ x, 3 ≤ K.degree x) (b i : Bool)
    (side : ∀ y, K.Adj (b,0) y → y.1=i) :
    ∃ a c d : A, a≠c ∧ a≠d ∧ c≠d ∧ K.Adj (b,0) (i,a) ∧
      K.Adj (b,0) (i,c) ∧ K.Adj (b,0) (i,d) := by
  obtain ⟨⟨j,a⟩,⟨k,c⟩,⟨m,d⟩,ha,hc,hd,ac,ad,cd⟩ :=
    Finset.two_lt_card_iff.mp (degree (b,0))
  rw [mem_neighborFinset] at ha hc hd
  obtain rfl : j=i := side _ ha
  obtain rfl : k=j := side _ hc
  obtain rfl : m=k := side _ hd
  exact ⟨a,c,d,fun h => ac (h ▸ rfl),fun h => ad (h ▸ rfl),fun h => cd (h ▸ rfl),ha,hc,hd⟩

/-- Every finite graph of minimum degree three invariant under simultaneous
translation of two copies of an abelian group has a 4-, 8-, or 16-cycle. -/
theorem two_regular_orbits (inv : (∀ (d : A) {i j : Bool} {x y : A}, K.Adj (i,x) (j,y) → K.Adj (i,d+x) (j,d+y))) (degree : ∀ x, 3 ≤ K.degree x) : (cycleGraph 4 ⊑ K ∨ cycleGraph 8 ⊑ K ∨ cycleGraph 16 ⊑ K) := by
  classical
  let layer (b : Bool) : A ↪ Bool × A := ⟨fun x => (b,x),fun _ _ e => congrArg Prod.snd e⟩
  by_cases across : ∃ c, K.Adj (false,0) (true,c)
  · obtain ⟨c,hc⟩ := across
    by_cases inside : ∀ b : Bool, ∃ s, K.Adj (b,0) (b,s)
    · obtain ⟨s,hs⟩ := inside false
      obtain ⟨t,ht⟩ := inside true
      let r : A ↪ Bool × A := (Equiv.addRight c).toEmbedding.trans (layer true)
      have h := matched_steps (G:=K) (layer false) r (fun _ _ h => Bool.false_ne_true (congrArg Prod.fst h))
        s t (fun h => hs.ne (h ▸ rfl)) (fun h => ht.ne (h ▸ rfl))
        (fun x => by change K.Adj (false,x) (false,x+s); simpa using inv x hs)
        (fun x => by change K.Adj (true,x+c) (true,x+t+c); simpa [add_assoc,add_comm c t] using inv (x+c) ht)
        (fun x => by change K.Adj (false,x) (true,x+c); simpa using inv x hc)
      exact h.imp_right Or.inl
    · push Not at inside
      obtain ⟨b,hb⟩ := inside
      obtain ⟨c,u,v,cu,cv,uv,e,f,g⟩ := neighbours_in_row K degree b (!b) (by
        rintro ⟨i,x⟩ adj
        cases b <;> cases i <;> simp_all)
      exact three_cross K inv b c u v cu cv uv e f g
  · push Not at across
    obtain ⟨a,b,c,ab,ac,bc,e,f,g⟩ := neighbours_in_row K degree false false (by
      rintro ⟨i,x⟩ adj; cases i <;> simp_all)
    apply Or.inl (internal_square (layer false) a b c ab ac bc ?_)
    rintro x u (rfl|rfl|rfl)
    · change K.Adj (false,x) (false,x+u); simpa using inv x e
    · change K.Adj (false,x) (false,x+u); simpa using inv x f
    · change K.Adj (false,x) (false,x+u); simpa using inv x g

end Erdos64TwoOrbits


namespace Erdos64TwicePrime

open Function SimpleGraph MulAction Erdos64TwoOrbits

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- If a nontrivial abelian group acts regularly on just one orbit and fixes
all remaining vertices, minimum degree three already forces a square. -/
theorem one_moving_orbit {A : Type*} [AddCommGroup A] [Nontrivial A]
    (f : A ↪ V) (act : A → V → V)
    (shift : ∀ a x, act a (f x)=f (a+x))
    (auto : ∀ a {u v}, G.Adj u v → G.Adj (act a u) (act a v))
    (fixed : ∀ z, z ∉ Set.range f → ∀ a, act a z=z)
    (degree : 3 ≤ G.degree (f 0)) : cycleGraph 4 ⊑ G := by
  classical
  obtain ⟨u,v,w,hu,hv,hw,uv,uw,vw⟩ := Finset.two_lt_card_iff.mp degree
  rw [mem_neighborFinset] at hu hv hw
  have translate {y : V} (h : y ∉ Set.range f) (e : G.Adj (f 0) y) (x : A) :
      G.Adj (f x) y := by simpa [shift,fixed _ h] using auto x e
  by_cases closed : ∀ z, G.Adj (f 0) z → z ∈ Set.range f
  · obtain ⟨a,rfl⟩ := closed _ hu
    obtain ⟨b,rfl⟩ := closed _ hv
    obtain ⟨c,rfl⟩ := closed _ hw
    apply internal_square f a b c (fun h => uv (congrArg f h)) (fun h => uw (congrArg f h))
      (fun h => vw (congrArg f h))
    rintro x d (rfl|rfl|rfl)
    · simpa [shift] using auto x hu
    · simpa [shift] using auto x hv
    · simpa [shift] using auto x hw
  · push Not at closed
    obtain ⟨z,hz,out⟩ := closed
    obtain ⟨a,ha⟩ := exists_ne (0 : A)
    have distinct : f 0 ≠ f a := fun h => ha (f.injective h).symm
    have opposite {i j : V} (ei : G.Adj (f 0) i) (ej : G.Adj (f 0) j) (ij : i≠j)
        (same : i ∈ Set.range f ↔ j ∈ Set.range f) : cycleGraph 4 ⊑ G := by
      by_cases mem : i ∈ Set.range f
      · obtain ⟨a,eq⟩ := mem
        obtain ⟨b,ejb⟩ := same.mp ⟨a,eq⟩
        exact square_of_four ei (eq ▸ translate out hz a) (ejb ▸ (translate out hz b).symm)
          ej.symm (fun h => out ⟨0,h⟩) ij
      · have other := mt same.mpr mem
        exact square_of_four ei (translate mem ei a).symm (translate other ej a) ej.symm distinct ij
    by_contra no
    have h1 := fun h => no (opposite hu hv uv h)
    have h2 := fun h => no (opposite hu hw uw h)
    have h3 := fun h => no (opposite hv hw vw h)
    tauto

omit [Fintype V] in
theorem prime_orbit {B : Type*} [Group B] [MulAction B V] [(Fact (Nat.card B).Prime)]
    (x : V) (moves : ∃ b : B, b • x ≠ x) : Injective (fun b : B => b • x) := by
  obtain ⟨b,hb⟩ := moves
  have bot : stabilizer B x = ⊥ := (stabilizer B x).eq_bot_or_eq_top_of_prime_card.resolve_right
    (fun h => hb (mem_stabilizer_iff.mp (h ▸ Subgroup.mem_top b)))
  intro u v h
  change u • x=v • x at h
  have mem : u⁻¹*v ∈ stabilizer B x := by rw [mem_stabilizer_iff,mul_smul,←h,inv_smul_smul]
  have id : u⁻¹*v=1 := Subgroup.mem_bot.mp (bot ▸ mem)
  exact inv_mul_eq_one.mp id

/-- A prime-order group acting nontrivially by automorphisms on 2p vertices
has one moving orbit and fixed points, or a pair of regular orbits. -/
theorem prime_action {B : Type*} [CommGroup B] [Fintype B] [MulAction B V]
    (prime : (Nat.card B).Prime) (size : Fintype.card V=2*Fintype.card B)
    (moved : ∃ (x : V) (b : B), b • x≠x)
    (auto : ∀ (b : B) {u v : V}, G.Adj u v → G.Adj (b • u) (b • v))
    (degree : ∀ v, 3 ≤ G.degree v) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  classical
  let : Fact (Nat.card B).Prime := ⟨prime⟩
  let : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp prime.one_lt
  obtain ⟨x,b,hb⟩ := moved
  let f : Additive B ↪ V := ⟨fun a => a.toMul • x,(prime_orbit (B:=B) x ⟨b,hb⟩).comp Additive.toMul.injective⟩
  have shift (d a : Additive B) : d.toMul • f a=f (d+a) := (mul_smul _ _ _).symm
  by_cases single : ∀ y, y ∉ Set.range f → ∀ b : B, b • y=y
  · exact Or.inl (one_moving_orbit G f (fun a z => a.toMul • z) shift
      (fun a _ _ e => auto a.toMul e) (fun z hz a => single z hz a.toMul) (degree _))
  push Not at single
  obtain ⟨y,out,c,hc⟩ := single
  let g : Additive B ↪ V := ⟨fun a => a.toMul • y,(prime_orbit (B:=B) y ⟨c,hc⟩).comp Additive.toMul.injective⟩
  have apart (a d : Additive B) : f a ≠ g d := by
    intro eq
    apply out
    refine ⟨Additive.ofMul (d.toMul⁻¹ * a.toMul),?_⟩
    change (d.toMul⁻¹ * a.toMul) • x=y
    rw [mul_smul]
    exact (congrArg (fun z => d.toMul⁻¹ • z) eq).trans (inv_smul_smul _ _)
  let pair : Bool × Additive B → V
    | (false,a) => f a
    | (true,a) => g a
  have inj : Injective pair := by
    rintro ⟨i,a⟩ ⟨j,t⟩ h
    cases i <;> cases j
    · exact Prod.ext rfl (f.injective h)
    · exact (apart _ _ h).elim
    · exact (apart _ _ h.symm).elim
    · exact Prod.ext rfl (g.injective h)
  let e := Equiv.ofBijective pair ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨inj,by simpa using size.symm⟩)
  let K := G.comap e
  let iso : K ≃g G := SimpleGraph.Iso.comap e G
  have coord (i : Bool) (d a : Additive B) : e (i,d+a)=d.toMul • e (i,a) := by
    cases i <;> exact mul_smul _ _ _
  have inv : (∀ (d : Additive B) {i j : Bool} {x y : Additive B}, K.Adj (i,x) (j,y) → K.Adj (i,d+x) (j,d+y)) := by
    intro d i j a t h
    change G.Adj (e (i,d+a)) (e (j,d+t))
    rw [coord,coord]
    exact auto _ h
  have deg (z) : 3 ≤ K.degree z := (degree (iso z)).trans_eq (iso.degree_eq z)
  exact short_map (isContained_iff_exists_le_comap.mpr ⟨e.toEmbedding,le_rfl⟩)
    (two_regular_orbits K inv deg)

/-- A prime divisor of the order of a transitive automorphism group gives the
prime-order action by Cauchy's theorem. No bound on the valency above three. -/
theorem vertex_transitive_twice_prime {p : ℕ} (prime : p.Prime) (size : Fintype.card V=2*p)
    (transitive : ∀ x y : V, ∃ g : G ≃g G, g x=y) (degree : ∀ v, 3 ≤ G.degree v) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  classical
  let : Fact p.Prime := ⟨prime⟩
  let A : Subgroup (Equiv.Perm V) :=
    { carrier := {g | ∀ u v, G.Adj (g u) (g v) ↔ G.Adj u v}
      mul_mem' := fun hg hh u v => (hg _ _).trans (hh u v)
      one_mem' := fun _ _ => Iff.rfl
      inv_mem' := fun {g} hg u v => by simpa using (hg (g.symm u) (g.symm v)).symm }
  let : IsPretransitive A V := ⟨fun u v => by
    obtain ⟨g,h⟩ := transitive u v
    exact ⟨⟨g.toEquiv,fun _ _ => g.map_rel_iff⟩,h⟩⟩
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp (size ▸ Nat.mul_pos (by decide) prime.pos)
  have dv := (stabilizer A x).index_dvd_card
  rw [index_stabilizer_of_transitive A x, Nat.card_eq_fintype_card, size] at dv
  obtain ⟨g,ord⟩ := exists_prime_orderOf_dvd_card' (G:=A) p ((dvd_mul_left p 2).trans dv)
  let B := Subgroup.zpowers g
  let : CommGroup B := IsCyclic.commGroup
  have count : Nat.card B=p := (Nat.card_zpowers g).trans ord
  have moves : ∃ y : V, g.val y ≠ y := by
    by_contra! fixed
    have eq : g=1 := Subtype.ext (Equiv.ext fixed)
    rw [eq,orderOf_one] at ord
    exact prime.ne_one ord.symm
  obtain ⟨y,hy⟩ := moves
  apply prime_action (B:=B) G (count ▸ prime) (by simpa [← Nat.card_eq_fintype_card, count] using size)
    ⟨y,⟨g,Subgroup.mem_zpowers g⟩,hy⟩ _ degree
  exact fun b _ _ h => (b.val.property _ _).mpr h

end Erdos64TwicePrime


/-- Every vertex-transitive graph of power-of-two order and minimum degree
three satisfies Erdős–Gyárfás, including the complete four-vertex case. -/
theorem transitive_dyadic_order {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (degree : ∀ x, 3 ≤ G.degree x)
    (transitive : ∀ x y, ∃ g : G ≃g G, g x=y) {k : ℕ} (order : Fintype.card V=2^k) :
    ∃ d : ℕ, 2 ≤ d ∧ cycleGraph (2^d) ⊑ G := by
  by_cases big : 3 ≤ k
  · obtain ⟨m,rfl⟩ : ∃ m, k=m+3 := ⟨k-3,by omega⟩
    obtain ⟨d,hd,_,c⟩ := short_of_transitive G degree transitive order
    exact ⟨d,hd,c⟩
  · have small : k≤2 := by omega
    let x : V := Classical.choice inferInstance
    have lt := G.degree_lt_card_verts x
    have low := degree x
    have four : Fintype.card V=4 := by interval_cases k <;> norm_num at order <;> omega
    exact ⟨2,by decide,square_at_four G four degree⟩

theorem reduced_component (asymmetric : H1) (trans : H2) {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (minimum : 3 ≤ G.minDegree)
    (edges : ∀ ⦃a b⦄, G.Adj a b → G.degree a=3 ∨ G.degree b=3)
    (near : ∀ a, ∃ b, G.Adj a b ∧ G.degree b=3) :
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length=2^k := by
  classical
  let C := G.connectedComponentMk (Classical.choice inferInstance)
  let K := G.induce C.supp
  have : Nonempty C.supp := C.nonempty_supp.to_subtype
  have equal (x : C.supp) : K.degree x=G.degree x.val :=
    degree_induce_of_neighborSet_subset fun _ h => C.mem_supp_of_adj_mem_supp x.property h
  have degree (x : C.supp) : 3 ≤ K.degree x := by rw [equal]; exact minimum.trans (G.minDegree_le_degree _)
  have neighbors (a : C.supp) : ∃ b, K.Adj a b ∧ K.degree b=3 := by
    obtain ⟨b,ab,db⟩ := near a.val
    let y : C.supp := ⟨b,C.mem_supp_of_adj_mem_supp a.property ab⟩
    exact ⟨y,ab,(equal y).trans db⟩
  have endpoints ⦃a b : C.supp⦄ (ab : K.Adj a b) : K.degree a=3 ∨ K.degree b=3 := by
    rw [equal,equal]
    exact edges ab
  have conn : K.Connected := C.connected_toSimpleGraph
  have here : ∃ d : ℕ, 2 ≤ d ∧ cycleGraph (2^d) ⊑ K := by
    by_cases sq : cycleGraph 4 ⊑ K
    · exact ⟨2,by decide,sq⟩
    by_cases oct : cycleGraph 8 ⊑ K
    · exact ⟨3,by decide,oct⟩
    by_cases sym : ∀ x y, ∃ g : K ≃g K, g x=y
    · by_cases dyadic : ∃ k : ℕ, Fintype.card C.supp=2^k
      · obtain ⟨k,hk⟩ := dyadic
        exact transitive_dyadic_order K degree sym hk
      · have three (v : C.supp) : K.degree v=3 := by
          obtain ⟨x,_,dx⟩ := neighbors v
          obtain ⟨g,hg⟩ := sym x v
          rw [←hg,g.degree_eq x,dx]
        by_cases size : ∃ p : ℕ, p.Prime ∧ Fintype.card C.supp=2*p
        · obtain ⟨p,hp,n⟩ := size
          rcases Erdos64TwicePrime.vertex_transitive_twice_prime K hp n sym degree with a|b|c
          · exact ⟨2,by decide,a⟩
          · exact ⟨3,by decide,b⟩
          · exact ⟨4,by decide,c⟩
        · exact trans _ K conn three sym (fun k eq => dyadic ⟨k,eq⟩)
            (fun p hp eq => size ⟨p,hp,eq⟩) sq oct
    · exact asymmetric _ K conn degree sym endpoints neighbors sq oct
  obtain ⟨k,hk,copy⟩ := here
  have four : 4≤2^k := Nat.pow_le_pow_right (by decide : 0<2) hk
  obtain ⟨v,c,cycle,len⟩ := (cycleGraph_isContained_iff (by omega)).mp copy
  let inc : K →g G := (SimpleGraph.Embedding.induce C.supp).toHom
  exact ⟨k,v.val,c.map inc,hk,cycle.map Subtype.val_injective,(Walk.length_map _ _).trans len⟩


theorem nonempty_of_min_degree {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (minimum : 3 ≤ G.minDegree) : Nonempty V := by
  rcases isEmpty_or_nonempty V with hv | hv
  · have := hv
    have hz := G.minDegree_of_subsingleton
    omega
  · exact hv

theorem delete_edge_degree {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b : V) (minimum : 3 ≤ G.minDegree)
    (ha : 3 < G.degree a) (hb : 3 < G.degree b) (x : V) :
    3 ≤ (G.deleteEdges {s(a, b)}).degree x := by
  let H := G.deleteEdges {s(a, b)}
  change 3 ≤ H.degree x
  let removed : Finset V := if x = a then {b} else if x = b then {a} else ∅
  have inclusion : G.neighborFinset x ⊆ H.neighborFinset x ∪ removed := by
    intro y hy
    have adj := (G.mem_neighborFinset x y).mp hy
    apply Finset.mem_union.mpr
    by_cases h : s(x, y) = s(a, b)
    · right
      rcases (Sym2.mk_eq_mk_iff (p := (x, y)) (q := (a, b))).mp h with hd | hd
      · have hx : x = a := congrArg Prod.fst hd
        have hyb : y = b := congrArg Prod.snd hd
        simp [removed, hx, hyb]
      · have hx : x = b := congrArg Prod.fst hd
        have hya : y = a := congrArg Prod.snd hd
        by_cases hab : a = b <;> simp [removed, hx, hya, hab, eq_comm]
    · left
      apply (H.mem_neighborFinset x y).mpr
      exact SimpleGraph.deleteEdges_adj.mpr ⟨adj, by simpa using h⟩
  have cardinal : G.degree x ≤ H.degree x + removed.card := by
    simpa only [card_neighborFinset_eq_degree] using
      (Finset.card_le_card inclusion).trans (Finset.card_union_le _ _)
  have loss : removed.card ≤ 1 := by
    dsimp [removed]
    split
    · simp
    · split <;> simp
  by_cases endpoints : x = a ∨ x = b
  · have larger : 3 < G.degree x := endpoints.elim (fun hx => hx.symm ▸ ha)
      (fun hx => hx.symm ▸ hb)
    omega
  · have noLoss : removed.card = 0 := by simp [removed, (not_or.mp endpoints).1,
      (not_or.mp endpoints).2]
    have lower := minimum.trans (G.minDegree_le_degree x)
    omega

theorem solve_restricted (asymmetric : H1) (trans : H2) (n : ℕ) :
    ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V + G.edgeFinset.card = n → 3 ≤ G.minDegree →
      ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V G finite dec measure minimum
    classical
    have : Nonempty V := nonempty_of_min_degree G minimum
    by_cases edgeCondition : ∀ ⦃a b⦄, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3
    · by_cases vertexCondition : ∀ a, ∃ b, G.Adj a b ∧ G.degree b = 3
      · exact reduced_component asymmetric trans G minimum edgeCondition vertexCondition
      · rw [not_forall] at vertexCondition
        obtain ⟨a, bad⟩ := vertexCondition
        let S : Set V := {v | v ≠ a}
        let H := G.induce S
        have positive : 0 < G.degree a := Nat.lt_of_lt_of_le (by decide)
          (minimum.trans (G.minDegree_le_degree a))
        obtain ⟨neighbor, hneighbor⟩ := (G.degree_pos_iff_exists_adj a).mp positive
        have : Nonempty S := ⟨⟨neighbor, hneighbor.ne.symm⟩⟩
        have minimumH : 3 ≤ H.minDegree := by
          apply H.le_minDegree_of_forall_le_degree
          intro x
          have lower := minimum.trans (G.minDegree_le_degree x.val)
          by_cases hx : G.Adj x.val a
          · have higher : 3 < G.degree x.val := by
              have ne : G.degree x.val ≠ 3 := fun eq => bad ⟨x.val, hx.symm, eq⟩
              omega
            have erased : (H.neighborFinset x).map (.subtype (· ∈ S)) =
                (G.neighborFinset x.val).erase a := by
              rw [SimpleGraph.map_neighborFinset_induce]
              ext y
              simp [S, and_comm]
            have cards := congrArg Finset.card erased
            rw [Finset.card_map, card_neighborFinset_eq_degree,
              Finset.card_erase_of_mem ((G.mem_neighborFinset x.val a).mpr hx),
              card_neighborFinset_eq_degree] at cards
            omega
          · have unchanged : H.degree x = G.degree x.val :=
              SimpleGraph.degree_induce_of_neighborSet_subset
                (fun y hy eq => hx (eq ▸ hy))
            omega
        have hv : Fintype.card S < Fintype.card V :=
          Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective
            (b := a) (fun ⟨x, eq⟩ => x.property eq)
        have he : H.edgeFinset.card ≤ G.edgeFinset.card := by
          have mapped := SimpleGraph.map_edgeFinset_induce (s := S) (G := G)
          rw [← Finset.card_map (f := (Function.Embedding.subtype (· ∈ S)).sym2Map), mapped]
          exact Finset.card_le_card Finset.inter_subset_left
        have smaller : Fintype.card S + H.edgeFinset.card < n := by omega
        obtain ⟨k, v, c, hk, hc, hl⟩ := ih _ smaller S H rfl minimumH
        let lift : H →g G := ⟨Subtype.val, fun h => h⟩
        exact ⟨k, v.val, c.map lift, hk, hc.map Subtype.val_injective, by simpa using hl⟩
    · push Not at edgeCondition
      obtain ⟨a, b, hadj, ha, hb⟩ := edgeCondition
      have hda := minimum.trans (G.minDegree_le_degree a)
      have hdb := minimum.trans (G.minDegree_le_degree b)
      let H := G.deleteEdges {s(a, b)}
      have minimumH : 3 ≤ H.minDegree :=
        H.le_minDegree_of_forall_le_degree 3
          (delete_edge_degree G a b minimum (by omega) (by omega))
      have reduced : H.edgeFinset = G.edgeFinset.erase s(a, b) := by
        ext e
        simp [H, edgeSet_deleteEdges, and_comm]
      have edgeOf : s(a, b) ∈ G.edgeFinset := G.mem_edgeFinset.mpr hadj
      have strict : H.edgeFinset.card < G.edgeFinset.card := by
        rw [reduced]
        exact Finset.card_erase_lt_of_mem edgeOf
      have smaller : Fintype.card V + H.edgeFinset.card < n := by omega
      obtain ⟨k, v, c, hk, hc, hl⟩ := ih _ smaller V H rfl minimumH
      let leG : H ≤ G := G.deleteEdges_le _
      exact ⟨k, v, c.mapLe leG, hk, hc.mapLe leG, by simpa using hl⟩

theorem main : H1 → H2 → type_of% @Erdos64.erdos_64 := by
  intro asymmetric trans V G finite dec minimum
  classical
  let e := (Fintype.equivFin V).symm
  let H := G.comap e
  let i : H ≃g G := SimpleGraph.Iso.comap e G
  have minimumH : 3 ≤ H.minDegree := i.minDegree_eq ▸ minimum
  obtain ⟨k, v, c, hk, hc, hl⟩ := solve_restricted asymmetric trans _ _ H rfl minimumH
  exact ⟨k, i v, c.map i.toHom, hk, hc.map i.injective, by simpa using hl⟩

end OMA.R_Erdos64_erdos_64_R4
