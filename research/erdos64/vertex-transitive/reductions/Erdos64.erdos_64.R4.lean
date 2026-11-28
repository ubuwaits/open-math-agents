import FormalConjectures.ErdosProblems.«64»
import Mathlib

/-!
# The vertex-transitive power-of-two order case of Erdős–Gyárfás

Graphs on N = 2^(m+3) vertices with minimum degree three admit a simple
power-of-two cycle of length at most N/2 whenever the automorphism group
is vertex transitive. A transitive Sylow two-subgroup supplies a central free
involution. Either there is a square or its pairs define a two-sheeted cover
that preserves every local degree. A binary cover of the tetrahedron always
has a square. Strong induction proves the bound.

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

/-- The remaining transitive case is cubic and its order is not a power of two. -/
def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.Connected → (∀ x, G.degree x=3) →
    (∀ x y, ∃ g : G ≃g G, g x=y) →
    (∀ k : ℕ, Fintype.card V ≠ 2^k) →
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
        exact trans _ K conn three sym (fun k eq => dyadic ⟨k,eq⟩) sq oct
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
