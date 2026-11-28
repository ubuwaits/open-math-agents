import Erdos64BinaryQuotients
import Erdos64TwoGroups

/-! Dyadic cycles in graphs admitting a transitive permutation 2-group. -/

namespace Erdos64VertexTransitive

open SimpleGraph Function Erdos64TriangleExpansion Erdos64SymmetricCycles Erdos64BinaryQuotients
open Erdos64TwoGroups

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

end Erdos64VertexTransitive
