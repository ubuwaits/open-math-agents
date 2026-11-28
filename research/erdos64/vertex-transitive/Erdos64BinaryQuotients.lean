import Erdos64SymmetricCycles

/-! Central involutions and two-sheeted quotients of symmetric cubic graphs. -/

namespace Erdos64BinaryQuotients

open SimpleGraph Function Erdos64TriangleExpansion Erdos64SymmetricCycles

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

end Erdos64BinaryQuotients
