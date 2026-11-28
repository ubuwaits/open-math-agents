import Erdos64ClassTwo

/-!
# Regular tetrahedral covers with a triangle and a sheet group of class at most two

Chad Mazzola (@ubuwaits), using Codex.

A triangle can be placed on colors 0, 3 and 1. Transporting the sheets from
its first vertex along the new spanning star makes the third chord trivial.
The central-commutator bound then gives a dyadic cycle of length at most 32.
-/

namespace Erdos64ClassTwo

open SimpleGraph Function Erdos64NormalCovers
open Fin.NatCast
open scoped commutatorElement

private def colors (i j k : Fin 4) : Fin 4 → Fin 4 := ![i,k,2-(i+j+k),j]

private theorem colors_injective : ∀ i j k : Fin 4, i ≠ j → j ≠ k → k ≠ i →
    Injective (colors i j k) := by decide

private def forward (i j : Fin 4) : Prop :=
  (i=0 ∧ j≠0) ∨ (i=1 ∧ j=2) ∨ (i=2 ∧ j=3) ∨ (i=3 ∧ j=1)

private instance (i j : Fin 4) : Decidable (forward i j) := by unfold forward; infer_instance

private theorem directions : ∀ i j : Fin 4, i ≠ j → forward i j ∨ forward j i := by decide

/-- The new star sends a sheet x in color i to the sheet hᵢ x of color σ(i). -/
private theorem rebase {A : Type} [Group A] (a b c : A) (σ : Fin 4 → Fin 4)
    (injective : Injective σ) (h : Fin 4 → A) (u v : A)
    (star : ∀ j, tetraEdges a b c (σ 0) (σ j) * h 0 = h j)
    (chord12 : tetraEdges a b c (σ 1) (σ 2) * h 1 = h 2 * u)
    (chord23 : tetraEdges a b c (σ 2) (σ 3) * h 2 = h 3 * v)
    (chord31 : tetraEdges a b c (σ 3) (σ 1) * h 3 = h 1) :
    tetraGraph u v 1 A ⊑ tetraGraph a b c A := by
  let step (i j : Fin 4) := tetraEdges a b c (σ i) (σ j) * h i = h j * tetraEdges u v 1 i j
  have direct {i j : Fin 4} (d : forward i j) : step i j := by
    rcases d with ⟨rfl,hj⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · change tetraEdges a b c (σ 0) (σ j) * h 0 = h j * tetraEdges u v 1 0 j
      rw [star]
      fin_cases j <;> simp [tetraEdges]
    · simpa [step,tetraEdges] using chord12
    · simpa [step,tetraEdges] using chord23
    · simpa [step,tetraEdges] using chord31
  have flip {i j : Fin 4} (s : step i j) : step j i := by
    change tetraEdges a b c (σ i) (σ j) * h i = h j * tetraEdges u v 1 i j at s
    change tetraEdges a b c (σ j) (σ i) * h j = h i * tetraEdges u v 1 j i
    rw [tetra_reverse a b c (σ i) (σ j),tetra_reverse u v 1 i j]
    calc _ = (tetraEdges a b c (σ i) (σ j))⁻¹ * (h j * tetraEdges u v 1 i j) *
              (tetraEdges u v 1 i j)⁻¹ := by group
         _ = _ := by rw [← s]; group
  let f (p : Fin 4 × A) := (σ p.1,h p.1 * p.2)
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · intro p q adj
    have neq : p.1 ≠ q.1 := adj.1
    have law := (directions p.1 q.1 neq).elim direct (fun d => flip (direct d))
    refine ⟨fun eq => neq (injective eq),?_⟩
    change tetraEdges a b c (σ p.1) (σ q.1) * (h p.1 * p.2) = h q.1 * q.2
    rw [← mul_assoc,law,mul_assoc]
    exact congrArg (h q.1 * ·) adj.2
  · rintro ⟨i,x⟩ ⟨j,y⟩ eq
    obtain rfl : i=j := injective (congrArg (fun p : Fin 4 × A => p.1) eq)
    have xy : x=y := mul_left_cancel (congrArg (fun p : Fin 4 × A => p.2) eq : h i*x=h i*y)
    rw [xy]

/-- In any finite regular tetrahedral cover with a triangle and central
commutators, the graph contains a simple 4-, 8-, 16- or 32-cycle. -/
theorem triangle_bound {A : Type} [Group A] [Finite A] (a b c : A)
    (central : ∀ u v g : A, Commute g ⁅u,v⁆)
    (triangle : ∃ x y z, (tetraGraph a b c A).Adj x y ∧
      (tetraGraph a b c A).Adj y z ∧ (tetraGraph a b c A).Adj z x) :
    ∃ d : ℕ, 2 ≤ d ∧ 2^d ≤ 32 ∧ cycleGraph (2^d) ⊑ tetraGraph a b c A := by
  obtain ⟨x,y,z,xy,yz,zx⟩ := triangle
  let σ := colors x.1 y.1 z.1
  let e (i j : Fin 4) := tetraEdges a b c (σ i) (σ j)
  let h (j : Fin 4) := e 0 j
  have h0 : h 0 = 1 := by
    change tetraEdges a b c x.1 x.1 = 1
    generalize x.1 = i
    fin_cases i <;> simp [tetraEdges]
  let u := (h 2)⁻¹ * (e 1 2 * h 1)
  let v := (h 3)⁻¹ * (e 2 3 * h 2)
  have flat : e 3 1 * h 3 = h 1 := by
    apply mul_right_cancel (b := x.2)
    rw [mul_assoc]
    change tetraEdges a b c y.1 z.1 * (tetraEdges a b c x.1 y.1 * x.2) = tetraEdges a b c x.1 z.1 * x.2
    rw [show tetraEdges a b c x.1 y.1 * x.2=y.2 from xy.2]
    exact yz.2.trans (zx.symm.2).symm
  have embed := rebase a b c σ (colors_injective _ _ _ xy.1 yz.1 zx.1) h u v
    (fun _ => by rw [h0,mul_one])
    (by change e 1 2 * h 1 = h 2 * ((h 2)⁻¹ * (e 1 2 * h 1)); group)
    (by change e 2 3 * h 2 = h 3 * ((h 3)⁻¹ * (e 2 3 * h 2)); group) flat
  obtain ⟨d,lo,hi,cycle⟩ := central_commutator_bound u v (central u v)
  exact ⟨d,lo,hi,cycle.trans embed⟩

/-- A triangular class-two quotient by a normal two-subgroup supplies a dyadic
cycle upstairs, even when the original cover has no triangle. -/
theorem triangle_quotient_bound {A : Type} [Group A] [Finite A] (a b c : A)
    (N : Subgroup A) [N.Normal] (two : IsPGroup 2 N)
    (central : ∀ u v g : A ⧸ N, Commute g ⁅u,v⁆) :
    let q := QuotientGroup.mk' N
    let K := tetraGraph (q a) (q b) (q c) (A ⧸ N)
    (∃ x y z, K.Adj x y ∧ K.Adj y z ∧ K.Adj z x) →
      ∃ d : ℕ, 2 ≤ d ∧ 2^d ≤ 32 * Nat.card N ∧ cycleGraph (2^d) ⊑ tetraGraph a b c A := by
  intro q K triangle
  obtain ⟨k,hk,len,cycle⟩ := triangle_bound (q a) (q b) (q c) central triangle
  have act (g : A) (y : A ⧸ N) : g • y = q g * y := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N y
    rfl
  have edges (i j : Fin 4) : q (tetraEdges a b c i j) = tetraEdges (q a) (q b) (q c) i j := by
    fin_cases i <;> fin_cases j <;> simp [tetraEdges]
  have same : tetraGraph a b c (A ⧸ N) = K := by
    ext u v
    change (_ ∧ tetraEdges a b c u.1 v.1 • u.2 = v.2) ↔ _ ∧ tetraEdges (q a) (q b) (q c) u.1 v.1 * u.2 = v.2
    rw [act,edges]
  have onQuotient : cycleGraph (2^k) ⊑ tetraGraph a b c (A ⧸ N) := same ▸ cycle
  obtain ⟨path⟩ := onQuotient
  have liftPoint (g : A) (stable : g • (path 0).2 = (path 0).2) :
      ∃ x : A, q x = (path 0).2 ∧ ∃ j : ℕ, IsPeriodicPt (MulAction.toPermHom A A g) (2^j) x := by
    have trivial : q g = 1 := mul_right_cancel ((act g _).symm.trans (stable.trans (one_mul _).symm))
    let n : N := ⟨g,(QuotientGroup.eq_one_iff g).mp trivial⟩
    obtain ⟨j,hj⟩ := two n
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective N (path 0).2
    refine ⟨x,hx,j,?_⟩
    have kill : g^(2^j) = 1 := congrArg Subtype.val hj
    change ((MulAction.toPermHom A A g : A → A)^[2^j]) x = x
    rw [← Equiv.Perm.coe_pow,← map_pow,kill,map_one]
    rfl
  have count (y : A ⧸ N) : Nat.card {x : A // q x=y} ≤ Nat.card N := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N y
    let f (n : N) : {w : A // q w = q x} :=
      ⟨(n : A)*x, by rw [map_mul,show q (n : A)=1 from (QuotientGroup.eq_one_iff _).mpr n.property,one_mul]⟩
    apply Nat.card_le_card_of_surjective f
    intro w
    have hz : q (w.val*x⁻¹) = 1 := by rw [map_mul,map_inv,w.property,mul_inv_cancel]
    exact ⟨⟨w.val*x⁻¹,(QuotientGroup.eq_one_iff _).mp hz⟩,Subtype.ext (by simp [f,mul_assoc])⟩
  obtain ⟨d,lo,hi,result⟩ := lift_cycle (⊤ : SimpleGraph (Fin 4)) (tetraEdges a b c)
    (fun {_ _} _ => tetra_reverse a b c _ _) q (QuotientGroup.mk'_surjective N)
    (fun _ _ => rfl) hk path liftPoint
  exact ⟨d,hk.trans lo,hi.trans (Nat.mul_le_mul len (count _)),result⟩

end Erdos64ClassTwo
