import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H1_R1
import Mathlib

/-!
# Prime-sheeted solvable tetrahedral covers and fixed-point-free affine actions

Credit: @ubuwaits, using Codex.

In the normalized cover of the tetrahedron, a Hamilton cycle uses two of the
three matching permutations. For affine actions, a nonidentity linear return
with invertible difference from identity has a fixed point, giving a square.
Otherwise all three linear parts agree and square to the identity. The
fixed-point-free assumption makes a nontrivial involution act by negation, so
the signed affine theorem in PR #7329 applies. For a solvable transitive
permutation group of prime degree, its last nontrivial derived subgroup is
abelian and acts regularly. Every nonidentity automorphism of this prime-order
group fixes only the identity. This proves the 4/8/16 bound for the entire
solvable prime-degree case.

The remaining cases are composite degree without an affine orbit of the stated
type, and prime degree with nonsolvable monodromy. The parent signed affine
reduction is PR #7329; its predecessors are PR #5246 by @mejiasd3v and PR #592
by @JamesSlash.
-/

open Function SimpleGraph MulAction
namespace TetrahedralPrimeReduction

private theorem hamiltonSquare {A V : Type*} (G : SimpleGraph V) (e : (Fin 4) × A ↪ V)
    (i j k : (Fin 4)) (colors : Injective (![0,i,j,k] : Fin 4 → (Fin 4))) (x y : A)
    (h₀ : G.Adj (e (0,x)) (e (i,x))) (h₁ : G.Adj (e (i,x)) (e (j,y)))
    (h₂ : G.Adj (e (j,y)) (e (k,x))) (h₃ : G.Adj (e (k,x)) (e (0,x))) :
    cycleGraph 4 ⊑ G := by
  let v : Fin 4 → (Fin 4) × A := ![(0,x),(i,x),(j,y),(k,x)]
  have projection (t : Fin 4) : (v t).1 = (![0,i,j,k] : Fin 4 → (Fin 4)) t := by
    fin_cases t <;> rfl
  refine ⟨⟨⟨fun t => e (v t), ?_⟩, ?_⟩⟩
  · intro s t edge
    fin_cases s <;> fin_cases t <;> first
      | exact h₀ | exact h₁ | exact h₂ | exact h₃
      | exact h₀.symm | exact h₁.symm | exact h₂.symm | exact h₃.symm
      | exact absurd edge (by decide)
  · intro s t eq
    apply colors
    rw [← projection, ← projection]
    exact congrArg Prod.fst (e.injective eq)

/-- A group acts additively on the sheets. If every nonidentity linear part
has invertible difference from the identity, three arbitrary affine chords
still force a 4-, 8-, or 16-cycle. -/
theorem fixed_point_free_affine_short {A S V : Type*} [AddCommGroup A] [Group S]
    [DistribMulAction S A] (G : SimpleGraph V) (e : (Fin 4) × A ↪ V)
    (regular : ∀ g : S, g ≠ 1 → Bijective (fun x : A => x - g • x))
    (p q r : S) (a b c : A)
    (star : ∀ i : (Fin 4), i ≠ 0 → ∀ x, G.Adj (e (0,x)) (e (i,x)))
    (oneTwo : ∀ x, G.Adj (e (1,x)) (e (2,p • x + a)))
    (twoThree : ∀ x, G.Adj (e (2,x)) (e (3,q • x + b)))
    (threeOne : ∀ x, G.Adj (e (3,x)) (e (1,r • x + c))) : cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  have fixed (s t : S) (u v : A) (ne : t*s ≠ 1) :
      ∃ x : A, t • (s • x + u) + v = x := by
    obtain ⟨x,hx⟩ := (regular _ ne).surjective (t • u + v)
    refine ⟨x,?_⟩
    change x - (t*s) • x = t • u + v at hx
    rw [sub_eq_iff_eq_add] at hx
    rw [smul_add, ← mul_smul]
    calc
      (t*s) • x + t • u + v = t • u + v + (t*s) • x := by abel
      _ = x := hx.symm
  by_cases qp : q*p = 1
  swap
  · obtain ⟨x,h⟩ := fixed p q a b qp
    exact Or.inl (hamiltonSquare G e 1 2 3 (by decide) x (p • x + a)
      (star 1 (by decide) x) (oneTwo x) (by simpa only [h] using twoThree (p • x + a)) (star 3 (by decide) x).symm)
  by_cases rq : r*q = 1
  swap
  · obtain ⟨x,h⟩ := fixed q r b c rq
    exact Or.inl (hamiltonSquare G e 2 3 1 (by decide) x (q • x + b)
      (star 2 (by decide) x) (twoThree x) (by simpa only [h] using threeOne (q • x + b)) (star 1 (by decide) x).symm)
  by_cases pr : p*r = 1
  swap
  · obtain ⟨x,h⟩ := fixed r p c a pr
    exact Or.inl (hamiltonSquare G e 3 1 2 (by decide) x (r • x + c)
      (star 3 (by decide) x) (threeOne x) (by simpa only [h] using oneTwo (r • x + c)) (star 2 (by decide) x).symm)
  have same : r = p := by
    calc r = r*1 := (mul_one r).symm
         _ = r*(q*p) := by rw [qp]
         _ = p := by rw [← mul_assoc,rq,one_mul]
  subst r
  have same : q = p := mul_right_cancel (qp.trans pr.symm)
  subst q
  by_cases trivial : p = 1
  · subst p
    apply TetrahedralReduction.affineTetrahedron G e false false false a b c star
    · simpa using oneTwo
    · simpa using twoThree
    · simpa using threeOne
  · have neg (x : A) : p • x = -x := by
      have invol : p • (p • x) = x := by rw [← mul_smul,pr,one_smul]
      have fixedSum : p • (x + p • x) = x + p • x := by rw [smul_add,invol,add_comm]
      have equal : x + p • x = 0 := (regular p trivial).injective (by
        rw [fixedSum,smul_zero,sub_self,sub_self])
      exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using equal)
    apply TetrahedralReduction.affineTetrahedron G e true true true a b c star
    · simpa [neg] using oneTwo
    · simpa [neg] using twoThree
    · simpa [neg] using threeOne

/-- Change the sheet coordinates independently in the three outer fibers.
This allows all six edge matchings to have arbitrary affine parts. -/
theorem affine_six_matchings_short {A S V : Type*} [AddCommGroup A] [Group S]
    [DistribMulAction S A] (G : SimpleGraph V) (e : (Fin 4) × A ↪ V)
    (regular : ∀ g : S, g ≠ 1 → Bijective (fun x : A => x - g • x))
    (st : (Fin 4) → S) (d : (Fin 4) → A) (p q r : S) (a b c : A)
    (star : ∀ i : (Fin 4), i ≠ 0 → ∀ x, G.Adj (e (0,x)) (e (i,st i • x + d i)))
    (oneTwo : ∀ x, G.Adj (e (1,x)) (e (2,p • x + a)))
    (twoThree : ∀ x, G.Adj (e (2,x)) (e (3,q • x + b)))
    (threeOne : ∀ x, G.Adj (e (3,x)) (e (1,r • x + c))) : cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  let frame (i : (Fin 4)) (x : A) := if i = 0 then x else st i • x + d i
  let label : (Fin 4) × A ↪ V := ⟨fun z => e (z.1,frame z.1 z.2), by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have h' := e.injective h
    have ij : i = j := congrArg Prod.fst h'
    subst j
    have eq : frame i x = frame i y := congrArg Prod.snd h'
    apply congrArg (fun z : A => (i,z))
    by_cases zero : i = 0
    · simpa only [frame,if_pos zero] using eq
    · simp only [frame,if_neg zero,add_left_inj] at eq
      exact (MulAction.bijective (st i)).injective eq⟩
  let linear (i j : (Fin 4)) (g : S) := (st j)⁻¹ * (g * st i)
  let bias (i j : (Fin 4)) (g : S) (z : A) := (st j)⁻¹ • (g • d i + z - d j)
  have chord (i j : (Fin 4)) (hi : i ≠ 0) (hj : j ≠ 0) (g : S) (z : A)
      (edge : ∀ x, G.Adj (e (i,x)) (e (j,g • x + z))) (x : A) :
      G.Adj (label (i,x)) (label (j,linear i j g • x + bias i j g z)) := by
    change G.Adj (e (i,frame i x)) (e (j,frame j _))
    simp only [frame, if_neg hi, if_neg hj]
    have norm : st j • (linear i j g • x + bias i j g z) + d j =
        g • (st i • x + d i) + z := by
      simp only [linear,bias,smul_add,mul_smul,smul_inv_smul]
      abel
    rw [norm]
    exact edge _
  apply fixed_point_free_affine_short G label regular (linear 1 2 p) (linear 2 3 q) (linear 3 1 r)
    (bias 1 2 p a) (bias 2 3 q b) (bias 3 1 r c)
  · intro i hi x
    change G.Adj (e (0,frame 0 x)) (e (i,frame i x))
    simpa only [frame,if_pos rfl,if_neg hi] using star i hi x
  · exact chord 1 2 (by decide) (by decide) p a oneTwo
  · exact chord 2 3 (by decide) (by decide) q b twoThree
  · exact chord 3 1 (by decide) (by decide) r c threeOne

/-- On finite sheets it suffices that every nonidentity element fixes only zero. -/
theorem finite_frobenius_short {A S V : Type*} [AddCommGroup A] [Finite A] [Group S]
    [DistribMulAction S A] (G : SimpleGraph V) (e : (Fin 4) × A ↪ V)
    (free : ∀ g : S, g ≠ 1 → ∀ x : A, g • x = x → x = 0)
    (st : (Fin 4) → S) (d : (Fin 4) → A) (p q r : S) (a b c : A)
    (star : ∀ i : (Fin 4), i ≠ 0 → ∀ x, G.Adj (e (0,x)) (e (i,st i • x + d i)))
    (oneTwo : ∀ x, G.Adj (e (1,x)) (e (2,p • x + a)))
    (twoThree : ∀ x, G.Adj (e (2,x)) (e (3,q • x + b)))
    (threeOne : ∀ x, G.Adj (e (3,x)) (e (1,r • x + c))) : cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  apply affine_six_matchings_short G e _ st d p q r a b c star oneTwo twoThree threeOne
  intro g ng
  apply Finite.injective_iff_bijective.mp
  intro x y equal
  change x - g • x = y - g • y at equal
  apply sub_eq_zero.mp
  apply free g ng
  rw [smul_sub]
  calc g • x - g • y = (x-y) - ((x-g • x)-(y-g • y)) := by abel
       _ = x-y := by rw [equal,sub_self,sub_zero]

private theorem abelianNormal {G : Type*} [Group G] [Group.IsSolvable G] [Nontrivial G] :
    ∃ N : Subgroup G, N ≠ ⊥ ∧ N.Normal ∧ IsMulCommutative N := by
  classical
  have terminating : ∃ n : ℕ, derivedSeries G n = ⊥ := Group.IsSolvable.solvable
  let m := Nat.find terminating
  have last : derivedSeries G m = ⊥ := Nat.find_spec terminating
  have pos : m ≠ 0 := by
    intro z
    rw [z,derivedSeries_zero] at last
    exact top_ne_bot last
  obtain ⟨k,hk⟩ : ∃ k, m = k+1 := ⟨m-1,by omega⟩
  refine ⟨derivedSeries G k, ?_, derivedSeries_normal G k, ?_⟩
  · intro trivial
    have le : m ≤ k := Nat.find_min' terminating trivial
    omega
  · rw [hk,derivedSeries_succ] at last
    exact Subgroup.commutator_self_eq_bot_iff.mp last

private theorem automorphism_fixed {N : Type*} [Group N] (prime : (Nat.card N).Prime)
    (u : MulAut N) (ne : u ≠ 1) (x : N) (hx : u x = x) : x = 1 := by
  classical
  by_contra nx
  let : Fact (Nat.card N).Prime := ⟨prime⟩
  apply ne
  ext y
  obtain ⟨k,rfl⟩ := mem_zpowers_of_prime_card (p := Nat.card N) rfl nx (g' := y)
  simp only [map_zpow, hx, MulAut.one_apply]

/-- A faithful transitive solvable permutation group on a prime number of
sheets gives a tetrahedral cover with a simple 4-, 8-, or 16-cycle. -/
theorem prime_solvable_short {G X V : Type*} [Group G] [Group.IsSolvable G]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X] [Finite X]
    (prime : (Nat.card X).Prime) (graph : SimpleGraph V) (e : (Fin 4) × X ↪ V)
    (p q r : G)
    (star : ∀ i : (Fin 4), i ≠ 0 → ∀ x, graph.Adj (e (0,x)) (e (i,x)))
    (oneTwo : ∀ x, graph.Adj (e (1,x)) (e (2,p • x)))
    (twoThree : ∀ x, graph.Adj (e (2,x)) (e (3,q • x)))
    (threeOne : ∀ x, graph.Adj (e (3,x)) (e (1,r • x))) : cycleGraph 4 ⊑ graph ∨ cycleGraph 8 ⊑ graph ∨ cycleGraph 16 ⊑ graph := by
  classical
  let : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp prime.one_lt
  obtain ⟨origin,y,xy⟩ := exists_pair_ne X
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G origin y
  let : Nontrivial G := ⟨⟨g,1,fun he => xy (by simpa only [he,one_smul] using hg)⟩⟩
  obtain ⟨N,nn,normal,comm⟩ := abelianNormal (G := G)
  let : N.Normal := normal
  let : IsMulCommutative N := comm
  let : CommGroup N := { (inferInstance : Group N) with mul_comm := mul_comm' }
  let : IsPreprimitive G X := IsPreprimitive.of_prime_card prime
  have nonfixed : fixedPoints N X ≠ Set.univ := by
    intro allFixed
    apply nn
    apply eq_bot_iff.mpr
    intro n hn
    change n = 1
    apply eq_of_smul_eq_smul (α := X)
    intro x
    have fixed : x ∈ fixedPoints N X := allFixed ▸ Set.mem_univ x
    simpa only [Subgroup.smul_def,one_smul] using (mem_fixedPoints.mp fixed (⟨n,hn⟩ : N))
  let : IsPretransitive N X := IsQuasiPreprimitive.isPretransitive_of_normal nonfixed
  let coords : N ≃ X := Equiv.ofBijective (fun n : N => n • origin) ⟨by
    intro n m same
    apply Subtype.ext
    apply eq_of_smul_eq_smul (α := X)
    intro x
    obtain ⟨h,rfl⟩ := MulAction.exists_smul_eq N origin x
    change n • (h • origin) = m • (h • origin)
    simpa only [smul_comm n h,smul_comm m h] using congrArg (fun z : X => h • z) same,
    fun x => MulAction.exists_smul_eq N origin x⟩
  have card : (Nat.card N).Prime := (Nat.card_congr coords).symm ▸ prime
  let : Finite N := Finite.of_equiv X coords.symm
  let : DistribMulAction (MulAut N) (Additive N) := {
    smul u x := Additive.ofMul (u x.toMul)
    one_smul x := rfl
    mul_smul u v x := rfl
    smul_zero u := u.map_one
    smul_add u x y := u.map_mul _ _ }
  let shift (h : G) : Additive N := Additive.ofMul (coords.symm (h • origin))
  let linear (h : G) : MulAut N := MulAut.conjNormal h
  let label : (Fin 4) × Additive N ↪ V :=
    ((Equiv.refl (Fin 4)).prodCongr (Additive.toMul.trans coords)).toEmbedding.trans e
  have affine (h : G) (x : Additive N) :
      coords ((linear h • x + shift h).toMul) = h • coords x.toMul := by
    change ((MulAut.conjNormal h x.toMul) * coords.symm (h • origin)) • origin =
      h • (x.toMul • origin)
    rw [mul_smul]
    have base : coords.symm (h • origin) • origin = h • origin := coords.apply_symm_apply _
    rw [base]
    change ((MulAut.conjNormal h x.toMul : N) : G) • (h • origin) =
      h • ((x.toMul : G) • origin)
    simp only [MulAut.conjNormal_apply, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
  apply finite_frobenius_short graph label (S := MulAut N) _ (fun _ => 1) (fun _ => 0)
    (linear p) (linear q) (linear r) (shift p) (shift q) (shift r)
  · intro i hi x
    change graph.Adj (e (0,coords x.toMul)) (e (i,coords (((1 : MulAut N) • x + 0).toMul)))
    simpa only [one_smul,add_zero] using star i hi (coords x.toMul)
  · intro x
    change graph.Adj (e (1,coords x.toMul)) (e (2,coords ((linear p • x + shift p).toMul)))
    rw [affine]
    exact oneTwo _
  · intro x
    change graph.Adj (e (2,coords x.toMul)) (e (3,coords ((linear q • x + shift q).toMul)))
    rw [affine]
    exact twoThree _
  · intro x
    change graph.Adj (e (3,coords x.toMul)) (e (1,coords ((linear r • x + shift r).toMul)))
    rw [affine]
    exact threeOne _
  · intro u nu x hx
    exact automorphism_fixed card u nu x.toMul hx

/-- A connected prime-sheeted tetrahedral cover whose chord permutations
generate a solvable group contains a cycle of length 4, 8, or 16. -/
theorem prime_solvable_cover_short {X : Type*} [Finite X] (p q r : Equiv.Perm X)
    (prime : (Nat.card X).Prime) (solvable : Group.IsSolvable (Subgroup.closure ({p,q,r} : Set _)))
    (connected : (SimpleGraph.fromRel (fun u v : Fin 4 × X =>
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨
    (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨
    (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2))).Connected) : let graph := SimpleGraph.fromRel (fun u v : Fin 4 × X =>
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨
    (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨
    (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2))
    cycleGraph 4 ⊑ graph ∨ cycleGraph 8 ⊑ graph ∨ cycleGraph 16 ⊑ graph := by
  classical
  let M := Subgroup.closure ({p,q,r} : Set (Equiv.Perm X))
  let : Group.IsSolvable M := solvable
  let P : M := ⟨p,Subgroup.subset_closure (by simp)⟩
  let Q : M := ⟨q,Subgroup.subset_closure (by simp)⟩
  let R : M := ⟨r,Subgroup.subset_closure (by simp)⟩
  let rel (u v : (Fin 4) × X) : Prop :=
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨ (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨ (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2)
  have directed {u v : (Fin 4) × X} (h : rel u v) : ∃ g : M, g • u.2 = v.2 := by
    rcases h with h | h | h | h
    · exact ⟨1,(one_smul M _).trans h.2.2.symm⟩
    · exact ⟨P,h.2.2.symm⟩
    · exact ⟨Q,h.2.2.symm⟩
    · exact ⟨R,h.2.2.symm⟩
  have adjacent {u v : (Fin 4) × X} (h : (SimpleGraph.fromRel (fun u v : Fin 4 × X =>
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨
    (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨
    (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2))).Adj u v) :
      ∃ g : M, g • u.2 = v.2 := by
    rcases h.2 with h | h
    · exact directed h
    · obtain ⟨g,hg⟩ := directed h
      exact ⟨g⁻¹,by rw [← hg,inv_smul_smul]⟩
  have path {u v : (Fin 4) × X} (w : (SimpleGraph.fromRel (fun u v : Fin 4 × X =>
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨
    (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨
    (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2))).Walk u v) :
      ∃ g : M, g • u.2 = v.2 := by
    induction w with
    | nil => exact ⟨1,one_smul M _⟩
    | cons edge tail ih =>
      obtain ⟨g,hg⟩ := adjacent edge
      obtain ⟨h,hh⟩ := ih
      exact ⟨h*g,by rw [mul_smul,hg,hh]⟩
  let : IsPretransitive M X := ⟨fun x y => by
    obtain ⟨w⟩ := connected.preconnected (0,x) (0,y)
    exact path w⟩
  apply prime_solvable_short (G := M) prime _ (Function.Embedding.refl _) P Q R
  · intro i hi x
    simp [SimpleGraph.fromRel, hi, Ne.symm hi]
  · intro x
    simp [SimpleGraph.fromRel, P]
  · intro x
    simp [SimpleGraph.fromRel, Q]
  · intro x
    simp [SimpleGraph.fromRel, R]

end TetrahedralPrimeReduction

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H1_R1_H2_R1

/-- Composite number of sheets, with neither a signed affine orbit nor an affine orbit
whose nontrivial linear parts have bijective difference from the identity. -/
def H1 : Prop := ∀ (X : Type) [Fintype X] [Nonempty X] (p q r : Equiv.Perm X),
  ¬ (Fintype.card X).Prime →
  (¬ ∃ (A : Type) (_ : AddCommGroup A) (f : A ↪ X) (s t u : Bool) (a b c : A),
    ∀ x, p (f x) = f ((if s then -x else x)+a) ∧ q (f x) = f ((if t then -x else x)+b) ∧
      r (f x) = f ((if u then -x else x)+c)) →
  ¬ (∃ (A S : Type) (_ : AddCommGroup A) (_ : Group S) (_ : DistribMulAction S A)
    (f : A ↪ X) (P Q R : S) (a b c : A), (∀ g : S, g ≠ 1 → Function.Bijective (fun x : A => x - g • x)) ∧
    ∀ x, p (f x) = f (P • x+a) ∧ q (f x) = f (Q • x+b) ∧ r (f x) = f (R • x+c)) →
  let K := SimpleGraph.fromRel (fun u v : Fin 4 × X =>
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨
    (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨
    (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2))
  K.Connected → ¬ K.IsBipartite → ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ K

/-- A prime number of sheets with nonsolvable monodromy. -/
def H2 : Prop := ∀ (X : Type) [Fintype X] [Nonempty X] (p q r : Equiv.Perm X),
  (Fintype.card X).Prime → ¬ Group.IsSolvable (Subgroup.closure ({p,q,r} : Set (Equiv.Perm X))) →
  let K := SimpleGraph.fromRel (fun u v : Fin 4 × X =>
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨
    (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨
    (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2))
  K.Connected → ¬ K.IsBipartite → ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ K

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H1_R1.H2 := by
  intro composite primeCase X fin nonempty p q r _ signed
  classical
  let K := SimpleGraph.fromRel (fun u v : Fin 4 × X =>
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨
    (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨
    (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2))
  change K.Connected → ¬ K.IsBipartite → ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ K
  intro connected nonbipartite
  have solved (h : cycleGraph 4 ⊑ K ∨ cycleGraph 8 ⊑ K ∨ cycleGraph 16 ⊑ K) :
      ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ K := by
    rcases h with h | h | h
    · exact ⟨2,by decide,h⟩
    · exact ⟨3,by decide,h⟩
    · exact ⟨4,by decide,h⟩
  by_cases prime : (Fintype.card X).Prime
  · by_cases sol : Group.IsSolvable (Subgroup.closure ({p,q,r} : Set (Equiv.Perm X)))
    · exact solved (TetrahedralPrimeReduction.prime_solvable_cover_short p q r
        (by simpa only [Nat.card_eq_fintype_card] using prime) sol connected)
    · exact primeCase X p q r prime sol connected nonbipartite
  · by_cases affine : (∃ (A S : Type) (_ : AddCommGroup A) (_ : Group S) (_ : DistribMulAction S A)
    (f : A ↪ X) (P Q R : S) (a b c : A), (∀ g : S, g ≠ 1 → Function.Bijective (fun x : A => x - g • x)) ∧
    ∀ x, p (f x) = f (P • x+a) ∧ q (f x) = f (Q • x+b) ∧ r (f x) = f (R • x+c))
    · obtain ⟨A,S,iA,iS,act,f,P,Q,R,a,b,c,regular,hf⟩ := affine
      let label : Fin 4 × A ↪ Fin 4 × X := (Function.Embedding.refl (Fin 4)).prodMap f
      apply solved
      apply TetrahedralPrimeReduction.fixed_point_free_affine_short K label regular P Q R a b c
      · intro i hi x
        simp [K,label,hi,Ne.symm hi]
      · intro x
        change K.Adj (1,f x) (2,f (P • x + a))
        rw [← (hf x).1]
        simp [K]
      · intro x
        change K.Adj (2,f x) (3,f (Q • x + b))
        rw [← (hf x).2.1]
        simp [K]
      · intro x
        change K.Adj (3,f x) (1,f (R • x + c))
        rw [← (hf x).2.2]
        simp [K]
    · exact composite X p q r prime signed affine connected nonbipartite

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H1_R1_H2_R1
