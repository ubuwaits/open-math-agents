import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H1_R1
import Mathlib

/-!
# Solvable tetrahedral covers of prime or power-of-two degree and affine orbits

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
solvable prime-degree case. For a power of two sheets, an odd-order element of
the solvable transitive matching group fixes a sheet. The odd part of a
Hamiltonian return then fixes a sheet, so the square lifts to a dyadic cycle.

The remaining cases are composite degree outside the power-of-two solvable
and affine orbit cases, and prime degree with nonsolvable monodromy. The parent signed affine
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

private theorem connected_transitive {X : Type*} [Finite X] (p q r : Equiv.Perm X)
    (connected : (SimpleGraph.fromRel (fun u v : Fin 4 × X =>
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨
    (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨
    (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2))).Connected) : IsPretransitive (Subgroup.closure ({p,q,r} : Set (Equiv.Perm X))) X := by
  classical
  let M := Subgroup.closure ({p,q,r} : Set (Equiv.Perm X))
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
  exact ⟨fun x y => by
    obtain ⟨w⟩ := connected.preconnected (0,x) (0,y)
    exact path w⟩

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
  let : IsPretransitive M X := connected_transitive p q r connected
  let P : M := ⟨p,Subgroup.subset_closure (by simp)⟩
  let Q : M := ⟨q,Subgroup.subset_closure (by simp)⟩
  let R : M := ⟨r,Subgroup.subset_closure (by simp)⟩
  apply prime_solvable_short (G := M) prime _ (Function.Embedding.refl _) P Q R
  · intro i hi x
    simp [SimpleGraph.fromRel, hi, Ne.symm hi]
  · intro x
    simp [SimpleGraph.fromRel, P]
  · intro x
    simp [SimpleGraph.fromRel, Q]
  · intro x
    simp [SimpleGraph.fromRel, R]

open Fin.NatCast
open scoped Pointwise

private theorem orbit_cycle {U X : Type*} {H : SimpleGraph U} (f : X → X)
    (label : X ↪ U) (adj : ∀ z, H.Adj (label z) (label (f z))) (z : X)
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

/-- An affine map with an orbit of length coprime to the size of a finite
abelian group has a fixed point, given by the orbit's average. -/
theorem fixed_of_coprime_affine_orbit {A : Type*} [AddCommGroup A]
    (L : A →+ A) (b : A) (m : ℕ) (coprime : (Nat.card A).Coprime m)
    (z : ℕ → A) (step : ∀ i, z (i+1) = L (z i) + b) (closed : z m = z 0) :
    ∃ x : A, L x + b = x := by
  classical
  let total := ∑ i ∈ Finset.range m, z i
  have mulBij : Bijective (fun x : A => m • x) := coprime.nsmul_right_bijective
  obtain ⟨x,hx⟩ := mulBij.surjective total
  have shifted : (∑ i ∈ Finset.range m, z (i+1)) = total := by
    have h := Finset.sum_range_succ' z m
    rw [Finset.sum_range_succ, closed] at h
    exact add_right_cancel h.symm
  have invariant : L total + m • b = total := calc
    L total + m • b = ∑ i ∈ Finset.range m, z (i+1) := by
      simp only [total,map_sum,step,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range]
    _ = total := shifted
  change m • x = total at hx
  refine ⟨x,mulBij.injective ?_⟩
  rw [nsmul_add, ← map_nsmul, hx]
  exact invariant

private theorem primitive_coprime_fixed {G X : Type*} [Group G] [Group.IsSolvable G]
    [MulAction G X] [FaithfulSMul G X] [IsPreprimitive G X] [Finite X] [Nonempty X]
    (g : G) {m : ℕ} (coprime : (Nat.card X).Coprime m) (torsion : g^m = 1) :
    ∃ x : X, g • x = x := by
  classical
  by_cases trivial : Subsingleton X
  · exact ⟨Classical.arbitrary X, trivial.elim _ _⟩
  let : Nontrivial X := not_subsingleton_iff_nontrivial.mp trivial
  obtain ⟨origin,y,xy⟩ := exists_pair_ne X
  obtain ⟨t,ht⟩ := MulAction.exists_smul_eq G origin y
  let : Nontrivial G := ⟨⟨t,1,fun he => xy (by simpa only [he,one_smul] using ht)⟩⟩
  obtain ⟨N,nn,normal,comm⟩ := abelianNormal (G := G)
  let : N.Normal := normal
  let : IsMulCommutative N := comm
  let : CommGroup N := { (inferInstance : Group N) with mul_comm := mul_comm' }
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
    intro n t same
    apply Subtype.ext
    apply eq_of_smul_eq_smul (α := X)
    intro x
    obtain ⟨h,rfl⟩ := MulAction.exists_smul_eq N origin x
    change n • (h • origin) = t • (h • origin)
    simpa only [smul_comm n h,smul_comm t h] using congrArg (fun z : X => h • z) same,
    fun x => MulAction.exists_smul_eq N origin x⟩
  let e : Additive N ≃ X := Additive.toMul.trans coords
  let L : Additive N →+ Additive N := (MulAut.conjNormal g).toMonoidHom.toAdditive
  let b := e.symm (g • origin)
  have affine (x : Additive N) : e (L x + b) = g • e x := by
    change ((MulAut.conjNormal g x.toMul) * coords.symm (g • origin)) • origin =
      g • (x.toMul • origin)
    rw [mul_smul]
    have base : coords.symm (g • origin) • origin = g • origin := coords.apply_symm_apply _
    rw [base]
    change ((MulAut.conjNormal g x.toMul : N) : G) • (g • origin) =
      g • ((x.toMul : G) • origin)
    simp only [MulAut.conjNormal_apply, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
  let z (i : ℕ) := e.symm ((g^i) • origin)
  have step (i : ℕ) : z (i+1) = L (z i) + b := by
    apply e.injective
    simp only [z,Equiv.apply_symm_apply,affine,pow_succ',mul_smul]
  have closed : z m = z 0 := by simp [z,torsion]
  obtain ⟨x,hx⟩ := fixed_of_coprime_affine_orbit L b m ((Nat.card_congr e).symm ▸ coprime)
    z step closed
  exact ⟨e x,(affine x).symm.trans (congrArg e hx)⟩

/-- In a finite transitive solvable permutation action, an element whose
order is coprime to the number of points fixes a point. -/
theorem solvable_coprime_fixed {G X : Type*} [Group G] [Group.IsSolvable G]
    [MulAction G X] [IsPretransitive G X] [Finite X] [Nonempty X]
    (g : G) {m : ℕ} (coprime : (Nat.card X).Coprime m) (torsion : g^m = 1) :
    ∃ x : X, g • x = x := by
  classical
  by_cases prim : IsPreprimitive G X
  · let ρ := MulAction.toPermHom G X
    let M := ρ.range
    let f : X →ₑ[ρ.rangeRestrict] X := ⟨id, fun _ _ => rfl⟩
    let : Group.IsSolvable M := Group.isSolvable_of_surjective ρ.rangeRestrict_surjective
    let : IsPreprimitive M X := IsPreprimitive.of_surjective (f := f) Function.surjective_id
    apply primitive_coprime_fixed (ρ.rangeRestrict g) coprime
    rw [← map_pow,torsion,map_one]
  obtain ⟨B,block,nontrivial⟩ : ∃ B : Set X, IsBlock G B ∧ ¬ IsTrivialBlock B := by
    by_contra! all
    exact prim ⟨fun h => all _ h⟩
  have nonsingle : ¬ B.Subsingleton := fun h => nontrivial (Or.inl h)
  have proper : B ≠ Set.univ := fun h => nontrivial (Or.inr h)
  have two : 1 < B.ncard := Set.one_lt_ncard_iff_nontrivial.mpr
    (Set.not_subsingleton_iff.mp nonsingle)
  have present := ((Set.ncard_pos (s := B)).mp (by omega : 0 < B.ncard))
  have product := block.ncard_block_mul_ncard_orbit_eq present
  have orbPos : 0 < (orbit G B).ncard := (Set.ncard_pos (s := orbit G B)).mpr (MulAction.nonempty_orbit B)
  have smallerOrbit : Nat.card (orbit G B) < Nat.card X := by
    change (orbit G B).ncard < Nat.card X
    nlinarith
  have simpOrbit : (Nat.card (orbit G B)).Coprime m :=
    coprime.coprime_dvd_left ⟨B.ncard,product.symm.trans (Nat.mul_comm _ _)⟩
  let : Nonempty (orbit G B) := ⟨⟨B,mem_orbit_self B⟩⟩
  obtain ⟨C,fixed⟩ := solvable_coprime_fixed (X := orbit G B) g simpOrbit torsion
  obtain ⟨t,ht⟩ := C.property
  have translated : IsBlock G (C : Set X) := ht ▸ block.translate t
  have count : (C : Set X).ncard = B.ncard := by rw [← ht, Set.ncard_smul_set]
  have smallBlock : Nat.card (C : Set X) < Nat.card X := count.trans_lt (Set.ncard_lt_card proper)
  have copBlock : (Nat.card (C : Set X)).Coprime m := by
    change (C : Set X).ncard.Coprime m
    rw [count]
    exact coprime.coprime_dvd_left (block.ncard_dvd_card present)
  let : Nonempty (C : Set X) := Set.nonempty_coe_sort.mpr ((Set.ncard_pos (s := (C : Set X))).mp (by omega))
  let : IsPretransitive (stabilizer G (C : Set X)) (C : Set X) := ⟨fun x y => by
    have mem : (y : X) ∈ orbit (stabilizer G (C : Set X)) (x : X) := by
      rw [translated.orbit_stabilizer_eq x.property]
      exact y.property
    obtain ⟨s,hs⟩ := mem
    exact ⟨s,Subtype.ext hs⟩⟩
  let gC : stabilizer G (C : Set X) := ⟨g,congrArg Subtype.val fixed⟩
  obtain ⟨x,hx⟩ := solvable_coprime_fixed (X := (C : Set X)) gC copBlock
    (by apply Subtype.ext; exact torsion)
  exact ⟨x,congrArg Subtype.val hx⟩
termination_by Nat.card X
decreasing_by all_goals assumption

/-- In any transitive solvable action on a power of two points, every group
element has a cycle of power-of-two length. -/
theorem solvable_dyadic_period {G X : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    [MulAction G X] [IsPretransitive G X] [Finite X] [Nonempty X]
    (r : ℕ) (size : Nat.card X = 2^r) (g : G) :
    ∃ (x : X) (j : ℕ), IsPeriodicPt (MulAction.toPermHom G X g) (2^j) x := by
  obtain ⟨j,m,odd,order⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have torsion : (g^(2^j))^m = 1 := by rw [← pow_mul,← order,pow_orderOf_eq_one]
  have coprime : (Nat.card X).Coprime m := size ▸ odd.coprime_two_left.pow_left r
  obtain ⟨x,hx⟩ := solvable_coprime_fixed (X := X) (g^(2^j)) coprime torsion
  refine ⟨x,j,?_⟩
  change ((MulAction.toPermHom G X g : X → X)^[2^j]) x = x
  rw [← Equiv.Perm.coe_pow, ← map_pow]
  exact hx

/-- When the sheet count is a power of two and the matching group is solvable,
a Hamiltonian square of the tetrahedron lifts to a simple power-of-two cycle. -/
theorem two_power_solvable_cover {X : Type*} [Finite X] [Nonempty X] (p q r : Equiv.Perm X)
    (e : ℕ) (size : Nat.card X = 2^e) (solvable : Group.IsSolvable (Subgroup.closure ({p,q,r} : Set (Equiv.Perm X))))
    (connected : (SimpleGraph.fromRel (fun u v : Fin 4 × X =>
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨
    (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨
    (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2))).Connected) :
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ (SimpleGraph.fromRel (fun u v : Fin 4 × X =>
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨
    (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨
    (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2))) := by
  classical
  let K := SimpleGraph.fromRel (fun u v : Fin 4 × X =>
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨
    (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨
    (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2))
  let M := Subgroup.closure ({p,q,r} : Set (Equiv.Perm X))
  let : Group.IsSolvable M := solvable
  let : IsPretransitive M X := connected_transitive p q r connected
  let P : M := ⟨p, Subgroup.subset_closure (by simp)⟩
  let Q : M := ⟨q, Subgroup.subset_closure (by simp)⟩
  let step : Fin 4 → M := ![1,P,Q,1]
  let f (u : Fin 4 × X) := (u.1+1, step u.1 • u.2)
  let h : Equiv.Perm X := MulAction.toPermHom M X (Q*P)
  have lap (x : X) : f^[4] (0,x) = (0,h x) := by
    change ((0 : Fin 4),(1:M) • (Q • (P • ((1:M) • x)))) = (0,(Q*P) • x)
    simp only [one_smul,mul_smul]
  have laps (x : X) (t : ℕ) : f^[4*t] (0,x) = (0,(h : X → X)^[t] x) := by
    have semi : Semiconj (fun y : X => ((0 : Fin 4),y)) (h : X → X) (f^[4]) :=
      fun y => (lap y).symm
    rw [iterate_mul]
    exact ((semi.iterate_right t) x).symm
  have phase (x : X) (t : ℕ) : (f^[t] (0,x)).1 = (t : Fin 4) := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [iterate_succ_apply']
      change (f^[t] (0,x)).1+1 = _
      rw [ih, Nat.cast_succ]
  obtain ⟨x,j,hj⟩ := solvable_dyadic_period e size (Q*P)
  have per : IsPeriodicPt h (2^j) x := hj
  obtain ⟨d,_,hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp per.minimalPeriod_dvd
  have length : minimalPeriod f (0,x) = 4 * minimalPeriod h x := by
    apply Nat.dvd_antisymm
    · apply IsPeriodicPt.minimalPeriod_dvd
      change f^[4 * minimalPeriod h x] (0,x) = (0,x)
      simp [laps]
    · let t := minimalPeriod f (0,x)
      have closed : f^[t] (0,x) = (0,x) := iterate_minimalPeriod
      have div : 4 ∣ t := Fin.natCast_eq_zero.mp ((phase x t).symm.trans (congrArg Prod.fst closed))
      obtain ⟨a,ha⟩ := div
      rw [ha,laps] at closed
      have periodic : IsPeriodicPt h a x := congrArg Prod.snd closed
      change 4 * _ ∣ t
      rw [ha]
      exact Nat.mul_dvd_mul_left _ periodic.minimalPeriod_dvd
  have dyadic : minimalPeriod f (0,x) = 2^(2+d) := by rw [length,hd,pow_add]; rfl
  have adjacent (u : Fin 4 × X) : K.Adj u (f u) := by
    rcases u with ⟨i,y⟩
    fin_cases i
    · change K.Adj (0,y) (1,(1:M) • y)
      simp [K,SimpleGraph.fromRel]
    · change K.Adj (1,y) (2,P • y)
      simp [K,P,SimpleGraph.fromRel]
    · change K.Adj (2,y) (3,Q • y)
      simp [K,Q,SimpleGraph.fromRel]
    · change K.Adj (3,y) (0,(1:M) • y)
      simp [K,SimpleGraph.fromRel]
  have large : 3 ≤ minimalPeriod f (0,x) := by
    rw [dyadic]
    have : 4 ≤ 2^(2+d) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ 2+d)
    omega
  have lifted := orbit_cycle f (Function.Embedding.refl _) adjacent (0,x) large
  exact ⟨2+d,by omega,dyadic ▸ lifted⟩

end TetrahedralPrimeReduction

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H1_R1_H2_R1

/-- Composite degree outside the power-of-two solvable case, without a signed
affine orbit or an affine orbit with bijective nonidentity differences. -/
def H1 : Prop := ∀ (X : Type) [Fintype X] [Nonempty X] (p q r : Equiv.Perm X),
  ¬ (Fintype.card X).Prime →
  ¬ ((∃ s : ℕ, Fintype.card X = 2^s) ∧ Group.IsSolvable (Subgroup.closure ({p,q,r} : Set (Equiv.Perm X)))) →
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
    · by_cases twoCase : (∃ s : ℕ, Fintype.card X = 2^s) ∧ Group.IsSolvable (Subgroup.closure ({p,q,r} : Set (Equiv.Perm X)))
      · obtain ⟨⟨s,hs⟩,sol⟩ := twoCase
        exact TetrahedralPrimeReduction.two_power_solvable_cover p q r s
          (by simpa only [Nat.card_eq_fintype_card] using hs) sol connected
      · exact composite X p q r prime twoCase signed affine connected nonbipartite

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H1_R1_H2_R1
