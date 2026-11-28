import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H1_R1

/-!
# Composite tetrahedral covers

Chad Mazzola (@ubuwaits), using Codex. A normal solvable subgroup with
power-of-two sheet orbits permits lifting a simple dyadic quotient cycle.
This excludes commuting actions on such a quotient, including two-group
commutator subgroups. Each of the three Hamiltonian square returns also
has to avoid every power-of-two orbit in a counterexample.

The solvable fixed-point lemma and the abelian tetrahedron theorem are from
PR 7329. Related lifting results are the bipartite reduction in PR 6375 by
@mejiasd3v and Michael C. Burkhart's Cayley graph Lemma 1.3, arXiv:2611.05060.
-/

namespace TetrahedralNormalReduction

open Function MulAction SimpleGraph
open scoped Pointwise
open Fin.NatCast

/-- Adjoining one element to a solvable normal subgroup gives a solvable group. -/
theorem solvable_adjoin {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    [Group.IsSolvable N] (g : G) : Group.IsSolvable (N ⊔ Subgroup.zpowers g : Subgroup G) := by
  let L := N ⊔ Subgroup.zpowers g
  let q := QuotientGroup.mk' N
  let C := Subgroup.zpowers (q g)
  have into : L ≤ C.comap q := by
    apply sup_le
    · intro a ha
      change q a ∈ C
      rw [show q a = 1 from (QuotientGroup.eq_one_iff a).2 ha]
      exact C.one_mem
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_zpowers (q g))
  let f : L →* C := (q.comp L.subtype).codRestrict C (fun x => into x.property)
  let i : N →* L := Subgroup.inclusion le_sup_left
  let : Group.IsSolvable C := Group.isSolvable_of_comm (fun a b => mul_comm' a b)
  apply Group.isSolvable_of_ker_le_range i f
  intro x hx
  have trivial : q (x : G) = 1 := congrArg Subtype.val (show f x = 1 from hx)
  exact ⟨⟨x.val, (QuotientGroup.eq_one_iff x.val).mp trivial⟩, rfl⟩

/-- On a normal solvable subgroup orbit of size a power of two, any element
preserving that orbit has a point of power-of-two period. The ambient group
can be nonsolvable. -/
theorem period_on_normal_orbit {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [Finite X] (N : Subgroup G) [N.Normal] [Group.IsSolvable N] (g : G) (x : X)
    (stable : g • x ∈ orbit N x) (r : ℕ) (size : Nat.card (orbit N x) = 2^r) :
    ∃ y ∈ orbit N x, ∃ j : ℕ, IsPeriodicPt (MulAction.toPermHom G X g) (2^j) y := by
  classical
  let L := N ⊔ Subgroup.zpowers g
  have keep (a : G) (h : a • x ∈ orbit N x) : a ∈ stabilizer G (orbit N x) :=
    (smul_orbit_eq_orbit_smul N x a).trans (orbit_eq_iff.mpr h)
  have fixesBlock : L ≤ stabilizer G (orbit N x) :=
    sup_le (fun a ha => keep a ⟨⟨a, ha⟩, rfl⟩) (Subgroup.zpowers_le.mpr (keep g stable))
  have same : orbit L x = orbit N x := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact orbit_eq_iff.mp ((smul_orbit_eq_orbit_smul N x a.val).symm.trans
        (show a.val • orbit N x = orbit N x from fixesBlock a.property))
    · rintro ⟨a, rfl⟩
      exact ⟨Subgroup.inclusion (show N ≤ L from le_sup_left) a, rfl⟩
  let : Group.IsSolvable L := solvable_adjoin N g
  let : Nonempty (orbit L x) := ⟨⟨x, mem_orbit_self x⟩⟩
  let h : L := ⟨g, (show Subgroup.zpowers g ≤ L from le_sup_right) (Subgroup.mem_zpowers g)⟩
  obtain ⟨y, j, hj⟩ := TetrahedralPrimeReduction.solvable_dyadic_period
    (X := orbit L x) r (by rw [same]; exact size) h
  refine ⟨y.val, same ▸ y.property, j, ?_⟩
  change ((MulAction.toPermHom L (orbit L x) h : _ → _)^[2^j]) y = y at hj
  change ((MulAction.toPermHom G X g : X → X)^[2^j]) y.val = y.val
  rw [← Equiv.Perm.coe_pow, ← map_pow] at hj ⊢
  exact congrArg Subtype.val hj

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

/-- The distinct quotient vertices certify simplicity of a lifted periodic word. -/
private theorem lift_word {V M X Y : Type*} [Group M] [MulAction M X] [MulAction M Y]
    [Finite X] (H : SimpleGraph (V × X)) (π : X → Y) (onto : Surjective π)
    (equivariant : ∀ (g : M) (x : X), π (g • x) = g • π x) {k : ℕ} (hk : 2 ≤ k)
    (c : Fin (2^k) ↪ V × Y) (s : Fin (2^k) → M)
    (follows : ∀ i, s i • (c i).2 = (c (i+1)).2)
    (edges : ∀ i (x : X), H.Adj ((c i).1,x) ((c (i+1)).1, s i • x))
    (good : ∀ g : M, g • (c 0).2 = (c 0).2 →
      ∃ x : X, π x = (c 0).2 ∧ ∃ j : ℕ, IsPeriodicPt (toPermHom M X g) (2^j) x) :
    ∃ d : ℕ, k ≤ d ∧ 2^d ≤ 2^k * Nat.card {x : X // π x = (c 0).2} ∧
      cycleGraph (2^d) ⊑ H := by
  classical
  let n := 2^k
  have four : 4 ≤ n := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  let : NeZero n := ⟨by omega⟩
  let D := {z : Fin n × X // π z.2 = (c z.1).2}
  let step (z : D) : D := ⟨(z.val.1+1,s z.val.1 • z.val.2), by
    rw [equivariant,z.property]; exact follows z.val.1⟩
  let label : D ↪ V × X := ⟨fun z => ((c z.val.1).1, z.val.2), by
    intro a b equal
    have sheets := congrArg (fun z : V × X => z.2) equal
    have colors := congrArg (fun z : V × X => z.1) equal
    have phase : a.val.1 = b.val.1 := c.injective (Prod.ext colors
      (a.property.symm.trans ((congrArg π sheets).trans b.property)))
    exact Subtype.ext (Prod.ext phase sheets)⟩
  have adjacent (z : D) : H.Adj (label z) (label (step z)) := edges z.val.1 z.val.2
  let F := {x : X // π x = (c 0).2}
  let start (x : F) : D := ⟨(0,x.val),x.property⟩
  let walkProduct : ℕ → M := Nat.rec 1 fun i g => s (i : Fin n) * g
  have travel (x : F) (t : ℕ) :
      (step^[t] (start x)).val = ((t : Fin n),walkProduct t • x.val) := by
    induction t with
    | zero => simp [start,walkProduct]
    | succ t ih =>
      rw [iterate_succ_apply']
      change ((step^[t] (start x)).val.1+1, s (step^[t] (start x)).val.1 •
        (step^[t] (start x)).val.2) = _
      rw [ih,Nat.cast_succ]
      exact Prod.ext rfl (mul_smul _ _ _).symm
  let g := walkProduct n
  have lap (x : F) : (step^[n] (start x)).val = (0, g • x.val) := by
    simpa [g] using travel x n
  have stable : g • (c 0).2 = (c 0).2 := by
    obtain ⟨x,hx⟩ := onto (c 0).2
    let z : F := ⟨x,hx⟩
    have h := (step^[n] (start z)).property
    rw [lap z] at h
    simpa only [equivariant,z.property] using h
  let back (x : F) : F := ⟨g • x.val,
    (equivariant _ _).trans ((congrArg (fun y : Y => g • y) x.property).trans stable)⟩
  have action : Semiconj (fun x : F => x.val) back (MulAction.toPermHom M X g) := fun _ => rfl
  have turns : Semiconj start back (step^[n]) := fun x => Subtype.ext (lap x).symm
  obtain ⟨x,hx,j,periodic⟩ := good g stable
  let z : F := ⟨x,hx⟩
  have p : IsPeriodicPt back (2^j) z :=
    Subtype.ext (((action.iterate_right (2^j)) z).trans periodic)
  let t := minimalPeriod back z
  obtain ⟨e,_,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp p.minimalPeriod_dvd
  have closed : IsPeriodicPt step (n*t) (start z) := by
    change step^[n*t] (start z) = start z
    rw [iterate_mul, ← (turns.iterate_right t) z]
    exact congrArg start (show back^[t] z = z from iterate_minimalPeriod)
  obtain ⟨d,_,hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show minimalPeriod step (start z) ∣ 2^(k+e) by
      simpa only [n,t,he,pow_add] using closed.minimalPeriod_dvd)
  have pos : 0 < minimalPeriod step (start z) := hd ▸ Nat.two_pow_pos d
  have phaseZero : ((minimalPeriod step (start z) : ℕ) : Fin n) = 0 := by
    have eq := congrArg Prod.fst (travel z (minimalPeriod step (start z)))
    rw [iterate_minimalPeriod] at eq
    exact eq.symm
  have lower : n ≤ 2^d := hd ▸ Nat.le_of_dvd pos (Fin.natCast_eq_zero.mp phaseZero)
  have small : t ≤ Nat.card F := by
    let := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact minimalPeriod_le_card
  have bound : 2^d ≤ n * Nat.card F := by
    rw [← hd]
    have tpos : 0 < t := by change 0 < minimalPeriod back z; rw [he]; positivity
    exact (Nat.le_of_dvd (Nat.mul_pos (by omega) tpos)
      closed.minimalPeriod_dvd).trans (Nat.mul_le_mul_left _ small)
  refine ⟨d,(Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp lower,bound,?_⟩
  exact hd ▸ cycle_of_period step label adjacent (start z) (by rw [hd]; omega)

/-- Transport a dyadic cycle through an equivariant quotient of tetrahedral sheets. -/
theorem tetra_lift {M X Y : Type} [Group M] [MulAction M X] [MulAction M Y]
    [Finite X] (a b c : M) (π : X → Y) (onto : Surjective π)
    (eqv : ∀ (g : M) (x : X), π (g • x) = g • π x)
    (good : ∀ (y : Y) (g : M), g • y = y →
      ∃ x : X, π x = y ∧ ∃ j : ℕ, IsPeriodicPt (toPermHom M X g) (2^j) x) :
  let graph (Z : Type) [MulAction M Z] := SimpleGraph.fromRel (fun u v : Fin 4 × Z =>
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨ (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = a • u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = b • u.2) ∨ (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = c • u.2))
  ∀ (k : ℕ), 2 ≤ k → cycleGraph (2^k) ⊑ graph Y →
    ∃ d : ℕ, k ≤ d ∧ cycleGraph (2^d) ⊑ graph X := by
  classical
  let graph (Z : Type) [MulAction M Z] := SimpleGraph.fromRel (fun u v : Fin 4 × Z =>
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨ (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = a • u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = b • u.2) ∨ (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = c • u.2))
  change ∀ (k : ℕ), 2 ≤ k → cycleGraph (2^k) ⊑ graph Y →
    ∃ d : ℕ, k ≤ d ∧ cycleGraph (2^d) ⊑ graph X
  intro k hk h
  let edge (i j : Fin 4) : M := ![![1,1,1,1], ![1,1,a,c⁻¹], ![1,a⁻¹,1,b], ![1,c,b⁻¹,1]] i j
  have edge_spec (Z : Type) [MulAction M Z] (i j : Fin 4) (x y : Z) :
      (graph Z).Adj (i,x) (j,y) ↔ i ≠ j ∧ edge i j • x = y := by
    fin_cases i <;> fin_cases j <;> simp [graph,edge,eq_comm] <;>
      exact ⟨fun h => by rw [h, inv_smul_smul], fun h => by rw [h, smul_inv_smul]⟩
  obtain ⟨path⟩ := h
  have side (i : Fin (2^k)) : (graph Y).Adj (path i) (path (i+1)) := by
    apply path.toHom.map_rel'
    apply cycleGraph_adj'.mpr
    right
    simp
    have four : 4 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    omega
  have follow (i : Fin (2^k)) := (edge_spec Y _ _ _ _).1 (side i)
  obtain ⟨d,lo,_,cyc⟩ := lift_word (graph X) π onto eqv hk ⟨path,path.injective⟩
    (fun i => edge (path i).1 (path (i+1)).1) (fun i => (follow i).2)
    (fun i x => (edge_spec X _ _ _ _).2 ⟨(follow i).1,rfl⟩) (good (path 0).2)
  exact ⟨d,lo,cyc⟩

/-- A commuting quotient of the sheet action supplies a 4-, 8- or 16-cycle.
A normal solvable commutator with dyadic orbits lets one of these lift. -/
theorem commutator_orbits {M X : Type} [Group M] [Finite M] [MulAction M X]
    [Finite X] [Nonempty X] (a b c : M) (sol : Group.IsSolvable (_root_.commutator M))
    (sizes : ∀ x : X, ∃ r : ℕ, Nat.card (orbit (_root_.commutator M) x) = 2^r) :
    ∃ d : ℕ, 2 ≤ d ∧ cycleGraph (2^d) ⊑ SimpleGraph.fromRel (fun u v : Fin 4 × X =>
      (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨ (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = a • u.2) ∨
      (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = b • u.2) ∨ (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = c • u.2)) := by
  classical
  let N := _root_.commutator M
  let : Group.IsSolvable N := sol
  let Y := Set.range (orbit N : X → Set X)
  let π (x : X) : Y := ⟨orbit N x, ⟨x,rfl⟩⟩
  have onto : Surjective π := fun ⟨_,x,rfl⟩ => ⟨x,rfl⟩
  have same (x y : X) : π x = π y ↔ x ∈ orbit N y := Subtype.ext_iff.trans orbit_eq_iff
  let : MulAction M Y := {
    smul := fun g z => ⟨g • z.val, by
      obtain ⟨x,hx⟩ := z.property
      exact ⟨g • x, by rw [← hx,smul_orbit_eq_orbit_smul]⟩⟩
    one_smul := fun z => Subtype.ext (one_smul _ _)
    mul_smul := fun g h z => Subtype.ext (mul_smul _ _ _) }
  let : Nonempty Y := Nonempty.map π (inferInstance : Nonempty X)
  have equivariant (g : M) (x : X) : π (g • x) = g • π x :=
    Subtype.ext (smul_orbit_eq_orbit_smul N x g).symm
  let act := toPermHom M Y
  have trivial : N ≤ act.ker := by
    intro g hg
    apply Equiv.Perm.ext
    intro y
    obtain ⟨x,rfl⟩ := onto y
    exact (equivariant g x).symm.trans ((same _ _).2 ⟨⟨g,hg⟩,rfl⟩)
  let q := QuotientGroup.lift N act trivial
  let : IsMulCommutative (M ⧸ N) := Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  have comm (g h : M) : Commute (act g) (act h) :=
    (show Commute ((QuotientGroup.mk' N) g) ((QuotientGroup.mk' N) h) from mul_comm' _ _).map q
  let graph (Z : Type) [MulAction M Z] := SimpleGraph.fromRel (fun u v : Fin 4 × Z =>
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨ (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = a • u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = b • u.2) ∨ (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = c • u.2))
  let edge (i j : Fin 4) : M := ![![1,1,1,1], ![1,1,a,c⁻¹], ![1,a⁻¹,1,b], ![1,c,b⁻¹,1]] i j
  have edge_spec (Z : Type) [MulAction M Z] (i j : Fin 4) (x y : Z) :
      (graph Z).Adj (i,x) (j,y) ↔ i ≠ j ∧ edge i j • x = y := by
    fin_cases i <;> fin_cases j <;> simp [graph,edge,eq_comm] <;>
      exact ⟨fun h => by rw [h, inv_smul_smul], fun h => by rw [h, smul_inv_smul]⟩
  obtain ⟨A, _, f, u,v,w,shifts⟩ := TetrahedralReduction.commutingOrbit
    _ _ _ (comm a b) (comm b c) (comm c a)
  let e : Fin 4 × A ↪ Fin 4 × Y := Function.Embedding.prodMap (Function.Embedding.refl _) f
  have short : cycleGraph 4 ⊑ graph Y ∨ cycleGraph 8 ⊑ graph Y ∨ cycleGraph 16 ⊑ graph Y := by
    apply TetrahedralReduction.abelianTetrahedron _ e u v w
    · intro j hj x
      change (graph Y).Adj (0,f x) (j,f x)
      exact (edge_spec Y _ _ _ _).2 ⟨Ne.symm hj, by fin_cases j <;> simp [edge]⟩
    · intro x
      exact (edge_spec Y 1 2 _ _).2 ⟨by decide,(shifts x).1⟩
    · intro x
      exact (edge_spec Y 2 3 _ _).2 ⟨by decide,(shifts x).2.1⟩
    · intro x
      exact (edge_spec Y 3 1 _ _).2 ⟨by decide,(shifts x).2.2⟩
  have lift {k : ℕ} (hk : 2 ≤ k) (h : cycleGraph (2^k) ⊑ graph Y) :
      ∃ d : ℕ, 2 ≤ d ∧ cycleGraph (2^d) ⊑ graph X := by
    have good (y : Y) (g : M) (stable : g • y = y) :
        ∃ x : X, π x = y ∧ ∃ j : ℕ, IsPeriodicPt (toPermHom M X g) (2^j) x := by
      obtain ⟨x,hx⟩ := onto y
      have fixedOrbit : g • x ∈ orbit N x := (same _ _).mp
        ((equivariant g x).trans ((congrArg (fun z : Y => g • z) hx).trans (stable.trans hx.symm)))
      obtain ⟨r,size⟩ := sizes x
      obtain ⟨z,hz,j,hj⟩ := period_on_normal_orbit N g x fixedOrbit r size
      exact ⟨z,((same _ _).mpr hz).trans hx,j,hj⟩
    obtain ⟨d,lo,cyc⟩ := tetra_lift a b c π onto equivariant good k hk h
    exact ⟨d,hk.trans lo,cyc⟩
  rcases short with h | h | h
  · exact lift (k := 2) (by decide) h
  · exact lift (k := 3) (by decide) h
  · exact lift (k := 4) (by decide) h

/-- A dyadic orbit of a Hamiltonian return gives a simple power cycle. -/
private theorem square_period {X V : Type} (H : SimpleGraph V)
    (label : Fin 4 × X ↪ V) (p q : Equiv.Perm X)
    (first : ∀ y : X, H.Adj (label (0,y)) (label (1,y)))
    (second : ∀ y : X, H.Adj (label (1,y)) (label (2,p y)))
    (third : ∀ y : X, H.Adj (label (2,y)) (label (3,q y)))
    (fourth : ∀ y : X, H.Adj (label (3,y)) (label (0,y)))
    (x : X) (j : ℕ) (periodic : IsPeriodicPt (q*p) (2^j) x) :
    ∃ d : ℕ, 2 ≤ d ∧ cycleGraph (2^d) ⊑ H := by
  let step : Fin 4 → Equiv.Perm X := ![1,p,q,1]
  let f (u : Fin 4 × X) := (u.1+1, step u.1 u.2)
  have lap (y : X) : f^[4] (0,y) = (0,(q*p) y) := rfl
  have turns : Semiconj (fun y : X => ((0 : Fin 4),y)) (q*p) (f^[4]) := fun y => (lap y).symm
  have closed : IsPeriodicPt f (2^(2+j)) (0,x) := by
    change f^[2^(2+j)] (0,x) = (0,x)
    rw [pow_add,show 2^2 = 4 from rfl,iterate_mul,← (turns.iterate_right _) x]
    exact congrArg (fun y : X => ((0 : Fin 4),y)) periodic
  obtain ⟨d,_,hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp closed.minimalPeriod_dvd
  have phase (t : ℕ) : (f^[t] (0,x)).1 = (t : Fin 4) := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [iterate_succ_apply']
      change (f^[t] (0,x)).1+1 = _
      rw [ih,Nat.cast_succ]
  have div : 4 ∣ minimalPeriod f (0,x) := Fin.natCast_eq_zero.mp
    ((phase _).symm.trans (congrArg Prod.fst (show f^[minimalPeriod f (0,x)] (0,x) = (0,x) from iterate_minimalPeriod)))
  have four : 4 ≤ 2^d := Nat.le_of_dvd (Nat.two_pow_pos d) (hd ▸ div)
  have adj (z : Fin 4 × X) : H.Adj (label z) (label (f z)) := by
    rcases z with ⟨i,y⟩
    fin_cases i
    · exact first y
    · exact second y
    · exact third y
    · exact fourth y
  exact ⟨d,(Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp four,
    hd ▸ cycle_of_period f label adj (0,x) (by rw [hd]; omega)⟩

/-- The three Hamiltonian squares have returns qp, rq and pr. -/
theorem square_returns {X : Type} (p q r : Equiv.Perm X)
    (good : ∃ h ∈ ({q*p,r*q,p*r} : Set (Equiv.Perm X)), ∃ x : X, ∃ j : ℕ, IsPeriodicPt h (2^j) x) :
    ∃ d : ℕ, 2 ≤ d ∧ cycleGraph (2^d) ⊑ SimpleGraph.fromRel (fun u v : Fin 4 × X =>
      (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨ (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
      (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨ (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2)) := by
  let H := SimpleGraph.fromRel (fun u v : Fin 4 × X =>
    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨ (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨
    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨ (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2))
  obtain ⟨h,hh,x,j,hj⟩ := good
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hh
  rcases hh with h | h | h <;> subst_vars
  · exact square_period H (Function.Embedding.refl _) p q
      (fun y => by simp [H]) (fun y => by simp [H]) (fun y => by simp [H]) (fun y => by simp [H]) x j hj
  · let e : Fin 4 ↪ Fin 4 := ⟨![0,2,3,1], by decide⟩
    let label := Function.Embedding.prodMap e (Function.Embedding.refl X)
    exact square_period H label q r
      (fun y => by simp [H,label,e]) (fun y => by simp [H,label,e])
      (fun y => by simp [H,label,e]) (fun y => by simp [H,label,e]) x j hj
  · let e : Fin 4 ↪ Fin 4 := ⟨![0,3,1,2], by decide⟩
    let label := Function.Embedding.prodMap e (Function.Embedding.refl X)
    exact square_period H label r p
      (fun y => by simp [H,label,e]) (fun y => by simp [H,label,e])
      (fun y => by simp [H,label,e]) (fun y => by simp [H,label,e]) x j hj

/-- Left multiplication in a quotient by a two-group admits a dyadic return
above every sheet fixed by the quotient return. -/
theorem regular_quotient {M : Type} [Group M] [Finite M] (a b c : M)
    (N : Subgroup M) [N.Normal] (two : IsPGroup 2 N) :
    let graph {Z : Type} [Group Z] (u v w : Z) := SimpleGraph.fromRel (fun h k : Fin 4 × Z =>
      (h.1 = 0 ∧ k.1 ≠ 0 ∧ k.2 = h.2) ∨ (h.1 = 1 ∧ k.1 = 2 ∧ k.2 = u*h.2) ∨
      (h.1 = 2 ∧ k.1 = 3 ∧ k.2 = v*h.2) ∨ (h.1 = 3 ∧ k.1 = 1 ∧ k.2 = w*h.2))
    let q := QuotientGroup.mk' N
    ∀ k : ℕ, 2 ≤ k → cycleGraph (2^k) ⊑ graph (q a) (q b) (q c) →
      ∃ d : ℕ, k ≤ d ∧ cycleGraph (2^d) ⊑ graph a b c := by
  let q := QuotientGroup.mk' N
  have eqv (g x : M) : q (g • x) = g • q x := rfl
  have act (g : M) (y : M ⧸ N) : g • y = q g * y := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N y
    rfl
  have good (y : M ⧸ N) (g : M) (h : g • y = y) :
      ∃ x : M, q x = y ∧ ∃ j : ℕ, IsPeriodicPt (toPermHom M M g) (2^j) x := by
    have qone : q g = 1 := mul_right_cancel (b := y) ((act g y).symm.trans (h.trans (one_mul y).symm))
    let n : N := ⟨g,(QuotientGroup.eq_one_iff g).mp qone⟩
    obtain ⟨j,hj⟩ := two n
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective N y
    refine ⟨x,hx,j,?_⟩
    have kill : g^(2^j) = 1 := congrArg Subtype.val hj
    change ((toPermHom M M g : M → M)^[2^j]) x = x
    rw [← Equiv.Perm.coe_pow, ← map_pow, kill, map_one]
    rfl
  intro graph quo k hk cyc
  apply tetra_lift a b c q (QuotientGroup.mk'_surjective N) eqv good k hk
  simp only [act]
  exact cyc

/-- An intertwining map on sheets maps the edges of the two covers. -/
theorem map_edges {X Y : Type} (p q r : X → X) (s t u : Y → Y) (f : X → Y)
    (hp : ∀ x, f (p x) = s (f x)) (hq : ∀ x, f (q x) = t (f x)) (hr : ∀ x, f (r x) = u (f x)) :
    let rel {Z : Type} (a b c : Z → Z) (v w : Fin 4 × Z) :=
      (v.1 = 0 ∧ w.1 ≠ 0 ∧ w.2 = v.2) ∨ (v.1 = 1 ∧ w.1 = 2 ∧ w.2 = a v.2) ∨
      (v.1 = 2 ∧ w.1 = 3 ∧ w.2 = b v.2) ∨ (v.1 = 3 ∧ w.1 = 1 ∧ w.2 = c v.2)
    ∀ {v w}, (SimpleGraph.fromRel (rel p q r)).Adj v w →
      (SimpleGraph.fromRel (rel s t u)).Adj (v.1,f v.2) (w.1,f w.2) := by
  intro rel v w h
  have directed {v w : Fin 4 × X} (h : rel p q r v w) :
      (SimpleGraph.fromRel (rel s t u)).Adj (v.1,f v.2) (w.1,f w.2) := by
    obtain ⟨i,x⟩ := v
    obtain ⟨j,y⟩ := w
    rcases h with h | h | h | h
    · obtain ⟨rfl,hj,rfl⟩ := h
      simp [rel,hj,Ne.symm hj]
    · obtain ⟨rfl,rfl,rfl⟩ := h
      simp [rel,hp]
    · obtain ⟨rfl,rfl,rfl⟩ := h
      simp [rel,hq]
    · obtain ⟨rfl,rfl,rfl⟩ := h
      simp [rel,hr]
  exact h.2.elim directed (fun edge => (directed edge).symm)

theorem generated_transitive {X : Type*} [Finite X] (p q r : Equiv.Perm X)
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


end TetrahedralNormalReduction

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H1_R1_H2_R1

open SimpleGraph Function MulAction TetrahedralNormalReduction

/-- The remaining regular group covers have trivial normal two-core. -/
def H1 : Prop := ∀ (A : Type) [Group A] [Fintype A] (a b c : A),
  (∀ N : Subgroup A, N.Normal → IsPGroup 2 N → N = ⊥) →
  ¬ IsPGroup 2 (_root_.commutator A) →
  (∀ w ∈ ({b*a,c*b,a*c} : Set A), ∀ j : ℕ, w^(2^j) ≠ 1) →
  ¬ (∃ (B : Type) (_ : AddCommGroup B) (f : B ↪ A) (s t u : Bool) (i j l : B),
    ∀ x, a*f x = f ((if s then -x else x)+i) ∧ b*f x = f ((if t then -x else x)+j) ∧
      c*f x = f ((if u then -x else x)+l)) →
  ¬ (∃ (B S : Type) (_ : AddCommGroup B) (_ : Group S) (_ : DistribMulAction S B)
    (f : B ↪ A) (P Q R : S) (i j l : B), (∀ g : S, g ≠ 1 → Bijective (fun x : B => x - g • x)) ∧
    ∀ x, a*f x = f (P • x+i) ∧ b*f x = f (Q • x+j) ∧ c*f x = f (R • x+l)) →
  let K := SimpleGraph.fromRel (fun u v : Fin 4 × A =>
    (u.1=0 ∧ v.1≠0 ∧ v.2=u.2) ∨ (u.1=1 ∧ v.1=2 ∧ v.2=a*u.2) ∨
    (u.1=2 ∧ v.1=3 ∧ v.2=b*u.2) ∨ (u.1=3 ∧ v.1=1 ∧ v.2=c*u.2))
  K.Connected → ¬ K.IsBipartite → ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ K

/-- In the nonregular case a sheet has a nonidentity stabilizer. A solvable
commutator must also have an orbit of nondyadic size. -/
def H2 : Prop := ∀ (X : Type) [Fintype X] [Nonempty X] (p q r : Equiv.Perm X),
  let M := Subgroup.closure ({p,q,r} : Set (Equiv.Perm X))
  ¬ (Fintype.card X).Prime →
  ¬ ((∃ s : ℕ, Fintype.card X = 2^s) ∧ Group.IsSolvable M) →
  (∃ (g : M) (x : X), g • x = x ∧ g ≠ 1) →
  ¬ (Group.IsSolvable (_root_.commutator M) ∧
    ∀ x : X, ∃ j : ℕ, Nat.card (MulAction.orbit (_root_.commutator M) x) = 2^j) →
  (∀ h ∈ ({q*p,r*q,p*r} : Set (Equiv.Perm X)), ∀ (x : X) (j : ℕ), ¬ IsPeriodicPt h (2^j) x) →
  ¬ (∃ (B : Type) (_ : AddCommGroup B) (f : B ↪ X) (s t u : Bool) (i j l : B),
    ∀ x, p (f x) = f ((if s then -x else x)+i) ∧ q (f x) = f ((if t then -x else x)+j) ∧
      r (f x) = f ((if u then -x else x)+l)) →
  ¬ (∃ (B S : Type) (_ : AddCommGroup B) (_ : Group S) (_ : DistribMulAction S B)
    (f : B ↪ X) (P Q R : S) (i j l : B), (∀ g : S, g ≠ 1 → Bijective (fun x : B => x - g • x)) ∧
    ∀ x, p (f x) = f (P • x+i) ∧ q (f x) = f (Q • x+j) ∧ r (f x) = f (R • x+l)) →
  let K := SimpleGraph.fromRel (fun u v : Fin 4 × X =>
    (u.1=0 ∧ v.1≠0 ∧ v.2=u.2) ∨ (u.1=1 ∧ v.1=2 ∧ v.2=p u.2) ∨
    (u.1=2 ∧ v.1=3 ∧ v.2=q u.2) ∨ (u.1=3 ∧ v.1=1 ∧ v.2=r u.2))
  K.Connected → ¬ K.IsBipartite → ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ K

/-- Successive normal two-group quotients decrease the group order. A quotient
of prime order is abelian and is already covered by the commutator test. -/
theorem regular_descent (last : H1) (A : Type) [Group A] [Fintype A] (a b c : A) :
  let K := SimpleGraph.fromRel (fun u v : Fin 4 × A =>
    (u.1=0 ∧ v.1≠0 ∧ v.2=u.2) ∨ (u.1=1 ∧ v.1=2 ∧ v.2=a*u.2) ∨
    (u.1=2 ∧ v.1=3 ∧ v.2=b*u.2) ∨ (u.1=3 ∧ v.1=1 ∧ v.2=c*u.2))
  K.Connected → ¬ K.IsBipartite → ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ K := by
  classical
  let graph {Z : Type} [Group Z] (u v w : Z) := SimpleGraph.fromRel (fun h k : Fin 4 × Z =>
    (h.1=0 ∧ k.1≠0 ∧ k.2=h.2) ∨ (h.1=1 ∧ k.1=2 ∧ k.2=u*h.2) ∨
    (h.1=2 ∧ k.1=3 ∧ k.2=v*h.2) ∨ (h.1=3 ∧ k.1=1 ∧ k.2=w*h.2))
  change (graph a b c).Connected → ¬ (graph a b c).IsBipartite →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ graph a b c
  suffices allGroups : ∀ n : ℕ, ∀ (A : Type) [Group A] [Fintype A] (a b c : A),
      Nat.card A = n → (graph a b c).Connected → ¬ (graph a b c).IsBipartite →
      ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ graph a b c from
    allGroups (Nat.card A) A a b c rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A group fin a b c card connected nonbip
    by_cases core : ∀ N : Subgroup A, N.Normal → IsPGroup 2 N → N = ⊥
    · by_cases two : IsPGroup 2 (_root_.commutator A)
      · let : Group.IsNilpotent (_root_.commutator A) := two.isNilpotent
        exact commutator_orbits (X := A) a b c inferInstance (fun x => two.card_orbit x)
      have square (w : A) (hw : w ∈ ({b*a,c*b,a*c} : Set A)) (j : ℕ) (hj : w^(2^j)=1) :
          ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ graph a b c := by
        let L := toPermHom A A
        apply square_returns (L a) (L b) (L c)
        refine ⟨L w,?_,1,j,?_⟩
        · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hw ⊢
          rcases hw with h | h | h <;> rw [h,map_mul] <;> simp
        · change ((L w : A → A)^[2^j]) 1 = 1
          rw [← Equiv.Perm.coe_pow, ← L.map_pow, hj,L.map_one]
          rfl
      by_cases bad : ∀ w ∈ ({b*a,c*b,a*c} : Set A), ∀ j : ℕ, w^(2^j) ≠ 1
      · have short (h : cycleGraph 4 ⊑ graph a b c ∨ cycleGraph 8 ⊑ graph a b c ∨
            cycleGraph 16 ⊑ graph a b c) : ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ graph a b c := by
          rcases h with h | h | h
          · exact ⟨2,by decide,h⟩
          · exact ⟨3,by decide,h⟩
          · exact ⟨4,by decide,h⟩
        by_cases signed : ∃ (B : Type) (_ : AddCommGroup B) (f : B ↪ A) (s t u : Bool) (i j l : B),
    ∀ x, a*f x = f ((if s then -x else x)+i) ∧ b*f x = f ((if t then -x else x)+j) ∧
      c*f x = f ((if u then -x else x)+l)
        · obtain ⟨B,inst,f,s,t,u,i,j,l,shifts⟩ := signed
          let e := Function.Embedding.prodMap (Function.Embedding.refl (Fin 4)) f
          apply short
          apply TetrahedralReduction.affineTetrahedron (graph a b c) e s t u i j l
          · intro k hk x
            simp [graph,e,hk,Ne.symm hk]
          · intro x
            change (graph a b c).Adj (1,f x) (2,f ((if s then -x else x)+i))
            rw [← (shifts x).1]
            simp [graph]
          · intro x
            change (graph a b c).Adj (2,f x) (3,f ((if t then -x else x)+j))
            rw [← (shifts x).2.1]
            simp [graph]
          · intro x
            change (graph a b c).Adj (3,f x) (1,f ((if u then -x else x)+l))
            rw [← (shifts x).2.2]
            simp [graph]
        by_cases affine : ∃ (B S : Type) (_ : AddCommGroup B) (_ : Group S) (_ : DistribMulAction S B)
    (f : B ↪ A) (P Q R : S) (i j l : B), (∀ g : S, g ≠ 1 → Bijective (fun x : B => x - g • x)) ∧
    ∀ x, a*f x = f (P • x+i) ∧ b*f x = f (Q • x+j) ∧ c*f x = f (R • x+l)
        · obtain ⟨B,S,iB,iS,act,f,P,Q,R,i,j,l,regular,shifts⟩ := affine
          let e := Function.Embedding.prodMap (Function.Embedding.refl (Fin 4)) f
          apply short
          apply TetrahedralPrimeReduction.fixed_point_free_affine_short (graph a b c) e regular P Q R i j l
          · intro k hk x
            simp [graph,e,hk,Ne.symm hk]
          · intro x
            change (graph a b c).Adj (1,f x) (2,f (P • x+i))
            rw [← (shifts x).1]
            simp [graph]
          · intro x
            change (graph a b c).Adj (2,f x) (3,f (Q • x+j))
            rw [← (shifts x).2.1]
            simp [graph]
          · intro x
            change (graph a b c).Adj (3,f x) (1,f (R • x+l))
            rw [← (shifts x).2.2]
            simp [graph]
        exact last A a b c core two bad signed affine connected nonbip
      · push Not at bad
        obtain ⟨w,hw,j,hj⟩ := bad
        exact square w hw j hj
    · push Not at core
      obtain ⟨N,normal,two,nontrivial⟩ := core
      let : N.Normal := normal
      let q := QuotientGroup.mk' N
      let f : graph a b c →g graph (q a) (q b) (q c) := ⟨fun z => (z.1,q z.2), fun edge =>
        map_edges (a*·) (b*·) (c*·) (q a*·) (q b*·) (q c*·) q
          (map_mul q a) (map_mul q b) (map_mul q c) edge⟩
      have surj : Surjective f := by
        rintro ⟨i,y⟩
        obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N y
        exact ⟨(i,x),rfl⟩
      have less : Nat.card (A ⧸ N) < n := by
        rw [← card,Subgroup.card_eq_card_quotient_mul_card_subgroup N]
        have pos : 0 < Nat.card (A ⧸ N) := Nat.card_pos
        simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left
          (N.one_lt_card_iff_ne_bot.mpr nontrivial) pos
      obtain ⟨k,hk,cyc⟩ := ih _ less (A ⧸ N) (q a) (q b) (q c) rfl
        (connected.map f surj) (fun color => nonbip (SimpleGraph.Colorable.of_hom f color))
      obtain ⟨j,lo,up⟩ := regular_quotient a b c N two k hk cyc
      exact ⟨j,hk.trans lo,up⟩

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H1_R1.H2 := by
  intro regular nonregular X fin nonempty p q r composite noTwo noSigned noAffine
  classical
  let graph {Z : Type} (s t u : Z → Z) := SimpleGraph.fromRel (fun h k : Fin 4 × Z =>
    (h.1=0 ∧ k.1≠0 ∧ k.2=h.2) ∨ (h.1=1 ∧ k.1=2 ∧ k.2=s h.2) ∨
    (h.1=2 ∧ k.1=3 ∧ k.2=t h.2) ∨ (h.1=3 ∧ k.1=1 ∧ k.2=u h.2))
  let K := graph p q r
  change K.Connected → ¬ K.IsBipartite → ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ K
  intro connected nonbip
  by_cases square : ∃ h ∈ ({q*p,r*q,p*r} : Set (Equiv.Perm X)),
      ∃ (x : X) (j : ℕ), IsPeriodicPt h (2^j) x
  · exact square_returns p q r square
  let M := Subgroup.closure ({p,q,r} : Set (Equiv.Perm X))
  let P : M := ⟨p,Subgroup.subset_closure (by simp)⟩
  let Q : M := ⟨q,Subgroup.subset_closure (by simp)⟩
  let R : M := ⟨r,Subgroup.subset_closure (by simp)⟩
  by_cases through : Group.IsSolvable (_root_.commutator M) ∧
      ∀ x : X, ∃ j : ℕ, Nat.card (orbit (_root_.commutator M) x) = 2^j
  · exact commutator_orbits P Q R through.1 through.2
  by_cases free : ∀ (g : M) (x : X), g • x = x → g = 1
  · let : IsPretransitive M X := generated_transitive p q r connected
    let x₀ := Classical.choice nonempty
    let ev (g : M) := g • x₀
    have inj : Injective ev := by
      intro a b same
      have h : a⁻¹*b = 1 := free _ x₀ (by
        change a • x₀ = b • x₀ at same
        rw [mul_smul,← same,inv_smul_smul])
      calc a = a*1 := (mul_one a).symm
           _ = a*(a⁻¹*b) := congrArg (a*·) h.symm
           _ = b := by simp
    let e := Equiv.ofBijective ev ⟨inj,fun x => exists_smul_eq M x₀ x⟩
    have fwd (g h : M) : e (g*h) = g • e h := by
      change (g*h) • x₀ = g • h • x₀
      exact mul_smul g h x₀
    have bwd (g : M) (x : X) : e.symm (g • x) = g * e.symm x := by
      apply e.injective
      rw [e.apply_symm_apply,fwd,e.apply_symm_apply]
    let C := graph (P*·) (Q*·) (R*·)
    let f : C →g K := ⟨fun z => (z.1,e z.2), fun edge =>
      map_edges (P*·) (Q*·) (R*·) p q r e (fwd P) (fwd Q) (fwd R) edge⟩
    let back : K →g C := ⟨fun z => (z.1,e.symm z.2), fun edge =>
      map_edges p q r (P*·) (Q*·) (R*·) e.symm (bwd P) (bwd Q) (bwd R) edge⟩
    have onto : Surjective back := by
      rintro ⟨i,x⟩
      exact ⟨(i,e x),Prod.ext rfl (e.symm_apply_apply x)⟩
    have inject : Injective f := by
      intro z w h
      have he : (z.1,e z.2) = (w.1,e w.2) := h
      exact Prod.ext (congrArg (fun t : Fin 4 × X => t.1) he)
        (e.injective (congrArg (fun t : Fin 4 × X => t.2) he))
    obtain ⟨k,hk,cyc⟩ := regular_descent regular M P Q R (connected.map back onto)
      (fun color => nonbip (SimpleGraph.Colorable.of_hom back color))
    exact ⟨k,hk,cyc.trans ⟨⟨f,inject⟩⟩⟩
  · push Not at free
    exact nonregular X p q r composite noTwo free through
      (fun h hh x j periodic => square ⟨h,hh,x,j,periodic⟩) noSigned noAffine connected nonbip

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H1_R1_H2_R1
