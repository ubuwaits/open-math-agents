import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H1_R1

/-!
# Normal subgroups and lifts of power-of-two cycles

Chad Mazzola (@ubuwaits), using Codex.
The solvable-action fixed-point lemma is from PR 7329 of lefttosolve2/open-math-agents.
Related cases include the bipartite descent in PR 6375 by @mejiasd3v and Lemma 1.3
for Cayley graphs in Michael C. Burkhart, arXiv:2611.05060.
-/

namespace Erdos64NormalCovers

open Function MulAction SimpleGraph
open scoped Pointwise

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

section Covers

open Fin.NatCast

/-- Over an oriented edge from `v` to `w`, its group label transports the sheet.
The inverse condition makes the resulting graph undirected. -/
def voltageGraph {V M : Type*} [Group M] (base : SimpleGraph V) (edge : V → V → M)
    (reverse : ∀ {v w}, base.Adj v w → edge w v = (edge v w)⁻¹)
    (X : Type*) [MulAction M X] : SimpleGraph (V × X) where
  Adj u v := base.Adj u.1 v.1 ∧ edge u.1 v.1 • u.2 = v.2
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, by rw [reverse h.1, ← h.2, inv_smul_smul]⟩⟩
  loopless := ⟨fun _ h => base.loopless.irrefl _ h.1⟩

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

/-- A simple dyadic cycle in the quotient lifts if its return on the chosen
fiber has a dyadic orbit. The length upstairs is at most the length downstairs
times the size of that fiber. -/
theorem lift_cycle {V M X Y : Type*} [Group M] [MulAction M X] [MulAction M Y]
    [Finite X] (base : SimpleGraph V) (edge : V → V → M)
    (reverse : ∀ {v w}, base.Adj v w → edge w v = (edge v w)⁻¹)
    (π : X → Y) (onto : Surjective π) (equivariant : ∀ (g : M) (x : X), π (g • x) = g • π x)
    {k : ℕ} (hk : 2 ≤ k)
    (c : (cycleGraph (2^k)).Copy (voltageGraph base edge reverse Y))
    (good : ∀ g : M, g • (c 0).2 = (c 0).2 →
      ∃ x : X, π x = (c 0).2 ∧ ∃ j : ℕ, IsPeriodicPt (MulAction.toPermHom M X g) (2^j) x) :
    ∃ d : ℕ, k ≤ d ∧ 2^d ≤ 2^k * Nat.card {x : X // π x = (c 0).2} ∧
      cycleGraph (2^d) ⊑ voltageGraph base edge reverse X := by
  classical
  let n := 2^k
  have four : 4 ≤ n := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  let : NeZero n := ⟨by omega⟩
  let s (i : Fin n) := edge (c i).1 (c (i+1)).1
  have side (i : Fin n) : (voltageGraph base edge reverse Y).Adj (c i) (c (i+1)) := by
    apply c.toHom.map_rel'
    apply cycleGraph_adj'.mpr
    right
    simp
    omega
  let D := {z : Fin n × X // π z.2 = (c z.1).2}
  let step (z : D) : D := ⟨(z.val.1+1,s z.val.1 • z.val.2), by
    rw [equivariant,z.property]; exact (side z.val.1).2⟩
  let label : D ↪ V × X := ⟨fun z => ((c z.val.1).1, z.val.2), by
    intro a b equal
    have sheets := congrArg (fun z : V × X => z.2) equal
    have colors := congrArg (fun z : V × X => z.1) equal
    have phase : a.val.1 = b.val.1 := c.injective (Prod.ext colors
      (a.property.symm.trans ((congrArg π sheets).trans b.property)))
    exact Subtype.ext (Prod.ext phase sheets)⟩
  have adjacent (z : D) : (voltageGraph base edge reverse X).Adj (label z) (label (step z)) :=
    ⟨(side z.val.1).1, rfl⟩
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

end Covers

/-- The sheets of the orbit quotient are the orbits of a normal subgroup. -/
def Blocks {M : Type*} [Group M] (N : Subgroup M) (X : Type*) [MulAction M X] :=
  Set.range (orbit N : X → Set X)

instance {M X : Type*} [Group M] [MulAction M X] (N : Subgroup M) [N.Normal] :
    MulAction M (Blocks N X) where
  smul g b := ⟨g • b.val, by
    obtain ⟨x,hx⟩ := b.property
    exact ⟨g • x, by rw [← hx,smul_orbit_eq_orbit_smul]⟩⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)

def block {M X : Type*} [Group M] [MulAction M X] (N : Subgroup M) (x : X) : Blocks N X :=
  ⟨orbit N x,⟨x,rfl⟩⟩

theorem block_onto {M X : Type*} [Group M] [MulAction M X] (N : Subgroup M) :
    Surjective (block (X := X) N) := by
  rintro ⟨_,x,rfl⟩
  exact ⟨x,rfl⟩

theorem block_eq_iff {M X : Type*} [Group M] [MulAction M X] (N : Subgroup M) (x y : X) :
    block N x = block N y ↔ x ∈ orbit N y :=
  Subtype.ext_iff.trans orbit_eq_iff

theorem block_smul {M X : Type*} [Group M] [MulAction M X] (N : Subgroup M)
    [N.Normal] (g : M) (x : X) : block N (g • x) = g • block N x :=
  Subtype.ext (smul_orbit_eq_orbit_smul N x g).symm

theorem fiber_card_le {M X : Type*} [Group M] [Finite M] [MulAction M X]
    (N : Subgroup M) (b : Blocks N X) :
    Nat.card {x : X // block N x = b} ≤ Nat.card N := by
  obtain ⟨x,rfl⟩ := block_onto N b
  let f (a : N) : {y : X // block N y = block N x} :=
    ⟨a • x,(block_eq_iff N _ _).mpr ⟨a,rfl⟩⟩
  apply Nat.card_le_card_of_surjective f
  intro z
  obtain ⟨a,ha⟩ := (block_eq_iff N _ _).mp z.property
  exact ⟨a,Subtype.ext ha⟩

/-- Every dyadic simple cycle in a quotient by a normal solvable subgroup
lifts whenever its orbits have power-of-two size. -/
theorem lift_normal_orbits {V M X : Type*} [Group M] [Finite M] [MulAction M X]
    [Finite X] (N : Subgroup M) [N.Normal] [Group.IsSolvable N]
    (sizes : ∀ x : X, ∃ r : ℕ, Nat.card (orbit N x) = 2^r)
    (base : SimpleGraph V) (edge : V → V → M)
    (rev : ∀ {v w}, base.Adj v w → edge w v = (edge v w)⁻¹)
    {k : ℕ} (hk : 2 ≤ k) (c : (cycleGraph (2^k)).Copy (voltageGraph base edge rev (Blocks N X))) :
    ∃ d : ℕ, k ≤ d ∧ 2^d ≤ 2^k * Nat.card {x : X // block N x = (c 0).2} ∧
      cycleGraph (2^d) ⊑ voltageGraph base edge rev X := by
  apply lift_cycle base edge rev (block N) (block_onto N) (block_smul N) hk c
  intro g stable
  obtain ⟨x,hx⟩ := block_onto N (c 0).2
  have h : g • x ∈ orbit N x := (block_eq_iff N _ _).mp
    ((block_smul N g x).trans ((congrArg (fun b : Blocks N X => g • b) hx).trans
      (stable.trans hx.symm)))
  obtain ⟨r,size⟩ := sizes x
  obtain ⟨y,hy,j,hj⟩ := period_on_normal_orbit N g x h r size
  exact ⟨y, ((block_eq_iff N _ _).mpr hy).trans hx,j,hj⟩

/-- In particular, a normal two-subgroup can be removed from the sheets of
any voltage graph when searching for a power-of-two cycle. -/
theorem lift_normal_two_group {V M X : Type*} [Group M] [Finite M] [MulAction M X]
    [Finite X] (N : Subgroup M) [N.Normal] (two : IsPGroup 2 N)
    (base : SimpleGraph V) (edge : V → V → M)
    (rev : ∀ {v w}, base.Adj v w → edge w v = (edge v w)⁻¹)
    {k : ℕ} (hk : 2 ≤ k) (cycle : cycleGraph (2^k) ⊑ voltageGraph base edge rev (Blocks N X)) :
    ∃ d : ℕ, k ≤ d ∧ 2^d ≤ 2^k * Nat.card N ∧ cycleGraph (2^d) ⊑ voltageGraph base edge rev X := by
  let : Group.IsNilpotent N := two.isNilpotent
  obtain ⟨c⟩ := cycle
  obtain ⟨d,low,high,lifted⟩ := lift_normal_orbits N (fun x : X => two.card_orbit x) base edge rev hk c
  exact ⟨d,low,high.trans (Nat.mul_le_mul_left _ (fiber_card_le N (c 0).2)),lifted⟩

section Tetrahedron

/-- Tree edges have label one and the three other edges carry `a,b,c`
in cyclic order on the three nonzero colors. -/
def tetraEdges {M : Type*} [Group M] (a b c : M) (i j : Fin 4) : M :=
  ![![1,1,1,1], ![1,1,a,c⁻¹], ![1,a⁻¹,1,b], ![1,c,b⁻¹,1]] i j

theorem tetra_reverse {M : Type*} [Group M] (a b c : M) (i j : Fin 4) :
    tetraEdges a b c j i = (tetraEdges a b c i j)⁻¹ := by
  fin_cases i <;> fin_cases j <;> simp [tetraEdges]

abbrev tetraGraph {M : Type*} [Group M] (a b c : M) (X : Type*) [MulAction M X] :=
  voltageGraph (⊤ : SimpleGraph (Fin 4)) (tetraEdges a b c) (fun {_ _} _ => tetra_reverse a b c _ _) X

/-- A commuting action on the orbit quotient supplies a square, octagon
or 16-cycle by the earlier signed tetrahedral reduction. -/
theorem commuting_tetra {M Y : Type} [Group M] [MulAction M Y] [Nonempty Y] (a b c : M)
    (ab : Commute (toPermHom M Y a) (toPermHom M Y b))
    (bc : Commute (toPermHom M Y b) (toPermHom M Y c))
    (ca : Commute (toPermHom M Y c) (toPermHom M Y a)) :
    cycleGraph 4 ⊑ tetraGraph a b c Y ∨ cycleGraph 8 ⊑ tetraGraph a b c Y ∨
      cycleGraph 16 ⊑ tetraGraph a b c Y := by
  obtain ⟨A, inst, f, u,v,w,shifts⟩ :=
    TetrahedralReduction.commutingOrbit _ _ _ ab bc ca
  let e : Fin 4 × A ↪ Fin 4 × Y := Function.Embedding.prodMap (Function.Embedding.refl _) f
  apply TetrahedralReduction.abelianTetrahedron _ e u v w
  · intro j hj x
    change (⊤ : SimpleGraph (Fin 4)).Adj 0 j ∧ tetraEdges a b c 0 j • f x = f x
    refine ⟨Ne.symm hj,?_⟩
    fin_cases j <;> simp [tetraEdges]
  · intro x
    exact ⟨show (1 : Fin 4) ≠ 2 by decide,(shifts x).1⟩
  · intro x
    exact ⟨show (2 : Fin 4) ≠ 3 by decide,(shifts x).2.1⟩
  · intro x
    exact ⟨show (3 : Fin 4) ≠ 1 by decide,(shifts x).2.2⟩

/-- When the three permutations commute on the orbit set of a normal
solvable subgroup and the orbits have dyadic sizes at most B, a dyadic
cycle exists upstairs with length at most 16B. -/
theorem tetra_solvable_blocks {M X : Type} [Group M] [Finite M] [MulAction M X]
    [Finite X] [Nonempty X] (N : Subgroup M) [N.Normal] [Group.IsSolvable N]
    (sizes : ∀ x : X, ∃ r : ℕ, Nat.card (orbit N x) = 2^r) (B : ℕ)
    (bound : ∀ x : X, Nat.card (orbit N x) ≤ B) (a b c : M)
    (ab : Commute (toPermHom M (Blocks N X) a) (toPermHom M (Blocks N X) b))
    (bc : Commute (toPermHom M (Blocks N X) b) (toPermHom M (Blocks N X) c))
    (ca : Commute (toPermHom M (Blocks N X) c) (toPermHom M (Blocks N X) a)) :
    ∃ d : ℕ, 2 ≤ d ∧ 2^d ≤ 16 * B ∧ cycleGraph (2^d) ⊑ tetraGraph a b c X := by
  classical
  let Y := Blocks N X
  let : Nonempty Y := Nonempty.map (block N) (inferInstance : Nonempty X)
  have lift {k : ℕ} (hk : 2 ≤ k) (ub : 2^k ≤ 16) (h : cycleGraph (2^k) ⊑ tetraGraph a b c Y) :
      ∃ d : ℕ, 2 ≤ d ∧ 2^d ≤ 16 * B ∧ cycleGraph (2^d) ⊑ tetraGraph a b c X := by
    obtain ⟨path⟩ := h
    obtain ⟨d,lo,hi,cyc⟩ := lift_normal_orbits N sizes (⊤ : SimpleGraph (Fin 4)) (tetraEdges a b c)
      (fun {_ _} _ => tetra_reverse a b c _ _) hk path
    obtain ⟨x,hx⟩ := block_onto N (path 0).2
    let e : {z : X // block N z = (path 0).2} ≃ orbit N x :=
      Equiv.subtypeEquivRight fun z => hx ▸ block_eq_iff N z x
    exact ⟨d,hk.trans lo,hi.trans (Nat.mul_le_mul ub ((Nat.card_congr e).le.trans (bound x))),cyc⟩
  rcases commuting_tetra a b c ab bc ca with h | h | h
  · exact lift (k := 2) (by decide) (by decide) h
  · exact lift (k := 3) (by decide) (by decide) h
  · exact lift (k := 4) (by decide) (by decide) h

/-- Commutation modulo N implies commutation of the permutations of its orbits. -/
theorem block_commute {M X : Type} [Group M] [MulAction M X]
    (N : Subgroup M) [N.Normal] (a b : M)
    (ab : Commute ((QuotientGroup.mk' N) a) ((QuotientGroup.mk' N) b)) :
    Commute (toPermHom M (Blocks N X) a) (toPermHom M (Blocks N X) b) := by
  let Y := Blocks N X
  let act := toPermHom M Y
  have trivial : N ≤ act.ker := by
    intro g hg
    apply Equiv.Perm.ext
    intro y
    obtain ⟨x,rfl⟩ := block_onto N y
    exact (block_smul N g x).symm.trans ((block_eq_iff N _ _).2 ⟨⟨g,hg⟩,rfl⟩)
  exact ab.map (QuotientGroup.lift N act trivial)

/-- If the marked permutations commute modulo a normal two-subgroup, the
cover contains a cycle of power-of-two length at most sixteen times its order. -/
theorem tetra_abelian_quotient {M X : Type} [Group M] [Finite M] [MulAction M X]
    [Finite X] [Nonempty X] (N : Subgroup M) [N.Normal] (two : IsPGroup 2 N)
    (a b c : M) (ab : Commute ((QuotientGroup.mk' N) a) ((QuotientGroup.mk' N) b))
    (bc : Commute ((QuotientGroup.mk' N) b) ((QuotientGroup.mk' N) c))
    (ca : Commute ((QuotientGroup.mk' N) c) ((QuotientGroup.mk' N) a)) :
    ∃ d : ℕ, 2 ≤ d ∧ 2^d ≤ 16 * Nat.card N ∧ cycleGraph (2^d) ⊑ tetraGraph a b c X := by
  let : Group.IsNilpotent N := two.isNilpotent
  apply tetra_solvable_blocks N (fun x : X => two.card_orbit x)
    (Nat.card N) (fun x => ?_) a b c (block_commute N a b ab) (block_commute N b c bc)
      (block_commute N c a ca)
  exact Nat.card_le_card_of_surjective (fun n : N => (⟨n • x,⟨n,rfl⟩⟩ : orbit N x))
    (fun ⟨_,n,hn⟩ => ⟨n,Subtype.ext hn⟩)

/-- A solvable commutator subgroup may have odd-order elements as long as
its orbits on the sheets have dyadic sizes. -/
theorem tetra_commutator_orbits {M X : Type} [Group M] [Finite M] [MulAction M X]
    [Finite X] [Nonempty X] [Group.IsSolvable (_root_.commutator M)]
    (sizes : ∀ x : X, ∃ r : ℕ, Nat.card (orbit (_root_.commutator M) x) = 2^r)
    (B : ℕ) (bound : ∀ x : X, Nat.card (orbit (_root_.commutator M) x) ≤ B) (a b c : M) :
    ∃ d : ℕ, 2 ≤ d ∧ 2^d ≤ 16 * B ∧ cycleGraph (2^d) ⊑ tetraGraph a b c X := by
  let N := _root_.commutator M
  let : IsMulCommutative (M ⧸ N) := Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  exact tetra_solvable_blocks N sizes B bound a b c (block_commute N a b (mul_comm' _ _))
    (block_commute N b c (mul_comm' _ _)) (block_commute N c a (mul_comm' _ _))

/-- The sheet action need not be regular or faithful. -/
theorem tetra_commutator_two {M X : Type} [Group M] [Finite M] [MulAction M X]
    [Finite X] [Nonempty X] (two : IsPGroup 2 (_root_.commutator M)) (a b c : M) :
    ∃ d : ℕ, 2 ≤ d ∧ 2^d ≤ 16 * Nat.card (_root_.commutator M) ∧
      cycleGraph (2^d) ⊑ tetraGraph a b c X := by
  let N := _root_.commutator M
  let : IsMulCommutative (M ⧸ N) := Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  exact tetra_abelian_quotient N two a b c (mul_comm' _ _) (mul_comm' _ _) (mul_comm' _ _)

end Tetrahedron

end Erdos64NormalCovers
