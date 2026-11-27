import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic

/-!
# Lifting a power-of-two cycle through a finite graph covering

A lap around a simple cycle permutes the sheets. A sheet of period `d`
gives a simple cycle upstairs of length `d` times the base length.
The sheet counts for which *every* return permutation has a power-of-two
orbit are exactly 1, 2 and 4.
-/

namespace Erdos64CycleCovers

open Function SimpleGraph
open Fin.NatCast

/-- Every permutation has a point fixed after some power-of-two number of steps. -/
def GoodSheets (S : Type*) : Prop :=
  ∀ σ : Equiv.Perm S, ∃ (x : S) (j : ℕ), (σ : S → S)^[2 ^ j] x = x

theorem goodSheets_of_equiv {S T : Type*} (e : S ≃ T) (h : GoodSheets S) : GoodSheets T := by
  intro σ
  let τ := (e.trans σ).trans e.symm
  obtain ⟨x, j, hx⟩ := h τ
  have conjugates : Semiconj e (τ : S → S) (σ : T → T) := by
    intro y
    simp [τ]
  exact ⟨e x, j, ((conjugates.iterate_right (2 ^ j)) x).symm.trans (congrArg e hx)⟩

private theorem rotate_iterate {m : ℕ} [NeZero m] (x : Fin m) (d : ℕ) :
    (finRotate m : Fin m → Fin m)^[d] x = x + (d : Fin m) := by
  induction d with
  | zero => simp
  | succ d ih => simp [iterate_succ_apply', ih, finRotate_apply, add_assoc]

private theorem odd_rotate {m : ℕ} (hm : 1 < m) (odd : Odd m) (x : Fin m) (j : ℕ) :
    (finRotate m : Fin m → Fin m)^[2 ^ j] x ≠ x := by
  let : NeZero m := ⟨by omega⟩
  intro eq
  rw [rotate_iterate, add_eq_left, Fin.natCast_eq_zero] at eq
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp eq
  cases k with
  | zero => simp only [pow_zero] at hk; omega
  | succ k =>
    rw [hk, pow_succ] at odd
    obtain ⟨a, ha⟩ := odd
    omega

set_option maxRecDepth 8192 in
private theorem small_fourth {m : ℕ} (small : m = 1 ∨ m = 2 ∨ m = 4) :
    ∀ f : Fin m → Fin m, Injective f → ∃ x, f (f (f (f x))) = x := by
  rcases small with rfl | rfl | rfl <;> decide

/-- Sharp as a criterion on a single return permutation. In even degree at
least six a permutation may consist of a 3-cycle and another odd cycle. -/
theorem goodSheets_fin_iff (m : ℕ) : GoodSheets (Fin m) ↔ m = 1 ∨ m = 2 ∨ m = 4 := by
  constructor
  · intro good
    by_contra! other
    rcases Nat.even_or_odd m with even | odd
    · by_cases empty : m = 0
      · subst m
        obtain ⟨x, _⟩ := good (Equiv.refl _)
        exact x.elim0
      obtain ⟨a, ha⟩ := even
      have hm : 6 ≤ m := by omega
      let S := Fin 3 ⊕ Fin (m - 3)
      let e : S ≃ Fin m := finSumFinEquiv.trans (finCongr (by omega))
      let σ : Equiv.Perm S := Equiv.sumCongr (finRotate 3) (finRotate (m - 3))
      obtain ⟨x, j, hx⟩ := goodSheets_of_equiv e.symm good σ
      cases x with
      | inl x =>
        have h : Semiconj (Sum.inl : Fin 3 → S) (finRotate 3) σ := fun _ => rfl
        exact odd_rotate (by decide : 1 < 3) (by decide) x j
          (Sum.inl.inj (((h.iterate_right _) x).trans hx))
      | inr x =>
        have h : Semiconj (Sum.inr : Fin (m - 3) → S) (finRotate (m - 3)) σ := fun _ => rfl
        exact odd_rotate (by omega : 1 < m - 3) ⟨a - 2, by omega⟩ x j
          (Sum.inr.inj (((h.iterate_right _) x).trans hx))
    · obtain ⟨x, j, hx⟩ := good (finRotate m)
      exact odd_rotate (by obtain ⟨a, ha⟩ := odd; omega) odd x j hx
  · intro small σ
    obtain ⟨x, hx⟩ := small_fourth small σ σ.injective
    exact ⟨x, 2, hx⟩

/-- The lift of a neighbor is unique at each vertex of a graph covering. -/
def LocallyBijective {U V : Type*} {H : SimpleGraph U} {G : SimpleGraph V}
    (π : H →g G) : Prop :=
  ∀ (u : U) (v : V), G.Adj (π u) v → ∃! w, H.Adj u w ∧ π w = v

abbrev Fiber {U V : Type*} {H : SimpleGraph U} {G : SimpleGraph V}
    (π : H →g G) (v : V) := {u : U // π u = v}

section Edges
variable {U V : Type*} {H : SimpleGraph U} {G : SimpleGraph V}
  {π : H →g G} (cover : LocallyBijective π)

private noncomputable def across {a b : V} (h : G.Adj a b) (u : Fiber π a) : Fiber π b :=
  let lift := cover u.1 b (u.2.symm ▸ h)
  ⟨lift.choose, lift.choose_spec.1.2⟩

private theorem across_adj {a b : V} (h : G.Adj a b) (u : Fiber π a) :
    H.Adj u.val (across cover h u).val :=
  (cover u.val b (u.2.symm ▸ h)).choose_spec.1.1

private theorem across_inverse {a b : V} (h : G.Adj a b) (u : Fiber π a) :
    across cover h.symm (across cover h u) = u := by
  apply Subtype.ext
  apply ((cover (across cover h u).val a ((across cover h u).property.symm ▸ h.symm)).unique)
  · exact ⟨across_adj cover h.symm _, (across cover h.symm _).property⟩
  · exact ⟨(across_adj cover h u).symm, u.property⟩

private noncomputable def acrossEquiv {a b : V} (h : G.Adj a b) : Fiber π a ≃ Fiber π b where
  toFun := across cover h
  invFun := across cover h.symm
  left_inv := across_inverse cover h
  right_inv := across_inverse cover h.symm

end Edges

section AroundCycle
variable {n : ℕ} [NeZero n] {S : Type*}

/-- One edge of a lifted cycle, in coordinates consisting of position and sheet. -/
private def advance (edge : Fin n → Equiv.Perm S) : Fin n × S → Fin n × S :=
  fun z => (z.1 + 1, edge z.1 z.2)

private theorem advance_injective (edge : Fin n → Equiv.Perm S) :
    Injective (advance edge) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  have ij : i = j := add_right_cancel (congrArg Prod.fst h)
  subst j
  exact Prod.ext rfl ((edge i).injective (congrArg Prod.snd h))

private theorem phase (edge : Fin n → Equiv.Perm S) (z : Fin n × S) (t : ℕ) :
    ((advance edge)^[t] z).1 = z.1 + (t : Fin n) := by
  induction t with
  | zero => simp
  | succ t ih => simp [iterate_succ_apply', advance, ih, add_assoc]

private theorem lap_phase (edge : Fin n → Equiv.Perm S) (x : S) :
    ((advance edge)^[n] (0, x)).1 = 0 := by simp [phase]

/-- The sheet permutation obtained by going around the base cycle once. -/
private noncomputable def lap [Finite S] (edge : Fin n → Equiv.Perm S) : Equiv.Perm S :=
  let f : S → S := fun x => ((advance edge)^[n] (0, x)).2
  let hf : Injective f := by
    intro x y eq
    have h := (advance_injective edge).iterate n
    have pairs : (advance edge)^[n] (0, x) = (advance edge)^[n] (0, y) :=
      Prod.ext ((lap_phase edge x).trans (lap_phase edge y).symm) eq
    exact congrArg Prod.snd (h pairs)
  Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)

private theorem laps [Finite S] (edge : Fin n → Equiv.Perm S) (x : S) (t : ℕ) :
    (advance edge)^[n*t] (0, x) = (0, (lap edge : S → S)^[t] x) := by
  have h : Semiconj (fun x : S => ((0 : Fin n), x)) (lap edge) ((advance edge)^[n]) := by
    intro y
    exact Prod.ext (lap_phase edge y).symm rfl
  rw [iterate_mul]
  exact ((h.iterate_right t) x).symm

private theorem period_above [Finite S] (edge : Fin n → Equiv.Perm S) (x : S) :
    minimalPeriod (advance edge) (0, x) = n * minimalPeriod (lap edge) x := by
  apply Nat.dvd_antisymm
  · apply IsPeriodicPt.minimalPeriod_dvd
    change (advance edge)^[n * minimalPeriod (lap edge) x] (0, x) = (0, x)
    simp [laps]
  · let t := minimalPeriod (advance edge) (0, x)
    have ht : (advance edge)^[t] (0, x) = (0, x) := iterate_minimalPeriod
    have div : n ∣ t := Fin.natCast_eq_zero.mp (by
      simpa [phase] using congrArg Prod.fst ht)
    obtain ⟨d, hd⟩ := div
    rw [hd, laps] at ht
    have hd' : IsPeriodicPt (lap edge) d x := congrArg Prod.snd ht
    change n * _ ∣ t
    rw [hd]
    exact Nat.mul_dvd_mul_left _ hd'.minimalPeriod_dvd

end AroundCycle

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

/-- Above an embedded cycle of length `n`, every cycle of the return
permutation produces a simple cycle of the corresponding multiple of `n`. -/
theorem lift_lengths {U V S : Type*} [Finite S] {H : SimpleGraph U} {G : SimpleGraph V}
    (π : H →g G) (cover : LocallyBijective π) (sheets : ∀ v, Fiber π v ≃ S)
    {n : ℕ} (hn : 3 ≤ n) (base : cycleGraph n ⊑ G) :
    ∃ ρ : Equiv.Perm S, ∀ x, cycleGraph (n * minimalPeriod ρ x) ⊑ H := by
  classical
  let : NeZero n := ⟨by omega⟩
  obtain ⟨c⟩ := base
  have side (i : Fin n) : G.Adj (c i) (c (i + 1)) := by
    apply c.toHom.map_rel'
    apply cycleGraph_adj'.mpr
    right
    simp [Nat.mod_eq_of_lt (show 1 < n by omega)]
  let edge (i : Fin n) : Equiv.Perm S :=
    ((sheets (c i)).symm.trans (acrossEquiv cover (side i))).trans (sheets (c (i + 1)))
  let vert (z : Fin n × S) : U := ((sheets (c z.1)).symm z.2).val
  have vert_inj : Injective vert := by
    rintro ⟨i, x⟩ ⟨j, y⟩ eq
    have proj := congrArg π eq
    change π ((sheets (c i)).symm x).val = π ((sheets (c j)).symm y).val at proj
    rw [((sheets (c i)).symm x).property, ((sheets (c j)).symm y).property] at proj
    have ij := c.injective proj
    subst j
    exact Prod.ext rfl ((sheets (c i)).symm.injective (Subtype.ext eq))
  let label : Fin n × S ↪ U := ⟨vert, vert_inj⟩
  have adj (z : Fin n × S) : H.Adj (label z) (label (advance edge z)) := by
    rcases z with ⟨i, x⟩
    simpa [label, vert, advance, edge, acrossEquiv] using
      across_adj cover (side i) ((sheets (c i)).symm x)
  refine ⟨lap edge, fun x => ?_⟩
  have pos := minimalPeriod_pos_of_mem_periodicPts ((lap edge).injective.mem_periodicPts x)
  have large : 3 ≤ n * minimalPeriod (lap edge) x :=
    hn.trans (Nat.le_mul_of_pos_right n pos)
  rw [← period_above] at large ⊢
  exact orbit_cycle (advance edge) label adj (0, x) large

/-- A graph covering with one, two or four sheets preserves the existence
of a simple power-of-two cycle, in the walk formulation of Erdős 64. -/
theorem lift_power_cycle {U V : Type*} {H : SimpleGraph U} {G : SimpleGraph V}
    (π : H →g G) (cover : LocallyBijective π) {m : ℕ} (sheets : ∀ v, Fiber π v ≃ Fin m)
    (small : m = 1 ∨ m = 2 ∨ m = 4) {k : ℕ} (hk : 2 ≤ k)
    {v : V} (c : G.Walk v v) (hc : c.IsCycle) (length : c.length = 2 ^ k) :
    ∃ (l : ℕ) (u : U) (p : H.Walk u u),
      2 ≤ l ∧ p.IsCycle ∧ p.length = 2 ^ l ∧ k ≤ l ∧ l ≤ k + 2 := by
  have hn : 3 ≤ 2 ^ k := length ▸ hc.three_le_length
  have base := (cycleGraph_isContained_iff hn).mpr ⟨v, c, hc, length⟩
  obtain ⟨ρ, lifts⟩ := lift_lengths π cover sheets hn base
  obtain ⟨x, hx⟩ := small_fourth small ρ ρ.injective
  have per : IsPeriodicPt ρ (2 ^ 2) x := hx
  obtain ⟨i, bound_i, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp per.minimalPeriod_dvd
  have upstairs := lifts x
  rw [hi, ← pow_add] at upstairs
  have bound : 2 ≤ k + i := by omega
  have hlen : 3 ≤ 2 ^ (k + i) := hn.trans (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨u, p, hp, hl⟩ := (cycleGraph_isContained_iff hlen).mp upstairs
  exact ⟨k + i, u, p, bound, hp, hl, by omega, by omega⟩

/-- In a voltage cover with finite two-group of sheets, any simple base cycle
of power-of-two length lifts to a simple cycle of power-of-two length.
The shifts may fail to commute. The hypothesis records just the edges above
the chosen cycle, so other edges in the covering graph are immaterial. -/
theorem lift_two_group {U S : Type*} [Group S] [Finite S] (two : IsPGroup 2 S)
    {G : SimpleGraph U} {k : ℕ} (hk : 2 ≤ k) (shift : Fin (2 ^ k) → S)
    (label : Fin (2 ^ k) × S ↪ U)
    (adj : ∀ i x, G.Adj (label (i,x)) (label (i + 1,x * shift i))) :
    ∃ d : ℕ, k ≤ d ∧ cycleGraph (2 ^ d) ⊑ G := by
  classical
  let n := 2 ^ k
  let edge (i : Fin n) : Equiv.Perm S := Equiv.mulRight (shift i)
  let translate (g : S) (z : Fin n × S) := (z.1, g * z.2)
  have equivariant (g : S) : Function.Commute (translate g) (advance edge) := by
    rintro ⟨i,x⟩
    exact Prod.ext rfl (mul_assoc g x (shift i)).symm
  let t := lap edge (1 : S)
  have oneLap (x : S) : lap edge x = x * t := by
    have eq := congrArg Prod.snd (((equivariant x).iterate_right n) (0,1))
    change x * t = ((advance edge)^[n] (0,x * 1)).2 at eq
    change ((advance edge)^[n] (0,x)).2 = x * t
    simpa only [mul_one] using eq.symm
  have iterates (j : ℕ) : (lap edge : S → S)^[j] 1 = t ^ j := by
    induction j with
    | zero => simp
    | succ j ih => rw [iterate_succ_apply', oneLap, ih, pow_succ]
  obtain ⟨j,hj⟩ := two t
  have closed : IsPeriodicPt (lap edge) (2 ^ j) 1 := (iterates _).trans hj
  obtain ⟨d,_,hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp closed.minimalPeriod_dvd
  have length : minimalPeriod (advance edge) (0,1) = 2 ^ (k + d) := by
    rw [period_above, hd, pow_add]
  have four : 4 ≤ 2 ^ (k + d) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ k + d)
  have big : 3 ≤ minimalPeriod (advance edge) (0,1) := by rw [length]; omega
  have cyc := orbit_cycle (advance edge) label (fun z => adj z.1 z.2) (0,1) big
  exact ⟨k + d, by omega, length ▸ cyc⟩

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

/-- Every affine permutation on an abelian group of power-of-two order
has a point of power-of-two period. Its linear part can be arbitrary. -/
theorem affine_dyadic_period {A : Type*} [AddCommGroup A] [Finite A]
    (r : ℕ) (size : Nat.card A = 2^r) (f : Equiv.Perm A)
    (L : A →+ A) (b : A) (affine : ∀ x, f x = L x + b) :
    ∃ (x : A) (j : ℕ), IsPeriodicPt f (2^j) x := by
  classical
  have powers (n : ℕ) : ∃ (T : A →+ A) (c : A), ∀ x : A, (f : A → A)^[n] x = T x + c := by
    induction n with
    | zero => exact ⟨AddMonoidHom.id A,0,fun x => (add_zero x).symm⟩
    | succ n ih =>
      obtain ⟨T,c,h⟩ := ih
      refine ⟨L.comp T,L c+b,fun x => ?_⟩
      rw [iterate_succ_apply',affine,h,map_add,AddMonoidHom.comp_apply,add_assoc]
  have positive := minimalPeriod_pos_of_mem_periodicPts (f.injective.mem_periodicPts (0:A))
  obtain ⟨j,m,odd,period⟩ := Nat.exists_eq_two_pow_mul_odd positive.ne'
  let g := (f : A → A)^[2^j]
  obtain ⟨T,c,hg⟩ := powers (2^j)
  let z (i : ℕ) := g^[i] 0
  have step (i : ℕ) : z (i+1) = T (z i) + c := by
    dsimp only [z]
    rw [iterate_succ_apply']
    exact hg _
  have closed : z m = z 0 := by
    change ((f : A → A)^[2^j])^[m] 0 = 0
    rw [← iterate_mul, ← period, iterate_minimalPeriod]
  have coprime : (Nat.card A).Coprime m := size ▸ odd.coprime_two_left.pow_left r
  obtain ⟨x,hx⟩ := fixed_of_coprime_affine_orbit T c m coprime z step closed
  exact ⟨x,j,(hg x).trans hx⟩

/-- An abelian group of finite order has a power-of-two orbit for every
affine permutation exactly when its order is a power of two. -/
theorem all_affine_dyadic_iff (A : Type*) [AddCommGroup A] [Finite A] :
    (∀ (f : Equiv.Perm A) (L : A →+ A) (b : A), (∀ x, f x = L x + b) →
      ∃ (x : A) (j : ℕ), IsPeriodicPt f (2^j) x) ↔ ∃ r : ℕ, Nat.card A = 2^r := by
  constructor
  · intro all
    have two : IsPGroup 2 (Multiplicative A) := by
      intro u
      let f := Equiv.addRight u.toAdd
      obtain ⟨x,k,hx⟩ := all f (AddMonoidHom.id A) u.toAdd (fun _ => rfl)
      have iter (n : ℕ) : (f : A → A)^[n] x = x + n • u.toAdd := by
        induction n with
        | zero => simp
        | succ n ih =>
          rw [iterate_succ_apply',ih,succ_nsmul]
          exact add_assoc _ _ _
      have zero : (2^k) • u.toAdd = 0 := add_left_cancel
        (((iter (2^k)).symm.trans hx).trans (add_zero x).symm)
      exact ⟨k,congrArg Multiplicative.ofAdd zero⟩
    exact two.exists_card_eq
  · rintro ⟨r,h⟩ f L b affine
    exact affine_dyadic_period r h f L b affine

/-- A simple dyadic cycle lifts through arbitrary affine matchings on sheets
indexed by a finite abelian group of power-of-two order. -/
theorem lift_affine_two_primary {U A : Type*} [AddCommGroup A] [Finite A] {G : SimpleGraph U}
    (r : ℕ) (size : Nat.card A = 2^r) {k : ℕ} (hk : 2 ≤ k)
    (linear : Fin (2^k) → A ≃+ A) (shift : Fin (2^k) → A)
    (label : Fin (2^k) × A ↪ U)
    (adj : ∀ i x, G.Adj (label (i,x)) (label (i+1,linear i x + shift i))) :
    ∃ d : ℕ, k ≤ d ∧ d ≤ k+r ∧ cycleGraph (2^d) ⊑ G := by
  classical
  let n := 2^k
  let edge (i : Fin n) : Equiv.Perm A := (linear i).toEquiv.trans (Equiv.addRight (shift i))
  have accumulated (t : ℕ) : ∃ (L : A →+ A) (b : A), ∀ x : A,
      ((advance edge)^[t] (0,x)).2 = L x + b := by
    induction t with
    | zero => exact ⟨AddMonoidHom.id A,0,fun x => (add_zero x).symm⟩
    | succ t ih =>
      obtain ⟨L,b,h⟩ := ih
      let T := (linear (t : Fin n)).toAddMonoidHom
      refine ⟨T.comp L,T b + shift (t : Fin n),fun x => ?_⟩
      rw [iterate_succ_apply']
      change linear _ (((advance edge)^[t] (0,x)).2) + shift _ = T (L x) + (T b + _)
      have pos : ((advance edge)^[t] (0,x)).1 = (t : Fin n) := by simp [phase]
      rw [pos,h,map_add,add_assoc]
      rfl
  obtain ⟨L,b,h⟩ := accumulated n
  obtain ⟨x,j,period⟩ := affine_dyadic_period r size (lap edge) L b h
  obtain ⟨d,_,hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp period.minimalPeriod_dvd
  have count : 2^d ≤ 2^r := by
    let := Fintype.ofFinite A
    rw [← hd, ← size, Nat.card_eq_fintype_card]
    exact minimalPeriod_le_card
  have bound : d ≤ r := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp count
  have length : minimalPeriod (advance edge) (0,x) = 2^(k+d) := by
    rw [period_above,hd,pow_add]
  have large : 3 ≤ minimalPeriod (advance edge) (0,x) := by
    rw [length]
    have four : 4 ≤ 2^(k+d) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ k+d)
    omega
  have cyc := orbit_cycle (advance edge) label (fun z => adj z.1 z.2) (0,x) large
  exact ⟨k+d,by omega,by omega,length ▸ cyc⟩

end Erdos64CycleCovers
