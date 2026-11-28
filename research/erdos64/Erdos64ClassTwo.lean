import Erdos64NormalCovers
import Erdos64Heisenberg
import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1

/-!
# A sharp 32 bound for regular tetrahedral covers with a central commutator

Chad Mazzola (@ubuwaits), using Codex.

Two marked chords multiply on the left by a and b. The third preserves the sheet.
If their commutator is central, a finite regular cover has a dyadic cycle of
length at most 32. For a commutator of order greater than two the proof gives
an explicit 32-cycle. The group normal-form identity used here was proved
by @mejiasd3v in the bipartite matching reduction, PR 5820.
-/

namespace Erdos64ClassTwo

open SimpleGraph Function MulAction Erdos64NormalCovers
open scoped commutatorElement
open Fin.NatCast

private abbrev Point := Fin 4 × (ℤ × ℤ × ℤ)

private def product (v w : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (v.1+w.1,v.2.1+w.2.1,v.2.2+w.2.2+v.1*w.2.1)

private def table : Fin 32 → Point :=
  ![(0,0,0,0), (1,0,0,0), (3,0,0,0), (2,0,-1,0),
    (1,-1,-1,1), (0,-1,-1,1), (2,-1,-1,1), (1,-2,-1,2),
    (3,-2,-1,2), (2,-2,-2,2), (0,-2,-2,2), (1,-2,-2,2),
    (2,-1,-2,0), (0,-1,-2,0), (1,-1,-2,0), (2,0,-2,-2),
    (3,0,-1,-2), (0,0,-1,-2), (2,0,-1,-2), (1,-1,-1,-1),
    (0,-1,-1,-1), (2,-1,-1,-1), (1,-2,-1,0), (0,-2,-1,0),
    (2,-2,-1,0), (3,-2,0,0), (0,-2,0,0), (1,-2,0,0),
    (2,-1,0,0), (0,-1,0,0), (1,-1,0,0), (2,0,0,0)]

/-- All repeated horizontal positions of the same color differ by two central steps. -/
private theorem separated : ∀ i j : Fin 32, i ≠ j →
    let v := table i
    let w := table j
    v.1 ≠ w.1 ∨ (0 < (v.2.1-w.2.1).natAbs ∧ (v.2.1-w.2.1).natAbs ≤ 2) ∨
      (0 < (v.2.2.1-w.2.2.1).natAbs ∧ (v.2.2.1-w.2.2.1).natAbs ≤ 2) ∨
      (v.2.1=w.2.1 ∧ v.2.2.1=w.2.2.1 ∧ 0 < (v.2.2.2-w.2.2.2).natAbs ∧
        (v.2.2.2-w.2.2.2).natAbs ≤ 2) := by decide

private theorem integral_edges : ∀ i : Fin 32,
    (Erdos64Heisenberg.graph ℤ).Adj (table i) (table (i+1)) := by decide

/-- For this word it suffices that the commutator commutes with the two marks. -/
theorem cycle32_of_commutator_sq_ne {A : Type} [Group A] [Finite A] (a b : A)
    (az : Commute a ⁅a,b⁆) (bz : Commute b ⁅a,b⁆) (large : ⁅a,b⁆^2 ≠ 1) :
    cycleGraph 32 ⊑ tetraGraph a b 1 A := by
  let z := ⁅a,b⁆
  let evaluate (v : ℤ × ℤ × ℤ) := b^v.2.1 * a^v.1 * z^v.2.2
  have correction := OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1.NonfreePerm.commutatorCorrection
    a b az bz
  have mult (v w : ℤ × ℤ × ℤ) : evaluate (product v w) = evaluate v * evaluate w :=
    OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1.NonfreePerm.normalForm_mul a b z correction az bz v w
  have xa (v : ℤ × ℤ × ℤ) : evaluate (Erdos64Heisenberg.shiftX v) = a * evaluate v := by
    simpa [product,Erdos64Heisenberg.shiftX,evaluate,add_comm] using mult (1,0,0) v
  have yb (v : ℤ × ℤ × ℤ) : evaluate (Erdos64Heisenberg.shiftY v) = b * evaluate v := by
    simpa [product,Erdos64Heisenberg.shiftY,evaluate,add_comm] using mult (0,1,0) v
  have crossA (v : ℤ × ℤ × ℤ) : a * evaluate v = evaluate v * a * z^v.2.1 := by
    calc a * evaluate v = evaluate (product (1,0,0) v) := by simp [mult,evaluate]
         _ = evaluate (product (product v (1,0,0)) (0,0,v.2.1)) := by
           congr 1
           ext <;> simp [product,add_comm]
         _ = evaluate v * a * z^v.2.1 := by simp [mult,evaluate]
  have crossB (v : ℤ × ℤ × ℤ) : evaluate v * b = b * evaluate v * z^v.1 := by
    calc evaluate v * b = evaluate (product v (0,1,0)) := by simp [mult,evaluate]
         _ = evaluate (product (product (0,1,0) v) (0,0,v.1)) := by
           congr 1
           ext <;> simp [product,add_comm]
         _ = b * evaluate v * z^v.1 := by simp [mult,evaluate]
  have longOrder : 3 ≤ orderOf z := by
    by_contra! short
    have pos := orderOf_pos z
    have dv : orderOf z ∣ 2 := by interval_cases h : orderOf z <;> decide
    exact large (orderOf_dvd_iff_pow_eq_one.mp dv)
  have distinguish {u v : ℤ} (pos : 0 < (u-v).natAbs) (small : (u-v).natAbs ≤ 2)
      (eq : z^u=z^v) : False := by
    have dv := orderOf_dvd_sub_iff_zpow_eq_zpow.mpr eq
    have ndiv : orderOf z ∣ (u-v).natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr dv)
    have := Nat.le_of_dvd pos ndiv
    omega
  let f (v : Point) := (v.1,evaluate v.2)
  have inj : Injective (f ∘ table) := by
    intro i j equal
    by_contra different
    let v := (table i).2
    let w := (table j).2
    have ev : evaluate v = evaluate w := congrArg Prod.snd equal
    have ey : z^v.2.1 = z^w.2.1 := by
      have h := (crossA v).symm.trans ((congrArg (a*·) ev).trans (crossA w))
      rw [ev] at h
      exact mul_left_cancel h
    have ex : z^v.1 = z^w.1 := by
      have h := (crossB v).symm.trans ((congrArg (·*b) ev).trans (crossB w))
      rw [ev] at h
      exact mul_left_cancel h
    rcases separated i j different with h | h | h | ⟨hx,hy,pos,small⟩
    · exact h (congrArg (fun u : Fin 4 × A => u.1) equal)
    · exact distinguish h.1 h.2 ex
    · exact distinguish h.1 h.2 ey
    · change b^v.2.1 * a^v.1 * z^v.2.2 = b^w.2.1 * a^w.1 * z^w.2.2 at ev
      change v.1=w.1 at hx
      change v.2.1=w.2.1 at hy
      rw [hx,hy] at ev
      exact distinguish pos small (mul_left_cancel ev)
  have dir {v w : Point} (h : Erdos64Heisenberg.oriented v w) :
      (tetraGraph a b 1 A).Adj (f v) (f w) := by
    obtain ⟨i,s⟩ := v
    obtain ⟨j,t⟩ := w
    rcases h with h | h | h | h
    · obtain ⟨rfl,hj,rfl⟩ := h
      refine ⟨Ne.symm hj,?_⟩
      fin_cases j <;> simp [f,tetraEdges]
    · obtain ⟨rfl,rfl,rfl⟩ := h
      exact ⟨show (1 : Fin 4) ≠ 2 by decide,(xa s).symm⟩
    · obtain ⟨rfl,rfl,rfl⟩ := h
      exact ⟨show (2 : Fin 4) ≠ 3 by decide,(yb s).symm⟩
    · obtain ⟨rfl,rfl,rfl⟩ := h
      exact ⟨show (3 : Fin 4) ≠ 1 by decide,one_mul _⟩
  have next (i : Fin 32) : (tetraGraph a b 1 A).Adj (f (table i)) (f (table (i+1))) :=
    (integral_edges i).2.elim dir (fun edge => (dir edge).symm)
  refine ⟨⟨⟨f ∘ table,?_⟩,inj⟩⟩
  intro i j h
  have diff : i-j=1 ∨ j-i=1 := by simpa only [Fin.ext_iff,Fin.val_one',Nat.reduceMod] using cycleGraph_adj'.mp h
  rcases diff with h | h
  · have hi : i=j+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h
    simpa only [hi,comp_apply] using (next j).symm
  · have hj : j=i+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h
    simpa only [hj,comp_apply] using next i

/-- A finite group with central marked commutator has a dyadic cycle of
length at most 32 in its regular tetrahedral cover with a third identity chord. -/
theorem central_commutator_bound {A : Type} [Group A] [Finite A] (a b : A)
    (central : ∀ g : A, Commute g ⁅a,b⁆) :
    ∃ d : ℕ, 2 ≤ d ∧ 2^d ≤ 32 ∧ cycleGraph (2^d) ⊑ tetraGraph a b 1 A := by
  let z := ⁅a,b⁆
  by_cases small : z^2 = 1
  · let N := Subgroup.zpowers z
    let : N.Normal := ⟨by
      intro n hn g
      obtain ⟨i,rfl⟩ := hn
      have h := ((central g).zpow_right i).eq
      rw [h,mul_assoc, mul_inv_cancel,mul_one]
      exact Subgroup.zpow_mem_zpowers z i⟩
    have cd : Nat.card N ∣ 2 := by
      rw [show Nat.card N = orderOf z from Nat.card_zpowers z]
      exact orderOf_dvd_iff_pow_eq_one.mpr small
    have two : IsPGroup 2 N := fun n => ⟨1,orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard n).trans cd)⟩
    let q := QuotientGroup.mk' N
    have commute : Commute (q a) (q b) := by
      apply commutatorElement_eq_one_iff_commute.mp
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z)
    obtain ⟨d,lo,hi,cyc⟩ := tetra_abelian_quotient (X := A) N two a b 1 commute
      (by simp) (by simp)
    exact ⟨d,lo,hi.trans (Nat.mul_le_mul_left 16 (Nat.le_of_dvd (by decide) cd)),cyc⟩
  · exact ⟨5,by decide,by decide,cycle32_of_commutator_sq_ne a b (central a) (central b) small⟩

end Erdos64ClassTwo
